/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
Modified for the Korean algebra textbook: extension namespace.
-/

import VersoManual
import AlgebraBook.Meta.Anchor

open Verso.Genre Manual
open Verso.Doc Elab
open Verso.ArgParse
open Lean

namespace AlgebraBook

-- Reader controls are HTML-only; the checked code and print output stay shared.
block_extension Block.playground
    (file : String) (source : String) (key : String)
    (keep : Bool) (visible : Bool) (exercise : Bool) where
  data := .arr #[.str file, .str source, .str key, .bool keep, .bool visible, .bool exercise]
  traverse _ _ _ := pure none
  toTeX := some fun _ goB _ _ contents => contents.mapM goB
  toHtml :=
    open Verso.Output.Html in
    some fun _ goB _ data contents => do
      let .arr #[_, _, .str key, _, .bool visible, .bool exercise] := data
        | Verso.reportError "Invalid playground metadata" *> pure .empty
      let contents ← contents.mapM goB
      if !visible then return contents
      return {{<div class="book-example" data-snippet={{key}}
        data-exercise-unit={{if exercise then "exercises" else ""}}>{{contents}}</div>}}

block_extension Block.readerDisclosure (title : String) where
  data := .str title
  traverse _ _ _ := pure none
  toTeX := some fun _ goB _ data contents => do
    let .str title := data
      | Verso.reportError "Invalid disclosure title" *> pure .empty
    return .seq #[.raw ("\\paragraph*{" ++ title ++ "}\n"), ← contents.mapM goB]
  toHtml :=
    open Verso.Output.Html in
    some fun _ goB _ data contents => do
      let .str title := data
        | Verso.reportError "Invalid disclosure title" *> pure .empty
      return {{<details class="book-disclosure"><summary>{{title}}</summary>
        <div>{{← contents.mapM goB}}</div></details>}}

@[directive]
meta def hint : DirectiveExpanderOf Unit
  | (), blocks => do
    let contents ← blocks.mapM elabBlock
    ``(Block.other (Block.readerDisclosure "힌트") #[$contents,*])

@[directive]
meta def solution : DirectiveExpanderOf Unit
  | (), blocks => do
    let contents ← blocks.mapM elabBlock
    ``(Block.other (Block.readerDisclosure "풀이") #[$contents,*])

block_extension Block.savedLean (file : String) (source : String) where
  data := .arr #[.str file, .str source]

  traverse _ _ _ := pure none
  toTeX := some fun _ goB _ _ contents =>
    contents.mapM goB
  toHtml := some fun _ goB _ _ contents =>
    contents.mapM goB

block_extension Block.savedImport (file : String) (source : String) where
  data := .arr #[.str file, .str source]

  traverse _ _ _ := pure none
  toTeX := some fun _ _ _ _ _ =>
    pure .empty
  toHtml := some fun _ _ _ _ _ =>
    pure .empty

/--
Lean code that is saved to the examples file.
-/
@[code_block savedLean]
def savedLean : CodeBlockExpanderOf InlineLean.LeanBlockConfig
  | args, code => do
    let underlying ← InlineLean.lean args code
    let file ← getFileName
    let pos := (← getFileMap).toPosition ((← getRef).getPos?.getD 0)
    let key := toString (hash (file, pos.line, pos.column))
    let saved ← ``(Block.other (Block.savedLean $(quote file) $(quote code.getString)) #[$underlying])
    let exercise := !args.keep && code.getString.contains "sorry"
    ``(Block.other (Block.playground $(quote file) $(quote code.getString)
      $(quote key) $(quote args.keep) $(quote args.show) $(quote exercise)) #[$saved])

/-- Checked scratch examples, including intentionally unfinished attempts, without exporting them. -/
@[code_block tryLean]
def tryLean : CodeBlockExpanderOf InlineLean.LeanBlockConfig
  | args, code => do
    let underlying ← InlineLean.lean args code
    let file ← getFileName
    let pos := (← getFileMap).toPosition ((← getRef).getPos?.getD 0)
    let key := toString (hash (file, pos.line, pos.column))
    ``(Block.other (Block.playground $(quote file) $(quote code.getString)
      $(quote key) false $(quote args.show) false) #[$underlying])

/--
An import of some other module, to be located in the saved code. Not rendered.
-/
@[code_block]
def savedImport : CodeBlockExpanderOf Unit
  | (), code => do
    ``(Block.other (Block.savedImport $(quote (← getFileName)) $(quote (code.getString))) #[])

/--
Comments to be added as module docstrings to the examples file.
-/
@[code_block]
def savedComment : CodeBlockExpanderOf Unit
  | (), code => do
    let str := code.getString.trimAsciiEnd.copy
    let comment := s!"/-!\n{str}\n-/"
    ``(Block.other (Block.savedLean $(quote (← getFileName)) $(quote comment)) #[])

end AlgebraBook
