/-
Copyright (c) 2024-2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
Modified for the textbook: preserve auxiliary proof completion states.
-/

import VersoManual.InlineLean.Block
import Lean.Data.Json.Basic
import VersoManual.Basic
import VersoManual.HighlightedCode
import Verso.Code.Highlighted.WebAssets
import Verso.Code.HighlightedToTex

import SubVerso.Highlighting


open Verso Genre Manual
open Verso Code Highlighted WebAssets
open Verso Doc Output Html
open Lean
open SubVerso.Highlighting

namespace AlgebraBook

block_extension Block.readerCode
    (hls : Highlighted) (file : Option System.FilePath := none) (range : Option Lsp.Range := none)
    via withHighlighting where
  init s := s.addQuickJumpMapper exampleDomain exampleDomainMapper
  data :=
    let defined := definedNames hls
    Json.arr #[ToJson.toJson hls, ToJson.toJson defined, ToJson.toJson file, ToJson.toJson range]

  traverse id data _ := do
    let .arr #[_, defined, _, _] := data
      | reportError "Expected two-element JSON for Lean code" *> pure none
    match FromJson.fromJson? defined with
    | .error err =>
      reportError <| "Couldn't deserialize Lean code while traversing block example: " ++ err
      pure none
    | .ok (defs : Array (Name × String)) =>
      saveExampleDefs id defs
      pure none
  toTeX :=
    some <| fun _ _ _ data _ => do
      let .arr #[hlJson, _ds, _, _] := data
        | reportError "Expected four-element JSON for Lean code" *> pure .empty
      match FromJson.fromJson? hlJson with
      | .error err =>
        reportError <| "Couldn't deserialize Lean code block while rendering TeX: " ++ err
        pure .empty
      | .ok (hl : Highlighted) =>
        hl.toTeX (g := Manual) (m := ReaderT ExtensionImpls (BuildLogT IO))
  toHtml :=
    open Verso.Output.Html in
    some <| fun _ _ _ data _ => do
      let .arr #[hlJson, _ds, _, _] := data
        | reportError "Expected four-element JSON for Lean code" *> pure .empty
      match FromJson.fromJson? hlJson with
      | .error err =>
        reportError <| "Couldn't deserialize Lean code block while rendering HTML: " ++ err
        pure .empty
      | .ok (hl : Highlighted) =>

        -- Keep completed inner steps even when they end at the same source
        -- position as the enclosing have. They are separate reader steps.
        pure {{<code class="hl lean block" data-lean-context="examples">{{← hl.trim.toHtml (g := Manual)}}</code>}}

/-- Use the reader renderer for checked Lean blocks throughout the document. -/
partial def readerCodeBlocks : Part Manual → Part Manual
  | .mk title titleString metadata intro parts =>
    .mk title titleString metadata (intro.map blocks) (parts.map readerCodeBlocks)
where
  blocks : Block Manual → Block Manual
    | .other kind contents =>
      let kind := if kind.name == ``Verso.Genre.Manual.InlineLean.Block.lean then
        { kind with name := ``Block.readerCode } else kind
      .other kind (contents.map blocks)
    | .concat bs => .concat (bs.map blocks)
    | .blockquote bs => .blockquote (bs.map blocks)
    | .ul items => .ul (items.map fun item => { item with contents := item.contents.map blocks })
    | .ol n items => .ol n (items.map fun item => { item with contents := item.contents.map blocks })
    | .dl items => .dl (items.map fun item => { item with desc := item.desc.map blocks })
    | b => b
