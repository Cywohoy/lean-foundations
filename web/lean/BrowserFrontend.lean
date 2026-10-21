module

prelude
public import Lean.Elab.Frontend
public import Lean.Elab.InfoTree.Util
public import Lean.Widget.InteractiveDiagnostic
public import Lean.Meta.PPGoal

public section

/-!
Synchronous frontend adapter for browser hosts. This module also runs with the
native toolchain so editor behavior can be checked before a WASM rebuild.
Positions use LSP's zero-based UTF-16 coordinates; goals come from Lean's info
trees, using the same position selection as the language server.
-/

open Lean

namespace AmpleBrowser

structure Document where
  fileMap : FileMap
  trees : Array Elab.InfoTree
  messages : MessageLog

def elaborate (code fileName : String) (cachedEnv? : Option Environment := none) : IO Document := do
  let inputCtx := Parser.mkInputContext code fileName
  let (header, parserState, headerMessages) ← Parser.parseHeader inputCtx
  unsafe enableInitializersExecution
  let opts := ({} : Options).setBool `Elab.async false
  let env ← match cachedEnv? with
    | some env => pure env
    | none =>
      importModules (Elab.headerToImports header) opts 0
        (level := if Elab.HeaderSyntax.isModule header then .exported else .private)
        (loadExts := true) (leakEnv := true)
  let commandState := { Elab.Command.mkState env headerMessages opts with
    infoState.enabled := true }
  let initial : Elab.Frontend.State :=
    { commandState, parserState, cmdPos := parserState.pos }
  let collect : Elab.Frontend.FrontendM Document := do
    let mut messages := headerMessages
    let mut trees := #[]
    let mut done := false
    while !done do
      -- Top-level elaboration resets its message log. Capture parser errors
      -- before that reset, just as the standard snapshot frontend does.
      Elab.Frontend.updateCmdPos
      let commandState ← Elab.Frontend.getCommandState
      let parserState ← Elab.Frontend.getParserState
      let scope := commandState.scopes.head!
      let parserContext := {
        env := commandState.env
        options := scope.opts
        currNamespace := scope.currNamespace
        openDecls := scope.openDecls }
      let (command, nextParserState, parserMessages) :=
        Parser.parseCommand inputCtx parserContext parserState {}
      messages := messages ++ parserMessages
      Elab.Frontend.setParserState nextParserState
      Elab.Frontend.setMessages parserMessages
      Elab.Frontend.elabCommandAtFrontend command
      done := Parser.isTerminalCommand command
      let state ← Elab.Frontend.getCommandState
      messages := messages ++ state.messages
      -- Term elaboration (including `have`) can report diagnostics in child
      -- snapshots even when Elab.async is false. The standard frontend flattens
      -- these snapshots; reading only state.messages silently loses errors.
      let nested := Language.SnapshotTree.mk { diagnostics := .empty } state.snapshotTasks
      messages := nested.getAll.foldl (fun log snap => log ++ snap.diagnostics.msgLog) messages
      trees := trees ++ state.infoState.trees.toArray.map
        (·.substitute state.infoState.assignment)
    return { fileMap := inputCtx.fileMap, trees, messages }
  let (document, _) ← StateRefT'.run (ReaderT.run collect {inputCtx}) initial
  return document

def goalsAt (document : Document) (position : Lsp.Position) : IO Json := do
  let offset := document.fileMap.lspPosToUtf8Pos position
  let results := document.trees.toList.flatMap (·.goalsAt? document.fileMap offset)
  let mut goals : Array Json := #[]
  for result in results do
    let info := result.tacticInfo
    let context := { result.ctxInfo with
      mctx := if result.useAfter then info.mctxAfter else info.mctxBefore }
    let ids := if result.useAfter then info.goalsAfter else info.goalsBefore
    let texts ← context.runMetaM {} do
      ids.toArray.mapM fun goal => return Json.str (toString (← Meta.ppGoal goal))
    goals := goals ++ texts
  return Json.mkObj [
    ("found", toJson (!results.isEmpty)),
    ("goals", Json.arr goals)
  ]

def diagnostics (document : Document) : IO Json := do
  let entries ← document.messages.toList.toArray.mapM fun msg => do
    let diagnostic ← Widget.msgToInteractiveDiagnostic document.fileMap msg false
    let text := diagnostic.toDiagnostic.message
    return Json.mkObj [
      ("severity", toJson (match msg.severity with
        | .error => "error" | .warning => "warning" | .information => "information")),
      ("kind", toJson msg.kind.toString),
      ("message", toJson text)
    ]
  return Json.arr entries

end AmpleBrowser
