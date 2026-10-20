import AlgebraBook.Meta.Lean

open Verso Doc
open Verso.Genre Manual
open Lean

namespace AlgebraBook

structure PlaygroundBuildState where
  contexts : Std.HashMap String String := {}
  snippets : Array (String × Json) := #[]

/-- Export each example with exactly its preceding, retained document context. -/
partial def buildPlaygrounds (mode : Mode) (cfg : Config)
    (_state : TraverseState) (text : Part Manual) : BuildLogT IO Unit := do
  let .multi := mode | pure ()
  let (_, st) ← (part text).run {}
  let snippetsDir := cfg.destination / "html-multi" / "playground"
  IO.FS.createDirAll snippetsDir
  for (key, snippet) in st.snippets do
    IO.FS.writeFile (snippetsDir / (key ++ ".json")) snippet.compress
  let target := cfg.destination / "html-multi" / "playground.json"
  IO.FS.writeFile target (Json.mkObj st.snippets.toList).compress
where
  part : Part Manual → StateT PlaygroundBuildState (BuildLogT IO) Unit
    | .mk _ _ _ intro subParts => do
      for b in intro do block b
      for p in subParts do part p
  block : Block Manual → StateT PlaygroundBuildState (BuildLogT IO) Unit
    | .other which contents => do
      if which.name == ``Block.playground then
        let .arr #[.str file, .str code, .str key, .bool keep, .bool visible, .bool exercise] := which.data
          | reportError "Invalid playground export data"
        let before := (← get).contexts[file]?.getD ""
        if visible then
          modify fun st => { st with snippets := st.snippets.push (key, json%{
            "code": $code, "before": $before,
            "exercise": $exercise
          }) }
        if keep then
          modify fun st => { st with contexts := st.contexts.insert file (before ++ code ++ "\n") }
        -- The wrapper owns its source; do not count its savedLean child twice.
        return
      if which.name == ``Block.savedImport then
        let .arr #[.str file, .str code] := which.data
          | reportError "Invalid playground import data"
        modify fun st =>
          let prior := st.contexts[file]?.getD ""
          { st with contexts := st.contexts.insert file (code ++ "\n" ++ prior) }
      for b in contents do block b
    | .concat bs | .blockquote bs => for b in bs do block b
    | .ol _ lis | .ul lis => for li in lis do for b in li.contents do block b
    | .dl dis => for di in dis do for b in di.desc do block b
    | .para .. | .code .. => pure ()

end AlgebraBook
