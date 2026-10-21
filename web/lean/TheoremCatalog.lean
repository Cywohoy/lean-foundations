import Lean

open Lean Elab Command Meta

namespace BookTheoremCatalog

/-- Export only requested, existing proof declarations from this exact context. -/
elab "#book_theorems " names:str : command => do
  let .ok (.arr requested) := Json.parse names.getString
    | throwError "Expected a JSON array of theorem names"
  let entries ← liftTermElabM do
    let env ← getEnv
    let opts ← getOptions
    let ns ← getCurrNamespace
    let opened ← getOpenDecls
    let mut entries := #[]
    for entry in requested do
      let .str text := entry | continue
      let name := text.toName
      let some info := env.find? name | continue
      unless info.isTheorem || [``True.intro, ``False.elim].contains name do continue
      let mut reference := text
      let parts := text.splitOn "."
      for length in [1:parts.length + 1] do
        let candidate := String.intercalate "." (parts.drop (parts.length - length))
        let resolved := Lean.ResolveName.resolveGlobalName env opts ns opened candidate.toName
        if resolved.length == 1 && resolved.head!.1 == name then
          reference := candidate
          break
      let statement ← ppExpr info.type
      let signature ← PrettyPrinter.ppSignature name
      entries := entries.push <| Json.mkObj [
        ("name", toJson text), ("reference", toJson reference),
        ("statement", toJson statement.pretty),
        ("declaration", toJson signature.fmt.pretty)]
    return entries
  liftIO <| IO.println ("BOOK_THEOREMS:" ++ (Json.arr entries).compress)

end BookTheoremCatalog
