import Lean

open Lean Elab Tactic

namespace AmpleBrowserContext

private partial def firstToken : Syntax → String
  | .atom _ value => value.trimAscii.toString
  | .ident _ raw _ _ => raw.toString
  | .node _ _ args =>
      (args.toList.map firstToken).find? (· != "") |>.getD ""
  | .missing => ""

private partial def checkTactics (allowed : List String) (stx : Syntax) : TacticM Unit := do
  -- Lean already reports parser recovery nodes as unknown tactics.
  if stx.isOfKind ``Parser.Tactic.unknown then return
  let some category := Parser.getParserCategory? (← getEnv) `tactic
    | throwError "The tactic parser category is unavailable."
  if category.kinds.contains stx.getKind then
    let token := firstToken stx
    if !allowed.contains token && !["·", "(", "{", ";", "<;>", "sorry"].contains token then
      throwErrorAt stx "Tactic '{token}' has not been introduced at this exercise."
  for child in stx.getArgs do
    checkTactics allowed child

/-- Check the written tactic syntax before elaboration. Nested proof blocks and
combinators are inspected too; tactics generated internally by approved tactics
are deliberately not restricted. This is a learning aid, not a security sandbox. -/
syntax (name := learningGuard) "learning_guard " str " in " tacticSeq : tactic

elab_rules : tactic
  | `(tactic| learning_guard $policy:str in $body:tacticSeq) => do
      -- Ordinary tactic try/catch restores its saved state, including messages.
      -- An abortTactic exception means the original error was already logged;
      -- backtracking here would erase that error and logException cannot recreate it.
      Tactic.tryCatch (do
        checkTactics (policy.getString.splitOn ",") body
        if (body.raw.find? (·.isOfKind ``Parser.Tactic.unknown)).isSome then return
        evalTactic body) fun error => do
        if error.isInterrupt then throw error
        -- Keep the current goals available after a rejected or malformed step.
        logException error

end AmpleBrowserContext
