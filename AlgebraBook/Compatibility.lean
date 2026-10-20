import Lean

/-! 기존 개인 풀이의 `Course` 이름은 교재에서만 지원한다. -/

open Lean Elab Command

namespace AlgebraBook.Compatibility

private partial def renameLegacyOpen (stx : Syntax) : Syntax :=
  match stx with
  | .ident _ _ name _ =>
      if (`Course).isPrefixOf name then
        mkIdentFrom stx (name.replacePrefix `Course `Ample)
      else stx
  | .node info kind args => .node info kind (args.map renameLegacyOpen)
  | _ => stx

-- Keep old exercise files unchanged. Only an explicit legacy namespace in an
-- open command is redirected; declarations are still defined under Ample.
@[command_elab Lean.Parser.Command.open]
def elabLegacyOpen : CommandElab := fun stx => do
  let renamed := renameLegacyOpen stx
  if renamed == stx then throwUnsupportedSyntax
  elabCommand renamed

-- Lean's ordinary export mechanism creates name-resolution aliases, not new
-- mathematical declarations. Invoke this after a chapter's definitions.
elab "export_course_compat" : command => do
  let env ← getEnv
  let mut updated := env.registerNamespace `Course
  for (name, _) in env.constants.toList do
    unless (`Ample).isPrefixOf name do continue
    let alias := name.replacePrefix `Ample `Course
    if (getAliases env alias false).contains name then continue
    updated := (addAlias updated alias name).registerNamespace alias.getPrefix
  setEnv updated

end AlgebraBook.Compatibility

export_course_compat
