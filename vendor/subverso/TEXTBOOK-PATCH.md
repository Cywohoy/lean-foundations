# Textbook highlighting patch

Upstream: https://github.com/leanprover/subverso
Revision: `892d6dc520270b5fb8c1291dd1b131e8c16255ed`

This copy preserves the upstream license and source files. The change in
`src/SubVerso/Highlighting/Code.lean` keeps nested `by` terms traversable and
reads their initial proof state from Lean's `by` annotation. Tactic lookup
also accepts the same canonical source range and syntax kind when macro
expansion has changed hygiene information. This exposes the
actual subproof goals and tactic states in optimized `have` and `let` proofs.
It does not change elaboration, proof terms, or axioms.

The textbook's `tests/PagesReader.Tests.cjs` checks the rendered transition
into a subproof, its internal steps, and the return to the enclosing proof.
When upgrading SubVerso, compare this file with the upstream revision and
remove the override once upstream provides the same behavior.
