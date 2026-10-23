"""Check curriculum boundaries and Lean's recursive written-tactic guard."""
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
from learning_policy import exercise_policies

policies = exercise_policies()
assert len(policies) == 154
assert policies['exercise_relation_specialization_apply'] == policies['exercise_relation_specialization']
assert policies['exercise_inter_union_absorb'] == policies['exercise_inter_union_absorb_via_subset']
assert 'arith' not in policies['exercise_congruent_add_left']
early = policies['exercise_add_three_preserves_lt']
assert 'apply' in early and 'exact' in early
assert not {'intro', 'arith', 'constructor', 'trivial'} & set(early)
assert 'have' in policies['exercise_two_shifts_lt']
assert 'and_intros' not in policies['exercise_implication_chain']
assert 'and_intros' in policies['exercise_logic_iff_trans']
assert 'and_intros' in policies['exercise_equal_values_equivalence']
assert 'replace' not in early
assert 'replace' in policies['exercise_implication_chain']
assert 'set' not in policies['exercise_preimage_subset']
assert 'set' in policies['exercise_diff_antitone_right']
assert 'set' in policies['exercise_equal_values_equivalence']
assert 'let' not in policies['exercise_equal_values_equivalence']
assert 'let' in policies['exercise_powerSet_mono']
assert 'set' in policies['exercise_powerSet_mono']
assert 'symm' not in policies['exercise_two_shifts_lt']
assert 'symm' in policies['exercise_parityClass_three_one']
assert 'intro' in policies['exercise_relation_specialization']
assert 'by_contra' in policies['exercise_implication_cases']
assert 'rcases' not in policies['exercise_implication_cases']
assert 'rw' not in policies['exercise_forall_implication']
assert 'by_contra' in policies['exercise_exists_forall_swap']
assert 'rw' not in policies['exercise_no_largest_nat']
assert 'rw' in policies['exercise_predicate_conjunction_comm']
assert 'arith' not in policies['exercise_congruent_divisor']
assert 'arith' in policies['exercise_equal_values_equivalence']
assert 'card' not in policies['exercise_powerSet_mono']
assert all('omega' not in allowed for allowed in policies.values())
assert 'apply_fun' not in policies['exercise_forall_implication']
assert 'apply_fun' in policies['exercise_predicate_conjunction_comm']
assert 'apply_fun' in policies['exercise_oneModThree_bijective']
assert all(not {'indisc', 'indisc!'} & set(allowed) for allowed in policies.values())
assert 'unpack' not in policies['exercise_double_successor_noncommute']
assert 'unpack' in policies['exercise_injective_of_compose']
assert 'unpack' in policies['exercise_surjective_of_compose']
assert all('congr' not in allowed for allowed in policies.values())

guard = 'import Ample.Tactic.Auto\n' + (ROOT / 'web/lean/LearningGuard.lean').read_text(encoding='utf-8')
cases = '''
open scoped Ample
example (P : Prop) (h : P) : P := by learning_guard "set,exact" in
  set Q := P
  exact h
example (P Q : Prop) (h : P) (f : P → Q) : Q := by learning_guard "replace,exact" in
  replace h : Q := f h
  exact h

example : True := by learning_guard "exact" in
  -- trivial here is only a comment
  exact True.intro
example : True := by learning_guard "have,exact" in
  have trivial : True := by exact True.intro
  exact trivial
example : True := by learning_guard "constructor" in
  constructor
example : True := by learning_guard "first,exact" in
  first | exact True.intro | exact True.intro
example : True := by learning_guard "exact" in
  trivial
example : True := by learning_guard "have,exact" in
  have h : True := by
    trivial
  exact h
example : True := by learning_guard "exact" in
  exact (by trivial)
example : True := by learning_guard "first,exact" in
  first | exact True.intro | trivial
example : 1 = 1 := by learning_guard "exact" in
  exact (by omega)
example : True := by learning_guard "exact" in
  nonsense
'''
target = ROOT / 'tmp/learning-policy-tests.lean'
target.parent.mkdir(exist_ok=True)
target.write_text(guard + cases, encoding='utf-8')
result = subprocess.run(['lake', 'env', 'lean', str(target)], cwd=ROOT,
                        capture_output=True, text=True, encoding='utf-8')
assert result.returncode == 1, result.stdout + result.stderr
assert result.stdout.count("Tactic 'trivial' has not been introduced") == 4, result.stdout
assert result.stdout.count("Tactic 'omega' has not been introduced") == 1, result.stdout
assert result.stdout.count('error: unsolved goals') == 6, result.stdout
assert result.stdout.count('error: unknown tactic') == 1, result.stdout
assert "Tactic 'nonsense' has not been introduced" not in result.stdout
assert result.stdout.count('error:') == 12, result.stdout
print('PASS: curriculum boundaries, nested proofs, combinators, comments, and tactic identifiers')
