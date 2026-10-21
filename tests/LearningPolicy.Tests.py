"""Check curriculum boundaries and Lean's recursive written-tactic guard."""
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
from learning_policy import exercise_policies

policies = exercise_policies()
assert len(policies) == 103
early = policies['exercise_add_three_preserves_lt']
assert 'apply' in early and 'exact' in early
assert not {'intro', 'arith', 'constructor', 'trivial'} & set(early)
assert 'have' in policies['exercise_two_shifts_lt']
assert 'intro' in policies['exercise_relation_specialization']
assert 'arith' not in policies['exercise_congruent_divisor']
assert 'arith' in policies['exercise_equal_values_equivalence']
assert 'card' not in policies['exercise_powerSet_mono']
assert all('omega' not in allowed for allowed in policies.values())

guard = (ROOT / 'web/lean/LearningGuard.lean').read_text(encoding='utf-8')
cases = '''
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
