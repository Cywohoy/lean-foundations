import AlgebraBook.Proof

open scoped Ample Classical
open IntroExamples ProofExamples

namespace Exercises.Proof

theorem exercise_four_square : 4 * 4 = 16 := by
  sorry

theorem exercise_add_three_preserves_lt (a b : Nat)
    (h : a < b) :
    a + 3 < b + 3 := by
  sorry

theorem exercise_shift_lt (a b c : Nat)
    (hab : a < b) :
    a + c < b + c := by
  sorry

theorem exercise_two_shifts_lt (a b c d : Nat)
    (hab : a < b) :
    (a + c) + d < (b + c) + d := by
  sorry

theorem exercise_implication_chain
    (P Q R : Prop) :
    P → (P → Q) → (Q → R) → R := by
  sorry

theorem exercise_logic_iff_trans (P Q R : Prop)
    (hPQ : P ↔ Q)
    (hQR : Q ↔ R) :
    P ↔ R := by
  sorry

theorem exercise_logic_and_or_distrib (P Q R : Prop) :
    (P ∧ (Q ∨ R)) ↔ ((P ∧ Q) ∨ (P ∧ R)) := by
  sorry

theorem exercise_implication_cases (P Q : Prop) :
    (P → Q) ↔ (¬ P ∨ Q) := by
  sorry

theorem exercise_four_solves_square :
    solvesSquare 16 4 := by
  sorry

theorem exercise_square_proof (a n : Nat)
    (h : solvesSquare a n) :
    n * n = a := by
  sorry

theorem exercise_relation_specialization_apply
    (A : Type) (R : A → A → Prop) (a b : A) :
    (∀ x : A, ∀ y : A, R x y) → R a b := by
  sorry

theorem exercise_relation_specialization
    (A : Type) (R : A → A → Prop) (a b : A) :
    (∀ x : A, ∀ y : A, R x y) → R a b := by
  sorry

theorem exercise_exists_forall_swap (A B : Type)
    (R : A → B → Prop)
    (h : ∃ x : A, ∀ y : B, R x y) :
    ∀ y : B, ∃ x : A, R x y := by
  sorry

theorem exercise_forall_implication
    (A : Type) (P Q : A → Prop) :
    (∀ x : A, P x → Q x) →
    (∀ x : A, P x) → ∀ x : A, Q x := by
  sorry

theorem exercise_increasing_composition (f g : Nat → Nat)
    (hf : ∀ a b, a < b → f a < f b)
    (hg : ∀ a b, a < b → g a < g b) :
    ∀ a b, a < b → g (f a) < g (f b) := by
  sorry

theorem exercise_increasing_at_three_five
    (f g : Nat → Nat)
    (hf : ∀ a b, a < b → f a < f b)
    (hg : ∀ a b, a < b → g a < g b) :
    g (f 3) < g (f 5) := by
  sorry

theorem exercise_function_bound (f g : Nat → Nat)
    (hfg : ∀ n, f n < g n)
    (hg : ∀ n, g n < n + 10) :
    f 3 < 13 := by
  sorry

theorem exercise_property_twice (A : Type)
    (P : A → Prop) (f : A → A)
    (hf : ∀ x, P x → P (f x)) :
    ∀ x, P x → P (f (f x)) := by
  sorry

theorem exercise_property_four_times (A : Type)
    (P : A → Prop) (f : A → A)
    (hf : ∀ x, P x → P (f x)) :
    ∀ x, P x → P (f (f (f (f x)))) := by
  sorry

theorem exercise_relation_iterate {A : Type}
    (f : A → A) (R : A → A → Prop)
    (h : ∀ x y, R x y → R y (f x))
    (a b : A)
    (hab : R a b) :
    R (f a) (f b) := by
  sorry

theorem exercise_relation_iterate_twice {A : Type}
    (f : A → A) (R : A → A → Prop)
    (h : ∀ x y, R x y → R y (f x))
    (a b : A)
    (hab : R a b) :
    R (f (f a)) (f (f b)) := by
  sorry

theorem exercise_no_largest_nat :
    ¬ ∃ m : Nat, ∀ n : Nat, n < m := by
  sorry

theorem exercise_predicate_conjunction_comm (A : Type)
    (P Q : A → Prop) :
    (fun x => P x ∧ Q x) = (fun x => Q x ∧ P x) := by
  sorry

end Exercises.Proof
