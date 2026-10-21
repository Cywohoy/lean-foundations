import AlgebraBook.Proof

open scoped Ample Classical
open IntroExamples ProofExamples

namespace Exercises.Proof

theorem exercise_four_square : 4 * 4 = 16 := by
  sorry

theorem exercise_four_solves_square :
    solvesSquare 16 4 := by
  sorry

theorem exercise_square_proof (a n : Nat)
    (h : solvesSquare a n) :
    n * n = a := by
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

theorem exercise_relation_specialization
    (A : Type) (R : A → A → Prop) (a b : A) :
    (∀ x : A, ∀ y : A, R x y) → R a b := by
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

end Exercises.Proof
