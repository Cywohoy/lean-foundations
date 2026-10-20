import AlgebraBook.CardinalityChapter

open scoped Ample Classical
open scoped Ample.Auto
open Ample
local infixr:90 (priority := high) " ∘ " => Ample.compose

namespace Exercises.CardinalityChapter

def practiceIndexTwo (i : Fin 2) : Elem twoThree :=
  { val := i.val + 2
    property := by
      expand
      arith }

theorem exercise_indexTwo_bijective :
    Bijective practiceIndexTwo := by
  sorry

theorem exercise_twoThree_cardinal :
    cardinal (Elem twoThree) = cardinal (Fin 2) := by
  sorry

theorem exercise_singletons_same_cardinal {A B : Type}
    (a : A) (b : B) :
    cardinal (Elem (singleton a)) =
      cardinal (Elem (singleton b)) := by
  sorry

theorem exercise_finite_cardinal_transport
    {A B : Type} {n : Nat}
    (hAB : cardinal A = cardinal B) :
    cardinal A = n ↔ cardinal B = n := by
  sorry

theorem exercise_fin_succ_not_injective
    (n : Nat) (f : Fin (n + 1) → Fin n) :
    ¬ Injective f := by
  sorry

theorem exercise_cardinal_product {A B : Type} {m n : Nat}
    (hA : cardinal A = m)
    (hB : cardinal B = n) :
    cardinal (A × B) = m * n := by
  sorry

theorem exercise_cardinal_swap (A B : Type) :
    cardinal (A × B) = cardinal (B × A) := by
  sorry

theorem exercise_two_by_three_cardinal :
    cardinal (Fin 2 × Fin 3) = 6 := by
  sorry

theorem exercise_three_by_two_cardinal :
    cardinal (Fin 3 × Fin 2) = 6 := by
  sorry

theorem exercise_fin_collision (n : Nat)
    (f : Fin (n + 1) → Fin n) :
    ∃ i j, i ≠ j ∧ f i = f j := by
  sorry

theorem exercise_birth_month_collision
    (month : Fin 13 → Fin 12) :
    ∃ i j, i ≠ j ∧ month i = month j := by
  sorry

theorem exercise_fin_two_three_not_same :
    ¬ SameCardinality (Fin 2) (Fin 3) := by
  sorry

theorem exercise_threeNumbers_not_four :
    cardinal (Elem threeNumbers) ≠ 4 := by
  sorry

theorem exercise_infinite_transport {A B : Type}
    (hA : IsInfinite A)
    (hAB : cardinal A = cardinal B) :
    IsInfinite B := by
  sorry

theorem exercise_from_two_countably_infinite {n : Nat} :
    IsCountablyInfinite
    (Elem (fun n : Nat => 2 ≤ n)) := by
  sorry

theorem exercise_powerSet_inter {A : Type} (S T : Set A) :
    powerSet (S ∩ T) = powerSet S ∩ powerSet T := by
  sorry

def practiceOneModThree : Set Nat :=
  fun n => ∃ k, n = 3 * k + 1
def practiceToOneModThree (n : Nat) :
    Elem practiceOneModThree :=
  { val := 3 * n + 1
    property := by exists n }

theorem exercise_oneModThree_bijective :
    Bijective practiceToOneModThree := by
  sorry

theorem exercise_oneModThree_countable :
    IsCountablyInfinite (Elem practiceOneModThree) := by
  sorry

theorem exercise_oneModThree_ne_whole :
    practiceOneModThree ≠ whole Nat := by
  sorry

theorem exercise_nat_pairs_infinite :
    IsInfinite (Nat × Nat) := by
  sorry

theorem exercise_powerSet_mono {A : Type} (S T : Set A)
    (hST : S ⊆ T) :
    powerSet S ⊆ powerSet T := by
  sorry

theorem exercise_powerSet_subset_iff {A : Type}
    (S T : Set A) :
    powerSet S ⊆ powerSet T ↔ S ⊆ T := by
  sorry

theorem exercise_powerSet_twoThree_positives :
    powerSet twoThree ⊆ powerSet positives := by
  sorry

def practiceSingletonDiagonal : Set Nat :=
  fun n => n ∉ singleton n
theorem exercise_singleton_diagonal_empty :
    practiceSingletonDiagonal = ∅ := by
  sorry

theorem exercise_empty_not_singleton_image :
    (∅ : Set Nat) ∉ image singleton (whole Nat) := by
  sorry

theorem exercise_singleton_not_surjective :
    ¬ Surjective (singleton : Nat → Set Nat) := by
  sorry

end Exercises.CardinalityChapter
