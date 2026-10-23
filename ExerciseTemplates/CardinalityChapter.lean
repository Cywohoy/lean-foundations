import AlgebraBook.CardinalityChapter

open scoped Ample Classical
open scoped Ample.Auto
open Ample ProofExamples
local infixr:90 (priority := high) " ∘ " => Ample.compose

namespace Exercises.CardinalityChapter

theorem exercise_singletons_same_cardinal {A B : Type}
    (a : A) (b : B) :
    cardinal (Elem (singleton a)) =
      cardinal (Elem (singleton b)) := by
  sorry

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

theorem exercise_fin_succ_not_injective
    (n : Nat) (f : Fin (n + 1) → Fin n) :
    ¬ Injective f := by
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

theorem exercise_finite_cardinal_transport
    {A B : Type} {n : Nat}
    (hAB : cardinal A = cardinal B) :
    cardinal A = n ↔ cardinal B = n := by
  sorry

theorem exercise_fin_injective_bijective (n : Nat)
    (f : Fin n → Fin n)
    (hf : Injective f) :
    Bijective f := by
  sorry

theorem exercise_successor_injective :
    Injective (fun k : Nat => k + 1) := by
  sorry

theorem exercise_successor_not_surjective :
    ¬ Surjective (fun k : Nat => k + 1) := by
  sorry

theorem exercise_cardinal_product {A B : Type} {m n : Nat}
    (hA : cardinal A = m)
    (hB : cardinal B = n) :
    cardinal (A × B) = ((m * n : Nat) : Cardinal) := by
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

def practiceTwoValues {A : Type} (p : A × A) : Fin 2 → A :=
  fun i => if i.val = 0 then p.1 else p.2

theorem exercise_twoValues_bijective (A : Type) :
    Bijective (practiceTwoValues (A := A)) := by
  sorry

theorem exercise_two_to_three_functions :
    cardinal (Fin 2 → Fin 3) = 9 := by
  sorry

theorem exercise_cardinal_sum_two_three {A B : Type}
    (hA : cardinal A = 2)
    (hB : cardinal B = 3) :
    cardinal (A ⊕ B) = 5 := by
  sorry

theorem exercise_cardinal_product_sum {A B C : Type}
    (hA : cardinal A = 2)
    (hB : cardinal B = 3)
    (hC : cardinal C = 4) :
    cardinal (A × (B ⊕ C)) = 14 := by
  sorry

def practiceSplitFunction {A B C : Type}
    (f : A ⊕ B → C) : (A → C) × (B → C) :=
  (fun a => f (.inl a), fun b => f (.inr b))
def practiceJoinFunction {A B C : Type}
    (p : (A → C) × (B → C)) : A ⊕ B → C
  | .inl a => p.1 a
  | .inr b => p.2 b

theorem exercise_splitFunction_bijective (A B C : Type) :
    Bijective (practiceSplitFunction (A := A) (B := B)
      (C := C)) := by
  sorry

theorem exercise_cardinal_power_sum (A B C : Type) :
    cardinal C ^ (cardinal A + cardinal B) =
      cardinal C ^ cardinal A *
        cardinal C ^ cardinal B := by
  sorry

theorem exercise_three_boxes_sum :
    cardinal (Fin 1 ⊕ (Fin 2 ⊕ Fin 3)) =
      ∑ i < 3, ((i + 1 : Nat) : Cardinal) := by
  sorry

theorem exercise_three_boxes_product :
    cardinal (Fin 1 × (Fin 2 × Fin 3)) =
      ∏ i < 3, ((i + 1 : Nat) : Cardinal) := by
  sorry

theorem exercise_infinite_finite_ne_cardinal {A B : Type}
    (hA : IsInfinite A)
    (hB : IsFinite B) :
    cardinal A ≠ cardinal B := by
  sorry

theorem exercise_nat_pairs_infinite :
    IsInfinite (Nat × Nat) := by
  sorry

def practiceImageMap {A B : Type} (f : A → B) (S : Set A) :
    Elem S → Elem (image f S) :=
  fun x =>
    { val := f x.val
      property := by
        exists x.val
        constructor
        · exact x.property
        · rfl }

theorem exercise_imageMap_bijective
    {A B : Type} (f : A → B) (S : Set A)
    (hf : Injective f) :
    Bijective (practiceImageMap f S) := by
  sorry

theorem exercise_injective_image_cardinal
    {A B : Type} (f : A → B) (S : Set A)
    (hf : Injective f) :
    cardinal (Elem (image f S)) = cardinal (Elem S) := by
  sorry

theorem exercise_positive_doubles_countable :
    IsCountablyInfinite
      (Elem (image double positives)) := by
  sorry

theorem exercise_from_two_countably_infinite :
    IsCountablyInfinite
    (Elem (fun n : Nat => 2 ≤ n)) := by
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

theorem exercise_powerSet_inter {A : Type} (S T : Set A) :
    powerSet (S ∩ T) = powerSet S ∩ powerSet T := by
  sorry

theorem exercise_three_boolean_choices :
    cardinal (Fin 3 → Bool) = 8 := by
  sorry

theorem exercise_three_powerSet :
    cardinal (Set (Fin 3)) = 8 := by
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

theorem exercise_powerSet_nat_infinite :
    IsInfinite (Set Nat) := by
  sorry

theorem exercise_powerSet_nat_not_countable :
    ¬ IsCountablyInfinite (Set Nat) := by
  sorry

end Exercises.CardinalityChapter
