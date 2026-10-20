import AlgebraBook.SetsFunctions

open scoped Ample Classical
open scoped Ample.Auto
open Ample
local infixr:90 (priority := high) " ∘ " => Ample.compose

namespace Exercises.SetsFunctions

theorem exercise_subset_chain {A : Type} (S T U V : Set A)
    (hST : S ⊆ T)
    (hTU : T ⊆ U)
    (hUV : U ⊆ V) :
    S ⊆ V := by
  sorry

theorem exercise_inter_subset_right
    {A : Type} (S T : Set A) :
    S ∩ T ⊆ T := by
  sorry

theorem exercise_diff_self_subset_empty
    {A : Type} (S : Set A) :
    S \ S ⊆ ∅ := by
  sorry

theorem exercise_diff_antitone_right
    {A : Type} (S T U : Set A)
    (hTU : T ⊆ U) :
    S \ U ⊆ S \ T := by
  sorry

theorem exercise_union_eq_right {A : Type} (S T : Set A)
    (hST : S ⊆ T) :
    S ∪ T = T := by
  sorry

theorem exercise_twoThree_union_positives :
    twoThree ∪ positives = positives := by
  sorry

theorem exercise_inter_union_absorb {A : Type}
    (S T : Set A) :
    S ∩ (S ∪ T) = S := by
  sorry

def practiceThreeFour : Set Nat :=
  fun n => n = 3 ∨ n = 4
theorem exercise_twoThree_inter :
    twoThree ∩ practiceThreeFour = (fun n => n = 3) := by
  sorry

theorem exercise_twoThree_diff :
    twoThree \ practiceThreeFour = (fun n => n = 2) := by
  sorry

theorem exercise_positives_not_subset_twoThree :
    ¬ positives ⊆ twoThree := by
  sorry

theorem exercise_positives_ne_twoThree :
    positives ≠ twoThree := by
  sorry

theorem exercise_compl_union {A : Type} (S T : Set A) :
    (S ∪ T)ᶜ = Sᶜ ∩ Tᶜ := by
  sorry

theorem exercise_diff_empty_iff {A : Type}
    (S T : Set A) :
    S \ T = ∅ ↔ S ⊆ T := by
  sorry

theorem exercise_preimage_subset {A B : Type}
    (f : A → B) (S T : Set B)
    (hST : S ⊆ T) :
    preimage f S ⊆ preimage f T := by
  sorry

def practiceFourSix : Set Nat := fun n => n = 4 ∨ n = 6
theorem exercise_image_double_twoThree :
    image double twoThree = practiceFourSix := by
  sorry

theorem exercise_preimage_double_fourSix :
    preimage double practiceFourSix = twoThree := by
  sorry

theorem exercise_double_after_successor_at_three :
    (double ∘ (fun n : Nat => n + 1)) 3 = 8 := by
  sorry

theorem exercise_successor_after_double_at_three :
    ((fun n : Nat => n + 1) ∘ double) 3 = 7 := by
  sorry

theorem exercise_double_successor_noncommute :
    double ∘ (fun n : Nat => n + 1) ≠
    (fun n : Nat => n + 1) ∘ double := by
  sorry

theorem exercise_setProduct_swap {A B : Type}
    (S : Set A) (T : Set B) (a : A) (b : B)
    (h : (a, b) ∈ setProduct S T) :
    (b, a) ∈ setProduct T S := by
  sorry

theorem exercise_injective_of_compose {A B C : Type}
    (f : A → B) (g : B → C)
    (h : Injective (g ∘ f)) :
    Injective f := by
  sorry

theorem exercise_surjective_of_compose {A B C : Type}
    (f : A → B) (g : B → C)
    (h : Surjective (g ∘ f)) :
    Surjective g := by
  sorry

theorem exercise_inverse_inverse {A B : Type}
    (f : A → B)
    (hf : Bijective f) :
    inverseMap (inverseMap f hf)
      (inverseMap_bijective f hf) = f := by
  sorry

def practiceFirst : Nat × Nat → Nat := fun p => p.1
theorem exercise_first_surjective :
    Surjective practiceFirst := by
  sorry

theorem exercise_first_not_injective :
    ¬ Injective practiceFirst := by
  sorry

def practiceDiagonal : Nat → Nat × Nat := fun n => (n, n)
theorem exercise_diagonal_injective :
    Injective practiceDiagonal := by
  sorry

theorem exercise_diagonal_not_surjective :
    ¬ Surjective practiceDiagonal := by
  sorry

theorem exercise_preimage_inter {A B : Type} (f : A → B)
    (S T : Set B) :
    preimage f (S ∩ T) = preimage f S ∩ preimage f T := by
  sorry

theorem exercise_preimage_compl {A B : Type}
    (f : A → B) (T : Set B) :
    preimage f Tᶜ = (preimage f T)ᶜ := by
  sorry

theorem exercise_image_union {A B : Type}
    (f : A → B) (S T : Set A) :
    image f (S ∪ T) = image f S ∪ image f T := by
  sorry

theorem exercise_cancel_injective {A B C : Type}
    (f g : A → B)
    (h : B → C)
    (hh : Injective h)
    (heq : h ∘ f = h ∘ g) :
    f = g := by
  sorry

theorem exercise_cancel_surjective {A B C : Type}
    (f g : B → C)
    (h : A → B)
    (hh : Surjective h)
    (heq : f ∘ h = g ∘ h) :
    f = g := by
  sorry

end Exercises.SetsFunctions
