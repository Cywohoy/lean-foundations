import AlgebraBook.NumbersRelations

open scoped Ample Classical
open scoped Ample.Auto
open Ample ProofExamples
local infixr:90 (priority := high) " ∘ " => Ample.compose
local infix:50 (priority := high) " ∣ " => Ample.Divides
local notation:50 a " ≡ " b " [MOD " n "]" => Ample.Congruent n a b

namespace Exercises.NumbersRelations

theorem exercise_one_add_induction
    (n : Nat) :
    1 + n = n + 1 := by
  sorry

theorem exercise_even_add (a b : Nat)
    (ha : IsEvenNat a)
    (hb : IsEvenNat b) :
    IsEvenNat (a + b) := by
  sorry

theorem exercise_even_add_double (a : Nat)
    (ha : IsEvenNat a) :
    IsEvenNat (a + double 7) := by
  sorry

theorem exercise_even_mul (a b : Nat)
    (ha : IsEvenNat a) :
    IsEvenNat (a * b) := by
  sorry

theorem exercise_double_mul_even (b : Nat) :
    IsEvenNat (double 3 * b) := by
  sorry

theorem exercise_divides_zero (a : Int) : a ∣ 0 := by
  sorry

theorem exercise_divisibility_sign :
    (3 ∣ -3) ∧ ((-3) ∣ 3) := by
  sorry

theorem exercise_three_ne_negative_three :
    (3 : Int) ≠ -3 := by
  sorry

theorem exercise_congruent_zero_iff (a b : Int) :
    a ≡ b [MOD 0] ↔ a = b := by
  sorry

theorem exercise_congruent_one (a b : Int) :
    a ≡ b [MOD 1] := by
  sorry

theorem exercise_congruent_add_left
    (n a b t : Int)
    (h : a ≡ b [MOD n]) :
    t + a ≡ t + b [MOD n] := by
  sorry

theorem exercise_congruent_thirty_seven_two :
    37 ≡ 2 [MOD 7] := by
  sorry

theorem exercise_congruent_thirty_seven_twenty_three :
    37 ≡ 23 [MOD 7] := by
  sorry

theorem exercise_congruent_divisor (n d a b : Int)
    (h : a ≡ b [MOD n * d]) :
    a ≡ b [MOD n] := by
  sorry

theorem exercise_twenty_mod_six : 20 ≡ 2 [MOD 6] := by
  sorry

theorem exercise_twenty_mod_three : 20 ≡ 2 [MOD 3] := by
  sorry

theorem exercise_congruent_six_iff_two_three (a b : Int) :
    a ≡ b [MOD 6] ↔ a ≡ b [MOD 2] ∧ a ≡ b [MOD 3] := by
  sorry

theorem exercise_sum_odds (n : Nat) :
    (∑ i < n, 2 * i + 1) = n * n := by
  sorry

theorem exercise_sum_ten_odds :
    (∑ i < 10, 2 * i + 1) = 100 := by
  sorry

theorem exercise_equal_values_equivalence {A B : Type}
    (f : A → B) :
    IsEquivalence (fun x y : A => f x = f y) := by
  sorry

theorem exercise_in_own_equivalenceClass {A : Type}
    (R : Relation A)
    (hR : IsEquivalence R)
    (a : A) :
    a ∈ equivalenceClass R a := by
  sorry

theorem exercise_relation_of_classes_equal {A : Type}
    (R : Relation A)
    (hR : IsEquivalence R)
    (a b : A)
    (h : equivalenceClass R a = equivalenceClass R b) :
    R a b := by
  sorry

def practiceOverlappingBlocks : Set (Set Nat) :=
  fun S => S = (fun x => x = 0 ∨ x = 1) ∨
    S = (fun x => 1 ≤ x)

theorem exercise_overlapping_not_partition :
    ¬ IsPartition practiceOverlappingBlocks := by
  sorry

theorem exercise_parityClass_three_one :
    parityClass 3 = parityClass 1 := by
  sorry

theorem exercise_parityClass_three_ne_zero :
    parityClass 3 ≠ parityClass 0 := by
  sorry

def practiceSameFirst : Relation (Int × Int) :=
  fun p q => p.1 = q.1
theorem exercise_sameFirst_equivalence :
    IsEquivalence practiceSameFirst := by
  sorry

theorem exercise_sameFirst_class (a b : Int) :
    equivalenceClass practiceSameFirst (a, b) =
      (fun p => p.1 = a) := by
  sorry

theorem exercise_vertical_class :
    equivalenceClass practiceSameFirst (2, 3) =
      equivalenceClass practiceSameFirst (2, -5) := by
  sorry

theorem exercise_classes_of_common_element {A : Type}
    (R : Relation A)
    (hR : IsEquivalence R)
    (a b : A)
    (h : ∃ x, x ∈ equivalenceClass R a ∧
      x ∈ equivalenceClass R b) :
    equivalenceClass R a = equivalenceClass R b := by
  sorry

theorem exercise_mod_six_common :
    2 ∈ equivalenceClass (Congruent 6) 8 ∧
      2 ∈ equivalenceClass (Congruent 6) 20 := by
  sorry

theorem exercise_mod_six_classes :
    equivalenceClass (Congruent 6) 8 =
      equivalenceClass (Congruent 6) 20 := by
  sorry

theorem exercise_parity_no_mod_three :
    ¬ ∃ F : Parity → Int,
      ∀ a, F (parityClass a) = a % 3 := by
  sorry

theorem exercise_nextParity_respects (a b : Int)
    (hab : Congruent 2 a b) :
    parityClass (a + 1) = parityClass (b + 1) := by
  sorry

noncomputable def practiceNextParity : Parity → Parity :=
  quotientLift
    (Congruent 2)
    (congruent_equivalence 2)
    (fun a => parityClass (a + 1))
    exercise_nextParity_respects
theorem exercise_nextParity_class (a : Int) :
    practiceNextParity (parityClass a) =
      parityClass (a + 1) := by
  sorry

theorem exercise_nextParity_twice (q : Parity) :
    practiceNextParity (practiceNextParity q) = q := by
  sorry

def practiceBalanced : Relation (Nat × Nat) :=
  fun p q => p.1 + q.2 = q.1 + p.2

theorem exercise_balanced_equivalence :
    IsEquivalence practiceBalanced := by
  sorry

theorem exercise_balanced_difference (p q : Nat × Nat)
    (h : practiceBalanced p q) :
    (p.1 : Int) - p.2 = (q.1 : Int) - q.2 := by
  sorry

noncomputable def practiceDifference :
    (Nat × Nat) / practiceBalanced → Int :=
  quotientLift
    practiceBalanced
    exercise_balanced_equivalence
    (fun p => (p.1 : Int) - p.2)
    exercise_balanced_difference

theorem exercise_difference_class (a b : Nat) :
    practiceDifference ⟦(a, b)⟧ = (a : Int) - b := by
  sorry

theorem exercise_difference_same_class :
    (⟦(2, 5)⟧ : (Nat × Nat) / practiceBalanced) =
      ⟦(4, 7)⟧ := by
  sorry

theorem exercise_difference_concrete :
    practiceDifference ⟦(4, 7)⟧ = -3 := by
  sorry

theorem exercise_parity_double_zero (a : Int) :
    parityClass (2 * a) = parityClass 0 := by
  sorry

theorem exercise_parity_double_respects (a b : Int)
    (_h : a ≡ b [MOD 2]) :
    parityClass (2 * a) = parityClass (2 * b) := by
  sorry

noncomputable def practiceParityDouble : Parity → Parity :=
  quotientLift
    (Congruent 2)
    (congruent_equivalence 2)
    (fun a => parityClass (2 * a))
    exercise_parity_double_respects

theorem exercise_parity_double_constant (q : Parity) :
    practiceParityDouble q = parityClass 0 := by
  sorry

end Exercises.NumbersRelations
