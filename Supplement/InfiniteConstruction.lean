import AlgebraBook.CardinalityChapter

/-!
이 파일은 본문에서 제외한 선택 과정의 구현을 보존한다.
아래 `InfiniteConstruction` 절은 유한 단사 목록을 한 원소 늘릴 수 있다는
보조정리 `extend`를 인수로 받는다. 그 보조정리까지 증명한 독립적인
무한집합 정리로 읽지 말고, 주어진 확장 방법을 자연수 전체의 단사로
연결하는 조건부 구성으로 읽어야 한다.
-/

namespace Ample
open scoped Ample Classical

def FiniteListing (A : Type) (n : Nat) :=
  {f : Fin n → A // Injective f}



attribute [implicit_reducible] FiniteListing



def emptyListing (A : Type) : FiniteListing A 0 :=
  { val := fun i : Fin 0 => Fin.elim0 i
    property := by
      intro i j hij
      exact Fin.elim0 i }


def appendValue {A : Type} {n : Nat} (f : Fin n → A) (a : A)
    (i : Fin (n + 1)) :
    A :=
  if hi : i.val < n then
    f { val := i.val, isLt := hi }
  else a


example {A : Type} {n : Nat} (f : Fin n → A) (a : A)
    (i : Fin (n + 1))
    (hi : i.val < n) :
    appendValue f a i = f { val := i.val, isLt := hi } := by
  rw [appendValue, dite_eq_left hi]

example {A : Type} {n : Nat} (f : Fin n → A) (a : A)
    (i : Fin (n + 1))
    (hi : ¬ i.val < n) :
    appendValue f a i = a := by
  rw [appendValue, dite_eq_right hi]


theorem appendValue_old {A : Type} {n : Nat}
    (f : Fin n → A) (a : A)
    (i : Fin n) :
    appendValue f a i.castSucc = f i := by
  have hi : i.castSucc.val < n :=
    i.isLt
  rw [appendValue]
  rw [dite_eq_left hi]
  rfl


def buildListings {A : Type}
    (step : (n : Nat) → FiniteListing A n →
      FiniteListing A (n + 1)) :
    (n : Nat) → FiniteListing A n
  | 0 => emptyListing A
  | n + 1 => step n (buildListings step n)


section InfiniteConstruction

variable
  (extend : ∀ {A : Type} {n : Nat},
    IsInfinite A → (s : FiniteListing A n) →
      ∃ t : FiniteListing A (n + 1),
        ∀ i : Fin n, t.val i.castSucc = s.val i)

include extend


noncomputable def nextListingData {A : Type}
    (hA : IsInfinite A)
    (n : Nat) (s : FiniteListing A n) :
    {t : FiniteListing A (n + 1) //
      ∀ i : Fin n, t.val i.castSucc = s.val i} :=
  { val := Classical.choose (extend hA s)
    property := Classical.choose_spec (extend hA s) }

noncomputable def nextListing {A : Type} (hA : IsInfinite A)
    (n : Nat) (s : FiniteListing A n) :
    FiniteListing A (n + 1) :=
  (nextListingData extend hA n s).val
theorem nextListing_spec {A : Type}
    (hA : IsInfinite A)
    (n : Nat) (s : FiniteListing A n) (i : Fin n) :
    (nextListing extend hA n s).val i.castSucc =
      s.val i := by
  exact (nextListingData extend hA n s).property i


noncomputable def infiniteListings {A : Type}
    (hA : IsInfinite A)
    (n : Nat) : FiniteListing A n :=
  buildListings (nextListing extend hA) n
noncomputable def natIntoInfinite {A : Type}
    (hA : IsInfinite A)
    (n : Nat) : A :=
  (infiniteListings extend hA (n + 1)).val
    { val := n, isLt := by arith }


theorem infiniteListings_value {A : Type}
    (hA : IsInfinite A)
    (n : Nat) (i : Fin n) :
    (infiniteListings extend hA n).val i =
      natIntoInfinite extend hA i.val := by
  -- 목록의 크기에 대한 귀납법으로 함수값을 비교한다.
  induction n with
  | zero =>
      exact Fin.elim0 i

  | succ n ih =>
      by_cases hi : i.val < n
      · let j : Fin n := { val := i.val, isLt := hi }

        -- 기존 번호를 앞 단계의 Fin n으로 옮긴다.
        have hij : i = j.castSucc := by
          ext

        rw [hij]
        rw [infiniteListings, buildListings]

        -- 확장은 기존 함수값을 보존하므로 귀납 가정을 쓴다.
        rw [nextListing_spec]
        exact ih j

      · have hin : i.val = n := by
          have hiBound : i.val < n + 1 :=
            i.isLt
          arith

        -- 새 번호 n으로 바꾸어 f(n)의 정의를 사용한다.
        let last : Fin (n + 1) :=
          { val := n, isLt := by arith }
        have hiLast : i = last := by
          ext
          exact hin

        rw [hiLast]
        rfl


theorem natIntoInfinite_injective {A : Type}
    (hA : IsInfinite A) :
    Injective (natIntoInfinite extend hA) := by
  intro i j hij
  -- 두 번호가 모두 들어 있는 유한한 목록을 택한다.
  let N := i + j + 1
  let p : Fin N := { val := i, isLt := by arith }
  let q : Fin N := { val := j, isLt := by arith }

  -- f(i) = f(j)를 그 목록 안의 함수값 등식으로 옮긴다.
  have hpq : (infiniteListings extend hA N).val p =
      (infiniteListings extend hA N).val q := by
    rw [infiniteListings_value extend hA N p,
      infiniteListings_value extend hA N q]
    exact hij

  -- 목록의 단사성으로 p = q를 얻고 번호 값을 비교한다.
  have hIndex : p = q :=
    (infiniteListings extend hA N).property p q hpq
  have hVal : p.val = q.val := by
    rw [hIndex]

  exact hVal

theorem infinite_has_nat_injection {A : Type}
    (hA : IsInfinite A) :
    ∃ f : Nat → A, Injective f := by
  exists natIntoInfinite extend hA
  exact natIntoInfinite_injective extend hA


theorem nat_least_infinite :
    IsInfinite Nat ∧ ∀ (A : Type), IsInfinite A →
      cardinal Nat ≤ cardinal A := by
  constructor
  · exact nat_isInfinite
  · intro A hA
    apply (cardinal_le_iff Nat A).mpr
    exact infinite_has_nat_injection extend hA

end InfiniteConstruction

end Ample
