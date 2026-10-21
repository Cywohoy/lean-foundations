import AlgebraBook.Meta.Lean
import AlgebraBook.NumbersRelations
import AlgebraBook.Tactic.Cardinality
import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open AlgebraBook

#doc (Manual) "집합의 크기" =>

%%%
tag := "sizes"
file := "sizes"
%%%

유한집합의 크기는 원소를 세어 비교할 수 있다. 무한집합의 크기는 어떻게 비교할까?
두 집합의 원소를 하나씩 짝짓는 방법을 사용하면 원소를 모두 세지 않고도 크기가 같은지 판단할 수 있다.
이 장에서는 전단사로 집합의 크기를 비교하고, 이 방법이 유한집합의 원소 수와 어떻게 연결되는지 살펴본다.
이어서 자연수와 같은 크기의 무한집합을 구성하고, 무한집합 사이에도 크기의 차이가 있음을 증명한다.

{anchor "cardinality"}[]
```savedImport
import AlgebraBook.NumbersRelations
import AlgebraBook.Tactic.Cardinality
```

```savedLean -show
open scoped Classical
```

```savedLean -show
namespace Ample
local infixr:90 (priority := high) " ∘ " => compose
```

# 전단사와 같은 크기
%%%
tag := "cardinality-same-size"
file := "same-cardinality"
%%%

앞 장에서 배운 전단사는 서로 다른 원소를 겹치지 않게 대응시키며 공역의 원소도 빠짐없이 포함한다.
따라서 전단사의 존재로 두 집합의 원소를 하나씩 짝지을 수 있음을 표현한다.

*정의* 두 집합 $`A`, $`B` 사이에 전단사함수가 존재하면 두 집합의 *크기가 같다*고 한다.
집합의 크기를 *기수*(cardinality)라고도 하며 두 집합의 기수가 같다는 관계를 $`|A|=|B|`로 쓴다.

Lean에서는 함수 절에서와 같이 원소들의 타입을 `A`, `B`로 두고
그 사이에 전단사가 존재한다는 명제를 정의한다.

```savedLean
def SameCardinality : Type → Type → Prop :=
  fun A B => ∃ f : A → B, Bijective f
```

집합 `S : Set A`와 `T : Set B`의 크기를 비교할 때는
{ref "functions-elements"}[집합 위의 함수]에서 정의한 원소 타입을 사용하여
`SameCardinality (Elem S) (Elem T)`로 쓴다.

`SameCardinality A B`의 정의를 펼치면 `∃ f : A → B, Bijective f`이다.
이 명제를 증명하려면 함수 하나를 제시하고 그 함수가 전단사임을 보이면 된다.
반대로 가정에서 이러한 함수와 전단사성의 증명을 꺼낼 때는 `unpack`을 사용한다.

이 관계가 동치관계임을 확인하자. 반사성에는 항등함수,
대칭성에는 역함수, 추이성에는 합성함수를 사용한다.

{anchor "cardinality-reflexivity"}[]*정리* 모든 집합은 자기 자신과 크기가 같다.

*증명* 항등함수는 전단사이므로 그 함수를 택하면 된다.

```savedLean
theorem sameCardinality_refl (A : Type) :
    SameCardinality A A := by
  exists identity A
  exact identity_bijective A
```

```savedLean -show
attribute [simp] sameCardinality_refl
```

{anchor "cardinality-symmetry"}[]*정리* $`|A|=|B|`이면 $`|B|=|A|`이다.

*증명* {ref "functions-inverse-bijectivity"}[역함수의 성질]에서 전단사의 역함수도 전단사임을 보였다.
주어진 전단사의 역함수를 택하면 된다.

```savedLean
theorem sameCardinality_symm {A B : Type}
    (h : SameCardinality A B) :
    SameCardinality B A := by
  unpack h with ⟨f, hf⟩
  exists (inverseMap f hf)
  exact inverseMap_bijective f hf
```

{anchor "cardinality-transitivity"}[]*정리* $`|A|=|B|`이고 $`|B|=|C|`이면 $`|A|=|C|`이다.

*증명* 전단사함수 $`f : A \to B`와 $`g : B \to C`를 택하자.
{ref "functions-composition-bijectivity"}[함수의 합성]에서 두 전단사함수의 합성도 전단사임을 증명했으므로 $`g\circ f`를 사용하면 된다.

```savedLean
theorem sameCardinality_trans {A B C : Type}
    (hAB : SameCardinality A B)
    (hBC : SameCardinality B C) :
    SameCardinality A C := by
  unpack hAB with ⟨f, hf⟩
  unpack hBC with ⟨g, hg⟩
  exists (g ∘ f)
  exact bijective_compose f g hf hg
```

# 기수와 동치류
%%%
tag := "cardinality-quotient-type"
file := "cardinals"
%%%

집합의 크기 자체를 값으로 두고 `cardinal A`로 나타내자.
앞으로 `cardinal A = cardinal B`는 두 타입 사이에 전단사가 존재한다는 뜻으로 사용하겠다.
이를 정의하기 위해 앞 장의 몫타입 구성을 같은 크기라는 관계에 적용한다.

이로써 같은 크기라는 관계의 반사성·대칭성·추이성을 모두 확인했다.
{ref "preliminaries-quotients"}[몫집합]에서는 같은 부류에 속하는 원소들이 같은 동치류를 정했다.
이번에는 원소 타입 `A`와 전단사가 존재하는 타입들을 하나의 동치류로 모으자.
정수의 합동에서는 정수들을 동치류로 묶었지만,
여기서는 `Nat`, `Int`, `Elem positives`와 같은 타입들이 관계의 대상이다.
각 동치류를 하나의 원소로 갖는 몫타입을 만들면 집합의 크기 자체를 값으로 다룰 수 있다.
이 몫타입을 `Cardinal`이라고 정의하자.

```savedLean -show
theorem sameCardinality_equivalence : IsEquivalence SameCardinality := by
  and_intros
  · exact sameCardinality_refl
  · intro A B hAB
    exact sameCardinality_symm hAB

  · intro A B C hAB hBC
    exact sameCardinality_trans hAB hBC
```

```savedLean
def Cardinal := Type / SameCardinality
def cardinal (A : Type) : Cardinal :=
  ⟦A⟧
```

```savedLean -show
attribute [reducible] Cardinal
```

`Type / SameCardinality`는 타입들을 전단사 관계로 나눈 몫타입이며,
정의를 펼치면 `Elem (quotientSet SameCardinality)`이다.
`cardinal A`는 `A`를 대표원으로 만든 몫 원소이다.
그 안에는 `A`와 전단사가 존재하는 타입들의 집합과, 이 집합이 동치류라는 증명이 들어 있다.
따라서 두 타입의 크기가 같으면 그 기수에 담긴 동치류도 같다.

*정리* 두 기수 `cardinal A`와 `cardinal B`가 같을 필요충분조건은
`SameCardinality A B`이다.

```savedLean
theorem cardinal_eq_iff (A B : Type) :
    cardinal A = cardinal B ↔ SameCardinality A B := by
  exact classOf_eq_iff SameCardinality
    sameCardinality_equivalence A B
```

```savedLean -show
attribute [ample_compare] cardinal_eq_iff
```

앞 장의 `classOf_eq_iff`를 전단사 관계에 적용한 결과이다.
이 정리를 `ext`와 `indisc`에도 연결했으므로
`ext`는 기수의 등식을 `SameCardinality A B`를 보이는 목표로 바꾸고,
`indisc at h`는 등식 가정에서 전단사의 존재를 얻는다.

```savedLean
example {A B : Type}
    (f : A → B)
    (hf : Bijective f) :
    cardinal A = cardinal B := by
  ext
  exists f

example {A B : Type}
    (h : cardinal A = cardinal B) :
    ∃ f : A → B, Bijective f := by
  exact (cardinal_eq_iff A B).mp h
```

집합 `S : Set A`의 기수는 `cardinal (Elem S)`이며
두 집합을 비교할 때도 그 원소 타입의 기수를 사용한다.

```savedLean -show
theorem cardinal_eq_of_sameCardinality {A B : Type}
    (h : SameCardinality A B) : cardinal A = cardinal B :=
  (cardinal_eq_iff A B).2 h

theorem sameCardinality_of_cardinal_eq {A B : Type}
    (h : cardinal A = cardinal B) : SameCardinality A B :=
  (cardinal_eq_iff A B).1 h

namespace Cardinal

theorem eq_symm {a b : Cardinal} (h : a = b) : b = a :=
  h.symm

theorem eq_trans {a b c : Cardinal}
    (hab : a = b) (hbc : b = c) : a = c :=
  hab.trans hbc

end Cardinal
```

# 유한한 번호
%%%
tag := "functions-fin"
%%%

원소가 $`n`개라는 것은 그 원소들에 번호 $`0,1,\ldots,n-1`을 하나씩 붙일 수 있다는 뜻이다.
번호와 원소 사이의 전단사로 이 조건을 나타내기 위해 먼저 번호들의 타입을 준비하자.
이 번호들의 집합은 $`\{k\in\mathbb{N}:k<n\}`이며
Lean에서는 이에 대응하는 타입으로 `Fin n`을 사용한다.
따라서 `Fin 3`의 원소가 나타내는 자연수는 $`0`, $`1`, $`2`이다.

Lean에 미리 정의된 `Fin`의 핵심 내용은 다음과 같다.
`structure`는 여러 자료를 하나로 묶는 선언이며
여기서는 자연수 `val`과 그 값이 `n`보다 작다는 증명 `isLt`를 묶는다.

```
structure Fin (n : Nat) where
  val : Nat
  isLt : val < n
```

즉 `Fin n`은 앞에서 본 부분타입 `{k : Nat // k < n}`과 마찬가지로
자연수와 범위 조건의 증명을 함께 담는다.
`i : Fin n`에서 `i.val : Nat`로 그 자연수를 꺼내고
`i.isLt : i.val < n`으로 범위 조건의 증명을 얻는다.
부분타입에서 조건의 증명을 꺼낼 때 쓴 `.property`에 해당하는 이름이 여기서는 `.isLt`이다.

가령 $`2<3`이므로 자연수 $`2`와 이 부등식의 증명을 묶어 `Fin 3`의 원소를 만들 수 있다.
부분타입에서와 같이 필드 이름을 적어 자연수 값과 범위 조건의 증명을 제시하자.

```savedLean
def cardinality_fin_three_last : Fin 3 :=
  { val := 2, isLt := by decide }
```

이 정의에서는 `Fin 3`의 원소 하나를 구성한다.
`val := 2`로 자연수 값을 정하고 `isLt := by decide`로 범위 조건 `2 < 3`을 확인한다.

`Fin 0`에는 $`0`보다 작은 자연수가 없으므로 원소가 없다.
따라서 `i : Fin 0`이라는 가정이 생기면 `Fin.elim0 i`로 모순에서 임의의 결론을 얻는다.
이는 앞에서 `False.elim`을 사용한 것과 같은 원리이다.

*보기* 같은 자연수 값을 갖는 두 번호는 같다. 부분타입에서와 같이 `ext`로 값의 등식을 보이면 된다.

```savedLean
example (i j : Fin n)
    (h : i.val = j.val) :
    i = j := by
  ext
  exact h
```

번호의 범위를 바꾸거나 번호를 하나씩 이동하는 방법은
{ref "cardinality-fin-conversions"}[자연수와 유한한 번호]에서 다룬다.

# 유한집합과 원소 수
%%%
tag := "cardinality-finite-sets"
file := "finite-sets"
%%%

{ref "functions-fin"}[유한한 번호]에서 `Fin n`을 자연수 값과 범위 조건으로 구성했다.
이제 각 원소에 번호를 하나씩 붙이는 전단사로 원소 수를 정의하자.

*정의* $`\{k\in\mathbb{N}:k<n\}`에서 $`A`로 가는 전단사가 존재하면
$`A`의 *원소 수가 $`n`*이라고 한다.
그러한 자연수 $`n`이 존재하는 집합을 *유한집합*이라고 한다.

```savedLean
def IsFinite : Type → Prop :=
  fun A => ∃ n : Nat, cardinal A = cardinal (Fin n)
```

원소 수가 $`n`이라는 조건은 `cardinal A = cardinal (Fin n)`으로 쓴다.
이 등식에 `ext`를 쓰면 `A`에서 `Fin n`으로 가는 전단사를 제시하는 목표가 된다.
정의에서 사용한 `Fin n → A`와 방향이 반대이지만, 전단사의 역함수도 전단사이므로 두 조건은 동치이다.
번호에서 원소로 가는 함수가 단사라는 조건은 같은 원소를 중복해서 세지 않는다는 뜻이고
전사라는 조건은 빠뜨린 원소가 없다는 뜻이다.

`Fin n`에는 항등함수로 번호를 붙일 수 있으므로 원소 수가 $`n`이며 유한하다.

```savedLean
theorem fin_isFinite (n : Nat) : IsFinite (Fin n) := by
  exists n
```

## 공집합과 한 원소 집합
%%%
tag := "cardinality-empty-and-singleton"
%%%

*보기* 공집합의 원소 수는 $`0`이다.

`Fin 0`과 공집합의 원소 타입에는 모두 원소가 없다.
정의역이 `Fin 0`인 함수는 `fun i => Fin.elim0 i`로 정의할 수 있으며
단사성과 전사성을 보일 때도 원소가 있다는 가정에서 모순을 얻는다.

번호에서 원소로 가는 함수를 제시하려면 먼저 `symm`으로 등식의 양변을 바꾸자.
그다음에 `ext`를 사용하면 `Fin 0`에서 공집합의 원소 타입으로 가는 전단사의 존재가 목표가 된다.

```savedLean
theorem empty_cardinal (A : Type) :
    cardinal (Elem (∅ : Set A)) = cardinal (Fin 0) := by
  symm
  ext
  exists (fun i : Fin 0 => Fin.elim0 i)
  constructor
  · intro i j hij
    exact Fin.elim0 i

  · intro x
    have hx : False :=
      x.property
    contradiction
```

전사성을 보이는 부분의 `x`는 공집합의 원소이므로 `x.property`는 `False`의 증명이다.
따라서 `contradiction`으로 그 경우를 마친다.

*보기* 원소 $`a` 하나로 이루어진 집합 $`\{a\}`의 원소 수는 $`1`이다.

먼저 원소 조건 $`x=a`로 이 집합을 정의하자.

```savedLean
def singleton {A : Type} (a : A) : Set A := fun x => x = a
```

유일한 번호 $`0`에 원소 $`a`를 대응시키자.
단사성을 확인하려고 번호 $`i`, $`j`를 택하면 둘 다 $`0`이므로 서로 같다.
또한 $`\{a\}`의 모든 원소가 $`a`와 같으므로 이 대응은 전사이다.

이 대응을 증명 안에서 여러 번 사용하므로 `let`으로 함수 `f`를 정의하자.
{ref "relations-local-definitions"}[앞에서는] `let`으로 대표원에 이름을 붙였으며,
이번에는 `let f (_ : Fin 1) ...`처럼 인수를 적어 함수를 정의한다.
이후에는 `f`를 함수 이름으로 사용하고 필요할 때 그 정의를 펼친다.
전사성을 증명할 때 쓰는 번호 `zero`도 같은 방법으로 정의한다.

```savedLean
theorem singleton_cardinal {A : Type} (a : A) :
    cardinal (Elem (singleton a)) = cardinal (Fin 1) := by
  symm
  ext
  -- 번호 0을 원소 a에 대응시킨다.
  let f (_ : Fin 1) : Elem (singleton a) :=
    { val := a, property := by rfl }
  exists f
  constructor
  · intro i j hij
    -- Fin 1의 두 번호는 모두 자연수 값이 0이다.
    ext
    have hi : i.val < 1 :=
      i.isLt
    have hj : j.val < 1 :=
      j.isLt
    arith

  · intro x
    -- 집합의 원소 x는 a이므로 번호 0에서 얻는다.
    let zero : Fin 1 :=
      { val := 0, isLt := by decide }
    exists zero
    ext
    exact x.property.symm
```

함수 `f`의 값은 원소 `a`와 그 원소 조건인 `a = a`의 증명을 함께 담는다.
단사성의 목표에 `ext`를 사용하면 목표가 `i.val = j.val`로 바뀐다.
두 값이 모두 $`1`보다 작은 자연수라는 조건 `i.isLt`와 `j.isLt`에 따라
두 값은 모두 $`0`이다. 이 범위 조건으로 두 값이 같음을 `arith`가 확인한다.
전사성에서는 번호 $`0`을 택하고 `ext`로 집합의 원소 값을 비교한다.
이때 `x.property`는 `x.val = a`의 증명이므로 `.symm`으로 양변의 순서를 바꾼다.

*문제 1* 원소가 하나씩 있는 두 집합은 크기가 같음을 증명하라.

```savedLean -keep
theorem exercise_singletons_same_cardinal {A B : Type}
    (a : A) (b : B) :
    cardinal (Elem (singleton a)) =
      cardinal (Elem (singleton b)) := by
  sorry
```

## 세 원소 집합의 원소 수
%%%
tag := "cardinality-counting-three-elements"
%%%

*보기* 자연수의 집합 $`\{10,11,12\}`의 원소 수는 $`3`이다.
이 집합을 부등식으로 정의하고 번호 $`0`, $`1`, $`2`를 각각 $`10`, $`11`, $`12`에 대응시키자.

```savedLean
def threeNumbers : Set Nat := fun k => 10 ≤ k ∧ k < 13
```

대응 함수는 $`f(i)=10+i`이다.
$`10+i=10+j`이면 $`i=j`이므로 단사이며,
집합의 원소 $`x`는 $`10\leq x<13`을 만족하므로 번호 $`x-10`에 대응한다.
원소 $`x`의 범위 조건에 따라 이 번호는 $`0`, $`1`, $`2` 중 하나이며 그 함수값은 다시 $`x`이다.
따라서 모든 원소가 함수값으로 나타나므로 함수는 전사이다.

Lean의 자연수 뺄셈은 결과가 음수가 되는 경우에 $`0`을 돌려준다.
여기서는 $`10\leq x`라는 조건이 있으므로 $`10+(x-10)=x`가 성립하며
이 등식으로 택한 번호의 함수값이 원래 원소임을 확인한다.

```savedLean
theorem threeNumbers_cardinal :
    cardinal (Elem threeNumbers) = cardinal (Fin 3) := by
  symm
  ext
  -- 번호 0, 1, 2를 각각 10, 11, 12에 대응시킨다.
  let f (i : Fin 3) : Elem threeNumbers :=
    { val := 10 + i.val
      property := by
        have hi : i.val < 3 :=
          i.isLt
        constructor
        · arith
        · arith }

  exists f
  constructor
  · intro i j hij
    -- 함수값의 등식을 자연수의 등식으로 옮긴다.
    expand at hij
    indisc at hij
    ext
    arith

  · intro x
    -- 원소 x에 대응하는 번호는 x - 10이다.
    have hx : 10 ≤ x.val ∧ x.val < 13 :=
      x.property
    let i : Fin 3 :=
      { val := x.val - 10, isLt := by arith }
    -- 이 번호에 10을 더하면 원래 원소 x를 얻는다.
    exists i
    ext
    dsimp [f, i]
    arith
```

함수값을 만들 때는 `i.isLt`가 번호의 범위 `i.val < 3`을 보장한다.
이를 사용하여 `10 + i.val`이 집합의 두 부등식 조건을 만족함을 확인한다.
단사성에서는 부분타입과 번호에 담긴 값만 비교하므로 공통 항 $`10`을 소거하면 된다.

전사성에서는 `x.property`에서 원소의 범위를 얻고 이를 바탕으로 번호 `i`를 만든다.
`ext`로 원소 값을 비교하고 `dsimp [f, i]`로 두 정의를 펼치면
목표는 `10 + (x.val - 10) = x.val`이며
`hx`의 하한 조건 `10 ≤ x.val`이 있으므로 자연수의 뺄셈에서도 이 등식이 성립한다.

## 연습문제: 두 원소 집합의 번호
%%%
tag := "cardinality-counting-practice"
%%%

앞의 세 원소 집합에서 사용한 번호 붙이기를 두 원소 집합에 적용해 보자.

*문제 2* (두 원소 집합의 번호)

집합 $`\{2,3\}`의 두 원소에 각각 번호 $`0`, $`1`을 붙인다.
아래 함수가 전단사임을 증명한 뒤 그 결과로 집합의 원소 수가 $`2`임을 보이라.

```savedLean -keep
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
```

## 전단사와 원소 수
%%%
tag := "cardinality-transport"
%%%

*정리* $`A`의 원소 수가 $`n`이고 $`|A|=|B|`이면 $`B`의 원소 수도 $`n`이다.

*증명* 번호에서 $`A`로 가는 전단사에 $`A`에서 $`B`로 가는 전단사를 합성한다.
이 합성도 전단사이므로 같은 번호로 $`B`의 원소를 셀 수 있다.
기수의 등식으로 증명할 때는 목표의 `cardinal B`를 `cardinal A`로 바꾸면 된다.
`rw [← hAB]`는 등식 `hAB`를 반대 방향으로 사용하므로 이 변환을 수행한다.

```savedLean
theorem cardinality_finite_transport {A B : Type} {n : Nat}
    (hAB : cardinal A = cardinal B)
    (hA : cardinal A = cardinal (Fin n)) :
    cardinal B = cardinal (Fin n) := by
  rw [← hAB]
  exact hA
```

# 번호와 자연수
%%%
tag := "cardinality-fin-conversions"
%%%

{anchor "cardinality-fin-values"}[]{anchor "cardinality-fin-bounds"}[]{anchor "cardinality-fin-equality"}[]
`i : Fin n`은 값 `i.val`과 범위 조건 `i.isLt : i.val < n`을 함께 담는다.
`↑i`도 자연수 값 `i.val`을 나타낸다.
번호의 범위를 바꿀 때에는 같은 값에 새 범위 조건의 증명을 붙이면 된다.

```savedLean
example (i : Fin n)
    (h : n ≤ m) :
    Fin m :=
  { val := i.val
    isLt := by arith }
```

이 구성은 값에 $`1`을 더하는 것과 다르다. 값은 그대로 두고 허용 범위만 넓혔다.
다음 증명에서는 번호 하나를 지운 뒤 남은 번호들을 다시 매기므로, 값과 범위를 함께 바꾼다.

```savedLean -show
example {n : Nat}
    (i : Fin n) :
    (i : Nat) = i.val := by
  rfl
```

```savedLean -show
def cardinality_fin_from_bound {n : Nat}
    (x : Nat)
    (hx : x < n) :
    Fin n :=
  { val := x, isLt := hx }
```

```savedLean -show
def cardinality_fin_embed_succ {n : Nat}
    (i : Fin n) : Fin (n + 1) :=
  { val := i.val
    isLt := by
      have hi : i.val < n :=
        i.isLt
      arith }
```

```savedLean -show
example {n : Nat}
    (i : Fin n) :
    i.castSucc.val = i.val := by
  rfl

example {n : Nat}
    (i : Fin n) :
    i.succ.val = i.val + 1 := by
  rfl
```

```savedLean -show
def cardinality_fin_castLE {m n : Nat}
    (i : Fin n)
    (h : n ≤ m) :
    Fin m := by
  exact i.castLE h

example {m n : Nat} (i : Fin n)
    (h : n ≤ m) :
    (i.castLE h).val = i.val := by
  rfl
```

```savedLean -show
def cardinality_fin_castLT {n : Nat}
    (i : Fin (n + 1))
    (hi : i.val < n) :
    Fin n :=
  { val := i.val, isLt := hi }
```

```savedLean -show
example {n : Nat}
    (i : Fin (n + 1))
    (hi : i.val < n) :
    (i.castLT hi).val = i.val := by
  rfl
```

```savedLean -show
def cardinality_fin_pred {n : Nat}
    (i : Fin (n + 1))
    (hi : i.val ≠ n) :
    Fin n :=
  { val := i.val
    isLt := by
      have hbound : i.val < n + 1 :=
        i.isLt
      arith }
```

```savedLean -show
theorem cardinality_fin_eq_iff_values {n : Nat}
    (i j : Fin n) :
    i = j ↔ i.val = j.val := by
  constructor
  · intro h
    rw [h]

  · intro h
    ext
    exact h
```

```savedLean -show
example {n : Nat}
    (i : Fin n) (j : Fin (n + 1))
    (h : i.val = j.val) :
    i.castSucc = j := by
  ext
  exact h
```

# 원소 수의 유일성
%%%
tag := "cardinality-uniqueness"
file := "uniqueness"
%%%

한 집합에 두 가지 방법으로 번호를 붙였다고 하자.
각 방법에서 번호로 쓴 `Fin m`과 `Fin n`은 모두 그 집합과 전단사로 연결되므로
두 번호 집합 사이에도 전단사가 있다.
따라서 원소 수가 하나로 정해짐을 보이려면 이러한 전단사에서 $`m=n`을 얻어야 한다.

이 절의 결론은 다음과 같다.

> 한 집합 `A`에 대해 `cardinal A = cardinal (Fin m)`과
> `cardinal A = cardinal (Fin n)`이 모두 성립하면 `m = n`이다.

예를 들어 앞에서 세 원소 집합으로 센 `threeNumbers`에 다른 번호를 붙여
`cardinal (Elem threeNumbers) = cardinal (Fin n)`을 얻었다면 $`n=3`이어야 한다.
이 결론을 사용할 때는 번호를 지우는 함수를 다시 구성할 필요 없이
아래에서 증명할 `finite_cardinal_unique`에 두 등식의 증명을 주면 된다.

증명은 다음 세 단계로 진행한다.

1. `Fin (m + 1)`에서 `Fin (n + 1)`로 가는 단사함수에서
   정의역의 번호 하나와 그 함수값을 지워 `Fin m`에서 `Fin n`으로 가는 단사함수를 만든다.
2. 이 축소를 귀납법으로 반복하여 `Fin m`에서 `Fin n`으로 가는 단사가 있으면 $`m\leq n`임을 보인다.
   이는 서로 다른 $`m`개의 원소를 $`n`개의 자리에 넣으려면 자리가 충분해야 한다는 비둘기집 원리이다.
3. 전단사와 그 역함수에 두 번째 결과를 적용하면 $`m\leq n`과 $`n\leq m`을 얻으므로 $`m=n`이다.

## 번호 한 쌍의 삭제
%%%
tag := "cardinality-removing-a-pair"
%%%

{anchor "cardinality-erasing-an-index"}[]단사함수 $`f`에서 정의역의 번호 $`0`과 공역의 번호 $`f(0)`을 지우자.
남은 정의역의 번호는 $`i+1`로 쓸 수 있다.
단사성에 따라 $`f(i+1)\ne f(0)`이므로 남은 함수값이 지운 자리에 들어갈 일은 없다.
공역에서 지운 번호보다 작은 번호는 그대로 두고, 큰 번호는 $`1`씩 줄이면 새 번호가 된다.

예를 들어 $`0,1,2,3,4`에서 $`2`를 지우면 $`0,1,3,4`에 각각 $`0,1,2,3`을 대응시킨다.
남은 번호 사이에서는 이 대응이 단사이다. 따라서 새 함수값이 같으면 원래 함수값이 같고,
$`f`의 단사성으로 원래 정의역의 번호도 같다.
이 구성으로 다음 보조정리를 얻는다.

```
fin_injection_remove {m n : Nat}
    (f : Fin (m + 1) → Fin (n + 1))
    (hf : Injective f) :
    ∃ g : Fin m → Fin n, Injective g
```

이 보조정리로 양쪽에서 한 쌍을 지운 단사함수를 얻는다.
귀납 단계에서는 이 함수에 귀납 가정을 적용한다.

```savedLean -show
def eraseIndex (r k : Nat) : Nat :=
  if k < r then k else k - 1
```

```savedLean -show
example :
    eraseIndex 2 0 = 0 ∧ eraseIndex 2 1 = 1 ∧
    eraseIndex 2 3 = 2 ∧ eraseIndex 2 4 = 3 := by
  decide
```

```savedLean -show
example :
    eraseIndex 2 1 = eraseIndex 2 2 := by
  rfl
```

```savedLean -show
example (r k : Nat)
    (h : k < r) :
    (if k < r then k else k - 1) = k := by
  exact ite_eq_left h

example
    (r k : Nat)
    (h : ¬ k < r) :
    (if k < r then k else k - 1) = k - 1 := by
  exact ite_eq_right h
```

```savedLean -show
theorem eraseIndex_lt {n r k : Nat}
    (hr : r < n + 1)
    (hk : k < n + 1)
    (hne : k ≠ r) :
    eraseIndex r k < n := by
  rw [eraseIndex]
  by_cases h : k < r
  · rw [ite_eq_left h]
    arith

  · rw [ite_eq_right h]
    arith
```

```savedLean -show
theorem eraseIndex_injective {r x y : Nat}
    (hx : x ≠ r)
    (hy : y ≠ r)
    (h : eraseIndex r x = eraseIndex r y) :
    x = y := by
  -- 두 번호가 지운 자리 r보다 작은지에 따라 경우를 나눈다.
  rw [eraseIndex, eraseIndex] at h
  by_cases hxr : x < r
  · by_cases hyr : y < r

    · -- 양쪽 모두 원래 번호를 유지한다.
      rw [ite_eq_left hxr, ite_eq_left hyr] at h
      arith

    · -- 새 번호가 r의 양쪽에 있으므로 같을 수 없다.
      rw [ite_eq_left hxr, ite_eq_right hyr] at h
      arith

  · by_cases hyr : y < r

    · -- 이번에도 새 번호가 r의 양쪽에 있다.
      rw [ite_eq_right hxr, ite_eq_left hyr] at h
      arith

    · -- 양변에 1을 더하면 원래 번호의 등식을 얻는다.
      rw [ite_eq_right hxr, ite_eq_right hyr] at h
      arith
```

```savedLean -show
theorem fin_injection_remove {m n : Nat}
    (f : Fin (m + 1) → Fin (n + 1))
    (hf : Injective f) :
    ∃ g : Fin m → Fin n, Injective g := by
  -- 정의역의 0을 지우고 나머지 번호를 i + 1로 쓴다.
  let first : Fin (m + 1) :=
    { val := 0, isLt := by arith }
  let next (i : Fin m) : Fin (m + 1) :=
    { val := i.val + 1
      isLt := Nat.succ_lt_succ i.isLt }

  -- 단사성에 따라 나머지 함수값은 f(0)과 다르다.
  have hne (i : Fin m) :
      (f (next i)).val ≠ (f first).val := by
    intro h
    have hfi : f (next i) = f first := by
      ext
      exact h

    have hi : next i = first :=
      hf (next i) first hfi
    have hiVal : (next i).val = first.val := by
      rw [hi]

    expand at hiVal
    arith

  -- 공역에서 f(0)을 지우고 번호를 다시 붙인다.
  let g (i : Fin m) : Fin n :=
    { val := eraseIndex (f first).val (f (next i)).val
      isLt := eraseIndex_lt
        (f first).isLt (f (next i)).isLt (hne i) }

  have hg : Injective g := by
    intro i j hij
    -- 새 번호의 등식에서 원래 함수값의 등식을 얻는다.
    have hVal : (g i).val = (g j).val := by
      rw [hij]

    have hfi : f (next i) = f (next j) := by
      ext
      exact eraseIndex_injective (hne i) (hne j) hVal

    -- f의 단사성으로 i + 1 = j + 1을 얻는다.
    have hi : next i = next j :=
      hf (next i) (next j) hfi
    have hiVal : (next i).val = (next j).val := by
      rw [hi]

    -- 양변의 1을 소거하여 i = j를 보인다.
    ext
    expand at hiVal
    arith

  exists g
```

## 비둘기집 원리
%%%
tag := "cardinality-pigeonhole"
%%%

*정리* `Fin m`에서 `Fin n`으로 가는 단사함수가 있으면 $`m\leq n`이다.

*증명* 공역의 번호 수 $`n`에 대한 귀납법을 사용한다.
$`n=0`이면 공역에 원소가 없으므로 정의역도 비어 있어야 하며 $`m=0`이다.
이제 공역의 번호 수가 $`n+1`이라고 하자.
정의역이 비어 있으면 결론이 성립하며
정의역의 번호 수가 $`m+1`이면 앞의 정리로 한 쌍을 지워 `Fin m`에서 `Fin n`으로 가는 단사를 얻는다.
귀납 가정에 따라 $`m\leq n`이므로 $`m+1\leq n+1`이다.

이 증명에서는 한 쌍을 지울 때 정의역과 공역의 번호 수가 모두 하나씩 줄어든다.
따라서 귀납 가정을 줄어든 정의역에도 적용할 수 있어야 한다.
그런데 `induction n`만 쓰면 정의역의 번호 수 `m`은 처음 정한 값으로 고정된다.
`m = k + 1`인 경우에 얻는 귀납 가정은 다음 형태이다.

```
ih : ∀ (f : Fin (k + 1) → Fin n),
  Injective f → k + 1 ≤ n
```

이 귀납 가정이 받는 함수의 정의역은 `Fin (k + 1)`이다.
앞의 정리로 한 쌍을 지운 뒤 얻은 함수는 `g : Fin k → Fin n`이므로
정의역이 맞지 않아 `ih g hg`에 사용할 수 없다.

`induction n generalizing m`을 쓰면 `m`을 고정하지 않고 모든 `m`에 대하여 귀납법을 적용한다.
이때 귀납 가정은 다음과 같이 임의의 정의역 크기를 받을 수 있다.

```
ih : ∀ {m : Nat} (f : Fin m → Fin n),
  Injective f → m ≤ n
```

이제 `g : Fin k → Fin n`과 `hg : Injective g`를 넣으면
암시적 인수 `m`이 `k`로 정해지므로 `ih g hg`에서 `k ≤ n`을 얻는다.
아래 코드에서는 `cases m`으로 정의역의 번호 수를 $`0`과 $`k+1`의 두 경우로 나눈다.
코드의 `succ m`에서 새로 붙인 이름 `m`은 이 설명의 $`k`에 해당한다.

```savedLean
theorem fin_injective_le {m n : Nat} (f : Fin m → Fin n)
    (hf : Injective f) :
    m ≤ n := by
  -- 정의역의 크기도 달라질 수 있도록 귀납법을 쓴다.
  induction n generalizing m with
  | zero =>
      -- 공역이 공집합이면 정의역도 공집합이어야 한다.
      cases m with
      | zero => arith
      | succ m =>
          let first : Fin (m + 1) :=
            { val := 0, isLt := by arith }
          exact Fin.elim0 (f first)

  | succ n ih =>
      cases m with
      | zero => arith
      | succ m =>
          -- 한 쌍을 지워 양쪽 번호 수를 하나씩 줄인다.
          unpack fin_injection_remove f hf with ⟨g, hg⟩
          have hmn : m ≤ n :=
            ih g hg
          -- m ≤ n에서 m + 1 ≤ n + 1을 얻는다.
          arith
```

공역이 `Fin 0`이고 정의역에 번호 $`0`인 `first`가 있다면
`f first : Fin 0`에서 `Fin.elim0`으로 모순을 얻는다.
양쪽 번호 수가 모두 양수인 경우에는 `fin_injection_remove`로 한 쌍을 지운 뒤
귀납 가정에서 얻은 `m ≤ n`으로 `m + 1 ≤ n + 1`을 증명한다.

*보기* `Fin 3`에서 `Fin 2`로 가는 함수는 단사가 될 수 없다.
단사라고 가정하면 방금 증명한 정리에 따라 $`3\leq2`가 되어 모순이다.

```savedLean
theorem three_into_two_not_injective (f : Fin 3 → Fin 2) :
    ¬ Injective f := by
  intro hf
  have h : 3 ≤ 2 := by
    exact fin_injective_le f hf

  arith
```

이 결과를 세 사람을 두 방에 배정하는 상황에 적용하자.
사람의 번호를 `Fin 3`, 방의 번호를 `Fin 2`로 두면 배정은 함수 `f : Fin 3 → Fin 2`이다.
서로 다른 두 사람이 같은 방에 배정된다는 것은
`i ≠ j ∧ f i = f j`를 만족하는 번호 `i`, `j`가 존재한다는 뜻이다.

*보기* 세 사람을 두 방에 배정하면 같은 방에 배정된 서로 다른 두 사람이 있다.

*풀이* 그런 두 사람이 없다고 가정하자.
같은 방에 배정된 번호 $`i`, $`j`가 서로 다르다면 처음에 없다고 가정한 두 사람을 찾은 셈이다.
따라서 $`i=j`이며 배정 함수가 단사가 된다. 이는 앞의 정리와 모순이다.

```savedLean
theorem three_into_two_collision (f : Fin 3 → Fin 2) :
    ∃ i j, i ≠ j ∧ f i = f j := by
  by_contra hCollision
  apply three_into_two_not_injective f
  intro i j hij
  -- 같은 함수값을 갖는 서로 다른 두 번호가 있으면 처음 가정과 모순이다.
  by_contra hne
  apply hCollision
  exists i
  exists j
```

`apply three_into_two_not_injective f` 뒤에는 `Injective f`가 목표로 남는다.
단사성을 증명하는 동안 `i ≠ j`라고 가정하면
`hne`와 `hij`가 처음의 존재명제에 필요한 두 조건을 모두 제공한다.
이처럼 단사가 될 수 없다는 일반적인 결론으로 실제로 겹치는 한 쌍의 존재를 얻는다.

*문제 3* $`n+1`개의 번호를 $`n`개의 번호에 단사로 대응시킬 수 없음을 증명하라.

```savedLean -keep
theorem exercise_fin_succ_not_injective
    (n : Nat) (f : Fin (n + 1) → Fin n) :
    ¬ Injective f := by
  sorry
```

*문제 4* (같은 달에 태어난 두 사람)

(1) $`n+1`개의 번호를 $`n`개의 번호로 보내는 함수에서는
서로 다른 두 번호의 함수값이 같음을 증명하라.

(2) 열세 사람에게 태어난 달을 대응시키면 같은 달에 태어난 두 사람이 있음을 첫 결과로 보이라.
사람과 달을 각각 `Fin 13`, `Fin 12`로 나타낸다.

```savedLean -keep
theorem exercise_fin_collision (n : Nat)
    (f : Fin (n + 1) → Fin n) :
    ∃ i j, i ≠ j ∧ f i = f j := by
  sorry

theorem exercise_birth_month_collision
    (month : Fin 13 → Fin 12) :
    ∃ i j, i ≠ j ∧ month i = month j := by
  sorry
```

*힌트* 첫 문제에서 같은 함수값을 갖는 서로 다른 두 번호가 없다고 가정하면 함수가 단사임을 보일 수 있다.

## 세는 방법과 원소 수
%%%
tag := "cardinality-number-unique"
%%%

*정리* `Fin m`과 `Fin n`의 크기가 같으면 $`m=n`이다.

*증명* 주어진 전단사와 그 역함수는 모두 단사이다.
각 함수에 앞의 정리를 적용하면 $`m\leq n`과 $`n\leq m`을 얻는다.
따라서 $`m=n`이다.

```savedLean
theorem fin_sameCardinality_eq {m n : Nat}
    (h : SameCardinality (Fin m) (Fin n)) :
    m = n := by
  -- 양방향의 전단사를 각각 택한다.
  have hReverse : SameCardinality (Fin n) (Fin m) :=
    sameCardinality_symm h
  unpack h with ⟨f, hf⟩
  unpack hReverse with ⟨g, hg⟩

  -- 각 단사성에서 두 번호 수 사이의 부등식을 얻는다.
  have hmn : m ≤ n :=
    fin_injective_le f hf.inj
  have hnm : n ≤ m :=
    fin_injective_le g hg.inj
  -- m ≤ n과 n ≤ m을 합치면 m = n이다.
  arith
```

기수의 등식에서 전단사의 존재를 얻으면 다음과 같이 같은 결론을 사용할 수 있다.

```savedLean
theorem cardinal_fin_eq {m n : Nat}
    (h : cardinal (Fin m) = cardinal (Fin n)) :
    m = n := by
  apply fin_sameCardinality_eq
  exact (cardinal_eq_iff _ _).mp h
```

*정리* 한 집합의 원소 수가 $`m`이면서 $`n`이면 $`m=n`이다.

*증명* 두 기수의 등식 $`|A|=|\operatorname{Fin}(m)|`와
$`|A|=|\operatorname{Fin}(n)|`에서 $`|\operatorname{Fin}(m)|=|\operatorname{Fin}(n)|`를 얻는다.
방금 증명한 정리를 사용하면 $`m=n`이다.

```savedLean
theorem finite_cardinal_unique {A : Type} {m n : Nat}
    (hm : cardinal A = cardinal (Fin m))
    (hn : cardinal A = cardinal (Fin n)) :
    m = n := by
  apply cardinal_fin_eq
  exact hm.symm.trans hn
```

`hm.symm`으로 첫 등식의 방향을 바꾸면 `cardinal (Fin m) = cardinal A`를 얻는다.
여기에 `.trans hn`으로 두 번째 등식을 이어 붙이면 두 번호 타입의 기수가 같다는 등식이 된다.

앞에서 센 집합에 이 정리를 적용하면 다음과 같다. 첫 번째 인수는 새로운 방법으로 센 결과이고,
두 번째 인수는 이미 증명한 원소 수이다.

```savedLean
example (n : Nat)
    (hn : cardinal (Elem threeNumbers) = cardinal (Fin n)) :
    n = 3 := by
  exact finite_cardinal_unique hn threeNumbers_cardinal
```

# 유한기수와 자연수
%%%
tag := "cardinality-natural-cardinals"
file := "natural-cardinals"
%%%

앞의 정리에 따라 $`\operatorname{Fin}(m)`과 $`\operatorname{Fin}(n)`의 기수가 같으면 $`m=n`이다.
따라서 자연수 $`n`을 $`\operatorname{Fin}(n)`의 기수에 대응시키는 함수는 단사이다.
이 대응을 정의하고 두 자연수의 등식과 그 기수의 등식을 연결하자.

```savedLean
namespace Cardinal

def ofNat (n : Nat) : Cardinal := cardinal (Fin n)
theorem ofNat_eq_iff (m n : Nat) :
    ofNat m = ofNat n ↔ m = n := by
  constructor
  · exact cardinal_fin_eq
  · intro h
    rw [h]

end Cardinal
```

`ofNat_eq_iff`는 서로 다른 자연수가 서로 다른 기수에 대응함을 보인다.
이 단사성을 바탕으로 `(n : Cardinal)`을 `Cardinal.ofNat n`의 표기로 사용하겠다.
기수가 필요한 문맥에서는 자연수를 기수로 바꾸는 형변환이 적용되며
증명 화면에는 같은 변환이 `↑n`으로 나타날 수 있다.
따라서 `cardinal A = n`은 `cardinal A = cardinal (Fin n)`이라는 뜻이다.

```savedLean -show
namespace Cardinal
instance : NatCast Cardinal := ⟨ofNat⟩
instance (n : Nat) : OfNat Cardinal n := ⟨ofNat n⟩
end Cardinal
```

```savedLean
theorem cardinal_fin (n : Nat) :
    cardinal (Fin n) = (n : Cardinal) := by
  rfl
```

예를 들어 `cardinal (Fin 3) = 3`은 오른쪽의 $`3`을 유한기수로 사용한 등식이다.
자연수의 곱으로 원소 수를 나타내는 `cardinal A = m * n`에서는
먼저 자연수의 곱 `m * n`을 구한 뒤 그 값을 기수로 바꾼다.

```savedLean -show
noncomputable def cardinalityData (A : Type)
    (hA : IsFinite A) : {n : Nat // cardinal A = n} :=
  { val := Classical.choose hA
    property := Classical.choose_spec hA }

noncomputable def cardinality (A : Type)
    (hA : IsFinite A) : Nat :=
  (cardinalityData A hA).val
theorem cardinality_spec (A : Type)
    (hA : IsFinite A) :
    cardinal A = cardinality A hA := by
  exact (cardinalityData A hA).property

theorem cardinality_eq {A : Type} {n : Nat}
    (hA : IsFinite A)
    (hn : cardinal A = n) :
    cardinality A hA = n := by
  exact finite_cardinal_unique (cardinality_spec A hA) hn
```

```savedLean -show
example :
    cardinality (Fin 3) (fin_isFinite 3) = 3 := by
  exact cardinality_eq (fin_isFinite 3) (cardinal_fin 3)
```

*문제 5* (서로 다른 원소 수)

(1) `Fin 2`와 `Fin 3` 사이에는 전단사가 존재하지 않음을 증명하라.

(2) 본문에서 센 집합 $`\{10,11,12\}`의 원소 수가 $`4`일 수 없음을 보이라.
원소 수의 유일성에 관한 정리들을 사용하라.

```savedLean -keep
theorem exercise_fin_two_three_not_same :
    ¬ SameCardinality (Fin 2) (Fin 3) := by
  sorry

theorem exercise_threeNumbers_not_four :
    cardinal (Elem threeNumbers) ≠ 4 := by
  sorry
```

## 유한성의 전달

기수가 같은 집합에는 같은 수의 번호를 붙일 수 있으므로 유한성이 유지된다.

```savedLean
theorem isFinite_of_cardinal_eq {A : Type} {n : Nat}
    (h : cardinal A = n) :
    IsFinite A := by
  exists n

theorem isFinite_transport {A B : Type}
    (hAB : cardinal A = cardinal B)
    (hA : IsFinite A) :
    IsFinite B := by
  unpack hA with ⟨n, hn⟩
  exists n
  rw [← hAB]
  exact hn
```

*문제 6* 크기가 같은 두 집합 $`A`, $`B`에 대하여
$`A`의 원소 수가 $`n`이라는 명제와 $`B`의 원소 수가 $`n`이라는 명제가 동치임을 증명하라.

```savedLean -keep
theorem exercise_finite_cardinal_transport
    {A B : Type} {n : Nat}
    (hAB : cardinal A = cardinal B) :
    cardinal A = n ↔ cardinal B = n := by
  sorry
```

# 유한집합의 곱

두 유한집합의 원소 수가 각각 $`m`, $`n`이면 그 곱에는 $`mn`개의 원소가 있다.
이를 보이려면 각 집합의 번호를 순서쌍으로 묶고, 번호 쌍을 다시 하나의 번호로 세면 된다.

## 성분별 함수의 단사·전사
%%%
tag := "functions-product-maps"
file := "product-maps"
%%%

합성함수에서는 한 함수의 값을 다음 함수에 넣었다.
집합의 곱에서는 두 성분에 서로 다른 함수를 적용하는 방식도 사용할 수 있다.
함수 $`f:A\to C`와 $`g:B\to D`가 주어지면
$`(a,b)\mapsto(f(a),g(b))`로 $`A\times B`에서 $`C\times D`로 가는 함수를 정의하자.

```savedLean
def productMap {A B C D : Type}
    (f : A → C) (g : B → D) : A × B → C × D :=
  fun p => (f p.1, g p.2)
```

*보기* $`f`와 $`g`가 각각 단사이면 `productMap f g`도 단사이다.
두 함수값인 순서쌍이 같으면 각 성분이 같으므로
$`f(a)=f(a')`와 $`g(b)=g(b')`를 얻는다.
각 함수의 단사성에 따라 $`a=a'`이고 $`b=b'`이므로 원래 순서쌍들도 같다.

```savedLean
theorem productMap_injective {A B C D : Type}
    (f : A → C) (g : B → D)
    (hf : Injective f)
    (hg : Injective g) :
    Injective (productMap f g) := by
  intro x y hxy
  -- 함수값의 두 성분을 각각 비교한다.
  indisc at hxy with hfirst hsecond
  ext
  · exact hf x.1 y.1 hfirst
  · exact hg x.2 y.2 hsecond
```

`indisc at hxy with hfirst hsecond`로 함수값의 두 성분이 같음을 얻는다.
이 두 등식에 `hf`와 `hg`를 사용하면 원래 순서쌍의 각 성분을 비교할 수 있다.

*보기* $`f`와 $`g`가 각각 전사이면 `productMap f g`도 전사이다.
공역의 원소 $`(c,d)`를 택하면 전사성에 따라 $`f(a)=c`와 $`g(b)=d`인 원소 $`a,b`가 존재한다.
그러면 $`(a,b)`에서의 함수값이 $`(c,d)`이므로 전사성을 얻는다.

```savedLean
theorem productMap_surjective {A B C D : Type}
    (f : A → C) (g : B → D)
    (hf : Surjective f)
    (hg : Surjective g) :
    Surjective (productMap f g) := by
  intro y
  -- 공역의 각 성분에 대응하는 원소를 택한다.
  unpack hf y.1 with ⟨a, ha⟩
  unpack hg y.2 with ⟨b, hb⟩
  exists (a, b)
  ext
  · exact ha
  · exact hb
```

여기서 `hf y.1`은 `∃ a, f a = y.1`의 증명이고
`hg y.2`는 `∃ b, g b = y.2`의 증명이다.
두 원소를 함께 택한 뒤 `ext`로 함수값의 두 성분을 비교하면
각 존재명제에서 얻은 등식을 그대로 사용할 수 있다.

*보기* $`f`와 $`g`가 각각 전단사이면 `productMap f g`도 전단사이다.
앞의 두 보기에서 단사성과 전사성을 각각 증명했으므로
그 결과를 사용하여 두 조건을 묶자.

```savedLean
theorem productMap_bijective {A B C D : Type}
    (f : A → C) (g : B → D)
    (hf : Bijective f)
    (hg : Bijective g) :
    Bijective (productMap f g) := by
  constructor
  · exact productMap_injective f g hf.inj hg.inj
  · exact productMap_surjective f g
      hf.surj hg.surj
```

각 집합에 번호를 붙이는 두 전단사에 이 결과를 사용하면 번호 쌍과 집합의 곱 사이의 전단사를 얻는다.

## 번호 쌍과 집합의 곱
%%%
tag := "cardinality-product-numbering"
file := "product-numbering"
%%%

두 집합의 곱을 세려면 먼저 번호 쌍을 하나의 번호로 바꾸는 방법이 필요하다.
첫 번호의 범위가 $`m`, 둘째 번호의 범위가 $`n`이면
$`(i,j)`에 번호 $`i+jm`을 붙일 수 있다.
이 번호를 $`m`으로 나눈 나머지와 몫에서 각각 $`i`, $`j`를 되찾는다.

$`0\leq i<m`이고 $`0\leq j<n`이면
$`i+jm<(j+1)m\leq nm=mn`이므로 새 번호도 범위 안에 있다.
또한 $`i<m`이므로 $`i+jm`을 $`m`으로 나눈 나머지는 $`i`이고 몫은 $`j`이다.
거꾸로 $`0\leq x<mn`인 번호에서 출발하면
나머지와 몫은 각각 $`m`, $`n`보다 작으며
$`x=(x\bmod m)+\lfloor x/m\rfloor m`에 따라 원래 번호를 복원한다.
이때 번호 $`x`가 존재하면 $`mn>0`이므로 $`m>0`과 $`n>0`을 사용할 수 있다.
한쪽이 $`0`이면 `Fin (m * n)`과 `Fin m × Fin n` 모두 원소가 없다.

*보기* `Fin (m * n)`에서 `Fin m × Fin n`으로 가는 전단사를 구성하자.
아래 함수는 번호 $`x`를 나머지와 몫으로 나누며 각 범위 조건은 `arith`로 확인한다.

```savedLean
def finProduct (m n : Nat) (x : Fin (m * n)) :
    Fin m × Fin n :=
  ({ val := x.val % m, isLt := by
       by_cases hm : 0 < m
       · arith
       · arith },
   { val := x.val / m, isLt := by
       by_cases hn : 0 < n
       · arith
       · arith })

theorem finProduct_bijective (m n : Nat) :
    Bijective (finProduct m n) := by
  constructor
  · intro x y hxy
    -- 같은 나머지와 몫에서 원래 번호의 같음을 얻는다.
    indisc : 2 at hxy
    arith

  · intro y
    by_cases hpos : 0 < m ∧ 0 < n
    -- 번호 쌍 (i, j)에 i + jm을 대응시킨다.
    · exists ({ val := y.1.val + y.2.val * m,
                isLt := by arith } : Fin (m * n))

      ext : 2
      · expand
        arith

      · expand
        arith

    · arith
```

단사성에서는 두 순서쌍이 같다는 가정에서 나머지와 몫의 등식을 얻는다.
몫과 나머지가 모두 같으면 원래 번호도 같으므로 `arith`로 마친다.
전사성에서는 $`(i,j)`에 대응하는 번호 $`i+jm`을 제시한 뒤
`ext`로 나머지와 몫을 각각 비교한다.
한쪽 범위가 $`0`이면 주어진 순서쌍의 해당 성분이 존재할 수 없으므로 마지막 경우에는 모순을 얻는다.

이 전단사와 {ref "functions-product-maps"}[집합의 곱과 함수]의
`productMap_bijective`를 합성하면 임의의 두 유한집합의 곱을 셀 수 있다.
이 연결은 다음 연습문제에서 증명한다.

## 연습문제: 유한집합의 곱
%%%
tag := "cardinality-exercises"
file := "exercises"
%%%

각 문제의 `sorry`를 증명으로 바꾸어 완성하라.

*문제 7* 유한집합 $`A`, $`B`의 원소 수가 각각 $`m`, $`n`이면
집합의 곱 $`A\times B`의 원소 수가 $`mn`임을 증명하라.
즉 $`|A\times B|=|A||B|`이다.
앞에서 증명한 `productMap_bijective`를 사용하여 `Fin m × Fin n`에서 `A × B`로 가는 전단사를 구성하라.

```savedLean -keep
theorem exercise_cardinal_product {A B : Type} {m n : Nat}
    (hA : cardinal A = m)
    (hB : cardinal B = n) :
    cardinal (A × B) = m * n := by
  sorry
```

*힌트* `finProduct_bijective`와 `productMap_bijective`를 합성하라. 기수의 등식에서 전단사를 꺼낼 때는 함수의 방향을 확인하라.

*문제 8* (색과 번호의 조합)

(1) 두 성분을 바꾸는 함수를 사용하여 $`|A\times B|=|B\times A|`임을 증명하라.

(2) 두 가지 색 중 하나와 세 가지 번호 중 하나를 고르는 방법이 모두 여섯 가지임을 보이라.
색과 번호를 각각 `Fin 2`, `Fin 3`으로 나타낸다.

(3) 앞의 두 결과를 사용하여 번호와 색의 순서로 나열해도 조합의 수는 같음을 보이라.

```savedLean -keep
theorem exercise_cardinal_swap (A B : Type) :
    cardinal (A × B) = cardinal (B × A) := by
  sorry

theorem exercise_two_by_three_cardinal :
    cardinal (Fin 2 × Fin 3) = 6 := by
  sorry

theorem exercise_three_by_two_cardinal :
    cardinal (Fin 3 × Fin 2) = 6 := by
  sorry
```

# 무한집합
%%%
tag := "cardinality-infinite-sets"
file := "infinite-sets"
%%%

유한집합의 원소는 어떤 자연수 $`n`을 택하여 $`n`개의 번호로 정확히 셀 수 있다.
어느 자연수를 택해도 이러한 번호 붙이기가 불가능한 경우를 다음과 같이 정의한다.

*정의* 유한집합이 아닌 집합을 *무한집합*이라고 한다.

```savedLean
def IsInfinite : Type → Prop := fun A => ¬ IsFinite A
```

자연수 전체가 무한함을 보이기 위해
먼저 자연수에서 유한한 번호 집합으로 가는 함수가 단사일 수 없음을 보이자.

*정리* 자연수에서 `Fin n`으로 가는 단사함수는 존재하지 않는다.

*증명* 그러한 함수가 있다고 가정하고 자연수 중 $`0,1,\ldots,n`에서의 값만 보자.
정의역을 이 원소들로 제한해도 단사이므로 `Fin (n + 1)`에서 `Fin n`으로 가는 단사를 얻는다.
비둘기집 원리에 따라 $`n+1\leq n`이 되어 모순이다.

```savedLean
theorem no_injection_nat_fin (n : Nat) (f : Nat → Fin n) :
    ¬ Injective f := by
  intro hf
  -- 처음 n + 1개의 자연수에 정의역을 제한한다.
  let g (i : Fin (n + 1)) : Fin n := f i.val
  have hg : Injective g := by
    intro i j hij
    ext
    exact hf i.val j.val hij

  -- 비둘기집 원리에서 n + 1 ≤ n이라는 모순을 얻는다.
  have hbound : n + 1 ≤ n :=
    fin_injective_le g hg
  arith
```

여기서 `g`는 `Fin (n + 1)`의 번호를 자연수 값으로 꺼내 `f`에 넣는 함수이다.
`hf`로 두 자연수 값이 같음을 얻은 뒤 `ext`를 사용하면 `g`의 단사성을 확인할 수 있다.

{anchor "cardinality-natural-injection"}[]*정리* 자연수에서 $`A`로 가는 단사함수가 존재하면 $`A`는 무한집합이다.

*증명* $`A`가 유한하다고 가정하자.
그러면 어떤 자연수 $`n`에 대하여 전단사 $`r:A\to\operatorname{Fin}(n)`가 존재한다.
주어진 단사함수 $`f : \mathbb{N}\to A`에 $`r`을 합성하면 자연수에서 `Fin n`으로 가는 단사가 되어 모순이다.

유한성의 가정은 `∃ n : Nat, cardinal A = n`이므로 먼저 번호 수와 기수의 등식을 꺼낸다.
이 등식에 `cardinal_eq_iff`를 사용하면 `A`에서 `Fin n`으로 가는 전단사의 존재를 얻으므로
다시 `unpack`으로 함수와 전단사성의 증명을 꺼낼 수 있다.

```savedLean
theorem infinite_of_nat_injection {A : Type} (f : Nat → A)
    (hf : Injective f) :
    IsInfinite A := by
  intro hA
  -- A가 유한하다고 가정하여 유한한 번호를 붙인다.
  unpack hA with ⟨n, hn⟩
  unpack (cardinal_eq_iff A (Fin n)).mp hn with ⟨r, hr⟩

  -- 두 단사함수를 합성하면 Nat에서 Fin n으로 가는 단사이다.
  apply no_injection_nat_fin n (r ∘ f)
  exact injective_compose f r hf hr.inj
```

자연수의 항등함수에 이 정리를 사용하면 자연수 전체가 무한집합임을 얻는다.

```savedLean
theorem nat_isInfinite : IsInfinite Nat := by
  exact infinite_of_nat_injection
    (identity Nat) (identity_injective Nat)
```

기수가 같은 두 집합 중 하나가 무한하면 다른 하나도 무한하다.
다른 쪽이 유한하다고 가정하면 방금 증명한 유한성의 전달로 모순을 얻는다.

```savedLean
theorem isInfinite_transport {A B : Type}
    (hAB : cardinal A = cardinal B)
    (hA : IsInfinite A) :
    IsInfinite B := by
  intro hB
  apply hA
  exact isFinite_transport hAB.symm hB
```

## 연습문제: 무한성의 전달

*문제 9* 무한집합과 크기가 같은 집합도 무한집합임을 증명하라.
이 문제에서는 유한성의 정의를 펼쳐 번호 수를 꺼낸 뒤,
앞의 `cardinality_finite_transport`로 그 번호를 다른 집합에 옮겨 모순을 얻으라.

```savedLean -keep
theorem exercise_infinite_transport {A B : Type}
    (hA : IsInfinite A)
    (hAB : cardinal A = cardinal B) :
    IsInfinite B := by
  sorry
```

```savedLean -show
end Ample
```

```savedLean -show
export_course_compat
```

{anchor "infinite-cardinality"}[]

```savedLean -show
open scoped Classical
```

```savedLean -show
namespace Ample
local infixr:90 (priority := high) " ∘ " => compose
```

*문제 10* (순서쌍 집합의 무한성)

자연수의 순서쌍 전체가 무한집합임을 증명하라.
자연수에서 오는 단사함수를 하나 구성하여 `infinite_of_nat_injection`을 사용하라.
선택한 함수가 전사일 필요가 없는 이유도 설명하라.

```savedLean -keep
theorem exercise_nat_pairs_infinite :
    IsInfinite (Nat × Nat) := by
  sorry
```

# 기수의 대소 관계
%%%
tag := "cardinality-comparison"
file := "comparison"
%%%

*정의* $`A`에서 $`B`로 가는 단사함수가 존재하면 $`|A|\leq|B|`로 쓴다.
이 관계가 성립하고 두 기수가 같지 않으면 $`|A|<|B|`로 쓴다.

Lean에서도 `cardinal A ≤ cardinal B`를 사용하며, 이 부등식은 `A`에서 `B`로 가는 단사의 존재와 연결된다.
아래에서는 단사의 존재를 술어로 정의한 뒤 대표원을 바꾸어도 이 조건이 유지됨을 확인한다.

```savedLean
def CardinalityLE : Type → Type → Prop :=
  fun A B => ∃ f : A → B, Injective f
```

```savedLean -show
def CardinalityLT : Type → Type → Prop :=
  fun A B => CardinalityLE A B ∧ ¬ SameCardinality A B
```

기수는 같은 크기의 타입들을 묶은 동치류이므로 기수의 부등식도 대표원으로 택한 타입에 의존하지 않아야 한다.
$`A`와 $`A'`, $`B`와 $`B'`의 크기가 각각 같고 단사함수 $`f:A\to B`가 있다고 하자.
전단사 $`a:A\to A'`의 역함수와 전단사 $`b:B\to B'`를 사용하면
$`b\circ f\circ a^{-1}:A'\to B'`도 단사이다.

```savedLean
theorem cardinalityLE_transport {A B : Type} {A' B' : Type}
    (hA : SameCardinality A A')
    (hB : SameCardinality B B')
    (h : CardinalityLE A B) :
    CardinalityLE A' B' := by
  unpack hA with ⟨a, ha⟩
  unpack hB with ⟨b, hb⟩
  unpack h with ⟨f, hf⟩

  -- 먼저 A'에서 A를 거쳐 B로 가는 단사를 얻는다.
  have hFirst : Injective (f ∘ inverseMap a ha) := by
    apply injective_compose
    · exact (inverseMap_bijective a ha).inj
    · exact hf

  -- B에서 B'로 가는 전단사를 이어 붙인다.
  exists b ∘ f ∘ inverseMap a ha
  exact injective_compose _ _ hFirst hb.inj
```

역방향은 두 전단사의 방향을 바꾸어 같은 정리를 사용하면 된다.
따라서 단사의 존재 여부는 대표원을 바꾸어도 달라지지 않는다.

이제 기수 `a`, `b`에 대하여, 각 동치류에 속하는 타입 `A`, `B`와 그 사이의 단사가 존재한다는 조건으로 `a ≤ b`를 정의하자.
`A ∈ a.val`과 `B ∈ b.val`은 각각 그 타입이 해당 동치류에 속한다는 조건이다.

```savedLean -show
namespace Cardinal
```

```savedLean
def le : Cardinal → Cardinal → Prop :=
  fun a b => ∃ A B : Type,
    A ∈ a.val ∧ B ∈ b.val ∧ CardinalityLE A B
```

`a ≤ b`는 이 조건이며, `a < b`는 `a ≤ b`이면서 두 기수가 다르다는 뜻이다.

```savedLean -show
instance : LE Cardinal := ⟨le⟩
instance : LT Cardinal := ⟨fun a b => a ≤ b ∧ a ≠ b⟩

end Cardinal
```

`cardinal A ≤ cardinal B`를 보일 때는 다음 정리의 `.mpr`로 단사가 존재한다는 목표를 얻고 함수를 제시한다.
가정의 부등식에서 단사를 꺼낼 때는 `.mp`를 사용한다.

```savedLean
theorem cardinal_le_iff (A B : Type) :
    cardinal A ≤ cardinal B ↔ ∃ f : A → B, Injective f := by
  constructor
  · intro h
    rcases h with ⟨A', B', hA, hB, hf⟩
    exact cardinalityLE_transport hA hB hf

  · intro hf
    exists A, B
    and_intros
    · exact sameCardinality_refl A
    · exact sameCardinality_refl B
    · exact hf

theorem cardinal_lt_iff (a b : Cardinal) :
    a < b ↔ a ≤ b ∧ a ≠ b := by
  rfl
```

첫 번째 방향에서는 `≤`의 정의에 따라 대표원 `A'`, `B'`와 세 조건을 꺼낸다.
`hA : A' ∈ (cardinal A).val`은 `SameCardinality A' A`의 증명이며 `hB`도 같은 역할을 한다.
따라서 앞의 정리로 단사를 원래 타입 `A`, `B` 사이로 옮길 수 있다.
반대 방향에서는 `A`, `B` 자체를 대표원으로 택하므로 각 동치류에 속한다는 조건은 반사성으로 증명한다.

기수의 등식에 전단사를 사용했던 것과 같이 부등식에는 단사를 사용한다.

*정리* 모든 기수는 자기 자신보다 작거나 같으며
$`|A|\leq|B|`, $`|B|\leq|C|`이면 $`|A|\leq|C|`이다.

*증명* 첫 명제에는 항등함수를 사용하고 둘째 명제에는 두 단사함수의 합성을 사용한다.
가정의 부등식에 `cardinal_le_iff`의 `.mp`를 적용하면 단사의 존재를 얻으므로
함수와 단사성의 증명을 `unpack`으로 꺼낼 수 있다.

```savedLean
theorem cardinal_le_refl (A : Type) :
    cardinal A ≤ cardinal A := by
  apply (cardinal_le_iff A A).mpr
  exists identity A
  exact identity_injective A

theorem cardinal_le_trans {A B C : Type}
    (hAB : cardinal A ≤ cardinal B)
    (hBC : cardinal B ≤ cardinal C) :
    cardinal A ≤ cardinal C := by
  unpack (cardinal_le_iff A B).mp hAB with ⟨f, hf⟩
  unpack (cardinal_le_iff B C).mp hBC with ⟨g, hg⟩

  -- 두 단사함수를 합성하여 크기의 비교를 연결한다.
  apply (cardinal_le_iff A C).mpr
  exists g ∘ f
  exact injective_compose f g hf hg
```

```savedLean -show
namespace Cardinal

theorem le_refl (a : Cardinal) : a ≤ a := by
  unpack (quotient_exists_classOf SameCardinality a) with ⟨A, hA⟩
  rw [hA]
  exact cardinal_le_refl A

theorem le_trans {a b c : Cardinal}
    (hAB : a ≤ b) (hBC : b ≤ c) : a ≤ c := by
  unpack (quotient_exists_classOf SameCardinality a) with ⟨A, hA⟩
  unpack (quotient_exists_classOf SameCardinality b) with ⟨B, hB⟩
  unpack (quotient_exists_classOf SameCardinality c) with ⟨C, hC⟩
  rw [hA, hB] at hAB
  rw [hB, hC] at hBC
  rw [hA, hC]
  exact cardinal_le_trans hAB hBC

theorem le_of_eq {a b : Cardinal} (h : a = b) : a ≤ b := by
  rw [← h]
  exact le_refl a

end Cardinal
```

단사함수에 의한 이 비교를 자연수와 같은 크기의 집합 및 멱집합에 적용하자.

# 자연수와 같은 크기의 집합
%%%
tag := "cardinality-countable-sets"
file := "countable-sets"
%%%

양의 자연수의 집합은 자연수 전체에서 $`0`을 뺀 집합이다.
자연수 $`n`을 양의 자연수 $`n+1`에 대응시키면
$`0,1,2,\ldots`와 $`1,2,3,\ldots`를 빠짐없이 짝지을 수 있다.
이 함수가 전단사임을 보여 두 집합의 크기를 비교하자.

```savedLean
def toPositive (n : Nat) : Elem positives :=
  { val := n + 1, property := by arith }
```

`val := n + 1`로 함수값을 정하고 `property`에서 그 수가 `positives`에 속함을 증명한다.
`arith`는 이 원소 조건을 `0 < n + 1`로 정리하여 부등식을 확인한다.

$`x+1=y+1`이면 $`x=y`이므로 이 함수는 단사이다.
또한 양의 자연수 $`y`에 대하여 $`y-1`을 택하면
$`(y-1)+1=y`이므로 전사이다.

```savedLean
theorem toPositive_bijective : Bijective toPositive := by
  constructor
  · intro x y hxy
    -- 함수값이 같으면 x + 1 = y + 1이다.
    expand at hxy
    indisc at hxy
    arith

  · intro y
    -- 양의 자연수 y에 대응하는 번호는 y - 1이다.
    exists (y.val - 1)
    ext
    have hy :=
      y.property
    -- y > 0이므로 뺀 1을 다시 더하면 y를 얻는다.
    arith
```

단사성에서는 `expand at hxy`로 함수값을 펼치고
`indisc at hxy`로 $`x+1=y+1`을 얻는다.
이 등식에서 공통 항을 소거하면 $`x=y`이므로 `arith`로 증명을 마친다.
전사성에서는 `y.val - 1`을 택하고 `ext`로 값을 비교하면
목표를 `y.val - 1 + 1 = y.val`로 바꾼다.
`have hy := y.property`로 양수라는 조건을 가정에 넣으면
`arith`가 이를 `0 < y.val`로 정리하여 자연수의 뺄셈에서 $`(y-1)+1=y`임을 확인한다.

이 전단사에 따라 자연수 전체와 양의 자연수의 집합은 크기가 같다.
양의 자연수의 집합은 자연수 전체에서 $`0`을 뺀 것이므로
무한집합은 일부 원소를 제외한 부분집합과도 크기가 같을 수 있다.

*정의* 자연수 전체와 크기가 같은 집합을 *가산무한집합*이라고 한다.
자연수의 기수를 $`\aleph_0`로 나타내므로 가산무한집합 $`A`에 대하여 $`|A|=\aleph_0`로 쓴다.

기호 $`\aleph_0`는 `\aleph0`로 입력한다.

```savedLean
def IsCountablyInfinite : Type → Prop :=
  fun A => cardinal Nat = cardinal A
```

`IsCountablyInfinite A`는 $`\aleph_0=|A|`라는 기수의 등식이다.
이 등식에서 전단사 $`f : \mathbb{N}\to A`의 존재를 얻는다.
이 함수는 단사이기도 하므로 앞의 `infinite_of_nat_injection`에 따라 $`A`는 무한집합이다.
한편 양의 자연수의 집합이 가산무한이라는 사실은
자연수에서 오는 전단사 `toPositive`를 제시하여 증명한다.

```savedLean
theorem countablyInfinite_isInfinite {A : Type}
    (hA : IsCountablyInfinite A) :
    IsInfinite A := by
  unpack (cardinal_eq_iff Nat A).mp hA with ⟨f, hf⟩
  exact infinite_of_nat_injection f hf.inj

theorem positives_countablyInfinite :
    IsCountablyInfinite (Elem positives) := by
  ext
  exists toPositive
  exact toPositive_bijective
```

*보기* 짝수 집합도 가산무한집합이다.
{ref "functions-element-equality"}[함수 절]에서 자연수 $`n`을 짝수 $`2n`에 대응시키는
`doubleToEvens`가 전단사임을 증명했다.
이 전단사를 제시하여 자연수와 짝수 집합의 기수가 같음을 보이자.

```savedLean
theorem evens_countablyInfinite :
    IsCountablyInfinite (Elem evens) := by
  ext
  exists doubleToEvens
  exact doubleToEvens_bijective

example : IsInfinite (Elem evens) := by
  exact countablyInfinite_isInfinite evens_countablyInfinite
```

첫 정리는 자연수와 짝수 집합 사이의 전단사를 제시하고,
둘째 증명은 가산무한집합의 무한성을 앞의 일반 정리에서 얻는다.
양의 자연수의 집합과 짝수 집합도 모두 자연수와 크기가 같으므로 서로 크기가 같다.

```savedLean
example :
    cardinal (Elem evens) = cardinal (Elem positives) := by
  rw [← evens_countablyInfinite,
    ← positives_countablyInfinite]
```

두 정리를 등식으로 읽으면 각각 `cardinal Nat = cardinal (Elem evens)`와
`cardinal Nat = cardinal (Elem positives)`이다.
이들을 반대 방향으로 사용하여 양변을 `cardinal Nat`로 바꾸면 원하는 등식을 얻는다.

## 연습문제: 자연수의 꼬리
%%%
tag := "cardinality-countable-practice"
%%%

양의 자연수에 사용한 대응을 바꾸어 다음 집합의 크기를 확인해 보자.

*문제 11* $`\{n\in\mathbb{N}:2\leq n\}`이 가산무한집합임을 증명하라.

```savedLean -keep
theorem exercise_from_two_countably_infinite {n : Nat} :
    IsCountablyInfinite
    (Elem (fun n : Nat => 2 ≤ n)) := by
  sorry
```

*문제 12* (등차수열과 가산무한집합)

집합 $`S=\{1,4,7,10,\ldots\}`을 $`3k+1` 꼴의 자연수로 정의한다.

(1) 아래 함수가 자연수에서 $`S`의 원소 타입으로 가는 전단사임을 증명하라.

(2) 첫 결과로 $`S`가 가산무한집합임을 보이라.

(3) $`S`가 자연수 전체와 같은 집합은 아님을 보이라.
집합의 같음과 크기의 같음을 구별하라.

```savedLean -keep
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
```

## 가장 작은 무한기수
%%%
tag := "cardinality-infinite-converse"
%%%

{anchor "cardinality-least-infinite"}[]자연수에서 집합 $`A`로 가는 단사가 있으면 $`A`가 무한임을 앞에서 보였다.
선택공리를 사용하면 그 역도 성립한다. 이미 고른 원소가 유한 개일 때
무한집합에는 아직 고르지 않은 원소가 있으므로, 서로 다른 원소를 하나씩 골라
$`a_0,a_1,\ldots`로 나열한다. 서로 다른 번호에는 다른 원소를 골랐으므로
$`n\mapsto a_n`은 자연수에서 $`A`로 가는 단사이다.

한 단계에서 새 원소가 존재한다는 사실과 모든 단계의 선택을 하나의 함수로 구성하는 것은 구별된다.
후자의 구성을 여기서는 선택공리에 의존하여 수행한다.
따라서 단사함수의 존재로 크기를 비교할 때 자연수 집합은 가장 작은 무한집합이며,
그 기수 $`\aleph_0`는 가장 작은 무한기수이다.

# 멱집합과 칸토어 정리
%%%
tag := "cardinality-power-sets"
file := "power-sets"
%%%

자연수와 양의 자연수처럼 무한집합은 자신의 진부분집합과도 크기가 같을 수 있다.
그렇다면 모든 무한집합의 크기가 같을까?
이 절에서는 부분집합들을 원소로 모은 멱집합을 정의하고
원래 집합보다 크기가 커진다는 칸토어 정리를 증명한다.

{anchor "cardinality-power-set-definition"}[]*정의* 집합 $`S`의 모든 부분집합으로 이루어진 집합을 $`S`의 *멱집합*이라고 하고 $`\mathcal{P}(S)`로 쓴다.
즉 $`T\in\mathcal{P}(S)`이라는 것은 $`T\subseteq S`라는 뜻이다.

```savedLean
def powerSet {A : Type} (S : Set A) : Set (Set A) :=
  fun T => T ⊆ S
```

`S`의 원소는 `A`의 원소이고 멱집합의 원소는 `A` 위의 집합이므로
`powerSet S`의 타입은 `Set (Set A)`이다.
예를 들어 $`S=\{a,b\}`이고 $`a\ne b`이면
$`\mathcal{P}(S)=\{\varnothing,\{a\},\{b\},\{a,b\}\}`이다.
공집합도 부분집합이므로 멱집합의 원소에 포함된다.

*보기* 모든 집합 $`S`에 대하여 $`\varnothing\in\mathcal{P}(S)`이고 $`S\in\mathcal{P}(S)`이다.

```savedLean
example {A : Type}
    (S : Set A) :
    (∅ : Set A) ∈ powerSet S := by
  exact empty_subset S

example {A : Type}
    (S : Set A) :
    S ∈ powerSet S := by
  exact subset_refl S
```

첫 목표는 공집합이 `S`의 부분집합이라는 명제이고
둘째 목표는 `S`가 자신의 부분집합이라는 명제이다.
따라서 집합 절에서 증명한 `empty_subset`과 `subset_refl`을 그대로 사용할 수 있다.

*문제 13* $`\mathcal{P}(S\cap T)=\mathcal{P}(S)\cap\mathcal{P}(T)`임을 증명하라.

```savedLean -keep
theorem exercise_powerSet_inter {A : Type} (S T : Set A) :
    powerSet (S ∩ T) = powerSet S ∩ powerSet T := by
  sorry
```

원소 타입 `A` 전체의 멱집합을 다룰 때는 `Set A`를 사용한다.
모든 `T : Set A`가 `whole A`의 부분집합이므로
`Set A`의 원소들이 바로 전체집합의 부분집합들이다.

```savedLean
example {A : Type}
    (T : Set A) :
    T ∈ powerSet (whole A) := by
  exact subset_whole T
```

{anchor "cardinality-singleton-injection"}[]멱집합과 원래 집합의 크기를 비교하려면 먼저 단사함수를 하나 찾으면 된다.
각 원소를 그 원소만으로 이루어진 부분집합에 대응시키자.

*보기* 원소 $`a`를 한 원소 집합 $`\{a\}`에 대응시키면
$`A`에서 그 멱집합으로 가는 단사함수를 얻는다.
$`\{a\}=\{b\}`이면 $`a\in\{b\}`이므로 $`a=b`이다.

```savedLean
theorem singleton_injective {A : Type} :
    Injective (singleton : A → Set A) := by
  intro a b hab
  have ha : a ∈ singleton a := by rfl
  rw [hab] at ha
  exact ha

theorem cardinal_le_powerSet (A : Type) :
    cardinal A ≤ cardinal (Set A) := by
  apply (cardinal_le_iff A (Set A)).mpr
  exists singleton
  exact singleton_injective
```

`singleton`의 단사성을 보일 때는 원소 `a`가 자신의 한 원소 집합에 속한다는 사실을 사용한다.
`rw [hab] at ha`로 그 집합을 `singleton b`로 바꾸면 `ha`는 `a = b`의 증명이 된다.
이 단사함수를 제시하면 멱집합과의 기수 부등식을 얻는다.

```savedLean -show
theorem cardinality_le_powerSet (A : Type) :
    CardinalityLE A (Set A) := by
  exact (cardinal_le_iff A (Set A)).mp (cardinal_le_powerSet A)
```

정리 `cardinal_le_powerSet`으로 $`|A|\leq|\mathcal{P}(A)|`를 얻었다.
이제 $`|A|<|\mathcal{P}(A)|`를 보이려면 두 기수가 다름을 증명하면 된다.
이를 위해 $`A`에서 멱집합으로 가는 전사함수가 없음을 보이자.

## 칸토어 정리
%%%
tag := "cardinality-cantor"
%%%

*정리* 어떤 집합 $`A`에 대하여도
$`A`에서 $`\mathcal{P}(A)`로 가는 전사함수는 존재하지 않는다.
따라서 $`|A|<|\mathcal{P}(A)|`이다.

*증명* 함수 $`f:A\to\mathcal{P}(A)`가 주어졌다고 하자.
이 함수가 전사가 아님을 보이려면 모든 함수값 $`f(x)`와 다른 집합 $`D`를 찾으면 된다.
각 원소 $`x`에 대하여 $`x\in f(x)`이면 $`D`에서 제외하고, $`x\notin f(x)`이면 $`D`에 넣자.
그러면 $`D`와 $`f(x)`는 원소 $`x`가 속하는지에서 다르다.
이에 따라 다음 집합을 정의하자.

$$`D=\{x\in A:x\notin f(x)\}.`

$`f`가 전사라면 $`f(a)=D`인 원소 $`a`가 존재한다.
이 원소가 $`D`에 속하는지 살펴보자.

먼저 $`a\in D`라고 가정하면 정의에 따라 $`a\notin f(a)`이다.
여기에 $`f(a)=D`를 대입하면 $`a\notin D`를 얻어 가정과 모순이므로 $`a\notin D`이다.

그러면 $`f(a)=D`에 따라 $`a\notin f(a)`이며,
이는 $`D`의 원소 조건이므로 $`a\in D`를 얻는다.
다시 모순이 생겼으므로 $`f`는 전사일 수 없으며 전단사도 존재하지 않는다.

이 증명은 각 $`x`에서 $`x\in f(x)`인지를 보고
그 조건을 뒤집어 $`D`를 만든다.
이를 원소 관계의 표로 생각할 수 있다.
행과 열을 각각 $`A`의 원소로 표시하고 $`(x,y)` 칸에 $`x\in f(y)`인지를 기록하면,
대각선의 $`(x,x)` 칸에는 $`x\in f(x)`인지가 기록된다.
그 칸의 조건을 모두 뒤집어 새 집합을 만드는 데서 *대각선 논법*이라는 이름이 나온다.

여기서 `f`의 공역은 집합들을 원소로 갖는 타입 `Set A`이다.
따라서 전사성의 가정 `hf`가 증명하는 전칭명제는 `∀ T : Set A, ∃ a, f a = T`이다.
이 증명에 집합 `D`를 넣은 `hf D`는 `∃ a, f a = D`의 증명이므로,
`unpack`으로 원소 `a`와 등식 `ha`를 꺼낼 수 있다.

```savedLean
theorem cantor_not_surjective {A : Type} (f : A → Set A) :
    ¬ Surjective f := by
  intro hf
  let D : Set A := fun x => x ∉ f x
  unpack hf D with ⟨a, ha⟩

  -- a ∈ D이면 원소 조건과 모순이다.
  have hnot : a ∉ D := by
    intro hmem
    apply hmem
    rw [ha]
    exact hmem

  -- a ∉ D에서 다시 a ∈ D를 얻는다.
  have hmem : a ∈ D := by
    expand
    rw [ha]
    exact hnot

  exact hnot hmem
```

첫 `have`에서 `hmem : a ∈ D`의 원소 조건은 `a ∉ f a`이다.
따라서 `apply hmem`을 쓰면 모순을 보이는 목표 `False`가 `a ∈ f a`로 바뀐다.
`ha : f a = D`를 대입하면 `a ∈ D`가 되어 원래 가정으로 증명할 수 있다.

둘째 `have`에서는 `expand`로 `D`의 원소 조건을 펼친 뒤 같은 등식을 대입한다.
이때 목표는 `a ∉ D`이므로 앞에서 얻은 `hnot`으로 마친다.
최종적으로 `hnot : a ∉ D`와 `hmem : a ∈ D`를 함께 사용하여 모순을 얻는다.

이제 전단사가 존재한다고 가정하면 그 전사성이 방금 증명한 정리와 모순이므로
멱집합과 원래 집합의 크기가 같을 수 없다.

```savedLean
theorem powerSet_not_sameCardinality (A : Type) :
    ¬ SameCardinality A (Set A) := by
  intro h
  unpack h with ⟨f, hf⟩
  exact cantor_not_surjective f hf.surj

```

```savedLean -show
theorem cardinality_lt_powerSet (A : Type) :
    CardinalityLT A (Set A) := by
  constructor
  · exact cardinality_le_powerSet A
  · exact powerSet_not_sameCardinality A

```

```savedLean
theorem cardinal_ne_powerSet (A : Type) :
    cardinal A ≠ cardinal (Set A) := by
  intro h
  apply powerSet_not_sameCardinality A
  exact (cardinal_eq_iff A (Set A)).mp h

theorem cardinal_lt_powerSet (A : Type) :
    cardinal A < cardinal (Set A) := by
  constructor
  · exact cardinal_le_powerSet A
  · exact cardinal_ne_powerSet A
```

*보기* 자연수 $`n`에 집합 $`\{0,\ldots,n-1\}`을 대응시키자.
$`n=0`일 때는 공집합을 얻으며, 이후의 함수값은 $`\{0\}`, $`\{0,1\}`, $`\{0,1,2\}`, $`\ldots`이다.
이 대응에 대각선 논법을 적용하면 어떤 집합이 빠져 있음을 알 수 있을까?

```savedLean
def initialSegment (n : Nat) : Set Nat := fun k => k < n
def initialSegmentDiagonal : Set Nat :=
  fun n => n ∉ initialSegment n
```

자연수 $`n`은 $`n`보다 작은 수들의 집합에 속하지 않는다.
따라서 모든 자연수가 대각선 집합에 속하며 이 집합은 자연수 전체이다.

```savedLean
theorem initialSegment_diagonal :
    initialSegmentDiagonal = whole Nat := by
  ext n
  constructor
  · intro hn
    trivial

  · intro hn
    expand
    expand
    arith
```

역방향에서 두 정의를 차례로 펼치면 `¬ n < n`이 남는다.
이것이 모든 자연수에서 성립하므로 대각선 집합은 전체집합이다.
어느 `initialSegment n`도 $`n`을 포함하지 못하므로 전체집합과 같을 수 없다.
전사함수가 없다는 결론은 앞의 칸토어 정리에 이 함수를 넣어 얻을 수도 있다.

```savedLean
example : ¬ Surjective initialSegment := by
  exact cantor_not_surjective initialSegment
```

이 예제의 대각선 집합은 자연수 전체이다.
다른 함수에서 출발하면 다른 대각선 집합을 얻을 수 있지만, 어느 경우에도 그 집합은 해당 함수의 상에 속하지 않는다.

*보기* 자연수의 멱집합은 무한집합이며 가산무한집합이 아니다.
한 원소 집합을 만드는 단사함수로 무한성을 얻으며
자연수와 크기가 같다고 가정하면 칸토어 정리와 모순이다.

```savedLean
theorem nat_powerSet_isInfinite :
    IsInfinite (Set Nat) := by
  exact infinite_of_nat_injection
    singleton singleton_injective

theorem nat_powerSet_not_countablyInfinite :
    ¬ IsCountablyInfinite (Set Nat) := by
  exact cardinal_ne_powerSet Nat
```

자연수에서 시작하여 멱집합을 거듭 만들면 다음과 같이 크기가 커진다.

$$`|\mathbb{N}|<|\mathcal{P}(\mathbb{N})|<|\mathcal{P}(\mathcal{P}(\mathbb{N}))|<\cdots.`

이처럼 무한집합 사이에서도 크기의 차이가 생긴다.

# 연습문제
%%%
tag := "infinite-cardinality-exercises"
file := "exercises"
%%%

각 문제의 `sorry`를 증명으로 바꾸어 완성하라.

*문제 14* (멱집합의 포함 관계)

(1) $`S\subseteq T`이면 $`\mathcal{P}(S)\subseteq\mathcal{P}(T)`임을 증명하라.

(2) 반대 방향도 증명하여 이 두 포함 관계가 동치임을 보이라.

(3) 첫 결과와 `twoThree_subset_positives`를 사용하여
$`\mathcal{P}(\{2,3\})\subseteq\mathcal{P}(\mathbb{N}_{>0})`임을 보이라.

```savedLean -keep
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
```

*문제 15* (한 원소 집합들을 나열한 경우)

$`f(n)=\{n\}`으로 부분집합들을 나열하자.

(1) 이 나열의 대각선 집합 $`D=\{n:n\notin f(n)\}`이 공집합임을 보이라.

(2) 공집합이 이 함수의 상에 속하지 않음을 직접 증명하라.

(3) 둘째 결과로 이 함수가 전사가 아님을 보이라.

```savedLean -keep
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
```

# 크기 비교의 자동화
%%%
tag := "infinite-cardinality-automation"
%%%

{anchor "cardinality-automation"}[]{anchor "cardinality-finiteness-transport"}[]
전술 `card`는 앞에서 증명한 기수의 등식·부등식과 유한성·무한성의 성질을 연결한다.
예를 들어 두 크기 부등식을 이어 붙일 때는 추이성을 직접 적용하는 대신 사용할 수 있다.
새로운 단사나 전단사를 구성하는 문제에서는 먼저 함수를 제시해야 한다.

```savedLean -show
attribute [ample_card_rules]
  sameCardinality_refl sameCardinality_symm sameCardinality_trans
  cardinal_eq_of_sameCardinality sameCardinality_of_cardinal_eq
  Cardinal.eq_symm Cardinal.eq_trans
  cardinal_fin fin_isFinite empty_cardinal singleton_cardinal
  threeNumbers_cardinal finite_cardinal_unique
  fin_sameCardinality_eq cardinal_fin_eq cardinality_spec cardinality_eq
  isFinite_of_cardinal_eq isFinite_transport isInfinite_transport
  nat_isInfinite
```

```savedLean -show
attribute [ample_card_rules]
  Cardinal.le_refl Cardinal.le_trans Cardinal.le_of_eq
  countablyInfinite_isInfinite positives_countablyInfinite
  cardinal_le_powerSet cardinal_ne_powerSet cardinal_lt_powerSet
```

*보기* $`|A|\leq|B|`이고 $`|B|\leq|C|`이면 $`|A|\leq|C|`이다.

```savedLean
theorem infinite_card_comparison {A B C : Type}
    (hAB : cardinal A ≤ cardinal B)
    (hBC : cardinal B ≤ cardinal C) :
    cardinal A ≤ cardinal C := by
  card
```

```savedLean -show
end Ample
```

```savedLean -show
export_course_compat
```
