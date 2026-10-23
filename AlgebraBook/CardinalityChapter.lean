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

어느 반의 학생 수와 의자 수가 같은지 확인하려면 학생마다 의자를 하나씩 짝지어 볼 수 있다.
겹치거나 남는 것이 없으면 두 수는 같다. 앞에서 배운 전단사는 이러한 짝짓기를 함수로 나타낸 것이다.
이 장에서는 전단사로 집합의 크기를 정의하고, 번호를 붙여 센 원소 수가 하나로 정해지는 이유를 증명한다.
이어 집합의 합·곱과 함수 공간의 크기를 계산하고, 원소를 유한하게 셀 수 없는 집합들의 크기도 비교하자.

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

# 기수
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

예를 들어 {ref "functions-element-equality"}[집합 위의 함수]에서 증명한
`doubleToEvens_bijective`는 자연수와 짝수 집합을 짝짓는 전단사이다.
따라서 다음과 같이 두 집합의 크기가 같음을 보일 수 있다.

```lean
example : SameCardinality Nat (Elem evens) := by
  exists doubleToEvens
  exact doubleToEvens_bijective
```

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
  apply bijective_compose f g
  · exact hf
  · exact hg
```

## 기수와 동치류
%%%
tag := "cardinality-quotient-type"
file := "cardinals"
%%%

앞에서 같은 크기라는 관계가 반사성·대칭성·추이성을 만족함을 보였다.
이 관계에 {ref "preliminaries-quotients"}[몫집합]의 구성을 적용하여 크기가 같은 타입들을 하나의 동치류로 묶자.
각 동치류를 하나의 원소로 갖는 타입을 `Cardinal`이라고 하며,
타입 `A`가 속한 동치류를 `cardinal A`로 나타낸다.

예를 들어 `Nat`와 `Elem positives` 사이에 전단사가 있으면 두 타입은 같은 기수를 갖는다.
기수의 등식은 원래 타입들이 같다는 주장이 아니라 그 원소들을 빠짐없이 짝지을 수 있다는 뜻이다.
먼저 앞의 세 정리를 동치관계의 증명으로 묶고 기수를 정의하자.

```savedLean
theorem sameCardinality_equivalence :
    IsEquivalence SameCardinality := by
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
  apply classOf_eq_iff SameCardinality
  exact sameCardinality_equivalence
```

```savedLean -show
attribute [ample_compare] cardinal_eq_iff
```

앞 장의 `classOf_eq_iff`를 전단사 관계에 적용한 결과이다.
이 정리를 `ext`에 연결했으므로 기수의 등식에 `ext`를 쓰면
`SameCardinality A B`가 새 목표가 된다.
기수의 등식이 가정으로 주어졌을 때는 `cardinal_eq_iff`의 정방향으로 전단사의 존재를 얻는다.

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
  apply (cardinal_eq_iff A B).mp
  exact h
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

theorem eq_symm {a b : Cardinal} (h : a = b) : b = a := by
  symm
  exact h

theorem eq_trans {a b c : Cardinal}
    (hab : a = b) (hbc : b = c) : a = c :=
  hab.trans hbc

end Cardinal
```

# 유한집합
%%%
tag := "cardinality-finite-numbering"
%%%

세는 순서가 달라도 원소 수는 같아야 한다.
먼저 번호를 붙인다는 조건을 Lean으로 표현하고 공집합과 작은 유한집합의 원소를 세어 보자.
서로 다른 방법으로 센 결과가 왜 같은지는 다음 절에서 증명한다.

## 유한한 번호
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

## 번호의 범위와 이동
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

여기서는 자연수 값은 그대로 두고 허용 범위만 넓혔다.
Lean에 준비된 다음 연산들도 범위를 바꾸거나 번호를 이동할 때 사용한다.
표에서 `i : Fin n`이고 `h : n ≤ m`이다.

:::table +header (align := left)
*
  * 표현
  * 타입
  * 자연수 값
*
  * `i.castSucc` (`i : Fin n`)
  * `Fin (n + 1)`
  * `i.val`
*
  * `i.succ` (`i : Fin n`)
  * `Fin (n + 1)`
  * `i.val + 1`
*
  * `i.castLE h` (`h : n ≤ m`)
  * `Fin m`
  * `i.val`
*
  * `Fin.last n`
  * `Fin (n + 1)`
  * `n`
:::

`i.castSucc`는 기존 번호를 더 큰 범위에 넣으며 `i.succ`는 번호 자체를 하나 올린다.
가령 `Fin 3`의 번호 $`1`에서 출발하면 두 결과는 모두 `Fin 4`에 속하지만
자연수 값은 각각 $`1`, $`2`이다. `Fin.last n`은 $`0`부터 $`n`까지의 번호 중 마지막 번호이다.

## 번호 붙이기와 유한성
%%%
tag := "cardinality-finite-sets"
file := "finite-sets"
%%%

{ref "functions-fin"}[유한한 번호]에서 `Fin n`을 자연수 값과 범위 조건으로 구성했다.
이제 각 원소에 번호를 하나씩 붙이는 전단사로 원소 수를 정의하자.

*정의* 집합 $`A`와 번호 집합 $`\{k\in\mathbb{N}:k<n\}` 사이에 전단사가 존재하면
$`A`의 *원소 수가 $`n`*이라고 한다.
그러한 자연수 $`n`이 존재하는 집합을 *유한집합*이라고 한다.

```savedLean
def IsFinite : Type → Prop :=
  fun A => ∃ n : Nat, cardinal A = cardinal (Fin n)
```

원소 수가 $`n`이라는 조건은 `cardinal A = cardinal (Fin n)`으로 쓴다.
이 등식에 `ext`를 쓰면 `A`에서 `Fin n`으로 가는 전단사를 제시하는 목표가 된다.
이는 각 원소에 번호를 붙이는 방향이다.
번호로 원소를 찾아가는 `Fin n → A` 방향의 전단사를 구성해도 역함수로 같은 결론을 얻는다.
이 방향에서는 단사성이 같은 원소를 중복해서 세지 않는다는 뜻이고 전사성이 빠뜨린 원소가 없다는 뜻이다.

`Fin n`에는 항등함수로 번호를 붙일 수 있으므로 원소 수가 $`n`이며 유한하다.

```savedLean
theorem fin_isFinite (n : Nat) : IsFinite (Fin n) := by
  exists n
```

### 공집합과 한 원소 집합
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

{anchor "cardinality-local-functions"}[]이 대응을 증명 안에서 여러 번 사용하므로 `let`으로 함수 `f`를 정의하자.
`let f (_ : Fin 1) ...`처럼 인수와 함수값을 적으면 이후에 `f`를 함수 이름으로 사용할 수 있다.
앞의 `set`이 이미 나타난 식에 이름을 붙이는 데 쓰였다면,
여기서는 새 함수를 구성하는 것이므로 `let`으로 그 정의를 적는다.
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
    symm
    exact x.property
```

함수 `f`의 값은 원소 `a`와 그 원소 조건인 `a = a`의 증명을 함께 담는다.
단사성의 목표에 `ext`를 사용하면 목표가 `i.val = j.val`로 바뀐다.
두 값이 모두 $`1`보다 작은 자연수라는 조건 `i.isLt`와 `j.isLt`에 따라
두 값은 모두 $`0`이다. 이 범위 조건으로 두 값이 같음을 `arith`가 확인한다.
전사성에서는 번호 $`0`을 택하고 `ext`로 집합의 원소 값을 비교한다.
이때 `x.property`는 `x.val = a`의 증명이므로 `symm`으로 목표의 양변을 바꾼 뒤 이를 제시한다.

*문제 1* 원소가 하나씩 있는 두 집합은 크기가 같음을 증명하라.

```savedLean -keep
theorem exercise_singletons_same_cardinal {A B : Type}
    (a : A) (b : B) :
    cardinal (Elem (singleton a)) =
      cardinal (Elem (singleton b)) := by
  sorry
```

### 세 원소 집합의 원소 수
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
    apply_fun (fun x => x.val) at hij
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

### 연습문제: 두 원소 집합의 번호
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

### 전단사와 원소 수
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

# 비둘기집 원리
%%%
tag := "cardinality-uniqueness"
file := "uniqueness"
%%%

세 학생에게 의자 두 개를 배정하면 적어도 두 학생이 같은 의자를 배정받는다.
이와 같이 자리가 원소보다 적으면 서로 다른 원소를 모두 다른 자리에 보낼 수 없다는 것이 *비둘기집 원리*이다.
번호로 쓰면 `Fin m`에서 `Fin n`으로 가는 단사함수가 존재할 때 $`m≤n`이라는 명제이다.

이 원리를 증명하면 원소 수가 하나로 정해진다는 사실도 얻는다.
한 집합에 `Fin m`과 `Fin n`으로 각각 번호를 붙이면 두 번호 타입 사이에 전단사가 생긴다.
전단사와 그 역함수에 비둘기집 원리를 적용하면 $`m≤n`과 $`n≤m`이므로 $`m=n`이다.

비둘기집 원리의 증명에는 번호 수에 대한 귀납법을 사용한다.
단사함수에서 정의역의 원소 하나와 그 함수값을 함께 지우면 남은 대응도 단사이다.
이때 양쪽의 번호 수가 하나씩 줄어들므로 귀납 가정을 적용할 수 있다.
먼저 번호 하나를 지우고 다시 번호를 붙이는 과정을 구성하자.

## 번호 하나의 삭제
%%%
tag := "cardinality-erasing-an-index"
%%%

$`0,1,2,3,4`에서 번호 $`2`를 지우면 $`0,1,3,4`가 남는다.
이들에게 새 번호 $`0,1,2,3`을 붙이려면 지운 번호보다 작은 수는 그대로 두고 큰 수에서는 $`1`을 뺀다.
지울 번호를 $`r`, 다시 번호를 붙일 대상을 $`k`라고 하여 다음 함수를 정의하자.

```savedLean
def eraseIndex (r k : Nat) : Nat :=
  if k < r then k else k - 1
```

```savedLean
example :
    eraseIndex 2 0 = 0 ∧ eraseIndex 2 1 = 1 ∧
    eraseIndex 2 3 = 2 ∧ eraseIndex 2 4 = 3 := by
  decide
```

`eraseIndex`는 자연수를 받으므로 지운 번호 $`2`도 인수로 넣을 수 있다.
그 경우에는 다음과 같이 서로 다른 두 번호의 결과가 같아진다.

```savedLean
example :
    eraseIndex 2 1 = eraseIndex 2 2 := by
  rfl
```

따라서 이 함수의 단사성을 사용할 때는 지운 번호를 제외해야 한다.
뒤의 `eraseIndex_injective`에서 두 인수가 모두 $`r`과 다르다는 조건을 받는 이유이다.


정의에 들어 있는 `if`를 계산할 때는 조건이 참인지 거짓인지 사용한다.
`ite_eq_left h`는 조건의 증명 `h`로 첫째 값을 택하고,
`ite_eq_right h`는 조건의 부정으로 둘째 값을 택한다.

```savedLean
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

이제 번호 범위와 단사성을 차례로 확인하자.
먼저 $`0≤r<n+1`인 번호를 지우면 나머지 번호 $`k`에는 $`n`보다 작은 새 번호가 붙어야 한다.
$`k<r`이면 새 번호는 $`k<n`이고, $`r<k`이면 새 번호는 $`k-1<n`이다.
`k ≠ r`이라는 조건이 이 두 경우를 보장한다.

```savedLean
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

두 번호가 같은 새 번호를 갖는 경우도 살펴보자.
둘 다 $`r`보다 작으면 값을 바꾸지 않았으며, 둘 다 $`r`보다 크면 양쪽에서 똑같이 $`1`을 뺐다.
한 번호만 $`r`보다 작으면 새 번호도 각각 $`r` 미만과 $`r` 이상에 있어 서로 다르다.
따라서 지운 번호를 제외한 원소들에서는 단사이다.

```savedLean
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

## 단사함수에서 한 쌍의 삭제
%%%
tag := "cardinality-removing-a-pair"
%%%

이제 $`f:\operatorname{Fin}(m+1)→\operatorname{Fin}(n+1)`이 단사라고 하자.
정의역의 번호 $`0`과 공역의 번호 $`f(0)`을 지우고 남은 대응을 옮긴다.

예를 들어 `Fin 3 → Fin 4`인 단사함수가 번호 $`0,1,2`를 각각 $`2,0,3`으로 보낸다고 하자.
정의역의 $`0`과 그 함수값 $`2`를 지운 뒤 새 번호를 붙이면 다음과 같다.

:::table +header (align := left)
*
  * 원래 번호
  * 원래 함수값
  * 새 번호
  * 새 함수값
*
  * $`0`
  * $`2`
  * 삭제
  * 삭제
*
  * $`1`
  * $`0`
  * $`0`
  * $`0`
*
  * $`2`
  * $`3`
  * $`1`
  * $`2`
:::

이렇게 얻은 함수는 `Fin 2 → Fin 3`이며 두 함수값이 서로 다르므로 단사이다.
일반적인 구성도 같은 방식으로 진행한다.

- 남은 정의역의 번호는 $`i+1`로 쓴다. 코드의 `next i`가 이 번호이다.
- 단사성 때문에 $`f(i+1)≠f(0)`이다. 이를 `hne i`로 증명한다.
- $`f(i+1)`에서 번호 $`f(0)`을 지우고 새 번호를 붙이면 `Fin n`의 원소를 얻는다.
  앞의 범위 정리를 사용하여 `g i`를 만든다.

새 함수값이 같으면 `eraseIndex_injective`로 원래 함수값도 같고,
$`f`의 단사성으로 $`i+1=j+1`이다. 양쪽에서 $`1`을 소거하면 $`i=j`이므로 새 함수 `g`도 단사이다.

```savedLean
theorem fin_injection_remove {m n : Nat}
    (f : Fin (m + 1) → Fin (n + 1))
    (hf : Injective f) :
    ∃ g : Fin m → Fin n, Injective g := by
  -- 정의역의 0을 지우고 나머지 번호를 i + 1로 쓴다.
  let first : Fin (m + 1) :=
    { val := 0, isLt := by arith }
  let next (i : Fin m) : Fin (m + 1) :=
    { val := i.val + 1
      isLt := by arith }

  -- 단사성에 따라 나머지 함수값은 f(0)과 다르다.
  have hne (i : Fin m) :
      (f (next i)).val ≠ (f first).val := by
    intro h
    replace h : f (next i) = f first := by
      ext
      exact h

    replace h : next i = first :=
      hf (next i) first h
    apply_fun (fun x => x.val) at h
    expand at h
    arith

  -- 공역에서 f(0)을 지우고 번호를 다시 붙인다.
  let g (i : Fin m) : Fin n :=
    { val := eraseIndex (f first).val (f (next i)).val
      isLt := eraseIndex_lt
        (f first).isLt (f (next i)).isLt (hne i) }

  have hg : Injective g := by
    intro i j hij
    -- 새 번호의 등식에서 원래 함수값의 등식을 얻는다.
    apply_fun (fun x => x.val) at hij
    replace hij : f (next i) = f (next j) := by
      ext
      exact eraseIndex_injective (hne i) (hne j) hij

    -- f의 단사성으로 i + 1 = j + 1을 얻는다.
    replace hij : next i = next j :=
      hf (next i) (next j) hij
    apply_fun (fun x => x.val) at hij

    -- 양변의 1을 소거하여 i = j를 보인다.
    ext
    expand at hij
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

귀납 명제는 “모든 $`m`에 대하여 `Fin m → Fin n`인 단사함수가 있으면 $`m≤n`”이다.
코드에서는 `induction n generalizing m`으로 이 형태의 귀납 가정을 얻는다.

```
ih : ∀ {m : Nat} (f : Fin m → Fin n),
  Injective f → m ≤ n
```

`generalizing m` 없이 시작하면 정의역의 번호 수가 처음의 값으로 고정된다.
예를 들어 `Fin (m + 1)`에 대한 귀납 가정으로는 한 쌍을 지운 뒤의
`g : Fin m → Fin n`을 받을 수 없다. 모든 정의역 크기에 대한 가정을 확보했으므로
아래에서는 `ih g hg`로 줄어든 두 번호 수의 부등식을 얻는다.

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
문제 3의 `exercise_fin_succ_not_injective`를 사용하라.

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
  apply (cardinal_eq_iff _ _).mp
  exact h
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
  symm at hm
  exact hm.trans hn
```

`symm at hm`으로 첫 등식의 방향을 바꾸면 `cardinal (Fin m) = cardinal A`를 얻는다.
여기에 `.trans hn`으로 두 번째 등식을 이어 붙이면 두 번호 타입의 기수가 같다는 등식이 된다.

앞에서 센 집합에 이 정리를 적용하면 다음과 같다. 첫 번째 인수는 새로운 방법으로 센 결과이고,
두 번째 인수는 이미 증명한 원소 수이다.

```savedLean
example (n : Nat)
    (hn : cardinal (Elem threeNumbers) = cardinal (Fin n)) :
    n = 3 := by
  apply finite_cardinal_unique hn
  exact threeNumbers_cardinal
```

## 유한기수와 자연수
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
자연수에서 먼저 계산한 값을 기수로 나타낼 때는 `((m * n : Nat) : Cardinal)`로 적을 수 있다.
이후 기수 자체의 곱셈도 정의하므로 계산하는 타입을 구별하여 사용하겠다.

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


### 자연수로 나타낸 원소 수
%%%
tag := "cardinality-natural-count"
%%%

유한집합의 원소 수를 길이나 횟수처럼 자연수로 사용할 때도 있다.
`hA : IsFinite A`는 `cardinal A = n`인 자연수 $`n`이 존재한다는 증명이며,
앞에서 이 $`n`이 유일함을 보였다. 이 자연수를 `cardinality A hA`로 나타내자.
`cardinal A : Cardinal`이 크기를 동치류로 나타낸 값이라면,
`cardinality A hA : Nat`은 유한하다는 증명 `hA`를 사용하여 얻은 자연수이다.
이 값은 유한군의 위수처럼 자연수로 정의하는 원소 수에 사용한다.

```savedLean
noncomputable def cardinalityData (A : Type)
    (hA : IsFinite A) : {n : Nat // cardinal A = n} :=
  { val := Classical.choose hA
    property := Classical.choose_spec hA }
```

`cardinalityData`에는 원소 수와 그 수를 사용한 기수 등식이 함께 들어 있다.
역함수에서와 같이 값을 꺼내는 정의와 성질을 꺼내는 정리를 두면 다음과 같다.

```savedLean
noncomputable def cardinality (A : Type)
    (hA : IsFinite A) : Nat :=
  (cardinalityData A hA).val
```

```savedLean
theorem cardinality_spec {A : Type}
    (hA : IsFinite A) :
    cardinal A = cardinality A hA := by
  exact (cardinalityData A hA).property
```

```savedLean
theorem cardinality_eq {A : Type} {n : Nat}
    (hA : IsFinite A)
    (hn : cardinal A = n) :
    cardinality A hA = n := by
  apply finite_cardinal_unique (cardinality_spec hA)
  exact hn
```

`cardinality_spec`는 선택한 원소 수가 실제 기수와 일치함을 보장하고,
`cardinality_eq`는 이미 센 결과로 이 값을 계산하게 한다.

```savedLean
example : cardinality (Fin 3) (fin_isFinite 3) = 3 := by
  apply cardinality_eq
  exact cardinal_fin 3
```

### 유한성의 전달

{anchor "cardinality-finiteness-transport"}[]

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


## 유한집합의 단사와 전사
%%%
tag := "cardinality-finite-maps"
%%%


서로 같은 수의 학생과 의자가 있을 때 학생마다 서로 다른 의자에 앉히면 빈 의자가 남지 않는다.
의자 하나를 비워 두었다면 학생 수보다 적은 의자에 학생들을 겹치지 않게 앉힌 셈이기 때문이다.
이는 비둘기집 원리로 배제한 상황이다.

*정리* 유한집합 $`A`, $`B`의 크기가 같으면 함수 $`f:A\to B`가 단사일 필요충분조건은 전사인 것이다.

먼저 두 집합 모두 번호 집합 $`\operatorname{Fin}(n)`인 경우를 보자.
$`n=0`이면 공역에 원소가 없어 전사성이 성립한다.
$`n=k+1`일 때 상에서 번호 $`r`이 빠졌다고 가정하자.
공역에서 그 번호를 `eraseIndex`로 지우면 `Fin (k + 1)`에서 `Fin k`로 가는 단사를 얻어
비둘기집 원리와 모순이다. 새 번호의 범위와 단사성에는 앞에서 증명한 두 보조정리를 사용한다.

```savedLean
theorem fin_injective_surjective (n : Nat)
    (f : Fin n → Fin n)
    (hf : Injective f) :
    Surjective f := by
  intro r
  by_contra hmissing
  cases n with
  | zero => exact Fin.elim0 r
  | succ n =>
    have hne (x : Fin (n + 1)) : (f x).val ≠ r.val := by
      intro hval
      apply hmissing
      exists x
      ext
      exact hval

    let g (x : Fin (n + 1)) : Fin n :=
      { val := eraseIndex r.val (f x).val
        isLt := eraseIndex_lt r.isLt (f x).isLt (hne x) }
    have hg : Injective g := by
      intro x y hxy
      apply hf
      ext
      apply eraseIndex_injective (hne x) (hne y)
      apply_fun (fun x => x.val) at hxy
      exact hxy

    -- 빠진 번호를 지우면 더 작은 번호 집합으로 가는 단사를 얻는다.
    have hbound : n + 1 ≤ n := by
      apply fin_injective_le g hg
    arith
```

이 증명에서는 빠진 공역의 번호만 지우고 정의역은 그대로 두었다.
비둘기집 원리의 귀납 단계에서 양쪽 번호를 하나씩 지운 것과 달리,
이번에는 $`n+1`개를 $`n`개로 보내는 단사를 얻어 모순을 만든다.

일반적인 유한집합에도 번호를 붙이면 같은 결과를 사용할 수 있다.
$`a:A\to\operatorname{Fin}(n)`, $`b:B\to\operatorname{Fin}(n)`이 번호를 붙이는 전단사이면
$`b\circ f\circ a^{-1}`에 앞의 정리를 적용한다.

```savedLean
theorem finite_injective_surjective {A B : Type} (f : A → B)
    (hA : IsFinite A)
    (hAB : cardinal A = cardinal B)
    (hf : Injective f) :
    Surjective f := by
  -- A와 B에 같은 수의 번호를 붙인다.
  unpack hA with ⟨n, hn⟩
  have hBn : cardinal B = cardinal (Fin n) := by
    rw [← hAB]
    exact hn

  unpack (cardinal_eq_iff A (Fin n)).mp hn with ⟨a, ha⟩
  unpack (cardinal_eq_iff B (Fin n)).mp hBn with ⟨b, hb⟩
  let F (i : Fin n) : Fin n := b (f (inverseMap a ha i))
  -- 번호 사이의 함수도 세 단사함수의 합성이므로 단사이다.
  have hF : Injective F := by
    intro i j hij
    apply (inverseMap_bijective a ha).inj
    apply hf
    apply hb.inj
    exact hij

  -- y의 번호를 만드는 원상을 A의 원소로 옮긴다.
  intro y
  unpack fin_injective_surjective n F hF (b y) with ⟨i, hi⟩
  exists inverseMap a ha i
  apply hb.inj
  exact hi
```

두 전단사 `a`, `b`로 원소를 번호로 바꾸었으므로 `F`는 번호들 사이의 함수이다.
`F`의 단사성은 번호를 원소로 되돌리는 역함수와 두 함수 `f`, `b`의 단사성에서 얻는다.
주어진 `y : B`의 번호 `b y`를 `F`가 만들 수 있으므로, 그 번호를 다시 `A`의 원소로 옮기면 `f`의 전사성을 얻는다.

반대 방향에서는 전사성으로 각 $`y\in B`에 대해 $`f(g(y))=y`인 원소를 하나씩 택한다.
그러면 $`g`는 단사이므로 방금 증명한 방향에 따라 전사이기도 하다.
임의의 $`x,x'\in A`를 $`g(u),g(v)`로 쓰면
$`f(x)=f(x')`에서 $`u=v`를 얻어 $`x=x'`가 된다.
이때 고른 함수와 $`f(g(y))=y`라는 성질은 앞의 역함수 구성처럼 함께 담아 두자.

```savedLean
theorem finite_surjective_injective {A B : Type} (f : A → B)
    (hA : IsFinite A)
    (hAB : cardinal A = cardinal B)
    (hf : Surjective f) :
    Injective f := by
  let gData : { g : B → A // ∀ y, f (g y) = y } :=
    { val := fun y => Classical.choose (hf y)
      property := by
        intro y
        exact Classical.choose_spec (hf y) }

  let g : B → A := gData.val
  have hfg (y : B) : f (g y) = y :=
    gData.property y
  -- g의 함수값이 같으면 f를 적용하여 원래 원소의 등식을 얻는다.
  have hg : Injective g := by
    intro x y hxy
    apply_fun f at hxy
    rw [hfg, hfg] at hxy
    exact hxy

  -- 같은 크기의 유한집합 사이의 단사이므로 g는 전사이기도 하다.
  have hgSurj : Surjective g := by
    apply finite_injective_surjective g
    · apply isFinite_transport hAB hA
    · symm
      exact hAB

    · exact hg

  -- x와 y를 g의 함수값으로 나타내어 f의 단사성을 보인다.
  intro x y hxy
  unpack hgSurj x with ⟨u, hu⟩
  unpack hgSurj y with ⟨v, hv⟩
  rw [← hu, ← hv, hfg, hfg] at hxy
  rw [← hu, ← hv, hxy]
```

```savedLean
theorem finite_injective_iff_surjective {A B : Type}
    (f : A → B)
    (hA : IsFinite A)
    (hAB : cardinal A = cardinal B) :
    Injective f ↔ Surjective f := by
  constructor
  · apply finite_injective_surjective f hA hAB
  · apply finite_surjective_injective f hA hAB
```

*문제 7* (유한성의 역할)

(1) `Fin n` 위의 단사함수는 전단사임을 증명하라.

(2) 자연수에서 $`k\mapsto k+1`은 단사이지만 전사가 아님을 증명하라.
정의역과 공역이 같아도 무한집합에서는 앞의 정리를 사용할 수 없다.

```savedLean -keep
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
```

# 기수 연산
%%%
tag := "cardinality-constructions"
%%%

두 상자 안의 원소를 모두 모으면 원소 수를 더하고, 각 상자에서 하나씩 고르면 원소 수를 곱한다.
이 계산을 번호들의 전단사로 확인한 뒤, 유한집합과 무한집합에 공통으로 사용하는 기수 연산을 정의하자.

## 합의 번호
%%%
tag := "cardinality-sum-numbering"
%%%

두 원소와 세 원소를 출처를 구별하여 합치면 다섯 원소를 얻는다.
번호 $`0,1`은 왼쪽에, $`2,3,4`는 오른쪽에 붙이면 된다.
일반적인 유한한 번호 집합의 합에서도 왼쪽 번호 $`i`는 그대로 두고 오른쪽 번호 $`j`를 $`m+j`로 옮기면 된다.
그러면 $`0,\ldots,m-1`과 $`m,\ldots,m+n-1`이 겹치지 않게 이어진다.

```savedLean
def finSum (m n : Nat) : Fin m ⊕ Fin n → Fin (m + n)
  | .inl a => { val := a.val, isLt := by arith }
  | .inr b => { val := m + b.val, isLt := by arith }
```

이 함수는 전단사이다. 주어진 번호가 $`m`보다 작으면 왼쪽에서 왔고,
그렇지 않으면 $`m`을 빼서 오른쪽 번호를 되찾을 수 있다.
단사성을 확인할 때도 두 원소가 어느 쪽에서 왔는지 나누어 살펴본다.
서로 다른 쪽에서 왔다면 한 번호는 $`m`보다 작고 다른 번호는 $`m` 이상이므로 같을 수 없다.

```savedLean
theorem finSum_bijective (m n : Nat) :
    Bijective (finSum m n) := by
  constructor
  · intro x y hxy
    -- 두 원소의 출처에 따라 번호가 같을 수 있는지 확인한다.
    cases x with
    | inl a =>
      cases y with
      | inl b =>
        apply_fun (fun x => x.val) at hxy with hval
        have hab : a = b := by
          ext
          exact hval

        rw [hab]

      | inr b =>
        apply_fun (fun x => x.val) at hxy with hval
        arith

    | inr a =>
      cases y with
      | inl b =>
        apply_fun (fun x => x.val) at hxy with hval
        arith

      | inr b =>
        apply_fun (fun x => x.val) at hxy with hval
        have hab : a = b := by
          ext
          arith

        rw [hab]

  · intro k
    -- m보다 작은 번호는 왼쪽, 나머지는 오른쪽에서 온다.
    by_cases hk : k.val < m
    · exists Sum.inl { val := k.val, isLt := hk }
    · exists Sum.inr { val := k.val - m, isLt := by arith }
      ext
      dsimp [finSum]
      arith
```

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
    apply_fun (fun p => p.1.val) at hxy with hmod
    apply_fun (fun p => p.2.val) at hxy with hdiv
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

*문제 8* (유한집합의 곱)

(1) 유한집합 $`A`, $`B`의 원소 수가 각각 $`m`, $`n`이면
집합 $`A\times B`의 원소 수가 $`mn`임을 증명하라.
`finProduct_bijective`와 `productMap_bijective`를 합성하되,
기수의 등식에서 전단사를 꺼낼 때는 함수의 방향을 확인하라.

(2) 두 성분을 바꾸는 함수를 사용하여 $`|A\times B|=|B\times A|`임을 증명하라.

(3) 두 가지 색과 세 가지 번호를 각각 `Fin 2`, `Fin 3`으로 나타낸다.
첫 결과를 사용하여 색과 번호를 짝짓는 방법이 모두 여섯 가지임을 보이라.

(4) 둘째와 셋째 결과를 사용하여 번호와 색의 순서로 나열해도 여섯 가지임을 보이라.

```savedLean -keep
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
```

*문제 9* (두 칸의 색칠)

두 칸을 색칠하는 방법은 각 칸에 색을 하나씩 대응시키는 함수이다.
색들의 타입이 $`A`이면 이러한 함수를 `Fin 2 → A`로 나타낸다.

(1) 아래 함수는 색 두 개를 받아 첫째 칸과 둘째 칸의 색을 정한다.
이 함수가 전단사임을 증명하라.

(2) 첫 결과와 `finProduct_bijective`를 사용하여 색이 세 가지일 때 두 칸을 색칠하는 방법이 아홉 가지임을 보이라.
같은 색을 두 번 사용해도 된다.

```savedLean -keep
def practiceTwoValues {A : Type} (p : A × A) : Fin 2 → A :=
  fun i => if i.val = 0 then p.1 else p.2

theorem exercise_twoValues_bijective (A : Type) :
    Bijective (practiceTwoValues (A := A)) := by
  sorry

theorem exercise_two_to_three_functions :
    cardinal (Fin 2 → Fin 3) = 9 := by
  sorry
```


## 기수의 연산
%%%
tag := "cardinality-arithmetic"
%%%


두 집합에서 원소를 모으거나 짝을 짓는 방법은 그 집합들의 크기에도 연산을 정한다.
서로소인 합에서는 두 쪽의 원소 수를 더하고, 곱에서는 각 쪽에서 하나씩 택하는 경우를 센다.
함수 공간에서는 정의역의 각 원소마다 공역의 값을 정하므로 공역의 크기를 밑으로 하는 거듭제곱을 얻는다.

이 연산을 기수에 정의하려면 같은 크기의 다른 집합으로 바꾸어도 결과가 같아야 한다.
합에서는 출처별로 전단사를 적용하고, 곱에서는 각 성분에 전단사를 적용하면 된다.

```savedLean
theorem sameCardinality_sum {A B C D : Type}
    (hAC : SameCardinality A C)
    (hBD : SameCardinality B D) :
    SameCardinality (A ⊕ B) (C ⊕ D) := by
  unpack hAC with ⟨f, hf⟩
  unpack hBD with ⟨g, hg⟩
  exists sumMap f g
  apply sumMap_bijective f g hf hg
```

```savedLean -show
theorem sameCardinality_product {A B C D : Type}
    (hAC : SameCardinality A C)
    (hBD : SameCardinality B D) :
    SameCardinality (A × B) (C × D) := by
  unpack hAC with ⟨f, hf⟩
  unpack hBD with ⟨g, hg⟩
  exists productMap f g
  apply productMap_bijective f g hf hg
```

곱에서도 각 성분에 전단사를 적용하면 같은 크기의 곱을 얻는다.
함수 공간에서는 정의역을 바꾸는 방향에 주의해야 한다.
전단사 $`f:A\to C`, $`g:B\to D`가 있고 함수 $`u:A\to B`가 주어지면,
$`c\in C`를 먼저 $`f^{-1}(c)\in A`로 옮긴 뒤 $`u`와 $`g`를 적용한다.
따라서 $`u`에 함수 $`g\circ u\circ f^{-1}:C\to D`를 대응시킨다.
역방향은 $`v:C\to D`를 $`g^{-1}\circ v\circ f`로 보내므로 이 대응도 전단사이다.

```savedLean -show
noncomputable def functionMap {A B C D : Type}
    (f : A → C)
    (hf : Bijective f)
    (g : B → D) :
    (A → B) → (C → D) :=
  fun u c => g (u (inverseMap f hf c))

theorem functionMap_bijective {A B C D : Type}
    (f : A → C) (g : B → D)
    (hf : Bijective f)
    (hg : Bijective g) :
    Bijective (functionMap f hf g) := by
  apply bijective_of_inverse _
    (fun v a => inverseMap g hg (v (f a)))

  · intro u
    ext a
    dsimp [functionMap]
    rw [inverseMap_left f, inverseMap_left g]

  · intro v
    ext c
    dsimp [functionMap]
    rw [inverseMap_right f, inverseMap_right g]

theorem sameCardinality_arrow {A B C D : Type}
    (hAC : SameCardinality A C)
    (hBD : SameCardinality B D) :
    SameCardinality (A → B) (C → D) := by
  unpack hAC with ⟨f, hf⟩
  unpack hBD with ⟨g, hg⟩
  exists functionMap f hf g
  apply functionMap_bijective f g hf hg
```

덧셈에서는 두 타입 `A`, `B`에 서로소인 합의 기수 `cardinal (A ⊕ B)`를 대응시키려 한다.
예를 들어 `A`에 두 원소, `B`에 세 원소가 있으면 그 합에는 다섯 원소가 있다.
이때 어떤 두 원소 집합과 세 원소 집합을 골랐는지는 합의 크기에 영향을 주지 않는다.
따라서 `cardinal A`와 `cardinal B`만으로 합의 기수를 정할 수 있어야 한다.

앞 장의 `quotientLift`는 대표원을 받는 함수에서 몫 원소를 받는 함수를 만들었다.
여기서는 대표원이 타입 `A`, `B`이고 몫 원소가 그 기수이다.
두 인수를 차례로 옮기기 위해 먼저 `A`를 고정하고 `B`만 기수로 바꾸자.
`sameCardinality_sum`에 따라 `B`와 크기가 같은 타입을 넣어도 합의 기수가 같으므로
다음 함수 `addToType A : Cardinal → Cardinal`을 얻는다.

```savedLean
namespace Cardinal

noncomputable def addToType (A : Type) :
    Cardinal → Cardinal :=
  quotientLift
    SameCardinality
    sameCardinality_equivalence
    (fun B : Type => cardinal (A ⊕ B))
    (by
      intro B D hBD
      ext
      apply sameCardinality_sum
      · exact sameCardinality_refl A
      · exact hBD)

theorem addToType_cardinal (A B : Type) :
    addToType A (cardinal B) = cardinal (A ⊕ B) := by
  exact quotientLift_classOf
```

`addToType A (cardinal B)`는 `cardinal (A ⊕ B)`이다.
이 계산 정리는 앞 장의 `quotientLift_classOf`를 그대로 적용한 결과이다.
이 단계의 첫째 인수는 타입 `A`이고 둘째 인수는 기수이다.

이제 `A`와 `C`의 크기가 같으면 `addToType A`와 `addToType C`도 같은 함수임을 보이자.
어느 타입 `B`를 더해도 `A ⊕ B`와 `C ⊕ B`의 크기가 같기 때문이다.
몫집합 위 함수의 유일성 정리 `quotientLift_unique`를 사용하면
`cardinal B`에서 두 함수의 값이 같음을 확인하여 함수의 등식을 얻는다.

```savedLean
theorem addToType_respects (A C : Type)
    (hAC : SameCardinality A C) :
    addToType A = addToType C := by
  apply quotientLift_unique SameCardinality
    (fun B : Type => cardinal (C ⊕ B))
  · intro B
    calc
      addToType A (cardinal B) = cardinal (A ⊕ B) := by
        rw [addToType_cardinal]
      _ = cardinal (C ⊕ B) := by
        ext
        apply sameCardinality_sum
        · exact hAC
        · exact sameCardinality_refl B

  · intro B
    exact addToType_cardinal C B
```

이 증명에서 `A`만 `C`로 바꾸고 `B`는 그대로 두었으므로
`sameCardinality_sum`에는 `hAC`와 `sameCardinality_refl B`를 사용했다.
이제 `addToType` 자체에 다시 `quotientLift`를 적용하여 첫째 인수도 기수로 바꾸자.
그 결과인 `add`는 두 기수 `a`, `b`를 받아 합의 기수를 돌려준다.

```savedLean
noncomputable def add (a b : Cardinal) : Cardinal :=
  quotientLift
    SameCardinality
    sameCardinality_equivalence
    addToType
    addToType_respects
    a b

noncomputable instance : Add Cardinal := ⟨add⟩

end Cardinal
```

두 번의 계산 규칙을 적용하면 `cardinal A + cardinal B = cardinal (A ⊕ B)`를 얻는다.
아래에서는 먼저 `Cardinal.add (cardinal A) = Cardinal.addToType A`에 이름 `h`를 붙인다.
이는 첫째 인수에 적용한 `quotientLift_classOf`이며,
`calc`에서는 둘째 인수의 계산 규칙과 `h`를 반대 순서로 사용하여 원하는 등식을 얻는다.
계산에 쓰기 편하도록 정리의 등식은 합의 타입에서 기수의 합으로 향하게 적는다.

```savedLean
theorem cardinal_sum (A B : Type) :
    cardinal (A ⊕ B) = cardinal A + cardinal B := by
  have h : Cardinal.add (cardinal A) =
      Cardinal.addToType A := by
    exact quotientLift_classOf

  calc
    cardinal (A ⊕ B) =
        Cardinal.addToType A (cardinal B) := by
      rw [Cardinal.addToType_cardinal]
    _ = Cardinal.add (cardinal A) (cardinal B) := by
      rw [h]
```

곱과 거듭제곱에도 같은 두 단계를 사용한다.
같은 크기의 집합으로 바꿀 수 있다는 두 보존 정리는 다음과 같다.

```lean -show (name := productPreservationType)
set_option format.width 50 in
#check sameCardinality_product
```

```leanOutput productPreservationType
Ample.sameCardinality_product {A B C D : Type} (hAC : SameCardinality A C) (hBD : SameCardinality B D) :
  SameCardinality (A × B) (C × D)
```

```lean -show (name := arrowPreservationType)
set_option format.width 50 in
#check sameCardinality_arrow
```

```leanOutput arrowPreservationType
Ample.sameCardinality_arrow {A B C D : Type} (hAC : SameCardinality A C) (hBD : SameCardinality B D) :
  SameCardinality (A → B) (C → D)
```

아래의 `mulToType A`는 타입 `A`를 고정하고 다른 쪽의 기수를 받아 곱의 기수를 구한다.
거듭제곱에서는 공역 `B`를 고정한 `powerToType B`로 정의역의 기수를 받는다.
이 두 함수에 다시 `quotientLift`를 적용하면 두 인수가 모두 기수인 연산을 얻는다.
`mulToType_respects`와 `powerToType_respects`는 고정했던 타입도 같은 크기의 타입으로 바꿀 수 있다는 증명이며,
앞의 `addToType_respects`와 같은 방식으로 얻는다.

```savedLean -show
namespace Cardinal

noncomputable def mulToType (A : Type) :
    Cardinal → Cardinal :=
  quotientLift
    SameCardinality
    sameCardinality_equivalence
    (fun B : Type => cardinal (A × B))
    (by
      intro B D hBD
      ext
      apply sameCardinality_product
      · exact sameCardinality_refl A
      · exact hBD)

theorem mulToType_cardinal (A B : Type) :
    mulToType A (cardinal B) = cardinal (A × B) := by
  exact quotientLift_classOf
theorem mulToType_respects (A C : Type)
    (hAC : SameCardinality A C) :
    mulToType A = mulToType C := by
  apply quotientLift_unique SameCardinality
    (fun B : Type => cardinal (C × B))
  · intro B
    calc
      mulToType A (cardinal B) = cardinal (A × B) := by
        rw [mulToType_cardinal]
      _ = cardinal (C × B) := by
        ext
        apply sameCardinality_product
        · exact hAC
        · exact sameCardinality_refl B

  · intro B
    exact mulToType_cardinal C B
noncomputable def powerToType (B : Type) :
    Cardinal → Cardinal :=
  quotientLift
    SameCardinality
    sameCardinality_equivalence
    (fun A : Type => cardinal (A → B))
    (by
      intro A C hAC
      ext
      apply sameCardinality_arrow
      · exact hAC
      · exact sameCardinality_refl B)

theorem powerToType_cardinal (A B : Type) :
    powerToType B (cardinal A) = cardinal (A → B) := by
  exact quotientLift_classOf
theorem powerToType_respects (B D : Type)
    (hBD : SameCardinality B D) :
    powerToType B = powerToType D := by
  apply quotientLift_unique SameCardinality
    (fun A : Type => cardinal (A → D))
  · intro A
    calc
      powerToType B (cardinal A) = cardinal (A → B) := by
        rw [powerToType_cardinal]
      _ = cardinal (A → D) := by
        ext
        apply sameCardinality_arrow
        · exact sameCardinality_refl A
        · exact hBD

  · intro A
    exact powerToType_cardinal A D

end Cardinal
```

```savedLean
namespace Cardinal

noncomputable def mul (a b : Cardinal) : Cardinal :=
  quotientLift
    SameCardinality
    sameCardinality_equivalence
    mulToType
    mulToType_respects
    a b

noncomputable instance : Mul Cardinal := ⟨mul⟩
noncomputable def power (a b : Cardinal) : Cardinal :=
  quotientLift
    SameCardinality
    sameCardinality_equivalence
    powerToType
    powerToType_respects
    a b

noncomputable instance : Pow Cardinal Cardinal := ⟨power⟩

end Cardinal
```

거듭제곱의 첫째 인수는 밑이고 둘째 인수는 지수이다.
따라서 함수 공간 `A → B`의 기수는 `cardinal B ^ cardinal A`로 계산한다.
곱과 거듭제곱의 계산 정리도 `cardinal_sum`과 같이 두 번의 계산 규칙으로 증명한다.

```savedLean -show
theorem cardinal_product (A B : Type) :
    cardinal (A × B) = cardinal A * cardinal B := by
  have h : Cardinal.mul (cardinal A) =
      Cardinal.mulToType A := by
    exact quotientLift_classOf

  calc
    cardinal (A × B) =
        Cardinal.mulToType A (cardinal B) := by
      rw [Cardinal.mulToType_cardinal]
    _ = Cardinal.mul (cardinal A) (cardinal B) := by
      rw [h]

theorem cardinal_arrow (A B : Type) :
    cardinal (A → B) = cardinal B ^ cardinal A := by
  have h : Cardinal.power (cardinal B) =
      Cardinal.powerToType B := by
    exact quotientLift_classOf

  calc
    cardinal (A → B) =
        Cardinal.powerToType B (cardinal A) := by
      rw [Cardinal.powerToType_cardinal]
    _ = Cardinal.power (cardinal B) (cardinal A) := by
      rw [h]
```

```lean -show (name := cardinalProductType)
set_option format.width 50 in
#check cardinal_product
```

```leanOutput cardinalProductType
Ample.cardinal_product (A B : Type) : cardinal (A × B) = cardinal A * cardinal B
```

```lean -show (name := cardinalArrowType)
set_option format.width 50 in
#check cardinal_arrow
```

```leanOutput cardinalArrowType
Ample.cardinal_arrow (A B : Type) : cardinal (A → B) = cardinal B ^ cardinal A
```

이후에는 다음 세 식으로 집합의 구성과 기수의 계산을 연결한다.

$$`|A\oplus B|=|A|+|B|,\qquad
|A\times B|=|A|\,|B|,\qquad
|A\to B|=|B|^{|A|}.`

## 유한기수의 계산
%%%
tag := "cardinality-finite-calculations"
%%%

앞에서 구성한 `finSum`과 `finProduct`를 사용하면 유한기수의 합·곱을 자연수의 계산과 연결할 수 있다.
합의 경우에는 `Fin m ⊕ Fin n`과 `Fin (m + n)`이 같은 크기이며,
곱의 경우에는 `Fin (m * n)`과 `Fin m × Fin n`이 같은 크기이다.

```savedLean
theorem cardinal_nat_add (m n : Nat) :
    (m : Cardinal) + n = ((m + n : Nat) : Cardinal) := by
  rw [← cardinal_fin m, ← cardinal_fin n, ← cardinal_sum]
  ext
  exists finSum m n
  exact finSum_bijective m n

theorem cardinal_nat_mul (m n : Nat) :
    (m : Cardinal) * n = ((m * n : Nat) : Cardinal) := by
  rw [← cardinal_fin m, ← cardinal_fin n,
    ← cardinal_product]
  ext
  apply sameCardinality_symm
  exists finProduct m n
  exact finProduct_bijective m n
```

두 정리는 유한기수의 덧셈·곱셈이 자연수의 덧셈·곱셈과 일치함을 보인다.
곱에 관한 증명에서는 앞에서 구성한 `finProduct`를 다시 사용했다.


*보기* 두 원소 집합과 한 원소 집합을 서로소인 합으로 모으면 원소가 세 개이다.
먼저 합의 기수를 두 기수의 합으로 바꾸고, 자연수의 계산과 연결하자.

```savedLean
example : cardinal (Fin 2 ⊕ Fin 1) = 3 := by
  rw [cardinal_sum, cardinal_fin, cardinal_fin]
  exact cardinal_nat_add 2 1
```

`rw` 이후에는 기수의 등식 `(2 : Cardinal) + 1 = 3`이 남는다.
`cardinal_nat_add 2 1`이 이 등식을 증명한다.

*문제 10* (합과 곱의 원소 수)

집합 $`A`, $`B`, $`C`의 원소 수가 각각 $`2`, $`3`, $`4`라고 하자.

(1) $`A\oplus B`의 원소 수를 구하라.

(2) $`A\times(B\oplus C)`의 원소 수를 구하라.

```savedLean -keep
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
```

## 전단사와 연산 법칙
%%%
tag := "cardinality-arithmetic-laws"
%%%

*보기* 곱에서 합의 두 출처를 구별하면
$`A\times(B\oplus C)`와 $`(A\times B)\oplus(A\times C)` 사이의 전단사를 얻는다.
역방향에서는 왼쪽 출처의 $`(a,b)`를 $`(a,\operatorname{inl}(b))`로,
오른쪽 출처의 $`(a,c)`를 $`(a,\operatorname{inr}(c))`로 보낸다.

```savedLean
def distribute {A B C : Type} :
    A × (B ⊕ C) → (A × B) ⊕ (A × C)
  | (a, .inl b) => .inl (a, b)
  | (a, .inr c) => .inr (a, c)
```

아래의 `match x with`는 앞의 `sumMap` 정의와 같이 출처에 따라 함수값을 정한다.
`rcases x with ⟨a, b | c⟩`는 순서쌍의 첫 성분을 `a`로 꺼내고 둘째 성분의 출처에 따라 두 경우로 나눈다.
반대로 `rcases y with ⟨a, b⟩ | ⟨a, c⟩`는 먼저 출처를 나눈 뒤 각 순서쌍의 성분을 꺼낸다.

```savedLean
theorem distribute_bijective (A B C : Type) :
    Bijective (distribute :
      A × (B ⊕ C) → (A × B) ⊕ (A × C)) := by
  apply bijective_of_inverse _ (fun x =>
    match x with
    | .inl (a, b) => (a, .inl b)
    | .inr (a, c) => (a, .inr c))

  · intro x
    rcases x with ⟨a, b | c⟩
    · rfl
    · rfl

  · intro y
    rcases y with ⟨a, b⟩ | ⟨a, c⟩
    · rfl
    · rfl

theorem cardinal_distrib (A B C : Type) :
    cardinal A * (cardinal B + cardinal C) =
      cardinal A * cardinal B +
        cardinal A * cardinal C := by
  rw [← cardinal_sum, ← cardinal_product,
    ← cardinal_product, ← cardinal_product, ← cardinal_sum]
  ext
  exists distribute
  exact distribute_bijective A B C
```

두 구성 사이의 전단사에서 기수의 분배법칙을 얻었다.

함수의 두 인수를 순서쌍으로 묶는 `curry`, `uncurry`에서도 계산 법칙을 얻는다.
$`A\times B\to C`와 $`A\to(B\to C)`가 같은 크기이므로 $`|C|^{|A||B|}=(|C|^{|B|})^{|A|}`이다.

```savedLean
theorem cardinal_curry (A B C : Type) :
    cardinal (A × B → C) = cardinal (A → B → C) := by
  ext
  exists curry
  apply bijective_of_inverse _ uncurry
  · exact uncurry_curry
  · exact curry_uncurry

theorem cardinal_power_mul (A B C : Type) :
    cardinal C ^ (cardinal A * cardinal B) =
      (cardinal C ^ cardinal B) ^ cardinal A := by
  rw [← cardinal_product, ← cardinal_arrow,
    ← cardinal_arrow, ← cardinal_arrow]
  exact cardinal_curry A B C
```

*문제 11* (합 위의 함수)

서로소인 합 위의 함수는 왼쪽과 오른쪽에서의 함수값을 각각 지정하여 정할 수 있다.

(1) 아래 두 변환이 서로 역방향임을 사용하여 `practiceSplitFunction`이 전단사임을 증명하라.

(2) 첫 결과를 사용하여 $`|C|^{|A|+|B|}=|C|^{|A|}|C|^{|B|}`를 증명하라.

```savedLean -keep
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
```

## 유한한 합과 곱
%%%
tag := "cardinality-indexed-arithmetic"
%%%


앞에서는 두 집합을 합치거나 원소를 하나씩 고르는 경우를 다루었다.
집합이 세 개라면 `A ⊕ (B ⊕ C)`와 `A × (B × C)`로 같은 구성을 반복할 수 있다.
각 집합의 원소 수가 $`1`, $`2`, $`3`이면 원소를 출처와 함께 모은 경우는 $`1+(2+3)=6`개이고,
각 집합에서 하나씩 고른 경우는 $`1\cdot(2\cdot3)=6`가지이다.

기수들을 여러 번 더하거나 곱할 때도 앞 장의 유한합·유한곱 표기를 사용할 수 있다.
자연수의 원소 수를 먼저 합산한 뒤 기수로 바꾸어도 같은 결과를 얻으며,
곱에서도 이 순서를 바꿀 수 있다.

```savedLean
theorem finiteSum_nat_cast (f : Nat → Nat) (n : Nat) :
    (∑ i < n, (f i : Cardinal)) =
      ((∑ i < n, f i : Nat) : Cardinal) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [finiteSum_succ, ih, cardinal_nat_add]
    rfl

theorem finiteProd_nat_cast (f : Nat → Nat) (n : Nat) :
    (∏ i < n, (f i : Cardinal)) =
      ((∏ i < n, f i : Nat) : Cardinal) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [finiteProd_succ, ih, cardinal_nat_mul]
    rfl
```

*보기* 기수 $`1`, $`2`, $`3`을 더하거나 곱한 값도 자연수의 계산으로 구할 수 있다.
먼저 `finiteSum_nat_cast`와 `finiteProd_nat_cast`로 자연수에서 계산한 결과의 기수로 바꾸자.
그 뒤에는 앞 장에서와 같이 유한합·유한곱의 정의를 계산하면 된다.

```savedLean
example : (∑ i < 3, ((i + 1 : Nat) : Cardinal)) = 6 := by
  rw [finiteSum_nat_cast]
  rfl

example : (∏ i < 3, ((i + 1 : Nat) : Cardinal)) = 6 := by
  rw [finiteProd_nat_cast]
  rfl
```

*문제 12* (크기가 다른 세 상자)

세 상자의 원소 수가 각각 $`1`, $`2`, $`3`이다.
상자에 $`0`, $`1`, $`2`라는 번호를 붙이면 $`i`번 상자의 원소 수는 $`i+1`이다.

(1) 원소를 출처와 함께 모두 모은 집합의 기수가 세 기수의 유한합과 같음을 보이라.

(2) 각 상자에서 하나씩 고르는 방법들의 집합의 기수가 세 기수의 유한곱과 같음을 보이라.

앞의 보기에서 두 계산의 값은 모두 $`6`임을 확인했다.

```savedLean -keep
theorem exercise_three_boxes_sum :
    cardinal (Fin 1 ⊕ (Fin 2 ⊕ Fin 3)) =
      ∑ i < 3, ((i + 1 : Nat) : Cardinal) := by
  sorry

theorem exercise_three_boxes_product :
    cardinal (Fin 1 × (Fin 2 × Fin 3)) =
      ∏ i < 3, ((i + 1 : Nat) : Cardinal) := by
  sorry
```

## 함수의 개수
%%%
tag := "cardinality-finite-functions"
%%%

$`m`개의 칸을 각각 $`n`가지 색 중 하나로 칠하는 방법은 함수 `Fin m → Fin n`으로 나타낸다.
각 칸에서 고를 수 있는 색이 $`n`가지이므로 전체 방법의 수는 $`n^m`이다.
이를 귀납법으로 확인하자. 칸이 없을 때는 빈 함수 하나가 있고,
칸이 하나 늘면 기존 색칠 방법마다 마지막 칸의 색을 $`n`가지로 고를 수 있다.

먼저 칸이 없는 경우를 살펴보자. `Fin 0`에는 원소가 없으므로
공역이 어떤 타입 `B`이든 값을 지정할 곳이 없다.
이때의 함수를 *빈 함수*라고 하며, `Fin.elim0`으로 정의할 수 있다.

```savedLean
def emptyFinFunction (B : Type) : Fin 0 → B :=
  fun i => Fin.elim0 i
```

`Fin 0 → B`의 원소는 이러한 함수들이며 그 원소가 하나임을 보이려면
이 함수들의 타입과 `Fin 1` 사이의 전단사를 구성하면 된다.
모든 함수를 유일한 번호 $`0`으로 보내고, 번호에서는 빈 함수로 돌아오도록 하자.
첫째 합성에서는 임의의 `f : Fin 0 → B`가 빈 함수와 같음을 보인다.
`ext i`로 값 하나를 비교하려 해도 `i : Fin 0`은 존재할 수 없으므로 증명이 끝난다.

```savedLean
theorem cardinal_empty_fin_arrow (B : Type) :
    cardinal (Fin 0 → B) = 1 := by
  ext
  let toSingle (_ : Fin 0 → B) : Fin 1 :=
    { val := 0, isLt := by decide }
  let fromSingle (_ : Fin 1) : Fin 0 → B :=
    emptyFinFunction B
  exists toSingle
  apply bijective_of_inverse _ fromSingle
  · intro f
    ext i
    exact Fin.elim0 i

  · intro i
    ext
    arith
```

다음으로 공역이 `B`인 함수에서 마지막 값을 분리하자.
`Fin (m + 1) → B`인 함수는 앞의 $`m`개 값과 마지막 값으로 결정되므로,
`(Fin m → B) × B`와 전단사를 이룬다.
`Fin.lastCases last rest i`는 번호 `i`가 마지막 번호이면 `last`를,
`j.castSucc` 꼴의 앞 번호이면 `rest j`를 값으로 갖는다.

가령 앞의 두 번호에서 $`1`, $`2`를, 마지막 번호에서 $`7`을 값으로 갖는 함수를 만들 수 있다.
앞의 두 값은 `fun i : Fin 2 => i.val + 1`로 정하고 마지막 값으로 `7`을 제시하자.

```savedLean
example :
    Fin.lastCases 7 (fun i : Fin 2 => i.val + 1)
      (Fin.last 2) = 7 := by
  rfl

example (i : Fin 2) :
    Fin.lastCases 7 (fun j : Fin 2 => j.val + 1)
      i.castSucc = i.val + 1 := by
  simp
```

이제 마지막 값에는 `p.2`를, 앞의 값들에는 함수 `p.1`을 사용하여 두 방향을 정의하자.

```savedLean
def finFunctionAppend (B : Type) (m : Nat)
    (p : (Fin m → B) × B) : Fin (m + 1) → B :=
  Fin.lastCases p.2 p.1

def finFunctionSplit (B : Type) (m : Nat)
    (f : Fin (m + 1) → B) : (Fin m → B) × B :=
  (fun i => f i.castSucc, f (Fin.last m))
```

`finFunctionAppend`는 앞의 함수에 마지막 값을 붙이고,
`finFunctionSplit`는 함수에서 이 둘을 꺼낸다.
붙였다가 꺼내거나 꺼냈다가 붙이면 원래 자료로 돌아온다.
아래의 `induction i using Fin.lastCases`는 방금 사용한 번호의 분해 규칙으로 두 경우를 나눈다.
`last`에서는 마지막 번호를, `cast i`에서는 앞 번호 `i.castSucc`를 비교한다.
각 경우의 함수값은 위의 두 계산과 같이 정해진다.

```savedLean
theorem finFunctionAppend_bijective (B : Type) (m : Nat) :
    Bijective (finFunctionAppend B m) := by
  apply bijective_of_inverse _ (finFunctionSplit B m)
  · intro p
    simp [finFunctionAppend, finFunctionSplit]

  · intro f
    ext i
    induction i using Fin.lastCases with
    | last => simp [finFunctionAppend, finFunctionSplit]
    | cast i => simp [finFunctionAppend, finFunctionSplit]
```

이제 공역을 `Fin n`으로 두고 칸의 수 $`m`에 대하여 귀납법을 사용한다.
귀납 단계에서는 방금 만든 전단사로 마지막 칸을 분리한 뒤,
앞의 함수 개수와 $`n`을 곱한다. 마지막 등식은 자연수 거듭제곱의 법칙 `Nat.pow_succ`이다.

```savedLean
theorem cardinal_fin_arrow (m n : Nat) :
    cardinal (Fin m → Fin n) =
      ((n ^ m : Nat) : Cardinal) := by
  induction m with
  | zero => exact cardinal_empty_fin_arrow (Fin n)
  | succ m ih =>
    calc
      cardinal (Fin (m + 1) → Fin n) =
          cardinal ((Fin m → Fin n) × Fin n) := by
        ext
        apply sameCardinality_symm
        exists finFunctionAppend (Fin n) m
        exact finFunctionAppend_bijective (Fin n) m

      _ = cardinal (Fin m → Fin n) * cardinal (Fin n) := by
        rw [cardinal_product]
      _ = ((n ^ m : Nat) : Cardinal) * n := by
        rw [ih, cardinal_fin]
      _ = ((n ^ m * n : Nat) : Cardinal) := by
        rw [cardinal_nat_mul]
      _ = ((n ^ (m + 1) : Nat) : Cardinal) := by
        rw [Nat.pow_succ]

theorem cardinal_nat_pow (m n : Nat) :
    (n : Cardinal) ^ (m : Cardinal) =
      ((n ^ m : Nat) : Cardinal) := by
  rw [← cardinal_fin m, ← cardinal_fin n, ← cardinal_arrow]
  exact cardinal_fin_arrow m n
```

```savedLean
example : cardinal (Fin 2 → Fin 3) = 9 := by
  rw [cardinal_fin_arrow]
  rfl
```

# 무한집합
%%%
tag := "cardinality-infinite-comparisons"
%%%

서로 다른 원소를 겹치지 않게 대응시키면 한 집합이 다른 집합 안에 얼마나 들어가는지 비교할 수 있다.
먼저 이 비교를 기수의 부등식으로 표현한 뒤, 유한한 번호를 붙일 수 없는 집합들을 살펴보자.

## 단사함수와 크기 비교
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
  apply injective_compose
  · exact hFirst
  · exact hb.inj
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
    apply cardinalityLE_transport hA hB
    exact hf

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

*보기* 두 개의 번호를 세 개의 번호 안으로 값이 바뀌지 않게 넣으면 단사함수를 얻는다.
`i.castSucc`는 번호의 범위를 `Fin 2`에서 `Fin 3`으로 넓히므로 이 함수를 사용하자.

```lean
example : cardinal (Fin 2) ≤ cardinal (Fin 3) := by
  apply (cardinal_le_iff _ _).mpr
  exists (fun i : Fin 2 => i.castSucc)
  intro i j hij
  apply_fun (fun x => x.val) at hij
  ext
  exact hij
```

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
  apply injective_compose f g
  · exact hf
  · exact hg
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

유한한 번호 사이에서는 이미 `fin_injective_le`로 이러한 비교를 사용했다.
이제 단사함수에 의한 비교를 무한집합에도 적용하자.

## 무한성과 자연수
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
  apply injective_compose f r
  · exact hf
  · exact hr.inj
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
  symm at hAB
  exact isFinite_transport hAB hB
```

### 연습문제: 유한성과 무한성

*문제 13* (유한집합과 무한집합의 구별)

$`A`가 무한집합이고 $`B`가 유한집합이면 두 집합의 크기가 다름을 증명하라.
크기가 같다고 가정하여 유한성을 옮기면 어떤 모순이 생기는지 살펴보라.

```savedLean -keep
theorem exercise_infinite_finite_ne_cardinal {A B : Type}
    (hA : IsInfinite A)
    (hB : IsFinite B) :
    cardinal A ≠ cardinal B := by
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

*문제 14* (순서쌍 집합의 무한성)

자연수의 순서쌍 전체가 무한집합임을 증명하라.
자연수에서 오는 단사함수를 하나 구성하여 `infinite_of_nat_injection`을 사용하라.
선택한 함수가 전사일 필요가 없는 이유도 설명하라.

```savedLean -keep
theorem exercise_nat_pairs_infinite :
    IsInfinite (Nat × Nat) := by
  sorry
```

## 가산무한집합
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
    apply_fun (fun x => x.val) at hxy
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
`apply_fun (fun x => x.val) at hxy`로 $`x+1=y+1`을 얻는다.
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
  apply infinite_of_nat_injection f
  exact hf.inj

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
  apply countablyInfinite_isInfinite
  exact evens_countablyInfinite
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

*문제 15* (부분집합의 상과 크기)

단사함수 $`f:A\to B`와 집합 $`S\subseteq A`가 주어져 있다.
아래 함수는 $`S`의 원소 $`x`를 $`f(S)`의 원소 $`f(x)`로 보낸다.

(1) 이 함수가 전단사임을 증명하라.

(2) 첫 결과를 사용하여 $`S`와 $`f(S)`의 크기가 같음을 보이라.

(3) 둘째 결과와 양의 자연수 집합의 가산무한성을 사용하여
양의 자연수를 두 배 한 값들의 집합도 가산무한임을 보이라.

```savedLean -keep
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
```

### 연습문제: 자연수의 꼬리
%%%
tag := "cardinality-countable-practice"
%%%

양의 자연수에 사용한 대응을 바꾸어 다음 집합의 크기를 확인해 보자.

*문제 16* $`\{n\in\mathbb{N}:2\leq n\}`이 가산무한집합임을 증명하라.

```savedLean -keep
theorem exercise_from_two_countably_infinite :
    IsCountablyInfinite
    (Elem (fun n : Nat => 2 ≤ n)) := by
  sorry
```

*문제 17* (등차수열과 가산무한집합)

집합 $`S=\{1,4,7,10,\ldots\}`을 $`3k+1` 꼴의 자연수로 정의한다.

(1) 아래 함수가 자연수에서 $`S`의 원소 타입으로 가는 전단사임을 증명하라.

(2) 첫 결과로 $`S`가 가산무한집합임을 보이라.

(3) $`S`가 자연수 전체와 같은 집합은 아님을 보이라.
집합의 같음과 크기의 같음을 구별하라.

아래 정의에서 `y : Elem practiceOneModThree`이면
`y.property`는 `∃ k, y.val = 3 * k + 1`의 증명이다.
짝수 집합의 전사성을 증명할 때와 같이 이 번호를 꺼내 사용할 수 있다.

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

### 가장 작은 무한기수
%%%
tag := "cardinality-infinite-converse"
%%%

{anchor "cardinality-least-infinite"}[]자연수에서 $`A`로 가는 단사가 있으면 $`A`가 무한임을 보였다.
선택공리를 사용하면 모든 무한집합에 이러한 단사가 존재한다. 원소를 서로 다르게 하나씩 골라
$`a_0,a_1,\ldots`로 나열하는 것이 그 구성이다.

이미 $`a_0,\ldots,a_{n-1}`을 골랐다고 하자.
이들이 $`A`의 모든 원소라면 $`i↦a_i`가 `Fin n`에서 `A`로 가는 전단사이므로 $`A`는 유한집합이다.
따라서 무한집합에는 아직 고르지 않은 원소가 있고 이를 다음 원소 $`a_n`으로 택할 수 있다.
처음에는 아무 원소도 고르지 않았으므로 같은 논리로 첫 원소도 택할 수 있다.
이 선택을 자연수 단계마다 이어 가면 서로 다른 번호에 서로 다른 원소를 대응시키는 단사를 얻는다.

각 단계에서 다음 원소가 존재한다는 사실은 무한성에서 얻으며,
모든 단계의 선택을 하나의 함수로 정하는 데 선택공리를 사용한다.
이에 따라 모든 무한집합 $`A`에 대하여 $`|\mathbb{N}|≤|A|`이므로
자연수의 기수 $`\aleph_0`가 가장 작은 무한기수이다.
여기서는 이 구성의 수학적 논증을 설명했으며 Lean 코드에서는 앞서 증명한 역방향만 사용한다.

# 멱집합
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

*문제 18* $`\mathcal{P}(S\cap T)=\mathcal{P}(S)\cap\mathcal{P}(T)`임을 증명하라.

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
  apply (cardinal_le_iff A (Set A)).mp
  apply cardinal_le_powerSet
```

이 단사로 $`|A|\leq|\mathcal{P}(A)|`를 얻었다.
이제 두 기수가 같을 수 없음을 보이면 멱집합의 기수가 더 크다는 결론을 얻는다.


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
    intro hin
    apply hin
    rw [ha]
    exact hin

  -- a ∉ D에서 다시 a ∈ D를 얻는다.
  have hin : a ∈ D := by
    expand
    rw [ha]
    exact hnot

  exact hnot hin
```

첫 `have`에서 `hin : a ∈ D`의 원소 조건은 `a ∉ f a`이다.
따라서 `apply hin`을 쓰면 모순을 보이는 목표 `False`가 `a ∈ f a`로 바뀐다.
`ha : f a = D`를 대입하면 `a ∈ D`가 되어 원래 가정으로 증명할 수 있다.

둘째 `have`에서는 `expand`로 `D`의 원소 조건을 펼친 뒤 같은 등식을 대입한다.
이때 목표는 `a ∉ D`이므로 앞에서 얻은 `hnot`으로 마친다.
최종적으로 `hnot : a ∉ D`와 `hin : a ∈ D`를 함께 사용하여 모순을 얻는다.

이제 전단사가 존재한다고 가정하면 그 전사성이 방금 증명한 정리와 모순이므로
멱집합과 원래 집합의 크기가 같을 수 없다.

```savedLean
theorem powerSet_not_sameCardinality (A : Type) :
    ¬ SameCardinality A (Set A) := by
  intro h
  unpack h with ⟨f, hf⟩
  apply cantor_not_surjective f
  exact hf.surj
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

자연수에서 시작하여 멱집합을 거듭 만들면 다음과 같이 크기가 커진다.

$$`|\mathbb{N}|<|\mathcal{P}(\mathbb{N})|<|\mathcal{P}(\mathcal{P}(\mathbb{N}))|<\cdots.`

이처럼 무한집합 사이에서도 크기의 차이가 생긴다.

## 멱집합과 거듭제곱
%%%
tag := "cardinality-characteristic-functions"
%%%

부분집합을 정하는 일은 각 원소를 포함할지 말지 정하는 일이다.
Lean의 `Bool`은 두 값 `false`, `true`를 갖는 타입이다.
포함하면 `true`, 포함하지 않으면 `false`를 대응시키면 부분집합마다 `Bool` 값 함수를 얻는다.
거꾸로 주어진 함수가 `true`인 원소들을 모으면 원래 부분집합을 되찾는다.
이 함수는 집합의 *특성함수*이다.

```savedLean
noncomputable def characteristic {A : Type}
    (S : Set A) : A → Bool :=
  fun x => if x ∈ S then true else false

def trueSet {A : Type} (f : A → Bool) : Set A :=
  fun x => f x = true

theorem trueSet_characteristic {A : Type} (S : Set A) :
    trueSet (characteristic S) = S := by
  ext x
  by_cases hx : x ∈ S
  · simp [trueSet, characteristic, hx]
  · simp [trueSet, characteristic, hx]

theorem characteristic_trueSet {A : Type} (f : A → Bool) :
    characteristic (trueSet f) = f := by
  ext x
  cases hx : f x with
  | false => simp [characteristic, trueSet, hx]
  | true => simp [characteristic, trueSet, hx]
```

`cases hx : f x with`는 `f x`의 값에 따라 경우를 나누면서
각 경우에 그 값이 `false` 또는 `true`라는 등식도 `hx`로 남긴다.
집합의 소속 조건을 판정하여 함수를 만들었으므로 `characteristic`에는 고전논리를 사용한다.

`Bool`과 `Fin 2`를 연결할 때는 `false`에 $`0`, `true`에 $`1`을 대응시킨다.
반대 방향에서는 번호가 $`1`인지를 확인한다.

```savedLean
theorem bool_cardinal : cardinal Bool = 2 := by
  ext
  exists fun b => if b then (1 : Fin 2) else 0
  apply bijective_of_inverse _
    (fun i => if i.val = 1 then true else false)
  · intro b
    cases b with
    | false => rfl
    | true => rfl

  · intro i
    have hi : i.val = 0 ∨ i.val = 1 := by arith
    rcases hi with hi | hi
    · ext
      simp [hi]

    · ext
      simp [hi]
```

`Bool`에는 `false`, `true` 두 원소가 있으므로 `bool_cardinal : cardinal Bool = 2`이다.
특성함수와 그 역방향으로 얻은 전단사에 함수 공간의 계산 정리를 적용하면 멱집합의 크기를 구할 수 있다.

```savedLean
theorem cardinal_set (A : Type) :
    cardinal (Set A) = (2 : Cardinal) ^ cardinal A := by
  rw [← bool_cardinal, ← cardinal_arrow]
  ext
  exists characteristic
  apply bijective_of_inverse _ trueSet
  · exact trueSet_characteristic
  · exact characteristic_trueSet
```

*문제 19* (세 원소 집합의 부분집합)

(1) 세 원소 집합에서 `Bool`로 가는 함수가 여덟 개임을 보이라.

(2) 특성함수와의 대응을 사용하여 세 원소 집합의 부분집합도 여덟 개임을 보이라.

```savedLean -keep
theorem exercise_three_boolean_choices :
    cardinal (Fin 3 → Bool) = 8 := by
  sorry

theorem exercise_three_powerSet :
    cardinal (Set (Fin 3)) = 8 := by
  sorry
```

이 대응은 무한집합에도 성립한다. 따라서 앞에서 증명한 칸토어 정리를 기수의 거듭제곱으로
$`|A|<2^{|A|}`라고 나타낼 수 있다.

## 연습문제: 멱집합
%%%
tag := "infinite-cardinality-exercises"
file := "exercises"
%%%

각 문제의 `sorry`를 증명으로 바꾸어 완성하라.

*문제 20* (멱집합의 포함 관계)

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

*문제 21* (한 원소 집합들을 나열한 경우)

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

*문제 22* (자연수 집합의 부분집합들)

(1) 자연수 집합의 모든 부분집합으로 이루어진 타입 `Set Nat`가 무한임을 증명하라.

(2) 이 타입이 가산무한집합은 아님을 보이라.
따라서 무한집합끼리도 크기가 다를 수 있다.

```savedLean -keep
theorem exercise_powerSet_nat_infinite :
    IsInfinite (Set Nat) := by
  sorry

theorem exercise_powerSet_nat_not_countable :
    ¬ IsCountablyInfinite (Set Nat) := by
  sorry
```

# 크기 비교의 자동화
%%%
tag := "infinite-cardinality-automation"
%%%

{anchor "cardinality-automation"}[]
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
  fin_sameCardinality_eq cardinal_fin_eq
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
