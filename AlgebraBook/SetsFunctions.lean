import AlgebraBook.Meta.Lean
import AlgebraBook.Meta.Notation
import AlgebraBook.Tactic.Auto
import AlgebraBook.Tactic.Classical
import AlgebraBook.Tactic.Ext
import AlgebraBook.Tactic.Rules
import AlgebraBook.Tactic.Unfold
import Lean.Elab.Tactic.Ext
import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open AlgebraBook

#doc (Manual) "집합과 함수" =>

%%%
tag := "sets-functions"
file := "sets-functions"
%%%

두 집합이 같음을 보일 때는 어느 원소가 속하는지 비교한다.
집합의 포함 관계나 교집합의 성질도 원소에 관한 명제로 바꾸면 앞 장에서 배운 방법으로 증명할 수 있다.
이 장에서는 집합을 이러한 원소 조건으로 나타내고, 집합 사이의 함수를 다룬다.
함수가 어떤 값을 갖는지 살펴보면서 상과 역상, 단사와 전사, 역함수의 관계를 알아보자.

{anchor "sets"}[]
```savedImport
import AlgebraBook.Meta.Notation
import AlgebraBook.Tactic.Classical
import AlgebraBook.Tactic.Auto
import Lean.Elab.Tactic.Ext
import AlgebraBook.Tactic.Ext
import AlgebraBook.Tactic.Rules
import AlgebraBook.Tactic.Unfold
```

```savedLean -show
namespace Ample
```

# 집합과 술어
%%%
tag := "sets-sets-as-predicates"
file := "sets-as-predicates"
%%%

양의 자연수들을 모으면 다음 집합을 얻는다.

$$`\{n \in \mathbb{N} : 0 < n\}`

이 집합은 술어 `positive`의 조건을 만족하는 자연수들을 모은 것이다.
$`\mathbb{N}`에는 Lean의 `Nat`와 마찬가지로 $`0`도 포함된다.

일반적으로 $`A` 위의 술어 $`P`가 주어졌을 때,
$`P(x)`가 성립하는 원소 $`x`들을 모은 집합을 $`S_P`라 하면 다음과 같다.

$$`S_P = \{x \in A : P(x)\}, \qquad x \in S_P \iff P(x).`

따라서 $`x \in S_P`를 보이는 것은 $`P(x)`를 보이는 것과 같다.
반대로 집합 $`S`가 주어지면 “$`x \in S`”가 $`x`에 관한 술어가 된다.
이처럼 집합은 어느 원소가 속하는지를 나타내는 술어로 표현할 수 있으므로,
Lean에서 사용할 집합도 이 방식으로 정의하겠다.

```savedLean
def Set (A : Type _) := A → Prop
```

```savedLean -show
attribute [implicit_reducible] Set
```

`Set A`는 `A → Prop`의 다른 이름으로, `A`의 원소들로 이루어진 집합을 `A` 위의 술어로 나타낸다.
`A`는 원소의 타입을 정하며, `Type _`의 `_`는 타입의 수준을 Lean이 추론하도록 둔 표시이다.
`S : Set A`일 때 `S x`는 $`x`가 $`S`에 속한다는 명제이다.
예를 들어 `Set Nat`은 자연수의 부분집합들을 나타내는 타입이다.

앞 장의 {ref "intro-predicates"}[술어]와 같은 조건을 사용한다. 아래 `positive`도 자연수가 양수라는 명제이다.

```savedLean
def positive : Nat → Prop := fun n => 0 < n
```

*보기* 이 술어로 양의 자연수의 집합 `positives`를 정의하자.

```savedLean
def positives : Set Nat := positive
```

`Set Nat`는 `Nat → Prop`이므로 술어 `positive`를 그대로 사용할 수 있다.
여기서는 조건을 나타낼 때의 이름과 집합을 나타낼 때의 이름을 구별하여 붙였다.
`positives n`의 정의를 펼치면 `positive n`, 곧 `0 < n`이므로
`positives`가 바로 위의 집합 $`\{n \in \mathbb{N} : 0 < n\}`이다.

## 원소 표기와 타입
%%%
tag := "sets-membership-notation"
file := "membership-notation"
%%%

`x ∈ S`는 `S x`, 곧 원소 `x`가 집합 `S`의 조건을 만족한다는 명제이다.
아래 `instance`는 이 표기를 정의에 연결한다. 처음에는 세부 문법보다 기호가 뜻하는 원소 조건에 주목하자.
뒤의 집합 기호도 같은 방식으로 정의에 연결한다.

```savedLean
instance {A : Type _} : Membership A (Set A) where
  mem S x := S x
```

{anchor "sets-types-and-sets"}[]양의 자연수의 집합에 속하는 원소를 다룰 때는
자연수 `n : Nat`를 정하고 `n ∈ positives`가 성립하는지 살펴본다.
여기서 `n : Nat`는 `n`의 타입을 밝히며,
`n ∈ positives`는 그 자연수가 양수라는 명제이다.
이 명제는 `n`이 양수인지 확인하기 전에도 쓸 수 있다.
예를 들어 `0 ∈ positives`도 명제이며 그 뜻은 `0 < 0`이다.
`0 ∈ positives`는 쓸 수 있는 명제이지만 참인 명제는 아니다.
자연수 `n`이 실제로 이 집합에 속한다고 주장하려면 `h : n ∈ positives`와 같은 증명이 필요하다.

일반적으로 `S : Set A`에서 타입 `A`는 어떤 대상을 원소로 다루는지 정하고,
집합 `S`는 그 원소에 대한 조건을 정한다.
`x : A`가 주어지면 `x ∈ S`라는 명제를 만들 수 있으며,
그 명제를 증명하여 `x`가 `S`에 속함을 보인다.
앞의 예에서 `Nat`은 자연수의 타입이고 `positives`는 그 위에 정의한 집합이다.
또한 `Set Nat`은 `positives`를 비롯한 자연수의 부분집합들이 속하는 타입이다.

## 정의와 원소 조건
%%%
tag := "sets-membership-simplification"
%%%

```savedLean -show
@[simp] theorem mem_def {A : Type} (S : Set A) (x : A) :
    (x ∈ S) = S x := rfl
attribute [ample_arith_simp] mem_def positives positive
```

`positives`의 정의를 읽으면 양수라는 조건을 알 수 있다.
증명 중에도 그 조건을 직접 보고 싶으면 `expand`로 정의를 한 층 펼친다.

```savedLean
example (n : Nat)
    (h : n ∈ positives) :
    0 < n := by
  expand at h
  -- h : positive n
  expand at h
  -- h : 0 < n
  exact h
```

첫 호출은 `positives`를, 둘째는 `positive`를 펼친다.
정의상 같은 명제이므로 이 예제는 처음부터 `exact h`로도 증명할 수 있다.
위 두 단계는 원소 조건이 어떻게 정해지는지 확인하기 위해 적었다.

정의 이름을 직접 지정하려면 `dsimp [positives] at h`와 `dsimp [positive] at h`를 차례로 쓴다.
어떤 표현으로 바꿀지 알고 있을 때는 `change 0 < n at h`로 한 번에 바꿀 수도 있다.
둘 다 정의상 같은 표현으로 바꾸며, 등식 정리를 사용한 변환은 뒤에서 배울 `rw`로 수행한다.

## 전체집합과 공집합
%%%
tag := "sets-universal-and-empty-sets"
file := "universal-and-empty-sets"
%%%

타입 $`A`의 모든 원소를 모은 집합이 전체집합이고, 원소가 하나도 없는 집합이 공집합이다.
집합을 술어로 나타내고 있으므로 전체집합의 조건은 항상 참이고 공집합의 조건은 항상 거짓이다.
Lean에서 항상 참인 명제는 `True`, 거짓인 명제는 `False`로 쓴다.

```savedLean
def whole (A : Type) : Set A := fun _ => True
def empty (A : Type) : Set A := fun _ => False
instance {A : Type} : EmptyCollection (Set A) where
  emptyCollection := empty A
```

두 함수에서는 원소의 값이 필요하지 않으므로 `fun _ => ...`와 같이 이름을 생략했다.
자연수의 전체집합은 `whole Nat`, 공집합은 `empty Nat`로 쓴다.
이때 `Nat`은 자연수의 타입이고 `whole Nat : Set Nat`은 모든 자연수를 포함하는 집합이다.
원소 조건이 항상 참이므로 어느 `n : Nat`에 대해서도 `n ∈ whole Nat`이 성립한다.

마지막 `instance`는 공집합의 기호 `∅`를 `empty A`에 연결한다.
`∅`만으로 원소의 타입을 알 수 없을 때는 `(∅ : Set Nat)`와 같이 타입을 덧붙이며,
이 경우에는 `empty Nat`와 같은 집합을 나타낸다.

# 포함 관계와 함의의 증명
%%%
tag := "sets-subsets"
file := "subsets"
%%%

*정의* 집합 $`S`의 모든 원소가 집합 $`T`의 원소이면 $`S`가 $`T`의
*부분집합*이라고 한다. 이를 $`S \subseteq T`로 나타낸다.

```savedLean
def Subset {A : Type} : Set A → Set A → Prop :=
  fun S T => ∀ x, x ∈ S → x ∈ T
instance {A : Type} : HasSubset (Set A) where
  Subset := Ample.Subset
```

앞에서와 같이 기호와 정의를 연결했으므로,
`S ⊆ T`는 `Subset S T`, 곧 `∀ x, x ∈ S → x ∈ T`를 뜻한다.

따라서 `S ⊆ T`를 증명하려면 임의의 원소 $`x`를 택하고,
$`x \in S`를 가정하여 $`x \in T`를 보이면 된다.

*정리* 모든 집합은 자기 자신의 부분집합이다.

*증명* 임의의 원소 $`x`에 대하여 $`x \in S`를 가정하면,
보일 명제도 $`x \in S`이므로 이 가정을 그대로 쓰면 된다.

{anchor "sets-proving-universal-statements-and-implications"}[]1장에서 배운 {ref "proofs-universal-statements"}[전칭명제의 증명]처럼
`intro x`로 임의의 원소를 도입한다. 이 정리에서는 남은 목표가 `x ∈ S → x ∈ S`이므로
`intro hx`로 전제도 가정으로 받는다.

```savedLean
theorem subset_refl {A : Type} (S : Set A) :
    S ⊆ S := by
  expand
  -- 포함 관계: ∀ x : A, x ∈ S → x ∈ S
  intro x
  intro hx
  exact hx
```

`theorem`으로 정리에 이름을 붙였으므로,
이후에는 `subset_refl S`로 이 포함 관계의 증명을 사용할 수 있다.

```savedLean -show
attribute [simp] subset_refl
```

각 증명 단계에서 가정과 목표는 다음과 같이 변한다.

1. `expand`로 포함 관계의 정의를 펼치면 전칭명제 `∀ x : A, x ∈ S → x ∈ S`를 얻는다.
2. `intro x`로 임의의 원소 `x : A`를 택하면 목표는 `x ∈ S → x ∈ S`가 된다.
3. `intro hx`로 가정 `hx : x ∈ S`를 도입하면 남은 목표는 `x ∈ S`이다.
4. `exact hx`로 목표 `x ∈ S`의 증명을 제시하여 마친다.

이 예제의 `expand`는 목표에 들어 있는 전칭명제의 구조를 보여 주기 위해 썼다.
Lean은 `intro`를 처리할 때도 포함 관계의 정의를 펼치므로,
`expand`를 생략하고 바로 `intro x`와 `intro hx`를 써도 된다.

`intro x`와 `intro hx`는 `intro x hx`로 한 번에 쓸 수 있으며,
이후 증명에서는 두 단계를 이렇게 묶어 쓰겠다.
웹에서는 증명 코드의 전술을 눌러 각 단계의 가정과 목표를 확인할 수 있다.

## 전체집합과 공집합의 포함 관계
%%%
tag := "sets-basic-subsets"
%%%

전체집합과 공집합의 원소 조건은 각각 `True`와 `False`이므로
이 두 명제를 증명에 사용하는 방법을 살펴보자.

*정리* 모든 집합은 전체집합의 부분집합이다.

*증명* 임의의 원소 $`x \in S`를 택하면 $`x`는 $`A`의 원소이므로 전체집합에 속한다.
Lean에서 남은 목표 `x ∈ whole A`는 정의에 따라 `True`이다.
전술 `trivial`은 이처럼 참인 목표를 증명한다.

```savedLean
theorem subset_whole {A : Type} (S : Set A) :
    S ⊆ whole A := by
  intro x hx
  trivial
```

```savedLean -show
attribute [simp] subset_whole
```

*정리* 공집합은 모든 집합의 부분집합이다.

*증명* 임의의 원소 $`x`에 대하여 $`x \in \varnothing`라고 가정하자.
이 가정의 원소 조건은 `False`이므로 모순이다.
전술 `contradiction`은 이러한 가정을 사용하여 남은 목표를 증명한다.

```savedLean
theorem empty_subset {A : Type} (S : Set A) :
    ∅ ⊆ S := by
  intro x hx
  contradiction
```

```savedLean -show
attribute [simp] empty_subset
```

두 전술이 사용하는 원리를 직접 적을 수도 있다.
`True.intro`는 `True`의 증명이므로 첫 예제에서는 `exact True.intro`로 마칠 수 있다.
`False.elim`은 `False`의 증명에서 임의의 결론을 얻는 원리이므로,
둘째 예제에서는 `exact False.elim hx`로 같은 목표를 증명한다.

앞에서 증명한 세 포함 관계도 `simp`의 정리 규칙으로 등록되어 있다.
따라서 이후에는 `S ⊆ S`, `S ⊆ whole A`, `∅ ⊆ S`를 `simp`로 확인할 수 있다.

```savedLean
example {A : Type} (S : Set A) :
    S ⊆ S := by
  simp
```

## 포함 관계의 추이성
%%%
tag := "sets-using-subset-proofs"
file := "using-subset-proofs"
%%%

*정리* $`S \subseteq T`이고 $`T \subseteq U`이면 $`S \subseteq U`이다.

*증명* $`x \in S`라고 하면 $`S \subseteq T`이므로 $`x \in T`이다.
또한 $`T \subseteq U`이므로 $`x \in U`를 얻는다.

```savedLean
theorem subset_trans {A : Type} (S T U : Set A)
    (hST : S ⊆ T)
    (hTU : T ⊆ U) :
    S ⊆ U := by
  intro x hx
  have hxT : x ∈ T := by
    exact hST x hx

  exact hTU x hxT
```

`intro` 뒤에는 `hx : x ∈ S`가 주어지고 목표는 `x ∈ U`이다.
`hST x`는 `x ∈ S → x ∈ T`의 증명이므로 여기에 `hx`를 넣어 중간 증명 `hxT`를 얻는다.
이 증명을 `hTU x : x ∈ T → x ∈ U`에 넣은 `hTU x hxT`가 마지막 목표의 증명이다.

*문제 1* (포함 관계의 연결)

$`S\subseteq T`, $`T\subseteq U`, $`U\subseteq V`일 때 $`S\subseteq V`임을
`subset_trans`를 사용하여 증명하라.

```savedLean -keep
theorem exercise_subset_chain {A : Type} (S T U V : Set A)
    (hST : S ⊆ T)
    (hTU : T ⊆ U)
    (hUV : U ⊆ V) :
    S ⊆ V := by
  sorry
```

# 교집합과 논리곱
%%%
tag := "sets-intersections-and-conjunctions"
file := "intersections-and-conjunctions"
%%%

*정의* $`S`와 $`T`에 모두 속하는 원소로 이루어진 집합을 *교집합*이라고 한다.

교집합을 Lean으로 정의하려면 `x ∈ S`와 `x ∈ T`가 모두 성립한다는 조건을 나타내야 한다.
이를 위해 두 명제 $`P`와 $`Q`가 모두 성립한다는 명제인 *논리곱* `P ∧ Q`를 사용하며
교집합의 원소 조건은 `x ∈ S ∧ x ∈ T`로 쓴다.

```savedLean
def inter {A : Type} (S T : Set A) : Set A :=
  fun x => x ∈ S ∧ x ∈ T
instance {A : Type} : Inter (Set A) where
  inter := Ample.inter
```

`S ∩ T`는 `inter S T`이며, 원소 조건은 `x ∈ S ∧ x ∈ T`이다.
논리곱 `P ∧ Q`의 증명에는 `P`의 증명과 `Q`의 증명이 함께 들어 있다.
`h : P ∧ Q`에서 이들을 각각 `h.left`, `h.right`로 꺼낼 수 있으므로,
교집합의 원소라는 증명에서도 두 집합에 속한다는 사실을 따로 사용할 수 있다.
첫 번째 사실을 사용하여 교집합이 $`S`의 부분집합임을 보이자.

```savedLean
theorem inter_subset_left {A : Type} (S T : Set A) :
    S ∩ T ⊆ S := by
  intro x hx
  exact hx.left
```

가정 `hx`는 `x ∈ S ∧ x ∈ T`의 증명이므로
`hx.left`로 `x ∈ S`를 얻고 `hx.right`로 `x ∈ T`를 얻는다.

*문제 2* 교집합이 두 번째 집합의 부분집합임을 증명하라.

```savedLean -keep
theorem exercise_inter_subset_right
    {A : Type} (S T : Set A) :
    S ∩ T ⊆ T := by
  sorry
```

이번에는 두 조건을 모아 교집합에 속함을 증명해 보자.

*정리* $`x \in S \cap T`이면 $`x \in T \cap S`이다.

*증명* $`x \in S \cap T`라고 하면 $`x \in S`와 $`x \in T`를 모두 얻는다.
이 두 사실의 순서를 바꾸어 묶으면 $`x \in T \cap S`이다.

Lean에서도 `x ∈ T ∩ S`를 보이려면 `x ∈ T`와 `x ∈ S`를 모두 보여야 하므로
`constructor`를 써서 목표를 두 명제로 나눈다.
각 목표의 증명은 `·` 뒤에 적으며, `·`는 `\.`로 입력한다.

```savedLean
theorem inter_comm_forward {A : Type} (S T : Set A)
    (x : A) :
    x ∈ S ∩ T → x ∈ T ∩ S := by
  intro hx
  constructor
  · exact hx.right
  · exact hx.left
```

# 동치와 두 방향의 함의
%%%
tag := "sets-equivalence"
file := "equivalence"
%%%

앞의 교집합 증명처럼 포함 관계 $`S \subseteq T`에서는 $`x \in S`로부터 $`x \in T`를 얻는 한쪽 방향만 보였다.
교집합의 순서를 바꾸어도 같은 원소를 갖는다는 것을 표현하려면 역방향도 필요하므로
먼저 두 방향의 함의를 함께 나타내는 *동치*를 살펴보자.

두 명제 $`P`와 $`Q`가 *동치*라는 것은
$`P \Rightarrow Q`와 $`Q \Rightarrow P`가 모두 성립한다는 뜻이며, Lean에서는 `P ↔ Q`로 쓴다.
수학에서 “$`P`일 필요충분조건은 $`Q`이다”라고 하는 것도 같은 뜻이다.
즉 `P`를 가정하여 `Q`를 보이고 `Q`를 가정하여 `P`를 보이면 된다.

{anchor "sets-proving-equivalence"}[]`hPQ : P → Q`와 `hQP : Q → P`가 주어졌다고 하자.
각 방향의 증명을 이미 갖고 있으므로 이를 묶으면 `P ↔ Q`를 얻는다.
이때 `constructor`를 쓰면 동치를 두 방향의 함의로 나누어 각각 증명할 수 있다.

```savedLean
example
    (P Q : Prop)
    (hPQ : P → Q)
    (hQP : Q → P) :
    P ↔ Q := by
  constructor
  · exact hPQ
  · exact hQP
```

`constructor`로 나뉜 목표는 `P → Q`와 `Q → P`이다.
목표가 여러 개로 나뉠 때는 `·` 뒤에 각 목표의 증명을 적으며,
첫 번째 목표는 `hPQ`로, 두 번째 목표는 `hQP`로 증명한다.

{anchor "sets-using-equivalence"}[]반대로 `h : P ↔ Q`가 있으면 `h.mp`로 `P → Q`의 증명을 얻고,
`h.mpr`로 `Q → P`의 증명을 얻는다.
따라서 `P`의 증명도 갖고 있다면 정방향인 `h.mp`를 사용하여 `Q`를 보일 수 있다.

```savedLean
example
    (P Q : Prop)
    (h : P ↔ Q)
    (hP : P) :
    Q := by
  apply h.mp
  exact hP
```

`apply h.mp` 이후에는 목표가 `P`로 바뀌므로 `exact hP`로 증명을 마친다.
역방향에서도 `h.mpr`를 사용하면 같은 방식으로 `Q`에서 `P`를 얻는다.

# 집합의 같음과 함수의 등식
%%%
tag := "sets-equality"
file := "equality"
%%%

두 집합이 같은 원소들을 가지면 두 집합은 같다.
따라서 $`S = T`를 보이려면 임의의 원소 $`x`가 $`S`에 속할 필요충분조건이
$`T`에 속하는 것임을 보이면 된다.
앞 절에서 배운 동치를 사용하면 이 조건을 `∀ x, x ∈ S ↔ x ∈ T`로 쓸 수 있다.
집합을 함수 `A → Prop`로 정의했으므로,
이 조건에서 `S = T`를 얻으려면 함수의 등식과 명제의 등식이 어떻게 증명되는지 알아야 한다.
먼저 함수의 등식을 증명하는 방법부터 살펴보자.

## 함수와 명제의 외연성
%%%
tag := "sets-function-extensionality"
%%%

두 함수 $`f, g : A \to B`가 모든 원소 $`x \in A`에서 같은 값을 가지면 두 함수는 같다.
이를 *함수의 외연성*이라고 하며 다음과 같이 나타낼 수 있다.

$$`\bigl(\text{모든 } x \in A \text{에 대하여 } f(x) = g(x)\bigr) \;\Longrightarrow\; f = g.`

Lean에서는 `funext x`로 임의의 원소 `x : A`를 도입하고
함수의 등식 `f = g`를 함수값의 등식 `f x = g x`로 바꾼다.

```savedLean
example (A B : Type) (f g : A → B)
    (h : ∀ x : A, f x = g x) :
    f = g := by
  funext x
  exact h x
```

1. 처음 목표인 `f = g`는 두 함수 자체가 같다는 명제이고, `h`는 모든 원소에서 함수값이 같다는 명제의 증명이다.
2. `funext x`를 쓰면 `x : A`가 도입되고, 목표는 이 원소에서의 등식 `f x = g x`가 된다.
3. `h x`는 전칭명제의 증명 `h`를 원소 `x`에서 사용한 것이므로 바로 그 등식의 증명이다.
   따라서 `exact h x`로 증명을 마친다.

{anchor "sets-proposition-extensionality"}[]이제 같은 방법으로 집합의 등식을 증명해 보자.
두 집합은 `A → Prop`의 함수이므로 먼저 `funext x`로 원소 하나에서의 값을 비교할 수 있다.
다음 코드는 이 단계에서 멈춘 미완성 증명이다.

```tryLean +error -keep
example {A : Type _} {S T : Set A}
    (h : ∀ x, x ∈ S ↔ x ∈ T) :
    S = T := by
  funext x
  have hx : S x ↔ T x := h x
```

이때 남은 목표와 가정에서 얻을 수 있는 증명을 나란히 적으면 다음과 같다.

:::table +header (align := left)
*
  * 구분
  * 명제
*
  * `funext x` 이후의 목표
  * `S x = T x`
*
  * 이미 얻은 증명 `hx`의 명제
  * `S x ↔ T x`
:::

`h x`로 얻은 동치에 `hx`라는 이름을 붙였으므로 `S x ↔ T x`의 증명은 이미 가지고 있다.
그러나 목표는 `S x = T x`이므로 `exact hx`로는 증명을 마칠 수 없다.
함수의 외연성으로 원소 하나에서의 비교까지는 왔지만,
그 원소에서 주어진 동치를 명제의 등식으로 바꾸는 단계가 남은 것이다.

`P ↔ Q`와 `P = Q`는 Lean에서 서로 다른 형태의 명제이다.
`P ↔ Q`는 두 방향의 함의이고, `P = Q`는 명제 `P`와 `Q`가 같다는 등식이다.
이 둘을 연결하는 원리가 *명제의 외연성*이며, Lean에서는 `propext`라고 한다.
`propext`에 `P ↔ Q`의 증명을 주면 `P = Q`의 증명을 얻는다.

```savedLean
example
    (P Q : Prop)
    (h : P ↔ Q) :
    P = Q := by
  apply propext
  exact h
```

`apply propext`는 결론 `P = Q`를 얻기 위해 필요한 전제 `P ↔ Q`를 새 목표로 삼는다.
이 새 목표는 가정 `h`로 증명할 수 있으므로 `exact h`로 증명을 마친다.
여기서는 두 명제의 정의를 펼쳐 비교하는 대신, 동치의 증명 `h`를 근거로 등식을 얻었다.

## 집합의 외연성
%%%
tag := "sets-proving-set-equality"
%%%

이제 `∀ x, x ∈ S ↔ x ∈ T`에서 `S = T`를 보이자.
`funext`로 집합의 등식을 원소별 명제의 등식으로 바꾸고,
`propext`로 그 등식을 원소 조건의 동치를 보이는 목표로 바꾸면 주어진 가정을 사용할 수 있다.

*정리* 모든 원소 $`x`에 대하여 $`x \in S \iff x \in T`이면 $`S = T`이다.

```savedLean
@[ext] theorem set_ext {A : Type _} {S T : Set A}
    (h : ∀ x, x ∈ S ↔ x ∈ T) : S = T := by
  funext x
  apply propext
  exact h x
```

1. 처음 목표인 `S = T`는 함수 `S`와 `T`의 등식이다.
2. `funext x`로 임의의 원소 `x : A`를 도입하면 목표는 함수값의 등식 `S x = T x`가 된다.
   원소 기호로 쓰면 두 명제 `x ∈ S`와 `x ∈ T`가 같다는 목표이다.
3. `apply propext`를 쓰면 목표가 `S x ↔ T x`, 곧 `x ∈ S ↔ x ∈ T`로 바뀐다.
4. `h x`는 전칭명제의 증명 `h`를 원소 `x`에서 사용한 것으로, 이 동치의 증명이다.
   따라서 `exact h x`로 모든 단계가 끝난다.

등식의 목표를 원소별 비교로 바꾸는 전술이 `ext`이다.
함수의 등식에서는 `ext x`를 `funext x` 대신 사용할 수 있다.
집합의 등식에서는 `funext x`와 `apply propext`를 대신하여 `x ∈ S ↔ x ∈ T`를 목표로 남긴다.

```savedLean
example (A B : Type) (f g : A → B)
    (h : ∀ x : A, f x = g x) :
    f = g := by
  ext x
  exact h x
```

정리 앞의 `@[ext]`는 `ext`가 이 정리를 찾아 사용하도록 등록하는 표시이다.

{anchor "sets-equality-from-subsets"}[]*정리* $`S \subseteq T`이고 $`T \subseteq S`이면 $`S = T`이다.

*증명* 임의의 원소 $`x`에 대하여 첫 번째 포함 관계로 $`x \in S \Rightarrow x \in T`를 얻고,
두 번째 포함 관계로 그 역방향을 얻는다.
따라서 두 집합의 원소 조건이 동치이므로 두 집합은 같다.

```savedLean
theorem set_eq_of_subset {A : Type} (S T : Set A)
    (hST : S ⊆ T)
    (hTS : T ⊆ S) :
    S = T := by
  ext x
  constructor
  · exact hST x
  · exact hTS x
```

`ext x`를 쓰면 임의의 원소 `x`에 대한 목표 `x ∈ S ↔ x ∈ T`가 남는다.
`constructor`로 이 동치를 두 방향의 함의로 나누면,
정방향은 `hST x`로, 역방향은 `hTS x`로 증명할 수 있다.

## 등식과 원소별 비교
%%%
tag := "sets-equality-comparisons"
%%%

이미 알고 있는 등식으로 목표나 가정을 바꾸는 전술이 `rw`이다.
함수의 등식 `h : f = g`에서 `f x = g x`를 얻으려면 등식에 따라 `f`를 `g`로 바꾸면 된다.
사용할 등식은 대괄호 안에 적는다.

```savedLean
example
    (A B : Type) (f g : A → B) (x : A)
    (h : f = g) :
    f x = g x := by
  rw [h]
```

`rw [h]`는 목표의 `f`를 `g`로 바꾸고, 남은 등식 `g x = g x`는 양변이 같으므로 증명을 마친다.
집합의 등식도 같은 방법으로 사용한다.
아래에서는 `hxS : x ∈ S`에 등식 `hST : S = T`를 사용하여 `hxS : x ∈ T`를 얻는다.

```savedLean
example {A : Type} (S T : Set A)
    (x : A)
    (hST : S = T)
    (hxS : x ∈ S) :
    x ∈ T := by
  rw [hST] at hxS
  exact hxS
```

`at hxS`는 등식을 사용할 가정을 지정한다.

등식의 방향만 바꾸려면 `symm`을 사용한다.
목표가 `b = a`일 때 `symm`을 쓰면 `a = b`가 새 목표가 되므로,
주어진 등식 `h : a = b`로 증명을 마칠 수 있다.

```savedLean
example (a b : Nat)
    (h : a = b) :
    b = a := by
  symm
  exact h
```

`symm at h`는 목표 대신 가정 `h`의 등식 방향을 바꾼다.

## 교집합의 교환법칙

{anchor "sets-intersection-equivalence"}[]앞의 정리에서는 $`x \in S \cap T`에서 $`x \in T \cap S`를 얻는 한 방향을 증명했다.
이 정리에서 $`S`와 $`T`의 순서를 바꾸면 역방향도 얻으므로,
두 방향을 묶어 원소 조건의 동치를 증명할 수 있다.

*정리* $`x \in S \cap T`일 필요충분조건은 $`x \in T \cap S`이다.

```savedLean
theorem inter_comm {A : Type} (S T : Set A) (x : A) :
    x ∈ S ∩ T ↔ x ∈ T ∩ S := by
  constructor
  · exact inter_comm_forward S T x
  · exact inter_comm_forward T S x
```

첫 번째 목표에서는 `inter_comm_forward S T x`로 정방향의 함의를 얻고,
두 번째 목표에서는 `inter_comm_forward T S x`로 역방향의 함의를 얻는다.

이를 집합의 등식으로 쓰려면 `ext x`를 사용한다.

```savedLean
theorem inter_comm_eq {A : Type} (S T : Set A) :
    S ∩ T = T ∩ S := by
  ext x
  exact inter_comm S T x
```

# 합집합과 논리합
%%%
tag := "sets-unions-and-disjunctions"
file := "unions-and-disjunctions"
%%%

*정의* $`S` 또는 $`T`에 속하는 원소로 이루어진 집합을 *합집합*이라고 한다.

합집합을 Lean으로 정의하려면 `x ∈ S`와 `x ∈ T` 중 적어도 하나가 성립한다는 조건을 나타내야 한다.
이를 위해 두 명제 $`P`와 $`Q` 중 적어도 하나가 성립한다는 명제인 *논리합* `P ∨ Q`를 사용하며
합집합의 원소 조건은 `x ∈ S ∨ x ∈ T`로 쓴다.

```savedLean
def union {A : Type} (S T : Set A) : Set A :=
  fun x => x ∈ S ∨ x ∈ T
instance {A : Type} : Union (Set A) where
  union := Ample.union
```

`S ∪ T`는 `union S T`이다. `x ∈ S ∪ T`를 보이려면 `x ∈ S`와 `x ∈ T` 중 하나를 보이면 된다.

*정리* $`S`는 $`S`와 $`T`의 합집합의 부분집합이다.

```savedLean
theorem subset_union_left {A : Type} (S T : Set A) :
    S ⊆ S ∪ T := by
  intro x hx
  left
  exact hx
```

목표는 `x ∈ S ∨ x ∈ T`이고, 가정 `hx`는 `x ∈ S`이다.
따라서 `left`로 왼쪽 명제를 선택하면 이 가정으로 증명할 수 있으며,
오른쪽 명제를 선택할 때는 `right`를 쓴다.

*정리* $`S`와 $`T`가 모두 $`U`의 부분집합이면 그 합집합도 $`U`의 부분집합이다.

합집합에 속한다는 가정에서는 두 원소 조건 중 적어도 하나가 성립함을 알 수 있다.
논리곱처럼 양쪽의 증명을 모두 꺼낼 수는 없으므로 어느 쪽이 주어지든 결론이 성립함을 보인다.
$`x\in S`인 경우에는 $`S\subseteq U`를, $`x\in T`인 경우에는 $`T\subseteq U`를 사용하면 된다.

```savedLean
theorem union_subset {A : Type} (S T U : Set A)
    (hSU : S ⊆ U)
    (hTU : T ⊆ U) :
    S ∪ T ⊆ U := by
  intro x hx
  cases hx with
  | inl hxS => exact hSU x hxS
  | inr hxT => exact hTU x hxT
```

이번에는 가정 `hx`가 `x ∈ S ∨ x ∈ T`이므로
`cases hx`로 $`x \in S`인 경우와 $`x \in T`인 경우를 나누어 생각한다.
`inl`은 첫 번째 경우, `inr`은 두 번째 경우이다.
첫 번째 경우에는 `hSU`, 두 번째 경우에는 `hTU`를 적용하여 $`x \in U`를 얻는다.

## 포함 관계와 교집합의 계산

*정리* $`S\subseteq T`이면 $`S\cap T=S`이다.

*증명* `inter_subset_left`에 따라 $`S\cap T\subseteq S`이다.
거꾸로 $`x\in S`이면 가정에 따라 $`x\in T`이기도 하므로 $`x\in S\cap T`이다.
두 포함 관계를 `set_eq_of_subset`에 사용하면 등식을 얻는다.

```savedLean
theorem inter_eq_left_of_subset {A : Type} (S T : Set A)
    (hST : S ⊆ T) :
    S ∩ T = S := by
  apply set_eq_of_subset
  · exact inter_subset_left S T
  · intro x hx
    constructor
    · exact hx
    · exact hST x hx
```

이 정리를 구체적인 집합의 교집합 계산에 사용하자.

*보기* $`S=\{2,3\}`과 양의 자연수의 집합 $`T`에 대하여 $`S\cap T=S`임을 보이자.
$`S`의 원소는 $`2` 또는 $`3`이므로 논리합으로 원소 조건을 나타낼 수 있다.

```savedLean
def twoThree : Set Nat := fun n => n = 2 ∨ n = 3
```

두 수가 모두 양수이므로 $`S\subseteq T`이다.
이 포함 관계를 먼저 증명한 뒤 앞의 교집합 정리에 사용하자.

```savedLean
theorem twoThree_subset_positives :
    twoThree ⊆ positives := by
  intro n hn
  cases hn with
  | inl hTwo =>
      rw [hTwo]
      expand
      expand
      decide

  | inr hThree =>
      rw [hThree]
      expand
      expand
      decide

example : twoThree ∩ positives = twoThree := by
  exact inter_eq_left_of_subset twoThree positives
    twoThree_subset_positives
```

첫 증명은 `n = 2`와 `n = 3`으로 경우를 나눈다.
각 경우에 원소를 해당 수로 바꾸고 `positives`와 `positive`를 펼치면
각각 `0 < 2`와 `0 < 3`이 남는다.
이로써 포함 관계를 얻었으므로 둘째 증명에서는 `inter_eq_left_of_subset`에
두 집합과 포함 관계의 증명을 넣어 교집합을 구한다.

*문제 3* (포함 관계와 합집합)

(1) $`S\subseteq T`이면 $`S\cup T=T`임을 증명하라.

(2) 첫 결과와 본문의 `twoThree_subset_positives`를 사용하여
$`\{2,3\}\cup\mathbb{N}_{>0}=\mathbb{N}_{>0}`임을 보이라.

```savedLean -keep
theorem exercise_union_eq_right {A : Type} (S T : Set A)
    (hST : S ⊆ T) :
    S ∪ T = T := by
  sorry

theorem exercise_twoThree_union_positives :
    twoThree ∪ positives = positives := by
  sorry
```

*문제 4* (흡수법칙)

$`S\cap(S\cup T)=S`임을 증명하라.
원소별로 두 방향을 보인 뒤, 본문의 `inter_eq_left_of_subset`을 사용한 증명도 작성하라.

```savedLean -keep
theorem exercise_inter_union_absorb {A : Type}
    (S T : Set A) :
    S ∩ (S ∪ T) = S := by
  sorry
```

## 교집합의 분배법칙
%%%
tag := "sets-intersection-distributes-over-union"
%%%

교집합과 합집합이 함께 있으면 원소 조건에도 논리곱과 논리합이 함께 나타난다.
앞에서 배운 두 증명 방법을 다음 등식에 사용해 보자.

*보기* $`S\cap(T\cup U)=(S\cap T)\cup(S\cap U)`이다.

*풀이* 왼쪽 집합의 원소 $`x`는 $`S`에 속하며 $`T` 또는 $`U`에 속한다.
$`T`에 속하는 경우에는 $`S\cap T`에 속하고 $`U`에 속하는 경우에는 $`S\cap U`에 속하므로
어느 경우에도 오른쪽 합집합에 속한다.
거꾸로 오른쪽 집합의 원소는 $`S\cap T` 또는 $`S\cap U`에 속한다.
두 경우 모두 $`S`에 속하고 $`T\cup U`에도 속하므로 왼쪽 집합의 원소이다.

```savedLean
example {A : Type}
     (S T U : Set A) :
    S ∩ (T ∪ U) = (S ∩ T) ∪ (S ∩ U) := by
  -- 각 원소에서 두 집합의 원소 조건이 동치임을 보인다.
  ext x
  constructor
  · intro hx
    -- x가 T와 U 중 어디에 속하는지 나눈다.
    cases hx.right with
    | inl hxT =>
        -- x는 S ∩ T의 원소이다.
        left
        constructor
        · exact hx.left
        · exact hxT

    | inr hxU =>
        -- x는 S ∩ U의 원소이다.
        right
        constructor
        · exact hx.left
        · exact hxU

  · intro hx
    -- 두 교집합 중 어디에 속해도 S에 속한다.
    cases hx with
    | inl hxST =>
        constructor
        · exact hxST.left
        -- T에 속하므로 T ∪ U에도 속한다.
        · left
          exact hxST.right

    | inr hxSU =>
        constructor
        · exact hxSU.left
        -- U에 속하므로 T ∪ U에도 속한다.
        · right
          exact hxSU.right
```

정방향에서는 `hx.left`가 `x ∈ S`의 증명이고 `hx.right`가 `x ∈ T ∨ x ∈ U`의 증명이다.
따라서 `hx.right`로 경우를 나누면서 `hx.left`는 두 경우에 모두 사용한다.
역방향에서는 가정 자체가 논리합이므로 `cases hx`로 나눈 뒤
각 경우에 `constructor`로 `x ∈ S`와 `x ∈ T ∪ U`를 보인다.

# 여집합과 부정
%%%
tag := "sets-complements-and-negation"
file := "complements-and-negation"
%%%

*정의* $`A`의 원소 중 집합 $`S`에 속하지 않는 원소로 이루어진 집합을
$`S`의 *여집합*이라고 하며 $`S^{\mathsf{c}}`로 나타낸다.

여집합을 구할 때는 어떤 전체집합을 기준으로 삼는지 정해져 있어야 한다.
가령 $`S = \{1, 2\}`의 여집합은 자연수 전체를 기준으로 하면 $`\{0, 3, 4, \ldots\}`이고,
정수 전체를 기준으로 하면 여기에 음의 정수들도 포함된다.
Lean에서는 `S : Set A`의 `A`가 원소의 범위를 정하므로
여집합도 같은 타입 `A`의 원소들로 이루어진다.

이 절에서는 여집합의 원소 조건을 통해 부정의 증명과 사용을 익히고,
이를 바탕으로 여집합을 두 번 취하면 원래 집합을 얻는다는 성질을 증명한다.

{anchor "sets-negation"}[]여집합을 Lean으로 정의하려면 “$`x`가 $`S`에 속하지 않는다”라는 조건을 명제로 표현해야 한다.
명제 $`P`가 성립하지 않는다는 명제를 $`P`의 *부정*이라고 하며 Lean에서는 `¬ P`로 쓴다.
따라서 여집합의 원소 조건은 `¬ (x ∈ S)`이고,
이를 원소 관계의 기호와 함께 줄여 쓰면 `x ∉ S`이다.

수학에서 $`P`가 성립하지 않음을 보일 때는 $`P`가 성립한다고 가정한 뒤 모순을 이끌어 낸다.
앞에서 모순을 `False`로 나타냈듯이,
“`P`를 가정하면 모순이 나온다”는 주장은 함의 `P → False`로 나타낼 수 있으므로,
Lean에서는 이를 부정 `¬ P`의 정의로 사용한다.

목표가 `¬ P`이면 `P → False`를 증명하면 되므로,
`intro hP`로 `P`를 가정하고 목표를 `False`로 바꾼다.
주어진 가정들과 `hP`에서 모순을 이끌어 내면 `P`를 부정하는 증명이 완성된다.

한편 `P`의 증명 `hP`와 그 부정의 증명 `hnotP`가 모두 주어지면 모순을 보일 수 있다.
`hnotP`의 타입은 `P → False`이므로
목표가 `False`일 때 `apply hnotP`를 쓰면 `P`가 새 목표가 된다.

```savedLean
example
    (P : Prop)
    (hP : P)
    (hnotP : ¬ P) :
    False := by
  apply hnotP
  exact hP
```

`apply hnotP`와 `exact hP`는 `exact hnotP hP` 한 줄로도 쓸 수 있다.

등식의 부정 `¬ (a = b)`는 `a ≠ b`로 줄여 쓴다.
따라서 두 집합이 다르다는 목표 `S ≠ T`에서도 `intro h`로 `h : S = T`를 가정하고 모순을 보이면 된다.

이제 이 부정을 사용하여 여집합의 원소 조건을 `x ∉ S`로 정하자.

```savedLean
def compl {A : Type} (S : Set A) : Set A :=
  fun x => x ∉ S
instance {A : Type} : Complement (Set A) where
  complement := Ample.compl

postfix:max "ᶜ" => Complement.complement
```

`Sᶜ`는 `compl S`이며,
`x ∈ Sᶜ`는 `x ∉ S`, 곧 `x ∈ S → False`를 뜻한다.
증명 상태에서는 여집합의 원소 관계를 `x ∈ Sᶜ`로 표시하며,
`expand`로 그 정의를 펼치면 `x ∉ S`가 된다.

*보기* 한 원소가 $`S`와 그 여집합에 모두 속한다고 가정하면 모순이다.

```savedLean
example {A : Type}
     (S : Set A) (x : A)
    (hx : x ∈ S)
    (hxc : x ∈ Sᶜ) :
    False := by
  apply hxc
  exact hx
```

여기서는 앞의 예제에서 `P`를 `x ∈ S`로 바꾼 것이다.
`hxc`는 `x ∉ S`, 곧 `x ∈ S → False`의 증명이므로
`apply hxc`로 필요한 전제를 목표로 삼고 `exact hx`로 그 증명을 제시한다.

## 부정의 증명
%%%
tag := "sets-proving-negation"
file := "proving-negation"
%%%

여집합을 취하면 포함 관계의 방향이 바뀐다는 것을 증명하자.
원소가 집합에 속하지 않음을 보여야 하므로 그 집합에 속한다고 가정하여 모순을 얻는 방법을 사용한다.

*정리* $`S \subseteq T`이면 $`T^{\mathsf{c}} \subseteq S^{\mathsf{c}}`이다.

*증명* 임의의 원소 $`x \in T^{\mathsf{c}}`를 택하면 $`x \notin T`이다.
만약 $`x \in S`라고 가정하면 $`S \subseteq T`에 따라 $`x \in T`를 얻으므로 앞의 가정과 모순이다.
따라서 $`x \notin S`, 곧 $`x \in S^{\mathsf{c}}`이며, 원하는 포함 관계가 성립한다.

```savedLean
theorem compl_subset_compl {A : Type} (S T : Set A)
    (hST : S ⊆ T) :
    Tᶜ ⊆ Sᶜ := by
  intro x hxTc
  intro hxS
  have hxT : x ∈ T := by
    exact hST x hxS

  exact hxTc hxT
```

Lean에서도 같은 순서로 가정을 도입하고 모순을 얻으며, 각 줄의 역할은 다음과 같다.

1. `intro x hxTc`: 임의의 원소 `x`에 대하여 `x ∈ Tᶜ`를 가정하고, `x ∈ Sᶜ`를 새 목표로 삼는다.
2. `intro hxS`: 목표는 `x ∈ S → False`이므로 `x ∈ S`를 가정하며 이제 보일 것은 `False`이다.
3. `have hxT : x ∈ T := by`: 포함 관계의 증명 `hST`를 사용하여 `x ∈ T`를 보이고, 그 증명에 `hxT`라는 이름을 붙인다.
4. `exact hxTc hxT`: `hxTc`는 `x ∈ T → False`의 증명이므로 여기에 `hxT`를 적용하여 `False`를 얻는다.

*문제 5* (드모르간 법칙)

$`(S\cup T)^{\mathsf c}=S^{\mathsf c}\cap T^{\mathsf c}`임을 증명하라.
원소 조건을 이용하여 합집합에 속하지 않는다는 말이 두 집합 각각에 속하지 않는다는 말과 동치임을 보이라.

```savedLean -keep
theorem exercise_compl_union {A : Type} (S T : Set A) :
    (S ∪ T)ᶜ = Sᶜ ∩ Tᶜ := by
  sorry
```

## 이중 여집합
%%%
tag := "sets-subset-double-complement"
file := "subset-double-complement"
%%%

여집합을 두 번 취한 집합 $`(S^{\mathsf{c}})^{\mathsf{c}}`가 원래 집합 $`S`와 같음을 보이려면,
두 집합이 서로의 부분집합임을 증명하면 된다.
먼저 $`S \subseteq (S^{\mathsf{c}})^{\mathsf{c}}`를 보이자.

*증명* 임의의 원소 $`x \in S`를 택하자.
만약 $`x \in S^{\mathsf{c}}`라고 가정하면 $`x \notin S`이므로 처음의 가정과 모순이다.
그러므로 $`x \notin S^{\mathsf{c}}`, 곧 $`x \in (S^{\mathsf{c}})^{\mathsf{c}}`이며, 원하는 포함 관계를 얻는다.

```savedLean
theorem subset_compl_compl {A : Type} (S : Set A) :
    S ⊆ Sᶜᶜ := by
  intro x hxS
  intro hxSc
  exact hxSc hxS
```

`intro x hxS`로 $`x \in S`를 가정하면 남은 목표는 `x ∈ Sᶜᶜ`, 곧 `x ∈ Sᶜ → False`이다.
이를 보이기 위해 `intro hxSc`로 $`x \in S^{\mathsf{c}}`를 가정하면
`hxSc`는 `x ∈ S → False`의 증명이므로 `hxSc hxS`에서 모순을 얻는다.
명제의 관점에서 보면 $`P \Rightarrow \neg\neg P`를 증명한 것이며,
여기까지는 앞에서 배운 부정의 정의만으로 충분하다.

## 배중률과 귀류법
%%%
tag := "sets-classical-logic"
file := "classical-logic"
%%%

반대 방향인 $`(S^{\mathsf{c}})^{\mathsf{c}} \subseteq S`에서는,
`x ∈ Sᶜᶜ`를 가정하고 `x ∈ S`를 보여야 한다.
가정을 펼치면 `¬¬ (x ∈ S)`이므로 이번에는 이중 부정에서 원래 명제를 얻는 추론이 필요하다.
부정의 정의까지 풀어 보면 가정과 목표는 다음과 같다.

```
hxScc : (x ∈ S → False) → False
⊢ x ∈ S
```

앞의 증명에서는 목표가 함의여서 `intro`로 그 전제를 가정할 수 있었다.
이번 목표는 `x ∈ S`이므로 같은 방법으로 시작할 수 없다.
또한 `hxScc`는 `x ∉ S`의 증명을 받아 `False`를 주는 함수이므로,
이를 사용하려면 먼저 그 부정의 증명이 있어야 한다.
이 지점에서 원래 명제 `x ∈ S`를 얻기 위해 고전논리의 배중률을 사용하자.

*배중률*은 모든 명제 $`P`에 대하여 $`P \lor \neg P`가 성립한다는 원리로,
$`P`가 성립하거나 그 부정이 성립한다는 뜻이다.
`¬¬ P`를 알고 있을 때 배중률에 따라 두 경우로 나누면,
`P`인 경우에는 원하는 결론을 이미 얻었으며, `¬ P`인 경우에는 주어진 이중 부정과 모순이 생긴다.
따라서 고전논리에서는 `¬¬ P`로부터 `P`를 얻을 수 있다.

이 경우 구분을 Lean으로 적을 때는 `by_cases h : P`를 사용한다.
첫 번째 경우에는 `h : P`를, 두 번째 경우에는 `h : ¬ P`를 가정으로 갖고
각 경우에 원래 목표를 증명한다.
이중 여집합의 포함 관계에서도 원소 `x`가 `S`에 속하는지에 따라 두 경우를 나누자.

```savedLean
theorem compl_compl_subset {A : Type} (S : Set A) :
    Sᶜᶜ ⊆ S := by
  intro x hxScc
  by_cases hxS : x ∈ S
  · exact hxS
  · have hFalse : False := by
      exact hxScc hxS

    contradiction
```

첫 번째 경우에는 목표 `x ∈ S`의 증명 `hxS`가 주어져 있으므로 이를 그대로 사용한다.
두 번째 경우의 `hxS`는 `x ∉ S`의 증명이며
이를 `hxScc : ¬¬ (x ∈ S)`에 적용하면 모순을 얻는다.
`have hFalse : False := by`로 이 모순의 증명을 가정에 추가하면
`contradiction`으로 남은 목표 `x ∈ S`를 증명할 수 있다.
`by_cases`에서는 두 경우 모두 목표가 `x ∈ S`로 유지된다는 점을 확인하라.

이처럼 `¬¬ P`에서 `P`를 얻는 추론을 *이중 부정 제거*(DNE, double negation elimination)라고 한다.
Lean의 정리 `Classical.not_not`는 `¬¬ P ↔ P`의 증명이므로
그 정방향인 `Classical.not_not.mp`를 사용하면 이중 부정을 제거할 수 있다.
같은 포함 관계를 이중 부정 제거 정리로 증명하면 다음과 같다.

```savedLean
example {A : Type}
     (S : Set A) :
    Sᶜᶜ ⊆ S := by
  intro x hxScc
  apply Classical.not_not.mp
  exact hxScc
```

`apply Classical.not_not.mp`는 목표를 `¬¬ (x ∈ S)`로 바꾼다.
이 명제는 `x ∈ Sᶜᶜ`의 정의와 같으므로 가정 `hxScc`로 증명을 마친다.
정리의 증명에 가정을 직접 적용하면 `exact Classical.not_not.mp hxScc` 한 줄로도 쓸 수 있다.

같은 결론을 귀류법으로도 증명할 수 있다. 고전논리의 *귀류법*에서는 `P`를 보이기 위해 `¬ P`를 가정하고 모순을 이끌어 낸다.
이 논증으로 `¬¬ P`를 증명한 뒤 이중 부정 제거를 사용하면 원래 목표인 `P`를 얻는다.
Lean에서는 `by_contra`로 귀류법을 시작할 수 있다.
아래 증명에서 `by_contra hxNotS`를 쓰면 목표인 `x ∈ S`의 부정을 `hxNotS`로 가정하고
`False`를 새 목표로 삼아 이 귀류법을 시작한다.

```savedLean
example {A : Type}
     (S : Set A) :
    Sᶜᶜ ⊆ S := by
  intro x hxScc
  by_contra hxNotS
  exact hxScc hxNotS
```

`hxScc : ¬¬ (x ∈ S)`에 `hxNotS : ¬ (x ∈ S)`를 넣으면 모순을 얻는다.

부정을 증명하는 앞의 방법과 귀류법에서 무엇을 가정했는지 비교하라.
`¬ P`를 보일 때 `P`를 가정하는 것은 부정의 정의에 따른 것이며,
`P`를 보일 때 `¬ P`를 가정하는 귀류법에는 이중 부정 제거가 필요하다.

이제 두 집합이 서로의 부분집합임을 보였으므로,
앞의 정리 `set_eq_of_subset`를 사용하여 이중 여집합의 등식을 얻자.

*정리* 모든 집합 $`S`에 대하여 $`(S^{\mathsf{c}})^{\mathsf{c}} = S`이다.

```savedLean
theorem compl_compl_eq {A : Type} (S : Set A) :
    Sᶜᶜ = S := by
  apply set_eq_of_subset
  · exact compl_compl_subset S
  · exact subset_compl_compl S
```

`apply set_eq_of_subset`를 쓰면 목표가 `Sᶜᶜ ⊆ S`와 `S ⊆ Sᶜᶜ`로 나뉜다.
첫 번째 목표에는 고전논리로 증명한 `compl_compl_subset S`를,
두 번째 목표에는 부정의 정의로 증명한 `subset_compl_compl S`를 사용하여 등식의 증명을 마친다.

이후의 본문에서는 고전논리를 기본으로 사용하겠다.
파일에서 다음 선언을 적으면 그 뒤의 증명과 정의에서 고전논리를 사용할 수 있다.

```savedLean
open scoped Classical
```

`classical`은 한 증명 안에서 고전논리를 사용할 범위를 정하며
`open scoped Classical`은 선언한 범위 전체에 같은 설정을 적용한다.
이 선언은 다른 파일을 가져오는 `import`로 전달되지 않으므로
이후의 예제 코드와 연습문제 파일에도 같은 선언을 둔다.

자동 표현 정리는 이미 증명한 이중 부정 제거를 사용하여 `¬¬ P`를 `P`로 정리한다.
아래 `open scoped Ample.Auto`로 이를 켠다. 고전논리 설정은 앞의 선언을 그대로 사용한다.
따라서 이중 여집합의 원소 조건을 펼친 뒤에는 다음과 같이 포함 관계를 증명할 수 있다.
자동 표현 정리의 설정과 범위는 {ref "tactic-auto-normalization"}[자동 표현 정리]에서 설명한다.

```savedLean -show
section
```

```savedLean
open scoped Ample.Auto
```

```savedLean
example {A : Type}
     (S : Set A) :
    Sᶜᶜ ⊆ S := by
  intro x hxScc
  expand at hxScc
  expand at hxScc
  exact hxScc
```

두 번의 `expand at hxScc`로 여집합의 원소 조건을 차례로 펼치면 이중 부정이 자동으로 제거된다.
그러면 가정이 목표 `x ∈ S`와 같은 명제로 정리되므로 `exact hxScc`로 증명을 마친다.

```savedLean -show
end
```

## 차집합
%%%
tag := "sets-differences"
file := "differences"
%%%

*정의* $`S`에 속하면서 $`T`에는 속하지 않는 원소로 이루어진 집합을
$`S`와 $`T`의 *차집합*이라고 하며 $`S \setminus T`로 나타낸다.

차집합의 원소는 두 조건을 모두 만족해야 하므로
논리곱과 부정을 함께 사용하여 `x ∈ S ∧ x ∉ T`로 표현한다.

```savedLean
def diff {A : Type} (S T : Set A) : Set A :=
  fun x => x ∈ S ∧ x ∉ T
instance {A : Type} : SDiff (Set A) where
  sdiff := Ample.diff
```

`S \ T`는 `diff S T`이다. `x ∈ S \ T`의 증명에서는 첫 번째 조건으로 `x ∈ S`를 얻고,
두 번째 조건으로 `x ∉ T`를 얻는다.

*보기* 두 집합 $`S`, $`T`에 대하여 $`S \setminus T = S \cap T^{\mathsf{c}}`임을 보이자.

*증명* 임의의 원소 $`x`에 대하여 차집합과 교집합, 여집합의 정의를 사용하면 다음을 얻는다.

$$`x \in S \setminus T
\iff (x \in S \land x \notin T)
\iff x \in S \cap T^{\mathsf{c}}.`

두 집합의 원소 조건이 서로 동치이므로 앞에서 배운 `ext`로 원소 조건을 비교하자.

```savedLean
theorem diff_eq_inter_compl {A : Type} (S T : Set A) :
    S \ T = S ∩ Tᶜ := by
  ext x
  expand
  expand
```

`ext x`를 쓰면 임의의 원소에 대하여
`x ∈ S \ T ↔ x ∈ S ∩ Tᶜ`를 보이는 것이 목표가 된다.
`expand`로 차집합과 교집합, 여집합의 정의를 차례로 펼치면 양쪽이 모두 `x ∈ S ∧ x ∉ T`이므로
동치의 반사성으로 증명이 자동으로 끝난다.

*문제 6* $`S \setminus S`가 공집합의 부분집합임을 증명하라.

```savedLean -keep
theorem exercise_diff_self_subset_empty
    {A : Type} (S : Set A) :
    S \ S ⊆ ∅ := by
  sorry
```

## 원소의 타입과 러셀의 역설
%%%
tag := "advanced-set-types"
%%%

수학에서는 $`\{1, 2\}`처럼 집합을 쓰면서 원소가 속하는 범위를 따로 표시하지 않기도 한다.
그러나 Lean에서 집합을 술어로 정의하려면 어떤 타입의 원소에 그 조건을 적용할지 정해야 하므로
`Set A`의 `A`로 그 범위를 나타낸다.

원소의 범위를 구별하는 것은 집합을 아무 제한 없이 만드는 데서 생기는 모순과도 관련이 있다.
모든 집합을 원소로 갖는 집합 `U`가 있고,
그 안에서 조건을 만족하는 원소들을 골라 집합을 만들 수 있다고 가정해 보자.
그러면 다음과 같은 집합을 만들게 된다.

$$`R = \{S \in U : S \notin S\}.`

`R`은 자기 자신에 속하지 않는 집합들을 모은 것이다.
`U`는 모든 집합을 포함한다고 가정했으므로 `R`도 `U`에 속한다.
이제 `R`이 자기 자신에 속하는지 물어 보자.

`R`이 자기 자신에 속한다고 하면 `R`의 원소 조건에 따라 자기 자신에 속하지 않아야 한다.
반대로 자기 자신에 속하지 않는다고 하면 `R`도 `U`의 원소이고 그 조건을 만족하므로 `R`에 속해야 한다.
어느 쪽으로 생각해도 모순이 생기며, 이를 *러셀의 역설*이라고 한다.

이러한 모순을 피하려면 모든 집합을 한꺼번에 모으는 방식과
조건으로 집합을 만드는 방식을 아무 제한 없이 함께 허용해서는 안 된다.
이 교재에서는 원소의 타입 `A`를 먼저 정하고, 그 타입 위의 조건으로 집합을 만든다.
`S : Set A`는 `A`의 원소에 적용하는 함수이므로
타입이 다른 `S` 자신을 그대로 원소로 넣는 식은 쓸 수 없다.

집합을 원소로 갖는 집합을 만들 때는 원소의 타입도 집합의 타입으로 정한다.
예를 들어 `U : Set (Set Nat)`라고 하면 `U`의 원소는 `Set Nat` 타입의 집합, 곧 자연수의 집합이다.
이렇게 원소와 집합의 타입을 구별하므로 러셀의 역설에 등장한 `S ∈ S`를 그대로 만들 수 없다.

```savedLean -show
end Ample
```

```savedLean -show
export_course_compat
```

{anchor "functions"}[]

```savedLean -show
open scoped Classical
```

```savedLean -show
namespace Ample
```

# 정의역과 공역
%%%
tag := "functions-domain-and-codomain"
file := "domain-and-codomain"
%%%

*정의* 집합 $`A`의 각 원소 $`x`에 집합 $`B`의 원소 $`f(x)` 하나를 대응시키는 것을
$`A`에서 $`B`로 가는 *함수*라고 한다.
이때 $`A`를 *정의역*, $`B`를 *공역*이라고 하며 $`f : A \to B`로 나타낸다.

수학에서 함수의 정의역과 공역으로 삼는 대상을 Lean에서는 타입 `A`와 `B`로 나타내고,
함수의 타입을 `A → B`로 쓴다.
이 타입의 함수를 정의하려면 `A`의 모든 원소에 대해 `B`의 값 하나를 정해야 한다.
따라서 `f : A → B`와 `x : A`가 주어지면 `f x : B`를 얻는다.
집합 `S : Set A`에 속하는 원소만 정의역으로 삼는 방법은
{ref "functions-elements"}[집합 위의 함수]에서 다룬다.

*보기* 자연수 $`n`을 $`2n`에 대응시키는 함수를 정의하자.

```savedLean
def double (n : Nat) : Nat := 2 * n
```

`double`의 정의역과 공역은 모두 `Nat`이며 `double 3`의 값은 $`6`이다.
정의역의 자연수를 모두 넣어 보면 함수값으로 $`0, 2, 4, \ldots`를 얻는다.
이 값들을 모은 집합은 공역인 자연수 전체의 부분집합으로, 짝수인 자연수들로 이루어져 있다.

{anchor "functions-identity"}[]`double`은 값을 두 배로 바꾸는 함수이다.
값을 그대로 돌려주는 함수를 항등함수라고 한다.

*정의* 집합 $`A`의 각 원소를 그 자신에 대응시키는 함수를
$`A`의 *항등함수*라고 하며 $`\operatorname{id}_A`로 나타낸다.

```savedLean
def identity (A : Type) : A → A :=
  fun x => x
```

Lean에서는 `identity A`가 $`\operatorname{id}_A`이다.
정의에 따라 `identity A x = x`이므로 이 등식은 `rfl`로 증명한다.

```savedLean
example {A : Type}
    (x : A) :
    identity A x = x := by
  rfl
```

## 함수값과 함수의 같음
%%%
tag := "functions-equality"
%%%

원소의 등식 $`x=y`를 알고 있다면 함수값도 같아서 $`f(x)=f(y)`이다.
앞에서 배운 `rw`로 목표의 `x`를 `y`로 바꾸면 이 등식을 증명할 수 있다.

```savedLean
example {A B : Type}
    (f : A → B) (x y : A)
    (hxy : x = y) :
    f x = f y := by
  rw [hxy]
```

두 함수가 다름을 보일 때는 값이 다른 원소 하나를 찾으면 된다.
예를 들어 `double`과 항등함수는 $`1`에서 각각 $`2`와 $`1`을 갖는다.
함수가 같다고 가정한 뒤 `rw`로 이 함수값을 비교하면 모순을 얻는다.
`f ≠ g`는 `¬ (f = g)`를 뜻한다.

```savedLean
theorem double_ne_identity : double ≠ identity Nat := by
  intro h
  have hOne : double 1 = identity Nat 1 := by
    rw [h]

  contradiction
```

반대로 모든 원소에서 함수값이 같음을 보여 함수의 같음을 증명할 때는
{ref "sets-proving-set-equality"}[`ext`]를 사용한다.

# 상과 역상
%%%
tag := "functions-images-and-preimages"
file := "images-and-preimages"
%%%

앞의 `double`에서는 자연수 전체의 함수값을 모았다.
이제 정의역의 부분집합 $`S`를 정하고 $`S`에 속하는 원소들의 함수값만 모아 보자.

## 상과 존재명제
%%%
tag := "functions-image"
%%%

*정의* 함수 $`f : A \to B`와 집합 $`S \subseteq A`에 대하여
$`S`의 원소들의 함수값을 모은 집합을 $`S`의 *상*이라고 하며 $`f(S)`로 나타낸다.
즉, $`f(S) = \{f(x) : x \in S\}`이다.
여기서 $`f(S)`는 원소 하나에서의 함수값 $`f(x)`와 구별해야 한다.
함수 `f : A → B`는 `A`의 원소를 받으므로 집합 `S : Set A`를 그대로 인수로 넣을 수 없다.
집합의 각 원소에 `f`를 적용한 값들을 모으는 별도의 정의가 필요하다.

$`y \in f(S)`라는 것은 $`x \in S`이고 $`f(x) = y`인 원소 $`x`가 존재한다는 뜻이다.
따라서 상의 원소 조건은 두 조건의 논리곱과 존재명제 `∃ x, ...`로 나타낸다.

```savedLean
def image {A B : Type} (f : A → B) (S : Set A) : Set B :=
  fun y => ∃ x, x ∈ S ∧ f x = y
```

정의역 전체의 상 $`f(A)`를 나타낼 때는 `S`에 전체집합을 넣어 `image f (whole A)`로 쓴다.

*보기* $`6`은 함수 `double`의 상에 속한다.
실제로 자연수 $`3`은 정의역에 속하고 $`\operatorname{double}(3) = 6`이다.

목표를 정의에 따라 펼치면 `∃ n, n ∈ whole Nat ∧ double n = 6`이다.
이런 존재명제는 조건을 만족하는 원소를 제시하여 증명하며
전술 `exists 3`으로 원소 `n`을 $`3`으로 택할 수 있다.

```savedLean
example :
    6 ∈ image double (whole Nat) := by
  exists 3
```

원소를 택한 뒤 확인할 조건은 `3 ∈ whole Nat`와 `double 3 = 6`이다.
첫째 조건은 전체집합의 정의로, 둘째 조건은 계산으로 확인되므로 이 예제에서는 `exists`가 증명까지 마친다.

{anchor "functions-image-monotonicity"}[]*정리* $`S \subseteq T`이면 $`f(S) \subseteq f(T)`이다.

*증명* 임의의 원소 $`y \in f(S)`를 택하자.
상의 정의에 따라 $`x \in S`이고 $`f(x) = y`인 원소 $`x`가 존재한다.
$`S \subseteq T`에 따라 이 원소는 $`T`에도 속하므로 $`y \in f(T)`이다.

Lean에서는 먼저 `intro y hy`로 임의의 원소 `y`와 가정 `hy : y ∈ image f S`를 도입한다.
이 가정의 명제를 정의에 따라 펼치면 `∃ x, x ∈ S ∧ f x = y`이므로
`hy`는 조건에 맞는 원소가 존재한다는 증명이다.

`rcases`를 쓰면 존재명제의 증명에서 원소와 조건의 증명을 꺼낼 수 있다.
아래의 `rcases hy with ⟨x, hxS, hxy⟩`는 원소를 `x`로 두고
`x ∈ S`와 `f x = y`의 증명에 각각 `hxS`, `hxy`라는 이름을 붙인다.
이 패턴에서는 먼저 존재명제에서 원소와 그 원소에 관한 증명을 꺼내고,
그 증명에 담긴 논리곱을 다시 두 조건으로 나눈다.
여기서 `x`는 임의로 정한 원소가 아니라 가정 `hy`가 존재를 보장하는 원소이다.
이후의 추론에서는 함께 얻은 두 조건을 사용할 수 있다.
여기서 `⟨`와 `⟩`는 각각 `\<`, `\>`로 입력한다.

```savedLean
theorem image_mono {A B : Type} (f : A → B) (S T : Set A)
    (hST : S ⊆ T) :
    image f S ⊆ image f T := by
  intro y hy
  rcases hy with ⟨x, hxS, hxy⟩

  -- 같은 원소 x를 더 큰 집합 T에서도 사용할 수 있다.
  exists x
  constructor
  · apply hST
    exact hxS

  · exact hxy
```

이제 `y ∈ image f T`를 보이기 위해 `exists x`로 같은 원소를 택하면
목표 `x ∈ T ∧ f x = y`가 남는다.
`constructor`로 두 조건을 나누고 첫째 조건에는 포함 관계 `hST`와 가정 `hxS`를 사용한다.
둘째 조건은 `rcases`에서 얻은 등식 `hxy`로 증명한다.

{anchor "functions-not-in-image"}[]상에 속하지 않음을 보일 때는 앞에서 배운 부정의 증명 방법을 사용하자.
상에 속한다고 가정한 뒤 조건에 맞는 원소를 꺼내 모순을 얻으면 된다.

*보기* 모든 자연수를 $`0`에 대응시키는 함수의 상에는 $`1`이 속하지 않는다.
상에 속한다고 가정하면 함수값이 $`1`인 자연수 $`n`이 존재하지만
함수의 정의에 따라 그 값은 $`0`이므로 $`0=1`이라는 모순이 생긴다.

```savedLean
example :
    1 ∉ image (fun _ : Nat => 0) (whole Nat) := by
  intro hy
  rcases hy with ⟨n, hn, hEq⟩
  contradiction
```

`intro hy`로 상에 속한다고 가정하면 목표는 `False`가 된다.
`rcases`로 자연수 `n`과 `hn : n ∈ whole Nat`, 함수값에 관한 등식 `hEq`를 얻는다.
이때 `hEq`는 정의에 따라 `0 = 1`의 증명이므로 `contradiction`으로 모순을 얻는다.

앞의 `double`에서도 $`5`가 상에 속한다고 가정하면 $`2n=5`인 자연수 $`n`을 얻게 된다.
이 등식에서 모순을 얻는 방법은 {ref "preliminaries-double-image"}[짝수와 함수의 상]에서 다룬다.

*문제 7* (합집합의 상)

$`f(S\cup T)=f(S)\cup f(T)`임을 증명하라.

```savedLean -keep
theorem exercise_image_union {A B : Type}
    (f : A → B) (S T : Set A) :
    image f (S ∪ T) = image f S ∪ image f T := by
  sorry
```

## 역상
%%%
tag := "functions-preimage"
%%%

상을 구할 때는 정의역의 집합에서 출발하여 그 원소들의 함수값을 모았다.
이번에는 공역의 집합을 먼저 정하고 함수값이 그 집합에 속하는 정의역의 원소들을 모아 보자.

*정의* 함수 $`f : A \to B`와 집합 $`T \subseteq B`에 대하여
함수값이 $`T`에 속하는 원소들을 모은 집합을 $`T`의 *역상*이라고 하며 $`f^{-1}(T)`로 나타낸다.
즉, $`f^{-1}(T) = \{x \in A : f(x) \in T\}`이다.

역상에 속한다는 조건은 `f x ∈ T`이므로 이 술어로 집합을 정의하자.

```savedLean
def preimage {A B : Type} (f : A → B) (T : Set B) : Set A :=
  fun x => f x ∈ T
```

*보기* 함수 `double`에 의한 양의 자연수의 집합의 역상에는 $`1`이 속한다.
실제로 $`\operatorname{double}(1)=2>0`이므로 역상의 원소 조건을 만족한다.

```savedLean
example :
    1 ∈ preimage double positives := by
  expand
  expand
  expand
  decide
```

`x ∈ preimage f T`는 `f x ∈ T`를 뜻하므로 이 예제의 목표는 `double 1 ∈ positives`, 곧 `0 < 2`이다.
`expand`를 거듭 사용하여 역상과 양수 조건의 정의를 펼친 뒤 `decide`로 부등식을 확인한다.

역상 $`f^{-1}(T)`를 정의하려면 함수 $`f`와 공역의 부분집합 $`T`만 있으면 된다.
기호에 $`-1`이 들어 있어도 역함수를 구할 필요는 없으며
위와 같이 원래 함수의 값이 $`T`에 속하는지만 확인한다.

{anchor "functions-preimage-of-image"}[]집합 $`S`의 상 $`f(S)`를 구한 뒤 다시 역상 $`f^{-1}(f(S))`를 구하면 어떤 집합을 얻을까?
$`x\in S`이면 $`f(x)\in f(S)`이므로 $`x\in f^{-1}(f(S))`이다.
따라서 원래 집합의 원소는 모두 이 역상에 들어 있다.

*보기* 모든 함수 $`f`와 정의역의 부분집합 $`S`에 대하여 $`S\subseteq f^{-1}(f(S))`이다.

```savedLean
theorem subset_preimage_image {A B : Type}
    (f : A → B) (S : Set A) :
    S ⊆ preimage f (image f S) := by
  intro x hx
  exists x
```

`intro x hx` 뒤의 목표는 `f x ∈ image f S`이며
정의를 펼치면 `∃ y, y ∈ S ∧ f y = f x`이다.
`exists x`로 원소를 택하면 `hx`와 등식 `f x = f x`로 두 조건이 확인된다.

*보기* 위 포함 관계에서 두 집합이 항상 같지는 않다.
모든 자연수를 $`0`에 보내는 함수와 집합 $`S=\{0\}`을 생각하자.
이때 $`f(S)=\{0\}`이고 모든 자연수의 함수값이 $`0`이므로 $`f^{-1}(f(S))=\mathbb{N}`이다.
특히 원래 집합에 없던 $`1`도 역상에 속한다.

```savedLean
example :
    1 ∈ preimage (fun _ : Nat => 0)
    (image (fun _ : Nat => 0) (fun n => n = 0)) := by
  exists 0
```

$`f(1)`이 $`f(S)`에 속함을 보이려면 $`S` 안에서 같은 함수값을 갖는 원소를 찾으면 된다.
그 원소로 $`0`을 택하면 $`0\in S`이고 $`f(0)=f(1)`이다.
원래 집합 밖의 원소도 집합 안의 원소와 같은 함수값을 가지면 이 역상에 들어간다.

*문제 8* $`S \subseteq T`이면 $`f^{-1}(S) \subseteq f^{-1}(T)`임을 증명하라.

```savedLean -keep
theorem exercise_preimage_subset {A B : Type}
    (f : A → B) (S T : Set B)
    (hST : S ⊆ T) :
    preimage f S ⊆ preimage f T := by
  sorry
```

*문제 9* (역상과 집합 연산)

역상은 교집합과 여집합을 보존한다. 다음 두 등식을 증명하라.
함수의 단사성이나 전사성을 가정하지 않고 증명하라.

```savedLean -keep
theorem exercise_preimage_inter {A B : Type} (f : A → B)
    (S T : Set B) :
    preimage f (S ∩ T) = preimage f S ∩ preimage f T := by
  sorry

theorem exercise_preimage_compl {A B : Type}
    (f : A → B) (T : Set B) :
    preimage f Tᶜ = (preimage f T)ᶜ := by
  sorry
```

# 단사, 전사, 전단사
%%%
tag := "functions-mapping-properties"
file := "mapping-properties"
%%%

서로 다른 원소가 서로 다른 함수값을 갖는 조건을 *단사성*이라고 하고
공역의 모든 원소가 함수값으로 나타나는 조건을 *전사성*이라고 한다.
이 두 성질을 차례로 정의하고 항등함수 등의 예에서 확인하자.

## 단사함수
%%%
tag := "functions-injectivity"
%%%

*정의* 함수 $`f : A \to B`가 임의의 $`x, y \in A`에 대하여
$`f(x) = f(y)`이면 $`x = y`라는 조건을 만족할 때
$`f`를 *단사함수*라고 한다.

이는 서로 다른 원소들이 서로 다른 값에 대응한다는 조건이다.
앞에서 $`x=y`이면 $`f(x)=f(y)`임을 보였으므로
단사함수에서는 $`x=y`와 $`f(x)=f(y)`가 서로 동치이다.

```savedLean
def Injective {A B : Type} : (A → B) → Prop :=
  fun f => ∀ x y, f x = f y → x = y
```

`Injective`는 함수 `f`에 “`f`가 단사이다”라는 명제를 대응시키는 술어이다.
인수가 `A → B` 타입의 함수이므로 술어 전체의 타입은 `(A → B) → Prop`이다.

*보기* 항등함수는 단사이다.
$`\operatorname{id}_A(x) = \operatorname{id}_A(y)`라는 가정이 곧 $`x = y`이므로
이 가정을 그대로 사용하면 된다.

```savedLean
theorem identity_injective (A : Type) :
    Injective (identity A) := by
  intro x y hxy
  exact hxy
```

*보기* 모든 자연수를 $`0`에 대응시키는 함수는 단사가 아니다.
이 함수가 단사라고 가정하면 $`0`과 $`1`에서 함수값이 같다는 사실로부터 $`0 = 1`을 얻어 모순이다.

```savedLean
example :
    ¬ Injective (fun _ : Nat => 0) := by
  intro h
  have h01 : 0 = 1 := by
    apply h 0 1
    rfl

  contradiction
```

`have`로 `0 = 1`을 보이는 부분을 시작한 뒤 `apply h 0 1`을 쓰면
단사성의 전제인 두 함수값의 등식이 새 목표가 된다.
두 값은 모두 $`0`이므로 `rfl`로 이 목표를 해결하여 `h01 : 0 = 1`을 얻는다.
바깥의 목표 `False`로 돌아오면 `contradiction`이 이 등식에서 모순을 얻어 증명을 마친다.

*보기* 함수 $`\operatorname{double}(n)=2n`은 단사이다.
$`2x=2y`에서 양변의 양수인 인수 $`2`를 소거하면 $`x=y`를 얻는다.
자연수의 이 소거법칙은 `Nat.mul_left_cancel`로 사용할 수 있다.
이 정리는 `0 < n`과 `n * x = n * y`의 증명을 받아 `x = y`의 증명을 제공한다.

```savedLean
theorem double_injective : Injective double := by
  intro x y hxy
  apply Nat.mul_left_cancel (n := 2) (by decide)
  exact hxy
```

여기서는 공통 인수 `n`을 `2`로 지정하고 `by decide`로 양수 조건을 확인했다.
남은 목표는 `2 * x = 2 * y`이며 `hxy`가 바로 이 등식의 증명이다.

앞에서는 상의 역상이 원래 집합보다 커질 수 있음을 보았다.
그 예제에서는 원래 집합 밖의 원소도 집합 안의 원소와 같은 함수값을 가졌다.
함수가 단사이면 이런 일이 없으므로 다음 등식을 얻는다.

*정리* $`f`가 단사이면 모든 집합 $`S`에 대하여 $`f^{-1}(f(S))=S`이다.

*증명* $`x\in f^{-1}(f(S))`이면 어떤 $`y\in S`에 대하여 $`f(y)=f(x)`이다.
단사성에 따라 $`y=x`이므로 $`x\in S`이다.
반대 포함 관계는 앞에서 증명한 `subset_preimage_image`이다.

```savedLean
theorem preimage_image_of_injective {A B : Type} (f : A → B)
    (hf : Injective f)
    (S : Set A) :
    preimage f (image f S) = S := by
  apply set_eq_of_subset
  · intro x hx
    rcases hx with ⟨y, hy, hxy⟩
    have hyx : y = x := by
      exact hf y x hxy

    rw [← hyx]
    exact hy

  · exact subset_preimage_image f S
```

`hx`는 `∃ y, y ∈ S ∧ f y = f x`라는 존재명제의 증명이므로
`rcases`로 원소 `y`, 원소 조건 `hy`, 함수값의 등식 `hxy`를 얻는다.
`hf`로 얻은 `hyx`를 오른쪽에서 왼쪽으로 사용하면 목표 `x ∈ S`가 `y ∈ S`로 바뀐다.
`rw [← hyx]`의 `←`는 이처럼 등식을 반대 방향으로 사용하라는 뜻이며 `\l`로 입력한다.

*보기* $`\{2,3\}`의 상은 $`\{4,6\}`이다. 이 상의 역상을 구하면 원래 집합 $`\{2,3\}`을 얻는다.
두 번째 사실은 `double`의 단사성에서 바로 따른다.
앞에서 정의한 `twoThree`와 방금 증명한 `double_injective`를 위 정리에 사용하자.

```savedLean
example :
    preimage double (image double twoThree) = twoThree := by
  exact preimage_image_of_injective double
    double_injective twoThree
```

이 증명은 역상의 원소 조건을 다시 풀지 않고 단사함수에 관한 일반 정리를 사용한다.

## 전사함수
%%%
tag := "functions-surjectivity"
%%%

앞의 `double`처럼 상이 공역의 일부인 함수도 있고 항등함수처럼 상과 공역이 같은 함수도 있다.
두 번째 경우를 나타내는 조건이 전사성이다.

*정의* 함수 $`f : A \to B`에 대하여
모든 $`y \in B`가 어떤 $`x \in A`의 함수값 $`f(x)`일 때
$`f`를 *전사함수*라고 한다.

Lean에서는 공역의 원소 `y`를 먼저 두고 `f x = y`인 원소 `x`의 존재를 요구한다.
따라서 `∀ y, ∃ x, ...`의 순서로 쓰며 원소 `x`는 `y`에 따라 달라질 수 있다.
예를 들어 자연수의 항등함수에서는 $`y=0`에 대해 $`x=0`을,
$`y=1`에 대해 $`x=1`을 택한다.
순서를 바꾸어 `∃ x, ∀ y, f x = y`라고 쓰면
하나의 `x`에서 얻는 함수값이 공역의 모든 원소와 같아야 하므로 전혀 다른 조건이 된다.

```savedLean
def Surjective {A B : Type} : (A → B) → Prop :=
  fun f => ∀ y, ∃ x, f x = y
```

*보기* 항등함수는 전사이다.
임의의 원소 $`y \in A`에 대하여 $`x = y`를 택하면
$`\operatorname{id}_A(x) = y`이므로 원하는 원소가 존재한다.

```savedLean
theorem identity_surjective (A : Type) :
    Surjective (identity A) := by
  intro y
  exists y
```

`intro y` 이후의 목표는 `∃ x, identity A x = y`이므로
`exists y`로 원소 `x`를 `y`로 선택한다.
남은 등식은 정의에 따라 `y = y`가 되므로 이 단계에서 증명도 끝난다.

## 전단사함수
%%%
tag := "functions-bijectivity"
%%%

이제 단사성과 전사성을 함께 만족하는 함수를 살펴보자.

*정의* 단사이면서 전사인 함수를 *전단사함수*라고 한다.

전사성에 따라 공역의 각 원소 $`y`에 대해 $`f(x)=y`인 원소 $`x`가 존재하고
단사성에 따라 그러한 원소는 하나뿐이다.
Lean에서는 두 조건을 논리곱으로 묶어 전단사성을 정의한다.

```savedLean
def Bijective {A B : Type} : (A → B) → Prop :=
  fun f => Injective f ∧ Surjective f
```

```savedLean -show
namespace Bijective

theorem inj {A B : Type}
    {f : A → B} (hf : Bijective f) : Injective f :=
    hf.left

theorem surj {A B : Type}
    {f : A → B} (hf : Bijective f) : Surjective f :=
    hf.right

end Bijective
```

`hf : Bijective f`가 주어지면 `hf.inj`로 단사성의 증명을,
`hf.surj`로 전사성의 증명을 꺼내 사용할 수 있다.

*보기* 항등함수는 전단사이다.
단사성과 전사성을 앞에서 각각 증명했으므로 `constructor`로 나뉜 목표에 두 정리를 사용하면 된다.

```savedLean
theorem identity_bijective (A : Type) :
    Bijective (identity A) := by
  constructor
  · exact identity_injective A
  · exact identity_surjective A
```

*문제 10* (두 원소 집합의 상과 역상)

(1) $`\operatorname{double}(\{2,3\})=\{4,6\}`임을 증명하라.

(2) 첫 결과와 `preimage_image_of_injective`를 사용하여
$`\operatorname{double}^{-1}(\{4,6\})=\{2,3\}`임을 보이라.

```savedLean -keep
def practiceFourSix : Set Nat := fun n => n = 4 ∨ n = 6
theorem exercise_image_double_twoThree :
    image double twoThree = practiceFourSix := by
  sorry

theorem exercise_preimage_double_fourSix :
    preimage double practiceFourSix = twoThree := by
  sorry
```

# 집합 위의 함수
%%%
tag := "functions-elements"
file := "elements"
%%%

앞에서 정의한 `double`은 자연수를 받아 자연수를 돌려준다.
그런데 함수값 $`2n`은 언제나 짝수이므로 공역을 짝수인 자연수들의 집합으로 정할 수도 있다.
이처럼 정의역이나 공역을 집합으로 정할 때 어떤 조건을 확인해야 하는지 살펴보고
그 조건을 함수의 타입에 반영하는 방법을 익히자.

{anchor "functions-codomain-condition"}[]짝수인 자연수들의 집합을 $`E`라고 하자.
$`n\mapsto 2n`을 함수 $`\mathbb{N}\to E`로 정의하려면
각 자연수 $`n`에 대하여 함수값 $`2n`이 $`E`에 속함을 보여야 한다.
짝수의 정의는 어떤 자연수의 두 배로 나타낼 수 있다는 것이므로
여기서는 그 자연수로 $`n`을 택하면 된다.

Lean에서는 우선 앞에서 정의한 `double : Nat → Nat`을 사용하고
함수값이 짝수 집합에 속한다는 사실을 따로 증명하자.
짝수 집합을 `evens`로 정의하면 증명할 명제는 `double n ∈ evens`이다.

```savedLean
def evens : Set Nat := fun n => ∃ k : Nat, n = 2 * k
theorem double_mem_evens (n : Nat) :
    double n ∈ evens := by
  exists n
```

목표의 원소 조건은 `∃ k : Nat, double n = 2 * k`이다.
`exists n`으로 $`k=n`을 택하면 `double`의 정의에 따라 등식이 성립한다.
이제 `double`은 함수값을 정하고 `double_mem_evens`는 그 값이 `evens`에 속함을 보인다.

{anchor "functions-domain-condition"}[]정의역이 부분집합이면 그 집합의 원소라는 조건도 사용할 수 있다.
예를 들어 양의 자연수의 집합 $`S=\{n\in\mathbb{N}:0<n\}`에서
$`T=\{m\in\mathbb{N}:2<m\}`로 가는 함수를 $`n\mapsto n+2`로 정의하자.
$`n\in S`이면 $`0<n`이므로 양변에 $`2`를 더하여 $`2<n+2`를 얻는다.
따라서 함수값은 $`T`에 속한다.
여기서 정의역의 조건을 빼면 $`n=0`일 때 함수값이 $`2`여서 $`T`에 속하지 않는다.

앞에서 정의한 `positives`가 $`S`에 해당한다.
$`T`를 `aboveTwo`로 정의하고 먼저 모든 자연수에서 $`n+2`를 계산하는 함수 `shiftTwo`를 만들자.
그 값이 `aboveTwo`에 속한다는 정리에는 `n ∈ positives`를 가정으로 넣는다.

```savedLean
def aboveTwo : Set Nat := fun n => 2 < n
def shiftTwo (n : Nat) : Nat := n + 2
theorem shiftTwo_mem_aboveTwo (n : Nat)
    (hn : n ∈ positives) :
    shiftTwo n ∈ aboveTwo := by
  apply Nat.add_lt_add_right (k := 2)
  exact hn
```

목표는 정의에 따라 `2 < n + 2`이고 가정 `hn`은 `0 < n`의 증명이다.
앞서 배운 `Nat.add_lt_add_right`를 더할 수 `2`와 함께 적용하면
목표가 `0 < n`으로 바뀌므로 `exact hn`으로 증명을 마친다.

일반적으로 $`f:A\to B`와 집합 $`S\subseteq A`, $`T\subseteq B`가 주어졌을 때
$`f`의 값을 이용하여 $`S`에서 $`T`로 가는 함수를 만들려면
$`x\in S`일 때 $`f(x)\in T`임을 보여야 한다.
지금처럼 함수와 이 조건의 증명을 따로 적을 수도 있고
각 원소를 원소 조건의 증명과 묶어 정의역과 공역에 사용할 타입을 만들 수도 있다.

## 부분타입
%%%
tag := "functions-subtypes"
%%%

앞에서 보인 `double n ∈ evens`를 함수의 타입에도 담아 보자.
수학에서는 $`\mathbb{N} \to E`처럼 공역에 짝수의 집합 $`E`를 적지만,
Lean에서 다음과 같이 적으면 오류가 난다.

```tryLean +error -keep
def doubleToEvensAttempt : Nat → evens := double
```

`evens`는 자연수의 원소 조건을 나타내는 술어 `Nat → Prop`이다.
함수의 화살표 오른쪽에는 함수값의 타입이 필요하므로 이 술어를 그대로 넣을 수 없다.
짝수라는 조건을 만족하는 자연수들을 하나의 타입으로 모으려면
자연수 값과 그 값이 짝수라는 증명을 함께 담으면 된다.

정의역이 양의 자연수의 집합이라는 조건을 함수의 타입에 반영하려면
자연수 `n : Nat`와 양수라는 증명 `hn : n ∈ positives`를 함께 받으면 된다.
이 둘을 하나로 묶으면 양의 자연수를 인수 하나로 전달할 수 있으며
함수값에도 같은 방법으로 값과 공역에 속한다는 증명을 담을 수 있다.

Lean의 *부분타입* `{x : A // P x}`는 원소 `x : A`와
그 원소가 조건 `P x`를 만족한다는 증명을 함께 담는다.
집합 `S`의 원소 조건을 넣어 다음과 같이 정의하자.

```savedLean
def Elem {A : Type _} (S : Set A) := {x : A // x ∈ S}
```

```savedLean -show
attribute [implicit_reducible] Elem
```

`{ val := 값, property := 증명 }`으로 원소와 그 조건의 증명을 함께 담는다.
양의 자연수 하나를 만들어 이 두 성분을 살펴보자.

*보기* $`1`은 양의 자연수이다.
먼저 `1 ∈ positives`의 원소 조건인 $`0<1`을 증명하고
그 증명에 `one_positive`라는 이름을 붙이자.

```savedLean
theorem one_positive : 0 < 1 := by decide
```

이제 자연수 값 $`1`과 이 증명을 묶어 `Elem positives`의 원소를 만들자.
`val`에는 `1`을, `property`에는 방금 얻은 증명 `one_positive`를 넣는다.
`0 < 1`과 `1 ∈ positives`는 정의상 같은 명제이므로 이 증명을 그대로 사용할 수 있다.

```savedLean
def oneInPositives : Elem positives :=
  { val := 1, property := one_positive }
```

`oneInPositives.val`은 자연수 $`1`이고, `oneInPositives.property`는 `1 ∈ positives`의 증명이다.
`1 ∈ positives`라는 명제 자체는 증명이 없어도 쓸 수 있지만,
값이 $`1`인 `Elem positives`의 원소를 만들 때는 그 증명을 함께 넣어야 한다.
예를 들어 `0 ∈ positives`도 명제이나, 값이 $`0`인 원소를 만들려면 거짓인 `0 < 0`의 증명이 필요하다.

일반적인 집합에서도 `a : A`와 `ha : a ∈ S`를 다음과 같이 묶는다.

```savedLean
def functions_element_from_membership {A : Type}
    (S : Set A) (a : A)
    (ha : a ∈ S) :
    Elem S :=
  { val := a, property := ha }
```

`s : Elem S`에서는 `s.val : A`와 `s.property : s.val ∈ S`를 꺼낼 수 있다.
이러한 타입을 함수의 정의역과 공역으로 사용하면 원소 조건도 함께 전달된다.

{anchor "functions-subtype-maps"}[]이제 앞의 두 함수를 원소 조건까지 포함한 타입으로 나타내자.
자연수에서 짝수 집합으로 가는 함수의 타입은 `Nat → Elem evens`이다.
각 `n : Nat`에 대해 값 `double n`과 그 값이 짝수라는 증명 `double_mem_evens n`을 함께 돌려주면 된다.
증명 단계를 직접 적을 때는 다음과 같이 `property := by` 아래에 적는다.

```savedLean
def doubleToEvens (n : Nat) : Elem evens :=
  { val := double n
    property := by
      exact double_mem_evens n }
```

양의 자연수에서 $`2`보다 큰 자연수로 가는 함수는
`Elem positives → Elem aboveTwo`로 정의한다.
이때 인수 `s`에서 자연수 값 `s.val`과 양수라는 증명 `s.property`를 꺼내
앞의 정리 `shiftTwo_mem_aboveTwo`에 함께 넣는다.

```savedLean
def shiftTwoOnPositives (s : Elem positives) :
    Elem aboveTwo :=
  { val := shiftTwo s.val
    property := by
      exact shiftTwo_mem_aboveTwo s.val s.property }

example :
    (shiftTwoOnPositives oneInPositives).val = 3 := by
  rfl
```

`shiftTwoOnPositives`는 `s.property`로 주어진 정의역의 조건을 사용하여
함수값이 공역에 속한다는 증명을 만든다.
`oneInPositives`를 넣으면 값 $`1`과 $`0<1`의 증명이 함께 전달되며
함수값에는 $`3`과 $`2<3`의 증명이 담긴다.

일반적인 집합 $`S`, $`T`에 대해서도 함수의 타입을 `Elem S → Elem T`로 쓸 수 있다.
인수에서 `S`의 원소 값과 원소 조건의 증명을 꺼내고
함수값을 만들 때는 `T`의 원소 값과 원소 조건의 증명을 함께 제시한다.

# 부분타입의 원소 비교
%%%
tag := "functions-element-equality"
file := "element-comparison"
%%%

부분타입의 원소에는 값과 증명이 함께 들어 있다.
예를 들어 양수라는 사실을 서로 다른 방법으로 증명하여 만든 두 원소가
모두 값 $`1`을 갖는다면 이 둘을 같은 양의 자연수로 취급해야 한다.

Lean에서는 같은 명제의 증명들을 같게 취급한다.
`s.val = t.val`이면 두 원소의 조건도 같은 명제이므로 그 증명들도 같다.
이 원리로 값의 등식에서 `s = t`를 얻는 정리가 `Subtype.ext`이며 `ext`로 사용할 수 있다.

```savedLean -show
@[ext] theorem elem_ext {A : Type _} {S : Set A} {s t : Elem S}
    (h : s.val = t.val) : s = t := by
  apply Subtype.ext
  exact h

@[simp] theorem elem_eq_iff {S : Set A}
    (s t : Elem S) :
    s = t ↔ s.val = t.val := by
  constructor
  · intro h
    rw [h]
  · intro h
    apply elem_ext
    exact h

attribute [ample_norm_hyp] elem_eq_iff
```

`s = t`라는 목표에 `ext`를 사용하면 새 목표는 `s.val = t.val`이다.
거꾸로 `h : s = t`가 주어졌을 때 `indisc at h`는 이를 값의 등식으로 바꾼다.
`ext`가 등식을 증명하기 위해 필요한 비교를 남긴다면, `indisc`은 이미 주어진 등식에서 그 비교를 얻는다.
같은 대상은 값이나 조건으로 비교해도 구별되지 않는다는 뜻에서 이를 *동일자의 구별 불가능성*이라고 한다.

```savedLean
example {A : Type}
    (S : Set A) (s t : Elem S)
    (h : s = t) :
    s.val = t.val := by
  indisc at h
  exact h
```

같은 값 비교를 사용하면 원소를 꺼내는 함수 `fun s => s.val`이 단사임을 보일 수 있다.

```savedLean
theorem elem_val_injective {A : Type} (S : Set A) :
    Injective (fun s : Elem S => s.val) := by
  intro s t hst
  ext
  exact hst
```

*보기* 앞에서 만든 `doubleToEvens : Nat → Elem evens`는 전단사이다.
자연수를 두 배로 하는 규칙은 `double`과 같으며 공역을 짝수 집합으로 정했다.
단사성에는 이미 증명한 `double_injective`를 사용하면 된다.
또한 공역의 원소 $`y`는 짝수이므로 $`y=2n`인 자연수 $`n`이 존재하며,
이 $`n`을 택하면 함수값이 $`y`가 되어 전사성도 얻는다.

전사성을 보일 때 `y : Elem evens`의 `y.property`는
`∃ n, y.val = 2 * n`의 증명이다. `unpack y.property with ⟨n, hn⟩`은
이 존재명제에서 원소 `n`과 등식 `hn`을 꺼낸다.
앞의 `rcases`가 여러 겹을 한꺼번에 분해한다면 `unpack`은 한 묶음을 분해한다.

```savedLean
theorem doubleToEvens_bijective :
    Bijective doubleToEvens := by
  constructor
  · intro x y hxy
    apply double_injective
    indisc at hxy
    exact hxy

  · intro y
    -- y의 원소 조건에서 y = 2n인 자연수 n을 얻는다.
    unpack y.property with ⟨n, hn⟩
    exists n
    ext
    symm
    exact hn
```

단사성에서는 부분타입 원소의 등식을 값의 등식으로 바꾸어 `double_injective`에 사용한다.
전사성에서 `y.property`는 `∃ n, y.val = 2 * n`의 증명이다.
따라서 `exists n`으로 원소를 정하고 `ext`로 값만 비교하면
`2 * n = y.val`이 남으며 이는 `hn`의 양변을 바꾼 등식이다.
뒤의 {ref "cardinality-countable-sets"}[가산무한집합]에서는 이 전단사를 사용하여
자연수 전체와 짝수 집합의 크기를 비교한다.

# 함수의 제한
%%%
tag := "functions-restriction"
file := "restrictions"
%%%

함수 $`f : A\to B`를 집합 $`S\subseteq A`의 원소에만 적용하는 함수를
$`f`의 $`S`에 대한 *제한*이라고 한다.
앞에서 `shiftTwoOnPositives`의 인수로 양의 자연수만 받았듯이,
일반적인 함수도 부분타입을 사용하여 정의역을 제한할 수 있다.
`s : Elem S`에서 원래 원소 `s.val`을 꺼내 `f`에 넣으면 이 함수를 얻는다.

```savedLean
def restrict {A B : Type}
    (f : A → B) (S : Set A) : Elem S → B :=
  fun s => f s.val
example :
    restrict double positives oneInPositives = 2 := by
  rfl
```

`restrict double positives`는 양의 자연수만 받아 그 두 배를 자연수로 돌려준다.
`oneInPositives`의 자연수 값이 $`1`이므로 위 함수값은 $`2`이다.

*정리* 단사함수의 정의역을 제한한 함수도 단사이다.

*증명* 제한한 함수의 두 함수값이 같으면 원래 함수의 단사성으로 두 원소 값이 같다.
그러므로 두 부분타입의 원소도 같다.

```savedLean
theorem restrict_injective {A B : Type}
    (f : A → B) (S : Set A)
    (hf : Injective f) :
    Injective (restrict f S) := by
  intro s t hst
  ext
  apply hf s.val t.val
  exact hst
```

`ext`로 원소 값을 비교한 뒤 `apply hf s.val t.val`을 쓰면 목표는 `f s.val = f t.val`이다.
이는 `hst`에서 `restrict`의 정의를 펼친 명제이므로 `exact hst`로 증명을 마친다.

## 공역의 제한
%%%
tag := "functions-codomain-image"
%%%

전사성은 공역의 모든 원소가 함수값으로 나타난다는 조건이다.
따라서 함수값은 그대로 두고 공역을 함수의 상으로 바꾸면 전사함수를 얻는다.
이때 상은 집합이므로 함수의 공역에는 그 원소 타입을 사용하자.

*보기* 함수 $`f:A\to B`로부터 $`A`에서 $`f(A)`로 가는 전사함수를 만들 수 있다.

```savedLean
def toImage {A B : Type} (f : A → B) (x : A) :
    Elem (image f (whole A)) :=
  { val := f x
    property := by
      exists x }

theorem toImage_surjective {A B : Type} (f : A → B) :
    Surjective (toImage f) := by
  intro y
  rcases y.property with ⟨x, hx, hxy⟩
  exists x
  ext
  exact hxy
```

`val := f x`는 함수값을 정하고 `property`는 이 값이 상에 속함을 증명한다.
이 원소 조건은 존재명제이므로 `exists x`로 원소 `x`를 제시한다.
`x ∈ whole A`와 `f x = f x`는 바로 확인되므로 함수값의 구성이 끝난다.

전사성 증명의 `y`는 상의 원소와 그 조건의 증명을 함께 담는다.
따라서 `y.property`는 `∃ x, x ∈ whole A ∧ f x = y.val`의 증명이다.
여기서 얻은 원소 `x`를 제시하고 `ext`로 원소 값만 비교하면
남은 목표는 `rcases`에서 얻은 등식 `hxy`와 같다.

# 합성함수
%%%
tag := "functions-composition"
file := "composition"
%%%

함수 $`f : A \to B`를 적용한 뒤 함수 $`g : B \to C`를 적용하면
$`A`의 원소에서 $`C`의 원소를 얻는다. 이 과정을 하나의 함수로 정의하자.

*정의* 함수 $`f : A \to B`와 $`g : B \to C`에 대하여
$`A`의 각 원소 $`x`를 $`g(f(x))`에 대응시키는 함수를 두 함수의 *합성함수*라고 한다.
이 함수를 $`g \circ f`로 쓰며 그 값은 $`(g \circ f)(x) = g(f(x))`이다.

합성하려면 먼저 적용하는 함수의 공역과 다음 함수의 정의역이 맞아야 한다.
아래의 정의에서는 `f`의 값이 `B`의 원소이므로 `g`를 적용하여 `C`의 원소를 얻는다.

```savedLean
def compose {A B C : Type}
    (g : B → C) (f : A → B) : A → C :=
  fun x => g (f x)
local infixr:90 (priority := high) " ∘ " => compose
```

마지막 선언은 `g ∘ f`를 `compose g f`에 연결하며 기호 `∘`는 `\circ`로 입력한다.
이 표기에서는 오른쪽의 `f`를 먼저 적용하고 그 값에 왼쪽의 `g`를 적용한다.
따라서 `(g ∘ f) x = g (f x)`는 정의를 펼쳐 `rfl`로 증명할 수 있다.

```savedLean
example {A B C : Type}
    (f : A → B) (g : B → C) (x : A) :
    (g ∘ f) x = g (f x) := by
  rfl
```

*보기* $`f(n) = n + 3`이고 $`g(n) = 2n`이면
$`(g \circ f)(4) = 2(4 + 3) = 14`이다.

```lean (name := compositionValue)
#eval (double ∘ (fun n : Nat => n + 3)) 4
```

```leanOutput compositionValue
14
```

{anchor "functions-congruence"}[]
```savedLean -show
theorem functions_compose_of_pointwise_equal {A B C : Type}
    (f : B → C)
    (g h : A → B)
    (hgh : ∀ x, g x = h x)
    (x : A) :
    f (g x) = f (h x) := by
  congr : 1
  exact hgh x
```

```savedLean -show
theorem compose_of_pointwise_equal {A B C : Type}
    (f : B → C)
    (g h : A → B)
    (hgh : ∀ x, g x = h x) :
    f ∘ g = f ∘ h := by
  ext x
  exact functions_compose_of_pointwise_equal f g h hgh x
```

*문제 11* $`f(n) = n + 1`, $`g(n) = 2n`인 두 자연수 함수에 대하여
$`(g \circ f)(3)`과 $`(f \circ g)(3)`을 계산하고 두 합성함수가 서로 다름을 증명하라.
세 번째 증명에서는 앞의 두 계산 결과를 사용하라.

```savedLean -keep
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
```

## 합성의 기본 성질
%%%
tag := "functions-associativity"
%%%

*정리* 함수 $`f : A \to B`, $`g : B \to C`, $`h : C \to D`에 대하여
$`h \circ (g \circ f) = (h \circ g) \circ f`이다.

*증명* 임의의 원소 $`x \in A`를 택하면
합성함수의 정의에 따라 두 함수의 값은 모두 $`h(g(f(x)))`이다.
두 함수가 모든 원소에서 같은 값을 가지므로 서로 같다.

```savedLean
theorem compose_assoc {A B C D : Type}
    (f : A → B) (g : B → C)
    (h : C → D) :
    h ∘ (g ∘ f) = (h ∘ g) ∘ f := by
  ext x
  rfl
```

{anchor "functions-composition-with-identity"}[]*정리* 함수 $`f : A \to B`에 대하여
$`f \circ \operatorname{id}_A = f`이고 $`\operatorname{id}_B \circ f = f`이다.

*증명* 임의의 원소 $`x \in A`에 대하여
$`f`를 적용하기 전에 항등함수를 적용해도 결과는 $`f(x)`이며
$`f`를 적용한 뒤에 항등함수를 적용해도 같은 값을 얻는다.

```savedLean
theorem compose_identity {A B : Type} (f : A → B) :
    f ∘ identity A = f := by
  ext x
  rfl

theorem identity_compose {A B : Type} (f : A → B) :
    identity B ∘ f = f := by
  ext x
  rfl
```

첫 번째 등식에는 정의역의 항등함수 `identity A`를,
두 번째 등식에는 공역의 항등함수 `identity B`를 사용한다.

```savedLean -show
attribute [simp] compose_identity identity_compose
```

이 두 성질도 `simp`에 등록되어 있으므로 합성에 들어 있는 항등함수를 다음과 같이 없앨 수 있다.

```savedLean
example {A B : Type} (f : A → B) :
    (identity B ∘ f) ∘ identity A = f := by
  simp
```

## 합성과 단사·전사
%%%
tag := "functions-composition-injectivity"
%%%

두 단사함수를 합성했을 때도 서로 다른 원소가 서로 다른 함수값을 갖는지 살펴보자.

*정리* 함수 $`f : A \to B`와 $`g : B \to C`가 모두 단사이면
합성함수 $`g \circ f`도 단사이다.

*증명* $`x, y \in A`에 대하여 $`g(f(x)) = g(f(y))`라고 하자.
$`g`가 단사이므로 $`f(x) = f(y)`이고 여기에 $`f`의 단사성을 사용하면 $`x = y`이다.
따라서 $`g \circ f`는 단사이다.

```savedLean
theorem injective_compose {A B C : Type}
    (f : A → B) (g : B → C)
    (hf : Injective f)
    (hg : Injective g) :
    Injective (g ∘ f) := by
  intro x y hxy
  apply hf
  apply hg
  exact hxy
```

위의 수학적 증명을 목표에서 거슬러 올라가면 Lean 코드의 순서가 된다.
`x = y`를 보이기 위해 `apply hf`로 `f x = f y`를 새 목표로 삼고
다시 `apply hg`로 목표를 `g (f x) = g (f y)`로 바꾼다.
이제 목표가 처음의 가정과 같으므로 `exact hxy`로 증명을 마친다.

{anchor "functions-composition-surjectivity"}[]전사성도 합성에서 유지된다.
이번에는 두 함수의 전사성을 차례로 사용하여 공역의 원소에 대응하는 정의역의 원소를 찾는다.

*정리* 함수 $`f : A \to B`와 $`g : B \to C`가 모두 전사이면
합성함수 $`g \circ f`도 전사이다.

*증명* 임의의 원소 $`z \in C`를 택하자.
$`g`가 전사이므로 $`g(y) = z`인 원소 $`y \in B`가 존재하고
$`f`가 전사이므로 $`f(x) = y`인 원소 $`x \in A`가 존재한다.
이때 $`(g \circ f)(x) = g(f(x)) = g(y) = z`이므로 원하는 원소를 얻는다.

`unpack hg z`로 `g y = z`인 원소 `y`를 얻고,
`unpack hf y`로 `f x = y`인 원소 `x`를 얻는다.

```savedLean
theorem surjective_compose {A B C : Type}
    (f : A → B) (g : B → C)
    (hf : Surjective f)
    (hg : Surjective g) :
    Surjective (g ∘ f) := by
  intro z
  -- g y = z인 y를 고르고, f x = y인 x를 고른다.
  unpack hg z with ⟨y, hy⟩
  unpack hf y with ⟨x, hx⟩

  -- 고른 x가 합성함수에서 z로 가는지 확인한다.
  exists x
  expand
  rw [hx]
  exact hy
```

`exists x`로 찾은 원소를 제시하고 `expand`로 합성의 정의를 펼치면 목표는 `g (f x) = z`이다.
여기서 `rw [hx]`로 `f x`를 `y`로 바꾸면 남은 목표 `g y = z`를 `hy`로 증명할 수 있다.

{anchor "functions-composition-bijectivity"}[]*정리* 전단사함수 두 개를 합성하면 전단사함수를 얻는다.

*증명* `constructor`로 목표를 단사성과 전사성으로 나누어 앞의 두 정리를 사용한다.
가정 `hf : Bijective f`에서는 `hf.inj`로 단사성의 증명을, `hf.surj`로 전사성의 증명을 꺼내며
`hg`도 같은 방식으로 사용한다.

```savedLean
theorem bijective_compose {A B C : Type}
    (f : A → B) (g : B → C)
    (hf : Bijective f)
    (hg : Bijective g) :
    Bijective (g ∘ f) := by
  constructor
  · exact injective_compose f g hf.inj hg.inj
  · exact surjective_compose f g hf.surj hg.surj
```

*문제 12* 합성함수 $`g \circ f`가 단사이면 $`f`도 단사임을 증명하라.

```savedLean -keep
theorem exercise_injective_of_compose {A B C : Type}
    (f : A → B) (g : B → C)
    (h : Injective (g ∘ f)) :
    Injective f := by
  sorry
```

*문제 13* 합성함수 $`g \circ f`가 전사이면 $`g`도 전사임을 증명하라.

```savedLean -keep
theorem exercise_surjective_of_compose {A B C : Type}
    (f : A → B) (g : B → C)
    (h : Surjective (g ∘ f)) :
    Surjective g := by
  sorry
```

# 집합의 곱과 함수
%%%
tag := "preliminaries-products"
file := "products"
%%%

두 집합에서 원소를 하나씩 택하면 순서쌍을 만들 수 있다.
순서쌍을 만들고 성분을 비교하는 방법으로 집합의 곱을 나타내자.

*정의* 집합 $`A`, $`B`의 원소를 하나씩 택하여 만든 순서쌍들의 집합을
두 집합의 *곱*이라고 하며 $`A \times B`로 나타낸다.

## 순서쌍과 인수의 구성
%%%
tag := "intro-pairs-and-currying"
file := "pairs-and-currying"
%%%

수학에서는 두 원소를 받는 함수를 $`f(x,y)`로 쓰기도 한다.
Lean에서도 두 원소를 순서쌍 `(x, y)` 하나로 묶어 함수에 넣을 수 있으며,
타입 `A`, `B`의 원소로 만든 순서쌍의 타입은 `A × B`이다.
`p : A × B`일 때 첫 번째 원소는 `p.1`, 두 번째 원소는 `p.2`로 꺼내며,
`×`는 `\times`로 입력한다.

자연수의 순서쌍 하나를 받아 두 성분의 합을 구하는 함수 `addPair`를 정의하자.

```savedLean
def addPair (p : Nat × Nat) : Nat := p.1 + p.2
```

Lean의 자연수 덧셈 함수 `Nat.add`는 앞에서 정의한 `add`와 같이 두 자연수를 차례로 받는다.
`addPair (2, 3)`을 계산하면 `Nat.add 2 3`과 같이 $`5`를 얻는다.
다만 인수를 받는 방식에 따라 두 함수의 타입은 각각
`Nat → Nat → Nat`와 `(Nat × Nat) → Nat`로 다르다.
`addPair`에는 `(2, 3)`처럼 순서쌍을 넣어야 한다.

{anchor "intro-argument-adapters"}[]`fun`으로 인수를 받는 방식을 바꿀 수도 있다.
자연수 덧셈 함수 `Nat.add`를 순서쌍에 사용하려면 순서쌍의 두 성분을 꺼내 `Nat.add`에 차례로 넣으면 된다.
이를 `fun (p : Nat × Nat) => Nat.add p.1 p.2`로 적으면
순서쌍 `p` 하나를 받는 새 함수를 얻는다.
여기에 `(2, 3)`을 넣으면 `p.1`은 `2`, `p.2`는 `3`이므로 `Nat.add 2 3`을 계산한다.

```lean (name := pairFromAddValue)
#eval (fun (p : Nat × Nat) => Nat.add p.1 p.2) (2, 3)
```

```leanOutput pairFromAddValue
5
```

반대로 순서쌍을 받는 `addPair`를 두 자연수 `x`, `y`에 사용하려면
이 둘을 `(x, y)`로 묶어 넣으면 된다.
이때 `fun` 뒤에 `x`와 `y`를 차례로 적으면
두 인수를 하나씩 받는 함수를 얻는다.

```lean (name := argumentsFromAddPairValue)
#eval (fun (x y : Nat) => addPair (x, y)) 2 3
```

```leanOutput argumentsFromAddPairValue
5
```

일반적으로도 `A → B → X` 타입의 함수를 순서쌍에 사용하려면
두 성분을 꺼내 차례로 넣고,
`(A × B) → X` 타입의 함수를 두 인수에 사용하려면 이들을 순서쌍으로 묶어 넣으면 된다.
두 타입은 서로 다르지만 이처럼 인수를 받는 방식을 바꾸어 사용할 수 있다.
이 교재에서는 주로 인수를 차례로 받는 방식으로 함수를 정의하겠다.

## 순서쌍의 비교
%%%
tag := "functions-pair-comparison"
%%%

두 순서쌍이 같으려면 각 자리의 원소가 같아야 한다.
즉 $`(a,b)=(a',b')`는 $`a=a'`이고 $`b=b'`인 것과 동치이다.

*보기* $`a=c`이고 $`b=d`이면 $`(a,b)=(c,d)`이다.
순서쌍에서도 `ext`로 두 성분을 각각 비교한다.

```savedLean
example {A B : Type} (a c : A) (b d : B)
    (ha : a = c)
    (hb : b = d) :
    (a, b) = (c, d) := by
  ext
  · exact ha
  · exact hb
```

반대로 순서쌍이 같다는 가정이 주어지면 각 성분의 등식을 얻을 수 있다.
`indisc at h with ha hb`는 가정 `h : (a, b) = (c, d)`에서
`ha : a = c`와 `hb : b = d`를 얻는 전술이다.
예를 들어 두 성분의 자리를 바꾼 순서쌍도 서로 같음을 보이자.
목표의 `(b, a)`에는 등식 `h`의 왼쪽인 `(a, b)`가 그대로 나타나지 않으므로
먼저 각 성분의 등식을 얻어 대입하면 편리하다.

```savedLean
example {A B : Type} (a c : A) (b d : B)
    (h : (a, b) = (c, d)) :
    (b, a) = (d, c) := by
  indisc at h with ha hb
  rw [ha, hb]
```

여기서 `indisc`은 원래 등식 `h`를 유지하며 성분의 등식 두 개에 각각 이름을 붙인다.
이후 `rw [ha, hb]`로 `a`를 `c`로, `b`를 `d`로 바꾸면 양변이 같아진다.

`ext`와 `indisc`은 기본적으로 비교 규칙을 한 번 적용한다.
순서쌍 안에 다시 순서쌍이 있으면 먼저 바깥의 두 성분을 비교하며,
안쪽 성분은 다음 호출에서 비교한다. 필요한 경우 `ext : 2`로 두 겹을 비교할 수 있다.

집합 `S : Set A`, `T : Set B`의 곱은 `A × B` 위의 집합으로 정의한다.
순서쌍 `p`가 이 집합에 속하려면 `p.1 ∈ S`와 `p.2 ∈ T`가 모두 성립해야 한다.

```savedLean
def setProduct {A B : Type}
    (S : Set A) (T : Set B) : Set (A × B) :=
  fun p => p.1 ∈ S ∧ p.2 ∈ T
```

*보기* $`a \in S`이고 $`b \in T`이면 $`(a,b) \in S \times T`이다.
원소 조건이 논리곱이므로 `constructor`로 나눈 두 목표에 주어진 증명을 사용하면 된다.

```savedLean
example {A B : Type}
    (S : Set A) (T : Set B) (a : A) (b : B)
    (ha : a ∈ S)
    (hb : b ∈ T) :
    (a, b) ∈ setProduct S T := by
  constructor
  · exact ha
  · exact hb
```

*문제 14* $`(a,b)\in S\times T`이면 $`(b,a)\in T\times S`임을 증명하라.

```savedLean -keep
theorem exercise_setProduct_swap {A B : Type}
    (S : Set A) (T : Set B) (a : A) (b : B)
    (h : (a, b) ∈ setProduct S T) :
    (b, a) ∈ setProduct T S := by
  sorry
```

*문제 15* (좌표 함수)

첫 좌표를 꺼내는 함수 $`p:\mathbb{N}\times\mathbb{N}\to\mathbb{N}`에 대하여
전사성을 증명하고 단사성이 성립하지 않음을 보이라.
단사성을 반박할 때에는 함수값이 같아지는 서로 다른 두 순서쌍을 찾으라.

```savedLean -keep
def practiceFirst : Nat × Nat → Nat := fun p => p.1
theorem exercise_first_surjective :
    Surjective practiceFirst := by
  sorry

theorem exercise_first_not_injective :
    ¬ Injective practiceFirst := by
  sorry
```

*문제 16* (대각선 함수)

$`d(n)=(n,n)`으로 정한 함수 $`d:\mathbb{N}\to\mathbb{N}\times\mathbb{N}`의 단사성을 증명하라.
또한 이 함수는 전사가 아님을 증명하라.

```savedLean -keep
def practiceDiagonal : Nat → Nat × Nat := fun n => (n, n)
theorem exercise_diagonal_injective :
    Injective practiceDiagonal := by
  sorry

theorem exercise_diagonal_not_surjective :
    ¬ Surjective practiceDiagonal := by
  sorry
```

# 역함수
%%%
tag := "functions-inverses"
file := "inverses"
%%%

함수 $`f : A\to B`를 적용한 뒤 원래 원소로 돌아가려면
반대 방향의 함수 $`g : B\to A`가 필요하다.
두 함수를 어느 순서로 합성하든 항등함수가 되는 경우를 정의하자.

*정의* 함수 $`f : A\to B`와 $`g : B\to A`가 모든 $`x\in A`, $`y\in B`에 대하여
$`g(f(x))=x`와 $`f(g(y))=y`를 만족하면 $`g`를 $`f`의 *역함수*라고 한다.
즉 $`g\circ f=\operatorname{id}_A`이고 $`f\circ g=\operatorname{id}_B`이다.

역함수는 보통 $`f^{-1}`로 쓰므로 앞에서 배운 역상의 표기 $`f^{-1}(T)`와 구별할 필요가 있다.
원소 $`y\in B`에 대한 $`f^{-1}(y)`는 역함수의 값이며,
집합 $`T\subseteq B`에 대한 $`f^{-1}(T)`는 $`f(x)\in T`를 만족하는 원소 $`x`들의 집합이다.
역상을 정의할 때는 이 원소 조건만 사용하므로 $`f`에 역함수가 없어도 $`f^{-1}(T)`를 쓸 수 있다.

*보기* 항등함수는 자기 자신의 역함수이다.
어느 원소에 두 번 적용해도 원래 원소를 얻으므로 다음 두 등식이 성립한다.

```savedLean
theorem functions_identity_twice {A : Type}
    (x : A) :
    identity A (identity A x) = x := by
  rfl

example {A : Type} :
    identity A ∘ identity A = identity A := by
  ext x
  exact functions_identity_twice x
```

*보기* 순서쌍의 두 원소를 바꾸는 함수는 한 번 더 원소를 바꾸면 원래 순서쌍을 돌려준다.
즉 $`A\times B`에서 $`B\times A`로 가는 함수 $`(a,b)\mapsto(b,a)`의 역함수는
$`B\times A`에서 $`A\times B`로 가는 함수 $`(b,a)\mapsto(a,b)`이다.

```savedLean
def swapPair {A B : Type} (p : A × B) : B × A := (p.2, p.1)
theorem swapPair_twice {A B : Type} (p : A × B) :
    swapPair (swapPair p) = p := by
  rfl
```

먼저 적용하는 안쪽의 `swapPair`의 값은 `B × A`의 원소이므로
그 값에 다시 사용하는 `swapPair`는 `B × A → A × B`인 함수이다.
위 등식은 두 타입을 서로 바꾸어도 성립하므로 양쪽 순서의 역함수 조건을 모두 확인한 것이다.

이 등식으로 `swapPair`가 전단사임을 보일 수 있다.
$`\operatorname{swapPair}(p)=\operatorname{swapPair}(q)`이면 양변에 한 번 더 `swapPair`를 적용하여
$`p=q`를 얻으므로 단사이다. 공역의 원소 $`q`에 대해서는
원소 $`\operatorname{swapPair}(q)`를 택하면 그 함수값이 $`q`이므로 전사이다.

```savedLean
theorem swapPair_bijective {A B : Type} :
    Bijective (swapPair : A × B → B × A) := by
  constructor
  · intro p q hpq
    have h :
        swapPair (swapPair p) = swapPair (swapPair q) := by
      rw [hpq]

    rw [swapPair_twice, swapPair_twice] at h
    exact h

  · intro q
    exists (swapPair q)
```

단사성의 증명에서는 `swapPair_twice`로 양변을 각각 `p`, `q`로 바꾼다.
전사성에서 선택한 원소의 함수값은 두 성분을 두 번 바꾼 순서쌍이므로
정의에 따른 계산으로 `q`와 같음을 확인한다.

## 전단사와 원소의 유일성
%%%
tag := "functions-inverse-construction"
%%%

역함수를 구성하려면 각 $`y\in B`에 대응하는 원소를 정해야 한다.
$`f`가 전단사이면 전사성에 따라 $`f(x)=y`인 원소 $`x\in A`가 존재한다.
다른 원소 $`z`도 $`f(z)=y`를 만족하면 $`f(z)=f(x)`이므로 단사성에 따라 $`z=x`이다.
각 $`y\in B`에 대하여 $`f(x)=y`인 원소 $`x\in A`가 유일하게 존재함을 Lean으로 증명하자.
아래 명제에서는 원소의 존재를 `∃ x`로 쓰고,
그 원소가 만족하는 조건과 유일성을 논리곱으로 묶었다.

```savedLean
theorem bijective_preimage_unique {A B : Type} (f : A → B)
    (hf : Bijective f) :
    ∀ y : B, ∃ x : A,
      f x = y ∧ ∀ z : A, f z = y → z = x := by
  intro y
  -- 전사성으로 f x = y인 원소를 얻는다.
  unpack hf.surj y with ⟨x, hx⟩
  exists x
  constructor
  · exact hx
  · intro z hz
    -- 같은 함수값을 갖는 원소는 단사성으로 같다.
    apply hf.inj
    rw [hz, hx]
```

`hf.surj y`는 `∃ x, f x = y`의 증명이므로 `unpack`으로 원소 `x`와 등식 `hx`를 얻는다.
유일성을 보이는 부분에서 `apply hf.inj`를 쓰면 목표가 `f z = f x`가 되고,
`rw [hz, hx]`는 대괄호 안의 등식을 왼쪽부터 차례로 사용한다.
먼저 `hz`로 `f z`를 `y`로 바꾸고 이어서 `hx`로 `f x`를 `y`로 바꾸면 양변이 같아진다.

## 원소의 선택과 역함수
%%%
tag := "functions-existence-and-values"
%%%

각 `y : B`에 대해 `hf.surj y`는 `f x = y`인 원소가 존재함을 보장한다.
이 원소를 역함수의 값으로 택할 때 `Classical.choose`를 사용한다.
선택한 원소가 조건을 만족한다는 증명은 `Classical.choose_spec`으로 얻는다.
이 선택은 Lean의 선택공리에 의존한다.

전단사성의 증명을 `hf`라고 할 때, 구성할 역함수를 `inverseMap f hf : B → A`로 나타내자.
이를 사용하여 계산할 때 필요한 성질은 다음 두 등식이다.

- `inverseMap f hf (f x) = x`: 먼저 `f`를 적용했다가 역함수로 돌아오면 `x`를 얻는다.
- `f (inverseMap f hf y) = y`: 역함수로 고른 원소에 `f`를 적용하면 `y`를 얻는다.

예를 들어 `swapPair`의 역함수는 두 성분을 다시 바꾸므로
`(b, a)`를 `(a, b)`로 보낸다. 일반적인 전단사에서도 이 두 등식을 만족하는 함수를
만들 수 있는지 확인하기 위해, 먼저 존재명제의 증명과 함수값으로 사용할 원소를 구별하자.
`hf.surj y`는 `∃ x, f x = y`의 증명이다.
이 명제를 `unpack`이나 `rcases`로 분해하여 다른 명제를 증명할 수는 있지만,
그 안의 원소를 꺼내 `A`의 값으로 반환할 수는 없다.
예를 들어 `∃ n : Nat, True`는 $`0`을 제시해서도, $`1`을 제시해서도 증명할 수 있다.
Lean은 이 두 증명을 같은 명제의 증명으로서 같게 취급한다.
만약 증명에 사용한 원소를 그대로 꺼내 계산할 수 있다면
같게 취급하는 두 증명에서 서로 다른 자연수 $`0`과 $`1`을 얻게 된다.
이를 막기 위해 존재명제의 증명을 분해하여 계산에 쓸 값을 만드는 데에는 제한이 있다.
원소의 유일성을 보인 경우에도 존재명제에서 값을 꺼내려면 별도의 원소 선택이 필요하다.

값과 증명을 부분타입 `{x : A // f x = y}`으로 제공받았다면 `.val`로 값을 꺼낼 수 있다.
전사성은 이 부분타입의 원소가 아니라 `∃ x, f x = y`의 증명으로 주어지므로 원소 선택이 필요하다.

```savedLean -show
theorem identity_preimage_exists {A : Type} (y : A) :
    ∃ x : A, identity A x = y := by
  exists y

def identityPreimage {A : Type} (y : A) :
    {x : A // identity A x = y} :=
  { val := y, property := by rfl }
```

술어 `P : A → Prop`와 존재명제의 증명 `h : ∃ x, P x`가 주어졌을 때
`Classical.choose h`는 `P`를 만족하는 `A`의 원소 하나를 정한다.
원소의 유일성을 요구하지 않으므로 조건을 만족하는 원소가 여러 개일 때도 사용할 수 있다.
조건을 만족하는 원소가 여러 개라면 존재성을 증명할 때 제시했던 원소와 다른 원소를 고를 수도 있다.
어느 원소를 고르든 조건 `P`를 만족한다는 성질을 사용할 수 있다.

선택한 원소로 추론하려면 그 원소가 조건을 만족한다는 증명도 필요하다.
`Classical.choose h`의 타입은 `A`이고,
`Classical.choose_spec h`는 바로 그 원소에 대한 `P (Classical.choose h)`의 증명이다.
역함수에서는 각 `y`에 대해 `hf.surj y`를 `Classical.choose`와 `Classical.choose_spec`에 넣는다.
선택한 원소들을 함수값으로 삼고 $`f(g(y))=y`의 증명을 함께 담으면
함수 $`g:B\to A`와 그 성질을 하나의 부분타입으로 구성할 수 있다.

`Classical.choose`는 조건을 만족하는 원소를 정하지만 그 원소를 계산하는 방법을 제공하지는 않는다.
이 선택을 이용하여 함수를 정의할 때는 `def` 앞에 `noncomputable`을 붙인다.

```savedLean
noncomputable def inverseMapData {A B : Type} (f : A → B)
    (hf : Bijective f) :
    { g : B → A // ∀ y, f (g y) = y } :=
  { val := fun y => Classical.choose (hf.surj y)
    property := by
      intro y
      exact Classical.choose_spec (hf.surj y) }
```

`val`에는 선택한 원소를 함수값으로 삼는 함수를 넣는다.
`property`에서는 임의의 `y`를 택한 뒤
같은 존재성의 증명 `hf.surj y`에 `choose_spec`을 적용한다.
이로써 `val`에 넣은 함수가 모든 `y`에서 $`f(g(y))=y`를 만족함을 보인다.

이제 `inverseMapData`에서 함수를 꺼내 `inverseMap`으로 정의하고,
그 성질을 `inverseMap_right`라는 정리로 사용하자.
`.val`은 함수이며 `.property`는 모든 `y`에서 성립하는 등식의 증명이므로
후자에 `y`를 넣으면 그 원소에서의 등식을 얻는다.

```savedLean
noncomputable def inverseMap {A B : Type} (f : A → B)
    (hf : Bijective f) : B → A :=
  (inverseMapData f hf).val
theorem inverseMap_right {A B : Type} (f : A → B)
    (hf : Bijective f)
    (y : B) :
    f (inverseMap f hf y) = y := by
  exact (inverseMapData f hf).property y
```

반대 순서로 적용한 $`g(f(x))=x`도 확인하자.
$`f(g(f(x)))=f(x)`이므로 $`f`의 단사성을 사용하면 된다.

```savedLean
theorem inverseMap_left {A B : Type} (f : A → B)
    (hf : Bijective f)
    (x : A) :
    inverseMap f hf (f x) = x := by
  apply hf.inj
  exact inverseMap_right f hf (f x)
```

`apply hf.inj`는 두 원소가 같다는 목표를 그 함수값이 같다는 목표로 바꾼다.
남은 목표 `f (inverseMap f hf (f x)) = f x`는
`inverseMap_right`에 공역의 원소 `f x`를 넣어 얻는다.

이름의 `left`와 `right`는 합성에서 역함수가 놓이는 위치를 가리킨다.
`inverseMap_left`는 $`g(f(x))=x`를, `inverseMap_right`는 $`f(g(y))=y`를 나타낸다.

이제 역함수의 존재를 하나의 명제로 정리하자.
`inverseMap`은 함수 자체의 정의이고,
다음 정리는 두 역함수 조건을 만족하는 함수가 존재한다는 증명이다.

```savedLean
theorem inverse_exists {A B : Type} (f : A → B)
    (hf : Bijective f) :
    ∃ g : B → A,
      (∀ x, g (f x) = x) ∧ (∀ y, f (g y) = y) := by
  exists (inverseMap f hf)
  constructor
  · intro x
    exact inverseMap_left f hf x

  · intro y
    exact inverseMap_right f hf y
```

`exists`로 앞에서 정의한 함수를 제시한 뒤 두 조건을 각각 증명했다.

## 역함수의 유일성
%%%
tag := "functions-inverse-uniqueness"
%%%

*정리* 두 함수 $`g,h : B\to A`가 모두 $`f : A\to B`의 역함수이면 $`g=h`이다.

*증명* 임의의 $`y\in B`를 택하자.
$`g`가 역함수이므로 $`g(f(h(y)))=h(y)`이고,
$`h`도 역함수이므로 $`f(h(y))=y`이다.
첫 번째 등식에 두 번째 등식을 대입하면 $`g(y)=h(y)`를 얻는다.
이 등식이 모든 $`y`에 대하여 성립하므로 두 함수는 같다.

Lean에서는 먼저 `g (f (h y)) = h y`에 이름 `hgy`를 붙인다.
`rw [hh.right y] at hgy`로 그 안의 `f (h y)`를 `y`로 바꾸면
목표인 `g y = h y`의 증명을 얻는다.

```savedLean
theorem inverse_function_unique {A B : Type} (f : A → B)
    (g h : B → A)
    (hg : (∀ x, g (f x) = x) ∧ (∀ y, f (g y) = y))
    (hh : (∀ x, h (f x) = x) ∧ (∀ y, f (h y) = y)) :
    g = h := by
  ext y
  -- h(y)에 f를 적용한 뒤 g로 돌아오는 값을 비교한다.
  have hgy : g (f (h y)) = h y := by
    exact hg.left (h y)

  rw [hh.right y] at hgy
  exact hgy
```

가정 `hg`와 `hh`는 각 함수의 역함수 조건을 논리곱으로 묶은 것이다.
`hg.left`에 `h y`를 넣어 첫 등식을 얻고,
`hh.right y`로 그 등식의 안쪽 함수값을 바꾼다.

*보기* 전단사 `swapPair`에 `inverseMap`을 적용하여 얻은 역함수는 다시 `swapPair`이다.
`inverseMap`의 정의에서 원소를 어떻게 골랐는지와 관계없이
두 함수가 같은 역함수 조건을 만족하므로 유일성 정리를 사용할 수 있다.

```savedLean
example {A B : Type} :
    inverseMap (swapPair : A × B → B × A)
      swapPair_bijective =
      swapPair := by
  apply inverse_function_unique swapPair
  · constructor
    · exact inverseMap_left swapPair swapPair_bijective
    · exact inverseMap_right swapPair swapPair_bijective

  · constructor
    · exact swapPair_twice
    · exact swapPair_twice
```

첫 두 목표에는 `inverseMap`의 성질을 사용하고,
나머지 두 목표에는 앞에서 증명한 `swapPair_twice`를 사용한다.
이처럼 역함수의 유일성을 사용하면 `inverseMap`으로 정의한 함수를 구체적인 식으로 나타낼 수 있다.

## 역함수의 성질
%%%
tag := "functions-inverse-laws"
%%%

`inverseMap_left`와 `inverseMap_right`은 각각의 원소에서 성립하는 등식이므로
`ext`로 원소별 등식을 목표로 삼으면 합성함수와 항등함수의 같음을 보일 수 있다.

```savedLean
theorem inverseMap_compose {A B : Type} (f : A → B)
    (hf : Bijective f) :
    inverseMap f hf ∘ f = identity A := by
  ext x
  exact inverseMap_left f hf x

theorem compose_inverseMap {A B : Type} (f : A → B)
    (hf : Bijective f) :
    f ∘ inverseMap f hf = identity B := by
  ext y
  exact inverseMap_right f hf y
```

{anchor "functions-inverse-bijectivity"}[]*정리* 전단사함수의 역함수도 전단사이다.

*증명* 역함수를 $`g`라고 하자.
$`g(x)=g(y)`이면 양변에 $`f`를 적용하여 $`f(g(x))=f(g(y))`를 얻고
역함수의 성질로 양변을 바꾸면 $`x=y`이다.
또한 임의의 $`a\in A`에 대하여 $`g(f(a))=a`이므로 $`g`는 전사이다.

```savedLean
theorem inverseMap_bijective {A B : Type} (f : A → B)
    (hf : Bijective f) :
    Bijective (inverseMap f hf) := by
  constructor
  · intro x y hxy
    -- 같은 두 역함수 값에 f를 적용한다.
    have h :
        f (inverseMap f hf x) = f (inverseMap f hf y) := by
      rw [hxy]

    -- f와 역함수를 차례로 적용하면 원래 원소이다.
    rw [inverseMap_right f hf x,
      inverseMap_right f hf y] at h
    exact h

  · intro x
    -- f x를 역함수에 넣으면 x를 얻는다.
    exists (f x)
    exact inverseMap_left f hf x
```

단사성을 보일 때는 `hxy`로 두 함수값의 등식 `h`를 얻은 뒤
`inverseMap_right`을 `x`와 `y`에 각각 적용한 등식으로 양변을 바꾼다.
전사성을 보일 때는 `exists (f x)`로 원소를 택하면
남은 목표가 `inverseMap f hf (f x) = x`가 되므로 `inverseMap_left`를 사용한다.

# 연습문제
%%%
tag := "functions-exercises"
file := "exercises"
%%%

{anchor "sets-exercises"}[]집합 연산과 함수의 성질을 연결하여 다음 문제를 풀어 보자.
각 문제의 `sorry`를 증명으로 바꾸어 완성하라.

*문제 17* $`T \subseteq U`이면 $`S \setminus U \subseteq S \setminus T`임을 보이라.

```savedLean -keep
theorem exercise_diff_antitone_right
    {A : Type} (S T U : Set A)
    (hTU : T ⊆ U) :
    S \ U ⊆ S \ T := by
  sorry
```

*문제 18* (구체적인 교집합과 차집합)

$`T=\{3,4\}`라 하자. 앞에서 정의한 `twoThree`를 사용하여
$`\{2,3\}\cap T=\{3\}`과 $`\{2,3\}\setminus T=\{2\}`를 각각 증명하라.
두 증명에서 $`3`을 다루는 방식이 어떻게 다른지 비교하라.

```savedLean -keep
def practiceThreeFour : Set Nat :=
  fun n => n = 3 ∨ n = 4
theorem exercise_twoThree_inter :
    twoThree ∩ practiceThreeFour = (fun n => n = 3) := by
  sorry

theorem exercise_twoThree_diff :
    twoThree \ practiceThreeFour = (fun n => n = 2) := by
  sorry
```

*문제 19* (포함 관계의 반례)

(1) $`\mathbb{N}_{>0}\not\subseteq\{2,3\}`임을 증명하라.

(2) 첫 결과를 사용하여 두 집합이 서로 다름을 보이라.

```savedLean -keep
theorem exercise_positives_not_subset_twoThree :
    ¬ positives ⊆ twoThree := by
  sorry

theorem exercise_positives_ne_twoThree :
    positives ≠ twoThree := by
  sorry
```

*힌트* (1)에서는 양수이면서 $`2`도 $`3`도 아닌 자연수를 하나 택하라.

*문제 20* (공집합인 차집합)

$`S\setminus T=\varnothing`일 필요충분조건이 $`S\subseteq T`임을 증명하라.

```savedLean -keep
theorem exercise_diff_empty_iff {A : Type}
    (S T : Set A) :
    S \ T = ∅ ↔ S ⊆ T := by
  sorry
```

*힌트* $`S\setminus T=\varnothing`에서 $`S\subseteq T`를 보일 때는 원소 $`x\in S`를 택하라. $`x\notin T`라고 가정하면 $`x`가 차집합에 속하여 모순이 생긴다.

*문제 21* 전단사함수의 역함수에 다시 역함수를 취하면 원래 함수를 얻음을 증명하라.

```savedLean -keep
theorem exercise_inverse_inverse {A B : Type}
    (f : A → B)
    (hf : Bijective f) :
    inverseMap (inverseMap f hf)
      (inverseMap_bijective f hf) = f := by
  sorry
```

*힌트* `ext x`로 원소별 등식을 보인 뒤 역함수의 단사성을 사용하라.
남은 두 함수값은 `inverseMap_right`과 `inverseMap_left`로 각각 `x`가 된다.

*문제 22* (합성에서의 소거)

(1) 단사함수 $`h`에 대하여 $`h\circ f=h\circ g`이면 $`f=g`임을 증명하라.

(2) 전사함수 $`h`에 대하여 $`f\circ h=g\circ h`이면 $`f=g`임을 증명하라.
두 증명에서 단사성과 전사성이 각각 어디에 쓰이는지 주석으로 적으라.

```savedLean -keep
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
```

```savedLean -show
end Ample
```

```savedLean -show
export_course_compat
```
