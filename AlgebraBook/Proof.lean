import AlgebraBook.Meta.Lean
import AlgebraBook.Tactic.Rule
import AlgebraBook.Tactic.Classical
import AlgebraBook.Tactic.Auto
import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open AlgebraBook

#doc (Manual) "증명의 기초" =>

%%%
tag := "proof"
file := "proof"
%%%

수학의 증명에서는 가정을 세우고, 이미 아는 사실을 사용하여 결론을 얻는다.
Lean에서는 그 과정에 쓰인 명제와 추론을 코드로 적어 증명을 확인한다.
간단한 계산의 증명에서 시작하여 “두 사실이 모두 성립한다”, “이 조건이면 저 조건이 성립한다”와 같은 주장을 다룬다.
이어서 모든 원소나 어떤 원소에 관한 명제를 증명하고, 마지막에는 원소마다 조건을 정하는 술어 자체를 비교한다.

{anchor "introduction"}[]
```savedImport
import AlgebraBook.Tactic.Rule
import AlgebraBook.Tactic.Classical
import AlgebraBook.Tactic.Auto
```

```savedLean -show
open scoped Ample
namespace IntroExamples
```

# 명제와 증명
%%%
tag := "intro-values-and-types"
%%%

먼저 두 자연수를 더해 보자. 식 앞의 `#eval`은 그 식을 계산하여 결과를 보여 준다.

```lean (name := firstSum)
#eval 2 + 3
```

```leanOutput firstSum
5
```

이 식의 값은 자연수이다. Lean에서 값의 종류를 *타입*이라고 하며,
$`0`을 포함하는 자연수의 타입은 `Nat`이다.
자주 사용할 값에는 `def`로 이름을 붙일 수 있다.

```savedLean
def three : Nat := 3
def five : Nat := three + 2
```

`three : Nat`는 `three`가 자연수라는 뜻이고, `:= 3`은 그 값을 $`3`으로 정한다.
두 번째 정의는 앞의 이름을 사용하므로 `five`의 값은 $`5`이다.

{anchor "intro-comments"}[]코드에 설명을 덧붙일 때는 `--` 뒤에 적는다.
그 줄의 나머지는 주석이므로 Lean이 코드로 해석하지 않는다.
여러 줄의 설명은 `/-`와 `-/` 사이에 적을 수 있다.

## 명제
%%%
tag := "intro-propositions-and-goals"
%%%

`2 + 3`은 수를 나타내지만 `2 + 3 = 5`는 그 수에 관한 주장이다.
참 또는 거짓을 말할 수 있는 이러한 문장을 *명제*라고 하며,
Lean에서 명제의 타입은 `Prop`이다.
참인 명제와 거짓인 명제 모두 이름을 붙여 표현할 수 있다.

```savedLean
def comparison : Prop := 3 < 5
def reversedComparison : Prop := 5 < 3
```

위 선언은 두 명제를 정의한다. 명제를 적는 것만으로 그 명제가 증명되지는 않는다.

## 계산 결과의 증명
%%%
tag := "intro-proofs-as-values"
%%%

앞에서 계산한 등식이 맞음을 Lean으로 증명해 보자.

```savedLean
example : 2 + 3 = 5 := by
  rfl
```

`example` 뒤의 `:`에는 증명할 명제를 적고, `by` 아래에는 증명 단계를 적는다.
이때 쓰는 명령을 *전술*이라고 한다. `rfl`은 양변이 정의와 계산에 따라 같음을 확인하며,
여기서는 왼쪽의 `2 + 3`을 계산하면 오른쪽의 $`5`가 된다.
증명에 이름을 붙여 다시 사용할 때는 `example` 대신 `theorem 이름`으로 쓴다.
따라서 `example`은 설명을 위한 이름 없는 `theorem`이다.

{anchor "intro-proof-value-notation"}[]{anchor "intro-proposition-and-proof"}[]
명제의 이름과 증명의 이름을 나란히 비교해 보자.

```lean +fresh -keep
def comparison : Prop := 3 < 5
theorem comparisonProof : 3 < 5 := by decide
```

첫째 선언의 `comparison`은 명제이고, 둘째 선언의 `comparisonProof`는 그 명제의 증명이다.
`decide`는 명제를 계산하여 참임을 확인할 수 있을 때 그 증명을 만든다.
명제의 증명도 `def`로 정의할 수 있지만 보통 `theorem`을 사용한다.

```savedLean -show
theorem comparisonProof : 3 < 5 := by decide
```

{anchor "intro-presenting-proofs"}[]이미 얻은 증명은 이름으로 다시 사용할 수 있다.

```savedLean
example : 3 < 5 := by
  exact comparisonProof
```

아직 증명해야 하는 명제를 *목표*라고 한다.
`exact comparisonProof`는 목표인 `3 < 5`의 증명을 제시하여 증명을 마친다.
여기에 `comparison`을 적으면 명제 자체를 제시하게 되므로 증명이 필요한 자리를 채울 수 없다.
이처럼 증명에도 이름을 붙이고 다른 증명에서 사용할 수 있다는 뜻에서 *증명을 값으로 다룬다*고 말한다.

{anchor "proofs-assumptions-and-goals"}[]이번에는 $`n>0`이 가정으로 주어졌다고 하자.

```savedLean
example (n : Nat)
    (h : 0 < n) :
    0 < n := by
  exact h
```

`h : 0 < n`은 `h`가 부등식의 증명이라는 뜻이다.
이 선언에서는 그 증명을 인수로 받으므로 $`n>0`이라는 가정 아래에서 논증한다.
`by` 뒤에서 사용할 수 있는 자료와 목표는 다음과 같다.

```
n : Nat
h : 0 < n
⊢ 0 < n
```

위쪽의 `h`는 사용할 수 있는 증명이고, `⊢` 뒤는 증명을 요구하는 명제이다.
웹의 코드 오른쪽 위 ‘단계 보기’나 코드 안의 전술을 누르면 이 상태를 확인할 수 있다.

*문제 1* (계산 결과)

$`4\cdot4=16`을 증명하라.
아래의 `sorry`는 미완성 증명의 자리이며 실제 증명으로 바꾸어야 한다.

```savedLean -keep
theorem exercise_four_square : 4 * 4 = 16 := by
  sorry
```

```savedLean -show
end IntroExamples
```

{anchor "using-proofs"}[]
```savedImport
import AlgebraBook.Tactic.Rule
```

```savedLean -show
open scoped Ample
```

```savedLean -show
namespace ProofExamples
```

```savedLean -show
open IntroExamples
```

# 함의
%%%
tag := "proofs-named-theorems"
file := "named-theorems"
%%%

“$`P`이면 $`Q`이다”라는 형태의 명제를 *함의*라고 하며 Lean에서는 `P → Q`로 쓴다.
먼저 이미 증명된 함의를 사용하여 결론을 얻은 뒤, 함의 자체를 증명하는 방법을 살펴보자.

부등식의 양변에 같은 수를 더하면 대소관계가 유지된다.
예를 들어 $`a<b`를 알고 있을 때 양변에 $`2`를 더하면 $`a+2<b+2`를 얻는다.
이 성질을 Lean에서는 `Nat.add_lt_add_right`라는 이름의 정리로 사용할 수 있다.

`#check` 뒤에 정리의 이름을 적으면 그 정리가 어떤 명제를 증명하는지 확인할 수 있다.

```lean (name := addLtAddRightType)
#check Nat.add_lt_add_right
```

```leanOutput addLtAddRightType
Nat.add_lt_add_right {n m : Nat} (h : n < m) (k : Nat) : n + k < m + k
```

{anchor "proofs-applying-named-theorems"}[]
아래에서는 자연수 `a`, `b`와 부등식 `a < b`의 증명 `h`가 주어졌다고 하자.
위 정리의 `n`, `m`에 각각 `a`, `b`를 넣고 `k`를 `2`로 정하면
결론은 `a + 2 < b + 2`가 된다.
목표는 `a + 2 < b + 2`이므로 위 정리를 사용하려면 전제 `a < b`를 확인하면 된다.
이처럼 정리의 결론을 현재 목표에 맞추고 필요한 전제를 새 목표로 삼는 전술이 `apply`이다.
`(k := 2)`로 양변에 더할 수를 명시하여 정리를 사용하자.

```savedLean
theorem add_two_preserves_lt (a b : Nat)
    (h : a < b) :
    a + 2 < b + 2 := by
  apply Nat.add_lt_add_right (k := 2)
  exact h
```

첫 줄에서는 `k`에 넣을 수를 `2`로 지정하여 정리를 사용하므로 목표가 `a < b`로 바뀐다.
이 부등식의 증명은 가정 `h`에 있으므로
둘째 줄에서 `exact h`로 제시하면 원래 부등식의 증명이 완성된다.
수학에서 “$`a<b`이므로 양변에 $`2`를 더하여 $`a+2<b+2`를 얻는다”라고 쓰는 추론을
Lean에서는 목표에서 필요한 전제로 거슬러 올라가며 작성한 것이다.

{anchor "intro-explicit-and-implicit-arguments"}[]이 정리의 `(h : n < m)`과 `(k : Nat)`는 직접 지정하는 *명시적 인수*이다.
앞에서는 `(k := 2)`처럼 이름으로 더할 수를 지정했다.
중괄호의 `{n m : Nat}`는 다른 인수나 목표에서 추론하는 *암시적 인수*이므로 보통 생략한다.
직접 정하려면 `(n := a)`처럼 적는다. `Nat.`는 자연수에 관한 정리들이 속한 이름 공간이다.

{anchor "proofs-inferred-theorem-arguments"}[]목표에 양변의 식이 모두 적혀 있으면 사용할 인수를 Lean이 정할 수도 있다.
앞의 목표 `a + 2 < b + 2`에서는 양변에 더하는 수가 `2`로 정해져 있으므로
`(k := 2)`를 생략해도 같은 정리를 사용할 수 있다.

```savedLean
example (a b : Nat)
    (h : a < b) :
    a + 2 < b + 2 := by
  apply Nat.add_lt_add_right
  exact h
```

이 코드에서 `apply`는 정리의 결론을 목표에 맞추면서 `k`를 `2`로 정하고,
전제 `a < b`를 새 목표로 남긴다.

이제 앞에서 증명한 `add_two_preserves_lt`를 사용해 새 부등식을 보이자.
양변에 $`2`를 두 번 더하려면 이 정리를 두 번 사용하면 된다.

```savedLean
example (a b : Nat)
    (h : a < b) :
    (a + 2) + 2 < (b + 2) + 2 := by
  apply add_two_preserves_lt
  apply add_two_preserves_lt
  exact h
```

첫 번째 적용 뒤에는 `a + 2 < b + 2`가 목표가 되고,
두 번째 적용 뒤에는 `a < b`가 목표가 된다.
마지막 전제의 증명으로 `h`를 제시하면 두 번의 정리 적용으로 원래 결론을 얻는다.

아래 문제에서 `sorry`를 증명으로 바꾸어 방금 배운 정리 적용을 연습하라.

*문제 2* 자연수의 부등식 양변에 $`3`을 더해도 부등식이 성립함을
앞에서 배운 정리 `Nat.add_lt_add_right`로 증명하라.

```savedLean -keep
theorem exercise_add_three_preserves_lt (a b : Nat)
    (h : a < b) :
    a + 3 < b + 3 := by
  sorry
```

:::solution
양변에 더할 수를 $`3`으로 지정하면 필요한 전제는 주어진 부등식이다.

```tryLean -keep
example (a b : Nat)
    (h : a < b) :
    a + 3 < b + 3 := by
  apply Nat.add_lt_add_right (k := 3)
  exact h
```
:::

## 식의 정리
%%%
tag := "proofs-propositions-and-proofs"
%%%

{anchor "proofs-simp"}[]식을 계산할 때는 $`a+0=a`, $`0a=0` 같은 성질로 불필요한 항을 없애기도 한다.
예를 들어 $`0a+(b+0)`은 $`0+b`를 거쳐 $`b`로 정리된다.
Lean의 `simp`는 정리 규칙으로 등록된 성질을 사용하여 식을 정리하는 전술이다.
자연수의 위 계산에는 이미 등록된 `Nat.zero_mul`, `Nat.add_zero`, `Nat.zero_add`를 사용한다.

```savedLean
example (a b : Nat) :
    0 * a + (b + 0) = b := by
  simp
```

각 규칙에는 식을 바꾸는 방향이 정해져 있다.
가령 `Nat.add_zero`는 `b + 0`을 `b`로 바꾸며,
이런 규칙을 반복하여 식을 일정한 형태로 정리하는 과정을 *정규화*라고 한다.
등식의 양변을 정리한 결과가 같으면 위와 같이 `simp`로 증명을 마칠 수 있다.

## 증명 안의 보조정리
%%%
tag := "proofs-naming-proofs"
file := "naming-proofs"
%%%

{anchor "intro-reusing-proof-values"}[]*보기* 직각을 낀 두 변의 길이가 $`3`, $`4`인 직각삼각형의 빗변을 구하자.

*풀이* 빗변을 $`c`라 하면 피타고라스 정리로 $`c^2=3^2+4^2=25`이다.
길이는 음수가 아니므로 $`c=5`이다.

{anchor "intro-pythagoras-proof-steps"}[]이 논증에서 피타고라스 정리는 직각이라는 증명을 받아
$`c^2=25`라는 중간 결론을 준다. 다음에는 그 등식의 증명을 제곱의 비교에 사용한다.
중간 결과에 이름을 붙이는 `have`를 쓰면 두 단계를 그대로 옮길 수 있다.

{anchor "intro-pythagoras-theorems"}[]이 예제는 빗변의 길이 `c`가 자연수인 경우로 한정한다.
삼각형이 직각삼각형이라는 명제를 `rightAngled`라고 하고,
피타고라스 정리와 제곱의 비교에 관한 다음 두 사실이 주어졌다고 하자.
기하학의 정의를 새로 작성하는 대신 이 두 사실을 사용하여 `c = 5`를 증명한다.

- `pythagoras : rightAngled → c * c = 3 * 3 + 4 * 4`
- `equal_of_equal_squares (a b : Nat) (h : a * a = b * b) : a = b`

첫 정리는 직각이라는 전제를 확인하면 빗변의 제곱을 구하는 데 쓸 수 있다.
둘째 정리는 두 자연수의 제곱이 같음을 확인하면 두 수가 같다는 결론을 준다.
화살표 `→`로 적은 첫 정리의 전제도 `apply`를 쓰면 새 목표로 남는다.

```savedLean -show
theorem equal_of_equal_squares (a b : Nat)
    (h : a * a = b * b) : a = b := by
  apply Nat.mul_self_inj.mp
  exact h

section Pythagoras
variable (c : Nat) (rightAngled : Prop)
variable (pythagoras : rightAngled → c * c = 3 * 3 + 4 * 4)
include pythagoras
```

이 증명에서 사용할 가정과 정리는 다음과 같다.
정리의 인수 `hRight`는 이 삼각형이 직각이라는 증명이다.

```
c : Nat
rightAngled : Prop
pythagoras : rightAngled → c * c = 3 * 3 + 4 * 4
```

{anchor "intro-pythagoras-lean"}[]`have hSquare : c * c = 25 := by` 아래에서 중간 등식을 증명하자.
`have`의 `:` 뒤에는 증명할 명제를 적고, `:= by` 아래에는 그 증명을 적는다.
이 증명을 마치면 `hSquare`라는 이름으로 사용할 수 있다.

```savedLean
theorem hypotenuse_eq_five
    (hRight : rightAngled) :
    c = 5 := by
  -- 직각이라는 가정으로 빗변의 제곱을 구한다.
  have hSquare : c * c = 25 := by
    apply pythagoras
    exact hRight

  -- 두 자연수의 제곱이 같으므로 길이도 같다.
  apply equal_of_equal_squares c 5
  exact hSquare
```

`have`를 시작하기 전에는 `c = 5`를 보이고 있다.
들여쓴 내부 증명에서는 잠시 `c * c = 25`를 목표로 삼으며,
`apply pythagoras`로 필요한 전제 `rightAngled`를 남긴 뒤 `exact hRight`로 확인한다.
정리에 적힌 `3 * 3 + 4 * 4`를 계산하면 `25`이므로 이 증명이 중간 등식에 맞는다.

내부 증명이 끝나면 원래 목표인 `c = 5`로 돌아오고,
사용할 수 있는 증명에 `hSquare : c * c = 25`가 추가된다.
두 제곱의 비교 정리를 적용하면 `c * c = 5 * 5`를 보이면 되므로
방금 얻은 `hSquare`로 증명을 마친다.
들여쓰기는 이처럼 중간 명제를 증명하는 부분과 원래 논증을 이어 가는 부분을 구별한다.

*확인* `have`의 내부 증명이 끝난 위치에서 증명 상태를 확인하라.
목표는 `c = 5`이고, 가정에는 새로 얻은 `hSquare : c * c = 25`가 있다.

```savedLean -show
end Pythagoras
```

*문제 3* (부등식과 연속된 덧셈)

(1) $`a<b`이면 임의의 자연수 $`c`에 대하여 $`a+c<b+c`임을 증명하라.

(2) 첫 결과를 두 번 사용하여 $`(a+c)+d<(b+c)+d`를 보이라.

```savedLean -keep
theorem exercise_shift_lt (a b c : Nat)
    (hab : a < b) :
    a + c < b + c := by
  sorry

theorem exercise_two_shifts_lt (a b c d : Nat)
    (hab : a < b) :
    (a + c) + d < (b + c) + d := by
  sorry
```

## 함의의 증명과 사용
%%%
tag := "proofs-proving-implications"
file := "proving-implications"
%%%

양변에 $`2`를 더한 예제에서는 $`a<b`를 가정하여 $`a+2<b+2`를 보였다.
그때는 가정을 `(h : a < b)`처럼 인수로 먼저 적었다.
이제 함의 자체를 `P → Q`라는 목표로 두고, 증명 안에서 가정을 도입해 보자.
`(h : P) : Q`와 `: P → Q`는 모두 $`P`를 가정하여 $`Q`를 보이는 명제를 나타낸다.
Lean에서는 목표가 `P → Q`일 때 `intro hP`로 가정 `hP : P`를 도입하며
이후에는 `Q`가 새 목표가 된다.

*보기* $`P`를 가정하면 $`P`가 성립하므로 $`P \Rightarrow P`이다.

```savedLean
example (P : Prop) : P → P := by
  intro hP
  exact hP
```

처음 목표인 `P → P`에서 `intro hP`를 쓰면 가정 `hP : P` 아래에서 `P`를 보이는 목표로 바뀐다.
따라서 `exact hP`로 이미 갖고 있는 증명을 제시하면 증명이 끝난다.

{anchor "proofs-two-assumptions"}[]*정리* $`P`가 성립하고 $`P \Rightarrow Q`도 성립하면 $`Q`가 성립한다.
이를 두 가정을 차례로 받는 함의로 쓰면 다음과 같다.

$$`P \Rightarrow \bigl((P \Rightarrow Q) \Rightarrow Q\bigr).`

Lean에서는 이 명제를 `P → (P → Q) → Q`로 쓴다.
화살표는 오른쪽부터 묶으므로 `P → ((P → Q) → Q)`로 읽으며,
먼저 `P`를 가정한 뒤 `P → Q`를 가정하여 `Q`를 보이라는 뜻이다.
가정의 순서를 정리하면 다음과 같다.

1. `P`를 가정하고 그 증명에 `hP`라는 이름을 붙인다.
2. `P → Q`를 가정하고 그 증명에 `hPQ`라는 이름을 붙인다.
3. 이제 `Q`를 보여야 하며 두 가정을 함께 사용하면 이 결론을 얻는다.

마지막 추론을 Lean으로 옮길 때는 목표에서 거꾸로 생각해 보자.
`hPQ : P → Q`에서 `hPQ`는 이 함의의 증명이다.
`hPQ`에 의하면 $`P`가 성립할 때 $`Q`가 성립하므로
목표 $`Q`를 보이는 데 필요한 것은 전제 $`P`이다.
이때 `apply hPQ`를 쓰면 목표가 `Q`에서 `P`로 바뀌며,
이미 갖고 있는 가정 `hP`로 이 목표를 해결할 수 있다.

```savedLean
example (P Q : Prop) : P → (P → Q) → Q := by
  intro hP
  intro hPQ
  apply hPQ
  exact hP
```

각 줄에서 가정과 목표는 다음과 같이 변한다.

1. `intro hP`: 가정 `hP : P`가 들어오고, 목표는 `(P → Q) → Q`가 된다.
2. `intro hPQ`: 가정 `hPQ : P → Q`가 들어오고, 목표는 `Q`가 된다.
3. `apply hPQ`: 함의의 결론이 목표 `Q`와 같으므로 그 전제 `P`를 새 목표로 삼는다.
4. `exact hP`: 새 목표 `P`의 증명을 이미 갖고 있으므로 이를 제시하여 증명을 마친다.

`apply hPQ`와 `exact hP`를 함께 읽으면 “$`P`를 알고 있고 $`P`이면 $`Q`이므로 $`Q`이다”라는 추론이 된다.

## 증명의 적용
%%%
tag := "proofs-proof-application"
file := "proof-application"
%%%

앞의 `apply hPQ`와 `exact hP`를 하나의 식으로도 나타낼 수 있다.
먼저 Lean이 함의의 증명을 어떻게 표현하는지 살펴보자.

예를 들어 “$`a<b`이면 $`a+2<b+2`이다”를 증명한 논증은
첫 부등식의 증명이 주어질 때마다 둘째 부등식의 증명을 얻는 데 사용할 수 있다.
두 자연수 `a`, `b`를 고정하면 이 논증에 필요한 것은 `a < b`의 증명이고,
그 논증으로 얻는 것은 `a + 2 < b + 2`의 증명이다.

Lean은 함의의 증명을 이와 같이 전제의 증명을 받아 결론의 증명을 돌려주는 *함수*로 표현한다.
명제 `P`를 그 증명들의 타입으로 사용하므로,
`P`의 증명을 인수로 받아 `Q`의 증명을 돌려주는 함수의 타입은 `P → Q`이다.
따라서 `hPQ : P → Q`는 이런 함수이며,
인수 `hP : P`를 넣은 함수값 `hPQ hP`의 타입은 `Q`가 된다.
이때 함수에 넣는 인수는 명제 `P`가 아니라 그 명제의 증명 `hP`이다.
`P`가 참임을 이미 보였거나 가정으로 알고 있을 때 그 증명을 넣어 `Q`의 증명을 얻는다.
수학의 함수값 $`f(x)`를 Lean에서는 `f x`로 쓰므로 여기서 얻는 증명도 `hPQ hP`로 적는다.
이처럼 함수로 표현한 증명에 필요한 인수를 넣는 것을 “증명의 적용”이라고 한다.

이제 같은 정리를 다음과 같이 증명할 수 있다.

```savedLean
example (P Q : Prop) : P → (P → Q) → Q := by
  intro hP
  intro hPQ
  exact hPQ hP
```

`hPQ hP` 자체가 `Q`의 증명이므로 앞의 두 단계를 `exact hPQ hP` 한 줄로 쓸 수 있다.

`intro hP hPQ`는 두 가정을 차례로 도입하는 명령으로,
`intro hP`와 `intro hPQ`를 각각 쓰는 것과 같다.

함의 `P → Q`를 증명할 때 `intro hP`로 전제의 증명을 받고 `Q`를 증명하면,
그 전체 과정이 `P`의 증명을 받아 `Q`의 증명을 돌려주는 함수를 구성한다.

{anchor "proofs-theorem-arguments"}[]{ref "proofs-named-theorems"}[부등식의 보기]에서 사용한 정리도 같은 방식으로 읽을 수 있다.
`Nat.add_lt_add_right`에 부등식 `a < b`의 증명 `h`와 더할 수 `2`를 넣으면
`a + 2 < b + 2`의 증명을 얻는다.

```savedLean
example (a b : Nat)
    (h : a < b) :
    a + 2 < b + 2 := by
  exact Nat.add_lt_add_right h 2
```

여기서 `h`는 증명이고 `2`는 자연수이다.
`Nat.add_lt_add_right h 2` 전체는 부등식의 증명이므로 `exact`로 제시할 수 있다.

이미 완성된 증명을 식으로 적을 수 있으면 `:=` 오른쪽에 그 식을 바로 쓸 수도 있다.
예를 들어 위 선언은 증명 부분을 `:= Nat.add_lt_add_right h 2`로 적어도 된다.
`:= by` 아래에 전술을 쓰는 방식은 이러한 증명을 단계별로 구성하는 방법이다.

{anchor "proofs-forward-application"}[]`apply hPQ at hP`를 쓰면 가정 `hP : P`에 함의를 적용하여 `hP : Q`로 바꿀 수도 있다.
이 용법은 {ref "tactic-hypotheses"}[전술 부록]에서 목표에 적용하는 방법과 비교한다.

### 함의의 연결과 중간 증명
%%%
tag := "proofs-chaining-proof-values"
%%%

*보기* $`P \Rightarrow Q`와 $`Q \Rightarrow R`을 알고 있을 때 $`P \Rightarrow R`을 보이자.
$`P`를 가정하면 첫 함의로 $`Q`를 얻고, 이 사실을 두 번째 함의에 사용하여 $`R`을 얻는다.
이때 중간에 얻은 $`Q`의 증명에 이름을 붙이면 두 추론을 나누어 읽을 수 있다.

{ref "proofs-naming-proofs"}[피타고라스 정리 예제]와 같이 `have hQ : Q := by` 아래에서 `Q`를 증명하면
그 증명을 `hQ`라는 이름으로 사용할 수 있다.

```savedLean
example
    (P Q R : Prop)
    (hPQ : P → Q)
    (hQR : Q → R) :
    P → R := by
  intro hP
  -- 첫 함의로 중간 결론 Q를 얻는다.
  have hQ : Q := by
    apply hPQ
    exact hP

  -- 얻은 Q를 두 번째 함의에 사용한다.
  apply hQR
  exact hQ
```

들여쓴 증명에서 `Q`를 보인 뒤에는 `hQ : Q`를 사용할 수 있고 목표는 다시 `R`이 된다.
앞에서 배운 증명항의 적용을 사용하면 이 중간 증명을
`have hQ : Q := hPQ hP`로 짧게 적을 수도 있다.

{anchor "proofs-replacing-proofs"}[]앞의 증명에서는 `hP : P`를 남겨 두고 `have`로 `hQ : Q`를 추가했다.
원래 가정을 더 이상 따로 쓰지 않는다면 `replace`로 그 가정을 새 사실로 교체할 수 있다.
다음 증명에서는 `h : P`로부터 `Q`를 증명하고, 이후에는 같은 이름 `h`로 `Q`의 증명을 사용한다.

```savedLean
example (P Q R : Prop)
    (h : P)
    (hPQ : P → Q)
    (hQR : Q → R) :
    R := by
  replace h : Q := by
    apply hPQ
    exact h

  apply hQR
  exact h
```

`replace`의 내부에서 새 사실을 증명하는 동안에는 원래 `h : P`를 사용할 수 있다.
그 증명이 끝난 뒤에는 `h : Q`로 바뀐다.
이미 증명항을 적을 수 있다면 `replace h : Q := hPQ h`로 줄여 쓸 수도 있다.

*문제 4* $`P`, $`P \Rightarrow Q`, $`Q \Rightarrow R`을 차례로 가정하여 $`R`을 얻으라.

```savedLean -keep
theorem exercise_implication_chain
    (P Q R : Prop) :
    P → (P → Q) → (Q → R) → R := by
  sorry
```

:::solution
마지막 결론 $`R`에서 출발하면 먼저 $`Q`가 필요하고, 이를 얻으려면 $`P`가 필요하다.

```tryLean -keep
example (P Q R : Prop) :
    P → (P → Q) → (Q → R) → R := by
  intro hP hPQ hQR
  apply hQR
  apply hPQ
  exact hP
```
:::

# 명제의 결합
%%%
tag := "logic-connectives"
%%%

“$`3<5`이고 $`5<8`이다”라는 주장을 증명하려면 두 부등식을 모두 확인해야 한다.
“$`n=2`이거나 $`n=3`이다”라는 주장은 두 등식 중 하나가 성립하면 된다.
이처럼 명제를 결합하는 방식에 따라 증명에서 해야 할 일도 달라진다.
명제를 함의·논리곱·논리합·부정 등으로 연결하고 그 사이의 추론을 다루는 논리를 *명제논리*라고 한다.

## 논리곱
%%%
tag := "logic-conjunction"
%%%

두 명제 $`P`, $`Q`가 모두 성립한다는 명제를 *논리곱*이라고 하며 `P ∧ Q`로 쓴다.
목표가 논리곱이면 `constructor`로 두 목표를 만들고 각각 증명한다.
각 목표의 증명은 `·` 뒤에 적으며 `·`는 `\.`으로 입력한다.

```savedLean
theorem three_lt_five_and_five_lt_eight :
    3 < 5 ∧ 5 < 8 := by
  constructor
  · exact comparisonProof
  · decide
```

반대로 `h : P ∧ Q`가 주어지면 두 사실을 꺼내 사용할 수 있다.
`unpack h with ⟨hP, hQ⟩`는 `P`의 증명을 `hP`, `Q`의 증명을 `hQ`로 꺼낸다.
꺾쇠괄호 `⟨`, `⟩`는 각각 `\<`, `\>`로 입력한다.
이 두 사실로 논리곱의 순서를 바꾸어 보자.

```savedLean
theorem conjunction_comm (P Q : Prop) :
    P ∧ Q → Q ∧ P := by
  intro h
  unpack h with ⟨hP, hQ⟩
  constructor
  · exact hQ
  · exact hP
```

`unpack` 뒤에는 `hP : P`와 `hQ : Q`를 함께 사용할 수 있다.
`constructor`로 나뉜 첫 목표에는 `hQ`를, 둘째 목표에는 `hP`를 사용한다.
두 증명을 따로 꺼내지 않고 `h.left`, `h.right`로 각각 사용할 수도 있다.

세 명제의 논리곱 `P ∧ Q ∧ R`는 `P ∧ (Q ∧ R)`로 묶인다.
`constructor`를 쓰면 먼저 `P`와 `Q ∧ R`로 나뉘므로 둘째 목표에서 한 번 더 나누어야 한다.
`and_intros`는 이처럼 겹친 논리곱을 모두 나누어 `P`, `Q`, `R`를 각각 목표로 남긴다.
가정에서도 `unpack h with ⟨hP, hQR⟩`는 바깥 묶음만 꺼내므로
`hQR : Q ∧ R`의 두 증명이 필요하면 다시 `unpack`을 사용한다.

```savedLean
example (P Q R : Prop)
    (hP : P)
    (hQ : Q)
    (hR : R) :
    P ∧ Q ∧ R := by
  and_intros
  · exact hP
  · exact hQ
  · exact hR
```

## 논리합
%%%
tag := "logic-disjunction"
%%%

“$`n=2`이거나 $`n=3`이다”를 알고 있을 때 $`n<4`를 보이려면 어느 등식이 주어지든 결론을 얻어야 한다.
이 주장을 나타내는 *논리합* `P ∨ Q`는 $`P`, $`Q` 중 적어도 하나가 성립한다는 뜻이다.
목표가 논리합이면 `left`나 `right`로 증명할 쪽을 선택한다.

```savedLean
example : 2 = 2 ∨ 2 = 3 := by
  left
  rfl
```

논리합을 가정으로 받았을 때는 `cases`로 경우를 나눈다.
아래에서 `inl`은 왼쪽 명제가 주어진 경우이고 `inr`은 오른쪽 명제가 주어진 경우이다.

```savedLean
theorem disjunction_comm (P Q : Prop) :
    P ∨ Q → Q ∨ P := by
  intro h
  cases h with
  | inl hP =>
      right
      exact hP

  | inr hQ =>
      left
      exact hQ
```

첫 경우에는 `hP : P`를 얻으므로 목표 `Q ∨ P`의 오른쪽을 증명하고,
둘째 경우에는 `hQ : Q`를 얻으므로 왼쪽을 증명한다.
논리곱에서는 두 증명을 모두 꺼낼 수 있었지만 논리합에서는 주어진 경우마다 논증을 완성해야 한다.

{anchor "logic-pattern-decomposition"}[]*보기* $`P`와 $`P\Rightarrow R`가 함께 성립하거나,
$`Q`와 $`Q\Rightarrow R`가 함께 성립한다고 하자. 어느 경우에도 $`R`을 얻는다.
첫 경우에는 $`P`를 $`P\Rightarrow R`에 사용하고, 둘째 경우에는 $`Q`를 $`Q\Rightarrow R`에 사용하면 된다.

Lean에서도 먼저 `cases`로 두 경우를 나누고 각 경우에서 `unpack`으로 두 증명을 꺼낼 수 있다.
이처럼 여러 단계의 분해와 경우 구분을 한 패턴으로 지정하는 전술이 `rcases`이다.
아래의 `⟨hP, hPR⟩ | ⟨hQ, hQR⟩`에서 `|`는 두 경우를 나누고,
각 꺾쇠괄호는 그 경우에 함께 주어진 두 증명을 꺼낸다.

```savedLean
example (P Q R : Prop)
    (h : (P ∧ (P → R)) ∨ (Q ∧ (Q → R))) :
    R := by
  rcases h with ⟨hP, hPR⟩ | ⟨hQ, hQR⟩
  · apply hPR
    exact hP

  · apply hQR
    exact hQ
```

첫 분기에서는 `hP : P`와 `hPR : P → R`를 사용할 수 있고,
둘째 분기에서는 `hQ : Q`와 `hQR : Q → R`를 사용할 수 있다.

{anchor "sets-equivalence"}[]{anchor "sets-proving-equivalence"}[]{anchor "sets-using-equivalence"}[]

## 동치
%%%
tag := "logic-equivalence"
%%%

두 조건이 같은 경우에 성립함을 보이려면 양쪽 방향을 모두 확인한다.
예를 들어 “$`n=2`이거나 $`n=3`이다”와 “$`n=3`이거나 $`n=2`이다”는 서로 같은 조건이다.
앞 정리를 한 번은 원래 순서로, 한 번은 두 명제를 바꾸어 사용하면 두 방향을 모두 얻는다.

두 명제 $`P`, $`Q` 사이에서 `P → Q`와 `Q → P`가 모두 성립하면 두 명제가 *동치*라고 하며 `P ↔ Q`로 쓴다.
동치의 목표에서도 `constructor`로 두 방향을 나눈다.

```savedLean
theorem disjunction_comm_iff (P Q : Prop) :
    (P ∨ Q) ↔ (Q ∨ P) := by
  constructor
  · apply disjunction_comm
  · apply disjunction_comm
```

`h : P ↔ Q`가 주어지면 `h.mp`는 정방향 `P → Q`의 증명이고,
`h.mpr`는 역방향 `Q → P`의 증명이다.

```savedLean
example (P Q : Prop)
    (h : P ↔ Q)
    (hP : P) :
    Q := by
  apply h.mp
  exact hP
```

*문제 5* (동치의 연결)

$`P\leftrightarrow Q`이고 $`Q\leftrightarrow R`이면 $`P\leftrightarrow R`임을 증명하라.
각 방향에서 두 동치의 어느 방향을 사용하는지 확인하라.

```savedLean -keep
theorem exercise_logic_iff_trans (P Q R : Prop)
    (hPQ : P ↔ Q)
    (hQR : Q ↔ R) :
    P ↔ R := by
  sorry
```

*문제 6* (분배법칙)

$`P\land(Q\lor R)`일 필요충분조건은 $`(P\land Q)\lor(P\land R)`임을 증명하라.

```savedLean -keep
theorem exercise_logic_and_or_distrib (P Q R : Prop) :
    (P ∧ (Q ∨ R)) ↔ ((P ∧ Q) ∨ (P ∧ R)) := by
  sorry
```

# 부정과 고전논리
%%%
tag := "logic-negation-classical"
%%%

두 조건을 함께 만족할 수 없음을 보일 때는 그 조건들이 모두 성립한다고 가정한 뒤 모순을 얻는다.
부정도 이런 방식으로 증명하며, 부정의 부정에서 원래 명제를 얻는 추론으로 나아가면 고전논리가 필요하다.

## 부정의 증명
%%%
tag := "logic-negation"
%%%

항상 참인 명제는 `True`, 모순을 나타내는 명제는 `False`로 쓴다.
전술 `trivial`은 `True`와 같은 참인 목표를 증명하고,
`contradiction`은 모순인 가정이 있을 때 남은 목표를 증명한다.
`True.intro`는 `True`의 증명이며 `False.elim`은 모순에서 임의의 결론을 얻는 원리이다.

```savedLean
example : True := by
  trivial

example (P : Prop)
    (h : False) :
    P := by
  contradiction
```

명제 $`P`가 성립하지 않는다는 명제를 그 *부정*이라고 하며 `¬ P`로 쓴다.
Lean에서 이는 `P → False`로 정의된다.
따라서 `¬ P`를 증명할 때는 `intro hP`로 `P`를 가정하고 모순을 보이면 된다.
이 임시 가정은 $`P`가 실제로 참이라고 주장하는 것이 아니라, $`P`가 성립하면 어떤 결과가 나오는지 확인하는 단계이다.

```savedLean
example : ¬ False := by
  intro hFalse
  exact hFalse
```

이 예에서 `intro hFalse` 뒤에는 가정과 목표가 모두 `False`이므로 그 가정을 제시하면 된다.

이번에는 `hnotP : ¬ P`와 `hP : P`를 함께 알고 있다고 하자.
`hnotP`는 `P → False`의 증명이므로 앞에서 배운 `apply`를 사용할 수 있다.
목표 `False`에 `apply hnotP`를 쓰면 `P`가 새 목표로 남으며, 이는 `hP`로 증명한다.

```savedLean
example (P : Prop)
    (hnotP : ¬ P)
    (hP : P) :
    False := by
  apply hnotP
  exact hP
```

등식의 부정 `¬ (a = b)`는 `a ≠ b`로 줄여 쓴다.
예를 들어 `3 ≠ 5`를 증명하려면 두 수가 같다고 가정하여 모순을 보이면 된다.

## 대우
%%%
tag := "logic-contrapositive"
%%%

$`a<b`이면 $`a+2<b+2`이다. 따라서 $`a+2<b+2`가 성립하지 않는다면 $`a<b`도 성립할 수 없다.
만약 $`a<b`라면 처음의 함의에 따라 $`a+2<b+2`를 얻어 모순이 생기기 때문이다.

함의 $`P\Rightarrow Q`의 *대우*는 $`\neg Q\Rightarrow\neg P`이다.
원래 함의에서 그 대우를 얻는 위 논증은 부정의 정의만으로 작성할 수 있다.

```savedLean
theorem contrapositive (P Q : Prop)
    (h : P → Q) :
    ¬ Q → ¬ P := by
  intro hnotQ
  intro hP
  apply hnotQ
  apply h
  exact hP
```

첫 `intro`로 `¬ Q`를 가정하면 목표는 `¬ P`이다.
둘째 `intro`로 `P`를 가정하면 목표가 `False`로 바뀌며,
`h`로 얻은 `Q`를 `hnotQ`와 함께 사용하여 모순을 보인다.

대우는 두 명제의 자리만 바꾼 *역* $`Q\Rightarrow P`와 구별해야 한다.
예를 들어 $`n=2`이면 $`n<4`이지만 $`n<4`인 수가 모두 $`2`인 것은 아니다.
$`n=3`이 그 역의 반례이다.

## 배중률과 이중 부정
%%%
tag := "sets-classical-logic"
%%%

$`P`가 성립하면 $`\neg\neg P`도 성립한다.
실제로 $`\neg P`라고 가정하면 이미 알고 있는 $`P`와 모순이다.

```savedLean
theorem double_negation_intro (P : Prop)
    (hP : P) :
    ¬¬ P := by
  intro hnotP
  apply hnotP
  exact hP
```

이번에는 반대 방향인 $`\neg\neg P\Rightarrow P`를 생각하자.
가정은 `¬ P`의 증명을 받아 모순을 주지만, 목표인 `P`의 증명을 직접 제공하지는 않는다.
여기서 고전논리의 *배중률*을 사용하자. 배중률은 모든 명제 $`P`에 대해
$`P\lor\neg P`가 성립한다는 원리이다.

$`P`인 경우에는 원하는 결론을 이미 갖고 있고,
$`\neg P`인 경우에는 가정 $`\neg\neg P`와 모순이므로 어느 경우에도 $`P`를 얻는다.
Lean에서는 `by_cases h : P`로 이 두 경우를 나눈다.
첫 경우에는 `h : P`, 둘째 경우에는 `h : ¬ P`를 사용하며 목표는 양쪽 모두 `P`이다.

```savedLean
theorem double_negation_elim (P : Prop)
    (h : ¬¬ P) :
    P := by
  by_cases hP : P
  · exact hP
  · have hFalse : False := by
      apply h
      exact hP

    contradiction
```

이를 *이중 부정 제거*라고 한다. Lean의 정리 `Classical.not_not`도 `¬¬ P ↔ P`를 나타내므로
그 정방향 `Classical.not_not.mp`로 같은 추론을 사용할 수 있다.

이후에는 고전논리를 기본으로 사용하겠다. 다음 선언을 적으면 그 범위에서 고전논리를 사용할 수 있다.
이 설정은 `import`로 다른 파일에 전달되지 않으므로 풀이 파일에도 같은 선언을 둔다.

```savedLean
open scoped Classical
```

한 증명 안에서만 설정할 때는 `classical`을 쓴다.

## 귀류법과 대우의 역방향
%%%
tag := "logic-classical-proofs"
%%%

$`P`를 보이기 위해 $`\neg P`를 가정하여 모순을 얻는 방법을 *귀류법*이라고 한다.
이 논증은 $`\neg\neg P`를 증명하므로 이중 부정 제거를 사용하면 $`P`를 얻는다.
전술 `by_contra h`는 목표의 부정을 `h`로 가정하고 목표를 `False`로 바꾼다.

```savedLean
example (P : Prop)
    (h : ¬¬ P) :
    P := by
  by_contra hnotP
  apply h
  exact hnotP
```

`¬ P`를 보이기 위해 `P`를 가정하는 `intro`와, `P`를 보이기 위해 `¬ P`를 가정하는 `by_contra`에서
무엇이 목표이고 무엇이 임시 가정인지 비교하라.

이중 부정 제거 정리를 직접 사용할 때는 `apply Classical.not_not.mp`로 목표 `P`를 `¬¬ P`로 바꾼다.
그 목표의 증명을 이미 갖고 있으면 다음과 같이 마칠 수 있다.

```savedLean
example (P : Prop)
    (h : ¬¬ P) :
    P := by
  apply Classical.not_not.mp
  exact h
```

이제 대우에서 원래 함의를 얻어 보자.
$`\neg Q\Rightarrow\neg P`를 알고 $`P`를 가정했다고 하자.
만약 $`\neg Q`라면 대우에 따라 $`\neg P`를 얻어 모순이므로 귀류법으로 $`Q`이다.

```savedLean
theorem implication_of_contrapositive (P Q : Prop)
    (h : ¬ Q → ¬ P) :
    P → Q := by
  intro hP
  by_contra hnotQ
  apply h hnotQ
  exact hP
```

따라서 고전논리에서는 원래 함의와 그 대우가 동치이다.
원래 함의에서 대우로 가는 방향과 달리, 위 역방향에서는 귀류법을 사용했다.

```savedLean
theorem implication_iff_contrapositive (P Q : Prop) :
    (P → Q) ↔ (¬ Q → ¬ P) := by
  constructor
  · apply contrapositive
  · apply implication_of_contrapositive
```

*문제 7* (함의가 성립하는 경우)

고전논리에서 $`P\Rightarrow Q`일 필요충분조건은 $`\neg P\lor Q`임을 증명하라.
각 방향의 증명에서 배중률이 필요한지 함께 확인하라.

```savedLean -keep
theorem exercise_implication_cases (P Q : Prop) :
    (P → Q) ↔ (¬ P ∨ Q) := by
  sorry
```

{anchor "logic-transformations"}[]

## 드모르간 법칙
%%%
tag := "logic-de-morgan"
%%%

$`P` 또는 $`Q`가 성립한다는 주장이 거짓이라면 둘 중 어느 것도 성립할 수 없다.
따라서 $`\neg(P\lor Q)`는 $`\neg P\land\neg Q`와 동치이다.
이런 식으로 논리곱·논리합의 부정을 바꾸는 법칙을 *드모르간 법칙*이라고 한다.

```savedLean
theorem not_or_iff (P Q : Prop) :
    ¬ (P ∨ Q) ↔ (¬ P ∧ ¬ Q) := by
  constructor
  · intro h
    constructor
    · intro hP
      apply h
      left
      exact hP

    · intro hQ
      apply h
      right
      exact hQ

  · intro h hOr
    cases hOr with
    | inl hP =>
        apply h.left
        exact hP
    | inr hQ =>
        apply h.right
        exact hQ
```

정방향에서 `¬ P`를 보이는 내부 증명은 `P`를 가정하여 `P ∨ Q`를 만든 뒤 `h`와 모순을 얻는다.
`¬ Q`도 같은 방식으로 증명한다. 역방향에서는 `P ∨ Q`의 어느 쪽이 주어져도 함께 주어진 부정과 모순이다.
이 증명에는 배중률이나 귀류법을 쓰지 않았다.

논리곱의 부정에서는 $`\neg(P\land Q)\leftrightarrow(\neg P\lor\neg Q)`이다.
정방향에서 $`P`인지에 따라 나누자. $`\neg P`이면 결론의 왼쪽을 얻는다.
$`P`이면 $`Q`까지 성립할 수는 없으므로 $`\neg Q`를 얻는다.

```savedLean
theorem not_and_iff (P Q : Prop) :
    ¬ (P ∧ Q) ↔ (¬ P ∨ ¬ Q) := by
  constructor
  · intro h
    by_cases hP : P
    · right
      intro hQ
      apply h
      constructor
      · exact hP
      · exact hQ

    · left
      exact hP

  · intro h hAnd
    cases h with
    | inl hnotP =>
        apply hnotP
        exact hAnd.left
    | inr hnotQ =>
        apply hnotQ
        exact hAnd.right
```

이 정방향에서는 `by_cases`로 배중률을 사용했다. 역방향은 `P ∧ Q`에서 필요한 한쪽을 꺼내 모순을 얻는다.

## 함의의 반례
%%%
tag := "logic-negated-implication"
%%%

“$`P`이면 $`Q`이다”가 성립하지 않는 경우는 $`P`가 성립하면서 $`Q`가 성립하지 않는 경우이다.
전제가 거짓인 경우에는 그 전제를 가정하여 모순에서 결론을 얻을 수 있으므로 함의의 반례가 되지 않는다.
따라서 고전논리에서는 다음 동치가 성립한다.

$$`\neg(P\Rightarrow Q)\ \longleftrightarrow\ P\land\neg Q.`

정방향에서 먼저 $`P`를 보이자. 만약 $`\neg P`라면 $`P`를 가정했을 때 모순이므로 $`P\Rightarrow Q`를 얻어 가정과 모순이다.
또 $`Q`가 성립하면 $`P`를 가정하든 하지 않든 $`Q`를 제시할 수 있으므로 역시 $`P\Rightarrow Q`가 되어 모순이다.

```savedLean
theorem not_imp_iff (P Q : Prop) :
    ¬ (P → Q) ↔ (P ∧ ¬ Q) := by
  constructor
  · intro h
    constructor
    · by_contra hnotP
      apply h
      intro hP
      have hFalse : False := by
        apply hnotP
        exact hP

      contradiction

    · intro hQ
      apply h
      intro hP
      exact hQ

  · intro h hPQ
    apply h.right
    apply hPQ
    exact h.left
```

역방향에서는 $`P`와 $`\neg Q`를 알고 $`P\Rightarrow Q`를 가정한다.
이 함의에 $`P`를 사용하면 $`Q`를 얻으므로 $`\neg Q`와 모순이다.

## 자동 표현 정리
%%%
tag := "logic-auto-normalization"
%%%

고전논리에서 이중 부정을 제거하는 법을 확인했으므로 이후에는 이 변환을 자동으로 수행할 수도 있다.
`open scoped Ample.Auto`를 선언하면 각 전술 전후에 표현을 정리하며,
고전논리 설정이 켜져 있을 때 가정과 목표의 `¬¬ P`도 `P`로 정리한다.
이 선언의 범위는 아래 `section`에서 `end`까지이며, 구체적인 정리 범위는 {ref "tactic-auto-normalization"}[전술 부록]에서 설명한다.

```savedLean
section
open scoped Ample.Auto

example (P : Prop)
    (h : ¬¬ P) :
    P := by
  exact h

end
```


# 술어와 양화사
%%%
tag := "logic-predicates-quantifiers"
%%%

“$`3`은 양의 자연수이다”는 명제이지만 “$`n`은 양의 자연수이다”라는 조건은 $`n`에 넣을 수에 따라 참과 거짓이 달라진다.
이 조건을 나타내면 “모든 자연수가 양수이다”나 “양수인 자연수가 존재한다”도 표현할 수 있다.
먼저 원소에 따라 달라지는 조건을 함수로 정의하고, 그 조건에 관한 명제로 범위를 넓혀 보자.

## 함수의 정의
%%%
tag := "intro-functions"
%%%

```savedLean -show
end ProofExamples
namespace IntroExamples
```

{anchor "intro-function-application"}[]{anchor "intro-defining-functions"}[]
더할 두 수를 인수로 받아 그 합을 구하는 함수를 정의하자.

```savedLean
def add (x y : Nat) : Nat := x + y
```

`(x y : Nat)`는 두 인수가 자연수라는 뜻이고, 뒤의 `: Nat`는 결과의 타입이다.
함수값 $`f(x)`를 `f x`로 쓰는 것과 같이 `add 2 3`은 이 함수에 $`2`와 $`3`을 넣은 식이다.

```lean (name := functionSum)
#eval add 2 3
```

```leanOutput functionSum
5
```

하나의 인수가 복잡한 식이면 괄호로 묶는다.
`add (2 + 1) 4`에서는 $`2+1`과 $`4`를 더하며,
`add 2 (add 3 4)`에서는 안쪽 함수값 $`7`과 $`2`를 더한다.

```savedLean
theorem add_two_three : add 2 3 = 5 := by
  rfl
```

{anchor "intro-arguments-one-at-a-time"}[]`add x y`는 `(add x) y`로 읽는다.
`add x`는 $`x`를 더하는 함수이며 여기에 $`y`를 넣어 합을 얻으므로
`add`의 타입은 `Nat → (Nat → Nat)`이다.
보통 괄호를 생략하여 `Nat → Nat → Nat`로 쓴다.
앞에서 사용한 `Nat.add_lt_add_right h 2`도 증명 `h`와 자연수 `2`를 차례로 넣는 같은 표기이다.

## 술어
%%%
tag := "intro-predicate-definitions"
%%%

{anchor "intro-predicates"}[]“$`n`은 양의 자연수이다”라는 조건에 $`3`을 넣으면 $`0<3`이고,
$`0`을 넣으면 $`0<0`이다. 이처럼 원소마다 명제를 정하는 조건을 *술어*라고 한다.
Lean에서는 수를 받아 명제를 돌려주는 함수로 나타낸다.

```savedLean
def positive : Nat → Prop := fun n => 0 < n
```

`Nat → Prop`은 자연수를 받아 명제를 돌려주는 함수의 타입이다.
`fun n => 0 < n`은 수학의 $`n\mapsto(0<n)`을 나타내며,
`def`로 이 함수에 `positive`라는 이름을 붙일 수 있다.
앞의 `add`처럼 `def positive (n : Nat) : Prop := 0 < n`으로 정의해도 같은 술어이며,
이후에는 함수의 타입을 먼저 적는 형태를 사용하겠다.
`positive`는 술어이고 `positive 3`은 명제 $`0<3`이다.

같은 방식으로 방정식의 해라는 조건도 나타낼 수 있다.
자연수 $`a`를 고정하면 각 $`n`에 명제 $`n^2=a`가 대응된다.

```savedLean
def solvesSquare (a : Nat) : Nat → Prop :=
  fun n => n * n = a
```

`solvesSquare 16 4`는 $`4\cdot4=16`이고,
`solvesSquare 16 3`은 $`3\cdot3=16`이다.
두 식 모두 명제이지만 첫째만 참이다.
정의를 펼쳐 같은 명제가 되면 증명도 그대로 사용할 수 있다.
가령 `h : positive n`은 `0 < n`의 증명으로 쓸 수 있다.

함의를 증명할 때도 `fun`으로 인수를 받는 함수를 직접 쓸 수 있다.
`P → P`의 증명은 받은 증명을 그대로 돌려주므로 다음과 같다.

```savedLean
example (P : Prop) : P → P :=
  fun hP => hP
```

여기서 `hP`의 타입은 `P`이며 함수값도 `P`의 증명이다.
앞에서 사용한 `intro hP`와 `exact hP`는 이 함수의 인수와 함수값을 단계별로 정한 것이다.

*문제 8* (방정식의 해)

(1) 앞에서 증명한 `exercise_four_square`를 사용하여 $`4`가 방정식 $`n^2=16`의 해임을 보이라.

(2) 수의 값이 주어지지 않은 경우에도 해라는 가정에서 등식을 얻으라.

```savedLean -keep
theorem exercise_four_solves_square :
    solvesSquare 16 4 := by
  sorry

theorem exercise_square_proof (a n : Nat)
    (h : solvesSquare a n) :
    n * n = a := by
  sorry
```

```savedLean -show
end IntroExamples
namespace ProofExamples
open IntroExamples
open scoped Classical
```

## 전칭명제
%%%
tag := "proofs-universal-statements"
file := "universal-statements"
%%%

모든 자연수는 $`0` 이상이므로 자연수 $`3`도 $`0` 이상이다.
이 추론에서는 모든 자연수에 관한 사실에서 $`n=3`인 경우를 사용했다.
이처럼 “모든 원소에서 성립한다”는 명제를 *전칭명제*라고 한다.
원소 전체나 어떤 원소에 관해 말할 때 사용하는 기호를 *양화사*라고 하며,
이러한 원소에 대한 양화를 다루는 논리를 *일차 논리*라고 한다.

술어 `P : A → Prop`가 주어졌을 때
“$`A`의 모든 원소 $`x`에서 $`P(x)`가 성립한다”는 명제는 `∀ x : A, P x`로 쓴다.
예를 들어 위의 자연수에 관한 명제는 `∀ n : Nat, 0 ≤ n`이며,
기호 `∀`는 `\forall`로 입력한다.

{anchor "proofs-proving-forall"}[]전칭명제를 증명할 때는 임의의 원소 $`x`를 택하여 $`P(x)`를 보인다.
Lean에서는 `intro x`로 원소 `x : A`를 도입하고, 그 원소에 관한 명제 `P x`를 새 목표로 삼는다.

`(A : Type)`는 원소가 속할 타입 자체를 인수로 받는다.
앞에서 수를 `(n : Nat)`로 받았듯이, 여기서는 `Nat` 같은 타입을 `A`로 받는다.
`{A : Type}`로 적으면 다른 인수에서 추론하는 암시적 인수가 된다.

*보기* 모든 원소 $`x`에 대하여 $`x = x`이다.
앞에서 사용한 `rfl`로 이 원소가 자기 자신과 같음을 보인다.

```savedLean
example (A : Type) : ∀ x : A, x = x := by
  intro x
  rfl
```

`intro x`로 도입한 `x`에는 `A`의 원소라는 조건만 주어지며 특정한 값을 고를 수 없다.
어떤 원소에서도 성립하는 논증을 작성해야 하기 때문이다.
목표가 `x = x`로 바뀌면 `rfl`로 증명하며 이 논증은 `A`의 모든 원소에 적용된다.

## 전칭명제의 사용
%%%
tag := "proofs-using-forall-with-apply"
file := "using-forall-with-apply"
%%%

이번에는 모든 원소에 관한 가정 `h : ∀ x : A, P x`로부터
주어진 원소 `a : A`에 관한 명제 `P a`를 보이자.
모든 원소에서 성립하는 사실은 `a`에서도 성립하므로 다음 추론을 사용할 수 있다.

$$`\bigl(\forall x \in A,\ P(x)\bigr) \Rightarrow P(a), \qquad a \in A.`

```savedLean
theorem use_forall (A : Type) (P : A → Prop) (a : A) :
    (∀ x : A, P x) → P a := by
  intro h
  apply h
```

첫 줄의 `intro h`는 함의의 전제 전체를 가정으로 받으므로,
가정은 `h : ∀ x : A, P x`이고 목표는 `P a`이다.
이어서 `apply h`를 쓰면 Lean은 `h`의 결론 `P x`를 목표 `P a`에 맞추어 원소를 `a`로 정한다.
이 예제에서는 추가로 확인할 전제가 없으므로 `apply h`에서 증명이 끝난다.

{anchor "proofs-forall-application"}[]앞의 `use_forall` 증명에서는 `apply h` 대신 `exact h a`로 증명을 마칠 수도 있다.
`apply h`에서는 Lean이 목표를 보고 원소를 정하고,
`exact h a`에서는 사용할 원소를 직접 지정한다.
`h : ∀ x : A, P x`에 원소 `a : A`를 넣으면 `P a`의 증명을 얻으며,
이를 `h a`로 쓴다.
이 추론도 함수로 표현할 수 있다.
모든 원소에 적용되는 논증이 주어지면 원소 하나를 받아 그 원소에 관한 증명을 돌려줄 수 있기 때문이다.
예를 들어 모든 자연수 `n`에 대해 `0 ≤ n`을 증명한 논증은
`3`을 주면 `0 ≤ 3`의 증명을, `5`를 주면 `0 ≤ 5`의 증명을 제공한다.

Lean은 전칭명제의 증명도 원소를 받아 그 원소에서의 증명을 돌려주는 함수로 표현한다.
`h : ∀ x : A, P x`에 `a : A`를 넣으면 함수값 `h a`의 타입은 `P a`이다.
여기서는 넣은 원소에 따라 증명할 명제가 달라지므로 함수값의 타입도 인수에 따라 달라진다.
`∀ x : A, P x`는 이러한 함수의 타입을 나타내는 표기이다.

앞의 함의에서는 전제의 *증명*을 인수로 넣었고, 여기서는 `A`의 *원소*를 인수로 넣었다.
두 경우 모두 함수를 적용하지만 어떤 것을 넣어야 하는지는 함수의 타입에 따라 정해진다.

```savedLean
example
    (A : Type) (P : A → Prop) (a : A) :
    (∀ x : A, P x) → P a := by
  intro h
  exact h a
```

`P a`는 술어에 원소를 넣어 얻은 명제이고, `h a`는 그 명제가 성립한다는 증명이다.
따라서 `P a`가 목표일 때 `exact h a`로 그 증명을 제시한다.

전칭명제를 증명할 때의 `intro x`는 임의의 인수 `x`를 받아 그 경우를 증명하는 단계이다.
임의의 `x`를 받아 `P x`를 증명하는 논증 전체를 작성하면 모든 원소에 관한 증명을 얻는다.
예를 들어 앞의 “모든 원소는 자기 자신과 같다”는 증명도 함수식으로 적을 수 있다.

```savedLean
example (A : Type) : ∀ x : A, x = x :=
  fun x => by rfl
```

`fun x => ...`는 원소 `x`를 받고, `by rfl`은 그 원소에 관한 `x = x`의 증명을 만든다.
어느 원소를 넣어도 이 논증을 사용할 수 있으므로 전칭명제의 증명이 된다.

*문제 9* 두 원소에 관한 술어 `R : A → A → Prop`를 생각하자.
모든 원소 `x`, `y`에서 `R x y`가 성립한다는 사실을 주어진 원소 `a`, `b`에서 사용하라.
첫 증명에서는 `apply`를 사용하고, 둘째 증명에서는 `exact h a b`처럼 인수를 직접 넣으라.

```savedLean -keep
theorem exercise_relation_specialization_apply
    (A : Type) (R : A → A → Prop) (a b : A) :
    (∀ x : A, ∀ y : A, R x y) → R a b := by
  sorry

theorem exercise_relation_specialization
    (A : Type) (R : A → A → Prop) (a b : A) :
    (∀ x : A, ∀ y : A, R x y) → R a b := by
  sorry
```

:::solution
전칭명제의 증명에 첫 원소 `a`를 넣으면 `∀ y, R a y`의 증명을 얻는다.
여기에 두 번째 원소 `b`를 넣으면 목표의 증명이 된다.

```tryLean -keep
example (A : Type) (R : A → A → Prop) (a b : A) :
    (∀ x : A, ∀ y : A, R x y) → R a b := by
  intro h
  exact h a b
```
:::

## 전칭명제와 함의의 결합
%%%
tag := "proofs-successive-application"
file := "successive-application"
%%%

전칭명제 안에 함의가 들어갈 수도 있다.
“모든 원소 $`x`에 대하여 $`P(x)`이면 $`Q(x)`이다”를 Lean으로 쓰면 `∀ x : A, P x → Q x`이다.
다음 장에서 다룰 집합의 포함 관계도 이런 형태로 표현한다.
이 사실을 알고 있고 특정한 원소 $`a`에서 $`P(a)`도 성립한다면,
먼저 전칭명제를 $`a`에서 사용하여 $`P(a) \Rightarrow Q(a)`를 얻고,
여기에 전제 $`P(a)`를 사용하여 $`Q(a)`를 얻는다.

우선 `apply`와 `exact`로 이 추론을 적어 보자.

```savedLean
example (A : Type) (P Q : A → Prop)
    (h : ∀ x : A, P x → Q x)
    (a : A)
    (hPa : P a) :
    Q a := by
  apply h
  exact hPa
```

목표가 `Q a`이므로 `apply h`는 원소를 `a`로 정하고,
그 원소에서 필요한 전제 `P a`를 새 목표로 삼는다.
이어서 `exact hPa`로 그 전제를 확인하면 증명이 끝난다.

이제 원소를 넣는 단계와 증명을 넣는 단계를 따로 적어 보자.
`h a`는 `P a → Q a`의 증명이므로 여기에 `hAtA`라는 이름을 붙일 수 있으며,
그 증명에 `hPa`를 넣은 `hAtA hPa`는 목표 `Q a`의 증명이 된다.

```savedLean
example (A : Type) (P Q : A → Prop)
    (h : ∀ x : A, P x → Q x)
    (a : A)
    (hPa : P a) :
    Q a := by
  have hAtA : P a → Q a := by
    exact h a

  exact hAtA hPa
```

`hAtA`를 따로 두지 않고 두 인수를 차례로 넣으면 `h a hPa`로 쓸 수 있다.
앞에서 두 인수의 함수를 읽은 것처럼 이 식은 `(h a) hPa`로 읽는다.
첫 번째 인수 `a`는 원소이고, 두 번째 인수 `hPa`는 그 원소에서 전제가 성립한다는 증명이다.

```savedLean
example (A : Type) (P Q : A → Prop)
    (h : ∀ x : A, P x → Q x)
    (a : A)
    (hPa : P a) :
    Q a := by
  exact h a hPa
```

세 증명은 같은 추론을 적은 것이며,
마지막의 `h a hPa`에도 원소를 대입하는 단계와 전제의 증명을 넣는 단계가 모두 들어 있다.

*보기* 자연수에서 정의된 함수 $`f`가 $`a<b`일 때마다 $`f(a)<f(b)`를 만족한다고 하자.
그러면 $`f(3)+2<f(5)+2`이다.

*풀이* 먼저 $`3<5`를 이 함수의 조건에 사용하여 $`f(3)<f(5)`를 얻는다.
여기에 앞에서 증명한 `add_two_preserves_lt`를 적용하면 원하는 부등식이 된다.
Lean에서는 결론에서 거꾸로 필요한 전제를 확인하자.

```savedLean
example (f : Nat → Nat)
    (hf : ∀ a b, a < b → f a < f b) :
    f 3 + 2 < f 5 + 2 := by
  apply add_two_preserves_lt
  apply hf 3 5
  exact comparisonProof
```

첫 줄은 앞의 정리를 $`f(3)`과 $`f(5)`에 적용하여 목표를 `f 3 < f 5`로 바꾼다.
둘째 줄에서는 함수의 조건 `hf`를 $`3`, $`5`에서 사용하므로 `3 < 5`가 남는다.
이는 첫 절의 `comparisonProof`로 이미 증명한 사실이다.
함수 $`f`의 구체적인 계산식을 몰라도 주어진 조건만으로 이 부등식을 얻을 수 있다.

## 존재명제
%%%
tag := "logic-existence"
%%%

방정식 $`n^2=16`의 자연수 해가 존재함을 보이려면 $`n=4`를 제시하고 $`4^2=16`임을 확인하면 된다.
이처럼 조건을 만족하는 원소가 하나 이상 있다는 명제를 *존재명제*라고 한다.
술어 `P : A → Prop`에 대하여 `∃ x : A, P x`로 쓰며 `∃`는 `\exists`로 입력한다.

목표가 존재명제일 때 `exists 4`를 쓰면 원소를 $`4`로 정하고 그 원소의 조건을 새 목표로 삼는다.

```savedLean
theorem square_sixteen_has_solution :
    ∃ n : Nat, solvesSquare 16 n := by
  exists 4
```

이 예제에서 남는 조건은 `4 * 4 = 16`이며 계산으로 확인되므로 `exists 4`가 증명까지 마친다.
일반적인 조건에서는 원소를 택한 뒤 남은 목표를 계속 증명해야 한다.

반대로 해가 존재한다는 사실을 알고 있다면 그 해와 함께 주어진 등식을 사용할 수 있다.
전술 `unpack h with ⟨n, hn⟩`는 존재명제의 증명 `h`에서 원소를 `n`으로,
그 원소가 조건을 만족한다는 증명을 `hn`으로 꺼낸다.
논리곱에서 꺼낸 두 항목은 모두 증명이었지만, 이번에는 원소와 그 원소의 성질에 대한 증명을 얻는다.

```savedLean
theorem square_solution_gives_square (a : Nat)
    (h : ∃ n : Nat, solvesSquare a n) :
    ∃ n : Nat, n * n = a := by
  unpack h with ⟨n, hn⟩
  exists n
```

`hn`은 `solvesSquare a n`, 곧 `n * n = a`의 증명이므로 같은 원소 `n`을 제시하면 된다.
이때 `n`은 임의로 고른 원소가 아니라 가정 `h`가 존재를 보장하는 해이다.
조건이 `P n ∧ Q n`처럼 두 사실을 담으면 원소를 꺼낸 뒤 그 조건을 다시 분해한다.
`rcases h with ⟨n, ⟨hP, hQ⟩⟩`로 두 단계를 함께 지정할 수도 있다.
바깥 꺾쇠괄호는 원소와 조건을, 안쪽 꺾쇠괄호는 그 조건의 두 증명을 꺼낸다.

## 양화사의 순서
%%%
tag := "logic-quantifier-order"
%%%

모든 자연수 $`n`에 대해 $`n`보다 큰 자연수는 존재한다.
이때 고르는 수는 $`n`에 따라 달라도 되므로 $`m=n+1`로 정하면 된다.
이를 “모든 자연수보다 큰 자연수가 하나 존재한다”는 주장과 구별해야 한다.
후자에서는 하나의 $`m`을 먼저 고른 뒤 어느 $`n`에도 같은 $`m`을 사용해야 한다.

```savedLean
theorem each_nat_has_larger_nat :
    ∀ n : Nat, ∃ m : Nat, n < m := by
  intro n
  exists n + 1
  apply Nat.lt_succ_self
```

`intro n`이 먼저 나오므로 `exists n + 1`에서 방금 받은 원소를 사용할 수 있다.
마지막 정리 `Nat.lt_succ_self`는 모든 자연수에 대하여 `n < n + 1`임을 보장한다.
양화사의 순서는 이처럼 어떤 원소를 고를 때 앞에서 받은 원소를 사용할 수 있는지도 정한다.

*문제 10* (같은 원소의 사용)

어떤 원소 $`x`가 모든 $`y`에 대하여 $`R(x,y)`를 만족한다고 하자.
그러면 모든 $`y`에 대하여 $`R(x,y)`를 만족하는 원소가 존재함을 증명하라.

```savedLean -keep
theorem exercise_exists_forall_swap (A B : Type)
    (R : A → B → Prop)
    (h : ∃ x : A, ∀ y : B, R x y) :
    ∀ y : B, ∃ x : A, R x y := by
  sorry
```

## 양화사의 부정
%%%
tag := "logic-quantifier-negation"
%%%

방정식의 해가 존재하지 않는다는 것은 모든 수가 그 방정식의 해가 아니라는 뜻이다.
술어 $`P`에 대해서도 $`\neg\exists x, P(x)`는 $`\forall x,\neg P(x)`와 동치이다.
원소의 범위가 빈 타입이어도 두 주장은 모두 성립한다.

```savedLean
theorem not_exists_iff (A : Type) (P : A → Prop) :
    (¬ ∃ x : A, P x) ↔ (∀ x : A, ¬ P x) := by
  constructor
  · intro h x hx
    apply h
    exists x

  · intro h hExists
    unpack hExists with ⟨x, hx⟩
    apply h x
    exact hx
```

정방향에서는 임의의 원소 `x`에서 `P x`를 가정하여 존재명제를 만들고 `h`와 모순을 얻는다.
역방향에서는 존재명제에서 꺼낸 원소에 `h`를 사용하면 그 원소의 조건과 부정을 함께 얻는다.
양쪽 모두 존재명제와 부정의 기본 규칙만 사용했다.

이번에는 “모든 수가 양수이다”라는 주장을 부정해 보자.
$`0`처럼 양수가 아닌 수 하나를 제시하면 이 주장이 거짓임을 알 수 있다.
일반적으로도 반례가 있으면 전칭명제를 부정할 수 있다.
고전논리에서는 그 역방향도 성립하여 전칭명제가 성립하지 않으면 반례가 존재한다.

$$`\neg\bigl(\forall x, P(x)\bigr)\ \longleftrightarrow\ \exists x,\neg P(x).`

정방향을 귀류법으로 증명하자. 반례가 없다고 가정하면 각 원소 $`x`에서 $`\neg P(x)`일 수 없다.
이중 부정 제거로 $`P(x)`이므로 모든 원소에서 $`P`가 성립하여 처음 가정과 모순이다.

```savedLean
theorem not_forall_iff (A : Type) (P : A → Prop) :
    (¬ ∀ x : A, P x) ↔ (∃ x : A, ¬ P x) := by
  constructor
  · intro h
    by_contra hNoCounterexample
    apply h
    intro x
    by_contra hnotPx
    apply hNoCounterexample
    exists x

  · intro h hAll
    unpack h with ⟨x, hnotPx⟩
    apply hnotPx
    exact hAll x
```

처음의 `by_contra`는 반례가 존재하지 않는다고 가정하고 `False`를 목표로 삼는다.
`apply h` 뒤에는 `∀ x, P x`를 보여야 하며, `intro x` 뒤의 목표는 `P x`이다.
둘째 `by_contra`로 `¬ P x`를 가정하면 이 원소 자체가 반례이므로 `hNoCounterexample`과 모순이다.

`¬ (∀ x, P x)`는 모든 원소에서 `P`가 성립한다는 주장의 부정이다.
이를 `∀ x, ¬ P x`와 혼동하지 않도록 하라. 양수가 아닌 자연수는 존재하지만 모든 자연수가 양수가 아닌 것은 아니다.

*보기* 모든 원소가 $`P(x)\Rightarrow Q(x)`를 만족하지는 않는다고 하자.
`not_forall_iff`에 술어 `fun x => P x → Q x`를 넣으면 그 함의가 성립하지 않는 원소의 존재를 얻는다.
그 원소에서 `not_imp_iff`를 사용하면 $`P(x)`와 $`\neg Q(x)`를 얻는다.

```savedLean
theorem exists_counterexample (A : Type) (P Q : A → Prop)
    (h : ¬ ∀ x, P x → Q x) :
    ∃ x, P x ∧ ¬ Q x := by
  have hIff : (¬ ∀ x : A, P x → Q x) ↔
      (∃ x : A, ¬ (P x → Q x)) :=
    not_forall_iff A (fun x => P x → Q x)
  have hExists : ∃ x, ¬ (P x → Q x) := by
    apply hIff.mp
    exact h

  unpack hExists with ⟨x, hx⟩
  exists x
  apply (not_imp_iff (P x) (Q x)).mp
  exact hx
```

## 연습문제
%%%
tag := "proofs-exercises"
file := "exercises"
%%%

전칭명제와 함의를 사용하여 여러 단계의 추론을 연결하라.
다음 코드의 `sorry`를 증명으로 바꾸어 완성하라.

*문제 11* 모든 원소 $`x`에서 $`P(x)\Rightarrow Q(x)`가 성립한다고 하자.
또한 모든 원소에서 $`P(x)`가 성립하면 모든 원소에서 $`Q(x)`도 성립함을 보이라.

```savedLean -keep
theorem exercise_forall_implication
    (A : Type) (P Q : A → Prop) :
    (∀ x : A, P x → Q x) →
    (∀ x : A, P x) → ∀ x : A, Q x := by
  sorry
```

:::solution
두 가정을 받은 뒤 임의의 원소 `a`에서 `Q a`를 보이자.
첫 가정을 이 원소에서 사용하면 `P a`가 필요하며, 둘째 가정이 그 증명을 제공한다.

```tryLean -keep
example (A : Type) (P Q : A → Prop) :
    (∀ x : A, P x → Q x) →
    (∀ x : A, P x) → ∀ x : A, Q x := by
  intro hPQ hP
  intro a
  apply hPQ a
  exact hP a
```
:::

*문제 12* (대소 관계를 보존하는 함수)

자연수 함수 $`f`, $`g`가 각각 $`a<b`이면 $`f(a)<f(b)`, $`g(a)<g(b)`를 만족한다고 하자.

(1) $`a<b`이면 $`g(f(a))<g(f(b))`임을 증명하라.

(2) 첫 결과와 `comparisonProof`를 사용하여 $`g(f(3))<g(f(5))`를 보이라.

```savedLean -keep
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
```

*문제 13* (함수값의 범위)

모든 자연수 $`n`에 대하여 $`f(n)<g(n)`이고 $`g(n)<n+10`이라고 하자.
$`f(3)<13`임을 증명하라.
부등식의 추이성은 `Nat.lt_trans`로 사용할 수 있으며,
이 정리는 $`a<b`와 $`b<c`의 증명을 받아 $`a<c`의 증명을 돌려준다.

```savedLean -keep
theorem exercise_function_bound (f g : Nat → Nat)
    (hfg : ∀ n, f n < g n)
    (hg : ∀ n, g n < n + 10) :
    f 3 < 13 := by
  sorry
```

*문제 14* (반복하여 유지되는 조건)

함수 $`f:A\to A`가 조건 $`P`를 유지한다고 하자.
즉 $`P(x)`이면 $`P(f(x))`이다.

(1) $`P(x)`이면 $`P(f(f(x)))`임을 증명하라.

(2) 첫 결과를 사용하여 $`f`를 네 번 적용한 뒤에도 $`P`가 성립함을 보이라.

```savedLean -keep
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
```

*문제 15* (두 인수의 역할)

두 원소에 관한 조건 `R`와 함수 `f`가 주어져 있다.
`R x y`에서 `R y (f x)`를 얻을 수 있다고 하자.

(1) 이 규칙을 두 번 사용하여 `R a b`에서 `R (f a) (f b)`를 얻으라.

(2) 첫 결과를 사용하여 두 원소에 `f`를 각각 두 번 적용한 뒤에도 `R`이 성립함을 보이라.

```savedLean -keep
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
```


*문제 16* (양화사의 순서와 반례)

모든 자연수 $`n`에 대해 $`n<m`인 자연수 $`m`이 존재함은 앞에서 보였다.
정리 `Nat.lt_irrefl m`은 `¬ m < m`의 증명이다.
이를 사용하여 모든 자연수보다 큰 자연수 하나가 존재하지는 않음을 증명하라.

```savedLean -keep
theorem exercise_no_largest_nat :
    ¬ ∃ m : Nat, ∀ n : Nat, n < m := by
  sorry
```

# 등식
%%%
tag := "logic-equality"
%%%

{anchor "logic-predicate-comparison"}[]두 식이 같은 대상을 나타내면 그 대상에 관한 조건에서도 서로 바꾸어 사용할 수 있다.
가령 $`a=b`이고 $`a<5`이면 $`b<5`이다.

## 등식의 사용
%%%
tag := "logic-equality-substitution"
%%%

전술 `rw [h]`는 등식 `h`의 왼쪽을 오른쪽으로 바꾼다.
반대 방향으로 바꿀 때는 `rw [← h]`로 쓰며 `←`는 `\l`로 입력한다.

```savedLean
example (a b : Nat)
    (h : a = b)
    (ha : a < 5) :
    b < 5 := by
  rw [← h]
  exact ha
```

`rw [← h]` 뒤에는 목표가 `a < 5`이므로 가정 `ha`를 쓸 수 있다.
가정 안에서 바꿀 때는 `rw [h] at ha`처럼 적용할 위치를 지정한다.
`symm`은 등식인 목표의 양변을 바꾸므로 `b = a`를 보일 때 `a = b`를 새 목표로 삼을 수 있다.

```savedLean
example (A : Type) (a b : A)
    (h : a = b) :
    b = a := by
  symm
  exact h
```

{anchor "logic-applying-functions"}[]같은 두 대상에 같은 함수를 적용하면 그 함수값도 같다.
가령 $`a=b`이면 양변에 $`1`을 더하여 $`a+1=b+1`을 얻는다.
`apply_fun`은 등식의 양변에 지정한 함수를 적용하는 전술이다.

```savedLean
example (a b : Nat)
    (h : a = b) :
    a + 1 = b + 1 := by
  apply_fun (fun x => x + 1) at h
  exact h
```

`fun x => x + 1`은 수에 $`1`을 더하는 함수이다.
이 함수를 등식 `h`의 양변에 적용하면 `h : a + 1 = b + 1`이 되어 목표의 증명으로 사용할 수 있다.
다른 함수에 대해서도 같은 방식으로 함수값의 등식을 얻는다.

## 모든 술어에 대한 양화
%%%
tag := "logic-higher-order-quantification"
%%%

등식에서의 치환은 어떤 조건에서도 사용할 수 있다.
이 성질을 하나의 명제로 표현하려면 원소에 따라 조건을 정하는 술어 자체에 대해 양화해야 한다.

어떤 조건을 $`3`이 만족한다면 그 조건을 만족하는 자연수가 존재한다.
양수라는 조건이면 $`3`이 양수인 자연수의 예이고, 홀수라는 조건이면 $`3`이 홀수인 자연수의 예이다.
어떤 술어를 사용하든 같은 추론이 성립하므로 술어 자체에 대해 다음과 같이 양화할 수 있다.

```savedLean
example : ∀ P : Nat → Prop, P 3 → ∃ n : Nat, P n := by
  intro P hThree
  exists 3
```

첫 `intro`에서 받는 `P`는 자연수가 아니라 `Nat → Prop` 타입의 술어이다.
`hThree : P 3`을 알고 있으므로 `exists 3`으로 조건에 맞는 원소와 그 증명을 제시한다.
이처럼 원소에 대한 함수나 술어 자체도 양화의 대상으로 삼는 논리를 *고차 논리*라고 한다.

앞의 등식 치환도 모든 술어에 대한 명제로 표현할 수 있다. 이를 등식의 *라이프니츠 법칙*이라고 한다.
즉 $`x=y`이면 어떤 조건 $`F`에 대해서도 $`F(x)\leftrightarrow F(y)`이다.

```savedLean
theorem equality_preserves_predicates (A : Type)
    (x y : A)
    (h : x = y) :
    ∀ F : A → Prop, F x ↔ F y := by
  intro F
  rw [h]
```

여기서 `∀ F`는 모든 원소가 아니라 모든 술어에 관한 양화이다.
역방향도 성립한다. 모든 조건에서 두 원소가 구별되지 않는다고 하면,
특히 “$`x`와 같다”는 조건 `fun z => x = z`를 사용할 수 있다.
이 조건은 $`x`에서 성립하므로 $`y`에서도 성립하여 $`x=y`를 얻는다.
따라서 등식을 다음과 같이 특징지을 수 있다.

```savedLean
theorem equality_iff_all_predicates (A : Type) (x y : A) :
    x = y ↔ ∀ F : A → Prop, F x ↔ F y := by
  constructor
  · apply equality_preserves_predicates
  · intro h
    have hxy : x = x ↔ x = y :=
      h (fun z => x = z)
    apply hxy.mp
    rfl
```

역방향에서는 `h`에 “`x`와 같다”는 술어를 넣어 동치 `x = x ↔ x = y`를 얻고 그 증명에 `hxy`라는 이름을 붙였다.
`apply hxy.mp` 뒤에는 `x = x`만 보이면 되므로 `rfl`로 마친다.
여기서는 Lean의 등식을 그대로 사용하여 그 성질을 증명했다.

{anchor "sets-proposition-extensionality"}[]

## 술어의 외연성
%%%
tag := "logic-predicate-extensionality"
%%%

$`P(x)\land Q(x)`와 $`Q(x)\land P(x)`는 같은 원소들에서 성립하는 조건이다.
논리식을 다르게 적었더라도 모든 원소에서 두 조건이 동치이면 두 술어를 같다고 보는 원리가 *술어의 외연성*이다.
Lean에서는 다음 가정에서 술어의 등식 `P = Q`를 얻는다.

```
h : ∀ x, P x ↔ Q x
⊢ P = Q
```

술어는 원소를 명제로 보내는 함수이므로 먼저 원소 하나에서의 값을 비교한다.
전술 `funext x`는 이 등식을 임의의 원소 `x`에서 `P x = Q x`를 보이는 목표로 바꾼다.
이 단계에서 가정 `h x`의 명제는 `P x ↔ Q x`이므로 아직 목표와 형태가 다르다.

다음은 이 단계에서 멈춘 미완성 증명이다.
중간 사실 `hx`를 얻었지만 목표는 `P x = Q x`이므로 그 증명을 그대로 제시할 수는 없다.

```tryLean +error -keep
example (A : Type) (P Q : A → Prop)
    (h : ∀ x, P x ↔ Q x) :
    P = Q := by
  funext x
  have hx : P x ↔ Q x :=
    h x
```

두 명제의 동치에서 그 명제의 등식을 얻는 원리를 *명제의 외연성*이라고 한다.
Lean에서는 `apply propext`로 등식 `P x = Q x`를 동치 `P x ↔ Q x`를 보이는 목표로 바꾼다.

```savedLean
theorem predicate_ext (A : Type _) (P Q : A → Prop)
    (h : ∀ x, P x ↔ Q x) :
    P = Q := by
  funext x
  apply propext
  exact h x
```

두 단계로 남은 목표가 가정 `h x`와 같아졌으므로 `exact h x`로 증명을 마친다.
여기서 `Type _`의 `_`는 타입의 수준을 Lean이 추론하도록 둔 표시이며 증명에서는 앞의 `Type`과 같은 방식으로 사용한다.
이 외연성은 배중률과는 별개의 원리이며 고전논리를 사용하지 않아도 성립한다.
다음 장에서는 집합을 술어로 나타내고 이 원리로 집합의 같음을 증명한다.
일반적인 함수의 같음도 함수값을 비교하는 같은 방식으로 다룬다.

*문제 17* (같은 조건을 나타내는 술어)

술어 $`P`, $`Q`에 대하여 “$`P`이고 $`Q`이다”와 “$`Q`이고 $`P`이다”를 나타내는 두 술어가 같음을 증명하라.
앞의 `conjunction_comm`으로 원소마다 두 방향을 증명할 수 있다.

```savedLean -keep
theorem exercise_predicate_conjunction_comm (A : Type)
    (P Q : A → Prop) :
    (fun x => P x ∧ Q x) = (fun x => Q x ∧ P x) := by
  sorry
```

```savedLean -show
end ProofExamples
```
