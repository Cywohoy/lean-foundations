import AlgebraBook.Meta.Lean
import AlgebraBook.SetsFunctions
import AlgebraBook.Tactic.Arithmetic
import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open AlgebraBook

#doc (Manual) "수와 동치관계" =>

%%%
tag := "numbers-relations"
file := "numbers-relations"
%%%

자연수를 짝수와 홀수로 나누면 모든 자연수는 어느 한쪽에 속하며 두 쪽에 동시에 속하지 않는다.
이러한 수의 성질을 모든 자연수에 대해 증명하는 방법이 귀납법이다.
이 장에서는 귀납법으로 짝수와 홀수를 구별한 뒤, 정수의 배수와 나머지를 다룬다.
짝수와 홀수의 구별을 나머지가 같은 정수끼리 묶는 분류로 넓혀 보면 동치관계와 동치류에 이른다.
이 분류를 하나의 집합으로 만들고 그 위에 함수를 정의하는 데까지 나아가자.

{anchor "mathematical-preliminaries"}[]
```savedImport
import AlgebraBook.SetsFunctions
import AlgebraBook.Tactic.Arithmetic
```

```savedLean -show
open scoped Classical
```

```savedLean -show
namespace Ample
local infixr:90 (priority := high) " ∘ " => compose
```

# 자연수와 귀납법
%%%
tag := "preliminaries-induction"
file := "induction"
%%%

앞에서는 이미 알려진 덧셈의 성질을 `simp`로 사용했다.
이번에는 그 성질을 자연수의 정의에서 직접 증명하는 방법을 살펴보자.
Lean의 덧셈은 두 번째 인수가 $`0`인지 어떤 수의 다음 수인지에 따라 계산된다.
따라서 임의의 $`n`에 대한 $`0+n=n`을 증명할 때도 두 경우를 연결하는 논증이 필요하다.

모든 자연수는 $`0`에서 시작하여 $`1`을 반복해서 더하면 얻을 수 있다.
이 성질을 이용하여 모든 자연수에 관한 명제를 증명하는 방법이 수학적 귀납법이다.

*수학적 귀납법* 모든 자연수 $`n`에 대하여 $`P(n)`을 보이려면 다음 두 단계를 증명하면 된다.

1. $`P(0)`이 성립한다.
2. 임의의 자연수 $`n`에 대하여 $`P(n)`을 가정하면 $`P(n+1)`이 성립한다.

두 번째 단계에서 가정하는 $`P(n)`을 *귀납 가정*이라고 한다.
Lean에서는 `induction n`으로 $`0`의 경우와 $`n+1`의 경우를 나누며
두 번째 경우에 귀납 가정을 사용할 수 있다.
`Nat.succ n`은 자연수 `n` 다음의 수, 곧 `n + 1`을 뜻한다.

*보기* 모든 자연수 $`n`에 대하여 $`0+n=n`임을 귀납법으로 증명하자.
먼저 $`n=0`이면 $`0+0=0`이다.
$`0+n=n`을 가정하면 $`0+(n+1)=(0+n)+1=n+1`이므로 다음 자연수에서도 등식이 성립한다.
이때 첫 등식은 두 번째 인수에 따라 계산하는 Lean의 자연수 덧셈 정의를 사용한다.
`Nat.add_succ`는 이 계산을 등식 `a + Nat.succ b = Nat.succ (a + b)`로 나타낸 정리이다.

```savedLean
theorem zero_add_induction (n : Nat) : 0 + n = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Nat.add_succ]
      -- 목표: Nat.succ (0 + n) = Nat.succ n
      rw [ih]
```

`zero`는 $`n=0`인 경우이며 목표가 `0 + 0 = 0`이므로 `rfl`로 증명한다.
`succ n ih`에서는 귀납 가정에 `ih`라는 이름을 붙여 `ih : 0 + n = n`을 얻는다.
이때 목표 `0 + Nat.succ n = Nat.succ n`을 덧셈의 정의에 따라 펼치면
`Nat.succ (0 + n) = Nat.succ n`이 된다.
`rw [Nat.add_succ]`로 이 계산을 적용한 뒤 `rw [ih]`를 쓰면 양변이 같아져 증명이 끝난다.

*문제 1* 모든 자연수 $`n`에 대하여 $`1+n=n+1`임을 귀납법으로 증명하라.

```savedLean -keep
theorem exercise_one_add_induction
    (n : Nat) :
    1 + n = n + 1 := by
  sorry
```

# 짝수와 함수의 상
%%%
tag := "preliminaries-even-induction"
file := "parity"
%%%

*정의* $`n=2k`인 자연수 $`k`가 존재하면 자연수 $`n`을 *짝수*라고 한다.

```savedLean
def IsEvenNat : Nat → Prop :=
  fun n => ∃ k : Nat, n = 2 * k
```

`IsEvenNat n`은 앞 장의 `n ∈ evens`와 같은 조건이다.
이번에는 이 조건을 사용하여 짝수와 홀수가 같을 수 없음을 증명하자.

$`5`가 짝수가 아님을 증명하려면 모든 자연수 $`m`에 대하여 $`2m\ne5`임을 보이면 된다.
그런데 $`m`에 대한 귀납법을 곧바로 사용하면 다음 단계에서 어려움이 생긴다.
$`2(m+1)=5`를 가정하여 얻은 등식은 $`2m=3`이므로
귀납 가정 $`2m\ne5`를 이 등식에 적용할 수 없다.
오른쪽의 수가 $`2`만큼 줄어든 경우에도 귀납 가정을 사용할 수 있도록
$`2m\ne2n+1`을 모든 자연수 $`n`에 대하여 함께 증명하자.

*정리* 모든 자연수 $`m`, $`n`에 대하여 $`2m\ne2n+1`이다.

*증명* $`m`에 대한 귀납법을 사용한다.
$`m=0`이면 왼쪽은 $`0`이고 오른쪽은 양수이므로 같을 수 없다.

이제 모든 자연수 $`n`에 대하여 $`2m\ne2n+1`이라고 가정하고
$`2(m+1)=2n+1`에서 모순을 얻자.
$`n=0`이면 $`2m+2=1`이므로 양변에서 $`1`을 빼서 양수 $`2m+1`이 $`0`과 같다는 모순을 얻는다.
$`n=r+1`이면 양변에서 $`2`를 빼서 $`2m=2r+1`을 얻으며 이는 귀납 가정에 어긋난다.

Lean에서 `Nat.succ.inj`는 `Nat.succ a = Nat.succ b`의 증명으로부터 `a = b`의 증명을 얻는 정리이다.
즉 양변에 더한 $`1`을 지우는 단계에 해당하며 두 번 사용하면 $`2`를 지울 수 있다.
아래의 `cases n`은 자연수를 $`0`과 다음 자연수의 두 경우로 나눈다.
`induction`과 달리 경우를 나누기만 하므로 새로운 귀납 가정은 생기지 않는다.

```savedLean
theorem even_ne_odd (m : Nat) :
    ∀ n : Nat, 2 * m ≠ 2 * n + 1 := by
  induction m with
  | zero =>
      intro n h
      -- 0과 다음 자연수가 같다는 가정에서 모순을 얻는다.
      expand at h
      contradiction

  | succ m ih =>
      -- ih : ∀ n, 2 * m ≠ 2 * n + 1
      -- 목표: ∀ n, 2 * Nat.succ m ≠ 2 * n + 1
      intro n h
      -- h : 2 * Nat.succ m = 2 * n + 1, 목표: False
      -- 오른쪽의 n이 0인지 양수인지 나눈다.
      cases n with
      | zero =>
          expand at h

          -- 양변의 1을 소거하면 양수와 0이 같아진다.
          have hZero : Nat.succ (2 * m) = 0 := by
            exact Nat.succ.inj h

          contradiction

      | succ n =>
          expand at h

          -- 양변의 2를 소거하면 귀납 가정에 어긋나는 등식이 된다.
          apply ih n
          exact Nat.succ.inj (Nat.succ.inj h)
```

앞의 덧셈 예제에서 귀납 가정은 한 등식 `0 + n = n`이었다.
여기서는 오른쪽의 홀수가 달라져도 귀납 가정을 써야 하므로
모든 `n`에 관한 명제를 귀납 가정으로 남긴다.
`∀ n`을 목표에 둔 채 `induction m`을 쓰면
귀납 가정은 `ih : ∀ n, 2 * m ≠ 2 * n + 1`이 된다.
각 경우의 `intro n h`는 자연수 `n`을 택하고 두 식이 같다는 가정을 도입한다.
이 증명의 `expand at h`는 양변에 더한 $`1`을 `Nat.succ`로 드러낸다.

$`m=0`인 경우에는 `0 = Nat.succ (2 * n)`에서 모순을 얻는다.
$`m+1`의 경우에는 `cases n`으로 다시 나누며,
$`n=0`이면 `Nat.succ.inj h`로 `Nat.succ (2 * m) = 0`을 얻는다.
이처럼 $`0`과 다음 자연수가 같다는 가정은 `contradiction`으로 처리할 수 있다.
마지막 `succ n`에서는 수학적 증명의 $`r`에 `n`이라는 이름을 붙인다.
`apply ih n`으로 목표를 `2 * m = 2 * n + 1`로 바꾼 뒤
`Nat.succ.inj`를 두 번 사용하여 `h`에서 이 등식을 얻는다.

*보기* $`5`는 짝수가 아니다.
짝수라고 가정하면 $`5=2k`인 자연수 $`k`가 존재한다.
그런데 앞의 정리에 $`m=k`, $`n=2`를 넣으면 $`2k\ne5`이므로 모순이다.

```savedLean
theorem five_not_even : ¬ IsEvenNat 5 := by
  intro h
  unpack h with ⟨k, hk⟩

  -- 2k = 5는 짝수와 홀수가 같을 수 없다는 정리에 어긋난다.
  apply even_ne_odd k 2
  exact hk.symm
```

`h : IsEvenNat 5`는 정의에 따라 `∃ k : Nat, 5 = 2 * k`의 증명이므로
`unpack`으로 자연수 `k`와 등식 `hk`를 얻는다.
`apply even_ne_odd k 2`로 모순을 보이는 데 필요한 등식 `2 * k = 5`를 목표로 삼고,
`hk`의 양변을 바꾼 증명 `hk.symm`을 제시한다.

## 함수의 상과 짝수
%%%
tag := "preliminaries-double-image"
%%%

이제 앞에서 미뤄 둔 $`5 \notin \operatorname{double}(\mathbb{N})`을 보이자.
`double n = 2 * n`이므로 모든 함수값이 짝수임을 먼저 확인하면 된다.

```savedLean
theorem double_is_even (n : Nat) :
    IsEvenNat (double n) := by
  exact double_mem_evens n

theorem five_not_in_double_image :
    5 ∉ image double (whole Nat) := by
  intro hy
  rcases hy with ⟨n, hn, hEq⟩

  -- 5가 상에 속한다면 5가 짝수라는 결론을 얻는다.
  apply five_not_even
  have hEven : IsEvenNat (double n) := by
    exact double_is_even n

  rw [hEq] at hEven
  exact hEven
```

첫 증명은 앞 장의 `double_mem_evens n`을 사용한다.
`IsEvenNat (double n)`과 `double n ∈ evens`는 정의상 같은 명제이다.

두 번째 증명에서는 `hy : 5 ∈ image double (whole Nat)`를 가정하고 모순을 보인다.
가정의 명제를 펼치면 `∃ n, n ∈ whole Nat ∧ double n = 5`이므로
`rcases`로 자연수 `n`과 등식 `hEq : double n = 5`를 얻는다.
앞의 정리 `five_not_even`은 `IsEvenNat 5 → False`의 증명이므로
`apply five_not_even`을 쓰면 목표가 `IsEvenNat 5`로 바뀐다.

이를 보이기 위해 `double_is_even n`으로 `hEven : IsEvenNat (double n)`을 얻은 뒤
`rw [hEq] at hEven`으로 가정 안의 `double n`을 `5`로 바꾼다.
이제 `hEven`이 바로 `IsEvenNat 5`의 증명이므로 `exact hEven`으로 증명을 마친다.

*보기* `double : Nat → Nat`는 전사함수가 아니다.
전사라면 $`5`도 함수값으로 나타나야 하지만 방금 증명한 결과에 어긋난다.

```savedLean
theorem double_not_surjective : ¬ Surjective double := by
  intro hf
  unpack hf 5 with ⟨n, hn⟩
  apply five_not_in_double_image
  exists n
```

`hf 5`는 `double n = 5`인 자연수 `n`이 존재한다는 증명이다.
여기서 얻은 `n`을 상의 원소 조건에 사용하면 $`5`가 `double`의 상에 속하여 모순이 생긴다.
함수 절의 `doubleToEvens_bijective`와 비교하면 공역의 역할을 볼 수 있다.
함수값은 똑같이 $`2n`이어도 공역을 자연수 전체로 정하면 전사가 아니고,
짝수의 집합으로 정하면 전단사이다.

*문제 2* (짝수의 합)

(1) 짝수 두 개의 합은 짝수임을 정의로 증명하라.

(2) 첫 결과와 `double_is_even`을 사용하여 $`a`가 짝수이면
$`a+\operatorname{double}(7)`도 짝수임을 보이라.
분배법칙은 `Nat.mul_add`로 사용할 수 있다.

```savedLean -keep
theorem exercise_even_add (a b : Nat)
    (ha : IsEvenNat a)
    (hb : IsEvenNat b) :
    IsEvenNat (a + b) := by
  sorry

theorem exercise_even_add_double (a : Nat)
    (ha : IsEvenNat a) :
    IsEvenNat (a + double 7) := by
  sorry
```

*문제 3* (짝수의 배수)

$`a`가 짝수이면 모든 자연수 $`b`에 대하여 $`ab`도 짝수임을 증명하라.
곱셈의 결합법칙 `Nat.mul_assoc`을 사용할 수 있다.
이 결과로 $`\operatorname{double}(3)\cdot b`가 짝수임을 보이라.

```savedLean -keep
theorem exercise_even_mul (a b : Nat)
    (ha : IsEvenNat a) :
    IsEvenNat (a * b) := by
  sorry

theorem exercise_double_mul_even (b : Nat) :
    IsEvenNat (double 3 * b) := by
  sorry
```

# 정수와 나누어떨어짐
%%%
tag := "preliminaries-divisibility"
file := "divisibility"
%%%

이제 수의 범위를 정수로 넓혀 보자.
정수의 집합은 $`\mathbb{Z}`로 쓰며 Lean에서는 `Int`로 나타낸다.
정수끼리는 작은 수에서 큰 수를 빼도 그 결과를 정수로 나타낼 수 있다.
앞에서 사용한 배수의 개념을 임의의 정수로 넓히고, 배수들의 합도 배수가 됨을 증명하자.
이 과정에서 여러 등식을 이어 쓰는 방법을 익힌다.

## 나누어떨어짐
%%%
tag := "preliminaries-defining-divisibility"
%%%

짝수의 정의에서는 $`2`의 배수라는 조건을 사용했다.
이제 임의의 정수의 배수를 나타내는 관계를 정의하자.

*정의* 정수 $`a`, $`b`에 대하여 $`b = ak`인 정수 $`k`가 존재하면
$`a`가 $`b`를 *나눈다*고 하며 $`a \mid b`로 나타낸다.

```savedLean
def Divides : Int → Int → Prop :=
  fun a b => ∃ k : Int, b = a * k
local infix:50 (priority := high) " ∣ " => Divides
```

기호 `∣`는 `Divides`에 연결했으며 `\mid`로 입력한다.
`a ∣ b`를 보이려면 `b = a * k`를 만족하는 정수 `k`를 제시하면 된다.
이 정의는 $`a=0`인 경우도 포함한다. 이때 $`0\mid b`이면 $`b=0\cdot k=0`이다.
정수의 짝수도 이 관계로 표현할 수 있다. 정수 $`a`가 어떤 정수의 두 배라는 조건은
`2 ∣ a`이며, 이때는 음의 정수도 포함한다.

*보기* $`54=6\cdot9`이므로 $`6 \mid 54`이다.

```savedLean
example :
    6 ∣ 54 := by
  exists 9
```

*정리* 모든 정수 $`a`에 대하여 $`a \mid a`이다.

*증명* $`a=a\cdot1`이므로 정수 $`1`을 택하면 된다.
Lean에서는 이 등식을 정수 곱셈의 법칙 `Int.mul_one`으로 확인한다.

```savedLean
theorem divides_refl (a : Int) : a ∣ a := by
  exists 1
  rw [Int.mul_one]
```

여기서는 `a : Int`이므로 곱셈에 쓰는 `1`도 정수이다.
`exists 1`을 쓰면 목표가 `a = a * 1`이 되며
`rw [Int.mul_one]`으로 오른쪽을 `a`로 바꾸면 증명이 끝난다.

{anchor "preliminaries-simp"}[]{ref "proofs-simp"}[앞에서 배운 `simp`]는 정수에서도
`Int.mul_one`, `Int.add_zero`, `Int.zero_mul` 같은 기본 법칙을 사용하여 식을 정리한다.

*문제 4* 모든 정수 $`a`에 대하여 $`a\mid0`임을 증명하라.

```savedLean -keep
theorem exercise_divides_zero (a : Int) : a ∣ 0 := by
  sorry
```

## 배수의 합과 등식의 계산
%%%
tag := "preliminaries-calc"
%%%

{anchor "preliminaries-divisibility-properties"}[]*정리* $`a \mid b`이고 $`a \mid c`이면 $`a \mid b+c`이다.

*증명* 가정에 따라 $`b=ak`, $`c=al`인 정수 $`k`, $`l`을 택하면
$`b+c=ak+al=a(k+l)`이므로 곱하는 정수로 $`k+l`을 사용할 수 있다.

이처럼 등식을 차례로 이어 쓸 때는 `calc`를 사용한다.
각 줄의 `:=` 왼쪽에 등식을 적고 오른쪽에 그 등식의 증명을 적으면,
등식의 추이성에 따라 처음 식과 마지막 식이 같다는 결론을 얻는다.
마지막 등식의 분배법칙은 `Int.mul_add`로 사용한다.

```savedLean
theorem divides_add (a b c : Int)
    (hab : a ∣ b)
    (hac : a ∣ c) :
    a ∣ b + c := by
  unpack hab with ⟨k, hk⟩
  unpack hac with ⟨l, hl⟩

  -- 각 배수의 계수를 더하여 합의 계수를 만든다.
  exists (k + l)
  calc
    b + c = a * k + a * l := by rw [hk, hl]
    _ = a * (k + l) := by rw [Int.mul_add]
```

`unpack`으로 두 가정에서 `hk : b = a * k`와 `hl : c = a * l`을 얻는다.
`exists (k + l)`로 목표를 `b + c = a * (k + l)`로 바꾼 뒤
`calc`의 첫 줄에서 두 등식을 사용하고 둘째 줄에서 분배법칙으로 식을 묶는다.
둘째 줄의 `_`는 앞줄 오른쪽의 식 `a * k + a * l`을 이어받는다.

*정리* $`a \mid b`이고 $`b \mid c`이면 $`a \mid c`이다.

*증명* $`b=ak`, $`c=bl`인 정수 $`k`, $`l`을 택하면 $`c=(ak)l=a(kl)`이므로
곱하는 정수로 $`kl`을 사용한다.
이때 괄호를 옮기는 데 필요한 곱셈의 결합법칙은 Lean에서 `Int.mul_assoc`이다.

```savedLean
theorem divides_trans (a b c : Int)
    (hab : a ∣ b)
    (hbc : b ∣ c) :
    a ∣ c := by
  unpack hab with ⟨k, hk⟩
  unpack hbc with ⟨l, hl⟩

  -- 두 배수의 계수를 곱하여 c를 a의 배수로 나타낸다.
  exists (k * l)
  calc
    c = b * l := by exact hl
    _ = (a * k) * l := by rw [hk]
    _ = a * (k * l) := by rw [Int.mul_assoc]
```

*보기* 정수 $`a`가 $`6`의 배수이고 정수 $`b`가 $`10`의 배수이면 $`a+b`는 $`2`의 배수이다.

*풀이* $`2\mid6`과 $`6\mid a`에서 추이성으로 $`2\mid a`를 얻는다.
같은 방법으로 $`2\mid10`과 $`10\mid b`에서 $`2\mid b`를 얻으면,
앞의 덧셈에 관한 정리로 $`2\mid a+b`를 결론 내릴 수 있다.

```savedLean
example (a b : Int)
    (ha : 6 ∣ a)
    (hb : 10 ∣ b) :
    2 ∣ a + b := by
  have hTwoSix : 2 ∣ 6 := by exists 3
  have hTwoTen : 2 ∣ 10 := by exists 5
  have hTwoA : 2 ∣ a := by
    exact divides_trans 2 6 a hTwoSix ha

  have hTwoB : 2 ∣ b := by
    exact divides_trans 2 10 b hTwoTen hb

  exact divides_add 2 a b hTwoA hTwoB
```

수를 직접 택하는 부분은 $`6=2\cdot3`과 $`10=2\cdot5`를 확인하는 두 줄이다.
$`a`, $`b`가 어떤 수인지는 몰라도 `divides_trans`와 `divides_add`에
주어진 나누어떨어짐을 사용하면 합에 관한 결론을 얻는다.

*문제 5* (서로를 나누는 정수)

$`3\mid-3`과 $`-3\mid3`을 각각 증명하라.
이어서 $`3\ne-3`을 확인하여 정수에서는 $`a\mid b`이고 $`b\mid a`여도
$`a=b`를 결론지을 수 없음을 보이라.

```savedLean -keep
theorem exercise_divisibility_sign :
    (3 ∣ -3) ∧ ((-3) ∣ 3) := by
  sorry

theorem exercise_three_ne_negative_three :
    (3 : Int) ≠ -3 := by
  sorry
```

# 나머지와 합동
%%%
tag := "preliminaries-congruence"
file := "congruence"
%%%

$`23=3\cdot7+2`이고 $`-5=(-1)\cdot7+2`이므로 두 정수는 $`7`로 나누었을 때 같은 나머지를 갖는다.
두 등식을 빼면 $`23-(-5)=(3-(-1))\cdot7`이므로 두 정수의 차이는 $`7`의 배수이다.
이처럼 같은 나머지를 갖는 정수들을 차이가 주어진 정수의 배수라는 조건으로 묶어 보자.

Lean에서는 자연수와 정수의 몫을 `a / n`, 나머지를 `a % n`으로 쓴다.
정수에서 $`n>0`이면 $`a=nq+r`이고 $`0\leq r<n`인 몫 $`q`와 나머지 $`r`을 구한다.
위 두 수의 나머지를 Lean으로 확인하면 다음과 같다.

```savedLean
example :
    (23 : Int) / 7 = 3 ∧ (23 : Int) % 7 = 2 := by
  decide

example :
    (-5) / 7 = -1 ∧ (-5) % 7 = 2 := by
  decide
```

두 등식 모두 나머지가 $`2`라는 사실을 확인한다.
이러한 관계를 나눗셈의 계산 대신 배수의 존재로 표현하면 다음 정의를 얻는다.

*정의* 정수 $`n`을 고정하자.
$`a=b+nk`인 정수 $`k`가 존재하면 $`a`와 $`b`가 $`n`을 법으로 *합동*이라고 하며
$`a\equiv b\pmod n`으로 나타낸다.

이 조건은 앞에서 정의한 나누어떨어짐으로 $`n\mid(a-b)`라고 쓸 수 있다.
나머지를 비교할 때는 $`n>0`으로 두지만 배수에 의한 정의는 $`n=0`이나 음의 정수에도 적용할 수 있다.
아래의 세 성질도 법의 부호와 관계없이 성립한다.

```savedLean
def Congruent (n : Int) : Int → Int → Prop :=
  fun a b => ∃ k : Int, a = b + n * k
local notation:50 a " ≡ " b " [ZMOD " n "]" =>
  Congruent n a b
```

법 `n`을 정하면 `Congruent n`의 타입은 `Int → Int → Prop`이다.
앞의 술어가 원소 하나에 명제를 대응시켰던 것처럼,
여기서는 두 정수 `a`, `b`에 합동이라는 명제를 대응시킨다.
수학식 $`a\equiv b\pmod{n}`을 Lean에서는 `a ≡ b [ZMOD n]`으로 쓴다.
기호 `≡`는 `\==`로 입력한다.

*보기* $`23=2+7\cdot3`이므로 $`23\equiv2\pmod7`이다.
`exists 3`으로 정수를 제시하면 남은 등식은 계산으로 확인된다.

```savedLean
theorem preliminaries_congruent_twenty_three_two :
    23 ≡ 2 [ZMOD 7] := by
  exists 3
```

합동의 법 $`n`을 고정하면 다음 세 성질이 성립한다.

1. 모든 정수 $`a`에 대하여 $`a\equiv a\pmod n`이다.
2. $`a\equiv b\pmod n`이면 $`b\equiv a\pmod n`이다.
3. $`a\equiv b\pmod n`이고 $`b\equiv c\pmod n`이면 $`a\equiv c\pmod n`이다.

첫째 성질에서는 $`a=a+n\cdot0`이므로 정수 $`0`을 택한다.
둘째 성질에서는 $`a=b+nk`를 $`b=a+n(-k)`로 정리하여 $`-k`를 택한다.
셋째 성질에서는 $`a=b+nk`와 $`b=c+nl`을 이어서 $`a=c+n(l+k)`를 얻으므로 $`l+k`를 택하면 된다.

```savedLean
theorem congruent_refl (n a : Int) : a ≡ a [ZMOD n] := by
  exists 0
  rw [Int.mul_zero, Int.add_zero]

theorem congruent_symm (n a b : Int)
    (h : a ≡ b [ZMOD n]) :
    b ≡ a [ZMOD n] := by
  unpack h with ⟨k, hk⟩
  exists (-k)
  rw [hk, Int.mul_neg, Int.add_neg_cancel_right]

theorem congruent_trans (n a b c : Int)
    (hab : a ≡ b [ZMOD n])
    (hbc : b ≡ c [ZMOD n]) :
    a ≡ c [ZMOD n] := by
  unpack hab with ⟨k, hk⟩
  unpack hbc with ⟨l, hl⟩
  exists (l + k)
  rw [hk, hl, Int.mul_add, Int.add_assoc]
```

```savedLean -show
attribute [simp] congruent_refl
```

각 증명의 마지막 `rw`는 선택한 정수가 조건을 만족하는지 확인한다.
첫 증명에서는 `Int.mul_zero`로 $`n\cdot0`을 $`0`으로 바꾸고
`Int.add_zero`로 $`a+0`을 $`a`로 바꾼다.
둘째 증명에서는 `Int.mul_neg`로 $`n(-k)`를 $`-(nk)`로 바꾼 뒤
`Int.add_neg_cancel_right`로 $`(b+nk)-(nk)=b`를 확인한다.
마지막 증명에서는 앞에서 쓴 분배법칙으로 $`n(l+k)=nl+nk`를 얻고
덧셈의 결합법칙 `Int.add_assoc`로 괄호를 정리한다.

*보기* 이 절 첫머리의 두 정수 $`23`, $`-5`가 $`7`을 법으로 합동임을 보이자.
$`23\equiv2\pmod7`은 이미 증명했다.
$`-5=2+7\cdot(-1)`에서 $`-5\equiv2\pmod7`을 얻고 그 방향을 바꾸면
$`23\equiv2\equiv-5\pmod7`로 두 합동을 연결할 수 있다.

```savedLean
theorem congruent_neg_five_two : -5 ≡ 2 [ZMOD 7] := by
  exists (-1)

theorem congruent_twenty_three_neg_five :
    23 ≡ -5 [ZMOD 7] := by
  apply congruent_trans 7 23 2 (-5)
  · exact preliminaries_congruent_twenty_three_two
  · exact congruent_symm 7 (-5) 2 congruent_neg_five_two
```

추이성의 중간 정수는 $`2`이다.
두 번째 목표는 `2 ≡ -5 [ZMOD 7]`이므로 방금 얻은 합동에 대칭성을 사용한다.
따라서 두 정수의 차이를 새로 계산하지 않고 앞의 합동들을 이어서 결론을 얻는다.

{anchor "preliminaries-congruence-zero-and-one"}[]*문제 6* (법이 0이나 1인 합동)
합동의 정의는 법이 $`0`이나 $`1`인 경우도 포함한다.
(1) 법이 $`0`이면 합동과 등식이 같음을 보이라.
(2) 법이 $`1`이면 모든 정수가 서로 합동임을 보이라.

```savedLean -keep
theorem exercise_congruent_zero_iff (a b : Int) :
    a ≡ b [ZMOD 0] ↔ a = b := by
  sorry

theorem exercise_congruent_one (a b : Int) :
    a ≡ b [ZMOD 1] := by
  sorry
```

*문제 7* $`a\equiv b\pmod n`이면 $`a+t\equiv b+t\pmod n`임을 증명하라.

```savedLean -keep
theorem exercise_congruent_add_right
    (n a b t : Int)
    (h : a ≡ b [ZMOD n]) :
    a + t ≡ b + t [ZMOD n] := by
  sorry
```

# 산술 연습문제
%%%
tag := "preliminaries-exercises"
file := "exercises"
%%%

각 문제의 `sorry`를 증명으로 바꾸어 완성하라.

*문제 8* $`37\equiv2\pmod7`을 증명한 뒤,
이 결과와 본문의 `preliminaries_congruent_twenty_three_two`를 사용하여
$`37\equiv23\pmod7`을 증명하라.

```savedLean -keep
theorem exercise_congruent_thirty_seven_two :
    37 ≡ 2 [ZMOD 7] := by
  sorry

theorem exercise_congruent_thirty_seven_twenty_three :
    37 ≡ 23 [ZMOD 7] := by
  sorry
```

*문제 9* (법의 배수와 합동)

(1) $`a\equiv b\pmod{nd}`이면 $`a\equiv b\pmod n`임을 증명하라.

(2) $`20\equiv2\pmod6`을 직접 증명한 뒤 첫 결과를 사용하여
$`20\equiv2\pmod3`을 보이라.

```savedLean -keep
theorem exercise_congruent_divisor (n d a b : Int)
    (h : a ≡ b [ZMOD n * d]) :
    a ≡ b [ZMOD n] := by
  sorry

theorem exercise_twenty_mod_six : 20 ≡ 2 [ZMOD 6] := by
  sorry

theorem exercise_twenty_mod_three : 20 ≡ 2 [ZMOD 3] := by
  sorry
```

# 산술 계산의 자동화
%%%
tag := "preliminaries-arith"
file := "arithmetic-automation"
%%%

앞에서는 자연수에 관한 귀납법으로 $`5`가 짝수가 아님을 증명했다.
이후의 증명에서는 이런 산술 계산을 전술 `arith`로 확인할 수 있다.
`arith`는 자연수와 정수의 덧셈·뺄셈·상수배에 관한 등식과 부등식,
다항식의 등식, 등록된 곱셈·몫·나머지·나누어떨어짐의 성질을 사용한다.
증명의 가정에 있는 등식과 부등식도 함께 사용하여 목표를 확인한다.

*보기* 모든 정수 $`n`에 대하여 $`2n\ne5`이다.

```savedLean
example
    (n : Int) :
    2 * n ≠ 5 := by
  arith
```

`arith`는 $`2n=5`를 만족하는 정수가 없음을 확인하여 증명을 마친다.
앞에서 한 단계씩 사용한 덧셈의 법칙도 같은 전술로 처리할 수 있다.

```savedLean
example
    (a b : Int) :
    (a + 0) + b = b + a := by
  arith
```

이 증명에서도 $`a+0=a`와 $`a+b=b+a`라는 덧셈의 법칙을 사용한다.
전술의 사용 범위와 더 많은 예는 {ref "tactic-arith"}[부록의 산술식 계산]에 정리했다.

자연수 $`a`, $`m`에 대하여 $`a<m`이면 $`a\bmod m=a`이다.
이처럼 원래 목표를 얻을 수 있는 조건을 먼저 증명할 때는 `suffices`를 사용한다.
아래의 `suffices bound : a < m by arith`에서는
`by arith`가 `bound : a < m`으로부터 나머지의 등식을 얻는 연결 증명이다.
이 연결을 확인한 뒤에는 `a < m` 자체가 새 목표로 남는다.

```savedLean
example
    (a m : Nat)
    (h : a < m) :
    a % m = a := by
  suffices bound : a < m by arith
  exact h
```

이후에 남는 목표 `a < m`은 주어진 `h`로 증명한다.

```savedLean -show
end Ample
export_course_compat
```

{anchor "relations"}[]

```savedLean -show
open scoped Classical
```

```savedLean -show
namespace Ample
local infixr:90 (priority := high) " ∘ " => compose
```

```savedLean -show
local notation:50 a " ≡ " b " [ZMOD " n "]" => Congruent n a b
```

# 동치관계
%%%
tag := "preliminaries-equivalence-relations"
file := "equivalence-relations"
%%%

정수를 같은 나머지를 갖는 것끼리 묶으면 같은 무리에 속하는 두 정수는 서로 합동이다.
앞에서 정의한 `Congruent n`은 두 정수 `a`, `b`가 같은 무리에 속한다는 조건을 나타낸다.
이처럼 두 원소 사이의 조건을 나타내는 것을 *이항관계*라고 한다.
원소 하나에 관한 술어의 타입이 `A → Prop`이었던 것과 같이
두 원소에 관한 관계의 타입은 `A → A → Prop`이다.
수학에서 $`R(a,b)`나 $`a\mathrel{R}b`, $`a\sim b`로 쓰는 명제는 Lean에서 `R a b`로 쓴다.

```savedLean
def Relation (A : Type _) := A → A → Prop
```

등식도 합동에서 확인한 세 성질을 만족한다.
자기 자신과 같고, 등식의 양변을 바꾸어도 성립하며, 두 등식을 이어 쓸 수 있다.
이 세 성질을 공통으로 다루기 위해 다음 정의를 사용한다.

*정의* 관계 $`R`이 다음 세 성질을 만족하면 *동치관계*라고 한다.

1. 모든 원소 $`a`에 대하여 $`R(a,a)`이다. 이를 *반사성*이라고 한다.
2. $`R(a,b)`이면 $`R(b,a)`이다. 이를 *대칭성*이라고 한다.
3. $`R(a,b)`이고 $`R(b,c)`이면 $`R(a,c)`이다. 이를 *추이성*이라고 한다.

```savedLean
def IsEquivalence {A : Type _} : Relation A → Prop :=
  fun R =>
    (∀ a, R a a) ∧
    (∀ a b, R a b → R b a) ∧
    (∀ a b c, R a b → R b c → R a c)
```

```savedLean -show
namespace IsEquivalence

theorem refl
    {A : Type _} {R : Relation A} (hR : IsEquivalence R) (a : A) :
    R a a := hR.left a

theorem symm
    {A : Type _} {R : Relation A} (hR : IsEquivalence R) {a b : A}
    (hab : R a b) : R b a := hR.right.left a b hab

theorem trans
    {A : Type _} {R : Relation A} (hR : IsEquivalence R) {a b c : A}
    (hab : R a b) (hbc : R b c) : R a c := hR.right.right a b c hab hbc

end IsEquivalence
```

세 성질을 논리곱으로 묶었으므로 `hR : IsEquivalence R`이 주어지면
반사성·대칭성·추이성의 증명을 각각 꺼낼 수 있다.
교재에서는 이 세 조건을 이름으로 사용하는 정리도 준비했다.
`hR.refl a`는 `R a a`의 증명이고,
`hR.symm hab`는 `hab : R a b`에서 `R b a`를 얻는다.
또한 `hR.trans hab hbc`는 `hab : R a b`와 `hbc : R b c`에서 `R a c`를 얻는다.

*보기* 임의의 정수 $`n`에 대하여 합동 관계 `Congruent n`은 동치관계이다.

*풀이* 앞에서 증명한 `congruent_refl n`, `congruent_symm n`, `congruent_trans n`이
각각 반사성·대칭성·추이성의 증명이다.
논리곱으로 묶인 여러 조건을 한 번에 나누는 전술 `and_intros`를 사용하자.
이 전술은 나뉜 목표가 다시 논리곱이면 그 목표도 나눈다.

```savedLean
theorem congruent_equivalence (n : Int) :
    IsEquivalence (Congruent n) := by
  and_intros
  · exact congruent_refl n
  · exact congruent_symm n
  · exact congruent_trans n
```

*보기* 자연수에서 $`a\leq b`라는 관계는 동치관계가 아니다.
이 관계에서는 $`0\leq1`이 성립하지만 그 반대인 $`1\leq0`은 성립하지 않으므로 대칭성이 없다.

```savedLean
example :
    ¬ IsEquivalence (fun a b : Nat => a ≤ b) := by
  intro h
  have h01 : 0 ≤ 1 := by decide

  -- 대칭성이 있다면 0 ≤ 1에서 1 ≤ 0을 얻어야 한다.
  have h10 : 1 ≤ 0 := by
    exact h.symm h01

  have hNot10 : ¬ 1 ≤ 0 := by decide
  exact hNot10 h10
```

`h.symm h01`은 대칭성을 사용하여 $`0\leq1`에서 $`1\leq0`을 얻는다.
`decide`로 확인한 그 부정 `hNot10`에 `h10`을 적용하면 모순이다.

*문제 10* 함수 $`f:A\to B`에 대하여 $`f(x)=f(y)`로 정한 관계가 동치관계임을 증명하라.

```savedLean -keep
theorem exercise_equal_values_equivalence {A B : Type}
    (f : A → B) :
    IsEquivalence (fun x y : A => f x = f y) := by
  sorry
```

# 동치류와 대표원
%%%
tag := "preliminaries-equivalence-classes"
file := "equivalence-classes"
%%%

동치관계가 주어지면 한 원소와 동치인 원소들을 모을 수 있다.
가령 $`7`을 법으로 하는 합동에서는 $`2`와 합동인 정수들을 모아
$`\{\ldots,-12,-5,2,9,16,23,\ldots\}`이라는 집합을 얻는다.

*정의* 동치관계 $`R`에 대하여 $`R(x,a)`를 만족하는 원소 $`x`들의 집합
$`[a]_R=\{x\in A:R(x,a)\}`를 $`a`의 *동치류*라고 한다.

```savedLean
def equivalenceClass {A : Type _} (R : Relation A) (a : A) :
    Set A :=
  fun x => R x a
```

`equivalenceClass R a`의 원소 조건은 `R x a`이다.
이 집합을 정의할 때는 관계 `R`만 있으면 되고
아래에서 동치류의 성질을 증명할 때는 `IsEquivalence R`를 가정한다.

동치류 $`[a]_R`를 나타내기 위해 택한 원소 $`a`를 *대표원*이라고 한다.
앞의 정수 집합은 $`23`과 합동인 정수들을 모아도 얻으므로 $`2`와 $`23`을 모두 대표원으로 택할 수 있다.
이처럼 관계를 만족하는 두 원소가 같은 동치류를 나타냄을 일반적으로 증명하자.

*정리* $`R`이 동치관계이고 $`R(a,b)`이면 $`[a]_R=[b]_R`이다.

*증명* $`x\in[a]_R`이라고 하자. 그러면 $`R(x,a)`이므로
가정 $`R(a,b)`와 추이성에 따라 $`R(x,b)`, 곧 $`x\in[b]_R`를 얻는다.
거꾸로 $`x\in[b]_R`이라고 하자.
대칭성으로 $`R(b,a)`를 얻고 여기에 $`R(x,b)`와 추이성을 사용하면 $`R(x,a)`, 곧 $`x\in[a]_R`이다.
두 동치류의 원소 조건이 동치이므로 두 집합은 같다.

```savedLean
theorem equivalenceClass_eq {A : Type _} (R : Relation A)
    (hR : IsEquivalence R)
    (a b : A)
    (hab : R a b) :
    equivalenceClass R a = equivalenceClass R b := by
  ext x
  constructor
  · intro hx
    -- R(x,a)와 R(a,b)에 추이성을 사용한다.
    exact hR.trans hx hab

  · intro hx
    -- 대칭성으로 R(b,a)를 얻은 뒤 추이성을 사용한다.
    exact hR.trans hx (hR.symm hab)
```

`ext x`로 원소 조건의 동치를 목표로 삼은 뒤 `constructor`로 두 방향을 나눈다.
정방향에서는 `hR.trans`에 `R x a`와 `R a b`의 증명을 넣고
역방향에서는 `R x b`와 `hR.symm hab`로 얻은 `R b a`의 증명을 넣는다.

*보기* $`7`을 법으로 할 때 $`23`과 $`-5`의 동치류는 같다.
정수 절에서 $`23\equiv2\pmod7`과 $`-5\equiv2\pmod7`을 연결하여
$`23\equiv-5\pmod7`을 증명했다. 이 결과를 동치류의 등식에 사용하자.

```savedLean
example :
    equivalenceClass (Congruent 7) 23 =
    equivalenceClass (Congruent 7) (-5) := by
  apply equivalenceClass_eq (Congruent 7)
    (congruent_equivalence 7) 23 (-5)
  exact congruent_twenty_three_neg_five
```

`apply`에 합동 관계와 그 관계가 동치관계라는 증명을 주면
남은 목표는 `23 ≡ -5 [ZMOD 7]`이다.
이는 앞의 보기 `congruent_twenty_three_neg_five`에서 증명한 합동이므로
그 결과를 사용하면 두 동치류의 등식을 얻는다.

*문제 11* 모든 원소는 자신의 동치류에 속함을 증명하라.

```savedLean -keep
theorem exercise_mem_own_equivalenceClass {A : Type}
    (R : Relation A)
    (hR : IsEquivalence R)
    (a : A) :
    a ∈ equivalenceClass R a := by
  sorry
```

*문제 12* 동치관계 $`R`에 대하여 $`[a]_R=[b]_R`이면 $`R(a,b)`임을 증명하라.

```savedLean -keep
theorem exercise_relation_of_classes_equal {A : Type}
    (R : Relation A)
    (hR : IsEquivalence R)
    (a b : A)
    (h : equivalenceClass R a = equivalenceClass R b) :
    R a b := by
  sorry
```

*힌트* 반사성으로 $`a\in[a]_R`를 얻은 뒤 두 동치류가 같다는 가정을 사용하라.

# 몫집합과 몫타입
%%%
tag := "preliminaries-quotients"
file := "quotients"
%%%

앞에서 정수 하나에 대하여 그 정수와 합동인 정수들의 집합을 만들었다.
$`2`를 법으로 하면 $`0`의 동치류는 짝수들의 집합이고 $`1`의 동치류는 홀수들의 집합이다.
이번에는 이 두 집합을 각각 하나의 원소로 갖는 집합을 생각하자.
정수를 원소로 갖는 짝수 집합과 달리, 이 새 집합의 원소는 짝수 집합과 홀수 집합이다.

*정의* 동치관계 $`R`에 대한 동치류 전체의 집합
$`A/R=\{[a]_R:a\in A\}`를 *몫집합*이라고 한다.

$`[a]_R`는 $`A`의 부분집합이므로 $`A/R`는 집합들을 원소로 갖는다.
따라서 Lean에서 몫집합의 타입은 `Set (Set A)`이다.
집합 `S : Set A`가 이 몫집합에 속한다는 조건은
어떤 원소 `a : A`에 대하여 `S = equivalenceClass R a`라는 것이다.

```savedLean
def quotientSet {A : Type _} (R : Relation A) :
    Set (Set A) :=
  fun S => ∃ a : A, S = equivalenceClass R a
```

가령 `quotientSet (Congruent 2)`의 원소는 짝수 집합과 홀수 집합이다.
대표원으로 $`0`과 $`2`를 각각 택해도 같은 짝수 집합을 얻으므로
두 대표원은 이 몫집합의 같은 원소를 가리킨다.

모든 동치류는 정의에 따라 몫집합에 속한다.
`equivalenceClass R a`가 어떤 원소의 동치류임을 보이려면 그 원소로 `a`를 제시하면 된다.

```savedLean
theorem equivalenceClass_mem_quotientSet {A : Type _}
    (R : Relation A) (a : A) :
    equivalenceClass R a ∈ quotientSet R := by
  exists a
```

## 몫집합의 원소 타입
%%%
tag := "relations-quotient-elements"
file := "quotient-elements"
%%%

이제 몫집합을 함수의 정의역이나 공역으로 사용하려고 한다.
앞의 {ref "functions-elements"}[집합 위의 함수]에서와 같이
동치류인 집합과 그 집합이 몫집합에 속한다는 증명을 묶으면 원소 타입을 얻는다.
이 원소 타입을 *몫타입*이라고 한다.

```savedLean
def QuotientType {A : Type _}
    (R : Relation A) :=
  Elem (quotientSet R)
```

수학에서 몫집합을 $`A/R`로 쓰는 것에 맞추어 이 원소 타입도 `A / R`로 표기하겠다.
여기서 `A`는 관계를 정의한 원소들의 타입이며, `A / R`은 `QuotientType (A := A) R`를 뜻한다.
`/`는 자연수와 정수의 나눗셈에 쓰는 것과 같은 기호이다.

```savedLean -show
attribute [reducible] QuotientType
scoped notation:70 (name := quotientTypeNotation) α " / " R:71 =>
  QuotientType (A := α) R

open Lean PrettyPrinter Delaborator SubExpr in
/-- Display the quotient carrier and relation without unfolding its construction. -/
def Notation.delabQuotientType : Delab :=
    whenNotPPOption getPPExplicit <| whenPPOption getPPNotation do
  withOverApp 2 do
    let carrier ← withNaryArg 0 delab
    let relation ← withNaryArg 1 delab
    return ⟨mkNode ``quotientTypeNotation #[carrier.raw, mkAtom "/", relation.raw]⟩

attribute [scoped delab app.Ample.QuotientType] Notation.delabQuotientType
```

`q : A / R`이면 `q.val`은 동치류인 집합이고
`q.property`는 `q.val ∈ quotientSet R`의 증명이다.
`S ∈ quotientSet R`는 집합 `S`가 주어지면 쓸 수 있는 명제인 데 비해,
`A / R`의 원소를 만들려면 이 명제의 증명을 함께 제시해야 한다.

앞에서 증명한 `equivalenceClass_mem_quotientSet R a`를 사용하여
동치류를 몫타입의 원소로 만들자.

```savedLean
def classOf {A : Type _} (R : Relation A) (a : A) :
    A / R :=
  { val := equivalenceClass R a
    property := equivalenceClass_mem_quotientSet R a }
```

`classOf R a`의 값은 동치류인 집합 `equivalenceClass R a`이다.
따라서 서로 다른 대표원을 넣어도 같은 동치류를 얻으면 두 몫 원소는 같다.

앞으로 원소 `a`에 대응하는 몫 원소는 `⟦a⟧`로 표기하겠다.
다음 선언으로 이 표기를 `classOf`에 연결한다.

```savedLean
scoped notation:max (name := classOfNotation) "⟦" a "⟧" => classOf _ a
```

여기서 `_`는 몫타입에서 추론할 관계이다.
따라서 몫타입이 `A / R`로 정해져 있으면 `⟦a⟧`는 `classOf R a`를 뜻한다.
가령 `F : A / R → B`일 때 `F ⟦a⟧`는 이 몫 원소에서의 함수값이다.
몫타입을 명시해야 할 때는 `(⟦a⟧ : A / R)`로 적는다.
`⟦`와 `⟧`는 각각 `\[[`와 `\]]`로 입력한다.

```savedLean -show
open Lean PrettyPrinter Delaborator SubExpr in
/-- Display a quotient constructor using the ambient quotient type. -/
def Notation.delabClassOf : Delab :=
    whenNotPPOption getPPExplicit <| whenPPOption getPPNotation do
  withOverApp 3 do
    let value ← withNaryArg 2 delab
    return ⟨mkNode ``classOfNotation #[mkAtom "⟦", value.raw, mkAtom "⟧"]⟩

attribute [scoped delab app.Ample.classOf] Notation.delabClassOf
```

## 몫 원소의 등식
%%%
tag := "relations-quotient-equality"
file := "quotient-equality"
%%%

두 몫 원소가 같은지는 그 안에 담긴 집합을 비교하여 판단한다.
가령 몫타입 `A / R`의 두 원소 `⟦a⟧`와 `⟦b⟧`를 비교하려면
두 동치류 $`[a]_R`, $`[b]_R`가 같은지 확인하면 된다.
부분타입의 원소를 비교할 때는 값의 등식만 증명하면 되기 때문이다.

*정리* 동치관계 $`R`에 대한 몫타입 `A / R`에서 `⟦a⟧ = ⟦b⟧`일 필요충분조건은 $`R(a,b)`이다.

*증명* 두 몫 원소가 같으면 그 값인 동치류도 같다.
반사성에 따라 $`a\in[a]_R`이므로 $`a\in[b]_R`, 곧 $`R(a,b)`를 얻는다.
역방향에서는 앞에서 증명한 `equivalenceClass_eq`로 두 동치류의 등식을 얻고
부분타입의 원소도 같다고 결론 내린다.

```savedLean
theorem classOf_eq_iff {A : Type _} (R : Relation A)
    (hR : IsEquivalence R)
    (a b : A) :
    (⟦a⟧ : A / R) = ⟦b⟧ ↔ R a b := by
  constructor
  · intro h
    indisc at h with hSets
    have ha : a ∈ equivalenceClass R a := by
      exact hR.refl a

    rw [hSets] at ha
    exact ha

  · intro hab
    ext
    exact equivalenceClass_eq R hR a b hab
```

첫 방향의 `indisc`은 부분타입의 값인 두 집합의 등식 `hSets`를 얻는다.
그 등식으로 `ha`의 집합을 바꾸면 `a ∈ equivalenceClass R b`가 되므로
원하는 관계 `R a b`를 얻는다.
역방향의 `ext`도 부분타입의 값만 비교하며,
남은 집합의 등식에는 앞의 정리 `equivalenceClass_eq`를 사용한다.

*보기* 짝수 집합과 홀수 집합을 원소로 갖는 타입을 다음과 같이 정의하자.

```savedLean
def Parity := Int / Congruent 2
def parityClass (a : Int) : Parity :=
  ⟦a⟧
```

```savedLean -show
attribute [reducible] Parity
```

앞의 `classOf_eq_iff`를 적용하면
두 몫 원소가 같다는 조건을 두 정수가 합동이라는 조건으로 바꿀 수 있다.

```savedLean
theorem parityClass_eq_iff (a b : Int) :
    parityClass a = parityClass b ↔ a ≡ b [ZMOD 2] := by
  exact classOf_eq_iff (Congruent 2)
    (congruent_equivalence 2) a b
```

```savedLean -show
attribute [ample_compare] parityClass_eq_iff
```

이 비교도 `ext`와 `indisc`에 연결했다.
예를 들어 `parityClass 0 = parityClass 2`를 보일 때 `ext`를 사용하면
목표가 `0 ≡ 2 [ZMOD 2]`로 바뀐다.
$`0=2+2\cdot(-1)`이므로 합동의 정의에 필요한 정수로 $`-1`을 제시하면 된다.

```savedLean
theorem parityClass_zero_two :
    parityClass 0 = parityClass 2 := by
  ext
  exists (-1)
```

몫 원소의 등식이 가정으로 주어졌다면 `indisc`으로 두 대표원의 합동을 얻을 수 있다.
다음 예제의 `indisc`은 `h`를 `a ≡ b [ZMOD 2]`의 증명으로 바꾼다.

```savedLean
example (a b : Int)
    (h : parityClass a = parityClass b) :
    a ≡ b [ZMOD 2] := by
  indisc at h
  exact h
```

두 명령 모두 방금 증명한 `parityClass_eq_iff`를 사용한다.

*문제 13* $`3`과 $`1`이 같은 홀수 동치류를 나타냄을 증명하라.
이 결과와 `parityClass_zero_ne_one`을 사용하여 $`3`의 동치류와 $`0`의 동치류가 다름을 보이라.

```savedLean -keep
theorem exercise_parityClass_three_one :
    parityClass 3 = parityClass 1 := by
  sorry

theorem exercise_parityClass_three_ne_zero :
    parityClass 3 ≠ parityClass 0 := by
  sorry
```

## 대표원의 선택
%%%
tag := "relations-quotient-representatives"
file := "quotient-representatives"
%%%

몫타입 `A / R`에서 `⟦a⟧`는 원소 `a`의 동치류에 해당하는 몫 원소이다.
이번에는 몫 원소 `q`가 주어졌을 때 `q = ⟦a⟧`인 대표원 `a`를 하나 고르자.
가령 짝수 집합을 나타내는 몫 원소에서는 $`0`이나 $`2`를 대표원으로 택할 수 있다.
다음에서는 `A`에서 정의한 함수를 이용하여 몫집합 위의 함수를 만든다.
원래 함수가 `A`의 원소를 받으므로 몫 원소에서 대표원을 골라 그 함수에 넣는다.

`q : A / R`에는 동치류인 집합 `q.val`과
그 집합이 몫집합에 속한다는 증명 `q.property`가 담겨 있다.
따라서 `q.val`로 꺼내는 것은 대표원 하나가 아니라 동치류 전체이다.
대표원은 이 집합이 어떤 원소의 동치류인지 밝히는 존재명제에서 찾아야 한다.
`q.property`는 정의에 따라 `∃ a, q.val = equivalenceClass R a`의 증명이므로
`unpack`으로 대표원 `a`와 집합의 등식을 얻을 수 있다.
이 등식으로 부분타입의 값을 비교하면 `q = ⟦a⟧`를 얻는다.

```savedLean
theorem quotient_exists_classOf {A : Type _}
    (R : Relation A) (q : A / R) :
    ∃ a : A, q = ⟦a⟧ := by
  unpack q.property with ⟨a, ha⟩
  exists a
  ext
  exact ha
```

역함수에서와 같이 존재 증명에서 대표원과 그 성질을 함께 고른다.
`quotientRepr R q`는 고른 대표원이고 `quotientRepr_spec R q`는
`q = ⟦quotientRepr R q⟧`의 증명이다.

```savedLean
noncomputable def quotientReprData {A : Type _}
    (R : Relation A) (q : A / R) :
    { a : A // q = ⟦a⟧ } :=
  { val := Classical.choose (quotient_exists_classOf R q)
    property :=
      Classical.choose_spec (quotient_exists_classOf R q) }

noncomputable def quotientRepr {A : Type _}
    (R : Relation A) (q : A / R) : A :=
  (quotientReprData R q).val
theorem quotientRepr_spec {A : Type _}
    (R : Relation A) (q : A / R) :
    q = ⟦quotientRepr R q⟧ := by
  exact (quotientReprData R q).property
```

가령 `q`가 `parityClass 0`이면 선택한 정수가 반드시 `0`일 필요는 없지만,
`parityClass_eq_iff`에 따라 그 정수는 $`0`과 합동이다.

## 몫집합 위의 함수
%%%
tag := "preliminaries-quotient-functions"
file := "quotient-functions"
%%%

짝수 집합에는 `0`을, 홀수 집합에는 `1`을 대응시키는 함수를 만들자.
정수 하나가 주어졌다면 그 수를 `2`로 나눈 나머지를 계산하면 된다.
몫집합에서는 정수들의 동치류를 인수로 받으므로
이 계산을 이용하려면 먼저 그 동치류에서 정수 하나를 골라야 한다.
짝수 집합에서 `0`을 고르든 `2`를 고르든 나머지는 `0`이고,
홀수 집합에서 `1`을 고르든 `23`을 고르든 나머지는 `1`이다.
따라서 대표원을 골라 그 나머지를 취하면 원하는 함수값을 얻는다.
이 함수를 `parityRemainder : Parity → Int`로 나타내면 필요한 계산 규칙은
`parityRemainder (parityClass a) = a % 2`이다.
가령 `parityClass 23`을 넣으면 `23 % 2 = 1`을 얻고,
같은 홀수 집합을 나타내는 `parityClass (-5)`를 넣어도 `1`을 얻어야 한다.
아래에서는 이 규칙을 만족하는 함수를 구성하고, 계산 규칙으로 함수값이 $`1`임을 증명한다.

이때 대표원을 바꾸어도 값이 같다는 사실이 중요하다.
가령 $`F([a])=a`라는 규칙으로는 함수를 정의할 수 없다.
$`[0]=[2]`인 같은 짝수 집합에서 $`F([0])=0`, $`F([2])=2`라는 서로 다른 값을 요구하기 때문이다.
먼저 $`F([a])=a`라는 규칙이 불가능하다는 설명을 증명으로 적자.
이 조건이 모든 정수에서 성립한다고 가정하면
`parityClass_zero_two`로 $`[0]=[2]`를 사용하여 $`0=2`라는 모순을 얻는다.

```savedLean
example :
    ¬ ∃ F : Parity → Int, ∀ a, F (parityClass a) = a := by
  intro h
  unpack h with ⟨F, hF⟩
  have hZero : F (parityClass 0) = 0 :=
    hF 0
  rw [parityClass_zero_two, hF 2] at hZero
  contradiction
```

`rw`의 첫 등식으로 같은 몫 원소를 다른 대표원으로 나타낸 뒤
두 번째 등식으로 그 함수값을 $`2`로 바꾸면 `hZero`는 `2 = 0`의 증명이 된다.
나머지를 취하는 규칙에서는 같은 동치류의 두 대표원이 같은 나머지를 갖기 때문에
이러한 충돌이 생기지 않는다.

*보기* $`a\equiv b\pmod2`이면 $`a\bmod2=b\bmod2`이다.

*풀이* 합동의 정의에 따라 $`a=b+2k`인 정수 $`k`가 존재한다.
두 수의 차이가 $`2`의 배수이므로 $`2`로 나눈 나머지는 같다.
Lean에서도 `rcases`로 이 정수 `k`와 등식 `hk`를 얻은 뒤 `arith`로 나머지의 등식을 확인한다.

```savedLean
theorem congruent_two_same_remainder (a b : Int)
    (hab : a ≡ b [ZMOD 2]) :
    a % 2 = b % 2 := by
  rcases hab with ⟨k, hk⟩
  arith
```

방금 증명한 `congruent_two_same_remainder`에 따라 대표원을 바꾸어도 나머지는 같다.
이 조건으로 몫집합 위의 함수를 구성하는 방법을 일반적인 동치관계 $`R`과 함수 $`f:A\to B`에 대해 정리하자.
나머지 함수가 $`a\bmod2`를 동치류의 값으로 정했듯이,
여기서는 $`F:A/R\to B`를 구성하여 $`F([a]_R)=f(a)`가 되게 한다.
$`R(a,b)`이면 $`[a]_R=[b]_R`이므로
$`F([a]_R)=F([b]_R)`이며, 원하는 등식이 성립하려면 다음 조건이 필요하다.

$$`R(a,b)\ \Longrightarrow\ f(a)=f(b).`

이 조건이 성립하면 동치류 $`S`의 대표원 $`a`를 골라 $`F(S)=f(a)`로 정할 수 있다.
다른 대표원 $`b`를 사용해도 $`R(a,b)`이므로 $`f(a)=f(b)`이며 같은 함수값을 얻는다.
이처럼 대표원의 선택에 무관하게 함수값이 정해질 때
동치류 위의 함수가 *잘 정의된다*고 한다.

*정리* 동치관계 $`R`에 대하여 함수 $`f`가
$`R(a,b)\Rightarrow f(a)=f(b)`를 만족한다고 하자.
그러면 모든 $`a\in A`에 대하여 $`F([a]_R)=f(a)`인 함수 $`F:A/R\to B`가 존재한다.

*증명* 각 몫 원소 $`q`에서 `quotientRepr`로 대표원 하나를 골라
그 원소에 $`f`를 적용한 값을 $`F(q)`로 정하자.
이 함수가 원하는 등식을 만족하는지 확인하기 위해
몫 원소 $`[a]_R`에서 고른 대표원을 $`b`라고 하자.
대표원을 고를 때 얻은 등식은 $`[a]_R=[b]_R`이므로
그 방향을 바꾸고 앞의 `classOf_eq_iff`를 사용하면 $`R(b,a)`를 얻는다.
가정으로 받은 조건에 따라 $`f(b)=f(a)`이며,
왼쪽 $`f(b)`가 바로 정의한 함수의 $`[a]_R`에서의 값이다.

대표원에 무관하다는 조건은 선택한 대표원으로 만든 함수가 $`F([a]_R)=f(a)`를 만족함을 증명할 때 사용한다.
Lean에서는 함수와 이 계산 규칙을 `quotientLiftData`에 함께 담는다.
`val`에는 대표원에 `f`를 적용하는 함수를, `property`에는 모든 대표원에서의 등식 증명을 넣는다.

{anchor "relations-local-definitions"}[]코드의 `let b := ...`는 선택한 대표원을 나타내는 긴 식에 `b`라는 이름을 붙인다.

```savedLean
noncomputable def quotientLiftData {A B : Type _}
    (R : Relation A)
    (hR : IsEquivalence R)
    (f : A → B)
    (hf : ∀ a b, R a b → f a = f b) :
    { F : A / R → B //
      ∀ a, F ⟦a⟧ = f a } :=
  { val := fun q => f (quotientRepr R q)
    property := by
      intro a
      let b := quotientRepr R ⟦a⟧
      have hRelation : R b a := by
        apply (classOf_eq_iff R hR b a).mp
        exact (quotientRepr_spec R ⟦a⟧).symm

      -- 같은 동치류에서 f의 값은 같다.
      exact hf b a hRelation }
```

`hRelation : R b a`를 얻은 뒤 `hf b a hRelation`으로 `f b = f a`를 보인다.
이 단계에서 대표원을 바꾸어도 함수값이 같다는 조건을 사용한다.

이제 `.val`로 함수를 꺼내 `quotientLift`로 정의하고,
함께 증명한 등식은 `quotientLift_classOf`로 사용하자.

```savedLean
noncomputable def quotientLift {A B : Type _}
    (R : Relation A)
    (hR : IsEquivalence R)
    (f : A → B)
    (hf : ∀ a b, R a b → f a = f b) :
    A / R → B :=
  (quotientLiftData R hR f hf).val
theorem quotientLift_classOf {A B : Type _}
    (R : Relation A)
    (hR : IsEquivalence R)
    (f : A → B)
    (hf : ∀ a b, R a b → f a = f b)
    (a : A) :
    quotientLift R hR f hf ⟦a⟧ = f a := by
  exact (quotientLiftData R hR f hf).property a
```

*보기* 이제 처음에 생각한 나머지 함수를 정의하자.
`Congruent 2`가 동치관계라는 증명과 원래 함수 `fun a => a % 2`를 준비하고,
대표원을 바꾸어도 나머지가 같다는 증명 `congruent_two_same_remainder`를
함께 `quotientLift`에 넣자.

```savedLean
noncomputable def parityRemainder : Parity → Int :=
  quotientLift (Congruent 2) (congruent_equivalence 2)
    (fun a => a % 2) congruent_two_same_remainder
```

정의할 때 함께 구성한 성질을 `quotientLift_classOf`로 꺼내면
`parityRemainder (parityClass a) = a % 2`를 얻는다.

```savedLean
theorem parityRemainder_class (a : Int) :
    parityRemainder (parityClass a) = a % 2 := by
  exact quotientLift_classOf (Congruent 2)
    (congruent_equivalence 2) (fun a => a % 2)
    congruent_two_same_remainder a
```

정의에 사용한 원소 선택은 계산 절차를 제공하지 않으므로 `#eval`로 값을 구하는 대신
이 정리로 함수값이 무엇인지 증명한다. 먼저 홀수의 동치류에서 값이 $`1`임을 확인하자.

```savedLean
theorem parityRemainder_twentyThree :
    parityRemainder (parityClass 23) = 1 := by
  rw [parityRemainder_class]
  decide

theorem parityRemainder_negFive :
    parityRemainder (parityClass (-5)) = 1 := by
  rw [parityRemainder_class]
  decide

example :
    parityRemainder (parityClass 23) =
      parityRemainder (parityClass (-5)) := by
  rw [parityRemainder_twentyThree, parityRemainder_negFive]
```

두 대표원에서 같은 값 $`1`을 얻었으므로 마지막 등식도 성립한다.

*보기* $`0`과 $`1`의 동치류는 서로 다르다.
같은 몫 원소라면 `parityRemainder`의 값도 같아야 하는데
각각의 나머지는 $`0`, $`1`이므로 모순이다.

```savedLean
theorem parityClass_zero_ne_one :
    parityClass 0 ≠ parityClass 1 := by
  intro h
  have hRemainders :
      parityRemainder (parityClass 0) =
        parityRemainder (parityClass 1) := by
    rw [h]

  rw [parityRemainder_class,
    parityRemainder_class] at hRemainders
  contradiction
```

이 증명은 두 동치류의 원소를 모두 비교하는 대신
이미 정의한 함수의 값으로 두 몫 원소를 구별한다.
일반적으로 $`f(x)\ne f(y)`임을 알면 $`x\ne y`임을 보일 수 있다.

대표원을 고르는 방식을 바꾸어 함수를 구성해도 같은 결과를 얻는지 확인하자.
어떤 방식으로 구성했든 모든 대표원에서 $`F([a]_R)=f(a)`를 만족한다면,
다음 유일성에 따라 같은 함수가 된다.

*정리* 두 함수 $`F,G:A/R\to B`가 모든 $`a\in A`에 대하여
$`F([a]_R)=f(a)`와 $`G([a]_R)=f(a)`를 만족하면 $`F=G`이다.

*증명* 임의의 몫 원소 $`q`는 어떤 대표원 $`a`에 대해 $`q=[a]_R`로 나타낼 수 있다.
따라서 $`F(q)=F([a]_R)=f(a)=G([a]_R)=G(q)`이며 두 함수는 모든 원소에서 값이 같다.

```savedLean
theorem quotientLift_unique {A B : Type _}
    (R : Relation A) (f : A → B)
    (F G : A / R → B)
    (hF : ∀ a, F ⟦a⟧ = f a)
    (hG : ∀ a, G ⟦a⟧ = f a) :
    F = G := by
  ext q
  unpack quotient_exists_classOf R q with ⟨a, ha⟩
  rw [ha, hF a, hG a]
```

`ext q`로 임의의 몫 원소에서 두 함수값을 비교한다.
`quotient_exists_classOf R q`는 `∃ a, q = ⟦a⟧`의 증명이므로
`unpack`으로 대표원과 등식을 얻은 뒤 `rw`로 두 함수값을 모두 `f a`로 바꾼다.

# 연습문제
%%%
tag := "relations-exercises"
file := "exercises"
%%%

각 문제의 `sorry`를 증명으로 바꾸어 완성하라.

*문제 14* (첫 좌표가 같은 점들)

두 좌표가 모두 정수인 점들 사이에 첫 좌표가 같다는 관계를 정의한다.

(1) 이 관계가 동치관계임을 증명하라.

(2) $`(a,b)`의 동치류가 첫 좌표가 $`a`인 점들의 집합임을 보이라.

(3) 첫 결과와 `equivalenceClass_eq`를 사용하여 $`(2,3)`과 $`(2,-5)`의 동치류가 같음을 보이라.

```savedLean -keep
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
```

*문제 15* (겹치는 동치류)

(1) 동치관계의 두 동치류가 공통 원소를 가지면 두 동치류가 같음을 증명하라.

(2) $`6`을 법으로 하는 합동에서 $`2`가 $`8`과 $`20`의 동치류에 모두 속함을 보이라.

(3) 앞의 두 결과를 사용하여 두 동치류가 같음을 보이라.

```savedLean -keep
theorem exercise_classes_of_common_element {A : Type}
    (R : Relation A)
    (hR : IsEquivalence R)
    (a b : A)
    (h : ∃ x, x ∈ equivalenceClass R a ∧
      x ∈ equivalenceClass R b) :
    equivalenceClass R a = equivalenceClass R b := by
  sorry

theorem exercise_mod_six_common :
    ∃ x, x ∈ equivalenceClass (Congruent 6) 8 ∧
      x ∈ equivalenceClass (Congruent 6) 20 := by
  sorry

theorem exercise_mod_six_classes :
    equivalenceClass (Congruent 6) 8 =
      equivalenceClass (Congruent 6) 20 := by
  sorry
```

*문제 16* (대표원에 따라 달라지는 값)

모든 정수 $`a`에 대하여 $`F([a])=a\bmod3`을 만족하는 함수 $`F:\operatorname{Parity}\to\mathbb{Z}`는 존재하지 않음을 증명하라.
여기서 $`[a]`는 $`2`를 법으로 한 동치류이다.
같은 동치류에 속하지만 $`3`으로 나눈 나머지가 다른 두 정수를 찾으라.

```savedLean -keep
theorem exercise_parity_no_mod_three :
    ¬ ∃ F : Parity → Int,
      ∀ a, F (parityClass a) = a % 3 := by
  sorry
```

*문제 17* (짝수 동치류와 홀수 동치류의 교환)

동치류 $`[a]`에 $`[a+1]`을 대응시키는 함수를 구성한다.

(1) $`a\equiv b\pmod2`이면 $`[a+1]=[b+1]`임을 증명하여 대표원에 무관함을 확인하라.

(2) 이 증명을 사용한 아래 함수의 계산 규칙을 증명하라.

(3) 이 함수를 두 번 적용하면 원래 몫 원소를 얻음을 보이라.

```savedLean -keep
theorem exercise_nextParity_respects (a b : Int)
    (hab : Congruent 2 a b) :
    parityClass (a + 1) = parityClass (b + 1) := by
  sorry

noncomputable def practiceNextParity : Parity → Parity :=
  quotientLift (Congruent 2) (congruent_equivalence 2)
    (fun a => parityClass (a + 1))
    exercise_nextParity_respects
theorem exercise_nextParity_class (a : Int) :
    practiceNextParity (parityClass a) =
      parityClass (a + 1) := by
  sorry

theorem exercise_nextParity_twice (q : Parity) :
    practiceNextParity (practiceNextParity q) = q := by
  sorry
```

*힌트* 마지막 증명에서는 `quotient_exists_classOf`로 `q`의 대표원을 얻은 뒤 두 번째 결과를 사용하라.

```savedLean -show
end Ample
```

```savedLean -show
export_course_compat
```
