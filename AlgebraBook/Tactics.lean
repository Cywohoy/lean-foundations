import VersoManual
import AlgebraBook.Meta.Lean
import AlgebraBook.CardinalityChapter

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open AlgebraBook

#doc (Manual) "부록: 전술 일람" =>
%%%
tag := "tactic-reference"
file := "tactics"
number := false
%%%

본문에서 사용하는 전술을 역할별로 모았다. `rw`, `expand`, `simp`처럼 가정에도 적용하는 명령은 `at h`로 그 가정을 지정한다.
`unpack h`와 `cases h`는 처음부터 가정을 받는 명령이므로 `at`을 쓰지 않는다.
코드의 새 이름은 실제 문제에 맞게 바꾸어 사용하라.

```savedImport
import AlgebraBook.CardinalityChapter
```

```savedLean -show
namespace TacticExamples
open scoped Ample Classical
```

# 가정과 정리
%%%
tag := "tactic-hypotheses"
%%%

`intro h`는 함의의 가정을 도입하고 `intro x`는 전칭명제의 임의의 원소를 도입한다.
`apply r`는 정리 `r`의 결론을 목표에 맞추고 필요한 전제를 새 목표로 남긴다.
`exact h`는 현재 목표의 증명을 제시하여 마친다.

```savedLean
example (P Q : Prop)
    (hPQ : P → Q) :
    P → Q := by
  intro hP
  apply hPQ
  exact hP
```

`apply`가 실패하면 정리의 *결론*과 목표를 비교하라.
예를 들어 `hPQ : P → Q`는 목표 `Q`에 쓸 수 있지만 목표 `P`를 `Q`로 바꾸지는 않는다.

함의를 가정에 적용할 때는 `apply hPQ at hP`로 `hP : P`를 `hP : Q`로 바꾼다.
목표에서는 결론으로부터 전제로 거슬러 올라가고, 가정에서는 전제로부터 결론을 얻는다.

```savedLean
example (P Q : Prop)
    (hPQ : P → Q)
    (hP : P) :
    Q := by
  apply hPQ at hP
  exact hP
```

# 대상과 중간 증명
%%%
tag := "tactic-local-definitions"
%%%

`set x := t`는 식 `t`에 이름 `x`를 붙이고 가정과 목표의 `t`를 `x`로 바꾼다.
`let x := t`는 증명 안에서 사용할 값을 정의하며, 이미 나타난 식을 새 이름으로 바꾸지는 않는다.
`set x := t with h`는 그 정의의 등식 `h : x = t`도 남긴다.
`have h : P := by ...`는 중간 명제 `P`를 증명하고 그 증명을 `h`로 사용한다.
이미 증명 `p : P`가 있으면 `have h : P := p`로 적을 수 있다.
`replace h : Q := by ...`는 기존 가정 `h`를 새로 증명한 `Q`로 교체한다.
새 증명 안에서는 원래 가정 `h`를 사용할 수 있다.
`suffices h : P by ...`는 먼저 `P`에서 원래 목표를 얻는 증명을 적고, 그다음 `P`를 증명한다.
자연수의 나머지를 다루는 {ref "preliminaries-arith"}[산술 자동화 예제]에서는 `suffices bound : a < m by arith`를 사용한다.

```savedLean
example (a b c : Nat)
    (hab : a = b)
    (hbc : b = c) :
    a = c := by
  have hac : a = c := by
    rw [hab]
    exact hbc

  exact hac
```

# 구성과 분해
%%%
tag := "tactic-conjunctions"
%%%

`constructor`는 논리곱을 두 명제로, 동치를 두 방향의 함의로 나눈다.
나뉜 목표는 `·` 뒤에서 각각 증명한다. `and_intros`는 여러 겹의 논리곱을 한 번에 나눈다.
`unpack h with ⟨hP, hQ⟩`는 논리곱의 증명에서 두 증명을 꺼낸다.

```savedLean
example (P Q : Prop)
    (h : P ∧ Q) :
    Q ∧ P := by
  unpack h with ⟨hP, hQ⟩
  constructor
  · exact hQ
  · exact hP
```

존재명제에서는 `exists a`로 증인을 제시하고 남은 조건을 증명한다.
가정 `h : ∃ x, P x`는 `unpack h with ⟨x, hx⟩`로 원소와 그 성질을 꺼낸다.
`rcases`는 `⟨x, hx, hy⟩`처럼 여러 겹의 묶음이나 `hP | hQ`처럼 경우를 지정하여 분해한다.
꺾쇠괄호는 한 묶음의 성분을 나타낸다.

논리합을 증명할 때는 `left` 또는 `right`로 보일 쪽을 정한다.
논리합인 가정은 두 경우를 모두 다루어야 하므로 `cases`를 사용한다.

```savedLean
example (P Q : Prop)
    (h : P ∨ Q) :
    Q ∨ P := by
  cases h with
  | inl hP =>
      right
      exact hP

  | inr hQ =>
      left
      exact hQ
```

`trivial`은 `True` 같은 자명한 목표를 증명한다.
`contradiction`은 `False`나 서로 모순되는 가정을 사용하여 목표를 증명한다.
`True.intro`와 `False.elim`을 직접 사용하는 방식도 본문에서 다룬다.

# 정의와 등식
%%%
tag := "tactic-unfold-auto"
%%%

`expand`는 현재 식에 나타난 교재나 풀이 파일의 정의를 한 층 펼치고 인수 대입과 성분 계산을 수행한다.
`expand at h`는 가정에 적용한다.
직접 정의를 정하려면 `dsimp [f]`를, 바꿀 식을 정하려면 `change 식`을 쓴다.
`change`는 새 식이 정의상 같을 때만 사용할 수 있다.

`rfl`은 정의와 계산에 따라 양변이 같은 등식을 증명한다.
`rw [h]`는 등식의 왼쪽을 오른쪽으로 바꾸며, `rw [← h]`는 반대 방향으로 바꾼다.
`rw [h] at hx`는 가정 `hx`에 사용한다.
`symm`은 목표 등식의 방향을, `symm at h`는 가정 `h`의 등식 방향을 바꾼다.
`calc`는 각 등식의 증명을 제시하면서 등식을 이어 쓴다.

```savedLean
example (a b c : Nat)
    (hab : a = b)
    (hbc : b = c) :
    a = c := by
  calc
    a = b := by exact hab
    _ = c := by exact hbc
```

`simp`는 등록된 정리를 정해진 방향으로 사용하여 식을 정리한다.
정의를 한 층 확인하려는 `expand`와 달리 이미 증명된 여러 성질이 적용될 수 있다.
`simp only [h]`는 지정한 정리 `h`만 사용한다. 유한곱의 기수를 계산할 때처럼
반복해서 나타나는 식을 한 가지 정리로 바꿀 때 사용할 수 있다.

# 전체와 성분의 비교
%%%
tag := "tactic-equality-comparison-rules"
%%%

`ext`는 목표의 등식을 원소나 성분의 비교로 바꾼다.
함수에서는 `ext x`로 함수값을, 집합에서는 원소 조건을 비교한다.
함수의 외연성만 사용할 때는 `funext x`를 쓸 수 있으며, 명제의 동치를 등식으로 바꾸는 정리는 `propext`이다.

```savedLean
example {A B : Type} (a c : A) (b d : B)
    (ha : a = c)
    (hb : b = d) :
    (a, b) = (c, d) := by
  ext
  · exact ha
  · exact hb
```

`indisc at h`는 등식인 가정에서 비교 조건을 얻는다.
`indisc at h with ha hb`처럼 이름을 붙이면 원래 등식을 유지하고 두 성분의 등식을 얻는다.
`ext`와 `indisc`은 기본적으로 한 겹만 비교하며 `: 2`로 두 겹을 지정한다.
`rw`로 바로 필요한 식을 바꿀 수 있는 곳에서는 등식을 먼저 분해할 필요가 없다.

# 경우 구분과 귀납법
%%%
tag := "tactic-cases-and-induction"
%%%

`cases hx : f x with`처럼 등식의 이름을 붙이면 경우를 나눈 함수값이 무엇인지 `hx`에 남는다.

`by_cases h : P`는 `h : P`인 경우와 `h : ¬ P`인 경우를 나눈다.
`by_contra h`는 목표의 부정을 가정하고 `False`를 보이는 귀류법을 시작한다.
`apply Classical.not_not.mp`는 목표 `P`를 이중 부정 `¬¬ P`로 바꾼다.
이중 부정을 제거하는 데에는 고전논리를 사용한다.

`induction n with`는 자연수의 `zero`, `succ n ih` 두 경우를 만든다.
귀납 단계에서 다른 매개변수도 달라지면 `generalizing` 뒤에 그 이름을 적는다.
이유와 실제 목표의 차이는 본문의 비둘기집 원리 증명에서 확인할 수 있다.
`induction i using Fin.lastCases with`는 `Fin (n + 1)`의 원소를
마지막 번호인 `last` 경우와 앞의 번호인 `cast i` 경우로 나눈다.
유한한 집합족의 합과 곱에서 마지막 항을 구별할 때 이 방식을 사용한다.

# 계산과 자동화
%%%
tag := "tactic-arith"
%%%

`decide`는 명제를 계산하여 참임을 확인할 수 있을 때 그 증명을 만든다.
구체적인 수의 비교와 달리 변수가 있는 임의의 부등식을 해결하는 전술은 아니다.

`arith`는 자연수·정수의 산술 규칙과 현재 가정을 연결한다.
선형 등식·부등식, 다항식 등식, 등록된 곱의 비교와 몫·나머지·나누어떨어짐을 다룬다.
모든 산술 명제를 증명하는 것은 아니므로 실패하면 필요한 중간 부등식이나 경우 구분을 제시하라.

`card`는 기수의 등식·부등식과 유한성·무한성에 관한 등록 정리를 사용한다.
조건을 만족하는 새 대응을 임의로 만들어 주지는 않는다.
두 전술은 서로 다른 분야의 기본 성질을 사용한다.

{anchor "tactic-auto-normalization"}[]`open scoped Ample.Auto`는 전술 전후에
부정된 부등식이나 익명 술어의 적용 등 정해진 표현을 자동으로 정리한다.
고전논리가 켜진 범위에서는 이중 부정도 정리한다.
이 설정과 명시적인 `simp` 호출은 구별된다.
일반적인 `x ∈ S`의 표기는 유지하며 논리곱의 분해나 외연성 증명을 대신하지 않는다.

```savedLean -show
end TacticExamples
```
