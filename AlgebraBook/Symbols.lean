import VersoManual

open Verso.Genre Manual

#doc (Manual) "부록: 기호 입력" =>

%%%
tag := "symbol-reference"
file := "symbols"
number := false
%%%

본문의 기호와 처음 설명하는 위치를 하나의 표에 모았다.
웹의 풀이 화면과 VS Code의 Lean 확장에서는 아래 표와 같은 입력법을 사용한다.
역슬래시와 이름을 입력하면 수학 기호로 바뀌며, `\forall`처럼 다른 이름의 앞부분이 아닌 입력은 완성하는 즉시 변환된다.
`\in`처럼 더 긴 이름으로 이어질 수 있는 입력은 공백이나 구두점을 입력할 때 변환되며, `Tab`으로 변환할 수도 있다.

:::table +header (align := left)
*
  * 처음 등장하는 절
  * 기호
  * 뜻
  * 입력
*
  * {ref "intro-propositions-and-goals"}[Lean과 증명: 명제와 술어]
  * `→`
  * 함수의 타입 또는 명제의 함의
  * `\to`
*
  * {ref "intro-propositions-and-goals"}[Lean과 증명: 명제와 술어]
  * `=`
  * 두 대상의 같음
  * 그대로 입력
*
  * {ref "intro-predicates"}[Lean과 증명: 명제와 술어]
  * `↦`
  * 수학식에서 원소와 함수값의 대응
  * `\mapsto`
*
  * {ref "proofs-assumptions-and-goals"}[Lean과 증명: 가정과 목표]
  * `⊢`
  * 증명 화면의 목표 표시
  * `\vdash`
*
  * {ref "proofs-universal-statements"}[Lean과 증명: 전칭명제]
  * `∀`
  * 모든 원소에 대한 전칭명제
  * `\forall`
*
  * {ref "sets-sets-as-predicates"}[집합과 함수: 술어와 집합]
  * `ℕ`
  * 수학식에서 자연수 전체의 집합
  * `\N`
*
  * {ref "sets-membership-notation"}[집합과 함수: 원소 표기]
  * `∈`
  * 원소 관계
  * `\in`
*
  * {ref "sets-universal-and-empty-sets"}[집합과 함수: 전체집합과 공집합]
  * `∅`
  * 공집합
  * `\emptyset`
*
  * {ref "sets-subsets"}[집합과 함수: 부분집합]
  * `⊆`
  * 포함 관계
  * `\subseteq`
*
  * {ref "sets-intersections-and-conjunctions"}[교집합과 논리곱]
  * `·`
  * 목표별 증명의 시작
  * `\.`
*
  * {ref "sets-intersections-and-conjunctions"}[교집합과 논리곱]
  * `∩`
  * 교집합
  * `\cap`
*
  * {ref "sets-intersections-and-conjunctions"}[교집합과 논리곱]
  * `∧`
  * 논리곱
  * `\and`
*
  * {ref "sets-equivalence"}[집합과 함수: 동치]
  * `↔`
  * 두 명제의 동치
  * `\iff`
*
  * {ref "sets-unions-and-disjunctions"}[합집합과 논리합]
  * `∪`
  * 합집합
  * `\cup`
*
  * {ref "sets-unions-and-disjunctions"}[합집합과 논리합]
  * `∨`
  * 논리합
  * `\or`
*
  * {ref "sets-complements-and-negation"}[여집합과 부정]
  * `¬`
  * 명제의 부정
  * `\neg`
*
  * {ref "sets-complements-and-negation"}[여집합과 부정]
  * `∉`
  * 원소 관계의 부정
  * `\notin`
*
  * {ref "sets-complements-and-negation"}[여집합과 부정]
  * `ᶜ`
  * 여집합의 위첨자
  * `\^c`
*
  * {ref "sets-complements-and-negation"}[집합과 함수: 여집합과 부정]
  * `≠`
  * 두 대상이 같지 않음
  * `\ne`
*
  * {ref "sets-differences"}[집합과 함수: 차집합]
  * `\`
  * 차집합
  * 역슬래시 하나를 그대로 입력
*
  * {ref "functions-image"}[집합과 함수: 상과 존재명제]
  * `⟨`, `⟩`
  * 묶인 대상의 성분을 분해하는 패턴
  * `\<`, `\>` (`\langle`, `\rangle`도 가능)
*
  * {ref "functions-image"}[집합과 함수: 상과 존재명제]
  * `∃`
  * 어떤 원소가 존재한다는 명제
  * `\exists`
*
  * {ref "sets-indexed-families"}[집합과 함수: 집합족]
  * `⋃`, `⋂`
  * 집합족의 합집합과 교집합
  * `\bigcup`, `\bigcap`
*
  * {ref "functions-injectivity"}[집합과 함수: 단사함수]
  * `←`
  * `rw`에서 등식을 반대 방향으로 사용
  * `\l` (`\leftarrow`도 가능)
*
  * {ref "functions-subtypes"}[집합과 함수: 부분타입]
  * `//`
  * `{x : A // P x}`에서 부분타입의 원소 조건
  * 슬래시 두 개를 그대로 입력
*
  * {ref "functions-composition"}[집합과 함수: 합성함수]
  * `∘`
  * 함수의 합성
  * `\circ`
*
  * {ref "intro-pairs-and-currying"}[집합과 함수: 순서쌍]
  * `×`
  * 순서쌍의 타입 또는 집합의 곱
  * `\times`
*
  * {ref "functions-sums-spaces"}[집합과 함수: 집합의 합과 함수 공간]
  * `⊕`
  * 출처를 구별한 타입의 합
  * `\oplus`
*
  * {ref "preliminaries-divisibility"}[수와 동치관계: 정수와 배수]
  * `ℤ`
  * 정수의 집합이며 Lean에서는 `Int`로 쓴다
  * `\Z`
*
  * {ref "preliminaries-defining-divisibility"}[수와 동치관계: 나누어떨어짐]
  * `∣`
  * 정수의 나누어떨어짐
  * `\mid`
*
  * {ref "preliminaries-congruence"}[수와 동치관계: 나머지와 합동]
  * `/`, `%`
  * 자연수와 정수의 몫, 나머지
  * 그대로 입력
*
  * {ref "preliminaries-congruence"}[수와 동치관계: 나머지와 합동]
  * `≡`
  * `a ≡ b [ZMOD n]`에서 정수의 합동
  * `\==`
*
  * {ref "numbers-finite-sums"}[수와 동치관계: 유한합과 유한곱]
  * `∑`, `∏`
  * 유한합과 유한곱
  * `\sum`, `\prod`
*
  * {ref "relations-quotient-elements"}[수와 동치관계: 몫집합의 원소 타입]
  * `/`
  * `A / R`에서 관계 `R`에 대한 몫타입
  * 그대로 입력
*
  * {ref "relations-quotient-elements"}[수와 동치관계: 몫집합의 원소 타입]
  * `⟦`, `⟧`
  * 대표원에서 만든 몫 원소: `(⟦a⟧ : A / R)`
  * `\[[`, `\]]`
*
  * {ref "cardinality-fin-values"}[집합의 크기: 번호와 자연수]
  * `↑`
  * 원소나 자연수를 다른 타입으로 옮기는 형변환
  * `\u` (`\coe`도 가능)
*
  * {ref "cardinality-countable-sets"}[집합의 크기: 자연수와 같은 크기의 집합]
  * `ℵ₀`
  * 수학식에서 자연수의 기수
  * `\aleph0`
:::

`\<>`와 `\[[]]`를 입력하면 각각 `⟨⟩`와 `⟦⟧`가 생기고 커서가 두 괄호 사이에 놓인다.
`⊢`는 증명 화면에서 목표 앞에 자동으로 표시된다.
