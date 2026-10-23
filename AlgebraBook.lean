import VersoManual
import AlgebraBook.Proof
import AlgebraBook.SetsFunctions
import AlgebraBook.NumbersRelations
import AlgebraBook.CardinalityChapter
import AlgebraBook.Tactics
import AlgebraBook.Symbols

open Verso.Genre Manual

#doc (Manual) "Lean으로 배우는 기초 수학" =>
%%%
tag := "home"
%%%

*WIP* 이 교재는 집필 중이며 본문과 코드가 바뀔 수 있다. 이전 버전과의 호환성은 보장하지 않는다.

이 책은 수학적 증명을 읽어 보았지만 Lean은 처음인 독자를 위한 입문서이다.
간단한 계산에서 시작하여 가정에서 필요한 사실을 얻고, 이미 증명한 정리를 연결해 새 증명을 작성한다.
집합과 함수의 성질을 다룬 뒤에는 동치류를 구성하고 무한집합의 크기도 비교한다.
각 장은 한 페이지에서 이어 읽을 수 있으며 목차의 소제목은 같은 페이지의 해당 위치로 이동한다.

코드의 전술이나 오른쪽 위 ‘단계 보기’를 누르면 그 단계의 가정과 목표를 확인할 수 있다.
연습문제의 ‘풀기’에서는 `sorry`를 자신의 증명으로 바꾼다.
전술과 기호의 사용법은 부록에서 찾아볼 수 있다.

{include 1 AlgebraBook.Proof}
{include 1 AlgebraBook.SetsFunctions}
{include 1 AlgebraBook.NumbersRelations}
{include 1 AlgebraBook.CardinalityChapter}
{include 1 AlgebraBook.Tactics}
{include 1 AlgebraBook.Symbols}
