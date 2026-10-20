# LeanFoundations 작업 지침

- 이 폴더는 네 장으로 구성한 독립 한국어 Lean 입문서이다. `../Textbook`과 `../Ample`은 별도 저장소이며 이 프로젝트는 기존 교재를 실행 의존성으로 삼지 않는다.
- Ample은 Lake에서 공개 Git 릴리스로 가져온다. 라이브러리의 공개 API나 수학 정의를 바꿀 때는 Ample에서 별도로 검토하고 검증한다. 교재 원고의 재배치는 Ample의 모듈 재배치를 뜻하지 않는다.
- 한국어 본문은 `STYLE.md`, 구성은 `RESTRUCTURING_PLAN.md`를 따른다. 검토 제안과 실제 반영을 구별한다.
- 본문은 `AlgebraBook/Proof.lean`, `SetsFunctions.lean`, `NumbersRelations.lean`, `CardinalityChapter.lean`이다. 장당 한 웹 페이지이며 필수 설명을 접거나 소절별 페이지로 분리하지 않는다.
- 첫 장은 간단한 산술 계산에서 함수·명제·술어·증명으로 이어진다. 부분 적용과 암시적 인수는 실제 사용하는 곳에서 설명한다. 정리 사용법과 직접 증명의 목적을 구별한다.
- 부록에는 실제 본문과 문제에서 사용하는 용법만 둔다. 라이브러리의 모든 확장 문법을 입문서에 싣지 않는다.
- 완성된 본문과 내보낸 의존 모듈에는 `sorry`나 임의의 추가 공리를 넣지 않는다. 연습문제는 `savedLean -keep`의 미완성 골격으로 두고 그 풀이를 이후 본문에 사용하지 않는다.
- `Exercises/`는 개인 풀이이다. 덮어쓰거나 초기화하지 않는다. 템플릿은 `scripts/exercise_templates.py`로 `ExerciseTemplates/`에 생성한다.
- `scripts/book_code.py`는 완성된 장의 코드를 브라우저용으로 내보낸다. `scripts/build_browser_book.py`는 실제 문제 직전의 문맥을 일치하는 wasm32 컴파일러로 검사한다. 이전 원고의 브라우저 문맥을 새 원고에 재사용하지 않는다.
- 문서 변경 뒤 `lake exe textbook`, `python tests/check_book.py`, `python tests/check_lean.py`로 본문·링크·추출 코드·템플릿을 검사한다.
- 라이브러리 도움말과 오류는 영어, 교재와 교육용 주석은 한국어로 쓴다.
- PDF 생성과 배포는 사용자가 명시적으로 요청할 때만 한다. GitHub 저장소 생성·원격 변경을 로컬 분리 작업의 일부로 추정하지 않는다.
- 외부 코드·폰트·브라우저 실행기의 라이선스와 출처를 보존한다.
