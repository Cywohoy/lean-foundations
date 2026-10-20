# Lean으로 배우는 기초 수학

수학적 증명을 어느 정도 알고 있지만 Lean은 처음 사용하는 독자를 위한 한국어 입문서이다.

1. **Lean과 증명** — 계산에서 명제와 증명으로, 가정과 정리에서 새로운 결론으로 이어 간다.
2. **집합과 함수** — 원소 조건, 집합의 등식, 상과 역상, 전단사와 역함수를 다룬다.
3. **수와 동치관계** — 귀납법과 합동을 배우고 동치류와 몫집합 위의 함수를 구성한다.
4. **집합의 크기** — 유한한 번호와 가산 대응을 구성하고 칸토어의 대각선 논법을 증명한다.

각 장은 한 웹 페이지이며 소제목은 같은 페이지의 해당 위치로 연결된다.
전술과 기호 입력법은 별도의 부록에서 찾을 수 있다.

공개 사이트의 [기본 페이지](https://lean.p4per.dev/)에서 교재를 고르며,
이 입문서는 [기초 수학](https://lean.p4per.dev/foundations/) 아래에 있다.

## 빌드

`lean-toolchain`에 지정된 Lean을 설치한 뒤 이 폴더에서 실행한다.

```text
lake exe textbook
python scripts/exercise_templates.py
python tests/check_book.py
python tests/check_lean.py
```

생성된 본문은 `_out/html-multi/`에 있다. `ExerciseTemplates/`는 배포용 문제 원본이고,
`Exercises/`는 개인 풀이용으로 Git에서 제외한다. 초기화 스크립트는 현재 풀이를 백업한다.

## 브라우저 풀이

풀이 편집기는 WASM Lean을 사용한다. 본문을 수정하면 문제 이전의 문맥도 달라지므로
기존 실행기만 복사하지 말고 새 문맥을 컴파일해야 한다.
`scripts/build_browser_book.py`에 일치하는 wasm32용 네이티브 Lean과 Ample 라이브러리를 지정하고,
`scripts/bundle_book_contexts.py`로 고정된 실행기에 검증된 문맥을 추가한다.
새 번들을 `web/wasm-runtime.local.json`으로 지정한 뒤 `preview.bat`를 실행하면 된다.
기본 미리보기 포트는 8010이다.

공개 원고와 이 책의 문제 문맥을 포함한 실행기는 [Cywohoy/lean-foundations](https://github.com/Cywohoy/lean-foundations)에 함께 배포한다.
공개 실행기의 주소와 체크섬은 `web/wasm-runtime.json`, 원본 실행기의 고정 정보는 `web/wasm-base-runtime.json`에 있다.
로컬 설정 없이 `python scripts/prepare_pages.py`를 실행하면 공개 실행기를 받아 정적 사이트를 만든다.

브라우저 실행기 구성은 `experiments/wasm/README.md`, 도메인과 배포 설정은 `DEPLOYMENT.md`에서 설명한다.
원고와 실행기 제작은 기존 교재 폴더를 필요로 하지 않는다.

## 개발과 출처

이 프로젝트는 기존 대수학 교재의 기초 수학 부분에서 독립하였다.
내부 Lean 모듈 이름 `AlgebraBook`과 일부 가져오기 경로는 기존 풀이를 위해 유지한다.
Ample은 별도의 공개 라이브러리이며 `lakefile.toml`의 Git 릴리스를 사용한다.
이 원고의 구조를 바꾸기 위해 Ample의 모듈이나 공개 API를 바꾸지는 않는다.

구성과 서술 기준은 `RESTRUCTURING_PLAN.md`, `STYLE.md`, 구현 후 점검 결과는 `REVIEW.md`에 있다.
기존 전술 연구는 `WORK_QUEUE.md`에 보존한다.
외부 코드와 폰트의 출처·라이선스는 `THIRD_PARTY_NOTICES.md`와 `licenses/`에 있다.
원본 대수학 교재와 개인 풀이는 이 저장소에 복제하지 않았다.
