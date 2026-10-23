# Lean으로 배우는 기초 수학

**WIP** — 이 교재는 집필 중이며 본문과 코드가 바뀔 수 있다. 이전 버전과의 호환성은 보장하지 않는다.

수학적 증명을 어느 정도 알고 있지만 Lean은 처음 사용하는 독자를 위한 한국어 입문서이다.

1. **증명의 기초** — 간단한 계산의 증명에서 명제논리로 시작하여 고전논리, 술어와 양화사, 등식과 외연성으로 확장한다.
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

풀이 편집기는 WASM Lean을 사용하며, 각 문제까지 본문에서 소개한 전술만 허용한다.
도입 위치는 `web/learning-tactics.json`, 구문 검사는 `web/lean/LearningGuard.lean`에서 관리한다.
작성한 풀이는 본문과 브라우저 저장소에 남으며, 목차에서 장별·전체 진행도를 확인하고 미완료 문제로 이동할 수 있다.
진행도는 현재 문제와 일치하는 검사 결과만 사용하고 문제 묶음 단위로 집계한다.

본문을 수정하면 문제 이전의 문맥도 달라지므로
기존 실행기만 복사하지 말고 새 문맥을 컴파일해야 한다.
`scripts/build_browser_book.py`에 일치하는 wasm32용 네이티브 Lean과 Ample 라이브러리를 지정하고,
`scripts/bundle_book_contexts.py`로 고정된 실행기에 검증된 문맥을 추가한다.
새 번들을 `web/wasm-runtime.local.json`으로 지정한 뒤 `preview.bat`를 실행하면 된다.
`preview.bat`의 미리보기 포트는 8000이다.

공개 원고와 이 책의 문제 문맥을 포함한 실행기는 [Cywohoy/lean-foundations](https://github.com/Cywohoy/lean-foundations)에 함께 배포한다.
공개 실행기의 주소와 체크섬은 `web/wasm-runtime.json`, 원본 실행기의 고정 정보는 `web/wasm-base-runtime.json`에 있다.
로컬 설정 없이 `python scripts/prepare_pages.py`를 실행하면 공개 실행기를 받아 정적 사이트를 만든다.

브라우저 실행기 구성은 [WASM 빌드 안내](experiments/wasm/README.md), 공개 배포는 [배포 안내](DEPLOYMENT.md)에서 설명한다.
원고와 실행기 제작은 기존 교재 폴더를 필요로 하지 않는다.

## 개발과 출처

이 프로젝트는 기존 대수학 교재의 기초 수학 부분에서 독립하였다.
문서 생성에 사용하는 Lean 모듈 이름은 `AlgebraBook`이다.
Ample은 별도의 공개 라이브러리이며 `lakefile.toml`의 Git 릴리스를 사용한다.
이 원고의 구조를 바꾸기 위해 Ample의 모듈이나 공개 API를 바꾸지는 않는다.

새 Ample 전술을 릴리스 전에 함께 개발할 때는 Lake의 표준 로컬 설정
`.lake/package-overrides.json`에서 형제 체크아웃을 지정한다.
그러면 일반 빌드와 검사 명령도 해당 Ample을 사용한다. 이 설정과 개발용 WASM 번들은 Git에서 제외하며 공개 의존 버전과 구별한다.
예를 들어 이 파일을 다음과 같이 작성할 수 있다.

```json
{
  "version": "1.3.0",
  "packagesDir": ".lake/packages",
  "packages": [{
    "type": "path", "scope": "", "name": "ample", "dir": "../Ample",
    "manifestFile": "lake-manifest.json", "inherited": false,
    "copy": false, "configFile": "lakefile.toml"
  }]
}
```

검토는 [검토 절차](REVIEW_PROCESS.md)에 따라 수정 위치의 위계와 의존 관계로 필요한 범위를 정한다.
읽을 범위와 고칠 범위를 구분하고, [검토 관리 도구](review/README.md)로 다시 확인할 항목과 수정 범위를 기록한다.
`review.bat`를 직접 실행하면 관리 화면이 열린다. [현재 검토 상태](REVIEW_STATE.md)의 원본은 `review/state.json`이다.
[기록 양식](REVIEW_TEMPLATE.md)은 범위·판단 근거·문제 풀이·재검토 결과를 남기는 데 사용한다.
서술 기준은 [STYLE.md](STYLE.md), 변경 종류별 검사는 [검사 안내](tests/README.md)에 있다.
개별 작업의 검토 결과와 개인 검토 상태는 로컬에만 보존하며 Git에 포함하지 않는다.
외부 코드와 폰트의 출처·라이선스는 `THIRD_PARTY_NOTICES.md`와 `licenses/`에 있다.
원본 대수학 교재와 개인 풀이는 이 저장소에 복제하지 않았다.
