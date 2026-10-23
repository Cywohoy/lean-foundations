# 공개 배포

이 저장소는 [lean.p4per.dev](https://lean.p4per.dev/)의 기본 페이지와
[/foundations/](https://lean.p4per.dev/foundations/)의 네 장 입문서를 GitHub Pages로 배포한다.
원고와 문제 풀이용 WASM 실행기는 `Cywohoy/lean-foundations`,
공유 라이브러리는 `Cywohoy/ample`에서 관리한다.
기존 대수학 교재나 개인 풀이 폴더 없이 빌드할 수 있다.

## 배포 실행

요청 범위의 수정과 검사를 모두 마친 뒤 한 번만 배포한다. 빌드나 검사 중 발견한 문제는
로컬에서 먼저 수정하며, 수정할 때마다 공개 사이트에 중간 버전을 올리지 않는다.

저장소의 `Pages` 워크플로는 수동 실행한다. 기본값은 사이트를 빌드하여 배포용 artifact를 생성하는 것이며, `publish`를 켰을 때만 GitHub Pages에 배포한다.
`Book checks`는 push와 pull request에서 원고·추출 Lean 코드·문제 템플릿을 검사한다.
원고의 완성 코드나 문제 직전 문맥이 바뀌면 WASM 문맥과 릴리스를 먼저 갱신해야 하며, 일치하지 않는 실행기로는 사이트 생성이 실패하도록 되어 있다.

```text
gh workflow run pages.yml --ref main -f publish=true
```

### 실행기의 진단 수집을 수정한 경우

브라우저 프런트엔드의 관리 원본은 `web/lean/BrowserFrontend.lean`이다.
`tests/BrowserDiagnostics.Tests.py`는 중첩된 `have`의 진단을 네이티브 Lean으로 검사하고,
`tests/BrowserDiagnostics.Tests.cjs`는 이미 실행 중인 미리보기에서 오류 표시·수정·문제 풀이를 검사한다.
두 번째 검사는 서버를 열거나 종료하지 않으며 `BOOK_URL`로 검사할 주소를 지정할 수 있다.

프런트엔드 수정은 일치하는 Lean 소스 트리에 설치하고 WASM 컴파일러를 다시 빌드해야 한다.
새 빌드의 런타임 글루는 `scripts/optimize_browser_runtime.py`로 처리하고,
`scripts/pack_browser_library.py`로 같은 빌드의 Lean·Ample 라이브러리를 묶는다.
`scripts/package_browser_runtime.py`는 이전 실행기의 라이선스·Worker를 보존하면서
새 컴파일러와 라이브러리, 프런트엔드 원본을 개발용 번들로 구성한다.
Ample을 변경할 때는 `scripts/build_browser_ample.py`로 공개할 커밋의 깨끗한 소스 스냅샷을 빌드한다.
`package_browser_runtime.py --ample-source ... --ample-commit ...`은 그 스냅샷과 빌드 기록의 소스·출력 체크섬을 확인한다.
작업 트리에 남아 있는 별도 수정은 공개 실행기에 섞지 않는다.

개발용 기본 번들의 핀은 `tmp/`에 두고, `bundle_book_contexts.py --base-config`로 지정한다.
문맥을 포함한 개발용 실행기는 `web/wasm-runtime.local.json`으로만 연결한다.
공개 배포를 요청받으면 기본 실행기와 문제 문맥 번들을 함께 공개하고
`web/wasm-base-runtime.json`과 `web/wasm-runtime.json`을 그 릴리스의 체크섬·주소로 갱신한 뒤
사이트를 한 번에 배포한다. 공개 핀에 로컬 파일 경로를 넣지 않는다.

GitHub 공식 안내:

- [사용자 도메인 연결](https://docs.github.com/en/pages/configuring-a-custom-domain-for-your-github-pages-site/managing-a-custom-domain-for-your-github-pages-site)
- [도메인 소유 확인](https://docs.github.com/en/pages/configuring-a-custom-domain-for-your-github-pages-site/verifying-your-custom-domain-for-github-pages)

## 사이트 기본 페이지와 교재 경로 분리

`lean.p4per.dev/`는 교재를 고르는 기본 페이지로 두고, 기초 수학 입문서는
`/foundations/` 아래에 배포한다. 장별 한 페이지 구성과 브라우저 Lean은 유지한다.
정적 사이트 준비 단계에서 경로를 나누므로 본문 원고의 상대 링크는 바꾸지 않는다.
기존 장 주소는 새 경로로 이동하며, 풀이 저장 식별자는 유지한다.
