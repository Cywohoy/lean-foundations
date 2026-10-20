# 저장소와 도메인

2026-10-21 기준.

## 저장소 분리

- `Cywohoy/lean-foundations`: 네 장으로 구성한 한국어 Lean·기초 수학 입문서.
- `Cywohoy/lean-algebra`: 기존 교재와 `full-book` 브랜치의 대수학 원고. 기존 내용과 개인 풀이를 보존한다.
- `Cywohoy/ample`: 두 교재에서 가져오는 전술·수학 라이브러리.

새 입문서는 별도의 Git 이력으로 관리하며, 원본 교재 체크아웃 없이 빌드할 수 있다.
문제 풀이용 WASM 실행기도 새 저장소의 릴리스에서 제공한다. `Exercises/`, 빌드 결과, 로컬 설정은 Git에 넣지 않는다.

## p4per.dev 연결 확인

`p4per.dev`는 현재 `Cywohoy/papertoy1127.github.io`의 GitHub Pages 블로그에 연결되어 있다.
공개 DNS의 네 A 레코드는 GitHub Pages를 가리키며, 네임서버는 Cloudflare이다.
기존 블로그의 DNS와 Pages 설정은 유지했다. 새 저장소의 Pages를 활성화하고 사용자 도메인을 `lean.p4per.dev`로 설정했다.
Cloudflare의 DNS 레코드는 사용자 계정에서 추가해야 한다.

교재를 따로 연결하려면 `lean.p4per.dev` 같은 하위 도메인을 사용하는 구성이 간단하다.
연결할 때는 다음 순서로 진행한다.

1. 새 저장소의 Pages를 GitHub Actions 배포 방식으로 활성화한다.
2. 교재를 배포하여 기본 Pages 주소에서 실행과 링크를 확인한다.
3. 저장소의 Pages 사용자 도메인을 `lean.p4per.dev`로 지정한다.
4. Cloudflare DNS에 이름 `lean`, 값 `Cywohoy.github.io`인 CNAME을 DNS 전용으로 추가한다. 값에는 저장소 경로를 붙이지 않는다.
5. GitHub의 DNS 확인과 인증서 발급 뒤 HTTPS를 적용한다. 도메인 검증 TXT가 필요하면 GitHub가 제시하는 값을 사용한다.

`p4per.dev/lean-foundations/` 같은 경로를 사용하려면 현재 루트 도메인을 소유한 블로그의 배포 산출물에 교재를 합치거나 별도 라우팅을 구성해야 한다.
루트 도메인의 Pages 연결을 새 저장소로 옮기면 기존 블로그 주소에 영향을 주므로, 경로형 구성을 단순한 도메인 설정 변경으로 처리하지 않는다.

사용자의 후속 요청으로 `Pages` 워크플로의 배포를 실행했다.

사용자가 Cloudflare에 추가할 레코드는 다음 하나이다.

| 항목 | 값 |
| --- | --- |
| 유형 | CNAME |
| 이름 | lean |
| 대상 | Cywohoy.github.io |
| 프록시 상태 | DNS 전용(회색 구름) |
| TTL | 자동 |

기존 `@`와 `www` 레코드는 유지한다. DNS 반영과 GitHub 인증서 발급이 완료되어야 `https://lean.p4per.dev/`에서 접속할 수 있다.
HTTPS 강제 적용은 인증서가 준비된 뒤 활성화한다.

## 배포 실행

저장소의 `Pages` 워크플로는 수동 실행한다. 기본값은 사이트를 빌드하여 배포용 artifact를 생성하는 것이며, `publish`를 켰을 때만 GitHub Pages에 배포한다.
`Book checks`는 push와 pull request에서 원고·추출 Lean 코드·문제 템플릿을 검사한다.
원고의 완성 코드나 문제 직전 문맥이 바뀌면 WASM 문맥과 릴리스를 먼저 갱신해야 하며, 일치하지 않는 실행기로는 사이트 생성이 실패하도록 되어 있다.

GitHub 공식 안내:

- [사용자 도메인 연결](https://docs.github.com/en/pages/configuring-a-custom-domain-for-your-github-pages-site/managing-a-custom-domain-for-your-github-pages-site)
- [도메인 소유 확인](https://docs.github.com/en/pages/configuring-a-custom-domain-for-your-github-pages-site/verifying-your-custom-domain-for-github-pages)

## 프록시를 켠 실제 연결

2026-10-21. 사용자가 Cloudflare 프록시를 켠 CNAME으로 연결했다. `https://lean.p4per.dev/`와 각 장, 브라우저 실행 스크립트의 HTTPS 응답을 확인했다. 이 연결의 방문자용 HTTPS는 Cloudflare가 제공한다.

DNS 전용은 초기 연결 확인을 위한 권장값이며 프록시 사용 자체를 금지하는 조건은 아니다. 다만 GitHub API상 원본 서버의 사용자 도메인 인증서는 아직 없으며, GitHub의 `https_enforced` 설정도 활성화할 수 없다. 방문자용 HTTPS 접속과 GitHub 자체 인증서 발급 상태를 구별하여 기록한다. Cloudflare의 실제 원본 연결 암호화 모드는 이 작업에서 변경하거나 확인하지 않았다.


## 사이트 기본 페이지와 교재 경로 분리

`lean.p4per.dev/`는 교재를 고르는 기본 페이지로 두고, 기초 수학 입문서는
`/foundations/` 아래에 배포한다. 장별 한 페이지 구성과 브라우저 Lean은 유지한다.
정적 사이트 준비 단계에서 경로를 나누므로 본문 원고의 상대 링크는 바꾸지 않는다.
기존 장 주소는 새 경로로 이동하며, 풀이 저장 식별자는 유지한다.
