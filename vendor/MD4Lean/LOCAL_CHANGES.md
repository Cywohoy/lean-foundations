# Windows 호환성 수정

- 원본: <https://github.com/acmepjz/md4lean>
- 원본 커밋: `31907cc18f48a95384f99cee5582c00fb39e0f67`
- 원본 라이선스는 `LICENSE`에 보존한다.

`wrapper/wrapper.c`에서 Markdown 파싱 및 HTML 변환 함수 두 개를
Windows DLL의 공개 함수로 명시한다.
기존 `LEAN_EXPORT`는 `LEAN_EXPORTING`이 없으면 빈 매크로이므로,
Lean 생성 코드가 공개 함수를 명시한 DLL에서는 이 두 함수의 자동 공개가 생략된다.
그 결과 VersoManual DLL의 연결 단계에서 `lean_md4c_markdown_parse`를 찾지 못한다.

Windows에서는 두 함수에 `__declspec(dllexport)`를 적용한다.
다른 운영체제에서는 원래의 `LEAN_EXPORT`를 그대로 사용한다.
수학적 정의나 증명은 변경하지 않는다.
