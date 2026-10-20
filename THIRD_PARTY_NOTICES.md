# 외부 구성 요소

`Main.lean`의 예제 추출 단계와 `AlgebraBook/Meta/Lean.lean`은
[Verso 공식 textbook 템플릿 v4.35.0](https://github.com/leanprover/verso-templates/tree/v4.35.0/textbook)을 바탕으로 수정했습니다.

Copyright (c) 2024–2025 Lean FRO LLC. Author: David Thrane Christiansen.
해당 코드의 라이선스는 Apache License 2.0이며,
원문의 저작권 표시와 [라이선스 사본](licenses/Apache-2.0.txt)을 보존합니다.

한국어 설명과 함수 예제는 이 프로젝트를 위해 작성했으며 교재 원문을 전재하지 않았습니다.
Verso, Batteries와 그 의존 패키지는 각 패키지의 라이선스를 따릅니다.

교재에서 사용하는 전술 구현은 독립 패키지 Ample의 `Ample/Tactic/`에서 제공한다.
Lean과 mathlib에서 수정하여 가져온 전술의 저작권 표시와 라이선스는
[Ample의 외부 구성 요소 안내](https://github.com/Cywohoy/ample/blob/main/THIRD_PARTY_NOTICES.md)에 정리했다.

`vendor/MD4Lean`은 MD4Lean의 원본 커밋
`31907cc18f48a95384f99cee5582c00fb39e0f67`을 포함한다.
Windows에서 필요한 함수 공개 표시만 수정했다.
자세한 변경 내역은 `vendor/MD4Lean/LOCAL_CHANGES.md`에,
라이선스는 `vendor/MD4Lean/LICENSE`에 보존한다.

`assets/fonts/PretendardVariable.woff2`는 [Pretendard v1.3.9](https://github.com/orioncactus/pretendard/tree/v1.3.9)의
수정하지 않은 가변 글꼴이다. SIL Open Font License 1.1의 사본을
`licenses/Pretendard-OFL.txt`에 보존한다.

`assets/fonts/CascadiaCode.woff2`와 `CascadiaCodeItalic.woff2`는
[Microsoft Cascadia Code v2407.24](https://github.com/microsoft/cascadia-code/releases/tag/v2407.24)의
수정하지 않은 가변 웹폰트이다. 원본 저작권 표시와 SIL Open Font License 1.1의 사본을
`licenses/CascadiaCode-OFL.txt`에 보존한다.

`assets/fonts/NotoSansMath-Regular.woff2`는
[Noto Sans Math v3.000](https://github.com/notofonts/math/releases/tag/NotoSansMath-v3.000)의
[공식 OTF 파일](https://notofonts.github.io/math/fonts/NotoSansMath/full/otf/NotoSansMath-Regular.otf)을
WOFF2 형식으로 변환한 웹폰트이다. 글자 모양과 폭은 수정하지 않았다.
원본 저작권 표시와 SIL Open Font License 1.1의 사본을
`licenses/NotoSansMath-OFL.txt`에 보존한다.

`assets/fonts/pdf/`에는 위의 웹폰트를 PDF 조판에 사용할 수 있도록 SFNT 형식으로 변환한 글꼴을 둔다.
Pretendard와 Cascadia Code는 가변 글꼴에서 굵기 400과 700을 선택한 정적 인스턴스이며,
Noto Sans Math는 원래의 OTF 형식으로 저장했다.
별도의 글자 모양 수정은 하지 않았으며, 위에 명시한 각 글꼴의 저작권과 SIL Open Font License 1.1이 그대로 적용된다.

`assets/fonts/BookQuotientSymbols-Cascadia.woff2` is a derivative of the above
Cascadia Code font under the same SIL Open Font License 1.1. It contains only
U+27E6 and U+27E7, built from its regular-weight square brackets with shortened
horizontal arms and paired components. The source TrueType instructions are
retained, and the component offsets use pixel-grid rounding. The family and
PostScript names are changed to Book Quotient Symbols. Copyright and license
records are retained in the font; `licenses/CascadiaCode-OFL.txt` also applies.
`web/build_quotient_font.py` reproduces it from the bundled source font using
fonttools[woff]. This font is used only for the quotient brackets; the rest of
the code continues to use the original code and math fonts.

The optional browser experiment in `experiments/wasm/` includes a patch against
[Lean 4.35.0](https://github.com/leanprover/lean4/tree/v4.35.0), based in part on
the browser port in [cauli/lean4](https://github.com/cauli/lean4) at commit
`dfe4953168`. Lean and the port are distributed under Apache-2.0; the license is
preserved in `licenses/Apache-2.0.txt`, and the original file headers remain in
the patched source checkout. Local changes include the 4.35 adaptation, correct
32-bit exit-code decoding, an export table generated from the matching build,
and cursor-goal queries. The experiment uses the upstream browser Worker and
COI Service Worker from pinned external checkouts; their license notices and
pins are recorded in `experiments/wasm/README.md`. Those Worker assets are not
included in the published book.

The static Pages build serves Verso's existing marked 11.1.1 dependency from
`assets/web/marked.min.js`, with the original SHA-384 integrity value retained.
It is copied without modification from the version pinned by Verso; its MIT
copyright and license are preserved in `licenses/Marked-MIT.txt`. Serving this
file locally avoids a third-party script request in the isolated browser editor.

## SubVerso

`vendor/subverso` contains SubVerso at revision
`892d6dc520270b5fb8c1291dd1b131e8c16255ed`, from
https://github.com/leanprover/subverso, under its included Apache-2.0 license.
The local nested-proof highlighting fix is documented in
`vendor/subverso/TEXTBOOK-PATCH.md`. Original copyright notices are preserved.
