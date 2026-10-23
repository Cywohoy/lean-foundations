/-
Copyright (c) 2024-2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
Modified for the Korean algebra textbook: module names and rendering configuration.
-/

import Std.Data.HashMap
import VersoManual
import VersoUtil.BinFiles
import AlgebraBook
import AlgebraBook.Meta.Playground
import AlgebraBook.Meta.ReaderCode

open Verso Doc
open Verso.Genre Manual

open Std (HashMap)

open AlgebraBook


-- Computes the path of this very `main`, to ensure that examples get names relative to it
open Lean Elab Term Command in
#eval show CommandElabM Unit from do
  let here := (← liftTermElabM (readThe Lean.Core.Context)).fileName
  elabCommand (← `(private def $(mkIdent `mainFileName) : System.FilePath := $(quote here)))

/--
Extract the marked exercises and example code.
-/
partial def buildExercises (mode : Mode) (cfg : Config) (_state : TraverseState) (text : Part Manual) : BuildLogT IO Unit := do
  let .multi := mode
    | pure ()
  let code := (← part text |>.run {}).snd
  let dest := cfg.destination / "example-code"
  let some mainDir := mainFileName.parent
    | throw <| IO.userError "Can't find directory of `Main.lean`"

  IO.FS.createDirAll <| dest
  let mut written : Array System.FilePath := #[]
  for ⟨fn, f⟩ in code do
    -- Make sure the path is relative to that of this one
    if let some fn' := fn.dropPrefix? mainDir.toString then
      let fn' := (fn'.dropWhile (· ∈ System.FilePath.pathSeparators)).copy
      let fn := dest / fn'
      if let some parent := fn.parent then IO.FS.createDirAll parent
      if (← fn.pathExists) then IO.FS.removeFile fn
      IO.FS.writeFile fn f
      written := written.push fn
    else
      reportError s!"Couldn't save example code. The path '{fn}' is not underneath '{mainDir}'."
  -- Moved document modules must not leave old exercise exports behind.
  for path in ← dest.walkDir do
    if path.extension == some "lean" && !written.contains path then
      IO.FS.removeFile path

where
  part : Part Manual → StateT (HashMap String String) (BuildLogT IO) Unit
    | .mk _ _ _ intro subParts => do
      for b in intro do block b
      for p in subParts do part p
  block : Block Manual → StateT (HashMap String String) (BuildLogT IO) Unit
    | .other which contents => do
      if which.name == ``Block.savedLean then
        let .arr #[.str fn, .str code] := which.data
          | reportError s!"Failed to deserialize saved Lean data {which.data}"
        modify fun saved =>
          saved.alter fn fun prior =>
            let prior := prior.getD ""
            some (prior ++ code ++ "\n")

      if which.name == ``Block.savedImport then
        let .arr #[.str fn, .str code] := which.data
          | reportError s!"Failed to deserialize saved Lean import data {which.data}"
        modify fun saved =>
          saved.alter fn fun prior =>
          let prior := prior.getD ""
          some (code.trimAsciiEnd.copy ++ "\n" ++ prior)

      for b in contents do block b
    | .concat bs | .blockquote bs =>
      for b in bs do block b
    | .ol _ lis | .ul lis =>
      for li in lis do
        for b in li.contents do block b
    | .dl dis =>
      for di in dis do
        for b in di.desc do block b
    | .para .. | .code .. => pure ()


/-- 본문의 절을 재배치한 뒤에도 이전 주소로 새 본문을 찾을 수 있게 한다. -/
def buildRedirects (mode : Mode) (cfg : Config) (_state : TraverseState)
    (_text : Part Manual) : BuildLogT IO Unit := do
  let .multi := mode | pure ()
  let root := cfg.destination / "html-multi"
  let foundations := root / "foundations"
  if ← foundations.pathExists then
    for page in ← foundations.walkDir do
      if page.fileName != some "index.html" then continue
      let some suffix := page.toString.dropPrefix? foundations.toString | continue
      let relative : System.FilePath :=
        (suffix.dropWhile (· ∈ System.FilePath.pathSeparators)).copy
      if !relative.isRelative || relative.components.contains ".." then continue
      if relative.components.length < 2 then continue
      let some parent := relative.parent | continue
      let url := "/foundations/" ++ parent.toString.replace "\\" "/" ++ "/"
      redirect root relative url
  for (old, url) in [
      ("foundations/introduction/explicit-and-implicit-arguments", "/foundations/using-proofs/named-theorems/#intro-explicit-and-implicit-arguments"),
      ("introduction/explicit-and-implicit-arguments", "/foundations/using-proofs/named-theorems/#intro-explicit-and-implicit-arguments"),
      ("foundations/introduction/pairs-and-currying", "/foundations/functions/products/#intro-pairs-and-currying"),
      ("introduction/pairs-and-currying", "/foundations/functions/products/#intro-pairs-and-currying"),
      ("foundations/using-proofs/successive-application", "/foundations/using-proofs/universal-statements/#proofs-successive-application"),
      ("using-proofs/successive-application", "/foundations/using-proofs/universal-statements/#proofs-successive-application"),
      ("foundations/functions/identity", "/foundations/functions/domain-and-codomain/#functions-identity"),
      ("functions/identity", "/foundations/functions/domain-and-codomain/#functions-identity"),
      ("foundations/introduction/propositions-and-goals", "/foundations/introduction/propositions-and-predicates/"),
      ("introduction/propositions-and-goals", "/foundations/introduction/propositions-and-predicates/"),
      ("foundations/introduction/predicates", "/foundations/introduction/propositions-and-predicates/#intro-predicates"),
      ("introduction/predicates", "/foundations/introduction/propositions-and-predicates/#intro-predicates"),
      ("foundations/introduction/predicates-and-propositions", "/foundations/introduction/propositions-and-predicates/#intro-predicates"),
      ("introduction/predicates-and-propositions", "/foundations/introduction/propositions-and-predicates/#intro-predicates"),
      ("foundations/preliminaries/products", "/foundations/functions/products/"),
      ("preliminaries/products", "/foundations/functions/products/"),
      ("foundations/preliminaries/equivalence-relations", "/foundations/relations/equivalence-relations/"),
      ("preliminaries/equivalence-relations", "/foundations/relations/equivalence-relations/"),
      ("foundations/cardinality/countable-sets", "/foundations/infinite-cardinality/countable-sets/"),
      ("foundations/cardinality/power-sets", "/foundations/infinite-cardinality/power-sets/"),
      ("cardinality/countable-sets", "/foundations/infinite-cardinality/countable-sets/"),
      ("cardinality/power-sets", "/foundations/infinite-cardinality/power-sets/"),
      ("cardinality/finite-sets/____________-___-______-______", "/foundations/cardinality/finite-sets/#cardinality-empty-and-singleton"),
      ("cardinality/finite-sets/____________-______-___-_________", "/foundations/cardinality/finite-sets/#cardinality-counting-three-elements"),
      ("cardinality/uniqueness/______-_________-______-___", "/foundations/cardinality/uniqueness/#cardinality-number-unique"),
      ("cardinality/elements", "/foundations/functions/elements/"),
      ("foundations/cardinality/elements", "/foundations/functions/elements/"),
      ("sets/universal-and-empty-sets", "/foundations/sets/sets-as-predicates/#sets-universal-and-empty-sets"),
      ("sets/differences", "/foundations/sets/complements-and-negation/#sets-differences"),
      ("function-composition", "/foundations/functions/"),
      ("function-composition/functions", "/foundations/functions/domain-and-codomain/"),
      ("function-composition/images-and-preimages", "/foundations/functions/images-and-preimages/"),
      ("function-composition/identity", "/foundations/functions/domain-and-codomain/#functions-identity"),
      ("function-composition/mapping-properties", "/foundations/functions/mapping-properties/"),
      ("function-composition/composition", "/foundations/functions/composition/"),
      ("function-composition/exercises", "/foundations/functions/exercises/")] do
    redirect root (old / "index.html") url
  -- Keep bookmarks to moved subsections working on pages that still exist.
  for (old, targets) in ([
      ("foundations/introduction/function-application", [
        ("intro-explicit-and-implicit-arguments", "/foundations/using-proofs/named-theorems/#intro-explicit-and-implicit-arguments"),
        ("intro-pairs-and-currying", "/foundations/functions/products/#intro-pairs-and-currying"),
        ("intro-argument-adapters", "/foundations/functions/products/#intro-argument-adapters")]),
      ("foundations/introduction/proof-values", [
        ("intro-pythagoras-theorems", "/foundations/using-proofs/naming-proofs/#intro-pythagoras-theorems"),
        ("intro-pythagoras-lean", "/foundations/using-proofs/naming-proofs/#intro-pythagoras-lean")]),
      ("foundations/using-proofs/propositions-and-proofs", [
        ("proofs-assumptions-and-goals", "/foundations/introduction/proof-values/#proofs-assumptions-and-goals")]),
      ("foundations/functions/elements", [
        ("functions-element-equality", "/foundations/functions/element-comparison/"),
        ("functions-fin", "/foundations/functions/element-comparison/#functions-fin"),
        ("functions-restriction", "/foundations/functions/restrictions/"),
        ("functions-codomain-image", "/foundations/functions/restrictions/#functions-codomain-image")]),
      ("foundations/functions/composition", [
        ("preliminaries-products", "/foundations/functions/products/"),
        ("functions-product-maps", "/foundations/functions/products/#functions-product-maps")]),
      ("foundations/preliminaries/divisibility", [
        ("preliminaries-even-induction", "/foundations/preliminaries/parity/"),
        ("preliminaries-double-image", "/foundations/preliminaries/parity/#preliminaries-double-image")]),
      ("foundations/relations/equivalence-relations", [
        ("preliminaries-equivalence-classes", "/foundations/relations/equivalence-classes/"),
        ("preliminaries-quotients", "/foundations/relations/quotients/"),
        ("preliminaries-quotient-functions", "/foundations/relations/quotients/#preliminaries-quotient-functions")]),
      ("foundations/cardinality/same-cardinality", [
        ("cardinality-quotient-type", "/foundations/cardinality/cardinals/")]),
      ("foundations/cardinality/finite-sets", [
        ("cardinality-fin-conversions", "/foundations/cardinality/finite-indices/"),
        ("cardinality-fin-values", "/foundations/cardinality/finite-indices/#cardinality-fin-values"),
        ("cardinality-fin-bounds", "/foundations/cardinality/finite-indices/#cardinality-fin-bounds"),
        ("cardinality-fin-equality", "/foundations/cardinality/finite-indices/#cardinality-fin-equality"),
        ("cardinality-fin-reference", "/foundations/cardinality/finite-indices/#cardinality-fin-reference")]),
      ("foundations/cardinality/uniqueness", [
        ("cardinality-natural-cardinals", "/foundations/cardinality/natural-cardinals/"),
        ("cardinality-natural-value", "/foundations/cardinality/natural-cardinals/#cardinality-natural-value")])] : List (String × List (String × String))) do
    let page := root / old / "index.html"
    if !(← page.pathExists) then continue
    let mapping := (Lean.Json.mkObj (targets.map fun (tag, url) => (tag, .str url))).compress
    let script := "<script>(()=>{const moved=" ++ mapping ++
      ";const target=moved[decodeURIComponent(location.hash.slice(1))];" ++
      "if(target)location.replace(new URL(target.slice(1),document.baseURI));})();</script>"
    let html ← IO.FS.readFile page
    IO.FS.writeFile page (html.replace "</head>" (script ++ "</head>"))
where
  redirect (root path : System.FilePath) (url : String) : IO Unit := do
    let target := root / path
    if let some parent := target.parent then IO.FS.createDirAll parent
    -- Resolve from this page, including when the book is hosted below a repository path.
    let rootPath := String.join (List.replicate (path.components.length - 1) "../")
    let url := rootPath ++ (url.dropWhile (· == '/')).copy
    let jsUrl := (Lean.Json.str url).compress
    let html := s!"<!doctype html><html lang=\"ko\"><head><meta charset=\"utf-8\"><meta http-equiv=\"refresh\" content=\"0;url={url}\"><link rel=\"canonical\" href=\"{url}\"><title>옮겨진 본문</title><script>const target={jsUrl};location.replace(target.includes('#') ? target : target+location.hash);</script></head><body><a href=\"{url}\">옮겨진 본문으로 이동</a></body></html>"
    IO.FS.writeFile target html

/-- Preserve subsection bookmarks when a whole learning unit shares one page. -/
def buildReadingRedirects (mode : Mode) (cfg : Config) (_state : TraverseState)
    (_text : Part Manual) : BuildLogT IO Unit := do
  let .multi := mode | pure ()
  let root := cfg.destination / "html-multi"
  let project := mainFileName.parent.getD "."
  let parse (path : System.FilePath) : IO Lean.Json := do
    match Lean.Json.parse (← IO.FS.readFile path) with
    | .ok json => pure json
    | .error error => throw <| IO.userError s!"{path}: {error}"
  let history ← parse (project / "web/reading-redirects.json")
  let xrefs ← parse (root / "xref.json")
  let .ok sections := (do
    let domain ← xrefs.getObjVal? "Verso.Genre.Manual.section"
    (← domain.getObjVal? "contents").getObj?)
    | throw <| IO.userError "Missing section references"
  let mut destinations : List (String × Lean.Json) := []
  for (tag, entries) in sections.toArray do
    let .ok entries := entries.getArr? | continue
    let some entry := entries[0]? | continue
    let .ok address := entry.getObjValAs? String "address" | continue
    let .ok id := entry.getObjValAs? String "id" | continue
    destinations := (tag, .str (address ++ "#" ++ id)) :: destinations
  let targets := Lean.Json.mkObj destinations
  let .ok routes := history.getObj? | throw <| IO.userError "Invalid reading redirects"
  for (old, tag) in routes.toArray do
    let .ok tag := tag.getStr? | continue
    let .ok target := targets.getObjValAs? String tag
      | throw <| IO.userError s!"Missing destination for historical section {tag}"
    -- A retained page must never be replaced by a redirect.
    if destinations.any (fun (_, value) =>
        value.getStr?.toOption.any (fun url => url.startsWith ("/" ++ old ++ "/#"))) then
      continue
    let path : System.FilePath := old / "index.html"
    let output := root / path
    if let some parent := output.parent then IO.FS.createDirAll parent
    let rootPrefix := String.join (List.replicate (path.components.length - 1) "../")
    let fallback := rootPrefix ++ (target.dropWhile (· == '/')).copy
    let jsPrefix := (Lean.Json.str rootPrefix).compress
    let jsTarget := (Lean.Json.str target).compress
    let script := "const targets=" ++ targets.compress ++ ";const fallback=" ++ jsTarget ++
      ";const hash=location.hash;let tag='';try{tag=decodeURIComponent(hash.slice(1));}catch{}" ++
      "const target=targets[tag]||(hash?fallback.split('#')[0]+hash:fallback);" ++
      "location.replace(" ++ jsPrefix ++ "+target.slice(1));"
    IO.FS.writeFile output s!"<!doctype html><html lang=\"ko\"><head><meta charset=\"utf-8\"><title>옮겨진 본문</title><script>{script}</script><noscript><meta http-equiv=\"refresh\" content=\"0;url={fallback}\"></noscript><link rel=\"canonical\" href=\"{fallback}\"></head><body><a href=\"{fallback}\">본문으로 이동</a></body></html>"

def config : RenderConfig where
  emitTeX := false
  emitHtmlSingle := .no
  emitHtmlMulti := .immediately
  htmlDepth := 1
  extraDataFiles := {
    { filename := "PretendardVariable.woff2",
      contents := include_bin "assets/fonts/PretendardVariable.woff2" },
    { filename := "NanumSquareNeo-Bold.woff2",
      contents := include_bin "assets/fonts/NanumSquareNeo-Bold.woff2" },
    { filename := "NanumSquareNeo-ExtraBold.woff2",
      contents := include_bin "assets/fonts/NanumSquareNeo-ExtraBold.woff2" },
    { filename := "CascadiaCode.woff2",
      contents := include_bin "assets/fonts/CascadiaCode.woff2" },
    { filename := "CascadiaCodeItalic.woff2",
      contents := include_bin "assets/fonts/CascadiaCodeItalic.woff2" },
    { filename := "NotoSansMath-Regular.woff2",
      contents := include_bin "assets/fonts/NotoSansMath-Regular.woff2" },
    { filename := "BookQuotientSymbols-Cascadia.woff2",
      contents := include_bin "assets/fonts/BookQuotientSymbols-Cascadia.woff2" }
  }
  extraCssFiles := {
    { filename := "typography.css",
      contents := .mk r#"
        @font-face {
          font-family: "Pretendard Variable";
          font-style: normal;
          font-weight: 45 920;
          font-display: swap;
          src: url("PretendardVariable.woff2") format("woff2");
        }
        @font-face {
          font-family: "NanumSquareNeo";
          font-style: normal;
          font-weight: 700;
          font-display: block;
          src: url("NanumSquareNeo-Bold.woff2") format("woff2");
        }
        @font-face {
          font-family: "NanumSquareNeo";
          font-style: normal;
          font-weight: 800;
          font-display: block;
          src: url("NanumSquareNeo-ExtraBold.woff2") format("woff2");
        }
        @font-face {
          font-family: "Cascadia Code";
          font-style: normal;
          font-weight: 200 700;
          font-display: swap;
          src: url("CascadiaCode.woff2") format("woff2");
        }
        @font-face {
          font-family: "Cascadia Code";
          font-style: italic;
          font-weight: 200 700;
          font-display: swap;
          src: url("CascadiaCodeItalic.woff2") format("woff2");
        }
        @font-face {
          font-family: "Noto Sans Math";
          font-style: normal;
          font-weight: 400;
          font-display: swap;
          src: url("NotoSansMath-Regular.woff2") format("woff2");
          size-adjust: 110%;
          unicode-range: U+00AC, U+00B1, U+00D7, U+00F7,
            U+2190-22FF, U+27C0-27E5, U+27E8-27FF, U+2900-2AFF;
        }
        @font-face {
          font-family: "Book Quotient Symbols";
          font-style: normal;
          font-weight: 400;
          font-display: swap;
          src: url("BookQuotientSymbols-Cascadia.woff2") format("woff2");
          unicode-range: U+27E6-27E7;
        }
      "# }
  }
  extraCss := { .mk r#"
    :root {
      --verso-text-font-family: "Pretendard Variable", "Malgun Gothic", system-ui, sans-serif;
      --verso-structure-font-family: "Pretendard Variable", "Malgun Gothic", system-ui, sans-serif;
      --verso-code-font-family: "Book Quotient Symbols", "Noto Sans Math", "Cascadia Code", "Pretendard Variable", Consolas, monospace;
    }
    p, dt, dd, main li { line-height: 1.9; }
    h1, h2, h3, h4, h5, h6 { font-family: "NanumSquareNeo", var(--verso-structure-font-family); }
    .hl.lean.block, pre, .lean-output { line-height: 1.85; }
    .hl.lean.block { padding-block: 0.45em; }
    .hl.lean .tactic > label[for]::after { display: none; }
    .hl.lean .tactic > label[for] { cursor: pointer; }
    .hl.lean .tactic:has(> .tactic-toggle:checked) > label[for] {
      background-color: var(--verso-code-hover-bg-color, #eeeeee);
      border-radius: 0.15em;
    }
    .hl.lean .tactic:has(> .tactic-toggle:focus-visible) > label[for] {
      outline: 2px solid currentColor;
      outline-offset: 2px;
    }
    .toc-title h1 { word-break: keep-all; }
    @media screen and (max-width: 1200px) {
      .toc-title { display: block; }
      .header-title { display: none; }
    }
  "# }

def main (args : List String) : IO UInt32 := do
  -- Read reader assets at generation time so CSS/JS edits never use an old compiled copy.
  let project := mainFileName.parent.getD "."
  let css ← IO.FS.readFile (project / "assets/web/reader.css")
  let js ← IO.FS.readFile (project / "assets/web/reader.js")
  let themeCss ← IO.FS.readFile (project / "assets/web/theme.css")
  let themeJs ← IO.FS.readFile (project / "assets/web/theme.js")
  let current := { config with
    extraCssFiles := (config.extraCssFiles.insert {
      filename := "reader.css", contents := .mk css }).insert {
      filename := "theme.css", contents := .mk themeCss }
    extraJsFiles := (config.extraJsFiles.insert {
      filename := "reader.js", contents := .mk js, defer := true, sourceMap? := none }).insert {
      filename := "theme.js", contents := .mk themeJs, defer := false, sourceMap? := none } }
  manualMain (readerCodeBlocks (%doc AlgebraBook))
    (options := args)
    (extraSteps := [buildExercises, buildPlaygrounds, buildReadingRedirects]) (config := current)
