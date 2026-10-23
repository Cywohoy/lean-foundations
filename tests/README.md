# Verification

Select checks through R6 of the [review process](../REVIEW_PROCESS.md). This is
an execution catalogue, not a substitute for reading the manuscript or solving
its exercises. Run commands from this project root and record the relevant
source, dependency, runtime and curriculum-policy versions.

Use the review hierarchy to distinguish the writable scope from the material
read for context. Track affected checks in [the review state](../REVIEW_STATE.md).
A passing check clears only its recorded scope and input version; it does not
clear prose, pedagogy, or dependency reviews. Compare the final diff against the
pre-edit baseline and writable scope, preserving unrelated existing changes.

## Select by change

| Change | Required verification | What it does not establish |
|---|---|---|
| Review instructions or other developer documentation only | Read for contradictions; check changed links and examples of process selection; inspect the diff | The textbook has been re-reviewed |
| Textbook prose or code layout | Build the book, regenerate templates, run the core checks below; inspect the changed rendered passage | Its explanation is understandable without R2/R3 |
| Definition, theorem, proof, exercise or declaration order | Core checks; current exercise contexts; affected solved exercises; curriculum and reference checks | Compiling `sorry` templates does not establish solvability |
| Exercise wording, hint or educational placement | R4/R5 on the affected problems and dependent problems; core checks; update contexts/policy when their inputs changed | An unchanged Lean statement does not imply an unchanged learning experience |
| Tactic implementation, registration or automatic normalization | Ample's independent tests; affected proof states and exercises; native and browser execution; diagnostics and recovery | Native success alone does not establish WASM success |
| Reader, editor or layout | Relevant UI/model tests, actual affected reading/editing flow, narrow-screen checks | Fixture tests alone do not establish the real WASM flow |

Keep checks whose inputs remain identical and record that reuse. Rebuild the
browser contexts when exported code or exercise prefixes change. Reuse a
matching context bundle for prose-only edits; staging verifies prefix identity.
Do not repeatedly rebuild or re-solve unaffected material without a reason.

## Review manager

For changes to review state or the local management UI:

```text
python tests/ReviewState.Tests.py
node tests/ReviewWeb.Tests.cjs
```

These use temporary Git repositories and open no listening port. The browser
suite intercepts requests and calls the real state engine. It covers stale
review rejection, evidence retention, independent review aspects, dependencies,
scope violations, range registration, and desktop/mobile layout. Set `PYTHON`
and `CHROME_PATH` if needed. The Python suite also exercises HTTP origin/token
checks directly without starting the HTTP server. These checks validate the
management tool; they do not review or compile the textbook.

## Core manuscript checks

```text
lake exe textbook
python scripts/exercise_templates.py
python tests/check_book.py
python tests/check_lean.py
```

These check generated documents, structure, exported code and templates.
Templates intentionally contain unfinished proofs. `check_lean.py` checks that
personal worksheets are unchanged; it does not solve their exercises.

For changes to introduction order, exercise dependencies or theorem lookup:

```text
python tests/LearningPolicy.Tests.py
python tests/TheoremCatalog.Tests.py
node tests/ExerciseContext.Tests.cjs
```

`LearningPolicy` checks declared curriculum boundaries and tactic restrictions.
It cannot judge whether the preceding explanation actually teaches a needed
idea. `ExerciseContext` tests dependency selection, including earlier exercise
results; R4 must still compile the actual solved chain.

## Exercise solutions and browser contexts

Follow [the context build instructions](../experiments/wasm/README.md) with the
matching wasm32 compiler and Ample library, then stage the current site.
Changing the Ample source requires a matching library/runtime, not just new
book contexts. Keep local development overrides separate from published pins.

For R4, retain the solved source, the exact preceding context, the applicable
tactic policy, dependency proofs and execution result for every selected
subproblem. Earlier exercise results must use their completed proofs. Check
axiom dependencies so that `sorryAx` in an earlier result cannot pass as a
completed solution. Do not edit personal `Exercises/` files.

There is currently no single committed command that independently solves all
exercises and evaluates their pedagogical quality. In particular,
`ExerciseCoverage.Tests.cjs` checks all exercise **skeletons** in WASM, their
initial goals and admitted-proof reporting. It does not supply completed
solutions. Do not report its success as “all exercises solved.”

## Static output and fixture checks

After staging the matching site, select the relevant checks:

```text
python tests/Pages.Tests.py
node tests/ReaderSteps.Tests.cjs
node tests/ExerciseModel.Tests.cjs
node tests/ExerciseContext.Tests.cjs
node tests/ExerciseProgress.Tests.cjs
node tests/BackgroundRecheck.Tests.cjs
node tests/UnicodeTable.Tests.cjs
node tests/MobileLayout.Tests.cjs
```

`ReaderSteps` checks worked-example states, including nested proof transitions.
The model/progress fixtures check state handling rather than a live compiler.
`MobileLayout` checks reading layouts at narrow widths. These checks do not
start an HTTP server. Browser-based fixtures require Playwright and Chrome.

On Windows, `./tests/ResetExercises.Tests.ps1` checks reset and backup behavior
inside a temporary test directory. It never resets personal worksheets.

## Existing-server browser checks

The user manages local servers. Do not start, stop or restart one for review.
If the user's server is available, set `BOOK_URL` to its actual book URL before
running either command below. For example, in PowerShell:

```powershell
$env:BOOK_URL = 'http://127.0.0.1:8000/foundations/'
node tests/BrowserReader.Tests.cjs
node tests/BrowserDiagnostics.Tests.cjs
```

With `BOOK_URL`, `BrowserReader` does not listen on a new port. `BrowserDiagnostics`
also uses an existing URL. Check that the served pages/runtime match the current
staged output; do not regenerate that output during a test. Use an isolated
browser test profile so the user's saved work is not changed.

`BrowserReader` covers real editing, completion, admitted dependencies,
persistence, errors and recovery for selected examples. `BrowserDiagnostics`
covers error display and recovery, including failures inside `have`. The native
diagnostic check is `python tests/BrowserDiagnostics.Tests.py` and is separate
from the browser check.

The following scripts currently open their own listener, **even when some of
them accept `BOOK_URL`**:

- `PagesReader.Tests.cjs`
- `ExerciseCoverage.Tests.cjs`
- `BrowserLearningPolicy.Tests.cjs`
- `UnicodeInput.Tests.cjs`
- `Portal.Tests.cjs`
- the server-based test in `Preview.Tests.py`

Do not run those unchanged under the current server instruction. Use the
existing-server path only after adapting and checking the test, or record the
unverified coverage. `BOOK_SITE` selects files; it is not a no-server option.
If no server is available, perform the applicable non-server checks and report
the browser checks as unverified instead of starting one.

Library tactic regressions belong to Ample and follow that repository's own
instructions. PDF output and public deployment require a separate explicit
request and are not consequences of passing these checks.

`node tests/Theme.Tests.cjs` checks the staged portal and all reading pages with
in-memory browser routes (no listener). It covers system/light/dark selection,
first-content timing, persistence, cross-tab changes, blocked storage, contrast,
narrow screens, keyboard focus, proof steps and light print colors. For a real
Lean exercise run with dark colors, set `BOOK_THEME=dark` when running
`BrowserDiagnostics.Tests.cjs` against the existing preview URL.
