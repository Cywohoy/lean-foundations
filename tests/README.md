# Verification

Run from the project root.

```text
lake exe textbook
python scripts/exercise_templates.py
python tests/check_book.py
python tests/check_lean.py
```

After compiling and staging the current browser contexts as described in
`../experiments/wasm/README.md`:

```text
python tests/Pages.Tests.py
python tests/Preview.Tests.py
node tests/ExerciseModel.Tests.cjs
node tests/UnicodeTable.Tests.cjs
node tests/UnicodeInput.Tests.cjs
node tests/PagesReader.Tests.cjs
node tests/ExerciseCoverage.Tests.cjs
node tests/BrowserReader.Tests.cjs
```

The browser tests require Playwright and Chrome. Do not regenerate the staged
site while a test is serving it. `BrowserReader.Tests.cjs` accepts `BOOK_SITE`
to serve an independent copy of the staged directory.

`ExerciseCoverage` checks every exercise in its exact preceding context.
`BrowserReader` checks editing, completion, admitted dependencies, persistence,
errors, and recovery. Worked examples have static proof states; browser
compilation is exposed through exercises.

On Windows, `./tests/ResetExercises.Tests.ps1` checks reset and backup behavior
inside a temporary test directory. It never resets personal worksheets.

Library tactic regressions belong to Ample. Obsolete copies of the former
textbook's structural tests are retained in that original repository, rather
than being presented as tests of this four-chapter book.
