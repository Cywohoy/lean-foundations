# Browser Lean runtime

This directory contains the Lean 4.35 WASM toolchain build, browser frontend
tests, and a standalone test host. The book uses the same runtime in its
exercise editor. See [deployment](../../DEPLOYMENT.md) for publishing and
[test guidance](../../tests/README.md) for book-level checks.

## Four-chapter book contexts

Build the manuscript with `lake exe textbook` first. From this project root,
using the matching native wasm32 compiler and Ample library:

```bash
python3 scripts/build_browser_book.py \
  --lean "$AMPLE_WASM_ROOT/lean4-4.35/build/wasm/stage0/bin/lean" \
  --ample-lib "$AMPLE_WASM_ROOT/ample-4.35/lib/lean" \
  --output "$AMPLE_WASM_ROOT/foundations-contexts"
python3 scripts/bundle_book_contexts.py \
  --base path/to/the-pinned-base-runtime.tar.gz \
  --contexts "$AMPLE_WASM_ROOT/foundations-contexts" \
  --output tmp/wasm/foundations-browser.tar.gz \
  --config web/wasm-runtime.local.json
python3 scripts/prepare_pages.py --runtime-config web/wasm-runtime.local.json
```

The base runtime URL and checksum are in `web/wasm-base-runtime.json`.
The published book runtime, including the checked exercise contexts, is pinned in
`web/wasm-runtime.json`. Use `--url` when bundling to set the resulting runtime URL. This workflow
preserves that runtime and replaces the book contexts. It does not import
modules from the previous textbook checkout. Staging rejects a bundle whose
contexts do not match the current exercise prefixes.

## Runtime background

This experiment runs Lean inside a browser Web Worker. The HTTP server only
serves static files; proof text is never submitted to a compiler server. The
same transport is used by the published textbook's browser editor; its normal
native Lean toolchain remains available for local preview and authoring.

## Frontend and runtime constraints

The frontend uses Lean's info trees and `InfoTree.goalsAt?`, rather than guessing
goals from diagnostics. Coordinates are zero-based UTF-16, as in LSP. Environment
caches distinguish ordinary files from `module` files and retain full import
specifications. Treating an ordinary Ample import as a `module` import would
be rejected by Lean 4.35.

Failed searches must return Lean diagnostics rather than terminate the Worker.
Lean 4.35's `grind` retains native stack frames in its continuation-based search
loop. The browser port limits that loop to 16 nested continuations, separately
from Lean's ordinary recursion limit. This leaves normalization, arithmetic
solvers, and proof checking at their normal limits. Reaching the search limit
returns a stuck goal and an English diagnostic; it does not accept a proof.
Native Lean keeps the original search budget. Deep browser searches can therefore
need an intermediate fact sooner than the native toolchain.

`tests/BrowserReader.Tests.cjs` covers repeated failed `arith` searches in the
arithmetic-progression exercise, the original `suffices ... by arith` failure,
the remaining goal, and a corrected proof in the same Worker. It also checks
successful polynomial, product-bound, division, and divisibility calculations.

Library data is split into gzip packs with SHA-256 and decoded-size checks.
Only Init is loaded at startup; the remaining libraries are loaded on the first
explicit import. This version does not compute a minimal closure per import.

`optimize-runtime.py` defers Emscripten's export enumeration until registering a
new table function for pthread catch-up, avoiding repeated work at boot. It
preserves the index protocol and does not assume that exports never change.
Unexpected SDK output fails the transform rather than receiving a guessed edit.
`runtime-tests.cjs` checks missing, non-enumerable, inherited, stub, data, existing,
new, and subsequently appended exports against the actual generated function.

The upstream Worker reserves 2 GiB of shared WASM memory on desktop. This is a
virtual-memory configuration, not a resident-RAM measurement. Mobile behavior
and memory exhaustion have not been validated. Some LibUV networking functions
are unavailable; these proofs do not establish support for arbitrary OS or
network APIs.

The adapter rechecks the entire file and caches imported environments. The
browser transport replaces its worker before importing a fifth distinct header
import set: Lean's retained compact regions otherwise accumulate as readers
move between partial exercise contexts on a continuous page. Checked context
files are restored from verified in-memory copies, and the editor keeps its
source and saved work. Repeated checks with the same imports reuse the worker.
It does not implement incremental LSP sessions, completion, hover, or interruption.
The remaining work includes smaller downloads,
persistent caching, mobile profiling, and the remaining editor interfaces.

The browser build uses `EXIT_RUNTIME=0`: the Worker owns the runtime lifetime.
With CLI-style cleanup enabled, a pthread mailbox callback could close standard
output between a successful compilation and the next goal query.
`tests/BrowserReader.Tests.cjs` covers successive requests through the real reader.
The runtime is distributed as a checksum-pinned release archive; binaries stay
outside Git. `scripts/build_wasm_bundle.py` includes build metadata and licenses.
`scripts/prepare_pages.py --download-wasm` stages a content-specific runtime path
and translates book-only imports. The published reader loads it on first edit.
Both the local textbook preview and public reader use WASM. Completion is not yet provided.

## Reproduce the matching build

The tested environment is x86 Linux in WSL, with a native 32-bit bootstrap and
Emscripten **4.0.22**. Keep the build cache on the Linux filesystem. Generated
artifacts belong in the isolated cache and ignored `tmp/wasm/`, not Ample's
normal Lake output. Expect a large build and several gigabytes of temporary
files.

On the tested Ubuntu installation the native dependencies were `build-essential`,
`clang`, `cmake`, `ninja-build`, `gcc-multilib`, `g++-multilib`,
`libuv1-dev:i386`, `libssl-dev:i386`, `pkg-config`, `python3`, `git`, `curl`,
`ca-certificates`, `xz-utils`, and `zstd`, with i386 enabled. Browser checks need
Node.js, Playwright, and desktop Chrome; build scripts need Python 3.10 or newer.
Run from the project root in Linux/WSL. The sibling Ample checkout should match the book's
pinned Ample version.

```bash
export AMPLE_WASM_ROOT="$HOME/.cache/ample-wasm"
mkdir -p "$AMPLE_WASM_ROOT"
git clone https://github.com/emscripten-core/emsdk.git "$AMPLE_WASM_ROOT/emsdk"
git -C "$AMPLE_WASM_ROOT/emsdk" checkout 3b3963d86a5c97adaf6eaa845cdfe0b811c2f960
"$AMPLE_WASM_ROOT/emsdk/emsdk" install 4.0.22
"$AMPLE_WASM_ROOT/emsdk/emsdk" activate 4.0.22
bash experiments/wasm/build-toolchain.sh

LEAN_SOURCE="$AMPLE_WASM_ROOT/lean4-4.35"
python3 experiments/wasm/build-ample.py \
  --lean "$LEAN_SOURCE/build/wasm/stage0/bin/lean" \
  --lean-lib "$LEAN_SOURCE/build/wasm/stage1/lib/lean" \
  --ample ../Ample --output "$AMPLE_WASM_ROOT/ample-4.35/lib/lean"
python3 experiments/wasm/verify-native.py \
  --lean "$LEAN_SOURCE/build/wasm/stage0/bin/lean" \
  --lean-lib "$LEAN_SOURCE/build/wasm/stage1/lib/lean" \
  --ample ../Ample --output "$AMPLE_WASM_ROOT/ample-4.35/lib/lean"
python3 experiments/wasm/pack-library.py \
  --lean-lib "$LEAN_SOURCE/build/wasm/stage1/lib/lean" \
  --ample-lib "$AMPLE_WASM_ROOT/ample-4.35/lib/lean" \
  --output tmp/wasm/packs435
```

`build-toolchain.sh` checks the official Lean base commit, applies the port
without resetting other files, installs the frontend, and builds the native
32-bit bootstrap and WASM stage1. It uses the make-based stdlib driver because
this cross build's Lake bootstrap inherits host C flags. `generate-exports.py`
derives C exports from the actual linked libraries, including ordinary, runtime,
and meta initializers. Keeping those initializers avoids duplicate environment
extension registration. The current export set is conservative, not minimal.
The build then applies the deferred-index transform to generated glue and runs
its focused runtime tests. The Emscripten checkout itself is not modified.

Fetch the pinned browser hosts. The matching build needs no old binary fixture:

```bash
git clone https://github.com/cauli/lean4-wasm-in-browser.git tmp/wasm/upstream
git -C tmp/wasm/upstream checkout 017c835ecf0ac8c74745a867c65faeac0baf6654
git clone https://github.com/gzuidhof/coi-serviceworker.git tmp/wasm/coi-serviceworker
git -C tmp/wasm/coi-serviceworker checkout 7b1d2a092d0d2dd2b7270b6f12f13605de26f214

export LEAN_WASM_ARTIFACTS="$LEAN_SOURCE/build/wasm/stage1"
export AMPLE_WASM_LIBRARY="$AMPLE_WASM_ROOT/ample-4.35/lib/lean"
export LEAN_WASM_PACKS="$(pwd)/tmp/wasm/packs435"
node experiments/wasm/browser-tests.cjs --matching-toolchain
node experiments/wasm/browser-tests.cjs --matching-toolchain --service-worker
node experiments/wasm/server.cjs
```

The last command prints a local URL. Press **Start Lean**. Edits are checked
automatically, and clicking in a proof queries its goals. **Check proof** triggers
an immediate check. If Node runs on Windows with Linux build artifacts, use
corresponding `\\wsl.localhost\Ubuntu\...` paths for artifact/library variables.
`LEAN_WASM_RUNTIME` can point to local copies of `lean.js` and `lean.wasm`;
otherwise the server reads the build's `bin/`.

The frontend can also be tested with the book's ordinary native toolchain:

```text
lake build Ample
python experiments/wasm/Frontend.Tests.py
```

Reports are saved to `tmp/wasm/browser-results-435.json` and
`browser-results-435-sw.json`; build records and native regression reports go
beside the isolated Ample library. Browser reports include sources, diagnostics,
timings, and browser version. HTTP proof submission fails the test.
`--project-path` tests under `/lean-algebra/wasm/`.
`--profile-boot --boot-only` records a Chrome Worker CPU profile and boot report
without the full proof suite.

## Pins and licenses

- [Lean 4.35.0](https://github.com/leanprover/lean4/tree/v4.35.0), base commit
  `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`, Apache-2.0.
- [cauli's browser port](https://github.com/cauli/lean4), based on changes between
  `ecf55de08b9d855e749f80c491c6f294dd307e60` and `dfe4953168`, adapted in
  `patches/lean4-4.35.patch`, Apache-2.0.
- [Browser Worker](https://github.com/cauli/lean4-wasm-in-browser), commit
  `017c835ecf0ac8c74745a867c65faeac0baf6654`, Apache-2.0. Its historical fixture
  pins Lean `62b6a2291302d4bbeace37642a066b7510d0145c` and Emscripten 4.0.22.
- [COI Service Worker](https://github.com/gzuidhof/coi-serviceworker), commit
  `7b1d2a092d0d2dd2b7270b6f12f13605de26f214`, MIT.
- [Emscripten SDK](https://github.com/emscripten-core/emsdk), commit
  `3b3963d86a5c97adaf6eaa845cdfe0b811c2f960`, SDK 4.0.22.

The port keeps the source's notices; `licenses/Apache-2.0.txt` preserves the
license. Worker scripts are served from pinned external checkouts without
copying them into this repository. Retain their notices and licenses when
packaging assets for deployment.
