#!/usr/bin/env bash
set -euo pipefail
ample_wasm_scripts="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
ample_wasm_root="${AMPLE_WASM_ROOT:-$HOME/.cache/ample-wasm}"
ample_wasm_source="$ample_wasm_root/lean4-4.35"
mkdir -p "$ample_wasm_root"
if [[ ! -d "$ample_wasm_source/.git" ]]; then
  git clone --depth 1 --branch v4.35.0 https://github.com/leanprover/lean4.git "$ample_wasm_source"
fi
python3 "$ample_wasm_scripts/prepare-toolchain.py" "$ample_wasm_source"
source "$ample_wasm_root/emsdk/emsdk_env.sh"
ample_wasm_emcc_version="$(emcc --version)"
if [[ "$ample_wasm_emcc_version" != *' 4.0.22 '* ]]; then
  printf '%s\n' 'This port is tested with Emscripten 4.0.22. Activate that SDK before building.' >&2
  exit 1
fi
export PKG_CONFIG_LIBDIR=/usr/lib/i386-linux-gnu/pkgconfig:/usr/share/pkgconfig
export NODE_OPTIONS=--max-old-space-size=8192
cd "$ample_wasm_source"
# Use Lean's make-based stdlib driver for this cross build. The 4.35 Lake
# bootstrap inherits host C flags (including x86 SSE flags) from stage0.
cmake -S . -B build/wasm \
  -DCMAKE_C_COMPILER_WORKS=1 \
  -DSTAGE0_USE_GMP=OFF -DSTAGE0_MMAP=OFF -DSTAGE0_USE_MIMALLOC=OFF \
  -DSTAGE0_LEAN_EXTRA_CXX_FLAGS='-m32 -msse2 -mfpmath=sse' \
  -DSTAGE0_LEANC_OPTS='-m32 -msse2 -mfpmath=sse' \
  -DSTAGE0_LEANC_EXTRA_CC_FLAGS='-m32 -msse2 -mfpmath=sse' \
  -DSTAGE0_LEAN_EXTRA_LINKER_FLAGS=-m32 \
  -DSTAGE0_CMAKE_CXX_COMPILER=clang++ -DSTAGE0_CMAKE_C_COMPILER=clang \
  -DSTAGE0_CMAKE_EXECUTABLE_SUFFIX='' \
  -DUSE_GMP=OFF -DMMAP=OFF -DUSE_MIMALLOC=OFF -DUSE_LAKE=OFF \
  -DCMAKE_AR="$EMSDK/upstream/emscripten/emar" \
  -DCMAKE_TOOLCHAIN_FILE="$EMSDK/upstream/emscripten/cmake/Modules/Platform/Emscripten.cmake" \
  -DSTAGE0_CMAKE_LIBRARY_PATH=/usr/lib/i386-linux-gnu/ \
  -DLEAN_INSTALL_SUFFIX=-linux_wasm32
cmake --build build/wasm --target stage1 --parallel "${AMPLE_WASM_JOBS:-6}"
python3 "$ample_wasm_scripts/optimize-runtime.py" build/wasm/stage1/bin/lean.js
node "$ample_wasm_scripts/runtime-tests.cjs" build/wasm/stage1/bin/lean.js
