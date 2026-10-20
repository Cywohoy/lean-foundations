# Lean Unicode input

Unmodified runtime sources and abbreviation table from `@leanprover/unicode-input` 0.1.12, the package used by Lean VS Code extension 0.0.240. The bundled extension and this table have identical 1857 mappings.

Upstream: https://github.com/leanprover/vscode-lean4

License: Apache-2.0 (see `LICENSE`). Package provenance and integrity are in `SOURCE.json`.

Run `python scripts/build_unicode_input.py` to regenerate the browser ES module from these pinned files. No package manager or network access is required for a normal book build. Textarea adaptation is separate in `assets/web/unicode-input.js`; the upstream matching, eager replacement, and cursor-marker rules are unchanged.
