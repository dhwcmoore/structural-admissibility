#!/usr/bin/env bash
# build_all.sh — build Rocq proofs and OCaml components.
# Run from structural-admissibility-library/, or via the repo-root wrapper.

set -euo pipefail

LIB_DIR="$(cd "$(dirname "$0")/.." && pwd)"

# Prefer the opam rocq installation if not already in PATH.
if ! command -v rocq >/dev/null 2>&1 && [ -d "$HOME/.opam" ]; then
  OPAM_ROCQ=$(find "$HOME/.opam" -name "rocq" -type f 2>/dev/null | head -1)
  [ -n "$OPAM_ROCQ" ] && export PATH="$(dirname "$OPAM_ROCQ"):$PATH"
fi

command -v rocq >/dev/null 2>&1 || {
  echo "ERROR: rocq not found. Add it to PATH or set up opam." >&2
  exit 1
}

echo "=== Building Rocq proofs ==="
(cd "$LIB_DIR" && make)

echo ""
echo "=== Building OCaml components ==="
(cd "$LIB_DIR/ocaml" && dune build)

echo ""
echo "=== Running OCaml tests ==="
(cd "$LIB_DIR/ocaml" && dune test)

echo ""
echo "=== All builds and tests passed ==="
