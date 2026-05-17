#!/usr/bin/env bash
# build_all.sh
# Build all Coq proofs and OCaml components.

set -e

echo "=== Building Coq proofs ==="
coq_makefile -f _CoqProject -o CoqMakefile
make -f CoqMakefile

echo ""
echo "=== Building OCaml components ==="
cd ocaml && dune build && cd ..

echo ""
echo "=== Running OCaml tests ==="
cd ocaml && dune test && cd ..

echo ""
echo "=== All builds and tests passed ==="
