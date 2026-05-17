#!/usr/bin/env bash
# extract_monitor.sh
# Run Coq extraction to produce the OCaml monitor kernel.

set -e

echo "=== Running Coq Extraction ==="
coqc -R coq StructuralAdmissibility \
  coq/Extraction/MonitorExtraction.v

echo "=== Extraction complete ==="
echo "Output: monitor_extracted.ml"

if [ -f monitor_extracted.ml ]; then
  mv monitor_extracted.ml ocaml/lib/monitor_extracted.ml
  echo "Moved to ocaml/lib/monitor_extracted.ml"
fi
