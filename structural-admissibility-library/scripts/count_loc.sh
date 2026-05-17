#!/usr/bin/env bash
# count_loc.sh
# Count lines of code per layer.

echo "=== Lines of Code by Layer ==="
echo ""

layers=(
  "Foundation:coq/Foundation"
  "Admissibility:coq/Admissibility"
  "Runtime:coq/Runtime"
  "Automation:coq/Automation"
  "CaseStudies:coq/CaseStudies"
  "Extraction:coq/Extraction"
  "OCaml:ocaml"
)

total=0

for entry in "${layers[@]}"; do
  name="${entry%%:*}"
  dir="${entry##*:}"
  if [ -d "$dir" ]; then
    count=$(find "$dir" -name "*.v" -o -name "*.ml" | xargs wc -l 2>/dev/null | tail -1 | awk '{print $1}')
    printf "%-20s %6d lines\n" "$name" "$count"
    total=$((total + count))
  fi
done

echo ""
printf "%-20s %6d lines\n" "TOTAL" "$total"
