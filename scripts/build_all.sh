#!/usr/bin/env bash
# Repo-root wrapper — delegates to the library build script.
set -e
REPO_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$REPO_ROOT/structural-admissibility-library"
exec bash scripts/build_all.sh "$@"
