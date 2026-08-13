#!/usr/bin/env bash
set -euo pipefail

if grep -RInE \
  '(^|[^[:alnum:]_])(sorry|native_decide|unsafe)([^[:alnum:]_]|$)|^[[:space:]]*axiom([[:space:]]|$)' \
  stoch_to_det stoch_to_det.lean; then
  echo "disallowed Lean source construct found" >&2
  exit 1
fi

lake build --log-level=error stoch_to_det
lake env lean Verify.lean
lake env lean Verify270.lean
echo "Verification passed: source audit, full build, no sorry dependencies, and exact axiom sets."
