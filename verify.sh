#!/usr/bin/env bash
set -euo pipefail

if grep -RInE \
  '(^|[^[:alnum:]_])(sorry|admit|native_decide|unsafe|run_tac|implemented_by|extern|Lean\.ofReduceBool|unsafeCast)([^[:alnum:]_]|$)|^[[:space:]]*(axiom|constant)([[:space:]]|$)|[.]_private[.]' \
  stoch_to_det stoch_to_det.lean Verify.lean Verify96.lean VerifySharedRace.lean; then
  echo "disallowed Lean source construct found" >&2
  exit 1
fi

lake build --log-level=error stoch_to_det
lake env lean Verify.lean
lake env lean Verify96.lean
lake env lean VerifySharedRace.lean
echo "Verification passed: source audit, full build, no sorry dependencies, and exact axiom sets."
