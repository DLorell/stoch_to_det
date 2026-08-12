import stoch_to_det.Conv1336

/-!
# Unconditional endpoint: `T ≤ 698 · τ`

The calibrated `1336` ledger (`Ledger1336.lean`) reduced the winner-entropy
bound to a single contact-level hypothesis, `ConversionHyp1336 infoFloor1336`.
That hypothesis is discharged by `conversion1336` (`Conv1336.lean`), whose
analytic core is the quartic moment bound for feasible kernels
(`QuarticMoment.lean`) together with the bulk quadratic and tail quartic
single-variable envelopes (`PhiBounds2.lean`) and the rational two-tangent
assembly (`Assembly1336.lean`).

The endpoint below is therefore unconditional: for every finite law `p`,
`T p ≤ 698 · τ p`.
-/

namespace stoch_to_det

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

/-- **Unconditional calibrated ledger endpoint.** For every finite law `p` on a
product alphabet, the winner-entropy functional satisfies `T p ≤ 698 · τ p`,
with no remaining hypotheses beyond `p` being a law. -/
theorem T_le_698 {p : α × β → ℝ} (hp : IsPMF p) : T p ≤ 698 * tau p :=
  T_lt_698 conversion1336 hp (tau_nonneg p)

end stoch_to_det
