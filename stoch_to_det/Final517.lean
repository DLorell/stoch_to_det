import stoch_to_det.PriceConv

/-!
# Unconditional endpoint: `T ≤ 517 · τ`

The parametric `517` ledger (`Ledger517.lean`, threshold `eta = 2/5`,
`rho517 = 17/50`) reduced the winner-entropy bound to a single contact-level
conversion hypothesis.  That hypothesis is discharged with information floor
`F = 9/400` bits by `conversion517` (`PriceConv.lean`), whose analytic core is
the price-dual (three-budget tangent) aggregation: five single-variable zone
envelopes (`PriceZoneLow.lean`, `PriceZoneHigh.lean`), the per-cell weighted
AM-GM against the feasibility, norm, and KL budgets (`PriceCell.lean`), and
the summation core (`PriceCore.lean`).

Both ledger branches then sit below `516`:
the far branch by the certified `Constants517` envelope, and the near branch
because `3·beta1771/(9/400) = (400/3)·(2 + cOff1771)/log 2 < 516`.
-/

namespace stoch_to_det

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

/-- The near branch of the `517` ledger at floor `9/400` bits is below `516`. -/
lemma near_branch_517_lt_516 : 3 * beta1771 / (9/400 : ℝ) < 516 := by
  have hβ : beta1771 * Real.log 2 = 2 + cOff1771 := beta1771_mul_log_two
  have hc : cOff1771 < (677 : ℝ) / 1000 := cOff1771_lt
  have hl : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hβpos : 0 < beta1771 := beta1771_pos
  have hlpos : 0 < Real.log 2 := Real.log_pos one_lt_two
  -- `3β/(9/400) = (400/3)·β` and `400·β·log 2 < 400·2.677 < 1548·log 2`.
  have hkey : 400 * beta1771 < 1548 := by
    nlinarith [mul_pos hβpos hlpos]
  rw [div_lt_iff₀ (by norm_num : (0:ℝ) < 9/400)]
  nlinarith

/-- The full `517` ledger coefficient at floor `9/400` bits is below `517`. -/
theorem Cdagger_price_lt_517 :
    (max (3 * beta1771 / (9/400 : ℝ)) (6 * KS517 + 2) + 1 : ℝ) < 517 := by
  have h1 := near_branch_517_lt_516
  have h2 : 6 * KS517 + 2 < (516 : ℝ) := by
    nlinarith [KS517_lt_bar, six_KSbar517_add_two_lt_516]
  have hmax : max (3 * beta1771 / (9/400 : ℝ)) (6 * KS517 + 2) < 516 :=
    max_lt h1 h2
  linarith

/-- **Unconditional `517` ledger endpoint.** For every finite law `p` on a
product alphabet, `T p ≤ 517 · τ p`, with no remaining hypotheses beyond `p`
being a law. -/
theorem T_le_517 {p : α × β → ℝ} (hp : IsPMF p) : T p ≤ 517 * tau p := by
  have h := T_le_parametric (9/400 : ℝ) (by norm_num)
    (conversion517 (α := α) (β := β)) hp
  calc
    T p ≤ (max (3 * beta1771 / (9/400 : ℝ)) (6 * KS517 + 2) + 1) * tau p := h
    _ ≤ 517 * tau p :=
      mul_le_mul_of_nonneg_right Cdagger_price_lt_517.le (tau_nonneg p)

end stoch_to_det
