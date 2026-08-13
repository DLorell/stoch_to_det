import stoch_to_det.PriceZoneLow
import stoch_to_det.PriceZoneHigh
import stoch_to_det.PriceCell
import stoch_to_det.PriceCore
import stoch_to_det.Ledger517

/-!
# Certified HGR-to-information conversion at the `517` calibration

The price-dual aggregation (zone lemmas + per-cell three-budget AM-GM +
summation core) proves that every contact of a feasible kernel with
`Knat ≤ (9/400)·log 2` has HGR correlation at most
`217/1000 + (6183/40000)·log 2 < 17/50 = rho517`.  Contrapositively, a
contact with `rhoHGR ≥ rho517` has `Ixy ≥ 9/400` bits, which is exactly
`ConversionHyp (9/400)` for the parametric `517` ledger.
-/

namespace stoch_to_det

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

/-- The unconditional per-cell price inequality, obtained by discharging the
five zone hypotheses of `price_cell_of_zones`. -/
theorem price_cell {μ s r : ℝ} (hμ : 0 ≤ μ) (hs : 0 ≤ s) (hr : 0 ≤ r) :
    Real.sqrt μ * |r - 1| * s ≤
      (167/1000 : ℝ) * (μ ^ ((1:ℝ)/3) * r * s ^ ((4:ℝ)/3))
        + (1/20 : ℝ) * s^2 + (687/100 : ℝ) * (μ * phi r) :=
  price_cell_of_zones
    (fun _ h1 h2 => price_zone1 h1 h2)
    (fun _ h1 h2 => price_zone2 h1 h2)
    (fun _ h1 h2 => price_zone3 h1 h2)
    (fun _ h1 h2 => price_zone4 h1 h2)
    (fun _ h1 => price_zone5 h1)
    hμ hs hr

/-- The certified price capacity sits strictly below the `rho517` threshold. -/
theorem price_capacity_lt_rho517 :
    (217/1000 : ℝ) + (6183/40000 : ℝ) * Real.log 2 < (17/50 : ℝ) := by
  nlinarith [Real.log_two_lt_d9]

/-- The final contact-level conversion used by the parametric `517` ledger:
information floor `9/400` bits at the `rho517 = 17/50` HGR threshold. -/
theorem conversion517 : ConversionHyp (α := α) (β := β) (9/400 : ℝ) := by
  unfold ConversionHyp
  intro S w q hw hcontact hrho
  by_contra hnot
  have hIlt : Ixy q < (9/400 : ℝ) := lt_of_not_ge hnot
  have hlogpos : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hKle : Knat q ≤ (9/400 : ℝ) * Real.log 2 := by
    calc
      Knat q = Real.log 2 * Ixy q := Knat_eq_log_two_mul_Ixy hcontact.1
      _ ≤ Real.log 2 * (9/400 : ℝ) :=
        mul_le_mul_of_nonneg_left hIlt.le hlogpos.le
      _ = (9/400 : ℝ) * Real.log 2 := by ring
  have hrho_cap : rhoHGR q ≤
      (217/1000 : ℝ) + (6183/40000 : ℝ) * Real.log 2 := by
    let ι := {fg : (α → ℝ) × (β → ℝ) //
      (∑ x, mX q x * fg.1 x = 0) ∧ (∑ y, mY q y * fg.2 y = 0) ∧
      (∑ x, mX q x * fg.1 x ^ 2 = 1) ∧ (∑ y, mY q y * fg.2 y ^ 2 = 1)}
    change (⨆ fg : ι, ∑ z, q z * fg.1.1 z.1 * fg.1.2 z.2) ≤
      (217/1000 : ℝ) + (6183/40000 : ℝ) * Real.log 2
    apply Real.iSup_le
    · intro fg
      exact contact_correlation_price hcontact.1 hw hcontact
        fg.2.1 fg.2.2.1 fg.2.2.2.1 fg.2.2.2.2
        (fun μc sc rc hμc hsc hrc => price_cell hμc hsc hrc) hKle
    · nlinarith [Real.log_two_gt_d9]
  have hthreshold : rho517 ≤
      (217/1000 : ℝ) + (6183/40000 : ℝ) * Real.log 2 := hrho.trans hrho_cap
  have hstrict : (217/1000 : ℝ) + (6183/40000 : ℝ) * Real.log 2 < rho517 := by
    rw [rho517_eq_seventeen_div_50]
    exact price_capacity_lt_rho517
  exact (not_lt_of_ge hthreshold) hstrict

end stoch_to_det
