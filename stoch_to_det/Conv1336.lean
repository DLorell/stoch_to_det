import stoch_to_det.DomFloorCore
import stoch_to_det.Ledger1336

/-!
# Certified HGR-to-information conversion at the 1336 calibration
-/

namespace stoch_to_det

open Finset

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

/-- The calibrated information floor fits inside the natural-log budget used by
the bulk/tail correlation estimate. -/
theorem log_two_mul_infoFloor1336_le :
    Real.log 2 * infoFloor1336 ≤ (116 : ℝ) / 10000 := by
  let a : ℝ := 2 + cOff1771
  have ha : 0 < a := by
    have h := mul_pos beta1771_pos (Real.log_pos one_lt_two)
    dsimp [a]
    rwa [beta1771_mul_log_two] at h
  have hab : a < (2677 : ℝ) / 1000 := by
    dsimp [a]
    linarith [cOff1771_lt]
  have hfar : far1336 = 14 + 12 * a / delta1336 := by
    unfold far1336 KS1336
    dsimp [a]
    rw [show 2 * beta1771 * Real.log 2 =
      2 * (beta1771 * Real.log 2) by ring, beta1771_mul_log_two]
    ring
  have hden : 0 < 14 * delta1336 + 12 * a := by
    nlinarith [delta1336_pos]
  calc
    Real.log 2 * infoFloor1336 = 3 * (beta1771 * Real.log 2) / far1336 := by
      unfold infoFloor1336
      ring
    _ = 3 * a / far1336 := by rw [beta1771_mul_log_two]
    _ = 3 * a * delta1336 / (14 * delta1336 + 12 * a) := by
      rw [hfar]
      field_simp [delta1336_pos.ne']
    _ ≤ (116 : ℝ) / 10000 := by
      apply (div_le_iff₀ hden).2
      rw [delta1336_eq_2197_div_46656]
      norm_num at hab ⊢
      nlinarith

/-- The final contact-level conversion used by the calibrated `1336` ledger. -/
theorem conversion1336 : ConversionHyp1336 (α := α) (β := β) infoFloor1336 := by
  unfold ConversionHyp1336
  intro S w q hw hcontact hrho
  by_contra hnot
  have hIlt : Ixy q < infoFloor1336 := lt_of_not_ge hnot
  have hlogpos : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hKlt : Knat q < (116 : ℝ) / 10000 := by
    calc
      Knat q = Real.log 2 * Ixy q := Knat_eq_log_two_mul_Ixy hcontact.1
      _ < Real.log 2 * infoFloor1336 := mul_lt_mul_of_pos_left hIlt hlogpos
      _ ≤ (116 : ℝ) / 10000 := log_two_mul_infoFloor1336_le
  have hrho_cap : rhoHGR q ≤ (3565 : ℝ) / 10000 := by
    let ι := {fg : (α → ℝ) × (β → ℝ) //
      (∑ x, mX q x * fg.1 x = 0) ∧ (∑ y, mY q y * fg.2 y = 0) ∧
      (∑ x, mX q x * fg.1 x ^ 2 = 1) ∧ (∑ y, mY q y * fg.2 y ^ 2 = 1)}
    change (⨆ fg : ι, ∑ z, q z * fg.1.1 z.1 * fg.1.2 z.2) ≤
      (3565 : ℝ) / 10000
    apply Real.iSup_le
    · intro fg
      exact contact_correlation_cap hcontact.1 hw hcontact
        fg.2.1 fg.2.2.1 fg.2.2.2.1 fg.2.2.2.2 hKlt.le
    · norm_num
  have hthreshold : rho1336 ≤ (3565 : ℝ) / 10000 := hrho.trans hrho_cap
  have hstrict : (3565 : ℝ) / 10000 < rho1336 := by
    rw [rho1336_eq_479_div_1296]
    exact cap_lt_rho1336
  exact (not_lt_of_ge hthreshold) hstrict

end stoch_to_det
