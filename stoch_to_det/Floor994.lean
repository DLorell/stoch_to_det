import stoch_to_det.Floor
import stoch_to_det.Constants994

namespace stoch_to_det

/-- The rational information-floor parameter is below the exact strengthened
HGR/Hellinger fraction at the chosen rational threshold. -/
theorem chi994_le_hgr_fraction :
    chi994 ≤ rho994 ^ ((14 : ℝ) / 3) /
      (1 + rho994 ^ ((4 : ℝ) / 3)) ^ 2 := by
  let t : ℝ := rho994 ^ ((1 : ℝ) / 3)
  let lo : ℝ := 73523 / 100000
  let hi : ℝ := 18381 / 25000
  have hrho0 : 0 ≤ rho994 := rho994_pos.le
  have ht0 : 0 ≤ t := Real.rpow_nonneg hrho0 _
  have ht3 : t ^ 3 = rho994 := by
    dsimp [t]
    convert Real.rpow_inv_natCast_pow hrho0 (by norm_num : (3 : ℕ) ≠ 0) using 1 <;>
      norm_num
  have hlo0 : 0 ≤ lo := by norm_num [lo]
  have hhi0 : 0 ≤ hi := by norm_num [hi]
  have hlo_cube : lo ^ 3 ≤ rho994 := by
    norm_num [lo, rho994, rho994Q, eta994Q]
  have hhi_cube : rho994 ≤ hi ^ 3 := by
    norm_num [hi, rho994, rho994Q, eta994Q]
  have hlo : lo ≤ t := by
    apply (pow_le_pow_iff_left₀ hlo0 ht0 (by norm_num : (3 : ℕ) ≠ 0)).mp
    rwa [ht3]
  have hhi : t ≤ hi := by
    apply (pow_le_pow_iff_left₀ ht0 hhi0 (by norm_num : (3 : ℕ) ≠ 0)).mp
    rwa [ht3]
  have hrho_four_thirds :
      rho994 ^ ((4 : ℝ) / 3) = rho994 * t := by
    rw [show (4 : ℝ) / 3 = 1 + 1 / 3 by norm_num,
      Real.rpow_add rho994_pos]
    simp [t]
  have ht2 : t ^ 2 = rho994 ^ ((2 : ℝ) / 3) := by
    dsimp [t]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hrho0]
    norm_num
  have hrho_fourteen_thirds :
      rho994 ^ ((14 : ℝ) / 3) = rho994 ^ 4 * t ^ 2 := by
    rw [show (14 : ℝ) / 3 = 4 + 2 / 3 by norm_num,
      Real.rpow_add rho994_pos, ht2]
    norm_num
  rw [hrho_fourteen_thirds, hrho_four_thirds]
  have hnum : rho994 ^ 4 * lo ^ 2 ≤ rho994 ^ 4 * t ^ 2 := by
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ hlo0 hlo 2) (by positivity)
  have hden : (1 + rho994 * t) ^ 2 ≤ (1 + rho994 * hi) ^ 2 := by
    apply pow_le_pow_left₀ (by positivity) _ 2
    simpa [add_comm] using add_le_add_left (mul_le_mul_of_nonneg_left hhi hrho0) 1
  have hden_pos : 0 < (1 + rho994 * t) ^ 2 := by positivity
  have hden_hi_pos : 0 < (1 + rho994 * hi) ^ 2 := by positivity
  calc
    chi994 ≤ (rho994 ^ 4 * lo ^ 2) / (1 + rho994 * hi) ^ 2 := by
      norm_num [chi994, chi994Q, rho994, rho994Q, eta994Q, lo, hi]
    _ ≤ (rho994 ^ 4 * lo ^ 2) / (1 + rho994 * t) ^ 2 :=
      div_le_div_of_nonneg_left (by positivity) hden_pos hden
    _ ≤ (rho994 ^ 4 * t ^ 2) / (1 + rho994 * t) ^ 2 :=
      (div_le_div_iff_of_pos_right hden_pos).2 hnum


theorem rho994_le_rhoHGR_of_contacts
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    {S : Finset (α × β)} {w q r : α × β → ℝ}
    (hw : Feasible S w) (hq : IsContact S w q) (hr : IsContact S w r)
    (hqs : support q = S) (hrs : support r = S) (hne : q ≠ r)
    (hclose : hellingerSq q r ≤ delta994) :
    rho994 ≤ rhoHGR q := by
  apply rhoThreshold_le_rhoHGR_of_contacts eta994_pos delta994_eq rho994_eq
    (by norm_num [eta994_eq]) hw hq hr hqs hrs hne hclose

private lemma hgr_fraction_14_factor {x : ℝ} (hx : 0 < x) :
    x ^ ((14 : ℝ) / 3) / (1 + x ^ ((4 : ℝ) / 3)) ^ 2 =
      x ^ 2 * (x ^ ((4 : ℝ) / 3) / (1 + x ^ ((4 : ℝ) / 3))) ^ 2 := by
  have hpow : x ^ ((14 : ℝ) / 3) = x ^ 2 * (x ^ ((4 : ℝ) / 3)) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_natCast,
      ← Real.rpow_mul hx.le, ← Real.rpow_add hx]
    norm_num
  rw [hpow, div_pow]
  ring

private theorem hgr_fraction_14_mono {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    a ^ ((14 : ℝ) / 3) / (1 + a ^ ((4 : ℝ) / 3)) ^ 2 ≤
      b ^ ((14 : ℝ) / 3) / (1 + b ^ ((4 : ℝ) / 3)) ^ 2 := by
  have hb : 0 < b := ha.trans_le hab
  let A : ℝ := a ^ ((4 : ℝ) / 3)
  let B : ℝ := b ^ ((4 : ℝ) / 3)
  have hA0 : 0 ≤ A := Real.rpow_nonneg ha.le _
  have hB0 : 0 ≤ B := Real.rpow_nonneg hb.le _
  have hAB : A ≤ B := Real.rpow_le_rpow ha.le hab (by norm_num)
  have hratio : A / (1 + A) ≤ B / (1 + B) := by
    apply (div_le_div_iff₀ (by positivity : 0 < 1 + A) (by positivity : 0 < 1 + B)).2
    nlinarith
  rw [hgr_fraction_14_factor ha, hgr_fraction_14_factor hb]
  exact mul_le_mul (pow_le_pow_left₀ ha.le hab 2)
    (pow_le_pow_left₀ (div_nonneg hA0 (by positivity)) hratio 2)
    (sq_nonneg _) (sq_nonneg _)

end stoch_to_det
