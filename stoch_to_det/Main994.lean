import stoch_to_det.Main
import stoch_to_det.SeedConstant994

/-!
# The improved finite-latent stoch_to_det theorem

This module proves the improved finite theorem. It reuses the
audited seed, cell, and connected-component reductions, changing only the
quantitative inputs proved in the improved modules.
-/

namespace stoch_to_det

variable {α β : Type*} [Fintype α] [Fintype β]
  [DecidableEq α] [DecidableEq β]

private theorem main994_M_nonneg {p : α × β → ℝ} (D : SeedSetup p) :
    0 ≤ D.M := by
  exact condMI_nonneg D.L.joint_isPMF
    (fun q => q.2.1) (fun q => q.2.2) (fun q => q.1)

private theorem main994_Bq_nonneg {p : α × β → ℝ} (D : SeedSetup p) :
    0 ≤ D.Bq := by
  unfold SeedSetup.Bq
  exact add_nonneg
    (condMI_nonneg D.L.joint_isPMF
      (fun q => q.1) (fun q => q.2.1) (fun q => q.2.2))
    (condMI_nonneg D.L.joint_isPMF
      (fun q => q.1) (fun q => q.2.2) (fun q => q.2.1))

/-- Improved universal cell-defect bound. -/
theorem Dwdefect_le_994 {p : α × β → ℝ} (D : SeedSetup p)
    (K : Clustering D) (R : RaceQuantities1771 D K) :
    Dwdefect D ≤ KD994 * tau p := by
  have hM := main994_M_nonneg D
  have hB := main994_Bq_nonneg D
  have hR : Rcell D ≤
      3 * KM994 * D.M + 3 * KS994 * bZ D := by
    calc
      Rcell D ≤ 3 * R.toRaceQuantities.winnerEntropy :=
        R.toRaceQuantities.rcell_le
      _ ≤ 3 * (KM994 * D.M + KS994 * bZ D) :=
        mul_le_mul_of_nonneg_left (winnerEntropy_bound_994 R) (by norm_num)
      _ = 3 * KM994 * D.M + 3 * KS994 * bZ D := by ring
  have hcoef : 0 ≤ 3 * KS994 + 1 := by
    nlinarith [KS994_pos]
  have hb : (3 * KS994 + 1) * bZ D ≤
      (3 * KS994 + 1) * (2 * D.Bq) :=
    mul_le_mul_of_nonneg_left (bZ_le_two_Bq D) hcoef
  have hKM : 3 * KM994 ≤ KD994 := by
    unfold KD994
    exact le_max_left _ _
  have hKS : 6 * KS994 + 2 ≤ KD994 := by
    unfold KD994
    exact le_max_right _ _
  rw [D.tau_eq_M_add_Bq]
  calc
    Dwdefect D ≤ Rcell D + bZ D := Dwdefect_le_Rcell_add_bZ D
    _ ≤ (3 * KM994 * D.M + 3 * KS994 * bZ D) + bZ D :=
      by
        simpa [add_comm, add_left_comm, add_assoc] using
          add_le_add_right hR (bZ D)
    _ = 3 * KM994 * D.M + (3 * KS994 + 1) * bZ D := by ring
    _ ≤ 3 * KM994 * D.M + (3 * KS994 + 1) * (2 * D.Bq) :=
      by
        simpa [add_comm, add_left_comm, add_assoc] using
          add_le_add_left hb (3 * KM994 * D.M)
    _ = 3 * KM994 * D.M + (6 * KS994 + 2) * D.Bq := by ring
    _ ≤ KD994 * D.M + KD994 * D.Bq :=
      add_le_add
        (mul_le_mul_of_nonneg_right hKM hM)
        (mul_le_mul_of_nonneg_right hKS hB)
    _ = KD994 * (D.M + D.Bq) := by ring

/-- The connected-support finite theorem with the exact symbolic constant. -/
theorem T_le_Cdagger994_connected {p : α × β → ℝ} (hp : IsPMF p)
    (hconn : IsConnected (support p)) :
    T p ≤ Cdagger994 * tau p := by
  obtain ⟨D⟩ := exists_seedSetup hp hconn
  obtain ⟨K⟩ := exists_clustering D
  obtain ⟨R⟩ := exists_raceQuantities1771 D K
  have hT := T_le_of_Dwdefect_le D (integrable_winnerScore D)
    (Dwdefect_le_994 D K R)
  simpa [Cdagger994] using hT

/-- Improved stoch_to_det for finite latents, with the exact symbolic constant. -/
theorem T_le_Cdagger994 {p : α × β → ℝ} (hp : IsPMF p) :
    T p ≤ Cdagger994 * tau p :=
  reduce_to_connected Cdagger994
    (fun q hq hconn => T_le_Cdagger994_connected hq hconn) p hp

end stoch_to_det
