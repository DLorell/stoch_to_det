import stoch_to_det.SeedConstant1771
import stoch_to_det.Mismatch

/-!
# The improved seed constant

This file carries the sharpened scalar estimate and the Hellinger mismatch
charge through the four-line seed ledger. The
historical `RaceQuantities` API and its constants remain untouched.
-/

namespace stoch_to_det

variable {α β : Type*} [Fintype α] [Fintype β]
  [DecidableEq α] [DecidableEq β]
variable {p : α × β → ℝ} {D : SeedSetup p} {K : Clustering D}

lemma KM994_pos : 0 < KM994 := by
  exact div_pos beta1771_pos infoFloor994_pos

lemma KS994_pos : 0 < KS994 := by
  have hterm : 0 ≤ 2 * beta1771 * Real.log 2 / delta994 :=
    div_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) beta1771_pos.le)
        (Real.log_pos one_lt_two).le)
      delta994_pos.le
  unfold KS994
  linarith

lemma KD994_nonneg : 0 ≤ KD994 := by
  unfold KD994
  exact le_max_of_le_left (mul_nonneg (by norm_num) KM994_pos.le)

lemma Cdagger994_pos : 0 < Cdagger994 := by
  unfold Cdagger994
  linarith [KD994_nonneg]

/-- The improved scalar and unchanged cone estimates combine to give
`D_lab ≤ S + beta d`. -/
theorem seedLeak_bound_994 (R : RaceQuantities1771 D K) :
    R.toRaceQuantities.seedLeak ≤ K.Sinfo + beta1771 * K.dMis := by
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hcone : R.toRaceQuantities.cone ≤ K.dMis / Real.log 2 := by
    exact (le_div_iff₀ hlog).2 R.toRaceQuantities.cone_le_nats
  calc
    R.toRaceQuantities.seedLeak =
        R.toRaceQuantities.scalar + R.toRaceQuantities.cone :=
      R.toRaceQuantities.chain_split
    _ ≤ (K.Sinfo + kappa1771 * K.dMis) +
        K.dMis / Real.log 2 :=
      add_le_add R.scalar_le_1771 hcone
    _ = K.Sinfo + beta1771 * K.dMis := by
      unfold kappa1771 beta1771
      field_simp [hlog.ne']
      ring

/-- The improved winner-entropy ledger:
`H(A | epsilon,L0) ≤ KM M + KS bZ`. -/
theorem winnerEntropy_bound_994 (R : RaceQuantities1771 D K) :
    R.toRaceQuantities.winnerEntropy ≤
      KM994 * D.M + KS994 * bZ D := by
  have hseed := seedLeak_bound_994 R
  have hmis := mismatch_charge_994 K
  have hβmis := mul_le_mul_of_nonneg_left hmis beta1771_pos.le
  calc
    R.toRaceQuantities.winnerEntropy =
        K.Sinfo + R.toRaceQuantities.seedLeak :=
      R.toRaceQuantities.winner_entropy_identity
    _ ≤ K.Sinfo + (K.Sinfo + beta1771 * K.dMis) :=
      by
        simpa [add_comm, add_left_comm, add_assoc] using
          add_le_add_left hseed K.Sinfo
    _ ≤ K.Sinfo +
        (K.Sinfo + beta1771 *
          (D.M / infoFloor994 +
            (2 * Real.log 2 / delta994) * K.Sinfo)) := by
      simpa [add_comm, add_left_comm, add_assoc] using
        add_le_add_left (add_le_add_left hβmis K.Sinfo) K.Sinfo
    _ = KM994 * D.M + KS994 * K.Sinfo := by
      unfold KM994 KS994
      ring
    _ = KM994 * D.M + KS994 * bZ D := by
      rw [K.Sinfo_eq_bZ]

end stoch_to_det
