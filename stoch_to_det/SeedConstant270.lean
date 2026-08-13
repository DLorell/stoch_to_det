import stoch_to_det.Race
import stoch_to_det.Constants270

/-! Quarter-diagonal seed constant for the `270` route. -/

namespace stoch_to_det

variable {α β : Type*} [Fintype α] [Fintype β]
  [DecidableEq α] [DecidableEq β]
variable {p : α × β → ℝ} {D : SeedSetup p} {K : Clustering D}

lemma quarterSeedNat_lt_betaNat270 :
    (5 / 4 : ℝ) + cOff1771 < betaNat270 := by
  rw [betaNat270_eq]
  linarith [cOff1771_lt]

lemma quarterSeedCoeff_le_beta270 :
    ((5 / 4 : ℝ) + cOff1771) / Real.log 2 ≤ beta270 := by
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  unfold beta270
  exact (div_le_div_iff_of_pos_right hlog).2 quarterSeedNat_lt_betaNat270.le

theorem seedLeak_bound_270 (R : RaceQuantitiesQuarter D K) :
    R.toRaceQuantities.seedLeak ≤ K.Sinfo + beta270 * K.dMis := by
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hcone : R.toRaceQuantities.cone ≤ K.dMis / Real.log 2 := by
    exact (le_div_iff₀ hlog).2 R.toRaceQuantities.cone_le_nats
  have hexact : R.toRaceQuantities.seedLeak ≤
      K.Sinfo + (((5 / 4 : ℝ) + cOff1771) / Real.log 2) * K.dMis := by
    calc
      R.toRaceQuantities.seedLeak =
          R.toRaceQuantities.scalar + R.toRaceQuantities.cone :=
        R.toRaceQuantities.chain_split
      _ ≤ (K.Sinfo + ((1 / 4 + cOff1771) / Real.log 2) * K.dMis) +
          K.dMis / Real.log 2 :=
        add_le_add R.scalar_le_quarter hcone
      _ = K.Sinfo + (((5 / 4 : ℝ) + cOff1771) / Real.log 2) * K.dMis := by
        field_simp [hlog.ne']
        ring
  exact hexact.trans <| add_le_add_right
    (mul_le_mul_of_nonneg_right quarterSeedCoeff_le_beta270 K.dMis_nonneg)
    K.Sinfo

end stoch_to_det
