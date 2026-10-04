import stoch_to_det.CoordinateLedger
import stoch_to_det.CoordinateRace
import stoch_to_det.Comparison
import stoch_to_det.Connected
import stoch_to_det.PoweredRaceFifth
import stoch_to_det.PoweredRaceSixthRefined
import stoch_to_det.MismatchRefined

/-! A convex combination of the checked fifth- and refined sixth-power entropy
estimates gives an unconditional stochastic-to-deterministic constant 9.4. -/

namespace stoch_to_det

/-- Weight `3/28` on the fifth-power reference and `25/28` on the refined sixth. -/
noncomputable def mixedCoordinateJ94 : ℝ :=
  (3*poweredRaceJ5Upper + 25*poweredRaceJ6Refined)/28

namespace SharedRace

universe u

/-- Interpolate the existing entropy inequalities before the coordinate ledger. -/
theorem sharedRaceEntropy_le_five_six_refined_mix
    {Ω : Type u} {κ : Type}
    [Fintype Ω] [Fintype κ] [DecidableEq Ω] [DecidableEq κ] [Nonempty κ]
    {μ : Ω → ℝ} {r : Ω → κ → ℝ}
    (hμ : IsPMF μ)
    (hr : ∀ z, μ z ≠ 0 → IsPMF (r z))
    (hrpos : ∀ z, μ z ≠ 0 → ∀ i, 0 < r z i) :
    sharedRaceEntropy μ r ≤
      ((165 : ℝ)/28+mixedCoordinateJ94) * MI Prod.fst Prod.snd (posteriorJoint μ r) +
        mixedCoordinateJ94 / Real.log 2 * categoricalMismatch μ r := by
  have h5 := sharedRaceEntropy_le_fifth hμ hr hrpos
  have h6 := sharedRaceEntropy_le_sixth_refined hμ hr hrpos
  unfold mixedCoordinateJ94
  have hdiv : (3*poweredRaceJ5Upper+25*poweredRaceJ6Refined)/28 / Real.log 2 =
      (3*(poweredRaceJ5Upper / Real.log 2) +
        25*(poweredRaceJ6Refined / Real.log 2))/28 := by ring
  rw [hdiv]
  nlinarith only [h5, h6]

end SharedRace

variable {α β : Type*} [Fintype α] [Fintype β]
  [DecidableEq α] [DecidableEq β]

lemma mixed_coordinate_ledger_arithmetic_94 {M B b u : ℝ}
    (hM : 0 ≤ M) (hB : 0 ≤ B) (hb : b ≤ M+B)
    (hu : u ≤ M + ((3 : ℝ)/2*((165 : ℝ)/28+mixedCoordinateJ94)-1/2)*B +
      3*mixedCoordinateJ94*((733 : ℝ)/50*M+(77 : ℝ)/50*b)) :
    u ≤ ((47 : ℝ)/5)*(M+B) := by
  norm_num [mixedCoordinateJ94, poweredRaceJ5Upper, poweredRaceJ6Refined,
    poweredRaceJ6Upper] at hu ⊢
  linarith

private theorem T_le_94_of_entropy_sum
    {p : α × β → ℝ} (D : SeedSetup p) (K : Clustering D)
    (hcoord :
      ((∫ ε, condH (winner D ε) Prod.fst p ∂seedLaw D.L.ι) +
       (∫ ε, condH (winner D ε) Prod.snd p ∂seedLaw D.L.ι)) ≤
      ((165 : ℝ)/28+mixedCoordinateJ94)*D.Bq +
        2*(mixedCoordinateJ94/Real.log 2)*K.dMis) :
    T p ≤ ((47 : ℝ)/5)*tau p := by
  have hledger := T_le_coordinate_entropy_ledger D
  have hmis := mismatch_refined D K
  rw [K.Sinfo_eq_bZ] at hmis
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hJ : 0 ≤ mixedCoordinateJ94 := by
    norm_num [mixedCoordinateJ94, poweredRaceJ5Upper, poweredRaceJ6Refined,
      poweredRaceJ6Upper]
  have hscale := mul_le_mul_of_nonneg_left hmis (div_nonneg hJ hlog.le)
  have heq : mixedCoordinateJ94/Real.log 2 *
      ((733 : ℝ)/50*Real.log 2*D.M + (77 : ℝ)/50*Real.log 2*bZ D) =
      mixedCoordinateJ94*((733 : ℝ)/50*D.M + (77 : ℝ)/50*bZ D) := by
    field_simp [hlog.ne']
  rw [heq] at hscale
  have htotal : T p ≤ D.M + ((3 : ℝ)/2*((165 : ℝ)/28+mixedCoordinateJ94)-1/2)*D.Bq +
      3*mixedCoordinateJ94*((733 : ℝ)/50*D.M+(77 : ℝ)/50*bZ D) := by
    nlinarith only [hcoord, hledger, hscale]
  have hM : 0 ≤ D.M := condMI_nonneg D.L.joint_isPMF
    (fun t => t.2.1) (fun t => t.2.2) Prod.fst
  have hB : 0 ≤ D.Bq := add_nonneg
    (condMI_nonneg D.L.joint_isPMF
      (fun t => t.1) (fun t => t.2.1) (fun t => t.2.2))
    (condMI_nonneg D.L.joint_isPMF
      (fun t => t.1) (fun t => t.2.2) (fun t => t.2.1))
  have hb : bZ D ≤ D.M+D.Bq := by
    rw [← D.tau_eq_M_add_Bq]
    exact bZ_le_tau D
  rw [D.tau_eq_M_add_Bq]
  exact mixed_coordinate_ledger_arithmetic_94 hM hB hb htotal

/-- Unconditional comparison with constant `9.4`, strictly below `9.5`. -/
theorem T_le_94 {p : α × β → ℝ} (hp : IsPMF p) :
    T p ≤ ((47 : ℝ)/5)*tau p := by
  apply reduce_to_connected ((47 : ℝ)/5) _ p hp
  intro q hq hconn
  obtain ⟨D⟩ := exists_seedSetup hq hconn
  obtain ⟨K⟩ := exists_clustering D
  letI : Nonempty K.κ := Nonempty.map K.cl (Latent.nonempty_ι D.L)
  apply T_le_94_of_entropy_sum D K
  apply coordinate_entropy_sum_le_of_uniform_entropy_bound D K
    ((165 : ℝ)/28+mixedCoordinateJ94) (mixedCoordinateJ94/Real.log 2)
  · norm_num [mixedCoordinateJ94, poweredRaceJ5Upper, poweredRaceJ6Refined,
      poweredRaceJ6Upper]
  · exact fun _ _ hμ hr hrpos => SharedRace.sharedRaceEntropy_le_five_six_refined_mix hμ hr hrpos

section JointLaw

universe u

variable [MeasurableSpace α] [MeasurableSpace β]
  [MeasurableSingletonClass α] [MeasurableSingletonClass β]

/-- One deterministic function satisfies the `9.4` comparison for every
measurable joint-law latent. -/
theorem generalized_stoch_to_det_94_joint
    {p : α × β → ℝ} (hp : IsPMF p) :
    ∃ Γ : α × β → Fin (Fintype.card (α × β)),
      condH Γ (fun z : α × β => z) p = 0 ∧
      ∀ {ι : Type u} [MeasurableSpace ι] (V : JointLatent p ι),
        condMI (fun z : α × β => z.1) (fun z => z.2) Γ p
            + condH Γ (fun z : α × β => z.1) p
            + condH Γ (fun z : α × β => z.2) p
          ≤ ((47 : ℝ)/5) * (V.IxyGiven + V.IvxGivenY + V.IvyGivenX) :=
  generalized_stoch_to_det_joint_of_comparison hp (by norm_num) (T_le_94 hp)

end JointLaw

end stoch_to_det
