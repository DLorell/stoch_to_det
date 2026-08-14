import stoch_to_det.Race
import stoch_to_det.Mismatch96
import stoch_to_det.Constants96
import stoch_to_det.Connected

/-!
# The exact `C < 96` closure from the joint seed estimate

This file isolates the abstract race interface exactly. Once the calibrated
all-label race satisfies

`seedLeak ≤ Sinfo + dMis`,

the calibrated near/far mismatch theorem and the hybrid bounds
`b_Z ≤ tau`, `b_Z ≤ 2 B_q` give the strict numerical endpoint `96`.
`SharedRace.lean` supplies this interface unconditionally.
-/

namespace stoch_to_det

universe u v

variable {α : Type u} {β : Type v} [Fintype α] [Fintype β]
  [DecidableEq α] [DecidableEq β]

/-- Abstract all-label race interface for every connected seed setup and its
duplicate-free clustering. `SharedRace.lean` proves it universally. -/
def HasJointSeedBound (α : Type u) (β : Type v)
    [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] : Prop :=
  ∀ (p : α × β → ℝ) (D : SeedSetup p) (K : Clustering D),
    ∃ R : RaceQuantities D K, R.seedLeak ≤ K.Sinfo + K.dMis

/-- A universal fixed-context shared-race theorem supplies exactly the joint
seed interface required by the `96` ledger. -/
theorem hasJointSeedBound_of_sharedRaceBound
    (hshared : ∀ (κ : Type) [Fintype κ] [DecidableEq κ] [Nonempty κ],
      SharedRace.HasSharedRaceBound (α × β) κ) :
    HasJointSeedBound α β := by
  intro p D K
  exact exists_raceQuantities_joint D K (hshared K.κ)

theorem winnerEntropy_bound_96
    {p : α × β → ℝ} {D : SeedSetup p} (K : Clustering D)
    (R : RaceQuantities D K) (hseed : R.seedLeak ≤ K.Sinfo + K.dMis) :
    R.winnerEntropy ≤ KM96 * D.M + KS96 * bZ D := by
  have hmis := mismatch_charge_96 K
  calc
    R.winnerEntropy = K.Sinfo + R.seedLeak := R.winner_entropy_identity
    _ ≤ K.Sinfo + (K.Sinfo + K.dMis) := by
      simpa [add_comm, add_left_comm, add_assoc] using add_le_add_left hseed K.Sinfo
    _ ≤ K.Sinfo +
        (K.Sinfo + (D.M / infoFloor96 +
          (2 * Real.log 2 / delta96) * K.Sinfo)) := by
      simpa [add_comm, add_left_comm, add_assoc] using
        add_le_add_left (add_le_add_left hmis K.Sinfo) K.Sinfo
    _ = KM96 * D.M + KS96 * K.Sinfo := by
      unfold KM96 KS96
      ring
    _ = KM96 * D.M + KS96 * bZ D := by rw [K.Sinfo_eq_bZ]

private theorem main96_M_nonneg {p : α × β → ℝ} (D : SeedSetup p) :
    0 ≤ D.M := by
  exact condMI_nonneg D.L.joint_isPMF
    (fun q => q.2.1) (fun q => q.2.2) (fun q => q.1)

private theorem main96_Bq_nonneg {p : α × β → ℝ} (D : SeedSetup p) :
    0 ≤ D.Bq := by
  unfold SeedSetup.Bq
  exact add_nonneg
    (condMI_nonneg D.L.joint_isPMF
      (fun q => q.1) (fun q => q.2.1) (fun q => q.2.2))
    (condMI_nonneg D.L.joint_isPMF
      (fun q => q.1) (fun q => q.2.2) (fun q => q.2.1))

/-- Hybrid closure at the exact `96` constants.  This is the formal version of
the branch switch: use `b_Z ≤ tau` when `M ≤ B_q`, and `b_Z ≤ 2B_q` otherwise. -/
theorem Dwdefect_le_96
    {p : α × β → ℝ} (D : SeedSetup p) (K : Clustering D)
    (R : RaceQuantities D K) (hseed : R.seedLeak ≤ K.Sinfo + K.dMis) :
    Dwdefect D ≤ KD96 * tau p := by
  have hM := main96_M_nonneg D
  have hB := main96_Bq_nonneg D
  have hRcell : Rcell D ≤ 3 * KM96 * D.M + 3 * KS96 * bZ D := by
    calc
      Rcell D ≤ 3 * R.winnerEntropy := R.rcell_le
      _ ≤ 3 * (KM96 * D.M + KS96 * bZ D) :=
        mul_le_mul_of_nonneg_left (winnerEntropy_bound_96 K R hseed) (by norm_num)
      _ = 3 * KM96 * D.M + 3 * KS96 * bZ D := by ring
  have hbase :
      Dwdefect D ≤ 3 * KM96 * D.M + (3 * KS96 + 1) * bZ D := by
    calc
      Dwdefect D ≤ Rcell D + bZ D := Dwdefect_le_Rcell_add_bZ D
      _ ≤ (3 * KM96 * D.M + 3 * KS96 * bZ D) + bZ D :=
        by
          simpa [add_comm, add_left_comm, add_assoc] using
            add_le_add_right hRcell (bZ D)
      _ = 3 * KM96 * D.M + (3 * KS96 + 1) * bZ D := by ring
  let F : ℝ := (3 / 2 : ℝ) * KM96 + 3 * KS96 + 1
  have hfar : Dwdefect D ≤ F * tau p := by
    rw [D.tau_eq_M_add_Bq]
    by_cases hMB : D.M ≤ D.Bq
    · have hb := mul_le_mul_of_nonneg_left (bZ_le_tau D)
        joint_bZ_coefficient_nonneg
      rw [D.tau_eq_M_add_Bq] at hb
      calc
        Dwdefect D ≤ 3 * KM96 * D.M + (3 * KS96 + 1) * bZ D := hbase
        _ ≤ 3 * KM96 * D.M + (3 * KS96 + 1) * (D.M + D.Bq) :=
          by
            simpa [add_comm, add_left_comm, add_assoc] using
              add_le_add_left hb (3 * KM96 * D.M)
        _ ≤ F * (D.M + D.Bq) := by
          dsimp [F]
          nlinarith [KM96_nonneg]
    · have hBM : D.Bq ≤ D.M := le_of_not_ge hMB
      have hb := mul_le_mul_of_nonneg_left (bZ_le_two_Bq D)
        joint_bZ_coefficient_nonneg
      calc
        Dwdefect D ≤ 3 * KM96 * D.M + (3 * KS96 + 1) * bZ D := hbase
        _ ≤ 3 * KM96 * D.M + (3 * KS96 + 1) * (2 * D.Bq) :=
          by
            simpa [add_comm, add_left_comm, add_assoc] using
              add_le_add_left hb (3 * KM96 * D.M)
        _ ≤ F * (D.M + D.Bq) := by
          dsimp [F]
          nlinarith [near_branch_96_lt_far]
  calc
    Dwdefect D ≤ F * tau p := hfar
    _ ≤ KD96 * tau p := by
      apply mul_le_mul_of_nonneg_right _ (tau_nonneg p)
      unfold KD96 F
      exact le_max_right _ _

theorem T_le_Cdagger96_connected_of_joint_seed_bound
    (hjoint : HasJointSeedBound α β)
    {p : α × β → ℝ} (hp : IsPMF p) (hconn : IsConnected (support p)) :
    T p ≤ Cdagger96 * tau p := by
  classical
  obtain ⟨D⟩ := exists_seedSetup hp hconn
  obtain ⟨K⟩ := exists_clustering D
  obtain ⟨R, hseed⟩ := hjoint p D K
  have hT := T_le_of_Dwdefect_le D (integrable_winnerScore D)
    (Dwdefect_le_96 D K R hseed)
  simpa [Cdagger96] using hT

theorem T_le_Cdagger96_of_joint_seed_bound
    (hjoint : HasJointSeedBound α β)
    {p : α × β → ℝ} (hp : IsPMF p) :
    T p ≤ Cdagger96 * tau p := by
  classical
  exact reduce_to_connected Cdagger96
    (fun q hq hconn => T_le_Cdagger96_connected_of_joint_seed_bound hjoint hq hconn)
    p hp

/-- Exact strict endpoint, conditional only on the explicitly named joint race
bound.  Every other link, including the hybrid branch switch and `Cdagger96 < 96`,
is kernel checked. -/
theorem T_le_96_of_joint_seed_bound
    (hjoint : HasJointSeedBound α β)
    {p : α × β → ℝ} (hp : IsPMF p) :
    T p ≤ 96 * tau p := by
  calc
    T p ≤ Cdagger96 * tau p := T_le_Cdagger96_of_joint_seed_bound hjoint hp
    _ ≤ 96 * tau p :=
      mul_le_mul_of_nonneg_right Cdagger96_lt_96.le (tau_nonneg p)

/-- The final ledger stated directly from the universal fixed-context race
theorem.  Once `SharedRace.HasSharedRaceBound` is proved for every finite
label type, no further seed-level hypothesis remains. -/
theorem T_le_96_of_sharedRaceBound
    (hshared : ∀ (κ : Type) [Fintype κ] [DecidableEq κ] [Nonempty κ],
      SharedRace.HasSharedRaceBound (α × β) κ)
    {p : α × β → ℝ} (hp : IsPMF p) :
    T p ≤ 96 * tau p :=
  T_le_96_of_joint_seed_bound
    (hasJointSeedBound_of_sharedRaceBound hshared) hp

end stoch_to_det
