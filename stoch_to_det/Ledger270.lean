import stoch_to_det.Floor270
import stoch_to_det.DomFloor270
import stoch_to_det.SeedConstant270

/-! Exact near/far ledger and unconditional `270` endpoint. -/

namespace stoch_to_det

universe u v

variable {α : Type u} {β : Type v} [Fintype α] [Fintype β]
  [DecidableEq α] [DecidableEq β]

theorem nearcollision_floor_270
    {S : Finset (α × β)} {w : α × β → ℝ}
    (hw : Feasible S w) (hS : IsConnected S)
    {q r : α × β → ℝ}
    (hq : IsContact S w q) (hr : IsContact S w r) (hne : q ≠ r)
    (hnear : hellingerSq q r ≤ delta270) :
    rho270 ≤ rhoHGR q ∧
    rho270 ≤ rhoHGR r ∧
    infoFloor270 ≤ Ixy q ∧
    infoFloor270 ≤ Ixy r := by
  have hqR := rho270_le_rhoHGR_of_contacts hw hS hq hr hne hnear
  have hrR := rho270_le_rhoHGR_of_contacts_right hw hS hq hr hne hnear
  exact ⟨hqR, hrR,
    infoFloor270_le_Ixy_of_contact hw hq hqR,
    infoFloor270_le_Ixy_of_contact hw hr hrR⟩

variable {p : α × β → ℝ} {D : SeedSetup p}

abbrev IsHNear270 (K : Clustering D) (c d : K.κ) : Prop :=
  IsHNearAt K delta270 c d

theorem near_charge_270 (K : Clustering D) :
    ∑ c, ∑ d ∈ Finset.univ.filter (fun d => c ≠ d ∧ IsHNear270 K c d),
        pairMass K c d ≤ D.M / infoFloor270 := by
  have hcharge := near_charge_of_hellinger_floor K delta270 infoFloor270
    infoFloor270_pos (by
      intro c d hcd hnear
      have hQne : K.Q c ≠ K.Q d := fun h => hcd (K.Q_injective h)
      exact (nearcollision_floor_270 D.feasible D.conn
        (K.Q_isContact c) (K.Q_isContact d) hQne hnear).2.2.1)
  simpa [IsHNear270, IsHNearAt] using hcharge

theorem far_charge_270 (K : Clustering D) :
    ∑ c, ∑ d ∈ Finset.univ.filter (fun d => c ≠ d ∧ ¬ IsHNear270 K c d),
        pairMass K c d ≤ 2 * Real.log 2 / delta270 * K.Sinfo := by
  simpa [IsHNear270, IsHNearAt] using
    far_charge_of_hellinger K delta270 delta270_pos

theorem mismatch_charge_270 (K : Clustering D) :
    K.dMis ≤ D.M / infoFloor270 +
      2 * Real.log 2 / delta270 * K.Sinfo := by
  apply mismatch_charge_of_hellinger_floor K delta270 infoFloor270
    delta270_pos infoFloor270_pos
  intro c d hcd hnear
  have hQne : K.Q c ≠ K.Q d := fun h => hcd (K.Q_injective h)
  exact (nearcollision_floor_270 D.feasible D.conn
    (K.Q_isContact c) (K.Q_isContact d) hQne hnear).2.2.1

private theorem main270_M_nonneg {p : α × β → ℝ} (D : SeedSetup p) :
    0 ≤ D.M := by
  exact condMI_nonneg D.L.joint_isPMF
    (fun q => q.2.1) (fun q => q.2.2) (fun q => q.1)

private theorem main270_Bq_nonneg {p : α × β → ℝ} (D : SeedSetup p) :
    0 ≤ D.Bq := by
  unfold SeedSetup.Bq
  exact add_nonneg
    (condMI_nonneg D.L.joint_isPMF
      (fun q => q.1) (fun q => q.2.1) (fun q => q.2.2))
    (condMI_nonneg D.L.joint_isPMF
      (fun q => q.1) (fun q => q.2.2) (fun q => q.2.1))

theorem winnerEntropy_bound_270
    {p : α × β → ℝ} {D : SeedSetup p} (K : Clustering D)
    (R : RaceQuantitiesQuarter D K) :
    R.toRaceQuantities.winnerEntropy ≤
      KM270 * D.M + KS270 * bZ D := by
  classical
  have hseed := seedLeak_bound_270 R
  have hmis := mismatch_charge_270 K
  have hβmis := mul_le_mul_of_nonneg_left hmis beta270_pos.le
  calc
    R.toRaceQuantities.winnerEntropy =
        K.Sinfo + R.toRaceQuantities.seedLeak :=
      R.toRaceQuantities.winner_entropy_identity
    _ ≤ K.Sinfo + (K.Sinfo + beta270 * K.dMis) := by
      simpa [add_comm, add_left_comm, add_assoc] using
        add_le_add_left hseed K.Sinfo
    _ ≤ K.Sinfo +
        (K.Sinfo + beta270 *
          (D.M / infoFloor270 +
            (2 * Real.log 2 / delta270) * K.Sinfo)) := by
      simpa [add_comm, add_left_comm, add_assoc] using
        add_le_add_left (add_le_add_left hβmis K.Sinfo) K.Sinfo
    _ = KM270 * D.M + KS270 * K.Sinfo := by
      unfold KM270 KS270
      ring
    _ = KM270 * D.M + KS270 * bZ D := by
      rw [K.Sinfo_eq_bZ]

theorem Dwdefect_le_270
    {p : α × β → ℝ} (D : SeedSetup p)
    (K : Clustering D) (R : RaceQuantitiesQuarter D K) :
    Dwdefect D ≤ KD270 * tau p := by
  classical
  have hM := main270_M_nonneg D
  have hB := main270_Bq_nonneg D
  have hR : Rcell D ≤ 3 * KM270 * D.M + 3 * KS270 * bZ D := by
    calc
      Rcell D ≤ 3 * R.toRaceQuantities.winnerEntropy :=
        R.toRaceQuantities.rcell_le
      _ ≤ 3 * (KM270 * D.M + KS270 * bZ D) :=
        mul_le_mul_of_nonneg_left (winnerEntropy_bound_270 K R) (by norm_num)
      _ = 3 * KM270 * D.M + 3 * KS270 * bZ D := by ring
  have hcoef : 0 ≤ 3 * KS270 + 1 := by
    rw [KS270_eq]
    norm_num
  have hb : (3 * KS270 + 1) * bZ D ≤
      (3 * KS270 + 1) * (2 * D.Bq) :=
    mul_le_mul_of_nonneg_left (bZ_le_two_Bq D) hcoef
  have hKM : 3 * KM270 ≤ KD270 := by
    unfold KD270
    exact le_max_left _ _
  have hKS : 6 * KS270 + 2 ≤ KD270 := by
    unfold KD270
    exact le_max_right _ _
  rw [D.tau_eq_M_add_Bq]
  calc
    Dwdefect D ≤ Rcell D + bZ D := Dwdefect_le_Rcell_add_bZ D
    _ ≤ (3 * KM270 * D.M + 3 * KS270 * bZ D) + bZ D := by
      simpa [add_comm, add_left_comm, add_assoc] using add_le_add_right hR (bZ D)
    _ = 3 * KM270 * D.M + (3 * KS270 + 1) * bZ D := by ring
    _ ≤ 3 * KM270 * D.M + (3 * KS270 + 1) * (2 * D.Bq) := by
      simpa [add_comm, add_left_comm, add_assoc] using
        add_le_add_left hb (3 * KM270 * D.M)
    _ = 3 * KM270 * D.M + (6 * KS270 + 2) * D.Bq := by ring
    _ ≤ KD270 * D.M + KD270 * D.Bq :=
      add_le_add
        (mul_le_mul_of_nonneg_right hKM hM)
        (mul_le_mul_of_nonneg_right hKS hB)
    _ = KD270 * (D.M + D.Bq) := by ring

theorem T_le_Cdagger270_connected
    {p : α × β → ℝ} (hp : IsPMF p)
    (hconn : IsConnected (support p)) :
    T p ≤ Cdagger270 * tau p := by
  classical
  obtain ⟨D⟩ := exists_seedSetup hp hconn
  obtain ⟨K⟩ := exists_clustering D
  obtain ⟨R⟩ := exists_raceQuantitiesQuarter D K
  have hT := T_le_of_Dwdefect_le D (integrable_winnerScore D)
    (Dwdefect_le_270 D K R)
  simpa [Cdagger270] using hT

theorem T_le_Cdagger270
    {p : α × β → ℝ} (hp : IsPMF p) :
    T p ≤ Cdagger270 * tau p := by
  classical
  exact reduce_to_connected Cdagger270
    (fun q hq hconn => T_le_Cdagger270_connected hq hconn) p hp

/-- Unconditional exact `270` endpoint. -/
theorem T_le_270
    {p : α × β → ℝ} (hp : IsPMF p) :
    T p ≤ 270 * tau p := by
  calc
    T p ≤ Cdagger270 * tau p := T_le_Cdagger270 hp
    _ ≤ 270 * tau p :=
      mul_le_mul_of_nonneg_right Cdagger270_lt_270.le (tau_nonneg p)

end stoch_to_det
