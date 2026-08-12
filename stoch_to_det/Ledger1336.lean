import stoch_to_det.Constants1336
import stoch_to_det.Floor1336

/-!
# Parametric downstream ledger at the `1336` near/far threshold

The only analytic input left abstract is a conversion from the certified HGR
floor `rho1336` to an information floor `F` for contacts.  The remainder of the
near/far mismatch ledger and the main theorem are assembled below.
-/

namespace stoch_to_det

universe u v

/-- A contact-level conversion, at fixed finite alphabets, from the certified
HGR threshold `rho1336` to an abstract information floor `F`. -/
def ConversionHyp1336
    {α : Type u} {β : Type v}
    [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (F : ℝ) : Prop :=
  ∀ {S : Finset (α × β)} {w q : α × β → ℝ},
    Feasible S w → IsContact S w q → rho1336 ≤ rhoHGR q → F ≤ Ixy q

variable {α : Type u} {β : Type v}
  [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

/-- Distinct `delta1336`-near contacts on a connected feasible support satisfy
both certified HGR bounds and, assuming `hconv`, both abstract information
floors. -/
theorem nearcollision_floor_1336
    (F : ℝ) (hconv : ConversionHyp1336 (α := α) (β := β) F)
    {S : Finset (α × β)} {w : α × β → ℝ}
    (hw : Feasible S w) (hS : IsConnected S)
    {q r : α × β → ℝ}
    (hq : IsContact S w q) (hr : IsContact S w r) (hne : q ≠ r)
    (hnear : hellingerSq q r ≤ delta1336) :
    rho1336 ≤ rhoHGR q ∧
    rho1336 ≤ rhoHGR r ∧
    F ≤ Ixy q ∧
    F ≤ Ixy r := by
  have hqR := rho1336_le_rhoHGR_of_contacts hw hS hq hr hne hnear
  have hrR := rho1336_le_rhoHGR_of_contacts_right hw hS hq hr hne hnear
  exact ⟨hqR, hrR, hconv hw hq hqR, hconv hw hr hrR⟩

variable {p : α × β → ℝ} {D : SeedSetup p}

/-- Squared-Hellinger near relation at the `delta1336` threshold. -/
abbrev IsHNear1336 (K : Clustering D) (c d : K.κ) : Prop :=
  IsHNearAt K delta1336 c d

/-- A `delta1336`-far cluster pair pays at least `delta1336 / log 2` in the two
directed KL charges. -/
theorem far_pair_KL_1336 (K : Clustering D) (c d : K.κ)
    (hfar : ¬ IsHNear1336 K c d) :
    delta1336 / Real.log 2 ≤
      KL (overlapLaw K c d) (K.Q c) + KL (overlapLaw K c d) (K.Q d) := by
  apply far_pair_KL_of_not_hnear K delta1336 c d
  simpa [IsHNear1336, IsHNearAt] using hfar

/-- Near pairs at the `delta1336` threshold are paid for by the abstract
information floor supplied by `hconv`. -/
theorem near_charge_1336
    (F : ℝ) (hF : 0 < F) (hconv : ConversionHyp1336 (α := α) (β := β) F)
    (K : Clustering D) :
    ∑ c, ∑ d ∈ Finset.univ.filter (fun d => c ≠ d ∧ IsHNear1336 K c d),
        pairMass K c d ≤ D.M / F := by
  have hcharge := near_charge_of_hellinger_floor K delta1336 F hF (by
    intro c d hcd hnear
    have hQne : K.Q c ≠ K.Q d := fun h => hcd (K.Q_injective h)
    exact (nearcollision_floor_1336 F hconv D.feasible D.conn
      (K.Q_isContact c) (K.Q_isContact d) hQne hnear).2.2.1)
  simpa [IsHNear1336, IsHNearAt] using hcharge

/-- Far pairs at the `delta1336` threshold are paid for by cluster information. -/
theorem far_charge_1336 (K : Clustering D) :
    ∑ c, ∑ d ∈ Finset.univ.filter (fun d => c ≠ d ∧ ¬ IsHNear1336 K c d),
        pairMass K c d ≤ 2 * Real.log 2 / delta1336 * K.Sinfo := by
  simpa [IsHNear1336, IsHNearAt] using
    far_charge_of_hellinger K delta1336 delta1336_pos

/-- Parametric `1336` mismatch charge: the near branch uses the assumed floor
`F`, while the far branch uses only `delta1336`. -/
theorem mismatch_charge_1336
    (F : ℝ) (hF : 0 < F) (hconv : ConversionHyp1336 (α := α) (β := β) F)
    (K : Clustering D) :
    K.dMis ≤ D.M / F + 2 * Real.log 2 / delta1336 * K.Sinfo := by
  apply mismatch_charge_of_hellinger_floor K delta1336 F delta1336_pos hF
  intro c d hcd hnear
  have hQne : K.Q c ≠ K.Q d := fun h => hcd (K.Q_injective h)
  exact (nearcollision_floor_1336 F hconv D.feasible D.conn
    (K.Q_isContact c) (K.Q_isContact d) hQne hnear).2.2.1

end stoch_to_det

namespace stoch_to_det

universe u v

variable {α : Type u} {β : Type v} [Fintype α] [Fintype β]
  [DecidableEq α] [DecidableEq β]

/-- Near-branch coefficient for an abstract positive information floor `F`. -/
noncomputable def KMParam1336 (F : ℝ) : ℝ :=
  beta1771 / F

/-- Cell-defect coefficient for the parametric `1336` ledger. -/
noncomputable def KDParam1336 (F : ℝ) : ℝ :=
  max (3 * KMParam1336 F) (6 * KS1336 + 2)

/-- Final coefficient produced by the parametric `1336` ledger. -/
noncomputable def CdaggerParam1336 (F : ℝ) : ℝ :=
  KDParam1336 F + 1

private theorem main1336_M_nonneg {p : α × β → ℝ} (D : SeedSetup p) :
    0 ≤ D.M := by
  exact condMI_nonneg D.L.joint_isPMF
    (fun q => q.2.1) (fun q => q.2.2) (fun q => q.1)

private theorem main1336_Bq_nonneg {p : α × β → ℝ} (D : SeedSetup p) :
    0 ≤ D.Bq := by
  unfold SeedSetup.Bq
  exact add_nonneg
    (condMI_nonneg D.L.joint_isPMF
      (fun q => q.1) (fun q => q.2.1) (fun q => q.2.2))
    (condMI_nonneg D.L.joint_isPMF
      (fun q => q.1) (fun q => q.2.2) (fun q => q.2.1))

/-- Winner-entropy ledger with abstract near information floor `F` and the
`delta1336` far coefficient. -/
theorem winnerEntropy_bound_1336
    (F : ℝ) (hF : 0 < F) (hconv : ConversionHyp1336 (α := α) (β := β) F)
    {p : α × β → ℝ} {D : SeedSetup p} (K : Clustering D)
    (R : RaceQuantities1771 D K) :
    R.toRaceQuantities.winnerEntropy ≤
      KMParam1336 F * D.M + KS1336 * bZ D := by
  classical
  have hseed := seedLeak_bound_1771 R
  have hmis := mismatch_charge_1336 F hF hconv K
  have hβmis := mul_le_mul_of_nonneg_left hmis beta1771_pos.le
  calc
    R.toRaceQuantities.winnerEntropy =
        K.Sinfo + R.toRaceQuantities.seedLeak :=
      R.toRaceQuantities.winner_entropy_identity
    _ ≤ K.Sinfo + (K.Sinfo + beta1771 * K.dMis) := by
      simpa [add_comm, add_left_comm, add_assoc] using
        add_le_add_left hseed K.Sinfo
    _ ≤ K.Sinfo +
        (K.Sinfo + beta1771 *
          (D.M / F + (2 * Real.log 2 / delta1336) * K.Sinfo)) := by
      simpa [add_comm, add_left_comm, add_assoc] using
        add_le_add_left (add_le_add_left hβmis K.Sinfo) K.Sinfo
    _ = KMParam1336 F * D.M + KS1336 * K.Sinfo := by
      unfold KMParam1336 KS1336
      ring
    _ = KMParam1336 F * D.M + KS1336 * bZ D := by
      rw [K.Sinfo_eq_bZ]

/-- Parametric `1336` cell-defect bound. -/
theorem Dwdefect_le_1336
    (F : ℝ) (hF : 0 < F) (hconv : ConversionHyp1336 (α := α) (β := β) F)
    {p : α × β → ℝ} (D : SeedSetup p)
    (K : Clustering D) (R : RaceQuantities1771 D K) :
    Dwdefect D ≤ KDParam1336 F * tau p := by
  classical
  have hM := main1336_M_nonneg D
  have hB := main1336_Bq_nonneg D
  have hR : Rcell D ≤
      3 * KMParam1336 F * D.M + 3 * KS1336 * bZ D := by
    calc
      Rcell D ≤ 3 * R.toRaceQuantities.winnerEntropy :=
        R.toRaceQuantities.rcell_le
      _ ≤ 3 * (KMParam1336 F * D.M + KS1336 * bZ D) :=
        mul_le_mul_of_nonneg_left
          (winnerEntropy_bound_1336 F hF hconv K R) (by norm_num)
      _ = 3 * KMParam1336 F * D.M + 3 * KS1336 * bZ D := by ring
  have hcoef : 0 ≤ 3 * KS1336 + 1 := by
    nlinarith [KS1336_pos]
  have hb : (3 * KS1336 + 1) * bZ D ≤
      (3 * KS1336 + 1) * (2 * D.Bq) :=
    mul_le_mul_of_nonneg_left (bZ_le_two_Bq D) hcoef
  have hKM : 3 * KMParam1336 F ≤ KDParam1336 F := by
    unfold KDParam1336
    exact le_max_left _ _
  have hKS : 6 * KS1336 + 2 ≤ KDParam1336 F := by
    unfold KDParam1336
    exact le_max_right _ _
  rw [D.tau_eq_M_add_Bq]
  calc
    Dwdefect D ≤ Rcell D + bZ D := Dwdefect_le_Rcell_add_bZ D
    _ ≤ (3 * KMParam1336 F * D.M + 3 * KS1336 * bZ D) + bZ D := by
      simpa [add_comm, add_left_comm, add_assoc] using
        add_le_add_right hR (bZ D)
    _ = 3 * KMParam1336 F * D.M + (3 * KS1336 + 1) * bZ D := by ring
    _ ≤ 3 * KMParam1336 F * D.M + (3 * KS1336 + 1) * (2 * D.Bq) := by
      simpa [add_comm, add_left_comm, add_assoc] using
        add_le_add_left hb (3 * KMParam1336 F * D.M)
    _ = 3 * KMParam1336 F * D.M + (6 * KS1336 + 2) * D.Bq := by ring
    _ ≤ KDParam1336 F * D.M + KDParam1336 F * D.Bq :=
      add_le_add
        (mul_le_mul_of_nonneg_right hKM hM)
        (mul_le_mul_of_nonneg_right hKS hB)
    _ = KDParam1336 F * (D.M + D.Bq) := by ring

/-- Connected-support endpoint of the parametric `1336` ledger. -/
theorem T_le_Cdagger_connected_1336
    (F : ℝ) (hF : 0 < F) (hconv : ConversionHyp1336 (α := α) (β := β) F)
    {p : α × β → ℝ} (hp : IsPMF p)
    (hconn : IsConnected (support p)) :
    T p ≤ CdaggerParam1336 F * tau p := by
  classical
  obtain ⟨D⟩ := exists_seedSetup hp hconn
  obtain ⟨K⟩ := exists_clustering D
  obtain ⟨R⟩ := exists_raceQuantities1771 D K
  have hT := T_le_of_Dwdefect_le D (integrable_winnerScore D)
    (Dwdefect_le_1336 F hF hconv D K R)
  simpa [CdaggerParam1336] using hT

/-- Every finite law satisfies the parametric `1336` ledger bound. -/
theorem T_le_Cdagger_1336
    (F : ℝ) (hF : 0 < F) (hconv : ConversionHyp1336 (α := α) (β := β) F)
    {p : α × β → ℝ} (hp : IsPMF p) :
    T p ≤ CdaggerParam1336 F * tau p := by
  classical
  exact reduce_to_connected (CdaggerParam1336 F)
    (fun q hq hconn => T_le_Cdagger_connected_1336 F hF hconv hq hconn) p hp

/-- Final parametric theorem: once a positive contact conversion floor `F` is
supplied, the complete downstream ledger closes with the displayed constant. -/
theorem T_le_parametric_1336
    (F : ℝ) (hF : 0 < F) (hconv : ConversionHyp1336 (α := α) (β := β) F)
    {p : α × β → ℝ} (hp : IsPMF p) :
    T p ≤
      (max (3 * beta1771 / F) (6 * KS1336 + 2) + 1) * tau p := by
  rw [show 3 * beta1771 / F = 3 * (beta1771 / F) by ring]
  simpa [CdaggerParam1336, KDParam1336, KMParam1336] using
    T_le_Cdagger_1336 F hF hconv hp

/-- Calibrated specialization of the `1336` ledger at `infoFloor1336`. -/
theorem T_le_Cdagger1336
    (hconv : ConversionHyp1336 (α := α) (β := β) infoFloor1336)
    {p : α × β → ℝ} (hp : IsPMF p) :
    T p ≤ Cdagger1336 * tau p := by
  have hparam :=
    T_le_parametric_1336 infoFloor1336 infoFloor1336_pos hconv hp
  have hnear : 3 * beta1771 / infoFloor1336 = far1336 := by
    rw [show 3 * beta1771 / infoFloor1336 =
      3 * (beta1771 / infoFloor1336) by ring]
    simpa [KM1336] using three_mul_KM1336_eq_far1336
  have hfar : 6 * KS1336 + 2 = far1336 := by
    rfl
  rw [hnear, hfar, max_self] at hparam
  simpa [Cdagger1336, KD1336_eq_far1336] using hparam

/-- Clean numerical endpoint of the calibrated `1336` ledger. -/
theorem T_lt_698
    (hconv : ConversionHyp1336 (α := α) (β := β) infoFloor1336)
    {p : α × β → ℝ} (hp : IsPMF p) (htau : 0 ≤ tau p) :
    T p ≤ 698 * tau p := by
  exact (T_le_Cdagger1336 hconv hp).trans
    (mul_le_mul_of_nonneg_right (le_of_lt Cdagger1336_lt_698) htau)

end stoch_to_det
