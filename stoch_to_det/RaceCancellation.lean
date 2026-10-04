import stoch_to_det.Race

/-!
# Retaining the coordinate-information terms in the race residual

The cell residual is `3 H(A | L, ε) - 2 I(A;X | L,ε) - 2 I(A;Y | L,ε)`.
The old ledger discards both negative terms.  Calibration and entropy
concavity bound them below by their posterior-replica counterparts.
-/

namespace stoch_to_det

open Finset MeasureTheory

private lemma cancellation_zero_of_mass_zero
    {ι : Type*} [Fintype ι] {m : ι → ℝ} (hm : IsFinMeas m)
    (hz : mass m = 0) : ∀ i, m i = 0 := by
  intro i
  exact (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hm i)).mp hz i (Finset.mem_univ i)

/-- Homogeneous cross entropy, allowing a reference measure of arbitrary mass. -/
private lemma cancellation_H_le_crossEntropy
    {ι : Type*} [Fintype ι] {m q : ι → ℝ}
    (hm : IsFinMeas m) (hq : IsFinMeas q)
    (hsupp : ∀ i, m i ≠ 0 → q i ≠ 0) :
    H m ≤ ∑ i, m i * lg (mass q / q i) := by
  classical
  have hm0 : 0 ≤ mass m := Finset.sum_nonneg fun i _ => hm i
  have hq0 : 0 ≤ mass q := Finset.sum_nonneg fun i _ => hq i
  by_cases hmz : mass m = 0
  · have hz : m = 0 := funext (cancellation_zero_of_mass_zero hm hmz)
    simp [hz, H]
  have hmp : 0 < mass m := lt_of_le_of_ne hm0 (Ne.symm hmz)
  have hqz : mass q ≠ 0 := by
    intro hz
    have hzero := cancellation_zero_of_mass_zero hq hz
    have hmzero : m = 0 := by
      funext i
      by_contra hi
      exact hsupp i hi (hzero i)
    simp [mass, hmzero] at hmz
  have hqp : 0 < mass q := lt_of_le_of_ne hq0 (Ne.symm hqz)
  let r : ι → ℝ := fun i => m i / mass m
  let s : ι → ℝ := fun i => q i / mass q
  have hr : IsPMF r := by
    refine ⟨fun i => div_nonneg (hm i) hm0, ?_⟩
    unfold mass
    dsimp [r]
    rw [← Finset.sum_div]
    exact div_self hmz
  have hs : IsPMF s := by
    refine ⟨fun i => div_nonneg (hq i) hq0, ?_⟩
    unfold mass
    dsimp [s]
    rw [← Finset.sum_div]
    exact div_self hqz
  have hcross := H_le_crossEntropy hr hs (fun i hi => by
    exact div_ne_zero (hsupp i ((div_ne_zero_iff.mp hi).1)) hqz)
  have hscale := H_smul hr.isFinMeas hmp.le
  have hrecover : (fun i => mass m * r i) = m := by
    funext i
    dsimp [r]
    field_simp [hmz]
  rw [hrecover] at hscale
  calc
    H m = mass m * H r := hscale
    _ ≤ mass m * ∑ i, r i * lg (1 / s i) :=
      mul_le_mul_of_nonneg_left hcross hmp.le
    _ = ∑ i, m i * lg (mass q / q i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      have href : 1 / s i = mass q / q i := by dsimp [s]; simp
      rw [href, ← mul_assoc]
      congr 1
      dsimp [r]
      field_simp [hmz]

/-- Jensen's inequality for the homogeneous finite entropy, written directly
for the mean measure.  The support hypothesis is convenient for the calibrated
race, whose posterior probabilities are positive throughout the source support. -/
private theorem cancellation_integral_H_le
    {E ι : Type*} [MeasurableSpace E] [Fintype ι]
    (ν : Measure E) (m : E → ι → ℝ) (q : ι → ℝ)
    (hm : ∀ e, IsFinMeas (m e)) (hq : IsFinMeas q)
    (hint : ∀ i, Integrable (fun e => m e i) ν)
    (hintH : Integrable (fun e => H (m e)) ν)
    (hmean : ∀ i, (∫ e, m e i ∂ν) = q i)
    (hsupp : ∀ e i, m e i ≠ 0 → q i ≠ 0) :
    (∫ e, H (m e) ∂ν) ≤ H q := by
  have hcross : Integrable
      (fun e => ∑ i, m e i * lg (mass q / q i)) ν :=
    integrable_finsetSum _ fun i _ => (hint i).mul_const _
  calc
    (∫ e, H (m e) ∂ν) ≤
        ∫ e, (∑ i, m e i * lg (mass q / q i)) ∂ν := by
      apply integral_mono hintH hcross
      intro e
      exact cancellation_H_le_crossEntropy (hm e) hq (hsupp e)
    _ = ∑ i, q i * lg (mass q / q i) := by
      rw [integral_finsetSum Finset.univ (fun i _ => (hint i).mul_const _)]
      apply Finset.sum_congr rfl
      intro i _
      rw [integral_mul_const, hmean]
    _ = H q := rfl

private theorem cancellation_integral_condH_le
    {E Ω Γ Δ : Type*} [MeasurableSpace E]
    [Fintype Ω] [Fintype Γ] [Fintype Δ]
    [DecidableEq Γ] [DecidableEq Δ]
    (ν : Measure E) (m : E → Ω → ℝ) (q : Ω → ℝ)
    (f : Ω → Γ) (g : Ω → Δ)
    (hm : ∀ e, IsPMF (m e)) (hq : IsPMF q)
    (hint : ∀ ω, Integrable (fun e => m e ω) ν)
    (hintH : ∀ d, Integrable
      (fun e => H (push f (fun ω => if g ω = d then m e ω else 0))) ν)
    (hmean : ∀ ω, (∫ e, m e ω ∂ν) = q ω)
    (hsupp : ∀ e ω, m e ω ≠ 0 → q ω ≠ 0) :
    (∫ e, condH f g (m e) ∂ν) ≤ condH f g q := by
  classical
  let fiber (r : Ω → ℝ) (d : Δ) : Γ → ℝ :=
    push f (fun ω => if g ω = d then r ω else 0)
  have hfin (r : Ω → ℝ) (hr : IsFinMeas r) (d : Δ) :
      IsFinMeas (fiber r d) := by
    apply isFinMeas_push
    intro ω
    by_cases hgd : g ω = d <;> simp [hgd, hr ω]
  have hfint (d : Δ) (c : Γ) :
      Integrable (fun e => fiber (m e) d c) ν := by
    unfold fiber push
    apply integrable_finsetSum
    intro ω _
    by_cases hgd : g ω = d
    · simpa [hgd] using hint ω
    · simp [hgd]
  have hfmean (d : Δ) (c : Γ) :
      (∫ e, fiber (m e) d c ∂ν) = fiber q d c := by
    unfold fiber push
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro ω _
      by_cases hgd : g ω = d <;> simp [hgd, hmean]
    · intro ω _
      by_cases hgd : g ω = d
      · simpa [hgd] using hint ω
      · simp [hgd]
  have hfsupp (e : E) (d : Δ) (c : Γ) :
      fiber (m e) d c ≠ 0 → fiber q d c ≠ 0 := by
    intro hne hzero
    apply hne
    change (∑ ω ∈ Finset.univ.filter (fun ω => f ω = c),
      if g ω = d then q ω else 0) = 0 at hzero
    have hterms := (Finset.sum_eq_zero_iff_of_nonneg
      (fun ω _ => by
        by_cases hgd : g ω = d <;> simp [hgd, hq.nonneg ω])).mp hzero
    unfold fiber push
    apply Finset.sum_eq_zero
    intro ω hω
    by_cases hgd : g ω = d
    · have hqω : q ω = 0 := by simpa [hgd] using hterms ω hω
      have hmω : m e ω = 0 := by
        by_contra h
        exact hsupp e ω h hqω
      simp [hmω]
    · simp [hgd]
  have hpoint (d : Δ) :
      (∫ e, H (fiber (m e) d) ∂ν) ≤ H (fiber q d) := by
    exact cancellation_integral_H_le ν (fun e => fiber (m e) d)
      (fiber q d) (fun e => hfin _ (hm e).isFinMeas d)
      (hfin q hq.isFinMeas d) (hfint d) (hintH d) (hfmean d)
      (fun e => hfsupp e d)
  have heq (e : E) : condH f g (m e) = ∑ d, H (fiber (m e) d) :=
    condH_eq_sum_H_fibers (hm e) f g
  simp_rw [heq]
  rw [integral_finsetSum Finset.univ (fun d _ => hintH d),
    condH_eq_sum_H_fibers hq]
  exact Finset.sum_le_sum fun d _ => hpoint d

section Race

variable {α β : Type*} [Fintype α] [Fintype β]
  [DecidableEq α] [DecidableEq β]
variable {p : α × β → ℝ} (D : SeedSetup p)

/-- The two coordinate-information terms discarded by the old race ledger. -/
noncomputable def replicaCoordinateX : ℝ :=
  condMI (fun u => u.2.1) (fun u => u.2.2.2.1) (fun u => u.1) (replicaLaw D)

noncomputable def replicaCoordinateY : ℝ :=
  condMI (fun u => u.2.1) (fun u => u.2.2.2.2) (fun u => u.1) (replicaLaw D)

/-- Replica chain rules retain a lower bound for the sum of coordinate terms. -/
theorem replica_coordinate_information_lower :
    2 * bZ D - D.Bq ≤ replicaCoordinateX D + replicaCoordinateY D := by
  unfold replicaCoordinateX replicaCoordinateY

  have hR := replicaLaw_isPMF D
  have hbSwap :
      condMI (fun u => u.2.1) (fun u => u.2.2.2) (fun u => u.1) (replicaLaw D) = bZ D := by
    simpa [bZ] using replica_condMI_swap D
  have hJ :
      MI (fun u : D.L.ι × D.L.ι × D.L.ι × (α × β) => u.1)
          (fun u => u.2.2.2) (replicaLaw D) =
        MI (fun v : D.L.ι × (α × β) => v.1) (fun v => v.2) D.L.joint := by
    simpa only using MI_replica_l₀_eq_joint D (fun z : α × β => z)
  have hIX := MI_replica_l₀_eq_joint D (fun z : α × β => z.1)
  have hIY := MI_replica_l₀_eq_joint D (fun z : α × β => z.2)
  have hB := Bq_info_identity D
  rw [← hJ, ← hIX, ← hIY] at hB
  have hL₁Z :
      MI (fun u : D.L.ι × D.L.ι × D.L.ι × (α × β) => u.2.1)
          (fun u => u.2.2.2) (replicaLaw D) =
        MI (fun u : D.L.ι × D.L.ι × D.L.ι × (α × β) => u.1)
          (fun u => u.2.2.2) (replicaLaw D) := by
    simpa only using MI_replica_swap D (fun z : α × β => z)
  have hZL₁ :
      MI (fun u : D.L.ι × D.L.ι × D.L.ι × (α × β) => u.2.2.2)
          (fun u => u.2.1) (replicaLaw D) =
        MI (fun u : D.L.ι × D.L.ι × D.L.ι × (α × β) => u.1)
          (fun u => u.2.2.2) (replicaLaw D) := by
    rw [MI_comm hR]
    exact hL₁Z
  have hPairZ :
      MI (fun u : D.L.ι × D.L.ι × D.L.ι × (α × β) => (u.2.2.2, u.1))
          (fun u => u.2.1) (replicaLaw D) =
        MI (fun u : D.L.ι × D.L.ι × D.L.ι × (α × β) => (u.1, u.2.2.2))
          (fun u => u.2.1) (replicaLaw D) := by
    have h := MI_equiv_left_local hR
      (fun u : D.L.ι × D.L.ι × D.L.ι × (α × β) => (u.1, u.2.2.2))
      (Equiv.prodComm D.L.ι (α × β)) (fun u => u.2.1)
    change _ = _ at h
    exact h
  have hbCondComm := condMI_comm_local hR
    (fun u : D.L.ι × D.L.ι × D.L.ι × (α × β) => u.2.2.2)
    (fun u => u.2.1) (fun u => u.1)
  have hchainZ₁ := MI_pair_left hR (fun u => u.2.2.2) (fun u => u.1) (fun u => u.2.1)
  have hchain₀Z := MI_pair_left hR (fun u => u.1) (fun u => u.2.2.2) (fun u => u.2.1)
  rw [hPairZ, hZL₁, replica_markov D, add_zero] at hchainZ₁
  rw [hbCondComm, hbSwap] at hchain₀Z
  have hbEq :
      bZ D =
        MI (fun u : D.L.ι × D.L.ι × D.L.ι × (α × β) => u.1)
            (fun u => u.2.2.2) (replicaLaw D)
          - MI (fun u : D.L.ι × D.L.ι × D.L.ι × (α × β) => u.1)
            (fun u => u.2.1) (replicaLaw D) := by
    linarith [hchainZ₁, hchain₀Z]
  have hL₁X :
      MI (fun u : D.L.ι × D.L.ι × D.L.ι × (α × β) => u.2.1)
          (fun u => u.2.2.2.1) (replicaLaw D) =
        MI (fun u : D.L.ι × D.L.ι × D.L.ι × (α × β) => u.1)
          (fun u => u.2.2.2.1) (replicaLaw D) := MI_replica_swap D (fun z => z.1)
  have hXL₁ :
      MI (fun u : D.L.ι × D.L.ι × D.L.ι × (α × β) => u.2.2.2.1)
          (fun u => u.2.1) (replicaLaw D) =
        MI (fun u : D.L.ι × D.L.ι × D.L.ι × (α × β) => u.1)
          (fun u => u.2.2.2.1) (replicaLaw D) := by
    rw [MI_comm hR]
    exact hL₁X
  have hPairX :
      MI (fun u : D.L.ι × D.L.ι × D.L.ι × (α × β) => (u.2.2.2.1, u.1))
          (fun u => u.2.1) (replicaLaw D) =
        MI (fun u : D.L.ι × D.L.ι × D.L.ι × (α × β) => (u.1, u.2.2.2.1))
          (fun u => u.2.1) (replicaLaw D) := by
    have h := MI_equiv_left_local hR
      (fun u : D.L.ι × D.L.ι × D.L.ι × (α × β) => (u.1, u.2.2.2.1))
      (Equiv.prodComm D.L.ι α) (fun u => u.2.1)
    change _ = _ at h
    exact h
  have hxCondComm := condMI_comm_local hR
    (fun u : D.L.ι × D.L.ι × D.L.ι × (α × β) => u.2.2.2.1)
    (fun u => u.2.1) (fun u => u.1)
  have hchainX₀ := MI_pair_left hR (fun u => u.2.2.2.1) (fun u => u.1) (fun u => u.2.1)
  have hchain₀X := MI_pair_left hR (fun u => u.1) (fun u => u.2.2.2.1) (fun u => u.2.1)
  rw [hPairX, hXL₁] at hchainX₀
  rw [hxCondComm] at hchain₀X
  have hxEq :
      condMI (fun u => u.2.1) (fun u => u.2.2.2.1) (fun u => u.1) (replicaLaw D) =
        MI (fun u => u.1) (fun u => u.2.2.2.1) (replicaLaw D)
          + condMI (fun u => u.1) (fun u => u.2.1) (fun u => u.2.2.2.1) (replicaLaw D)
          - MI (fun u => u.1) (fun u => u.2.1) (replicaLaw D) := by
    linarith [hchainX₀, hchain₀X]
  have hL₁Y :
      MI (fun u : D.L.ι × D.L.ι × D.L.ι × (α × β) => u.2.1)
          (fun u => u.2.2.2.2) (replicaLaw D) =
        MI (fun u : D.L.ι × D.L.ι × D.L.ι × (α × β) => u.1)
          (fun u => u.2.2.2.2) (replicaLaw D) := MI_replica_swap D (fun z => z.2)
  have hYL₁ :
      MI (fun u : D.L.ι × D.L.ι × D.L.ι × (α × β) => u.2.2.2.2)
          (fun u => u.2.1) (replicaLaw D) =
        MI (fun u : D.L.ι × D.L.ι × D.L.ι × (α × β) => u.1)
          (fun u => u.2.2.2.2) (replicaLaw D) := by
    rw [MI_comm hR]
    exact hL₁Y
  have hPairY :
      MI (fun u : D.L.ι × D.L.ι × D.L.ι × (α × β) => (u.2.2.2.2, u.1))
          (fun u => u.2.1) (replicaLaw D) =
        MI (fun u : D.L.ι × D.L.ι × D.L.ι × (α × β) => (u.1, u.2.2.2.2))
          (fun u => u.2.1) (replicaLaw D) := by
    have h := MI_equiv_left_local hR
      (fun u : D.L.ι × D.L.ι × D.L.ι × (α × β) => (u.1, u.2.2.2.2))
      (Equiv.prodComm D.L.ι β) (fun u => u.2.1)
    change _ = _ at h
    exact h
  have hyCondComm := condMI_comm_local hR
    (fun u : D.L.ι × D.L.ι × D.L.ι × (α × β) => u.2.2.2.2)
    (fun u => u.2.1) (fun u => u.1)
  have hchainY₀ := MI_pair_left hR (fun u => u.2.2.2.2) (fun u => u.1) (fun u => u.2.1)
  have hchain₀Y := MI_pair_left hR (fun u => u.1) (fun u => u.2.2.2.2) (fun u => u.2.1)
  rw [hPairY, hYL₁] at hchainY₀
  rw [hyCondComm] at hchain₀Y
  have hyEq :
      condMI (fun u => u.2.1) (fun u => u.2.2.2.2) (fun u => u.1) (replicaLaw D) =
        MI (fun u => u.1) (fun u => u.2.2.2.2) (replicaLaw D)
          + condMI (fun u => u.1) (fun u => u.2.1) (fun u => u.2.2.2.2) (replicaLaw D)
          - MI (fun u => u.1) (fun u => u.2.1) (replicaLaw D) := by
    linarith [hchainY₀, hchain₀Y]
  have hcx := condMI_nonneg hR (fun u => u.1) (fun u => u.2.1) (fun u => u.2.2.2.1)
  have hcy := condMI_nonneg hR (fun u => u.1) (fun u => u.2.1) (fun u => u.2.2.2.2)
  linarith [hbEq, hB, hcx, hcy, hxEq, hyEq]

private noncomputable def cancellationWinnerJoint (ε : D.L.ι → ℝ) :
    D.L.ι × (D.L.ι × (α × β)) → ℝ :=
  fun t => if winner D ε t.2.2 = t.1 then D.L.joint t.2 else 0

private noncomputable def cancellationReplicaJoint :
    D.L.ι × (D.L.ι × (α × β)) → ℝ :=
  fun t => D.L.joint t.2 * D.post t.1 t.2.2

private lemma cancellationWinnerJoint_eq_push (ε : D.L.ι → ℝ) :
    cancellationWinnerJoint D ε =
      push (fun t : D.L.ι × (α × β) => (winner D ε t.2, t)) D.L.joint := by
  funext t
  rcases t with ⟨a, b⟩
  unfold push cancellationWinnerJoint
  rw [Finset.sum_filter, Finset.sum_eq_single b]
  · simp
  · intro c _ hcb
    simp [Prod.mk.injEq, hcb]
  · simp

private lemma cancellationWinnerJoint_isPMF (ε : D.L.ι → ℝ) :
    IsPMF (cancellationWinnerJoint D ε) := by
  rw [cancellationWinnerJoint_eq_push]
  exact isPMF_push D.L.joint_isPMF

private lemma cancellation_integrable_joint (t : D.L.ι × (D.L.ι × (α × β))) :
    Integrable (fun ε => cancellationWinnerJoint D ε t) (seedLaw D.L.ι) := by
  exact integrable_winner_code D
    (fun A => if A t.2.2 = t.1 then D.L.joint t.2 else 0)

private lemma cancellation_joint_mean (t : D.L.ι × (D.L.ι × (α × β))) :
    (∫ ε, cancellationWinnerJoint D ε t ∂(seedLaw D.L.ι)) =
      cancellationReplicaJoint D t := by
  by_cases hpz : p t.2.2 = 0
  · have hj : D.L.joint t.2 = 0 := by
      unfold Latent.joint
      rw [(component_eq_zero_iff D t.2.1 t.2.2).mpr hpz, mul_zero]
    simp [cancellationWinnerJoint, cancellationReplicaJoint, hj]
  · have hpzpos : 0 < p t.2.2 :=
      lt_of_le_of_ne (D.isPMF.nonneg _) (Ne.symm hpz)
    have hfun : (fun ε => cancellationWinnerJoint D ε t) =
        fun ε => D.L.joint t.2 *
          (if winner D ε t.2.2 = t.1 then (1 : ℝ) else 0) := by
      funext ε
      by_cases hw : winner D ε t.2.2 = t.1 <;>
        simp [cancellationWinnerJoint, hw]
    rw [hfun, integral_const_mul, winner_probability D _ hpzpos]
    rfl

private lemma cancellationReplicaJoint_isPMF : IsPMF (cancellationReplicaJoint D) := by
  constructor
  · intro t
    exact mul_nonneg (D.L.joint_isPMF.nonneg t.2) (post_nonneg D _ _)
  · unfold mass
    simp_rw [← cancellation_joint_mean D]
    rw [← integral_finsetSum Finset.univ (fun t _ => cancellation_integrable_joint D t)]
    have hsum (ε : D.L.ι → ℝ) : ∑ t, cancellationWinnerJoint D ε t = 1 :=
      (cancellationWinnerJoint_isPMF D ε).total
    simp_rw [hsum]
    simp

private lemma cancellation_joint_support (ε : D.L.ι → ℝ)
    (t : D.L.ι × (D.L.ι × (α × β))) :
    cancellationWinnerJoint D ε t ≠ 0 → cancellationReplicaJoint D t ≠ 0 := by
  intro ht
  have hj : D.L.joint t.2 ≠ 0 := by
    intro hz
    simp [cancellationWinnerJoint, hz] at ht
  have hcomp : D.L.comp t.2.1 t.2.2 ≠ 0 := by
    intro hz
    apply hj
    simp [Latent.joint, hz]
  have hpz : p t.2.2 ≠ 0 := (component_eq_zero_iff D _ _).not.mp hcomp
  exact mul_ne_zero hj
    (post_pos_of_p_pos D _ _
      (lt_of_le_of_ne (D.isPMF.nonneg _) (Ne.symm hpz))).ne'

private lemma cancellationReplicaJoint_eq_push :
    cancellationReplicaJoint D =
      push (fun u : D.L.ι × D.L.ι × D.L.ι × (α × β) =>
        (u.2.1, u.1, u.2.2.2)) (replicaLaw D) := by
  funext t
  rcases t with ⟨a, l, z⟩
  unfold push
  rw [Finset.sum_filter, sum_replica_domain D]
  simp only [Prod.mk.injEq]
  have hite (l₀ l₁ l₂ : D.L.ι) (z' : α × β) :
      (if l₁ = a ∧ l₀ = l ∧ z' = z then replicaLaw D (l₀, l₁, l₂, z') else 0) =
        if l₀ = l then if l₁ = a then if z' = z then
          replicaLaw D (l₀, l₁, l₂, z') else 0 else 0 else 0 := by
    by_cases h₀ : l₀ = l <;> by_cases h₁ : l₁ = a <;>
      by_cases hz : z' = z <;> simp [h₀, h₁, hz]
  simp_rw [hite]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  rw [sum_replica_l₂ D]
  unfold cancellationReplicaJoint Latent.joint
  rw [p_mul_post D]

private lemma cancellation_condH_push
    {Ω Λ Γ Δ : Type*} [Fintype Ω] [Fintype Λ] [Fintype Γ] [Fintype Δ]
    [DecidableEq Λ] [DecidableEq Γ] [DecidableEq Δ]
    (m : Ω → ℝ) (k : Ω → Λ) (f : Λ → Γ) (g : Λ → Δ) :
    condH f g (push k m) = condH (fun x => f (k x)) (fun x => g (k x)) m := by
  unfold condH Hvar
  simp only [push_push, Function.comp_def]

private lemma cancellation_condMI_push
    {Ω Λ Γ Δ K : Type*} [Fintype Ω] [Fintype Λ]
    [Fintype Γ] [Fintype Δ] [Fintype K]
    [DecidableEq Λ] [DecidableEq Γ] [DecidableEq Δ] [DecidableEq K]
    (m : Ω → ℝ) (k : Ω → Λ) (f : Λ → Γ) (g : Λ → Δ) (h : Λ → K) :
    condMI f g h (push k m) =
      condMI (fun x => f (k x)) (fun x => g (k x)) (fun x => h (k x)) m := by
  unfold condMI Hvar
  simp only [push_push, Function.comp_def]

private lemma cancellation_joint_base :
    push Prod.snd (cancellationReplicaJoint D) = D.L.joint := by
  funext t
  unfold push cancellationReplicaJoint
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  by_cases hpz : p t.2 = 0
  · have hj : D.L.joint t = 0 := by
      simp [Latent.joint, (component_eq_zero_iff D t.1 t.2).mpr hpz]
    simp [hj]
  · rw [← Finset.mul_sum,
      sum_post_of_pos D t.2 (lt_of_le_of_ne (D.isPMF.nonneg _) (Ne.symm hpz)), mul_one]

/-- Conditioning on the seed can only increase the calibrated coordinate
information, because the seed is independent of the source and old label. -/
theorem average_winner_coordinate_information_lower
    {Γ : Type*} [Fintype Γ] [DecidableEq Γ] (g : α × β → Γ) :
    condMI (fun u => u.2.1) (fun u => g u.2.2.2) (fun u => u.1) (replicaLaw D) ≤
      ∫ ε, condMI (fun t : D.L.ι × (α × β) => winner D ε t.2)
        (fun t => g t.2) Prod.fst D.L.joint ∂(seedLaw D.L.ι) := by
  let m := cancellationWinnerJoint D
  let q := cancellationReplicaJoint D
  let f : D.L.ι × (D.L.ι × (α × β)) → Γ := fun t => g t.2.2
  let a : D.L.ι × (D.L.ι × (α × β)) → D.L.ι := Prod.fst
  let l : D.L.ι × (D.L.ι × (α × β)) → D.L.ι := fun t => t.2.1
  have hconcave := cancellation_integral_condH_le (seedLaw D.L.ι) m q f
    (fun t => (a t, l t)) (cancellationWinnerJoint_isPMF D)
    (cancellationReplicaJoint_isPMF D) (cancellation_integrable_joint D)
    (fun c => integrable_winner_code D (fun A =>
      H (push f (fun t => if (a t, l t) = c then
        (if A t.2.2 = t.1 then D.L.joint t.2 else 0) else 0))))
    (cancellation_joint_mean D) (cancellation_joint_support D)
  let baseH : ℝ := condH (fun t : D.L.ι × (α × β) => g t.2) Prod.fst D.L.joint
  have hbaseq : condH f l q = baseH := by
    have h := cancellation_condH_push q Prod.snd
      (fun t : D.L.ι × (α × β) => g t.2) Prod.fst
    rw [cancellation_joint_base D] at h
    exact h.symm
  have hbasem (ε : D.L.ι → ℝ) : condH f l (m ε) = baseH := by
    dsimp [m]
    rw [cancellationWinnerJoint_eq_push, cancellation_condH_push]
  have heq (ε : D.L.ι → ℝ) :
      condMI (fun t : D.L.ι × (α × β) => winner D ε t.2)
        (fun t => g t.2) Prod.fst D.L.joint =
      baseH - condH f (fun t => (a t, l t)) (m ε) := by
    have h := condMI_eq_condH_sub_pair (cancellationWinnerJoint_isPMF D ε) f a l
    rw [hbasem] at h
    have hc := condMI_comm_local (cancellationWinnerJoint_isPMF D ε) a f l
    have hpush : condMI a f l (m ε) =
        condMI (fun t : D.L.ι × (α × β) => winner D ε t.2)
          (fun t => g t.2) Prod.fst D.L.joint := by
      dsimp [m]
      rw [cancellationWinnerJoint_eq_push, cancellation_condMI_push]
    rw [← hpush, hc, h]
  have heqq :
      condMI (fun u => u.2.1) (fun u => g u.2.2.2) (fun u => u.1) (replicaLaw D) =
      baseH - condH f (fun t => (a t, l t)) q := by
    have h := condMI_eq_condH_sub_pair (cancellationReplicaJoint_isPMF D) f a l
    rw [hbaseq] at h
    have hc := condMI_comm_local (cancellationReplicaJoint_isPMF D) a f l
    have hrep : condMI a f l q =
        condMI (fun u => u.2.1) (fun u => g u.2.2.2) (fun u => u.1)
          (replicaLaw D) := by
      dsimp [q]
      rw [cancellationReplicaJoint_eq_push, cancellation_condMI_push]
    rw [← hrep, hc, h]
  have hi : Integrable
      (fun ε => condH f (fun t => (a t, l t)) (m ε)) (seedLaw D.L.ι) := by
    exact integrable_winner_code D (fun A => condH f (fun t => (a t, l t))
      (fun t => if A t.2.2 = t.1 then D.L.joint t.2 else 0))
  rw [heqq]
  simp_rw [heq]
  rw [integral_sub (integrable_const baseH) hi]
  simpa using sub_le_sub_left hconcave baseH

/-- The residual bound with both calibrated coordinate terms retained. -/
theorem Rcell_le_with_coordinate_cancellation :
    Rcell D ≤ 3 * raceWinnerEntropy D - 4 * bZ D + 2 * D.Bq := by
  let HX : (D.L.ι → ℝ) → ℝ := fixedWinnerIX D
  let HY : (D.L.ι → ℝ) → ℝ := fixedWinnerIY D
  let HA : (D.L.ι → ℝ) → ℝ := fun ε =>
    condH (fun t : D.L.ι × (α × β) => winner D ε t.2)
      Prod.fst D.L.joint
  have hX : Integrable HX (seedLaw D.L.ι) := by
    exact integrable_winner_code D (fun A =>
      condMI (fun t : D.L.ι × (α × β) => A t.2)
        (fun t => t.2.1) Prod.fst D.L.joint)
  have hY : Integrable HY (seedLaw D.L.ι) := by
    exact integrable_winner_code D (fun A =>
      condMI (fun t : D.L.ι × (α × β) => A t.2)
        (fun t => t.2.2) Prod.fst D.L.joint)
  have hA : Integrable HA (seedLaw D.L.ι) := integrable_raceWinnerEntropy D
  have hpoint (ε : D.L.ι → ℝ) :
      raceCellIntegrand D ε ≤ 3 * HA ε - 2 * HX ε - 2 * HY ε := by
    rw [fixed_seed_rcell_identity]
    have h := fixed_seed_info_le_entropy D ε
    dsimp [HA, HX, HY]
    linarith
  have hbound := integral_mono (integrable_raceCellIntegrand D)
    (((hA.const_mul 3).sub (hX.const_mul 2)).sub (hY.const_mul 2)) hpoint
  change (∫ ε, raceCellIntegrand D ε ∂(seedLaw D.L.ι)) ≤
    ∫ ε, 3 * HA ε - 2 * HX ε - 2 * HY ε ∂(seedLaw D.L.ι) at hbound
  rw [integral_sub (f := fun ε => 3 * HA ε - 2 * HX ε)
      (g := fun ε => 2 * HY ε)
      ((hA.const_mul 3).sub (hX.const_mul 2)) (hY.const_mul 2),
    integral_sub (f := fun ε => 3 * HA ε) (g := fun ε => 2 * HX ε)
      (hA.const_mul 3) (hX.const_mul 2), integral_const_mul,
    integral_const_mul, integral_const_mul] at hbound
  have hXlower := average_winner_coordinate_information_lower D
    (fun z : α × β => z.1)
  have hYlower := average_winner_coordinate_information_lower D
    (fun z : α × β => z.2)
  change replicaCoordinateX D ≤ ∫ ε, HX ε ∂(seedLaw D.L.ι) at hXlower
  change replicaCoordinateY D ≤ ∫ ε, HY ε ∂(seedLaw D.L.ι) at hYlower
  change Rcell D ≤ 3 * raceWinnerEntropy D -
    2 * (∫ ε, HX ε ∂(seedLaw D.L.ι)) -
    2 * (∫ ε, HY ε ∂(seedLaw D.L.ι)) at hbound
  linarith [replica_coordinate_information_lower D]

/-- The improved defect ledger, for the actual calibrated race. -/
theorem Dwdefect_le_two_Bq_add_three_seedLeak (K : Clustering D) :
    Dwdefect D ≤ 2 * D.Bq + 3 * (concreteRaceQuantities D K).seedLeak := by
  have hcell := Rcell_le_with_coordinate_cancellation D
  have hdefect := Dwdefect_le_Rcell_add_bZ D
  have hidentity := (concreteRaceQuantities D K).winner_entropy_identity
  rw [K.Sinfo_eq_bZ] at hidentity
  change raceWinnerEntropy D = bZ D + (concreteRaceQuantities D K).seedLeak at hidentity
  linarith

/-- The deterministic score retains the old-label coordinate cancellation. -/
theorem T_le_M_add_three_Bq_add_three_seedLeak (K : Clustering D) :
    T p ≤ D.M + 3 * D.Bq + 3 * (concreteRaceQuantities D K).seedLeak := by
  have hdefect := Dwdefect_le_two_Bq_add_three_seedLeak D K
  have hint := integrable_winnerScore D
  have havg :
      (∫ ε, (winnerLatent D ε).score ∂(seedLaw D.L.ι)) ≤
        D.M + 3 * D.Bq + 3 * (concreteRaceQuantities D K).seedLeak := by
    rw [expected_score_eq D hint, D.tau_eq_M_add_Bq]
    linarith
  obtain ⟨ε, hε⟩ := exists_good_seed D _ hint havg
  exact (T_le_score (winnerLatent D ε) (winnerLatent_isDet D ε)).trans hε

lemma cancellation_source_marginal : push Prod.snd D.L.joint = p := by
  funext z
  unfold push
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  simpa [Latent.joint] using D.L.mixture z

private lemma cancellation_codedJoint_eq_push (A : α × β → D.L.ι) :
    codedJoint D A = push (fun z => (A z, z)) p := by
  funext t
  rcases t with ⟨a, z₀⟩
  unfold codedJoint push
  rw [Finset.sum_filter, Finset.sum_eq_single z₀]
  · simp
  · intro z _ hz
    simp [Prod.mk.injEq, hz]
  · simp

private lemma cancellation_codedJoint_eq_push_joint (A : α × β → D.L.ι) :
    codedJoint D A = push (fun t : D.L.ι × (α × β) => (A t.2, t.2)) D.L.joint := by
  rw [cancellation_codedJoint_eq_push]
  calc
    _ = push (fun z => (A z, z)) (push Prod.snd D.L.joint) := by
      rw [cancellation_source_marginal D]
    _ = _ := by rw [push_push]; rfl

private lemma cancellation_MI_push
    {Ω Λ Γ Δ : Type*} [Fintype Ω] [Fintype Λ] [Fintype Γ] [Fintype Δ]
    [DecidableEq Λ] [DecidableEq Γ] [DecidableEq Δ]
    (m : Ω → ℝ) (k : Ω → Λ) (f : Λ → Γ) (g : Λ → Δ) :
    MI f g (push k m) = MI (fun x => f (k x)) (fun x => g (k x)) m := by
  unfold MI Hvar
  simp only [push_push, Function.comp_def]

/-- Calibration increases each unconditional coordinate information after
the independent seed is revealed. -/
theorem average_winner_information_lower
    {Γ : Type*} [Fintype Γ] [DecidableEq Γ] (g : α × β → Γ) :
    MI Prod.fst (fun t : D.L.ι × (α × β) => g t.2) D.L.joint ≤
      ∫ ε, MI (fun t : D.L.ι × (α × β) => winner D ε t.2)
        (fun t => g t.2) D.L.joint ∂seedLaw D.L.ι := by
  let m := fun ε => codedJoint D (winner D ε)
  let f : D.L.ι × (α × β) → Γ := fun t => g t.2
  have hm (ε : D.L.ι → ℝ) : IsPMF (m ε) := by
    dsimp [m]
    rw [cancellation_codedJoint_eq_push]
    exact isPMF_push D.isPMF
  have hint (t : D.L.ι × (α × β)) : Integrable (fun ε => m ε t) (seedLaw D.L.ι) :=
    integrable_winner_code D (fun A => codedJoint D A t)
  have hmean (t : D.L.ι × (α × β)) : (∫ ε, m ε t ∂seedLaw D.L.ι) = D.L.joint t := by
    by_cases hpz : p t.2 = 0
    · have hj : D.L.joint t = 0 := by
        simp [Latent.joint, (component_eq_zero_iff D t.1 t.2).mpr hpz]
      simp [m, codedJoint, hpz, hj]
    · have hfun : (fun ε => m ε t) = fun ε => p t.2 *
          (if winner D ε t.2 = t.1 then (1 : ℝ) else 0) := by
        funext ε
        by_cases ha : winner D ε t.2 = t.1 <;> simp [m, codedJoint, ha]
      rw [hfun, integral_const_mul,
        winner_probability D t.2 (lt_of_le_of_ne (D.isPMF.nonneg _) (Ne.symm hpz)),
        p_mul_post D]
      rfl
  have hsupp (ε : D.L.ι → ℝ) (t : D.L.ι × (α × β)) (hne : m ε t ≠ 0) :
      D.L.joint t ≠ 0 := by
    have hpz : p t.2 ≠ 0 := by
      intro hz
      simp [m, codedJoint, hz] at hne
    exact mul_ne_zero (D.prior_pos t.1).ne'
      ((component_eq_zero_iff D t.1 t.2).not.mpr hpz)
  have hconcave := cancellation_integral_condH_le (seedLaw D.L.ι) m D.L.joint
    f Prod.fst hm D.L.joint_isPMF hint
    (fun a => integrable_winner_code D (fun A =>
      H (push f (fun t => if t.1 = a then codedJoint D A t else 0)))) hmean hsupp
  have hH (ε : D.L.ι → ℝ) : Hvar f (m ε) = Hvar f D.L.joint := by
    dsimp [m]
    rw [cancellation_codedJoint_eq_push_joint]
    simp only [Hvar, push_push, Function.comp_def, f]
  have hMI (r : (D.L.ι × (α × β)) → ℝ) (hr : IsPMF r) :
      MI Prod.fst f r = Hvar f r - condH f Prod.fst r := by
    rw [MI_comm hr]
    unfold MI condH
    ring
  have heq (ε : D.L.ι → ℝ) :
      MI (fun t : D.L.ι × (α × β) => winner D ε t.2) f D.L.joint =
        Hvar f D.L.joint - condH f Prod.fst (m ε) := by
    calc
      _ = MI Prod.fst f (m ε) := by
        dsimp [m]
        rw [cancellation_codedJoint_eq_push_joint, cancellation_MI_push]
      _ = _ := by rw [hMI (m ε) (hm ε), hH]
  change MI Prod.fst f D.L.joint ≤
    ∫ ε, MI (fun t : D.L.ι × (α × β) => winner D ε t.2) f D.L.joint ∂seedLaw D.L.ι
  rw [hMI D.L.joint D.L.joint_isPMF]
  simp_rw [heq]
  rw [integral_sub (integrable_const _) (integrable_winner_code D
    (fun A => condH f Prod.fst (codedJoint D A)))]
  simpa using sub_le_sub_left hconcave (Hvar f D.L.joint)

private lemma cancellation_MI_exchange
    {Ω Λ Γ Δ : Type*} [Fintype Ω] [Fintype Λ] [Fintype Γ] [Fintype Δ]
    [DecidableEq Λ] [DecidableEq Γ] [DecidableEq Δ]
    {m : Ω → ℝ} (hm : IsPMF m) (a : Ω → Λ) (l : Ω → Γ) (z : Ω → Δ) :
    MI a z m - MI l z m = condMI a z l m - condMI l z a m := by
  have h₁ := MI_pair_left hm a l z
  have h₂ := MI_pair_left hm l a z
  have hswap := MI_equiv_left_local hm (fun t => (a t, l t))
    (Equiv.prodComm Λ Γ) z
  change MI (fun t => (l t, a t)) z m = MI (fun t => (a t, l t)) z m at hswap
  linarith

lemma cancellation_winner_latent_MI
    {Γ : Type*} [Fintype Γ] [DecidableEq Γ]
    (ε : D.L.ι → ℝ) (g : α × β → Γ) :
    MI Prod.fst (fun t => g t.2) (winnerLatent D ε).joint =
      MI (fun t : D.L.ι × (α × β) => winner D ε t.2)
        (fun t => g t.2) D.L.joint := by
  change MI (fun t : D.L.ι × (α × β) => t.1) (fun t => g t.2)
    (winnerLatent D ε).joint = _
  have hjoint : (winnerLatent D ε).joint = codedJoint D (winner D ε) := by
    funext q
    unfold Latent.joint codedJoint
    simpa only [winnerLatent] using cellMass_mul_cellLaw D ε q.1 q.2
  rw [hjoint, cancellation_codedJoint_eq_push_joint, cancellation_MI_push]

/-- The second side of the cancellation interpolation: revealing the seed
increases each unconditional coordinate information. -/
theorem Dwdefect_le_three_winnerEntropy_sub_condInfo :
    Dwdefect D ≤ 3 * (raceWinnerEntropy D -
      ∫ ε, condMI (fun t : D.L.ι × (α × β) => t.1) (fun t => t.2)
        (fun t => winner D ε t.2) D.L.joint ∂seedLaw D.L.ι) := by
  let HA := fun ε => condH
    (fun t : D.L.ι × (α × β) => winner D ε t.2) Prod.fst D.L.joint
  let C := fun ε => condMI (fun t : D.L.ι × (α × β) => t.1) (fun t => t.2)
    (fun t => winner D ε t.2) D.L.joint
  let AX := fun ε => MI (fun t : D.L.ι × (α × β) => winner D ε t.2)
    (fun t => t.2.1) D.L.joint
  let AY := fun ε => MI (fun t : D.L.ι × (α × β) => winner D ε t.2)
    (fun t => t.2.2) D.L.joint
  let LX := MI Prod.fst (fun t : D.L.ι × (α × β) => t.2.1) D.L.joint
  let LY := MI Prod.fst (fun t : D.L.ι × (α × β) => t.2.2) D.L.joint
  have hA : Integrable HA (seedLaw D.L.ι) := integrable_raceWinnerEntropy D
  have hC : Integrable C (seedLaw D.L.ι) := integrable_winnerCondInfo D
  have hX : Integrable AX (seedLaw D.L.ι) := integrable_winner_code D
    (fun A => MI (fun t : D.L.ι × (α × β) => A t.2) (fun t => t.2.1) D.L.joint)
  have hY : Integrable AY (seedLaw D.L.ι) := integrable_winner_code D
    (fun A => MI (fun t : D.L.ι × (α × β) => A t.2) (fun t => t.2.2) D.L.joint)
  have hpoint (ε : D.L.ι → ℝ) :
      (winnerLatent D ε).score ≤ tau p + 3 * (HA ε - C ε)
        - 2 * (AX ε - LX) - 2 * (AY ε - LY) := by
    have hw := (winnerLatent D ε).score_sub_Ixy D.isPMF
    have hL := D.L.score_sub_Ixy D.isPMF
    rw [D.optimal] at hL
    rw [cancellation_winner_latent_MI D ε (fun z => z),
      cancellation_winner_latent_MI D ε (fun z => z.1),
      cancellation_winner_latent_MI D ε (fun z => z.2)] at hw
    have hex := cancellation_MI_exchange D.L.joint_isPMF
      (fun t : D.L.ι × (α × β) => winner D ε t.2) Prod.fst Prod.snd
    have hcap := fixed_seed_info_le_entropy D ε
    change fixedWinnerIZ D ε ≤ HA ε at hcap
    change _ = fixedWinnerIZ D ε - C ε at hex
    dsimp only [HA, C, AX, AY, LX, LY] at *
    linarith
  have hright : Integrable
      (fun ε => tau p + 3 * (HA ε - C ε) - 2 * (AX ε - LX) - 2 * (AY ε - LY))
      (seedLaw D.L.ι) :=
    (((integrable_const _).add ((hA.sub hC).const_mul 3)).sub
      ((hX.sub (integrable_const LX)).const_mul 2)).sub
      ((hY.sub (integrable_const LY)).const_mul 2)
  have havg := integral_mono (integrable_winnerScore D) hright hpoint
  have hint :
      (∫ ε, tau p + 3 * (HA ε - C ε) - 2 * (AX ε - LX) - 2 * (AY ε - LY)
        ∂seedLaw D.L.ι) = tau p + 3 * ((∫ ε, HA ε ∂seedLaw D.L.ι) -
          ∫ ε, C ε ∂seedLaw D.L.ι) -
        2 * ((∫ ε, AX ε ∂seedLaw D.L.ι) - LX) -
        2 * ((∫ ε, AY ε ∂seedLaw D.L.ι) - LY) := by
    rw [integral_sub
      (f := fun ε => tau p + 3 * (HA ε - C ε) - 2 * (AX ε - LX))
      (g := fun ε => 2 * (AY ε - LY))
      (((integrable_const _).add ((hA.sub hC).const_mul 3)).sub
        ((hX.sub (integrable_const LX)).const_mul 2))
      ((hY.sub (integrable_const LY)).const_mul 2),
      integral_sub
        (f := fun ε => tau p + 3 * (HA ε - C ε))
        (g := fun ε => 2 * (AX ε - LX))
        ((integrable_const _).add ((hA.sub hC).const_mul 3))
        ((hX.sub (integrable_const LX)).const_mul 2),
      integral_add (f := fun _ => tau p) (g := fun ε => 3 * (HA ε - C ε))
        (integrable_const _) ((hA.sub hC).const_mul 3),
      integral_const_mul, integral_const_mul, integral_const_mul,
      integral_sub hA hC, integral_sub hX (integrable_const LX),
      integral_sub hY (integrable_const LY)]
    simp
  rw [hint, expected_score_eq D (integrable_winnerScore D)] at havg
  have hXL := average_winner_information_lower D (fun z : α × β => z.1)
  have hYL := average_winner_information_lower D (fun z : α × β => z.2)
  change LX ≤ ∫ ε, AX ε ∂seedLaw D.L.ι at hXL
  change LY ≤ ∫ ε, AY ε ∂seedLaw D.L.ι at hYL
  change Dwdefect D ≤ 3 * ((∫ ε, HA ε ∂seedLaw D.L.ι) -
    ∫ ε, C ε ∂seedLaw D.L.ι)
  linarith

/-- Interpolating the conditional and unconditional calibrated bounds saves
half of the old-label conditional-information budget. -/
theorem Dwdefect_le_three_halves_Bq_add_three_seedLeak (K : Clustering D) :
    Dwdefect D ≤ (3 / 2 : ℝ) * D.Bq + 3 * (concreteRaceQuantities D K).seedLeak := by
  have hcell := Rcell_le_with_coordinate_cancellation D
  have hfirst := Dwdefect_le_Rcell_add_integral_condInfo D
  have hsecond := Dwdefect_le_three_winnerEntropy_sub_condInfo D
  have hid := (concreteRaceQuantities D K).winner_entropy_identity
  rw [K.Sinfo_eq_bZ] at hid
  change raceWinnerEntropy D = bZ D + (concreteRaceQuantities D K).seedLeak at hid
  linarith

/-- The sharpened cancellation ledger for the actual shared race. -/
theorem T_le_M_add_five_halves_Bq_add_three_seedLeak (K : Clustering D) :
    T p ≤ D.M + (5 / 2 : ℝ) * D.Bq + 3 * (concreteRaceQuantities D K).seedLeak := by
  have hdefect := Dwdefect_le_three_halves_Bq_add_three_seedLeak D K
  have hint := integrable_winnerScore D
  have havg : (∫ ε, (winnerLatent D ε).score ∂seedLaw D.L.ι) ≤
      D.M + (5 / 2 : ℝ) * D.Bq + 3 * (concreteRaceQuantities D K).seedLeak := by
    rw [expected_score_eq D hint, D.tau_eq_M_add_Bq]
    linarith
  obtain ⟨ε, hε⟩ := exists_good_seed D _ hint havg
  exact (T_le_score (winnerLatent D ε) (winnerLatent_isDet D ε)).trans hε

end Race

end stoch_to_det
