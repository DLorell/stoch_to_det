import stoch_to_det.PoweredRaceEntropy

/-! Conditioning the shared-race entropy bound on an observed coordinate. -/

namespace stoch_to_det

open Finset MeasureTheory

private lemma coordinate_condMI_eq_sum
    {Ω Γ Δ Ξ : Type*} [Fintype Ω] [Fintype Γ] [Fintype Δ] [Fintype Ξ]
    [DecidableEq Γ] [DecidableEq Δ] [DecidableEq Ξ]
    {m : Ω → ℝ} (hm : IsPMF m) (f : Ω → Γ) (g : Ω → Δ) (h : Ω → Ξ) :
    condMI f g h m = ∑ k, MI f g (fun z => if h z = k then m z else 0) := by
  let mh : Ξ → Ω → ℝ := fun k z => if h z = k then m z else 0
  have hF := Hvar_pair_eq_sum_fibers hm f h
  have hG := Hvar_pair_eq_sum_fibers hm g h
  have hFG := Hvar_pair_eq_sum_fibers hm (fun z => (f z, g z)) h
  change Hvar (fun z => (f z, h z)) m = Hvar h m + ∑ k, H (push f (mh k)) at hF
  change Hvar (fun z => (g z, h z)) m = Hvar h m + ∑ k, H (push g (mh k)) at hG
  change Hvar (fun z => ((f z, g z), h z)) m = Hvar h m +
    ∑ k, H (push (fun z => (f z, g z)) (mh k)) at hFG
  have hAssoc : Hvar (fun z => (f z, g z, h z)) m =
      Hvar (fun z => ((f z, g z), h z)) m := by
    simpa using Hvar_equiv hm (fun z => ((f z, g z), h z))
      (Equiv.prodAssoc Γ Δ Ξ)
  unfold condMI
  rw [hF, hG, hAssoc, hFG]
  simp only [MI, Hvar, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  ring

namespace SharedRace

universe u v
variable {Ω : Type u} {κ : Type} {Γ : Type v}
  [Fintype Ω] [Fintype κ] [Fintype Γ]
  [DecidableEq Ω] [DecidableEq κ] [DecidableEq Γ] [Nonempty κ]

lemma integrable_sharedWinner_code (r : Ω → κ → ℝ) (F : (Ω → κ) → ℝ) :
    Integrable (fun E : κ → ℝ => F (sharedWinner r E)) (seedLaw κ) := by
  letI : MeasurableSpace κ := ⊤
  have hA : Measurable (fun E : κ → ℝ => sharedWinner r E) := by
    apply measurable_pi_lambda
    intro z
    unfold sharedWinner weightedLexWinner
    apply measurable_lexMax
    intro i
    exact measurable_const.add (measurable_pi_apply i)
  apply Integrable.of_bound
    ((measurable_of_finite F).comp hA).aestronglyMeasurable
    (∑ A : Ω → κ, ‖F A‖)
  filter_upwards [] with E
  exact Finset.single_le_sum (fun A _ => norm_nonneg (F A))
    (Finset.mem_univ (sharedWinner r E))

/-- Homogeneous extension of any source-law entropy comparison. -/
theorem sharedRaceEntropy_le_of_finMeas
    (a b : ℝ)
    (h : ∀ (μ : Ω → ℝ) (r : Ω → κ → ℝ),
      IsPMF μ → (∀ z, μ z ≠ 0 → IsPMF (r z)) →
      (∀ z, μ z ≠ 0 → ∀ i, 0 < r z i) →
      sharedRaceEntropy μ r ≤ a * MI Prod.fst Prod.snd (posteriorJoint μ r) +
        b * categoricalMismatch μ r)
    {μ : Ω → ℝ} {r : Ω → κ → ℝ} (hμ : IsFinMeas μ)
    (hr : ∀ z, μ z ≠ 0 → IsPMF (r z))
    (hrpos : ∀ z, μ z ≠ 0 → ∀ i, 0 < r z i) :
    sharedRaceEntropy μ r ≤ a * MI Prod.fst Prod.snd (posteriorJoint μ r) +
      b * categoricalMismatch μ r := by
  have hm0 : 0 ≤ mass μ := Finset.sum_nonneg fun z _ => hμ z
  by_cases hm : mass μ = 0
  · have hzero : μ = 0 := by
      funext z
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun z _ => hμ z)).mp hm z (mem_univ z)
    simp [hzero, sharedRaceEntropy, posteriorJoint, categoricalMismatch, MI, Hvar, H,
      push, mass]
  have hmp : 0 < mass μ := lt_of_le_of_ne hm0 (Ne.symm hm)
  let ν : Ω → ℝ := fun z => μ z / mass μ
  have hν : IsPMF ν := by
    refine ⟨fun z => div_nonneg (hμ z) hm0, ?_⟩
    change (∑ z, μ z / mass μ) = 1
    rw [← Finset.sum_div]
    exact div_self hm
  have hs := h ν r hν
    (fun z hz => hr z (fun hh => hz (by simp [ν, hh])))
    (fun z hz => hrpos z (fun hh => hz (by simp [ν, hh])))
  have hrec : (fun z => mass μ * ν z) = μ := by
    funext z
    dsimp [ν]
    field_simp
  have hH : mass μ * sharedRaceEntropy ν r = sharedRaceEntropy μ r := by
    unfold sharedRaceEntropy
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with E
    rw [← H_smul (isFinMeas_push hν.isFinMeas) hm0, ← push_smul, hrec]
  have hMI : mass μ * MI Prod.fst Prod.snd (posteriorJoint ν r) =
      MI Prod.fst Prod.snd (posteriorJoint μ r) := by
    have hfin := (posteriorJoint_isPMF_of_support hν
      (fun z hz => hr z (fun hh => hz (by simp [ν, hh])))).isFinMeas
    rw [← MI_smul hfin Prod.fst Prod.snd hm0]
    congr 1
    funext zi
    change mass μ * (ν zi.1 * r zi.1 zi.2) = μ zi.1 * r zi.1 zi.2
    rw [← mul_assoc, congrFun hrec zi.1]
  have hd : mass μ * categoricalMismatch ν r = categoricalMismatch μ r := by
    unfold categoricalMismatch
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro z _
    rw [← mul_assoc, congrFun hrec z]
  have hh := mul_le_mul_of_nonneg_left hs hm0
  rw [hH, mul_add] at hh
  have heq : mass μ * (a * MI Prod.fst Prod.snd (posteriorJoint ν r)) +
      mass μ * (b * categoricalMismatch ν r) =
      a * MI Prod.fst Prod.snd (posteriorJoint μ r) + b * categoricalMismatch μ r := by
    calc
      _ = a * (mass μ * MI Prod.fst Prod.snd (posteriorJoint ν r)) +
          b * (mass μ * categoricalMismatch ν r) := by ring
      _ = _ := by rw [hMI, hd]
  rwa [heq] at hh

/-- A universal shared-race entropy estimate can be conditioned on any finite
function of the source, without changing its mismatch term. -/
theorem conditional_entropy_le_of_uniform_entropy_bound
    (a b : ℝ)
    (h : ∀ (μ : Ω → ℝ) (r : Ω → κ → ℝ),
      IsPMF μ → (∀ z, μ z ≠ 0 → IsPMF (r z)) →
      (∀ z, μ z ≠ 0 → ∀ i, 0 < r z i) →
      sharedRaceEntropy μ r ≤ a * MI Prod.fst Prod.snd (posteriorJoint μ r) +
        b * categoricalMismatch μ r)
    {μ : Ω → ℝ} {r : Ω → κ → ℝ} (hμ : IsPMF μ)
    (hr : ∀ z, μ z ≠ 0 → IsPMF (r z))
    (hrpos : ∀ z, μ z ≠ 0 → ∀ i, 0 < r z i) (g : Ω → Γ) :
    (∫ E : κ → ℝ, condH (sharedWinner r E) g μ ∂seedLaw κ) ≤
      a * condMI Prod.fst Prod.snd (fun zi : Ω × κ => g zi.1) (posteriorJoint μ r) +
        b * categoricalMismatch μ r := by
  let fiber : Γ → Ω → ℝ := fun c z => if g z = c then μ z else 0
  have hfin (c : Γ) : IsFinMeas (fiber c) := by
    intro z
    dsimp [fiber]
    split <;> simp_all [hμ.nonneg z]
  have hs (c : Γ) : sharedRaceEntropy (fiber c) r ≤
      a * MI Prod.fst Prod.snd (posteriorJoint (fiber c) r) +
        b * categoricalMismatch (fiber c) r := by
    apply sharedRaceEntropy_le_of_finMeas a b h (hfin c)
    · intro z hz
      apply hr z
      intro hh
      simp [fiber, hh] at hz
    · intro z hz
      apply hrpos z
      intro hh
      simp [fiber, hh] at hz
  have hpost (c : Γ) : posteriorJoint (fiber c) r =
      fun zi : Ω × κ => if g zi.1 = c then posteriorJoint μ r zi else 0 := by
    funext zi
    by_cases hh : g zi.1 = c <;> simp [posteriorJoint, fiber, hh]
  have hd : (∑ c, categoricalMismatch (fiber c) r) = categoricalMismatch μ r := by
    unfold categoricalMismatch
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro z _
    simp [fiber]
  calc
    _ = ∑ c, sharedRaceEntropy (fiber c) r := by
      simp_rw [condH_eq_sum_H_fibers hμ]
      rw [integral_finsetSum]
      · rfl
      · intro c _
        exact integrable_sharedWinner_code r (fun A => H (push A (fiber c)))
    _ ≤ ∑ c, (a * MI Prod.fst Prod.snd (posteriorJoint (fiber c) r) +
        b * categoricalMismatch (fiber c) r) := Finset.sum_le_sum fun c _ => hs c
    _ = _ := by
      simp_rw [hpost]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hd,
        ← coordinate_condMI_eq_sum (posteriorJoint_isPMF_of_support hμ hr)]

end SharedRace

private lemma coordinate_condMI_le_of_comp
    {Ω Γ Δ Ξ Δ' : Type*} [Fintype Ω] [Fintype Γ] [Fintype Δ] [Fintype Ξ]
    [Fintype Δ'] [DecidableEq Γ] [DecidableEq Δ] [DecidableEq Ξ] [DecidableEq Δ']
    {m : Ω → ℝ} (hm : IsPMF m) (f : Ω → Γ) (g : Ω → Δ) (h : Ω → Ξ)
    (u : Δ → Δ') : condMI f (fun z => u (g z)) h m ≤ condMI f g h m := by
  let enc : Δ → Δ' × Δ := fun d => (u d, d)
  have hleft : Function.LeftInverse Prod.snd enc := fun _ => rfl
  have hH : Hvar (fun z => ((u (g z), g z), h z)) m = Hvar (fun z => (g z, h z)) m := by
    exact Hvar_eq_of_leftInverse hm (fun z => (g z, h z))
      (fun d => (enc d.1, d.2)) (fun d => (d.1.2, d.2)) (fun _ => rfl)
  have hT : Hvar (fun z => ((u (g z), g z), f z, h z)) m =
      Hvar (fun z => (g z, f z, h z)) m := by
    exact Hvar_eq_of_leftInverse hm (fun z => (g z, f z, h z))
      (fun d => (enc d.1, d.2)) (fun d => (d.1.2, d.2)) (fun _ => rfl)
  have hEq : condMI (fun z => (u (g z), g z)) f h m = condMI g f h m := by
    unfold condMI
    rw [hH, hT]
  have hc := condMI_pair_left_local hm (fun z => u (g z)) g f h
  have hn := condMI_nonneg hm g f (fun z => (h z, u (g z)))
  rw [hEq, condMI_comm_local hm g f h,
    condMI_comm_local hm (fun z => u (g z)) f h] at hc
  linarith

section Grouped

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
variable {p : α × β → ℝ} (D : SeedSetup p) (K : Clustering D)

private lemma coordinate_cluster_posterior_push :
    SharedRace.posteriorJoint p (fun z c => K.sigma c z) =
      push (fun lz : D.L.ι × (α × β) => (lz.2, K.cl lz.1)) D.L.joint := by
  funext zc
  rcases zc with ⟨z,c⟩
  unfold SharedRace.posteriorJoint Clustering.sigma push
  rw [Finset.mul_sum]
  simp_rw [Finset.sum_filter]
  rw [Fintype.sum_prod_type]
  simp only [Prod.mk.injEq]
  apply Finset.sum_congr rfl
  intro l _
  have hz : (∑ z', if z' = z ∧ K.cl l = c then D.L.joint (l,z') else 0) =
      if K.cl l = c then D.L.joint (l,z) else 0 := by
    by_cases hc : K.cl l = c <;> simp [hc]
  rw [hz]
  by_cases hc : K.cl l = c
  · simp only [hc, if_true]
    exact p_mul_post D l z
  · simp [hc]

private lemma coordinate_cluster_condMI_le
    {Γ : Type*} [Fintype Γ] [DecidableEq Γ] (g : α × β → Γ) :
    condMI Prod.fst Prod.snd (fun zi : (α × β) × K.κ => g zi.1)
        (SharedRace.posteriorJoint p (fun z c => K.sigma c z)) ≤
      condMI Prod.fst Prod.snd (fun lz : D.L.ι × (α × β) => g lz.2) D.L.joint := by
  rw [coordinate_cluster_posterior_push D K]
  have hp : condMI Prod.fst Prod.snd (fun zi : (α × β) × K.κ => g zi.1)
      (push (fun lz : D.L.ι × (α × β) => (lz.2, K.cl lz.1)) D.L.joint) =
      condMI Prod.snd (fun lz : D.L.ι × (α × β) => K.cl lz.1)
        (fun lz => g lz.2) D.L.joint := by
    unfold condMI Hvar
    simp only [push_push, Function.comp_def]
  rw [hp, condMI_comm_local D.L.joint_isPMF Prod.fst Prod.snd]
  exact coordinate_condMI_le_of_comp D.L.joint_isPMF Prod.snd Prod.fst
    (fun lz => g lz.2) K.cl

private lemma coordinate_condH_grouped_eq
    {Γ : Type*} [Fintype Γ] [DecidableEq Γ] (g : α × β → Γ) :
    (∫ ε, condH (winner D ε) g p ∂seedLaw D.L.ι) =
      ∫ E, condH (SharedRace.sharedWinner (fun z c => K.sigma c z) E) g p
        ∂seedLaw K.κ := by
  letI : Nonempty K.κ := Nonempty.map K.cl (Latent.nonempty_ι D.L)
  let F : (K.κ → ℝ) → ℝ := fun E =>
    condH (SharedRace.sharedWinner (fun z c => K.sigma c z) E) g p
  have heq : (fun ε => condH (winner D ε) g p) =ᵐ[seedLaw D.L.ι]
      fun ε => F (groupedG K ε) := by
    filter_upwards [grouped_winner_agrees_ae D K,
      groupedClusterWinner_ae_eq_lex_after_grouping D K] with ε hlabel hcluster
    let f : (α × β) → K.κ :=
      SharedRace.sharedWinner (fun z c => K.sigma c z) (groupedG K ε)
    let u : K.κ → D.L.ι := fun c => (groupedWithinWinner K ε c).1
    have hleft : Function.LeftInverse K.cl u := fun c => (groupedWithinWinner K ε c).2
    have hpoint (z : α × β) (hz : z ∈ support p) : winner D ε z = u (f z) := by
      rw [congrFun hlabel z]
      simp only [groupedLabelWinner, hz, if_true, u, f]
      rw [congrFun hcluster z]
      rw [sharedRace_sharedWinner_eq_groupedClusterLexWinner K]
    have hpush : push (fun z => (winner D ε z, g z)) p =
        push (fun z => (u (f z), g z)) p := by
      funext ag
      unfold push
      simp_rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro z _
      by_cases hz : z ∈ support p
      · rw [hpoint z hz]
      · have hpz : p z = 0 := by simpa [support] using hz
        simp [hpz]
    have hH : Hvar (fun z => (u (f z), g z)) p = Hvar (fun z => (f z, g z)) p :=
      Hvar_eq_of_leftInverse D.isPMF (fun z => (f z,g z))
        (fun cg => (u cg.1,cg.2)) (fun ag => (K.cl ag.1,ag.2))
        (fun cg => by simp [hleft cg.1])
    change condH (winner D ε) g p = condH f g p
    unfold condH
    rw [show Hvar (fun z => (winner D ε z, g z)) p =
        Hvar (fun z => (u (f z), g z)) p by exact congrArg H hpush, hH]
  have hG : Measurable (groupedG K) := measurable_fst.comp (groupedPair_measurable K)
  have hF : AEStronglyMeasurable F (Measure.map (groupedG K) (seedLaw D.L.ι)) := by
    rw [grouped_gumbel_law K]
    exact (SharedRace.integrable_sharedWinner_code (fun z c => K.sigma c z)
      (fun A => condH A g p)).aestronglyMeasurable
  calc
    _ = ∫ ε, F (groupedG K ε) ∂seedLaw D.L.ι := integral_congr_ae heq
    _ = ∫ E, F E ∂Measure.map (groupedG K) (seedLaw D.L.ι) :=
      (integral_map hG.aemeasurable hF).symm
    _ = _ := by rw [grouped_gumbel_law K]

/-- Coordinate conditioning preserves the universal race bound, with the
original latent's conditional information and the quotient mismatch. -/
theorem coordinate_condH_le_of_uniform_entropy_bound
    {Γ : Type*} [Fintype Γ] [DecidableEq Γ] (g : α × β → Γ)
    (a b : ℝ) (ha : 0 ≤ a)
    (h : ∀ (μ : α × β → ℝ) (r : (α × β) → K.κ → ℝ),
      IsPMF μ → (∀ z, μ z ≠ 0 → IsPMF (r z)) →
      (∀ z, μ z ≠ 0 → ∀ i, 0 < r z i) →
      SharedRace.sharedRaceEntropy μ r ≤
        a * MI Prod.fst Prod.snd (SharedRace.posteriorJoint μ r) +
          b * SharedRace.categoricalMismatch μ r) :
    (∫ ε, condH (winner D ε) g p ∂seedLaw D.L.ι) ≤
      a * condMI Prod.fst Prod.snd (fun lz : D.L.ι × (α × β) => g lz.2) D.L.joint +
        b * K.dMis := by
  letI : Nonempty K.κ := Nonempty.map K.cl (Latent.nonempty_ι D.L)
  have hr (z : α × β) (hz : p z ≠ 0) : IsPMF (fun c => K.sigma c z) := by
    refine ⟨fun c => (K.sigma_pos c z (by simpa [support] using hz)).le, ?_⟩
    unfold mass Clustering.sigma
    rw [Finset.sum_fiberwise]
    exact sum_post_of_pos D z (lt_of_le_of_ne (D.isPMF.nonneg z) (Ne.symm hz))
  have hpos (z : α × β) (hz : p z ≠ 0) (c : K.κ) : 0 < K.sigma c z :=
    K.sigma_pos c z (by simpa [support] using hz)
  have hcond := SharedRace.conditional_entropy_le_of_uniform_entropy_bound a b h
    D.isPMF hr hpos g
  rw [← coordinate_condH_grouped_eq D K g] at hcond
  have hd : SharedRace.categoricalMismatch p (fun z c => K.sigma c z) = K.dMis :=
    (K.dMis_eq).symm
  rw [hd] at hcond
  exact hcond.trans (add_le_add
    (mul_le_mul_of_nonneg_left (coordinate_cluster_condMI_le D K g) ha) le_rfl)

/-- The two coordinate entropy bounds share the same categorical mismatch. -/
theorem coordinate_entropy_sum_le_of_uniform_entropy_bound
    (a b : ℝ) (ha : 0 ≤ a)
    (h : ∀ (μ : α × β → ℝ) (r : (α × β) → K.κ → ℝ),
      IsPMF μ → (∀ z, μ z ≠ 0 → IsPMF (r z)) →
      (∀ z, μ z ≠ 0 → ∀ i, 0 < r z i) →
      SharedRace.sharedRaceEntropy μ r ≤
        a * MI Prod.fst Prod.snd (SharedRace.posteriorJoint μ r) +
          b * SharedRace.categoricalMismatch μ r) :
    (∫ ε, condH (winner D ε) Prod.fst p ∂seedLaw D.L.ι) +
        (∫ ε, condH (winner D ε) Prod.snd p ∂seedLaw D.L.ι) ≤
      a * D.Bq + 2 * b * K.dMis := by
  have hX := coordinate_condH_le_of_uniform_entropy_bound D K Prod.fst a b ha h
  have hY := coordinate_condH_le_of_uniform_entropy_bound D K Prod.snd a b ha h
  have hZX : Hvar (fun lz : D.L.ι × (α × β) => (lz.2, lz.2.1)) D.L.joint =
      Hvar (fun lz : D.L.ι × (α × β) => (lz.2.2, lz.2.1)) D.L.joint :=
    Hvar_eq_of_leftInverse D.L.joint_isPMF (fun lz => (lz.2.2,lz.2.1))
      (fun yx => ((yx.2,yx.1),yx.2)) (fun zx => (zx.1.2,zx.2)) (fun _ => rfl)
  have hLZX : Hvar (fun lz : D.L.ι × (α × β) => (lz.1, lz.2, lz.2.1)) D.L.joint =
      Hvar (fun lz : D.L.ι × (α × β) => (lz.1, lz.2.2, lz.2.1)) D.L.joint :=
    Hvar_eq_of_leftInverse D.L.joint_isPMF (fun lz => (lz.1,lz.2.2,lz.2.1))
      (fun lyx => (lyx.1,(lyx.2.2,lyx.2.1),lyx.2.2))
      (fun lzx => (lzx.1,lzx.2.1.2,lzx.2.2)) (fun _ => rfl)
  have hZY : Hvar (fun lz : D.L.ι × (α × β) => (lz.2, lz.2.2)) D.L.joint =
      Hvar (fun lz : D.L.ι × (α × β) => (lz.2.1, lz.2.2)) D.L.joint :=
    Hvar_eq_of_leftInverse D.L.joint_isPMF (fun lz => (lz.2.1,lz.2.2))
      (fun xy => ((xy.1,xy.2),xy.2)) (fun zy => (zy.1.1,zy.2)) (fun _ => rfl)
  have hLZY : Hvar (fun lz : D.L.ι × (α × β) => (lz.1, lz.2, lz.2.2)) D.L.joint =
      Hvar (fun lz : D.L.ι × (α × β) => (lz.1, lz.2.1, lz.2.2)) D.L.joint :=
    Hvar_eq_of_leftInverse D.L.joint_isPMF (fun lz => (lz.1,lz.2.1,lz.2.2))
      (fun lxy => (lxy.1,(lxy.2.1,lxy.2.2),lxy.2.2))
      (fun lzy => (lzy.1,lzy.2.1.1,lzy.2.2)) (fun _ => rfl)
  have hIX : condMI Prod.fst Prod.snd (fun lz : D.L.ι × (α × β) => lz.2.1)
      D.L.joint = condMI Prod.fst (fun lz => lz.2.2) (fun lz => lz.2.1) D.L.joint := by
    unfold condMI
    rw [hZX, hLZX]
  have hIY : condMI Prod.fst Prod.snd (fun lz : D.L.ι × (α × β) => lz.2.2)
      D.L.joint = condMI Prod.fst (fun lz => lz.2.1) (fun lz => lz.2.2) D.L.joint := by
    unfold condMI
    rw [hZY, hLZY]
  rw [hIX] at hX
  rw [hIY] at hY
  unfold SeedSetup.Bq
  nlinarith only [hX, hY]

end Grouped

end stoch_to_det
