import stoch_to_det.Envelope

/-! Lifting a latent of a coordinatewise coarsening back to the original source. -/

namespace stoch_to_det.SourceCoarsening

open Finset

section Joint
variable {X Y : Type*} {K : Type} [Fintype X] [Fintype Y] [Fintype K]
  [DecidableEq X] [DecidableEq Y] [DecidableEq K]

private def priorOf (r : K × (X × Y) → ℝ) (k : K) : ℝ := ∑ z, r (k, z)

omit [Fintype K] [DecidableEq X] [DecidableEq Y] [DecidableEq K] in
private lemma joint_zero {r : K × (X × Y) → ℝ} (hr : IsFinMeas r)
    {k : K} (hk : priorOf r k = 0) (z : X × Y) : r (k, z) = 0 := by
  have h := Finset.single_le_sum (fun t (_ : t ∈ (univ : Finset (X × Y))) =>
    hr (k, t)) (Finset.mem_univ z)
  change r (k, z) ≤ priorOf r k at h
  exact le_antisymm (hk ▸ h) (hr _)

/-- A finite joint law with the specified source marginal defines a latent.
Zero-prior labels are filled with the source law. -/
noncomputable def ofJoint {p : X × Y → ℝ} (hp : IsPMF p)
    (r : K × (X × Y) → ℝ) (hr : IsPMF r) (hsource : push Prod.snd r = p) :
    Latent p where
  ι := K
  fin := inferInstance
  dec := inferInstance
  prior := priorOf r
  comp := fun k z => if priorOf r k = 0 then p z else r (k, z) / priorOf r k
  prior_isPMF := by
    constructor
    · intro k
      exact Finset.sum_nonneg fun z _ => hr.nonneg (k, z)
    · simpa [mass, priorOf, Fintype.sum_prod_type] using hr.total
  comp_isPMF := by
    intro k
    by_cases hk : priorOf r k = 0
    · simpa [hk] using hp
    · constructor
      · intro z
        simp only [hk, if_false]
        exact div_nonneg (hr.nonneg _) (Finset.sum_nonneg fun z _ => hr.nonneg (k, z))
      · simp only [mass, hk, if_false, ← Finset.sum_div]
        exact div_self hk
  mixture := by
    intro z
    have heq (k : K) : priorOf r k *
        (if priorOf r k = 0 then p z else r (k, z) / priorOf r k) = r (k, z) := by
      by_cases hk : priorOf r k = 0
      · simp [hk, joint_zero hr.isFinMeas hk z]
      · simp [hk, mul_div_cancel₀ _ hk]
    simp_rw [heq]
    have h := congrFun hsource z
    simpa [push, Finset.sum_filter, Fintype.sum_prod_type] using h

theorem ofJoint_joint {p : X × Y → ℝ} (hp : IsPMF p)
    (r : K × (X × Y) → ℝ) (hr : IsPMF r) (hsource : push Prod.snd r = p) :
    (ofJoint hp r hr hsource).joint = r := by
  funext ⟨k, z⟩
  change priorOf r k *
    (if priorOf r k = 0 then p z else r (k, z) / priorOf r k) = r (k, z)
  by_cases hk : priorOf r k = 0
  · simp [hk, joint_zero hr.isFinMeas hk z]
  · simp [hk, mul_div_cancel₀ _ hk]

theorem ofJoint_score {p : X × Y → ℝ} (hp : IsPMF p)
    (r : K × (X × Y) → ℝ) (hr : IsPMF r) (hsource : push Prod.snd r = p) :
    (ofJoint hp r hr hsource).score =
      condMI (fun v => v.2.1) (fun v => v.2.2) Prod.fst r +
      condMI Prod.fst (fun v => v.2.1) (fun v => v.2.2) r +
      condMI Prod.fst (fun v => v.2.2) (fun v => v.2.1) r := by
  change condMI (fun v : K × (X × Y) => v.2.1) (fun v => v.2.2) Prod.fst
      (ofJoint hp r hr hsource).joint +
      condMI Prod.fst (fun v => v.2.1) (fun v => v.2.2) (ofJoint hp r hr hsource).joint +
      condMI Prod.fst (fun v => v.2.2) (fun v => v.2.1) (ofJoint hp r hr hsource).joint = _
  rw [ofJoint_joint]
  rfl

end Joint

section Channel
variable {Z W : Type*} {K : Type} [Fintype Z] [Fintype W] [Fintype K]
  [DecidableEq Z] [DecidableEq W] [DecidableEq K]

/-- Joint law formed by sampling a source and then a finite channel. -/
noncomputable def channelJoint (p : Z → ℝ) (r : Z → K → ℝ) : K × Z → ℝ :=
  fun v => p v.2 * r v.2 v.1

omit [DecidableEq K] in
lemma channelJoint_source (p : Z → ℝ) (r : Z → K → ℝ)
    (hr : ∀ z, IsPMF (r z)) : push Prod.snd (channelJoint p r) = p := by
  funext z
  have ht : ∑ k, r z k = 1 := (hr z).total
  simp [push, Finset.sum_filter, Fintype.sum_prod_type, channelJoint,
    ← Finset.mul_sum, ht]

omit [DecidableEq K] in
lemma channelJoint_isPMF {p : Z → ℝ} (hp : IsPMF p) (r : Z → K → ℝ)
    (hr : ∀ z, IsPMF (r z)) : IsPMF (channelJoint p r) := by
  constructor
  · intro v
    exact mul_nonneg (hp.nonneg _) ((hr _).nonneg _)
  · have h := mass_push Prod.snd (channelJoint p r)
    rw [channelJoint_source p r hr, hp.total] at h
    exact h.symm

omit [Fintype W] [DecidableEq Z] in
lemma channelJoint_coarsen (p : Z → ℝ) (r : W → K → ℝ) (h : Z → W) :
    push (fun v : K × Z => (v.1, h v.2)) (channelJoint p (r ∘ h)) =
      channelJoint (push h p) r := by
  funext ⟨k, w⟩
  simp only [push, Finset.sum_filter, Fintype.sum_prod_type,
    channelJoint, Function.comp_apply, Prod.mk.injEq]
  rw [Finset.sum_comm]
  simp only [ite_and, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro z _
  by_cases hz : h z = w <;> simp [hz]

private lemma MI_push {Ω A B C : Type*} [Fintype Ω] [Fintype A]
    [Fintype B] [Fintype C] [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (m : Ω → ℝ) (h : Ω → A) (f : A → B) (g : A → C) :
    MI f g (push h m) = MI (f ∘ h) (g ∘ h) m := by
  simp only [MI, Hvar, push_push, Function.comp_def]

private lemma channelJoint_MI {p : Z → ℝ} (hp : IsPMF p)
    (r : Z → K → ℝ) (hr : ∀ z, IsPMF (r z)) :
    MI Prod.fst Prod.snd (channelJoint p r) =
      H (push Prod.fst (channelJoint p r)) - ∑ z, p z * H (r z) := by
  have hid : push (fun v : K × Z => (v.1, v.2)) (channelJoint p r) =
      channelJoint p r := by
    funext v
    simp [push, Finset.sum_filter]
  have he := H_prod_eq_snd_add_fibers (channelJoint_isPMF hp r hr)
  simp only [channelJoint, H_smul (hr _).isFinMeas (hp.nonneg _)] at he
  unfold MI Hvar
  rw [hid]
  linarith

/-- A channel depending only on a coarse observation preserves exactly its
mutual information when that observation is refined. -/
theorem channelJoint_MI_coarsen {p : Z → ℝ} (hp : IsPMF p)
    (r : W → K → ℝ) (hr : ∀ w, IsPMF (r w)) (h : Z → W) :
    MI Prod.fst Prod.snd (channelJoint p (r ∘ h)) =
      MI Prod.fst Prod.snd (channelJoint (push h p) r) := by
  have hprior : push Prod.fst (channelJoint (push h p) r) =
      push Prod.fst (channelJoint p (r ∘ h)) := by
    rw [← channelJoint_coarsen p r h, push_push]
    rfl
  rw [channelJoint_MI hp (r ∘ h) (fun z => hr (h z)),
    channelJoint_MI (isPMF_push hp) r hr, hprior, sum_push_mul h p (fun w => H (r w))]
  rfl

end Channel

section Posterior
variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
  {q : A × B → ℝ}

/-- A universe-polymorphic posterior, using the prior at null source atoms. -/
noncomputable def posterior (V : Latent q) (z : A × B) (k : V.ι) : ℝ :=
  if q z = 0 then V.prior k else V.joint (k, z) / q z

lemma posterior_isPMF (hq : IsPMF q) (V : Latent q) (z : A × B) :
    IsPMF (posterior V z) := by
  by_cases hz : q z = 0
  · have heq : posterior V z = V.prior := by funext k; simp [posterior, hz]
    rw [heq]
    exact V.prior_isPMF
  · constructor
    · intro k
      simp only [posterior, hz, if_false]
      exact div_nonneg (V.joint_isPMF.nonneg _) (hq.nonneg z)
    · have hs : ∑ k, V.joint (k, z) = q z := V.mixture z
      simp [mass, posterior, hz, ← Finset.sum_div, hs]

lemma source_mul_posterior (V : Latent q) (z : A × B) (k : V.ι) :
    q z * posterior V z k = V.joint (k, z) := by
  by_cases hz : q z = 0
  · have hs : ∑ j, V.joint (j, z) = 0 := (V.mixture z).trans hz
    have hle := Finset.single_le_sum (fun j (_ : j ∈ (univ : Finset V.ι)) =>
      V.joint_isPMF.nonneg (j, z)) (Finset.mem_univ k)
    have hj : V.joint (k, z) = 0 := le_antisymm (hs ▸ hle) (V.joint_isPMF.nonneg _)
    simp [posterior, hz, hj]
  · simp [posterior, hz, mul_div_cancel₀ _ hz]

end Posterior

section Lift
variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
  [DecidableEq X] [DecidableEq Y] [DecidableEq A] [DecidableEq B]
  {p : X × Y → ℝ}

/-- Pull back the coarse posterior along the coordinate maps. -/
noncomputable def liftJoint (p : X × Y → ℝ) (f : X → A) (g : Y → B)
    (V : Latent (push (Prod.map f g) p)) : V.ι × (X × Y) → ℝ :=
  channelJoint p (posterior V ∘ Prod.map f g)

lemma liftJoint_isPMF (hp : IsPMF p) (f : X → A) (g : Y → B)
    (V : Latent (push (Prod.map f g) p)) : IsPMF (liftJoint p f g V) :=
  channelJoint_isPMF hp _ fun z =>
    posterior_isPMF (isPMF_push hp) V (Prod.map f g z)

lemma liftJoint_source (hp : IsPMF p) (f : X → A) (g : Y → B)
    (V : Latent (push (Prod.map f g) p)) : push Prod.snd (liftJoint p f g V) = p :=
  channelJoint_source p _ fun z =>
    posterior_isPMF (isPMF_push hp) V (Prod.map f g z)

omit [DecidableEq X] [DecidableEq Y] in
private lemma coarse_channel (f : X → A) (g : Y → B)
    (V : Latent (push (Prod.map f g) p)) :
    channelJoint (push (Prod.map f g) p) (posterior V) = V.joint := by
  funext ⟨k, z⟩
  exact source_mul_posterior V z k

omit [DecidableEq X] [DecidableEq Y] in
lemma liftJoint_coarse (f : X → A) (g : Y → B)
    (V : Latent (push (Prod.map f g) p)) :
    push (fun v : V.ι × (X × Y) => (v.1, Prod.map f g v.2)) (liftJoint p f g V) =
      V.joint := by
  rw [liftJoint, channelJoint_coarsen, coarse_channel]

/-- The lifted latent retains the coarse latent alphabet. -/
noncomputable def liftLatent (hp : IsPMF p) (f : X → A) (g : Y → B)
    (V : Latent (push (Prod.map f g) p)) : Latent p :=
  ofJoint hp (liftJoint p f g V) (liftJoint_isPMF hp f g V) (liftJoint_source hp f g V)

lemma liftLatent_joint (hp : IsPMF p) (f : X → A) (g : Y → B)
    (V : Latent (push (Prod.map f g) p)) :
    (liftLatent hp f g V).joint = liftJoint p f g V :=
  ofJoint_joint hp _ _ _

/-- The lift adds no information about the full source beyond the coarse
source already used to sample the posterior. -/
theorem liftJoint_MI (hp : IsPMF p) (f : X → A) (g : Y → B)
    (V : Latent (push (Prod.map f g) p)) :
    MI Prod.fst Prod.snd (liftJoint p f g V) = MI Prod.fst Prod.snd V.joint := by
  rw [liftJoint, channelJoint_MI_coarsen hp _
    (posterior_isPMF (isPMF_push hp) V), coarse_channel]

/-- Lifting a coarse latent costs at most the information lost by the two
coordinate maps. The coarse source need not have full support. -/
theorem lift_score_le (hp : IsPMF p) (f : X → A) (g : Y → B)
    (V : Latent (push (Prod.map f g) p)) :
    (liftLatent hp f g V).score ≤
      V.score + Ixy p - Ixy (push (Prod.map f g) p) := by
  have hx : MI Prod.fst (fun v => v.2.1) V.joint ≤
      MI Prod.fst (fun v => v.2.1) (liftJoint p f g V) := by
    rw [← liftJoint_coarse f g V, MI_push]
    exact MI_le_of_comp (liftJoint_isPMF hp f g V) Prod.fst (fun v => v.2.1) f
  have hy : MI Prod.fst (fun v => v.2.2) V.joint ≤
      MI Prod.fst (fun v => v.2.2) (liftJoint p f g V) := by
    rw [← liftJoint_coarse f g V, MI_push]
    exact MI_le_of_comp (liftJoint_isPMF hp f g V) Prod.fst (fun v => v.2.2) g
  have hf := Latent.score_sub_Ixy hp (liftLatent hp f g V)
  have hc := Latent.score_sub_Ixy (isPMF_push hp) V
  rw [liftLatent_joint] at hf
  change (liftLatent hp f g V).score - Ixy p =
    3 * MI Prod.fst Prod.snd (liftJoint p f g V) -
    2 * MI Prod.fst (fun v => v.2.1) (liftJoint p f g V) -
    2 * MI Prod.fst (fun v => v.2.2) (liftJoint p f g V) at hf
  rw [liftJoint_MI hp f g V] at hf
  linarith

/-- Stochastic cost under deterministic coordinatewise coarsening satisfies
`τ(p) ≤ τ(coarse p) + I(p) - I(coarse p)`. -/
theorem tau_le_coarsened_add_Ixy_loss (hp : IsPMF p) (f : X → A) (g : Y → B) :
    tau p ≤ tau (push (Prod.map f g) p) + Ixy p - Ixy (push (Prod.map f g) p) := by
  obtain ⟨V, hV⟩ := exists_tau_optimal_latent (isPMF_push (f := Prod.map f g) hp)
  have h := (tau_le_score (liftLatent hp f g V)).trans (lift_score_le hp f g V)
  simpa only [hV] using h

/-- A deterministic coarse latent remains deterministic after the lift. -/
theorem liftLatent_isDet (hp : IsPMF p) (f : X → A) (g : Y → B)
    (V : Latent (push (Prod.map f g) p)) (hV : V.IsDet) :
    (liftLatent hp f g V).IsDet := by
  change ∀ z (k k' : V.ι), (liftLatent hp f g V).joint (k, z) ≠ 0 →
    (liftLatent hp f g V).joint (k', z) ≠ 0 → k = k'
  intro z k k' hk hk'
  rw [liftLatent_joint] at hk hk'
  have hle (j : V.ι) : liftJoint p f g V (j, z) ≤ V.joint (j, Prod.map f g z) := by
    rw [← liftJoint_coarse f g V]
    unfold push
    exact Finset.single_le_sum (fun v _ => (liftJoint_isPMF hp f g V).nonneg v)
      (by simp)
  apply hV (Prod.map f g z) k k'
  · change V.joint (k, Prod.map f g z) ≠ 0
    exact ne_of_gt ((lt_of_le_of_ne ((liftJoint_isPMF hp f g V).nonneg _)
      (Ne.symm hk)).trans_le (hle k))
  · change V.joint (k', Prod.map f g z) ≠ 0
    exact ne_of_gt ((lt_of_le_of_ne ((liftJoint_isPMF hp f g V).nonneg _)
      (Ne.symm hk')).trans_le (hle k'))

/-- The same information-loss bound holds for the deterministic optimum. -/
theorem T_le_coarsened_add_Ixy_loss (hp : IsPMF p) (f : X → A) (g : Y → B) :
    T p ≤ T (push (Prod.map f g) p) + Ixy p - Ixy (push (Prod.map f g) p) := by
  obtain ⟨V, hVdet, hV⟩ := exists_T_optimal_latent (isPMF_push (f := Prod.map f g) hp)
  have h := (T_le_score (liftLatent hp f g V) (liftLatent_isDet hp f g V hVdet)).trans
    (lift_score_le hp f g V)
  simpa only [hV] using h

end Lift

end stoch_to_det.SourceCoarsening
