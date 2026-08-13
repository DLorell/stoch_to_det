import stoch_to_det.Seed
import stoch_to_det.Constants
import stoch_to_det.Constants1771

/-!
# §7. The duplicate quotient, the exact race law, and the seed interface


The latent labels are grouped into **clusters** by exact equality of component
laws. The point is that the within-cluster posterior
`π_{u∣c}` does **not depend on `z`**, so the seed factorizes exactly: the label
race is the cluster race followed by an independent within-cluster race. That
is what lets §§8-10 analyse a race among *pairwise distinct* contacts, which is
exactly the hypothesis Theorem 6.2 needs.

## The quotient as a fibre map

Clusters are represented as the fibres of a map `cl : ι → κ` rather than as a
quotient type, so cluster-level quantities are `push cl`-images of label-level
ones, `stoch_to_det.Entropy` applies unchanged, and Lemma 7.2(d)'s
`I(L₁;Z ∣ L₀) = I(C₁;Z ∣ C₀)` is a `push_push` computation rather than a
transport.

## The seed-conditioned informations are not defined here

`D = I(ε; Z ∣ A, L₀)`, `scalar = I(U; Z ∣ B, C₀)` and
`cone = I(X*₋B; Z ∣ B, C₀, U)` pair a continuous variable against a finite `Z`,
and their status differs:

* `scalar` conditions on `B, C₀` only — both finite — so it is expressible by
  `condMIcts` (`stoch_to_det.Seed`), with the conditional law of `U` given `(Z=z, B=b)`
  an explicit exponential of mean `σ_b(z)` by Lemma 7.4.
* `cone` conditions additionally on `U`, which is continuous, and `condMIcts`
  does not cover that. The construction never uses `cone` as a standalone object:
  it bounds it in one step by integrating (10.2) against the exact joint
  density of (7.1).
* `D` conditions on the finite `A`, but its argument `ε` is the whole seed
  vector.

§§8-11 are therefore stated against the interface `RaceQuantities` below. The
structure carries the four scalars, the two structural identities, and the two
channel bounds plus the cell-residual link as obligations. Constructing an
instance (`stoch_to_det/Race.lean`, `exists_raceQuantities`) is Lemmas 7.2-7.5 +
Theorems 8.1 and 10.1, and is the only place the seed measure theory lives.
-/

namespace stoch_to_det

open Finset MeasureTheory ProbabilityTheory

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

/-! ### Definition 7.1 — the duplicate quotient -/

/-- The duplicate quotient of `Definition 7.1`: a cluster map identifying labels
with equal component laws. -/
structure Clustering {p : α × β → ℝ} (D : SeedSetup p) : Type 1 where
  /-- Cluster index type. -/
  κ : Type
  /-- Finiteness. -/
  fin : Fintype κ
  /-- Decidable equality. -/
  dec : DecidableEq κ
  /-- The cluster map. -/
  cl : D.L.ι → κ
  /-- Clusters are exactly the fibres of "equal component law". -/
  spec : ∀ ℓ ℓ', cl ℓ = cl ℓ' ↔ D.L.comp ℓ = D.L.comp ℓ'
  /-- Every cluster is inhabited. -/
  surj : Function.Surjective cl

attribute [instance] Clustering.fin Clustering.dec

/-- Every setup has a duplicate quotient (`DecidableEq` on component laws is
classical). -/
theorem exists_clustering {p : α × β → ℝ} (D : SeedSetup p) : Nonempty (Clustering D) := by
  classical
  let r : Setoid D.L.ι := {
    r ℓ ℓ' := D.L.comp ℓ = D.L.comp ℓ'
    iseqv := ⟨fun _ => rfl, fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩
  }
  let cl : D.L.ι → Quotient r := Quotient.mk r
  exact ⟨{
    κ := Quotient r
    fin := Fintype.ofSurjective cl Quotient.mk_surjective
    dec := Classical.decEq _
    cl := cl
    spec := by
      intro ℓ ℓ'
      exact Quotient.eq
    surj := Quotient.mk_surjective
  }⟩

namespace Clustering

variable {p : α × β → ℝ} {D : SeedSetup p} (K : Clustering D)

/-- The common component law `Q_c` of a cluster. -/
noncomputable def Q (c : K.κ) : α × β → ℝ := D.L.comp (Classical.choose (K.surj c))

/-- The cluster mass `s_c := ∑_{ℓ ∈ c} λ_ℓ`. -/
noncomputable def s (c : K.κ) : ℝ := ∑ ℓ ∈ univ.filter (fun ℓ => K.cl ℓ = c), D.L.prior ℓ

/-- The cluster posterior `σ_c(z) := ∑_{ℓ ∈ c} t_ℓ(z) = s_c Q_c(z)/p(z)`
. -/
noncomputable def sigma (c : K.κ) (z : α × β) : ℝ :=
  ∑ ℓ ∈ univ.filter (fun ℓ => K.cl ℓ = c), D.post ℓ z

/-- The defining property of the duplicate quotient:
`t_ℓ(z) = σ_{cl ℓ}(z) · π_{ℓ}` with the second factor **independent of `z`**. -/
theorem post_eq_sigma_mul (ℓ : D.L.ι) (z : α × β) (hz : z ∈ support p) :
    D.post ℓ z = K.sigma (K.cl ℓ) z * (D.L.prior ℓ / K.s (K.cl ℓ)) := by
  have hpz : p z ≠ 0 := by
    simpa [support] using hz
  have hs_le : D.L.prior ℓ ≤ K.s (K.cl ℓ) := by
    unfold s
    exact Finset.single_le_sum
      (fun ℓ' _ => D.L.prior_isPMF.nonneg ℓ') (by simp)
  have hs_pos : 0 < K.s (K.cl ℓ) := (D.prior_pos ℓ).trans_le hs_le
  have hsigma :
      K.sigma (K.cl ℓ) z = K.s (K.cl ℓ) * D.L.comp ℓ z / p z := by
    unfold sigma s SeedSetup.post
    calc
      (∑ ℓ' ∈ univ.filter (fun ℓ' => K.cl ℓ' = K.cl ℓ),
          D.L.prior ℓ' * D.L.comp ℓ' z / p z)
          = ∑ ℓ' ∈ univ.filter (fun ℓ' => K.cl ℓ' = K.cl ℓ),
              D.L.prior ℓ' * D.L.comp ℓ z / p z := by
                apply Finset.sum_congr rfl
                intro ℓ' hℓ'
                have hcomp : D.L.comp ℓ' = D.L.comp ℓ :=
                  (K.spec ℓ' ℓ).mp (Finset.mem_filter.mp hℓ').2
                rw [hcomp]
      _ = (∑ ℓ' ∈ univ.filter (fun ℓ' => K.cl ℓ' = K.cl ℓ),
              D.L.prior ℓ' * D.L.comp ℓ z) / p z := by
            rw [Finset.sum_div]
      _ = (∑ ℓ' ∈ univ.filter (fun ℓ' => K.cl ℓ' = K.cl ℓ),
              D.L.prior ℓ') * D.L.comp ℓ z / p z := by
            rw [Finset.sum_mul]
  rw [hsigma]
  unfold SeedSetup.post
  field_simp [hpz, hs_pos.ne']

/-- On a connected support every cluster posterior is strictly positive
(Lemma 2.6), so no zero-posterior edge cases arise. -/
theorem sigma_pos (c : K.κ) (z : α × β) (hz : z ∈ support p) : 0 < K.sigma c z := by
  let ℓ : D.L.ι := Classical.choose (K.surj c)
  have hcl : K.cl ℓ = c := Classical.choose_spec (K.surj c)
  have hpz_ne : p z ≠ 0 := by
    simpa [support] using hz
  have hpz : 0 < p z := lt_of_le_of_ne (D.isPMF.nonneg z) (Ne.symm hpz_ne)
  have hcontact : IsContact (support p) D.w (D.L.comp ℓ) :=
    D.contact ℓ (D.prior_pos ℓ).ne'
  have hsupp : support (D.L.comp ℓ) = support p :=
    contact_support_eq D.feasible D.conn hcontact
  have hzcomp : z ∈ support (D.L.comp ℓ) := by
    rw [hsupp]
    exact hz
  have hcomp_ne : D.L.comp ℓ z ≠ 0 := by
    simpa [support] using hzcomp
  have hcomp_pos : 0 < D.L.comp ℓ z :=
    lt_of_le_of_ne ((D.L.comp_isPMF ℓ).nonneg z) (Ne.symm hcomp_ne)
  have hpost_pos : 0 < D.post ℓ z := by
    unfold SeedSetup.post
    exact div_pos (mul_pos (D.prior_pos ℓ) hcomp_pos) hpz
  have hpost_nonneg : ∀ ℓ' : D.L.ι, 0 ≤ D.post ℓ' z := by
    intro ℓ'
    unfold SeedSetup.post
    exact div_nonneg
      (mul_nonneg (D.L.prior_isPMF.nonneg ℓ') ((D.L.comp_isPMF ℓ').nonneg z)) hpz.le
  have hle : D.post ℓ z ≤ K.sigma c z := by
    unfold sigma
    exact Finset.single_le_sum (fun ℓ' _ => hpost_nonneg ℓ') (by simp [hcl])
  exact hpost_pos.trans_le hle

/-- Distinct clusters are pairwise distinct contacts of `w` — the hypothesis
Theorem 6.2 and Theorem 9.1 require. -/
theorem Q_isContact (c : K.κ) : IsContact (support p) D.w (K.Q c) := by
  let ℓ : D.L.ι := Classical.choose (K.surj c)
  have hℓ : D.L.prior ℓ ≠ 0 := (D.prior_pos ℓ).ne'
  simpa [Q, ℓ] using D.contact ℓ hℓ

theorem Q_injective : Function.Injective K.Q := by
  intro c c' hQ
  have hrep :
      K.cl (Classical.choose (K.surj c)) =
        K.cl (Classical.choose (K.surj c')) :=
    (K.spec _ _).mpr (by simpa [Q] using hQ)
  simpa only [Classical.choose_spec (K.surj c),
    Classical.choose_spec (K.surj c')] using hrep

/-- `S := I(C₁; Z ∣ C₀)`. -/
noncomputable def Sinfo : ℝ :=
  condMI (fun u => K.cl u.2.1) (fun u => u.2.2.2) (fun u => K.cl u.1) (replicaLaw D)

/-- `d := P(C₁ ≠ C₀)`, the **mismatch probability**. -/
noncomputable def dMis : ℝ :=
  ∑ u ∈ univ.filter (fun u : D.L.ι × D.L.ι × D.L.ι × (α × β) => K.cl u.1 ≠ K.cl u.2.1),
    replicaLaw D u

private lemma sum_post_eq_one (z : α × β) (hz : p z ≠ 0) :
    ∑ ℓ, D.post ℓ z = 1 := by
  calc
    ∑ ℓ, D.post ℓ z = (∑ ℓ, D.L.prior ℓ * D.L.comp ℓ z) / p z := by
      simp only [SeedSetup.post, Finset.sum_div]
    _ = p z / p z := by rw [D.L.mixture]
    _ = 1 := div_self hz

private lemma sigma_eq_push (z : α × β) :
    push K.cl (fun ℓ => D.post ℓ z) = fun c => K.sigma c z := by
  rfl

private lemma push_id_local {A : Type*} [Fintype A] [DecidableEq A] (m : A → ℝ) :
    push (fun a => a) m = m := by
  funext a
  unfold push
  apply Finset.sum_eq_single a
  · intro b hb hba
    exact (hba (Finset.mem_filter.mp hb).2).elim
  · intro ha
    exact (ha (by simp)).elim

private lemma push_fst_local {A B : Type*}
    [Fintype A] [DecidableEq A] [Fintype B] (m : A × B → ℝ) :
    push Prod.fst m = fun a => ∑ b, m (a, b) := by
  funext a
  unfold push
  simp_rw [Finset.sum_filter]
  rw [Fintype.sum_prod_type]
  change (∑ a', ∑ b, if a' = a then m (a', b) else 0) = ∑ b, m (a, b)
  calc
    (∑ a', ∑ b, if a' = a then m (a', b) else 0) =
        ∑ b, if a = a then m (a, b) else 0 := by
      apply Finset.sum_eq_single a
      · intro a' _ ha'
        simp [ha']
      · intro ha
        exact (ha (by simp)).elim
    _ = ∑ b, m (a, b) := by simp

private lemma push_fst_snd_fiber_local {A B : Type*}
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (m : A × B → ℝ) (b : B) :
    push Prod.fst (fun v => if v.2 = b then m v else 0) = fun a => m (a, b) := by
  funext a
  unfold push
  simp_rw [Finset.sum_filter]
  rw [Fintype.sum_prod_type]
  simp

private lemma H_eq_push_add_fibers_pmf {A B : Type*}
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    {m : A → ℝ} (hm : IsPMF m) (f : A → B) :
    H m = H (push f m) + ∑ b, H (fun a => if f a = b then m a else 0) := by
  have hchain := Hvar_pair_eq_sum_fibers hm (fun a : A => a) f
  have hleft : Function.LeftInverse (@Prod.fst A B) (fun a => (a, f a)) := by
    intro a
    rfl
  have henc := Hvar_eq_of_leftInverse hm (fun a : A => a)
    (fun a => (a, f a)) (@Prod.fst A B) hleft
  have henc' : Hvar (fun a : A => (a, f a)) m = Hvar (fun a : A => a) m := by
    simpa [Function.comp_def] using henc
  rw [henc'] at hchain
  simpa only [Hvar, push_id_local] using hchain

private lemma H_eq_push_add_fibers_fin {A B : Type*}
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    {m : A → ℝ} (hm : IsFinMeas m) (f : A → B) :
    H m = H (push f m) + ∑ b, H (fun a => if f a = b then m a else 0) := by
  have hmass_nonneg : 0 ≤ mass m := Finset.sum_nonneg fun a _ => hm a
  by_cases hmass : mass m = 0
  · have hm_zero : m = fun _ => 0 := by
      funext a
      apply le_antisymm
      · have ha_le : m a ≤ mass m := by
          unfold mass
          exact Finset.single_le_sum (fun b _ => hm b) (Finset.mem_univ a)
        simpa [hmass] using ha_le
      · exact hm a
    rw [hm_zero]
    simp [H, push, mass]
  · let M : ℝ := mass m
    have hM_pos : 0 < M := lt_of_le_of_ne hmass_nonneg (Ne.symm hmass)
    have hM_ne : M ≠ 0 := hM_pos.ne'
    let q : A → ℝ := fun a => M⁻¹ * m a
    have hq : IsPMF q := by
      constructor
      · intro a
        exact mul_nonneg (inv_nonneg.mpr hM_pos.le) (hm a)
      · unfold mass q
        rw [← Finset.mul_sum]
        exact inv_mul_cancel₀ hM_ne
    have hscale : (fun a => M * q a) = m := by
      funext a
      dsimp only [q]
      field_simp
    have hchain := H_eq_push_add_fibers_pmf hq f
    have hHm : H m = M * H q := by
      rw [← hscale]
      exact H_smul hq.isFinMeas hM_pos.le
    have hpush : push f m = fun b => M * push f q b := by
      rw [← hscale]
      exact push_smul f q M
    have hHpush : H (push f m) = M * H (push f q) := by
      rw [hpush]
      exact H_smul (isFinMeas_push hq.isFinMeas) hM_pos.le
    have hHfiber (b : B) :
        H (fun a => if f a = b then m a else 0) =
          M * H (fun a => if f a = b then q a else 0) := by
      have hfiber : (fun a => if f a = b then m a else 0) =
          fun a => M * (if f a = b then q a else 0) := by
        funext a
        have ha := congrFun hscale a
        by_cases hab : f a = b <;> simp [hab, ha]
      rw [hfiber]
      apply H_smul
      · intro a
        by_cases hab : f a = b <;> simp [hab, hq.nonneg a]
      · exact hM_pos.le
    calc
      H m = M * H q := hHm
      _ = M * (H (push f q) +
          ∑ b, H (fun a => if f a = b then q a else 0)) := by rw [hchain]
      _ = M * H (push f q) +
          ∑ b, M * H (fun a => if f a = b then q a else 0) := by
            rw [mul_add, Finset.mul_sum]
      _ = H (push f m) + ∑ b, H (fun a => if f a = b then m a else 0) := by
            rw [hHpush]
            simp_rw [hHfiber]

private lemma MI_eq_Hvar_sub_fibers {A B C : Type*}
    [Fintype A] [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]
    {m : A → ℝ} (hm : IsPMF m) (f : A → B) (g : A → C) :
    MI f g m = Hvar f m -
      ∑ c, H (push f (fun a => if g a = c then m a else 0)) := by
  have hchain := Hvar_pair_eq_sum_fibers hm f g
  unfold MI
  rw [hchain]
  ring

private lemma MI_eq_joint_push {A B C : Type*}
    [Fintype A] [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]
    (m : A → ℝ) (f : A → B) (g : A → C) :
    MI f g m = MI Prod.fst Prod.snd (push (fun a => (f a, g a)) m) := by
  unfold MI Hvar
  rw [push_push, push_push, push_id_local]
  rfl

private lemma condMI_eq_sum_MI_fibers {A B C E : Type*}
    [Fintype A] [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]
    [Fintype E] [DecidableEq E] {m : A → ℝ} (hm : IsPMF m)
    (f : A → B) (g : A → C) (h : A → E) :
    condMI f g h m = ∑ e, MI f g (fun a => if h a = e then m a else 0) := by
  let mh : E → A → ℝ := fun e a => if h a = e then m a else 0
  have hF := Hvar_pair_eq_sum_fibers hm f h
  have hG := Hvar_pair_eq_sum_fibers hm g h
  have hFG := Hvar_pair_eq_sum_fibers hm (fun a => (f a, g a)) h
  change Hvar (fun a => (f a, h a)) m = Hvar h m +
    ∑ e, H (push f (mh e)) at hF
  change Hvar (fun a => (g a, h a)) m = Hvar h m +
    ∑ e, H (push g (mh e)) at hG
  change Hvar (fun a => ((f a, g a), h a)) m = Hvar h m +
    ∑ e, H (push (fun a => (f a, g a)) (mh e)) at hFG
  have hAssoc : Hvar (fun a => (f a, g a, h a)) m =
      Hvar (fun a => ((f a, g a), h a)) m := by
    simpa using Hvar_equiv hm (fun a => ((f a, g a), h a))
      (Equiv.prodAssoc B C E)
  unfold condMI
  rw [hF, hG, hAssoc, hFG]
  simp only [MI, Hvar, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  ring

private lemma s_pos_local (c : K.κ) : 0 < K.s c := by
  obtain ⟨ℓ, hℓ⟩ := K.surj c
  unfold s
  apply Finset.sum_pos'
  · intro ℓ' _
    exact D.L.prior_isPMF.nonneg ℓ'
  · exact ⟨ℓ, by simp [hℓ], D.prior_pos ℓ⟩

private lemma comp_eq_Q_local (c : K.κ) (ℓ : D.L.ι) (hℓ : K.cl ℓ = c) :
    D.L.comp ℓ = K.Q c := by
  rw [Q]
  apply (K.spec ℓ (Classical.choose (K.surj c))).mp
  exact hℓ.trans (Classical.choose_spec (K.surj c)).symm

private lemma p_mul_post_eq_prior_mul_comp (ℓ : D.L.ι) (z : α × β) :
    p z * D.post ℓ z = D.L.prior ℓ * D.L.comp ℓ z := by
  by_cases hz : p z = 0
  · have hzS : z ∉ support p := by simp [support, hz]
    have hcomp : D.L.comp ℓ z = 0 :=
      (D.contact ℓ (D.prior_pos ℓ).ne').2.1 z hzS
    simp [SeedSetup.post, hz, hcomp]
  · unfold SeedSetup.post
    field_simp

private lemma sigma_nonneg_local (c : K.κ) (z : α × β) : 0 ≤ K.sigma c z := by
  unfold sigma
  apply Finset.sum_nonneg
  intro ℓ _
  unfold SeedSetup.post
  exact div_nonneg
    (mul_nonneg (D.L.prior_isPMF.nonneg ℓ) ((D.L.comp_isPMF ℓ).nonneg z))
    (D.isPMF.nonneg z)

private noncomputable def posteriorJoint (g : K.κ) : D.L.ι × (α × β) → ℝ :=
  fun v => K.Q g v.2 * D.post v.1 v.2

private lemma posteriorJoint_isPMF (g : K.κ) : IsPMF (posteriorJoint K g) := by
  have hQ := (K.Q_isContact g).1
  have hQS := (K.Q_isContact g).2.1
  constructor
  · intro v
    exact mul_nonneg (hQ.nonneg v.2) (by
      unfold SeedSetup.post
      exact div_nonneg
        (mul_nonneg (D.L.prior_isPMF.nonneg v.1) ((D.L.comp_isPMF v.1).nonneg v.2))
        (D.isPMF.nonneg v.2))
  · unfold mass posteriorJoint
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    calc
      (∑ z, ∑ ℓ, K.Q g z * D.post ℓ z) = ∑ z, K.Q g z := by
        apply Finset.sum_congr rfl
        intro z _
        by_cases hz : p z = 0
        · have hzS : z ∉ support p := by simp [support, hz]
          have hQz : K.Q g z = 0 := hQS z hzS
          simp [hQz]
        · rw [← Finset.mul_sum, sum_post_eq_one (D := D) z hz, mul_one]
      _ = 1 := by simpa [mass] using hQ.total

private lemma posteriorJoint_cluster_factor (g d : K.κ) (ℓ : D.L.ι) (z : α × β) :
    (if K.cl ℓ = d then posteriorJoint K g (ℓ, z) else 0) =
      (K.Q g z * K.sigma d z / K.s d) *
        (if K.cl ℓ = d then D.L.prior ℓ else 0) := by
  by_cases hℓ : K.cl ℓ = d
  · simp only [hℓ, if_true]
    by_cases hQz : K.Q g z = 0
    · simp [posteriorJoint, hQz]
    · have hz : z ∈ support p := by
        by_contra hz
        exact hQz ((K.Q_isContact g).2.1 z hz)
      rw [posteriorJoint, K.post_eq_sigma_mul ℓ z hz, hℓ]
      ring
  · simp [hℓ]

private lemma MI_posteriorJoint_eq_cluster (g : K.κ) :
    MI (fun v : D.L.ι × (α × β) => v.1) (fun v => v.2) (posteriorJoint K g) =
      MI (fun v : D.L.ι × (α × β) => K.cl v.1) (fun v => v.2)
        (posteriorJoint K g) := by
  let m : D.L.ι × (α × β) → ℝ := posteriorJoint K g
  let qz : (α × β) → D.L.ι → ℝ := fun z ℓ => m (ℓ, z)
  let ml : D.L.ι → ℝ := fun ℓ => ∑ z, qz z ℓ
  let base : K.κ → D.L.ι → ℝ :=
    fun d ℓ => if K.cl ℓ = d then D.L.prior ℓ else 0
  let coeff : K.κ → (α × β) → ℝ :=
    fun d z => K.Q g z * K.sigma d z / K.s d
  have hm : IsPMF m := by
    simpa only [m] using posteriorJoint_isPMF K g
  have hqz_fin (z : α × β) : IsFinMeas (qz z) := by
    intro ℓ
    exact hm.nonneg (ℓ, z)
  have hml_fin : IsFinMeas ml := by
    intro ℓ
    exact Finset.sum_nonneg fun z _ => hqz_fin z ℓ
  have hbase_fin (d : K.κ) : IsFinMeas (base d) := by
    intro ℓ
    by_cases hℓ : K.cl ℓ = d <;> simp [base, hℓ, D.L.prior_isPMF.nonneg ℓ]
  have hcoeff_nonneg (d : K.κ) (z : α × β) : 0 ≤ coeff d z := by
    exact div_nonneg
      (mul_nonneg ((K.Q_isContact g).1.nonneg z) (sigma_nonneg_local K d z))
      (s_pos_local K d).le
  have hqfactor (d : K.κ) (z : α × β) :
      (fun ℓ => if K.cl ℓ = d then qz z ℓ else 0) =
        fun ℓ => coeff d z * base d ℓ := by
    funext ℓ
    simpa only [m, qz, coeff, base] using
      posteriorJoint_cluster_factor K g d ℓ z
  have hmlfactor (d : K.κ) :
      (fun ℓ => if K.cl ℓ = d then ml ℓ else 0) =
        fun ℓ => (∑ z, coeff d z) * base d ℓ := by
    funext ℓ
    by_cases hℓ : K.cl ℓ = d
    · simp only [hℓ, if_true]
      dsimp only [ml, qz]
      calc
        (∑ z, m (ℓ, z)) = ∑ z, coeff d z * D.L.prior ℓ := by
          apply Finset.sum_congr rfl
          intro z _
          have hfactor := posteriorJoint_cluster_factor K g d ℓ z
          simpa only [m, coeff, hℓ, if_true] using hfactor
        _ = (∑ z, coeff d z) * D.L.prior ℓ := by rw [Finset.sum_mul]
        _ = (∑ z, coeff d z) * base d ℓ := by simp [base, hℓ]
    · simp [base, hℓ]
  have hHq (d : K.κ) (z : α × β) :
      H (fun ℓ => if K.cl ℓ = d then qz z ℓ else 0) =
        coeff d z * H (base d) := by
    rw [hqfactor]
    exact H_smul (hbase_fin d) (hcoeff_nonneg d z)
  have hHml (d : K.κ) :
      H (fun ℓ => if K.cl ℓ = d then ml ℓ else 0) =
        (∑ z, coeff d z) * H (base d) := by
    rw [hmlfactor]
    exact H_smul (hbase_fin d) (Finset.sum_nonneg fun z _ => hcoeff_nonneg d z)
  have hcorr :
      (∑ d, H (fun ℓ => if K.cl ℓ = d then ml ℓ else 0)) =
        ∑ z, ∑ d, H (fun ℓ => if K.cl ℓ = d then qz z ℓ else 0) := by
    calc
      (∑ d, H (fun ℓ => if K.cl ℓ = d then ml ℓ else 0)) =
          ∑ d, (∑ z, coeff d z) * H (base d) := by
            apply Finset.sum_congr rfl
            intro d _
            exact hHml d
      _ = ∑ d, ∑ z, coeff d z * H (base d) := by
            apply Finset.sum_congr rfl
            intro d _
            rw [Finset.sum_mul]
      _ = ∑ z, ∑ d, coeff d z * H (base d) := Finset.sum_comm
      _ = ∑ z, ∑ d, H (fun ℓ => if K.cl ℓ = d then qz z ℓ else 0) := by
            apply Finset.sum_congr rfl
            intro z _
            apply Finset.sum_congr rfl
            intro d _
            exact (hHq d z).symm
  have hloss :
      H ml - H (push K.cl ml) =
        ∑ z, (H (qz z) - H (push K.cl (qz z))) := by
    have hchain_ml := H_eq_push_add_fibers_fin hml_fin K.cl
    calc
      H ml - H (push K.cl ml) =
          ∑ d, H (fun ℓ => if K.cl ℓ = d then ml ℓ else 0) := by
            rw [hchain_ml]
            ring
      _ = ∑ z, ∑ d, H (fun ℓ => if K.cl ℓ = d then qz z ℓ else 0) := hcorr
      _ = ∑ z, (H (qz z) - H (push K.cl (qz z))) := by
            apply Finset.sum_congr rfl
            intro z _
            have hchain_q := H_eq_push_add_fibers_fin (hqz_fin z) K.cl
            rw [hchain_q]
            ring
  have hpush_m : push (fun v : D.L.ι × (α × β) => v.1) m = ml := by
    simpa only [ml, qz] using push_fst_local m
  have hpush_fiber (z : α × β) :
      push (fun v : D.L.ι × (α × β) => v.1)
          (fun v => if v.2 = z then m v else 0) = qz z := by
    simpa only [qz] using push_fst_snd_fiber_local m z
  have hpush_cluster :
      push (fun v : D.L.ι × (α × β) => K.cl v.1) m = push K.cl ml := by
    calc
      push (fun v : D.L.ι × (α × β) => K.cl v.1) m =
          push (K.cl ∘ fun v : D.L.ι × (α × β) => v.1) m := rfl
      _ = push K.cl (push (fun v : D.L.ι × (α × β) => v.1) m) :=
        (push_push (fun v : D.L.ι × (α × β) => v.1) K.cl m).symm
      _ = push K.cl ml := by rw [hpush_m]
  have hpush_cluster_fiber (z : α × β) :
      push (fun v : D.L.ι × (α × β) => K.cl v.1)
          (fun v => if v.2 = z then m v else 0) = push K.cl (qz z) := by
    calc
      push (fun v : D.L.ι × (α × β) => K.cl v.1)
          (fun v => if v.2 = z then m v else 0) =
          push (K.cl ∘ fun v : D.L.ι × (α × β) => v.1)
            (fun v => if v.2 = z then m v else 0) := rfl
      _ = push K.cl (push (fun v : D.L.ι × (α × β) => v.1)
            (fun v => if v.2 = z then m v else 0)) :=
        (push_push (fun v : D.L.ι × (α × β) => v.1) K.cl
          (fun v => if v.2 = z then m v else 0)).symm
      _ = push K.cl (qz z) := by rw [hpush_fiber]
  have hlabel := MI_eq_Hvar_sub_fibers hm
    (fun v : D.L.ι × (α × β) => v.1) (fun v => v.2)
  have hcluster := MI_eq_Hvar_sub_fibers hm
    (fun v : D.L.ι × (α × β) => K.cl v.1) (fun v => v.2)
  unfold Hvar at hlabel hcluster
  rw [hpush_m] at hlabel
  simp_rw [hpush_fiber] at hlabel
  rw [hpush_cluster] at hcluster
  simp_rw [hpush_cluster_fiber] at hcluster
  rw [hlabel, hcluster]
  rw [Finset.sum_sub_distrib] at hloss
  linarith

private lemma push_replica_condition_label (ℓ₁ : D.L.ι) :
    push (fun u : D.L.ι × D.L.ι × D.L.ι × (α × β) => (u.1, u.2.2.2))
        (fun u => if u.2.1 = ℓ₁ then replicaLaw D u else 0) =
      fun v => D.L.prior ℓ₁ * posteriorJoint K (K.cl ℓ₁) v := by
  funext v
  rcases v with ⟨ℓ₀, z⟩
  unfold push
  simp_rw [Finset.sum_filter]
  rw [Fintype.sum_prod_type_right, Fintype.sum_prod_type_right,
    Fintype.sum_prod_type_right]
  unfold replicaLaw
  change
    (∑ z', ∑ ℓ₂, ∑ ℓ₁', ∑ ℓ₀',
      if (ℓ₀', z') = (ℓ₀, z) then
        (if ℓ₁' = ℓ₁ then
          p z' * D.post ℓ₀' z' * D.post ℓ₁' z' * D.post ℓ₂ z' else 0)
      else 0) =
        D.L.prior ℓ₁ * posteriorJoint K (K.cl ℓ₁) (ℓ₀, z)
  calc
    (∑ z', ∑ ℓ₂, ∑ ℓ₁', ∑ ℓ₀',
      if (ℓ₀', z') = (ℓ₀, z) then
        (if ℓ₁' = ℓ₁ then
          p z' * D.post ℓ₀' z' * D.post ℓ₁' z' * D.post ℓ₂ z' else 0)
      else 0) =
        ∑ ℓ₂, p z * D.post ℓ₀ z * D.post ℓ₁ z * D.post ℓ₂ z := by
          simp only [Prod.mk.injEq, ite_and, Fintype.sum_ite_eq']
          calc
            (∑ z', ∑ ℓ₂, ∑ ℓ₁',
              if z' = z then
                (if ℓ₁' = ℓ₁ then
                  p z' * D.post ℓ₀ z' * D.post ℓ₁' z' * D.post ℓ₂ z' else 0)
              else 0) =
                ∑ z', ∑ ℓ₁', ∑ ℓ₂,
                  if z' = z then
                    (if ℓ₁' = ℓ₁ then
                      p z' * D.post ℓ₀ z' * D.post ℓ₁' z' * D.post ℓ₂ z' else 0)
                  else 0 := by
                    apply Finset.sum_congr rfl
                    intro z' _
                    exact Finset.sum_comm
            _ = ∑ z', if z' = z then
                  (∑ ℓ₂, p z' * D.post ℓ₀ z' * D.post ℓ₁ z' * D.post ℓ₂ z')
                else 0 := by
                  apply Finset.sum_congr rfl
                  intro z' _
                  by_cases hz' : z' = z <;> simp [hz']
            _ = ∑ ℓ₂, p z * D.post ℓ₀ z * D.post ℓ₁ z * D.post ℓ₂ z := by
                  rw [Fintype.sum_ite_eq']
    _ = D.L.prior ℓ₁ * posteriorJoint K (K.cl ℓ₁) (ℓ₀, z) := by
      by_cases hz : p z = 0
      · have hzS : z ∉ support p := by simp [support, hz]
        have hQz : K.Q (K.cl ℓ₁) z = 0 :=
          (K.Q_isContact (K.cl ℓ₁)).2.1 z hzS
        simp [hz, posteriorJoint, hQz]
      · rw [show (∑ ℓ₂, p z * D.post ℓ₀ z * D.post ℓ₁ z * D.post ℓ₂ z) =
            (p z * D.post ℓ₁ z) * D.post ℓ₀ z * (∑ ℓ₂, D.post ℓ₂ z) by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro ℓ₂ _
              ring]
        rw [sum_post_eq_one (D := D) z hz, mul_one,
          p_mul_post_eq_prior_mul_comp (D := D) ℓ₁ z,
          comp_eq_Q_local K (K.cl ℓ₁) ℓ₁ rfl]
        unfold posteriorJoint
        ring

private lemma push_posteriorJoint_cluster_pair (g d : K.κ) (z : α × β) :
    push (fun v : D.L.ι × (α × β) => (K.cl v.1, v.2)) (posteriorJoint K g) (d, z) =
      ∑ ℓ ∈ univ.filter (fun ℓ => K.cl ℓ = d), K.Q g z * D.post ℓ z := by
  unfold push posteriorJoint
  simp_rw [Finset.sum_filter]
  rw [Fintype.sum_prod_type]
  simp only [Prod.mk.injEq, ite_and]
  apply Finset.sum_congr rfl
  intro ℓ _
  by_cases hℓ : K.cl ℓ = d <;> simp [hℓ]

private lemma push_replica_condition_cluster (g : K.κ) :
    push (fun u : D.L.ι × D.L.ι × D.L.ι × (α × β) =>
        (K.cl u.2.1, u.2.2.2))
        (fun u => if K.cl u.1 = g then replicaLaw D u else 0) =
      fun v => K.s g *
        push (fun w : D.L.ι × (α × β) => (K.cl w.1, w.2))
          (posteriorJoint K g) v := by
  funext v
  rcases v with ⟨d, z⟩
  rw [push_posteriorJoint_cluster_pair K g d z]
  unfold push
  rw [Finset.sum_filter]
  rw [Fintype.sum_prod_type_right, Fintype.sum_prod_type_right,
    Fintype.sum_prod_type_right]
  unfold replicaLaw
  change
    (∑ z', ∑ ℓ₂, ∑ ℓ₁, ∑ ℓ₀,
      if (K.cl ℓ₁, z') = (d, z) then
        (if K.cl ℓ₀ = g then
          p z' * D.post ℓ₀ z' * D.post ℓ₁ z' * D.post ℓ₂ z' else 0)
      else 0) =
        K.s g * ∑ ℓ ∈ univ.filter (fun ℓ => K.cl ℓ = d),
          K.Q g z * D.post ℓ z
  calc
    (∑ z', ∑ ℓ₂, ∑ ℓ₁, ∑ ℓ₀,
      if (K.cl ℓ₁, z') = (d, z) then
        (if K.cl ℓ₀ = g then
          p z' * D.post ℓ₀ z' * D.post ℓ₁ z' * D.post ℓ₂ z' else 0)
      else 0) =
        ∑ z', if z' = z then
          (∑ ℓ₂, ∑ ℓ₁, ∑ ℓ₀,
            if K.cl ℓ₁ = d then
              (if K.cl ℓ₀ = g then
                p z' * D.post ℓ₀ z' * D.post ℓ₁ z' * D.post ℓ₂ z' else 0)
            else 0)
          else 0 := by
            apply Finset.sum_congr rfl
            intro z' _
            by_cases hz' : z' = z <;> simp [Prod.mk.injEq, hz']
    _ = ∑ ℓ₂, ∑ ℓ₁, ∑ ℓ₀,
          if K.cl ℓ₁ = d then
            (if K.cl ℓ₀ = g then
              p z * D.post ℓ₀ z * D.post ℓ₁ z * D.post ℓ₂ z else 0)
          else 0 := by
            rw [Fintype.sum_ite_eq']
    _ = K.s g * ∑ ℓ ∈ univ.filter (fun ℓ => K.cl ℓ = d),
          K.Q g z * D.post ℓ z := by
      by_cases hz : p z = 0
      · have hzS : z ∉ support p := by simp [support, hz]
        have hQz : K.Q g z = 0 := (K.Q_isContact g).2.1 z hzS
        simp [hz, hQz]
      · have hsum₂ (ℓ₀ ℓ₁ : D.L.ι) :
            (∑ ℓ₂, p z * D.post ℓ₀ z * D.post ℓ₁ z * D.post ℓ₂ z) =
              p z * D.post ℓ₀ z * D.post ℓ₁ z := by
          calc
            (∑ ℓ₂, p z * D.post ℓ₀ z * D.post ℓ₁ z * D.post ℓ₂ z) =
                (p z * D.post ℓ₀ z * D.post ℓ₁ z) *
                  (∑ ℓ₂, D.post ℓ₂ z) := by rw [Finset.mul_sum]
            _ = p z * D.post ℓ₀ z * D.post ℓ₁ z := by
              rw [sum_post_eq_one (D := D) z hz, mul_one]
        have hsource (ℓ₁ : D.L.ι) :
            (∑ ℓ₀, if K.cl ℓ₀ = g then
              p z * D.post ℓ₀ z * D.post ℓ₁ z else 0) =
                K.s g * K.Q g z * D.post ℓ₁ z := by
          calc
            (∑ ℓ₀, if K.cl ℓ₀ = g then
              p z * D.post ℓ₀ z * D.post ℓ₁ z else 0) =
                ∑ ℓ₀ ∈ univ.filter (fun ℓ₀ => K.cl ℓ₀ = g),
                  p z * D.post ℓ₀ z * D.post ℓ₁ z := by
                    rw [Finset.sum_filter]
            _ = ∑ ℓ₀ ∈ univ.filter (fun ℓ₀ => K.cl ℓ₀ = g),
                  D.L.prior ℓ₀ * K.Q g z * D.post ℓ₁ z := by
                    apply Finset.sum_congr rfl
                    intro ℓ₀ hℓ₀
                    rw [p_mul_post_eq_prior_mul_comp (D := D) ℓ₀ z,
                      comp_eq_Q_local K g ℓ₀ (Finset.mem_filter.mp hℓ₀).2]
            _ = K.s g * K.Q g z * D.post ℓ₁ z := by
                    unfold s
                    calc
                      (∑ ℓ₀ ∈ univ.filter (fun ℓ₀ => K.cl ℓ₀ = g),
                        D.L.prior ℓ₀ * K.Q g z * D.post ℓ₁ z) =
                          ∑ ℓ₀ ∈ univ.filter (fun ℓ₀ => K.cl ℓ₀ = g),
                            D.L.prior ℓ₀ * (K.Q g z * D.post ℓ₁ z) := by
                              apply Finset.sum_congr rfl
                              intro ℓ₀ _
                              ring
                      _ = (∑ ℓ₀ ∈ univ.filter (fun ℓ₀ => K.cl ℓ₀ = g),
                            D.L.prior ℓ₀) * (K.Q g z * D.post ℓ₁ z) := by
                              rw [Finset.sum_mul]
                      _ = (∑ ℓ₀ ∈ univ.filter (fun ℓ₀ => K.cl ℓ₀ = g),
                            D.L.prior ℓ₀) * K.Q g z * D.post ℓ₁ z := by ring
        calc
          (∑ ℓ₂, ∑ ℓ₁, ∑ ℓ₀,
            if K.cl ℓ₁ = d then
              (if K.cl ℓ₀ = g then
                p z * D.post ℓ₀ z * D.post ℓ₁ z * D.post ℓ₂ z else 0)
            else 0) =
              ∑ ℓ₁, ∑ ℓ₀, ∑ ℓ₂,
                if K.cl ℓ₁ = d then
                  (if K.cl ℓ₀ = g then
                    p z * D.post ℓ₀ z * D.post ℓ₁ z * D.post ℓ₂ z else 0)
                else 0 := by
                  rw [Finset.sum_comm]
                  apply Finset.sum_congr rfl
                  intro ℓ₁ _
                  exact Finset.sum_comm
          _ = ∑ ℓ₁, if K.cl ℓ₁ = d then
                (∑ ℓ₀, if K.cl ℓ₀ = g then
                  p z * D.post ℓ₀ z * D.post ℓ₁ z else 0)
              else 0 := by
                apply Finset.sum_congr rfl
                intro ℓ₁ _
                by_cases h₁ : K.cl ℓ₁ = d
                · simp only [h₁, if_true]
                  apply Finset.sum_congr rfl
                  intro ℓ₀ _
                  by_cases h₀ : K.cl ℓ₀ = g
                  · simp only [h₀, if_true]
                    exact hsum₂ ℓ₀ ℓ₁
                  · simp [h₀]
                · simp [h₁]
          _ = ∑ ℓ₁, if K.cl ℓ₁ = d then
                K.s g * K.Q g z * D.post ℓ₁ z else 0 := by
                apply Finset.sum_congr rfl
                intro ℓ₁ _
                by_cases h₁ : K.cl ℓ₁ = d <;> simp [h₁, hsource ℓ₁]
          _ = K.s g * ∑ ℓ ∈ univ.filter (fun ℓ => K.cl ℓ = d),
                K.Q g z * D.post ℓ z := by
                rw [Finset.mul_sum, Finset.sum_filter]
                apply Finset.sum_congr rfl
                intro ℓ _
                by_cases hℓ : K.cl ℓ = d
                · simp [hℓ]
                  ring
                · simp [hℓ]

private lemma bZ_eq_posterior_sum :
    bZ D = ∑ ℓ, D.L.prior ℓ *
      MI (fun v : D.L.ι × (α × β) => v.1) (fun v => v.2)
        (posteriorJoint K (K.cl ℓ)) := by
  unfold bZ
  rw [condMI_eq_sum_MI_fibers (replicaLaw_isPMF D)]
  apply Finset.sum_congr rfl
  intro ℓ₁ _
  let fiber : D.L.ι × D.L.ι × D.L.ι × (α × β) → ℝ :=
    fun u => if u.2.1 = ℓ₁ then replicaLaw D u else 0
  calc
    MI (fun u : D.L.ι × D.L.ι × D.L.ι × (α × β) => u.1)
        (fun u => u.2.2.2) fiber =
        MI Prod.fst Prod.snd
          (push (fun u : D.L.ι × D.L.ι × D.L.ι × (α × β) =>
            (u.1, u.2.2.2)) fiber) :=
      MI_eq_joint_push fiber (fun u => u.1) (fun u => u.2.2.2)
    _ = MI Prod.fst Prod.snd
        (fun v => D.L.prior ℓ₁ * posteriorJoint K (K.cl ℓ₁) v) := by
      rw [show fiber = fun u => if u.2.1 = ℓ₁ then replicaLaw D u else 0 by rfl,
        push_replica_condition_label K ℓ₁]
    _ = D.L.prior ℓ₁ *
        MI (fun v : D.L.ι × (α × β) => v.1) (fun v => v.2)
          (posteriorJoint K (K.cl ℓ₁)) := by
      exact MI_smul (posteriorJoint_isPMF K (K.cl ℓ₁)).isFinMeas
        Prod.fst Prod.snd (D.L.prior_isPMF.nonneg ℓ₁)

private lemma bZ_eq_cluster_posterior_sum :
    bZ D = ∑ g, K.s g *
      MI (fun v : D.L.ι × (α × β) => v.1) (fun v => v.2)
        (posteriorJoint K g) := by
  rw [bZ_eq_posterior_sum K]
  have hpush : push K.cl D.L.prior = fun g => K.s g := by
    rfl
  have hsum := sum_push_mul K.cl D.L.prior
    (fun g => MI (fun v : D.L.ι × (α × β) => v.1) (fun v => v.2)
      (posteriorJoint K g))
  rw [hpush] at hsum
  exact hsum.symm

private lemma Sinfo_eq_cluster_posterior_sum :
    K.Sinfo = ∑ g, K.s g *
      MI (fun v : D.L.ι × (α × β) => v.1) (fun v => v.2)
        (posteriorJoint K g) := by
  unfold Sinfo
  rw [condMI_eq_sum_MI_fibers (replicaLaw_isPMF D)]
  apply Finset.sum_congr rfl
  intro g _
  let fiber : D.L.ι × D.L.ι × D.L.ι × (α × β) → ℝ :=
    fun u => if K.cl u.1 = g then replicaLaw D u else 0
  let clusterJoint : K.κ × (α × β) → ℝ :=
    push (fun w : D.L.ι × (α × β) => (K.cl w.1, w.2)) (posteriorJoint K g)
  have hcluster_fin : IsFinMeas clusterJoint := by
    exact isFinMeas_push (posteriorJoint_isPMF K g).isFinMeas
  calc
    MI (fun u : D.L.ι × D.L.ι × D.L.ι × (α × β) => K.cl u.2.1)
        (fun u => u.2.2.2) fiber =
        MI Prod.fst Prod.snd
          (push (fun u : D.L.ι × D.L.ι × D.L.ι × (α × β) =>
            (K.cl u.2.1, u.2.2.2)) fiber) :=
      MI_eq_joint_push fiber (fun u => K.cl u.2.1) (fun u => u.2.2.2)
    _ = MI Prod.fst Prod.snd (fun v => K.s g * clusterJoint v) := by
      rw [show fiber = fun u => if K.cl u.1 = g then replicaLaw D u else 0 by rfl,
        push_replica_condition_cluster K g]
    _ = K.s g * MI Prod.fst Prod.snd clusterJoint := by
      exact MI_smul hcluster_fin Prod.fst Prod.snd (s_pos_local K g).le
    _ = K.s g *
        MI (fun v : D.L.ι × (α × β) => K.cl v.1) (fun v => v.2)
          (posteriorJoint K g) := by
      rw [MI_eq_joint_push (posteriorJoint K g)
        (fun v : D.L.ι × (α × β) => K.cl v.1) (fun v => v.2)]
    _ = K.s g *
        MI (fun v : D.L.ι × (α × β) => v.1) (fun v => v.2)
          (posteriorJoint K g) := by
      rw [← MI_posteriorJoint_eq_cluster K g]

private lemma posterior_mismatch_eq (z : α × β) (hz : p z ≠ 0) :
    (∑ ℓ₁, ∑ ℓ₀,
      if K.cl ℓ₀ ≠ K.cl ℓ₁ then D.post ℓ₀ z * D.post ℓ₁ z else 0) =
        1 - ∑ c, K.sigma c z ^ 2 := by
  have hpost : ∑ ℓ, D.post ℓ z = 1 := sum_post_eq_one (D := D) z hz
  have hneq (ℓ₁ : D.L.ι) :
      (∑ ℓ₀ ∈ univ.filter (fun ℓ₀ => K.cl ℓ₀ ≠ K.cl ℓ₁), D.post ℓ₀ z) =
        1 - K.sigma (K.cl ℓ₁) z := by
    have hsplit := Finset.sum_filter_add_sum_filter_not univ
      (fun ℓ₀ => K.cl ℓ₀ ≠ K.cl ℓ₁) (fun ℓ₀ => D.post ℓ₀ z)
    have heq :
        (∑ ℓ₀ ∈ univ.filter (fun ℓ₀ => ¬K.cl ℓ₀ ≠ K.cl ℓ₁), D.post ℓ₀ z) =
          K.sigma (K.cl ℓ₁) z := by
      simp only [not_ne_iff]
      rfl
    rw [heq] at hsplit
    have htotal : ∑ ℓ₀ ∈ univ, D.post ℓ₀ z = 1 := by
      simpa using hpost
    rw [htotal] at hsplit
    linarith
  have hinner (ℓ₁ : D.L.ι) :
      (∑ ℓ₀,
        if K.cl ℓ₀ ≠ K.cl ℓ₁ then D.post ℓ₀ z * D.post ℓ₁ z else 0) =
          (1 - K.sigma (K.cl ℓ₁) z) * D.post ℓ₁ z := by
    calc
      (∑ ℓ₀,
        if K.cl ℓ₀ ≠ K.cl ℓ₁ then D.post ℓ₀ z * D.post ℓ₁ z else 0) =
          ∑ ℓ₀ ∈ univ.filter (fun ℓ₀ => K.cl ℓ₀ ≠ K.cl ℓ₁),
            D.post ℓ₀ z * D.post ℓ₁ z := by
              rw [Finset.sum_filter]
      _ = (∑ ℓ₀ ∈ univ.filter (fun ℓ₀ => K.cl ℓ₀ ≠ K.cl ℓ₁),
              D.post ℓ₀ z) * D.post ℓ₁ z := by
            rw [Finset.sum_mul]
      _ = (1 - K.sigma (K.cl ℓ₁) z) * D.post ℓ₁ z := by rw [hneq]
  have hweighted :=
    sum_push_mul K.cl (fun ℓ => D.post ℓ z) (fun c => K.sigma c z)
  rw [sigma_eq_push K z] at hweighted
  calc
    (∑ ℓ₁, ∑ ℓ₀,
      if K.cl ℓ₀ ≠ K.cl ℓ₁ then D.post ℓ₀ z * D.post ℓ₁ z else 0) =
        ∑ ℓ₁, (1 - K.sigma (K.cl ℓ₁) z) * D.post ℓ₁ z := by
          apply Finset.sum_congr rfl
          intro ℓ₁ _
          exact hinner ℓ₁
    _ = (∑ ℓ₁, D.post ℓ₁ z) -
        ∑ ℓ₁, D.post ℓ₁ z * K.sigma (K.cl ℓ₁) z := by
          rw [← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro ℓ₁ _
          ring
    _ = 1 - ∑ c, K.sigma c z * K.sigma c z := by
          rw [hpost, ← hweighted]
    _ = 1 - ∑ c, K.sigma c z ^ 2 := by
          congr 1
          apply Finset.sum_congr rfl
          intro c _
          ring

private lemma dMis_eq_sum_posterior_mismatch :
    K.dMis = ∑ z, p z * (∑ ℓ₁, ∑ ℓ₀,
      if K.cl ℓ₀ ≠ K.cl ℓ₁ then D.post ℓ₀ z * D.post ℓ₁ z else 0) := by
  unfold dMis replicaLaw
  rw [Finset.sum_filter]
  rw [Fintype.sum_prod_type_right, Fintype.sum_prod_type_right,
    Fintype.sum_prod_type_right]
  apply Finset.sum_congr rfl
  intro z _
  by_cases hz : p z = 0
  · simp [hz]
  · let pairSum : ℝ := ∑ ℓ₁, ∑ ℓ₀,
      if K.cl ℓ₀ ≠ K.cl ℓ₁ then D.post ℓ₀ z * D.post ℓ₁ z else 0
    have hfactor (ℓ₂ : D.L.ι) :
        (∑ ℓ₁, ∑ ℓ₀,
          if K.cl ℓ₀ ≠ K.cl ℓ₁ then
            p z * D.post ℓ₀ z * D.post ℓ₁ z * D.post ℓ₂ z else 0) =
          (p z * D.post ℓ₂ z) * pairSum := by
      dsimp only [pairSum]
      symm
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ℓ₁ _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ℓ₀ _
      by_cases hcl : K.cl ℓ₀ ≠ K.cl ℓ₁
      · simp [hcl]
        ring
      · simp [hcl]
    calc
      (∑ ℓ₂, ∑ ℓ₁, ∑ ℓ₀,
        if K.cl ℓ₀ ≠ K.cl ℓ₁ then
          p z * D.post ℓ₀ z * D.post ℓ₁ z * D.post ℓ₂ z else 0) =
          ∑ ℓ₂, (p z * D.post ℓ₂ z) * pairSum := by
            apply Finset.sum_congr rfl
            intro ℓ₂ _
            exact hfactor ℓ₂
      _ = p z * ∑ ℓ₂, D.post ℓ₂ z * pairSum := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro ℓ₂ _
            ring
      _ = p z * ((∑ ℓ₂, D.post ℓ₂ z) * pairSum) := by
            rw [Finset.sum_mul]
      _ = p z * pairSum := by rw [sum_post_eq_one (D := D) z hz, one_mul]

/-- **Lemma 7.2(d)**: `I(L₁;Z ∣ L₀) = S = b_Z`.
*Finite* — a `push_push` computation using `post_eq_sigma_mul`. -/
theorem Sinfo_eq_bZ : K.Sinfo = bZ D := by
  rw [Sinfo_eq_cluster_posterior_sum K, bZ_eq_cluster_posterior_sum K]

/-- **Lemma 7.2(d)**, second half: `d = E_p[1 − ∑_c σ_c(Z)²]`.
*Finite.* Used by Theorem 10.1's final line. -/
theorem dMis_eq : K.dMis = ∑ z, p z * (1 - ∑ c, K.sigma c z ^ 2) := by
  rw [dMis_eq_sum_posterior_mismatch K]
  apply Finset.sum_congr rfl
  intro z _
  by_cases hz : p z = 0
  · simp [hz]
  · rw [posterior_mismatch_eq K z hz]

theorem dMis_nonneg : 0 ≤ K.dMis := by
  unfold dMis
  exact Finset.sum_nonneg fun u _ => (replicaLaw_isPMF D).nonneg u

/-! ### Lemma 7.4 — the exact race law

At fixed `Z = z` the cluster clocks `T_c := X*_c/σ_c(z)` are
independent `Exp(σ_c(z))` (rate form), giving

* `P(Z=z, B=b, U ∈ du ∣ C₀=g) = q_g(z) e^{−u/σ_b(z)} du`  (7.1)
* losing clocks `X*_c ∼ u r_c(z) + Exp(1)`, independent          (7.2)
* `T := U/σ_B(Z) ∼ Exp(1)` independent of `(B,Z)`, and `P(B=b ∣ Z=z) = σ_b(z)`.

These are the inputs to §§8 and 10. -/

/-- The conditional law of the winner's raw clock `U` given `(Z = z, B = b)`:
an exponential of **mean** `σ_b(z)`, i.e. rate `1/σ_b(z)` (Lemma 7.4). -/
noncomputable def clockLawGiven (b : K.κ) (z : α × β) : Measure ℝ :=
  expMeasure (1 / K.sigma b z)

end Clustering

/-! ### The seed interface

§§8-11 are theorems about any `RaceQuantities`. Its equation fields are
Lemmas 7.3 and 7.5; the construction also records nonnegativity, the §8/§10
channel bounds, and the §12 cell-residual link. -/

/-- The four seed-level scalars of §§7-11, with the structural identities and
bounds the assembly uses. See this module's docstring on why they are packaged
rather than defined. -/
structure RaceQuantities {p : α × β → ℝ} (D : SeedSetup p) (K : Clustering D) where
  /-- `D = I(ε; Z ∣ A, L₀)`, the seed leak. -/
  seedLeak : ℝ
  /-- `scalar = I(U; Z ∣ B, C₀)`. -/
  scalar : ℝ
  /-- `cone = I(X*₋B; Z ∣ B, C₀, U)`. -/
  cone : ℝ
  /-- `H(A ∣ ε, L₀)`, the quantity Theorem 11.1 bounds. -/
  winnerEntropy : ℝ
  /-- **Lemma 7.5** (exact chain split). -/
  chain_split : seedLeak = scalar + cone
  /-- **Lemma 7.3** (winner-entropy identity):
  `H(A ∣ ε,L₀) = I(L₁;Z ∣ L₀) + D_lab`, with `D_lab = D` by Lemma 7.2(c). -/
  winner_entropy_identity : winnerEntropy = K.Sinfo + seedLeak
  /-- `D_lab ≥ 0`. -/
  seedLeak_nonneg : 0 ≤ seedLeak
  scalar_nonneg : 0 ≤ scalar
  cone_nonneg : 0 ≤ cone
  /-- **Theorem 8.1** (*cone-scalar-channel-bound*, first half), in bits:
  `scalar ≤ S + κ d`. Proved by the race
  construction (`stoch_to_det/Race.lean`). -/
  scalar_le : scalar ≤ K.Sinfo + kappa * K.dMis
  /-- **Theorem 10.1** (*cone-orthant-bound*), in
  nats: `cone · ln 2 ≤ d`. Proved by the race construction. -/
  cone_le_nats : cone * Real.log 2 ≤ K.dMis
  /-- The `I ≤ H` link of Theorem 12.1: the cell
  residual is at most three times the winner entropy. Proved by the race
  construction. -/
  rcell_le : Rcell D ≤ 3 * winnerEntropy

/-- The race interface extended by the sharpened scalar-channel estimate.
Keeping this as an extension preserves the audited
historical theorem unchanged. -/
structure RaceQuantities1771 {p : α × β → ℝ}
    (D : SeedSetup p) (K : Clustering D) extends RaceQuantities D K where
  scalar_le_1771 : toRaceQuantities.scalar ≤
    K.Sinfo + kappa1771 * K.dMis

/-- The race interface with the sharpened quarter-diagonal scalar estimate.
The off-diagonal estimate is unchanged, so the natural-log mismatch charge
is `1/4 + cOff1771`. -/
structure RaceQuantitiesQuarter {p : α × β → ℝ}
    (D : SeedSetup p) (K : Clustering D) extends RaceQuantities D K where
  scalar_le_quarter : toRaceQuantities.scalar ≤
    K.Sinfo + ((1 / 4 + cOff1771) / Real.log 2) * K.dMis

end stoch_to_det
