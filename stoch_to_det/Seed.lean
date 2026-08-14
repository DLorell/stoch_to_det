import Mathlib.Probability.Distributions.Exponential
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.InformationTheory.KullbackLeibler.Basic
import stoch_to_det.Duality
import stoch_to_det.Toolkit

/-!
# §4-§5. The calibrated shared-Gumbel race, and posterior replicas


## Where the finite part ends

This is where the development leaves the finite world. For a *fixed* seed `ε`, the
winner `A_ε` is a deterministic function of `z` and Lemma 4.3's first display

  `∑ₐ μₐ^ε G_w(rₐ^ε) = S_p(A_ε) − τ(p)`

is an identity between finite sums — `Gdef_fusion` applied to one mixture. No
measure theory. The measure enters at exactly two points:

1. `Dwdefect` — the average over `ε` — and Corollary 4.4, which only needs
   *existence of one good seed* (`exists_good_seed` below);
2. `§7`-`§11`, where `I(ε; Z ∣ A, L₀)` is genuinely an information quantity of
   a continuous variable.

Correspondingly, §5 is **entirely finite except Theorem 5.7**: `L₀, L₁, L₂` are
finite-valued, so Lemmas 5.2, 5.3, 5.4 and 5.6 are finite statements about the
replica coupling and are listed here with no measure-theoretic hypotheses.

## Representation of the seed

There are two equivalent pictures: iid standard
Gumbel `ε`, or iid `Exp(1)` clocks `E_ℓ = e^{−ε_ℓ}` raced at rates `t_ℓ(z)`.
Here the exponential picture is primitive (`clockLaw`), matching §7.4 and §10,
which work in it throughout (memorylessness, shifted-exponential losing clocks),
and matching Mathlib's `ProbabilityTheory.expMeasure`. The Gumbel form is the
pushforward along the bijection `ε = −log E`.

## Conditional mutual information against a continuous variable

`I(ε; Z ∣ A, L₀)` pairs a continuous `ε` against a **finite** `Z`. For finite
`Z` conditioned on finite variables,

  `I(W ; Z ∣ C) = ∑_{z,c} P(z,c) · D( Law(W ∣ z,c) ‖ Law(W ∣ c) )`,

a KL between measures on `ι → ℝ`, always well defined; `condMIcts` below takes
this as its definition, over Mathlib's `InformationTheory.klDiv` (`ℝ≥0∞`, nats).
No general theory of mutual information is involved.
-/

namespace stoch_to_det

open Finset MeasureTheory ProbabilityTheory InformationTheory

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

/-! ### The standing data of §§4-12 -/

/-- The data fixed once and for all by Theorem 2.5 for the rest of the proof
: a law with connected support together with an attained
`τ`-optimal common-contact pair `(L, w)`. -/
structure SeedSetup (p : α × β → ℝ) where
  /-- `p` is a probability law. -/
  isPMF : IsPMF p
  /-- Standing assumption of §§4-12. -/
  conn : IsConnected (support p)
  /-- The attaining latent of Corollary 1.3. -/
  L : Latent p
  /-- The `τ`-optimal kernel of Corollary 2.4. -/
  w : α × β → ℝ
  /-- `w` is feasible. -/
  feasible : Feasible (support p) w
  /-- `L` attains `τ`. -/
  optimal : L.score = tau p
  /-- Every positive component of `L` is a contact of `w` (Theorem 2.5). -/
  contact : ∀ v, L.prior v ≠ 0 → IsContact (support p) w (L.comp v)
  /-- All prior weights are strictly positive: zero-mass labels are pruned
  when the setup is constructed (`exists_seedSetup`). §7's clustering
  needs this. -/
  prior_pos : ∀ v, 0 < L.prior v

namespace SeedSetup

variable {p : α × β → ℝ} (D : SeedSetup p)

/-- The posterior `t_ℓ(z) := λ_ℓ q^ℓ(z) / p(z)`. -/
noncomputable def post (ℓ : D.L.ι) (z : α × β) : ℝ := D.L.prior ℓ * D.L.comp ℓ z / p z

/-- `M := I(X;Y ∣ L)`. -/
noncomputable def M : ℝ :=
  condMI (fun q => q.2.1) (fun q => q.2.2) (fun q => q.1) D.L.joint

/-- `B := I(L;X ∣ Y) + I(L;Y ∣ X)`. -/
noncomputable def Bq : ℝ :=
  condMI (fun q => q.1) (fun q => q.2.1) (fun q => q.2.2) D.L.joint
    + condMI (fun q => q.1) (fun q => q.2.2) (fun q => q.2.1) D.L.joint

/-- `τ = S_p(L) = M + B`. -/
lemma tau_eq_M_add_Bq : tau p = D.M + D.Bq := by
  rw [← D.optimal]
  unfold Latent.score M Bq
  ring

end SeedSetup

private lemma sum_ne_zero_subtype_eq {κ : Type*} [Fintype κ]
    (a f : κ → ℝ) (hf : ∀ i, a i = 0 → f i = 0) :
    (∑ i : {i : κ // a i ≠ 0}, f i.1) = ∑ i, f i := by
  classical
  have hsplit := Fintype.sum_subtype_add_sum_subtype (fun i => a i ≠ 0) f
  have hzero : (∑ i : {i : κ // ¬ a i ≠ 0}, f i.1) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    exact hf i.1 (not_ne_iff.mp i.2)
  rw [hzero, add_zero] at hsplit
  exact hsplit

/-- Theorem 2.5 packaged as a `SeedSetup`: prune the zero-prior labels
of `exists_common_contact_pair`'s latent (pruning to the subtype
`{v // L.prior v ≠ 0}` preserves the score and the mixture). -/
theorem exists_seedSetup {p : α × β → ℝ} (hp : IsPMF p)
    (hconn : IsConnected (support p)) :
    Nonempty (SeedSetup p) := by
  rcases exists_common_contact_pair hp with ⟨L, w, hw, hoptimal, hcontact⟩
  let L' : Latent p := {
    ι := {v : L.ι // L.prior v ≠ 0}
    fin := inferInstance
    dec := inferInstance
    prior := fun v => L.prior v.1
    comp := fun v => L.comp v.1
    prior_isPMF := by
      refine ⟨fun v => L.prior_isPMF.nonneg v.1, ?_⟩
      rw [mass, sum_ne_zero_subtype_eq L.prior L.prior (fun _ h => h)]
      simpa [mass] using L.prior_isPMF.total
    comp_isPMF := fun v => L.comp_isPMF v.1
    mixture := by
      intro z
      rw [sum_ne_zero_subtype_eq L.prior
        (fun v => L.prior v * L.comp v z) (fun _ h => by simp [h])]
      exact L.mixture z
  }
  have hpayoff :
      (∑ v, L'.prior v * Phi (L'.comp v)) =
        ∑ v, L.prior v * Phi (L.comp v) := by
    change (∑ v : {v : L.ι // L.prior v ≠ 0},
      L.prior v.1 * Phi (L.comp v.1)) = ∑ v, L.prior v * Phi (L.comp v)
    exact sum_ne_zero_subtype_eq L.prior
      (fun v => L.prior v * Phi (L.comp v)) (fun _ h => by simp [h])
  have hscore : L'.score = L.score := by
    rw [Latent.score_eq hp L', Latent.score_eq hp L, hpayoff]
  refine ⟨{
    isPMF := hp
    conn := hconn
    L := L'
    w := w
    feasible := hw
    optimal := hscore.trans hoptimal
    contact := ?_
    prior_pos := ?_
  }⟩
  · intro v _
    change IsContact (support p) w (L.comp v.1)
    exact hcontact v.1 v.2
  · intro v
    change 0 < L.prior v.1
    exact lt_of_le_of_ne (L.prior_isPMF.nonneg v.1) (Ne.symm v.2)

/-! ### Definition 4.1 — the race at a fixed seed -/

section FixedSeed

variable {p : α × β → ℝ} (D : SeedSetup p)

/-- The **calibrated shared-Gumbel winner** `A_ε(z) := argmax_ℓ [ln tℓ(z) + εℓ]`
. Ties are broken by `Finite.exists_max`'s choice; Lemma 4.2 shows ties are null. -/
noncomputable def winner (ε : D.L.ι → ℝ) (z : α × β) : D.L.ι :=
  Classical.choose (Finite.exists_max fun ℓ => Real.log (D.post ℓ z) + ε ℓ)

/-- The winner cell `C_a^ε := {z : A_ε(z) = a}`. -/
noncomputable def cell (ε : D.L.ι → ℝ) (a : D.L.ι) : Finset (α × β) :=
  univ.filter (fun z => winner D ε z = a)

/-- The cell mass `μ_a^ε := p(C_a^ε)`. -/
noncomputable def cellMass (ε : D.L.ι → ℝ) (a : D.L.ι) : ℝ := ∑ z ∈ cell D ε a, p z

/-- The conditional law `r_a^ε := p(· ∣ C_a^ε)`.
For zero-mass cells this falls back to `p`,
which keeps `winnerLatent.comp_isPMF` provable and changes no expression
weighted by the zero cell mass. -/
noncomputable def cellLaw (ε : D.L.ι → ℝ) (a : D.L.ι) (z : α × β) : ℝ :=
  if cellMass D ε a = 0 then p z
  else if winner D ε z = a then p z / cellMass D ε a else 0

private lemma cellMass_nonneg (ε : D.L.ι → ℝ) (a : D.L.ι) :
    0 ≤ cellMass D ε a := by
  exact Finset.sum_nonneg fun z _ => D.isPMF.nonneg z

private lemma sum_cellMass (ε : D.L.ι → ℝ) :
    ∑ a, cellMass D ε a = 1 := by
  unfold cellMass cell
  calc
    ∑ a, ∑ z ∈ univ.filter (fun z => winner D ε z = a), p z = ∑ z, p z :=
      Finset.sum_fiberwise univ (winner D ε) p
    _ = 1 := by simpa [mass] using D.isPMF.total

private lemma le_cellMass_winner (ε : D.L.ι → ℝ) (z : α × β) :
    p z ≤ cellMass D ε (winner D ε z) := by
  unfold cellMass
  apply Finset.single_le_sum (fun z _ => D.isPMF.nonneg z)
  simp [cell]

private lemma cellMass_mul_cellLaw (ε : D.L.ι → ℝ) (a : D.L.ι) (z : α × β) :
    cellMass D ε a * cellLaw D ε a z =
      if winner D ε z = a then p z else 0 := by
  by_cases hmass : cellMass D ε a = 0
  · by_cases hw : winner D ε z = a
    · have hzle := le_cellMass_winner D ε z
      rw [hw, hmass] at hzle
      have hpz : p z = 0 := le_antisymm hzle (D.isPMF.nonneg z)
      simp [cellLaw, hmass, hw, hpz]
    · simp [cellLaw, hmass, hw]
  · by_cases hw : winner D ε z = a
    · simp only [cellLaw, hmass, if_false, hw, if_true]
      field_simp
    · simp [cellLaw, hmass, hw]

private lemma law_supported_support : Supported (support p) p := by
  intro z hz
  simpa [support] using hz

private lemma cellLaw_supported (ε : D.L.ι → ℝ) (a : D.L.ι) :
    Supported (support p) (cellLaw D ε a) := by
  intro z hz
  have hpz : p z = 0 := law_supported_support z hz
  simp [cellLaw, hpz]

/-- At a fixed seed, `A_ε` is a deterministic latent for `p`. This is what makes
Corollary 4.4 a statement about `T`. -/
noncomputable def winnerLatent (ε : D.L.ι → ℝ) : Latent p where
  ι := D.L.ι
  fin := D.L.fin
  dec := D.L.dec
  prior := cellMass D ε
  comp := cellLaw D ε
  prior_isPMF := ⟨cellMass_nonneg D ε, sum_cellMass D ε⟩
  comp_isPMF := by
    intro a
    by_cases hmass : cellMass D ε a = 0
    · have hcell : cellLaw D ε a = p := by
        funext z
        simp [cellLaw, hmass]
      rw [hcell]
      exact D.isPMF
    · have hmass_nonneg := cellMass_nonneg D ε a
      refine ⟨?_, ?_⟩
      · intro z
        by_cases hw : winner D ε z = a
        · simp [cellLaw, hmass, hw, div_nonneg (D.isPMF.nonneg z) hmass_nonneg]
        · simp [cellLaw, hmass, hw]
      · unfold mass
        simp only [cellLaw, hmass, if_false]
        calc
          ∑ z, (if winner D ε z = a then p z / cellMass D ε a else 0) =
              ∑ z ∈ cell D ε a, p z / cellMass D ε a := by
                rw [cell, Finset.sum_filter]
          _ = cellMass D ε a / cellMass D ε a := by
                simp only [div_eq_mul_inv, ← Finset.sum_mul]
                rfl
          _ = 1 := div_self hmass
  mixture := by
    intro z
    simp_rw [cellMass_mul_cellLaw D ε]
    simp

lemma winnerLatent_isDet (ε : D.L.ι → ℝ) : (winnerLatent D ε).IsDet := by
  change ∀ z, ∀ a b : D.L.ι,
    cellMass D ε a * cellLaw D ε a z ≠ 0 →
      cellMass D ε b * cellLaw D ε b z ≠ 0 → a = b
  intro z a b ha hb
  rw [cellMass_mul_cellLaw D ε] at ha hb
  have hwa : winner D ε z = a := by
    by_contra h
    simp [h] at ha
  have hwb : winner D ε z = b := by
    by_contra h
    simp [h] at hb
  exact hwa.symm.trans hwb

/-- **Lemma 4.3**, per-seed half. *Finite: no measure theory.*
`∑ₐ μₐ^ε G_w(rₐ^ε) = S_p(A_ε) − τ(p)`.

It follows from `Gdef_fusion` (Lemma 2.8(a)),
`Latent.score_sub_Ixy` (Lemma 1.2) and `Gdef_of_common_contact_pair`
(Lemma 2.8(c)). -/
theorem per_seed_ledger (ε : D.L.ι → ℝ) :
    (∑ a, cellMass D ε a * Gdef (support p) D.w (cellLaw D ε a))
      = (winnerLatent D ε).score - tau p := by
  let V := winnerLatent D ε
  have hfusion := Gdef_fusion D.feasible.1 D.isPMF law_supported_support V
  have hscore := Latent.score_sub_Ixy D.isPMF V
  have hbase := Gdef_of_common_contact_pair D.isPMF D.L D.feasible D.optimal D.contact
  change (∑ a, V.prior a * Gdef (support p) D.w (V.comp a)) = V.score - tau p
  calc
    ∑ a, V.prior a * Gdef (support p) D.w (V.comp a) =
        ((∑ a, V.prior a * Gdef (support p) D.w (V.comp a)) -
          Gdef (support p) D.w p) + Gdef (support p) D.w p := by ring
    _ = (V.score - Ixy p) + (Ixy p - tau p) := by
      rw [hfusion, ← hscore, hbase]
    _ = V.score - tau p := by ring

/-- Each per-seed ledger term is nonnegative (Theorem 2.3). -/
theorem per_seed_ledger_nonneg (ε : D.L.ι → ℝ) :
    0 ≤ ∑ a, cellMass D ε a * Gdef (support p) D.w (cellLaw D ε a) := by
  apply Finset.sum_nonneg
  intro a _
  apply mul_nonneg (cellMass_nonneg D ε a)
  apply Gdef_nonneg D.feasible
  · exact (winnerLatent D ε).comp_isPMF a
  · exact cellLaw_supported D ε a

end FixedSeed

/-! ### The seed law -/

/-- The clock law: iid `Exp(1)` coordinates, `E_ℓ = e^{−ε_ℓ}`.
Taken as primitive because §7.4 and §10 reason by memorylessness. -/
noncomputable def clockLaw (ι : Type) [Fintype ι] : Measure (ι → ℝ) :=
  Measure.pi fun _ : ι => expMeasure 1

instance (ι : Type) [Fintype ι] : IsProbabilityMeasure (clockLaw ι) := by
  unfold clockLaw
  letI : ∀ _ : ι, IsProbabilityMeasure (expMeasure 1) :=
    fun _ => isProbabilityMeasure_expMeasure zero_lt_one
  infer_instance

/-- The seed law on `ι → ℝ`: iid standard Gumbel, the pushforward of `clockLaw`
under `E ↦ −log E`. -/
noncomputable def seedLaw (ι : Type) [Fintype ι] : Measure (ι → ℝ) :=
  (clockLaw ι).map fun E i => -Real.log (E i)

instance (ι : Type) [Fintype ι] : IsProbabilityMeasure (seedLaw ι) := by
  unfold seedLaw
  apply Measure.isProbabilityMeasure_map
  exact (measurable_pi_lambda _ fun i =>
    (Real.measurable_log.comp (measurable_pi_apply i)).neg).aemeasurable

/- The one-coordinate seed law is atomless.  The only junk-value issue is at
nonpositive clocks: `-log E = 0` there, but `Exp(1)` assigns that half-line
measure zero. -/
noncomputable def gumbel1 : Measure ℝ :=
  (expMeasure 1).map fun E => -Real.log E

instance : IsProbabilityMeasure gumbel1 := by
  letI : IsProbabilityMeasure (expMeasure 1) :=
    isProbabilityMeasure_expMeasure zero_lt_one
  unfold gumbel1
  apply Measure.isProbabilityMeasure_map
  exact Real.measurable_log.neg.aemeasurable

lemma expMeasure_one_Iic_zero : expMeasure 1 (Set.Iic 0) = 0 := by
  letI := isProbabilityMeasure_expMeasure (r := (1 : ℝ)) zero_lt_one
  have hreal : (expMeasure 1).real (Set.Iic 0) = 0 := by
    rw [← cdf_eq_real]
    simpa using cdf_expMeasure_eq (r := (1 : ℝ)) zero_lt_one 0
  exact (measureReal_eq_zero_iff).mp hreal

lemma expMeasure_one_Ioi (x : ℝ) (hx : 0 ≤ x) :
    expMeasure 1 (Set.Ioi x) = ENNReal.ofReal (Real.exp (-x)) := by
  letI := isProbabilityMeasure_expMeasure (r := (1 : ℝ)) zero_lt_one
  have hsub : 0 ≤ 1 - Real.exp (-x) := by
    exact sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by linarith))
  have hreal : (expMeasure 1).real (Set.Iic x) = 1 - Real.exp (-x) := by
    rw [← cdf_eq_real, cdf_expMeasure_eq (r := (1 : ℝ)) zero_lt_one x,
      if_pos hx]
    ring
  have hIic : expMeasure 1 (Set.Iic x) =
      ENNReal.ofReal (1 - Real.exp (-x)) := by
    rw [← ENNReal.toReal_eq_toReal_iff'
      (measure_ne_top (expMeasure 1) (Set.Iic x)) ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal hsub]
    simpa [measureReal_def] using hreal
  rw [show Set.Ioi x = (Set.Iic x)ᶜ by ext y; simp, measure_compl measurableSet_Iic
    (measure_ne_top (expMeasure 1) (Set.Iic x)), measure_univ, hIic,
    ← ENNReal.ofReal_one, ← ENNReal.ofReal_sub 1 hsub]
  congr 1
  ring

lemma expMeasure_one_laplace (c : ℝ) (hc : 0 ≤ c) :
    (∫⁻ x, ENNReal.ofReal (Real.exp (-(c * x))) ∂(expMeasure 1)) =
      ENNReal.ofReal (1 / (1 + c)) := by
  have hr : 0 < 1 + c := by linarith
  have hmeasPDF : Measurable (gammaPDF 1 1) :=
    (measurable_gammaPDFReal 1 1).ennreal_ofReal
  have hmeasExp : Measurable (fun x : ℝ =>
      ENNReal.ofReal (Real.exp (-(c * x)))) := by fun_prop
  unfold expMeasure gammaMeasure
  rw [lintegral_withDensity_eq_lintegral_mul volume hmeasPDF hmeasExp]
  have hpoint :
      (fun x : ℝ => gammaPDF 1 1 x * ENNReal.ofReal (Real.exp (-(c * x)))) =ᵐ[volume]
        Set.indicator (Set.Ioi 0)
          (fun x => ENNReal.ofReal (Real.exp (-((1 + c) * x)))) := by
    have hne : ∀ᵐ x : ℝ ∂volume, x ∉ ({0} : Set ℝ) :=
      measure_eq_zero_iff_ae_notMem.mp (measure_singleton 0)
    filter_upwards [hne] with x hx0
    by_cases hx : 0 < x
    · have hxmem : x ∈ Set.Ioi (0 : ℝ) := hx
      rw [Set.indicator_of_mem hxmem]
      simp only [gammaPDF_eq, if_pos hx.le, Real.one_rpow, Real.Gamma_one, div_one,
        sub_self, Real.rpow_zero, mul_one, one_mul]
      rw [← ENNReal.ofReal_mul (Real.exp_nonneg (-x)), ← Real.exp_add]
      congr 2
      ring
    · have hxne : x ≠ 0 := by simpa using hx0
      have hxneg : x < 0 := lt_of_le_of_ne (le_of_not_gt hx) hxne
      have hxmem : x ∉ Set.Ioi (0 : ℝ) := not_lt.mpr hxneg.le
      rw [Set.indicator_of_notMem hxmem]
      simp [gammaPDF_of_neg hxneg]
  change (∫⁻ x, gammaPDF 1 1 x * ENNReal.ofReal (Real.exp (-(c * x))) ∂volume) = _
  rw [lintegral_congr_ae hpoint, lintegral_indicator measurableSet_Ioi]
  have hint : IntegrableOn (fun x : ℝ => Real.exp (-((1 + c) * x))) (Set.Ioi 0) :=
    by
      convert exp_neg_integrableOn_Ioi 0 hr using 1
      funext x
      congr 2
      ring
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall fun x => Real.exp_nonneg _)]
  have hvalue := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (a := (1 : ℝ)) (r := 1 + c) zero_lt_one hr
  apply congrArg ENNReal.ofReal
  simpa using hvalue

def strictClockWin {κ : Type*} (t : κ → ℝ) (a : κ)
    (E : κ → ℝ) : Prop :=
  ∀ b, b ≠ a → E a / t a < E b / t b

lemma pi_exp_strictClockWin {κ : Type*} [Fintype κ] [DecidableEq κ]
    (t : κ → ℝ) (ht : ∀ a, 0 < t a) (htotal : ∑ a, t a = 1) (a : κ) :
    Measure.pi (fun _ : κ => expMeasure 1) {E | strictClockWin t a E} =
      ENNReal.ofReal (t a) := by
  letI : ∀ _ : κ, IsProbabilityMeasure (expMeasure 1) :=
    fun _ => isProbabilityMeasure_expMeasure zero_lt_one
  letI : IsProbabilityMeasure (expMeasure 1) :=
    isProbabilityMeasure_expMeasure zero_lt_one
  let e : Option {i : κ // i ≠ a} ≃ κ := Equiv.optionSubtypeNe a
  let f := (MeasurableEquiv.piOptionEquivProd
    (fun _ : Option {i : κ // i ≠ a} => ℝ)).symm
  let g := MeasurableEquiv.piCongrLeft (fun _ : κ => ℝ) e
  let q := (Measure.pi (fun _ : {i : κ // i ≠ a} => expMeasure 1)).prod
    (expMeasure 1)
  have hfirst :
      Measure.map f q =
        Measure.pi (fun _ : Option {i : κ // i ≠ a} => expMeasure 1) := by
    dsimp [f, q]
    exact Measure.pi_map_piOptionEquivProd
      (fun _ : Option {i : κ // i ≠ a} => expMeasure 1)
  have hsecond :
      Measure.map g
          (Measure.pi (fun _ : Option {i : κ // i ≠ a} => expMeasure 1)) =
        Measure.pi (fun _ : κ => expMeasure 1) := by
    dsimp [g]
    simpa [e] using Measure.pi_map_piCongrLeft e
      (fun _ : κ => expMeasure 1)
  have hmap : Measure.map (g ∘ f) q =
      Measure.pi (fun _ : κ => expMeasure 1) := by
    calc
      Measure.map (g ∘ f) q = Measure.map g (Measure.map f q) :=
        (Measure.map_map g.measurable f.measurable).symm
      _ = _ := by rw [hfirst, hsecond]
  have hset : MeasurableSet {E : κ → ℝ | strictClockWin t a E} := by
    unfold strictClockWin
    measurability
  rw [← hmap, Measure.map_apply (g.measurable.comp f.measurable) hset]
  have hpre : MeasurableSet ((g ∘ f) ⁻¹' {E : κ → ℝ | strictClockWin t a E}) :=
    hset.preimage (g.measurable.comp f.measurable)
  rw [Measure.prod_apply_symm hpre]
  have hsection (y : ℝ) :
      (fun x : {i : κ // i ≠ a} → ℝ => (x, y)) ⁻¹'
          ((g ∘ f) ⁻¹' {E : κ → ℝ | strictClockWin t a E}) =
        Set.pi Set.univ
          (fun i : {i : κ // i ≠ a} => Set.Ioi (t i.1 / t a * y)) := by
    ext x
    have hf_pair := (MeasurableEquiv.piOptionEquivProd
      (fun _ : Option {i : κ // i ≠ a} => ℝ)).apply_symm_apply (x, y)
    have hf_some (i : {i : κ // i ≠ a}) : f (x, y) (some i) = x i :=
      congrFun (congrArg Prod.fst hf_pair) i
    have hf_none : f (x, y) none = y := congrArg Prod.snd hf_pair
    have he_i (i : {i : κ // i ≠ a}) : (g (f (x, y))) i.1 = x i := by
      dsimp [g]
      rw [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]
      simp [e, Equiv.optionSubtypeNe_symm_of_ne i.2, hf_some]
    have he_a : (g (f (x, y))) a = y := by
      dsimp [g]
      rw [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]
      simp [e, hf_none]
    simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ,
      true_implies, Set.mem_Ioi]
    constructor
    · intro h i
      have hrel := h i.1 i.2
      change g (f (x, y)) a / t a < g (f (x, y)) i.1 / t i.1 at hrel
      rw [he_a, he_i] at hrel
      have hcross : y * t i.1 < x i * t a :=
        (div_lt_div_iff₀ (ht a) (ht i.1)).1 hrel
      have hdiv : t i.1 * y / t a < x i :=
        (div_lt_iff₀ (ht a)).2 (by nlinarith)
      simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hdiv
    · intro h b hba
      let i : {i : κ // i ≠ a} := ⟨b, hba⟩
      have hdiv := h i
      change t b / t a * y < x i at hdiv
      have hdiv' : t b * y / t a < x i := by
        simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hdiv
      have hcross : y * t b < x i * t a := by
        have := (div_lt_iff₀ (ht a)).1 hdiv'
        nlinarith
      change g (f (x, y)) a / t a < g (f (x, y)) b / t b
      have hib := he_i i
      change g (f (x, y)) b = x i at hib
      rw [he_a, hib]
      exact (div_lt_div_iff₀ (ht a) (ht b)).2 hcross
  simp_rw [hsection, Measure.pi_pi]
  let c : ℝ := ∑ i : {i : κ // i ≠ a}, t i.1 / t a
  have hsplit := Fintype.sum_eq_add_sum_subtype_ne t a
  have hsubsum : (∑ i : {i : κ // i ≠ a}, t i.1) = 1 - t a := by
    linarith
  have hc : c = (1 - t a) / t a := by
    dsimp [c]
    rw [← Finset.sum_div, hsubsum]
  have hc_nonneg : 0 ≤ c := by
    dsimp [c]
    exact Finset.sum_nonneg fun i _ => div_nonneg (ht i.1).le (ht a).le
  have hypos : ∀ᵐ y : ℝ ∂(expMeasure 1), 0 < y := by
    have hnot := measure_eq_zero_iff_ae_notMem.mp expMeasure_one_Iic_zero
    filter_upwards [hnot] with y hy
    simpa only [Set.mem_Iic, not_le] using hy
  have hprod : ∀ᵐ y : ℝ ∂(expMeasure 1),
      (∏ i : {i : κ // i ≠ a},
          expMeasure 1 (Set.Ioi (t i.1 / t a * y))) =
        ENNReal.ofReal (Real.exp (-(c * y))) := by
    filter_upwards [hypos] with y hy
    simp_rw [expMeasure_one_Ioi _
      (mul_nonneg (div_nonneg (ht _).le (ht a).le) hy.le)]
    rw [← ENNReal.ofReal_prod_of_nonneg
      (fun i _ => Real.exp_nonneg (-(t i.1 / t a * y))), ← Real.exp_sum]
    congr 2
    dsimp [c]
    rw [Finset.sum_neg_distrib, Finset.sum_mul]
  calc
    (∫⁻ y, ∏ i : {i : κ // i ≠ a},
        expMeasure 1 (Set.Ioi (t i.1 / t a * y)) ∂(expMeasure 1)) =
        ∫⁻ y, ENNReal.ofReal (Real.exp (-(c * y))) ∂(expMeasure 1) :=
      lintegral_congr_ae hprod
    _ = ENNReal.ofReal (1 / (1 + c)) := expMeasure_one_laplace c hc_nonneg
    _ = ENNReal.ofReal (t a) := by
      congr 1
      rw [hc]
      field_simp [(ht a).ne']
      ring

instance : NullSingletonClass gumbel1 where
  measure_singleton x := by
    letI : NullSingletonClass (expMeasure 1) := by
      unfold expMeasure gammaMeasure
      infer_instance
    have hsingle : expMeasure 1 ({Real.exp (-x)} : Set ℝ) = 0 := measure_singleton _
    unfold gumbel1
    rw [Measure.map_apply (f := fun E : ℝ => -Real.log E)
      Real.measurable_log.neg (measurableSet_singleton x)]
    apply measure_mono_null ?_
      (measure_union_null expMeasure_one_Iic_zero hsingle)
    intro E hE
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hE
    rw [Set.mem_union, Set.mem_Iic, Set.mem_singleton_iff]
    by_cases hpos : 0 < E
    · right
      rw [← Real.exp_log hpos]
      congr 1
      linarith
    · exact Or.inl (le_of_not_gt hpos)

lemma seedLaw_eq_pi_gumbel1 (ι : Type) [Fintype ι] :
    seedLaw ι = Measure.pi (fun _ : ι => gumbel1) := by
  letI : IsProbabilityMeasure (expMeasure 1) :=
    isProbabilityMeasure_expMeasure zero_lt_one
  letI : IsProbabilityMeasure
      ((expMeasure 1).map fun E : ℝ => -Real.log E) := by
    apply Measure.isProbabilityMeasure_map
    exact Real.measurable_log.neg.aemeasurable
  letI : ∀ _ : ι, SigmaFinite
      ((expMeasure 1).map fun E : ℝ => -Real.log E) := fun _ => inferInstance
  unfold seedLaw clockLaw gumbel1
  exact Measure.pi_map_pi fun _ => Real.measurable_log.neg.aemeasurable

/- An affine equality between two distinct coordinates has measure zero under
a finite product of any atomless sigma-finite law.  Splitting off the second
coordinate turns every section into a singleton. -/
lemma pi_affine_tie_null {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : Measure ℝ) [SigmaFinite μ] [NullSingletonClass μ]
    (a b : ι) (hab : a ≠ b) (ca cb : ℝ) :
    Measure.pi (fun _ : ι => μ) {ε | ca + ε a = cb + ε b} = 0 := by
  let e : Option {i : ι // i ≠ b} ≃ ι := Equiv.optionSubtypeNe b
  let f := (MeasurableEquiv.piOptionEquivProd
    (fun _ : Option {i : ι // i ≠ b} => ℝ)).symm
  let g := MeasurableEquiv.piCongrLeft (fun _ : ι => ℝ) e
  let q := (Measure.pi (fun _ : {i : ι // i ≠ b} => μ)).prod μ
  have hfirst :
      Measure.map f q = Measure.pi (fun _ : Option {i : ι // i ≠ b} => μ) := by
    dsimp [f, q]
    exact Measure.pi_map_piOptionEquivProd (fun _ : Option {i : ι // i ≠ b} => μ)
  have hsecond :
      Measure.map g (Measure.pi (fun _ : Option {i : ι // i ≠ b} => μ)) =
        Measure.pi (fun _ : ι => μ) := by
    dsimp [g]
    simpa [e] using Measure.pi_map_piCongrLeft e (fun _ : ι => μ)
  have hmap : Measure.map (g ∘ f) q = Measure.pi (fun _ : ι => μ) := by
    calc
      Measure.map (g ∘ f) q = Measure.map g (Measure.map f q) :=
        (Measure.map_map g.measurable f.measurable).symm
      _ = _ := by rw [hfirst, hsecond]
  rw [← hmap, Measure.map_apply (g.measurable.comp f.measurable)]
  · apply Measure.measure_prod_null_of_ae_null
    · exact (measurableSet_eq_fun
        ((measurable_pi_apply a).const_add ca)
        ((measurable_pi_apply b).const_add cb)).preimage
          (g.measurable.comp f.measurable)
    · filter_upwards [] with x
      have hsec :
          Set.preimage (Prod.mk x) (Set.preimage (g ∘ f)
            {ε : ι → ℝ | ca + ε a = cb + ε b}) =
            {ca + x ⟨a, hab⟩ - cb} := by
        ext y
        simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_singleton_iff]
        have hf_pair := (MeasurableEquiv.piOptionEquivProd
          (fun _ : Option {i : ι // i ≠ b} => ℝ)).apply_symm_apply (x, y)
        have hf_some (i : {i : ι // i ≠ b}) : f (x, y) (some i) = x i := by
          exact congrFun (congrArg Prod.fst hf_pair) i
        have hf_none : f (x, y) none = y := by
          exact congrArg Prod.snd hf_pair
        have he_a : (g (f (x, y))) a = x ⟨a, hab⟩ := by
          dsimp [g]
          rw [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]
          simp [e, Equiv.optionSubtypeNe_symm_of_ne hab, hf_some]
        have he_b : (g (f (x, y))) b = y := by
          dsimp [g]
          rw [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]
          simp [e, hf_none]
        change ca + g (f (x, y)) a = cb + g (f (x, y)) b ↔ _
        rw [he_a, he_b]
        constructor <;> intro h <;> linarith
      rw [hsec, measure_singleton]
      rfl
  · exact measurableSet_eq_fun
      (measurable_const.add (measurable_pi_apply a))
      (measurable_const.add (measurable_pi_apply b))

/- A fixed list order supplies a measurable tie-breaking version of argmax. -/
noncomputable def lexMax {Ω ι : Type*} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] (F : Ω → ι → ℝ) (ω : Ω) : ι :=
  (List.argmax (F ω) Finset.univ.toList).get (by
    rw [Option.isSome_iff_ne_none, Ne, List.argmax_eq_none]
    simpa using (Finset.univ_nonempty : (Finset.univ : Finset ι).Nonempty).ne_empty)

lemma lexMax_eq_iff {Ω ι : Type*} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] (F : Ω → ι → ℝ) (ω : Ω) (a : ι) :
    lexMax F ω = a ↔ List.argmax (F ω) Finset.univ.toList = some a := by
  unfold lexMax
  let hsome : (List.argmax (F ω) Finset.univ.toList).isSome := by
    rw [Option.isSome_iff_ne_none, Ne, List.argmax_eq_none]
    simpa using (Finset.univ_nonempty : (Finset.univ : Finset ι).Nonempty).ne_empty
  constructor
  · intro h
    exact (Option.some_get hsome).symm.trans (congrArg some h)
  · intro h
    exact Option.get_of_eq_some hsome h

lemma measurable_lexMax {Ω ι : Type*} [MeasurableSpace Ω]
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (F : Ω → ι → ℝ) (hF : ∀ a, Measurable fun ω => F ω a) :
    Measurable (lexMax F) := by
  have hlevel (a : ι) : MeasurableSet {ω | lexMax F ω = a} := by
    have hchar : {ω | lexMax F ω = a} =
        {ω | (∀ b, F ω b ≤ F ω a) ∧
          ∀ b, F ω a ≤ F ω b →
            List.idxOf a Finset.univ.toList ≤ List.idxOf b Finset.univ.toList} := by
      ext ω
      simp only [Set.mem_ofPred_eq]
      rw [lexMax_eq_iff, List.argmax_eq_some_iff]
      simp
    rw [hchar]
    have hleft₀ := MeasurableSet.iInter fun b => measurableSet_le (hF b) (hF a)
    have heqleft : (⋂ b, {ω | F ω b ≤ F ω a}) = {ω | ∀ b, F ω b ≤ F ω a} := by
      ext ω
      simp
    have hleft : MeasurableSet {ω | ∀ b, F ω b ≤ F ω a} := by
      rw [← heqleft]
      exact hleft₀
    have hright₀ := MeasurableSet.iInter fun b =>
      (measurableSet_le (hF a) (hF b)).imp
        (MeasurableSet.const (List.idxOf a Finset.univ.toList ≤
          List.idxOf b Finset.univ.toList))
    have heqright : (⋂ b, {ω | F ω a ≤ F ω b →
        List.idxOf a Finset.univ.toList ≤ List.idxOf b Finset.univ.toList}) =
        {ω | ∀ b, F ω a ≤ F ω b →
          List.idxOf a Finset.univ.toList ≤ List.idxOf b Finset.univ.toList} := by
      ext ω
      simp
    have hright : MeasurableSet {ω | ∀ b, F ω a ≤ F ω b →
        List.idxOf a Finset.univ.toList ≤ List.idxOf b Finset.univ.toList} := by
      rw [← heqright]
      exact hright₀
    change MeasurableSet ({ω | ∀ b, F ω b ≤ F ω a} ∩
      {ω | ∀ b, F ω a ≤ F ω b →
        List.idxOf a Finset.univ.toList ≤ List.idxOf b Finset.univ.toList})
    exact hleft.inter hright
  apply measurable_to_countable
  intro ω
  exact hlevel (lexMax F ω)

lemma lexMax_max {Ω ι : Type*} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] (F : Ω → ι → ℝ) (ω : Ω) (a : ι) :
    F ω a ≤ F ω (lexMax F ω) := by
  have hmem : lexMax F ω ∈ List.argmax (F ω) Finset.univ.toList := by
    unfold lexMax
    exact Option.get_mem _
  exact List.le_of_mem_argmax (by simp) hmem

noncomputable def raceValue {p : α × β → ℝ} (D : SeedSetup p)
    (z : α × β) (ε : D.L.ι → ℝ) (a : D.L.ι) : ℝ :=
  Real.log (D.post a z) + ε a

noncomputable def lexWinner {p : α × β → ℝ} (D : SeedSetup p)
    (ε : D.L.ι → ℝ) (z : α × β) : D.L.ι :=
  lexMax (fun ε a => raceValue D z ε a) ε

lemma winner_max {p : α × β → ℝ} (D : SeedSetup p)
    (ε : D.L.ι → ℝ) (z : α × β) (a : D.L.ι) :
    raceValue D z ε a ≤ raceValue D z ε (winner D ε z) := by
  exact Classical.choose_spec
    (Finite.exists_max fun a => Real.log (D.post a z) + ε a) a

lemma winner_eq_lexWinner_of_noTie {p : α × β → ℝ}
    (D : SeedSetup p) (ε : D.L.ι → ℝ) (z : α × β)
    (htie : ∀ a b, a ≠ b → raceValue D z ε a ≠ raceValue D z ε b) :
    winner D ε z = lexWinner D ε z := by
  have hleft := lexMax_max (fun ε a => raceValue D z ε a) ε (winner D ε z)
  have hright := winner_max D ε z (lexWinner D ε z)
  have hvalue :
      raceValue D z ε (winner D ε z) = raceValue D z ε (lexWinner D ε z) :=
    le_antisymm hleft hright
  by_contra hne
  exact htie _ _ hne hvalue

lemma seed_tie_null {p : α × β → ℝ} (D : SeedSetup p)
    (z : α × β) (a b : D.L.ι) (hab : a ≠ b) :
    seedLaw D.L.ι {ε | raceValue D z ε a = raceValue D z ε b} = 0 := by
  rw [seedLaw_eq_pi_gumbel1]
  simpa [raceValue] using pi_affine_tie_null gumbel1 a b hab
    (Real.log (D.post a z)) (Real.log (D.post b z))

lemma ae_forall_fintype {Ω κ : Type*} [Finite κ]
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} {R : κ → Ω → Prop}
    (hR : ∀ k, ∀ᵐ ω ∂P, R k ω) : ∀ᵐ ω ∂P, ∀ k, R k ω := by
  have h := (Filter.eventually_all_finite (I := (Set.univ : Set κ)) Set.finite_univ).2
    (fun k _ => hR k)
  simpa using h

lemma ae_no_race_ties {p : α × β → ℝ} (D : SeedSetup p) :
    ∀ᵐ ε ∂(seedLaw D.L.ι), ∀ z a b, a ≠ b →
      raceValue D z ε a ≠ raceValue D z ε b := by
  have hpair (z : α × β) (a b : D.L.ι) :
      ∀ᵐ ε ∂(seedLaw D.L.ι), a ≠ b →
        raceValue D z ε a ≠ raceValue D z ε b := by
    by_cases hab : a = b
    · exact Filter.Eventually.of_forall fun _ hne => (hne hab).elim
    · have hae := measure_eq_zero_iff_ae_notMem.mp (seed_tie_null D z a b hab)
      filter_upwards [hae] with ε hε
      intro _
      simpa only [Set.mem_ofPred_eq] using hε
  exact ae_forall_fintype fun z => ae_forall_fintype fun a =>
    ae_forall_fintype fun b => hpair z a b

lemma winner_ae_eq_lexWinner {p : α × β → ℝ} (D : SeedSetup p) :
    (fun ε => winner D ε) =ᵐ[seedLaw D.L.ι] fun ε => lexWinner D ε := by
  filter_upwards [ae_no_race_ties D] with ε hε
  funext z
  exact winner_eq_lexWinner_of_noTie D ε z (hε z)

private noncomputable def codedJoint {p : α × β → ℝ} (D : SeedSetup p)
    (A : α × β → D.L.ι) : D.L.ι × (α × β) → ℝ :=
  fun q => if A q.2 = q.1 then p q.2 else 0

private noncomputable def codedScore {p : α × β → ℝ} (D : SeedSetup p)
    (A : α × β → D.L.ι) : ℝ :=
  condMI (fun q => q.2.1) (fun q => q.2.2) (fun q => q.1) (codedJoint D A)
    + condMI (fun q => q.1) (fun q => q.2.1) (fun q => q.2.2) (codedJoint D A)
    + condMI (fun q => q.1) (fun q => q.2.2) (fun q => q.2.1) (codedJoint D A)

private lemma winner_score_eq_codedScore {p : α × β → ℝ} (D : SeedSetup p)
    (ε : D.L.ι → ℝ) :
    (winnerLatent D ε).score = codedScore D (winner D ε) := by
  have hjoint : (winnerLatent D ε).joint = codedJoint D (winner D ε) := by
    funext q
    unfold Latent.joint codedJoint
    simpa only [winnerLatent] using cellMass_mul_cellLaw D ε q.1 q.2
  unfold Latent.score codedScore
  rw [hjoint]
  rfl

/-! ### Conditional mutual information against a continuous variable

When `Z` and the conditioning variable are finite and only the observed
variable `W` is continuous, `I(W;Z ∣ C)` is a weighted sum of KL divergences
between measures on the observation space. -/

/-- `I(W ; Z ∣ C)` in **bits**, for finite `Z`, finite `C`, and `W` valued in an
arbitrary measurable space:
`∑_{z,c} P(z,c) · D( Law(W ∣ Z=z, C=c) ‖ Law(W ∣ C=c) )`.

`klDiv` is `ℝ≥0∞`-valued and in nats, hence the `toReal` and the `/ log 2`.
Statements using this carry finiteness hypotheses on the divergences;
`klDiv_ne_top_iff` is the relevant Mathlib lemma.

This is conditional mutual information **only** when `lawC c` is instantiated
with the true conditional marginal `∑_z P(z∣c) · law z c`; golden-formula
steps must be stated against that mixture (see `stoch_to_det/Race.lean`). -/
noncomputable def condMIcts {Ω : Type*} [MeasurableSpace Ω] {ζ γ : Type*}
    [Fintype ζ] [Fintype γ]
    (P : ζ → γ → ℝ) (law : ζ → γ → Measure Ω) (lawC : γ → Measure Ω) : ℝ :=
  (∑ c, ∑ z, P z c * (klDiv (law z c) (lawC c)).toReal) / Real.log 2

/-! ### The averaged defect, and the export to §12 -/

section Average

variable {p : α × β → ℝ} (D : SeedSetup p)

/-- The winner score is `seedLaw`-integrable: it is bounded (entropies
on fixed finite alphabets) and a.e. equal to a measurable function of
the seed (ties are null; off ties the winner is locally constant). -/
theorem integrable_winnerScore :
    Integrable (fun ε => (winnerLatent D ε).score) (seedLaw D.L.ι) := by
  letI : MeasurableSpace D.L.ι := ⊤
  have hlex (z : α × β) : Measurable (fun ε => lexWinner D ε z) := by
    unfold lexWinner
    apply measurable_lexMax
    intro a
    change Measurable (fun ε : D.L.ι → ℝ => Real.log (D.post a z) + ε a)
    exact measurable_const.add (measurable_pi_apply a)
  have hlexCode : Measurable (fun ε => lexWinner D ε) :=
    measurable_pi_lambda _ hlex
  have hcoded : Measurable (codedScore D) := measurable_of_finite _
  have hversion : Measurable (fun ε => codedScore D (lexWinner D ε)) :=
    hcoded.comp hlexCode
  have hscoreAE :
      (fun ε => (winnerLatent D ε).score) =ᵐ[seedLaw D.L.ι]
        fun ε => codedScore D (lexWinner D ε) := by
    filter_upwards [winner_ae_eq_lexWinner D] with ε hε
    rw [winner_score_eq_codedScore D ε, hε]
  have hstrong :
      AEStronglyMeasurable (fun ε => (winnerLatent D ε).score) (seedLaw D.L.ι) :=
    hversion.aestronglyMeasurable.congr hscoreAE.symm
  let C := ∑ A : α × β → D.L.ι, ‖codedScore D A‖
  apply MeasureTheory.Integrable.of_bound hstrong C
  filter_upwards [] with ε
  rw [winner_score_eq_codedScore D ε]
  exact Finset.single_le_sum (fun A _ => norm_nonneg (codedScore D A))
    (Finset.mem_univ (winner D ε))

/-- The **average complete-cell defect**
`𝒟_w(p,L) := E_ε ∑ₐ μₐ^ε G_w(rₐ^ε)`. -/
noncomputable def Dwdefect : ℝ :=
  ∫ ε, (∑ a, cellMass D ε a * Gdef (support p) D.w (cellLaw D ε a)) ∂(seedLaw D.L.ι)

/-- **Lemma 4.3**, averaged half:
`E_ε S_p(A_ε) = τ(p) + 𝒟_w(p,L)`. -/
theorem expected_score_eq (hint : Integrable (fun ε => (winnerLatent D ε).score) (seedLaw D.L.ι)) :
    ∫ ε, (winnerLatent D ε).score ∂(seedLaw D.L.ι) = tau p + Dwdefect D := by
  have hledger :
      (fun ε => ∑ a, cellMass D ε a * Gdef (support p) D.w (cellLaw D ε a)) =
        fun ε => (winnerLatent D ε).score - tau p := by
    funext ε
    exact per_seed_ledger D ε
  unfold Dwdefect
  rw [hledger, integral_sub hint (integrable_const (tau p))]
  simp

theorem Dwdefect_nonneg : 0 ≤ Dwdefect D := by
  unfold Dwdefect
  exact integral_nonneg fun ε => per_seed_ledger_nonneg D ε

/-- The averaging step of Corollary 4.4: some fixed seed does at least as well
as the average. This is where §12 uses the seed measure. -/
theorem exists_good_seed (c : ℝ)
    (hint : Integrable (fun ε => (winnerLatent D ε).score) (seedLaw D.L.ι))
    (h : ∫ ε, (winnerLatent D ε).score ∂(seedLaw D.L.ι) ≤ c) :
    ∃ ε : D.L.ι → ℝ, (winnerLatent D ε).score ≤ c := by
  by_contra hnone
  push_neg at hnone
  let f : (D.L.ι → ℝ) → ℝ := fun ε => (winnerLatent D ε).score - c
  have hfpos (ε : D.L.ι → ℝ) : 0 < f ε := sub_pos.mpr (hnone ε)
  have hfint : Integrable f (seedLaw D.L.ι) := hint.sub (integrable_const c)
  have hsupport : Function.support f = Set.univ := by
    ext ε
    simp only [Function.mem_support, Set.mem_univ, iff_true]
    exact (hfpos ε).ne'
  have hpos : 0 < ∫ ε, f ε ∂(seedLaw D.L.ι) := by
    rw [integral_pos_iff_support_of_nonneg (fun ε => (hfpos ε).le) hfint,
      hsupport]
    simp
  have heq :
      ∫ ε, f ε ∂(seedLaw D.L.ι) =
        (∫ ε, (winnerLatent D ε).score ∂(seedLaw D.L.ι)) - c := by
    dsimp [f]
    rw [integral_sub hint (integrable_const c)]
    simp
  rw [heq] at hpos
  linarith

/-- **Corollary 4.4**: a defect bound gives stoch_to_det on this law.
If `𝒟_w(p,L) ≤ C τ(p)` then `T(p) ≤ (C+1) τ(p)`. -/
theorem T_le_of_Dwdefect_le {C : ℝ}
    (hint : Integrable (fun ε => (winnerLatent D ε).score) (seedLaw D.L.ι))
    (h : Dwdefect D ≤ C * tau p) :
    T p ≤ (C + 1) * tau p := by
  have havg :
      ∫ ε, (winnerLatent D ε).score ∂(seedLaw D.L.ι) ≤
        (C + 1) * tau p := by
    calc
      ∫ ε, (winnerLatent D ε).score ∂(seedLaw D.L.ι) =
          tau p + Dwdefect D := expected_score_eq D hint
      _ ≤ tau p + C * tau p := add_le_add (le_refl _) h
      _ = (C + 1) * tau p := by ring
  obtain ⟨ε, hε⟩ := exists_good_seed D ((C + 1) * tau p) hint havg
  exact (T_le_score (winnerLatent D ε) (winnerLatent_isDet D ε)).trans hε

end Average

/-! ### §5. Posterior replicas — finite except Theorem 5.7

`L₀, L₁, L₂` are conditionally iid finite draws from the posterior given `Z`
, so the replica space is a finite product and Lemmas
5.2-5.6 below are finite statements. Only Theorem 5.7 involves `ε`.

The replica joint law on `ι × ι × ι × (α × β)` is
`P(ℓ₀,ℓ₁,ℓ₂,z) = p(z) t_{ℓ₀}(z) t_{ℓ₁}(z) t_{ℓ₂}(z)`; exchangeability of the
three coordinates is then a `Finset.sum` symmetry, not a probabilistic
argument. -/

section Replica

variable {p : α × β → ℝ} (D : SeedSetup p)

/-- The source-resolved replica law on `(ℓ₀, ℓ₁, ℓ₂, z)`. -/
noncomputable def replicaLaw : D.L.ι × D.L.ι × D.L.ι × (α × β) → ℝ :=
  fun u => p u.2.2.2 * D.post u.1 u.2.2.2 * D.post u.2.1 u.2.2.2 * D.post u.2.2.1 u.2.2.2

lemma post_nonneg (l : D.L.ι) (z : α × β) : 0 ≤ D.post l z := by
  exact div_nonneg
    (mul_nonneg (D.L.prior_isPMF.nonneg l) ((D.L.comp_isPMF l).nonneg z))
    (D.isPMF.nonneg z)

lemma sum_post_of_pos (z : α × β) (hz : 0 < p z) :
    ∑ l, D.post l z = 1 := by
  unfold SeedSetup.post
  calc
    ∑ l, D.L.prior l * D.L.comp l z / p z =
        (∑ l, D.L.prior l * D.L.comp l z) / p z := by
          rw [Finset.sum_div]
    _ = p z / p z := by rw [D.L.mixture z]
    _ = 1 := div_self hz.ne'

private lemma sum_replica_at (z : α × β) :
    (∑ l₀, ∑ l₁, ∑ l₂,
      p z * D.post l₀ z * D.post l₁ z * D.post l₂ z) = p z := by
  rcases (D.isPMF.nonneg z).eq_or_lt with hpz | hpz
  · have hpz' : p z = 0 := hpz.symm
    simp [hpz']
  · have hpost := sum_post_of_pos D z hpz
    calc
      (∑ l₀, ∑ l₁, ∑ l₂,
          p z * D.post l₀ z * D.post l₁ z * D.post l₂ z) =
          ∑ l₀, ∑ l₁,
            (p z * D.post l₀ z * D.post l₁ z) * (∑ l₂, D.post l₂ z) := by
              apply Finset.sum_congr rfl
              intro l₀ _
              apply Finset.sum_congr rfl
              intro l₁ _
              rw [Finset.mul_sum]
      _ = ∑ l₀, ∑ l₁, p z * D.post l₀ z * D.post l₁ z := by
            rw [hpost]
            simp
      _ = ∑ l₀, (p z * D.post l₀ z) * (∑ l₁, D.post l₁ z) := by
            apply Finset.sum_congr rfl
            intro l₀ _
            rw [Finset.mul_sum]
      _ = ∑ l₀, p z * D.post l₀ z := by rw [hpost]; simp
      _ = p z * (∑ l₀, D.post l₀ z) := by rw [Finset.mul_sum]
      _ = p z := by rw [hpost, mul_one]

lemma replicaLaw_isPMF : IsPMF (replicaLaw D) := by
  refine ⟨?_, ?_⟩
  · intro u
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (D.isPMF.nonneg u.2.2.2) (post_nonneg D u.1 u.2.2.2))
        (post_nonneg D u.2.1 u.2.2.2))
      (post_nonneg D u.2.2.1 u.2.2.2)
  · unfold mass
    calc
      (∑ u, replicaLaw D u) =
          ∑ l₀, ∑ u : D.L.ι × D.L.ι × (α × β), replicaLaw D (l₀, u) := by
            rw [Fintype.sum_prod_type]
      _ = ∑ l₀, ∑ l₁, ∑ u : D.L.ι × (α × β), replicaLaw D (l₀, l₁, u) := by
            apply Finset.sum_congr rfl
            intro l₀ _
            rw [Fintype.sum_prod_type]
      _ = ∑ l₀, ∑ l₁, ∑ l₂, ∑ z, replicaLaw D (l₀, l₁, l₂, z) := by
            apply Finset.sum_congr rfl
            intro l₀ _
            apply Finset.sum_congr rfl
            intro l₁ _
            rw [Fintype.sum_prod_type]
      _ = ∑ l₀, ∑ l₁, ∑ z, ∑ l₂,
            p z * D.post l₀ z * D.post l₁ z * D.post l₂ z := by
              simp only [replicaLaw]
              apply Finset.sum_congr rfl
              intro l₀ _
              apply Finset.sum_congr rfl
              intro l₁ _
              exact Finset.sum_comm
      _ = ∑ l₀, ∑ z, ∑ l₁, ∑ l₂,
            p z * D.post l₀ z * D.post l₁ z * D.post l₂ z := by
              apply Finset.sum_congr rfl
              intro l₀ _
              exact Finset.sum_comm
      _ = ∑ z, ∑ l₀, ∑ l₁, ∑ l₂,
            p z * D.post l₀ z * D.post l₁ z * D.post l₂ z :=
              Finset.sum_comm
      _ = ∑ z, p z := by
            apply Finset.sum_congr rfl
            intro z _
            exact sum_replica_at D z
      _ = 1 := by simpa [mass] using D.isPMF.total

private lemma p_mul_post (l : D.L.ι) (z : α × β) :
    p z * D.post l z = D.L.prior l * D.L.comp l z := by
  unfold SeedSetup.post
  by_cases hpz : p z = 0
  · have hle : D.L.prior l * D.L.comp l z ≤
        ∑ v, D.L.prior v * D.L.comp v z := by
      simpa using (Finset.single_le_sum
        (s := (Finset.univ : Finset D.L.ι))
        (fun v _ => mul_nonneg (D.L.prior_isPMF.nonneg v) ((D.L.comp_isPMF v).nonneg z))
        (Finset.mem_univ l))
    rw [D.L.mixture z, hpz] at hle
    have hzero : D.L.prior l * D.L.comp l z = 0 :=
      le_antisymm hle
        (mul_nonneg (D.L.prior_isPMF.nonneg l) ((D.L.comp_isPMF l).nonneg z))
    simp [hpz, hzero]
  · field_simp

private lemma sum_replica_l₂ (l₀ l₁ : D.L.ι) (z : α × β) :
    (∑ l₂, replicaLaw D (l₀, l₁, l₂, z)) =
      p z * D.post l₀ z * D.post l₁ z := by
  by_cases hpz : p z = 0
  · simp [replicaLaw, hpz]
  · have hpost := sum_post_of_pos D z
      (lt_of_le_of_ne (D.isPMF.nonneg z) (Ne.symm hpz))
    change (∑ l₂, p z * D.post l₀ z * D.post l₁ z * D.post l₂ z) =
      p z * D.post l₀ z * D.post l₁ z
    rw [← Finset.mul_sum, hpost, mul_one]

private lemma sum_replica_domain
    (F : D.L.ι × D.L.ι × D.L.ι × (α × β) → ℝ) :
    (∑ u, F u) = ∑ l₀, ∑ l₁, ∑ l₂, ∑ z, F (l₀, l₁, l₂, z) := by
  calc
    (∑ u, F u) = ∑ l₀, ∑ u : D.L.ι × D.L.ι × (α × β), F (l₀, u) := by
      rw [Fintype.sum_prod_type]
    _ = ∑ l₀, ∑ l₁, ∑ u : D.L.ι × (α × β), F (l₀, l₁, u) := by
      apply Finset.sum_congr rfl
      intro l₀ _
      rw [Fintype.sum_prod_type]
    _ = ∑ l₀, ∑ l₁, ∑ l₂, ∑ z, F (l₀, l₁, l₂, z) := by
      apply Finset.sum_congr rfl
      intro l₀ _
      apply Finset.sum_congr rfl
      intro l₁ _
      rw [Fintype.sum_prod_type]

private lemma comp_eq_zero_of_p_eq_zero (l : D.L.ι) (z : α × β)
    (hpz : p z = 0) : D.L.comp l z = 0 := by
  have hprod := p_mul_post D l z
  have hprod0 : D.L.prior l * D.L.comp l z = 0 := by
    calc
      D.L.prior l * D.L.comp l z = p z * D.post l z := hprod.symm
      _ = 0 := by rw [hpz]; simp
  have hprior : D.L.prior l ≠ 0 := (D.prior_pos l).ne'
  exact (mul_eq_zero.mp hprod0).resolve_left hprior

private lemma sum_comp_mul_post (l₀ : D.L.ι) (z : α × β) :
    (∑ l₁, D.L.comp l₀ z * D.post l₁ z) = D.L.comp l₀ z := by
  by_cases hpz : p z = 0
  · simp [comp_eq_zero_of_p_eq_zero D l₀ z hpz]
  · rw [← Finset.mul_sum, sum_post_of_pos D z
      (lt_of_le_of_ne (D.isPMF.nonneg z) (Ne.symm hpz)), mul_one]

noncomputable def resamplePrior (l₀ l₁ : D.L.ι) : ℝ :=
  ∑ z, D.L.comp l₀ z * D.post l₁ z

private noncomputable def resampleComp (l₀ l₁ : D.L.ι) (z : α × β) : ℝ :=
  if resamplePrior D l₀ l₁ = 0 then D.L.comp l₀ z
  else D.L.comp l₀ z * D.post l₁ z / resamplePrior D l₀ l₁

private lemma resamplePrior_nonneg (l₀ l₁ : D.L.ι) :
    0 ≤ resamplePrior D l₀ l₁ := by
  exact Finset.sum_nonneg fun z _ =>
    mul_nonneg ((D.L.comp_isPMF l₀).nonneg z) (post_nonneg D l₁ z)

private lemma sum_resamplePrior (l₀ : D.L.ι) :
    ∑ l₁, resamplePrior D l₀ l₁ = 1 := by
  unfold resamplePrior
  calc
    (∑ l₁, ∑ z, D.L.comp l₀ z * D.post l₁ z) =
        ∑ z, ∑ l₁, D.L.comp l₀ z * D.post l₁ z := Finset.sum_comm
    _ = ∑ z, D.L.comp l₀ z := by
      apply Finset.sum_congr rfl
      intro z _
      exact sum_comp_mul_post D l₀ z
    _ = 1 := by simpa [mass] using (D.L.comp_isPMF l₀).total

private lemma resamplePrior_mul_resampleComp (l₀ l₁ : D.L.ι) (z : α × β) :
    resamplePrior D l₀ l₁ * resampleComp D l₀ l₁ z =
      D.L.comp l₀ z * D.post l₁ z := by
  by_cases hprior : resamplePrior D l₀ l₁ = 0
  · have hle : D.L.comp l₀ z * D.post l₁ z ≤ resamplePrior D l₀ l₁ := by
      unfold resamplePrior
      exact Finset.single_le_sum
        (fun z _ => mul_nonneg ((D.L.comp_isPMF l₀).nonneg z) (post_nonneg D l₁ z))
        (by simp)
    rw [hprior] at hle
    have hterm : D.L.comp l₀ z * D.post l₁ z = 0 :=
      le_antisymm hle
        (mul_nonneg ((D.L.comp_isPMF l₀).nonneg z) (post_nonneg D l₁ z))
    simp [resampleComp, hprior, hterm]
  · simp only [resampleComp, hprior, if_false]
    field_simp

private lemma resampleComp_isPMF (l₀ l₁ : D.L.ι) :
    IsPMF (resampleComp D l₀ l₁) := by
  by_cases hprior : resamplePrior D l₀ l₁ = 0
  · have hcomp : resampleComp D l₀ l₁ = D.L.comp l₀ := by
      funext z
      simp [resampleComp, hprior]
    rw [hcomp]
    exact D.L.comp_isPMF l₀
  · have hprior_nonneg := resamplePrior_nonneg D l₀ l₁
    refine ⟨?_, ?_⟩
    · intro z
      simp only [resampleComp, hprior, if_false]
      exact div_nonneg
        (mul_nonneg ((D.L.comp_isPMF l₀).nonneg z) (post_nonneg D l₁ z))
        hprior_nonneg
    · unfold mass
      simp only [resampleComp, hprior, if_false]
      calc
        (∑ z, D.L.comp l₀ z * D.post l₁ z / resamplePrior D l₀ l₁) =
            resamplePrior D l₀ l₁ / resamplePrior D l₀ l₁ := by
              simp only [div_eq_mul_inv, ← Finset.sum_mul]
              rfl
        _ = 1 := div_self hprior

private lemma resampleComp_supported (l₀ l₁ : D.L.ι) :
    Supported (support p) (resampleComp D l₀ l₁) := by
  have hcontact := D.contact l₀ (D.prior_pos l₀).ne'
  intro z hz
  have hz0 : D.L.comp l₀ z = 0 := hcontact.2.1 z hz
  simp [resampleComp, hz0]

private noncomputable def resampleLatent (l₀ : D.L.ι) : Latent (D.L.comp l₀) where
  ι := D.L.ι
  fin := D.L.fin
  dec := D.L.dec
  prior := resamplePrior D l₀
  comp := resampleComp D l₀
  prior_isPMF := ⟨resamplePrior_nonneg D l₀, sum_resamplePrior D l₀⟩
  comp_isPMF := resampleComp_isPMF D l₀
  mixture := by
    intro z
    simp_rw [resamplePrior_mul_resampleComp D l₀]
    exact sum_comp_mul_post D l₀ z

private lemma resampleLatent_joint (l₀ : D.L.ι) (v : D.L.ι × (α × β)) :
    (resampleLatent D l₀).joint v = D.L.comp l₀ v.2 * D.post v.1 v.2 := by
  change resamplePrior D l₀ v.1 * resampleComp D l₀ v.1 v.2 = _
  exact resamplePrior_mul_resampleComp D l₀ v.1 v.2

private lemma resample_MI_ineq (l₀ : D.L.ι) :
    2 * MI (fun v : D.L.ι × (α × β) => v.1) (fun v => v.2.1)
          (resampleLatent D l₀).joint
      + 2 * MI (fun v : D.L.ι × (α × β) => v.1) (fun v => v.2.2)
          (resampleLatent D l₀).joint
      ≤ 3 * MI (fun v : D.L.ι × (α × β) => v.1) (fun v => v.2)
          (resampleLatent D l₀).joint := by
  let V := resampleLatent D l₀
  have hcontact := D.contact l₀ (D.prior_pos l₀).ne'
  have hbase := (Gdef_eq_zero_iff D.feasible hcontact.1 hcontact.2.1).2 hcontact
  have hfusion := Gdef_fusion D.feasible.1 hcontact.1 hcontact.2.1 V
  have hsum : 0 ≤ ∑ b, V.prior b * Gdef (support p) D.w (V.comp b) := by
    apply Finset.sum_nonneg
    intro b _
    apply mul_nonneg (V.prior_isPMF.nonneg b)
    apply Gdef_nonneg D.feasible (V.comp_isPMF b)
    change Supported (support p) (resampleComp D l₀ b)
    exact resampleComp_supported D l₀ b
  rw [hbase, sub_zero] at hfusion
  dsimp only [V] at hfusion hsum ⊢
  rw [hfusion] at hsum
  change 0 ≤
    3 * MI (fun v : D.L.ι × (α × β) => v.1) (fun v => v.2)
        (resampleLatent D l₀).joint
      - 2 * MI (fun v : D.L.ι × (α × β) => v.1) (fun v => v.2.1)
        (resampleLatent D l₀).joint
      - 2 * MI (fun v : D.L.ι × (α × β) => v.1) (fun v => v.2.2)
        (resampleLatent D l₀).joint at hsum
  linarith

private lemma condMI_eq_sum_MI_fibers
    {A Γ Δ K : Type*} [Fintype A] [Fintype Γ] [Fintype Δ] [Fintype K]
    [DecidableEq Γ] [DecidableEq Δ] [DecidableEq K]
    {m : A → ℝ} (hm : IsPMF m) (f : A → Γ) (g : A → Δ) (h : A → K) :
    condMI f g h m = ∑ k, MI f g (fun a => if h a = k then m a else 0) := by
  let mh : K → A → ℝ := fun k a => if h a = k then m a else 0
  have hF := Hvar_pair_eq_sum_fibers hm f h
  have hG := Hvar_pair_eq_sum_fibers hm g h
  have hFG := Hvar_pair_eq_sum_fibers hm (fun a => (f a, g a)) h
  change Hvar (fun a => (f a, h a)) m = Hvar h m + ∑ k, H (push f (mh k)) at hF
  change Hvar (fun a => (g a, h a)) m = Hvar h m + ∑ k, H (push g (mh k)) at hG
  change Hvar (fun a => ((f a, g a), h a)) m = Hvar h m +
    ∑ k, H (push (fun a => (f a, g a)) (mh k)) at hFG
  have hAssoc : Hvar (fun a => (f a, g a, h a)) m =
      Hvar (fun a => ((f a, g a), h a)) m := by
    simpa using Hvar_equiv hm (fun a => ((f a, g a), h a))
      (Equiv.prodAssoc Γ Δ K)
  unfold condMI
  rw [hF, hG, hAssoc, hFG]
  simp only [MI, Hvar, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  ring

private lemma push_id_local {A : Type*} [Fintype A] [DecidableEq A] (m : A → ℝ) :
    push (fun a => a) m = m := by
  funext a
  unfold push
  apply Finset.sum_eq_single a
  · intro b hb hba
    exact (hba (Finset.mem_filter.mp hb).2).elim
  · intro ha
    exact (ha (by simp)).elim

private lemma MI_eq_of_pair_push_eq
    {A A' Γ Δ : Type*} [Fintype A] [Fintype A'] [Fintype Γ] [Fintype Δ]
    [DecidableEq Γ] [DecidableEq Δ]
    (m : A → ℝ) (n : A' → ℝ) (f : A → Γ) (g : A → Δ)
    (f' : A' → Γ) (g' : A' → Δ)
    (hpair : push (fun a => (f a, g a)) m = push (fun a => (f' a, g' a)) n) :
    MI f g m = MI f' g' n := by
  have hf : push f m = push f' n := by
    calc
      push f m = push Prod.fst (push (fun a => (f a, g a)) m) := by
        symm
        simpa [Function.comp_def] using
          (push_push (fun a => (f a, g a)) Prod.fst m)
      _ = push Prod.fst (push (fun a => (f' a, g' a)) n) := by rw [hpair]
      _ = push f' n := by
        simpa [Function.comp_def] using
          (push_push (fun a => (f' a, g' a)) Prod.fst n)
  have hg : push g m = push g' n := by
    calc
      push g m = push Prod.snd (push (fun a => (f a, g a)) m) := by
        symm
        simpa [Function.comp_def] using
          (push_push (fun a => (f a, g a)) Prod.snd m)
      _ = push Prod.snd (push (fun a => (f' a, g' a)) n) := by rw [hpair]
      _ = push g' n := by
        simpa [Function.comp_def] using
          (push_push (fun a => (f' a, g' a)) Prod.snd n)
  unfold MI Hvar
  rw [hf, hg, hpair]

private noncomputable def replicaFiber (l₀ : D.L.ι) :
    D.L.ι × D.L.ι × D.L.ι × (α × β) → ℝ :=
  fun u => if u.1 = l₀ then replicaLaw D u else 0

private lemma push_replicaFiber_pair (l₀ : D.L.ι) :
    push (fun u : D.L.ι × D.L.ι × D.L.ι × (α × β) =>
      (u.2.1, u.2.2.2)) (replicaFiber D l₀) =
        fun v : D.L.ι × (α × β) =>
          D.L.prior l₀ * (D.L.comp l₀ v.2 * D.post v.1 v.2) := by
  funext v
  rcases v with ⟨l₁, z⟩
  unfold push replicaFiber
  rw [Finset.sum_filter, sum_replica_domain D]
  simp only [Prod.mk.injEq]
  have hite (a b c : D.L.ι) (z' : α × β) :
      (if b = l₁ ∧ z' = z then if a = l₀ then replicaLaw D (a, b, c, z') else 0 else 0) =
        if a = l₀ then if b = l₁ then if z' = z then replicaLaw D (a, b, c, z') else 0 else 0 else 0 := by
    by_cases ha : a = l₀ <;> by_cases hb : b = l₁ <;> by_cases hz : z' = z <;>
      simp [ha, hb, hz]
  simp_rw [hite]
  simp
  rw [sum_replica_l₂ D l₀ l₁ z, p_mul_post D l₀ z]
  ring

private lemma MI_replicaFiber_eq_smul
    {Γ : Type*} [Fintype Γ] [DecidableEq Γ]
    (l₀ : D.L.ι) (g : α × β → Γ) :
    MI (fun u : D.L.ι × D.L.ι × D.L.ι × (α × β) => u.2.1)
        (fun u => g u.2.2.2) (replicaFiber D l₀) =
      D.L.prior l₀ *
        MI (fun v : D.L.ι × (α × β) => v.1) (fun v => g v.2)
          (resampleLatent D l₀).joint := by
  let n : D.L.ι × (α × β) → ℝ := fun v =>
    D.L.prior l₀ * (D.L.comp l₀ v.2 * D.post v.1 v.2)
  let base : D.L.ι × D.L.ι × D.L.ι × (α × β) →
      D.L.ι × (α × β) := fun u => (u.2.1, u.2.2.2)
  let k : D.L.ι × (α × β) → D.L.ι × Γ := fun v => (v.1, g v.2)
  have hpair :
      push (fun u : D.L.ι × D.L.ι × D.L.ι × (α × β) =>
        (u.2.1, g u.2.2.2)) (replicaFiber D l₀) =
        push (fun v : D.L.ι × (α × β) => (v.1, g v.2)) n := by
    calc
      push (fun u : D.L.ι × D.L.ι × D.L.ι × (α × β) =>
          (u.2.1, g u.2.2.2)) (replicaFiber D l₀) =
          push k (push base (replicaFiber D l₀)) := by
            symm
            simpa [base, k, Function.comp_def] using
              (push_push base k (replicaFiber D l₀))
      _ = push k n := by rw [push_replicaFiber_pair D l₀]
      _ = push (fun v : D.L.ι × (α × β) => (v.1, g v.2)) n := rfl
  have hMI := MI_eq_of_pair_push_eq (replicaFiber D l₀) n
    (fun u : D.L.ι × D.L.ι × D.L.ι × (α × β) => u.2.1)
    (fun u => g u.2.2.2) (fun v : D.L.ι × (α × β) => v.1)
    (fun v => g v.2) hpair
  have hscale := MI_smul (resampleLatent D l₀).joint_isPMF.isFinMeas
    (fun v => v.1) (fun v => g v.2) (D.L.prior_isPMF.nonneg l₀)
  change MI (fun v : D.L.ι × (α × β) => v.1) (fun v => g v.2)
      (fun v => D.L.prior l₀ * (resampleLatent D l₀).joint v) =
    D.L.prior l₀ *
      MI (fun v : D.L.ι × (α × β) => v.1) (fun v => g v.2)
        (resampleLatent D l₀).joint at hscale
  have hn : (fun v : D.L.ι × (α × β) =>
      D.L.prior l₀ * (resampleLatent D l₀).joint v) = n := by
    funext v
    rw [resampleLatent_joint D l₀ v]
  rw [hn] at hscale
  exact hMI.trans hscale

private lemma replica_cond_resampling :
    2 * condMI (fun u => u.2.1) (fun u => u.2.2.2.1) (fun u => u.1) (replicaLaw D)
      + 2 * condMI (fun u => u.2.1) (fun u => u.2.2.2.2) (fun u => u.1) (replicaLaw D)
      ≤ 3 * condMI (fun u => u.2.1) (fun u => u.2.2.2) (fun u => u.1) (replicaLaw D) := by
  have hX := condMI_eq_sum_MI_fibers (replicaLaw_isPMF D)
    (fun u => u.2.1) (fun u => u.2.2.2.1) (fun u => u.1)
  have hY := condMI_eq_sum_MI_fibers (replicaLaw_isPMF D)
    (fun u => u.2.1) (fun u => u.2.2.2.2) (fun u => u.1)
  have hZ := condMI_eq_sum_MI_fibers (replicaLaw_isPMF D)
    (fun u => u.2.1) (fun u => u.2.2.2) (fun u => u.1)
  change condMI (fun u => u.2.1) (fun u => u.2.2.2.1) (fun u => u.1) (replicaLaw D) =
      ∑ l₀, MI (fun u => u.2.1) (fun u => u.2.2.2.1) (replicaFiber D l₀) at hX
  change condMI (fun u => u.2.1) (fun u => u.2.2.2.2) (fun u => u.1) (replicaLaw D) =
      ∑ l₀, MI (fun u => u.2.1) (fun u => u.2.2.2.2) (replicaFiber D l₀) at hY
  change condMI (fun u => u.2.1) (fun u => u.2.2.2) (fun u => u.1) (replicaLaw D) =
      ∑ l₀, MI (fun u => u.2.1) (fun u => u.2.2.2) (replicaFiber D l₀) at hZ
  have hZfiber (l₀ : D.L.ι) :
      MI (fun u : D.L.ι × D.L.ι × D.L.ι × (α × β) => u.2.1)
          (fun u => u.2.2.2) (replicaFiber D l₀) =
        D.L.prior l₀ *
          MI (fun v : D.L.ι × (α × β) => v.1) (fun v => v.2)
            (resampleLatent D l₀).joint := by
    simpa only using MI_replicaFiber_eq_smul D l₀ (fun z : α × β => z)
  rw [hX, hY, hZ]
  simp_rw [MI_replicaFiber_eq_smul D]
  simp_rw [hZfiber]
  calc
    2 * (∑ l₀, D.L.prior l₀ *
        MI (fun v : D.L.ι × (α × β) => v.1) (fun v => v.2.1)
          (resampleLatent D l₀).joint)
      + 2 * (∑ l₀, D.L.prior l₀ *
        MI (fun v : D.L.ι × (α × β) => v.1) (fun v => v.2.2)
          (resampleLatent D l₀).joint) =
      ∑ l₀, D.L.prior l₀ *
        (2 * MI (fun v : D.L.ι × (α × β) => v.1) (fun v => v.2.1)
            (resampleLatent D l₀).joint
          + 2 * MI (fun v : D.L.ι × (α × β) => v.1) (fun v => v.2.2)
            (resampleLatent D l₀).joint) := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro l₀ _
        ring
    _ ≤ ∑ l₀, D.L.prior l₀ *
        (3 * MI (fun v : D.L.ι × (α × β) => v.1) (fun v => v.2)
          (resampleLatent D l₀).joint) := by
        apply Finset.sum_le_sum
        intro l₀ _
        exact mul_le_mul_of_nonneg_left (resample_MI_ineq D l₀)
          (D.L.prior_isPMF.nonneg l₀)
    _ = 3 * (∑ l₀, D.L.prior l₀ *
        MI (fun v : D.L.ι × (α × β) => v.1) (fun v => v.2)
          (resampleLatent D l₀).joint) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro l₀ _
        ring

private def replicaSwap₀₁ :
    (D.L.ι × D.L.ι × D.L.ι × (α × β)) ≃
      (D.L.ι × D.L.ι × D.L.ι × (α × β)) where
  toFun u := (u.2.1, u.1, u.2.2.1, u.2.2.2)
  invFun u := (u.2.1, u.1, u.2.2.1, u.2.2.2)
  left_inv := by rintro ⟨l₀, l₁, l₂, z⟩; rfl
  right_inv := by rintro ⟨l₀, l₁, l₂, z⟩; rfl

private lemma replicaLaw_swap₀₁ (u : D.L.ι × D.L.ι × D.L.ι × (α × β)) :
    replicaLaw D (replicaSwap₀₁ D u) = replicaLaw D u := by
  rcases u with ⟨l₀, l₁, l₂, z⟩
  change p z * D.post l₁ z * D.post l₀ z * D.post l₂ z =
    p z * D.post l₀ z * D.post l₁ z * D.post l₂ z
  ring

private lemma push_comp_equiv_eq_of_invariant
    {A Γ : Type*} [Fintype A] [Fintype Γ] [DecidableEq Γ]
    (e : A ≃ A) (m : A → ℝ) (hm : ∀ a, m (e a) = m a) (f : A → Γ) :
    push (f ∘ e) m = push f m := by
  funext c
  unfold push
  rw [Finset.sum_filter, Finset.sum_filter]
  calc
    (∑ a, if f (e a) = c then m a else 0) =
        ∑ a, if f (e a) = c then m (e a) else 0 := by
          apply Finset.sum_congr rfl
          intro a _
          rw [hm a]
    _ = ∑ a, if f a = c then m a else 0 :=
      e.sum_comp (fun a => if f a = c then m a else 0)

private lemma condMI_eq_of_triple_push_eq
    {A A' Γ Δ K : Type*} [Fintype A] [Fintype A'] [Fintype Γ] [Fintype Δ]
    [Fintype K] [DecidableEq Γ] [DecidableEq Δ] [DecidableEq K]
    (m : A → ℝ) (n : A' → ℝ) (f : A → Γ) (g : A → Δ) (h : A → K)
    (f' : A' → Γ) (g' : A' → Δ) (h' : A' → K)
    (htriple : push (fun a => (f a, g a, h a)) m =
      push (fun a => (f' a, g' a, h' a)) n) :
    condMI f g h m = condMI f' g' h' n := by
  let pfh : Γ × Δ × K → Γ × K := fun t => (t.1, t.2.2)
  let pgh : Γ × Δ × K → Δ × K := fun t => (t.2.1, t.2.2)
  let ph : Γ × Δ × K → K := fun t => t.2.2
  have hfh : push (fun a => (f a, h a)) m = push (fun a => (f' a, h' a)) n := by
    calc
      push (fun a => (f a, h a)) m =
          push pfh (push (fun a => (f a, g a, h a)) m) := by
            symm
            simpa [pfh, Function.comp_def] using
              (push_push (fun a => (f a, g a, h a)) pfh m)
      _ = push pfh (push (fun a => (f' a, g' a, h' a)) n) := by rw [htriple]
      _ = push (fun a => (f' a, h' a)) n := by
            simpa [pfh, Function.comp_def] using
              (push_push (fun a => (f' a, g' a, h' a)) pfh n)
  have hgh : push (fun a => (g a, h a)) m = push (fun a => (g' a, h' a)) n := by
    calc
      push (fun a => (g a, h a)) m =
          push pgh (push (fun a => (f a, g a, h a)) m) := by
            symm
            simpa [pgh, Function.comp_def] using
              (push_push (fun a => (f a, g a, h a)) pgh m)
      _ = push pgh (push (fun a => (f' a, g' a, h' a)) n) := by rw [htriple]
      _ = push (fun a => (g' a, h' a)) n := by
            simpa [pgh, Function.comp_def] using
              (push_push (fun a => (f' a, g' a, h' a)) pgh n)
  have hh : push h m = push h' n := by
    calc
      push h m = push ph (push (fun a => (f a, g a, h a)) m) := by
        symm
        simpa [ph, Function.comp_def] using
          (push_push (fun a => (f a, g a, h a)) ph m)
      _ = push ph (push (fun a => (f' a, g' a, h' a)) n) := by rw [htriple]
      _ = push h' n := by
        simpa [ph, Function.comp_def] using
          (push_push (fun a => (f' a, g' a, h' a)) ph n)
  unfold condMI Hvar
  rw [hfh, hgh, htriple, hh]

private lemma replica_condMI_swap :
    condMI (fun u => u.2.1) (fun u => u.2.2.2) (fun u => u.1) (replicaLaw D) =
      condMI (fun u => u.1) (fun u => u.2.2.2) (fun u => u.2.1) (replicaLaw D) := by
  let f : D.L.ι × D.L.ι × D.L.ι × (α × β) →
      D.L.ι × (α × β) × D.L.ι := fun u => (u.1, u.2.2.2, u.2.1)
  have htriple :
      push (fun u : D.L.ι × D.L.ι × D.L.ι × (α × β) =>
        (u.2.1, u.2.2.2, u.1)) (replicaLaw D) =
      push (fun u : D.L.ι × D.L.ι × D.L.ι × (α × β) =>
        (u.1, u.2.2.2, u.2.1)) (replicaLaw D) := by
    have h := push_comp_equiv_eq_of_invariant (replicaSwap₀₁ D) (replicaLaw D)
      (replicaLaw_swap₀₁ D) f
    simpa [f, replicaSwap₀₁, Function.comp_def] using h
  exact condMI_eq_of_triple_push_eq (replicaLaw D) (replicaLaw D)
    (fun u => u.2.1) (fun u => u.2.2.2) (fun u => u.1)
    (fun u => u.1) (fun u => u.2.2.2) (fun u => u.2.1) htriple

private lemma MI_iidProduct_zero
    {A : Type*} [Fintype A] [DecidableEq A] {t : A → ℝ} (ht : IsPMF t) :
    MI Prod.fst Prod.snd (fun u : A × A => t u.1 * t u.2) = 0 := by
  let q : A × A → ℝ := fun u => t u.1 * t u.2
  have ht_sum : ∑ a, t a = 1 := by simpa [mass] using ht.total
  have hq : IsPMF q := by
    constructor
    · intro u
      exact mul_nonneg (ht.nonneg u.1) (ht.nonneg u.2)
    · unfold mass q
      rw [Fintype.sum_prod_type]
      simp_rw [← Finset.mul_sum]
      rw [ht_sum]
      simp [ht_sum]
  have hfst : push Prod.fst q = t := by
    funext a
    unfold push
    rw [Finset.sum_filter, Fintype.sum_prod_type]
    simp [q, ← Finset.mul_sum, ht_sum]
  have hsnd : push Prod.snd q = t := by
    funext b
    unfold push
    rw [Finset.sum_filter, Fintype.sum_prod_type]
    simp [q, ← Finset.sum_mul, ht_sum]
  have hpair : push (fun u : A × A => (u.1, u.2)) q = q := by
    simpa only using push_id_local q
  have hfiber (b : A) : H (fun a => q (a, b)) = t b * H t := by
    have heq : (fun a => q (a, b)) = fun a => t b * t a := by
      funext a
      dsimp only [q]
      ring
    rw [heq]
    exact H_smul ht.isFinMeas (ht.nonneg b)
  have hqH := H_prod_eq_snd_add_fibers hq
  rw [hsnd] at hqH
  simp_rw [hfiber] at hqH
  rw [← Finset.sum_mul, ht_sum, one_mul] at hqH
  change MI Prod.fst Prod.snd q = 0
  unfold MI Hvar
  rw [hfst, hsnd, hpair, hqH]
  ring

private lemma MI_indepProduct_zero
    {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    {s : A → ℝ} {t : B → ℝ} (hs : IsPMF s) (ht : IsPMF t) :
    MI Prod.fst Prod.snd (fun u : A × B => s u.1 * t u.2) = 0 := by
  let q : A × B → ℝ := fun u => s u.1 * t u.2
  have hs_sum : ∑ a, s a = 1 := by simpa [mass] using hs.total
  have ht_sum : ∑ b, t b = 1 := by simpa [mass] using ht.total
  have hq : IsPMF q := by
    constructor
    · intro u
      exact mul_nonneg (hs.nonneg u.1) (ht.nonneg u.2)
    · unfold mass q
      rw [Fintype.sum_prod_type]
      simp_rw [← Finset.mul_sum]
      rw [ht_sum]
      simp [hs_sum]
  have hfst : push Prod.fst q = s := by
    funext a
    unfold push
    rw [Finset.sum_filter, Fintype.sum_prod_type]
    simp [q, ← Finset.mul_sum, ht_sum]
  have hsnd : push Prod.snd q = t := by
    funext b
    unfold push
    rw [Finset.sum_filter, Fintype.sum_prod_type]
    simp [q, ← Finset.sum_mul, hs_sum]
  have hpair : push (fun u : A × B => (u.1, u.2)) q = q := by
    simpa only using push_id_local q
  have hfiber (b : B) : H (fun a => q (a, b)) = t b * H s := by
    have heq : (fun a => q (a, b)) = fun a => t b * s a := by
      funext a
      dsimp only [q]
      ring
    rw [heq]
    exact H_smul hs.isFinMeas (ht.nonneg b)
  have hqH := H_prod_eq_snd_add_fibers hq
  rw [hsnd] at hqH
  simp_rw [hfiber] at hqH
  rw [← Finset.sum_mul, ht_sum, one_mul] at hqH
  change MI Prod.fst Prod.snd q = 0
  unfold MI Hvar
  rw [hfst, hsnd, hpair, hqH]
  ring

private noncomputable def replicaZFiber (z : α × β) :
    D.L.ι × D.L.ι × D.L.ι × (α × β) → ℝ :=
  fun u => if u.2.2.2 = z then replicaLaw D u else 0

private lemma push_replicaZFiber_pair (z : α × β) :
    push (fun u : D.L.ι × D.L.ι × D.L.ι × (α × β) =>
      (u.1, u.2.1)) (replicaZFiber D z) =
        fun v : D.L.ι × D.L.ι => p z * D.post v.1 z * D.post v.2 z := by
  funext v
  rcases v with ⟨l₀, l₁⟩
  unfold push replicaZFiber
  rw [Finset.sum_filter, sum_replica_domain D]
  simp only [Prod.mk.injEq]
  have hite (a b c : D.L.ι) (z' : α × β) :
      (if a = l₀ ∧ b = l₁ then if z' = z then replicaLaw D (a, b, c, z') else 0 else 0) =
        if a = l₀ then if b = l₁ then if z' = z then replicaLaw D (a, b, c, z') else 0 else 0 else 0 := by
    by_cases ha : a = l₀ <;> by_cases hb : b = l₁ <;> by_cases hz : z' = z <;>
      simp [ha, hb, hz]
  simp_rw [hite]
  simp
  exact sum_replica_l₂ D l₀ l₁ z

private lemma MI_replicaZFiber_zero (z : α × β) :
    MI (fun u : D.L.ι × D.L.ι × D.L.ι × (α × β) => u.1)
      (fun u => u.2.1) (replicaZFiber D z) = 0 := by
  let n : D.L.ι × D.L.ι → ℝ := fun v => p z * D.post v.1 z * D.post v.2 z
  have hpair :
      push (fun u : D.L.ι × D.L.ι × D.L.ι × (α × β) =>
        (u.1, u.2.1)) (replicaZFiber D z) =
        push (fun v : D.L.ι × D.L.ι => (v.1, v.2)) n := by
    rw [push_replicaZFiber_pair D z]
    symm
    simpa only using push_id_local n
  have hMI := MI_eq_of_pair_push_eq (replicaZFiber D z) n
    (fun u : D.L.ι × D.L.ι × D.L.ι × (α × β) => u.1)
    (fun u => u.2.1) (fun v : D.L.ι × D.L.ι => v.1) (fun v => v.2) hpair
  rw [hMI]
  by_cases hpz : p z = 0
  · simp [n, hpz, MI, Hvar, H, push, mass]
  · let t : D.L.ι → ℝ := fun l => D.post l z
    have ht : IsPMF t := by
      constructor
      · intro l
        exact post_nonneg D l z
      · simpa [mass, t] using sum_post_of_pos D z
          (lt_of_le_of_ne (D.isPMF.nonneg z) (Ne.symm hpz))
    let q : D.L.ι × D.L.ι → ℝ := fun v => t v.1 * t v.2
    have hq : IsPMF q := by
      constructor
      · intro v
        exact mul_nonneg (ht.nonneg v.1) (ht.nonneg v.2)
      · unfold mass q
        rw [Fintype.sum_prod_type]
        simp_rw [← Finset.mul_sum]
        have ht_sum : ∑ l, t l = 1 := by simpa [mass] using ht.total
        rw [ht_sum]
        simp [ht_sum]
    have hzero : MI Prod.fst Prod.snd q = 0 := MI_iidProduct_zero ht
    have hscale := MI_smul hq.isFinMeas Prod.fst Prod.snd (D.isPMF.nonneg z)
    have hn : n = fun v : D.L.ι × D.L.ι => p z * q v := by
      funext v
      simp [n, q, t]
      ring
    rw [hn, hscale, hzero, mul_zero]

private lemma replica_markov :
    condMI (fun u => u.1) (fun u => u.2.1) (fun u => u.2.2.2) (replicaLaw D) = 0 := by
  have h := condMI_eq_sum_MI_fibers (replicaLaw_isPMF D)
    (fun u => u.1) (fun u => u.2.1) (fun u => u.2.2.2)
  change condMI (fun u => u.1) (fun u => u.2.1) (fun u => u.2.2.2) (replicaLaw D) =
      ∑ z, MI (fun u => u.1) (fun u => u.2.1) (replicaZFiber D z) at h
  rw [h]
  exact Finset.sum_eq_zero fun z _ => MI_replicaZFiber_zero D z

private lemma push_replicaZFiber_triple (z : α × β) :
    push (fun u : D.L.ι × D.L.ι × D.L.ι × (α × β) =>
      ((u.1, u.2.1), u.2.2.1)) (replicaZFiber D z) =
        fun v : (D.L.ι × D.L.ι) × D.L.ι =>
          p z * (D.post v.1.1 z * D.post v.1.2 z) * D.post v.2 z := by
  funext v
  rcases v with ⟨⟨l₀, l₁⟩, l₂⟩
  unfold push replicaZFiber
  rw [Finset.sum_filter, sum_replica_domain D]
  simp only [Prod.mk.injEq]
  have hite (a b c : D.L.ι) (z' : α × β) :
      (if (a = l₀ ∧ b = l₁) ∧ c = l₂ then
          if z' = z then replicaLaw D (a, b, c, z') else 0 else 0) =
        if a = l₀ then if b = l₁ then if c = l₂ then
          if z' = z then replicaLaw D (a, b, c, z') else 0 else 0 else 0 else 0 := by
    by_cases ha : a = l₀ <;> by_cases hb : b = l₁ <;> by_cases hc : c = l₂ <;>
      by_cases hz : z' = z <;> simp [ha, hb, hc, hz]
  simp_rw [hite]
  simp
  change p z * D.post l₀ z * D.post l₁ z * D.post l₂ z =
    p z * (D.post l₀ z * D.post l₁ z) * D.post l₂ z
  ring

private lemma MI_replicaZFiber_triple_zero (z : α × β) :
    MI (fun u : D.L.ι × D.L.ι × D.L.ι × (α × β) => (u.1, u.2.1))
      (fun u => u.2.2.1) (replicaZFiber D z) = 0 := by
  let n : (D.L.ι × D.L.ι) × D.L.ι → ℝ := fun v =>
    p z * (D.post v.1.1 z * D.post v.1.2 z) * D.post v.2 z
  have hpair :
      push (fun u : D.L.ι × D.L.ι × D.L.ι × (α × β) =>
        ((u.1, u.2.1), u.2.2.1)) (replicaZFiber D z) =
        push (fun v : (D.L.ι × D.L.ι) × D.L.ι => (v.1, v.2)) n := by
    rw [push_replicaZFiber_triple D z]
    symm
    simpa only using push_id_local n
  have hMI := MI_eq_of_pair_push_eq (replicaZFiber D z) n
    (fun u : D.L.ι × D.L.ι × D.L.ι × (α × β) => (u.1, u.2.1))
    (fun u => u.2.2.1) (fun v : (D.L.ι × D.L.ι) × D.L.ι => v.1) (fun v => v.2) hpair
  rw [hMI]
  by_cases hpz : p z = 0
  · simp [n, hpz, MI, Hvar, H, push, mass]
  · let t : D.L.ι → ℝ := fun l => D.post l z
    have ht : IsPMF t := by
      constructor
      · intro l
        exact post_nonneg D l z
      · simpa [mass, t] using sum_post_of_pos D z
          (lt_of_le_of_ne (D.isPMF.nonneg z) (Ne.symm hpz))
    let s : D.L.ι × D.L.ι → ℝ := fun v => t v.1 * t v.2
    have hs : IsPMF s := by
      constructor
      · intro v
        exact mul_nonneg (ht.nonneg v.1) (ht.nonneg v.2)
      · unfold mass s
        rw [Fintype.sum_prod_type]
        simp_rw [← Finset.mul_sum]
        have ht_sum : ∑ l, t l = 1 := by simpa [mass] using ht.total
        rw [ht_sum]
        simp [ht_sum]
    let q : (D.L.ι × D.L.ι) × D.L.ι → ℝ := fun v => s v.1 * t v.2
    have hq : IsPMF q := by
      constructor
      · intro v
        exact mul_nonneg (hs.nonneg v.1) (ht.nonneg v.2)
      · unfold mass q
        rw [Fintype.sum_prod_type]
        simp_rw [← Finset.mul_sum]
        have ht_sum : ∑ l, t l = 1 := by simpa [mass] using ht.total
        rw [ht_sum]
        simpa [mass] using hs.total
    have hzero : MI Prod.fst Prod.snd q = 0 := MI_indepProduct_zero hs ht
    have hscale := MI_smul hq.isFinMeas Prod.fst Prod.snd (D.isPMF.nonneg z)
    have hn : n = fun v : (D.L.ι × D.L.ι) × D.L.ι => p z * q v := by
      funext v
      simp [n, q, s, t]
      ring
    rw [hn, hscale, hzero, mul_zero]

private lemma replica_triple_markov :
    condMI (fun u => (u.1, u.2.1)) (fun u => u.2.2.1) (fun u => u.2.2.2)
      (replicaLaw D) = 0 := by
  have h := condMI_eq_sum_MI_fibers (replicaLaw_isPMF D)
    (fun u => (u.1, u.2.1)) (fun u => u.2.2.1) (fun u => u.2.2.2)
  change condMI (fun u => (u.1, u.2.1)) (fun u => u.2.2.1) (fun u => u.2.2.2)
      (replicaLaw D) =
    ∑ z, MI (fun u => (u.1, u.2.1)) (fun u => u.2.2.1) (replicaZFiber D z) at h
  rw [h]
  exact Finset.sum_eq_zero fun z _ => MI_replicaZFiber_triple_zero D z

private lemma sum_replica_l₁_l₂ (l₀ : D.L.ι) (z : α × β) :
    (∑ l₁, ∑ l₂, replicaLaw D (l₀, l₁, l₂, z)) = D.L.joint (l₀, z) := by
  by_cases hpz : p z = 0
  · have hcomp := comp_eq_zero_of_p_eq_zero D l₀ z hpz
    simp [replicaLaw, hpz, Latent.joint, hcomp]
  · have hpost := sum_post_of_pos D z
      (lt_of_le_of_ne (D.isPMF.nonneg z) (Ne.symm hpz))
    calc
      (∑ l₁, ∑ l₂, replicaLaw D (l₀, l₁, l₂, z)) =
          ∑ l₁, p z * D.post l₀ z * D.post l₁ z := by
            apply Finset.sum_congr rfl
            intro l₁ _
            exact sum_replica_l₂ D l₀ l₁ z
      _ = (p z * D.post l₀ z) * (∑ l₁, D.post l₁ z) := by
            rw [Finset.mul_sum]
      _ = p z * D.post l₀ z := by rw [hpost, mul_one]
      _ = D.L.joint (l₀, z) := by
            rw [p_mul_post D l₀ z]
            rfl

private lemma push_replica_l₀z :
    push (fun u : D.L.ι × D.L.ι × D.L.ι × (α × β) =>
      (u.1, u.2.2.2)) (replicaLaw D) = D.L.joint := by
  funext v
  rcases v with ⟨l₀, z⟩
  unfold push
  rw [Finset.sum_filter, sum_replica_domain D]
  simp only [Prod.mk.injEq]
  have hite (a b c : D.L.ι) (z' : α × β) :
      (if a = l₀ ∧ z' = z then replicaLaw D (a, b, c, z') else 0) =
        if a = l₀ then if z' = z then replicaLaw D (a, b, c, z') else 0 else 0 := by
    by_cases ha : a = l₀ <;> by_cases hz : z' = z <;> simp [ha, hz]
  simp_rw [hite]
  simp
  exact sum_replica_l₁_l₂ D l₀ z

private lemma MI_replica_l₀_eq_joint
    {Γ : Type*} [Fintype Γ] [DecidableEq Γ] (g : α × β → Γ) :
    MI (fun u : D.L.ι × D.L.ι × D.L.ι × (α × β) => u.1)
        (fun u => g u.2.2.2) (replicaLaw D) =
      MI (fun v : D.L.ι × (α × β) => v.1) (fun v => g v.2) D.L.joint := by
  let base : D.L.ι × D.L.ι × D.L.ι × (α × β) →
      D.L.ι × (α × β) := fun u => (u.1, u.2.2.2)
  let k : D.L.ι × (α × β) → D.L.ι × Γ := fun v => (v.1, g v.2)
  have hpair :
      push (fun u : D.L.ι × D.L.ι × D.L.ι × (α × β) =>
        (u.1, g u.2.2.2)) (replicaLaw D) =
      push (fun v : D.L.ι × (α × β) => (v.1, g v.2)) D.L.joint := by
    calc
      push (fun u : D.L.ι × D.L.ι × D.L.ι × (α × β) =>
          (u.1, g u.2.2.2)) (replicaLaw D) = push k (push base (replicaLaw D)) := by
            symm
            simpa [base, k, Function.comp_def] using push_push base k (replicaLaw D)
      _ = push k D.L.joint := by rw [push_replica_l₀z D]
      _ = push (fun v : D.L.ι × (α × β) => (v.1, g v.2)) D.L.joint := rfl
  exact MI_eq_of_pair_push_eq (replicaLaw D) D.L.joint
    (fun u : D.L.ι × D.L.ι × D.L.ι × (α × β) => u.1)
    (fun u => g u.2.2.2) (fun v : D.L.ι × (α × β) => v.1)
    (fun v => g v.2) hpair

private lemma condMI_replica_l₀_eq_joint
    {Γ Δ : Type*} [Fintype Γ] [Fintype Δ] [DecidableEq Γ] [DecidableEq Δ]
    (g : α × β → Γ) (h : α × β → Δ) :
    condMI (fun u : D.L.ι × D.L.ι × D.L.ι × (α × β) => u.1)
        (fun u => g u.2.2.2) (fun u => h u.2.2.2) (replicaLaw D) =
      condMI (fun v : D.L.ι × (α × β) => v.1) (fun v => g v.2)
        (fun v => h v.2) D.L.joint := by
  let base : D.L.ι × D.L.ι × D.L.ι × (α × β) →
      D.L.ι × (α × β) := fun u => (u.1, u.2.2.2)
  let k : D.L.ι × (α × β) → D.L.ι × Γ × Δ :=
    fun v => (v.1, g v.2, h v.2)
  have htriple :
      push (fun u : D.L.ι × D.L.ι × D.L.ι × (α × β) =>
        (u.1, g u.2.2.2, h u.2.2.2)) (replicaLaw D) =
      push (fun v : D.L.ι × (α × β) => (v.1, g v.2, h v.2)) D.L.joint := by
    calc
      _ = push k (push base (replicaLaw D)) := by
        symm
        simpa [base, k, Function.comp_def] using push_push base k (replicaLaw D)
      _ = push k D.L.joint := by rw [push_replica_l₀z D]
      _ = _ := rfl
  exact condMI_eq_of_triple_push_eq (replicaLaw D) D.L.joint
    (fun u : D.L.ι × D.L.ι × D.L.ι × (α × β) => u.1)
    (fun u => g u.2.2.2) (fun u => h u.2.2.2)
    (fun v : D.L.ι × (α × β) => v.1) (fun v => g v.2) (fun v => h v.2) htriple

private lemma MI_equiv_left_local
    {A Γ Γ' Δ : Type*} [Fintype A] [Fintype Γ] [Fintype Γ'] [Fintype Δ]
    [DecidableEq Γ] [DecidableEq Γ'] [DecidableEq Δ]
    {m : A → ℝ} (hm : IsPMF m) (f : A → Γ) (e : Γ ≃ Γ') (g : A → Δ) :
    MI (fun a => e (f a)) g m = MI f g m := by
  have hf := Hvar_equiv hm f e
  have hfg := Hvar_equiv hm (fun a => (f a, g a))
    (Equiv.prodCongr e (Equiv.refl Δ))
  change Hvar (fun a => (e (f a), g a)) m = Hvar (fun a => (f a, g a)) m at hfg
  unfold MI
  rw [hf, hfg]

private lemma condMI_comm_local
    {A Γ Δ K : Type*} [Fintype A] [Fintype Γ] [Fintype Δ] [Fintype K]
    [DecidableEq Γ] [DecidableEq Δ] [DecidableEq K]
    {m : A → ℝ} (hm : IsPMF m) (f : A → Γ) (g : A → Δ) (h : A → K) :
    condMI f g h m = condMI g f h m := by
  let e : Γ × Δ × K ≃ Δ × Γ × K :=
    { toFun := fun t => (t.2.1, t.1, t.2.2)
      invFun := fun t => (t.2.1, t.1, t.2.2)
      left_inv := by rintro ⟨x, y, k⟩; rfl
      right_inv := by rintro ⟨y, x, k⟩; rfl }
  have htrip : Hvar (fun a => (g a, f a, h a)) m = Hvar (fun a => (f a, g a, h a)) m := by
    simpa [e] using Hvar_equiv hm (fun a => (f a, g a, h a)) e
  unfold condMI
  rw [htrip]
  ring

private lemma Bq_info_identity :
    D.Bq = 2 * MI (fun v : D.L.ι × (α × β) => v.1) (fun v => v.2) D.L.joint -
      MI (fun v : D.L.ι × (α × β) => v.1) (fun v => v.2.1) D.L.joint -
      MI (fun v : D.L.ι × (α × β) => v.1) (fun v => v.2.2) D.L.joint := by
  have hXY := MI_pair_left D.L.joint_isPMF (fun v => v.2.1) (fun v => v.2.2) (fun v => v.1)
  have hYX := MI_pair_left D.L.joint_isPMF (fun v => v.2.2) (fun v => v.2.1) (fun v => v.1)
  have hpairSwap :
      MI (fun v : D.L.ι × (α × β) => (v.2.2, v.2.1)) (fun v => v.1) D.L.joint =
        MI (fun v : D.L.ι × (α × β) => v.2) (fun v => v.1) D.L.joint := by
    have h := MI_equiv_left_local D.L.joint_isPMF
      (fun v : D.L.ι × (α × β) => v.2)
      (Equiv.prodComm α β) (fun v => v.1)
    change MI (fun v : D.L.ι × (α × β) => (v.2.2, v.2.1)) (fun v => v.1) D.L.joint =
      MI (fun v : D.L.ι × (α × β) => v.2) (fun v => v.1) D.L.joint at h
    exact h
  have hZcomm := MI_comm D.L.joint_isPMF
    (fun v : D.L.ι × (α × β) => v.2) (fun v => v.1)
  have hXcomm := MI_comm D.L.joint_isPMF
    (fun v : D.L.ι × (α × β) => v.2.1) (fun v => v.1)
  have hYcomm := MI_comm D.L.joint_isPMF
    (fun v : D.L.ι × (α × β) => v.2.2) (fun v => v.1)
  have hcX := condMI_comm_local D.L.joint_isPMF
    (fun v : D.L.ι × (α × β) => v.2.1) (fun v => v.1) (fun v => v.2.2)
  have hcY := condMI_comm_local D.L.joint_isPMF
    (fun v : D.L.ι × (α × β) => v.2.2) (fun v => v.1) (fun v => v.2.1)
  unfold SeedSetup.Bq
  change
    condMI (fun v => v.1) (fun v => v.2.1) (fun v => v.2.2) D.L.joint +
      condMI (fun v => v.1) (fun v => v.2.2) (fun v => v.2.1) D.L.joint = _
  rw [← hcX, ← hcY]
  rw [hpairSwap] at hYX
  rw [hZcomm, hXcomm] at hXY
  rw [hZcomm, hYcomm] at hYX
  linarith

private lemma MI_replica_swap
    {Γ : Type*} [Fintype Γ] [DecidableEq Γ] (g : α × β → Γ) :
    MI (fun u : D.L.ι × D.L.ι × D.L.ι × (α × β) => u.2.1)
        (fun u => g u.2.2.2) (replicaLaw D) =
      MI (fun u : D.L.ι × D.L.ι × D.L.ι × (α × β) => u.1)
        (fun u => g u.2.2.2) (replicaLaw D) := by
  let f : D.L.ι × D.L.ι × D.L.ι × (α × β) → D.L.ι × Γ :=
    fun u => (u.1, g u.2.2.2)
  have hpair :
      push (fun u : D.L.ι × D.L.ι × D.L.ι × (α × β) =>
        (u.2.1, g u.2.2.2)) (replicaLaw D) =
      push (fun u : D.L.ι × D.L.ι × D.L.ι × (α × β) =>
        (u.1, g u.2.2.2)) (replicaLaw D) := by
    have h := push_comp_equiv_eq_of_invariant (replicaSwap₀₁ D) (replicaLaw D)
      (replicaLaw_swap₀₁ D) f
    simpa [f, replicaSwap₀₁, Function.comp_def] using h
  exact MI_eq_of_pair_push_eq (replicaLaw D) (replicaLaw D)
    (fun u : D.L.ι × D.L.ι × D.L.ι × (α × β) => u.2.1)
    (fun u => g u.2.2.2)
    (fun u : D.L.ι × D.L.ι × D.L.ι × (α × β) => u.1)
    (fun u => g u.2.2.2) hpair

private lemma Hvar_replica_swap
    {Γ : Type*} [Fintype Γ] [DecidableEq Γ] (g : D.L.ι → α × β → Γ) :
    Hvar (fun u : D.L.ι × D.L.ι × D.L.ι × (α × β) => g u.2.1 u.2.2.2)
        (replicaLaw D) =
      Hvar (fun u : D.L.ι × D.L.ι × D.L.ι × (α × β) => g u.1 u.2.2.2)
        (replicaLaw D) := by
  let f : D.L.ι × D.L.ι × D.L.ι × (α × β) → Γ := fun u => g u.1 u.2.2.2
  have hpush := push_comp_equiv_eq_of_invariant (replicaSwap₀₁ D) (replicaLaw D)
    (replicaLaw_swap₀₁ D) f
  unfold Hvar
  simpa [f, replicaSwap₀₁, Function.comp_def] using congrArg H hpush

private lemma condMI_eq_MI_pair_sub_local
    {A Γ Δ K : Type*} [Fintype A] [Fintype Γ] [Fintype Δ] [Fintype K]
    [DecidableEq Γ] [DecidableEq Δ] [DecidableEq K]
    {m : A → ℝ} (hm : IsPMF m) (f : A → Γ) (g : A → Δ) (h : A → K) :
    condMI f g h m = MI (fun a => (h a, f a)) g m - MI h g m := by
  have hchain := MI_pair_left hm h f g
  linarith

private lemma condMI_pair_left_local
    {A Γ Δ E K : Type*} [Fintype A] [Fintype Γ] [Fintype Δ] [Fintype E]
    [Fintype K] [DecidableEq Γ] [DecidableEq Δ] [DecidableEq E] [DecidableEq K]
    {m : A → ℝ} (hm : IsPMF m) (f : A → Γ) (g : A → Δ) (k : A → E)
    (h : A → K) :
    condMI (fun a => (f a, g a)) k h m =
      condMI f k h m + condMI g k (fun a => (h a, f a)) m := by
  have hleft := condMI_eq_MI_pair_sub_local hm (fun a => (f a, g a)) k h
  have hfirst := condMI_eq_MI_pair_sub_local hm f k h
  have hsecond := condMI_eq_MI_pair_sub_local hm g k (fun a => (h a, f a))
  have hassoc := MI_equiv_left_local hm (fun a => ((h a, f a), g a))
    (Equiv.prodAssoc K Γ Δ) k
  change MI (fun a => (h a, f a, g a)) k m = MI (fun a => ((h a, f a), g a)) k m at hassoc
  linarith

private lemma condMI_equiv_cond_local
    {A Γ Δ K K' : Type*} [Fintype A] [Fintype Γ] [Fintype Δ]
    [Fintype K] [Fintype K'] [DecidableEq Γ] [DecidableEq Δ]
    [DecidableEq K] [DecidableEq K']
    {m : A → ℝ} (hm : IsPMF m) (f : A → Γ) (g : A → Δ) (h : A → K)
    (e : K ≃ K') :
    condMI f g (fun a => e (h a)) m = condMI f g h m := by
  have hfh := Hvar_equiv hm (fun a => (f a, h a))
    (Equiv.prodCongr (Equiv.refl Γ) e)
  have hgh := Hvar_equiv hm (fun a => (g a, h a))
    (Equiv.prodCongr (Equiv.refl Δ) e)
  have htrip := Hvar_equiv hm (fun a => (f a, g a, h a))
    (Equiv.prodCongr (Equiv.refl Γ) (Equiv.prodCongr (Equiv.refl Δ) e))
  have hh := Hvar_equiv hm h e
  change Hvar (fun a => (f a, e (h a))) m = Hvar (fun a => (f a, h a)) m at hfh
  change Hvar (fun a => (g a, e (h a))) m = Hvar (fun a => (g a, h a)) m at hgh
  change Hvar (fun a => (f a, g a, e (h a))) m = Hvar (fun a => (f a, g a, h a)) m at htrip
  unfold condMI
  rw [hfh, hgh, htrip, hh]

private lemma condMI_equiv_left_local
    {A Γ Γ' Δ K : Type*} [Fintype A] [Fintype Γ] [Fintype Γ'] [Fintype Δ]
    [Fintype K] [DecidableEq Γ] [DecidableEq Γ'] [DecidableEq Δ] [DecidableEq K]
    {m : A → ℝ} (hm : IsPMF m) (f : A → Γ) (e : Γ ≃ Γ') (g : A → Δ) (h : A → K) :
    condMI (fun a => e (f a)) g h m = condMI f g h m := by
  have hfh := Hvar_equiv hm (fun a => (f a, h a))
    (Equiv.prodCongr e (Equiv.refl K))
  have htrip := Hvar_equiv hm (fun a => (f a, g a, h a))
    (Equiv.prodCongr e (Equiv.refl (Δ × K)))
  change Hvar (fun a => (e (f a), h a)) m = Hvar (fun a => (f a, h a)) m at hfh
  change Hvar (fun a => (e (f a), g a, h a)) m = Hvar (fun a => (f a, g a, h a)) m at htrip
  unfold condMI
  rw [hfh, htrip]

private def replicaSwap₁₂ :
    (D.L.ι × D.L.ι × D.L.ι × (α × β)) ≃
      (D.L.ι × D.L.ι × D.L.ι × (α × β)) where
  toFun u := (u.1, u.2.2.1, u.2.1, u.2.2.2)
  invFun u := (u.1, u.2.2.1, u.2.1, u.2.2.2)
  left_inv := by rintro ⟨l₀, l₁, l₂, z⟩; rfl
  right_inv := by rintro ⟨l₀, l₁, l₂, z⟩; rfl

private lemma replicaLaw_swap₁₂ (u : D.L.ι × D.L.ι × D.L.ι × (α × β)) :
    replicaLaw D (replicaSwap₁₂ D u) = replicaLaw D u := by
  rcases u with ⟨l₀, l₁, l₂, z⟩
  change p z * D.post l₀ z * D.post l₂ z * D.post l₁ z =
    p z * D.post l₀ z * D.post l₁ z * D.post l₂ z
  ring

private lemma replica_condMI_l₂_eq_l₁ :
    condMI (fun u => u.2.2.1) (fun u => u.2.2.2) (fun u => u.1) (replicaLaw D) =
      condMI (fun u => u.2.1) (fun u => u.2.2.2) (fun u => u.1) (replicaLaw D) := by
  let f : D.L.ι × D.L.ι × D.L.ι × (α × β) →
      D.L.ι × (α × β) × D.L.ι := fun u => (u.2.1, u.2.2.2, u.1)
  have htriple :
      push (fun u : D.L.ι × D.L.ι × D.L.ι × (α × β) =>
        (u.2.2.1, u.2.2.2, u.1)) (replicaLaw D) =
      push (fun u : D.L.ι × D.L.ι × D.L.ι × (α × β) =>
        (u.2.1, u.2.2.2, u.1)) (replicaLaw D) := by
    have h := push_comp_equiv_eq_of_invariant (replicaSwap₁₂ D) (replicaLaw D)
      (replicaLaw_swap₁₂ D) f
    simpa [f, replicaSwap₁₂, Function.comp_def] using h
  exact condMI_eq_of_triple_push_eq (replicaLaw D) (replicaLaw D)
    (fun u => u.2.2.1) (fun u => u.2.2.2) (fun u => u.1)
    (fun u => u.2.1) (fun u => u.2.2.2) (fun u => u.1) htriple

/-- `b_Z := I(L₀; Z ∣ L₁)`. -/
noncomputable def bZ : ℝ :=
  condMI (fun u => u.1) (fun u => u.2.2.2) (fun u => u.2.1) (replicaLaw D)

/-- The three nonnegative replica interactions which measure the gap between
`b_Z` and the full `M + B_q` budget. -/
noncomputable def jointCharge : ℝ :=
  condMI (fun u => u.1) (fun u => u.2.1) (fun u => u.2.2.2.1) (replicaLaw D)
    + condMI (fun u => u.1) (fun u => u.2.1) (fun u => u.2.2.2.2) (replicaLaw D)
    + condMI (fun u => u.2.2.2.1) (fun u => u.2.2.2.2)
      (fun u => (u.1, u.2.1)) (replicaLaw D)

/-- `j := I(L;Z)`. -/
noncomputable def jInfo : ℝ := MI (fun q => q.1) (fun q => q.2) D.L.joint

/-- **Lemma 5.2** (one-use posterior resampling).
Every contact satisfies `D(r‖q) ≥ ⅔D(r_X‖q_X) + ⅔D(r_Y‖q_Y)`.
*Finite.* One application of (T1) plus `contact_hypercontractive`. -/
theorem posterior_resampling {S : Finset (α × β)} {w : α × β → ℝ} (hw : Feasible S w)
    {q : α × β → ℝ} (hq : IsContact S w q) {r : α × β → ℝ} (hr : IsPMF r)
    (hac : AbsCont r q) :
    2 / 3 * KL (mX r) (mX q) + 2 / 3 * KL (mY r) (mY q) ≤ KL r q := by
  have hrS : Supported S r := by
    intro z hzS
    exact hac z (hq.2.1 z hzS)
  have hsum_support (k : α × β → ℝ) :
      (∑ z ∈ S, r z * k z) = ∑ z, r z * k z := by
    apply Finset.sum_subset (Finset.subset_univ S)
    intro z _ hzS
    rw [hrS z hzS, zero_mul]
  have hKL : (∑ z ∈ S, r z * lg (r z / q z)) = KL r q := by
    rw [hsum_support]
    rfl
  have hKLX :
      (∑ z ∈ S, r z * lg (mX r z.1 / mX q z.1)) = KL (mX r) (mX q) := by
    calc
      (∑ z ∈ S, r z * lg (mX r z.1 / mX q z.1)) =
          ∑ z, r z * lg (mX r z.1 / mX q z.1) := hsum_support _
      _ = ∑ x, mX r x * lg (mX r x / mX q x) :=
        (sum_push_mul Prod.fst r (fun x => lg (mX r x / mX q x))).symm
      _ = KL (mX r) (mX q) := rfl
  have hKLY :
      (∑ z ∈ S, r z * lg (mY r z.2 / mY q z.2)) = KL (mY r) (mY q) := by
    calc
      (∑ z ∈ S, r z * lg (mY r z.2 / mY q z.2)) =
          ∑ z, r z * lg (mY r z.2 / mY q z.2) := hsum_support _
      _ = ∑ y, mY r y * lg (mY r y / mY q y) :=
        (sum_push_mul Prod.snd r (fun y => lg (mY r y / mY q y))).symm
      _ = KL (mY r) (mY q) := rfl
  have hterm (z : α × β) (hzS : z ∈ S) :
      r z * lg (r z / refMeas S w r z) =
        r z * lg (r z / q z)
          - ((2 : ℝ) / 3) * (r z * lg (mX r z.1 / mX q z.1))
          - ((2 : ℝ) / 3) * (r z * lg (mY r z.2 / mY q z.2)) := by
    by_cases hrz : r z = 0
    · simp [hrz]
    · have hrz_pos : 0 < r z := lt_of_le_of_ne (hr.nonneg z) (Ne.symm hrz)
      have hqz : q z ≠ 0 := fun hqz => hrz (hac z hqz)
      have hqz_pos : 0 < q z := lt_of_le_of_ne (hq.1.nonneg z) (Ne.symm hqz)
      have hrX_le : r z ≤ mX r z.1 := by
        unfold mX push
        exact Finset.single_le_sum (fun z _ => hr.nonneg z) (by simp)
      have hrY_le : r z ≤ mY r z.2 := by
        unfold mY push
        exact Finset.single_le_sum (fun z _ => hr.nonneg z) (by simp)
      have hqX_le : q z ≤ mX q z.1 := by
        unfold mX push
        exact Finset.single_le_sum (fun z _ => hq.1.nonneg z) (by simp)
      have hqY_le : q z ≤ mY q z.2 := by
        unfold mY push
        exact Finset.single_le_sum (fun z _ => hq.1.nonneg z) (by simp)
      have hrX_pos : 0 < mX r z.1 := hrz_pos.trans_le hrX_le
      have hrY_pos : 0 < mY r z.2 := hrz_pos.trans_le hrY_le
      have hqX_pos : 0 < mX q z.1 := hqz_pos.trans_le hqX_le
      have hqY_pos : 0 < mY q z.2 := hqz_pos.trans_le hqY_le
      have hw0 : w z ≠ 0 := (hw.1 z hzS).ne'
      have hrXpow0 : mX r z.1 ^ ((2 : ℝ) / 3) ≠ 0 :=
        (Real.rpow_pos_of_pos hrX_pos _).ne'
      have hrYpow0 : mY r z.2 ^ ((2 : ℝ) / 3) ≠ 0 :=
        (Real.rpow_pos_of_pos hrY_pos _).ne'
      have hqXpow0 : mX q z.1 ^ ((2 : ℝ) / 3) ≠ 0 :=
        (Real.rpow_pos_of_pos hqX_pos _).ne'
      have hqYpow0 : mY q z.2 ^ ((2 : ℝ) / 3) ≠ 0 :=
        (Real.rpow_pos_of_pos hqY_pos _).ne'
      have hrefR :
          w z * mX r z.1 ^ ((2 : ℝ) / 3) * mY r z.2 ^ ((2 : ℝ) / 3) ≠ 0 :=
        mul_ne_zero (mul_ne_zero hw0 hrXpow0) hrYpow0
      have hrefQ :
          w z * mX q z.1 ^ ((2 : ℝ) / 3) * mY q z.2 ^ ((2 : ℝ) / 3) ≠ 0 :=
        mul_ne_zero (mul_ne_zero hw0 hqXpow0) hqYpow0
      rw [refMeas, if_pos hzS, hq.2.2 z hzS]
      simp only [lg_eq_log_div]
      rw [Real.log_div hrz hrefR, Real.log_div hrz hrefQ,
        Real.log_div hrX_pos.ne' hqX_pos.ne', Real.log_div hrY_pos.ne' hqY_pos.ne',
        Real.log_mul (mul_ne_zero hw0 hrXpow0) hrYpow0,
        Real.log_mul hw0 hrXpow0, Real.log_rpow hrX_pos, Real.log_rpow hrY_pos,
        Real.log_mul (mul_ne_zero hw0 hqXpow0) hqYpow0,
        Real.log_mul hw0 hqXpow0, Real.log_rpow hqX_pos, Real.log_rpow hqY_pos]
      field_simp [Real.log_ne_zero_of_pos_of_ne_one (by norm_num : (0 : ℝ) < 2)
        (by norm_num : (2 : ℝ) ≠ 1)] <;> ring
  have hsum :
      (∑ z ∈ S, r z * lg (r z / refMeas S w r z)) =
        (∑ z ∈ S, r z * lg (r z / q z))
          - ((2 : ℝ) / 3) * (∑ z ∈ S, r z * lg (mX r z.1 / mX q z.1))
          - ((2 : ℝ) / 3) * (∑ z ∈ S, r z * lg (mY r z.2 / mY q z.2)) := by
    calc
      (∑ z ∈ S, r z * lg (r z / refMeas S w r z)) =
          ∑ z ∈ S, (r z * lg (r z / q z)
            - ((2 : ℝ) / 3) * (r z * lg (mX r z.1 / mX q z.1))
            - ((2 : ℝ) / 3) * (r z * lg (mY r z.2 / mY q z.2))) := by
              apply Finset.sum_congr rfl
              intro z hzS
              exact hterm z hzS
      _ = _ := by
        rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
          ← Finset.mul_sum]
  have hg := Gdef_nonneg hw hr hrS
  rw [Gdef, hsum, hKL, hKLX, hKLY] at hg
  linarith

/-- **Lemma 5.3** (the resampling budget): `b_Z ≤ 2B`.
*Finite.* §12 turns every `b_Z` into `2B` and hence into `τ`. -/
theorem bZ_le_two_Bq : bZ D ≤ 2 * D.Bq := by
  have hR := replicaLaw_isPMF D
  have hbSwap :
      condMI (fun u => u.2.1) (fun u => u.2.2.2) (fun u => u.1) (replicaLaw D) = bZ D := by
    simpa [bZ] using replica_condMI_swap D
  have hres := replica_cond_resampling D
  rw [hbSwap] at hres
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
  rw [hxEq, hyEq] at hres
  have hcx := condMI_nonneg hR (fun u => u.1) (fun u => u.2.1) (fun u => u.2.2.2.1)
  have hcy := condMI_nonneg hR (fun u => u.1) (fun u => u.2.1) (fun u => u.2.2.2.2)
  linarith [hres, hbEq, hB, hcx, hcy]

/-- **Lemma 5.4** (a replica pair carries at most two singles):
`I(L₁,L₂;Z ∣ L₀) ≤ 2 b_Z`. *Finite.* -/
theorem pair_le_two_bZ :
    condMI (fun u => (u.2.1, u.2.2.1)) (fun u => u.2.2.2) (fun u => u.1) (replicaLaw D)
      ≤ 2 * bZ D := by
  have hR := replicaLaw_isPMF D
  have htripleChain := condMI_pair_left_local hR
    (fun u => u.1) (fun u => u.2.1) (fun u => u.2.2.1) (fun u => u.2.2.2)
  rw [replica_triple_markov D] at htripleChain
  have hn₀ := condMI_nonneg hR (fun u => u.1) (fun u => u.2.2.1) (fun u => u.2.2.2)
  have hn₁ := condMI_nonneg hR (fun u => u.2.1) (fun u => u.2.2.1)
    (fun u => (u.2.2.2, u.1))
  have hindZ₀ :
      condMI (fun u => u.2.1) (fun u => u.2.2.1) (fun u => (u.2.2.2, u.1))
        (replicaLaw D) = 0 := by
    linarith [htripleChain, hn₀, hn₁]
  have hcondSwap := condMI_equiv_cond_local hR (fun u => u.2.1) (fun u => u.2.2.1)
    (fun u => (u.2.2.2, u.1)) (Equiv.prodComm (α × β) D.L.ι)
  change condMI (fun u => u.2.1) (fun u => u.2.2.1) (fun u => (u.1, u.2.2.2))
      (replicaLaw D) =
    condMI (fun u => u.2.1) (fun u => u.2.2.1) (fun u => (u.2.2.2, u.1))
      (replicaLaw D) at hcondSwap
  have hind₀Z :
      condMI (fun u => u.2.1) (fun u => u.2.2.1) (fun u => (u.1, u.2.2.2))
        (replicaLaw D) = 0 := by rw [hcondSwap, hindZ₀]
  have hA := condMI_pair_left_local hR (fun u => u.2.1) (fun u => u.2.2.2)
    (fun u => u.2.2.1) (fun u => u.1)
  have hB := condMI_pair_left_local hR (fun u => u.2.2.2) (fun u => u.2.1)
    (fun u => u.2.2.1) (fun u => u.1)
  have hPairCond := condMI_equiv_left_local hR
    (fun u => (u.2.1, u.2.2.2)) (Equiv.prodComm D.L.ι (α × β))
    (fun u => u.2.2.1) (fun u => u.1)
  change condMI (fun u => (u.2.2.2, u.2.1)) (fun u => u.2.2.1) (fun u => u.1)
      (replicaLaw D) =
    condMI (fun u => (u.2.1, u.2.2.2)) (fun u => u.2.2.1) (fun u => u.1)
      (replicaLaw D) at hPairCond
  have hSecondComm := condMI_comm_local hR (fun u => u.2.2.2) (fun u => u.2.2.1)
    (fun u => (u.1, u.2.1))
  have hSingleComm := condMI_comm_local hR (fun u => u.2.2.2) (fun u => u.2.2.1)
    (fun u => u.1)
  rw [hPairCond, hSingleComm, hind₀Z, add_zero] at hB
  rw [hSecondComm] at hA
  have hnPair := condMI_nonneg hR (fun u => u.2.1) (fun u => u.2.2.1) (fun u => u.1)
  have hsecondLe :
      condMI (fun u => u.2.2.1) (fun u => u.2.2.2) (fun u => (u.1, u.2.1))
          (replicaLaw D) ≤
        condMI (fun u => u.2.2.1) (fun u => u.2.2.2) (fun u => u.1)
          (replicaLaw D) := by
    linarith [hA, hB, hnPair]
  have hPairChain := condMI_pair_left_local hR (fun u => u.2.1) (fun u => u.2.2.1)
    (fun u => u.2.2.2) (fun u => u.1)
  have hsingle₁ :
      condMI (fun u => u.2.1) (fun u => u.2.2.2) (fun u => u.1) (replicaLaw D) =
        bZ D := by
    simpa [bZ] using replica_condMI_swap D
  have hsingle₂ :
      condMI (fun u => u.2.2.1) (fun u => u.2.2.2) (fun u => u.1) (replicaLaw D) =
        bZ D := by
    rw [replica_condMI_l₂_eq_l₁ D, hsingle₁]
  rw [hsingle₁] at hPairChain
  rw [hsingle₂] at hsecondLe
  linarith [hPairChain, hsecondLe]

private lemma sum_comp_mul_two_post (l₀ : D.L.ι) (z : α × β) :
    (∑ l₁, ∑ l₂, D.L.comp l₀ z * D.post l₁ z * D.post l₂ z) =
      D.L.comp l₀ z := by
  by_cases hpz : p z = 0
  · simp [comp_eq_zero_of_p_eq_zero D l₀ z hpz]
  · have hpost := sum_post_of_pos D z
      (lt_of_le_of_ne (D.isPMF.nonneg z) (Ne.symm hpz))
    calc
      (∑ l₁, ∑ l₂, D.L.comp l₀ z * D.post l₁ z * D.post l₂ z) =
          ∑ l₁, (D.L.comp l₀ z * D.post l₁ z) * (∑ l₂, D.post l₂ z) := by
            apply Finset.sum_congr rfl
            intro l₁ _
            rw [Finset.mul_sum]
      _ = ∑ l₁, D.L.comp l₀ z * D.post l₁ z := by rw [hpost]; simp
      _ = D.L.comp l₀ z * (∑ l₁, D.post l₁ z) := by rw [Finset.mul_sum]
      _ = D.L.comp l₀ z := by rw [hpost, mul_one]

private noncomputable def pairResamplePrior (l₀ : D.L.ι) (v : D.L.ι × D.L.ι) : ℝ :=
  ∑ z, D.L.comp l₀ z * D.post v.1 z * D.post v.2 z

private noncomputable def pairResampleComp (l₀ : D.L.ι) (v : D.L.ι × D.L.ι)
    (z : α × β) : ℝ :=
  if pairResamplePrior D l₀ v = 0 then D.L.comp l₀ z
  else D.L.comp l₀ z * D.post v.1 z * D.post v.2 z / pairResamplePrior D l₀ v

private lemma pairResamplePrior_nonneg (l₀ : D.L.ι) (v : D.L.ι × D.L.ι) :
    0 ≤ pairResamplePrior D l₀ v := by
  exact Finset.sum_nonneg fun z _ => mul_nonneg
    (mul_nonneg ((D.L.comp_isPMF l₀).nonneg z) (post_nonneg D v.1 z))
    (post_nonneg D v.2 z)

private lemma sum_pairResamplePrior (l₀ : D.L.ι) :
    ∑ v, pairResamplePrior D l₀ v = 1 := by
  unfold pairResamplePrior
  rw [Fintype.sum_prod_type]
  calc
    (∑ l₁, ∑ l₂, ∑ z,
        D.L.comp l₀ z * D.post l₁ z * D.post l₂ z) =
      ∑ l₁, ∑ z, ∑ l₂,
        D.L.comp l₀ z * D.post l₁ z * D.post l₂ z := by
          apply Finset.sum_congr rfl
          intro l₁ _
          exact Finset.sum_comm
    _ = ∑ z, ∑ l₁, ∑ l₂,
        D.L.comp l₀ z * D.post l₁ z * D.post l₂ z := Finset.sum_comm
    _ = ∑ z, D.L.comp l₀ z := by
      apply Finset.sum_congr rfl
      intro z _
      exact sum_comp_mul_two_post D l₀ z
    _ = 1 := by simpa [mass] using (D.L.comp_isPMF l₀).total

private lemma pairResamplePrior_mul_comp (l₀ : D.L.ι) (v : D.L.ι × D.L.ι)
    (z : α × β) :
    pairResamplePrior D l₀ v * pairResampleComp D l₀ v z =
      D.L.comp l₀ z * D.post v.1 z * D.post v.2 z := by
  by_cases hprior : pairResamplePrior D l₀ v = 0
  · have hle : D.L.comp l₀ z * D.post v.1 z * D.post v.2 z ≤
        pairResamplePrior D l₀ v := by
      unfold pairResamplePrior
      exact Finset.single_le_sum
        (fun z _ => mul_nonneg
          (mul_nonneg ((D.L.comp_isPMF l₀).nonneg z) (post_nonneg D v.1 z))
          (post_nonneg D v.2 z)) (by simp)
    rw [hprior] at hle
    have hterm : D.L.comp l₀ z * D.post v.1 z * D.post v.2 z = 0 :=
      le_antisymm hle (mul_nonneg
        (mul_nonneg ((D.L.comp_isPMF l₀).nonneg z) (post_nonneg D v.1 z))
        (post_nonneg D v.2 z))
    simp [pairResampleComp, hprior, hterm]
  · simp only [pairResampleComp, hprior, if_false]
    field_simp

private lemma pairResampleComp_isPMF (l₀ : D.L.ι) (v : D.L.ι × D.L.ι) :
    IsPMF (pairResampleComp D l₀ v) := by
  by_cases hprior : pairResamplePrior D l₀ v = 0
  · have hcomp : pairResampleComp D l₀ v = D.L.comp l₀ := by
      funext z
      simp [pairResampleComp, hprior]
    rw [hcomp]
    exact D.L.comp_isPMF l₀
  · have hprior_nonneg := pairResamplePrior_nonneg D l₀ v
    refine ⟨?_, ?_⟩
    · intro z
      simp only [pairResampleComp, hprior, if_false]
      exact div_nonneg (mul_nonneg
        (mul_nonneg ((D.L.comp_isPMF l₀).nonneg z) (post_nonneg D v.1 z))
        (post_nonneg D v.2 z)) hprior_nonneg
    · unfold mass
      simp only [pairResampleComp, hprior, if_false]
      calc
        (∑ z, D.L.comp l₀ z * D.post v.1 z * D.post v.2 z / pairResamplePrior D l₀ v) =
            pairResamplePrior D l₀ v / pairResamplePrior D l₀ v := by
              simp only [div_eq_mul_inv, ← Finset.sum_mul]
              rfl
        _ = 1 := div_self hprior

private lemma pairResampleComp_supported (l₀ : D.L.ι) (v : D.L.ι × D.L.ι) :
    Supported (support p) (pairResampleComp D l₀ v) := by
  have hcontact := D.contact l₀ (D.prior_pos l₀).ne'
  intro z hz
  have hz0 : D.L.comp l₀ z = 0 := hcontact.2.1 z hz
  simp [pairResampleComp, hz0]

private noncomputable def pairResampleLatent (l₀ : D.L.ι) : Latent (D.L.comp l₀) where
  ι := D.L.ι × D.L.ι
  fin := inferInstance
  dec := inferInstance
  prior := pairResamplePrior D l₀
  comp := pairResampleComp D l₀
  prior_isPMF := ⟨pairResamplePrior_nonneg D l₀, sum_pairResamplePrior D l₀⟩
  comp_isPMF := pairResampleComp_isPMF D l₀
  mixture := by
    intro z
    rw [Fintype.sum_prod_type]
    simp_rw [pairResamplePrior_mul_comp D l₀]
    exact sum_comp_mul_two_post D l₀ z

private lemma pairResampleLatent_joint (l₀ : D.L.ι) (v : (D.L.ι × D.L.ι) × (α × β)) :
    (pairResampleLatent D l₀).joint v =
      D.L.comp l₀ v.2 * D.post v.1.1 v.2 * D.post v.1.2 v.2 := by
  change pairResamplePrior D l₀ v.1 * pairResampleComp D l₀ v.1 v.2 = _
  exact pairResamplePrior_mul_comp D l₀ v.1 v.2

private lemma pairResample_fusion (l₀ : D.L.ι) :
    (∑ v, pairResamplePrior D l₀ v *
      Gdef (support p) D.w (pairResampleComp D l₀ v)) =
      3 * MI (fun v : (D.L.ι × D.L.ι) × (α × β) => v.1) (fun v => v.2)
          (pairResampleLatent D l₀).joint
        - 2 * MI (fun v : (D.L.ι × D.L.ι) × (α × β) => v.1) (fun v => v.2.1)
          (pairResampleLatent D l₀).joint
        - 2 * MI (fun v : (D.L.ι × D.L.ι) × (α × β) => v.1) (fun v => v.2.2)
          (pairResampleLatent D l₀).joint := by
  let V := pairResampleLatent D l₀
  have hcontact := D.contact l₀ (D.prior_pos l₀).ne'
  have hbase := (Gdef_eq_zero_iff D.feasible hcontact.1 hcontact.2.1).2 hcontact
  have hfusion := Gdef_fusion D.feasible.1 hcontact.1 hcontact.2.1 V
  rw [hbase, sub_zero] at hfusion
  change (∑ v, pairResamplePrior D l₀ v *
      Gdef (support p) D.w (pairResampleComp D l₀ v)) = _
  change (∑ v, pairResamplePrior D l₀ v *
      Gdef (support p) D.w (pairResampleComp D l₀ v)) = _ at hfusion
  exact hfusion

private lemma push_replicaFiber_pairZ (l₀ : D.L.ι) :
    push (fun u : D.L.ι × D.L.ι × D.L.ι × (α × β) =>
      ((u.2.1, u.2.2.1), u.2.2.2)) (replicaFiber D l₀) =
        fun v : (D.L.ι × D.L.ι) × (α × β) =>
          D.L.prior l₀ *
            (D.L.comp l₀ v.2 * D.post v.1.1 v.2 * D.post v.1.2 v.2) := by
  funext v
  rcases v with ⟨⟨l₁, l₂⟩, z⟩
  unfold push replicaFiber
  rw [Finset.sum_filter, sum_replica_domain D]
  simp only [Prod.mk.injEq]
  have hite (a b c : D.L.ι) (z' : α × β) :
      (if (b = l₁ ∧ c = l₂) ∧ z' = z then
          if a = l₀ then replicaLaw D (a, b, c, z') else 0 else 0) =
        if a = l₀ then if b = l₁ then if c = l₂ then
          if z' = z then replicaLaw D (a, b, c, z') else 0 else 0 else 0 else 0 := by
    by_cases ha : a = l₀ <;> by_cases hb : b = l₁ <;> by_cases hc : c = l₂ <;>
      by_cases hz : z' = z <;> simp [ha, hb, hc, hz]
  simp_rw [hite]
  simp
  change p z * D.post l₀ z * D.post l₁ z * D.post l₂ z =
    D.L.prior l₀ * (D.L.comp l₀ z * D.post l₁ z * D.post l₂ z)
  rw [p_mul_post D l₀ z]
  ring

private lemma MI_replicaFiber_pair_eq_smul
    {Γ : Type*} [Fintype Γ] [DecidableEq Γ]
    (l₀ : D.L.ι) (g : α × β → Γ) :
    MI (fun u : D.L.ι × D.L.ι × D.L.ι × (α × β) => (u.2.1, u.2.2.1))
        (fun u => g u.2.2.2) (replicaFiber D l₀) =
      D.L.prior l₀ *
        MI (fun v : (D.L.ι × D.L.ι) × (α × β) => v.1) (fun v => g v.2)
          (pairResampleLatent D l₀).joint := by
  let n : (D.L.ι × D.L.ι) × (α × β) → ℝ := fun v =>
    D.L.prior l₀ * (D.L.comp l₀ v.2 * D.post v.1.1 v.2 * D.post v.1.2 v.2)
  let base : D.L.ι × D.L.ι × D.L.ι × (α × β) →
      (D.L.ι × D.L.ι) × (α × β) := fun u => ((u.2.1, u.2.2.1), u.2.2.2)
  let k : (D.L.ι × D.L.ι) × (α × β) → (D.L.ι × D.L.ι) × Γ :=
    fun v => (v.1, g v.2)
  have hpair :
      push (fun u : D.L.ι × D.L.ι × D.L.ι × (α × β) =>
        ((u.2.1, u.2.2.1), g u.2.2.2)) (replicaFiber D l₀) =
      push (fun v : (D.L.ι × D.L.ι) × (α × β) => (v.1, g v.2)) n := by
    calc
      _ = push k (push base (replicaFiber D l₀)) := by
        symm
        simpa [base, k, Function.comp_def] using push_push base k (replicaFiber D l₀)
      _ = push k n := by rw [push_replicaFiber_pairZ D l₀]
      _ = _ := rfl
  have hMI := MI_eq_of_pair_push_eq (replicaFiber D l₀) n
    (fun u : D.L.ι × D.L.ι × D.L.ι × (α × β) => (u.2.1, u.2.2.1))
    (fun u => g u.2.2.2)
    (fun v : (D.L.ι × D.L.ι) × (α × β) => v.1) (fun v => g v.2) hpair
  have hscale := MI_smul (pairResampleLatent D l₀).joint_isPMF.isFinMeas
    (fun v => v.1) (fun v => g v.2) (D.L.prior_isPMF.nonneg l₀)
  change MI (fun v : (D.L.ι × D.L.ι) × (α × β) => v.1) (fun v => g v.2)
      (fun v => D.L.prior l₀ * (pairResampleLatent D l₀).joint v) =
    D.L.prior l₀ *
      MI (fun v : (D.L.ι × D.L.ι) × (α × β) => v.1) (fun v => g v.2)
        (pairResampleLatent D l₀).joint at hscale
  have hn : (fun v : (D.L.ι × D.L.ι) × (α × β) =>
      D.L.prior l₀ * (pairResampleLatent D l₀).joint v) = n := by
    funext v
    rw [pairResampleLatent_joint D l₀ v]
  rw [hn] at hscale
  exact hMI.trans hscale

private lemma pairFusion_cond_identity :
    (∑ l₀, D.L.prior l₀ *
      (∑ v, pairResamplePrior D l₀ v * Gdef (support p) D.w (pairResampleComp D l₀ v))) =
      3 * condMI (fun u => (u.2.1, u.2.2.1)) (fun u => u.2.2.2) (fun u => u.1)
          (replicaLaw D)
        - 2 * condMI (fun u => (u.2.1, u.2.2.1)) (fun u => u.2.2.2.1) (fun u => u.1)
          (replicaLaw D)
        - 2 * condMI (fun u => (u.2.1, u.2.2.1)) (fun u => u.2.2.2.2) (fun u => u.1)
          (replicaLaw D) := by
  have hX := condMI_eq_sum_MI_fibers (replicaLaw_isPMF D)
    (fun u => (u.2.1, u.2.2.1)) (fun u => u.2.2.2.1) (fun u => u.1)
  have hY := condMI_eq_sum_MI_fibers (replicaLaw_isPMF D)
    (fun u => (u.2.1, u.2.2.1)) (fun u => u.2.2.2.2) (fun u => u.1)
  have hZ := condMI_eq_sum_MI_fibers (replicaLaw_isPMF D)
    (fun u => (u.2.1, u.2.2.1)) (fun u => u.2.2.2) (fun u => u.1)
  change condMI (fun u => (u.2.1, u.2.2.1)) (fun u => u.2.2.2.1) (fun u => u.1)
      (replicaLaw D) =
    ∑ l₀, MI (fun u => (u.2.1, u.2.2.1)) (fun u => u.2.2.2.1) (replicaFiber D l₀) at hX
  change condMI (fun u => (u.2.1, u.2.2.1)) (fun u => u.2.2.2.2) (fun u => u.1)
      (replicaLaw D) =
    ∑ l₀, MI (fun u => (u.2.1, u.2.2.1)) (fun u => u.2.2.2.2) (replicaFiber D l₀) at hY
  change condMI (fun u => (u.2.1, u.2.2.1)) (fun u => u.2.2.2) (fun u => u.1)
      (replicaLaw D) =
    ∑ l₀, MI (fun u => (u.2.1, u.2.2.1)) (fun u => u.2.2.2) (replicaFiber D l₀) at hZ
  have hZfiber (l₀ : D.L.ι) :
      MI (fun u : D.L.ι × D.L.ι × D.L.ι × (α × β) => (u.2.1, u.2.2.1))
          (fun u => u.2.2.2) (replicaFiber D l₀) =
        D.L.prior l₀ *
          MI (fun v : (D.L.ι × D.L.ι) × (α × β) => v.1) (fun v => v.2)
            (pairResampleLatent D l₀).joint := by
    simpa only using MI_replicaFiber_pair_eq_smul D l₀ (fun z : α × β => z)
  rw [hX, hY, hZ]
  simp_rw [MI_replicaFiber_pair_eq_smul D]
  simp_rw [hZfiber]
  simp_rw [pairResample_fusion D]
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro l₀ _
  ring

/-- `Q⁽²⁾`, the triple overlap defect. -/
noncomputable def Q2 : ℝ :=
  ∑ a, ∑ c, ∑ b, (∑ z, p z * D.post a z * D.post c z * D.post b z) *
    Gdef (support p) D.w (fun z =>
      p z * D.post a z * D.post c z * D.post b z /
        ∑ z', p z' * D.post a z' * D.post c z' * D.post b z')

private lemma tripleWeight_eq (a c b : D.L.ι) :
    (∑ z, p z * D.post a z * D.post c z * D.post b z) =
      D.L.prior a * pairResamplePrior D a (c, b) := by
  unfold pairResamplePrior
  calc
    (∑ z, p z * D.post a z * D.post c z * D.post b z) =
        ∑ z, D.L.prior a *
          (D.L.comp a z * D.post c z * D.post b z) := by
            apply Finset.sum_congr rfl
            intro z _
            rw [p_mul_post D a z]
            ring
    _ = D.L.prior a * (∑ z, D.L.comp a z * D.post c z * D.post b z) := by
      rw [Finset.mul_sum]

private lemma tripleLaw_eq_pairComp (a c b : D.L.ι)
    (hweight : (∑ z, p z * D.post a z * D.post c z * D.post b z) ≠ 0) :
    (fun z => p z * D.post a z * D.post c z * D.post b z /
      ∑ z', p z' * D.post a z' * D.post c z' * D.post b z') =
        pairResampleComp D a (c, b) := by
  have ha : D.L.prior a ≠ 0 := (D.prior_pos a).ne'
  have hprior : pairResamplePrior D a (c, b) ≠ 0 := by
    intro hp
    apply hweight
    rw [tripleWeight_eq D a c b, hp]
    simp
  funext z
  simp only [pairResampleComp, hprior, if_false]
  rw [tripleWeight_eq D a c b]
  have hnum : p z * D.post a z * D.post c z * D.post b z =
      D.L.prior a * (D.L.comp a z * D.post c z * D.post b z) := by
    rw [p_mul_post D a z]
    ring
  rw [hnum]
  field_simp

private lemma tripleTerm_eq_pairTerm (a c b : D.L.ι) :
    (∑ z, p z * D.post a z * D.post c z * D.post b z) *
      Gdef (support p) D.w (fun z =>
        p z * D.post a z * D.post c z * D.post b z /
          ∑ z', p z' * D.post a z' * D.post c z' * D.post b z') =
    D.L.prior a * pairResamplePrior D a (c, b) *
      Gdef (support p) D.w (pairResampleComp D a (c, b)) := by
  by_cases hweight : (∑ z, p z * D.post a z * D.post c z * D.post b z) = 0
  · have hprior : pairResamplePrior D a (c, b) = 0 := by
      have h := tripleWeight_eq D a c b
      rw [hweight] at h
      exact (mul_eq_zero.mp h.symm).resolve_left (D.prior_pos a).ne'
    simp [hweight, hprior]
  · rw [tripleLaw_eq_pairComp D a c b hweight, tripleWeight_eq D a c b]

private lemma Q2_eq_pairFusion :
    Q2 D = ∑ a, D.L.prior a *
      (∑ v, pairResamplePrior D a v * Gdef (support p) D.w (pairResampleComp D a v)) := by
  unfold Q2
  calc
    (∑ a, ∑ c, ∑ b, (∑ z, p z * D.post a z * D.post c z * D.post b z) *
        Gdef (support p) D.w (fun z =>
          p z * D.post a z * D.post c z * D.post b z /
            ∑ z', p z' * D.post a z' * D.post c z' * D.post b z')) =
      ∑ a, ∑ c, ∑ b, D.L.prior a * pairResamplePrior D a (c, b) *
        Gdef (support p) D.w (pairResampleComp D a (c, b)) := by
          apply Finset.sum_congr rfl
          intro a _
          apply Finset.sum_congr rfl
          intro c _
          apply Finset.sum_congr rfl
          intro b _
          exact tripleTerm_eq_pairTerm D a c b
    _ = ∑ a, D.L.prior a *
        (∑ v, pairResamplePrior D a v * Gdef (support p) D.w (pairResampleComp D a v)) := by
          apply Finset.sum_congr rfl
          intro a _
          rw [Fintype.sum_prod_type, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro c _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro b _
          ring

private lemma Q2_cond_identity :
    Q2 D =
      3 * condMI (fun u => (u.2.1, u.2.2.1)) (fun u => u.2.2.2) (fun u => u.1)
          (replicaLaw D)
        - 2 * condMI (fun u => (u.2.1, u.2.2.1)) (fun u => u.2.2.2.1) (fun u => u.1)
          (replicaLaw D)
        - 2 * condMI (fun u => (u.2.1, u.2.2.1)) (fun u => u.2.2.2.2) (fun u => u.1)
          (replicaLaw D) := by
  rw [Q2_eq_pairFusion D, pairFusion_cond_identity D]

private lemma replica_M_identity :
    condMI (fun u => u.2.2.2.1) (fun u => u.2.2.2.2) (fun u => u.1)
        (replicaLaw D) = D.M := by
  let base : D.L.ι × D.L.ι × D.L.ι × (α × β) →
      D.L.ι × (α × β) := fun u => (u.1, u.2.2.2)
  let k : D.L.ι × (α × β) → α × β × D.L.ι :=
    fun v => (v.2.1, v.2.2, v.1)
  have htriple :
      push (fun u : D.L.ι × D.L.ι × D.L.ι × (α × β) =>
        (u.2.2.2.1, u.2.2.2.2, u.1)) (replicaLaw D) =
      push (fun v : D.L.ι × (α × β) => (v.2.1, v.2.2, v.1)) D.L.joint := by
    calc
      _ = push k (push base (replicaLaw D)) := by
        symm
        simpa [base, k, Function.comp_def] using push_push base k (replicaLaw D)
      _ = push k D.L.joint := by rw [push_replica_l₀z D]
      _ = _ := rfl
  have h := condMI_eq_of_triple_push_eq (replicaLaw D) D.L.joint
    (fun u => u.2.2.2.1) (fun u => u.2.2.2.2) (fun u => u.1)
    (fun v => v.2.1) (fun v => v.2.2) (fun v => v.1) htriple
  simpa [SeedSetup.M] using h

private lemma replica_Bq_identity :
    condMI (fun u => u.1) (fun u => u.2.2.2.1) (fun u => u.2.2.2.2)
        (replicaLaw D)
      + condMI (fun u => u.1) (fun u => u.2.2.2.2) (fun u => u.2.2.2.1)
        (replicaLaw D) = D.Bq := by
  rw [condMI_replica_l₀_eq_joint D (fun z : α × β => z.1) (fun z => z.2),
    condMI_replica_l₀_eq_joint D (fun z : α × β => z.2) (fun z => z.1)]
  rfl

/-- Exact replica ledger identity:
`M + B_q = b_Z + I(L₀;L₁|X) + I(L₀;L₁|Y) + I(X;Y|L₀,L₁)`. -/
theorem M_add_Bq_eq_bZ_add_jointCharge :
    D.M + D.Bq = bZ D + jointCharge D := by
  have hR := replicaLaw_isPMF D
  have hXA :
      Hvar (fun u : D.L.ι × D.L.ι × D.L.ι × (α × β) => (u.2.2.2.1, u.1))
          (replicaLaw D) =
        Hvar (fun u => (u.1, u.2.2.2.1)) (replicaLaw D) := by
    symm
    simpa using Hvar_equiv hR (fun u => (u.2.2.2.1, u.1))
      (Equiv.prodComm α D.L.ι)
  have hYA :
      Hvar (fun u : D.L.ι × D.L.ι × D.L.ι × (α × β) => (u.2.2.2.2, u.1))
          (replicaLaw D) =
        Hvar (fun u => (u.1, u.2.2.2.2)) (replicaLaw D) := by
    symm
    simpa using Hvar_equiv hR (fun u => (u.2.2.2.2, u.1))
      (Equiv.prodComm β D.L.ι)
  let cycleXYA : α × (β × D.L.ι) ≃ D.L.ι × (α × β) :=
    { toFun := fun t => (t.2.2, t.1, t.2.1)
      invFun := fun t => (t.2.1, t.2.2, t.1)
      left_inv := by rintro ⟨x, y, a⟩; rfl
      right_inv := by rintro ⟨a, x, y⟩; rfl }
  have hXYA :
      Hvar (fun u : D.L.ι × D.L.ι × D.L.ι × (α × β) =>
          (u.2.2.2.1, u.2.2.2.2, u.1)) (replicaLaw D) =
        Hvar (fun u => (u.1, u.2.2.2.1, u.2.2.2.2)) (replicaLaw D) := by
    symm
    simpa [cycleXYA] using Hvar_equiv hR
      (fun u => (u.2.2.2.1, u.2.2.2.2, u.1)) cycleXYA
  have hYX :
      Hvar (fun u : D.L.ι × D.L.ι × D.L.ι × (α × β) =>
          (u.2.2.2.2, u.2.2.2.1)) (replicaLaw D) =
        Hvar (fun u => (u.2.2.2.1, u.2.2.2.2)) (replicaLaw D) := by
    symm
    simpa using Hvar_equiv hR (fun u => (u.2.2.2.2, u.2.2.2.1))
      (Equiv.prodComm β α)
  have hAYX :
      Hvar (fun u : D.L.ι × D.L.ι × D.L.ι × (α × β) =>
          (u.1, u.2.2.2.2, u.2.2.2.1)) (replicaLaw D) =
        Hvar (fun u => (u.1, u.2.2.2.1, u.2.2.2.2)) (replicaLaw D) := by
    symm
    simpa using Hvar_equiv hR
      (fun u => (u.1, u.2.2.2.2, u.2.2.2.1))
      (Equiv.prodCongr (Equiv.refl D.L.ι) (Equiv.prodComm β α))
  have hB :
      Hvar (fun u : D.L.ι × D.L.ι × D.L.ι × (α × β) => u.2.1)
          (replicaLaw D) = Hvar (fun u => u.1) (replicaLaw D) := by
    simpa only using Hvar_replica_swap D (fun l _ => l)
  have hBX :
      Hvar (fun u : D.L.ι × D.L.ι × D.L.ι × (α × β) => (u.2.1, u.2.2.2.1))
          (replicaLaw D) =
        Hvar (fun u => (u.1, u.2.2.2.1)) (replicaLaw D) := by
    simpa only using Hvar_replica_swap D (fun l z => (l, z.1))
  have hBY :
      Hvar (fun u : D.L.ι × D.L.ι × D.L.ι × (α × β) => (u.2.1, u.2.2.2.2))
          (replicaLaw D) =
        Hvar (fun u => (u.1, u.2.2.2.2)) (replicaLaw D) := by
    simpa only using Hvar_replica_swap D (fun l z => (l, z.2))
  have hBZ :
      Hvar (fun u : D.L.ι × D.L.ι × D.L.ι × (α × β) => (u.2.1, u.2.2.2))
          (replicaLaw D) =
        Hvar (fun u => (u.1, u.2.2.2)) (replicaLaw D) := by
    simpa only using Hvar_replica_swap D (fun l z => (l, z))
  have hZB :
      Hvar (fun u : D.L.ι × D.L.ι × D.L.ι × (α × β) => (u.2.2.2, u.2.1))
          (replicaLaw D) =
        Hvar (fun u => (u.1, u.2.2.2)) (replicaLaw D) := by
    calc
      _ = Hvar (fun u => (u.2.1, u.2.2.2)) (replicaLaw D) := by
        symm
        simpa using Hvar_equiv hR (fun u => (u.2.2.2, u.2.1))
          (Equiv.prodComm (α × β) D.L.ι)
      _ = _ := hBZ
  have hAZB :
      Hvar (fun u : D.L.ι × D.L.ι × D.L.ι × (α × β) =>
          (u.1, u.2.2.2, u.2.1)) (replicaLaw D) =
        Hvar (fun u => (u.1, u.2.1, u.2.2.2)) (replicaLaw D) := by
    symm
    simpa using Hvar_equiv hR (fun u => (u.1, u.2.2.2, u.2.1))
      (Equiv.prodCongr (Equiv.refl D.L.ι) (Equiv.prodComm (α × β) D.L.ι))
  let cycleXAB : α × (D.L.ι × D.L.ι) ≃ D.L.ι × (D.L.ι × α) :=
    { toFun := fun t => (t.2.1, t.2.2, t.1)
      invFun := fun t => (t.2.2, t.1, t.2.1)
      left_inv := by rintro ⟨x, a, b⟩; rfl
      right_inv := by rintro ⟨a, b, x⟩; rfl }
  have hXAB :
      Hvar (fun u : D.L.ι × D.L.ι × D.L.ι × (α × β) =>
          (u.2.2.2.1, (u.1, u.2.1))) (replicaLaw D) =
        Hvar (fun u => (u.1, u.2.1, u.2.2.2.1)) (replicaLaw D) := by
    symm
    simpa [cycleXAB] using Hvar_equiv hR
      (fun u => (u.2.2.2.1, (u.1, u.2.1))) cycleXAB
  let cycleYAB : β × (D.L.ι × D.L.ι) ≃ D.L.ι × (D.L.ι × β) :=
    { toFun := fun t => (t.2.1, t.2.2, t.1)
      invFun := fun t => (t.2.2, t.1, t.2.1)
      left_inv := by rintro ⟨y, a, b⟩; rfl
      right_inv := by rintro ⟨a, b, y⟩; rfl }
  have hYAB :
      Hvar (fun u : D.L.ι × D.L.ι × D.L.ι × (α × β) =>
          (u.2.2.2.2, (u.1, u.2.1))) (replicaLaw D) =
        Hvar (fun u => (u.1, u.2.1, u.2.2.2.2)) (replicaLaw D) := by
    symm
    simpa [cycleYAB] using Hvar_equiv hR
      (fun u => (u.2.2.2.2, (u.1, u.2.1))) cycleYAB
  let cycleXYAB : α × (β × (D.L.ι × D.L.ι)) ≃
      D.L.ι × (D.L.ι × (α × β)) :=
    { toFun := fun t => (t.2.2.1, t.2.2.2, t.1, t.2.1)
      invFun := fun t => (t.2.2.1, t.2.2.2, t.1, t.2.1)
      left_inv := by rintro ⟨x, y, a, b⟩; rfl
      right_inv := by rintro ⟨a, b, x, y⟩; rfl }
  have hXYAB :
      Hvar (fun u : D.L.ι × D.L.ι × D.L.ι × (α × β) =>
          (u.2.2.2.1, u.2.2.2.2, (u.1, u.2.1))) (replicaLaw D) =
        Hvar (fun u => (u.1, u.2.1, u.2.2.2)) (replicaLaw D) := by
    symm
    simpa [cycleXYAB] using Hvar_equiv hR
      (fun u => (u.2.2.2.1, u.2.2.2.2, (u.1, u.2.1))) cycleXYAB
  have hmarkov := replica_markov D
  unfold condMI at hmarkov
  simp only at hmarkov
  rw [hBZ] at hmarkov
  rw [← replica_M_identity D, ← replica_Bq_identity D]
  unfold bZ jointCharge condMI
  simp only
  rw [hXA, hYA, hXYA, hYX, hAYX, hZB, hAZB, hB, hBX, hBY, hXAB, hYAB, hXYAB]
  linarith

/-- The joint replica charge is nonnegative. -/
theorem jointCharge_nonneg : 0 ≤ jointCharge D := by
  have hR := replicaLaw_isPMF D
  have hX := condMI_nonneg hR (fun u => u.1) (fun u => u.2.1)
    (fun u => u.2.2.2.1)
  have hY := condMI_nonneg hR (fun u => u.1) (fun u => u.2.1)
    (fun u => u.2.2.2.2)
  have hXY := condMI_nonneg hR (fun u => u.2.2.2.1) (fun u => u.2.2.2.2)
    (fun u => (u.1, u.2.1))
  unfold jointCharge
  linarith

/-- The replica leakage fits inside the full optimality budget: `b_Z ≤ τ`. -/
theorem bZ_le_tau : bZ D ≤ tau p := by
  rw [D.tau_eq_M_add_Bq, M_add_Bq_eq_bZ_add_jointCharge D]
  exact le_add_of_nonneg_right (jointCharge_nonneg D)

private lemma replica_interaction_identity :
    condMI (fun u => (u.2.1, u.2.2.1)) (fun u => u.2.2.2) (fun u => u.1)
        (replicaLaw D)
      - condMI (fun u => (u.2.1, u.2.2.1)) (fun u => u.2.2.2.1) (fun u => u.1)
        (replicaLaw D)
      - condMI (fun u => (u.2.1, u.2.2.1)) (fun u => u.2.2.2.2) (fun u => u.1)
        (replicaLaw D) =
    condMI (fun u => u.2.2.2.1) (fun u => u.2.2.2.2)
        (fun u => (u.1, (u.2.1, u.2.2.1))) (replicaLaw D)
      - condMI (fun u => u.2.2.2.1) (fun u => u.2.2.2.2) (fun u => u.1)
        (replicaLaw D) := by
  have hR := replicaLaw_isPMF D
  have hXY := condMI_pair_left_local hR (fun u => u.2.2.2.1) (fun u => u.2.2.2.2)
    (fun u => (u.2.1, u.2.2.1)) (fun u => u.1)
  have hZcomm := condMI_comm_local hR
    (fun u => (u.2.1, u.2.2.1)) (fun u => u.2.2.2) (fun u => u.1)
  have hXcomm := condMI_comm_local hR
    (fun u => u.2.2.2.1) (fun u => (u.2.1, u.2.2.1)) (fun u => u.1)
  have hYcommCX := condMI_comm_local hR
    (fun u => u.2.2.2.2) (fun u => (u.2.1, u.2.2.1))
    (fun u => (u.1, u.2.2.2.1))
  rw [← hZcomm, hXcomm, hYcommCX] at hXY
  have hVX := condMI_pair_left_local hR
    (fun u => (u.2.1, u.2.2.1)) (fun u => u.2.2.2.1)
    (fun u => u.2.2.2.2) (fun u => u.1)
  have hXV := condMI_pair_left_local hR
    (fun u => u.2.2.2.1) (fun u => (u.2.1, u.2.2.1))
    (fun u => u.2.2.2.2) (fun u => u.1)
  have hPair := condMI_equiv_left_local hR
    (fun u => ((u.2.1, u.2.2.1), u.2.2.2.1))
    (Equiv.prodComm (D.L.ι × D.L.ι) α) (fun u => u.2.2.2.2) (fun u => u.1)
  change condMI (fun u => (u.2.2.2.1, (u.2.1, u.2.2.1))) (fun u => u.2.2.2.2)
      (fun u => u.1) (replicaLaw D) =
    condMI (fun u => ((u.2.1, u.2.2.1), u.2.2.2.1)) (fun u => u.2.2.2.2)
      (fun u => u.1) (replicaLaw D) at hPair
  rw [hPair] at hXV
  linarith [hXY, hVX, hXV]

/-- **Lemma 5.6(c)**: `Q⁽²⁾ ≤ 6 b_Z`. *Finite.* -/
theorem Q2_le_six_bZ : Q2 D ≤ 6 * bZ D := by
  have hQ := Q2_cond_identity D
  have hR := replicaLaw_isPMF D
  have hX := condMI_nonneg hR (fun u => (u.2.1, u.2.2.1))
    (fun u => u.2.2.2.1) (fun u => u.1)
  have hY := condMI_nonneg hR (fun u => (u.2.1, u.2.2.1))
    (fun u => u.2.2.2.2) (fun u => u.1)
  have hpair := pair_le_two_bZ D
  linarith

/-- **Lemma 5.6(d)** (co-information form):
`I(L₁,L₂;Z ∣ L₀) ≤ Q⁽²⁾ + 2M`. *Finite.* -/
theorem pair_le_Q2_add_two_M :
    condMI (fun u => (u.2.1, u.2.2.1)) (fun u => u.2.2.2) (fun u => u.1) (replicaLaw D)
      ≤ Q2 D + 2 * D.M := by
  have hQ := Q2_cond_identity D
  have hinter := replica_interaction_identity D
  have hM := replica_M_identity D
  have hnonneg := condMI_nonneg (replicaLaw_isPMF D)
    (fun u => u.2.2.2.1) (fun u => u.2.2.2.2)
    (fun u => (u.1, (u.2.1, u.2.2.1)))
  rw [hM] at hinter
  linarith

/-! #### Calibration of the finite winner law -/

lemma post_pos_contact (b : D.L.ι) (z : α × β) (hz : 0 < p z) :
    0 < D.post b z := by
  have hsupp := contact_support_eq D.feasible D.conn
    (D.contact b (D.prior_pos b).ne')
  have hzmem : z ∈ support p := by simp [support, hz.ne']
  have hcompmem : z ∈ support (D.L.comp b) := by
    rw [hsupp]
    exact hzmem
  have hcompne : D.L.comp b z ≠ 0 := by
    simpa [support] using hcompmem
  unfold SeedSetup.post
  exact div_pos (mul_pos (D.prior_pos b)
    (lt_of_le_of_ne ((D.L.comp_isPMF b).nonneg z) (Ne.symm hcompne))) hz

lemma raceValue_clock_lt_iff (z : α × β) (a b : D.L.ι)
    (ha : 0 < D.post a z) (hb : 0 < D.post b z)
    (E : D.L.ι → ℝ) (hE : ∀ i, 0 < E i) :
    raceValue D z (fun i => -Real.log (E i)) b <
        raceValue D z (fun i => -Real.log (E i)) a ↔
      E a / D.post a z < E b / D.post b z := by
  have hscore (i : D.L.ι) (hi : 0 < D.post i z) :
      raceValue D z (fun j => -Real.log (E j)) i =
        Real.log (D.post i z / E i) := by
    unfold raceValue
    rw [Real.log_div hi.ne' (hE i).ne']
    ring
  rw [hscore b hb, hscore a ha]
  have hratioB : 0 < D.post b z / E b := div_pos hb (hE b)
  have hratioA : 0 < D.post a z / E a := div_pos ha (hE a)
  have hclockB : 0 < E b / D.post b z := div_pos (hE b) hb
  have hclockA : 0 < E a / D.post a z := div_pos (hE a) ha
  have hinvB : (E b / D.post b z)⁻¹ = D.post b z / E b := by
    field_simp
  have hinvA : (E a / D.post a z)⁻¹ = D.post a z / E a := by
    field_simp
  constructor
  · intro hlog
    have hratio : D.post b z / E b < D.post a z / E a := by
      rw [← Real.exp_log hratioB, ← Real.exp_log hratioA]
      exact Real.exp_lt_exp.mpr hlog
    rw [← hinvB, ← hinvA] at hratio
    exact (inv_lt_inv₀ hclockB hclockA).1 hratio
  · intro hclock
    have hinv : (E b / D.post b z)⁻¹ < (E a / D.post a z)⁻¹ :=
      (inv_lt_inv₀ hclockB hclockA).2 hclock
    rw [hinvB, hinvA] at hinv
    exact Real.strictMonoOn_log (Set.mem_Ioi.mpr hratioB)
      (Set.mem_Ioi.mpr hratioA) hinv

lemma lexWinner_clock_iff (z : α × β) (hz : 0 < p z)
    (E : D.L.ι → ℝ) (hE : ∀ i, 0 < E i)
    (a : D.L.ι)
    (htie : ∀ b, b ≠ a →
      raceValue D z (fun i => -Real.log (E i)) b ≠
        raceValue D z (fun i => -Real.log (E i)) a) :
    lexWinner D (fun i => -Real.log (E i)) z = a ↔
      strictClockWin (fun i => D.post i z) a E := by
  have hpost (i : D.L.ι) : 0 < D.post i z := post_pos_contact D i z hz
  constructor
  · intro hlex b hba
    have hle := lexMax_max
      (fun ε i => raceValue D z ε i) (fun i => -Real.log (E i)) b
    change raceValue D z (fun i => -Real.log (E i)) b ≤
      raceValue D z (fun i => -Real.log (E i))
        (lexWinner D (fun i => -Real.log (E i)) z) at hle
    rw [hlex] at hle
    have hlt :
        raceValue D z (fun i => -Real.log (E i)) b <
          raceValue D z (fun i => -Real.log (E i)) a := by
      rcases lt_trichotomy
          (raceValue D z (fun i => -Real.log (E i)) b)
          (raceValue D z (fun i => -Real.log (E i)) a) with hlt | heq | hgt
      · exact hlt
      · exact (htie b hba heq).elim
      · exact (not_lt_of_ge hle hgt).elim
    exact (raceValue_clock_lt_iff D z a b (hpost a) (hpost b) E hE).1
      hlt
  · intro hstrict
    by_contra hne
    have hmax := lexMax_max (fun ε i => raceValue D z ε i)
      (fun i => -Real.log (E i)) a
    change raceValue D z (fun i => -Real.log (E i)) a ≤
      raceValue D z (fun i => -Real.log (E i))
        (lexWinner D (fun i => -Real.log (E i)) z) at hmax
    have hlt := (raceValue_clock_lt_iff D z a
      (lexWinner D (fun i => -Real.log (E i)) z)
      (hpost a) (hpost _) E hE).2 (hstrict _ hne)
    exact (not_lt_of_ge hmax) hlt

lemma seedLaw_lexWinner_measure (z : α × β) (hz : 0 < p z)
    (a : D.L.ι) :
    seedLaw D.L.ι {ε | lexWinner D ε z = a} = ENNReal.ofReal (D.post a z) := by
  letI : MeasurableSpace D.L.ι := ⊤
  letI : IsProbabilityMeasure (expMeasure 1) :=
    isProbabilityMeasure_expMeasure zero_lt_one
  let F : (D.L.ι → ℝ) → (D.L.ι → ℝ) := fun E i => -Real.log (E i)
  have hF : Measurable F := measurable_pi_lambda _ fun i =>
    (Real.measurable_log.comp (measurable_pi_apply i)).neg
  have hlex : Measurable (fun ε => lexWinner D ε z) := by
    unfold lexWinner
    apply measurable_lexMax
    intro b
    exact measurable_const.add (measurable_pi_apply b)
  have hset : MeasurableSet {ε | lexWinner D ε z = a} :=
    measurableSet_singleton a |>.preimage hlex
  unfold seedLaw
  rw [Measure.map_apply hF hset]
  have hone : ∀ᵐ x : ℝ ∂(expMeasure 1), 0 < x := by
    have hnot := measure_eq_zero_iff_ae_notMem.mp expMeasure_one_Iic_zero
    filter_upwards [hnot] with x hx
    simpa only [Set.mem_Iic, not_le] using hx
  have hpos : ∀ᵐ E ∂(clockLaw D.L.ι), ∀ i, 0 < E i := by
    unfold clockLaw
    exact ae_forall_fintype fun i =>
      Measure.tendsto_eval_ae_ae.eventually hone
  have htieSeed := ae_no_race_ties D
  change ∀ᵐ ε ∂((clockLaw D.L.ι).map F), ∀ z a b, a ≠ b →
    raceValue D z ε a ≠ raceValue D z ε b at htieSeed
  have htieClock : ∀ᵐ E ∂(clockLaw D.L.ι), ∀ z a b, a ≠ b →
      raceValue D z (F E) a ≠ raceValue D z (F E) b :=
    ae_of_ae_map hF.aemeasurable htieSeed
  have hae : ∀ᵐ E ∂(clockLaw D.L.ι),
      E ∈ F ⁻¹' {ε | lexWinner D ε z = a} ↔
        E ∈ {E | strictClockWin (fun i => D.post i z) a E} := by
    filter_upwards [hpos, htieClock] with E hE htie
    change (lexWinner D (F E) z = a ↔
      strictClockWin (fun i => D.post i z) a E)
    exact lexWinner_clock_iff D z hz E hE a
      (fun b hba => htie z b a hba)
  calc
    clockLaw D.L.ι (F ⁻¹' {ε | lexWinner D ε z = a}) =
        clockLaw D.L.ι {E | strictClockWin (fun i => D.post i z) a E} :=
      measure_congr (hae.mono fun E h => propext h)
    _ = ENNReal.ofReal (D.post a z) := by
      unfold clockLaw
      exact pi_exp_strictClockWin (fun i => D.post i z)
        (fun i => post_pos_contact D i z hz) (sum_post_of_pos D z hz) a

lemma winner_probability (z : α × β) (hz : 0 < p z) (a : D.L.ι) :
    (∫ ε, (if winner D ε z = a then (1 : ℝ) else 0) ∂(seedLaw D.L.ι)) =
      D.post a z := by
  letI : MeasurableSpace D.L.ι := ⊤
  have hae :
      (fun ε => if winner D ε z = a then (1 : ℝ) else 0) =ᵐ[seedLaw D.L.ι]
        fun ε => if lexWinner D ε z = a then 1 else 0 := by
    filter_upwards [winner_ae_eq_lexWinner D] with ε hε
    rw [hε]
  rw [integral_congr_ae hae]
  have hlex : Measurable (fun ε => lexWinner D ε z) := by
    unfold lexWinner
    apply measurable_lexMax
    intro b
    exact measurable_const.add (measurable_pi_apply b)
  let s : Set (D.L.ι → ℝ) := {ε | lexWinner D ε z = a}
  have hs : MeasurableSet s := measurableSet_singleton a |>.preimage hlex
  have hfun : (fun ε => if lexWinner D ε z = a then (1 : ℝ) else 0) =
      s.indicator (1 : (D.L.ι → ℝ) → ℝ) := by
    funext ε
    simp [s, Set.indicator]
  rw [hfun]
  rw [integral_indicator_one hs, measureReal_def,
    seedLaw_lexWinner_measure D z hz a,
    ENNReal.toReal_ofReal (post_nonneg D a z)]

/- Any real-valued expression which depends on the seed only through the
finite winner map is integrable.  We use the measurable lexicographic winner
as an a.e. version of the arbitrary maximizer in `winner`. -/
lemma integrable_winner_code
    (F : ((α × β) → D.L.ι) → ℝ) :
    Integrable (fun ε => F (winner D ε)) (seedLaw D.L.ι) := by
  letI : MeasurableSpace D.L.ι := ⊤
  have hlex (z : α × β) : Measurable (fun ε => lexWinner D ε z) := by
    unfold lexWinner
    apply measurable_lexMax
    intro a
    change Measurable (fun ε : D.L.ι → ℝ => Real.log (D.post a z) + ε a)
    exact measurable_const.add (measurable_pi_apply a)
  have hlexCode : Measurable (fun ε => lexWinner D ε) :=
    measurable_pi_lambda _ hlex
  have hversion : Measurable (fun ε => F (lexWinner D ε)) :=
    (measurable_of_finite F).comp hlexCode
  have hae :
      (fun ε => F (winner D ε)) =ᵐ[seedLaw D.L.ι]
        fun ε => F (lexWinner D ε) := by
    filter_upwards [winner_ae_eq_lexWinner D] with ε hε
    rw [hε]
  have hstrong :
      AEStronglyMeasurable (fun ε => F (winner D ε)) (seedLaw D.L.ι) :=
    hversion.aestronglyMeasurable.congr hae.symm
  let C := ∑ A : (α × β) → D.L.ι, ‖F A‖
  apply Integrable.of_bound hstrong C
  filter_upwards [] with ε
  exact Finset.single_le_sum (fun A _ => norm_nonneg (F A))
    (Finset.mem_univ (winner D ε))

/-! #### The cellwise source latent used in Theorem 5.7 -/

lemma component_support_eq (b : D.L.ι) :
    support (D.L.comp b) = support p := by
  exact contact_support_eq D.feasible D.conn
    (D.contact b (D.prior_pos b).ne')

lemma component_eq_zero_iff (b : D.L.ι) (z : α × β) :
    D.L.comp b z = 0 ↔ p z = 0 := by
  have hmem := Finset.ext_iff.mp (component_support_eq D b) z
  simpa [support] using not_congr hmem

lemma post_pos_of_p_pos (b : D.L.ι) (z : α × β) (hz : 0 < p z) :
    0 < D.post b z := by
  unfold SeedSetup.post
  exact div_pos (mul_pos (D.prior_pos b)
    (lt_of_le_of_ne ((D.L.comp_isPMF b).nonneg z)
      (Ne.symm ((component_eq_zero_iff D b z).not.mpr hz.ne')))) hz

noncomputable def componentCellMass (ε : D.L.ι → ℝ)
    (a b : D.L.ι) : ℝ :=
  ∑ z ∈ cell D ε a, D.L.comp b z

lemma componentCellMass_nonneg (ε : D.L.ι → ℝ) (a b : D.L.ι) :
    0 ≤ componentCellMass D ε a b := by
  exact Finset.sum_nonneg fun z _ => (D.L.comp_isPMF b).nonneg z

lemma componentCellMass_eq_zero_iff (ε : D.L.ι → ℝ) (a b : D.L.ι) :
    componentCellMass D ε a b = 0 ↔ cellMass D ε a = 0 := by
  rw [componentCellMass, cellMass]
  constructor
  · intro h
    apply (Finset.sum_eq_zero_iff_of_nonneg
      (fun z _ => D.isPMF.nonneg z)).2
    intro z hz
    apply (component_eq_zero_iff D b z).mp
    exact (Finset.sum_eq_zero_iff_of_nonneg
      (fun z _ => (D.L.comp_isPMF b).nonneg z)).1 h z hz
  · intro h
    apply (Finset.sum_eq_zero_iff_of_nonneg
      (fun z _ => (D.L.comp_isPMF b).nonneg z)).2
    intro z hz
    apply (component_eq_zero_iff D b z).mpr
    exact (Finset.sum_eq_zero_iff_of_nonneg
      (fun z _ => D.isPMF.nonneg z)).1 h z hz

lemma sum_prior_componentCellMass (ε : D.L.ι → ℝ) (a : D.L.ι) :
    (∑ b, D.L.prior b * componentCellMass D ε a b) = cellMass D ε a := by
  unfold componentCellMass cellMass
  calc
    (∑ b, D.L.prior b * ∑ z ∈ cell D ε a, D.L.comp b z) =
        ∑ z ∈ cell D ε a, ∑ b, D.L.prior b * D.L.comp b z := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
    _ = ∑ z ∈ cell D ε a, p z := by
      apply Finset.sum_congr rfl
      intro z _
      exact D.L.mixture z

noncomputable def componentCellRaw (ε : D.L.ι → ℝ)
    (a b : D.L.ι) (z : α × β) : ℝ :=
  if winner D ε z = a then D.L.comp b z / componentCellMass D ε a b else 0

noncomputable def componentCellLaw (ε : D.L.ι → ℝ)
    (a b : D.L.ι) (z : α × β) : ℝ :=
  if componentCellMass D ε a b = 0 then cellLaw D ε a z
  else componentCellRaw D ε a b z

noncomputable def componentCellPrior (ε : D.L.ι → ℝ)
    (a b : D.L.ι) : ℝ :=
  if cellMass D ε a = 0 then D.L.prior b
  else D.L.prior b * componentCellMass D ε a b / cellMass D ε a

noncomputable def cellSourceLatent (ε : D.L.ι → ℝ)
    (a : D.L.ι) : Latent (cellLaw D ε a) where
  ι := D.L.ι
  fin := D.L.fin
  dec := D.L.dec
  prior := componentCellPrior D ε a
  comp := componentCellLaw D ε a
  prior_isPMF := by
    refine ⟨?_, ?_⟩
    · intro b
      unfold componentCellPrior
      split_ifs
      · exact D.L.prior_isPMF.nonneg b
      · exact div_nonneg
          (mul_nonneg (D.L.prior_isPMF.nonneg b)
            (componentCellMass_nonneg D ε a b))
          (cellMass_nonneg D ε a)
    · unfold mass componentCellPrior
      by_cases hmass : cellMass D ε a = 0
      · simp only [hmass, if_true]
        simpa [mass] using D.L.prior_isPMF.total
      · simp only [hmass, if_false]
        rw [← Finset.sum_div, sum_prior_componentCellMass D ε a,
          div_self hmass]
  comp_isPMF := by
    intro b
    by_cases hmass : componentCellMass D ε a b = 0
    · have hlaw : componentCellLaw D ε a b = cellLaw D ε a := by
        funext z
        simp [componentCellLaw, hmass]
      rw [hlaw]
      exact (winnerLatent D ε).comp_isPMF a
    · refine ⟨?_, ?_⟩
      · intro z
        unfold componentCellLaw componentCellRaw
        simp only [hmass, if_false]
        split_ifs
        · exact div_nonneg ((D.L.comp_isPMF b).nonneg z)
            (componentCellMass_nonneg D ε a b)
        · exact le_rfl
      · unfold mass componentCellLaw componentCellRaw
        simp only [hmass, if_false]
        calc
          (∑ z, if winner D ε z = a then
              D.L.comp b z / componentCellMass D ε a b else 0) =
              ∑ z ∈ cell D ε a,
                D.L.comp b z / componentCellMass D ε a b := by
            rw [cell, Finset.sum_filter]
          _ = componentCellMass D ε a b /
                componentCellMass D ε a b := by
            simp only [div_eq_mul_inv, ← Finset.sum_mul]
            rfl
          _ = 1 := div_self hmass
  mixture := by
    intro z
    by_cases hmass : cellMass D ε a = 0
    · have hcm (b : D.L.ι) : componentCellMass D ε a b = 0 :=
        (componentCellMass_eq_zero_iff D ε a b).2 hmass
      simp only [componentCellPrior, componentCellLaw, hmass, hcm, if_true]
      rw [← Finset.sum_mul, show (∑ b, D.L.prior b) = 1 by
        simpa [mass] using D.L.prior_isPMF.total, one_mul]
    · have hcm (b : D.L.ι) : componentCellMass D ε a b ≠ 0 :=
        fun h => hmass ((componentCellMass_eq_zero_iff D ε a b).1 h)
      by_cases hwinner : winner D ε z = a
      · simp only [componentCellPrior, componentCellLaw, componentCellRaw,
          hmass, hcm, hwinner, if_false, if_true]
        calc
          (∑ b, (D.L.prior b * componentCellMass D ε a b /
              cellMass D ε a) *
              (D.L.comp b z / componentCellMass D ε a b)) =
              ∑ b, D.L.prior b * D.L.comp b z / cellMass D ε a := by
            apply Finset.sum_congr rfl
            intro b _
            field_simp [hcm b]
          _ = p z / cellMass D ε a := by
            rw [← Finset.sum_div, D.L.mixture z]
          _ = cellLaw D ε a z := by
            simp [cellLaw, hmass, hwinner]
      · simp [componentCellPrior, componentCellLaw, componentCellRaw,
          hmass, hcm, hwinner, cellLaw]

lemma cellSource_weighted_G (ε : D.L.ι → ℝ) (a : D.L.ι) :
    cellMass D ε a *
        (∑ b, (cellSourceLatent D ε a).prior b *
          Gdef (support p) D.w ((cellSourceLatent D ε a).comp b)) =
      ∑ b, D.L.prior b * componentCellMass D ε a b *
        Gdef (support p) D.w (componentCellRaw D ε a b) := by
  by_cases hmass : cellMass D ε a = 0
  · have hcm (b : D.L.ι) : componentCellMass D ε a b = 0 :=
      (componentCellMass_eq_zero_iff D ε a b).2 hmass
    simp [hmass, hcm]
  · have hcm (b : D.L.ι) : componentCellMass D ε a b ≠ 0 :=
      fun h => hmass ((componentCellMass_eq_zero_iff D ε a b).1 h)
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    change cellMass D ε a *
        (componentCellPrior D ε a b *
          Gdef (support p) D.w (componentCellLaw D ε a b)) = _
    have hlaw : componentCellLaw D ε a b = componentCellRaw D ε a b := by
      funext z
      simp [componentCellLaw, hcm b]
    rw [hlaw]
    simp only [componentCellPrior, hmass, if_false]
    field_simp

lemma cellSource_fiber (ε : D.L.ι → ℝ) (a : D.L.ι) :
    (fun q : D.L.ι × (α × β) =>
      if winner D ε q.2 = a then D.L.joint q else 0) =
    fun q => cellMass D ε a * (cellSourceLatent D ε a).joint q := by
  funext q
  rcases q with ⟨b, z⟩
  change (if winner D ε z = a then D.L.prior b * D.L.comp b z else 0) =
    cellMass D ε a *
      (componentCellPrior D ε a b * componentCellLaw D ε a b z)
  by_cases hmass : cellMass D ε a = 0
  · simp only [hmass, zero_mul]
    by_cases hwinner : winner D ε z = a
    · have hzmem : z ∈ cell D ε a := by simp [cell, hwinner]
      have hpz : p z = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg
          (fun z _ => D.isPMF.nonneg z)).1 hmass z hzmem
      have hcomp : D.L.comp b z = 0 := (component_eq_zero_iff D b z).2 hpz
      simp [hwinner, hcomp]
    · simp [hwinner]
  · have hcm : componentCellMass D ε a b ≠ 0 :=
      fun h => hmass ((componentCellMass_eq_zero_iff D ε a b).1 h)
    by_cases hwinner : winner D ε z = a
    · simp only [hwinner, if_true]
      simp only [componentCellPrior, componentCellLaw, componentCellRaw,
        hmass, hcm, hwinner, if_false, if_true]
      field_simp
    · simp [hwinner, componentCellPrior, componentCellLaw,
        componentCellRaw, hmass, hcm]

lemma winner_condInfo_eq_cells (ε : D.L.ι → ℝ) :
    condMI (fun q : D.L.ι × (α × β) => q.1) (fun q => q.2)
        (fun q => winner D ε q.2) D.L.joint =
      ∑ a, cellMass D ε a *
        MI (fun q : D.L.ι × (α × β) => q.1) (fun q => q.2)
          (cellSourceLatent D ε a).joint := by
  rw [condMI_eq_sum_MI_fibers D.L.joint_isPMF]
  apply Finset.sum_congr rfl
  intro a _
  rw [cellSource_fiber D ε a]
  exact MI_smul (cellSourceLatent D ε a).joint_isPMF.isFinMeas
    (fun q : D.L.ι × (α × β) => q.1) (fun q => q.2)
    (cellMass_nonneg D ε a)

lemma fixed_seed_cell_comparison (ε : D.L.ι → ℝ) :
    (∑ a, cellMass D ε a * Gdef (support p) D.w (cellLaw D ε a)) ≤
      (∑ a, ∑ b, D.L.prior b * componentCellMass D ε a b *
        Gdef (support p) D.w (componentCellRaw D ε a b)) +
      condMI (fun q : D.L.ι × (α × β) => q.1) (fun q => q.2)
        (fun q => winner D ε q.2) D.L.joint := by
  have hcell (a : D.L.ι) :
      cellMass D ε a * Gdef (support p) D.w (cellLaw D ε a) ≤
        (∑ b, D.L.prior b * componentCellMass D ε a b *
          Gdef (support p) D.w (componentCellRaw D ε a b)) +
        cellMass D ε a *
          MI (fun q : D.L.ι × (α × β) => q.1) (fun q => q.2)
            (cellSourceLatent D ε a).joint := by
    let V := cellSourceLatent D ε a
    let IZ : ℝ := MI (fun q : D.L.ι × (α × β) => q.1) (fun q => q.2) V.joint
    let IX : ℝ := MI (fun q : D.L.ι × (α × β) => q.1) (fun q => q.2.1) V.joint
    let IY : ℝ := MI (fun q : D.L.ι × (α × β) => q.1) (fun q => q.2.2) V.joint
    have hfusion := Gdef_fusion D.feasible.1
      ((winnerLatent D ε).comp_isPMF a) (cellLaw_supported D ε a) V
    have hXraw := MI_le_of_comp V.joint_isPMF
      (fun q : D.L.ι × (α × β) => q.1) (fun q => q.2) Prod.fst
    have hYraw := MI_le_of_comp V.joint_isPMF
      (fun q : D.L.ι × (α × β) => q.1) (fun q => q.2) Prod.snd
    change MI (fun q : D.L.ι × (α × β) => q.1) (fun q => q.2.1) V.joint ≤
      MI (fun q => q.1) (fun q => q.2) V.joint at hXraw
    change MI (fun q : D.L.ι × (α × β) => q.1) (fun q => q.2.2) V.joint ≤
      MI (fun q => q.1) (fun q => q.2) V.joint at hYraw
    have hX : IX ≤ IZ := hXraw
    have hY : IY ≤ IZ := hYraw
    change (∑ b, V.prior b * Gdef (support p) D.w (V.comp b)) -
        Gdef (support p) D.w (cellLaw D ε a) =
      3 * IZ - 2 * IX - 2 * IY at hfusion
    have hfinite' :
        Gdef (support p) D.w (cellLaw D ε a) ≤
          (∑ b, V.prior b * Gdef (support p) D.w (V.comp b)) + IZ := by
      linarith
    have hfinite :
        Gdef (support p) D.w (cellLaw D ε a) ≤
          (∑ b, V.prior b * Gdef (support p) D.w (V.comp b)) +
            MI (fun q : D.L.ι × (α × β) => q.1) (fun q => q.2) V.joint := by
      exact hfinite'
    have hmul := mul_le_mul_of_nonneg_left hfinite (cellMass_nonneg D ε a)
    rw [mul_add] at hmul
    dsimp only [V] at hmul
    rw [cellSource_weighted_G D ε a] at hmul
    exact hmul
  calc
    (∑ a, cellMass D ε a * Gdef (support p) D.w (cellLaw D ε a)) ≤
        ∑ a, ((∑ b, D.L.prior b * componentCellMass D ε a b *
          Gdef (support p) D.w (componentCellRaw D ε a b)) +
          cellMass D ε a *
            MI (fun q : D.L.ι × (α × β) => q.1) (fun q => q.2)
              (cellSourceLatent D ε a).joint) :=
      Finset.sum_le_sum fun a _ => hcell a
    _ = (∑ a, ∑ b, D.L.prior b * componentCellMass D ε a b *
          Gdef (support p) D.w (componentCellRaw D ε a b)) +
        condMI (fun q : D.L.ι × (α × β) => q.1) (fun q => q.2)
          (fun q => winner D ε q.2) D.L.joint := by
      rw [Finset.sum_add_distrib, winner_condInfo_eq_cells D ε]

private lemma integrable_Dw_integrand :
    Integrable
      (fun ε => ∑ a, cellMass D ε a *
        Gdef (support p) D.w (cellLaw D ε a))
      (seedLaw D.L.ι) := by
  have heq :
      (fun ε => ∑ a, cellMass D ε a *
        Gdef (support p) D.w (cellLaw D ε a)) =
        fun ε => (winnerLatent D ε).score - tau p := by
    funext ε
    exact per_seed_ledger D ε
  rw [heq]
  exact (integrable_winnerScore D).sub (integrable_const (tau p))

private lemma integrable_cellResidual_integrand :
    Integrable
      (fun ε => ∑ a, ∑ b, D.L.prior b * componentCellMass D ε a b *
        Gdef (support p) D.w (componentCellRaw D ε a b))
      (seedLaw D.L.ι) := by
  let F : ((α × β) → D.L.ι) → ℝ := fun A =>
    ∑ a, ∑ b, D.L.prior b *
      (∑ z ∈ Finset.univ.filter (fun z => A z = a), D.L.comp b z) *
      Gdef (support p) D.w (fun z =>
        if A z = a then
          D.L.comp b z /
            ∑ z' ∈ Finset.univ.filter (fun z' => A z' = a), D.L.comp b z'
        else 0)
  have h := integrable_winner_code D F
  unfold componentCellRaw
  unfold componentCellMass
  simpa only [F, cell] using h

lemma integrable_winnerCondInfo :
    Integrable
      (fun ε => condMI
        (fun q : D.L.ι × (α × β) => q.1) (fun q => q.2)
        (fun q => winner D ε q.2) D.L.joint)
      (seedLaw D.L.ι) := by
  let F : ((α × β) → D.L.ι) → ℝ := fun A =>
    condMI (fun q : D.L.ι × (α × β) => q.1) (fun q => q.2)
      (fun q => A q.2) D.L.joint
  simpa only [F] using integrable_winner_code D F

/-- The **cell residual** `R_cell`. Involves the seed. -/
noncomputable def Rcell : ℝ :=
  ∫ ε, (∑ a, ∑ b, D.L.prior b *
      (∑ z ∈ cell D ε a, D.L.comp b z) *
      Gdef (support p) D.w (fun z =>
        if winner D ε z = a then D.L.comp b z / ∑ z' ∈ cell D ε a, D.L.comp b z' else 0))
    ∂(seedLaw D.L.ι)

private lemma Dwdefect_le_Rcell_add_integral_condInfo :
    Dwdefect D ≤
      Rcell D +
        ∫ ε, condMI
          (fun q : D.L.ι × (α × β) => q.1) (fun q => q.2)
          (fun q => winner D ε q.2) D.L.joint ∂(seedLaw D.L.ι) := by
  have hDw := integrable_Dw_integrand D
  have hR := integrable_cellResidual_integrand D
  have hI := integrable_winnerCondInfo D
  have hmono :
      (∫ ε, (∑ a, cellMass D ε a *
          Gdef (support p) D.w (cellLaw D ε a)) ∂(seedLaw D.L.ι)) ≤
        ∫ ε, ((∑ a, ∑ b, D.L.prior b * componentCellMass D ε a b *
            Gdef (support p) D.w (componentCellRaw D ε a b)) +
          condMI (fun q : D.L.ι × (α × β) => q.1) (fun q => q.2)
            (fun q => winner D ε q.2) D.L.joint) ∂(seedLaw D.L.ι) := by
    exact integral_mono hDw (hR.add hI) (fixed_seed_cell_comparison D)
  rw [integral_add hR hI] at hmono
  unfold Dwdefect Rcell
  unfold componentCellRaw at hmono
  unfold componentCellMass at hmono
  exact hmono

/- The finite cross-entropy inequality used for conditional-entropy
concavity.  It is just Gibbs' inequality, with all quantities in bits. -/
lemma H_le_crossEntropy
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {r q : κ → ℝ} (hr : IsPMF r) (hq : IsPMF q)
    (hsupp : ∀ i, r i ≠ 0 → q i ≠ 0) :
    H r ≤ ∑ i, r i * lg (1 / q i) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hH := H_eq_negMulLog hr.isFinMeas
  rw [hr.total, Real.log_one, mul_zero, zero_add] at hH
  have hcross :
      Real.log 2 * (∑ i, r i * lg (1 / q i)) =
        ∑ i, r i * Real.log (1 / q i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [lg_eq_log_div]
    field_simp [hlog2.ne']
  have hdiff :
      (∑ i, r i * Real.log (1 / q i)) -
          ∑ i, Real.negMulLog (r i) =
        ∑ i, r i * Real.log (r i / q i) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hri : r i = 0
    · simp [hri, Real.negMulLog]
    · have hqi : q i ≠ 0 := hsupp i hri
      rw [Real.negMulLog, Real.log_div one_ne_zero hqi,
        Real.log_one, Real.log_div hri hqi]
      ring
  have hgibbs := gibbs_nonneg hr hq hsupp
  apply (mul_le_mul_iff_of_pos_left hlog2).mp
  rw [hH, hcross]
  linarith

lemma condH_graph_right
    {A Γ Δ K : Type*} [Fintype A] [Fintype Γ] [Fintype Δ] [Fintype K]
    [DecidableEq Γ] [DecidableEq Δ] [DecidableEq K]
    {m : A → ℝ} (hm : IsPMF m) (f : A → Γ) (g : A → Δ) (u : Δ → K) :
    condH f (fun x => (g x, u (g x))) m = condH f g m := by
  let encG : Δ → Δ × K := fun y => (y, u y)
  let decG : Δ × K → Δ := Prod.fst
  have hleftG : Function.LeftInverse decG encG := fun _ => rfl
  have hg : Hvar (fun x => (g x, u (g x))) m = Hvar g m := by
    simpa [encG, Function.comp_def] using
      Hvar_eq_of_leftInverse hm g encG decG hleftG
  let encFG : Γ × Δ → Γ × (Δ × K) := fun y => (y.1, y.2, u y.2)
  let decFG : Γ × (Δ × K) → Γ × Δ := fun y => (y.1, y.2.1)
  have hleftFG : Function.LeftInverse decFG encFG := fun _ => rfl
  have hfg :
      Hvar (fun x => (f x, (g x, u (g x)))) m =
        Hvar (fun x => (f x, g x)) m := by
    simpa [encFG, Function.comp_def] using
      Hvar_eq_of_leftInverse hm (fun x => (f x, g x)) encFG decFG hleftFG
  unfold condH
  rw [hg, hfg]

lemma condH_equiv_right
    {A Γ Δ K : Type*} [Fintype A] [Fintype Γ] [Fintype Δ] [Fintype K]
    [DecidableEq Γ] [DecidableEq Δ] [DecidableEq K]
    {m : A → ℝ} (hm : IsPMF m) (f : A → Γ) (g : A → Δ) (e : Δ ≃ K) :
    condH f (fun x => e (g x)) m = condH f g m := by
  have hg := Hvar_equiv hm g e
  let ep : Γ × Δ ≃ Γ × K := Equiv.prodCongr (Equiv.refl Γ) e
  have hfg := Hvar_equiv hm (fun x => (f x, g x)) ep
  change Hvar (fun x => e (g x)) m = Hvar g m at hg
  change Hvar (fun x => (f x, e (g x))) m =
    Hvar (fun x => (f x, g x)) m at hfg
  unfold condH
  rw [hg, hfg]

lemma condH_eq_sum_H_fibers
    {A Γ K : Type*} [Fintype A] [Fintype Γ] [Fintype K]
    [DecidableEq Γ] [DecidableEq K]
    {m : A → ℝ} (hm : IsPMF m) (f : A → Γ) (h : A → K) :
    condH f h m =
      ∑ k, H (push f (fun x => if h x = k then m x else 0)) := by
  have hdecomp := Hvar_pair_eq_sum_fibers hm f h
  unfold condH
  rw [hdecomp]
  ring

lemma cellMass_mul_componentCellPrior
    (ε : D.L.ι → ℝ) (a b : D.L.ι) :
    cellMass D ε a * componentCellPrior D ε a b =
      D.L.prior b * componentCellMass D ε a b := by
  by_cases hmass : cellMass D ε a = 0
  · have hcm : componentCellMass D ε a b = 0 :=
      (componentCellMass_eq_zero_iff D ε a b).2 hmass
    simp [hmass, hcm]
  · simp only [componentCellPrior, hmass, if_false]
    field_simp

lemma push_latent_fst_joint_local
    {r : α × β → ℝ} (V : Latent r) :
    push (fun q : V.ι × (α × β) => q.1) V.joint = V.prior := by
  funext b
  have hcomp : ∀ c, ∑ z, V.comp c z = 1 := fun c => by
    simpa [mass] using (V.comp_isPMF c).total
  unfold push Latent.joint
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  calc
    (∑ x, ∑ z, if x = b then V.prior x * V.comp x z else 0) =
        ∑ x, if x = b then V.prior x * (∑ z, V.comp x z) else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : x = b
      · simp [hx, Finset.mul_sum]
      · simp [hx]
    _ = V.prior b := by simp [hcomp]

lemma push_winner_source_fiber
    (ε : D.L.ι → ℝ) (a : D.L.ι) :
    push (fun q : D.L.ι × (α × β) => q.1)
        (fun q => if winner D ε q.2 = a then D.L.joint q else 0) =
      fun b => D.L.prior b * componentCellMass D ε a b := by
  have hfiber :
      push (fun q : D.L.ι × (α × β) => q.1)
          (fun q => if winner D ε q.2 = a then D.L.joint q else 0) =
        push (fun q : D.L.ι × (α × β) => q.1)
          (fun q => cellMass D ε a * (cellSourceLatent D ε a).joint q) :=
    congrArg
    (push (fun q : D.L.ι × (α × β) => q.1))
    (cellSource_fiber D ε a)
  have hscale :
      push (fun q : D.L.ι × (α × β) => q.1)
          (fun q => cellMass D ε a * (cellSourceLatent D ε a).joint q) =
        fun b => cellMass D ε a * componentCellPrior D ε a b := by
    funext b
    have hs := congrFun
      (push_smul (fun q : D.L.ι × (α × β) => q.1)
        (cellSourceLatent D ε a).joint (cellMass D ε a)) b
    have hp := congrFun
      (push_latent_fst_joint_local (cellSourceLatent D ε a)) b
    change push (fun q : D.L.ι × (α × β) => q.1)
        (fun q => cellMass D ε a * (cellSourceLatent D ε a).joint q) b =
      cellMass D ε a * (cellSourceLatent D ε a).prior b
    rw [hs]
    exact congrArg (fun x : ℝ => cellMass D ε a * x) hp
  calc
    _ = (fun b => cellMass D ε a * componentCellPrior D ε a b) :=
      hfiber.trans hscale
    _ = _ := by
      funext b
      exact cellMass_mul_componentCellPrior D ε a b

lemma winner_condH_eq_cellEntropies (ε : D.L.ι → ℝ) :
    condH (fun q : D.L.ι × (α × β) => q.1)
        (fun q => winner D ε q.2) D.L.joint =
      ∑ a, cellMass D ε a * H (componentCellPrior D ε a) := by
  rw [condH_eq_sum_H_fibers D.L.joint_isPMF]
  simp_rw [push_winner_source_fiber D ε]
  apply Finset.sum_congr rfl
  intro a _
  have hfun :
      (fun b => D.L.prior b * componentCellMass D ε a b) =
        fun b => cellMass D ε a * componentCellPrior D ε a b := by
    funext b
    exact (cellMass_mul_componentCellPrior D ε a b).symm
  rw [hfun]
  exact H_smul (cellSourceLatent D ε a).prior_isPMF.isFinMeas
    (cellMass_nonneg D ε a)

lemma winner_condInfo_eq_condH_sub (ε : D.L.ι → ℝ) :
    condMI (fun q : D.L.ι × (α × β) => q.1) (fun q => q.2)
        (fun q => winner D ε q.2) D.L.joint =
      condH (fun q : D.L.ι × (α × β) => q.1)
          (fun q => winner D ε q.2) D.L.joint -
        condH (fun q : D.L.ι × (α × β) => q.1) (fun q => q.2) D.L.joint := by
  rw [condMI_eq_condH_sub_pair D.L.joint_isPMF]
  rw [condH_graph_right D.L.joint_isPMF
    (fun q : D.L.ι × (α × β) => q.1) (fun q => q.2) (winner D ε)]

private lemma resamplePrior_pos (a b : D.L.ι) :
    0 < resamplePrior D a b := by
  obtain ⟨z, _, hz⟩ : ∃ z ∈ (Finset.univ : Finset (α × β)), 0 < p z := by
    apply (Finset.sum_pos_iff_of_nonneg
      (fun z _ => D.isPMF.nonneg z)).mp
    have hsum : ∑ z, p z = 1 := by simpa [mass] using D.isPMF.total
    rw [hsum]
    norm_num
  have hcomp : 0 < D.L.comp a z := by
    apply lt_of_le_of_ne ((D.L.comp_isPMF a).nonneg z)
    exact Ne.symm ((component_eq_zero_iff D a z).not.mpr hz.ne')
  have hpost : 0 < D.post b z := post_pos_of_p_pos D b z hz
  unfold resamplePrior
  apply Finset.sum_pos'
  · intro z _
    exact mul_nonneg ((D.L.comp_isPMF a).nonneg z) (post_nonneg D b z)
  · exact ⟨z, Finset.mem_univ z, mul_pos hcomp hpost⟩

private lemma prior_mul_resamplePrior_comm (a b : D.L.ι) :
    D.L.prior b * resamplePrior D b a =
      D.L.prior a * resamplePrior D a b := by
  unfold resamplePrior
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  calc
    D.L.prior b * (D.L.comp b z * D.post a z) =
        (D.L.prior b * D.L.comp b z) * D.post a z := by ring
    _ = (p z * D.post b z) * D.post a z := by rw [p_mul_post D b z]
    _ = (p z * D.post a z) * D.post b z := by ring
    _ = (D.L.prior a * D.L.comp a z) * D.post b z := by
      rw [p_mul_post D a z]
    _ = D.L.prior a * (D.L.comp a z * D.post b z) := by ring

private lemma push_replica_l₁_fiber (a : D.L.ι) :
    push (fun u : D.L.ι × D.L.ι × D.L.ι × (α × β) => u.1)
        (fun u => if u.2.1 = a then replicaLaw D u else 0) =
      fun b => D.L.prior a * resamplePrior D a b := by
  funext b
  unfold push
  rw [Finset.sum_filter, sum_replica_domain D]
  change (∑ l₀, ∑ l₁, ∑ l₂, ∑ z,
      if l₀ = b then
        if l₁ = a then replicaLaw D (l₀, l₁, l₂, z) else 0
      else 0) = _
  have hcollapse :
      (∑ l₀, ∑ l₁, ∑ l₂, ∑ z,
        if l₀ = b then
          if l₁ = a then replicaLaw D (l₀, l₁, l₂, z) else 0
        else 0) =
      ∑ l₂, ∑ z, replicaLaw D (b, a, l₂, z) := by
    calc
      _ = ∑ l₁, ∑ l₂, ∑ z,
          if b = b then
            if l₁ = a then replicaLaw D (b, l₁, l₂, z) else 0
          else 0 := by
        apply Fintype.sum_eq_single b
        intro l₀ hl₀
        simp [hl₀]
      _ = ∑ l₁, ∑ l₂, ∑ z,
          if l₁ = a then replicaLaw D (b, l₁, l₂, z) else 0 := by simp
      _ = ∑ l₂, ∑ z,
          if a = a then replicaLaw D (b, a, l₂, z) else 0 := by
        apply Fintype.sum_eq_single a
        intro l₁ hl₁
        simp [hl₁]
      _ = ∑ l₂, ∑ z, replicaLaw D (b, a, l₂, z) := by simp
  rw [hcollapse, Finset.sum_comm]
  simp_rw [sum_replica_l₂ D]
  unfold resamplePrior
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  calc
    p z * D.post b z * D.post a z =
        (p z * D.post a z) * D.post b z := by ring
    _ = (D.L.prior a * D.L.comp a z) * D.post b z := by
      rw [p_mul_post D a z]
    _ = D.L.prior a * (D.L.comp a z * D.post b z) := by ring

private lemma replica_condH_eq_resampleEntropies :
    condH
        (fun u : D.L.ι × D.L.ι × D.L.ι × (α × β) => u.1)
        (fun u => u.2.1) (replicaLaw D) =
      ∑ a, D.L.prior a * H (resamplePrior D a) := by
  rw [condH_eq_sum_H_fibers (replicaLaw_isPMF D)]
  simp_rw [push_replica_l₁_fiber D]
  apply Finset.sum_congr rfl
  intro a _
  exact H_smul (resampleLatent D a).prior_isPMF.isFinMeas
    (D.L.prior_isPMF.nonneg a)

lemma integrable_componentCellMass
    (a b : D.L.ι) :
    Integrable (fun ε => componentCellMass D ε a b) (seedLaw D.L.ι) := by
  let F : ((α × β) → D.L.ι) → ℝ := fun A =>
    ∑ z ∈ Finset.univ.filter (fun z => A z = a), D.L.comp b z
  simpa only [F, componentCellMass, cell] using integrable_winner_code D F

lemma integral_winner_component
    (z : α × β) (a b : D.L.ι) :
    (∫ ε, (if winner D ε z = a then D.L.comp b z else 0)
        ∂(seedLaw D.L.ι)) =
      D.L.comp b z * D.post a z := by
  by_cases hpz : p z = 0
  · have hcomp : D.L.comp b z = 0 := (component_eq_zero_iff D b z).2 hpz
    simp [hcomp]
  · have hz : 0 < p z := lt_of_le_of_ne (D.isPMF.nonneg z) (Ne.symm hpz)
    have hfun :
        (fun ε => if winner D ε z = a then D.L.comp b z else 0) =
          fun ε => D.L.comp b z *
            (if winner D ε z = a then (1 : ℝ) else 0) := by
      funext ε
      by_cases hwin : winner D ε z = a <;> simp [hwin]
    rw [hfun, integral_const_mul, winner_probability D z hz a]

lemma integral_cellSource_weight (a b : D.L.ι) :
    (∫ ε, cellMass D ε a * componentCellPrior D ε a b
        ∂(seedLaw D.L.ι)) =
      D.L.prior a * resamplePrior D a b := by
  have hfun :
      (fun ε => cellMass D ε a * componentCellPrior D ε a b) =
        fun ε => D.L.prior b * componentCellMass D ε a b := by
    funext ε
    exact cellMass_mul_componentCellPrior D ε a b
  rw [hfun, integral_const_mul]
  have hcm :
      (∫ ε, componentCellMass D ε a b ∂(seedLaw D.L.ι)) =
        resamplePrior D b a := by
    unfold componentCellMass
    simp only [cell, Finset.sum_filter]
    rw [integral_finsetSum Finset.univ]
    · simp_rw [integral_winner_component D]
      rfl
    · intro z _
      let F : ((α × β) → D.L.ι) → ℝ := fun A =>
        if A z = a then D.L.comp b z else 0
      simpa only [F] using integrable_winner_code D F
  rw [hcm, prior_mul_resamplePrior_comm D a b]

lemma winner_condH_le_crossEntropy (ε : D.L.ι → ℝ) :
    condH (fun q : D.L.ι × (α × β) => q.1)
        (fun q => winner D ε q.2) D.L.joint ≤
      ∑ a, ∑ b,
        (cellMass D ε a * componentCellPrior D ε a b) *
          lg (1 / resamplePrior D a b) := by
  rw [winner_condH_eq_cellEntropies D ε]
  apply Finset.sum_le_sum
  intro a _
  have hcross := H_le_crossEntropy
    (cellSourceLatent D ε a).prior_isPMF
    (resampleLatent D a).prior_isPMF
    (fun b _ => (resamplePrior_pos D a b).ne')
  have hmul := mul_le_mul_of_nonneg_left hcross (cellMass_nonneg D ε a)
  calc
    cellMass D ε a * H (componentCellPrior D ε a) ≤
        cellMass D ε a *
          (∑ b, componentCellPrior D ε a b *
            lg (1 / resamplePrior D a b)) := hmul
    _ = ∑ b, (cellMass D ε a * componentCellPrior D ε a b) *
          lg (1 / resamplePrior D a b) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      ring

lemma integrable_winnerCondH :
    Integrable
      (fun ε => condH (fun q : D.L.ι × (α × β) => q.1)
        (fun q => winner D ε q.2) D.L.joint)
      (seedLaw D.L.ι) := by
  let F : ((α × β) → D.L.ι) → ℝ := fun A =>
    condH (fun q : D.L.ι × (α × β) => q.1) (fun q => A q.2) D.L.joint
  simpa only [F] using integrable_winner_code D F

lemma integrable_cellCrossEntropy :
    Integrable
      (fun ε => ∑ a, ∑ b,
        (cellMass D ε a * componentCellPrior D ε a b) *
          lg (1 / resamplePrior D a b))
      (seedLaw D.L.ι) := by
  have heq :
      (fun ε => ∑ a, ∑ b,
        (cellMass D ε a * componentCellPrior D ε a b) *
          lg (1 / resamplePrior D a b)) =
      fun ε => ∑ a, ∑ b,
        (D.L.prior b * componentCellMass D ε a b) *
          lg (1 / resamplePrior D a b) := by
    funext ε
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    rw [cellMass_mul_componentCellPrior D ε a b]
  rw [heq]
  apply integrable_finsetSum Finset.univ
  intro a _
  apply integrable_finsetSum Finset.univ
  intro b _
  have h := (integrable_componentCellMass D a b).const_mul
    (D.L.prior b * lg (1 / resamplePrior D a b))
  simpa only [mul_assoc, mul_left_comm, mul_comm] using h

lemma average_winner_condH_le_replica_condH :
    (∫ ε, condH (fun q : D.L.ι × (α × β) => q.1)
        (fun q => winner D ε q.2) D.L.joint ∂(seedLaw D.L.ι)) ≤
      condH
        (fun u : D.L.ι × D.L.ι × D.L.ι × (α × β) => u.1)
        (fun u => u.2.1) (replicaLaw D) := by
  have hleft := integrable_winnerCondH D
  have hright := integrable_cellCrossEntropy D
  have hmono :
      (∫ ε, condH (fun q : D.L.ι × (α × β) => q.1)
          (fun q => winner D ε q.2) D.L.joint ∂(seedLaw D.L.ι)) ≤
        ∫ ε, (∑ a, ∑ b,
          (cellMass D ε a * componentCellPrior D ε a b) *
            lg (1 / resamplePrior D a b)) ∂(seedLaw D.L.ι) :=
    integral_mono hleft hright (winner_condH_le_crossEntropy D)
  have hweight (a b : D.L.ι) :
      Integrable
        (fun ε => cellMass D ε a * componentCellPrior D ε a b)
        (seedLaw D.L.ι) := by
    have h := (integrable_componentCellMass D a b).const_mul (D.L.prior b)
    convert h using 1
    funext ε
    exact cellMass_mul_componentCellPrior D ε a b
  have hterm (a b : D.L.ι) :
      Integrable
        (fun ε => (cellMass D ε a * componentCellPrior D ε a b) *
          lg (1 / resamplePrior D a b))
        (seedLaw D.L.ι) := by
    have h := (hweight a b).const_mul (lg (1 / resamplePrior D a b))
    simpa only [mul_comm] using h
  have hinner (a : D.L.ι) :
      Integrable
        (fun ε => ∑ b,
          (cellMass D ε a * componentCellPrior D ε a b) *
            lg (1 / resamplePrior D a b))
        (seedLaw D.L.ι) := by
    exact integrable_finsetSum Finset.univ fun b _ => hterm a b
  calc
    (∫ ε, condH (fun q : D.L.ι × (α × β) => q.1)
        (fun q => winner D ε q.2) D.L.joint ∂(seedLaw D.L.ι)) ≤
      ∫ ε, (∑ a, ∑ b,
        (cellMass D ε a * componentCellPrior D ε a b) *
          lg (1 / resamplePrior D a b)) ∂(seedLaw D.L.ι) := hmono
    _ = ∑ a, ∫ ε, (∑ b,
          (cellMass D ε a * componentCellPrior D ε a b) *
            lg (1 / resamplePrior D a b)) ∂(seedLaw D.L.ι) := by
      rw [integral_finsetSum Finset.univ]
      exact fun a _ => hinner a
    _ = ∑ a, ∑ b, ∫ ε,
          ((cellMass D ε a * componentCellPrior D ε a b) *
            lg (1 / resamplePrior D a b)) ∂(seedLaw D.L.ι) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [integral_finsetSum Finset.univ]
      exact fun b _ => hterm a b
    _ = ∑ a, ∑ b,
          (D.L.prior a * resamplePrior D a b) *
            lg (1 / resamplePrior D a b) := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      rw [integral_mul_const, integral_cellSource_weight D a b]
    _ = ∑ a, D.L.prior a * H (resamplePrior D a) := by
      apply Finset.sum_congr rfl
      intro a _
      have hmass : mass (resamplePrior D a) = 1 := by
        unfold mass
        exact sum_resamplePrior D a
      rw [H, hmass, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      ring
    _ = condH
        (fun u : D.L.ι × D.L.ι × D.L.ι × (α × β) => u.1)
        (fun u => u.2.1) (replicaLaw D) :=
      (replica_condH_eq_resampleEntropies D).symm

lemma condH_eq_of_pair_push_eq
    {A A' Γ Δ : Type*} [Fintype A] [Fintype A'] [Fintype Γ] [Fintype Δ]
    [DecidableEq Γ] [DecidableEq Δ]
    (m : A → ℝ) (n : A' → ℝ) (f : A → Γ) (g : A → Δ)
    (f' : A' → Γ) (g' : A' → Δ)
    (hpair : push (fun x => (f x, g x)) m =
      push (fun x => (f' x, g' x)) n) :
    condH f g m = condH f' g' n := by
  have hg : push g m = push g' n := by
    calc
      push g m = push Prod.snd (push (fun x => (f x, g x)) m) := by
        symm
        simpa [Function.comp_def] using
          (push_push (fun x => (f x, g x)) Prod.snd m)
      _ = push Prod.snd (push (fun x => (f' x, g' x)) n) := by rw [hpair]
      _ = push g' n := by
        simpa [Function.comp_def] using
          (push_push (fun x => (f' x, g' x)) Prod.snd n)
  unfold condH Hvar
  rw [hpair, hg]

private lemma replica_condH_l₀z_eq_joint :
    condH
        (fun u : D.L.ι × D.L.ι × D.L.ι × (α × β) => u.1)
        (fun u => u.2.2.2) (replicaLaw D) =
      condH (fun q : D.L.ι × (α × β) => q.1) (fun q => q.2)
        D.L.joint := by
  have hpair :
      push (fun u : D.L.ι × D.L.ι × D.L.ι × (α × β) =>
        (u.1, u.2.2.2)) (replicaLaw D) =
      push (fun q : D.L.ι × (α × β) => (q.1, q.2)) D.L.joint := by
    calc
      _ = D.L.joint := push_replica_l₀z D
      _ = _ := (push_id_local D.L.joint).symm
  exact condH_eq_of_pair_push_eq (replicaLaw D) D.L.joint
    (fun u => u.1) (fun u => u.2.2.2) (fun q => q.1) (fun q => q.2) hpair

lemma bZ_eq_condH_sub :
    bZ D =
      condH
          (fun u : D.L.ι × D.L.ι × D.L.ι × (α × β) => u.1)
          (fun u => u.2.1) (replicaLaw D) -
        condH (fun q : D.L.ι × (α × β) => q.1) (fun q => q.2)
          D.L.joint := by
  have hmarkov := condMI_eq_condH_sub_pair (replicaLaw_isPMF D)
    (fun u : D.L.ι × D.L.ι × D.L.ι × (α × β) => u.1)
    (fun u => u.2.1) (fun u => u.2.2.2)
  rw [replica_markov D] at hmarkov
  have hpair :
      condH
          (fun u : D.L.ι × D.L.ι × D.L.ι × (α × β) => u.1)
          (fun u => (u.2.1, u.2.2.2)) (replicaLaw D) =
        condH (fun u => u.1) (fun u => u.2.2.2) (replicaLaw D) := by
    linarith
  have hswap := condH_equiv_right (replicaLaw_isPMF D)
    (fun u : D.L.ι × D.L.ι × D.L.ι × (α × β) => u.1)
    (fun u => (u.2.1, u.2.2.2))
    (Equiv.prodComm D.L.ι (α × β))
  change condH (fun u : D.L.ι × D.L.ι × D.L.ι × (α × β) => u.1)
      (fun u => (u.2.2.2, u.2.1)) (replicaLaw D) =
    condH (fun u => u.1) (fun u => (u.2.1, u.2.2.2)) (replicaLaw D) at hswap
  unfold bZ
  rw [condMI_eq_condH_sub_pair (replicaLaw_isPMF D), hswap, hpair,
    replica_condH_l₀z_eq_joint D]

lemma average_winner_condInfo_le_bZ :
    (∫ ε, condMI
        (fun q : D.L.ι × (α × β) => q.1) (fun q => q.2)
        (fun q => winner D ε q.2) D.L.joint ∂(seedLaw D.L.ι)) ≤
      bZ D := by
  let c : ℝ := condH (fun q : D.L.ι × (α × β) => q.1)
    (fun q => q.2) D.L.joint
  have heq :
      (fun ε => condMI
        (fun q : D.L.ι × (α × β) => q.1) (fun q => q.2)
        (fun q => winner D ε q.2) D.L.joint) =
      fun ε => condH (fun q : D.L.ι × (α × β) => q.1)
        (fun q => winner D ε q.2) D.L.joint - c := by
    funext ε
    exact winner_condInfo_eq_condH_sub D ε
  have hintegral :
      (∫ ε, condMI
          (fun q : D.L.ι × (α × β) => q.1) (fun q => q.2)
          (fun q => winner D ε q.2) D.L.joint ∂(seedLaw D.L.ι)) =
        (∫ ε, condH (fun q : D.L.ι × (α × β) => q.1)
          (fun q => winner D ε q.2) D.L.joint ∂(seedLaw D.L.ι)) - c := by
    rw [heq, integral_sub (integrable_winnerCondH D) (integrable_const c)]
    simp
  rw [hintegral, bZ_eq_condH_sub D]
  exact sub_le_sub_right (average_winner_condH_le_replica_condH D) c

/-- **Theorem 5.7** (posterior-resampling comparison, *cell-defect-posterior-comparison*):
`𝒟_w(p,L) ≤ R_cell + b_Z`.

The one genuinely continuous statement here. Its proof is four steps:
fusion within a cell, data processing, removing the
seed via `L₀ ⟂ ε ∣ (Z,A)`, and the calibration coupling `(L₀,A,Z) ≟ (L₀,L₁,Z)`.
Step (iv) is Lemma 4.2 and is where the continuous seed is discharged back into
the finite replica coupling. -/
theorem Dwdefect_le_Rcell_add_bZ :
    Dwdefect D ≤ Rcell D + bZ D := by
  calc
    Dwdefect D ≤ Rcell D +
        ∫ ε, condMI
          (fun q : D.L.ι × (α × β) => q.1) (fun q => q.2)
          (fun q => winner D ε q.2) D.L.joint ∂(seedLaw D.L.ι) :=
      Dwdefect_le_Rcell_add_integral_condInfo D
    _ ≤ Rcell D + bZ D :=
      add_le_add_right (average_winner_condInfo_le_bZ D) (Rcell D)

end Replica

end stoch_to_det
