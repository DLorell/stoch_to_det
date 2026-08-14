import stoch_to_det.SharedRace.Clock
import stoch_to_det.SharedRace.BetaGamma
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Probability.Independence.Integration

/-!
# One-coordinate law of normalized iid exponential clocks

The key input is proved directly from exponential tails and product
independence: one normalized coordinate has the `Beta(1,k-1)` tail.  This
avoids depending on a Dirichlet-distribution API.
-/

namespace stoch_to_det
namespace SharedRace

open Finset MeasureTheory ProbabilityTheory Set

variable {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]

omit [DecidableEq κ] [Nonempty κ] in
lemma measurable_clockTotal : Measurable (clockTotal : (κ → ℝ) → ℝ) := by
  unfold clockTotal
  fun_prop

omit [DecidableEq κ] [Nonempty κ] in
lemma measurable_normClock (i : κ) :
    Measurable (fun E : κ → ℝ => normClock E i) := by
  unfold normClock
  exact (measurable_pi_apply i).div measurable_clockTotal

omit [DecidableEq κ] [Nonempty κ] in
/-- Every coordinate of the iid exponential clock is strictly positive
almost surely. -/
lemma ae_clockLaw_pos : ∀ᵐ E ∂(clockLaw κ), ∀ i, 0 < E i := by
  let _ : IsProbabilityMeasure (expMeasure 1) :=
    isProbabilityMeasure_expMeasure zero_lt_one
  have hone : ∀ᵐ x : ℝ ∂(expMeasure 1), 0 < x := by
    have hnot := measure_eq_zero_iff_ae_notMem.mp expMeasure_one_Iic_zero
    filter_upwards [hnot] with x hx
    simpa only [Set.mem_Iic, not_le] using hx
  unfold clockLaw
  exact ae_forall_fintype fun i =>
    Measure.tendsto_eval_ae_ae.eventually hone

omit [DecidableEq κ] in
lemma ae_normClock_nonneg (i : κ) :
    0 ≤ᵐ[clockLaw κ] fun E => normClock E i := by
  filter_upwards [ae_clockLaw_pos (κ := κ)] with E hE
  exact normClock_nonneg E hE i

omit [DecidableEq κ] in
lemma ae_normClock_le_one (i : κ) :
    (fun E => normClock E i) ≤ᵐ[clockLaw κ] fun _ => 1 := by
  filter_upwards [ae_clockLaw_pos (κ := κ)] with E hE
  exact normClock_le_one E hE i

omit [Nonempty κ] in
/-- Tail law of one normalized iid exponential coordinate. -/
theorem clockLaw_normClock_Ioi (i : κ) (t : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t < 1) :
    clockLaw κ {E | t < normClock E i} =
      ENNReal.ofReal ((1 - t) ^ (Fintype.card κ - 1)) := by
  let _ : IsProbabilityMeasure (expMeasure 1) :=
    isProbabilityMeasure_expMeasure zero_lt_one
  let _ : ∀ _ : {j : κ // j ≠ i}, IsProbabilityMeasure (expMeasure 1) :=
    fun _ => isProbabilityMeasure_expMeasure zero_lt_one
  let e : Option {j : κ // j ≠ i} ≃ κ := Equiv.optionSubtypeNe i
  let f := (MeasurableEquiv.piOptionEquivProd
    (fun _ : Option {j : κ // j ≠ i} => ℝ)).symm
  let g := MeasurableEquiv.piCongrLeft (fun _ : κ => ℝ) e
  let q := (Measure.pi (fun _ : {j : κ // j ≠ i} => expMeasure 1)).prod
    (expMeasure 1)
  have hfirst :
      Measure.map f q =
        Measure.pi (fun _ : Option {j : κ // j ≠ i} => expMeasure 1) := by
    dsimp [f, q]
    exact Measure.pi_map_piOptionEquivProd
      (fun _ : Option {j : κ // j ≠ i} => expMeasure 1)
  have hsecond :
      Measure.map g
          (Measure.pi (fun _ : Option {j : κ // j ≠ i} => expMeasure 1)) =
        Measure.pi (fun _ : κ => expMeasure 1) := by
    dsimp [g]
    simpa [e] using Measure.pi_map_piCongrLeft e
      (fun _ : κ => expMeasure 1)
  have hmap : Measure.map (g ∘ f) q = clockLaw κ := by
    unfold clockLaw
    calc
      Measure.map (g ∘ f) q = Measure.map g (Measure.map f q) :=
        (Measure.map_map g.measurable f.measurable).symm
      _ = _ := by rw [hfirst, hsecond]
  have heval_other (x : {j : κ // j ≠ i} → ℝ) (y : ℝ)
      (j : {j : κ // j ≠ i}) : (g (f (x, y))) j.1 = x j := by
    have hf_pair := (MeasurableEquiv.piOptionEquivProd
      (fun _ : Option {j : κ // j ≠ i} => ℝ)).apply_symm_apply (x, y)
    have hf_some : f (x, y) (some j) = x j :=
      congrFun (congrArg Prod.fst hf_pair) j
    dsimp [g]
    rw [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]
    simp [e, Equiv.optionSubtypeNe_symm_of_ne j.2, hf_some]
  have heval_i (x : {j : κ // j ≠ i} → ℝ) (y : ℝ) :
      (g (f (x, y))) i = y := by
    have hf_pair := (MeasurableEquiv.piOptionEquivProd
      (fun _ : Option {j : κ // j ≠ i} => ℝ)).apply_symm_apply (x, y)
    have hf_none : f (x, y) none = y := congrArg Prod.snd hf_pair
    dsimp [g]
    rw [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]
    simp [e, hf_none]
  have htotal (x : {j : κ // j ≠ i} → ℝ) (y : ℝ) :
      clockTotal (g (f (x, y))) = y + ∑ j, x j := by
    unfold clockTotal
    rw [Fintype.sum_eq_add_sum_subtype_ne (g (f (x, y))) i,
      heval_i]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    exact heval_other x y j
  have hset : MeasurableSet {E : κ → ℝ | t < normClock E i} :=
    measurableSet_lt measurable_const (measurable_normClock i)
  rw [← hmap, Measure.map_apply (g.measurable.comp f.measurable) hset]
  have hpre : MeasurableSet
      ((g ∘ f) ⁻¹' {E : κ → ℝ | t < normClock E i}) :=
    hset.preimage (g.measurable.comp f.measurable)
  rw [Measure.prod_apply hpre]
  let c : ℝ := t / (1 - t)
  have h1mt : 0 < 1 - t := sub_pos.mpr ht1
  have hc0 : 0 ≤ c := div_nonneg ht0 h1mt.le
  have hone : ∀ᵐ y : ℝ ∂(expMeasure 1), 0 < y := by
    have hnot := measure_eq_zero_iff_ae_notMem.mp expMeasure_one_Iic_zero
    filter_upwards [hnot] with y hy
    simpa only [Set.mem_Iic, not_le] using hy
  have hpos_other :
      ∀ᵐ x ∂Measure.pi (fun _ : {j : κ // j ≠ i} => expMeasure 1),
        ∀ j, 0 < x j := by
    exact ae_forall_fintype fun j =>
      Measure.tendsto_eval_ae_ae.eventually hone
  have hsection :
      ∀ᵐ x ∂Measure.pi (fun _ : {j : κ // j ≠ i} => expMeasure 1),
        expMeasure 1
            (Prod.mk x ⁻¹' ((g ∘ f) ⁻¹' {E : κ → ℝ | t < normClock E i})) =
          ENNReal.ofReal (Real.exp (-(c * ∑ j, x j))) := by
    filter_upwards [hpos_other] with x hx
    have hsum0 : 0 ≤ ∑ j, x j :=
      Finset.sum_nonneg fun j _ => (hx j).le
    have hsection_eq :
        expMeasure 1
            (Prod.mk x ⁻¹' ((g ∘ f) ⁻¹' {E : κ → ℝ | t < normClock E i})) =
          expMeasure 1 (Set.Ioi (c * ∑ j, x j)) := by
      apply measure_congr
      filter_upwards [hone] with y hy
      apply propext
      change (t < normClock (g (f (x, y))) i ↔ c * ∑ j, x j < y)
      rw [show normClock (g (f (x, y))) i = y / (y + ∑ j, x j) by
        unfold normClock
        rw [heval_i, htotal]]
      have htotal_pos : 0 < y + ∑ j, x j := add_pos_of_pos_of_nonneg hy hsum0
      have hc_eq : c * (∑ j, x j) = t * (∑ j, x j) / (1 - t) := by
        dsimp [c]
        field_simp [h1mt.ne']
      rw [hc_eq]
      constructor
      · intro h
        have hcross := (lt_div_iff₀ htotal_pos).mp h
        apply (div_lt_iff₀ h1mt).2
        nlinarith
      · intro h
        have hcross := (div_lt_iff₀ h1mt).1 h
        apply (lt_div_iff₀ htotal_pos).2
        nlinarith
    rw [hsection_eq, expMeasure_one_Ioi]
    exact mul_nonneg hc0 hsum0
  rw [lintegral_congr_ae hsection]
  let X : {j : κ // j ≠ i} →
      (({j : κ // j ≠ i} → ℝ) → ENNReal) :=
    fun j x => ENNReal.ofReal (Real.exp (-(c * x j)))
  have hfactor (x : {j : κ // j ≠ i} → ℝ) :
      ENNReal.ofReal (Real.exp (-(c * ∑ j, x j))) = ∏ j, X j x := by
    dsimp [X]
    rw [← ENNReal.ofReal_prod_of_nonneg
      (fun j _ => Real.exp_nonneg (-(c * x j))), ← Real.exp_sum]
    congr 2
    rw [Finset.sum_neg_distrib, Finset.mul_sum]
  have hindep_eval :
      iIndepFun (fun j (x : {j : κ // j ≠ i} → ℝ) => x j)
        (Measure.pi (fun _ : {j : κ // j ≠ i} => expMeasure 1)) := by
    simpa only [id_eq] using
      (iIndepFun_pi (μ := fun _ : {j : κ // j ≠ i} => expMeasure 1)
        (X := fun _ => id) (fun _ => aemeasurable_id))
  have hindep :
      iIndepFun X
        (Measure.pi (fun _ : {j : κ // j ≠ i} => expMeasure 1)) := by
    simpa [X, Function.comp_def] using hindep_eval.comp
      (fun _ y => ENNReal.ofReal (Real.exp (-(c * y)))) (fun _ => by fun_prop)
  have hprodIntegral := lintegral_prod_eq_prod_lintegral_of_indepFun
    (Finset.univ : Finset {j : κ // j ≠ i}) X hindep (fun _ => by fun_prop)
  calc
    (∫⁻ x, ENNReal.ofReal (Real.exp (-(c * ∑ j, x j)))
        ∂Measure.pi (fun _ : {j : κ // j ≠ i} => expMeasure 1)) =
        ∫⁻ x, ∏ j, X j x
          ∂Measure.pi (fun _ : {j : κ // j ≠ i} => expMeasure 1) := by
      apply lintegral_congr
      exact hfactor
    _ = ∏ j, ∫⁻ x, X j x
          ∂Measure.pi (fun _ : {j : κ // j ≠ i} => expMeasure 1) := by
      simpa using hprodIntegral
    _ = ∏ _j : {j : κ // j ≠ i}, ENNReal.ofReal (1 / (1 + c)) := by
      apply Finset.prod_congr rfl
      intro j _
      calc
        (∫⁻ x, X j x
            ∂Measure.pi (fun _ : {j : κ // j ≠ i} => expMeasure 1)) =
            ∫⁻ y, ENNReal.ofReal (Real.exp (-(c * y))) ∂(expMeasure 1) := by
          dsimp [X]
          have hmeas : Measurable
              (fun y : ℝ => ENNReal.ofReal (Real.exp (-(c * y)))) := by
            fun_prop
          exact (measurePreserving_eval
            (fun _ : {j : κ // j ≠ i} => expMeasure 1) j).lintegral_comp
              hmeas
        _ = ENNReal.ofReal (1 / (1 + c)) := expMeasure_one_laplace c hc0
    _ = ENNReal.ofReal ((1 - t) ^ (Fintype.card κ - 1)) := by
      have hc : 1 / (1 + c) = 1 - t := by
        dsimp [c]
        field_simp [h1mt.ne']
        ring
      rw [Finset.prod_const, hc]
      have hcard : Fintype.card {j : κ // j ≠ i} = Fintype.card κ - 1 := by
        simp [Fintype.card_subtype_compl]
      rw [Finset.card_univ, hcard]
      exact (ENNReal.ofReal_pow h1mt.le (Fintype.card κ - 1)).symm

omit [Nonempty κ] in
/-- Scaled form of `clockLaw_normClock_Ioi`: `k U_i` has the
`k * Beta(1,k-1)` tail on `(0,k)`. -/
theorem clockLaw_scaledNormClock_Ioi (i : κ) (s : ℝ)
    (hk : 2 ≤ Fintype.card κ) (hs0 : 0 ≤ s)
    (hsk : s < Fintype.card κ) :
    (clockLaw κ).map
        (fun E => (Fintype.card κ : ℝ) * normClock E i) (Set.Ioi s) =
      ENNReal.ofReal
        ((1 - s / (Fintype.card κ : ℝ)) ^ (Fintype.card κ - 1)) := by
  have hkpos : (0 : ℝ) < Fintype.card κ := by
    exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2) hk)
  have hmapMeas : Measurable
      (fun E : κ → ℝ => (Fintype.card κ : ℝ) * normClock E i) :=
    measurable_const.mul (measurable_normClock i)
  rw [Measure.map_apply hmapMeas measurableSet_Ioi]
  have hpre :
      (fun E : κ → ℝ => (Fintype.card κ : ℝ) * normClock E i) ⁻¹'
          Set.Ioi s =
        {E | s / (Fintype.card κ : ℝ) < normClock E i} := by
    ext E
    simp only [Set.mem_preimage, Set.mem_Ioi, Set.mem_ofPred_eq]
    simpa [mul_comm] using
      (div_lt_iff₀ hkpos :
        s / (Fintype.card κ : ℝ) < normClock E i ↔
          s < normClock E i * (Fintype.card κ : ℝ)).symm
  rw [hpre]
  exact clockLaw_normClock_Ioi i (s / (Fintype.card κ : ℝ))
    (div_nonneg hs0 hkpos.le) ((div_lt_one hkpos).2 hsk)

/-! ### Explicit scaled-Beta density interface -/

/-- The probability measure with the literal density used by
`SharedRace.betaOneExpMoment`. -/
noncomputable def scaledBetaOneLaw (k : ℕ) : Measure ℝ :=
  (volume.restrict (Set.Ioc 0 (k : ℝ))).withDensity
    (fun x => ENNReal.ofReal (SharedRace.betaOneDensity k x))

private lemma hasDerivAt_one_sub_div_clockLaw (k : ℕ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => 1 - y / (k : ℝ)) (-1 / (k : ℝ)) x := by
  convert (hasDerivAt_const x 1).sub
    ((hasDerivAt_id x).div_const (k : ℝ)) using 1
  all_goals first
    | rfl
    | simp [div_eq_mul_inv]

private lemma betaOneTailAnti_hasDerivAt (k : ℕ) (hk : 2 ≤ k) (x : ℝ) :
    HasDerivAt (fun y : ℝ => -(1 - y / (k : ℝ)) ^ (k - 1))
      (SharedRace.betaOneDensity k x) x := by
  have hbase := hasDerivAt_one_sub_div_clockLaw k x
  unfold SharedRace.betaOneDensity
  convert (hbase.pow (k - 1)).neg using 1
  all_goals first
    | rfl
    | (simp only [show (k - 1) - 1 = k - 2 by omega,
          Nat.cast_sub (show 1 ≤ k by omega), Nat.cast_one]
       field_simp [show (k : ℝ) ≠ 0 by positivity])

private lemma integral_betaOneDensity (k : ℕ) (hk : 2 ≤ k)
    {s : ℝ} (_hs0 : 0 ≤ s) (_hsk : s ≤ k) :
    (∫ x : ℝ in s..(k : ℝ), SharedRace.betaOneDensity k x) =
      (1 - s / (k : ℝ)) ^ (k - 1) := by
  have hint : IntervalIntegrable (SharedRace.betaOneDensity k) volume s (k : ℝ) := by
    exact (by
      unfold SharedRace.betaOneDensity
      fun_prop : Continuous (SharedRace.betaOneDensity k)).intervalIntegrable _ _
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := s) (b := (k : ℝ))
    (f := fun y : ℝ => -(1 - y / (k : ℝ)) ^ (k - 1))
    (f' := SharedRace.betaOneDensity k)
    (fun x hx => betaOneTailAnti_hasDerivAt k hk x) hint
  have hk0 : (k : ℝ) ≠ 0 := by positivity
  have hk1 : k - 1 ≠ 0 := by omega
  simpa [hk0, hk1] using hftc

/-- Tail of the literal scaled-Beta density. -/
lemma scaledBetaOneLaw_Ioi (k : ℕ) (hk : 2 ≤ k) (s : ℝ)
    (hs0 : 0 ≤ s) (hsk : s < k) :
    scaledBetaOneLaw k (Set.Ioi s) =
      ENNReal.ofReal ((1 - s / (k : ℝ)) ^ (k - 1)) := by
  have hsle : s ≤ (k : ℝ) := hsk.le
  have hdensity_nonneg : ∀ x ∈ Set.Ioc s (k : ℝ),
      0 ≤ SharedRace.betaOneDensity k x := by
    intro x hx
    unfold SharedRace.betaOneDensity
    have hkpos : (0 : ℝ) < k := by positivity
    exact mul_nonneg (div_nonneg (by positivity) hkpos.le)
      (pow_nonneg (sub_nonneg.mpr ((div_le_one hkpos).2 hx.2)) _)
  have hdensity_int : IntegrableOn (SharedRace.betaOneDensity k)
      (Set.Ioc s (k : ℝ)) := by
    exact ((by
      unfold SharedRace.betaOneDensity
      fun_prop : Continuous (SharedRace.betaOneDensity k)).intervalIntegrable
        s (k : ℝ)).1
  unfold scaledBetaOneLaw
  rw [withDensity_apply _ measurableSet_Ioi]
  change (∫⁻ x, ENNReal.ofReal (SharedRace.betaOneDensity k x)
      ∂((volume.restrict (Set.Ioc 0 (k : ℝ))).restrict (Set.Ioi s))) = _
  rw [Measure.restrict_restrict measurableSet_Ioi]
  have hinter : Set.Ioc 0 (k : ℝ) ∩ Set.Ioi s = Set.Ioc s (k : ℝ) := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Ioi]
    constructor
    · intro hx
      exact ⟨hx.2, hx.1.2⟩
    · intro hx
      exact ⟨⟨lt_of_le_of_lt hs0 hx.1, hx.2⟩, hx.1⟩
  rw [Set.inter_comm, hinter]
  rw [← ofReal_integral_eq_lintegral_ofReal hdensity_int
    (ae_restrict_of_forall_mem measurableSet_Ioc hdensity_nonneg)]
  congr 1
  rw [(intervalIntegral.integral_of_le hsle).symm,
    integral_betaOneDensity k hk hs0 hsle]

/-- The literal scaled-Beta density has total mass one. -/
lemma scaledBetaOneLaw_isProbability (k : ℕ) (hk : 2 ≤ k) :
    IsProbabilityMeasure (scaledBetaOneLaw k) := by
  constructor
  have hdensity_nonneg : ∀ x ∈ Set.Ioc (0 : ℝ) (k : ℝ),
      0 ≤ SharedRace.betaOneDensity k x := by
    intro x hx
    unfold SharedRace.betaOneDensity
    have hkpos : (0 : ℝ) < k := by positivity
    exact mul_nonneg (div_nonneg (by positivity) hkpos.le)
      (pow_nonneg (sub_nonneg.mpr ((div_le_one hkpos).2 hx.2)) _)
  have hdensity_int : IntegrableOn (SharedRace.betaOneDensity k)
      (Set.Ioc (0 : ℝ) (k : ℝ)) := by
    exact ((by
      unfold SharedRace.betaOneDensity
      fun_prop : Continuous (SharedRace.betaOneDensity k)).intervalIntegrable
        0 (k : ℝ)).1
  unfold scaledBetaOneLaw
  rw [withDensity_apply _ MeasurableSet.univ]
  change (∫⁻ x, ENNReal.ofReal (SharedRace.betaOneDensity k x)
      ∂((volume.restrict (Set.Ioc 0 (k : ℝ))).restrict Set.univ)) = 1
  rw [Measure.restrict_univ]
  rw [← ofReal_integral_eq_lintegral_ofReal hdensity_int
    (ae_restrict_of_forall_mem measurableSet_Ioc hdensity_nonneg)]
  rw [show (∫ x : ℝ in Set.Ioc 0 (k : ℝ),
      SharedRace.betaOneDensity k x) =
        ∫ x : ℝ in 0..(k : ℝ),
          SharedRace.betaOneDensity k x by
      exact (intervalIntegral.integral_of_le (by positivity)).symm]
  rw [integral_betaOneDensity k hk (by positivity) (by positivity)]
  simp

/-- One scaled normalized exponential coordinate has exactly the literal
`k * Beta(1,k-1)` density. -/
theorem clockLaw_scaledNormClock_map_eq_scaledBetaOneLaw (i : κ)
    (hk : 2 ≤ Fintype.card κ) :
    (clockLaw κ).map
        (fun E => (Fintype.card κ : ℝ) * normClock E i) =
      scaledBetaOneLaw (Fintype.card κ) := by
  let Y : (κ → ℝ) → ℝ :=
    fun E => (Fintype.card κ : ℝ) * normClock E i
  let μ : Measure ℝ := (clockLaw κ).map Y
  let ν : Measure ℝ := scaledBetaOneLaw (Fintype.card κ)
  have hY : Measurable Y :=
    measurable_const.mul (measurable_normClock i)
  let _ : IsProbabilityMeasure μ :=
    Measure.isProbabilityMeasure_map hY.aemeasurable
  let _ : IsProbabilityMeasure ν :=
    scaledBetaOneLaw_isProbability (Fintype.card κ) hk
  have hkpos : (0 : ℝ) < Fintype.card κ := by positivity
  have htail : ∀ s : ℝ, μ (Set.Ioi s) = ν (Set.Ioi s) := by
    intro s
    by_cases hs0 : 0 ≤ s
    · by_cases hsk : s < (Fintype.card κ : ℝ)
      · dsimp only [μ, ν, Y]
        rw [clockLaw_scaledNormClock_Ioi i s hk hs0 hsk,
          scaledBetaOneLaw_Ioi (Fintype.card κ) hk s hs0 hsk]
      · have hks : (Fintype.card κ : ℝ) ≤ s := le_of_not_gt hsk
        have hμzero : μ (Set.Ioi s) = 0 := by
          dsimp only [μ]
          rw [Measure.map_apply hY measurableSet_Ioi]
          apply measure_eq_zero_iff_ae_notMem.mpr
          filter_upwards [ae_normClock_le_one i] with E hE
          simp only [Set.mem_preimage, Set.mem_Ioi, not_lt]
          dsimp only [Y]
          have hscaled : (Fintype.card κ : ℝ) * normClock E i ≤
              (Fintype.card κ : ℝ) := by
            simpa using mul_le_mul_of_nonneg_left hE hkpos.le
          exact hscaled.trans hks
        have hνzero : ν (Set.Ioi s) = 0 := by
          dsimp only [ν]
          unfold scaledBetaOneLaw
          rw [withDensity_apply _ measurableSet_Ioi]
          change (∫⁻ x, ENNReal.ofReal
              (SharedRace.betaOneDensity (Fintype.card κ) x)
              ∂((volume.restrict (Set.Ioc 0 (Fintype.card κ : ℝ))).restrict
                (Set.Ioi s))) = 0
          rw [Measure.restrict_restrict measurableSet_Ioi]
          have hinter : Set.Ioi s ∩ Set.Ioc 0 (Fintype.card κ : ℝ) = ∅ := by
            ext x
            simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Ioc,
              Set.mem_empty_iff_false, iff_false]
            intro hx
            linarith [hx.1, hx.2.2, hks]
          rw [hinter, Measure.restrict_empty, lintegral_zero_measure]
        rw [hμzero, hνzero]
    · have hsneg : s < 0 := lt_of_not_ge hs0
      have hμone : μ (Set.Ioi s) = 1 := by
        dsimp only [μ]
        rw [Measure.map_apply hY measurableSet_Ioi]
        calc
          clockLaw κ (Y ⁻¹' Set.Ioi s) = clockLaw κ Set.univ := by
            apply measure_congr
            filter_upwards [ae_normClock_nonneg i] with E hE
            apply propext
            change (s < Y E ↔ True)
            dsimp only [Y]
            exact iff_true_intro (hsneg.trans_le (mul_nonneg hkpos.le hE))
          _ = 1 := measure_univ
      have hνzero : ν (Set.Iic s) = 0 := by
        dsimp only [ν]
        unfold scaledBetaOneLaw
        rw [withDensity_apply _ measurableSet_Iic]
        change (∫⁻ x, ENNReal.ofReal
            (SharedRace.betaOneDensity (Fintype.card κ) x)
            ∂((volume.restrict (Set.Ioc 0 (Fintype.card κ : ℝ))).restrict
              (Set.Iic s))) = 0
        rw [Measure.restrict_restrict measurableSet_Iic]
        have hinter : Set.Iic s ∩ Set.Ioc 0 (Fintype.card κ : ℝ) = ∅ := by
          ext x
          simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Ioc,
            Set.mem_empty_iff_false, iff_false]
          intro hx
          linarith [hx.1, hx.2.1, hsneg]
        rw [hinter, Measure.restrict_empty, lintegral_zero_measure]
      have hνone : ν (Set.Ioi s) = 1 := by
        rw [← Set.compl_Iic]
        rw [measure_compl measurableSet_Iic (by simp [hνzero]),
          measure_univ, hνzero]
        simp
      rw [hμone, hνone]
  change μ = ν
  apply Measure.ext_of_Iic μ ν
  intro s
  rw [← Set.compl_Ioi]
  rw [measure_compl measurableSet_Ioi (by finiteness),
    measure_compl measurableSet_Ioi (by finiteness),
    measure_univ, measure_univ, htail s]

/-- Integrating an exponential against the literal density gives exactly the
moment functional defined in `SharedRace`. -/
lemma integral_exp_scaledBetaOneLaw_eq_betaOneExpMoment (k : ℕ)
    (hk : 2 ≤ k) (lam : ℝ) :
    (∫ t : ℝ, Real.exp (lam * t) ∂(scaledBetaOneLaw k)) =
      SharedRace.betaOneExpMoment k lam := by
  have hdensity_nonneg : ∀ x ∈ Set.Ioc (0 : ℝ) (k : ℝ),
      0 ≤ SharedRace.betaOneDensity k x := by
    intro x hx
    unfold SharedRace.betaOneDensity
    have hkpos : (0 : ℝ) < k := by positivity
    exact mul_nonneg (div_nonneg (by positivity) hkpos.le)
      (pow_nonneg (sub_nonneg.mpr ((div_le_one hkpos).2 hx.2)) _)
  unfold scaledBetaOneLaw
  rw [integral_withDensity_eq_integral_toReal_smul
    (by
      exact ENNReal.measurable_ofReal.comp (by
        unfold SharedRace.betaOneDensity
        fun_prop))
    (by simp)]
  change (∫ t : ℝ in Set.Ioc 0 (k : ℝ),
      (ENNReal.ofReal (SharedRace.betaOneDensity k t)).toReal *
        Real.exp (lam * t)) = SharedRace.betaOneExpMoment k lam
  have hremove :
      (∫ t : ℝ in Set.Ioc 0 (k : ℝ),
          (ENNReal.ofReal (SharedRace.betaOneDensity k t)).toReal *
            Real.exp (lam * t)) =
        ∫ t : ℝ in Set.Ioc 0 (k : ℝ),
          Real.exp (lam * t) * SharedRace.betaOneDensity k t := by
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    dsimp only
    rw [ENNReal.toReal_ofReal (hdensity_nonneg t ht)]
    ring
  rw [hremove]
  unfold SharedRace.betaOneExpMoment
  exact (intervalIntegral.integral_of_le (by
    exact_mod_cast (Nat.zero_le k))).symm

/-- Exact exponential moment of one scaled normalized clock coordinate. -/
theorem clockLaw_scaledNormClock_expMoment_eq (i : κ)
    (hk : 2 ≤ Fintype.card κ) (lam : ℝ) :
    (∫ E : κ → ℝ,
        Real.exp (lam * ((Fintype.card κ : ℝ) * normClock E i))
        ∂(clockLaw κ)) =
      SharedRace.betaOneExpMoment (Fintype.card κ) lam := by
  let Y : (κ → ℝ) → ℝ :=
    fun E => (Fintype.card κ : ℝ) * normClock E i
  have hY : Measurable Y :=
    measurable_const.mul (measurable_normClock i)
  calc
    (∫ E : κ → ℝ,
        Real.exp (lam * ((Fintype.card κ : ℝ) * normClock E i))
        ∂(clockLaw κ)) =
        ∫ E : κ → ℝ, Real.exp (lam * Y E) ∂(clockLaw κ) := by rfl
    _ = ∫ t : ℝ, Real.exp (lam * t) ∂((clockLaw κ).map Y) :=
      (integral_map hY.aemeasurable (by
        have hcont : Continuous (fun t : ℝ => Real.exp (lam * t)) := by
          fun_prop
        exact hcont.stronglyMeasurable.aestronglyMeasurable)).symm
    _ = ∫ t : ℝ, Real.exp (lam * t)
        ∂(scaledBetaOneLaw (Fintype.card κ)) := by
      rw [show (clockLaw κ).map Y = scaledBetaOneLaw (Fintype.card κ) by
        exact clockLaw_scaledNormClock_map_eq_scaledBetaOneLaw i hk]
    _ = SharedRace.betaOneExpMoment (Fintype.card κ) lam :=
      integral_exp_scaledBetaOneLaw_eq_betaOneExpMoment
        (Fintype.card κ) hk lam

/-- The literal exponential-moment winner bound for one normalized iid
exponential clock coordinate. -/
theorem clockLaw_scaledNormClock_expMoment_le (i : κ)
    (hk : 2 ≤ Fintype.card κ) {lam : ℝ} (hlam : lam < 1) :
    (∫ E : κ → ℝ,
        Real.exp (lam * ((Fintype.card κ : ℝ) * normClock E i))
        ∂(clockLaw κ)) ≤ (1 - lam)⁻¹ := by
  rw [clockLaw_scaledNormClock_expMoment_eq i hk lam]
  exact SharedRace.winnerBetaExpMoment_le (Fintype.card κ) hk hlam

/-! ### First moments and logarithmic moments -/

omit [DecidableEq κ] in
/-- A normalized clock coordinate is integrable. -/
lemma integrable_normClock (i : κ) :
    Integrable (fun E : κ → ℝ => normClock E i) (clockLaw κ) := by
  apply Integrable.of_bound (measurable_normClock i).aestronglyMeasurable 1
  filter_upwards [ae_normClock_nonneg i, ae_normClock_le_one i] with E hE0 hE1
  simpa [Real.norm_eq_abs, abs_of_nonneg hE0] using hE1

omit [DecidableEq κ] in
/-- The normalized clock coordinates sum to one almost surely. -/
lemma ae_sum_normClock_eq_one :
    ∀ᵐ E ∂(clockLaw κ), ∑ i, normClock E i = 1 := by
  filter_upwards [ae_clockLaw_pos (κ := κ)] with E hE
  unfold normClock clockTotal
  rw [← Finset.sum_div]
  exact div_self (clockTotal_pos E hE).ne'

/-- All normalized clock coordinates have the same expectation. -/
theorem integral_normClock_eq (i j : κ) :
    (∫ E : κ → ℝ, normClock E i ∂(clockLaw κ)) =
      ∫ E : κ → ℝ, normClock E j ∂(clockLaw κ) := by
  by_cases hk : 2 ≤ Fintype.card κ
  · let k : ℝ := Fintype.card κ
    let Yi : (κ → ℝ) → ℝ := fun E => k * normClock E i
    let Yj : (κ → ℝ) → ℝ := fun E => k * normClock E j
    let f : ℝ → ℝ := fun t => t / k
    have hkpos : 0 < k := by
      dsimp only [k]
      positivity
    have hYi : Measurable Yi :=
      measurable_const.mul (measurable_normClock i)
    have hYj : Measurable Yj :=
      measurable_const.mul (measurable_normClock j)
    have hf : StronglyMeasurable f := by
      exact (by
        dsimp only [f]
        fun_prop : Continuous f).stronglyMeasurable
    calc
      (∫ E : κ → ℝ, normClock E i ∂(clockLaw κ)) =
          ∫ E : κ → ℝ, f (Yi E) ∂(clockLaw κ) := by
        apply integral_congr_ae
        filter_upwards [] with E
        dsimp only [f, Yi, k]
        field_simp [show (Fintype.card κ : ℝ) ≠ 0 by positivity]
      _ = ∫ t : ℝ, f t ∂((clockLaw κ).map Yi) :=
        (integral_map hYi.aemeasurable hf.aestronglyMeasurable).symm
      _ = ∫ t : ℝ, f t ∂(scaledBetaOneLaw (Fintype.card κ)) := by
        rw [show (clockLaw κ).map Yi =
            scaledBetaOneLaw (Fintype.card κ) by
          exact clockLaw_scaledNormClock_map_eq_scaledBetaOneLaw i hk]
      _ = ∫ t : ℝ, f t ∂((clockLaw κ).map Yj) := by
        rw [show (clockLaw κ).map Yj =
            scaledBetaOneLaw (Fintype.card κ) by
          exact clockLaw_scaledNormClock_map_eq_scaledBetaOneLaw j hk]
      _ = ∫ E : κ → ℝ, f (Yj E) ∂(clockLaw κ) :=
        integral_map hYj.aemeasurable hf.aestronglyMeasurable
      _ = ∫ E : κ → ℝ, normClock E j ∂(clockLaw κ) := by
        apply integral_congr_ae
        filter_upwards [] with E
        dsimp only [f, Yj, k]
        field_simp [show (Fintype.card κ : ℝ) ≠ 0 by positivity]
  · have hcard : Fintype.card κ ≤ 1 := by omega
    let _ : Subsingleton κ :=
      Fintype.card_le_one_iff_subsingleton.mp hcard
    rw [Subsingleton.elim i j]

/-- Each normalized iid exponential clock coordinate has mean `1 / k`. -/
theorem integral_normClock (i : κ) :
    (∫ E : κ → ℝ, normClock E i ∂(clockLaw κ)) =
      1 / (Fintype.card κ : ℝ) := by
  have hkpos : (0 : ℝ) < Fintype.card κ := by positivity
  have htotal :
      (∫ E : κ → ℝ, ∑ j, normClock E j ∂(clockLaw κ)) = 1 := by
    calc
      (∫ E : κ → ℝ, ∑ j, normClock E j ∂(clockLaw κ)) =
          ∫ _E : κ → ℝ, (1 : ℝ) ∂(clockLaw κ) :=
        integral_congr_ae ae_sum_normClock_eq_one
      _ = 1 := by simp
  have hmul : (Fintype.card κ : ℝ) *
      (∫ E : κ → ℝ, normClock E i ∂(clockLaw κ)) = 1 := by
    calc
      (Fintype.card κ : ℝ) *
          (∫ E : κ → ℝ, normClock E i ∂(clockLaw κ)) =
          ∑ _j : κ, ∫ E : κ → ℝ, normClock E i ∂(clockLaw κ) := by simp
      _ = ∑ j : κ, ∫ E : κ → ℝ, normClock E j ∂(clockLaw κ) := by
        apply Finset.sum_congr rfl
        intro j _
        exact integral_normClock_eq i j
      _ = ∫ E : κ → ℝ, ∑ j, normClock E j ∂(clockLaw κ) := by
        rw [integral_finsetSum Finset.univ]
        intro j _
        exact integrable_normClock j
      _ = 1 := htotal
  apply (eq_div_iff hkpos.ne').2
  simpa [mul_comm] using hmul

/-- The common logarithmic mean of a normalized clock coordinate, expressed
against the literal scaled-Beta law.  No closed-form harmonic-number
evaluation is needed downstream. -/
noncomputable def normClockLogIntegral (k : ℕ) : ℝ :=
  ∫ t : ℝ, Real.log (t / (k : ℝ)) ∂(scaledBetaOneLaw k)

/-- The logarithmic observable is integrable against the literal scaled-Beta
law. -/
lemma integrable_log_scaledBetaOneLaw (k : ℕ) (hk : 2 ≤ k) :
    Integrable (fun t : ℝ => Real.log (t / (k : ℝ)))
      (scaledBetaOneLaw k) := by
  have hkpos : (0 : ℝ) < k := by positivity
  have hdensity_nonneg : ∀ x ∈ Set.Ioc (0 : ℝ) (k : ℝ),
      0 ≤ SharedRace.betaOneDensity k x := by
    intro x hx
    unfold SharedRace.betaOneDensity
    exact mul_nonneg (div_nonneg (by positivity) hkpos.le)
      (pow_nonneg (sub_nonneg.mpr ((div_le_one hkpos).2 hx.2)) _)
  have hlog : IntervalIntegrable
      (fun t : ℝ => Real.log (t / (k : ℝ))) volume 0 (k : ℝ) := by
    have hbase : IntervalIntegrable
        (fun t : ℝ => Real.log t - Real.log (k : ℝ)) volume 0 (k : ℝ) := by
      have hlogBase : IntervalIntegrable Real.log volume 0 (k : ℝ) :=
        intervalIntegral.intervalIntegrable_log'
      exact hlogBase.sub intervalIntegrable_const
    apply hbase.congr_uIoo
    intro t ht
    rw [uIoo_of_le hkpos.le] at ht
    exact (Real.log_div ht.1.ne' hkpos.ne').symm
  have hdensity_cont : Continuous
      (SharedRace.betaOneDensity k) := by
    unfold SharedRace.betaOneDensity
    fun_prop
  have hweighted : IntervalIntegrable
      (fun t : ℝ => Real.log (t / (k : ℝ)) *
        SharedRace.betaOneDensity k t) volume 0 (k : ℝ) :=
    hlog.mul_continuousOn hdensity_cont.continuousOn
  unfold scaledBetaOneLaw
  rw [integrable_withDensity_iff
    (by
      exact ENNReal.measurable_ofReal.comp hdensity_cont.measurable)
    (by simp)]
  change Integrable
    (fun t : ℝ => Real.log (t / (k : ℝ)) *
      (ENNReal.ofReal (SharedRace.betaOneDensity k t)).toReal)
    (volume.restrict (Set.Ioc 0 (k : ℝ)))
  rw [integrable_congr (by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [ENNReal.toReal_ofReal (hdensity_nonneg t ht)])]
  exact hweighted.1

/-- The logarithm of a normalized clock coordinate is integrable. -/
theorem integrable_log_normClock (i : κ)
    (hk : 2 ≤ Fintype.card κ) :
    Integrable (fun E : κ → ℝ => Real.log (normClock E i))
      (clockLaw κ) := by
  let k : ℝ := Fintype.card κ
  let Y : (κ → ℝ) → ℝ := fun E => k * normClock E i
  let f : ℝ → ℝ := fun t => Real.log (t / k)
  have hY : Measurable Y :=
    measurable_const.mul (measurable_normClock i)
  have hf : Integrable f ((clockLaw κ).map Y) := by
    rw [show (clockLaw κ).map Y = scaledBetaOneLaw (Fintype.card κ) by
      exact clockLaw_scaledNormClock_map_eq_scaledBetaOneLaw i hk]
    exact integrable_log_scaledBetaOneLaw (Fintype.card κ) hk
  have hcomp := hf.comp_measurable hY
  simpa [Function.comp_def, f, Y, k,
    show (Fintype.card κ : ℝ) ≠ 0 by positivity] using hcomp

/-- The logarithmic clock integral is the common scaled-Beta integral. -/
theorem integral_log_normClock_eq_normClockLogIntegral (i : κ)
    (hk : 2 ≤ Fintype.card κ) :
    (∫ E : κ → ℝ, Real.log (normClock E i) ∂(clockLaw κ)) =
      normClockLogIntegral (Fintype.card κ) := by
  let k : ℝ := Fintype.card κ
  let Y : (κ → ℝ) → ℝ := fun E => k * normClock E i
  let f : ℝ → ℝ := fun t => Real.log (t / k)
  have hY : Measurable Y :=
    measurable_const.mul (measurable_normClock i)
  have hf : AEStronglyMeasurable f ((clockLaw κ).map Y) := by
    exact (integrable_log_scaledBetaOneLaw (Fintype.card κ) hk).aestronglyMeasurable.mono_ac
      (by
        rw [clockLaw_scaledNormClock_map_eq_scaledBetaOneLaw i hk])
  calc
    (∫ E : κ → ℝ, Real.log (normClock E i) ∂(clockLaw κ)) =
        ∫ E : κ → ℝ, f (Y E) ∂(clockLaw κ) := by
      apply integral_congr_ae
      filter_upwards [] with E
      dsimp only [f, Y, k]
      rw [show (Fintype.card κ : ℝ) * normClock E i /
          (Fintype.card κ : ℝ) = normClock E i by
        field_simp [show (Fintype.card κ : ℝ) ≠ 0 by positivity]]
    _ = ∫ t : ℝ, f t ∂((clockLaw κ).map Y) :=
      (integral_map hY.aemeasurable hf).symm
    _ = ∫ t : ℝ, f t ∂(scaledBetaOneLaw (Fintype.card κ)) := by
      rw [clockLaw_scaledNormClock_map_eq_scaledBetaOneLaw i hk]
    _ = normClockLogIntegral (Fintype.card κ) := by
      rfl

/-- Logarithmic clock expectations are coordinate-independent. -/
theorem integral_log_normClock_eq (i j : κ)
    (hk : 2 ≤ Fintype.card κ) :
    (∫ E : κ → ℝ, Real.log (normClock E i) ∂(clockLaw κ)) =
      ∫ E : κ → ℝ, Real.log (normClock E j) ∂(clockLaw κ) := by
  rw [integral_log_normClock_eq_normClockLogIntegral i hk,
    integral_log_normClock_eq_normClockLogIntegral j hk]

end SharedRace
end stoch_to_det
