import stoch_to_det.SharedRace.ClockLaw
import stoch_to_det.SharedRace.Mobius
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Integral.Prod

/-!
# The two-clock sum/ratio law

This file proves the pair-clock factorization used by the loser-coordinate
estimate.  The proof starts from the product of two unit exponential laws;
it does not use a Dirichlet-distribution API.
-/

namespace stoch_to_det
namespace SharedRace

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal Interval

local notation "L" => SharedRace.logTwo

/-- Sum/ratio coordinates mapped back to two positive clocks. -/
noncomputable def pairPolar (q : ℝ × ℝ) : ℝ × ℝ :=
  (q.1 * q.2, q.1 * (1 - q.2))

/-- Natural domain of `(total, first-coordinate fraction)`. -/
def pairPolarSource : Set (ℝ × ℝ) :=
  Ioi (0 : ℝ) ×ˢ Ioo (0 : ℝ) 1

/-- Strictly positive clock pairs. -/
def positivePair : Set (ℝ × ℝ) :=
  Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)

lemma pairPolar_image : pairPolar '' pairPolarSource = positivePair := by
  ext z
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact ⟨mul_pos hq.1 hq.2.1,
      mul_pos hq.1 (sub_pos.mpr hq.2.2)⟩
  · intro hz
    change 0 < z.1 ∧ 0 < z.2 at hz
    let t : ℝ := z.1 + z.2
    let v : ℝ := z.1 / t
    have ht : 0 < t := by dsimp [t]; linarith [hz.1, hz.2]
    have hv0 : 0 < v := div_pos hz.1 ht
    have hv1 : v < 1 := by
      dsimp [v]
      rw [div_lt_one ht]
      linarith [hz.2]
    have htne : z.1 + z.2 ≠ 0 := by
      dsimp [t] at ht
      exact ht.ne'
    refine ⟨(t, v), ⟨ht, hv0, hv1⟩, ?_⟩
    apply Prod.ext
    · dsimp [pairPolar, t, v]
      exact mul_div_cancel₀ z.1 htne
    · dsimp [pairPolar, t, v]
      field_simp [htne]
      ring

lemma pairPolar_injOn : Set.InjOn pairPolar pairPolarSource := by
  intro q hq r hr hqr
  have hfst := congrArg Prod.fst hqr
  have hsnd := congrArg Prod.snd hqr
  have ht : q.1 = r.1 := by
    dsimp [pairPolar] at hfst hsnd
    nlinarith
  apply Prod.ext ht
  dsimp [pairPolar] at hfst
  rw [ht] at hfst
  exact (mul_left_cancel₀ hr.1.ne' hfst)

/-- Fréchet derivative of `pairPolar`. -/
noncomputable def pairPolarFDeriv (q : ℝ × ℝ) : ℝ × ℝ →L[ℝ] ℝ × ℝ :=
  (Matrix.toLin (.finTwoProd ℝ) (.finTwoProd ℝ)
    !![q.2, q.1; 1 - q.2, -q.1]).toContinuousLinearMap

lemma hasFDerivAt_pairPolar (q : ℝ × ℝ) :
    HasFDerivAt pairPolar (pairPolarFDeriv q) q := by
  unfold pairPolarFDeriv
  rw [Matrix.toLin_finTwoProd_toContinuousLinearMap]
  convert!
    HasFDerivAt.prodMk (𝕜 := ℝ)
      ((hasFDerivAt_fst (𝕜 := ℝ) (p := q)).mul
        (hasFDerivAt_snd (𝕜 := ℝ) (p := q)))
      ((hasFDerivAt_fst (𝕜 := ℝ) (p := q)).mul
        ((hasFDerivAt_snd (𝕜 := ℝ) (p := q)).const_sub 1)) using 2 <;>
  module

lemma det_pairPolarFDeriv (q : ℝ × ℝ) :
    (pairPolarFDeriv q).det = -q.1 := by
  unfold pairPolarFDeriv
  simp only [LinearMap.det_toContinuousLinearMap, LinearMap.det_toLin,
    Matrix.det_fin_two_of]
  ring

/-- Jacobian formula for the positive two-clock quadrant. -/
theorem lintegral_pairPolar (g : ℝ × ℝ → ℝ≥0∞) :
    (∫⁻ z : ℝ × ℝ in positivePair, g z) =
      ∫⁻ q : ℝ × ℝ in pairPolarSource,
        ENNReal.ofReal q.1 * g (pairPolar q) := by
  rw [← pairPolar_image]
  have hchange := lintegral_image_eq_lintegral_abs_det_fderiv_mul
    volume (measurableSet_Ioi.prod measurableSet_Ioo)
    (fun q _ => (hasFDerivAt_pairPolar q).hasFDerivWithinAt)
    pairPolar_injOn g
  refine hchange.trans ?_
  apply setLIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo)
  intro q hq
  change ENNReal.ofReal |(pairPolarFDeriv q).det| * g (pairPolar q) = _
  rw [det_pairPolarFDeriv, abs_neg, abs_of_pos hq.1]

/-- Positive part of the unit exponential density. -/
noncomputable def unitExpDensity (x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-x))

/-- Literal `Gamma(2,1)` density on the positive half-line. -/
noncomputable def rawGammaTwoDensity (t : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (t * Real.exp (-t))

/-- Literal raw sum law of two unit exponential clocks. -/
noncomputable def rawGammaTwoLaw : Measure ℝ :=
  (volume.restrict (Ioi (0 : ℝ))).withDensity rawGammaTwoDensity

/-- Uniform probability law on the open unit interval. -/
noncomputable def uniformUnitLaw : Measure ℝ :=
  volume.restrict (Ioo (0 : ℝ) 1)

private lemma uniformUnitLaw_univ : uniformUnitLaw Set.univ = 1 := by
  unfold uniformUnitLaw
  simp

private noncomputable instance : IsProbabilityMeasure uniformUnitLaw :=
  ⟨uniformUnitLaw_univ⟩

private lemma measurable_unitExpDensity : Measurable unitExpDensity := by
  unfold unitExpDensity
  fun_prop

private lemma measurable_rawGammaTwoDensity : Measurable rawGammaTwoDensity := by
  unfold rawGammaTwoDensity
  fun_prop

/-- The library unit exponential measure in positive-density form. -/
lemma expMeasure_one_eq_restrict_withDensity :
    expMeasure 1 =
      (volume.restrict (Ioi (0 : ℝ))).withDensity unitExpDensity := by
  unfold expMeasure gammaMeasure
  calc
    volume.withDensity (gammaPDF 1 1) =
        volume.withDensity ((Ioi (0 : ℝ)).indicator unitExpDensity) := by
      apply withDensity_congr_ae
      filter_upwards [(volume : Measure ℝ).ae_ne 0] with x hx
      by_cases hxpos : 0 < x
      · rw [Set.indicator_of_mem (show x ∈ Ioi (0 : ℝ) from hxpos)]
        simp [unitExpDensity, gammaPDF, gammaPDFReal, hxpos.le]
      · have hxneg : x < 0 := lt_of_le_of_ne (le_of_not_gt hxpos) hx
        rw [Set.indicator_of_notMem
          (show x ∉ Ioi (0 : ℝ) from hxpos), gammaPDF_of_neg hxneg]
    _ = (volume.restrict (Ioi (0 : ℝ))).withDensity unitExpDensity :=
      withDensity_indicator measurableSet_Ioi unitExpDensity

/-- Sum and ratio of a positive clock pair. -/
noncomputable def pairSumRatio (z : ℝ × ℝ) : ℝ × ℝ :=
  (z.1 + z.2, z.1 / (z.1 + z.2))

private lemma pairSumRatio_pairPolar {q : ℝ × ℝ} (hq : q ∈ pairPolarSource) :
    pairSumRatio (pairPolar q) = q := by
  apply Prod.ext
  · dsimp [pairSumRatio, pairPolar]
    ring
  · dsimp [pairSumRatio, pairPolar]
    have ht : q.1 ≠ 0 := hq.1.ne'
    field_simp [ht]
    ring

private lemma measurable_pairSumRatio : Measurable pairSumRatio := by
  unfold pairSumRatio
  fun_prop

private lemma expPairLaw_eq :
    (expMeasure 1).prod (expMeasure 1) =
      (volume.restrict positivePair).withDensity
        (fun z : ℝ × ℝ => unitExpDensity z.1 * unitExpDensity z.2) := by
  rw [expMeasure_one_eq_restrict_withDensity,
    prod_withDensity measurable_unitExpDensity measurable_unitExpDensity,
    Measure.prod_restrict, ← Measure.volume_eq_prod]
  rfl

private lemma rawPairFactorLaw_eq :
    rawGammaTwoLaw.prod uniformUnitLaw =
      (volume.restrict pairPolarSource).withDensity
        (fun q : ℝ × ℝ => rawGammaTwoDensity q.1) := by
  unfold rawGammaTwoLaw uniformUnitLaw pairPolarSource
  rw [prod_withDensity_left measurable_rawGammaTwoDensity,
    Measure.prod_restrict, ← Measure.volume_eq_prod]

private lemma pairPolar_density_cancel {q : ℝ × ℝ} (hq : q ∈ pairPolarSource) :
    ENNReal.ofReal q.1 *
        (unitExpDensity (pairPolar q).1 * unitExpDensity (pairPolar q).2) =
      rawGammaTwoDensity q.1 := by
  have ht : 0 ≤ q.1 := hq.1.le
  unfold unitExpDensity rawGammaTwoDensity pairPolar
  rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
  have hexp : -(q.1 * q.2) + -(q.1 * (1 - q.2)) = -q.1 := by ring
  rw [hexp, ← ENNReal.ofReal_mul ht]

/-- Two iid unit exponentials factor exactly into their sum, with literal
`Gamma(2,1)` density, and an independent uniform ratio. -/
theorem map_pairSumRatio_expPair :
    Measure.map pairSumRatio ((expMeasure 1).prod (expMeasure 1)) =
      rawGammaTwoLaw.prod uniformUnitLaw := by
  rw [expPairLaw_eq, rawPairFactorLaw_eq]
  apply Measure.ext_of_lintegral
  intro g hg
  rw [lintegral_map hg measurable_pairSumRatio]
  have hleft :
      (∫⁻ a : ℝ × ℝ, g (pairSumRatio a)
        ∂(volume.restrict positivePair).withDensity
          (fun z : ℝ × ℝ => unitExpDensity z.1 * unitExpDensity z.2)) =
        ∫⁻ a : ℝ × ℝ,
          ((fun z : ℝ × ℝ => unitExpDensity z.1 * unitExpDensity z.2) *
            (fun z => g (pairSumRatio z))) a ∂(volume.restrict positivePair) := by
    exact lintegral_withDensity_eq_lintegral_mul
      (volume.restrict positivePair)
      ((measurable_unitExpDensity.comp measurable_fst).mul
        (measurable_unitExpDensity.comp measurable_snd))
      (hg.comp measurable_pairSumRatio)
  have hright :
      (∫⁻ a : ℝ × ℝ, g a
        ∂(volume.restrict pairPolarSource).withDensity
          (fun q : ℝ × ℝ => rawGammaTwoDensity q.1)) =
        ∫⁻ a : ℝ × ℝ,
          ((fun q : ℝ × ℝ => rawGammaTwoDensity q.1) * g) a
            ∂(volume.restrict pairPolarSource) := by
    exact lintegral_withDensity_eq_lintegral_mul
      (volume.restrict pairPolarSource)
      (measurable_rawGammaTwoDensity.comp measurable_fst) hg
  rw [hleft, hright]
  change (∫⁻ z : ℝ × ℝ in positivePair,
      (unitExpDensity z.1 * unitExpDensity z.2) * g (pairSumRatio z)) =
    ∫⁻ q : ℝ × ℝ in pairPolarSource, rawGammaTwoDensity q.1 * g q
  rw [lintegral_pairPolar]
  apply setLIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo)
  intro q hq
  change ENNReal.ofReal q.1 *
      ((unitExpDensity (pairPolar q).1 * unitExpDensity (pairPolar q).2) *
        g (pairSumRatio (pairPolar q))) =
    rawGammaTwoDensity q.1 * g q
  rw [pairSumRatio_pairPolar hq]
  rw [← mul_assoc, pairPolar_density_cancel hq]

/-- Survival function of the literal raw `Gamma(2,1)` law. -/
lemma rawGammaTwoLaw_Ioi (y : ℝ) (hy : 0 ≤ y) :
    rawGammaTwoLaw (Ioi y) =
      ENNReal.ofReal ((y + 1) * Real.exp (-y)) := by
  let anti : ℝ → ℝ := fun t => -(t + 1) * Real.exp (-t)
  let density : ℝ → ℝ := fun t => t * Real.exp (-t)
  have hderiv : ∀ t ∈ Ici y, HasDerivAt anti (density t) t := by
    intro t _ht
    dsimp [anti, density]
    have hleft : HasDerivAt (fun s : ℝ => -(s + 1)) (-1) t :=
      ((hasDerivAt_id t).add_const 1).neg
    have hright : HasDerivAt (fun s : ℝ => Real.exp (-s))
        (-Real.exp (-t)) t := by
      simpa only [Pi.neg_apply, id_eq, mul_neg, mul_one] using
        ((hasDerivAt_id t).neg.exp)
    have hprod := hleft.mul hright
    have hprod' : HasDerivAt
        (fun s : ℝ => (-(s + 1)) * Real.exp (-s))
        ((-1) * Real.exp (-t) + (-(t + 1)) * (-Real.exp (-t))) t :=
      hprod.congr_of_eventuallyEq (Filter.Eventually.of_forall fun _ => rfl)
    convert hprod' using 1
    ring
  have hdensity_nonneg : ∀ t ∈ Ioi y, 0 ≤ density t := by
    intro t ht
    exact mul_nonneg (hy.trans ht.le) (Real.exp_nonneg _)
  have hanti_tendsto : Tendsto anti atTop (nhds 0) := by
    have ht : Tendsto (fun t : ℝ => t * Real.exp (-t)) atTop (nhds 0) := by
      simpa only [pow_one] using Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
    have he := Real.tendsto_exp_neg_atTop_nhds_zero
    have hadd : Tendsto (fun t : ℝ => (t + 1) * Real.exp (-t)) atTop (nhds 0) := by
      simpa only [add_mul, one_mul, zero_add] using ht.add he
    dsimp only [anti]
    simpa only [neg_mul, neg_zero] using hadd.neg
  have hdensity_int : IntegrableOn density (Ioi y) :=
    integrableOn_Ioi_deriv_of_nonneg' hderiv hdensity_nonneg hanti_tendsto
  have hintegral : (∫ t : ℝ in Ioi y, density t) =
      (y + 1) * Real.exp (-y) := by
    have h := integral_Ioi_of_hasDerivAt_of_nonneg'
      hderiv hdensity_nonneg hanti_tendsto
    dsimp [anti] at h
    linarith
  unfold rawGammaTwoLaw rawGammaTwoDensity
  rw [withDensity_apply _ measurableSet_Ioi]
  change (∫⁻ t : ℝ,
      ENNReal.ofReal (t * Real.exp (-t))
        ∂((volume.restrict (Ioi (0 : ℝ))).restrict (Ioi y))) = _
  rw [Measure.restrict_restrict measurableSet_Ioi]
  have hinter : Ioi y ∩ Ioi (0 : ℝ) = Ioi y := by
    ext t
    simp only [mem_inter_iff, mem_Ioi]
    constructor
    · exact fun ht => ht.1
    · intro ht
      exact ⟨ht, hy.trans_lt ht⟩
  rw [hinter]
  change (∫⁻ t : ℝ in Ioi y, ENNReal.ofReal (density t)) = _
  rw [← ofReal_integral_eq_lintegral_ofReal hdensity_int
    (ae_restrict_of_forall_mem measurableSet_Ioi hdensity_nonneg)]
  rw [hintegral]

private lemma integral_mul_exp_neg_mul_Ioi (r : ℝ) (hr : 0 < r) :
    IntegrableOn (fun x : ℝ => x * Real.exp (-(r * x))) (Ioi 0) ∧
      (∫ x : ℝ in Ioi 0, x * Real.exp (-(r * x))) = 1 / r ^ 2 := by
  let anti : ℝ → ℝ :=
    fun x => -(x / r + 1 / r ^ 2) * Real.exp (-(r * x))
  let density : ℝ → ℝ := fun x => x * Real.exp (-(r * x))
  have hderiv : ∀ x ∈ Ici (0 : ℝ), HasDerivAt anti (density x) x := by
    intro x _hx
    have hleft : HasDerivAt (fun y : ℝ => -(y / r + 1 / r ^ 2))
        (-(1 / r)) x := by
      have h := (((hasDerivAt_id x).div_const r).add_const (1 / r ^ 2)).neg
      exact h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun _ => rfl)
    have hright : HasDerivAt (fun y : ℝ => Real.exp (-(r * y)))
        (-r * Real.exp (-(r * x))) x := by
      have hlin : HasDerivAt (fun y : ℝ => r * y) r x :=
        hasDerivAt_const_mul r
      have h := hlin.neg.exp
      have h' : HasDerivAt (fun y : ℝ => Real.exp (-(r * y)))
          (Real.exp (-(r * x)) * -r) x :=
        h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun _ => rfl)
      convert h' using 1
      ring
    have hprod := hleft.mul hright
    have hprod' : HasDerivAt
        (fun y : ℝ => (-(y / r + 1 / r ^ 2)) * Real.exp (-(r * y)))
        (-(1 / r) * Real.exp (-(r * x)) +
          (-(x / r + 1 / r ^ 2)) * (-r * Real.exp (-(r * x)))) x :=
      hprod.congr_of_eventuallyEq (Filter.Eventually.of_forall fun _ => rfl)
    dsimp only [anti, density]
    convert hprod' using 1
    field_simp [hr.ne']
    ring
  have hdensity_nonneg : ∀ x ∈ Ioi (0 : ℝ), 0 ≤ density x := by
    intro x hx
    exact mul_nonneg hx.le (Real.exp_nonneg _)
  have hanti_tendsto : Tendsto anti atTop (nhds 0) := by
    have ht : Tendsto (fun x : ℝ => x * Real.exp (-(r * x))) atTop (nhds 0) := by
      simpa only [Real.rpow_one, neg_mul] using
        tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 r hr
    have he : Tendsto (fun x : ℝ => Real.exp (-(r * x))) atTop (nhds 0) := by
      simpa only [Real.rpow_zero, one_mul, neg_mul] using
        tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 r hr
    have hsum : Tendsto
        (fun x : ℝ => x / r * Real.exp (-(r * x)) +
          (1 / r ^ 2) * Real.exp (-(r * x))) atTop (nhds 0) := by
      have h := (ht.const_mul (1 / r)).add (he.const_mul (1 / r ^ 2))
      convert h using 1
      · funext x
        ring
      · simp
    dsimp only [anti]
    have hneg := hsum.neg
    convert hneg using 1
    · funext x
      ring
    · simp
  have hint : IntegrableOn density (Ioi 0) :=
    integrableOn_Ioi_deriv_of_nonneg' hderiv hdensity_nonneg hanti_tendsto
  refine ⟨by simpa only [density] using hint, ?_⟩
  have h := integral_Ioi_of_hasDerivAt_of_nonneg'
    hderiv hdensity_nonneg hanti_tendsto
  dsimp [anti, density] at h
  simpa [hr.ne'] using h

/-- First tilted moment of a unit exponential. -/
private lemma expMeasure_one_laplace_first (c : ℝ) (hc : 0 ≤ c) :
    (∫⁻ x : ℝ, ENNReal.ofReal (x * Real.exp (-(c * x))) ∂(expMeasure 1)) =
      ENNReal.ofReal (1 / (1 + c) ^ 2) := by
  rw [expMeasure_one_eq_restrict_withDensity]
  rw [lintegral_withDensity_eq_lintegral_mul
    (volume.restrict (Ioi (0 : ℝ))) measurable_unitExpDensity (by fun_prop)]
  have hpoint : ∀ x ∈ Ioi (0 : ℝ),
      unitExpDensity x * ENNReal.ofReal (x * Real.exp (-(c * x))) =
        ENNReal.ofReal (x * Real.exp (-((1 + c) * x))) := by
    intro x hx
    unfold unitExpDensity
    rw [← ENNReal.ofReal_mul (Real.exp_nonneg _)]
    congr 1
    calc
      Real.exp (-x) * (x * Real.exp (-(c * x))) =
          x * (Real.exp (-x) * Real.exp (-(c * x))) := by ring
      _ = x * Real.exp (-x + -(c * x)) := by rw [Real.exp_add]
      _ = x * Real.exp (-((1 + c) * x)) := by ring_nf
  rw [show (∫⁻ x : ℝ,
      (unitExpDensity * fun x => ENNReal.ofReal (x * Real.exp (-(c * x)))) x
        ∂volume.restrict (Ioi (0 : ℝ))) =
      ∫⁻ x : ℝ in Ioi (0 : ℝ),
        ENNReal.ofReal (x * Real.exp (-((1 + c) * x))) by
      apply setLIntegral_congr_fun measurableSet_Ioi
      exact hpoint]
  have hr : 0 < 1 + c := by linarith
  have hint := (integral_mul_exp_neg_mul_Ioi (1 + c) hr).1
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (ae_restrict_of_forall_mem measurableSet_Ioi (fun x hx =>
      mul_nonneg hx.le (Real.exp_nonneg _)))]
  rw [(integral_mul_exp_neg_mul_Ioi (1 + c) hr).2]

/-- Laplace transform of a finite sum of iid unit exponential clocks. -/
private lemma pi_exp_laplace {ι : Type} [Fintype ι] (c : ℝ) (hc : 0 ≤ c) :
    (∫⁻ x : ι → ℝ,
        ENNReal.ofReal (Real.exp (-(c * ∑ i, x i)))
        ∂Measure.pi (fun _ : ι => expMeasure 1)) =
      ENNReal.ofReal ((1 / (1 + c)) ^ Fintype.card ι) := by
  let _ : IsProbabilityMeasure (expMeasure 1) :=
    isProbabilityMeasure_expMeasure zero_lt_one
  let X : ι → ((ι → ℝ) → ENNReal) :=
    fun i x => ENNReal.ofReal (Real.exp (-(c * x i)))
  have hfactor (x : ι → ℝ) :
      ENNReal.ofReal (Real.exp (-(c * ∑ i, x i))) = ∏ i, X i x := by
    dsimp [X]
    rw [← ENNReal.ofReal_prod_of_nonneg
      (fun i _ => Real.exp_nonneg (-(c * x i))), ← Real.exp_sum]
    congr 2
    rw [Finset.sum_neg_distrib, Finset.mul_sum]
  have hindep_eval :
      iIndepFun (fun i (x : ι → ℝ) => x i)
        (Measure.pi (fun _ : ι => expMeasure 1)) := by
    simpa only [id_eq] using
      (iIndepFun_pi (μ := fun _ : ι => expMeasure 1)
        (X := fun _ => id) (fun _ => aemeasurable_id))
  have hindep : iIndepFun X
      (Measure.pi (fun _ : ι => expMeasure 1)) := by
    simpa [X, Function.comp_def] using hindep_eval.comp
      (fun _ y => ENNReal.ofReal (Real.exp (-(c * y)))) (fun _ => by fun_prop)
  have hprodIntegral := lintegral_prod_eq_prod_lintegral_of_indepFun
    (Finset.univ : Finset ι) X hindep (fun _ => by fun_prop)
  calc
    (∫⁻ x : ι → ℝ, ENNReal.ofReal (Real.exp (-(c * ∑ i, x i)))
        ∂Measure.pi (fun _ : ι => expMeasure 1)) =
        ∫⁻ x : ι → ℝ, ∏ i, X i x
          ∂Measure.pi (fun _ : ι => expMeasure 1) := by
      apply lintegral_congr
      exact hfactor
    _ = ∏ i, ∫⁻ x : ι → ℝ, X i x
          ∂Measure.pi (fun _ : ι => expMeasure 1) := by
      simpa using hprodIntegral
    _ = ∏ _i : ι, ENNReal.ofReal (1 / (1 + c)) := by
      apply Finset.prod_congr rfl
      intro i _hi
      calc
        (∫⁻ x : ι → ℝ, X i x
            ∂Measure.pi (fun _ : ι => expMeasure 1)) =
            ∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (-(c * y)))
              ∂(expMeasure 1) := by
          dsimp [X]
          have hmeas : Measurable
              (fun y : ℝ => ENNReal.ofReal (Real.exp (-(c * y)))) := by
            fun_prop
          exact (measurePreserving_eval
            (fun _ : ι => expMeasure 1) i).lintegral_comp hmeas
        _ = ENNReal.ofReal (1 / (1 + c)) := expMeasure_one_laplace c hc
    _ = ENNReal.ofReal ((1 / (1 + c)) ^ Fintype.card ι) := by
      rw [Finset.prod_const, Finset.card_univ]
      exact (ENNReal.ofReal_pow (by positivity) (Fintype.card ι)).symm

/-- One-coordinate first moment in a finite iid exponential product, with a
common Laplace tilt by the total. -/
private lemma pi_exp_laplace_first_coordinate {ι : Type} [Fintype ι]
    (i : ι) (c : ℝ) (hc : 0 ≤ c) :
    (∫⁻ x : ι → ℝ,
        ENNReal.ofReal (x i * Real.exp (-(c * ∑ j, x j)))
        ∂Measure.pi (fun _ : ι => expMeasure 1)) =
      ENNReal.ofReal (1 / (1 + c) ^ 2) *
        ENNReal.ofReal (1 / (1 + c)) ^ (Fintype.card ι - 1) := by
  classical
  let _ : IsProbabilityMeasure (expMeasure 1) :=
    isProbabilityMeasure_expMeasure zero_lt_one
  let X : ι → ((ι → ℝ) → ENNReal) := fun j x =>
    ENNReal.ofReal
      ((if j = i then x j else 1) * Real.exp (-(c * x j)))
  have hpos : ∀ᵐ x ∂Measure.pi (fun _ : ι => expMeasure 1), ∀ j, 0 < x j := by
    have hone : ∀ᵐ y : ℝ ∂(expMeasure 1), 0 < y := by
      have hnot := measure_eq_zero_iff_ae_notMem.mp expMeasure_one_Iic_zero
      filter_upwards [hnot] with y hy
      simpa only [Set.mem_Iic, not_le] using hy
    exact ae_forall_fintype fun j =>
      Measure.tendsto_eval_ae_ae.eventually hone
  have hfactor : ∀ᵐ x ∂Measure.pi (fun _ : ι => expMeasure 1),
      ENNReal.ofReal (x i * Real.exp (-(c * ∑ j, x j))) = ∏ j, X j x := by
    filter_upwards [hpos] with x hx
    dsimp [X]
    rw [← ENNReal.ofReal_prod_of_nonneg]
    · congr 2
      rw [Finset.prod_mul_distrib, Fintype.prod_ite_eq' i x,
        ← Real.exp_sum]
      congr 1
      rw [Finset.sum_neg_distrib, Finset.mul_sum]
    · intro j _hj
      have hfirst : 0 ≤ if j = i then x j else 1 := by
        by_cases hji : j = i
        · simp only [hji, if_pos]
          exact (hx i).le
        · simp [hji]
      exact mul_nonneg hfirst (Real.exp_nonneg _)
  have hindep_eval :
      iIndepFun (fun j (x : ι → ℝ) => x j)
        (Measure.pi (fun _ : ι => expMeasure 1)) := by
    simpa only [id_eq] using
      (iIndepFun_pi (μ := fun _ : ι => expMeasure 1)
        (X := fun _ => id) (fun _ => aemeasurable_id))
  have hindep : iIndepFun X
      (Measure.pi (fun _ : ι => expMeasure 1)) := by
    simpa [X, Function.comp_def] using hindep_eval.comp
      (fun j y => ENNReal.ofReal
        ((if j = i then y else 1) * Real.exp (-(c * y))))
      (fun j => by
        by_cases hji : j = i <;> simp only [hji, if_pos, if_false] <;> fun_prop)
  have hprodIntegral := lintegral_prod_eq_prod_lintegral_of_indepFun
    (Finset.univ : Finset ι) X hindep (fun j => by
      unfold X
      by_cases hji : j = i <;> simp only [hji, if_pos, if_false] <;> fun_prop)
  calc
    (∫⁻ x : ι → ℝ,
        ENNReal.ofReal (x i * Real.exp (-(c * ∑ j, x j)))
        ∂Measure.pi (fun _ : ι => expMeasure 1)) =
        ∫⁻ x : ι → ℝ, ∏ j, X j x
          ∂Measure.pi (fun _ : ι => expMeasure 1) :=
      lintegral_congr_ae hfactor
    _ = ∏ j, ∫⁻ x : ι → ℝ, X j x
          ∂Measure.pi (fun _ : ι => expMeasure 1) := by
      simpa using hprodIntegral
    _ = ∏ j : ι, if j = i then ENNReal.ofReal (1 / (1 + c) ^ 2)
          else ENNReal.ofReal (1 / (1 + c)) := by
      apply Finset.prod_congr rfl
      intro j _hj
      by_cases hji : j = i
      · subst j
        rw [if_pos rfl]
        calc
          (∫⁻ x : ι → ℝ, X i x
              ∂Measure.pi (fun _ : ι => expMeasure 1)) =
              ∫⁻ y : ℝ, ENNReal.ofReal (y * Real.exp (-(c * y)))
                ∂(expMeasure 1) := by
            dsimp [X]
            simp only [if_pos]
            have hmeas : Measurable
                (fun y : ℝ => ENNReal.ofReal (y * Real.exp (-(c * y)))) := by
              fun_prop
            exact (measurePreserving_eval
              (fun _ : ι => expMeasure 1) i).lintegral_comp hmeas
          _ = _ := expMeasure_one_laplace_first c hc
      · rw [if_neg hji]
        calc
          (∫⁻ x : ι → ℝ, X j x
              ∂Measure.pi (fun _ : ι => expMeasure 1)) =
              ∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (-(c * y)))
                ∂(expMeasure 1) := by
            dsimp only [X]
            simp only [hji, if_false, one_mul]
            have hmeas : Measurable
                (fun y : ℝ => ENNReal.ofReal (Real.exp (-(c * y)))) := by
              fun_prop
            exact (measurePreserving_eval
              (fun _ : ι => expMeasure 1) j).lintegral_comp hmeas
          _ = _ := expMeasure_one_laplace c hc
    _ = ENNReal.ofReal (1 / (1 + c) ^ 2) *
        ENNReal.ofReal (1 / (1 + c)) ^ (Fintype.card ι - 1) := by
      rw [Finset.prod_eq_mul_prod_sdiff_singleton_of_mem
        (Finset.mem_univ i)]
      simp only [if_pos]
      congr 1
      have herase :
          (∏ x ∈ Finset.univ \ {i},
              if x = i then ENNReal.ofReal (1 / (1 + c) ^ 2)
              else ENNReal.ofReal (1 / (1 + c))) =
            ∏ _x ∈ Finset.univ \ {i}, ENNReal.ofReal (1 / (1 + c)) := by
        apply Finset.prod_congr rfl
        intro x hx
        rw [if_neg]
        simpa only [Finset.mem_singleton] using (Finset.mem_sdiff.mp hx).2
      rw [herase, Finset.prod_const, Finset.card_sdiff]
      simp

/-- First moment of the total of finitely many iid unit exponentials under a
common Laplace tilt.  The sum form is convenient for the subsequent tail
calculation and also covers the empty index type literally. -/
private lemma pi_exp_laplace_total {ι : Type} [Fintype ι]
    (c : ℝ) (hc : 0 ≤ c) :
    (∫⁻ x : ι → ℝ,
        ENNReal.ofReal ((∑ i, x i) * Real.exp (-(c * ∑ i, x i)))
        ∂Measure.pi (fun _ : ι => expMeasure 1)) =
      ∑ _i : ι, ENNReal.ofReal (1 / (1 + c) ^ 2) *
        ENNReal.ofReal (1 / (1 + c)) ^ (Fintype.card ι - 1) := by
  let _ : IsProbabilityMeasure (expMeasure 1) :=
    isProbabilityMeasure_expMeasure zero_lt_one
  have hpos : ∀ᵐ x ∂Measure.pi (fun _ : ι => expMeasure 1), ∀ i, 0 < x i := by
    have hone : ∀ᵐ y : ℝ ∂(expMeasure 1), 0 < y := by
      have hnot := measure_eq_zero_iff_ae_notMem.mp expMeasure_one_Iic_zero
      filter_upwards [hnot] with y hy
      simpa only [Set.mem_Iic, not_le] using hy
    exact ae_forall_fintype fun i =>
      Measure.tendsto_eval_ae_ae.eventually hone
  have hfactor : ∀ᵐ x ∂Measure.pi (fun _ : ι => expMeasure 1),
      ENNReal.ofReal ((∑ i, x i) * Real.exp (-(c * ∑ i, x i))) =
        ∑ i, ENNReal.ofReal (x i * Real.exp (-(c * ∑ j, x j))) := by
    filter_upwards [hpos] with x hx
    rw [Finset.sum_mul, ENNReal.ofReal_sum_of_nonneg]
    intro i _hi
    exact mul_nonneg (hx i).le (Real.exp_nonneg _)
  calc
    (∫⁻ x : ι → ℝ,
        ENNReal.ofReal ((∑ i, x i) * Real.exp (-(c * ∑ i, x i)))
        ∂Measure.pi (fun _ : ι => expMeasure 1)) =
        ∫⁻ x : ι → ℝ,
          ∑ i, ENNReal.ofReal (x i * Real.exp (-(c * ∑ j, x j)))
          ∂Measure.pi (fun _ : ι => expMeasure 1) :=
      lintegral_congr_ae hfactor
    _ = ∑ i, ∫⁻ x : ι → ℝ,
          ENNReal.ofReal (x i * Real.exp (-(c * ∑ j, x j)))
          ∂Measure.pi (fun _ : ι => expMeasure 1) := by
      rw [lintegral_finsetSum]
      intro i _hi
      fun_prop
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _hi
      exact pi_exp_laplace_first_coordinate i c hc

/-- A raw `Gamma(2,1)` variable is strictly positive almost surely. -/
private lemma ae_rawGammaTwoLaw_pos : ∀ᵐ t ∂rawGammaTwoLaw, 0 < t := by
  have hzero : rawGammaTwoLaw (Iic (0 : ℝ)) = 0 := by
    unfold rawGammaTwoLaw
    rw [withDensity_apply _ measurableSet_Iic]
    change (∫⁻ t : ℝ, rawGammaTwoDensity t
      ∂((volume.restrict (Ioi (0 : ℝ))).restrict (Iic 0))) = 0
    rw [Measure.restrict_restrict measurableSet_Iic]
    have hinter : Iic (0 : ℝ) ∩ Ioi 0 = ∅ := by ext t; simp
    rw [hinter, Measure.restrict_empty, lintegral_zero_measure]
  have hnot := measure_eq_zero_iff_ae_notMem.mp hzero
  filter_upwards [hnot] with t ht
  simpa only [Set.mem_Iic, not_le] using ht

private lemma rawGammaTwoLaw_univ : rawGammaTwoLaw Set.univ = 1 := by
  calc
    rawGammaTwoLaw Set.univ =
        rawGammaTwoLaw (Iic (0 : ℝ) ∪ Ioi 0) := by
      congr 1
      ext t
      simp only [Set.mem_univ, Set.mem_union, Set.mem_Iic, Set.mem_Ioi,
        true_iff]
      exact le_or_gt t 0
    _ = rawGammaTwoLaw (Iic (0 : ℝ)) + rawGammaTwoLaw (Ioi 0) := by
      rw [measure_union]
      · exact Set.disjoint_left.2 (by
          intro t ht0 ht1
          change t ≤ 0 at ht0
          change 0 < t at ht1
          exact (not_lt_of_ge ht0) ht1)
      · exact measurableSet_Ioi
    _ = 1 := by
      have hzero : rawGammaTwoLaw (Iic (0 : ℝ)) = 0 :=
        measure_eq_zero_iff_ae_notMem.mpr (by
          filter_upwards [ae_rawGammaTwoLaw_pos] with t ht
          simpa only [Set.mem_Iic, not_le] using ht)
      rw [hzero, rawGammaTwoLaw_Ioi 0 (le_refl 0)]
      simp

private noncomputable instance : IsProbabilityMeasure rawGammaTwoLaw :=
  ⟨rawGammaTwoLaw_univ⟩

/-- The scaled share of a two-clock sum among that pair and a finite family of
remaining clocks. -/
noncomputable def scaledPairShare {ι : Type} [Fintype ι]
    (z : (ι → ℝ) × ℝ) : ℝ :=
  (Fintype.card ι + 2 : ℝ) * z.2 / (z.2 + ∑ i, z.1 i)

private lemma measurable_scaledPairShare {ι : Type} [Fintype ι] :
    Measurable (scaledPairShare : ((ι → ℝ) × ℝ) → ℝ) := by
  unfold scaledPairShare
  fun_prop

/- Tail law of the scaled normalized sum of two exponential clocks, after
grouping the other clocks into an independent product. -/
set_option maxHeartbeats 4000000 in
private lemma restProd_rawGamma_scaledPairShare_Ioi
    {ι : Type} [Fintype ι] (s : ℝ) (hs0 : 0 ≤ s)
    (hsk : s < Fintype.card ι + 2) :
    ((Measure.pi (fun _ : ι => expMeasure 1)).prod rawGammaTwoLaw)
        {z | s < scaledPairShare z} =
      ENNReal.ofReal
        ((1 - s / (Fintype.card ι + 2 : ℝ)) ^ Fintype.card ι *
          (1 + (Fintype.card ι : ℝ) *
            (s / (Fintype.card ι + 2 : ℝ)))) := by
  let _ : IsProbabilityMeasure (expMeasure 1) :=
    isProbabilityMeasure_expMeasure zero_lt_one
  let n : ℕ := Fintype.card ι
  let k : ℝ := n + 2
  let c : ℝ := s / (k - s)
  have hkpos : 0 < k := by dsimp [k, n]; positivity
  have hkspos : 0 < k - s := sub_pos.mpr (by simpa [k, n] using hsk)
  have hc0 : 0 ≤ c := div_nonneg hs0 hkspos.le
  have hpos : ∀ᵐ x ∂Measure.pi (fun _ : ι => expMeasure 1), ∀ i, 0 < x i := by
    have hone : ∀ᵐ y : ℝ ∂(expMeasure 1), 0 < y := by
      have hnot := measure_eq_zero_iff_ae_notMem.mp expMeasure_one_Iic_zero
      filter_upwards [hnot] with y hy
      simpa only [Set.mem_Iic, not_le] using hy
    exact ae_forall_fintype fun i =>
      Measure.tendsto_eval_ae_ae.eventually hone
  have hset : MeasurableSet {z : (ι → ℝ) × ℝ | s < scaledPairShare z} :=
    measurableSet_lt measurable_const measurable_scaledPairShare
  rw [Measure.prod_apply hset]
  have hsection : ∀ᵐ x ∂Measure.pi (fun _ : ι => expMeasure 1),
      rawGammaTwoLaw
          (Prod.mk x ⁻¹' {z : (ι → ℝ) × ℝ | s < scaledPairShare z}) =
        ENNReal.ofReal
          ((c * ∑ i, x i + 1) * Real.exp (-(c * ∑ i, x i))) := by
    filter_upwards [hpos] with x hx
    have hsum0 : 0 ≤ ∑ i, x i :=
      Finset.sum_nonneg fun i _ => (hx i).le
    have hpre : rawGammaTwoLaw
        (Prod.mk x ⁻¹' {z : (ι → ℝ) × ℝ | s < scaledPairShare z}) =
        rawGammaTwoLaw (Ioi (c * ∑ i, x i)) := by
      apply measure_congr
      filter_upwards [ae_rawGammaTwoLaw_pos] with t ht
      apply propext
      change (s < k * t / (t + ∑ i, x i) ↔ c * ∑ i, x i < t)
      have hden : 0 < t + ∑ i, x i := add_pos_of_pos_of_nonneg ht hsum0
      dsimp [c]
      have hcR : s / (k - s) * (∑ i, x i) =
          s * (∑ i, x i) / (k - s) := by ring
      constructor
      · intro h
        have hcross := (lt_div_iff₀ hden).mp h
        rw [hcR]
        apply (div_lt_iff₀ hkspos).2
        nlinarith
      · intro h
        rw [hcR] at h
        have hcross := (div_lt_iff₀ hkspos).1 h
        apply (lt_div_iff₀ hden).2
        nlinarith
    rw [hpre, rawGammaTwoLaw_Ioi]
    exact mul_nonneg hc0 hsum0
  rw [lintegral_congr_ae hsection]
  have hsplit : ∀ x : ι → ℝ, (∀ i, 0 ≤ x i) →
      ENNReal.ofReal
          ((c * ∑ i, x i + 1) * Real.exp (-(c * ∑ i, x i))) =
        ENNReal.ofReal (Real.exp (-(c * ∑ i, x i))) +
          ENNReal.ofReal c *
            ENNReal.ofReal ((∑ i, x i) * Real.exp (-(c * ∑ i, x i))) := by
    intro x hx
    have hsum0 : 0 ≤ ∑ i, x i := Finset.sum_nonneg fun i _ => hx i
    rw [show (c * ∑ i, x i + 1) * Real.exp (-(c * ∑ i, x i)) =
        Real.exp (-(c * ∑ i, x i)) +
          c * ((∑ i, x i) * Real.exp (-(c * ∑ i, x i))) by ring]
    rw [ENNReal.ofReal_add (Real.exp_nonneg _)
      (mul_nonneg hc0 (mul_nonneg hsum0 (Real.exp_nonneg _))),
      ← ENNReal.ofReal_mul hc0]
  have hsplit_ae : ∀ᵐ x ∂Measure.pi (fun _ : ι => expMeasure 1),
      ENNReal.ofReal
          ((c * ∑ i, x i + 1) * Real.exp (-(c * ∑ i, x i))) =
        ENNReal.ofReal (Real.exp (-(c * ∑ i, x i))) +
          ENNReal.ofReal c *
            ENNReal.ofReal ((∑ i, x i) * Real.exp (-(c * ∑ i, x i))) := by
    filter_upwards [hpos] with x hx
    exact hsplit x fun i => (hx i).le
  rw [lintegral_congr_ae hsplit_ae, lintegral_add_left (by fun_prop),
    lintegral_const_mul _ (by fun_prop), pi_exp_laplace c hc0,
    pi_exp_laplace_total c hc0]
  dsimp only [n, k, c]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hbase : 0 ≤ 1 / (1 + s / ((Fintype.card ι : ℝ) + 2 - s)) := by
    positivity
  rw [← ENNReal.ofReal_pow hbase (Fintype.card ι - 1)]
  rw [show (Fintype.card ι : ENNReal) =
      ENNReal.ofReal (Fintype.card ι : ℝ) by simp]
  rw [← one_div_pow]
  rw [← ENNReal.ofReal_mul (pow_nonneg hbase 2),
    ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ Fintype.card ι),
    ← ENNReal.ofReal_mul hc0,
    ← ENNReal.ofReal_add (pow_nonneg hbase _) (by positivity)]
  congr 1
  have hdenne : (Fintype.card ι : ℝ) + 2 - s ≠ 0 := by positivity
  have hkne : (Fintype.card ι : ℝ) + 2 ≠ 0 := by positivity
  have hb_eq : 1 / (1 + s / ((Fintype.card ι : ℝ) + 2 - s)) =
      1 - s / ((Fintype.card ι : ℝ) + 2) := by
    field_simp [hdenne, hkne]
    ring
  rw [hb_eq]
  by_cases hn : Fintype.card ι = 0
  · simp [hn]
  · have hnpos : 0 < Fintype.card ι := Nat.pos_of_ne_zero hn
    have hpow :
        (1 - s / ((Fintype.card ι : ℝ) + 2)) ^ 2 *
            (1 - s / ((Fintype.card ι : ℝ) + 2)) ^
              (Fintype.card ι - 1) =
          (1 - s / ((Fintype.card ι : ℝ) + 2)) ^ Fintype.card ι *
            (1 - s / ((Fintype.card ι : ℝ) + 2)) := by
      rw [← pow_add, ← pow_succ]
      congr 1
      omega
    rw [hpow]
    have hcb :
        s / ((Fintype.card ι : ℝ) + 2 - s) *
            (1 - s / ((Fintype.card ι : ℝ) + 2)) =
          s / ((Fintype.card ι : ℝ) + 2) := by
      field_simp [hdenne, hkne]
    have hcb' :
        c * (1 - s / ((Fintype.card ι : ℝ) + 2)) =
          s / ((Fintype.card ι : ℝ) + 2) := by
      simpa only [c, k, n] using hcb
    calc
      (1 - s / ((Fintype.card ι : ℝ) + 2)) ^ Fintype.card ι +
          c * ((Fintype.card ι : ℝ) *
            ((1 - s / ((Fintype.card ι : ℝ) + 2)) ^ Fintype.card ι *
              (1 - s / ((Fintype.card ι : ℝ) + 2)))) =
          (1 - s / ((Fintype.card ι : ℝ) + 2)) ^ Fintype.card ι *
            (1 + (Fintype.card ι : ℝ) *
              (c * (1 - s / ((Fintype.card ι : ℝ) + 2)))) := by ring
      _ = _ := by rw [hcb']

/-! ### Literal scaled-Beta(2,k-2) law -/

/-- The probability law with the literal density used by
`SharedRace.betaTwoExpMoment`. -/
noncomputable def scaledBetaTwoLaw (k : ℕ) : Measure ℝ :=
  (volume.restrict (Ioc (0 : ℝ) (k : ℝ))).withDensity
    (fun x => ENNReal.ofReal (SharedRace.betaTwoDensity k x))

private lemma betaTwoTailAnti_hasDerivAt (k : ℕ) (hk : 3 ≤ k) (x : ℝ) :
    HasDerivAt (SharedRace.betaTwoCallDeriv k)
      (SharedRace.betaTwoDensity k x) x := by
  unfold SharedRace.betaTwoCallDeriv SharedRace.betaTwoDensity
  have hbase : HasDerivAt (fun y : ℝ => 1 - y / (k : ℝ))
      (-1 / (k : ℝ)) x := by
    convert (hasDerivAt_const x 1).sub
      ((hasDerivAt_id x).div_const (k : ℝ)) using 1
    all_goals first | rfl | simp [div_eq_mul_inv]
  have hlinear : HasDerivAt
      (fun y : ℝ => 1 + ((k : ℝ) - 2) * y / (k : ℝ))
      (((k : ℝ) - 2) / (k : ℝ)) x := by
    convert (hasDerivAt_const x 1).add
      (((hasDerivAt_const x ((k : ℝ) - 2)).mul
        (hasDerivAt_id x)).div_const (k : ℝ)) using 1
    all_goals first | rfl | simp [div_eq_mul_inv]
  have hcast : ((k - 2 : ℕ) : ℝ) = (k : ℝ) - 2 := by
    rw [Nat.cast_sub (show 2 ≤ k by omega), Nat.cast_ofNat]
  have hpow : (1 - x / (k : ℝ)) ^ (k - 2) =
      (1 - x / (k : ℝ)) ^ (k - 3) * (1 - x / (k : ℝ)) := by
    rw [show k - 2 = (k - 3) + 1 by omega, pow_succ]
  have halg :
      -(((k - 2 : ℕ) : ℝ) * (1 - x / (k : ℝ)) ^ ((k - 2) - 1) *
            (-1 / (k : ℝ)) * (1 + ((k : ℝ) - 2) * x / (k : ℝ)) +
          (1 - x / (k : ℝ)) ^ (k - 2) * (((k : ℝ) - 2) / (k : ℝ))) =
        (((k : ℝ) - 1) * ((k : ℝ) - 2) / (k : ℝ) ^ 2) * x *
          (1 - x / (k : ℝ)) ^ (k - 3) := by
    rw [show (k - 2) - 1 = k - 3 by omega, hcast, hpow]
    field_simp [show (k : ℝ) ≠ 0 by positivity]
    ring
  convert ((hbase.pow (k - 2)).mul hlinear).neg using 1
  all_goals first
    | rfl
    | simpa only [Pi.mul_apply, Pi.pow_apply, id_eq] using halg.symm

private lemma integral_betaTwoDensity (k : ℕ) (hk : 3 ≤ k)
    {s : ℝ} (_hs0 : 0 ≤ s) (_hsk : s ≤ k) :
    (∫ x : ℝ in s..(k : ℝ), SharedRace.betaTwoDensity k x) =
      (1 - s / (k : ℝ)) ^ (k - 2) *
        (1 + ((k : ℝ) - 2) * s / (k : ℝ)) := by
  have hint : IntervalIntegrable (SharedRace.betaTwoDensity k)
      volume s (k : ℝ) := by
    exact (by
      unfold SharedRace.betaTwoDensity
      fun_prop : Continuous (SharedRace.betaTwoDensity k)).intervalIntegrable _ _
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := s) (b := (k : ℝ))
    (f := SharedRace.betaTwoCallDeriv k)
    (f' := SharedRace.betaTwoDensity k)
    (fun x _hx => betaTwoTailAnti_hasDerivAt k hk x) hint
  have hk0 : (k : ℝ) ≠ 0 := by positivity
  have hpow : k - 2 ≠ 0 := by omega
  unfold SharedRace.betaTwoCallDeriv at hftc
  simpa [hk0, hpow] using hftc

/-- Tail of the literal scaled-Beta(2,k-2) density. -/
lemma scaledBetaTwoLaw_Ioi (k : ℕ) (hk : 3 ≤ k) (s : ℝ)
    (hs0 : 0 ≤ s) (hsk : s < k) :
    scaledBetaTwoLaw k (Ioi s) =
      ENNReal.ofReal
        ((1 - s / (k : ℝ)) ^ (k - 2) *
          (1 + ((k : ℝ) - 2) * s / (k : ℝ))) := by
  have hdensity_nonneg : ∀ x ∈ Ioc s (k : ℝ),
      0 ≤ SharedRace.betaTwoDensity k x := by
    intro x hx
    unfold SharedRace.betaTwoDensity
    have hkR : (3 : ℝ) ≤ k := by exact_mod_cast hk
    have hkpos : (0 : ℝ) < k := by positivity
    exact mul_nonneg
      (mul_nonneg (div_nonneg (mul_nonneg (by linarith) (by linarith))
        (sq_nonneg _)) (lt_of_le_of_lt hs0 hx.1).le)
      (pow_nonneg (sub_nonneg.mpr ((div_le_one hkpos).2 hx.2)) _)
  have hdensity_int : IntegrableOn (SharedRace.betaTwoDensity k)
      (Ioc s (k : ℝ)) := by
    exact ((by
      unfold SharedRace.betaTwoDensity
      fun_prop : Continuous (SharedRace.betaTwoDensity k)).intervalIntegrable
        s (k : ℝ)).1
  unfold scaledBetaTwoLaw
  rw [withDensity_apply _ measurableSet_Ioi]
  change (∫⁻ x, ENNReal.ofReal (SharedRace.betaTwoDensity k x)
    ∂((volume.restrict (Ioc 0 (k : ℝ))).restrict (Ioi s))) = _
  rw [Measure.restrict_restrict measurableSet_Ioi]
  have hinter : Ioc 0 (k : ℝ) ∩ Ioi s = Ioc s (k : ℝ) := by
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
  rw [(intervalIntegral.integral_of_le hsk.le).symm,
    integral_betaTwoDensity k hk hs0 hsk.le]

private lemma scaledBetaTwoLaw_isProbability (k : ℕ) (hk : 3 ≤ k) :
    IsProbabilityMeasure (scaledBetaTwoLaw k) := by
  constructor
  have htail := scaledBetaTwoLaw_Ioi k hk 0 (le_refl 0) (by positivity)
  have hnonpos : scaledBetaTwoLaw k (Iic (0 : ℝ)) = 0 := by
    unfold scaledBetaTwoLaw
    rw [withDensity_apply _ measurableSet_Iic]
    change (∫⁻ x, ENNReal.ofReal (SharedRace.betaTwoDensity k x)
      ∂((volume.restrict (Ioc 0 (k : ℝ))).restrict (Iic 0))) = 0
    rw [Measure.restrict_restrict measurableSet_Iic]
    have hinter : Iic (0 : ℝ) ∩ Ioc 0 (k : ℝ) = ∅ := by
      ext x
      constructor
      · intro hx
        exact False.elim ((not_lt_of_ge hx.1) hx.2.1)
      · intro hx
        exact False.elim hx
    rw [hinter, Measure.restrict_empty, lintegral_zero_measure]
  calc
    scaledBetaTwoLaw k Set.univ =
        scaledBetaTwoLaw k (Iic (0 : ℝ) ∪ Ioi 0) := by
      congr 1
      ext x
      simp only [Set.mem_univ, Set.mem_union, Set.mem_Iic, Set.mem_Ioi,
        true_iff]
      exact le_or_gt x 0
    _ = scaledBetaTwoLaw k (Iic (0 : ℝ)) +
        scaledBetaTwoLaw k (Ioi 0) := by
      rw [measure_union]
      · exact Set.disjoint_left.2 (by
          intro x hx0 hx1
          change x ≤ 0 at hx0
          change 0 < x at hx1
          exact (not_lt_of_ge hx0) hx1)
      · exact measurableSet_Ioi
    _ = 1 := by
      rw [hnonpos, htail]
      simp

private lemma ae_scaledPairShare_pos_le {ι : Type} [Fintype ι] :
    ∀ᵐ z ∂((Measure.pi (fun _ : ι => expMeasure 1)).prod rawGammaTwoLaw),
      0 < scaledPairShare z ∧ scaledPairShare z ≤ (Fintype.card ι + 2 : ℝ) := by
  let _ : IsProbabilityMeasure (expMeasure 1) :=
    isProbabilityMeasure_expMeasure zero_lt_one
  have hrest : ∀ᵐ x ∂Measure.pi (fun _ : ι => expMeasure 1), ∀ i, 0 < x i := by
    have hone : ∀ᵐ y : ℝ ∂(expMeasure 1), 0 < y := by
      have hnot := measure_eq_zero_iff_ae_notMem.mp expMeasure_one_Iic_zero
      filter_upwards [hnot] with y hy
      simpa only [Set.mem_Iic, not_le] using hy
    exact ae_forall_fintype fun i =>
      Measure.tendsto_eval_ae_ae.eventually hone
  apply (Measure.ae_prod_iff_ae_ae (by
    apply MeasurableSet.inter
    · exact measurableSet_lt measurable_const measurable_scaledPairShare
    · exact measurableSet_le measurable_scaledPairShare measurable_const)).2
  filter_upwards [hrest] with x hx
  filter_upwards [ae_rawGammaTwoLaw_pos] with t ht
  have hsum0 : 0 ≤ ∑ i, x i :=
    Finset.sum_nonneg fun i _ => (hx i).le
  have hkpos : (0 : ℝ) < Fintype.card ι + 2 := by positivity
  have hden : 0 < t + ∑ i, x i := add_pos_of_pos_of_nonneg ht hsum0
  constructor
  · unfold scaledPairShare
    positivity
  · unfold scaledPairShare
    apply (div_le_iff₀ hden).2
    nlinarith

/-- The scaled normalized sum of two clocks has exactly the literal
`k * Beta(2,k-2)` law, where `k` is the total number of clocks. -/
theorem restProd_rawGamma_scaledPairShare_map_eq_scaledBetaTwoLaw
    {ι : Type} [Fintype ι] [Nonempty ι] :
    Measure.map scaledPairShare
        ((Measure.pi (fun _ : ι => expMeasure 1)).prod rawGammaTwoLaw) =
      scaledBetaTwoLaw (Fintype.card ι + 2) := by
  let _ : IsProbabilityMeasure (expMeasure 1) :=
    isProbabilityMeasure_expMeasure zero_lt_one
  let Y : ((ι → ℝ) × ℝ) → ℝ := scaledPairShare
  let μ : Measure ℝ :=
    Measure.map Y ((Measure.pi (fun _ : ι => expMeasure 1)).prod rawGammaTwoLaw)
  let ν : Measure ℝ := scaledBetaTwoLaw (Fintype.card ι + 2)
  have hY : Measurable Y := measurable_scaledPairShare
  have hk : 3 ≤ Fintype.card ι + 2 := by
    have : 1 ≤ Fintype.card ι := Fintype.card_pos
    omega
  let _ : IsProbabilityMeasure μ :=
    Measure.isProbabilityMeasure_map hY.aemeasurable
  let _ : IsProbabilityMeasure ν :=
    scaledBetaTwoLaw_isProbability (Fintype.card ι + 2) hk
  have htail : ∀ s : ℝ, μ (Ioi s) = ν (Ioi s) := by
    intro s
    by_cases hs0 : 0 ≤ s
    · by_cases hsk : s < (Fintype.card ι + 2 : ℝ)
      · dsimp only [μ, ν, Y]
        rw [Measure.map_apply hY measurableSet_Ioi]
        change ((Measure.pi (fun _ : ι => expMeasure 1)).prod rawGammaTwoLaw)
            {z | s < scaledPairShare z} =
          scaledBetaTwoLaw (Fintype.card ι + 2) (Ioi s)
        have hsk' : s < ((Fintype.card ι + 2 : ℕ) : ℝ) := by
          norm_num
          exact hsk
        rw [
          restProd_rawGamma_scaledPairShare_Ioi s hs0 hsk,
          scaledBetaTwoLaw_Ioi (Fintype.card ι + 2) hk s hs0 hsk']
        norm_num
        rw [← mul_div_assoc]
      · have hks : (Fintype.card ι + 2 : ℝ) ≤ s := le_of_not_gt hsk
        have hμzero : μ (Ioi s) = 0 := by
          dsimp only [μ]
          rw [Measure.map_apply hY measurableSet_Ioi]
          apply measure_eq_zero_iff_ae_notMem.mpr
          filter_upwards [ae_scaledPairShare_pos_le (ι := ι)] with z hz
          simp only [Set.mem_preimage, Set.mem_Ioi, not_lt]
          exact hz.2.trans hks
        have hνzero : ν (Ioi s) = 0 := by
          dsimp only [ν]
          unfold scaledBetaTwoLaw
          rw [withDensity_apply _ measurableSet_Ioi]
          have hks' : ((Fintype.card ι + 2 : ℕ) : ℝ) ≤ s := by
            norm_num at hks ⊢
            exact hks
          change (∫⁻ x, ENNReal.ofReal
              (SharedRace.betaTwoDensity (Fintype.card ι + 2) x)
            ∂((volume.restrict (Ioc 0 ((Fintype.card ι + 2 : ℕ) : ℝ))).restrict
              (Ioi s))) = 0
          rw [Measure.restrict_restrict measurableSet_Ioi]
          have hinter : Ioi s ∩ Ioc 0 ((Fintype.card ι + 2 : ℕ) : ℝ) = ∅ := by
            ext x
            constructor
            · intro hx
              exact False.elim
                (not_lt_of_ge hx.2.2 (hks'.trans_lt hx.1))
            · intro hx
              exact False.elim hx
          rw [hinter, Measure.restrict_empty, lintegral_zero_measure]
        rw [hμzero, hνzero]
    · have hsneg : s < 0 := lt_of_not_ge hs0
      have hμone : μ (Ioi s) = 1 := by
        dsimp only [μ]
        rw [Measure.map_apply hY measurableSet_Ioi]
        calc
          ((Measure.pi (fun _ : ι => expMeasure 1)).prod rawGammaTwoLaw)
              (Y ⁻¹' Ioi s) =
              ((Measure.pi (fun _ : ι => expMeasure 1)).prod rawGammaTwoLaw)
                Set.univ := by
            apply measure_congr
            filter_upwards [ae_scaledPairShare_pos_le (ι := ι)] with z hz
            apply propext
            change (s < Y z ↔ True)
            exact iff_true_intro (hsneg.trans hz.1)
          _ = 1 := measure_univ
      have hνzero : ν (Iic s) = 0 := by
        dsimp only [ν]
        unfold scaledBetaTwoLaw
        rw [withDensity_apply _ measurableSet_Iic]
        change (∫⁻ x, ENNReal.ofReal
            (SharedRace.betaTwoDensity (Fintype.card ι + 2) x)
          ∂((volume.restrict (Ioc 0 ((Fintype.card ι + 2 : ℕ) : ℝ))).restrict
            (Iic s))) = 0
        rw [Measure.restrict_restrict measurableSet_Iic]
        have hinter : Iic s ∩ Ioc 0 ((Fintype.card ι + 2 : ℕ) : ℝ) = ∅ := by
          ext x
          constructor
          · intro hx
            exact False.elim (not_lt_of_ge hx.1 (hsneg.trans hx.2.1))
          · intro hx
            exact False.elim hx
        rw [hinter, Measure.restrict_empty, lintegral_zero_measure]
      have hνone : ν (Ioi s) = 1 := by
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

/-- Integrating an exponential against the shape-two density yields
`betaTwoExpMoment`. -/
lemma integral_exp_scaledBetaTwoLaw_eq_betaTwoExpMoment (k : ℕ)
    (hk : 3 ≤ k) (lam : ℝ) :
    (∫ t : ℝ, Real.exp (lam * t) ∂(scaledBetaTwoLaw k)) =
      SharedRace.betaTwoExpMoment k lam := by
  have hdensity_nonneg : ∀ x ∈ Ioc (0 : ℝ) (k : ℝ),
      0 ≤ SharedRace.betaTwoDensity k x := by
    intro x hx
    unfold SharedRace.betaTwoDensity
    have hkR : (3 : ℝ) ≤ k := by exact_mod_cast hk
    have hkpos : (0 : ℝ) < k := by positivity
    exact mul_nonneg
      (mul_nonneg (div_nonneg (mul_nonneg (by linarith) (by linarith))
        (sq_nonneg _)) hx.1.le)
      (pow_nonneg (sub_nonneg.mpr ((div_le_one hkpos).2 hx.2)) _)
  unfold scaledBetaTwoLaw
  rw [integral_withDensity_eq_integral_toReal_smul
    (by
      exact ENNReal.measurable_ofReal.comp (by
        unfold SharedRace.betaTwoDensity
        fun_prop))
    (by simp)]
  change (∫ t : ℝ in Ioc 0 (k : ℝ),
      (ENNReal.ofReal (SharedRace.betaTwoDensity k t)).toReal *
        Real.exp (lam * t)) = SharedRace.betaTwoExpMoment k lam
  have hremove :
      (∫ t : ℝ in Ioc 0 (k : ℝ),
          (ENNReal.ofReal (SharedRace.betaTwoDensity k t)).toReal *
            Real.exp (lam * t)) =
        ∫ t : ℝ in Ioc 0 (k : ℝ),
          Real.exp (lam * t) * SharedRace.betaTwoDensity k t := by
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    dsimp only
    rw [ENNReal.toReal_ofReal (hdensity_nonneg t ht)]
    ring
  rw [hremove]
  unfold SharedRace.betaTwoExpMoment
  exact (intervalIntegral.integral_of_le (by
    exact_mod_cast (Nat.zero_le k))).symm

/-- In the abstract product coordinates, the normalized pair share and the
within-pair ratio are independent, with scaled-Beta and uniform laws. -/
theorem restRawUniform_joint_map_eq
    {ι : Type} [Fintype ι] [Nonempty ι] :
    Measure.map
        (fun z : (((ι → ℝ) × ℝ) × ℝ) => (scaledPairShare z.1, z.2))
        (((Measure.pi (fun _ : ι => expMeasure 1)).prod rawGammaTwoLaw).prod
          uniformUnitLaw) =
      (scaledBetaTwoLaw (Fintype.card ι + 2)).prod uniformUnitLaw := by
  let _ : IsProbabilityMeasure (expMeasure 1) :=
    isProbabilityMeasure_expMeasure zero_lt_one
  have hshare : Measurable (scaledPairShare : ((ι → ℝ) × ℝ) → ℝ) :=
    measurable_scaledPairShare
  calc
    Measure.map
        (fun z : (((ι → ℝ) × ℝ) × ℝ) => (scaledPairShare z.1, z.2))
        (((Measure.pi (fun _ : ι => expMeasure 1)).prod rawGammaTwoLaw).prod
          uniformUnitLaw) =
        (Measure.map scaledPairShare
          ((Measure.pi (fun _ : ι => expMeasure 1)).prod rawGammaTwoLaw)).prod
            (Measure.map id uniformUnitLaw) := by
      exact (Measure.map_prod_map
        ((Measure.pi (fun _ : ι => expMeasure 1)).prod rawGammaTwoLaw)
        uniformUnitLaw hshare measurable_id).symm
    _ = _ := by
      rw [restProd_rawGamma_scaledPairShare_map_eq_scaledBetaTwoLaw,
        Measure.map_id]

/-! ### Transport back to a finite family of iid clocks -/

/-- The two selected labels, as a subtype of the full index type. -/
abbrev pairIndex {κ : Type} (a j : κ) : Type :=
  {i : κ // i = a ∨ i = j}

/-- All labels outside the selected pair. -/
abbrev pairRestIndex {κ : Type} (a j : κ) : Type :=
  {i : κ // ¬(i = a ∨ i = j)}

private noncomputable def finTwoEquivPairIndex {κ : Type} [DecidableEq κ]
    (a j : κ) (haj : a ≠ j) : Fin 2 ≃ pairIndex a j where
  toFun i := if i = 0 then ⟨a, Or.inl rfl⟩ else ⟨j, Or.inr rfl⟩
  invFun x := if x.1 = a then 0 else 1
  left_inv i := by
    fin_cases i
    · simp
    · simp [haj.symm]
  right_inv x := by
    apply Subtype.ext
    rcases x.2 with h | h
    · have hx : x = ⟨a, Or.inl rfl⟩ := Subtype.ext h
      rw [hx]
      simp
    · have hx : x = ⟨j, Or.inr rfl⟩ := Subtype.ext h
      rw [hx]
      simp [haj.symm]

/-- Read a function on the selected two-label subtype in `(a,j)` order. -/
noncomputable def pairExtractEquiv {κ : Type} [DecidableEq κ]
    (a j : κ) (haj : a ≠ j) :
    (pairIndex a j → ℝ) ≃ᵐ (ℝ × ℝ) :=
  (MeasurableEquiv.piCongrLeft (fun _ : pairIndex a j => ℝ)
      (finTwoEquivPairIndex a j haj)).symm.trans
    (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℝ))

private lemma pairExtractEquiv_apply {κ : Type} [DecidableEq κ]
    (a j : κ) (haj : a ≠ j) (x : pairIndex a j → ℝ) :
    pairExtractEquiv a j haj x =
      (x ⟨a, Or.inl rfl⟩, x ⟨j, Or.inr rfl⟩) := by
  apply Prod.ext
  · let g := MeasurableEquiv.piCongrLeft
      (fun _ : pairIndex a j => ℝ) (finTwoEquivPairIndex a j haj)
    change g.symm x 0 = _
    have h := congrFun (g.apply_symm_apply x) ((finTwoEquivPairIndex a j haj) 0)
    rw [MeasurableEquiv.piCongrLeft_apply_apply] at h
    simpa [finTwoEquivPairIndex] using h
  · let g := MeasurableEquiv.piCongrLeft
      (fun _ : pairIndex a j => ℝ) (finTwoEquivPairIndex a j haj)
    change g.symm x 1 = _
    have h := congrFun (g.apply_symm_apply x) ((finTwoEquivPairIndex a j haj) 1)
    rw [MeasurableEquiv.piCongrLeft_apply_apply] at h
    simpa [finTwoEquivPairIndex, haj] using h

private lemma card_pairRestIndex {κ : Type} [Fintype κ] [DecidableEq κ]
    (a j : κ) (haj : a ≠ j) :
    Fintype.card (pairRestIndex a j) + 2 = Fintype.card κ := by
  have hpair : Fintype.card (pairIndex a j) = 2 :=
    Fintype.card_congr (finTwoEquivPairIndex a j haj).symm
  have hinj : Function.Injective
      (fun i : Fin 2 => ((finTwoEquivPairIndex a j haj) i : κ)) := by
    intro x y hxy
    apply (finTwoEquivPairIndex a j haj).injective
    exact Subtype.ext hxy
  have hle : 2 ≤ Fintype.card κ := by
    simpa using Fintype.card_le_of_injective _ hinj
  change Fintype.card {i : κ // ¬(i = a ∨ i = j)} + 2 = Fintype.card κ
  rw [Fintype.card_subtype_compl, hpair, Nat.sub_add_cancel hle]

private lemma clockTotal_eq_pair_add_rest {κ : Type} [Fintype κ]
    [DecidableEq κ] (a j : κ) (haj : a ≠ j) (W : κ → ℝ) :
    SharedRace.clockTotal W =
      W a + W j + ∑ i : pairRestIndex a j, W i := by
  have hpair : (∑ i : pairIndex a j, W i) = W a + W j := by
    calc
      (∑ i : pairIndex a j, W i) =
          ∑ i : Fin 2, W ((finTwoEquivPairIndex a j haj) i) :=
        ((finTwoEquivPairIndex a j haj).sum_comp
          (fun x : pairIndex a j => W x.1)).symm
      _ = _ := by
        rw [Fin.sum_univ_two]
        simp [finTwoEquivPairIndex]
  unfold SharedRace.clockTotal
  rw [← Fintype.sum_subtype_add_sum_subtype
    (fun i : κ => i = a ∨ i = j) W, hpair]

/-- The load-bearing joint clock law: the scaled normalized sum of two
distinct clocks is independent of their within-pair ratio. -/
theorem clockLaw_pairShareRatio_map_eq {κ : Type} [Fintype κ]
    [DecidableEq κ] [Nonempty κ] (a j : κ) (haj : a ≠ j)
    (hk : 3 ≤ Fintype.card κ) :
    Measure.map
        (fun W : κ → ℝ =>
          ((Fintype.card κ : ℝ) * (W a + W j) /
              SharedRace.clockTotal W,
            W a / (W a + W j)))
        (clockLaw κ) =
      (scaledBetaTwoLaw (Fintype.card κ)).prod uniformUnitLaw := by
  classical
  let _ : IsProbabilityMeasure (expMeasure 1) :=
    isProbabilityMeasure_expMeasure zero_lt_one
  let P := pairIndex a j
  let R := pairRestIndex a j
  let pairLaw : Measure (P → ℝ) := Measure.pi (fun _ : P => expMeasure 1)
  let restLaw : Measure (R → ℝ) := Measure.pi (fun _ : R => expMeasure 1)
  let expPair : Measure (ℝ × ℝ) := (expMeasure 1).prod (expMeasure 1)
  let rawRatio : Measure (ℝ × ℝ) := rawGammaTwoLaw.prod uniformUnitLaw
  have hcard : Fintype.card R + 2 = Fintype.card κ := by
    simpa [R] using card_pairRestIndex a j haj
  have hRpos : 0 < Fintype.card R := by omega
  let _ : Nonempty R := Fintype.card_pos_iff.mp hRpos
  let split := MeasurableEquiv.piEquivPiSubtypeProd
    (fun _ : κ => ℝ) (fun i : κ => i = a ∨ i = j)
  have hsplit : MeasurePreserving split (clockLaw κ)
      (pairLaw.prod restLaw) := by
    have h := measurePreserving_piEquivPiSubtypeProd
      (fun _ : κ => expMeasure 1) (fun i : κ => i = a ∨ i = j)
    simpa only [clockLaw, split, pairLaw, restLaw, P, R] using h
  have hswap : MeasurePreserving Prod.swap (pairLaw.prod restLaw)
      (restLaw.prod pairLaw) := by
    exact ⟨measurable_swap, Measure.prod_swap⟩
  let ePair := finTwoEquivPairIndex a j haj
  let gPair := MeasurableEquiv.piCongrLeft (fun _ : P => ℝ) ePair
  have hgPair : MeasurePreserving gPair
      (Measure.pi (fun _ : Fin 2 => expMeasure 1)) pairLaw := by
    simpa only [gPair, ePair, pairLaw, P] using
      measurePreserving_piCongrLeft (fun _ : P => expMeasure 1) ePair
  have hgPairSymm : MeasurePreserving gPair.symm pairLaw
      (Measure.pi (fun _ : Fin 2 => expMeasure 1)) :=
    MeasurePreserving.symm gPair hgPair
  have hfinPair : MeasurePreserving
      (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℝ))
      (Measure.pi (fun _ : Fin 2 => expMeasure 1)) expPair := by
    simpa only [expPair] using
      measurePreserving_piFinTwo (fun _ : Fin 2 => expMeasure 1)
  have hextract : MeasurePreserving (pairExtractEquiv a j haj)
      pairLaw expPair := by
    have h := hfinPair.comp hgPairSymm
    change MeasurePreserving
      (fun x => (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℝ)) (gPair.symm x))
      pairLaw expPair
    simpa only [Function.comp_def] using h
  have hrestExtract : MeasurePreserving
      (Prod.map id (pairExtractEquiv a j haj))
      (restLaw.prod pairLaw) (restLaw.prod expPair) :=
    (MeasurePreserving.id restLaw).prod hextract
  have hsumRatio : MeasurePreserving pairSumRatio expPair rawRatio := by
    exact ⟨measurable_pairSumRatio, by
      simpa only [expPair, rawRatio] using map_pairSumRatio_expPair⟩
  have hrestSumRatio : MeasurePreserving (Prod.map id pairSumRatio)
      (restLaw.prod expPair) (restLaw.prod rawRatio) :=
    (MeasurePreserving.id restLaw).prod hsumRatio
  have hassoc : MeasurePreserving
      (MeasurableEquiv.prodAssoc :
        (((R → ℝ) × ℝ) × ℝ) ≃ᵐ ((R → ℝ) × (ℝ × ℝ))).symm
      (restLaw.prod rawRatio)
      ((restLaw.prod rawGammaTwoLaw).prod uniformUnitLaw) := by
    exact MeasurePreserving.symm MeasurableEquiv.prodAssoc
      (by simpa only [rawRatio] using
        measurePreserving_prodAssoc restLaw rawGammaTwoLaw uniformUnitLaw)
  let joint : ((((R → ℝ) × ℝ) × ℝ)) → ℝ × ℝ :=
    fun z => (scaledPairShare z.1, z.2)
  have hjoint : MeasurePreserving joint
      ((restLaw.prod rawGammaTwoLaw).prod uniformUnitLaw)
      ((scaledBetaTwoLaw (Fintype.card R + 2)).prod uniformUnitLaw) := by
    refine ⟨?_, ?_⟩
    · dsimp only [joint]
      exact (measurable_scaledPairShare.comp measurable_fst).prodMk measurable_snd
    · simpa only [joint, restLaw, R] using
        (restRawUniform_joint_map_eq (ι := R))
  let fullTransform : (κ → ℝ) → ℝ × ℝ :=
    joint ∘
      (MeasurableEquiv.prodAssoc :
        (((R → ℝ) × ℝ) × ℝ) ≃ᵐ ((R → ℝ) × (ℝ × ℝ))).symm ∘
      Prod.map id pairSumRatio ∘
      Prod.map id (pairExtractEquiv a j haj) ∘
      Prod.swap ∘ split
  have hfull : MeasurePreserving fullTransform (clockLaw κ)
      ((scaledBetaTwoLaw (Fintype.card R + 2)).prod uniformUnitLaw) := by
    exact hjoint.comp (hassoc.comp
      (hrestSumRatio.comp (hrestExtract.comp (hswap.comp hsplit))))
  have hfun : fullTransform = fun W : κ → ℝ =>
      ((Fintype.card κ : ℝ) * (W a + W j) /
          SharedRace.clockTotal W,
        W a / (W a + W j)) := by
    funext W
    dsimp only [fullTransform, Function.comp_apply, joint]
    simp only [split, MeasurableEquiv.piEquivPiSubtypeProd_apply]
    change
      (((Fintype.card R : ℝ) + 2) *
          ((pairExtractEquiv a j haj (fun x : pairIndex a j => W x.1)).1 +
            (pairExtractEquiv a j haj (fun x : pairIndex a j => W x.1)).2) /
          (((pairExtractEquiv a j haj (fun x : pairIndex a j => W x.1)).1 +
              (pairExtractEquiv a j haj (fun x : pairIndex a j => W x.1)).2) +
            ∑ x : pairRestIndex a j, W x.1),
        (pairExtractEquiv a j haj (fun x : pairIndex a j => W x.1)).1 /
          ((pairExtractEquiv a j haj (fun x : pairIndex a j => W x.1)).1 +
            (pairExtractEquiv a j haj (fun x : pairIndex a j => W x.1)).2)) =
        ((Fintype.card κ : ℝ) * (W a + W j) /
            SharedRace.clockTotal W,
          W a / (W a + W j))
    rw [pairExtractEquiv_apply]
    rw [clockTotal_eq_pair_add_rest a j haj W, ← hcard]
    congr 1
    norm_num
  rw [← hfun]
  rw [hfull.map_eq, hcard]

/-- The raw two selected clocks have their iid exponential product law. -/
theorem clockLaw_pairEval_map_eq {κ : Type} [Fintype κ]
    [DecidableEq κ] [Nonempty κ] (a j : κ) (haj : a ≠ j) :
    Measure.map (fun W : κ → ℝ => (W a, W j)) (clockLaw κ) =
      (expMeasure 1).prod (expMeasure 1) := by
  let _ : IsProbabilityMeasure (expMeasure 1) :=
    isProbabilityMeasure_expMeasure zero_lt_one
  have hind : iIndepFun (fun l (W : κ → ℝ) => W l) (clockLaw κ) := by
    unfold clockLaw
    simpa only [id_eq] using
      (iIndepFun_pi (μ := fun _ : κ => expMeasure 1)
        (X := fun _ => id) (fun _ => aemeasurable_id))
  have hp := (hind.indepFun haj).map_prod_eq_prod_map_map
    (measurable_pi_apply a).aemeasurable (measurable_pi_apply j).aemeasurable
  have ha : Measure.map (fun W : κ → ℝ => W a) (clockLaw κ) =
      expMeasure 1 := by
    unfold clockLaw
    exact (measurePreserving_eval (fun _ : κ => expMeasure 1) a).map_eq
  have hj : Measure.map (fun W : κ → ℝ => W j) (clockLaw κ) =
      expMeasure 1 := by
    unfold clockLaw
    exact (measurePreserving_eval (fun _ : κ => expMeasure 1) j).map_eq
  rw [ha, hj] at hp
  exact hp

/-- For any two distinct clocks, their within-pair ratio is uniform on the
unit interval. -/
theorem clockLaw_pairRatio_map_eq_uniformUnitLaw {κ : Type} [Fintype κ]
    [DecidableEq κ] [Nonempty κ] (a j : κ) (haj : a ≠ j) :
    Measure.map (fun W : κ → ℝ => W a / (W a + W j)) (clockLaw κ) =
      uniformUnitLaw := by
  let evalPair : (κ → ℝ) → ℝ × ℝ := fun W => (W a, W j)
  have heval : Measurable evalPair := by
    dsimp only [evalPair]
    fun_prop
  have hratio : Measurable (fun z : ℝ × ℝ => (pairSumRatio z).2) :=
    measurable_snd.comp measurable_pairSumRatio
  calc
    Measure.map (fun W : κ → ℝ => W a / (W a + W j)) (clockLaw κ) =
        Measure.map (fun z : ℝ × ℝ => (pairSumRatio z).2)
          (Measure.map evalPair (clockLaw κ)) := by
      rw [Measure.map_map hratio heval]
      rfl
    _ = Measure.map (fun z : ℝ × ℝ => (pairSumRatio z).2)
          ((expMeasure 1).prod (expMeasure 1)) := by
      rw [clockLaw_pairEval_map_eq a j haj]
    _ = Measure.map Prod.snd
          (Measure.map pairSumRatio ((expMeasure 1).prod (expMeasure 1))) := by
      rw [Measure.map_map measurable_snd measurable_pairSumRatio]
      rfl
    _ = Measure.map Prod.snd (rawGammaTwoLaw.prod uniformUnitLaw) := by
      rw [map_pairSumRatio_expPair]
    _ = uniformUnitLaw := measurePreserving_snd.map_eq

/-- Degenerate two-clock joint law: the scaled pair share is constantly two,
while the within-pair ratio remains uniform. -/
theorem clockLaw_pairShareRatio_map_eq_two {κ : Type} [Fintype κ]
    [DecidableEq κ] [Nonempty κ] (a j : κ) (haj : a ≠ j)
    (hk : Fintype.card κ = 2) :
    Measure.map
        (fun W : κ → ℝ =>
          ((Fintype.card κ : ℝ) * (W a + W j) /
              SharedRace.clockTotal W,
            W a / (W a + W j)))
        (clockLaw κ) =
      (Measure.dirac (2 : ℝ)).prod uniformUnitLaw := by
  have hcard := card_pairRestIndex a j haj
  have hRzero : Fintype.card (pairRestIndex a j) = 0 := by omega
  let _ : IsEmpty (pairRestIndex a j) := Fintype.card_eq_zero_iff.mp hRzero
  have hae :
      (fun W : κ → ℝ =>
          ((Fintype.card κ : ℝ) * (W a + W j) /
              SharedRace.clockTotal W,
            W a / (W a + W j))) =ᵐ[clockLaw κ]
        (fun W : κ → ℝ => ((2 : ℝ), W a / (W a + W j))) := by
    filter_upwards [SharedRace.ae_clockLaw_pos (κ := κ)] with W hW
    apply Prod.ext
    · have hrest : (∑ i : pairRestIndex a j, W i.1) = 0 :=
        Finset.sum_eq_zero (fun i _hi => isEmptyElim i)
      rw [clockTotal_eq_pair_add_rest a j haj W, hrest, add_zero, hk]
      have hsum : W a + W j ≠ 0 :=
        (add_pos (hW a) (hW j)).ne'
      field_simp [hsum]
      norm_num
    · rfl
  calc
    Measure.map
        (fun W : κ → ℝ =>
          ((Fintype.card κ : ℝ) * (W a + W j) /
              SharedRace.clockTotal W,
            W a / (W a + W j)))
        (clockLaw κ) =
        Measure.map (fun W : κ → ℝ => ((2 : ℝ), W a / (W a + W j)))
          (clockLaw κ) := Measure.map_congr hae
    _ = Measure.map (Prod.mk (2 : ℝ))
          (Measure.map (fun W : κ → ℝ => W a / (W a + W j)) (clockLaw κ)) := by
      rw [Measure.map_map]
      · rfl
      · fun_prop
      · fun_prop
    _ = Measure.map (Prod.mk (2 : ℝ)) uniformUnitLaw := by
      rw [clockLaw_pairRatio_map_eq_uniformUnitLaw a j haj]
    _ = (Measure.dirac (2 : ℝ)).prod uniformUnitLaw :=
      (Measure.dirac_prod (2 : ℝ)).symm

/-! ### Clock-ready loser-moment corollaries -/

/-- The losing-coordinate statistic expressed in the independent coordinates
`(scaled pair share, within-pair ratio)`. -/
noncomputable def pairMobiusIntegrand (p : ℝ) (sv : ℝ × ℝ) : ℝ :=
  let x := SharedRace.mobius p sv.2
  x ^ 2 * Real.exp (sv.1 * SharedRace.loserExponent p x)

lemma measurable_pairMobiusIntegrand (p : ℝ) :
    Measurable (pairMobiusIntegrand p) := by
  unfold pairMobiusIntegrand SharedRace.mobius
    SharedRace.loserExponent
  fun_prop

private lemma continuousOn_pairMobiusIntegrand_rectangle (k : ℕ) {p : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) :
    ContinuousOn (pairMobiusIntegrand p)
      (Icc (0 : ℝ) k ×ˢ Icc (0 : ℝ) 1) := by
  intro sv hsv
  have hv : sv.2 ∈ Icc (0 : ℝ) 1 := hsv.2
  have hforward : 0 < p * sv.2 + 1 - sv.2 := by
    have hq : 0 ≤ 1 - p := sub_nonneg.mpr hp1.le
    have hv' : 0 ≤ 1 - sv.2 := sub_nonneg.mpr hv.2
    nlinarith [mul_nonneg hq hv']
  have hx := SharedRace.mobius_mem_Icc hp0 hp1 hv
  have hdensity : 0 < p + (1 - p) * SharedRace.mobius p sv.2 :=
    add_pos_of_pos_of_nonneg hp0
      (mul_nonneg (sub_nonneg.mpr hp1.le) hx.1)
  apply ContinuousAt.continuousWithinAt
  unfold pairMobiusIntegrand SharedRace.mobius
    SharedRace.loserExponent
  fun_prop (disch := positivity)

private lemma ae_scaledBetaTwoLaw_mem_Ioc (k : ℕ) :
    ∀ᵐ s ∂scaledBetaTwoLaw k, s ∈ Ioc (0 : ℝ) k := by
  unfold scaledBetaTwoLaw
  exact Filter.Eventually.filter_mono
    (withDensity_absolutelyContinuous
      (volume.restrict (Ioc (0 : ℝ) k))
      (fun x => ENNReal.ofReal (SharedRace.betaTwoDensity k x))).ae_le
    (ae_restrict_mem measurableSet_Ioc)

private lemma ae_uniformUnitLaw_mem_Ioo :
    ∀ᵐ v ∂uniformUnitLaw, v ∈ Ioo (0 : ℝ) 1 := by
  unfold uniformUnitLaw
  exact ae_restrict_mem measurableSet_Ioo

private lemma integrable_pairMobiusIntegrand_prod (k : ℕ) (hk : 3 ≤ k)
    {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    Integrable (pairMobiusIntegrand p)
      ((scaledBetaTwoLaw k).prod uniformUnitLaw) := by
  let _ : IsProbabilityMeasure (scaledBetaTwoLaw k) :=
    scaledBetaTwoLaw_isProbability k hk
  let K : Set (ℝ × ℝ) := Icc (0 : ℝ) k ×ˢ Icc (0 : ℝ) 1
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hcont : ContinuousOn (pairMobiusIntegrand p) K := by
    simpa only [K] using continuousOn_pairMobiusIntegrand_rectangle k hp0 hp1
  have himage : IsCompact (pairMobiusIntegrand p '' K) :=
    hK.image_of_continuousOn hcont
  obtain ⟨C, hC⟩ := himage.isBounded.exists_norm_le
  apply Integrable.of_bound
    (measurable_pairMobiusIntegrand p).aestronglyMeasurable C
  have hs := ae_scaledBetaTwoLaw_mem_Ioc k
  have hv := ae_uniformUnitLaw_mem_Ioo
  rw [Measure.ae_prod_iff_ae_ae
    (measurableSet_le (measurable_pairMobiusIntegrand p).norm measurable_const)]
  filter_upwards [hs] with s hs
  filter_upwards [hv] with v hv
  exact hC _ ⟨(s, v), ⟨Ioc_subset_Icc_self hs, ⟨hv.1.le, hv.2.le⟩⟩, rfl⟩

/-- Product-coordinate evaluation of the losing statistic in the
nondegenerate `k ≥ 3` branch. -/
theorem integral_pairMobiusIntegrand_prod_eq_beta (k : ℕ) (hk : 3 ≤ k)
    {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    (∫ sv : ℝ × ℝ, pairMobiusIntegrand p sv
        ∂((scaledBetaTwoLaw k).prod uniformUnitLaw)) =
      ∫ v : ℝ in 0..1,
        SharedRace.loserBetaIntegrand k p
          (SharedRace.mobius p v) := by
  let _ : IsProbabilityMeasure (scaledBetaTwoLaw k) :=
    scaledBetaTwoLaw_isProbability k hk
  have hint := integrable_pairMobiusIntegrand_prod k hk hp0 hp1
  have hinner : ∀ v : ℝ,
      (∫ s : ℝ, pairMobiusIntegrand p (s, v) ∂scaledBetaTwoLaw k) =
        SharedRace.loserBetaIntegrand k p
          (SharedRace.mobius p v) := by
    intro v
    unfold pairMobiusIntegrand SharedRace.loserBetaIntegrand
    dsimp only
    rw [integral_const_mul]
    congr 1
    simpa only [mul_comm] using
      integral_exp_scaledBetaTwoLaw_eq_betaTwoExpMoment k hk
        (SharedRace.loserExponent p (SharedRace.mobius p v))
  rw [integral_prod_symm _ hint]
  simp_rw [hinner]
  unfold uniformUnitLaw
  rw [← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le zero_le_one]

/-- Product-coordinate evaluation in the degenerate `k = 2` branch. -/
theorem integral_pairMobiusIntegrand_prod_eq_degenerate (p : ℝ) :
    (∫ sv : ℝ × ℝ, pairMobiusIntegrand p sv
        ∂((Measure.dirac (2 : ℝ)).prod uniformUnitLaw)) =
      ∫ v : ℝ in 0..1,
        SharedRace.loserDegenerateIntegrand p
          (SharedRace.mobius p v) := by
  rw [Measure.dirac_prod]
  rw [integral_map]
  · unfold pairMobiusIntegrand SharedRace.loserDegenerateIntegrand
    dsimp only
    unfold uniformUnitLaw
    rw [← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le zero_le_one]
  · exact measurable_const.prodMk measurable_id |>.aemeasurable
  · exact (measurable_pairMobiusIntegrand p).aestronglyMeasurable

/-- Clock-law evaluation of the fresh losing-pair statistic for `k ≥ 3`. -/
theorem integral_pairMobiusIntegrand_clockLaw_eq_beta
    {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (a j : κ) (haj : a ≠ j) (hk : 3 ≤ Fintype.card κ)
    {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    (∫ W : κ → ℝ,
        pairMobiusIntegrand p
          ((Fintype.card κ : ℝ) * (W a + W j) /
              SharedRace.clockTotal W,
            W a / (W a + W j))
        ∂clockLaw κ) =
      ∫ v : ℝ in 0..1,
        SharedRace.loserBetaIntegrand (Fintype.card κ) p
          (SharedRace.mobius p v) := by
  let transform : (κ → ℝ) → ℝ × ℝ := fun W =>
    ((Fintype.card κ : ℝ) * (W a + W j) /
        SharedRace.clockTotal W,
      W a / (W a + W j))
  have htransform : Measurable transform := by
    dsimp only [transform]
    exact ((measurable_const.mul
      ((measurable_pi_apply a).add (measurable_pi_apply j))).div
        SharedRace.measurable_clockTotal).prodMk
      ((measurable_pi_apply a).div
        ((measurable_pi_apply a).add (measurable_pi_apply j)))
  calc
    (∫ W : κ → ℝ, pairMobiusIntegrand p (transform W) ∂clockLaw κ) =
        ∫ sv : ℝ × ℝ, pairMobiusIntegrand p sv
          ∂Measure.map transform (clockLaw κ) :=
      (integral_map htransform.aemeasurable
        (measurable_pairMobiusIntegrand p).aestronglyMeasurable).symm
    _ = ∫ sv : ℝ × ℝ, pairMobiusIntegrand p sv
          ∂((scaledBetaTwoLaw (Fintype.card κ)).prod uniformUnitLaw) := by
      rw [clockLaw_pairShareRatio_map_eq a j haj hk]
    _ = _ := integral_pairMobiusIntegrand_prod_eq_beta
      (Fintype.card κ) hk hp0 hp1

/-- Clock-law evaluation in the degenerate two-label branch. -/
theorem integral_pairMobiusIntegrand_clockLaw_eq_degenerate
    {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (a j : κ) (haj : a ≠ j) (hk : Fintype.card κ = 2) (p : ℝ) :
    (∫ W : κ → ℝ,
        pairMobiusIntegrand p
          ((Fintype.card κ : ℝ) * (W a + W j) /
              SharedRace.clockTotal W,
            W a / (W a + W j))
        ∂clockLaw κ) =
      ∫ v : ℝ in 0..1,
        SharedRace.loserDegenerateIntegrand p
          (SharedRace.mobius p v) := by
  let transform : (κ → ℝ) → ℝ × ℝ := fun W =>
    ((Fintype.card κ : ℝ) * (W a + W j) /
        SharedRace.clockTotal W,
      W a / (W a + W j))
  have htransform : Measurable transform := by
    dsimp only [transform]
    exact ((measurable_const.mul
      ((measurable_pi_apply a).add (measurable_pi_apply j))).div
        SharedRace.measurable_clockTotal).prodMk
      ((measurable_pi_apply a).div
        ((measurable_pi_apply a).add (measurable_pi_apply j)))
  calc
    (∫ W : κ → ℝ, pairMobiusIntegrand p (transform W) ∂clockLaw κ) =
        ∫ sv : ℝ × ℝ, pairMobiusIntegrand p sv
          ∂Measure.map transform (clockLaw κ) :=
      (integral_map htransform.aemeasurable
        (measurable_pairMobiusIntegrand p).aestronglyMeasurable).symm
    _ = ∫ sv : ℝ × ℝ, pairMobiusIntegrand p sv
          ∂((Measure.dirac (2 : ℝ)).prod uniformUnitLaw) := by
      rw [clockLaw_pairShareRatio_map_eq_two a j haj hk]
    _ = _ := integral_pairMobiusIntegrand_prod_eq_degenerate p

end SharedRace
end stoch_to_det
