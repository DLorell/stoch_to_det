import stoch_to_det.SharedRace.ClockLaw
import stoch_to_det.SharedRace.Information

/-!
# Finite source assembly for the clock-form shared race

This module performs only finite source averaging.  The analytic clock-cell
work enters through a row-wise reference-loss bound; no result from
`Race.lean` is imported.
-/

namespace stoch_to_det
namespace SharedRace

open Finset MeasureTheory

universe u

variable {Ω : Type u} {κ : Type}
  [Fintype Ω] [Fintype κ] [DecidableEq Ω] [DecidableEq κ] [Nonempty κ]

/-- Average fixed-clock entropy of the shared exponential-race winner. -/
noncomputable def clockSharedRaceEntropy
    (μ : Ω → ℝ) (r : Ω → κ → ℝ) : ℝ :=
  ∫ E, H (push (fun z => clockArgmin (r z) E) μ) ∂(clockLaw κ)

omit [DecidableEq Ω] in
/-- The fixed-clock entropy integrand is bounded and hence integrable. -/
lemma integrable_clockSharedRaceEntropy_integrand
    {μ : Ω → ℝ} (hμ : IsPMF μ) (r : Ω → κ → ℝ) :
    Integrable
      (fun E => H (push (fun z => clockArgmin (r z) E) μ))
      (clockLaw κ) := by
  let _ : MeasurableSpace κ := ⊤
  let A : (κ → ℝ) → (Ω → κ) :=
    fun E z => clockArgmin (r z) E
  let F : (Ω → κ) → ℝ := fun a => H (push a μ)
  have hA : Measurable A := by
    apply measurable_pi_lambda
    intro z
    dsimp only [A]
    unfold clockArgmin
    apply measurable_lexMax
    intro i
    change Measurable (fun E : κ → ℝ => -(E i / r z i))
    fun_prop
  have hF : Measurable F := measurable_of_finite F
  apply Integrable.of_bound (hF.comp hA).aestronglyMeasurable
    (lg (Fintype.card κ))
  filter_upwards [] with E
  have hp : IsPMF (push (A E) μ) := isPMF_push hμ
  have hnonneg : 0 ≤ H (push (A E) μ) := H_nonneg_of_isPMF hp
  have hle : H (push (A E) μ) ≤ lg (Fintype.card κ) := H_le_card hp
  simpa only [Function.comp_apply, F, A, Real.norm_eq_abs,
    abs_of_nonneg hnonneg] using hle

/-- Finite source averaging of row-wise reference-loss bounds.

The hypotheses `hrowInt` and `hrowBound` are required only on the support of
`μ`.  The conclusion is in bits; the row hypotheses use natural logarithms,
so the final step cancels the positive factor `logTwo`. -/
theorem clockSharedRaceEntropy_le_of_referenceLoss
    {μ : Ω → ℝ} {r : Ω → κ → ℝ}
    (hμ : IsPMF μ)
    (hr : ∀ z, μ z ≠ 0 → IsPMF (r z))
    (hrpos : ∀ z, μ z ≠ 0 → ∀ i, 0 < r z i)
    (hrowInt : ∀ z, μ z ≠ 0 →
      Integrable
        (fun E : κ → ℝ =>
          Real.log (1 /
            referencePMF (posteriorMean μ r) E
              (clockArgmin (r z) E)))
        (clockLaw κ))
    (hrowBound : ∀ z, μ z ≠ 0 →
      (∫ E : κ → ℝ,
          Real.log (1 /
            referencePMF (posteriorMean μ r) E
              (clockArgmin (r z) E))
          ∂(clockLaw κ)) ≤
        2 * (∑ i, r z i *
          Real.log (r z i / posteriorMean μ r i)) +
        SharedRace.logTwo * (1 - ∑ i, (r z i) ^ 2)) :
    clockSharedRaceEntropy μ r ≤
      2 * MI Prod.fst Prod.snd (posteriorJoint μ r) +
        categoricalMismatch μ r := by
  let π : κ → ℝ := posteriorMean μ r
  let a : (κ → ℝ) → Ω → κ :=
    fun E z => clockArgmin (r z) E
  let loss : Ω → (κ → ℝ) → ℝ :=
    fun z E => Real.log (1 / referencePMF π E (a E z))
  have hπpos : ∀ i, 0 < π i := by
    exact posteriorMean_pos_of_support hμ hrpos
  have hentropyInt : Integrable
      (fun E => H (push (a E) μ)) (clockLaw κ) := by
    simpa only [a] using
      integrable_clockSharedRaceEntropy_integrand hμ r
  have hlossInt : ∀ z, μ z ≠ 0 →
      Integrable (loss z) (clockLaw κ) := by
    intro z hz
    simpa only [loss, π, a] using hrowInt z hz
  have hweightedLossInt : ∀ z,
      Integrable (fun E => μ z * loss z E) (clockLaw κ) := by
    intro z
    by_cases hz : μ z = 0
    · simp [hz]
    · exact (hlossInt z hz).const_mul (μ z)
  have hsumLossInt : Integrable
      (fun E => ∑ z, μ z * loss z E) (clockLaw κ) :=
    integrable_finsetSum Finset.univ fun z _ => hweightedLossInt z
  have hpoint : ∀ᵐ E ∂(clockLaw κ),
      SharedRace.logTwo * H (push (a E) μ) ≤
        ∑ z, μ z * loss z E := by
    filter_upwards [ae_clockLaw_pos (κ := κ)] with E hE
    have hrefPMF : IsPMF (referencePMF π E) :=
      referencePMF_isPMF π E hπpos hE
    have hrefPos : ∀ i, 0 < referencePMF π E i :=
      referencePMF_pos π E hπpos hE
    have hcross := H_push_le_expected_crossEntropy
      hμ (a E) hrefPMF hrefPos
    have hscaled := mul_le_mul_of_nonneg_left hcross
      SharedRace.L_pos.le
    calc
      SharedRace.logTwo * H (push (a E) μ) ≤
          SharedRace.logTwo *
            (∑ z, μ z * lg (1 / referencePMF π E (a E z))) := hscaled
      _ = ∑ z, μ z * loss z E := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro z _
        have hconvert :
            SharedRace.logTwo *
                lg (1 / referencePMF π E (a E z)) =
              Real.log (1 / referencePMF π E (a E z)) :=
          (logTwo_mul_lg_inv_referencePMF π E hπpos hE (a E z)).trans
            (log_inv_referencePMF π E hπpos hE (a E z)).symm
        dsimp only [loss]
        rw [← hconvert]
        ring
  have hscaledEntropyInt : Integrable
      (fun E => SharedRace.logTwo * H (push (a E) μ))
      (clockLaw κ) :=
    hentropyInt.const_mul SharedRace.logTwo
  have hintegralLe :
      (∫ E, SharedRace.logTwo * H (push (a E) μ)
          ∂(clockLaw κ)) ≤
        ∫ E, ∑ z, μ z * loss z E ∂(clockLaw κ) :=
    integral_mono_ae hscaledEntropyInt hsumLossInt hpoint
  have hrowAverage :
      (∑ z, μ z * ∫ E, loss z E ∂(clockLaw κ)) ≤
        ∑ z, μ z *
          (2 * (∑ i, r z i *
            Real.log (r z i / posteriorMean μ r i)) +
          SharedRace.logTwo * (1 - ∑ i, (r z i) ^ 2)) := by
    apply Finset.sum_le_sum
    intro z _
    by_cases hz : μ z = 0
    · simp [hz]
    · exact mul_le_mul_of_nonneg_left (hrowBound z hz) (hμ.nonneg z)
  have hMI := posteriorMI_mul_logTwo_eq_expectedKL hμ hr hrpos
  have hbudget :
      (∑ z, μ z *
          (2 * (∑ i, r z i *
            Real.log (r z i / posteriorMean μ r i)) +
          SharedRace.logTwo * (1 - ∑ i, (r z i) ^ 2))) =
        SharedRace.logTwo *
          (2 * MI Prod.fst Prod.snd (posteriorJoint μ r) +
            categoricalMismatch μ r) := by
    unfold categoricalMismatch
    calc
      (∑ z, μ z *
          (2 * (∑ i, r z i *
            Real.log (r z i / posteriorMean μ r i)) +
          SharedRace.logTwo * (1 - ∑ i, (r z i) ^ 2))) =
        2 * (∑ z, μ z * ∑ i, r z i *
          Real.log (r z i / posteriorMean μ r i)) +
        SharedRace.logTwo *
          (∑ z, μ z * (1 - ∑ i, (r z i) ^ 2)) := by
            rw [Finset.mul_sum, Finset.mul_sum,
              ← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro z _
            ring
      _ = 2 * (SharedRace.logTwo *
          MI Prod.fst Prod.snd (posteriorJoint μ r)) +
        SharedRace.logTwo *
          (∑ z, μ z * (1 - ∑ i, (r z i) ^ 2)) := by
            rw [hMI]
      _ = SharedRace.logTwo *
          (2 * MI Prod.fst Prod.snd (posteriorJoint μ r) +
            ∑ z, μ z * (1 - ∑ i, (r z i) ^ 2)) := by ring
  have hnat :
      SharedRace.logTwo * clockSharedRaceEntropy μ r ≤
        SharedRace.logTwo *
          (2 * MI Prod.fst Prod.snd (posteriorJoint μ r) +
            categoricalMismatch μ r) := by
    calc
      SharedRace.logTwo * clockSharedRaceEntropy μ r =
          ∫ E, SharedRace.logTwo * H (push (a E) μ)
            ∂(clockLaw κ) := by
        unfold clockSharedRaceEntropy
        rw [integral_const_mul]
      _ ≤ ∫ E, ∑ z, μ z * loss z E ∂(clockLaw κ) := hintegralLe
      _ = ∑ z, μ z * ∫ E, loss z E ∂(clockLaw κ) := by
        rw [integral_finsetSum Finset.univ]
        · apply Finset.sum_congr rfl
          intro z _
          rw [integral_const_mul]
        · intro z _
          exact hweightedLossInt z
      _ ≤ ∑ z, μ z *
          (2 * (∑ i, r z i *
            Real.log (r z i / posteriorMean μ r i)) +
          SharedRace.logTwo * (1 - ∑ i, (r z i) ^ 2)) :=
        hrowAverage
      _ = SharedRace.logTwo *
          (2 * MI Prod.fst Prod.snd (posteriorJoint μ r) +
            categoricalMismatch μ r) := hbudget
  exact le_of_mul_le_mul_left hnat SharedRace.L_pos

end SharedRace
end stoch_to_det
