import stoch_to_det.SharedRace.Clock

/-!
# Finite assembly for the normalized shared-race estimate

This file contains the measure-independent bookkeeping after the
one-coordinate estimates have been proved.  The clock-law module only has to
provide one integrable contribution for each output coordinate and its mean
bound.  The logarithmic tangent and the finite sum then close the normalized
simplex inequality.
-/

namespace stoch_to_det
namespace SharedRace

open Finset MeasureTheory

universe u

/-- Coordinatewise moment bounds against a PMF sum to a unit moment bound. -/
lemma integral_finset_sum_le_one
    {X : Type u} {κ : Type} [MeasurableSpace X] [Fintype κ]
    (μ : Measure X) (π : κ → ℝ) (hπ : IsPMF π)
    (f : κ → X → ℝ)
    (hf : ∀ i, Integrable (f i) μ)
    (hle : ∀ i, (∫ x, f i x ∂μ) ≤ π i) :
    Integrable (fun x => ∑ i, f i x) μ ∧
      (∫ x, ∑ i, f i x ∂μ) ≤ 1 := by
  have hsum : Integrable (fun x => ∑ i, f i x) μ :=
    integrable_finsetSum univ fun i _ => hf i
  refine ⟨hsum, ?_⟩
  rw [integral_finsetSum univ (fun i _ => hf i)]
  calc
    (∑ i, ∫ x, f i x ∂μ) ≤ ∑ i, π i :=
      Finset.sum_le_sum fun i _ => hle i
    _ = 1 := by simpa [mass] using hπ.total

/-- Abstract normalized-race closure.

The clock geometry is encapsulated by the coordinate functions `q`, the
normalized simplex coordinates `u`, and the normalized minimum `t`.  Once
each coordinate contribution has mean at most its prior mass, the logarithmic
tangent proves the desired `log 2` bound. -/
theorem normalizedRaceLogIntegral_le
    {X : Type u} {κ : Type} [MeasurableSpace X] [Fintype κ]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (π : κ → ℝ) (hπ : IsPMF π)
    (q u : X → κ → ℝ) (t : X → ℝ)
    (hzpos : ∀ᵐ x ∂μ,
      0 < ∑ i, (q x i) ^ 2 *
        Real.exp ((Fintype.card κ : ℝ) * SharedRace.logTwo * u x i))
    (hzlog : Integrable (fun x => Real.log
      (∑ i, (q x i) ^ 2 *
        Real.exp ((Fintype.card κ : ℝ) * SharedRace.logTwo * u x i))) μ)
    (htint : Integrable t μ)
    (htmean : (∫ x, (Fintype.card κ : ℝ) *
      SharedRace.logTwo * t x ∂μ) = SharedRace.logTwo)
    (hcoordInt : ∀ i, Integrable (fun x =>
      (q x i) ^ 2 * Real.exp ((Fintype.card κ : ℝ) *
        SharedRace.logTwo * (u x i - t x))) μ)
    (hcoord : ∀ i, (∫ x,
      (q x i) ^ 2 * Real.exp ((Fintype.card κ : ℝ) *
        SharedRace.logTwo * (u x i - t x)) ∂μ) ≤ π i) :
    (∫ x, Real.log
      (∑ i, (q x i) ^ 2 *
        Real.exp ((Fintype.card κ : ℝ) * SharedRace.logTwo * u x i))
      ∂μ) ≤ SharedRace.logTwo := by
  let c : ℝ := (Fintype.card κ : ℝ) * SharedRace.logTwo
  let z : X → ℝ := fun x =>
    ∑ i, (q x i) ^ 2 * Real.exp (c * u x i)
  let a : X → ℝ := fun x => c * t x
  let f : κ → X → ℝ := fun i x =>
    (q x i) ^ 2 * Real.exp (c * (u x i - t x))
  have hf : ∀ i, Integrable (f i) μ := by
    intro i
    simpa only [f, c, mul_assoc] using hcoordInt i
  have hfle : ∀ i, (∫ x, f i x ∂μ) ≤ π i := by
    intro i
    simpa only [f, c, mul_assoc] using hcoord i
  have hsum := integral_finset_sum_le_one μ π hπ f hf hfle
  have haInt : Integrable a μ := by
    exact htint.const_mul c
  have hmomEq : (fun x => Real.exp (-a x) * z x) =
      fun x => ∑ i, f i x := by
    funext x
    simp only [a, z, f, c]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    calc
      Real.exp (-((Fintype.card κ : ℝ) * SharedRace.logTwo * t x)) *
          ((q x i) ^ 2 *
            Real.exp ((Fintype.card κ : ℝ) * SharedRace.logTwo * u x i)) =
          (q x i) ^ 2 *
            (Real.exp (-((Fintype.card κ : ℝ) * SharedRace.logTwo * t x)) *
              Real.exp ((Fintype.card κ : ℝ) * SharedRace.logTwo * u x i)) := by
        ring
      _ = (q x i) ^ 2 * Real.exp
          (-((Fintype.card κ : ℝ) * SharedRace.logTwo * t x) +
            (Fintype.card κ : ℝ) * SharedRace.logTwo * u x i) := by
        rw [Real.exp_add]
      _ = (q x i) ^ 2 * Real.exp
          ((Fintype.card κ : ℝ) * SharedRace.logTwo * (u x i - t x)) := by
        congr 2
        ring
  have hmomInt : Integrable (fun x => Real.exp (-a x) * z x) μ := by
    rw [hmomEq]
    exact hsum.1
  have hmom : (∫ x, Real.exp (-a x) * z x ∂μ) ≤ 1 := by
    rw [hmomEq]
    exact hsum.2
  apply SharedRace.integral_log_le_logTwo_of_moment
    μ z a hzpos
  · simpa only [z, c] using hzlog
  · exact haInt
  · exact hmomInt
  · simpa only [a, c] using htmean
  · exact hmom

/-- Row-wise cross-entropy closure after the two winner-cell moments have
been identified.

This theorem deliberately keeps the probability geometry behind two compact
interfaces.  The clock module must show that the winning reference ratio has
mean log-score `∑ i, r i * log (π i / r i)`, and that the winning
normalized clock has mean `(∑ i, r i ^ 2) / k`.  The universal normalized
partition-function bound then turns the reference cross entropy into the
desired KL plus mismatch budget. -/
theorem referenceLossIntegral_le
    {X : Type u} {κ : Type} [MeasurableSpace X] [Fintype κ]
    [DecidableEq κ] [Nonempty κ]
    (μ : Measure X) (π r : κ → ℝ) (E : X → κ → ℝ) (a : X → κ)
    (hπpos : ∀ i, 0 < π i)
    (hEpos : ∀ᵐ x ∂μ, ∀ i, 0 < E x i)
    (hlogZ : Integrable (fun x => Real.log (normRaceZ π (E x))) μ)
    (hlogRatio : Integrable
      (fun x => Real.log (raceRatio π (E x) (a x))) μ)
    (hwinClock : Integrable (fun x => normClock (E x) (a x)) μ)
    (hlogZ_le : (∫ x, Real.log (normRaceZ π (E x)) ∂μ) ≤
      SharedRace.logTwo)
    (hlogRatio_eq :
      (∫ x, Real.log (raceRatio π (E x) (a x)) ∂μ) =
        ∑ i, r i * Real.log (π i / r i))
    (hwinClock_eq :
      (∫ x, normClock (E x) (a x) ∂μ) =
        (∑ i, r i ^ 2) / (Fintype.card κ : ℝ)) :
    (∫ x, Real.log (1 / referencePMF π (E x) (a x)) ∂μ) ≤
      2 * (∑ i, r i * Real.log (r i / π i)) +
        SharedRace.logTwo * (1 - ∑ i, r i ^ 2) := by
  have hkpos : (0 : ℝ) < Fintype.card κ := by
    exact_mod_cast Fintype.card_pos
  have hpoint :
      (fun x => Real.log (1 / referencePMF π (E x) (a x))) =ᵐ[μ]
        fun x =>
          Real.log (normRaceZ π (E x)) -
            2 * Real.log (raceRatio π (E x) (a x)) -
              (Fintype.card κ : ℝ) * SharedRace.logTwo *
                normClock (E x) (a x) := by
    filter_upwards [hEpos] with x hx
    exact log_inv_referencePMF π (E x) hπpos hx (a x)
  have htwoRatio : Integrable
      (fun x => 2 * Real.log (raceRatio π (E x) (a x))) μ :=
    hlogRatio.const_mul 2
  have hscaledClock : Integrable
      (fun x => (Fintype.card κ : ℝ) * SharedRace.logTwo *
        normClock (E x) (a x)) μ :=
    hwinClock.const_mul ((Fintype.card κ : ℝ) * SharedRace.logTwo)
  rw [integral_congr_ae hpoint]
  have hsplitOuter :
      (∫ x,
          (Real.log (normRaceZ π (E x)) -
            2 * Real.log (raceRatio π (E x) (a x))) -
              (Fintype.card κ : ℝ) * SharedRace.logTwo *
                normClock (E x) (a x) ∂μ) =
        (∫ x,
          Real.log (normRaceZ π (E x)) -
            2 * Real.log (raceRatio π (E x) (a x)) ∂μ) -
          ∫ x, (Fintype.card κ : ℝ) * SharedRace.logTwo *
            normClock (E x) (a x) ∂μ :=
    integral_sub (hlogZ.sub htwoRatio) hscaledClock
  have hsplitInner :
      (∫ x,
          Real.log (normRaceZ π (E x)) -
            2 * Real.log (raceRatio π (E x) (a x)) ∂μ) =
        (∫ x, Real.log (normRaceZ π (E x)) ∂μ) -
          ∫ x, 2 * Real.log (raceRatio π (E x) (a x)) ∂μ :=
    integral_sub hlogZ htwoRatio
  rw [hsplitOuter, hsplitInner, integral_const_mul, integral_const_mul,
    hlogRatio_eq, hwinClock_eq]
  calc
    (∫ x, Real.log (normRaceZ π (E x)) ∂μ) -
          2 * (∑ i, r i * Real.log (π i / r i)) -
            (Fintype.card κ : ℝ) * SharedRace.logTwo *
              ((∑ i, r i ^ 2) / (Fintype.card κ : ℝ)) ≤
        SharedRace.logTwo -
          2 * (∑ i, r i * Real.log (π i / r i)) -
            (Fintype.card κ : ℝ) * SharedRace.logTwo *
              ((∑ i, r i ^ 2) / (Fintype.card κ : ℝ)) := by
      linarith
    _ = 2 * (∑ i, r i * Real.log (r i / π i)) +
          SharedRace.logTwo * (1 - ∑ i, r i ^ 2) := by
      have hkne : (Fintype.card κ : ℝ) ≠ 0 := hkpos.ne'
      have hlog (i : κ) :
          Real.log (π i / r i) = -Real.log (r i / π i) := by
        by_cases hri : r i = 0
        · simp [hri]
        · have hpi : π i ≠ 0 := (hπpos i).ne'
          rw [Real.log_div hpi hri, Real.log_div hri hpi]
          ring
      simp_rw [hlog]
      field_simp [hkne]
      rw [Finset.sum_neg_distrib]
      ring

end SharedRace
end stoch_to_det
