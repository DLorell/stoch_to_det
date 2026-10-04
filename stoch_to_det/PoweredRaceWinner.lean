import stoch_to_det.Race

/-! A fourth-power clock reference. Its winning log score is an exact KL
identity; only the bounded partition-function expectation remains to bound. -/

namespace stoch_to_det.SharedRace

open Finset MeasureTheory

variable {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]

/-- Bounded normalization of the fourth powers of inverse prior clocks. -/
noncomputable def poweredRaceZ (π E : κ → ℝ) : ℝ :=
  ∑ i, raceRatio π E i ^ 4

/-- The fourth-power reference categorical law. -/
noncomputable def poweredReferencePMF (π E : κ → ℝ) (i : κ) : ℝ :=
  raceRatio π E i ^ 4 / poweredRaceZ π E

lemma measurable_clockArgmin [MeasurableSpace κ] [MeasurableSingletonClass κ]
    (π : κ → ℝ) : Measurable (clockArgmin π) := by
  unfold clockArgmin
  apply measurable_lexMax
  intro i
  change Measurable (fun E : κ → ℝ => -(E i / π i))
  fun_prop

lemma measurable_rawRaceMin (π : κ → ℝ) : Measurable (rawRaceMin π) := by
  let : MeasurableSpace κ := ⊤
  have harg : Measurable (clockArgmin π) := measurable_clockArgmin π
  have hsum : Measurable (fun E : κ → ℝ =>
      ∑ i, if clockArgmin π E = i then E i / π i else 0) := by
    apply Finset.measurable_sum
    intro i _
    exact Measurable.ite (measurableSet_singleton i |>.preimage harg)
      (by fun_prop) measurable_const
  have heq : rawRaceMin π = fun E : κ → ℝ =>
      ∑ i, if clockArgmin π E = i then E i / π i else 0 := by
    funext E
    unfold rawRaceMin
    simp
  rwa [heq]

lemma measurable_raceRatio (π : κ → ℝ) (i : κ) :
    Measurable (fun E : κ → ℝ => raceRatio π E i) := by
  unfold raceRatio
  exact ((measurable_rawRaceMin π).mul measurable_const).div (measurable_pi_apply i)

lemma measurable_poweredRaceZ (π : κ → ℝ) : Measurable (poweredRaceZ π) := by
  unfold poweredRaceZ
  exact Finset.measurable_sum _ fun i _ => (measurable_raceRatio π i).pow_const 4

lemma poweredRaceZ_one_le (π E : κ → ℝ)
    (hπ : ∀ i, 0 < π i) (hE : ∀ i, 0 < E i) : 1 ≤ poweredRaceZ π E := by
  have h := Finset.single_le_sum (s := (univ : Finset κ))
    (f := fun i => raceRatio π E i ^ 4)
    (fun i _ => pow_nonneg (raceRatio_pos π E hπ hE i).le _)
    (mem_univ (clockArgmin π E))
  simpa only [raceRatio_argmin π E hπ hE, one_pow, poweredRaceZ] using h

lemma poweredRaceZ_le_card (π E : κ → ℝ)
    (hπ : ∀ i, 0 < π i) (hE : ∀ i, 0 < E i) :
    poweredRaceZ π E ≤ Fintype.card κ := by
  calc
    poweredRaceZ π E ≤ ∑ _i : κ, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      exact pow_le_one₀ (raceRatio_pos π E hπ hE i).le (raceRatio_le_one π E hπ hE i)
    _ = _ := by simp

/-- The logarithm of the normalization is bounded by the sum of its losing
coordinate logarithms. The winning coordinate contributes exactly one. -/
theorem log_poweredRaceZ_le_sum_loser (π E : κ → ℝ)
    (hπ : ∀ i, 0 < π i) (hE : ∀ i, 0 < E i) :
    Real.log (poweredRaceZ π E) ≤
      ∑ i ∈ univ.erase (clockArgmin π E), Real.log (1 + raceRatio π E i ^ 4) := by
  have hprod (s : Finset κ) :
      1 + (∑ i ∈ s, raceRatio π E i ^ 4) ≤ ∏ i ∈ s, (1 + raceRatio π E i ^ 4) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
      rw [sum_insert ha, prod_insert ha]
      have hsum : 0 ≤ ∑ i ∈ s, raceRatio π E i ^ 4 :=
        Finset.sum_nonneg fun i _ => by positivity
      have hmul := mul_le_mul_of_nonneg_left ih
        (show 0 ≤ 1 + raceRatio π E a ^ 4 by positivity)
      nlinarith [mul_nonneg (show 0 ≤ raceRatio π E a ^ 4 by positivity) hsum]
  have hsum : poweredRaceZ π E =
      1 + ∑ i ∈ univ.erase (clockArgmin π E), raceRatio π E i ^ 4 := by
    have heq := Finset.sum_erase_add (s := (univ : Finset κ))
      (f := fun i => raceRatio π E i ^ 4) (mem_univ (clockArgmin π E))
    rw [raceRatio_argmin π E hπ hE, one_pow] at heq
    unfold poweredRaceZ
    linarith
  have hle : poweredRaceZ π E ≤
      ∏ i ∈ univ.erase (clockArgmin π E), (1 + raceRatio π E i ^ 4) := by
    rw [hsum]
    exact hprod _
  have hl := Real.log_le_log
    (zero_lt_one.trans_le (poweredRaceZ_one_le π E hπ hE)) hle
  rw [Real.log_prod (fun i _ => (show 0 < 1 + raceRatio π E i ^ 4 by positivity).ne')] at hl
  exact hl

lemma poweredReferencePMF_pos (π E : κ → ℝ)
    (hπ : ∀ i, 0 < π i) (hE : ∀ i, 0 < E i) (i : κ) :
    0 < poweredReferencePMF π E i := by
  exact div_pos (pow_pos (raceRatio_pos π E hπ hE i) _)
    (zero_lt_one.trans_le (poweredRaceZ_one_le π E hπ hE))

lemma poweredReferencePMF_isPMF (π E : κ → ℝ)
    (hπ : ∀ i, 0 < π i) (hE : ∀ i, 0 < E i) :
    IsPMF (poweredReferencePMF π E) := by
  constructor
  · intro i
    exact (poweredReferencePMF_pos π E hπ hE i).le
  · unfold mass poweredReferencePMF
    rw [← sum_div]
    exact div_self (ne_of_gt (zero_lt_one.trans_le (poweredRaceZ_one_le π E hπ hE)))

lemma integrable_log_poweredRaceZ (π : κ → ℝ) (hπ : ∀ i, 0 < π i) :
    Integrable (fun E : κ → ℝ => Real.log (poweredRaceZ π E)) (clockLaw κ) := by
  apply Integrable.of_bound
    (Real.measurable_log.comp (measurable_poweredRaceZ π)).aestronglyMeasurable
    (Real.log (Fintype.card κ))
  filter_upwards [ae_clockLaw_pos (κ := κ)] with E hE
  have hZ1 := poweredRaceZ_one_le π E hπ hE
  have hZ0 := zero_lt_one.trans_le hZ1
  change |Real.log (poweredRaceZ π E)| ≤ Real.log (Fintype.card κ)
  rw [abs_of_nonneg (Real.log_nonneg hZ1)]
  exact Real.log_le_log hZ0 (poweredRaceZ_le_card π E hπ hE)

/-- Each losing-coordinate logarithmic term is bounded between zero and `log 2`. -/
lemma integrable_log_one_add_raceRatio_four (π : κ → ℝ) (hπ : ∀ i, 0 < π i) (i : κ) :
    Integrable (fun E : κ → ℝ => Real.log (1 + raceRatio π E i ^ 4)) (clockLaw κ) := by
  have hm : Measurable (fun E : κ → ℝ => Real.log (1 + raceRatio π E i ^ 4)) :=
    Real.measurable_log.comp (measurable_const.add ((measurable_raceRatio π i).pow_const 4))
  apply Integrable.of_bound hm.aestronglyMeasurable (Real.log 2)
  filter_upwards [ae_clockLaw_pos (κ := κ)] with E hE
  have hR0 := (raceRatio_pos π E hπ hE i).le
  have hR1 := raceRatio_le_one π E hπ hE i
  have hpow : raceRatio π E i ^ 4 ≤ 1 := pow_le_one₀ hR0 hR1
  have harg : 1 ≤ 1 + raceRatio π E i ^ 4 := le_add_of_nonneg_right (by positivity)
  change |Real.log (1 + raceRatio π E i ^ 4)| ≤ Real.log 2
  rw [abs_of_nonneg (Real.log_nonneg harg)]
  apply Real.log_le_log (zero_lt_one.trans_le harg)
  linarith

lemma log_inv_poweredReferencePMF (π E : κ → ℝ)
    (hπ : ∀ i, 0 < π i) (hE : ∀ i, 0 < E i) (i : κ) :
    Real.log (1 / poweredReferencePMF π E i) =
      Real.log (poweredRaceZ π E) - 4 * Real.log (raceRatio π E i) := by
  have hR := raceRatio_pos π E hπ hE i
  have hZ := zero_lt_one.trans_le (poweredRaceZ_one_le π E hπ hE)
  rw [one_div, Real.log_inv, poweredReferencePMF,
    Real.log_div (pow_ne_zero _ hR.ne') hZ.ne', Real.log_pow]
  push_cast
  ring

lemma integrable_log_inv_poweredReferencePMF_clockArgmin
    (π r : κ → ℝ) (hπ : ∀ i, 0 < π i) (hπtotal : ∑ i, π i = 1)
    (hr : ∀ i, 0 < r i) (hrtotal : ∑ i, r i = 1)
    (hk : 2 ≤ Fintype.card κ) :
    Integrable (fun E : κ → ℝ =>
      Real.log (1 / poweredReferencePMF π E (clockArgmin r E))) (clockLaw κ) := by
  have hZ := integrable_log_poweredRaceZ π hπ
  have hR := integrable_log_raceRatio_clockArgmin π r hπ hπtotal hr hrtotal hk
  apply (hZ.sub (hR.const_mul 4)).congr
  filter_upwards [ae_clockLaw_pos (κ := κ)] with E hE
  exact (log_inv_poweredReferencePMF π E hπ hE (clockArgmin r E)).symm

/-- The fourth-power reference loss is exactly four times the row KL plus
its common partition-function cost. -/
theorem integral_log_inv_poweredReferencePMF_clockArgmin_eq
    (π r : κ → ℝ) (hπ : ∀ i, 0 < π i) (hπtotal : ∑ i, π i = 1)
    (hr : ∀ i, 0 < r i) (hrtotal : ∑ i, r i = 1)
    (hk : 2 ≤ Fintype.card κ) :
    (∫ E : κ → ℝ, Real.log (1 / poweredReferencePMF π E (clockArgmin r E))
      ∂clockLaw κ) =
      4 * (∑ i, r i * Real.log (r i / π i)) +
        ∫ E : κ → ℝ, Real.log (poweredRaceZ π E) ∂clockLaw κ := by
  have hZ := integrable_log_poweredRaceZ π hπ
  have hR := integrable_log_raceRatio_clockArgmin π r hπ hπtotal hr hrtotal hk
  have hae : (fun E : κ → ℝ => Real.log
      (1 / poweredReferencePMF π E (clockArgmin r E))) =ᵐ[clockLaw κ]
      fun E => Real.log (poweredRaceZ π E) - 4 * Real.log (raceRatio π E (clockArgmin r E)) := by
    filter_upwards [ae_clockLaw_pos (κ := κ)] with E hE
    exact log_inv_poweredReferencePMF π E hπ hE _
  rw [integral_congr_ae hae, integral_sub hZ (hR.const_mul 4), integral_const_mul,
    integral_log_raceRatio_clockArgmin_eq π r hπ hπtotal hr hrtotal hk]
  have hlog (i : κ) : Real.log (π i / r i) = -Real.log (r i / π i) := by
    rw [Real.log_div (hπ i).ne' (hr i).ne', Real.log_div (hr i).ne' (hπ i).ne']
    ring
  simp_rw [hlog, mul_neg]
  rw [Finset.sum_neg_distrib]
  ring

end stoch_to_det.SharedRace
