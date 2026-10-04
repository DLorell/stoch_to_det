import stoch_to_det.PoweredRaceRefined

/-! Sixth-power shared-race entropy with a five-term rational normalizer. -/
namespace stoch_to_det

/-- Five alternating logarithm terms integrated against the sixth-power tail. -/
noncomputable def poweredRaceJ6Upper : ℝ :=
  1 / 5 - 1 / 22 + 1 / 51 - 1 / 92 + 1 / 145

namespace SharedRace.Sixth

open Finset MeasureTheory Set
open scoped Interval

variable {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]

/-- Bounded normalization of the sixth powers of inverse prior clocks. -/
noncomputable def poweredRaceZ (π E : κ → ℝ) : ℝ :=
  ∑ i, raceRatio π E i ^ 6

/-- The sixth-power reference categorical law. -/
noncomputable def poweredReferencePMF (π E : κ → ℝ) (i : κ) : ℝ :=
  raceRatio π E i ^ 6 / poweredRaceZ π E

lemma measurable_poweredRaceZ (π : κ → ℝ) : Measurable (poweredRaceZ π) := by
  unfold poweredRaceZ
  exact Finset.measurable_sum _ fun i _ => (measurable_raceRatio π i).pow_const 6

lemma poweredRaceZ_one_le (π E : κ → ℝ)
    (hπ : ∀ i, 0 < π i) (hE : ∀ i, 0 < E i) : 1 ≤ poweredRaceZ π E := by
  have h := Finset.single_le_sum (s := (univ : Finset κ))
    (f := fun i => raceRatio π E i ^ 6)
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
      ∑ i ∈ univ.erase (clockArgmin π E), Real.log (1 + raceRatio π E i ^ 6) := by
  have hprod (s : Finset κ) :
      1 + (∑ i ∈ s, raceRatio π E i ^ 6) ≤ ∏ i ∈ s, (1 + raceRatio π E i ^ 6) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
      rw [sum_insert ha, prod_insert ha]
      have hsum : 0 ≤ ∑ i ∈ s, raceRatio π E i ^ 6 :=
        Finset.sum_nonneg fun i _ => by positivity
      have hmul := mul_le_mul_of_nonneg_left ih
        (show 0 ≤ 1 + raceRatio π E a ^ 6 by positivity)
      nlinarith [mul_nonneg (show 0 ≤ raceRatio π E a ^ 6 by positivity) hsum]
  have hsum : poweredRaceZ π E =
      1 + ∑ i ∈ univ.erase (clockArgmin π E), raceRatio π E i ^ 6 := by
    have heq := Finset.sum_erase_add (s := (univ : Finset κ))
      (f := fun i => raceRatio π E i ^ 6) (mem_univ (clockArgmin π E))
    rw [raceRatio_argmin π E hπ hE, one_pow] at heq
    unfold poweredRaceZ
    linarith
  have hle : poweredRaceZ π E ≤
      ∏ i ∈ univ.erase (clockArgmin π E), (1 + raceRatio π E i ^ 6) := by
    rw [hsum]
    exact hprod _
  have hl := Real.log_le_log
    (zero_lt_one.trans_le (poweredRaceZ_one_le π E hπ hE)) hle
  rw [Real.log_prod (fun i _ => (show 0 < 1 + raceRatio π E i ^ 6 by positivity).ne')] at hl
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
lemma integrable_log_one_add_raceRatio_six (π : κ → ℝ) (hπ : ∀ i, 0 < π i) (i : κ) :
    Integrable (fun E : κ → ℝ => Real.log (1 + raceRatio π E i ^ 6)) (clockLaw κ) := by
  have hm : Measurable (fun E : κ → ℝ => Real.log (1 + raceRatio π E i ^ 6)) :=
    Real.measurable_log.comp (measurable_const.add ((measurable_raceRatio π i).pow_const 6))
  apply Integrable.of_bound hm.aestronglyMeasurable (Real.log 2)
  filter_upwards [ae_clockLaw_pos (κ := κ)] with E hE
  have hR0 := (raceRatio_pos π E hπ hE i).le
  have hR1 := raceRatio_le_one π E hπ hE i
  have hpow : raceRatio π E i ^ 6 ≤ 1 := pow_le_one₀ hR0 hR1
  have harg : 1 ≤ 1 + raceRatio π E i ^ 6 := le_add_of_nonneg_right (by positivity)
  change |Real.log (1 + raceRatio π E i ^ 6)| ≤ Real.log 2
  rw [abs_of_nonneg (Real.log_nonneg harg)]
  apply Real.log_le_log (zero_lt_one.trans_le harg)
  linarith

lemma log_inv_poweredReferencePMF (π E : κ → ℝ)
    (hπ : ∀ i, 0 < π i) (hE : ∀ i, 0 < E i) (i : κ) :
    Real.log (1 / poweredReferencePMF π E i) =
      Real.log (poweredRaceZ π E) - 6 * Real.log (raceRatio π E i) := by
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
  apply (hZ.sub (hR.const_mul 6)).congr
  filter_upwards [ae_clockLaw_pos (κ := κ)] with E hE
  exact (log_inv_poweredReferencePMF π E hπ hE (clockArgmin r E)).symm

/-- The sixth-power reference loss is exactly six times the row KL plus
its common partition-function cost. -/
theorem integral_log_inv_poweredReferencePMF_clockArgmin_eq
    (π r : κ → ℝ) (hπ : ∀ i, 0 < π i) (hπtotal : ∑ i, π i = 1)
    (hr : ∀ i, 0 < r i) (hrtotal : ∑ i, r i = 1)
    (hk : 2 ≤ Fintype.card κ) :
    (∫ E : κ → ℝ, Real.log (1 / poweredReferencePMF π E (clockArgmin r E))
      ∂clockLaw κ) =
      6 * (∑ i, r i * Real.log (r i / π i)) +
        ∫ E : κ → ℝ, Real.log (poweredRaceZ π E) ∂clockLaw κ := by
  have hZ := integrable_log_poweredRaceZ π hπ
  have hR := integrable_log_raceRatio_clockArgmin π r hπ hπtotal hr hrtotal hk
  have hae : (fun E : κ → ℝ => Real.log
      (1 / poweredReferencePMF π E (clockArgmin r E))) =ᵐ[clockLaw κ]
      fun E => Real.log (poweredRaceZ π E) - 6 * Real.log (raceRatio π E (clockArgmin r E)) := by
    filter_upwards [ae_clockLaw_pos (κ := κ)] with E hE
    exact log_inv_poweredReferencePMF π E hπ hE _
  rw [integral_congr_ae hae, integral_sub hZ (hR.const_mul 6), integral_const_mul,
    integral_log_raceRatio_clockArgmin_eq π r hπ hπtotal hr hrtotal hk]
  have hlog (i : κ) : Real.log (π i / r i) = -Real.log (r i / π i) := by
    rw [Real.log_div (hπ i).ne' (hr i).ne', Real.log_div (hr i).ne' (hπ i).ne']
    ring
  simp_rw [hlog, mul_neg]
  rw [Finset.sum_neg_distrib]
  ring


noncomputable def logTaylor5 (x : ℝ) : ℝ :=
  x ^ 1 / 1 - x ^ 2 / 2 + x ^ 3 / 3 - x ^ 4 / 4 + x ^ 5 / 5

/-- Five alternating terms majorize the logarithm on the positive axis. -/
theorem log_one_add_le_five_terms {x : ℝ} (hx : 0 ≤ x) :
    Real.log (1+x) ≤ logTaylor5 x := by
  let F : ℝ → ℝ := fun x => logTaylor5 x - Real.log (1+x)
  have hd (x : ℝ) (hx : 0 ≤ x) : HasDerivAt F (x^5/(1+x)) x := by
    have hx1 : 1+x ≠ 0 := ne_of_gt (by linarith)
    have hp := (((((((hasDerivAt_id x).pow 1).div_const 1).sub
      (((hasDerivAt_id x).pow 2).div_const 2)).add
      (((hasDerivAt_id x).pow 3).div_const 3)).sub
      (((hasDerivAt_id x).pow 4).div_const 4)).add
      (((hasDerivAt_id x).pow 5).div_const 5)).sub
      (((hasDerivAt_id x).const_add 1).log hx1)
    apply hp.congr_deriv
    norm_num only [id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one, pow_zero]
    field_simp [hx1]
    ring
  have hmono : MonotoneOn F (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · intro y hy
      exact (hd y hy).continuousAt.continuousWithinAt
    · intro y hy
      have hy0 : 0 ≤ y := (interior_subset hy : y ∈ Set.Ici 0)
      exact (hd y hy0).differentiableAt.differentiableWithinAt
    · intro y hy
      have hy0 : 0 ≤ y := (interior_subset hy : y ∈ Set.Ici 0)
      rw [(hd y hy0).deriv]
      exact div_nonneg (pow_nonneg hy0 5) (by linarith)
  have h := hmono (by simp) hx hx
  norm_num [F, logTaylor5] at h
  simpa [logTaylor5] using h

noncomputable def loserLogPolynomial (x : ℝ) : ℝ :=
  x ^ 4 / 1 - x ^ 10 / 2 + x ^ 16 / 3 - x ^ 22 / 4 + x ^ 28 / 5

theorem loserLogPolynomial_identity (x : ℝ) :
    logTaylor5 (x^6) = x^2*loserLogPolynomial x := by
  unfold logTaylor5 loserLogPolynomial
  ring

theorem integral_loserLogPolynomial :
    (∫ x : ℝ in 0..1, loserLogPolynomial x) = poweredRaceJ6Upper := by
  have h1 : IntervalIntegrable (fun x : ℝ => x ^ 4 / 1) volume 0 1 :=
    (by fun_prop : Continuous (fun x : ℝ => x ^ 4 / 1)).intervalIntegrable _ _
  have h2 : IntervalIntegrable (fun x : ℝ => x ^ 10 / 2) volume 0 1 :=
    (by fun_prop : Continuous (fun x : ℝ => x ^ 10 / 2)).intervalIntegrable _ _
  have h3 : IntervalIntegrable (fun x : ℝ => x ^ 16 / 3) volume 0 1 :=
    (by fun_prop : Continuous (fun x : ℝ => x ^ 16 / 3)).intervalIntegrable _ _
  have h4 : IntervalIntegrable (fun x : ℝ => x ^ 22 / 4) volume 0 1 :=
    (by fun_prop : Continuous (fun x : ℝ => x ^ 22 / 4)).intervalIntegrable _ _
  have h5 : IntervalIntegrable (fun x : ℝ => x ^ 28 / 5) volume 0 1 :=
    (by fun_prop : Continuous (fun x : ℝ => x ^ 28 / 5)).intervalIntegrable _ _
  unfold loserLogPolynomial
  rw [intervalIntegral.integral_add (f := fun x : ℝ => x ^ 4 / 1 - x ^ 10 / 2 + x ^ 16 / 3 - x ^ 22 / 4) (g := fun x : ℝ => x ^ 28 / 5) ((((h1).sub h2).add h3).sub h4) h5]
  rw [intervalIntegral.integral_sub (f := fun x : ℝ => x ^ 4 / 1 - x ^ 10 / 2 + x ^ 16 / 3) (g := fun x : ℝ => x ^ 22 / 4) (((h1).sub h2).add h3) h4]
  rw [intervalIntegral.integral_add (f := fun x : ℝ => x ^ 4 / 1 - x ^ 10 / 2) (g := fun x : ℝ => x ^ 16 / 3) ((h1).sub h2) h3]
  rw [intervalIntegral.integral_sub (f := fun x : ℝ => x ^ 4 / 1) (g := fun x : ℝ => x ^ 10 / 2) (h1) h2]
  simp_rw [intervalIntegral.integral_div, integral_pow]
  norm_num [poweredRaceJ6Upper]

theorem powered_loser_mobius_integral_le {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    (∫ v : ℝ in 0..1, Real.log (1+(mobius p v)^6)) ≤ p*poweredRaceJ6Upper := by
  have hlogcont : Continuous (fun x : ℝ => Real.log (1+x^6)) := by
    apply Continuous.log (by fun_prop)
    intro x
    positivity
  rw [integral_comp_mobius hp0 hp1 hlogcont.continuousOn]
  have hd (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) : 0 < p+(1-p)*x := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hp1.le) hx.1]
  have hdens : ContinuousOn (mobiusDensity p) (Icc (0 : ℝ) 1) := by
    unfold mobiusDensity
    apply ContinuousOn.div continuousOn_const (by fun_prop)
    intro x hx
    exact pow_ne_zero _ (hd x hx).ne'
  have hi1 : IntervalIntegrable
      (fun x : ℝ => mobiusDensity p x * Real.log (1+x^6)) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    intro x hx
    exact (hdens x hx).mul hlogcont.continuousAt.continuousWithinAt
  have hi2 : IntervalIntegrable (fun x : ℝ => p*loserLogPolynomial x) volume 0 1 :=
    (by unfold loserLogPolynomial; fun_prop : Continuous (fun x : ℝ => p*loserLogPolynomial x)).intervalIntegrable _ _
  have hbound : (∫ x : ℝ in 0..1, mobiusDensity p x * Real.log (1+x^6)) ≤
      ∫ x : ℝ in 0..1, p*loserLogPolynomial x := by
    apply intervalIntegral.integral_mono_on (by norm_num) hi1 hi2
    intro x hx
    by_cases hxzero : x = 0
    · subst x
      norm_num [loserLogPolynomial]
    have hxpos : 0 < x := lt_of_le_of_ne hx.1 (Ne.symm hxzero)
    have hpoly := log_one_add_le_five_terms (show 0 ≤ x^6 by positivity)
    rw [loserLogPolynomial_identity] at hpoly
    have hlog0 : 0 ≤ Real.log (1+x^6) :=
      Real.log_nonneg (le_add_of_nonneg_right (by positivity))
    have hP0 : 0 ≤ loserLogPolynomial x :=
      nonneg_of_mul_nonneg_right (hlog0.trans hpoly) (sq_pos_of_pos hxpos)
    have hd0 : 0 ≤ mobiusDensity p x := by unfold mobiusDensity; positivity
    have hdenx : x ≤ p+(1-p)*x := by
      nlinarith [mul_nonneg hp0.le (sub_nonneg.mpr hx.2)]
    have hdx : mobiusDensity p x * x^2 ≤ p := by
      unfold mobiusDensity
      rw [div_mul_eq_mul_div]
      apply (div_le_iff₀ (sq_pos_of_pos (hd x hx))).2
      have hxpow : x^2 ≤ (p+(1-p)*x)^2 := pow_le_pow_left₀ hx.1 hdenx 2
      exact mul_le_mul_of_nonneg_left hxpow hp0.le
    calc
      mobiusDensity p x * Real.log (1+x^6) ≤
          mobiusDensity p x * (x^2*loserLogPolynomial x) :=
        mul_le_mul_of_nonneg_left hpoly hd0
      _ = (mobiusDensity p x*x^2)*loserLogPolynomial x := by ring
      _ ≤ p*loserLogPolynomial x := mul_le_mul_of_nonneg_right hdx hP0
  rw [intervalIntegral.integral_const_mul, integral_loserLogPolynomial] at hbound
  exact hbound

lemma integral_fresh_powered_loser_eq (p : ℝ) (hp : 0 < p)
    (a i : κ) (hai : a ≠ i) :
    (∫ W : κ → ℝ, Real.log (1 + (p * W a / (p * W a + W i)) ^ 6)
      ∂clockLaw κ) =
      ∫ v : ℝ in 0..1, Real.log (1 + (mobius p v) ^ 6) := by
  let F : ℝ → ℝ := fun v => Real.log (1 + (mobius p v) ^ 6)
  have hF : Measurable F := by unfold F mobius; fun_prop
  have hratio : Measurable (fun W : κ → ℝ => W a / (W a + W i)) := by fun_prop
  calc
    _ = ∫ W : κ → ℝ, F (W a / (W a + W i)) ∂clockLaw κ := by
      apply integral_congr_ae
      filter_upwards [ae_clockLaw_pos (κ := κ)] with W hW
      simp only [F, mobius_pairRatio hp (hW a) (hW i)]
    _ = ∫ v : ℝ, F v ∂uniformUnitLaw := by
      rw [← clockLaw_pairRatio_map_eq_uniformUnitLaw a i hai]
      exact (integral_map hratio.aemeasurable hF.aestronglyMeasurable).symm
    _ = _ := by
      unfold uniformUnitLaw
      rw [← integral_Ioc_eq_integral_Ioo,
        ← intervalIntegral.integral_of_le zero_le_one]

lemma integral_powered_loser_on_cell_eq
    (π : κ → ℝ) (hπ : ∀ i, 0 < π i) (hπtotal : ∑ i, π i = 1)
    (a i : κ) (hia : i ≠ a) :
    (∫ E : κ → ℝ, Real.log (1 + raceRatio π E i ^ 6)
      ∂(clockLaw κ).restrict {E | strictClockWin π a E}) =
      π a * ∫ v : ℝ in 0..1, Real.log (1 + (mobius (π i) v) ^ 6) := by
  let f : (κ → ℝ) → ℝ := fun W =>
    Real.log (1 + (π i * W a / (π i * W a + W i)) ^ 6)
  have hf : Measurable f := by unfold f; fun_prop
  calc
    _ = ∫ E : κ → ℝ, f (winnerResidualClock π a E)
        ∂(clockLaw κ).restrict {E | strictClockWin π a E} := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem (strictClockWin_measurableSet π a)] with E hE
      simp only [f, raceRatio_loser_eq_residual π hπ a i hia E hE]
    _ = π a * ∫ W : κ → ℝ, f W ∂clockLaw κ :=
      integral_comp_winnerResidualClock π hπ hπtotal a f hf
    _ = _ := by rw [integral_fresh_powered_loser_eq (π i) (hπ i) a i hia.symm]

/-- A scalar Möbius integral bound controls the full partition function.
The factor is the categorical variance of the reference marginal. -/
theorem integral_log_poweredRaceZ_le_of_loser_integral
    (J : ℝ)
    (hJ : ∀ p : ℝ, 0 < p → p < 1 →
      (∫ v : ℝ in 0..1, Real.log (1 + (mobius p v) ^ 6)) ≤ p * J)
    (π : κ → ℝ) (hπ : ∀ i, 0 < π i) (hπtotal : ∑ i, π i = 1) :
    (∫ E : κ → ℝ, Real.log (poweredRaceZ π E) ∂clockLaw κ) ≤
      J * (1 - ∑ i, π i ^ 2) := by
  have hcell (a : κ) :
      (∫ E : κ → ℝ, Real.log (poweredRaceZ π E)
        ∂(clockLaw κ).restrict {E | strictClockWin π a E}) ≤
      ∑ i ∈ univ.erase a, π a * (π i * J) := by
    have hs : Integrable
        (fun E : κ → ℝ => ∑ i ∈ univ.erase a, Real.log (1 + raceRatio π E i ^ 6))
        ((clockLaw κ).restrict {E | strictClockWin π a E}) := by
      apply integrable_finsetSum
      intro i _
      exact (integrable_log_one_add_raceRatio_six π hπ i).restrict
    calc
      _ ≤ ∫ E : κ → ℝ, ∑ i ∈ univ.erase a, Real.log (1 + raceRatio π E i ^ 6)
          ∂(clockLaw κ).restrict {E | strictClockWin π a E} := by
        apply integral_mono_ae (integrable_log_poweredRaceZ π hπ).restrict hs
        filter_upwards [(ae_clockLaw_pos (κ := κ)).filter_mono ae_restrict_le,
          ae_restrict_mem (strictClockWin_measurableSet π a)] with E hE ha
        have hb := log_poweredRaceZ_le_sum_loser π E hπ hE
        rwa [clockArgmin_eq_of_strictClockWin π E a ha] at hb
      _ = ∑ i ∈ univ.erase a,
          ∫ E : κ → ℝ, Real.log (1 + raceRatio π E i ^ 6)
            ∂(clockLaw κ).restrict {E | strictClockWin π a E} := by
        rw [integral_finsetSum]
        intro i _
        exact (integrable_log_one_add_raceRatio_six π hπ i).restrict
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro i hi
        have hia : i ≠ a := (Finset.mem_erase.mp hi).1
        rw [integral_powered_loser_on_cell_eq π hπ hπtotal a i hia]
        apply mul_le_mul_of_nonneg_left _ (hπ a).le
        exact hJ (π i) (hπ i) (pmf_coordinate_lt_one_of_ne π hπ hπtotal i a hia.symm)
  calc
    _ = ∑ a, ∫ E : κ → ℝ, Real.log (poweredRaceZ π E)
        ∂(clockLaw κ).restrict {E | strictClockWin π a E} :=
      integral_clock_eq_sum_strictClockWin π hπ hπtotal _ (integrable_log_poweredRaceZ π hπ)
    _ ≤ ∑ a, ∑ i ∈ univ.erase a, π a * (π i * J) :=
      Finset.sum_le_sum fun a _ => hcell a
    _ = J * (1 - ∑ i, π i ^ 2) := by
      have hsum (a : κ) : ∑ i ∈ univ.erase a, π i = 1 - π a := by
        have h := Finset.sum_erase_add (s := (univ : Finset κ))
          (f := π) (mem_univ a)
        rw [hπtotal] at h
        linarith
      simp_rw [← Finset.mul_sum, ← Finset.sum_mul, hsum]
      calc
        (∑ a, π a * ((1 - π a) * J)) =
            J * ((∑ a, π a) - ∑ a, π a ^ 2) := by
          rw [mul_sub, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro a _
          ring
        _ = _ := by rw [hπtotal]

/-- The sixth-power normalization cost is at most the certified scalar
bound times categorical variance. -/
theorem integral_log_poweredRaceZ_le
    (π : κ → ℝ) (hπ : ∀ i, 0 < π i) (hπtotal : ∑ i, π i = 1) :
    (∫ E : κ → ℝ, Real.log (poweredRaceZ π E) ∂clockLaw κ) ≤
      poweredRaceJ6Upper * (1 - ∑ i, π i ^ 2) :=
  integral_log_poweredRaceZ_le_of_loser_integral poweredRaceJ6Upper
    (fun _ hp0 hp1 => powered_loser_mobius_integral_le hp0 hp1) π hπ hπtotal

universe u

variable {Ω : Type u} {κ : Type}
  [Fintype Ω] [Fintype κ] [DecidableEq Ω] [DecidableEq κ] [Nonempty κ]

/-- Averaging the powered reference loss bounds shared-race entropy. -/
theorem clockSharedRaceEntropy_le_powered_reference
    {μ : Ω → ℝ} {r : Ω → κ → ℝ}
    (hμ : IsPMF μ)
    (hr : ∀ z, μ z ≠ 0 → IsPMF (r z))
    (hrpos : ∀ z, μ z ≠ 0 → ∀ i, 0 < r z i)
    (hk : 2 ≤ Fintype.card κ) :
    logTwo * clockSharedRaceEntropy μ r ≤
      6 * logTwo * MI Prod.fst Prod.snd (posteriorJoint μ r) +
        ∫ E : κ → ℝ, Real.log (poweredRaceZ (posteriorMean μ r) E) ∂clockLaw κ := by
  let π : κ → ℝ := posteriorMean μ r
  let A : (κ → ℝ) → Ω → κ := fun E z => clockArgmin (r z) E
  let loss : Ω → (κ → ℝ) → ℝ :=
    fun z E => Real.log (1 / poweredReferencePMF π E (A E z))
  let C : ℝ := ∫ E : κ → ℝ, Real.log (poweredRaceZ π E) ∂clockLaw κ
  have hπpos : ∀ i, 0 < π i := posteriorMean_pos_of_support hμ hrpos
  have hπ : IsPMF π := posteriorMean_isPMF_of_support hμ hr
  have hπtotal : ∑ i, π i = 1 := hπ.total
  have hloss (z : Ω) (hz : μ z ≠ 0) : Integrable (loss z) (clockLaw κ) :=
    integrable_log_inv_poweredReferencePMF_clockArgmin π (r z) hπpos hπtotal
      (hrpos z hz) (hr z hz).total hk
  have hwloss (z : Ω) : Integrable (fun E => μ z * loss z E) (clockLaw κ) := by
    by_cases hz : μ z = 0
    · simp [hz]
    · exact (hloss z hz).const_mul (μ z)
  have hsumloss : Integrable (fun E => ∑ z, μ z * loss z E) (clockLaw κ) :=
    integrable_finsetSum univ fun z _ => hwloss z
  have hH : Integrable (fun E => H (push (A E) μ)) (clockLaw κ) :=
    integrable_clockSharedRaceEntropy_integrand hμ r
  have hpoint : ∀ᵐ E ∂clockLaw κ,
      logTwo * H (push (A E) μ) ≤ ∑ z, μ z * loss z E := by
    filter_upwards [ae_clockLaw_pos (κ := κ)] with E hE
    have hc := H_push_le_expected_crossEntropy hμ (A E)
      (poweredReferencePMF_isPMF π E hπpos hE)
      (poweredReferencePMF_pos π E hπpos hE)
    have hm := mul_le_mul_of_nonneg_left hc L_pos.le
    convert hm using 1 <;> try rfl
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro z _
    dsimp [loss]
    rw [lg_eq_log_div]
    change μ z * Real.log (1 / poweredReferencePMF π E (A E z)) =
      Real.log 2 * (μ z * (Real.log (1 / poweredReferencePMF π E (A E z)) / Real.log 2))
    field_simp
  have hint := integral_mono_ae (hH.const_mul logTwo) hsumloss hpoint
  rw [integral_const_mul, integral_finsetSum univ (fun z _ => hwloss z)] at hint
  simp_rw [integral_const_mul] at hint
  have hrow (z : Ω) : μ z * (∫ E, loss z E ∂clockLaw κ) =
      μ z * (6 * (∑ i, r z i * Real.log (r z i / π i)) + C) := by
    by_cases hz : μ z = 0
    · simp [hz]
    · rw [show (∫ E, loss z E ∂clockLaw κ) = _ from
        integral_log_inv_poweredReferencePMF_clockArgmin_eq π (r z)
          hπpos hπtotal (hrpos z hz) (hr z hz).total hk]
  simp_rw [hrow] at hint
  have hsum : (∑ z, μ z * (6 * (∑ i, r z i * Real.log (r z i / π i)) + C)) =
      6 * logTwo * MI Prod.fst Prod.snd (posteriorJoint μ r) + C := by
    simp_rw [mul_add]
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, show (∑ z, μ z) = 1 from hμ.total, one_mul]
    have hm := posteriorMI_mul_logTwo_eq_expectedKL hμ hr hrpos
    calc
      (∑ z, μ z * (6 * ∑ i, r z i * Real.log (r z i / π i))) + C =
          6 * (∑ z, μ z * ∑ i, r z i * Real.log (r z i / π i)) + C := by
        congr 1
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro z _
        ring
      _ = _ := by rw [← hm]; ring
  rw [hsum] at hint
  exact hint

/-- A normalization bound and a posterior-variance estimate give the powered
shared-race entropy bound, including singleton output alphabets. -/
theorem sharedRaceEntropy_le_powered_of_dispersion
    {μ : Ω → ℝ} {r : Ω → κ → ℝ}
    (hμ : IsPMF μ)
    (hr : ∀ z, μ z ≠ 0 → IsPMF (r z))
    (hrpos : ∀ z, μ z ≠ 0 → ∀ i, 0 < r z i)
    {J : ℝ} (hJ : 0 ≤ J)
    (hZ : ∀ (π : κ → ℝ), IsPMF π → (∀ i, 0 < π i) →
      (∫ E : κ → ℝ, Real.log (poweredRaceZ π E) ∂clockLaw κ) ≤
        J * (1 - ∑ i, π i ^ 2))
    (hdisp : 1 - ∑ i, (posteriorMean μ r i)^2 ≤
      categoricalMismatch μ r + logTwo * MI Prod.fst Prod.snd (posteriorJoint μ r)) :
    sharedRaceEntropy μ r ≤ (6 + J) * MI Prod.fst Prod.snd (posteriorJoint μ r) +
      J / logTwo * categoricalMismatch μ r := by
  classical
  by_cases hk : 2 ≤ Fintype.card κ
  · rw [sharedRaceEntropy_eq_clockSharedRaceEntropy hrpos]
    have he := clockSharedRaceEntropy_le_powered_reference hμ hr hrpos hk
    have hnorm := hZ (posteriorMean μ r) (posteriorMean_isPMF_of_support hμ hr)
      (posteriorMean_pos_of_support hμ hrpos)
    have hv := mul_le_mul_of_nonneg_left hdisp hJ
    have hcancel : logTwo * (J / logTwo * categoricalMismatch μ r) =
        J * categoricalMismatch μ r := by field_simp [L_pos.ne']
    apply le_of_mul_le_mul_left (a := logTwo) _ L_pos
    nlinarith only [he, hnorm, hv, hcancel]
  · have hcard : Fintype.card κ = 1 := by
      have hpos := Fintype.card_pos (α := κ)
      omega
    have hzero (G : κ → ℝ) : H (push (sharedWinner r G) μ) = 0 := by
      have hp := isPMF_push (f := sharedWinner r G) hμ
      apply le_antisymm
      · have hle := H_le_card hp
        simpa [hcard] using hle
      · exact H_nonneg_of_isPMF hp
    have he : sharedRaceEntropy μ r = 0 := by
      unfold sharedRaceEntropy
      simp_rw [hzero]
      simp
    rw [he]
    exact add_nonneg
      (mul_nonneg (by linarith) (MI_nonneg (posteriorJoint_isPMF_of_support hμ hr)
        Prod.fst Prod.snd))
      (mul_nonneg (div_nonneg hJ L_pos.le) (categoricalMismatch_nonneg_of_support hμ hr))


end SharedRace.Sixth

namespace SharedRace

universe u

/-- Sixth-power entropy bound with an explicit categorical-dispersion input. -/
theorem sharedRaceEntropy_le_sixth_of_dispersion
    {Ω : Type u} {κ : Type}
    [Fintype Ω] [Fintype κ] [DecidableEq Ω] [DecidableEq κ] [Nonempty κ]
    {μ : Ω → ℝ} {r : Ω → κ → ℝ}
    (hμ : IsPMF μ)
    (hr : ∀ z, μ z ≠ 0 → IsPMF (r z))
    (hrpos : ∀ z, μ z ≠ 0 → ∀ i, 0 < r z i)
    (hdisp : 1 - ∑ i, (posteriorMean μ r i)^2 ≤
      categoricalMismatch μ r + logTwo * MI Prod.fst Prod.snd (posteriorJoint μ r)) :
    sharedRaceEntropy μ r ≤
      (6 + poweredRaceJ6Upper) * MI Prod.fst Prod.snd (posteriorJoint μ r) +
        poweredRaceJ6Upper / Real.log 2 * categoricalMismatch μ r := by
  apply Sixth.sharedRaceEntropy_le_powered_of_dispersion hμ hr hrpos
    (by norm_num [poweredRaceJ6Upper])
  · intro π hπ hπpos
    exact Sixth.integral_log_poweredRaceZ_le π hπpos hπ.total
  · exact hdisp

/-- Unconditional sixth-power entropy estimate for arbitrary finite sources. -/
theorem sharedRaceEntropy_le_sixth
    {Ω : Type u} {κ : Type}
    [Fintype Ω] [Fintype κ] [DecidableEq Ω] [DecidableEq κ] [Nonempty κ]
    {μ : Ω → ℝ} {r : Ω → κ → ℝ}
    (hμ : IsPMF μ)
    (hr : ∀ z, μ z ≠ 0 → IsPMF (r z))
    (hrpos : ∀ z, μ z ≠ 0 → ∀ i, 0 < r z i) :
    sharedRaceEntropy μ r ≤
      (6 + poweredRaceJ6Upper) * MI Prod.fst Prod.snd (posteriorJoint μ r) +
        poweredRaceJ6Upper / Real.log 2 * categoricalMismatch μ r :=
  sharedRaceEntropy_le_sixth_of_dispersion hμ hr hrpos (posteriorMean_mismatch_le hμ hr hrpos)

end SharedRace
end stoch_to_det
