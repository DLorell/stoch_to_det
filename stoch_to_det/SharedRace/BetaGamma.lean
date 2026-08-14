import stoch_to_det.Prelude
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Probability.Distributions.Beta

/-!
# One-dimensional beta--gamma exponential comparisons

This file isolates the two convex-order consequences used by the direct
simplex proof.  The intended random variables are

* `k * Beta(1, k - 1)`, compared with `Gamma(1, 1)`;
* `k * Beta(2, k - 2)`, compared with `Gamma(2, 1)`.

Rather than requiring a Dirichlet or beta--gamma independence API, we use the
explicit stop-loss functions.  The final exponential-moment bounds are valid
for every real exponent `lam < 1`, so in particular they include negative
exponents.  The degenerate `k = 2`, shape-two case is stated separately.
-/

namespace stoch_to_det
namespace SharedRace

open MeasureTheory Set
open scoped Interval

/-- Stop-loss function of `Gamma(1,1)`. -/
noncomputable def gammaOneCall (t : ℝ) : ℝ := Real.exp (-t)

/-- Stop-loss function of `Gamma(2,1)`. -/
noncomputable def gammaTwoCall (t : ℝ) : ℝ := (t + 2) * Real.exp (-t)

/-- Stop-loss function of `k * Beta(1,k-1)` on its natural support. -/
noncomputable def betaOneCall (k : ℕ) (t : ℝ) : ℝ :=
  (1 - t / (k : ℝ)) ^ k

/-- Stop-loss function of `k * Beta(2,k-2)` on its natural support. -/
noncomputable def betaTwoCall (k : ℕ) (t : ℝ) : ℝ :=
  (1 - t / (k : ℝ)) ^ (k - 1) *
    (2 + ((k : ℝ) - 2) * t / (k : ℝ))

/-- First derivative of the shape-one beta call on its support. -/
noncomputable def betaOneCallDeriv (k : ℕ) (t : ℝ) : ℝ :=
  -(1 - t / (k : ℝ)) ^ (k - 1)

/-- Density of `k * Beta(1,k-1)` on `(0,k)`. -/
noncomputable def betaOneDensity (k : ℕ) (t : ℝ) : ℝ :=
  ((k - 1 : ℕ) : ℝ) / (k : ℝ) * (1 - t / (k : ℝ)) ^ (k - 2)

/-- Literal one-dimensional exponential moment of `k * Beta(1,k-1)`. -/
noncomputable def betaOneExpMoment (k : ℕ) (lam : ℝ) : ℝ :=
  ∫ t : ℝ in 0..(k : ℝ), Real.exp (lam * t) * betaOneDensity k t

/-- First derivative of the shape-two beta call on its support. -/
noncomputable def betaTwoCallDeriv (k : ℕ) (t : ℝ) : ℝ :=
  -((1 - t / (k : ℝ)) ^ (k - 2) *
    (1 + ((k : ℝ) - 2) * t / (k : ℝ)))

/-- Density of `k * Beta(2,k-2)` on `(0,k)`. -/
noncomputable def betaTwoDensity (k : ℕ) (t : ℝ) : ℝ :=
  (((k : ℝ) - 1) * ((k : ℝ) - 2) / (k : ℝ) ^ 2) * t *
    (1 - t / (k : ℝ)) ^ (k - 3)

/-- Literal one-dimensional exponential moment of `k * Beta(2,k-2)`. -/
noncomputable def betaTwoExpMoment (k : ℕ) (lam : ℝ) : ℝ :=
  ∫ t : ℝ in 0..(k : ℝ), Real.exp (lam * t) * betaTwoDensity k t

/-- The shape-one beta stop-loss is bounded by the exponential stop-loss. -/
theorem betaOneCall_le_gammaOne (k : ℕ) (t : ℝ) (ht : t ≤ k) :
    betaOneCall k t ≤ gammaOneCall t := by
  exact Real.one_sub_div_pow_le_exp_neg ht

private noncomputable def betaTwoLogRatio (k : ℕ) (t : ℝ) : ℝ :=
  ((k : ℝ) - 1) * Real.log (1 - t / (k : ℝ)) +
    Real.log (2 + ((k : ℝ) - 2) * t / (k : ℝ)) + t -
      Real.log (t + 2)

private lemma betaTwoLogRatio_zero (k : ℕ) (_hk : 3 ≤ k) :
    betaTwoLogRatio k 0 = 0 := by
  simp [betaTwoLogRatio]

private lemma betaTwoLogRatio_antitone (k : ℕ) (hk : 3 ≤ k) :
    AntitoneOn (betaTwoLogRatio k) (Ico (0 : ℝ) k) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ico (0 : ℝ) k)
  · intro t ht
    have hk0 : (0 : ℝ) < k := by positivity
    have hbase : 0 < 1 - t / (k : ℝ) := by
      rw [sub_pos, div_lt_one hk0]
      exact ht.2
    have hmid : 0 < 2 + ((k : ℝ) - 2) * t / (k : ℝ) := by
      have hkR : (3 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
      have hkm : (0 : ℝ) ≤ (k : ℝ) - 2 := by linarith
      have hprod : 0 ≤ ((k : ℝ) - 2) * t / (k : ℝ) :=
        div_nonneg (mul_nonneg hkm ht.1) hk0.le
      linarith
    have hlast : 0 < t + 2 := by linarith [ht.1]
    have hkne : (k : ℝ) ≠ 0 := hk0.ne'
    have hbase_ne : 1 - t / (k : ℝ) ≠ 0 := hbase.ne'
    have hmid_ne : 2 + ((k : ℝ) - 2) * t / (k : ℝ) ≠ 0 := hmid.ne'
    have hlast_ne : t + 2 ≠ 0 := hlast.ne'
    apply ContinuousAt.continuousWithinAt
    unfold betaTwoLogRatio
    fun_prop (disch := assumption)
  · intro t ht
    rw [interior_Ico] at ht
    have hk0 : (0 : ℝ) < k := by positivity
    have hbase : 0 < 1 - t / (k : ℝ) := by
      rw [sub_pos, div_lt_one hk0]
      exact ht.2
    have hmid : 0 < 2 + ((k : ℝ) - 2) * t / (k : ℝ) := by
      have hkR : (3 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
      have hkm : (0 : ℝ) ≤ (k : ℝ) - 2 := by linarith
      have hprod : 0 ≤ ((k : ℝ) - 2) * t / (k : ℝ) :=
        div_nonneg (mul_nonneg hkm ht.1.le) hk0.le
      linarith
    have hlast : 0 < t + 2 := by linarith [ht.1]
    have hkne : (k : ℝ) ≠ 0 := hk0.ne'
    have hbase_ne : 1 - t / (k : ℝ) ≠ 0 := hbase.ne'
    have hmid_ne : 2 + ((k : ℝ) - 2) * t / (k : ℝ) ≠ 0 := hmid.ne'
    have hlast_ne : t + 2 ≠ 0 := hlast.ne'
    apply DifferentiableAt.differentiableWithinAt
    unfold betaTwoLogRatio
    fun_prop (disch := assumption)
  · intro t ht
    rw [interior_Ico] at ht
    have hk0 : (0 : ℝ) < k := by positivity
    have hkt : 0 < (k : ℝ) - t := sub_pos.mpr ht.2
    have hmid : 0 < 2 * (k : ℝ) + ((k : ℝ) - 2) * t := by
      have hkR : (3 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
      have hkm : (0 : ℝ) ≤ (k : ℝ) - 2 := by linarith
      nlinarith [mul_nonneg hkm ht.1.le]
    have hlast : 0 < t + 2 := by linarith [ht.1]
    have hbase : 0 < 1 - t / (k : ℝ) := by
      rw [sub_pos, div_lt_one hk0]
      exact ht.2
    have hmiddle : 0 < 2 + ((k : ℝ) - 2) * t / (k : ℝ) := by
      rw [show 2 + ((k : ℝ) - 2) * t / (k : ℝ) =
        (2 * (k : ℝ) + ((k : ℝ) - 2) * t) / (k : ℝ) by field_simp]
      positivity
    have hbaseDeriv :
        HasDerivAt (fun x : ℝ => Real.log (1 - x / (k : ℝ)))
          (-1 / ((k : ℝ) - t)) t := by
      convert ((hasDerivAt_const t 1).sub
        ((hasDerivAt_id t).div_const (k : ℝ))).log hbase.ne' using 1
      · funext x
        simp [div_eq_mul_inv]
      · simp only [Pi.sub_apply, id_eq]
        field_simp [hk0.ne', hkt.ne']
        ring
    have hmiddleDeriv :
        HasDerivAt
          (fun x : ℝ => Real.log (2 + ((k : ℝ) - 2) * x / (k : ℝ)))
          (((k : ℝ) - 2) /
            (2 * (k : ℝ) + ((k : ℝ) - 2) * t)) t := by
      convert ((hasDerivAt_const t 2).add
        (((hasDerivAt_const t ((k : ℝ) - 2)).mul
          (hasDerivAt_id t)).div_const (k : ℝ))).log hmiddle.ne' using 1
      · funext x
        simp [div_eq_mul_inv]
      · simp [Function.id_def]
        field_simp [hk0.ne', hmid.ne']
    have hlastDeriv :
        HasDerivAt (fun x : ℝ => Real.log (x + 2)) (1 / (t + 2)) t := by
      convert ((hasDerivAt_id t).add_const 2).log hlast.ne' using 1 <;> simp
    have hderiv :
        HasDerivAt (betaTwoLogRatio k)
          (1 - ((k : ℝ) - 1) / ((k : ℝ) - t) +
            ((k : ℝ) - 2) /
              (2 * (k : ℝ) + ((k : ℝ) - 2) * t) -
                1 / (t + 2)) t := by
      unfold betaTwoLogRatio
      have hcomb := (((hbaseDeriv.const_mul ((k : ℝ) - 1)).add
        hmiddleDeriv).add (hasDerivAt_id t)).sub hlastDeriv
      convert hcomb using 1
      all_goals first
        | rfl
        | (simp [div_eq_mul_inv]; ring)
    rw [hderiv.deriv]
    have hden : 0 < ((k : ℝ) - t) *
        (2 * (k : ℝ) + ((k : ℝ) - 2) * t) * (t + 2) := by positivity
    have hid :
        1 - ((k : ℝ) - 1) / ((k : ℝ) - t) +
              ((k : ℝ) - 2) /
                (2 * (k : ℝ) + ((k : ℝ) - 2) * t) - 1 / (t + 2) =
          -(t ^ 2 * (((3 : ℝ) * k - 2) + ((k : ℝ) - 2) * t)) /
            (((k : ℝ) - t) *
              (2 * (k : ℝ) + ((k : ℝ) - 2) * t) * (t + 2)) := by
      let B : ℝ := 2 * (k : ℝ) + ((k : ℝ) - 2) * t
      have hB : 0 < B := by simpa only [B] using hmid
      change 1 - ((k : ℝ) - 1) / ((k : ℝ) - t) +
          ((k : ℝ) - 2) / B - 1 / (t + 2) =
        -(t ^ 2 * (((3 : ℝ) * k - 2) + ((k : ℝ) - 2) * t)) /
          (((k : ℝ) - t) * B * (t + 2))
      field_simp [hkt.ne', hB.ne', hlast.ne']
      ring
    rw [hid]
    have hkR : (3 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have hkm : (0 : ℝ) ≤ (k : ℝ) - 2 := by linarith
    have hcoef : 0 ≤ (3 : ℝ) * k - 2 := by linarith
    exact div_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr (mul_nonneg (sq_nonneg t)
        (add_nonneg hcoef (mul_nonneg hkm ht.1.le)))) hden.le

/-- The shape-two beta stop-loss is bounded by the Gamma(2,1) stop-loss. -/
theorem betaTwoCall_le_gammaTwo (k : ℕ) (hk : 3 ≤ k) (t : ℝ)
    (ht0 : 0 ≤ t) (htk : t ≤ k) :
    betaTwoCall k t ≤ gammaTwoCall t := by
  by_cases htk' : t = k
  · subst t
    have hk1 : k - 1 ≠ 0 := by omega
    simp [betaTwoCall, gammaTwoCall, hk1, show (k : ℝ) ≠ 0 by positivity]
    positivity
  · have hlt : t < (k : ℝ) := lt_of_le_of_ne htk htk'
    have hzmem : (0 : ℝ) ∈ Ico 0 (k : ℝ) := ⟨le_rfl, by positivity⟩
    have htmem : t ∈ Ico (0 : ℝ) (k : ℝ) := ⟨ht0, hlt⟩
    have hlog := betaTwoLogRatio_antitone k hk
      hzmem htmem ht0
    rw [betaTwoLogRatio_zero k hk] at hlog
    have hk0 : (0 : ℝ) < k := by positivity
    have hbase : 0 < 1 - t / (k : ℝ) := by
      rw [sub_pos, div_lt_one hk0]
      exact hlt
    have hmid : 0 < 2 + ((k : ℝ) - 2) * t / (k : ℝ) := by
      have hkR : (3 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
      have hkm : (0 : ℝ) ≤ (k : ℝ) - 2 := by linarith
      have hprod : 0 ≤ ((k : ℝ) - 2) * t / (k : ℝ) :=
        div_nonneg (mul_nonneg hkm ht0) hk0.le
      linarith
    have hlast : 0 < t + 2 := by linarith
    have hlogform :
        betaTwoLogRatio k t =
          Real.log (betaTwoCall k t) - Real.log (gammaTwoCall t) := by
      rw [betaTwoCall, gammaTwoCall, Real.log_mul
        (pow_ne_zero _ hbase.ne') hmid.ne', Real.log_pow, Real.log_mul
          hlast.ne' (Real.exp_ne_zero _), Real.log_exp]
      dsimp [betaTwoLogRatio]
      have hkcast : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one]
      rw [hkcast]
      ring
    rw [hlogform] at hlog
    exact (Real.log_le_log_iff
      (mul_pos (pow_pos hbase _) hmid)
      (mul_pos hlast (Real.exp_pos _))).mp (sub_nonpos.mp hlog)

/-- The `k = 2` endpoint of the shape-two comparison: the beta variable is
the constant one, so its scaled value is exactly two. -/
theorem betaTwoDegenerate_exp_le_gammaTwo {lam : ℝ} (hlam : lam < 1) :
    Real.exp (2 * lam) ≤ (1 - lam)⁻¹ ^ 2 := by
  have hpos : 0 < 1 - lam := sub_pos.mpr hlam
  have hlog : Real.log (1 - lam) ≤ -lam := by
    have := Real.log_le_sub_one_of_pos hpos
    linarith
  calc
    Real.exp (2 * lam) ≤ Real.exp (2 * (-Real.log (1 - lam))) :=
      Real.exp_le_exp.mpr (by linarith)
    _ = Real.exp (-Real.log (1 - lam)) ^ 2 := by
      rw [show (2 : ℝ) * (-Real.log (1 - lam)) =
        (2 : ℕ) * (-Real.log (1 - lam)) by norm_num]
      exact Real.exp_nat_mul _ _
    _ = (1 - lam)⁻¹ ^ 2 := by rw [Real.exp_neg, Real.exp_log hpos]

/-! ## Exponential call transforms

For a nonnegative random variable `Y` of mean `m`, two integrations by
parts give

`E exp(lam * Y) = 1 + m * lam + lam^2 * ∫₀∞ exp(lam*t) E[(Y-t)₊] dt`.

The definitions and lemmas below isolate the right-hand side.  In particular,
the square on `lam` makes the comparison valid also when `lam < 0`.
-/

/-- The beta call formula, extended by zero beyond its support. -/
noncomputable def betaOneCallCut (k : ℕ) (t : ℝ) : ℝ :=
  if t ≤ (k : ℝ) then betaOneCall k t else 0

/-- The shape-two beta call formula, extended by zero beyond its support. -/
noncomputable def betaTwoCallCut (k : ℕ) (t : ℝ) : ℝ :=
  if t ≤ (k : ℝ) then betaTwoCall k t else 0

/-- The call-transform representation of an exponential moment. -/
noncomputable def expCallTransform (mean lam : ℝ) (call : ℝ → ℝ) : ℝ :=
  1 + mean * lam + lam ^ 2 *
    ∫ t : ℝ in Ioi 0, Real.exp (lam * t) * call t

private lemma hasDerivAt_one_sub_div (k : ℕ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => 1 - y / (k : ℝ)) (-1 / (k : ℝ)) x := by
  convert (hasDerivAt_const x 1).sub
    ((hasDerivAt_id x).div_const (k : ℝ)) using 1
  all_goals first
    | rfl
    | simp [div_eq_mul_inv]

private lemma betaOneCall_hasDerivAt (k : ℕ) (hk : 2 ≤ k) (x : ℝ) :
    HasDerivAt (betaOneCall k) (betaOneCallDeriv k x) x := by
  unfold betaOneCall betaOneCallDeriv
  have hbase := hasDerivAt_one_sub_div k x
  convert hbase.pow k using 1
  all_goals first
    | rfl
    | field_simp [show (k : ℝ) ≠ 0 by positivity]

private lemma betaOneCallDeriv_hasDerivAt (k : ℕ) (hk : 2 ≤ k) (x : ℝ) :
    HasDerivAt (betaOneCallDeriv k) (betaOneDensity k x) x := by
  unfold betaOneCallDeriv betaOneDensity
  have hbase := hasDerivAt_one_sub_div k x
  convert (hbase.pow (k - 1)).neg using 1
  all_goals first
    | rfl
    | (simp only [show (k - 1) - 1 = k - 2 by omega,
          Nat.cast_sub (show 1 ≤ k by omega), Nat.cast_one]
       field_simp [show (k : ℝ) ≠ 0 by positivity])

private lemma hasDerivAt_const_add_mul_div (a b : ℝ) (k : ℕ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => a + b * y / (k : ℝ)) (b / (k : ℝ)) x := by
  convert (hasDerivAt_const x a).add
    (((hasDerivAt_const x b).mul (hasDerivAt_id x)).div_const (k : ℝ)) using 1
  all_goals first
    | rfl
    | simp [div_eq_mul_inv]

private lemma betaTwoCall_hasDerivAt (k : ℕ) (hk : 3 ≤ k) (x : ℝ) :
    HasDerivAt (betaTwoCall k) (betaTwoCallDeriv k x) x := by
  unfold betaTwoCall betaTwoCallDeriv
  have hbase := hasDerivAt_one_sub_div k x
  have hlinear := hasDerivAt_const_add_mul_div 2 ((k : ℝ) - 2) k x
  have hcast : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
    rw [Nat.cast_sub (show 1 ≤ k by omega), Nat.cast_one]
  have hpow : (1 - x / (k : ℝ)) ^ (k - 1) =
      (1 - x / (k : ℝ)) ^ (k - 2) * (1 - x / (k : ℝ)) := by
    rw [show k - 1 = (k - 2) + 1 by omega, pow_succ]
  have halg :
      ((k - 1 : ℕ) : ℝ) * (1 - x / (k : ℝ)) ^ ((k - 1) - 1) *
            (-1 / (k : ℝ)) * (2 + ((k : ℝ) - 2) * x / (k : ℝ)) +
          (1 - x / (k : ℝ)) ^ (k - 1) * (((k : ℝ) - 2) / (k : ℝ)) =
        -((1 - x / (k : ℝ)) ^ (k - 2) *
          (1 + ((k : ℝ) - 2) * x / (k : ℝ))) := by
    rw [show (k - 1) - 1 = k - 2 by omega, hcast, hpow]
    field_simp [show (k : ℝ) ≠ 0 by positivity]
    ring
  convert (hbase.pow (k - 1)).mul hlinear using 1
  all_goals first
    | rfl
    | simpa only [Pi.mul_apply, Pi.pow_apply, id_eq] using halg.symm

private lemma betaTwoCallDeriv_hasDerivAt (k : ℕ) (hk : 3 ≤ k) (x : ℝ) :
    HasDerivAt (betaTwoCallDeriv k) (betaTwoDensity k x) x := by
  unfold betaTwoCallDeriv betaTwoDensity
  have hbase := hasDerivAt_one_sub_div k x
  have hlinear := hasDerivAt_const_add_mul_div 1 ((k : ℝ) - 2) k x
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

/-- Two integrations by parts, in the exact form needed to identify a density
with the exponential transform of its call function. -/
private lemma integral_exp_mul_secondDeriv_eq
    {K mean lam : ℝ} {call call' density : ℝ → ℝ}
    (hcall : ∀ x ∈ [[0, K]], HasDerivAt call (call' x) x)
    (hcall' : ∀ x ∈ [[0, K]], HasDerivAt call' (density x) x)
    (hcall'Int : IntervalIntegrable call' volume 0 K)
    (hdensityInt : IntervalIntegrable density volume 0 K)
    (hcall0 : call 0 = mean) (hcallK : call K = 0)
    (hcall'0 : call' 0 = -1) (hcall'K : call' K = 0) :
    (∫ x : ℝ in 0..K, Real.exp (lam * x) * density x) =
      1 + mean * lam + lam ^ 2 *
        ∫ x : ℝ in 0..K, Real.exp (lam * x) * call x := by
  have hexp : ∀ x ∈ [[0, K]],
      HasDerivAt (fun y : ℝ => Real.exp (lam * y))
        (lam * Real.exp (lam * x)) x := by
    intro x hx
    convert (Real.hasDerivAt_exp (lam * x)).comp x (hasDerivAt_const_mul lam) using 1
    all_goals first
      | rfl
      | simp [mul_comm]
  have hexp'Int : IntervalIntegrable
      (fun x : ℝ => lam * Real.exp (lam * x)) volume 0 K := by
    exact (by fun_prop : Continuous (fun x : ℝ => lam * Real.exp (lam * x))).intervalIntegrable _ _
  have hparts1 := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    hexp hcall' hexp'Int hdensityInt
  have hparts2 := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    hexp hcall hexp'Int hcall'Int
  have hp1 :
      (∫ x : ℝ in 0..K, Real.exp (lam * x) * density x) =
        1 - ∫ x : ℝ in 0..K, (lam * Real.exp (lam * x)) * call' x := by
    simpa [hcall'0, hcall'K] using hparts1
  have hp2 :
      (∫ x : ℝ in 0..K, Real.exp (lam * x) * call' x) =
        -mean - ∫ x : ℝ in 0..K, (lam * Real.exp (lam * x)) * call x := by
    simpa [hcall0, hcallK] using hparts2
  rw [hp1]
  rw [show (fun x : ℝ => (lam * Real.exp (lam * x)) * call' x) =
      fun x : ℝ => lam * (Real.exp (lam * x) * call' x) by funext x; ring]
  rw [intervalIntegral.integral_const_mul, hp2]
  rw [show (fun x : ℝ => (lam * Real.exp (lam * x)) * call x) =
      fun x : ℝ => lam * (Real.exp (lam * x) * call x) by funext x; ring]
  rw [intervalIntegral.integral_const_mul]
  ring

private lemma betaOneCallCut_weighted_integral (k : ℕ) (hk : 2 ≤ k) (lam : ℝ) :
    (∫ t : ℝ in Ioi 0, Real.exp (lam * t) * betaOneCallCut k t) =
      ∫ t : ℝ in 0..(k : ℝ), Real.exp (lam * t) * betaOneCall k t := by
  have hk0 : (0 : ℝ) ≤ k := by positivity
  have hsubset : Ioc (0 : ℝ) (k : ℝ) ⊆ Ioi 0 := by
    intro t ht
    exact ht.1
  calc
    (∫ t : ℝ in Ioi 0, Real.exp (lam * t) * betaOneCallCut k t) =
        ∫ t : ℝ in Ioc 0 (k : ℝ), Real.exp (lam * t) * betaOneCallCut k t := by
      apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi hsubset
      intro t ht
      have hnot : ¬t ≤ (k : ℝ) := by
        intro hle
        exact ht.2 ⟨ht.1, hle⟩
      simp [betaOneCallCut, hnot]
    _ = ∫ t : ℝ in Ioc 0 (k : ℝ), Real.exp (lam * t) * betaOneCall k t := by
      apply setIntegral_congr_fun measurableSet_Ioc
      intro t ht
      simp [betaOneCallCut, ht.2]
    _ = ∫ t : ℝ in 0..(k : ℝ), Real.exp (lam * t) * betaOneCall k t :=
      (intervalIntegral.integral_of_le hk0).symm

/-- The literal scaled-Beta(1,k-1) density moment is exactly its call
transform. -/
theorem betaOneExpMoment_eq_expCallTransform (k : ℕ) (hk : 2 ≤ k) (lam : ℝ) :
    betaOneExpMoment k lam = expCallTransform 1 lam (betaOneCallCut k) := by
  have hcall'Int : IntervalIntegrable (betaOneCallDeriv k) volume 0 (k : ℝ) := by
    exact (by
      unfold betaOneCallDeriv
      fun_prop : Continuous (betaOneCallDeriv k)).intervalIntegrable _ _
  have hdensityInt : IntervalIntegrable (betaOneDensity k) volume 0 (k : ℝ) := by
    exact (by
      unfold betaOneDensity
      fun_prop : Continuous (betaOneDensity k)).intervalIntegrable _ _
  have hparts := integral_exp_mul_secondDeriv_eq
    (K := (k : ℝ)) (mean := (1 : ℝ)) (lam := lam)
    (call := betaOneCall k) (call' := betaOneCallDeriv k)
    (density := betaOneDensity k)
    (fun x hx => betaOneCall_hasDerivAt k hk x)
    (fun x hx => betaOneCallDeriv_hasDerivAt k hk x)
    hcall'Int hdensityInt
    (by simp [betaOneCall])
    (by
      have hk0 : (k : ℝ) ≠ 0 := by positivity
      have hkn : k ≠ 0 := by omega
      simp [betaOneCall, hk0, hkn])
    (by simp [betaOneCallDeriv])
    (by
      have hk0 : (k : ℝ) ≠ 0 := by positivity
      have hk1 : k - 1 ≠ 0 := by omega
      simp [betaOneCallDeriv, hk0, hk1])
  rw [betaOneExpMoment, hparts, expCallTransform,
    betaOneCallCut_weighted_integral k hk lam]

private lemma betaTwoCallCut_weighted_integral (k : ℕ) (hk : 3 ≤ k) (lam : ℝ) :
    (∫ t : ℝ in Ioi 0, Real.exp (lam * t) * betaTwoCallCut k t) =
      ∫ t : ℝ in 0..(k : ℝ), Real.exp (lam * t) * betaTwoCall k t := by
  have hk0 : (0 : ℝ) ≤ k := by positivity
  have hsubset : Ioc (0 : ℝ) (k : ℝ) ⊆ Ioi 0 := by
    intro t ht
    exact ht.1
  calc
    (∫ t : ℝ in Ioi 0, Real.exp (lam * t) * betaTwoCallCut k t) =
        ∫ t : ℝ in Ioc 0 (k : ℝ), Real.exp (lam * t) * betaTwoCallCut k t := by
      apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi hsubset
      intro t ht
      have hnot : ¬t ≤ (k : ℝ) := by
        intro hle
        exact ht.2 ⟨ht.1, hle⟩
      simp [betaTwoCallCut, hnot]
    _ = ∫ t : ℝ in Ioc 0 (k : ℝ), Real.exp (lam * t) * betaTwoCall k t := by
      apply setIntegral_congr_fun measurableSet_Ioc
      intro t ht
      simp [betaTwoCallCut, ht.2]
    _ = ∫ t : ℝ in 0..(k : ℝ), Real.exp (lam * t) * betaTwoCall k t :=
      (intervalIntegral.integral_of_le hk0).symm

/-- The literal scaled-Beta(2,k-2) density moment is exactly its call
transform. -/
theorem betaTwoExpMoment_eq_expCallTransform (k : ℕ) (hk : 3 ≤ k) (lam : ℝ) :
    betaTwoExpMoment k lam = expCallTransform 2 lam (betaTwoCallCut k) := by
  have hcall'Int : IntervalIntegrable (betaTwoCallDeriv k) volume 0 (k : ℝ) := by
    exact (by
      unfold betaTwoCallDeriv
      fun_prop : Continuous (betaTwoCallDeriv k)).intervalIntegrable _ _
  have hdensityInt : IntervalIntegrable (betaTwoDensity k) volume 0 (k : ℝ) := by
    exact (by
      unfold betaTwoDensity
      fun_prop : Continuous (betaTwoDensity k)).intervalIntegrable _ _
  have hparts := integral_exp_mul_secondDeriv_eq
    (K := (k : ℝ)) (mean := (2 : ℝ)) (lam := lam)
    (call := betaTwoCall k) (call' := betaTwoCallDeriv k)
    (density := betaTwoDensity k)
    (fun x hx => betaTwoCall_hasDerivAt k hk x)
    (fun x hx => betaTwoCallDeriv_hasDerivAt k hk x)
    hcall'Int hdensityInt
    (by simp [betaTwoCall])
    (by
      have hk0 : (k : ℝ) ≠ 0 := by positivity
      have hk1 : k - 1 ≠ 0 := by omega
      simp [betaTwoCall, hk0, hk1])
    (by simp [betaTwoCallDeriv])
    (by
      have hk0 : (k : ℝ) ≠ 0 := by positivity
      have hk2 : k - 2 ≠ 0 := by omega
      simp [betaTwoCallDeriv, hk0, hk2])
  rw [betaTwoExpMoment, hparts, expCallTransform,
    betaTwoCallCut_weighted_integral k hk lam]

lemma betaOneCallCut_nonneg (k : ℕ) (hk : 1 ≤ k) (t : ℝ) (_ht : 0 ≤ t) :
    0 ≤ betaOneCallCut k t := by
  rw [betaOneCallCut]
  split_ifs with h
  · exact pow_nonneg (by
      rw [sub_nonneg, div_le_one (by positivity : (0 : ℝ) < k)]
      exact h) _
  · exact le_rfl

lemma betaTwoCallCut_nonneg (k : ℕ) (hk : 3 ≤ k) (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ betaTwoCallCut k t := by
  rw [betaTwoCallCut]
  split_ifs with h
  · have hk0 : (0 : ℝ) < k := by positivity
    have hbase : 0 ≤ 1 - t / (k : ℝ) := by
      rw [sub_nonneg, div_le_one hk0]
      exact h
    have hkR : (3 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have hkm : (0 : ℝ) ≤ (k : ℝ) - 2 := by linarith
    have hprod : 0 ≤ ((k : ℝ) - 2) * t / (k : ℝ) :=
      div_nonneg (mul_nonneg hkm ht) hk0.le
    exact mul_nonneg (pow_nonneg hbase _) (by linarith)
  · exact le_rfl

lemma betaOneCallCut_le_gammaOne (k : ℕ) (_hk : 1 ≤ k) (t : ℝ) (_ht : 0 ≤ t) :
    betaOneCallCut k t ≤ gammaOneCall t := by
  rw [betaOneCallCut]
  split_ifs with h
  · exact betaOneCall_le_gammaOne k t h
  · exact (Real.exp_pos _).le

lemma betaTwoCallCut_le_gammaTwo (k : ℕ) (hk : 3 ≤ k) (t : ℝ) (ht : 0 ≤ t) :
    betaTwoCallCut k t ≤ gammaTwoCall t := by
  rw [betaTwoCallCut]
  split_ifs with h
  · exact betaTwoCall_le_gammaTwo k hk t ht h
  · exact mul_nonneg (by linarith) (Real.exp_pos _).le

private lemma expCallIntegral_mono {lam : ℝ} {call₁ call₂ : ℝ → ℝ}
    (h₁ : ∀ t, 0 ≤ t → 0 ≤ call₁ t)
    (h₁₂ : ∀ t, 0 ≤ t → call₁ t ≤ call₂ t)
    (h₂int : IntegrableOn (fun t : ℝ => Real.exp (lam * t) * call₂ t) (Ioi 0)) :
    (∫ t : ℝ in Ioi 0, Real.exp (lam * t) * call₁ t) ≤
      ∫ t : ℝ in Ioi 0, Real.exp (lam * t) * call₂ t := by
  apply integral_mono_of_nonneg
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg (Real.exp_pos _).le (h₁ t ht.le)
  · exact h₂int
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_le_mul_of_nonneg_left (h₁₂ t ht.le) (Real.exp_pos _).le

private lemma gammaOne_weighted_integrable {lam : ℝ} (hlam : lam < 1) :
    IntegrableOn (fun t : ℝ => Real.exp (lam * t) * gammaOneCall t) (Ioi 0) := by
  have h := integrableOn_exp_mul_Ioi (a := lam - 1) (by linarith) 0
  refine h.congr_fun ?_ measurableSet_Ioi
  intro t ht
  change Real.exp ((lam - 1) * t) = Real.exp (lam * t) * Real.exp (-t)
  rw [← Real.exp_add]
  congr 1
  ring

private lemma gammaOne_weighted_integral {lam : ℝ} (hlam : lam < 1) :
    (∫ t : ℝ in Ioi 0, Real.exp (lam * t) * gammaOneCall t) = (1 - lam)⁻¹ := by
  have h := integral_exp_mul_Ioi (a := lam - 1) (by linarith) 0
  rw [show (fun t : ℝ => Real.exp (lam * t) * gammaOneCall t) =
      fun t : ℝ => Real.exp ((lam - 1) * t) by
    funext t
    rw [gammaOneCall, ← Real.exp_add]
    congr 1
    ring]
  rw [h]
  norm_num
  rw [inv_eq_one_div]
  field_simp [show lam - 1 ≠ 0 by linarith, show 1 - lam ≠ 0 by linarith]
  ring

/-- The complete shape-one call-transform bound.  It is stated for every
`lam < 1`, including negative `lam`. -/
theorem betaOneExpCallTransform_le (k : ℕ) (hk : 1 ≤ k) {lam : ℝ}
    (hlam : lam < 1) :
    expCallTransform 1 lam (betaOneCallCut k) ≤ (1 - lam)⁻¹ := by
  have hint := expCallIntegral_mono
    (fun t ht => betaOneCallCut_nonneg k hk t ht)
    (fun t ht => betaOneCallCut_le_gammaOne k hk t ht)
    (gammaOne_weighted_integrable hlam)
  rw [expCallTransform, gammaOne_weighted_integral hlam] at *
  calc
    1 + 1 * lam + lam ^ 2 *
          (∫ t : ℝ in Ioi 0, Real.exp (lam * t) * betaOneCallCut k t) ≤
        1 + 1 * lam + lam ^ 2 * (1 - lam)⁻¹ := by gcongr
    _ = (1 - lam)⁻¹ := by
      have hne : 1 - lam ≠ 0 := by linarith
      have hmul : (1 - lam) * (1 - lam)⁻¹ = 1 := mul_inv_cancel₀ hne
      apply eq_of_sub_eq_zero
      calc
        (1 + 1 * lam + lam ^ 2 * (1 - lam)⁻¹) - (1 - lam)⁻¹ =
            (1 + lam) * (1 - (1 - lam) * (1 - lam)⁻¹) := by ring
        _ = 0 := by rw [hmul]; ring

private lemma gammaTwo_weighted_integrable {lam : ℝ} (hlam : lam < 1) :
    IntegrableOn (fun t : ℝ => Real.exp (lam * t) * gammaTwoCall t) (Ioi 0) := by
  have ha : 0 < 1 - lam := sub_pos.mpr hlam
  have hpow := integrableOn_rpow_mul_exp_neg_mul_rpow
    (p := (1 : ℝ)) (s := (1 : ℝ)) (b := 1 - lam)
    (by norm_num) (by norm_num) ha
  have ht : IntegrableOn (fun t : ℝ => t * Real.exp ((lam - 1) * t)) (Ioi 0) := by
    refine hpow.congr_fun ?_ measurableSet_Ioi
    intro t ht
    dsimp only
    rw [Real.rpow_one]
    congr 2
    ring
  have he := integrableOn_exp_mul_Ioi (a := lam - 1) (by linarith) 0
  have hsum : IntegrableOn
      (fun t : ℝ => t * Real.exp ((lam - 1) * t) +
        2 * Real.exp ((lam - 1) * t)) (Ioi 0) :=
    ht.add (he.const_mul 2)
  refine hsum.congr_fun ?_ measurableSet_Ioi
  intro t ht
  change t * Real.exp ((lam - 1) * t) + 2 * Real.exp ((lam - 1) * t) =
    Real.exp (lam * t) * ((t + 2) * Real.exp (-t))
  calc
    _ = (t + 2) * Real.exp ((lam - 1) * t) := by ring
    _ = (t + 2) * (Real.exp (lam * t) * Real.exp (-t)) := by
      rw [← Real.exp_add]
      congr 2
      ring
    _ = _ := by ring

private lemma gammaTwo_weighted_integral {lam : ℝ} (hlam : lam < 1) :
    (∫ t : ℝ in Ioi 0, Real.exp (lam * t) * gammaTwoCall t) =
      (1 - lam)⁻¹ ^ 2 + 2 * (1 - lam)⁻¹ := by
  have ha : 0 < 1 - lam := sub_pos.mpr hlam
  have htint : IntegrableOn (fun t : ℝ => t * Real.exp ((lam - 1) * t)) (Ioi 0) := by
    have hpow := integrableOn_rpow_mul_exp_neg_mul_rpow
      (p := (1 : ℝ)) (s := (1 : ℝ)) (b := 1 - lam)
      (by norm_num) (by norm_num) ha
    refine hpow.congr_fun ?_ measurableSet_Ioi
    intro t ht
    dsimp only
    rw [Real.rpow_one]
    congr 2
    ring
  have heint := integrableOn_exp_mul_Ioi (a := lam - 1) (by linarith) 0
  have htvalue :
      (∫ t : ℝ in Ioi 0, t * Real.exp ((lam - 1) * t)) = (1 - lam)⁻¹ ^ 2 := by
    calc
      (∫ t : ℝ in Ioi 0, t * Real.exp ((lam - 1) * t)) =
          ∫ t : ℝ in Ioi 0,
            t ^ ((2 : ℝ) - 1) * Real.exp (-((1 - lam) * t)) := by
            apply setIntegral_congr_fun measurableSet_Ioi
            intro t ht
            dsimp only
            rw [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one]
            congr 2
            ring
      _ = (1 / (1 - lam)) ^ (2 : ℝ) * Real.Gamma 2 :=
        Real.integral_rpow_mul_exp_neg_mul_Ioi (by norm_num) ha
      _ = (1 - lam)⁻¹ ^ 2 := by
        have hGamma : Real.Gamma 2 = 1 := by
          norm_num [Real.Gamma_ofNat_eq_factorial]
        rw [hGamma, mul_one, one_div, Real.rpow_two]
  have hevalue :
      (∫ t : ℝ in Ioi 0, Real.exp ((lam - 1) * t)) = (1 - lam)⁻¹ := by
    have h := integral_exp_mul_Ioi (a := lam - 1) (by linarith) 0
    rw [h]
    norm_num
    rw [inv_eq_one_div]
    field_simp [show lam - 1 ≠ 0 by linarith, show 1 - lam ≠ 0 by linarith]
    ring
  rw [show (fun t : ℝ => Real.exp (lam * t) * gammaTwoCall t) =
      fun t : ℝ => t * Real.exp ((lam - 1) * t) +
        2 * Real.exp ((lam - 1) * t) by
    funext t
    rw [gammaTwoCall]
    calc
      Real.exp (lam * t) * ((t + 2) * Real.exp (-t)) =
          (t + 2) * (Real.exp (lam * t) * Real.exp (-t)) := by ring
      _ = (t + 2) * Real.exp ((lam - 1) * t) := by
        rw [← Real.exp_add]
        congr 2
        ring
      _ = _ := by ring]
  rw [integral_add htint (heint.const_mul 2), integral_const_mul, htvalue, hevalue]

/-- The complete shape-two call-transform bound for the nondegenerate beta
law.  It is valid for every `lam < 1`, including negative `lam`. -/
theorem betaTwoExpCallTransform_le (k : ℕ) (hk : 3 ≤ k) {lam : ℝ}
    (hlam : lam < 1) :
    expCallTransform 2 lam (betaTwoCallCut k) ≤ (1 - lam)⁻¹ ^ 2 := by
  have hint := expCallIntegral_mono
    (fun t ht => betaTwoCallCut_nonneg k hk t ht)
    (fun t ht => betaTwoCallCut_le_gammaTwo k hk t ht)
    (gammaTwo_weighted_integrable hlam)
  rw [expCallTransform, gammaTwo_weighted_integral hlam] at *
  calc
    1 + 2 * lam + lam ^ 2 *
          (∫ t : ℝ in Ioi 0, Real.exp (lam * t) * betaTwoCallCut k t) ≤
        1 + 2 * lam + lam ^ 2 *
          ((1 - lam)⁻¹ ^ 2 + 2 * (1 - lam)⁻¹) := by gcongr
    _ = (1 - lam)⁻¹ ^ 2 := by
      have hne : 1 - lam ≠ 0 := by linarith
      rw [inv_eq_one_div]
      field_simp [hne]
      ring

/-- Winner-cell exponential-moment bound, in the literal scaled
`Beta(1,k-1)` density form used by the clock proof. -/
theorem winnerBetaExpMoment_le (k : ℕ) (hk : 2 ≤ k) {lam : ℝ}
    (hlam : lam < 1) :
    betaOneExpMoment k lam ≤ (1 - lam)⁻¹ := by
  rw [betaOneExpMoment_eq_expCallTransform k hk lam]
  exact betaOneExpCallTransform_le k (by omega) hlam

/-- Loser-cell exponential-moment bound, in the literal scaled
`Beta(2,k-2)` density form used by the clock proof. -/
theorem loserBetaExpMoment_le (k : ℕ) (hk : 3 ≤ k) {lam : ℝ}
    (hlam : lam < 1) :
    betaTwoExpMoment k lam ≤ (1 - lam)⁻¹ ^ 2 := by
  rw [betaTwoExpMoment_eq_expCallTransform k hk lam]
  exact betaTwoExpCallTransform_le k hk hlam

/-- The `k=2` loser-cell endpoint is the constant scaled value two. -/
theorem loserBetaExpMoment_two_le {lam : ℝ} (hlam : lam < 1) :
    Real.exp (lam * 2) ≤ (1 - lam)⁻¹ ^ 2 := by
  rw [mul_comm]
  exact betaTwoDegenerate_exp_le_gammaTwo hlam

end SharedRace
end stoch_to_det
