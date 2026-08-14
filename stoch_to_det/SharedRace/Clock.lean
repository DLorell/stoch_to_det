import stoch_to_det.SharedRace.Definitions
import stoch_to_det.SharedRace.Scalar

/-!
# Normalized exponential-clock quantities

These bounded normalized quantities are the analytic core of the all-label
shared-race theorem.  Their distributional estimates are proved using the
winner-cell factorization in `Race.lean`.
-/

namespace stoch_to_det
namespace SharedRace

open Finset

variable {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]

/-- Sum of the iid exponential clocks. -/
noncomputable def clockTotal (E : κ → ℝ) : ℝ := ∑ i, E i

/-- Clock vector normalized to the simplex. -/
noncomputable def normClock (E : κ → ℝ) (i : κ) : ℝ :=
  E i / clockTotal E

/-- A total lexicographic argmin of `E_i / π_i`. -/
noncomputable def clockArgmin (π E : κ → ℝ) : κ :=
  lexMax (fun E i => -(E i / π i)) E

/-- Minimum weighted raw clock. -/
noncomputable def rawRaceMin (π E : κ → ℝ) : ℝ :=
  E (clockArgmin π E) / π (clockArgmin π E)

/-- Minimum weighted clock after simplex normalization. -/
noncomputable def normRaceMin (π E : κ → ℝ) : ℝ :=
  rawRaceMin π E / clockTotal E

/-- Ratio of the minimum weighted clock to coordinate `i`; it lies in
`(0,1]` on positive clocks and positive weights. -/
noncomputable def raceRatio (π E : κ → ℝ) (i : κ) : ℝ :=
  rawRaceMin π E * π i / E i

/-- The bounded normalized partition function used by the log-tangent proof. -/
noncomputable def normRaceZ (π E : κ → ℝ) : ℝ :=
  ∑ i, (raceRatio π E i) ^ 2 *
    Real.exp ((Fintype.card κ : ℝ) * SharedRace.logTwo * normClock E i)

omit [DecidableEq κ] in
lemma clockTotal_pos (E : κ → ℝ) (hE : ∀ i, 0 < E i) :
    0 < clockTotal E := by
  unfold clockTotal
  rw [Finset.sum_pos_iff_of_nonneg (fun i _ => (hE i).le)]
  let i : κ := Classical.choice inferInstance
  exact ⟨i, Finset.mem_univ i, hE i⟩

lemma rawRaceMin_le (π E : κ → ℝ) (i : κ) :
    rawRaceMin π E ≤ E i / π i := by
  have h := lexMax_max (fun E i => -(E i / π i)) E i
  change -(E i / π i) ≤ -(E (clockArgmin π E) / π (clockArgmin π E)) at h
  unfold rawRaceMin
  linarith

lemma rawRaceMin_pos (π E : κ → ℝ)
    (hπ : ∀ i, 0 < π i) (hE : ∀ i, 0 < E i) :
    0 < rawRaceMin π E := by
  unfold rawRaceMin
  exact div_pos (hE _) (hπ _)

omit [DecidableEq κ] in
lemma normClock_nonneg (E : κ → ℝ) (hE : ∀ i, 0 < E i) (i : κ) :
    0 ≤ normClock E i := by
  exact div_nonneg (hE i).le (clockTotal_pos E hE).le

omit [DecidableEq κ] in
lemma normClock_le_one (E : κ → ℝ) (hE : ∀ i, 0 < E i) (i : κ) :
    normClock E i ≤ 1 := by
  apply (div_le_one (clockTotal_pos E hE)).2
  unfold clockTotal
  exact Finset.single_le_sum (fun j _ => (hE j).le) (Finset.mem_univ i)

lemma raceRatio_pos (π E : κ → ℝ)
    (hπ : ∀ i, 0 < π i) (hE : ∀ i, 0 < E i) (i : κ) :
    0 < raceRatio π E i := by
  unfold raceRatio
  exact div_pos (mul_pos (rawRaceMin_pos π E hπ hE) (hπ i)) (hE i)

lemma raceRatio_le_one (π E : κ → ℝ)
    (hπ : ∀ i, 0 < π i) (hE : ∀ i, 0 < E i) (i : κ) :
    raceRatio π E i ≤ 1 := by
  apply (div_le_one (hE i)).2
  have h := rawRaceMin_le π E i
  exact (le_div_iff₀ (hπ i)).mp h

@[simp] lemma raceRatio_argmin (π E : κ → ℝ)
    (hπ : ∀ i, 0 < π i) (hE : ∀ i, 0 < E i) :
    raceRatio π E (clockArgmin π E) = 1 := by
  unfold raceRatio rawRaceMin
  field_simp [(hπ _).ne', (hE _).ne']

lemma normRaceZ_pos (π E : κ → ℝ)
    (hπ : ∀ i, 0 < π i) (hE : ∀ i, 0 < E i) :
    0 < normRaceZ π E := by
  let a := clockArgmin π E
  have hterm : 0 < (raceRatio π E a) ^ 2 *
      Real.exp ((Fintype.card κ : ℝ) * SharedRace.logTwo * normClock E a) := by
    rw [raceRatio_argmin π E hπ hE]
    positivity
  have hle : (raceRatio π E a) ^ 2 *
      Real.exp ((Fintype.card κ : ℝ) * SharedRace.logTwo * normClock E a) ≤
        normRaceZ π E := by
    unfold normRaceZ
    exact Finset.single_le_sum
      (f := fun i => (raceRatio π E i) ^ 2 *
        Real.exp ((Fintype.card κ : ℝ) * SharedRace.logTwo * normClock E i))
      (fun i _ => mul_nonneg (sq_nonneg _) (Real.exp_nonneg _))
      (Finset.mem_univ a)
  exact hterm.trans_le hle

/-- A uniform pointwise bound on the normalized partition function.  This is
deliberately stated with `exp (k * log 2)` so later integrability arguments do
not need any power-of-two rewriting. -/
lemma normRaceZ_le (π E : κ → ℝ)
    (hπ : ∀ i, 0 < π i) (hE : ∀ i, 0 < E i) :
    normRaceZ π E ≤
      (Fintype.card κ : ℝ) *
        Real.exp ((Fintype.card κ : ℝ) * SharedRace.logTwo) := by
  have hk0 : 0 ≤ (Fintype.card κ : ℝ) := by positivity
  have hL0 : 0 ≤ SharedRace.logTwo :=
    SharedRace.L_pos.le
  unfold normRaceZ
  calc
    (∑ i, (raceRatio π E i) ^ 2 *
        Real.exp ((Fintype.card κ : ℝ) * SharedRace.logTwo * normClock E i)) ≤
        ∑ _i : κ,
          Real.exp ((Fintype.card κ : ℝ) * SharedRace.logTwo) := by
      apply Finset.sum_le_sum
      intro i _
      have hratio0 : 0 ≤ raceRatio π E i := (raceRatio_pos π E hπ hE i).le
      have hratio1 : raceRatio π E i ≤ 1 := raceRatio_le_one π E hπ hE i
      have hsquare : (raceRatio π E i) ^ 2 ≤ 1 := by nlinarith
      have hexp :
          Real.exp ((Fintype.card κ : ℝ) * SharedRace.logTwo * normClock E i) ≤
            Real.exp ((Fintype.card κ : ℝ) * SharedRace.logTwo) := by
        apply Real.exp_le_exp.mpr
        have hu := normClock_le_one E hE i
        have hc := mul_le_mul_of_nonneg_left hu (mul_nonneg hk0 hL0)
        simpa [mul_assoc] using hc
      calc
        (raceRatio π E i) ^ 2 *
            Real.exp ((Fintype.card κ : ℝ) * SharedRace.logTwo * normClock E i) ≤
            1 * Real.exp ((Fintype.card κ : ℝ) * SharedRace.logTwo * normClock E i) :=
          mul_le_mul_of_nonneg_right hsquare (Real.exp_nonneg _)
        _ ≤ 1 * Real.exp ((Fintype.card κ : ℝ) * SharedRace.logTwo) :=
          mul_le_mul_of_nonneg_left hexp zero_le_one
        _ = _ := one_mul _
    _ = (Fintype.card κ : ℝ) *
        Real.exp ((Fintype.card κ : ℝ) * SharedRace.logTwo) := by simp

/-! ### The bounded reference law -/

/-- The unnormalized reference weight of label `i`.  Dividing these weights
by `normRaceZ` gives the reference categorical law used in the
cross-entropy argument. -/
noncomputable def raceGamma (π E : κ → ℝ) (i : κ) : ℝ :=
  (raceRatio π E i) ^ 2 *
    Real.exp ((Fintype.card κ : ℝ) * SharedRace.logTwo * normClock E i)

/-- The normalized, seed-dependent reference categorical law. -/
noncomputable def referencePMF (π E : κ → ℝ) (i : κ) : ℝ :=
  raceGamma π E i / normRaceZ π E

@[simp] lemma sum_raceGamma (π E : κ → ℝ) :
    ∑ i, raceGamma π E i = normRaceZ π E := by
  rfl

lemma raceGamma_pos (π E : κ → ℝ)
    (hπ : ∀ i, 0 < π i) (hE : ∀ i, 0 < E i) (i : κ) :
    0 < raceGamma π E i := by
  unfold raceGamma
  exact mul_pos (sq_pos_of_pos (raceRatio_pos π E hπ hE i))
    (Real.exp_pos _)

lemma referencePMF_pos (π E : κ → ℝ)
    (hπ : ∀ i, 0 < π i) (hE : ∀ i, 0 < E i) (i : κ) :
    0 < referencePMF π E i := by
  unfold referencePMF
  exact div_pos (raceGamma_pos π E hπ hE i) (normRaceZ_pos π E hπ hE)

lemma referencePMF_isPMF (π E : κ → ℝ)
    (hπ : ∀ i, 0 < π i) (hE : ∀ i, 0 < E i) :
    IsPMF (referencePMF π E) := by
  constructor
  · intro i
    exact (referencePMF_pos π E hπ hE i).le
  · unfold mass referencePMF
    rw [← Finset.sum_div, sum_raceGamma]
    exact div_self (normRaceZ_pos π E hπ hE).ne'

lemma referencePMF_le_one (π E : κ → ℝ)
    (hπ : ∀ i, 0 < π i) (hE : ∀ i, 0 < E i) (i : κ) :
    referencePMF π E i ≤ 1 := by
  have hpmf := referencePMF_isPMF π E hπ hE
  calc
    referencePMF π E i ≤ ∑ j, referencePMF π E j :=
      Finset.single_le_sum (fun j _ => hpmf.nonneg j) (Finset.mem_univ i)
    _ = 1 := by simpa [mass] using hpmf.total

/-- Exact natural-log score of the reference law. -/
lemma log_referencePMF (π E : κ → ℝ)
    (hπ : ∀ i, 0 < π i) (hE : ∀ i, 0 < E i) (i : κ) :
    Real.log (referencePMF π E i) =
      2 * Real.log (raceRatio π E i) +
        (Fintype.card κ : ℝ) * SharedRace.logTwo * normClock E i -
          Real.log (normRaceZ π E) := by
  have hratio := raceRatio_pos π E hπ hE i
  have hZ := normRaceZ_pos π E hπ hE
  have hnum : (raceRatio π E i) ^ 2 *
      Real.exp ((Fintype.card κ : ℝ) * SharedRace.logTwo * normClock E i) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hratio.ne') (Real.exp_ne_zero _)
  unfold referencePMF raceGamma
  rw [Real.log_div hnum hZ.ne',
    Real.log_mul (pow_ne_zero _ hratio.ne') (Real.exp_ne_zero _),
    Real.log_pow, Real.log_exp]
  ring

/-- Exact natural-log loss of the reference law. -/
lemma log_inv_referencePMF (π E : κ → ℝ)
    (hπ : ∀ i, 0 < π i) (hE : ∀ i, 0 < E i) (i : κ) :
    Real.log (1 / referencePMF π E i) =
      Real.log (normRaceZ π E) -
        2 * Real.log (raceRatio π E i) -
          (Fintype.card κ : ℝ) * SharedRace.logTwo * normClock E i := by
  have href := referencePMF_pos π E hπ hE i
  rw [Real.log_div one_ne_zero href.ne', Real.log_one,
    log_referencePMF π E hπ hE i]
  ring

/-- Bit log-loss, after multiplication by `logTwo`, is the natural-log
score from `log_inv_referencePMF`. -/
lemma logTwo_mul_lg_inv_referencePMF (π E : κ → ℝ)
    (hπ : ∀ i, 0 < π i) (hE : ∀ i, 0 < E i) (i : κ) :
    SharedRace.logTwo * lg (1 / referencePMF π E i) =
      Real.log (normRaceZ π E) -
        2 * Real.log (raceRatio π E i) -
          (Fintype.card κ : ℝ) * SharedRace.logTwo * normClock E i := by
  have hconvert :
      SharedRace.logTwo * lg (1 / referencePMF π E i) =
        Real.log (1 / referencePMF π E i) := by
    rw [lg_eq_log_div]
    unfold SharedRace.logTwo
    field_simp [(Real.log_pos one_lt_two).ne']
  rw [hconvert]
  exact log_inv_referencePMF π E hπ hE i

/-- Exact natural-log cross entropy against the reference law. -/
lemma crossEntropy_referencePMF (p π E : κ → ℝ) (hp : IsPMF p)
    (hπ : ∀ i, 0 < π i) (hE : ∀ i, 0 < E i) :
    (∑ i, p i * Real.log (1 / referencePMF π E i)) =
      Real.log (normRaceZ π E) -
        2 * (∑ i, p i * Real.log (raceRatio π E i)) -
          (Fintype.card κ : ℝ) * SharedRace.logTwo *
            (∑ i, p i * normClock E i) := by
  have htotal : ∑ i, p i = 1 := by
    simpa [mass] using hp.total
  calc
    (∑ i, p i * Real.log (1 / referencePMF π E i)) =
        ∑ i, p i *
          (Real.log (normRaceZ π E) -
            2 * Real.log (raceRatio π E i) -
              (Fintype.card κ : ℝ) * SharedRace.logTwo * normClock E i) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [log_inv_referencePMF π E hπ hE i]
    _ = (∑ i, p i) * Real.log (normRaceZ π E) -
          2 * (∑ i, p i * Real.log (raceRatio π E i)) -
            ((Fintype.card κ : ℝ) * SharedRace.logTwo) *
              (∑ i, p i * normClock E i) := by
      calc
        _ = ∑ i,
            (p i * Real.log (normRaceZ π E) -
              2 * (p i * Real.log (raceRatio π E i)) -
                ((Fintype.card κ : ℝ) * SharedRace.logTwo) *
                  (p i * normClock E i)) := by
          apply Finset.sum_congr rfl
          intro i _
          ring
        _ = _ := by
          rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib,
            ← Finset.sum_mul, ← Finset.mul_sum, ← Finset.mul_sum]
    _ = Real.log (normRaceZ π E) -
        2 * (∑ i, p i * Real.log (raceRatio π E i)) -
          (Fintype.card κ : ℝ) * SharedRace.logTwo *
            (∑ i, p i * normClock E i) := by
      rw [htotal, one_mul]

/-- The same cross-entropy identity in the bit convention used by `H`. -/
lemma logTwo_mul_crossEntropy_referencePMF
    (p π E : κ → ℝ) (hp : IsPMF p)
    (hπ : ∀ i, 0 < π i) (hE : ∀ i, 0 < E i) :
    SharedRace.logTwo *
        (∑ i, p i * lg (1 / referencePMF π E i)) =
      Real.log (normRaceZ π E) -
        2 * (∑ i, p i * Real.log (raceRatio π E i)) -
          (Fintype.card κ : ℝ) * SharedRace.logTwo *
            (∑ i, p i * normClock E i) := by
  have hpoint (i : κ) :
      SharedRace.logTwo * lg (1 / referencePMF π E i) =
        Real.log (1 / referencePMF π E i) :=
    (logTwo_mul_lg_inv_referencePMF π E hπ hE i).trans
      (log_inv_referencePMF π E hπ hE i).symm
  calc
    SharedRace.logTwo *
        (∑ i, p i * lg (1 / referencePMF π E i)) =
      ∑ i, p i * Real.log (1 / referencePMF π E i) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [← hpoint i]
        ring
    _ = _ := crossEntropy_referencePMF p π E hp hπ hE

end SharedRace
end stoch_to_det
