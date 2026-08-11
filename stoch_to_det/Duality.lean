import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Data.Fintype.EquivFin
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import stoch_to_det.Envelope

/-!
# §2. Kernel duality, contacts, and the defect functional


The defect `G_w` and the notion of a **contact** are used in every later
section. Everything here is finite-dimensional real analysis — no probability
space, no measure theory.

## Contents

| Lean name | Label | Note |
|---|---|---|
| `Lambda`, `Feasible`, `Gdef`, `IsContact` | Def 2.1 | definitions |
| `Gdef_eq_certificate_gap` | Lemma 2.2 | pure algebra |
| `valid_iff_feasible`, `Gdef_nonneg` | Thm 2.3 | Gibbs + a Lagrange/perturbation argument |
| `exists_tau_optimal_kernel` | Cor 2.4 | compactness; attainment |
| `exists_common_contact_pair` | Thm 2.5 *contact-opt* | **the pair `(L,w)` fixed for §§4-12** |
| `contact_support_eq` | Lemma 2.6 | contacts have full support on connected `𝒮` |
| `contact_hypercontractive` | Lemma 2.7 | `E_q[f(X)g(Y)] ≤ ‖f‖_{3/2} ‖g‖_{3/2}` |
| `Gdef_fusion` | Lemma 2.8(a) | fusion identity |

## Mathlib background

§5.2, §6.1 and §6.2 all reduce to Lemma 2.7, derived from `Feasible` by Hölder.
The `(⇒)` direction of Theorem 2.3 and Corollary 2.4 both
use a first-order (one-sided `ε^{2/3}` perturbation) argument at a maximizer of
`Λ_w` on a simplex, for which Mathlib has no packaged KKT statement.
-/

namespace stoch_to_det

open Finset

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

/-! ### Definition 2.1 -/

/-- `Λ_w(u,v) := ∑_{(x,y) ∈ 𝒮} w(x,y) u(x)^{2/3} v(y)^{2/3}`. -/
noncomputable def Lambda (S : Finset (α × β)) (w : α × β → ℝ) (u : α → ℝ) (v : β → ℝ) : ℝ :=
  ∑ z ∈ S, w z * u z.1 ^ ((2 : ℝ) / 3) * v z.2 ^ ((2 : ℝ) / 3)

/-- A kernel is **feasible** when `Λ_w(u,v) ≤ 1` for all probability vectors
`u, v`. -/
def Feasible (S : Finset (α × β)) (w : α × β → ℝ) : Prop :=
  (∀ z ∈ S, 0 < w z) ∧ ∀ u : α → ℝ, ∀ v : β → ℝ, IsPMF u → IsPMF v → Lambda S w u v ≤ 1

/-- A certificate `c : 𝒮 → ℝ` is **valid** when `⟨c,q⟩ ≥ Φ(q)` for every law `q`
on `𝒮`. -/
def Valid (S : Finset (α × β)) (c : α × β → ℝ) : Prop :=
  ∀ q : α × β → ℝ, IsPMF q → Supported S q → Phi q ≤ ∑ z ∈ S, c z * q z

/-- The reference measure `m_q := w · q_X^{2/3} ⊗ q_Y^{2/3}` restricted to `𝒮`
. -/
noncomputable def refMeas (S : Finset (α × β)) (w : α × β → ℝ) (q : α × β → ℝ) :
    α × β → ℝ :=
  fun z => if z ∈ S then w z * mX q z.1 ^ ((2 : ℝ) / 3) * mY q z.2 ^ ((2 : ℝ) / 3) else 0

/-- The **defect** `G_w(q) := 3 ∑ q · lg (q / (w q_X^{2/3} q_Y^{2/3})) = 3 D(q ‖ m_q)`
, in bits, with `D` taken against an *unnormalized* reference. -/
noncomputable def Gdef (S : Finset (α × β)) (w : α × β → ℝ) (q : α × β → ℝ) : ℝ :=
  3 * ∑ z ∈ S, q z * lg (q z / refMeas S w q z)

/-- `q` is a **contact** of `w`: `G_w(q) = 0`, equivalently `q = w q_X^{2/3} q_Y^{2/3}`
pointwise. The pointwise form is taken as the definition,
since that is the form later sections use (§5.2 and §6.2 divide two contact
equations); the equivalence with `G_w(q) = 0` is `Gdef_eq_zero_iff`. -/
def IsContact (S : Finset (α × β)) (w : α × β → ℝ) (q : α × β → ℝ) : Prop :=
  IsPMF q ∧ Supported S q ∧ ∀ z ∈ S, q z = w z * mX q z.1 ^ ((2 : ℝ) / 3) * mY q z.2 ^ ((2 : ℝ) / 3)

/-! ### Lemma 2.2 -/

private lemma sum_mul_lg_self_eq_neg_H {γ : Type*} [Fintype γ]
    {m : γ → ℝ} (hm : IsPMF m) :
    (∑ a, m a * lg (m a)) = -H m := by
  rw [H, hm.total, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : m a = 0
  · simp [ha]
  · rw [lg_eq_log_div, lg_eq_log_div, Real.log_div one_ne_zero ha]
    simp
    ring

private lemma unnormalized_gibbs_nonneg_lg {γ : Type*} [Fintype γ]
    {p m : γ → ℝ} (hp : IsPMF p) (hm : IsFinMeas m)
    (hmass : mass m ≤ 1) (hsupp : ∀ a, p a ≠ 0 → m a ≠ 0) :
    0 ≤ ∑ a, p a * lg (p a / m a) := by
  have hterm : ∀ a, p a - m a ≤ p a * Real.log (p a / m a) := by
    intro a
    by_cases hpa : p a = 0
    · simp [hpa, hm a]
    · have hppos : 0 < p a := lt_of_le_of_ne (hp.nonneg a) (Ne.symm hpa)
      have hma : m a ≠ 0 := hsupp a hpa
      have hmpos : 0 < m a := lt_of_le_of_ne (hm a) (Ne.symm hma)
      have hlog := Real.log_le_sub_one_of_pos (div_pos hmpos hppos)
      have hmul := mul_le_mul_of_nonneg_left hlog (hp.nonneg a)
      have hident : p a * (m a / p a - 1) = m a - p a := by
        field_simp [hpa]
      have hswap : p a * Real.log (m a / p a) =
          -(p a * Real.log (p a / m a)) := by
        rw [Real.log_div hma hpa, Real.log_div hpa hma]
        ring
      rw [hswap, hident] at hmul
      linarith
  have hp_sum : ∑ a, p a = 1 := by simpa [mass] using hp.total
  have hnats : 0 ≤ ∑ a, p a * Real.log (p a / m a) := by
    calc
      0 ≤ 1 - mass m := sub_nonneg.mpr hmass
      _ = ∑ a, (p a - m a) := by
        rw [Finset.sum_sub_distrib, hp_sum]
        rfl
      _ ≤ ∑ a, p a * Real.log (p a / m a) :=
        Finset.sum_le_sum fun a _ => hterm a
  change 0 ≤ ∑ a, p a * (Real.log (p a / m a) / Real.log 2)
  simp_rw [← mul_div_assoc]
  rw [← Finset.sum_div]
  exact div_nonneg hnats (Real.log_pos one_lt_two).le

private lemma unnormalized_gibbs_eq_zero_iff {γ : Type*} [Fintype γ]
    {p m : γ → ℝ} (hp : IsPMF p) (hm : IsFinMeas m)
    (hmass : mass m ≤ 1) (hsupp : ∀ a, p a ≠ 0 → m a ≠ 0) :
    (∑ a, p a * lg (p a / m a)) = 0 ↔ p = m := by
  have hterm : ∀ a, p a - m a ≤ p a * Real.log (p a / m a) := by
    intro a
    by_cases hpa : p a = 0
    · simp [hpa, hm a]
    · have hppos : 0 < p a := lt_of_le_of_ne (hp.nonneg a) (Ne.symm hpa)
      have hma : m a ≠ 0 := hsupp a hpa
      have hmpos : 0 < m a := lt_of_le_of_ne (hm a) (Ne.symm hma)
      have hlog := Real.log_le_sub_one_of_pos (div_pos hmpos hppos)
      have hmul := mul_le_mul_of_nonneg_left hlog (hp.nonneg a)
      have hident : p a * (m a / p a - 1) = m a - p a := by
        field_simp [hpa]
      have hswap : p a * Real.log (m a / p a) =
          -(p a * Real.log (p a / m a)) := by
        rw [Real.log_div hma hpa, Real.log_div hpa hma]
        ring
      rw [hswap, hident] at hmul
      linarith
  constructor
  · intro hzero
    have hconvert :
        (∑ a, p a * lg (p a / m a)) =
          (∑ a, p a * Real.log (p a / m a)) / Real.log 2 := by
      simp only [lg_eq_log_div]
      simp_rw [← mul_div_assoc]
      rw [Finset.sum_div]
    rw [hconvert] at hzero
    have hnats :
        (∑ a, p a * Real.log (p a / m a)) = 0 :=
      (div_eq_zero_iff.mp hzero).resolve_right (Real.log_pos one_lt_two).ne'
    have hp_sum : ∑ a, p a = 1 := by simpa [mass] using hp.total
    have hmass_eq : mass m = 1 := by
      have hlower : 1 - mass m ≤ ∑ a, p a * Real.log (p a / m a) := by
        calc
          1 - mass m = ∑ a, (p a - m a) := by
            rw [Finset.sum_sub_distrib, hp_sum]
            rfl
          _ ≤ ∑ a, p a * Real.log (p a / m a) :=
            Finset.sum_le_sum fun a _ => hterm a
      linarith
    have hslack_nonneg :
        ∀ a, 0 ≤ p a * Real.log (p a / m a) - (p a - m a) :=
      fun a => sub_nonneg.mpr (hterm a)
    have hslack_sum :
        (∑ a, (p a * Real.log (p a / m a) - (p a - m a))) = 0 := by
      rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, hp_sum]
      change (∑ a, p a * Real.log (p a / m a)) - (1 - mass m) = 0
      rw [hnats, hmass_eq]
      norm_num
    have hslack_zero :
        ∀ a, p a * Real.log (p a / m a) - (p a - m a) = 0 := by
      intro a
      exact (Finset.sum_eq_zero_iff_of_nonneg
        (fun b _ => hslack_nonneg b)).mp hslack_sum a (Finset.mem_univ a)
    funext a
    by_cases hpa : p a = 0
    · have := hslack_zero a
      simp [hpa] at this
      linarith
    · have hppos : 0 < p a := lt_of_le_of_ne (hp.nonneg a) (Ne.symm hpa)
      have hma : m a ≠ 0 := hsupp a hpa
      have hmpos : 0 < m a := lt_of_le_of_ne (hm a) (Ne.symm hma)
      by_contra hne
      have hratio : m a / p a ≠ 1 := by
        intro hratio
        apply hne
        calc
          p a = (m a / p a) * p a := by rw [hratio, one_mul]
          _ = m a := by field_simp [hpa]
      have hstrict := Real.log_lt_sub_one_of_pos (div_pos hmpos hppos) hratio
      have hmul := mul_lt_mul_of_pos_left hstrict hppos
      have hident : p a * (m a / p a - 1) = m a - p a := by
        field_simp [hpa]
      have hswap : p a * Real.log (m a / p a) =
          -(p a * Real.log (p a / m a)) := by
        rw [Real.log_div hma hpa, Real.log_div hpa hma]
        ring
      rw [hswap, hident] at hmul
      linarith [hslack_zero a]
  · rintro rfl
    apply Finset.sum_eq_zero
    intro a _
    by_cases hpa : p a = 0
    · simp [hpa]
    · rw [div_self hpa, lg_one, mul_zero]

private lemma mass_refMeas_eq_Lambda (S : Finset (α × β)) (w : α × β → ℝ)
    (q : α × β → ℝ) :
    mass (refMeas S w q) = Lambda S w (mX q) (mY q) := by
  simp [mass, refMeas, Lambda]

/-- **Lemma 2.2** (defect = certificate gap).
With `c = −3 lg w`: `G_w(q) = ⟨c,q⟩ − Φ(q)`. -/
theorem Gdef_eq_certificate_gap {S : Finset (α × β)} {w : α × β → ℝ}
    (hw : ∀ z ∈ S, 0 < w z) {q : α × β → ℝ} (hq : IsPMF q) (hqS : Supported S q) :
    Gdef S w q = (∑ z ∈ S, (-3 * lg (w z)) * q z) - Phi q := by
  have hqX : IsPMF (mX q) := isPMF_push hq
  have hqY : IsPMF (mY q) := isPMF_push hq
  have hsum_support (k : α × β → ℝ) :
      (∑ z ∈ S, q z * k z) = ∑ z, q z * k z := by
    apply Finset.sum_subset (Finset.subset_univ S)
    intro z _ hzS
    rw [hqS z hzS, zero_mul]
  have hsumq : (∑ z ∈ S, q z * lg (q z)) = -H q := by
    rw [hsum_support]
    exact sum_mul_lg_self_eq_neg_H hq
  have hsumX : (∑ z ∈ S, q z * lg (mX q z.1)) = -H (mX q) := by
    calc
      (∑ z ∈ S, q z * lg (mX q z.1)) =
          ∑ z, q z * lg (mX q z.1) := hsum_support _
      _ = ∑ x, mX q x * lg (mX q x) :=
        (sum_push_mul Prod.fst q (fun x => lg (mX q x))).symm
      _ = -H (mX q) := sum_mul_lg_self_eq_neg_H hqX
  have hsumY : (∑ z ∈ S, q z * lg (mY q z.2)) = -H (mY q) := by
    calc
      (∑ z ∈ S, q z * lg (mY q z.2)) =
          ∑ z, q z * lg (mY q z.2) := hsum_support _
      _ = ∑ y, mY q y * lg (mY q y) :=
        (sum_push_mul Prod.snd q (fun y => lg (mY q y))).symm
      _ = -H (mY q) := sum_mul_lg_self_eq_neg_H hqY
  have hterm (z : α × β) (hzS : z ∈ S) :
      q z * lg (q z / refMeas S w q z) =
        q z * lg (q z) - q z * lg (w z)
          - ((2 : ℝ) / 3) * (q z * lg (mX q z.1))
          - ((2 : ℝ) / 3) * (q z * lg (mY q z.2)) := by
    rw [refMeas, if_pos hzS]
    by_cases hz : q z = 0
    · simp [hz]
    · have hzpos : 0 < q z := lt_of_le_of_ne (hq.nonneg z) (Ne.symm hz)
      have hxle : q z ≤ mX q z.1 := by
        change q z ≤ push Prod.fst q z.1
        unfold push
        exact Finset.single_le_sum (fun a _ ↦ hq.nonneg a) (by simp)
      have hyle : q z ≤ mY q z.2 := by
        change q z ≤ push Prod.snd q z.2
        unfold push
        exact Finset.single_le_sum (fun a _ ↦ hq.nonneg a) (by simp)
      have hxpos : 0 < mX q z.1 := hzpos.trans_le hxle
      have hypos : 0 < mY q z.2 := hzpos.trans_le hyle
      have hw0 : w z ≠ 0 := (hw z hzS).ne'
      have hxpow0 : mX q z.1 ^ ((2 : ℝ) / 3) ≠ 0 :=
        (Real.rpow_pos_of_pos hxpos _).ne'
      have hypow0 : mY q z.2 ^ ((2 : ℝ) / 3) ≠ 0 :=
        (Real.rpow_pos_of_pos hypos _).ne'
      simp only [lg_eq_log_div]
      rw [Real.log_div hz (mul_ne_zero (mul_ne_zero hw0 hxpow0) hypow0),
        Real.log_mul (mul_ne_zero hw0 hxpow0) hypow0, Real.log_mul hw0 hxpow0,
        Real.log_rpow hxpos, Real.log_rpow hypos]
      ring
  have hsumlog :
      (∑ z ∈ S, q z * lg (q z / refMeas S w q z)) =
        (∑ z ∈ S, q z * lg (q z)) - (∑ z ∈ S, q z * lg (w z))
          - ((2 : ℝ) / 3) * (∑ z ∈ S, q z * lg (mX q z.1))
          - ((2 : ℝ) / 3) * (∑ z ∈ S, q z * lg (mY q z.2)) := by
    calc
      (∑ z ∈ S, q z * lg (q z / refMeas S w q z)) =
          ∑ z ∈ S, (q z * lg (q z) - q z * lg (w z)
            - ((2 : ℝ) / 3) * (q z * lg (mX q z.1))
            - ((2 : ℝ) / 3) * (q z * lg (mY q z.2))) := by
              apply Finset.sum_congr rfl
              intro z hzS
              exact hterm z hzS
      _ = _ := by
        rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
          ← Finset.mul_sum, ← Finset.mul_sum]
  have hkernel :
      (∑ z ∈ S, (-3 * lg (w z)) * q z) =
        -3 * (∑ z ∈ S, q z * lg (w z)) := by
    calc
      (∑ z ∈ S, (-3 * lg (w z)) * q z) =
          ∑ z ∈ S, -3 * (q z * lg (w z)) := by
            apply Finset.sum_congr rfl
            intro z _
            ring
      _ = -3 * (∑ z ∈ S, q z * lg (w z)) := by rw [Finset.mul_sum]
  rw [Gdef, hsumlog, hsumq, hsumX, hsumY, hkernel]
  unfold Phi
  ring

/-! ### Theorem 2.3 -/

private theorem Gdef_nonneg_aux {S : Finset (α × β)} {w : α × β → ℝ}
    (hw : Feasible S w) {q : α × β → ℝ} (hq : IsPMF q) (hqS : Supported S q) :
    0 ≤ Gdef S w q := by
  have hqX : IsPMF (mX q) := isPMF_push hq
  have hqY : IsPMF (mY q) := isPMF_push hq
  have hm : IsFinMeas (refMeas S w q) := by
    intro z
    rw [refMeas]
    split_ifs with hzS
    · exact mul_nonneg
        (mul_nonneg (hw.1 z hzS).le (Real.rpow_nonneg (hqX.nonneg z.1) _))
        (Real.rpow_nonneg (hqY.nonneg z.2) _)
    · exact le_rfl
  have hmass : mass (refMeas S w q) ≤ 1 := by
    rw [mass_refMeas_eq_Lambda]
    exact hw.2 (mX q) (mY q) hqX hqY
  have hsupp : ∀ z, q z ≠ 0 → refMeas S w q z ≠ 0 := by
    intro z hz
    have hzpos : 0 < q z := lt_of_le_of_ne (hq.nonneg z) (Ne.symm hz)
    have hzS : z ∈ S := by
      by_contra hzS
      exact hz (hqS z hzS)
    have hxle : q z ≤ mX q z.1 := by
      change q z ≤ push Prod.fst q z.1
      unfold push
      exact Finset.single_le_sum (fun a _ ↦ hq.nonneg a) (by simp)
    have hyle : q z ≤ mY q z.2 := by
      change q z ≤ push Prod.snd q z.2
      unfold push
      exact Finset.single_le_sum (fun a _ ↦ hq.nonneg a) (by simp)
    rw [refMeas, if_pos hzS]
    exact (mul_pos
      (mul_pos (hw.1 z hzS) (Real.rpow_pos_of_pos (hzpos.trans_le hxle) _))
      (Real.rpow_pos_of_pos (hzpos.trans_le hyle) _)).ne'
  have hKL : 0 ≤ ∑ z, q z * lg (q z / refMeas S w q z) :=
    unnormalized_gibbs_nonneg_lg hq hm hmass hsupp
  have hsum :
      (∑ z ∈ S, q z * lg (q z / refMeas S w q z)) =
        ∑ z, q z * lg (q z / refMeas S w q z) := by
    apply Finset.sum_subset (Finset.subset_univ S)
    intro z _ hzS
    rw [hqS z hzS, zero_mul]
  rw [Gdef, hsum]
  positivity

private lemma maximizer_rpow_two_thirds {γ : Type*} [Fintype γ] [DecidableEq γ]
    {R u : γ → ℝ} (hR : ∀ x, 0 ≤ R x) (hu : IsPMF u)
    (hmax : ∀ t : γ → ℝ, IsPMF t →
      (∑ x, R x * t x ^ ((2 : ℝ) / 3)) ≤
        ∑ x, R x * u x ^ ((2 : ℝ) / 3)) :
    (∀ x, R x * u x ^ ((2 : ℝ) / 3) =
      (∑ a, R a * u a ^ ((2 : ℝ) / 3)) * u x) ∧
    (0 < (∑ a, R a * u a ^ ((2 : ℝ) / 3)) →
      ∀ x, R x = 0 ↔ u x = 0) := by
  let C : ℝ := ∑ x, R x ^ (3 : ℕ)
  have hC : 0 ≤ C := by
    dsimp [C]
    exact Finset.sum_nonneg fun x _ => pow_nonneg (hR x) _
  by_cases hCzero : C = 0
  · have hRzero : ∀ x, R x = 0 := by
      intro x
      have hx := (Finset.sum_eq_zero_iff_of_nonneg
        (fun a _ => pow_nonneg (hR a) (3 : ℕ))).mp hCzero x (Finset.mem_univ x)
      simpa using hx
    constructor
    · intro x
      simp [hRzero]
    · intro hpos
      have : (∑ a, R a * u a ^ ((2 : ℝ) / 3)) = 0 := by simp [hRzero]
      linarith
  · have hCpos : 0 < C := lt_of_le_of_ne hC (Ne.symm hCzero)
    let D : ℝ := C ^ ((1 : ℝ) / 3)
    have hDpos : 0 < D := Real.rpow_pos_of_pos hCpos _
    have hDcube : D ^ (3 : ℕ) = C := by
      dsimp [D]
      rw [← Real.rpow_natCast, ← Real.rpow_mul hC]
      norm_num
    let a : γ → ℝ := fun x => R x / D
    have ha : ∀ x, 0 ≤ a x := fun x => div_nonneg (hR x) hDpos.le
    have hR_eq : ∀ x, R x = D * a x := by
      intro x
      dsimp [a]
      field_simp [hDpos.ne']
    let t : γ → ℝ := fun x => a x ^ (3 : ℕ)
    have ht : IsPMF t := by
      constructor
      · intro x
        exact pow_nonneg (ha x) _
      · unfold mass
        dsimp [t]
        calc
          (∑ x, a x ^ (3 : ℕ)) = ∑ x, R x ^ (3 : ℕ) / C := by
            apply Finset.sum_congr rfl
            intro x _
            dsimp [a]
            rw [div_pow, hDcube]
          _ = (∑ x, R x ^ (3 : ℕ)) / C := by rw [Finset.sum_div]
          _ = C / C := rfl
          _ = 1 := div_self hCzero
    have hpow32 (x : γ) :
        (a x ^ (3 : ℕ)) ^ ((2 : ℝ) / 3) = a x ^ (2 : ℕ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (ha x)]
      norm_num
    have hupow (x : γ) :
        (u x ^ ((2 : ℝ) / 3)) ^ ((3 : ℝ) / 2) = u x := by
      rw [← Real.rpow_mul (hu.nonneg x)]
      norm_num
    have hFt : (∑ x, R x * t x ^ ((2 : ℝ) / 3)) = D := by
      calc
        (∑ x, R x * t x ^ ((2 : ℝ) / 3)) =
            ∑ x, D * a x ^ (3 : ℕ) := by
              apply Finset.sum_congr rfl
              intro x _
              rw [hR_eq x]
              dsimp [t]
              rw [hpow32]
              ring
        _ = D * ∑ x, a x ^ (3 : ℕ) := by rw [Finset.mul_sum]
        _ = D := by
          have htotal := ht.total
          change (∑ x, a x ^ (3 : ℕ)) = 1 at htotal
          rw [htotal, mul_one]
    have hpq : (3 : ℝ).HolderConjugate ((3 : ℝ) / 2) := by
      rw [Real.holderConjugate_iff]
      norm_num
    have hYoung (x : γ) :
        a x * u x ^ ((2 : ℝ) / 3) ≤
          a x ^ (3 : ℕ) / 3 + u x / ((3 : ℝ) / 2) := by
      have hy := Real.young_inequality_of_nonneg
        (a := a x) (b := u x ^ ((2 : ℝ) / 3))
        (p := (3 : ℝ)) (q := (3 : ℝ) / 2)
        (ha x) (Real.rpow_nonneg (hu.nonneg x) _) hpq
      calc
        a x * u x ^ ((2 : ℝ) / 3) ≤
            a x ^ (3 : ℝ) / 3
              + (u x ^ ((2 : ℝ) / 3)) ^ ((3 : ℝ) / 2) / ((3 : ℝ) / 2) := hy
        _ = a x ^ (3 : ℕ) / 3 + u x / ((3 : ℝ) / 2) := by
          exact congrArg₂ (· + ·)
            (congrArg (fun s : ℝ => s / 3) (Real.rpow_natCast (a x) 3))
            (congrArg (fun s : ℝ => s / ((3 : ℝ) / 2)) (hupow x))
    have hsumRhs :
        (∑ x, (a x ^ (3 : ℕ) / 3 + u x / ((3 : ℝ) / 2))) = 1 := by
      rw [Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.sum_div]
      have hta := ht.total
      have huu := hu.total
      change (∑ x, a x ^ (3 : ℕ)) = 1 at hta
      change (∑ x, u x) = 1 at huu
      rw [hta, huu]
      norm_num
    have hsumLe : (∑ x, a x * u x ^ ((2 : ℝ) / 3)) ≤ 1 := by
      calc
        (∑ x, a x * u x ^ ((2 : ℝ) / 3)) ≤
            ∑ x, (a x ^ (3 : ℕ) / 3 + u x / ((3 : ℝ) / 2)) :=
          Finset.sum_le_sum fun x _ => hYoung x
        _ = 1 := hsumRhs
    have hFuRewrite :
        (∑ x, R x * u x ^ ((2 : ℝ) / 3)) =
          D * ∑ x, a x * u x ^ ((2 : ℝ) / 3) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      rw [hR_eq x]
      ring
    have hFuLe : (∑ x, R x * u x ^ ((2 : ℝ) / 3)) ≤ D := by
      rw [hFuRewrite]
      simpa using mul_le_mul_of_nonneg_left hsumLe hDpos.le
    have hFuEq : (∑ x, R x * u x ^ ((2 : ℝ) / 3)) = D := by
      apply le_antisymm hFuLe
      rw [← hFt]
      exact hmax t ht
    have hsumEq : (∑ x, a x * u x ^ ((2 : ℝ) / 3)) = 1 := by
      have hmul : D * (∑ x, a x * u x ^ ((2 : ℝ) / 3)) = D * 1 := by
        rw [← hFuRewrite, hFuEq, mul_one]
      exact (mul_left_cancel₀ hDpos.ne') hmul
    have hgapSum :
        (∑ x, ((a x ^ (3 : ℕ) / 3 + u x / ((3 : ℝ) / 2))
          - a x * u x ^ ((2 : ℝ) / 3))) = 0 := by
      rw [Finset.sum_sub_distrib, hsumRhs, hsumEq, sub_self]
    have hYoungEq : ∀ x,
        a x * u x ^ ((2 : ℝ) / 3) =
          a x ^ (3 : ℕ) / 3 + u x / ((3 : ℝ) / 2) := by
      intro x
      have hxzero := (Finset.sum_eq_zero_iff_of_nonneg
        (fun y _ => sub_nonneg.mpr (hYoung y))).mp hgapSum x (Finset.mem_univ x)
      linarith
    have hau : ∀ x, a x ^ (3 : ℕ) = u x := by
      intro x
      have heq :
          a x * u x ^ ((2 : ℝ) / 3) =
            a x ^ (3 : ℝ) / 3
              + (u x ^ ((2 : ℝ) / 3)) ^ ((3 : ℝ) / 2) / ((3 : ℝ) / 2) := by
        calc
          a x * u x ^ ((2 : ℝ) / 3) =
              a x ^ (3 : ℕ) / 3 + u x / ((3 : ℝ) / 2) := hYoungEq x
          _ = a x ^ (3 : ℝ) / 3
              + (u x ^ ((2 : ℝ) / 3)) ^ ((3 : ℝ) / 2) / ((3 : ℝ) / 2) := by
            exact congrArg₂ (· + ·)
              (congrArg (fun s : ℝ => s / 3) (Real.rpow_natCast (a x) 3).symm)
              (congrArg (fun s : ℝ => s / ((3 : ℝ) / 2)) (hupow x).symm)
      have hpowers := (Real.young_inequality_eq_iff_of_nonneg
        (a := a x) (b := u x ^ ((2 : ℝ) / 3))
        (p := (3 : ℝ)) (q := (3 : ℝ) / 2)
        (ha x) (Real.rpow_nonneg (hu.nonneg x) _) hpq).mp heq
      exact (Real.rpow_natCast (a x) 3).symm.trans (hpowers.trans (hupow x))
    constructor
    · intro x
      rw [hFuEq, ← hau x, hR_eq x, hpow32]
      ring
    · intro _ x
      rw [← hau x]
      dsimp [a]
      simp [hDpos.ne']

/-- **Theorem 2.3** (validity ⟺ feasibility). -/
theorem valid_iff_feasible {S : Finset (α × β)} {w : α × β → ℝ} (hw : ∀ z ∈ S, 0 < w z) :
    Valid S (fun z => -3 * lg (w z)) ↔ Feasible S w := by
  constructor
  · intro hvalid
    refine ⟨hw, ?_⟩
    intro u v hu hv
    by_cases hSempty : S = ∅
    · simp [Lambda, hSempty]
    let K : Set ((α → ℝ) × (β → ℝ)) :=
      Set.prod (stdSimplex ℝ α) (stdSimplex ℝ β)
    have huΔ : u ∈ stdSimplex ℝ α := by
      exact ⟨hu.nonneg, by simpa [mass] using hu.total⟩
    have hvΔ : v ∈ stdSimplex ℝ β := by
      exact ⟨hv.nonneg, by simpa [mass] using hv.total⟩
    have huvK : (u, v) ∈ K := ⟨huΔ, hvΔ⟩
    have hK : IsCompact K :=
      (isCompact_stdSimplex ℝ α).prod (isCompact_stdSimplex ℝ β)
    have hcont : Continuous (fun uv : (α → ℝ) × (β → ℝ) =>
        Lambda S w uv.1 uv.2) := by
      unfold Lambda
      fun_prop (disch := norm_num)
    obtain ⟨uv, huv, huvMax⟩ :=
      hK.exists_isMaxOn ⟨(u, v), huvK⟩ hcont.continuousOn
    let u₀ : α → ℝ := uv.1
    let v₀ : β → ℝ := uv.2
    have hu₀Δ : u₀ ∈ stdSimplex ℝ α := huv.1
    have hv₀Δ : v₀ ∈ stdSimplex ℝ β := huv.2
    have hu₀ : IsPMF u₀ :=
      ⟨hu₀Δ.1, by simpa [mass] using hu₀Δ.2⟩
    have hv₀ : IsPMF v₀ :=
      ⟨hv₀Δ.1, by simpa [mass] using hv₀Δ.2⟩
    have htarget : Lambda S w u v ≤ Lambda S w u₀ v₀ :=
      huvMax huvK
    let R : α → ℝ := fun x =>
      ∑ z ∈ S.filter (fun z => z.1 = x), w z * v₀ z.2 ^ ((2 : ℝ) / 3)
    have hR : ∀ x, 0 ≤ R x := by
      intro x
      dsimp [R]
      exact Finset.sum_nonneg fun z hz =>
        mul_nonneg (hw z (Finset.mem_filter.mp hz).1).le
          (Real.rpow_nonneg (hv₀.nonneg z.2) _)
    have hLambdaRow (s : α → ℝ) :
        Lambda S w s v₀ = ∑ x, R x * s x ^ ((2 : ℝ) / 3) := by
      unfold Lambda
      rw [← Finset.sum_fiberwise S Prod.fst
        (fun z => w z * s z.1 ^ ((2 : ℝ) / 3) * v₀ z.2 ^ ((2 : ℝ) / 3))]
      apply Finset.sum_congr rfl
      intro x _
      dsimp [R]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro z hz
      rw [(Finset.mem_filter.mp hz).2]
      ring
    have hu₀Max : ∀ t : α → ℝ, IsPMF t →
        (∑ x, R x * t x ^ ((2 : ℝ) / 3)) ≤
          ∑ x, R x * u₀ x ^ ((2 : ℝ) / 3) := by
      intro t ht
      rw [← hLambdaRow, ← hLambdaRow]
      have htK : (t, v₀) ∈ K :=
        ⟨⟨ht.nonneg, by simpa [mass] using ht.total⟩, hv₀Δ⟩
      simpa [u₀, v₀] using (huvMax htK)
    have hrow := (maximizer_rpow_two_thirds hR hu₀ hu₀Max).1
    let Q : β → ℝ := fun y =>
      ∑ z ∈ S.filter (fun z => z.2 = y), w z * u₀ z.1 ^ ((2 : ℝ) / 3)
    have hQ : ∀ y, 0 ≤ Q y := by
      intro y
      dsimp [Q]
      exact Finset.sum_nonneg fun z hz =>
        mul_nonneg (hw z (Finset.mem_filter.mp hz).1).le
          (Real.rpow_nonneg (hu₀.nonneg z.1) _)
    have hLambdaCol (s : β → ℝ) :
        Lambda S w u₀ s = ∑ y, Q y * s y ^ ((2 : ℝ) / 3) := by
      unfold Lambda
      rw [← Finset.sum_fiberwise S Prod.snd
        (fun z => w z * u₀ z.1 ^ ((2 : ℝ) / 3) * s z.2 ^ ((2 : ℝ) / 3))]
      apply Finset.sum_congr rfl
      intro y _
      dsimp [Q]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro z hz
      rw [(Finset.mem_filter.mp hz).2]
    have hv₀Max : ∀ t : β → ℝ, IsPMF t →
        (∑ y, Q y * t y ^ ((2 : ℝ) / 3)) ≤
          ∑ y, Q y * v₀ y ^ ((2 : ℝ) / 3) := by
      intro t ht
      rw [← hLambdaCol, ← hLambdaCol]
      have htK : (u₀, t) ∈ K :=
        ⟨hu₀Δ, ⟨ht.nonneg, by simpa [mass] using ht.total⟩⟩
      simpa [u₀, v₀] using (huvMax htK)
    have hcol := (maximizer_rpow_two_thirds hQ hv₀ hv₀Max).1
    let M : ℝ := Lambda S w u₀ v₀
    have hrow' : ∀ x, R x * u₀ x ^ ((2 : ℝ) / 3) = M * u₀ x := by
      intro x
      rw [hrow x, ← hLambdaRow]
    have hcol' : ∀ y, Q y * v₀ y ^ ((2 : ℝ) / 3) = M * v₀ y := by
      intro y
      rw [hcol y, ← hLambdaCol]
    obtain ⟨z₀, hz₀⟩ : S.Nonempty := by
      simpa [Finset.nonempty_iff_ne_empty] using hSempty
    let du : α → ℝ := fun x => if x = z₀.1 then 1 else 0
    let dv : β → ℝ := fun y => if y = z₀.2 then 1 else 0
    have hdu : IsPMF du := by
      constructor
      · intro x
        dsimp [du]
        split <;> norm_num
      · simp [mass, du]
    have hdv : IsPMF dv := by
      constructor
      · intro y
        dsimp [dv]
        split <;> norm_num
      · simp [mass, dv]
    have hdelta : Lambda S w du dv = w z₀ := by
      unfold Lambda
      calc
        (∑ z ∈ S, w z * du z.1 ^ ((2 : ℝ) / 3) * dv z.2 ^ ((2 : ℝ) / 3)) =
            w z₀ * du z₀.1 ^ ((2 : ℝ) / 3) * dv z₀.2 ^ ((2 : ℝ) / 3) := by
          apply Finset.sum_eq_single z₀
          · intro z hzS hne
            by_cases hx : z.1 = z₀.1
            · by_cases hy : z.2 = z₀.2
              · exact (hne (Prod.ext hx hy)).elim
              · simp [du, dv, hx, hy]
            · simp [du, dv, hx]
          · intro hz
            exact (hz hz₀).elim
        _ = w z₀ := by simp [du, dv]
    have hdeltaMax : Lambda S w du dv ≤ M := by
      have hdK : (du, dv) ∈ K :=
        ⟨⟨hdu.nonneg, by simpa [mass] using hdu.total⟩,
          ⟨hdv.nonneg, by simpa [mass] using hdv.total⟩⟩
      simpa [M, u₀, v₀] using (huvMax hdK)
    have hMpos : 0 < M := by
      rw [hdelta] at hdeltaMax
      exact (hw z₀ hz₀).trans_le hdeltaMax
    let m : α × β → ℝ := fun z =>
      if z ∈ S then
        w z * u₀ z.1 ^ ((2 : ℝ) / 3) * v₀ z.2 ^ ((2 : ℝ) / 3)
      else 0
    have hm : IsFinMeas m := by
      intro z
      dsimp [m]
      split_ifs with hzS
      · exact mul_nonneg
          (mul_nonneg (hw z hzS).le (Real.rpow_nonneg (hu₀.nonneg z.1) _))
          (Real.rpow_nonneg (hv₀.nonneg z.2) _)
      · exact le_rfl
    have hmassm : mass m = M := by
      simp [mass, m, M, Lambda]
    have hmX (x : α) :
        mX m x = R x * u₀ x ^ ((2 : ℝ) / 3) := by
      let T := (Finset.univ.filter fun z : α × β => z.1 = x)
      let U := (S.filter fun z : α × β => z.1 = x)
      have hUT : U ⊆ T := by
        intro z hz
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_univ z, (Finset.mem_filter.mp hz).2⟩
      calc
        mX m x = ∑ z ∈ T, m z := rfl
        _ = ∑ z ∈ U, m z := by
          symm
          apply Finset.sum_subset hUT
          intro z hzT hzU
          have hzS : z ∉ S := by
            intro hzS
            exact hzU (Finset.mem_filter.mpr
              ⟨hzS, (Finset.mem_filter.mp hzT).2⟩)
          simp [m, hzS]
        _ = ∑ z ∈ U,
            w z * u₀ z.1 ^ ((2 : ℝ) / 3) * v₀ z.2 ^ ((2 : ℝ) / 3) := by
          apply Finset.sum_congr rfl
          intro z hz
          simp [m, (Finset.mem_filter.mp hz).1]
        _ = R x * u₀ x ^ ((2 : ℝ) / 3) := by
          dsimp [R, U]
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro z hz
          rw [(Finset.mem_filter.mp hz).2]
          ring
    have hmY (y : β) :
        mY m y = Q y * v₀ y ^ ((2 : ℝ) / 3) := by
      let T := (Finset.univ.filter fun z : α × β => z.2 = y)
      let U := (S.filter fun z : α × β => z.2 = y)
      have hUT : U ⊆ T := by
        intro z hz
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_univ z, (Finset.mem_filter.mp hz).2⟩
      calc
        mY m y = ∑ z ∈ T, m z := rfl
        _ = ∑ z ∈ U, m z := by
          symm
          apply Finset.sum_subset hUT
          intro z hzT hzU
          have hzS : z ∉ S := by
            intro hzS
            exact hzU (Finset.mem_filter.mpr
              ⟨hzS, (Finset.mem_filter.mp hzT).2⟩)
          simp [m, hzS]
        _ = ∑ z ∈ U,
            w z * u₀ z.1 ^ ((2 : ℝ) / 3) * v₀ z.2 ^ ((2 : ℝ) / 3) := by
          apply Finset.sum_congr rfl
          intro z hz
          simp [m, (Finset.mem_filter.mp hz).1]
        _ = Q y * v₀ y ^ ((2 : ℝ) / 3) := by
          dsimp [Q, U]
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro z hz
          rw [(Finset.mem_filter.mp hz).2]
    let q : α × β → ℝ := fun z => M⁻¹ * m z
    have hq : IsPMF q := by
      constructor
      · intro z
        exact mul_nonneg (inv_nonneg.mpr hMpos.le) (hm z)
      · unfold mass
        dsimp [q]
        rw [← Finset.mul_sum]
        change M⁻¹ * mass m = 1
        rw [hmassm, inv_mul_cancel₀ hMpos.ne']
    have hqS : Supported S q := by
      intro z hzS
      simp [q, m, hzS]
    have hqX : mX q = u₀ := by
      funext x
      have hpush := congrFun (push_smul Prod.fst m M⁻¹) x
      change mX (fun z => M⁻¹ * m z) x = M⁻¹ * mX m x at hpush
      change mX q x = u₀ x
      rw [hpush, hmX, hrow']
      field_simp [hMpos.ne']
    have hqY : mY q = v₀ := by
      funext y
      have hpush := congrFun (push_smul Prod.snd m M⁻¹) y
      change mY (fun z => M⁻¹ * m z) y = M⁻¹ * mY m y at hpush
      change mY q y = v₀ y
      rw [hpush, hmY, hcol']
      field_simp [hMpos.ne']
    have href : refMeas S w q = m := by
      funext z
      by_cases hzS : z ∈ S
      · simp [refMeas, m, hzS, hqX, hqY]
      · simp [refMeas, m, hzS]
    have hsumqS : (∑ z ∈ S, q z) = 1 := by
      calc
        (∑ z ∈ S, q z) = ∑ z, q z := by
          apply Finset.sum_subset (Finset.subset_univ S)
          intro z _ hzS
          exact hqS z hzS
        _ = 1 := by simpa [mass] using hq.total
    have hGcalc : Gdef S w q = 3 * lg M⁻¹ := by
      rw [Gdef, href]
      congr 1
      calc
        (∑ z ∈ S, q z * lg (q z / m z)) =
            ∑ z ∈ S, q z * lg M⁻¹ := by
              apply Finset.sum_congr rfl
              intro z _
              by_cases hmz : m z = 0
              · simp [q, hmz]
              · congr 1
                dsimp [q]
                field_simp [hmz]
        _ = (∑ z ∈ S, q z) * lg M⁻¹ := by rw [Finset.sum_mul]
        _ = lg M⁻¹ := by rw [hsumqS, one_mul]
    have hvalidq := hvalid q hq hqS
    have hgap := Gdef_eq_certificate_gap hw hq hqS
    have hGnonneg : 0 ≤ Gdef S w q := by linarith
    rw [hGcalc] at hGnonneg
    have hlginv : 0 ≤ lg M⁻¹ := by linarith
    rw [lg_eq_log_div] at hlginv
    have hloginv : 0 ≤ Real.log M⁻¹ := by
      rcases div_nonneg_iff.mp hlginv with h | h
      · exact h.1
      · exfalso
        linarith [Real.log_pos one_lt_two]
    have hinv : 1 ≤ M⁻¹ :=
      (Real.log_nonneg_iff (inv_pos.mpr hMpos)).mp hloginv
    have hMle : M ≤ 1 := by
      rw [inv_eq_one_div] at hinv
      have := (le_div_iff₀ hMpos).mp hinv
      simpa using this
    exact htarget.trans hMle
  · intro hfeas q hq hqS
    have hgap := Gdef_eq_certificate_gap hfeas.1 hq hqS
    have hnonneg := Gdef_nonneg_aux hfeas hq hqS
    linarith

/-- **Theorem 2.3**, consequence: the defect of a feasible kernel is nonnegative
on *every* law. -/
theorem Gdef_nonneg {S : Finset (α × β)} {w : α × β → ℝ} (hw : Feasible S w)
    {q : α × β → ℝ} (hq : IsPMF q) (hqS : Supported S q) :
    0 ≤ Gdef S w q := by
  exact Gdef_nonneg_aux hw hq hqS

/-- **Theorem 2.3**, equality case: `G_w(q) = 0` exactly at contacts. -/
theorem Gdef_eq_zero_iff {S : Finset (α × β)} {w : α × β → ℝ} (hw : Feasible S w)
    {q : α × β → ℝ} (hq : IsPMF q) (hqS : Supported S q) :
    Gdef S w q = 0 ↔ IsContact S w q := by
  have hqX : IsPMF (mX q) := isPMF_push hq
  have hqY : IsPMF (mY q) := isPMF_push hq
  have hm : IsFinMeas (refMeas S w q) := by
    intro z
    rw [refMeas]
    split_ifs with hzS
    · exact mul_nonneg
        (mul_nonneg (hw.1 z hzS).le (Real.rpow_nonneg (hqX.nonneg z.1) _))
        (Real.rpow_nonneg (hqY.nonneg z.2) _)
    · exact le_rfl
  have hmass : mass (refMeas S w q) ≤ 1 := by
    rw [mass_refMeas_eq_Lambda]
    exact hw.2 (mX q) (mY q) hqX hqY
  have hsupp : ∀ z, q z ≠ 0 → refMeas S w q z ≠ 0 := by
    intro z hz
    have hzpos : 0 < q z := lt_of_le_of_ne (hq.nonneg z) (Ne.symm hz)
    have hzS : z ∈ S := by
      by_contra hzS
      exact hz (hqS z hzS)
    have hxle : q z ≤ mX q z.1 := by
      change q z ≤ push Prod.fst q z.1
      unfold push
      exact Finset.single_le_sum (fun a _ ↦ hq.nonneg a) (by simp)
    have hyle : q z ≤ mY q z.2 := by
      change q z ≤ push Prod.snd q z.2
      unfold push
      exact Finset.single_le_sum (fun a _ ↦ hq.nonneg a) (by simp)
    rw [refMeas, if_pos hzS]
    exact (mul_pos
      (mul_pos (hw.1 z hzS) (Real.rpow_pos_of_pos (hzpos.trans_le hxle) _))
      (Real.rpow_pos_of_pos (hzpos.trans_le hyle) _)).ne'
  have hsum :
      (∑ z ∈ S, q z * lg (q z / refMeas S w q z)) =
        ∑ z, q z * lg (q z / refMeas S w q z) := by
    apply Finset.sum_subset (Finset.subset_univ S)
    intro z _ hzS
    rw [hqS z hzS, zero_mul]
  constructor
  · intro hG
    have hsumS :
        (∑ z ∈ S, q z * lg (q z / refMeas S w q z)) = 0 := by
      rw [Gdef] at hG
      linarith
    have hsumAll :
        (∑ z, q z * lg (q z / refMeas S w q z)) = 0 := by
      rw [← hsum]
      exact hsumS
    have href : q = refMeas S w q :=
      (unnormalized_gibbs_eq_zero_iff hq hm hmass hsupp).mp hsumAll
    refine ⟨hq, hqS, ?_⟩
    intro z hzS
    calc
      q z = refMeas S w q z := congrFun href z
      _ = w z * mX q z.1 ^ ((2 : ℝ) / 3) * mY q z.2 ^ ((2 : ℝ) / 3) := by
        rw [refMeas, if_pos hzS]
  · rintro ⟨_, hqS', hcontact⟩
    have href : refMeas S w q = q := by
      funext z
      by_cases hzS : z ∈ S
      · rw [refMeas, if_pos hzS, ← hcontact z hzS]
      · rw [refMeas, if_neg hzS, hqS' z hzS]
    have hsumZero :
        (∑ z ∈ S, q z * lg (q z / refMeas S w q z)) = 0 := by
      rw [href]
      apply Finset.sum_eq_zero
      intro z _
      by_cases hz : q z = 0
      · simp [hz]
      · rw [div_self hz, lg_one, mul_zero]
    rw [Gdef, hsumZero, mul_zero]

/-! ### Corollary 2.4 and Theorem 2.5 -/

private noncomputable def dualContinuousEntropy {γ : Type*} [Fintype γ]
    (m : γ → ℝ) : ℝ :=
  (∑ a, Real.negMulLog (m a)) / Real.log 2

private lemma H_eq_dualContinuousEntropy {γ : Type*} [Fintype γ]
    {m : γ → ℝ} (hm : IsPMF m) : H m = dualContinuousEntropy m := by
  have h := H_eq_negMulLog hm.isFinMeas
  rw [hm.total, Real.log_one, mul_zero, zero_add] at h
  apply (eq_div_iff (Real.log_pos one_lt_two).ne').2
  rw [mul_comm]
  exact h

private lemma continuous_dualContinuousEntropy {γ : Type*} [Fintype γ] :
    Continuous (dualContinuousEntropy : (γ → ℝ) → ℝ) := by
  unfold dualContinuousEntropy
  fun_prop

private noncomputable def dualContinuousPhi (q : α × β → ℝ) : ℝ :=
  3 * dualContinuousEntropy q
    - 2 * dualContinuousEntropy (push Prod.fst q)
    - 2 * dualContinuousEntropy (push Prod.snd q)

private lemma dual_continuous_push_map {γ δ : Type*} [Fintype γ] [Fintype δ]
    [DecidableEq δ] (f : γ → δ) :
    Continuous (fun m : γ → ℝ => push f m) := by
  apply continuous_pi
  intro c
  unfold push
  fun_prop

private lemma continuous_dualContinuousPhi :
    Continuous (dualContinuousPhi : (α × β → ℝ) → ℝ) := by
  unfold dualContinuousPhi
  have hq : Continuous (fun q : α × β → ℝ => dualContinuousEntropy q) :=
    continuous_dualContinuousEntropy
  have hqX : Continuous (fun q : α × β → ℝ =>
      dualContinuousEntropy (push Prod.fst q)) :=
    continuous_dualContinuousEntropy.comp (dual_continuous_push_map Prod.fst)
  have hqY : Continuous (fun q : α × β → ℝ =>
      dualContinuousEntropy (push Prod.snd q)) :=
    continuous_dualContinuousEntropy.comp (dual_continuous_push_map Prod.snd)
  exact ((continuous_const.mul hq).sub (continuous_const.mul hqX)).sub
    (continuous_const.mul hqY)

private lemma Phi_eq_dualContinuousPhi {q : α × β → ℝ} (hq : IsPMF q) :
    Phi q = dualContinuousPhi q := by
  have hqX : IsPMF (mX q) := isPMF_push hq
  have hqY : IsPMF (mY q) := isPMF_push hq
  unfold Phi dualContinuousPhi
  rw [H_eq_dualContinuousEntropy hq, H_eq_dualContinuousEntropy hqX,
    H_eq_dualContinuousEntropy hqY]

private def dualPmfSet (S : Finset (α × β)) : Set (α × β → ℝ) :=
  {q | IsPMF q ∧ Supported S q}

private noncomputable def dualPhiGraph (S : Finset (α × β)) :
    Set ((α × β → ℝ) × ℝ) :=
  (fun q => (q, Phi q)) '' dualPmfSet S

private lemma isCompact_dualPmfSet (S : Finset (α × β)) :
    IsCompact (dualPmfSet S : Set (α × β → ℝ)) := by
  let Z : Set (α × β → ℝ) := {q | Supported S q}
  have hZ :
      Z = ⋂ z ∈ (Finset.univ.filter fun z : α × β => z ∉ S),
        {q : α × β → ℝ | q z = 0} := by
    ext q
    simp only [Z, Set.mem_setOf_eq, Set.mem_iInter, Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor
    · intro h z hz
      exact h z hz
    · intro h z hz
      exact h z hz
  have hZclosed : IsClosed Z := by
    rw [hZ]
    exact isClosed_biInter fun z _ =>
      isClosed_eq (continuous_apply z) continuous_const
  have heq :
      dualPmfSet S =
        stdSimplex ℝ (α × β) ∩ Z := by
    ext q
    constructor
    · rintro ⟨hq, hqS⟩
      exact ⟨⟨hq.nonneg, by simpa [mass] using hq.total⟩, hqS⟩
    · rintro ⟨⟨hq, htotal⟩, hqS⟩
      exact ⟨⟨hq, by simpa [mass] using htotal⟩, hqS⟩
  rw [heq]
  exact (isCompact_stdSimplex ℝ (α × β)).inter_right hZclosed

private lemma isCompact_dualPhiGraph (S : Finset (α × β)) :
    IsCompact (dualPhiGraph S : Set ((α × β → ℝ) × ℝ)) := by
  let graphMap : (α × β → ℝ) → (α × β → ℝ) × ℝ :=
    fun q => (q, dualContinuousPhi q)
  have hgraphMap : Continuous graphMap :=
    continuous_id.prodMk continuous_dualContinuousPhi
  have heq : dualPhiGraph S = graphMap '' dualPmfSet S := by
    ext x
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact ⟨q, hq, by simp [graphMap, Phi_eq_dualContinuousPhi hq.1]⟩
    · rintro ⟨q, hq, rfl⟩
      exact ⟨q, hq, by simp [graphMap, Phi_eq_dualContinuousPhi hq.1]⟩
  rw [heq]
  exact (isCompact_dualPmfSet S).image hgraphMap

private noncomputable def dualHullSize : ℕ :=
  Module.finrank ℝ ((α × β → ℝ) × ℝ) + 1

private noncomputable def dualHullBarycenter
    (a : (Fin (dualHullSize (α := α) (β := β)) → ℝ) ×
      (Fin (dualHullSize (α := α) (β := β)) → (α × β → ℝ) × ℝ)) :
    (α × β → ℝ) × ℝ :=
  ∑ i, a.1 i • a.2 i

private noncomputable def dualHullParams (S : Finset (α × β)) :
    Set ((Fin (dualHullSize (α := α) (β := β)) → ℝ) ×
      (Fin (dualHullSize (α := α) (β := β)) → (α × β → ℝ) × ℝ)) :=
  stdSimplex ℝ (Fin (dualHullSize (α := α) (β := β))) ×ˢ
    Set.pi (Set.univ : Set (Fin (dualHullSize (α := α) (β := β))))
      (fun _ => dualPhiGraph S)

private lemma continuous_dualHullBarycenter :
    Continuous (dualHullBarycenter (α := α) (β := β)) := by
  unfold dualHullBarycenter
  fun_prop

private lemma isCompact_dualHullParams (S : Finset (α × β)) :
    IsCompact (dualHullParams S) := by
  unfold dualHullParams
  apply IsCompact.prod (isCompact_stdSimplex ℝ _)
  exact isCompact_univ_pi fun _ => isCompact_dualPhiGraph S

private lemma dualHullBarycenter_image_subset (S : Finset (α × β)) :
    dualHullBarycenter (α := α) (β := β) '' dualHullParams S ⊆
      convexHull ℝ (dualPhiGraph S) := by
  rintro x ⟨a, ha, rfl⟩
  rcases ha with ⟨hweights, hpoints⟩
  apply mem_convexHull_of_exists_fintype a.1 a.2
  · exact hweights.1
  · exact hweights.2
  · intro i
    exact hpoints i (Set.mem_univ i)
  · rfl

private lemma dualConvexHull_subset_barycenter_image
    {S : Finset (α × β)} {p : α × β → ℝ}
    (hp : IsPMF p) (hpS : Supported S p) :
    convexHull ℝ (dualPhiGraph S) ⊆
      dualHullBarycenter (α := α) (β := β) '' dualHullParams S := by
  intro x hx
  rw [convexHull_eq_union] at hx
  simp only [Set.mem_iUnion, exists_prop] at hx
  rcases hx with ⟨t, htGraph, htIndependent, hxt⟩
  have htcard : Fintype.card t ≤ dualHullSize (α := α) (β := β) := by
    calc
      Fintype.card t ≤
          Module.finrank ℝ (vectorSpan ℝ
            (Set.range ((↑) : t → (α × β → ℝ) × ℝ))) + 1 :=
        htIndependent.card_le_finrank_succ
      _ ≤ Module.finrank ℝ ((α × β → ℝ) × ℝ) + 1 :=
        Nat.add_le_add_right (Submodule.finrank_le _) 1
      _ = dualHullSize (α := α) (β := β) := rfl
  let e : t ↪ Fin (dualHullSize (α := α) (β := β)) :=
    Classical.choice (Function.Embedding.nonempty_of_card_le (by simpa using htcard))
  rcases (Finset.mem_convexHull'.mp hxt) with
    ⟨weights₀, hweights₀_nonneg, hweights₀_sum, hcenter⟩
  let weights : Fin (dualHullSize (α := α) (β := β)) → ℝ :=
    fun j => ∑ i : t, if e i = j then weights₀ i.1 else 0
  let points : Fin (dualHullSize (α := α) (β := β)) →
      (α × β → ℝ) × ℝ :=
    fun j => if h : ∃ i : t, e i = j then (Classical.choose h).1 else (p, Phi p)
  have hinner_weight (i : t) :
      (∑ j, if e i = j then weights₀ i.1 else 0) = weights₀ i.1 := by
    have hsingle :
        (∑ j, if e i = j then weights₀ i.1 else 0) =
          (if e i = e i then weights₀ i.1 else 0) := by
      apply Finset.sum_eq_single (e i)
      · intro j _ hji
        simp [Ne.symm hji]
      · simp
    simpa using hsingle
  have hweights_nonneg : ∀ j, 0 ≤ weights j := by
    intro j
    dsimp [weights]
    apply Finset.sum_nonneg
    intro i _
    split
    · exact hweights₀_nonneg i.1 i.2
    · exact le_rfl
  have hweights_sum : ∑ j, weights j = 1 := by
    calc
      (∑ j, weights j) =
          ∑ j, ∑ i : t, if e i = j then weights₀ i.1 else 0 := rfl
      _ = ∑ i : t, ∑ j, if e i = j then weights₀ i.1 else 0 := by
        rw [Finset.sum_comm]
      _ = ∑ i : t, weights₀ i.1 := by
        apply Finset.sum_congr rfl
        intro i _
        exact hinner_weight i
      _ = ∑ y ∈ t, weights₀ y := by
        simp only [univ_eq_attach]
        rw [Finset.sum_attach]
      _ = 1 := hweights₀_sum
  have hpoints (j : Fin (dualHullSize (α := α) (β := β))) :
      points j ∈ dualPhiGraph S := by
    by_cases hj : ∃ i : t, e i = j
    · rw [show points j = (Classical.choose hj).1 by simp [points, hj]]
      exact htGraph (Classical.choose hj).2
    · rw [show points j = (p, Phi p) by simp [points, hj]]
      exact ⟨p, ⟨hp, hpS⟩, rfl⟩
  have hterm (j : Fin (dualHullSize (α := α) (β := β))) :
      weights j • points j =
        ∑ i : t, if e i = j then weights₀ i.1 • i.1 else 0 := by
    by_cases hj : ∃ i : t, e i = j
    · let i₀ : t := Classical.choose hj
      have hi₀ : e i₀ = j := Classical.choose_spec hj
      have hweight : weights j = weights₀ i₀.1 := by
        dsimp [weights]
        have hsingle :
            (∑ i : t, if e i = j then weights₀ i.1 else 0) =
              (if e i₀ = j then weights₀ i₀.1 else 0) := by
          apply Finset.sum_eq_single i₀
          · intro i _ hii₀
            have hei : e i ≠ j := by
              intro hei
              exact hii₀ (e.injective (hei.trans hi₀.symm))
            simp [hei]
          · simp
        simpa [hi₀] using hsingle
      have hpoint : points j = i₀.1 := by
        dsimp [points, i₀]
        rw [dif_pos hj]
      rw [hweight, hpoint]
      symm
      have hsingle :
          (∑ i : t, if e i = j then weights₀ i.1 • i.1 else 0) =
            (if e i₀ = j then weights₀ i₀.1 • i₀.1 else 0) := by
        apply Finset.sum_eq_single i₀
        · intro i _ hii₀
          have hei : e i ≠ j := by
            intro hei
            exact hii₀ (e.injective (hei.trans hi₀.symm))
          simp [hei]
        · simp
      simpa [hi₀] using hsingle
    · have hnot (i : t) : e i ≠ j := fun hi => hj ⟨i, hi⟩
      have hweight : weights j = 0 := by
        dsimp [weights]
        exact Finset.sum_eq_zero fun i _ => by simp [hnot i]
      rw [hweight, zero_smul]
      symm
      exact Finset.sum_eq_zero fun i _ => by simp [hnot i]
  have hbary : dualHullBarycenter (weights, points) = x := by
    calc
      dualHullBarycenter (weights, points) = ∑ j, weights j • points j := rfl
      _ = ∑ j, ∑ i : t, if e i = j then weights₀ i.1 • i.1 else 0 := by
        apply Finset.sum_congr rfl
        intro j _
        exact hterm j
      _ = ∑ i : t, ∑ j, if e i = j then weights₀ i.1 • i.1 else 0 := by
        rw [Finset.sum_comm]
      _ = ∑ i : t, weights₀ i.1 • i.1 := by
        apply Finset.sum_congr rfl
        intro i _
        have hsingle :
            (∑ j, if e i = j then weights₀ i.1 • i.1 else 0) =
              (if e i = e i then weights₀ i.1 • i.1 else 0) := by
          apply Finset.sum_eq_single (e i)
          · intro j _ hji
            simp [Ne.symm hji]
          · simp
        simpa using hsingle
      _ = ∑ y ∈ t, weights₀ y • y := by
        simp only [univ_eq_attach]
        simpa using (Finset.sum_attach t (fun y => weights₀ y • y))
      _ = x := hcenter
  refine ⟨(weights, points), ?_, hbary⟩
  exact ⟨⟨hweights_nonneg, hweights_sum⟩, fun j _ => hpoints j⟩

private lemma isCompact_dualConvexHull
    {S : Finset (α × β)} {p : α × β → ℝ}
    (hp : IsPMF p) (hpS : Supported S p) :
    IsCompact (convexHull ℝ (dualPhiGraph S)) := by
  have heq :
      convexHull ℝ (dualPhiGraph S) =
        dualHullBarycenter (α := α) (β := β) '' dualHullParams S :=
    Set.Subset.antisymm (dualConvexHull_subset_barycenter_image hp hpS)
      (dualHullBarycenter_image_subset S)
  rw [heq]
  exact (isCompact_dualHullParams S).image continuous_dualHullBarycenter

private lemma supported_support_self (p : α × β → ℝ) :
    Supported (support p) p := by
  intro z hz
  simpa [support] using hz

private lemma dualConvexHull_fiber_le_envelope
    {S : Finset (α × β)} {p : α × β → ℝ} (hp : IsPMF p)
    (hpS : Supported S p) {r : ℝ}
    (hr : (p, r) ∈ convexHull ℝ (dualPhiGraph S)) :
    r ≤ concaveEnvelopePhi p := by
  rcases dualConvexHull_subset_barycenter_image hp hpS hr with
    ⟨a, ha, hbary⟩
  have hpoint (i : Fin (dualHullSize (α := α) (β := β))) :
      a.2 i ∈ dualPhiGraph S :=
    ha.2 i (Set.mem_univ i)
  have hcompPMF (i : Fin (dualHullSize (α := α) (β := β))) :
      IsPMF (a.2 i).1 := by
    rcases hpoint i with ⟨q, hq, hqi⟩
    rw [← hqi]
    exact hq.1
  have hcompPhi (i : Fin (dualHullSize (α := α) (β := β))) :
      Phi (a.2 i).1 = (a.2 i).2 := by
    rcases hpoint i with ⟨q, _, hqi⟩
    rw [← hqi]
  let L : Latent p := {
    ι := Fin (dualHullSize (α := α) (β := β))
    fin := inferInstance
    dec := inferInstance
    prior := a.1
    comp := fun i => (a.2 i).1
    prior_isPMF := ⟨ha.1.1, by simpa [mass] using ha.1.2⟩
    comp_isPMF := hcompPMF
    mixture := by
      intro z
      have hfirst := congrArg Prod.fst hbary
      rw [dualHullBarycenter, Prod.fst_sum] at hfirst
      have hfirstz := congrFun hfirst z
      simpa [smul_eq_mul] using hfirstz
  }
  have hpayoff : (∑ i, L.prior i * Phi (L.comp i)) = r := by
    have hsnd := congrArg Prod.snd hbary
    rw [dualHullBarycenter, Prod.snd_sum] at hsnd
    simp only [Prod.smul_snd, smul_eq_mul] at hsnd
    calc
      (∑ i, L.prior i * Phi (L.comp i)) =
          ∑ i, a.1 i * (a.2 i).2 := by
            apply Finset.sum_congr rfl
            intro i _
            dsimp [L]
            rw [hcompPhi i]
      _ = r := hsnd
  have hbdd :
      BddAbove (Set.range fun V : Latent p =>
        ∑ i, V.prior i * Phi (V.comp i)) := by
    refine ⟨Psi p, ?_⟩
    rintro _ ⟨V, rfl⟩
    have hscore := V.score_nonneg
    rw [V.score_eq hp] at hscore
    linarith
  rw [← hpayoff]
  unfold concaveEnvelopePhi
  exact le_ciSup hbdd L

private lemma dual_envelope_point_mem_convexHull
    {p : α × β → ℝ} (hp : IsPMF p) :
    (p, concaveEnvelopePhi p) ∈
      convexHull ℝ (dualPhiGraph (support p)) := by
  obtain ⟨V, hVopt⟩ := exists_tau_optimal_latent hp
  have hpS : Supported (support p) p := supported_support_self p
  have hcompS (i : V.ι) (hi : V.prior i ≠ 0) :
      Supported (support p) (V.comp i) := by
    intro z hzS
    have hpz : p z = 0 := hpS z hzS
    have hmix := V.mixture z
    rw [hpz] at hmix
    have hzero := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => mul_nonneg (V.prior_isPMF.nonneg j)
        ((V.comp_isPMF j).nonneg z))).mp hmix i (Finset.mem_univ i)
    exact (mul_eq_zero.mp hzero).resolve_left hi
  let points : V.ι → (α × β → ℝ) × ℝ := fun i =>
    if hi : V.prior i = 0 then (p, Phi p)
    else (V.comp i, Phi (V.comp i))
  have hpoints : ∀ i, points i ∈ dualPhiGraph (support p) := by
    intro i
    by_cases hi : V.prior i = 0
    · simp [points, hi, dualPhiGraph, dualPmfSet, hp, hpS]
    · exact ⟨V.comp i, ⟨V.comp_isPMF i, hcompS i hi⟩, by simp [points, hi]⟩
  have hpayoff :
      (∑ i, V.prior i * Phi (V.comp i)) = concaveEnvelopePhi p := by
    have hscore := V.score_eq hp
    have htau := tau_eq_Psi_sub_envelope hp
    rw [hVopt, htau] at hscore
    linarith
  apply mem_convexHull_of_exists_fintype V.prior points
  · exact V.prior_isPMF.nonneg
  · simpa [mass] using V.prior_isPMF.total
  · exact hpoints
  · apply Prod.ext
    · simp only [Prod.fst_sum, Prod.smul_fst]
      funext z
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      calc
        (∑ i, V.prior i * (points i).1 z) =
            ∑ i, V.prior i * V.comp i z := by
              apply Finset.sum_congr rfl
              intro i _
              by_cases hi : V.prior i = 0
              · simp [points, hi]
              · simp [points, hi]
        _ = p z := V.mixture z
    · simp only [Prod.snd_sum, Prod.smul_snd]
      change (∑ i, V.prior i * (points i).2) = concaveEnvelopePhi p
      calc
        (∑ i, V.prior i * (points i).2) =
            ∑ i, V.prior i * Phi (V.comp i) := by
              apply Finset.sum_congr rfl
              intro i _
              by_cases hi : V.prior i = 0
              · simp [points, hi]
              · simp [points, hi]
        _ = concaveEnvelopePhi p := hpayoff

private def dualDirac (z : α × β) : α × β → ℝ :=
  fun z' => if z' = z then 1 else 0

private lemma dualDirac_isPMF (z : α × β) : IsPMF (dualDirac z) := by
  refine ⟨?_, ?_⟩
  · intro z'
    by_cases h : z' = z <;> simp [dualDirac, h]
  · simp [mass, dualDirac]

private lemma dualDirac_supported {S : Finset (α × β)} {z : α × β}
    (hz : z ∈ S) : Supported S (dualDirac z) := by
  intro z' hz'
  by_cases h : z' = z
  · exact (hz' (h.symm ▸ hz)).elim
  · simp [dualDirac, h]

private lemma Phi_dualDirac (z : α × β) : Phi (dualDirac z) = 0 := by
  simp [Phi, H, mass, mX, mY, push, dualDirac]

private lemma valid_nonneg_on {S : Finset (α × β)} {c : α × β → ℝ}
    (hc : Valid S c) {z : α × β} (hz : z ∈ S) : 0 ≤ c z := by
  have h := hc (dualDirac z) (dualDirac_isPMF z)
    (dualDirac_supported hz)
  rw [Phi_dualDirac] at h
  simpa [dualDirac, hz] using h

private lemma envelope_le_valid_objective
    {p : α × β → ℝ} (hp : IsPMF p) {c : α × β → ℝ}
    (hc : Valid (support p) c) :
    concaveEnvelopePhi p ≤ ∑ z ∈ support p, c z * p z := by
  let ell : ((α × β → ℝ) × ℝ) → ℝ := fun x =>
    x.2 - ∑ z ∈ support p, c z * x.1 z
  have hell : IsLinearMap ℝ ell := by
    refine ⟨?_, ?_⟩
    · intro x y
      dsimp [ell]
      simp only [Prod.snd_add, Prod.fst_add, Pi.add_apply,
        mul_add, Finset.sum_add_distrib]
      ring
    · intro a x
      dsimp [ell]
      rw [mul_sub]
      rw [Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro z _
      ring
  have hgraph : dualPhiGraph (support p) ⊆ {x | ell x ≤ 0} := by
    rintro _ ⟨q, hq, rfl⟩
    exact sub_nonpos.mpr (hc q hq.1 hq.2)
  have hhull : convexHull ℝ (dualPhiGraph (support p)) ⊆
      {x | ell x ≤ 0} :=
    convexHull_min hgraph (convex_halfSpace_le hell 0)
  have htop := hhull (dual_envelope_point_mem_convexHull hp)
  exact sub_nonpos.mp htop

private lemma sum_smul_dualDirac (q : α × β → ℝ) :
    (∑ z, q z • dualDirac z) = q := by
  funext z'
  simp [dualDirac]

private lemma dualFunctional_expand
    (f : StrongDual ℝ ((α × β → ℝ) × ℝ))
    (q : α × β → ℝ) (t : ℝ) :
    f (q, t) =
      (∑ z, q z * f (dualDirac z, 0)) + t * f (0, 1) := by
  have hq : q = ∑ z, q z • dualDirac z := (sum_smul_dualDirac q).symm
  calc
    f (q, t) = f ((q, 0) + (0, t)) := by simp
    _ = f (q, 0) + f (0, t) := f.map_add _ _
    _ = f (∑ z, q z • (dualDirac z, 0)) + f (t • (0, 1)) := by
      congr 2
      · ext z'
        · simp only [Prod.fst_sum, Prod.smul_fst]
          exact congrFun hq z'
        · simp only [Prod.snd_sum]
          simp
      · simp
    _ = (∑ z, q z * f (dualDirac z, 0)) + t * f (0, 1) := by
      rw [map_sum]
      simp_rw [map_smul]
      simp only [smul_eq_mul]

private lemma sum_eq_sum_of_supported {S : Finset (α × β)}
    {q : α × β → ℝ} (hqS : Supported S q) (F : α × β → ℝ) :
    (∑ z, F z * q z) = ∑ z ∈ S, F z * q z := by
  symm
  apply Finset.sum_subset (Finset.subset_univ S)
  intro z _ hzS
  simp [hqS z hzS]

private lemma exists_approx_valid_certificate
    {p : α × β → ℝ} (hp : IsPMF p) {ε : ℝ} (hε : 0 < ε) :
    ∃ c : α × β → ℝ,
      Valid (support p) c ∧
        (∑ z ∈ support p, c z * p z) = concaveEnvelopePhi p + ε := by
  let K := convexHull ℝ (dualPhiGraph (support p))
  have hpS : Supported (support p) p := supported_support_self p
  have htop : (p, concaveEnvelopePhi p) ∈ K :=
    dual_envelope_point_mem_convexHull hp
  have habove : (p, concaveEnvelopePhi p + ε) ∉ K := by
    intro hmem
    have hle := dualConvexHull_fiber_le_envelope hp hpS hmem
    linarith
  have hKcompact : IsCompact K := isCompact_dualConvexHull hp hpS
  obtain ⟨f, u, hbelow, habove'⟩ :=
    geometric_hahn_banach_closed_point (convex_convexHull ℝ _)
      hKcompact.isClosed habove
  have hvertical_lt :
      f (p, concaveEnvelopePhi p) <
        f (p, concaveEnvelopePhi p + ε) :=
    (hbelow _ htop).trans habove'
  have hb : 0 < f (0, 1) := by
    rw [dualFunctional_expand f p (concaveEnvelopePhi p),
      dualFunctional_expand f p (concaveEnvelopePhi p + ε)] at hvertical_lt
    nlinarith
  let A : ℝ := ∑ z, p z * f (dualDirac z, 0)
  let T : ℝ := concaveEnvelopePhi p + ε
  let b : ℝ := f (0, 1)
  let c : α × β → ℝ := fun z => T + (A - f (dualDirac z, 0)) / b
  have hb' : 0 < b := hb
  refine ⟨c, ?_, ?_⟩
  · intro q hq hqS
    have hgraph : (q, Phi q) ∈ K := by
      apply subset_convexHull ℝ
      exact ⟨q, ⟨hq, hqS⟩, rfl⟩
    have hsep : f (q, Phi q) < f (p, T) :=
      (hbelow _ hgraph).trans habove'
    rw [dualFunctional_expand f q (Phi q),
      dualFunctional_expand f p T] at hsep
    have hphi : Phi q < T +
        (A - ∑ z, q z * f (dualDirac z, 0)) / b := by
      rw [add_comm T, ← sub_lt_iff_lt_add, lt_div_iff₀ hb']
      dsimp [A, T, b] at hsep ⊢
      linarith
    have hqtotal : ∑ z, q z = 1 := by simpa [mass] using hq.total
    have hsum : (∑ z, c z * q z) =
        T + (A - ∑ z, q z * f (dualDirac z, 0)) / b := by
      calc
        (∑ z, c z * q z) =
            ∑ z, (T * q z +
              (A * q z - f (dualDirac z, 0) * q z) / b) := by
                apply Finset.sum_congr rfl
                intro z _
                dsimp [c]
                field_simp [ne_of_gt hb']
        _ = T * (∑ z, q z) +
            ((A * (∑ z, q z) -
              ∑ z, f (dualDirac z, 0) * q z) / b) := by
                rw [Finset.sum_add_distrib, ← Finset.sum_div,
                  Finset.sum_sub_distrib, ← Finset.mul_sum,
                  ← Finset.mul_sum]
        _ = T + (A - ∑ z, q z * f (dualDirac z, 0)) / b := by
              have hcross :
                  (∑ z, f (dualDirac z, 0) * q z) =
                    ∑ z, q z * f (dualDirac z, 0) := by
                apply Finset.sum_congr rfl
                intro z _
                ring
              rw [hqtotal, hcross]
              simp
    rw [← sum_eq_sum_of_supported hqS c, hsum]
    exact hphi.le
  · have hptotal : ∑ z, p z = 1 := by simpa [mass] using hp.total
    rw [← sum_eq_sum_of_supported hpS c]
    calc
      (∑ z, c z * p z) =
          ∑ z, (T * p z +
            (A * p z - f (dualDirac z, 0) * p z) / b) := by
              apply Finset.sum_congr rfl
              intro z _
              dsimp [c]
              field_simp [ne_of_gt hb']
      _ = T * (∑ z, p z) +
          ((A * (∑ z, p z) -
            ∑ z, f (dualDirac z, 0) * p z) / b) := by
              rw [Finset.sum_add_distrib, ← Finset.sum_div,
                Finset.sum_sub_distrib, ← Finset.mul_sum,
                ← Finset.mul_sum]
      _ = T := by
            have hA : A = ∑ z, f (dualDirac z, 0) * p z := by
              dsimp [A]
              apply Finset.sum_congr rfl
              intro z _
              ring
            rw [hptotal, mul_one, hA]
            ring
      _ = concaveEnvelopePhi p + ε := rfl

private def restrictTo (S : Finset (α × β)) (c : α × β → ℝ) :
    α × β → ℝ := fun z => if z ∈ S then c z else 0

private lemma restrictTo_valid {S : Finset (α × β)} {c : α × β → ℝ}
    (hc : Valid S c) : Valid S (restrictTo S c) := by
  intro q hq hqS
  simpa [restrictTo] using hc q hq hqS

private lemma restrictTo_supported (S : Finset (α × β)) (c : α × β → ℝ) :
    Supported S (restrictTo S c) := by
  intro z hz
  simp [restrictTo, hz]

private lemma restrictTo_objective (S : Finset (α × β))
    (c q : α × β → ℝ) :
    (∑ z ∈ S, restrictTo S c z * q z) = ∑ z ∈ S, c z * q z := by
  simp [restrictTo]

private lemma isClosed_valid (S : Finset (α × β)) :
    IsClosed {c : α × β → ℝ | Valid S c} := by
  have heq : {c : α × β → ℝ | Valid S c} =
      ⋂ q : α × β → ℝ, ⋂ (_ : IsPMF q), ⋂ (_ : Supported S q),
        {c : α × β → ℝ | Phi q ≤ ∑ z ∈ S, c z * q z} := by
    ext c
    simp [Valid]
  rw [heq]
  apply isClosed_iInter
  intro q
  apply isClosed_iInter
  intro hq
  apply isClosed_iInter
  intro hqS
  apply isClosed_le continuous_const
  fun_prop

private lemma isClosed_supported_set (S : Finset (α × β)) :
    IsClosed {c : α × β → ℝ | Supported S c} := by
  have heq : {c : α × β → ℝ | Supported S c} =
      ⋂ z ∈ (Finset.univ.filter fun z : α × β => z ∉ S),
        {c : α × β → ℝ | c z = 0} := by
    ext c
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor
    · intro h z hz
      exact h z hz
    · intro h z hz
      exact h z hz
  rw [heq]
  exact isClosed_biInter fun z _ =>
    isClosed_eq (continuous_apply z) continuous_const

private def certificateSlice (p : α × β → ℝ) (T : ℝ) :
    Set (α × β → ℝ) :=
  {c | Valid (support p) c} ∩ {c | Supported (support p) c} ∩
    {c | (∑ z ∈ support p, c z * p z) ≤ T}

private lemma isClosed_certificateSlice (p : α × β → ℝ) (T : ℝ) :
    IsClosed (certificateSlice p T) := by
  unfold certificateSlice
  apply IsClosed.inter
  · exact IsClosed.inter (isClosed_valid (support p))
      (isClosed_supported_set (support p))
  · apply isClosed_le
    · fun_prop
    · exact continuous_const

private lemma certificateSlice_nonempty {p : α × β → ℝ} (hp : IsPMF p) :
    (certificateSlice p (concaveEnvelopePhi p + 1)).Nonempty := by
  obtain ⟨c₀, hc₀, hobj₀⟩ :=
    exists_approx_valid_certificate hp (ε := 1) zero_lt_one
  refine ⟨restrictTo (support p) c₀, ?_⟩
  refine ⟨⟨restrictTo_valid hc₀,
    restrictTo_supported (support p) c₀⟩, ?_⟩
  change (∑ z ∈ support p, restrictTo (support p) c₀ z * p z) ≤
    concaveEnvelopePhi p + 1
  rw [restrictTo_objective, hobj₀]

private lemma isCompact_certificateSlice {p : α × β → ℝ} (hp : IsPMF p) :
    IsCompact (certificateSlice p (concaveEnvelopePhi p + 1)) := by
  let upper : α × β → ℝ := fun z =>
    if z ∈ support p then (concaveEnvelopePhi p + 1) / p z else 0
  apply (isCompact_Icc (a := (0 : α × β → ℝ)) (b := upper)).of_isClosed_subset
    (isClosed_certificateSlice p (concaveEnvelopePhi p + 1))
  intro c hc
  rcases hc with ⟨⟨hcValid, hcSupported⟩, hcObj⟩
  refine ⟨?_, ?_⟩
  · intro z
    change (0 : ℝ) ≤ c z
    by_cases hz : z ∈ support p
    · exact valid_nonneg_on hcValid hz
    · rw [hcSupported z hz]
  · intro z
    by_cases hz : z ∈ support p
    · have hpzne : p z ≠ 0 := by
        simpa [support] using hz
      have hpz : 0 < p z :=
        lt_of_le_of_ne (hp.nonneg z) (Ne.symm hpzne)
      have hterm : c z * p z ≤
          ∑ z' ∈ support p, c z' * p z' := by
        exact Finset.single_le_sum
          (s := support p) (f := fun z' => c z' * p z')
          (fun z' hz' => mul_nonneg (valid_nonneg_on hcValid hz')
            (hp.nonneg z')) hz
      have hle : c z * p z ≤ concaveEnvelopePhi p + 1 :=
        hterm.trans hcObj
      simpa [upper, hz] using (le_div_iff₀ hpz).2 hle
    · simp [upper, hz, hcSupported z hz]

private lemma exists_optimal_valid_certificate
    {p : α × β → ℝ} (hp : IsPMF p) :
    ∃ c : α × β → ℝ,
      Valid (support p) c ∧
        (∑ z ∈ support p, c z * p z) = concaveEnvelopePhi p := by
  let obj : (α × β → ℝ) → ℝ := fun c =>
    ∑ z ∈ support p, c z * p z
  have hobj : Continuous obj := by
    dsimp [obj]
    fun_prop
  obtain ⟨c, hc, hmin⟩ :=
    (isCompact_certificateSlice hp).exists_isMinOn
      (certificateSlice_nonempty hp) hobj.continuousOn
  rcases hc with ⟨⟨hcValid, hcSupported⟩, hcBound⟩
  have hlower : concaveEnvelopePhi p ≤ obj c := by
    exact envelope_le_valid_objective hp hcValid
  have hupper : obj c ≤ concaveEnvelopePhi p := by
    by_contra hnot
    have hlt : concaveEnvelopePhi p < obj c := lt_of_not_ge hnot
    let ε : ℝ := (obj c - concaveEnvelopePhi p) / 2
    have hε : 0 < ε := by
      dsimp [ε]
      linarith
    have hεone : ε ≤ 1 := by
      dsimp [ε]
      dsimp [obj] at hcBound ⊢
      linarith
    obtain ⟨c₀, hc₀, hobj₀⟩ := exists_approx_valid_certificate hp hε
    let d := restrictTo (support p) c₀
    have hd : d ∈ certificateSlice p (concaveEnvelopePhi p + 1) := by
      refine ⟨⟨restrictTo_valid hc₀,
        restrictTo_supported (support p) c₀⟩, ?_⟩
      change (∑ z ∈ support p, d z * p z) ≤
        concaveEnvelopePhi p + 1
      rw [show (∑ z ∈ support p, d z * p z) =
          ∑ z ∈ support p, c₀ z * p z by
        exact restrictTo_objective (support p) c₀ p,
        hobj₀]
      linarith
    have hmin' := hmin hd
    change obj c ≤ obj d at hmin'
    have hdobj : obj d = concaveEnvelopePhi p + ε := by
      dsimp [obj, d]
      rw [restrictTo_objective, hobj₀]
    rw [hdobj] at hmin'
    dsimp [ε] at hmin'
    linarith
  refine ⟨c, hcValid, ?_⟩
  change obj c = concaveEnvelopePhi p
  exact le_antisymm hupper hlower

private lemma neg_three_lg_two_rpow (r : ℝ) :
    -3 * lg ((2 : ℝ) ^ (-r / 3)) = r := by
  rw [lg_eq_log_div, Real.log_rpow (by norm_num : (0 : ℝ) < 2)]
  field_simp [Real.log_ne_zero_of_pos_of_ne_one
    (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1)]

/-- **Corollary 2.4**: `τ` as an attained convex program over
feasible kernels. -/
theorem exists_tau_optimal_kernel {p : α × β → ℝ} (hp : IsPMF p) :
    ∃ w : α × β → ℝ, Feasible (support p) w ∧
      tau p = Psi p + 3 * ∑ z ∈ support p, p z * lg (w z) := by
  obtain ⟨c, hcValid, hcObj⟩ := exists_optimal_valid_certificate hp
  let w : α × β → ℝ := fun z => (2 : ℝ) ^ (-c z / 3)
  have hwpos : ∀ z ∈ support p, 0 < w z := by
    intro z _
    exact Real.rpow_pos_of_pos (by norm_num) _
  have hcert : (fun z => -3 * lg (w z)) = c := by
    funext z
    exact neg_three_lg_two_rpow (c z)
  have hw : Feasible (support p) w := by
    apply (valid_iff_feasible hwpos).mp
    rw [hcert]
    exact hcValid
  refine ⟨w, hw, ?_⟩
  have hsum :
      3 * (∑ z ∈ support p, p z * lg (w z)) =
        -(∑ z ∈ support p, c z * p z) := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro z _
    rw [← congrFun hcert z]
    ring
  rw [tau_eq_Psi_sub_envelope hp, ← hcObj, hsum]
  ring

/-- **Theorem 2.5** (*contact-opt*). The existence of an
**attained τ(p)-optimal common-contact pair** `(L, w)`: a latent achieving `τ`
all of whose components are contacts of one feasible kernel.

This is the hypothesis §§4-12 run on; `SeedSetup` in `stoch_to_det.Seed` packages it. -/
theorem exists_common_contact_pair {p : α × β → ℝ} (hp : IsPMF p) :
    ∃ (L : Latent p) (w : α × β → ℝ),
      Feasible (support p) w ∧ L.score = tau p ∧
      ∀ v, L.prior v ≠ 0 → IsContact (support p) w (L.comp v) := by
  obtain ⟨L, hLopt⟩ := exists_tau_optimal_latent hp
  obtain ⟨w, hw, hwopt⟩ := exists_tau_optimal_kernel hp
  have hpS : Supported (support p) p := supported_support_self p
  have hcompS (v : L.ι) (hv : L.prior v ≠ 0) :
      Supported (support p) (L.comp v) := by
    intro z hzS
    have hpz : p z = 0 := hpS z hzS
    have hmix := L.mixture z
    rw [hpz] at hmix
    have hzero := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => mul_nonneg (L.prior_isPMF.nonneg j)
        ((L.comp_isPMF j).nonneg z))).mp hmix v (Finset.mem_univ v)
    exact (mul_eq_zero.mp hzero).resolve_left hv
  let c : α × β → ℝ := fun z => -3 * lg (w z)
  have hcertsum :
      (∑ z ∈ support p, c z * p z) =
        -3 * ∑ z ∈ support p, p z * lg (w z) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro z _
    dsimp [c]
    ring
  have hcompGap :
      (∑ v, L.prior v * Gdef (support p) w (L.comp v)) =
        ∑ v, L.prior v *
          ((∑ z ∈ support p, c z * L.comp v z) - Phi (L.comp v)) := by
    apply Finset.sum_congr rfl
    intro v _
    by_cases hv : L.prior v = 0
    · simp [hv]
    · rw [Gdef_eq_certificate_gap hw.1 (L.comp_isPMF v) (hcompS v hv)]
  have hkernel :
      (∑ v, L.prior v * (∑ z ∈ support p, c z * L.comp v z)) =
        ∑ z ∈ support p, c z * p z := by
    calc
      (∑ v, L.prior v * (∑ z ∈ support p, c z * L.comp v z)) =
          ∑ v, ∑ z ∈ support p, c z * (L.prior v * L.comp v z) := by
            apply Finset.sum_congr rfl
            intro v _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro z _
            ring
      _ = ∑ z ∈ support p, ∑ v, c z * (L.prior v * L.comp v z) := by
        rw [Finset.sum_comm]
      _ = ∑ z ∈ support p, c z * p z := by
        apply Finset.sum_congr rfl
        intro z _
        rw [← Finset.mul_sum, L.mixture]
  have hsumGap :
      (∑ v, L.prior v * Gdef (support p) w (L.comp v)) =
        (∑ z ∈ support p, c z * p z) -
          ∑ v, L.prior v * Phi (L.comp v) := by
    rw [hcompGap]
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, hkernel]
  have hscoreIdentity := Latent.score_eq hp L
  have hsumZero :
      (∑ v, L.prior v * Gdef (support p) w (L.comp v)) = 0 := by
    rw [hLopt] at hscoreIdentity
    rw [hsumGap]
    linarith [hcertsum, hwopt]
  have htermNonneg (v : L.ι) :
      0 ≤ L.prior v * Gdef (support p) w (L.comp v) := by
    by_cases hv : L.prior v = 0
    · simp [hv]
    · exact mul_nonneg (L.prior_isPMF.nonneg v)
        (Gdef_nonneg hw (L.comp_isPMF v) (hcompS v hv))
  refine ⟨L, w, hw, hLopt, ?_⟩
  intro v hv
  have htermZero :
      L.prior v * Gdef (support p) w (L.comp v) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => htermNonneg j)).mp hsumZero v (Finset.mem_univ v)
  have hGzero : Gdef (support p) w (L.comp v) = 0 :=
    (mul_eq_zero.mp htermZero).resolve_left hv
  exact (Gdef_eq_zero_iff hw (L.comp_isPMF v) (hcompS v hv)).mp hGzero

/-! ### Lemmas 2.6-2.8 -/

/-- **Lemma 2.6**: on a connected support every contact has
full support. Used from §3 on; it is what makes the near/far dichotomy of
Theorem 9.1 total. -/
theorem contact_support_eq {S : Finset (α × β)} {w : α × β → ℝ} (hw : Feasible S w)
    (hS : IsConnected S) {q : α × β → ℝ} (hq : IsContact S w q) :
    support q = S := by
  let u : α → ℝ := mX q
  let v : β → ℝ := mY q
  have hu : IsPMF u := isPMF_push hq.1
  have hv : IsPMF v := isPMF_push hq.1
  have hLambda : Lambda S w u v = 1 := by
    calc
      Lambda S w u v = ∑ z ∈ S, q z := by
        unfold Lambda
        apply Finset.sum_congr rfl
        intro z hzS
        rw [hq.2.2 z hzS]
      _ = ∑ z, q z := by
        apply Finset.sum_subset (Finset.subset_univ S)
        intro z _ hzS
        exact hq.2.1 z hzS
      _ = 1 := by simpa [mass] using hq.1.total
  let R : α → ℝ := fun x =>
    ∑ z ∈ S.filter (fun z => z.1 = x), w z * v z.2 ^ ((2 : ℝ) / 3)
  have hR : ∀ x, 0 ≤ R x := by
    intro x
    dsimp [R]
    exact Finset.sum_nonneg fun z hz =>
      mul_nonneg (hw.1 z (Finset.mem_filter.mp hz).1).le
        (Real.rpow_nonneg (hv.nonneg z.2) _)
  have hLambdaRow (s : α → ℝ) :
      Lambda S w s v = ∑ x, R x * s x ^ ((2 : ℝ) / 3) := by
    unfold Lambda
    rw [← Finset.sum_fiberwise S Prod.fst
      (fun z => w z * s z.1 ^ ((2 : ℝ) / 3) * v z.2 ^ ((2 : ℝ) / 3))]
    apply Finset.sum_congr rfl
    intro x _
    dsimp [R]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro z hz
    rw [(Finset.mem_filter.mp hz).2]
    ring
  have huMax : ∀ t : α → ℝ, IsPMF t →
      (∑ x, R x * t x ^ ((2 : ℝ) / 3)) ≤
        ∑ x, R x * u x ^ ((2 : ℝ) / 3) := by
    intro t ht
    rw [← hLambdaRow, ← hLambdaRow, hLambda]
    exact hw.2 t v ht hv
  have hRzero : ∀ x, R x = 0 ↔ u x = 0 := by
    apply (maximizer_rpow_two_thirds hR hu huMax).2
    rw [← hLambdaRow, hLambda]
    norm_num
  let Q : β → ℝ := fun y =>
    ∑ z ∈ S.filter (fun z => z.2 = y), w z * u z.1 ^ ((2 : ℝ) / 3)
  have hQ : ∀ y, 0 ≤ Q y := by
    intro y
    dsimp [Q]
    exact Finset.sum_nonneg fun z hz =>
      mul_nonneg (hw.1 z (Finset.mem_filter.mp hz).1).le
        (Real.rpow_nonneg (hu.nonneg z.1) _)
  have hLambdaCol (s : β → ℝ) :
      Lambda S w u s = ∑ y, Q y * s y ^ ((2 : ℝ) / 3) := by
    unfold Lambda
    rw [← Finset.sum_fiberwise S Prod.snd
      (fun z => w z * u z.1 ^ ((2 : ℝ) / 3) * s z.2 ^ ((2 : ℝ) / 3))]
    apply Finset.sum_congr rfl
    intro y _
    dsimp [Q]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro z hz
    rw [(Finset.mem_filter.mp hz).2]
  have hvMax : ∀ t : β → ℝ, IsPMF t →
      (∑ y, Q y * t y ^ ((2 : ℝ) / 3)) ≤
        ∑ y, Q y * v y ^ ((2 : ℝ) / 3) := by
    intro t ht
    rw [← hLambdaCol, ← hLambdaCol, hLambda]
    exact hw.2 u t hu ht
  have hQzero : ∀ y, Q y = 0 ↔ v y = 0 := by
    apply (maximizer_rpow_two_thirds hQ hv hvMax).2
    rw [← hLambdaCol, hLambda]
    norm_num
  have hmargX (z : α × β) : q z ≤ u z.1 := by
    change q z ≤ push Prod.fst q z.1
    unfold push
    exact Finset.single_le_sum (fun a _ ↦ hq.1.nonneg a) (by simp)
  have hmargY (z : α × β) : q z ≤ v z.2 := by
    change q z ≤ push Prod.snd q z.2
    unfold push
    exact Finset.single_le_sum (fun a _ ↦ hq.1.nonneg a) (by simp)
  have hpropagate {z z' : α × β} (hzS : z ∈ S) (hz'S : z' ∈ S)
      (hzz' : Adj z z') (hzpos : 0 < q z) : 0 < q z' := by
    have hupos : 0 < u z.1 := hzpos.trans_le (hmargX z)
    have hvpos : 0 < v z.2 := hzpos.trans_le (hmargY z)
    rcases hzz' with hrow | hcol
    · have huz' : 0 < u z'.1 := by simpa [hrow] using hupos
      have hterm :
          0 < w z' * u z'.1 ^ ((2 : ℝ) / 3) :=
        mul_pos (hw.1 z' hz'S) (Real.rpow_pos_of_pos huz' _)
      have hterm_le :
          w z' * u z'.1 ^ ((2 : ℝ) / 3) ≤ Q z'.2 := by
        dsimp [Q]
        exact Finset.single_le_sum
          (fun a ha => mul_nonneg (hw.1 a (Finset.mem_filter.mp ha).1).le
            (Real.rpow_nonneg (hu.nonneg a.1) _))
          (Finset.mem_filter.mpr ⟨hz'S, rfl⟩)
      have hQpos : 0 < Q z'.2 := hterm.trans_le hterm_le
      have hvz' : 0 < v z'.2 := by
        have hvne : v z'.2 ≠ 0 := by
          intro hvzero
          exact hQpos.ne' ((hQzero z'.2).2 hvzero)
        exact lt_of_le_of_ne (hv.nonneg z'.2) (Ne.symm hvne)
      rw [hq.2.2 z' hz'S]
      exact mul_pos (mul_pos (hw.1 z' hz'S)
        (Real.rpow_pos_of_pos huz' _)) (Real.rpow_pos_of_pos hvz' _)
    · have hvz' : 0 < v z'.2 := by simpa [hcol] using hvpos
      have hterm :
          0 < w z' * v z'.2 ^ ((2 : ℝ) / 3) :=
        mul_pos (hw.1 z' hz'S) (Real.rpow_pos_of_pos hvz' _)
      have hterm_le :
          w z' * v z'.2 ^ ((2 : ℝ) / 3) ≤ R z'.1 := by
        dsimp [R]
        exact Finset.single_le_sum
          (fun a ha => mul_nonneg (hw.1 a (Finset.mem_filter.mp ha).1).le
            (Real.rpow_nonneg (hv.nonneg a.2) _))
          (Finset.mem_filter.mpr ⟨hz'S, rfl⟩)
      have hRpos : 0 < R z'.1 := hterm.trans_le hterm_le
      have huz' : 0 < u z'.1 := by
        have hune : u z'.1 ≠ 0 := by
          intro huzero
          exact hRpos.ne' ((hRzero z'.1).2 huzero)
        exact lt_of_le_of_ne (hu.nonneg z'.1) (Ne.symm hune)
      rw [hq.2.2 z' hz'S]
      exact mul_pos (mul_pos (hw.1 z' hz'S)
        (Real.rpow_pos_of_pos huz' _)) (Real.rpow_pos_of_pos hvz' _)
  obtain ⟨z₀, _, hz₀pos⟩ :
      ∃ z ∈ (Finset.univ : Finset (α × β)), 0 < q z := by
    apply (Finset.sum_pos_iff_of_nonneg
      (fun z _ => hq.1.nonneg z)).mp
    have hsum : ∑ z, q z = 1 := by simpa [mass] using hq.1.total
    rw [hsum]
    norm_num
  have hz₀S : z₀ ∈ S := by
    by_contra hz₀S
    have := hq.2.1 z₀ hz₀S
    linarith
  have hall : ∀ z ∈ S, 0 < q z := by
    intro z hzS
    have hpath := hS z₀ hz₀S z hzS
    induction hpath with
    | refl => exact hz₀pos
    | tail hpath hstep ih =>
        exact hpropagate hstep.1 hstep.2.1 hstep.2.2 (ih hstep.1)
  apply Finset.ext
  intro z
  simp only [support, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hz
    by_contra hzS
    exact hz (hq.2.1 z hzS)
  · intro hzS
    exact (hall z hzS).ne'

/-- **Lemma 2.7** (hypercontractivity of contacts):
`E_q[f(X) g(Y)] ≤ ‖f‖_{L^{3/2}(q_X)} ‖g‖_{L^{3/2}(q_Y)}` for `f, g ≥ 0`.

A frequently reused inequality (§5.2, §6.1, §6.2), proved by applying
`Feasible` to the tilted marginals. -/
theorem contact_hypercontractive {S : Finset (α × β)} {w : α × β → ℝ} (hw : Feasible S w)
    {q : α × β → ℝ} (hq : IsContact S w q) {f : α → ℝ} {g : β → ℝ}
    (hf : ∀ x, 0 ≤ f x) (hg : ∀ y, 0 ≤ g y) :
    (∑ z ∈ S, q z * f z.1 * g z.2)
      ≤ (∑ x, mX q x * f x ^ ((3 : ℝ) / 2)) ^ ((2 : ℝ) / 3)
        * (∑ y, mY q y * g y ^ ((3 : ℝ) / 2)) ^ ((2 : ℝ) / 3) := by
  let A : ℝ := ∑ x, mX q x * f x ^ ((3 : ℝ) / 2)
  let B : ℝ := ∑ y, mY q y * g y ^ ((3 : ℝ) / 2)
  change (∑ z ∈ S, q z * f z.1 * g z.2) ≤
    A ^ ((2 : ℝ) / 3) * B ^ ((2 : ℝ) / 3)
  have hqX : IsPMF (mX q) := isPMF_push hq.1
  have hqY : IsPMF (mY q) := isPMF_push hq.1
  have hA : 0 ≤ A := by
    dsimp [A]
    exact Finset.sum_nonneg fun x _ =>
      mul_nonneg (hqX.nonneg x) (Real.rpow_nonneg (hf x) _)
  have hB : 0 ≤ B := by
    dsimp [B]
    exact Finset.sum_nonneg fun y _ =>
      mul_nonneg (hqY.nonneg y) (Real.rpow_nonneg (hg y) _)
  by_cases hAz : A = 0
  · have hAterm :
        ∀ x, mX q x * f x ^ ((3 : ℝ) / 2) = 0 := by
      intro x
      apply (Finset.sum_eq_zero_iff_of_nonneg
        (fun a _ => mul_nonneg (hqX.nonneg a) (Real.rpow_nonneg (hf a) _))).mp
      · exact hAz
      · exact Finset.mem_univ x
    have hleft :
        (∑ z ∈ S, q z * f z.1 * g z.2) = 0 := by
      apply Finset.sum_eq_zero
      intro z _
      by_cases hz : q z = 0
      · simp [hz]
      · have hzpos : 0 < q z :=
          lt_of_le_of_ne (hq.1.nonneg z) (Ne.symm hz)
        have hxle : q z ≤ mX q z.1 := by
          change q z ≤ push Prod.fst q z.1
          unfold push
          exact Finset.single_le_sum (fun a _ ↦ hq.1.nonneg a) (by simp)
        have hfpow : f z.1 ^ ((3 : ℝ) / 2) = 0 :=
          (mul_eq_zero.mp (hAterm z.1)).resolve_left (hzpos.trans_le hxle).ne'
        have hfzero : f z.1 = 0 :=
          (Real.rpow_eq_zero (hf z.1) (by norm_num)).mp hfpow
        simp [hfzero]
    rw [hleft, hAz]
    positivity
  · by_cases hBz : B = 0
    · have hBterm :
          ∀ y, mY q y * g y ^ ((3 : ℝ) / 2) = 0 := by
        intro y
        apply (Finset.sum_eq_zero_iff_of_nonneg
          (fun b _ => mul_nonneg (hqY.nonneg b) (Real.rpow_nonneg (hg b) _))).mp
        · exact hBz
        · exact Finset.mem_univ y
      have hleft :
          (∑ z ∈ S, q z * f z.1 * g z.2) = 0 := by
        apply Finset.sum_eq_zero
        intro z _
        by_cases hz : q z = 0
        · simp [hz]
        · have hzpos : 0 < q z :=
            lt_of_le_of_ne (hq.1.nonneg z) (Ne.symm hz)
          have hyle : q z ≤ mY q z.2 := by
            change q z ≤ push Prod.snd q z.2
            unfold push
            exact Finset.single_le_sum (fun a _ ↦ hq.1.nonneg a) (by simp)
          have hgpow : g z.2 ^ ((3 : ℝ) / 2) = 0 :=
            (mul_eq_zero.mp (hBterm z.2)).resolve_left (hzpos.trans_le hyle).ne'
          have hgzero : g z.2 = 0 :=
            (Real.rpow_eq_zero (hg z.2) (by norm_num)).mp hgpow
          simp [hgzero]
      rw [hleft, hBz]
      positivity
    · have hApos : 0 < A := lt_of_le_of_ne hA (Ne.symm hAz)
      have hBpos : 0 < B := lt_of_le_of_ne hB (Ne.symm hBz)
      let u : α → ℝ := fun x => (mX q x * f x ^ ((3 : ℝ) / 2)) / A
      let v : β → ℝ := fun y => (mY q y * g y ^ ((3 : ℝ) / 2)) / B
      have hu : IsPMF u := by
        constructor
        · intro x
          exact div_nonneg
            (mul_nonneg (hqX.nonneg x) (Real.rpow_nonneg (hf x) _)) hA
        · unfold mass
          dsimp [u]
          rw [← Finset.sum_div]
          change A / A = 1
          exact div_self hAz
      have hv : IsPMF v := by
        constructor
        · intro y
          exact div_nonneg
            (mul_nonneg (hqY.nonneg y) (Real.rpow_nonneg (hg y) _)) hB
        · unfold mass
          dsimp [v]
          rw [← Finset.sum_div]
          change B / B = 1
          exact div_self hBz
      have hfpow (x : α) :
          (f x ^ ((3 : ℝ) / 2)) ^ ((2 : ℝ) / 3) = f x := by
        rw [← Real.rpow_mul (hf x)]
        norm_num
      have hgpow (y : β) :
          (g y ^ ((3 : ℝ) / 2)) ^ ((2 : ℝ) / 3) = g y := by
        rw [← Real.rpow_mul (hg y)]
        norm_num
      have hLambda :
          Lambda S w u v =
            (∑ z ∈ S, q z * f z.1 * g z.2) /
              (A ^ ((2 : ℝ) / 3) * B ^ ((2 : ℝ) / 3)) := by
        unfold Lambda
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro z hzS
        dsimp [u, v]
        rw [Real.div_rpow
              (mul_nonneg (hqX.nonneg z.1) (Real.rpow_nonneg (hf z.1) _)) hA,
          Real.div_rpow
              (mul_nonneg (hqY.nonneg z.2) (Real.rpow_nonneg (hg z.2) _)) hB,
          Real.mul_rpow (hqX.nonneg z.1) (Real.rpow_nonneg (hf z.1) _),
          Real.mul_rpow (hqY.nonneg z.2) (Real.rpow_nonneg (hg z.2) _),
          hfpow, hgpow, hq.2.2 z hzS]
        ring
      have hfeas := hw.2 u v hu hv
      rw [hLambda] at hfeas
      exact (div_le_one
        (mul_pos (Real.rpow_pos_of_pos hApos _) (Real.rpow_pos_of_pos hBpos _))).mp hfeas

/-- **Lemma 2.7′** (interpolated contact hypercontractivity):
`E_q[F(X) G(Y)] ≤ ‖F‖_{L^{4/3}(q_X)} ‖G‖_{L²(q_Y)}` for `F, G ≥ 0`.

Dually this is `‖T‖_{L²(q_Y) → L⁴(q_X)} ≤ 1`, the Riesz–Thorin midpoint between
Lemma 2.7 (the `(3/2, 3/2)` pair) and the trivial `‖T‖_{∞→∞} ≤ 1`. It is reached
here by one Hölder split at the conjugate pair `(4/3, 4)` instead, so no
interpolation theory is needed: `(3/4)·(8/9) + (1/4)·(4/3) = 1` is the unique
such split, and Lemma 2.7 applied to `(F^{8/9}, G^{4/3})` has exactly
`(∑ q_X F^{4/3})^{2/3} (∑ q_Y G²)^{2/3}` on the right, since `(8/9)(3/2) = 4/3`
and `(4/3)(3/2) = 2`.

This is what lets `singular_f_moment_four_le` close where the `(3/2,3/2)` pair
closes only at the third moment. -/
theorem contact_hypercontractive_two_four {S : Finset (α × β)} {w : α × β → ℝ}
    (hw : Feasible S w) {q : α × β → ℝ} (hq : IsContact S w q) {F : α → ℝ} {G : β → ℝ}
    (hF : ∀ x, 0 ≤ F x) (hG : ∀ y, 0 ≤ G y) :
    (∑ z ∈ S, q z * F z.1 * G z.2)
      ≤ (∑ x, mX q x * F x ^ ((4 : ℝ) / 3)) ^ ((3 : ℝ) / 4)
        * (∑ y, mY q y * G y ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) := by
  have hqnn := hq.1.nonneg
  have hqX : IsPMF (mX q) := isPMF_push hq.1
  have hqY : IsPMF (mY q) := isPMF_push hq.1
  set R : ℝ := ∑ x, mX q x * F x ^ ((4 : ℝ) / 3) with hRdef
  set T : ℝ := ∑ y, mY q y * G y ^ (2 : ℝ) with hTdef
  set P : ℝ := ∑ z ∈ S, q z * F z.1 ^ ((8 : ℝ) / 9) * G z.2 ^ ((4 : ℝ) / 3) with hPdef
  have hRnn : 0 ≤ R := Finset.sum_nonneg fun x _ =>
    mul_nonneg (hqX.nonneg x) (Real.rpow_nonneg (hF x) _)
  have hTnn : 0 ≤ T := Finset.sum_nonneg fun y _ =>
    mul_nonneg (hqY.nonneg y) (Real.rpow_nonneg (hG y) _)
  have hPnn : 0 ≤ P := Finset.sum_nonneg fun z _ =>
    mul_nonneg (mul_nonneg (hqnn z) (Real.rpow_nonneg (hF z.1) _))
      (Real.rpow_nonneg (hG z.2) _)
  -- The tail factor of the Hölder split is `R` itself.
  have hRsupp : (∑ z ∈ S, q z * F z.1 ^ ((4 : ℝ) / 3)) = R := by
    have hfull : (∑ z, q z * F z.1 ^ ((4 : ℝ) / 3))
        = ∑ z ∈ S, q z * F z.1 ^ ((4 : ℝ) / 3) := by
      symm
      apply Finset.sum_subset (Finset.subset_univ S)
      intro z _ hz
      simp [hq.2.1 z hz]
    rw [← hfull, hRdef]
    exact (sum_push_mul Prod.fst q fun x => F x ^ ((4 : ℝ) / 3)).symm
  -- Step 1: Hölder at the conjugate pair `(4/3, 4)`.
  have hholder : (∑ z ∈ S, q z * F z.1 * G z.2) ≤ P ^ ((3 : ℝ) / 4) * R ^ ((1 : ℝ) / 4) := by
    have hpq : Real.HolderConjugate ((4 : ℝ) / 3) 4 :=
      Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
    have h := Real.inner_le_Lp_mul_Lq S
      (fun z : α × β => q z ^ ((3 : ℝ) / 4) * F z.1 ^ ((2 : ℝ) / 3) * G z.2)
      (fun z : α × β => q z ^ ((1 : ℝ) / 4) * F z.1 ^ ((1 : ℝ) / 3)) hpq
    have hprod : ∀ z : α × β,
        (q z ^ ((3 : ℝ) / 4) * F z.1 ^ ((2 : ℝ) / 3) * G z.2)
          * (q z ^ ((1 : ℝ) / 4) * F z.1 ^ ((1 : ℝ) / 3)) = q z * F z.1 * G z.2 := by
      intro z
      have hq' : q z ^ ((3 : ℝ) / 4) * q z ^ ((1 : ℝ) / 4) = q z := by
        rw [← Real.rpow_add' (hqnn z) (by norm_num)]
        norm_num
      have hF' : F z.1 ^ ((2 : ℝ) / 3) * F z.1 ^ ((1 : ℝ) / 3) = F z.1 := by
        rw [← Real.rpow_add' (hF z.1) (by norm_num)]
        norm_num
      calc (q z ^ ((3 : ℝ) / 4) * F z.1 ^ ((2 : ℝ) / 3) * G z.2)
            * (q z ^ ((1 : ℝ) / 4) * F z.1 ^ ((1 : ℝ) / 3))
          = (q z ^ ((3 : ℝ) / 4) * q z ^ ((1 : ℝ) / 4))
              * (F z.1 ^ ((2 : ℝ) / 3) * F z.1 ^ ((1 : ℝ) / 3)) * G z.2 := by ring
        _ = q z * F z.1 * G z.2 := by rw [hq', hF']
    have hleft : ∀ z : α × β,
        |q z ^ ((3 : ℝ) / 4) * F z.1 ^ ((2 : ℝ) / 3) * G z.2| ^ ((4 : ℝ) / 3)
          = q z * F z.1 ^ ((8 : ℝ) / 9) * G z.2 ^ ((4 : ℝ) / 3) := by
      intro z
      rw [abs_of_nonneg (mul_nonneg (mul_nonneg (Real.rpow_nonneg (hqnn z) _)
        (Real.rpow_nonneg (hF z.1) _)) (hG z.2)),
        Real.mul_rpow (mul_nonneg (Real.rpow_nonneg (hqnn z) _)
          (Real.rpow_nonneg (hF z.1) _)) (hG z.2),
        Real.mul_rpow (Real.rpow_nonneg (hqnn z) _) (Real.rpow_nonneg (hF z.1) _),
        ← Real.rpow_mul (hqnn z), ← Real.rpow_mul (hF z.1)]
      norm_num
    have hright : ∀ z : α × β,
        |q z ^ ((1 : ℝ) / 4) * F z.1 ^ ((1 : ℝ) / 3)| ^ (4 : ℝ)
          = q z * F z.1 ^ ((4 : ℝ) / 3) := by
      intro z
      rw [abs_of_nonneg (mul_nonneg (Real.rpow_nonneg (hqnn z) _)
        (Real.rpow_nonneg (hF z.1) _)),
        Real.mul_rpow (Real.rpow_nonneg (hqnn z) _) (Real.rpow_nonneg (hF z.1) _),
        ← Real.rpow_mul (hqnn z), ← Real.rpow_mul (hF z.1)]
      norm_num
    simp only [hprod, hleft, hright] at h
    calc (∑ z ∈ S, q z * F z.1 * G z.2)
        ≤ P ^ (1 / ((4 : ℝ) / 3)) * R ^ (1 / (4 : ℝ)) := by
          rw [← hRsupp]; simpa [hPdef, hRsupp] using h
      _ = P ^ ((3 : ℝ) / 4) * R ^ ((1 : ℝ) / 4) := by norm_num
  -- Step 2: Lemma 2.7 on the tilted pair `(F^{8/9}, G^{4/3})`.
  have hP : P ≤ R ^ ((2 : ℝ) / 3) * T ^ ((2 : ℝ) / 3) := by
    have h := contact_hypercontractive hw hq
      (f := fun x => F x ^ ((8 : ℝ) / 9)) (g := fun y => G y ^ ((4 : ℝ) / 3))
      (fun x => Real.rpow_nonneg (hF x) _) (fun y => Real.rpow_nonneg (hG y) _)
    have hFpow : ∀ x, (F x ^ ((8 : ℝ) / 9)) ^ ((3 : ℝ) / 2) = F x ^ ((4 : ℝ) / 3) := by
      intro x; rw [← Real.rpow_mul (hF x)]; norm_num
    have hGpow : ∀ y, (G y ^ ((4 : ℝ) / 3)) ^ ((3 : ℝ) / 2) = G y ^ (2 : ℝ) := by
      intro y; rw [← Real.rpow_mul (hG y)]; norm_num
    simp only [hFpow, hGpow] at h
    exact h
  -- Step 3: combine, using `R^{1/2} · T^{1/2} · R^{1/4} = R^{3/4} · T^{1/2}`.
  refine hholder.trans ?_
  have hmono : P ^ ((3 : ℝ) / 4) ≤ R ^ ((1 : ℝ) / 2) * T ^ ((1 : ℝ) / 2) := by
    have h := Real.rpow_le_rpow hPnn hP (by norm_num : (0 : ℝ) ≤ 3 / 4)
    rwa [Real.mul_rpow (Real.rpow_nonneg hRnn _) (Real.rpow_nonneg hTnn _),
      ← Real.rpow_mul hRnn, ← Real.rpow_mul hTnn,
      show (2 : ℝ) / 3 * ((3 : ℝ) / 4) = 1 / 2 by norm_num] at h
  calc P ^ ((3 : ℝ) / 4) * R ^ ((1 : ℝ) / 4)
      ≤ (R ^ ((1 : ℝ) / 2) * T ^ ((1 : ℝ) / 2)) * R ^ ((1 : ℝ) / 4) := by
        gcongr
    _ = R ^ ((3 : ℝ) / 4) * T ^ ((1 : ℝ) / 2) := by
        rw [show R ^ ((1 : ℝ) / 2) * T ^ ((1 : ℝ) / 2) * R ^ ((1 : ℝ) / 4)
              = R ^ ((1 : ℝ) / 2) * R ^ ((1 : ℝ) / 4) * T ^ ((1 : ℝ) / 2) by ring,
          ← Real.rpow_add' hRnn (by norm_num : (1 : ℝ) / 2 + 1 / 4 ≠ 0)]
        norm_num

/-- **Lemma 2.7′, mirrored**: `E_q[F(X) G(Y)] ≤ ‖F‖_{L²(q_X)} ‖G‖_{L^{4/3}(q_Y)}`.

Lemma 2.7 is symmetric in its two arguments but Lemma 2.7′ is not, so §5.2 needs
both orientations; this is `contact_hypercontractive_two_four` with the roles of
the two coordinates exchanged, i.e. the tilt `(F^{4/3}, G^{8/9})` rather than
`(F^{8/9}, G^{4/3})`. -/
theorem contact_hypercontractive_four_two {S : Finset (α × β)} {w : α × β → ℝ}
    (hw : Feasible S w) {q : α × β → ℝ} (hq : IsContact S w q) {F : α → ℝ} {G : β → ℝ}
    (hF : ∀ x, 0 ≤ F x) (hG : ∀ y, 0 ≤ G y) :
    (∑ z ∈ S, q z * F z.1 * G z.2)
      ≤ (∑ x, mX q x * F x ^ (2 : ℝ)) ^ ((1 : ℝ) / 2)
        * (∑ y, mY q y * G y ^ ((4 : ℝ) / 3)) ^ ((3 : ℝ) / 4) := by
  have hqnn := hq.1.nonneg
  have hqX : IsPMF (mX q) := isPMF_push hq.1
  have hqY : IsPMF (mY q) := isPMF_push hq.1
  set R : ℝ := ∑ y, mY q y * G y ^ ((4 : ℝ) / 3) with hRdef
  set T : ℝ := ∑ x, mX q x * F x ^ (2 : ℝ) with hTdef
  set P : ℝ := ∑ z ∈ S, q z * F z.1 ^ ((4 : ℝ) / 3) * G z.2 ^ ((8 : ℝ) / 9) with hPdef
  have hRnn : 0 ≤ R := Finset.sum_nonneg fun y _ =>
    mul_nonneg (hqY.nonneg y) (Real.rpow_nonneg (hG y) _)
  have hTnn : 0 ≤ T := Finset.sum_nonneg fun x _ =>
    mul_nonneg (hqX.nonneg x) (Real.rpow_nonneg (hF x) _)
  have hPnn : 0 ≤ P := Finset.sum_nonneg fun z _ =>
    mul_nonneg (mul_nonneg (hqnn z) (Real.rpow_nonneg (hF z.1) _))
      (Real.rpow_nonneg (hG z.2) _)
  have hRsupp : (∑ z ∈ S, q z * G z.2 ^ ((4 : ℝ) / 3)) = R := by
    have hfull : (∑ z, q z * G z.2 ^ ((4 : ℝ) / 3))
        = ∑ z ∈ S, q z * G z.2 ^ ((4 : ℝ) / 3) := by
      symm
      apply Finset.sum_subset (Finset.subset_univ S)
      intro z _ hz
      simp [hq.2.1 z hz]
    rw [← hfull, hRdef]
    exact (sum_push_mul Prod.snd q fun y => G y ^ ((4 : ℝ) / 3)).symm
  have hholder : (∑ z ∈ S, q z * F z.1 * G z.2) ≤ P ^ ((3 : ℝ) / 4) * R ^ ((1 : ℝ) / 4) := by
    have hpq : Real.HolderConjugate ((4 : ℝ) / 3) 4 :=
      Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
    have h := Real.inner_le_Lp_mul_Lq S
      (fun z : α × β => q z ^ ((3 : ℝ) / 4) * F z.1 * G z.2 ^ ((2 : ℝ) / 3))
      (fun z : α × β => q z ^ ((1 : ℝ) / 4) * G z.2 ^ ((1 : ℝ) / 3)) hpq
    have hprod : ∀ z : α × β,
        (q z ^ ((3 : ℝ) / 4) * F z.1 * G z.2 ^ ((2 : ℝ) / 3))
          * (q z ^ ((1 : ℝ) / 4) * G z.2 ^ ((1 : ℝ) / 3)) = q z * F z.1 * G z.2 := by
      intro z
      have hq' : q z ^ ((3 : ℝ) / 4) * q z ^ ((1 : ℝ) / 4) = q z := by
        rw [← Real.rpow_add' (hqnn z) (by norm_num)]
        norm_num
      have hG' : G z.2 ^ ((2 : ℝ) / 3) * G z.2 ^ ((1 : ℝ) / 3) = G z.2 := by
        rw [← Real.rpow_add' (hG z.2) (by norm_num)]
        norm_num
      calc (q z ^ ((3 : ℝ) / 4) * F z.1 * G z.2 ^ ((2 : ℝ) / 3))
            * (q z ^ ((1 : ℝ) / 4) * G z.2 ^ ((1 : ℝ) / 3))
          = (q z ^ ((3 : ℝ) / 4) * q z ^ ((1 : ℝ) / 4)) * F z.1
              * (G z.2 ^ ((2 : ℝ) / 3) * G z.2 ^ ((1 : ℝ) / 3)) := by ring
        _ = q z * F z.1 * G z.2 := by rw [hq', hG']
    have hleft : ∀ z : α × β,
        |q z ^ ((3 : ℝ) / 4) * F z.1 * G z.2 ^ ((2 : ℝ) / 3)| ^ ((4 : ℝ) / 3)
          = q z * F z.1 ^ ((4 : ℝ) / 3) * G z.2 ^ ((8 : ℝ) / 9) := by
      intro z
      rw [abs_of_nonneg (mul_nonneg (mul_nonneg (Real.rpow_nonneg (hqnn z) _) (hF z.1))
          (Real.rpow_nonneg (hG z.2) _)),
        Real.mul_rpow (mul_nonneg (Real.rpow_nonneg (hqnn z) _) (hF z.1))
          (Real.rpow_nonneg (hG z.2) _),
        Real.mul_rpow (Real.rpow_nonneg (hqnn z) _) (hF z.1),
        ← Real.rpow_mul (hqnn z), ← Real.rpow_mul (hG z.2)]
      norm_num
    have hright : ∀ z : α × β,
        |q z ^ ((1 : ℝ) / 4) * G z.2 ^ ((1 : ℝ) / 3)| ^ (4 : ℝ)
          = q z * G z.2 ^ ((4 : ℝ) / 3) := by
      intro z
      rw [abs_of_nonneg (mul_nonneg (Real.rpow_nonneg (hqnn z) _)
          (Real.rpow_nonneg (hG z.2) _)),
        Real.mul_rpow (Real.rpow_nonneg (hqnn z) _) (Real.rpow_nonneg (hG z.2) _),
        ← Real.rpow_mul (hqnn z), ← Real.rpow_mul (hG z.2)]
      norm_num
    simp only [hprod, hleft, hright] at h
    calc (∑ z ∈ S, q z * F z.1 * G z.2)
        ≤ P ^ (1 / ((4 : ℝ) / 3)) * R ^ (1 / (4 : ℝ)) := by
          rw [← hRsupp]; simpa [hPdef, hRsupp] using h
      _ = P ^ ((3 : ℝ) / 4) * R ^ ((1 : ℝ) / 4) := by norm_num
  have hP : P ≤ T ^ ((2 : ℝ) / 3) * R ^ ((2 : ℝ) / 3) := by
    have h := contact_hypercontractive hw hq
      (f := fun x => F x ^ ((4 : ℝ) / 3)) (g := fun y => G y ^ ((8 : ℝ) / 9))
      (fun x => Real.rpow_nonneg (hF x) _) (fun y => Real.rpow_nonneg (hG y) _)
    have hFpow : ∀ x, (F x ^ ((4 : ℝ) / 3)) ^ ((3 : ℝ) / 2) = F x ^ (2 : ℝ) := by
      intro x; rw [← Real.rpow_mul (hF x)]; norm_num
    have hGpow : ∀ y, (G y ^ ((8 : ℝ) / 9)) ^ ((3 : ℝ) / 2) = G y ^ ((4 : ℝ) / 3) := by
      intro y; rw [← Real.rpow_mul (hG y)]; norm_num
    simp only [hFpow, hGpow] at h
    exact h
  refine hholder.trans ?_
  have hmono : P ^ ((3 : ℝ) / 4) ≤ T ^ ((1 : ℝ) / 2) * R ^ ((1 : ℝ) / 2) := by
    have h := Real.rpow_le_rpow hPnn hP (by norm_num : (0 : ℝ) ≤ 3 / 4)
    rwa [Real.mul_rpow (Real.rpow_nonneg hTnn _) (Real.rpow_nonneg hRnn _),
      ← Real.rpow_mul hTnn, ← Real.rpow_mul hRnn,
      show (2 : ℝ) / 3 * ((3 : ℝ) / 4) = 1 / 2 by norm_num] at h
  calc P ^ ((3 : ℝ) / 4) * R ^ ((1 : ℝ) / 4)
      ≤ (T ^ ((1 : ℝ) / 2) * R ^ ((1 : ℝ) / 2)) * R ^ ((1 : ℝ) / 4) := by
        gcongr
    _ = T ^ ((1 : ℝ) / 2) * R ^ ((3 : ℝ) / 4) := by
        rw [mul_assoc, ← Real.rpow_add' hRnn (by norm_num : (1 : ℝ) / 2 + 1 / 4 ≠ 0)]
        norm_num

/-- **Lemma 2.8(a)** (fusion identity).
`∑_b θ_b G_w(r_b) − G_w(r) = 3 I(B;Z) − 2 I(B;X) − 2 I(B;Y)`.

The positivity hypothesis is exactly Definition 2.1's kernel positivity; the
identity fails without it.

Together with Lemma 1.2 this converts defects into information quantities;
§4.3, §5.6 and §5.7 are corollaries of it. -/
theorem Gdef_fusion {S : Finset (α × β)} {w : α × β → ℝ}
    (hw : ∀ z ∈ S, 0 < w z) {r : α × β → ℝ}
    (hr : IsPMF r) (hrS : Supported S r) (V : Latent r) :
    (∑ b, V.prior b * Gdef S w (V.comp b)) - Gdef S w r
      = 3 * MI (fun q => q.1) (fun q => q.2) V.joint
        - 2 * MI (fun q => q.1) (fun q => q.2.1) V.joint
        - 2 * MI (fun q => q.1) (fun q => q.2.2) V.joint := by
  let c : α × β → ℝ := fun z => -3 * lg (w z)
  have hcompS (b : V.ι) (hb : V.prior b ≠ 0) : Supported S (V.comp b) := by
    intro z hzS
    have hrz : r z = 0 := hrS z hzS
    have hmix := V.mixture z
    rw [hrz] at hmix
    have hzero := (Finset.sum_eq_zero_iff_of_nonneg
      (fun a _ => mul_nonneg (V.prior_isPMF.nonneg a)
        ((V.comp_isPMF a).nonneg z))).mp hmix b (Finset.mem_univ b)
    exact (mul_eq_zero.mp hzero).resolve_left hb
  have hcompGap :
      (∑ b, V.prior b * Gdef S w (V.comp b)) =
        ∑ b, V.prior b * ((∑ z ∈ S, c z * V.comp b z) - Phi (V.comp b)) := by
    apply Finset.sum_congr rfl
    intro b _
    by_cases hb : V.prior b = 0
    · simp [hb]
    · rw [Gdef_eq_certificate_gap hw (V.comp_isPMF b) (hcompS b hb)]
  have hrGap :
      Gdef S w r = (∑ z ∈ S, c z * r z) - Phi r := by
    exact Gdef_eq_certificate_gap hw hr hrS
  have hkernel :
      (∑ b, V.prior b * (∑ z ∈ S, c z * V.comp b z)) =
        ∑ z ∈ S, c z * r z := by
    calc
      (∑ b, V.prior b * (∑ z ∈ S, c z * V.comp b z)) =
          ∑ b, ∑ z ∈ S, c z * (V.prior b * V.comp b z) := by
            apply Finset.sum_congr rfl
            intro b _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro z _
            ring
      _ = ∑ z ∈ S, ∑ b, c z * (V.prior b * V.comp b z) := by
        rw [Finset.sum_comm]
      _ = ∑ z ∈ S, c z * r z := by
        apply Finset.sum_congr rfl
        intro z _
        rw [← Finset.mul_sum, V.mixture]
  calc
    (∑ b, V.prior b * Gdef S w (V.comp b)) - Gdef S w r =
        Phi r - ∑ b, V.prior b * Phi (V.comp b) := by
          rw [hcompGap, hrGap]
          simp_rw [mul_sub]
          rw [Finset.sum_sub_distrib, hkernel]
          ring
    _ = V.score - Ixy r := by
      rw [Latent.score_eq hr V, Phi_eq_Psi_sub_Ixy]
      ring
    _ = 3 * MI (fun q => q.1) (fun q => q.2) V.joint
        - 2 * MI (fun q => q.1) (fun q => q.2.1) V.joint
        - 2 * MI (fun q => q.1) (fun q => q.2.2) V.joint :=
      Latent.score_sub_Ixy hr V

/-- **Lemma 2.8(c)**: for an attained τ-optimal
common-contact pair, `G_w(p) = I(X;Y) − τ(p)`. -/
theorem Gdef_of_common_contact_pair {p : α × β → ℝ} (hp : IsPMF p) (L : Latent p)
    {w : α × β → ℝ} (hw : Feasible (support p) w) (hopt : L.score = tau p)
    (hcontact : ∀ v, L.prior v ≠ 0 → IsContact (support p) w (L.comp v)) :
    Gdef (support p) w p = Ixy p - tau p := by
  have hpS : Supported (support p) p := by
    intro z hz
    simpa [support] using hz
  have hsumZero :
      (∑ v, L.prior v * Gdef (support p) w (L.comp v)) = 0 := by
    apply Finset.sum_eq_zero
    intro v _
    by_cases hv : L.prior v = 0
    · simp [hv]
    · have hc := hcontact v hv
      rw [(Gdef_eq_zero_iff hw (L.comp_isPMF v) hc.2.1).mpr hc, mul_zero]
  have hfusion := Gdef_fusion hw.1 hp hpS L
  rw [hsumZero, zero_sub] at hfusion
  have hscore := Latent.score_sub_Ixy hp L
  rw [hopt] at hscore
  linarith

end stoch_to_det
