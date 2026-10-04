import stoch_to_det.SharedRace.Definitions
import stoch_to_det.SharedRace.Scalar

/-!
# Finite KL identities for the all-label shared-race bound

This file converts the bit-valued mutual information used by the finite
problem into its natural-log KL form.  It also records the finite
cross-entropy inequality in a form suited to deterministic winner maps.
-/

namespace stoch_to_det
namespace SharedRace

open Finset

universe u v w

/-- Mutual information in bits, multiplied by `log 2`, is the KL divergence
of the joint law from the product of its marginals. -/
lemma logTwo_mul_MI_eq_kl
    {A : Type u} {B : Type v} {C : Type w}
    [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq B] [DecidableEq C]
    {m : A → ℝ} (hm : IsPMF m) (f : A → B) (g : A → C) :
    SharedRace.logTwo * MI f g m =
      ∑ z, push (fun a => (f a, g a)) m z *
        Real.log
          (push (fun a => (f a, g a)) m z /
            (push f m z.1 * push g m z.2)) := by
  let joint : B × C → ℝ := push (fun a => (f a, g a)) m
  let fstMarginal : B → ℝ := push Prod.fst joint
  let sndMarginal : C → ℝ := push Prod.snd joint
  let productMarginal : B × C → ℝ :=
    fun z => fstMarginal z.1 * sndMarginal z.2
  have hjoint : IsPMF joint := isPMF_push hm
  have hfst : IsPMF fstMarginal := isPMF_push hjoint
  have hsnd : IsPMF sndMarginal := isPMF_push hjoint
  have hsupp : ∀ z, joint z ≠ 0 → productMarginal z ≠ 0 := by
    intro z hz
    have hjpos : 0 < joint z :=
      lt_of_le_of_ne (hjoint.nonneg z) (Ne.symm hz)
    have hfst_le : joint z ≤ fstMarginal z.1 := by
      dsimp [fstMarginal]
      unfold push
      exact Finset.single_le_sum (fun w _ => hjoint.nonneg w) (by simp)
    have hsnd_le : joint z ≤ sndMarginal z.2 := by
      dsimp [sndMarginal]
      unfold push
      exact Finset.single_le_sum (fun w _ => hjoint.nonneg w) (by simp)
    dsimp [productMarginal]
    exact mul_ne_zero (lt_of_lt_of_le hjpos hfst_le).ne'
      (lt_of_lt_of_le hjpos hsnd_le).ne'
  have hfst_eq : fstMarginal = push f m := by
    dsimp [fstMarginal, joint]
    simpa [Function.comp_def] using
      (push_push (fun a => (f a, g a)) Prod.fst m)
  have hsnd_eq : sndMarginal = push g m := by
    dsimp [sndMarginal, joint]
    simpa [Function.comp_def] using
      (push_push (fun a => (f a, g a)) Prod.snd m)
  have hMIent : MI f g m = H fstMarginal + H sndMarginal - H joint := by
    unfold MI Hvar
    rw [hfst_eq, hsnd_eq]
  have hlift_fst : ∑ x, Real.negMulLog (fstMarginal x) =
      ∑ z, joint z * (-Real.log (fstMarginal z.1)) := by
    calc
      (∑ x, Real.negMulLog (fstMarginal x)) =
          ∑ x, fstMarginal x * (-Real.log (fstMarginal x)) := by
        apply Finset.sum_congr rfl
        intro x _
        rw [Real.negMulLog]
        ring
      _ = ∑ z, joint z * (-Real.log (fstMarginal z.1)) :=
        sum_push_mul Prod.fst joint _
  have hlift_snd : ∑ y, Real.negMulLog (sndMarginal y) =
      ∑ z, joint z * (-Real.log (sndMarginal z.2)) := by
    calc
      (∑ y, Real.negMulLog (sndMarginal y)) =
          ∑ y, sndMarginal y * (-Real.log (sndMarginal y)) := by
        apply Finset.sum_congr rfl
        intro y _
        rw [Real.negMulLog]
        ring
      _ = ∑ z, joint z * (-Real.log (sndMarginal z.2)) :=
        sum_push_mul Prod.snd joint _
  have hlift_joint : ∑ z, Real.negMulLog (joint z) =
      ∑ z, joint z * (-Real.log (joint z)) := by
    apply Finset.sum_congr rfl
    intro z _
    rw [Real.negMulLog]
    ring
  have hEntropyKL :
      (∑ x, Real.negMulLog (fstMarginal x)) +
          (∑ y, Real.negMulLog (sndMarginal y)) -
            ∑ z, Real.negMulLog (joint z) =
        ∑ z, joint z * Real.log (joint z / productMarginal z) := by
    rw [hlift_fst, hlift_snd, hlift_joint,
      ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro z _
    by_cases hz : joint z = 0
    · simp [hz]
    · have hprod := hsupp z hz
      dsimp [productMarginal] at hprod ⊢
      have hfst0 : fstMarginal z.1 ≠ 0 := (mul_ne_zero_iff.mp hprod).1
      have hsnd0 : sndMarginal z.2 ≠ 0 := (mul_ne_zero_iff.mp hprod).2
      rw [Real.log_div hz hprod, Real.log_mul hfst0 hsnd0]
      ring
  have hHjoint := H_eq_negMulLog hjoint.isFinMeas
  have hHfst := H_eq_negMulLog hfst.isFinMeas
  have hHsnd := H_eq_negMulLog hsnd.isFinMeas
  rw [hjoint.total, Real.log_one, mul_zero, zero_add] at hHjoint
  rw [hfst.total, Real.log_one, mul_zero, zero_add] at hHfst
  rw [hsnd.total, Real.log_one, mul_zero, zero_add] at hHsnd
  unfold SharedRace.logTwo
  calc
    Real.log 2 * MI f g m =
        Real.log 2 * (H fstMarginal + H sndMarginal - H joint) := by
      rw [hMIent]
    _ = Real.log 2 * H fstMarginal + Real.log 2 * H sndMarginal -
          Real.log 2 * H joint := by ring
    _ = (∑ x, Real.negMulLog (fstMarginal x)) +
          (∑ y, Real.negMulLog (sndMarginal y)) -
            ∑ z, Real.negMulLog (joint z) := by
      rw [hHfst, hHsnd, hHjoint]
    _ = ∑ z, joint z * Real.log (joint z / productMarginal z) :=
      hEntropyKL
    _ = ∑ z, push (fun a => (f a, g a)) m z *
        Real.log
          (push (fun a => (f a, g a)) m z /
            (push f m z.1 * push g m z.2)) := by
      dsimp only [joint, productMarginal]
      rw [hfst_eq, hsnd_eq]

/-- Pushing a PMF through a deterministic map and applying the finite
cross-entropy bound turns the cross entropy into a source expectation. -/
lemma H_push_le_expected_crossEntropy
    {A : Type u} {B : Type v} [Fintype A] [Fintype B] [DecidableEq B]
    {m : A → ℝ} (hm : IsPMF m) (f : A → B)
    {q : B → ℝ} (hq : IsPMF q) (hqpos : ∀ b, 0 < q b) :
    H (push f m) ≤ ∑ a, m a * lg (1 / q (f a)) := by
  calc
    H (push f m) ≤ ∑ b, push f m b * lg (1 / q b) :=
      H_le_crossEntropy (isPMF_push hm) hq
        (fun b _ => (hqpos b).ne')
    _ = ∑ a, m a * lg (1 / q (f a)) :=
      sum_push_mul f m _

private lemma push_prod_eta
    {A : Type u} {B : Type v} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (m : A × B → ℝ) :
    push (fun z : A × B => (z.1, z.2)) m = m := by
  funext z
  unfold push
  apply Finset.sum_eq_single z
  · intro w hw hwz
    exact (hwz (Finset.mem_filter.mp hw).2).elim
  · intro hz
    exact (hz (by simp)).elim

/-- For a finite source and a support-local family of strictly positive
categorical posterior rows, mutual information is the expected row-wise KL
divergence from the mean posterior.  The left side is converted from bits to
nats by `logTwo`. -/
theorem posteriorMI_mul_logTwo_eq_expectedKL
    {A : Type u} {B : Type} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    {m : A → ℝ} {r : A → B → ℝ}
    (hm : IsPMF m)
    (hr : ∀ a, m a ≠ 0 → IsPMF (r a))
    (hrpos : ∀ a, m a ≠ 0 → ∀ b, 0 < r a b) :
    SharedRace.logTwo *
        MI Prod.fst Prod.snd (posteriorJoint m r) =
      ∑ a, m a * ∑ b, r a b *
        Real.log (r a b / posteriorMean m r b) := by
  have hjoint : IsPMF (posteriorJoint m r) :=
    posteriorJoint_isPMF_of_support hm hr
  have hKL := logTwo_mul_MI_eq_kl hjoint
    (@Prod.fst A B) (@Prod.snd A B)
  rw [push_prod_eta,
    push_posteriorJoint_fst hr,
    push_posteriorJoint_snd] at hKL
  rw [hKL, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  by_cases ha : m a = 0
  · simp [posteriorJoint, ha]
  · have hma_pos : 0 < m a :=
      lt_of_le_of_ne (hm.nonneg a) (Ne.symm ha)
    have hrab_pos : 0 < r a b := hrpos a ha b
    have hmean_pos : 0 < posteriorMean m r b := by
      unfold posteriorMean
      have hnonneg : ∀ x ∈ (Finset.univ : Finset A), 0 ≤ m x * r x b := by
        intro x _
        by_cases hx : m x = 0
        · simp [hx]
        · exact mul_nonneg (hm.nonneg x) ((hr x hx).nonneg b)
      have hle : m a * r a b ≤ ∑ x, m x * r x b :=
        Finset.single_le_sum hnonneg (Finset.mem_univ a)
      exact lt_of_lt_of_le (mul_pos hma_pos hrab_pos) hle
    have hquot :
        (m a * r a b) / (m a * posteriorMean m r b) =
          r a b / posteriorMean m r b := by
      field_simp [ha, hmean_pos.ne']
    rw [show posteriorJoint m r (a, b) = m a * r a b by rfl,
      hquot]
    ring

end SharedRace
end stoch_to_det
