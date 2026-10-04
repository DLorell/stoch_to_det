import stoch_to_det.SharedRace.Information
import stoch_to_det.Toolkit

/-! Posterior dispersion controls the collision defect of the mean posterior. -/

namespace stoch_to_det
namespace SharedRace

open Finset

private theorem sum_sq_le_half_sq_sum_abs
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : ι → ℝ) (hv : ∑ i, v i = 0) :
    (∑ i, (v i)^2) ≤ (∑ i, |v i|)^2/2 := by
  have hcoord (i : ι) : 2*|v i| ≤ ∑ j, |v j| := by
    have hsum := sum_erase_add (s := (univ : Finset ι))
      (f := v) (mem_univ i)
    have hrem : (∑ j ∈ univ.erase i, v j) = -v i := by
      rw [hv] at hsum
      linarith
    have htri := abs_sum_le_sum_abs v (univ.erase i)
    rw [hrem, abs_neg] at htri
    have habs := sum_erase_add (s := (univ : Finset ι))
      (f := fun j => |v j|) (mem_univ i)
    linarith
  calc
    (∑ i, (v i)^2) ≤ ∑ i, ((∑ j, |v j|)/2)*|v i| := by
      apply sum_le_sum
      intro i _
      have hm := mul_le_mul_of_nonneg_right (hcoord i) (abs_nonneg (v i))
      nlinarith [sq_abs (v i)]
    _ = (∑ i, |v i|)^2/2 := by rw [← mul_sum]; ring

/-- Pinsker improves to coefficient one for squared Euclidean distance on
the probability simplex, because a difference of PMFs has zero sum. -/
theorem sum_sq_sub_le_kl_nats
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {P Q : ι → ℝ} (hP : IsPMF P) (hQ : IsPMF Q) (hac : AbsCont P Q) :
    (∑ i, (P i-Q i)^2) ≤ ∑ i, P i*Real.log (P i/Q i) := by
  have hz : ∑ i, (P i-Q i) = 0 := by
    rw [sum_sub_distrib]
    have hp : ∑ i, P i = 1 := hP.total
    have hq : ∑ i, Q i = 1 := hQ.total
    rw [hp, hq]
    ring
  have hl2 := sum_sq_le_half_sq_sum_abs (fun i => P i-Q i) hz
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hp := mul_le_mul_of_nonneg_left (pinsker hP hQ hac) hlog.le
  have heq : Real.log 2*(2/Real.log 2*tvDist P Q^2) =
      (∑ i, |P i-Q i|)^2/2 := by
    unfold tvDist
    field_simp [hlog.ne']
  have hkl : Real.log 2*KL P Q = ∑ i, P i*Real.log (P i/Q i) := by
    unfold KL
    rw [mul_sum]
    apply sum_congr rfl
    intro i _
    rw [lg_eq_log_div]
    field_simp [hlog.ne']
  rw [heq, hkl] at hp
  exact hl2.trans hp

variable {Ω : Type*} {κ : Type} [Fintype Ω] [Fintype κ]
  [DecidableEq Ω] [DecidableEq κ]

omit [DecidableEq Ω] [DecidableEq κ] in
/-- The exact finite variance decomposition for posterior collision defects. -/
theorem posteriorMean_mismatch_identity
    {μ : Ω → ℝ} (hμ : IsPMF μ) (r : Ω → κ → ℝ) :
    1-(∑ i, (posteriorMean μ r i)^2) = categoricalMismatch μ r +
      ∑ z, μ z*∑ i, (r z i-posteriorMean μ r i)^2 := by
  have hμsum : ∑ z, μ z = 1 := hμ.total
  have hcoord (i : κ) :
      (∑ z, μ z*(r z i-posteriorMean μ r i)^2) =
      (∑ z, μ z*(r z i)^2)-(posteriorMean μ r i)^2 := by
    calc
      _ = (∑ z, μ z*(r z i)^2) -
          2*posteriorMean μ r i*(∑ z, μ z*r z i) +
          (posteriorMean μ r i)^2*(∑ z, μ z) := by
        simp only [mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
        apply sum_congr rfl
        intro z _
        ring
      _ = _ := by
        rw [hμsum]
        change (∑ z, μ z*(r z i)^2) -
          2*posteriorMean μ r i*posteriorMean μ r i +
          (posteriorMean μ r i)^2*1 = _
        ring
  have hvar : (∑ z, μ z*∑ i, (r z i-posteriorMean μ r i)^2) =
      (∑ z, μ z*∑ i, (r z i)^2)-(∑ i, (posteriorMean μ r i)^2) := by
    simp only [mul_sum]
    rw [sum_comm]
    simp_rw [hcoord]
    rw [sum_sub_distrib, sum_comm]
  have hmis : categoricalMismatch μ r = 1-(∑ z, μ z*∑ i, (r z i)^2) := by
    unfold categoricalMismatch
    simp_rw [mul_sub, mul_one]
    rw [sum_sub_distrib, hμsum]
  rw [hvar, hmis]
  ring

/-- Mean-posterior mismatch exceeds the averaged row mismatch by at most
the mutual information in natural-log units. -/
theorem posteriorMean_mismatch_le
    {μ : Ω → ℝ} {r : Ω → κ → ℝ}
    (hμ : IsPMF μ)
    (hr : ∀ z, μ z ≠ 0 → IsPMF (r z))
    (hrpos : ∀ z, μ z ≠ 0 → ∀ i, 0 < r z i) :
    1-(∑ i, (posteriorMean μ r i)^2) ≤ categoricalMismatch μ r +
      Real.log 2*MI Prod.fst Prod.snd (posteriorJoint μ r) := by
  have hπ := posteriorMean_isPMF_of_support hμ hr
  have hπpos := posteriorMean_pos_of_support hμ hrpos
  have hMI := posteriorMI_mul_logTwo_eq_expectedKL hμ hr hrpos
  change Real.log 2*MI Prod.fst Prod.snd (posteriorJoint μ r) = _ at hMI
  have hv : (∑ z, μ z*∑ i, (r z i-posteriorMean μ r i)^2) ≤
      ∑ z, μ z*∑ i, r z i*Real.log (r z i/posteriorMean μ r i) := by
    apply sum_le_sum
    intro z _
    by_cases hz : μ z = 0
    · simp [hz]
    · have hac : AbsCont (r z) (posteriorMean μ r) := by
        intro i hi
        exact ((hπpos i).ne' hi).elim
      exact mul_le_mul_of_nonneg_left
        (sum_sq_sub_le_kl_nats (hr z hz) hπ hac) (hμ.nonneg z)
  rw [posteriorMean_mismatch_identity hμ r, hMI]
  linarith

end SharedRace
end stoch_to_det
