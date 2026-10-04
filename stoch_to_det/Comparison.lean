import stoch_to_det.JointLatent
import stoch_to_det.Envelope

/-!
# Transferring a finite comparison constant to the full joint-law theorem

A bound on `T p / tau p` applies to arbitrary measurable latents by exact
finite compression. The deterministic minimizer depends only on `p`, so the
same code works simultaneously for all latent alphabets and all joint laws.
This transfer is independent of the proof or value of the finite constant.
-/

universe u

namespace stoch_to_det

variable {α β : Type*} [Fintype α] [Fintype β]
  [DecidableEq α] [DecidableEq β]

theorem T_le_mul_generalScore_of_comparison
    {p : α × β → ℝ} (hp : IsPMF p)
    {C : ℝ} (hC : 0 ≤ C) (hbound : T p ≤ C * tau p)
    {ι : Type u} [MeasurableSpace ι] (V : GeneralLatent p ι) :
    T p ≤ C * V.infoScore := by
  obtain ⟨W, hW⟩ := V.exists_finite_score_eq hp
  calc
    T p ≤ C * tau p := hbound
    _ ≤ C * W.score := mul_le_mul_of_nonneg_left (tau_le_score W) hC
    _ = C * V.infoScore := by rw [hW]

variable [MeasurableSpace α] [MeasurableSpace β]
  [MeasurableSingletonClass α] [MeasurableSingletonClass β]

/-- One deterministic minimizer, chosen before the measurable latent and its
joint law, inherits any nonnegative finite comparison constant. -/
theorem generalized_stoch_to_det_joint_of_comparison
    {p : α × β → ℝ} (hp : IsPMF p)
    {C : ℝ} (hC : 0 ≤ C) (hbound : T p ≤ C * tau p) :
    ∃ Γ : α × β → Fin (Fintype.card (α × β)),
      condH Γ (fun z : α × β => z) p = 0 ∧
      ∀ {ι : Type u} [MeasurableSpace ι] (V : JointLatent p ι),
        condMI (fun z : α × β => z.1) (fun z => z.2) Γ p
            + condH Γ (fun z : α × β => z.1) p
            + condH Γ (fun z : α × β => z.2) p
          ≤ C * (V.IxyGiven + V.IvxGivenY + V.IvyGivenX) := by
  obtain ⟨Γ, hΓ⟩ := exists_T_optimal_code hp
  refine ⟨Γ, condH_function_given_pair_zero hp Γ, ?_⟩
  intro ι _ V
  have h := T_le_mul_generalScore_of_comparison hp hC hbound (V.toGeneralLatent hp)
  rw [← hΓ, Latent.ofFunction_score_eq_detScore hp Γ] at h
  simpa [detScore, JointLatent.infoScore] using h

end stoch_to_det
