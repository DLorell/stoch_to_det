import stoch_to_det.LW
import stoch_to_det.ConstantBound994

/-!
# Headline generalized stoch_to_det theorems

This is the canonical declaration site for the three public endpoints of the
improved development:

1. generalized stoch_to_det for an ordinary measurable joint-law latent, with the
   exact symbolic constant `Cdagger1771`;
2. the analytic bound `Cdagger1771 < 1771`;
3. the rounded LessWrong three-term corollary with an unrestricted finite
   latent witness.

The statements intentionally display the three information terms rather than
hiding them behind `detScore` or `JointLatent.infoScore`.  In particular, the
first statement visibly chooses one deterministic code from `p` before
quantifying over the latent alphabet and its joint law.  The deterministic
rounded intermediate is also displayed, while the final headline theorem is
the bare `∀ V, ∃ G : Latent p` corollary with no determinism condition.
-/

universe u

namespace stoch_to_det

open MeasureTheory

variable {α β : Type*} [Fintype α] [Fintype β]
  [DecidableEq α] [DecidableEq β]

section JointLaw

variable [MeasurableSpace α] [MeasurableSpace β]
  [MeasurableSingletonClass α] [MeasurableSingletonClass β]

/-- **Generalized stoch_to_det, exact constant.** For each finite joint law `p`, one
deterministic code `Γ`, depending only on `p`, works simultaneously for every
ordinary joint probability law of a measurable latent and `(X,Y)`. -/
theorem generalized_stoch_to_det_Cdagger1771_joint
    {p : α × β → ℝ} (hp : IsPMF p) :
    ∃ Γ : α × β → Fin (Fintype.card (α × β)),
      condH Γ (fun z : α × β => z) p = 0 ∧
      ∀ {ι : Type u} [MeasurableSpace ι]
        (V : JointLatent p ι),
        condMI (fun z : α × β => z.1) (fun z => z.2) Γ p
            + condH Γ (fun z : α × β => z.1) p
            + condH Γ (fun z : α × β => z.2) p
          ≤ Cdagger1771 *
            (V.IxyGiven + V.IvxGivenY + V.IvyGivenX) := by
  obtain ⟨Γ, hΓ⟩ := exists_T_optimal_code hp
  refine ⟨Γ, condH_function_given_pair_zero hp Γ, ?_⟩
  intro ι _ V
  simpa [detScore, JointLatent.infoScore] using
    optimal_code_le_joint_Cdagger1771 hp hΓ V

/-- **Exact analytic constant bound.** The symbolic constant used in the
preceding theorem is strictly smaller than `1771`. -/
theorem Cdagger1771_lt_1771 : Cdagger1771 < (1771 : ℝ) := by
  unfold Cdagger1771
  linarith [KD1771_lt_1770]

/-- **Deterministic rounded intermediate.** The witness remains explicitly a
function of `(X,Y)`; the bare theorem below weakens its witness class. -/
theorem LW_sum_1771_joint_deterministic
    {p : α × β → ℝ} (hp : IsPMF p)
    {ι : Type u} [MeasurableSpace ι]
    (V : JointLatent p ι) :
    ∃ Γ : α × β → Fin (Fintype.card (α × β)),
      condMI (fun z : α × β => z.1) (fun z => z.2) Γ p
          + condH Γ (fun z : α × β => z.1) p
          + condH Γ (fun z : α × β => z.2) p
        ≤ (1771 : ℝ) *
          (V.IxyGiven + V.IvxGivenY + V.IvyGivenX) := by
  obtain ⟨Γ, _, hΓ⟩ := generalized_stoch_to_det_Cdagger1771_joint hp
  refine ⟨Γ, (hΓ V).trans ?_⟩
  exact mul_le_mul_of_nonneg_right (le_of_lt Cdagger1771_lt_1771) <| by
    simpa [JointLatent.infoScore] using V.infoScore_nonneg hp

/-- **Bare LessWrong sum corollary.** The witness is an arbitrary finite
latent in the proposition.  No `IsDet` hypothesis and no function-witness type
appears in the conclusion, although the proof supplies a deterministic
witness from the stronger theorem above. -/
theorem LW_sum_1771_joint
    {p : α × β → ℝ} (hp : IsPMF p)
    {ι : Type u} [MeasurableSpace ι]
    (V : JointLatent p ι) :
    ∃ G : Latent p,
      G.DScore ≤ (1771 : ℝ) * V.infoScore := by
  obtain ⟨Γ, hΓ⟩ := LW_sum_1771_joint_deterministic hp V
  refine ⟨Latent.ofFunction hp Γ, ?_⟩
  simpa [detScore, JointLatent.infoScore] using hΓ


/-! ### Strengthened `994` endpoints -/

/-- The exact strengthened finite theorem applies to an ordinary joint-law
latent after lossless finite compression. -/
theorem T_le_Cdagger994_mul_jointScore
    {p : α × β → ℝ} (hp : IsPMF p)
    {ι : Type u} [MeasurableSpace ι]
    (V : JointLatent p ι) :
    T p ≤ Cdagger994 * V.infoScore := by
  obtain ⟨W, hW⟩ := (V.toGeneralLatent hp).exists_finite_score_eq hp
  calc
    T p ≤ Cdagger994 * tau p := T_le_Cdagger994 hp
    _ ≤ Cdagger994 * W.score :=
      mul_le_mul_of_nonneg_left (tau_le_score W) Cdagger994_pos.le
    _ = Cdagger994 * V.infoScore := by simpa using congrArg (Cdagger994 * ·) hW

/-- **Generalized stochastic-to-deterministic theorem, strengthened exact
constant.** One deterministic code selected from `p` works for every ordinary
measurable joint-law latent. -/
theorem generalized_stoch_to_det_Cdagger994_joint
    {p : α × β → ℝ} (hp : IsPMF p) :
    ∃ Γ : α × β → Fin (Fintype.card (α × β)),
      condH Γ (fun z : α × β => z) p = 0 ∧
      ∀ {ι : Type u} [MeasurableSpace ι]
        (V : JointLatent p ι),
        condMI (fun z : α × β => z.1) (fun z => z.2) Γ p
            + condH Γ (fun z : α × β => z.1) p
            + condH Γ (fun z : α × β => z.2) p
          ≤ Cdagger994 *
            (V.IxyGiven + V.IvxGivenY + V.IvyGivenX) := by
  obtain ⟨Γ, hΓ⟩ := exists_T_optimal_code hp
  refine ⟨Γ, condH_function_given_pair_zero hp Γ, ?_⟩
  intro ι _ V
  have hdet : detScore p Γ ≤ Cdagger994 * V.infoScore := by
    rw [← Latent.ofFunction_score_eq_detScore hp Γ, hΓ]
    exact T_le_Cdagger994_mul_jointScore hp V
  simpa [detScore, JointLatent.infoScore] using hdet

/-- **Exact analytic constant bound.** -/
theorem Cdagger994_lt_994 : Cdagger994 < (994 : ℝ) := by
  unfold Cdagger994
  linarith [KD994_lt_993]

/-- The deterministic rounded intermediate at the improved constant. -/
theorem LW_sum_994_joint_deterministic
    {p : α × β → ℝ} (hp : IsPMF p)
    {ι : Type u} [MeasurableSpace ι]
    (V : JointLatent p ι) :
    ∃ Γ : α × β → Fin (Fintype.card (α × β)),
      condMI (fun z : α × β => z.1) (fun z => z.2) Γ p
          + condH Γ (fun z : α × β => z.1) p
          + condH Γ (fun z : α × β => z.2) p
        ≤ (994 : ℝ) *
          (V.IxyGiven + V.IvxGivenY + V.IvyGivenX) := by
  obtain ⟨Γ, _, hΓ⟩ := generalized_stoch_to_det_Cdagger994_joint hp
  refine ⟨Γ, (hΓ V).trans ?_⟩
  exact mul_le_mul_of_nonneg_right Cdagger994_lt_994.le <| by
    simpa [JointLatent.infoScore] using V.infoScore_nonneg hp

/-- **Bare LessWrong sum corollary at 994.** The proof supplies a deterministic
witness, while the statement only requires a finite latent. -/
theorem LW_sum_994_joint
    {p : α × β → ℝ} (hp : IsPMF p)
    {ι : Type u} [MeasurableSpace ι]
    (V : JointLatent p ι) :
    ∃ G : Latent p,
      G.DScore ≤ (994 : ℝ) * V.infoScore := by
  obtain ⟨Γ, hΓ⟩ := LW_sum_994_joint_deterministic hp V
  refine ⟨Latent.ofFunction hp Γ, ?_⟩
  simpa [detScore, JointLatent.infoScore] using hΓ

end JointLaw

end stoch_to_det
