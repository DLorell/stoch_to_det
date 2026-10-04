import stoch_to_det.Bound94
import stoch_to_det.SourceCoarsening

/-! A deterministic finite latent attaining the 9.4 bound uniformly over stochastic latents. -/

open scoped BigOperators
open stoch_to_det

namespace FiniteBoundProof

variable {α β : Type} [Fintype α] [Fintype β]
  [DecidableEq α] [DecidableEq β]

theorem finite_bound {p : α × β → ℝ} (hp : IsPMF p) :
    ∃ Γ : α × β → Fin (Fintype.card (α × β)),
      condH Γ id p = 0 ∧
      ∀ {K : Type} [Fintype K] [DecidableEq K]
        (q : K × (α × β) → ℝ), IsPMF q →
        (∀ z, ∑ v, q (v, z) = p z) →
        condMI Prod.fst Prod.snd Γ p + condH Γ Prod.fst p + condH Γ Prod.snd p
          ≤ (47 / 5 : ℝ) *
            (condMI (fun w => w.2.1) (fun w => w.2.2) Prod.fst q
              + condMI Prod.fst (fun w => w.2.1) (fun w => w.2.2) q
              + condMI Prod.fst (fun w => w.2.2) (fun w => w.2.1) q) := by
  obtain ⟨Γ, hΓ⟩ := exists_T_optimal_code hp
  refine ⟨Γ, condH_function_given_pair_zero hp Γ, ?_⟩
  intro K _ _ q hq hmarginal
  have hsource : push Prod.snd q = p := by
    funext z
    simpa [push, Finset.sum_filter, Fintype.sum_prod_type] using hmarginal z
  let L := SourceCoarsening.ofJoint hp q hq hsource
  have hbound : detScore p Γ ≤ (47 / 5 : ℝ) * L.score := by
    calc
      detScore p Γ = T p := by
        rw [← Latent.ofFunction_score_eq_detScore hp Γ]
        exact hΓ
      _ ≤ (47 / 5 : ℝ) * tau p := T_le_94 hp
      _ ≤ (47 / 5 : ℝ) * L.score :=
        mul_le_mul_of_nonneg_left (tau_le_score L) (by norm_num)
  simpa only [detScore, L, SourceCoarsening.ofJoint_score] using hbound

end FiniteBoundProof
