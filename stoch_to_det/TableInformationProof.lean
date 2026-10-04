import stoch_to_det.FiniteBoundProof

/-! Probability-table information quantities and their correspondence with the core library. -/

open scoped BigOperators
open stoch_to_det

namespace TableInformationProof

variable {A B C Ω : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype Ω]

def probability (p : A → ℝ) : Prop := (∀ a, 0 ≤ p a) ∧ ∑ a, p a = 1

noncomputable def entropy (p : A → ℝ) : ℝ :=
  -∑ a, p a * (Real.log (p a) / Real.log 2)

noncomputable def conditionalEntropy (p : A × B → ℝ) : ℝ :=
  entropy p - entropy (fun b => ∑ a, p (a, b))

noncomputable def mutualInformation (p : A × B → ℝ) : ℝ :=
  entropy (fun a => ∑ b, p (a, b)) + entropy (fun b => ∑ a, p (a, b)) - entropy p

noncomputable def conditionalMutualInformation (p : A × B × C → ℝ) : ℝ :=
  entropy (fun ac : A × C => ∑ b, p (ac.1, b, ac.2))
    + entropy (fun bc : B × C => ∑ a, p (a, bc.1, bc.2))
    - entropy p - entropy (fun c => ∑ a, ∑ b, p (a, b, c))

noncomputable def latentError (p : A × B × C → ℝ) : ℝ :=
  conditionalMutualInformation p
    + conditionalMutualInformation (fun vxy : C × A × B => p (vxy.2.1, vxy.2.2, vxy.1))
    + conditionalMutualInformation (fun vyx : C × B × A => p (vyx.2.2, vyx.2.1, vyx.1))

theorem entropy_eq_H {p : A → ℝ} (hp : IsPMF p) : entropy p = H p := by
  unfold entropy H
  rw [hp.total, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro a _
  simp only [lg_eq_log_div, one_div, Real.log_inv, neg_div]
  ring

variable [DecidableEq A] [DecidableEq B] [DecidableEq C]

theorem entropy_push_eq_Hvar {p : Ω → ℝ} (hp : IsPMF p) (f : Ω → A) :
    entropy (push f p) = Hvar f p := entropy_eq_H (isPMF_push hp)

theorem push_id (p : A → ℝ) : push id p = p := by
  funext a
  simp [push, Finset.sum_filter]

omit [DecidableEq B] in
theorem push_pair_a (p : A × B → ℝ) :
    push Prod.fst p = fun a => ∑ b, p (a, b) := by
  funext a
  simp only [push, Finset.sum_filter, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  simp

omit [DecidableEq A] in
theorem push_pair_b (p : A × B → ℝ) :
    push Prod.snd p = fun b => ∑ a, p (a, b) := by
  funext b
  simp [push, Finset.sum_filter, Fintype.sum_prod_type]

theorem conditionalEntropy_eq_condH {p : A × B → ℝ} (hp : IsPMF p) :
    conditionalEntropy p = condH Prod.fst Prod.snd p := by
  unfold conditionalEntropy condH
  rw [← push_pair_b p, entropy_push_eq_Hvar hp, entropy_eq_H hp]
  congr 1
  exact congrArg H (push_id p).symm

theorem mutualInformation_eq_MI {p : A × B → ℝ} (hp : IsPMF p) :
    mutualInformation p = MI Prod.fst Prod.snd p := by
  unfold mutualInformation MI
  rw [← push_pair_a p, ← push_pair_b p, entropy_push_eq_Hvar hp,
    entropy_push_eq_Hvar hp, entropy_eq_H hp]
  congr 1
  exact congrArg H (push_id p).symm

omit [DecidableEq B] in
theorem push_ac (p : A × B × C → ℝ) :
    push (fun w => (w.1, w.2.2)) p = fun ac => ∑ b, p (ac.1, b, ac.2) := by
  funext ac
  rcases ac with ⟨a, c⟩
  simp [push, Finset.sum_filter, Fintype.sum_prod_type, Prod.mk.injEq, ite_and]

omit [DecidableEq A] in
theorem push_bc (p : A × B × C → ℝ) :
    push (fun w => (w.2.1, w.2.2)) p = fun bc => ∑ a, p (a, bc.1, bc.2) := by
  funext bc
  simp [push, Finset.sum_filter, Fintype.sum_prod_type]

omit [DecidableEq A] [DecidableEq B] in
theorem push_c (p : A × B × C → ℝ) :
    push (fun w => w.2.2) p = fun c => ∑ a, ∑ b, p (a, b, c) := by
  funext c
  simp [push, Finset.sum_filter, Fintype.sum_prod_type]

theorem conditionalMutualInformation_eq_condMI {p : A × B × C → ℝ} (hp : IsPMF p) :
    conditionalMutualInformation p =
      condMI (fun w => w.1) (fun w => w.2.1) (fun w => w.2.2) p := by
  unfold conditionalMutualInformation
  rw [← push_ac p, ← push_bc p, ← push_c p]
  rw [entropy_push_eq_Hvar hp, entropy_push_eq_Hvar hp, entropy_eq_H hp,
    entropy_push_eq_Hvar hp]
  unfold condMI
  congr 2
  exact congrArg H (push_id p).symm

theorem conditionalMutualInformation_push {p : Ω → ℝ} (hp : IsPMF p)
    (x : Ω → A) (y : Ω → B) (v : Ω → C) :
    conditionalMutualInformation (push (fun w => (x w, y w, v w)) p) = condMI x y v p := by
  rw [conditionalMutualInformation_eq_condMI (isPMF_push hp)]
  simp only [condMI, Hvar, push_push, Function.comp_def]

theorem push_vxy (p : A × B × C → ℝ) :
    push (fun w => (w.2.2, w.1, w.2.1)) p =
      fun vxy => p (vxy.2.1, vxy.2.2, vxy.1) := by
  funext vxy
  rcases vxy with ⟨v, x, y⟩
  simp [push, Finset.sum_filter, Fintype.sum_prod_type, Prod.mk.injEq, ite_and]

theorem push_vyx (p : A × B × C → ℝ) :
    push (fun w => (w.2.2, w.2.1, w.1)) p =
      fun vyx => p (vyx.2.2, vyx.2.1, vyx.1) := by
  funext vyx
  rcases vyx with ⟨v, y, x⟩
  simp [push, Finset.sum_filter, Fintype.sum_prod_type, Prod.mk.injEq, ite_and]

theorem latentError_eq_core {p : A × B × C → ℝ} (hp : IsPMF p) :
    latentError p =
      condMI (fun w => w.1) (fun w => w.2.1) (fun w => w.2.2) p
        + condMI (fun w => w.2.2) (fun w => w.1) (fun w => w.2.1) p
        + condMI (fun w => w.2.2) (fun w => w.2.1) (fun w => w.1) p := by
  unfold latentError
  rw [conditionalMutualInformation_eq_condMI hp, ← push_vxy p, ← push_vyx p,
    conditionalMutualInformation_push hp, conditionalMutualInformation_push hp]

theorem latentError_push {p : Ω → ℝ} (hp : IsPMF p)
    (x : Ω → A) (y : Ω → B) (v : Ω → C) :
    latentError (push (fun w => (x w, y w, v w)) p) =
      condMI x y v p + condMI v x y p + condMI v y x p := by
  rw [latentError_eq_core (isPMF_push hp)]
  simp only [condMI, Hvar, push_push, Function.comp_def]

end TableInformationProof
