import stoch_to_det.TableBoundProof

/-! The finite natural-latent theorem with explicit probability-table definitions in bits. -/

open scoped BigOperators
namespace NaturalLatentsFinite

variable {A B C : Type} [Fintype A] [Fintype B] [Fintype C]
  [DecidableEq A] [DecidableEq B] [DecidableEq C]

def Probability (p : A → ℝ) : Prop :=
  (∀ a, 0 ≤ p a) ∧ ∑ a, p a = 1

/-- H(X) in bits, directly from pX(x) = P(X=x). Here 0 log 0 = 0. -/
noncomputable def H (pX : A → ℝ) : ℝ :=
  -∑ x, pX x * (Real.log (pX x) / Real.log 2)

/-- H(X | Y) from the joint table pXY(x,y) = P(X=x,Y=y). -/
noncomputable def Hcond (pXY : A × B → ℝ) : ℝ :=
  H pXY - H (fun y => ∑ x, pXY (x, y))

/-- I(X;Y) = H(X) + H(Y) − H(X,Y). Summing rows/columns gives marginals. -/
noncomputable def MI (pXY : A × B → ℝ) : ℝ :=
  H (fun x => ∑ y, pXY (x, y)) + H (fun y => ∑ x, pXY (x, y)) - H pXY

/-- I(X;Y | Z) = H(X,Z) + H(Y,Z) − H(X,Y,Z) − H(Z). -/
noncomputable def CMI (pXYZ : A × B × C → ℝ) : ℝ :=
  H (fun (x, z) => ∑ y, pXYZ (x, y, z))
    + H (fun (y, z) => ∑ x, pXYZ (x, y, z))
    - H pXYZ - H (fun z => ∑ x, ∑ y, pXYZ (x, y, z))

/-- Stochastic natural-latent error: I(X;Y|V) + I(V;X|Y) + I(V;Y|X). -/
noncomputable def StochasticError (pXYV : A × B × C → ℝ) : ℝ :=
  CMI pXYV
    + CMI (fun (v, x, y) => pXYV (x, y, v))
    + CMI (fun (v, y, x) => pXYV (x, y, v))

/-- Deterministic error: I(X;Y|Γ) + H(Γ|X) + H(Γ|Y). -/
noncomputable def DeterministicError (pXYΓ : A × B × C → ℝ) : ℝ :=
  CMI pXYΓ
    + Hcond (fun (g, x) => ∑ y, pXYΓ (x, y, g))
    + Hcond (fun (g, y) => ∑ x, pXYΓ (x, y, g))

/-- Joint table of (X,Y,Γ): all probability at (x,y) goes to Γ(x,y). -/
def deterministicTable (pXY : A × B → ℝ) (Γ : A × B → C) : A × B × C → ℝ :=
  fun (x, y, g) => if Γ (x, y) = g then pXY (x, y) else 0

/-- One deterministic Γ works for every finite stochastic latent V.
The marginal condition says that pXYV and pXY describe the same (X,Y).
The supporting proof is in TableBoundProof; 47/5 = 9.4 exactly. -/
theorem natural_latents_linear_bound
    {pXY : A × B → ℝ} (hp : Probability pXY) :
    ∃ Γ : A × B → Fin (Fintype.card (A × B)),
      ∀ (k : ℕ) (pXYV : A × B × Fin k → ℝ),
        Probability pXYV → (∀ x y, ∑ v, pXYV (x, y, v) = pXY (x, y)) →
        DeterministicError (deterministicTable pXY Γ)
          ≤ (47 / 5 : ℝ) * StochasticError pXYV := by
  exact TableBoundProof.table_bound_entropy hp

end NaturalLatentsFinite
