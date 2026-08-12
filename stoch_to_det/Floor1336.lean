import stoch_to_det.Floor
import stoch_to_det.Constants1336

/-!
# Secant rigidity at the `1336` constants

This module instantiates the value-independent exact-secant argument from
`Floor` at `eta1336 = 13/36`.
-/

namespace stoch_to_det

open Lean Meta Elab Tactic

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

/-- Distinct `delta1336`-near contacts on a connected feasible support have
HGR maximal correlation at least `rho1336`, oriented toward the first contact. -/
theorem rho1336_le_rhoHGR_of_contacts
    {S : Finset (α × β)} {w : α × β → ℝ}
    (hw : Feasible S w) (hS : IsConnected S)
    {q r : α × β → ℝ}
    (hq : IsContact S w q) (hr : IsContact S w r) (hne : q ≠ r)
    (hnear : hellingerSq q r ≤ delta1336) :
    rho1336 ≤ rhoHGR q := by
  have hqs : support q = S := contact_support_eq hw hS hq
  have hrs : support r = S := contact_support_eq hw hS hr
  rw [rho1336_eq, eta1336_eq]
  run_tac do
    let goal ← getMainGoal
    let theoremExpr ← mkConstWithFreshMVarLevels
      "_private.stoch_to_det.Floor.0.stoch_to_det.rho_le_rhoHGR_of_contacts_param".toName
    let goals ← goal.apply theoremExpr
    replaceMainGoal goals
  · norm_num
  · norm_num
  · exact hw
  · exact hq
  · exact hr
  · exact hqs
  · exact hrs
  · exact hne
  · simpa only [delta1336_eq, eta1336_eq] using hnear

/-- The symmetric `r`-oriented form of `rho1336_le_rhoHGR_of_contacts`. -/
theorem rho1336_le_rhoHGR_of_contacts_right
    {S : Finset (α × β)} {w : α × β → ℝ}
    (hw : Feasible S w) (hS : IsConnected S)
    {q r : α × β → ℝ}
    (hq : IsContact S w q) (hr : IsContact S w r) (hne : q ≠ r)
    (hnear : hellingerSq q r ≤ delta1336) :
    rho1336 ≤ rhoHGR r := by
  have hnear_rev : hellingerSq r q ≤ delta1336 := by
    rw [hellingerSq_comm]
    exact hnear
  exact rho1336_le_rhoHGR_of_contacts
    hw hS hr hq hne.symm hnear_rev

end stoch_to_det
