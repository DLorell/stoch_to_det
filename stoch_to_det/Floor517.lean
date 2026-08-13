import stoch_to_det.Floor
import stoch_to_det.Constants517

/-!
# Secant rigidity at the `517` constants

This module instantiates the value-independent exact-secant argument from
`Floor` at `eta517 = 2/5`.
-/

namespace stoch_to_det

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

/-- Distinct `delta517`-near contacts on a connected feasible support have
HGR maximal correlation at least `rho517`, oriented toward the first contact. -/
theorem rho517_le_rhoHGR_of_contacts
    {S : Finset (α × β)} {w : α × β → ℝ}
    (hw : Feasible S w) (hS : IsConnected S)
    {q r : α × β → ℝ}
    (hq : IsContact S w q) (hr : IsContact S w r) (hne : q ≠ r)
    (hnear : hellingerSq q r ≤ delta517) :
    rho517 ≤ rhoHGR q := by
  have hqs : support q = S := contact_support_eq hw hS hq
  have hrs : support r = S := contact_support_eq hw hS hr
  rw [rho517_eq]
  exact rho_le_rhoHGR_of_contacts_param eta517 eta517_pos
    two_mul_eta517_sq_lt_one hw hq hr hqs hrs hne
    (by simpa only [delta517_eq] using hnear)

/-- The symmetric `r`-oriented form of `rho517_le_rhoHGR_of_contacts`. -/
theorem rho517_le_rhoHGR_of_contacts_right
    {S : Finset (α × β)} {w : α × β → ℝ}
    (hw : Feasible S w) (hS : IsConnected S)
    {q r : α × β → ℝ}
    (hq : IsContact S w q) (hr : IsContact S w r) (hne : q ≠ r)
    (hnear : hellingerSq q r ≤ delta517) :
    rho517 ≤ rhoHGR r := by
  have hnear_rev : hellingerSq r q ≤ delta517 := by
    rw [hellingerSq_comm]
    exact hnear
  exact rho517_le_rhoHGR_of_contacts
    hw hS hr hq hne.symm hnear_rev

end stoch_to_det
