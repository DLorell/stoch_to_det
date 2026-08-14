import stoch_to_det.Floor
import stoch_to_det.Constants96

/-! Hellinger-near contacts have the calibrated HGR floor used by `T_le_96`. -/

namespace stoch_to_det

variable {α β : Type*} [Fintype α] [Fintype β]
  [DecidableEq α] [DecidableEq β]

theorem rho96_le_rhoHGR_of_contacts
    {S : Finset (α × β)} {w : α × β → ℝ}
    (hw : Feasible S w) (hS : IsConnected S)
    {q r : α × β → ℝ}
    (hq : IsContact S w q) (hr : IsContact S w r) (hne : q ≠ r)
    (hnear : hellingerSq q r ≤ delta96) :
    rho96 ≤ rhoHGR q := by
  have hqs : support q = S := contact_support_eq hw hS hq
  have hrs : support r = S := contact_support_eq hw hS hr
  rw [rho96_eq]
  exact rho_le_rhoHGR_of_contacts_param_l2 eta96 eta96_pos
    two_mul_eta96_sq_lt_one hw hq hr hqs hrs hne
    (by simpa only [delta96_eq] using hnear)

theorem rho96_le_rhoHGR_of_contacts_right
    {S : Finset (α × β)} {w : α × β → ℝ}
    (hw : Feasible S w) (hS : IsConnected S)
    {q r : α × β → ℝ}
    (hq : IsContact S w q) (hr : IsContact S w r) (hne : q ≠ r)
    (hnear : hellingerSq q r ≤ delta96) :
    rho96 ≤ rhoHGR r := by
  have hnear_rev : hellingerSq r q ≤ delta96 := by
    rw [hellingerSq_comm]
    exact hnear
  exact rho96_le_rhoHGR_of_contacts
    hw hS hr hq hne.symm hnear_rev

end stoch_to_det
