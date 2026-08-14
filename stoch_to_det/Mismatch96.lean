import stoch_to_det.Floor96
import stoch_to_det.DomFloor96
import stoch_to_det.Mismatch

/-! The calibrated near/far mismatch charge used by the standalone `96` ledger. -/

namespace stoch_to_det

universe u v

variable {α : Type u} {β : Type v} [Fintype α] [Fintype β]
  [DecidableEq α] [DecidableEq β]

theorem nearcollision_floor_96
    {S : Finset (α × β)} {w : α × β → ℝ}
    (hw : Feasible S w) (hS : IsConnected S)
    {q r : α × β → ℝ}
    (hq : IsContact S w q) (hr : IsContact S w r) (hne : q ≠ r)
    (hnear : hellingerSq q r ≤ delta96) :
    rho96 ≤ rhoHGR q ∧
    rho96 ≤ rhoHGR r ∧
    infoFloor96 ≤ Ixy q ∧
    infoFloor96 ≤ Ixy r := by
  have hqR := rho96_le_rhoHGR_of_contacts hw hS hq hr hne hnear
  have hrR := rho96_le_rhoHGR_of_contacts_right hw hS hq hr hne hnear
  exact ⟨hqR, hrR,
    infoFloor96_le_Ixy_of_contact hw hq hqR,
    infoFloor96_le_Ixy_of_contact hw hr hrR⟩

variable {p : α × β → ℝ} {D : SeedSetup p}

theorem mismatch_charge_96 (K : Clustering D) :
    K.dMis ≤ D.M / infoFloor96 +
      2 * Real.log 2 / delta96 * K.Sinfo := by
  apply mismatch_charge_of_hellinger_floor K delta96 infoFloor96
    delta96_pos infoFloor96_pos
  intro c d hcd hnear
  have hQne : K.Q c ≠ K.Q d := fun h => hcd (K.Q_injective h)
  exact (nearcollision_floor_96 D.feasible D.conn
    (K.Q_isContact c) (K.Q_isContact d) hQne hnear).2.2.1

end stoch_to_det
