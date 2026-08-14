import stoch_to_det.DomFloorCore
import stoch_to_det.Assembly96
import stoch_to_det.Floor

/-! Contact information floor at the calibration used by `T_le_96`. -/

namespace stoch_to_det

open Finset

variable {α β : Type*} [Fintype α] [Fintype β]
  [DecidableEq α] [DecidableEq β]

theorem contact_correlation_cap_96
    {S : Finset (α × β)} {w q : α × β → ℝ}
    (hq : IsPMF q) (hw : Feasible S w) (hcontact : IsContact S w q)
    {f : α → ℝ} {g : β → ℝ}
    (hf0 : ∑ x, mX q x * f x = 0)
    (hg0 : ∑ y, mY q y * g y = 0)
    (hf2 : ∑ x, mX q x * f x ^ 2 = 1)
    (hg2 : ∑ y, mY q y * g y ^ 2 = 1)
    (hK : Knat q ≤ floorNat96) :
    (∑ z, q z * f z.1 * g z.2) ≤ (4511 : ℝ) / 10000 := by
  rw [floorNat96_eq] at hK
  exact contact_correlation_cap_of_tail_param
    ((231 : ℝ) / 10000) ((4511 : ℝ) / 10000)
    hq hw hcontact hf0 hg0 hf2 hg2 tail_quartic_cell assembly_cap_96 hK

theorem rhoHGR_le_cap_96
    {S : Finset (α × β)} {w q : α × β → ℝ}
    (hw : Feasible S w) (hcontact : IsContact S w q)
    (hK : Knat q ≤ floorNat96) :
    rhoHGR q ≤ (4511 : ℝ) / 10000 := by
  let ι := {fg : (α → ℝ) × (β → ℝ) //
    (∑ x, mX q x * fg.1 x = 0) ∧ (∑ y, mY q y * fg.2 y = 0) ∧
    (∑ x, mX q x * fg.1 x ^ 2 = 1) ∧
      (∑ y, mY q y * fg.2 y ^ 2 = 1)}
  change (⨆ fg : ι, ∑ z, q z * fg.1.1 z.1 * fg.1.2 z.2) ≤
    (4511 : ℝ) / 10000
  apply Real.iSup_le
  · intro fg
    exact contact_correlation_cap_96 hcontact.1 hw hcontact
      fg.2.1 fg.2.2.1 fg.2.2.2.1 fg.2.2.2.2 hK
  · norm_num

theorem infoFloor96_le_Ixy_of_contact
    {S : Finset (α × β)} {w q : α × β → ℝ}
    (hw : Feasible S w) (hcontact : IsContact S w q)
    (hrho : rho96 ≤ rhoHGR q) :
    infoFloor96 ≤ Ixy q := by
  by_contra hnot
  have hIlt : Ixy q < infoFloor96 := lt_of_not_ge hnot
  have hlogpos : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hKle : Knat q ≤ floorNat96 := by
    calc
      Knat q = Real.log 2 * Ixy q := Knat_eq_log_two_mul_Ixy hcontact.1
      _ ≤ Real.log 2 * infoFloor96 :=
        mul_le_mul_of_nonneg_left hIlt.le hlogpos.le
      _ = floorNat96 := by
        unfold infoFloor96
        field_simp [hlogpos.ne']
  have hcap := rhoHGR_le_cap_96 hw hcontact hKle
  have hthreshold : rho96 ≤ (4511 : ℝ) / 10000 := hrho.trans hcap
  exact (not_lt_of_ge hthreshold) assembly_cap_96_lt_rho

end stoch_to_det
