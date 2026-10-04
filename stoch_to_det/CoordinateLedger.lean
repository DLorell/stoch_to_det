import stoch_to_det.RaceCancellation

/-!
# A direct coordinate-entropy ledger

Calibration bounds the average information that the rounded label carries
about each coordinate. Retaining both bounds reduces the cost of the two
conditional entropies from two to three halves.
-/

namespace stoch_to_det

open MeasureTheory

variable {α β : Type*} [Fintype α] [Fintype β]
  [DecidableEq α] [DecidableEq β]
variable {p : α × β → ℝ} (D : SeedSetup p)

private lemma coordinate_MI_source
    {Γ Δ : Type*} [Fintype Γ] [Fintype Δ] [DecidableEq Γ] [DecidableEq Δ]
    (f : α × β → Γ) (g : α × β → Δ) :
    MI (fun t : D.L.ι × (α × β) => f t.2) (fun t => g t.2) D.L.joint =
      MI f g p := by
  conv_rhs => rw [← cancellation_source_marginal D]
  unfold MI Hvar
  simp only [push_push, Function.comp_def]

private lemma coordinate_MI_graph (A : α × β → D.L.ι) :
    MI A (fun z => z) p = Hvar A p := by
  have h := Hvar_eq_of_leftInverse D.isPMF (fun z : α × β => z)
    (fun z => (A z, z)) Prod.snd (by intro z; rfl)
  change Hvar (fun z => (A z, z)) p = Hvar (fun z => z) p at h
  unfold MI
  rw [h]
  ring

private lemma coordinate_MI_condH
    {Γ : Type*} [Fintype Γ] [DecidableEq Γ]
    (A : α × β → D.L.ι) (g : α × β → Γ) :
    MI A g p = Hvar A p - condH A g p := by
  unfold MI condH
  ring

/-- The deterministic score, before averaging over the seed. -/
lemma winner_score_coordinate_identity (ε : D.L.ι → ℝ) :
    (winnerLatent D ε).score = Ixy p + (3 / 2 : ℝ) *
      (condH (winner D ε) Prod.fst p + condH (winner D ε) Prod.snd p) -
      (1 / 2 : ℝ) * (MI (winner D ε) Prod.fst p + MI (winner D ε) Prod.snd p) := by
  have hw := (winnerLatent D ε).score_sub_Ixy D.isPMF
  rw [cancellation_winner_latent_MI D ε (fun z => z),
    cancellation_winner_latent_MI D ε Prod.fst,
    cancellation_winner_latent_MI D ε Prod.snd,
    coordinate_MI_source D (winner D ε) (fun z => z),
    coordinate_MI_source D (winner D ε) Prod.fst,
    coordinate_MI_source D (winner D ε) Prod.snd,
    coordinate_MI_graph] at hw
  have hx := coordinate_MI_condH D (winner D ε) Prod.fst
  have hy := coordinate_MI_condH D (winner D ε) Prod.snd
  linarith

/-- Source-coordinate calibration survives averaging over the shared seed. -/
lemma average_winner_coordinate_MI_lower
    {Γ : Type*} [Fintype Γ] [DecidableEq Γ] (g : α × β → Γ) :
    MI Prod.fst (fun t : D.L.ι × (α × β) => g t.2) D.L.joint ≤
      ∫ ε, MI (winner D ε) g p ∂seedLaw D.L.ι := by
  have h := average_winner_information_lower D g
  simp_rw [coordinate_MI_source D] at h
  exact h

/-- The original stochastic score fixes the constant term of the new ledger. -/
lemma coordinate_information_balance :
    Ixy p - (1 / 2 : ℝ) *
      (MI Prod.fst (fun t : D.L.ι × (α × β) => t.2.1) D.L.joint +
       MI Prod.fst (fun t : D.L.ι × (α × β) => t.2.2) D.L.joint) =
      D.M - (1 / 2 : ℝ) * D.Bq := by
  have hs := D.L.score_sub_Ixy D.isPMF
  rw [D.optimal, D.tau_eq_M_add_Bq] at hs
  have hb := Bq_info_identity D
  linarith

/-- Direct conditional-entropy ledger; no assumption on cell information. -/
theorem T_le_coordinate_entropy_ledger :
    T p ≤ D.M - (1 / 2 : ℝ) * D.Bq + (3 / 2 : ℝ) *
      ((∫ ε, condH (winner D ε) Prod.fst p ∂seedLaw D.L.ι) +
       (∫ ε, condH (winner D ε) Prod.snd p ∂seedLaw D.L.ι)) := by
  let HX := fun ε => condH (winner D ε) Prod.fst p
  let HY := fun ε => condH (winner D ε) Prod.snd p
  let IX := fun ε => MI (winner D ε) Prod.fst p
  let IY := fun ε => MI (winner D ε) Prod.snd p
  have hHX : Integrable HX (seedLaw D.L.ι) :=
    integrable_winner_code D (fun A => condH A Prod.fst p)
  have hHY : Integrable HY (seedLaw D.L.ι) :=
    integrable_winner_code D (fun A => condH A Prod.snd p)
  have hIX : Integrable IX (seedLaw D.L.ι) :=
    integrable_winner_code D (fun A => MI A Prod.fst p)
  have hIY : Integrable IY (seedLaw D.L.ι) :=
    integrable_winner_code D (fun A => MI A Prod.snd p)
  have havg : (∫ ε, (winnerLatent D ε).score ∂seedLaw D.L.ι) =
      Ixy p + (3 / 2 : ℝ) * ((∫ ε, HX ε ∂seedLaw D.L.ι) +
        (∫ ε, HY ε ∂seedLaw D.L.ι)) -
      (1 / 2 : ℝ) * ((∫ ε, IX ε ∂seedLaw D.L.ι) +
        (∫ ε, IY ε ∂seedLaw D.L.ι)) := by
    simp_rw [winner_score_coordinate_identity D]
    rw [integral_sub
        (f := fun ε => Ixy p + (3 / 2 : ℝ) * (HX ε + HY ε))
        (g := fun ε => (1 / 2 : ℝ) * (IX ε + IY ε))
        ((integrable_const _).add ((hHX.add hHY).const_mul _))
        ((hIX.add hIY).const_mul _),
      integral_add (f := fun _ => Ixy p) (g := fun ε => (3 / 2 : ℝ) * (HX ε + HY ε))
        (integrable_const _) ((hHX.add hHY).const_mul _),
      integral_const_mul, integral_const_mul,
      integral_add hHX hHY, integral_add hIX hIY]
    simp
  have hx := average_winner_coordinate_MI_lower D Prod.fst
  have hy := average_winner_coordinate_MI_lower D Prod.snd
  have hbalance := coordinate_information_balance D
  have hbound : (∫ ε, (winnerLatent D ε).score ∂seedLaw D.L.ι) ≤
      D.M - (1 / 2 : ℝ) * D.Bq + (3 / 2 : ℝ) *
        ((∫ ε, condH (winner D ε) Prod.fst p ∂seedLaw D.L.ι) +
         (∫ ε, condH (winner D ε) Prod.snd p ∂seedLaw D.L.ι)) := by
    dsimp only [HX, HY, IX, IY] at havg
    linarith
  obtain ⟨ε, hε⟩ := exists_good_seed D _ (integrable_winnerScore D) hbound
  exact (T_le_score (winnerLatent D ε) (winnerLatent_isDet D ε)).trans hε

end stoch_to_det
