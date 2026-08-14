import stoch_to_det.Race
import stoch_to_det.Ledger96

/-!
# Final assembly of the all-label shared-race estimate

Everything in this file is finite-source bookkeeping.  The analytic input is
the coordinate moment `clockCoordinateIntegral_le`, proved by the exact
winner/loser clock analysis in `Race.lean`.
-/

namespace stoch_to_det
namespace SharedRace

open Finset MeasureTheory

universe u

/-- The one analytic clock estimate still abstracted by this assembly file.

The cardinality hypothesis deliberately lives inside the proposition: the
singleton label alphabet is discharged without invoking any coordinate
analysis. -/
def HasClockCoordinateBound (κ : Type)
    [Fintype κ] [DecidableEq κ] [Nonempty κ] : Prop :=
  ∀ (π : κ → ℝ), IsPMF π → (∀ i, 0 < π i) →
    2 ≤ Fintype.card κ → ∀ i,
      (∫ E : κ → ℝ, clockCoordinateIntegrand π i E ∂clockLaw κ) ≤ π i

/-- Row-reference-loss assembly for one finite source context. -/
theorem clockSharedRaceEntropy_le
    {Ω : Type u} {κ : Type}
    [Fintype Ω] [Fintype κ] [DecidableEq Ω] [DecidableEq κ] [Nonempty κ]
    {μ : Ω → ℝ} {r : Ω → κ → ℝ}
    (hμ : IsPMF μ)
    (hr : ∀ z, μ z ≠ 0 → IsPMF (r z))
    (hrpos : ∀ z, μ z ≠ 0 → ∀ i, 0 < r z i)
    (hk : 2 ≤ Fintype.card κ)
    (hcoordinate : HasClockCoordinateBound κ) :
    clockSharedRaceEntropy μ r ≤
      2 * MI Prod.fst Prod.snd (posteriorJoint μ r) +
        categoricalMismatch μ r := by
  let π : κ → ℝ := posteriorMean μ r
  have hπ : IsPMF π := posteriorMean_isPMF_of_support hμ hr
  have hπpos : ∀ i, 0 < π i := posteriorMean_pos_of_support hμ hrpos
  have hcoord : ∀ i,
      (∫ E : κ → ℝ, clockCoordinateIntegrand π i E ∂clockLaw κ) ≤ π i :=
    hcoordinate π hπ hπpos hk
  apply clockSharedRaceEntropy_le_of_referenceLoss hμ hr hrpos
  · intro z hz
    exact integrable_log_inv_referencePMF_clockArgmin
      π (r z) hπ hπpos (hr z hz) (hrpos z hz) hk
  · intro z hz
    exact referenceLossIntegral_le_of_coordinate
      π (r z) hπ hπpos (hr z hz) (hrpos z hz) hk hcoord

/-- Nontrivial finite label alphabets satisfy the Gumbel shared-race theorem
as soon as the coordinate moment is available. -/
theorem hasSharedRaceBound_of_two_le_card
    {Ω : Type u} {κ : Type}
    [Fintype Ω] [Fintype κ] [DecidableEq Ω] [DecidableEq κ] [Nonempty κ]
    (hk : 2 ≤ Fintype.card κ)
    (hcoordinate : HasClockCoordinateBound κ) :
    HasSharedRaceBound Ω κ := by
  intro μ r hμ hr hrpos
  rw [sharedRaceEntropy_eq_clockSharedRaceEntropy hrpos]
  exact clockSharedRaceEntropy_le hμ hr hrpos hk hcoordinate

/-- Singleton/nontrivial split for the universal shared-race theorem. -/
theorem hasSharedRaceBound_of_clockCoordinateBound
    {Ω : Type u} {κ : Type}
    [Fintype Ω] [Fintype κ] [DecidableEq Ω] [DecidableEq κ] [Nonempty κ]
    (hcoordinate : HasClockCoordinateBound κ) :
    HasSharedRaceBound Ω κ := by
  classical
  by_cases hk : 2 ≤ Fintype.card κ
  · exact hasSharedRaceBound_of_two_le_card hk hcoordinate
  · have hcard : Fintype.card κ ≤ 1 := by omega
    exact @hasSharedRaceBound_of_subsingleton Ω κ _ _ _ _ _
      (Fintype.card_le_one_iff_subsingleton.mp hcard)

/-- Uniform coordinate interface, quantified over all finite nonempty label
alphabets exactly as required by the `96` ledger. -/
def UniversalClockCoordinateBound : Prop :=
  ∀ (κ : Type) [Fintype κ] [DecidableEq κ] [Nonempty κ],
    HasClockCoordinateBound κ

/-- The winner/loser pair-clock theorem supplies the coordinate interface for
every finite nonempty label alphabet. -/
theorem universalClockCoordinateBound : UniversalClockCoordinateBound :=
  fun _κ _ _ _ π hπ hπpos hk i =>
    clockCoordinateIntegral_le π hπ hπpos hk i

/-- The shared-race theorem for every source-supported strictly positive
posterior family, including the singleton label alphabet. -/
theorem hasSharedRaceBound
    {Ω : Type u} {κ : Type}
    [Fintype Ω] [Fintype κ] [DecidableEq Ω] [DecidableEq κ] [Nonempty κ] :
    HasSharedRaceBound Ω κ :=
  hasSharedRaceBound_of_clockCoordinateBound
    (universalClockCoordinateBound κ)

end SharedRace

/-- Parameterized `96` wiring through the fixed-context shared-race theorem;
its sole explicit argument is the universal analytic coordinate interface. -/
theorem T_le_96_of_universalClockCoordinateBound
    {α : Type u} {β : Type*}
    [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (hcoordinate : SharedRace.UniversalClockCoordinateBound)
    {p : α × β → ℝ} (hp : IsPMF p) :
    T p ≤ 96 * tau p :=
  T_le_96_of_sharedRaceBound
    (fun κ _ _ _ =>
      SharedRace.hasSharedRaceBound_of_clockCoordinateBound (hcoordinate κ)) hp

/-- The unconditional strict two-digit upper bound. -/
theorem T_le_96
    {α : Type u} {β : Type*}
    [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    {p : α × β → ℝ} (hp : IsPMF p) :
    T p ≤ 96 * tau p :=
  T_le_96_of_universalClockCoordinateBound
    SharedRace.universalClockCoordinateBound hp

end stoch_to_det
