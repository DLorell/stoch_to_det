import stoch_to_det.Scalar
import stoch_to_det.Cone
import stoch_to_det.SharedRace.Definitions
import stoch_to_det.SharedRace.ClockLaw
import stoch_to_det.SharedRace.CoordinateBound
import stoch_to_det.SharedRace.ReferenceLoss
import stoch_to_det.SharedRace.EntropyAssembly
import stoch_to_det.SharedRace.PairClockLaw
import Mathlib.InformationTheory.KullbackLeibler.ChainRule
import Mathlib.InformationTheory.KullbackLeibler.DataProcessing
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.Kernel.CompProdEqIff

/-!
# §§7–10. The race construction

The single obligation of the continuous tier: build the actual
`RaceQuantities` for any `SeedSetup` and `Clustering` — i.e. define the
four seed-level scalars and
prove Lemmas 7.2–7.5 (grouping, winner-entropy identity, exact race law,
chain split), Theorem 8.1 (`scalar ≤ S + κd`), Theorem 10.1
(`cone · ln 2 ≤ d`), and the `I ≤ H` cell-residual link of Theorem 12.1.

Intended concrete realizations:
* `winnerEntropy := ∫ H(A_ε ∣ L₀) d(seedLaw)` — at fixed `ε` the winner
  is a finite variable, so the integrand is a finite conditional entropy
  of the joint `(winner ε ∘ ·, id)`-pushforward of `L.joint`;
* `scalar` — contexts `(g, b)` are finite and `Law(U ∣ Z=z, B=b)` is the
  explicit `clockLawGiven b z` (Lemma 7.4), so `scalar` is a finite sum
  of `klDiv`s against the true conditional mixtures;
* `seedLeak` — KLs of restricted-and-normalized seed laws;
* `cone` — the context-integrated KL of the losing vector, or the
  remainder `seedLeak − scalar` with Lemma 7.5 proved for it.
-/

namespace stoch_to_det

universe u

open Finset MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

/-! ### Concrete realizations of the four quantities

The continuous informations are written in the finite-context KL form exposed
by `condMIcts`.  In both cases the final measure argument is the *true*
conditional mixture of the source laws, not an arbitrary reference measure.
-/

/-- `P(B=b ∣ C₀=g) = ∑_z Q_g(z) σ_b(z)`. -/
private noncomputable def scalarWinnerProb {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D) (g b : K.κ) : ℝ :=
  ∑ z, K.Q g z * K.sigma b z

/-- The global mass of a scalar context `(C₀ = g, B = b)`. -/
private noncomputable def scalarContextMass {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D) (g b : K.κ) : ℝ :=
  K.s g * scalarWinnerProb K g b

/-- The source posterior `ν_{gb}(z) ∝ Q_g(z) σ_b(z)`. -/
private noncomputable def scalarSource {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D) (g b : K.κ)
    (z : α × β) : ℝ :=
  K.Q g z * K.sigma b z / scalarWinnerProb K g b

/-- The true conditional marginal law of the winning raw clock in a context
`(C₀ = g, B = b)`. -/
private noncomputable def scalarClockMarginal {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D) (g b : K.κ) : Measure ℝ :=
  ∑ z, ENNReal.ofReal (scalarSource K g b z) • K.clockLawGiven b z

/-- `I(U; Z ∣ B, C₀)` in bits, expanded over the finite contexts `(g,b)`.
Lemma 7.4 supplies the conditional clock law `clockLawGiven`. -/
private noncomputable def raceScalar {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D) : ℝ :=
  condMIcts
    (fun z (gb : K.κ × K.κ) => K.s gb.1 * K.Q gb.1 z * K.sigma gb.2 z)
    (fun z (gb : K.κ × K.κ) => K.clockLawGiven gb.2 z)
    (fun (gb : K.κ × K.κ) => scalarClockMarginal K gb.1 gb.2)

/-! #### The exact duplicate grouping

`clusterFiber K c` is the set of labels in cluster `c`.  The grouped seed is
the within-fibre maximum of `log π + ε`; subtracting that maximum from every
coordinate records the within-cluster winner and all excesses, so no seed
information is discarded.
-/

private abbrev clusterFiber {p : α × β → ℝ} {D : SeedSetup p}
    (K : Clustering D) (c : K.κ) := {ℓ : D.L.ι // K.cl ℓ = c}

private instance clusterNonempty {p : α × β → ℝ} {D : SeedSetup p}
    (K : Clustering D) : Nonempty K.κ :=
  Nonempty.map K.cl (Latent.nonempty_ι D.L)

private instance clusterFiberNonempty {p : α × β → ℝ} {D : SeedSetup p}
    (K : Clustering D) (c : K.κ) : Nonempty (clusterFiber K c) := by
  obtain ⟨ℓ, hℓ⟩ := K.surj c
  exact ⟨⟨ℓ, hℓ⟩⟩

/-- The within-cluster winner `W_c`. -/
private noncomputable def groupedWithinWinner {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D) (ε : D.L.ι → ℝ) (c : K.κ) :
    clusterFiber K c :=
  Classical.choose (Finite.exists_max fun u : clusterFiber K c =>
    Real.log (D.L.prior u.1 / K.s c) + ε u.1)

/-- The grouped Gumbel `G̃_c = max_{ℓ∈c}(log π_{ℓ|c}+ε_ℓ)`. -/
private noncomputable def groupedG {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D) (ε : D.L.ι → ℝ) (c : K.κ) : ℝ :=
  Real.log (D.L.prior (groupedWithinWinner K ε c).1 / K.s c) +
    ε (groupedWithinWinner K ε c).1

/-- The within-cluster exponential excess coordinates
`e_u / π_{u|c} - min_v (e_v / π_{v|c})`.  The zero coordinate records the
winner; together with `groupedG` these recover the original seed. -/
private noncomputable def groupedResidual {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D) (ε : D.L.ι → ℝ)
    (c : K.κ) (u : clusterFiber K c) : ℝ :=
  Real.exp (-(Real.log (D.L.prior u.1 / K.s c) + ε u.1)) -
    Real.exp (-(groupedG K ε c))

/-- The cluster winner for a grouped seed. -/
private noncomputable def groupedClusterWinner {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D) (G : K.κ → ℝ)
    (z : α × β) : K.κ :=
  Classical.choose (Finite.exists_max fun c : K.κ =>
    Real.log (K.sigma c z) + G c)

/-- The two-stage label winner `(B,W_B)`. -/
private noncomputable def groupedLabelWinner {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D) (ε : D.L.ι → ℝ)
    (z : α × β) : D.L.ι :=
  if z ∈ support p then
    (groupedWithinWinner K ε
      (groupedClusterWinner K (groupedG K ε) z)).1
  else winner D ε z

/-- The grouped-Gumbel law conditioned on cluster `b` winning at `z`. -/
private noncomputable def clusterSeedLawGivenWinner {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D) (b : K.κ)
    (z : α × β) : Measure (K.κ → ℝ) :=
  if K.sigma b z = 0 then seedLaw K.κ
  else (ENNReal.ofReal (K.sigma b z))⁻¹ •
    (seedLaw K.κ).restrict {G | groupedClusterWinner K G z = b}

/-- The true grouped-seed marginal in the context `(B=b,C₀=g)`. -/
private noncomputable def clusterSeedContextMarginal {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D) (g b : K.κ) :
    Measure (K.κ → ℝ) :=
  ∑ z, ENNReal.ofReal (scalarSource K g b z) •
    clusterSeedLawGivenWinner K b z

/-- `I(G̃;Z ∣ B,C₀)` in bits.  Lemma 7.2(c) identifies this with the
label-seed expansion `raceSeedLeak`. -/
private noncomputable def raceClusterLeak {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D) : ℝ :=
  condMIcts
    (fun z (bg : K.κ × K.κ) => K.s bg.2 * K.Q bg.2 z * K.sigma bg.1 z)
    (fun z (bg : K.κ × K.κ) => clusterSeedLawGivenWinner K bg.1 z)
    (fun (bg : K.κ × K.κ) => clusterSeedContextMarginal K bg.2 bg.1)

/-! #### The conditional losing-clock channel

The cone calculation keeps the whole losing vector intact.  At fixed
`(g,b,u,z)` its law is a product of shifted unit exponentials; the marginal
below is again the true source mixture used by the golden formula.
-/

private abbrev losingIndex {p : α × β → ℝ} {D : SeedSetup p}
    (K : Clustering D) (b : K.κ) := {c : K.κ // c ≠ b}

private noncomputable def losingClockLaw {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D) (b : K.κ) (z : α × β)
    (u : ℝ) : Measure (losingIndex K b → ℝ) :=
  Measure.pi fun c : losingIndex K b =>
    (expMeasure 1).map
      (fun e => u * (K.sigma c.1 z / K.sigma b z) + e)

private noncomputable def losingReference {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D) (b : K.κ) :
    Measure (losingIndex K b → ℝ) :=
  Measure.pi fun _ : losingIndex K b => expMeasure 1

/-- `D_{gb}(u)=∑_z Q_g(z)e^{-u/σ_b(z)}`, the density of `(B=b,U=u)`
conditional on `C₀=g`. -/
private noncomputable def coneContextDensity {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D) (g b : K.κ) (u : ℝ) : ℝ :=
  ∑ z, K.Q g z * Real.exp (-u / K.sigma b z)

/-- The exact source posterior `ν_{gbu}`. -/
private noncomputable def coneSource {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D) (g b : K.κ) (u : ℝ)
    (z : α × β) : ℝ :=
  K.Q g z * Real.exp (-u / K.sigma b z) / coneContextDensity K g b u

/-- The true conditional output mixture of the losing vector. -/
private noncomputable def losingClockMarginal {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D) (g b : K.κ) (u : ℝ) :
    Measure (losingIndex K b → ℝ) :=
  ∑ z, ENNReal.ofReal (coneSource K g b u z) • losingClockLaw K b z u

/-- The single-context losing-vector information in nats. -/
private noncomputable def coneContextInfoNats {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D) (g b : K.κ) (u : ℝ) : ℝ :=
  ∑ z, coneSource K g b u z *
    (klDiv (losingClockLaw K b z u)
      (losingClockMarginal K g b u)).toReal

/-- The exact integral of the conditional losing-vector channel, in nats. -/
private noncomputable def integratedConeNats {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D) : ℝ :=
  ∑ g, K.s g * ∑ b,
    ∫ u in Set.Ioi (0 : ℝ),
      coneContextDensity K g b u * coneContextInfoNats K g b u

/-- Joint mass of `(Z=z, A=a, L₀=ℓ₀)` after averaging the seed.  Winner
calibration identifies the last factor with `P(A=a ∣ Z=z)`. -/
private noncomputable def seedContextJoint {p : α × β → ℝ}
    (D : SeedSetup p) (a ℓ₀ : D.L.ι) (z : α × β) : ℝ :=
  D.L.joint (ℓ₀, z) * D.post a z

/-- The mass of the finite conditioning context `(A=a,L₀=ℓ₀)`. -/
private noncomputable def seedContextMass {p : α × β → ℝ}
    (D : SeedSetup p) (a ℓ₀ : D.L.ι) : ℝ :=
  ∑ z, seedContextJoint D a ℓ₀ z

/-- The seed law conditioned on the event that the race at `z` is won by
`a`.  The zero-posterior branch is irrelevant to the KL expansion and gives a
total definition on the ambient finite alphabets. -/
private noncomputable def seedLawGivenWinner {p : α × β → ℝ}
    (D : SeedSetup p) (a : D.L.ι) (z : α × β) : Measure (D.L.ι → ℝ) :=
  if D.post a z = 0 then seedLaw D.L.ι
  else (ENNReal.ofReal (D.post a z))⁻¹ •
    (seedLaw D.L.ι).restrict {ε | winner D ε z = a}

/-- The true conditional marginal seed law in the context `(A=a,L₀=ℓ₀)`. -/
private noncomputable def seedContextMarginal {p : α × β → ℝ}
    (D : SeedSetup p) (a ℓ₀ : D.L.ι) : Measure (D.L.ι → ℝ) :=
  ∑ z, ENNReal.ofReal
      (seedContextJoint D a ℓ₀ z / seedContextMass D a ℓ₀) •
        seedLawGivenWinner D a z

/-- `I(ε; Z ∣ A,L₀)` in bits, as KLs between normalized restrictions of
`seedLaw` and their true context mixtures. -/
private noncomputable def raceSeedLeak {p : α × β → ℝ}
    (D : SeedSetup p) : ℝ :=
  condMIcts
    (fun z (aℓ₀ : D.L.ι × D.L.ι) => seedContextJoint D aℓ₀.1 aℓ₀.2 z)
    (fun z (aℓ₀ : D.L.ι × D.L.ι) => seedLawGivenWinner D aℓ₀.1 z)
    (fun (aℓ₀ : D.L.ι × D.L.ι) => seedContextMarginal D aℓ₀.1 aℓ₀.2)

/-- `H(A_ε ∣ L₀)` averaged over the shared-Gumbel seed. -/
private noncomputable def raceWinnerEntropy {p : α × β → ℝ}
    (D : SeedSetup p) : ℝ :=
  ∫ ε, condH (fun w => winner D ε w.2) Prod.fst D.L.joint
    ∂(seedLaw D.L.ι)

/-- The cone term is the exact chain-rule remainder.  Its mathematical
content is the data-processing inequality `raceScalar ≤ raceSeedLeak` and the
orthant estimate below. -/
private noncomputable def raceCone {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D) : ℝ :=
  raceSeedLeak D - raceScalar K

/-- The fixed-seed integrand whose average is `Rcell D`.  Naming it here keeps
the fusion and integration parts of `rcell_le` separate. -/
private noncomputable def raceCellIntegrand {p : α × β → ℝ}
    (D : SeedSetup p) (ε : D.L.ι → ℝ) : ℝ :=
  ∑ a, ∑ b, D.L.prior b *
    (∑ z ∈ cell D ε a, D.L.comp b z) *
    Gdef (support p) D.w (fun z =>
      if winner D ε z = a then
        D.L.comp b z / ∑ z' ∈ cell D ε a, D.L.comp b z'
      else 0)

/-! ### Elementary positivity and definitional identities -/

private lemma racePost_nonneg {p : α × β → ℝ} (D : SeedSetup p)
    (a : D.L.ι) (z : α × β) : 0 ≤ D.post a z := by
  unfold SeedSetup.post
  exact div_nonneg
    (mul_nonneg (D.L.prior_isPMF.nonneg a) ((D.L.comp_isPMF a).nonneg z))
    (D.isPMF.nonneg z)

private lemma clusterMass_nonneg {p : α × β → ℝ} {D : SeedSetup p}
    (K : Clustering D) (g : K.κ) : 0 ≤ K.s g := by
  unfold Clustering.s
  exact Finset.sum_nonneg fun a _ => D.L.prior_isPMF.nonneg a

private theorem clusterMass_pos {p : α × β → ℝ} {D : SeedSetup p}
    (K : Clustering D) (g : K.κ) : 0 < K.s g := by
  obtain ⟨ℓ, hℓ⟩ := K.surj g
  unfold Clustering.s
  apply Finset.sum_pos'
  · intro a _
    exact D.L.prior_isPMF.nonneg a
  · exact ⟨ℓ, by simp [hℓ], D.prior_pos ℓ⟩

private lemma raceSigma_nonneg {p : α × β → ℝ} {D : SeedSetup p}
    (K : Clustering D) (b : K.κ) (z : α × β) : 0 ≤ K.sigma b z := by
  unfold Clustering.sigma
  exact Finset.sum_nonneg fun a _ => racePost_nonneg D a z

private theorem raceSigma_sum_eq_one {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D) (z : α × β)
    (hz : z ∈ support p) : ∑ b, K.sigma b z = 1 := by
  have hp : p z ≠ 0 := by simpa [support] using hz
  calc
    (∑ b, K.sigma b z) =
        ∑ b, ∑ ℓ ∈ univ.filter (fun ℓ => K.cl ℓ = b), D.post ℓ z := by
      rfl
    _ = ∑ ℓ, D.post ℓ z := by
      simpa using Finset.sum_fiberwise (univ : Finset D.L.ι) K.cl
        (fun ℓ => D.post ℓ z)
    _ = (∑ ℓ, D.L.prior ℓ * D.L.comp ℓ z) / p z := by
      simp only [SeedSetup.post, Finset.sum_div]
    _ = p z / p z := by rw [D.L.mixture z]
    _ = 1 := div_self hp

private theorem clusterWeight_eq_pSigma {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D) (g : K.κ) (z : α × β) :
    K.s g * K.Q g z = p z * K.sigma g z := by
  by_cases hp : p z = 0
  · have hz : z ∉ support p := by simp [support, hp]
    have hQ : K.Q g z = 0 := (K.Q_isContact g).2.1 z hz
    simp [hp, hQ]
  · have hfiber :
        K.s g * K.Q g z =
          ∑ ℓ ∈ univ.filter (fun ℓ => K.cl ℓ = g),
            D.L.prior ℓ * D.L.comp ℓ z := by
      unfold Clustering.s Clustering.Q
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro ℓ hℓ
      have hcl : K.cl ℓ =
          K.cl (Classical.choose (K.surj g)) :=
        (Finset.mem_filter.mp hℓ).2.trans
          (Classical.choose_spec (K.surj g)).symm
      rw [(K.spec _ _).mp hcl]
    calc
      K.s g * K.Q g z =
          ∑ ℓ ∈ univ.filter (fun ℓ => K.cl ℓ = g),
            D.L.prior ℓ * D.L.comp ℓ z := hfiber
      _ = ∑ ℓ ∈ univ.filter (fun ℓ => K.cl ℓ = g),
          p z * D.post ℓ z := by
        apply Finset.sum_congr rfl
        intro ℓ _
        unfold SeedSetup.post
        field_simp
      _ = p z * K.sigma g z := by
        unfold Clustering.sigma
        rw [Finset.mul_sum]

private lemma seedContextJoint_nonneg {p : α × β → ℝ} (D : SeedSetup p)
    (a ℓ₀ : D.L.ι) (z : α × β) : 0 ≤ seedContextJoint D a ℓ₀ z := by
  unfold seedContextJoint Latent.joint
  exact mul_nonneg
    (mul_nonneg (D.L.prior_isPMF.nonneg ℓ₀) ((D.L.comp_isPMF ℓ₀).nonneg z))
    (racePost_nonneg D a z)

private theorem seedContextMass_pos {p : α × β → ℝ}
    (D : SeedSetup p) (a ℓ₀ : D.L.ι) :
    0 < seedContextMass D a ℓ₀ := by
  have hsum : (∑ z, D.L.comp ℓ₀ z) ≠ 0 := by
    have htotal : ∑ z, D.L.comp ℓ₀ z = 1 := by
      simpa [mass] using (D.L.comp_isPMF ℓ₀).total
    rw [htotal]
    norm_num
  obtain ⟨z, _, hz0⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum
  have hz0pos : 0 < D.L.comp ℓ₀ z :=
    lt_of_le_of_ne ((D.L.comp_isPMF ℓ₀).nonneg z) (Ne.symm hz0)
  have hsupp0 := contact_support_eq D.feasible D.conn
    (D.contact ℓ₀ (D.prior_pos ℓ₀).ne')
  have hzComp0 : z ∈ support (D.L.comp ℓ₀) := by
    simpa [support] using hz0
  have hz : z ∈ support p := by
    rw [← hsupp0]
    exact hzComp0
  have hp : 0 < p z := by
    exact lt_of_le_of_ne (D.isPMF.nonneg z)
      (Ne.symm (by simpa [support] using hz))
  have hsuppA := contact_support_eq D.feasible D.conn
    (D.contact a (D.prior_pos a).ne')
  have hzCompA : z ∈ support (D.L.comp a) := by
    rw [hsuppA]
    exact hz
  have hcompA : 0 < D.L.comp a z :=
    lt_of_le_of_ne ((D.L.comp_isPMF a).nonneg z)
      (Ne.symm (by simpa [support] using hzCompA))
  have hpost : 0 < D.post a z := by
    unfold SeedSetup.post
    exact div_pos (mul_pos (D.prior_pos a) hcompA) hp
  unfold seedContextMass
  apply Finset.sum_pos'
  · intro z _
    exact seedContextJoint_nonneg D a ℓ₀ z
  · unfold seedContextJoint Latent.joint
    exact ⟨z, Finset.mem_univ z,
      mul_pos (mul_pos (D.prior_pos ℓ₀) hz0pos) hpost⟩

private theorem seedSource_isPMF {p : α × β → ℝ}
    (D : SeedSetup p) (a ℓ₀ : D.L.ι) :
    IsPMF (fun z => seedContextJoint D a ℓ₀ z / seedContextMass D a ℓ₀) := by
  have hmass := seedContextMass_pos D a ℓ₀
  constructor
  · intro z
    exact div_nonneg (seedContextJoint_nonneg D a ℓ₀ z) hmass.le
  · unfold mass
    rw [← Finset.sum_div]
    change seedContextMass D a ℓ₀ / seedContextMass D a ℓ₀ = 1
    exact div_self hmass.ne'

private theorem coneContextDensity_pos {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D) (g b : K.κ) (u : ℝ) :
    0 < coneContextDensity K g b u := by
  have hsum : (∑ z, K.Q g z) ≠ 0 := by
    have htotal : ∑ z, K.Q g z = 1 := by
      simpa [mass] using (K.Q_isContact g).1.total
    rw [htotal]
    norm_num
  obtain ⟨z, _, hQz⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum
  have hQpos : 0 < K.Q g z :=
    lt_of_le_of_ne ((K.Q_isContact g).1.nonneg z) (Ne.symm hQz)
  unfold coneContextDensity
  apply Finset.sum_pos'
  · intro z _
    exact mul_nonneg ((K.Q_isContact g).1.nonneg z) (Real.exp_nonneg _)
  · exact ⟨z, Finset.mem_univ z, mul_pos hQpos (Real.exp_pos _)⟩

private theorem coneSource_isPMF {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D) (g b : K.κ) (u : ℝ) :
    IsPMF (coneSource K g b u) := by
  have hden := coneContextDensity_pos K g b u
  constructor
  · intro z
    unfold coneSource
    exact div_nonneg
      (mul_nonneg ((K.Q_isContact g).1.nonneg z) (Real.exp_nonneg _)) hden.le
  · unfold mass coneSource
    rw [← Finset.sum_div]
    change coneContextDensity K g b u / coneContextDensity K g b u = 1
    exact div_self hden.ne'

private theorem coneContextInfoNats_nonneg {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D) (g b : K.κ) (u : ℝ) :
    0 ≤ coneContextInfoNats K g b u := by
  unfold coneContextInfoNats
  exact Finset.sum_nonneg fun z _ =>
    mul_nonneg ((coneSource_isPMF K g b u).nonneg z) ENNReal.toReal_nonneg

private theorem integratedConeNats_nonneg {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D) :
    0 ≤ integratedConeNats K := by
  unfold integratedConeNats
  apply Finset.sum_nonneg
  intro g _
  apply mul_nonneg (clusterMass_nonneg K g)
  apply Finset.sum_nonneg
  intro b _
  exact integral_nonneg fun u =>
    mul_nonneg (coneContextDensity_pos K g b u).le
      (coneContextInfoNats_nonneg K g b u)

/-- The exact split is definitional because `raceCone` is the chain-rule
remainder. -/
private theorem race_chain_split {p : α × β → ℝ} {D : SeedSetup p}
    (K : Clustering D) : raceSeedLeak D = raceScalar K + raceCone K := by
  unfold raceCone
  ring

private theorem raceScalar_nonneg {p : α × β → ℝ} {D : SeedSetup p}
    (K : Clustering D) : 0 ≤ raceScalar K := by
  unfold raceScalar condMIcts
  apply div_nonneg
  · apply Finset.sum_nonneg
    intro gb _
    apply Finset.sum_nonneg
    intro z _
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (clusterMass_nonneg K gb.1)
          ((K.Q_isContact gb.1).1.nonneg z))
        (raceSigma_nonneg K gb.2 z))
      ENNReal.toReal_nonneg
  · exact (Real.log_pos one_lt_two).le

private theorem raceSeedLeak_nonneg {p : α × β → ℝ} (D : SeedSetup p) :
    0 ≤ raceSeedLeak D := by
  unfold raceSeedLeak condMIcts
  apply div_nonneg
  · apply Finset.sum_nonneg
    intro aℓ₀ _
    apply Finset.sum_nonneg
    intro z _
    exact mul_nonneg (seedContextJoint_nonneg D aℓ₀.1 aℓ₀.2 z)
      ENNReal.toReal_nonneg
  · exact (Real.log_pos one_lt_two).le

/-! ### Finiteness of the KL expansions

Only positive-mass summands need a finiteness assertion; all remaining
summands have zero coefficient in `condMIcts`.
-/

private theorem isFiniteMeasure_finset_mixture
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (r : ι → ℝ) (μ : ι → Measure Ω)
    (hfinite : ∀ i, r i ≠ 0 → μ i Set.univ < ⊤) :
    IsFiniteMeasure (∑ i, ENNReal.ofReal (r i) • μ i) := by
  constructor
  rw [show (∑ i, ENNReal.ofReal (r i) • μ i) Set.univ =
      ∑ i, (ENNReal.ofReal (r i) • μ i) Set.univ by simp]
  rw [ENNReal.sum_lt_top]
  intro i _
  rw [Measure.smul_apply, smul_eq_mul]
  by_cases hr : r i = 0
  · simp [hr]
  · exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hfinite i hr)

/-- A positive component of a finite mixture has finite KL divergence to the
mixture.  The likelihood ratio is bounded above by the reciprocal mixture
weight; its negative part is controlled by `exp (-llr)`. -/
private theorem klDiv_ne_top_of_pos_smul_le
    {Ω : Type*} [MeasurableSpace Ω] (μ ν : Measure Ω)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (c : ℝ≥0∞)
    (hc : c ≠ 0) (hcTop : c ≠ ⊤) (hle : c • μ ≤ ν) :
    klDiv μ ν ≠ ⊤ := by
  have hcμν : c • μ ≪ ν := Measure.absolutelyContinuous_of_le hle
  have hμcμ : μ ≪ c • μ := Measure.absolutelyContinuous_smul hc
  have hμν : μ ≪ ν := hμcμ.trans hcμν
  have hrn : (c • μ).rnDeriv ν ≤ᵐ[ν] 1 :=
    Measure.rnDeriv_le_one_of_le hle
  have hscale := llr_smul_left hμν c hc hcTop
  have hupper : ∀ᵐ x ∂μ, llr μ ν x ≤ -Real.log c.toReal := by
    filter_upwards [hscale, hμν.ae_le hrn] with x hscaleX hrnX
    have hrnReal : ((c • μ).rnDeriv ν x).toReal ≤ 1 := by
      simpa using ENNReal.toReal_mono ENNReal.one_ne_top hrnX
    have hscaled : llr (c • μ) ν x ≤ 0 := by
      exact Real.log_nonpos ENNReal.toReal_nonneg hrnReal
    rw [hscaleX] at hscaled
    linarith
  have hexp : Integrable (fun x => Real.exp (-llr μ ν x)) μ := by
    exact (Measure.integrable_toReal_rnDeriv (μ := ν) (ν := μ)).congr
      (exp_neg_llr hμν).symm
  let C : ℝ := -Real.log c.toReal
  have hdom : Integrable (fun x => |C| + Real.exp (-llr μ ν x)) μ :=
    (integrable_const |C|).add hexp
  have hbound : ∀ᵐ x ∂μ,
      ‖llr μ ν x‖ ≤ |C| + Real.exp (-llr μ ν x) := by
    filter_upwards [hupper] with x hx
    change |llr μ ν x| ≤ |C| + Real.exp (-llr μ ν x)
    change llr μ ν x ≤ C at hx
    by_cases hnonneg : 0 ≤ llr μ ν x
    · rw [abs_of_nonneg hnonneg]
      exact (hx.trans (le_abs_self C)).trans
        (le_add_of_nonneg_right (Real.exp_nonneg _))
    · rw [abs_of_nonpos (le_of_not_ge hnonneg)]
      have hexpBound := Real.add_one_le_exp (-llr μ ν x)
      have hneg : -llr μ ν x ≤ Real.exp (-llr μ ν x) := by linarith
      exact hneg.trans (le_add_of_nonneg_left (abs_nonneg C))
  exact klDiv_ne_top hμν
    (hdom.mono' (stronglyMeasurable_llr μ ν).aestronglyMeasurable hbound)

private theorem scalarClock_klDiv_ne_top {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D) (g b : K.κ) (z : α × β)
    (hz : 0 < K.Q g z * K.sigma b z) :
    klDiv (K.clockLawGiven b z) (scalarClockMarginal K g b) ≠ ⊤ := by
  have hP : 0 < scalarWinnerProb K g b := by
    unfold scalarWinnerProb
    apply Finset.sum_pos'
    · intro z _
      exact mul_nonneg ((K.Q_isContact g).1.nonneg z)
        (raceSigma_nonneg K b z)
    · exact ⟨z, Finset.mem_univ z, hz⟩
  have hsource : 0 < scalarSource K g b z := by
    unfold scalarSource
    exact div_pos hz hP
  have hsigma : 0 < K.sigma b z := by
    exact lt_of_le_of_ne (raceSigma_nonneg K b z)
      (Ne.symm (mul_ne_zero_iff.mp hz.ne').2)
  letI : IsProbabilityMeasure (K.clockLawGiven b z) := by
    unfold Clustering.clockLawGiven
    exact isProbabilityMeasure_expMeasure (one_div_pos.mpr hsigma)
  letI : IsFiniteMeasure (scalarClockMarginal K g b) := by
    unfold scalarClockMarginal
    apply isFiniteMeasure_finset_mixture
    intro z' hz'
    have hnum : K.Q g z' * K.sigma b z' ≠ 0 := by
      intro hzero
      apply hz'
      unfold scalarSource
      rw [hzero]
      simp
    have hsigma' : 0 < K.sigma b z' :=
      lt_of_le_of_ne (raceSigma_nonneg K b z')
        (Ne.symm (mul_ne_zero_iff.mp hnum).2)
    letI : IsProbabilityMeasure (K.clockLawGiven b z') := by
      unfold Clustering.clockLawGiven
      exact isProbabilityMeasure_expMeasure (one_div_pos.mpr hsigma')
    exact measure_lt_top _ _
  let c : ℝ≥0∞ := ENNReal.ofReal (scalarSource K g b z)
  have hc : c ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hsource
  have hcTop : c ≠ ⊤ := ENNReal.ofReal_ne_top
  have hle : c • K.clockLawGiven b z ≤ scalarClockMarginal K g b := by
    unfold scalarClockMarginal
    exact Finset.single_le_sum (fun z _ => Measure.zero_le _)
      (Finset.mem_univ z)
  exact klDiv_ne_top_of_pos_smul_le _ _ c hc hcTop hle

private theorem seedWinner_klDiv_ne_top {p : α × β → ℝ}
    (D : SeedSetup p) (a ℓ₀ : D.L.ι) (z : α × β)
    (hz : 0 < seedContextJoint D a ℓ₀ z) :
    klDiv (seedLawGivenWinner D a z) (seedContextMarginal D a ℓ₀) ≠ ⊤ := by
  have hjoint : seedContextJoint D a ℓ₀ z ≠ 0 := hz.ne'
  have hpostNe : D.post a z ≠ 0 := by
    intro hpost
    apply hjoint
    unfold seedContextJoint
    simp [hpost]
  have hpost : 0 < D.post a z :=
    lt_of_le_of_ne (racePost_nonneg D a z) (Ne.symm hpostNe)
  letI : IsFiniteMeasure (seedLawGivenWinner D a z) := by
    constructor
    unfold seedLawGivenWinner
    rw [if_neg hpostNe, Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top
      (ENNReal.inv_lt_top.mpr (ENNReal.ofReal_pos.mpr hpost))
      (measure_lt_top _ _)
  letI : IsFiniteMeasure (seedContextMarginal D a ℓ₀) := by
    unfold seedContextMarginal
    apply isFiniteMeasure_finset_mixture
    intro z' hweight
    have hjoint' : seedContextJoint D a ℓ₀ z' ≠ 0 := by
      intro hzero
      apply hweight
      rw [hzero]
      simp
    have hpostNe' : D.post a z' ≠ 0 := by
      intro hpost'
      apply hjoint'
      unfold seedContextJoint
      simp [hpost']
    have hpost' : 0 < D.post a z' :=
      lt_of_le_of_ne (racePost_nonneg D a z') (Ne.symm hpostNe')
    unfold seedLawGivenWinner
    rw [if_neg hpostNe', Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top
      (ENNReal.inv_lt_top.mpr (ENNReal.ofReal_pos.mpr hpost'))
      (measure_lt_top _ _)
  have hsource : 0 < seedContextJoint D a ℓ₀ z / seedContextMass D a ℓ₀ :=
    div_pos hz (seedContextMass_pos D a ℓ₀)
  let c : ℝ≥0∞ :=
    ENNReal.ofReal (seedContextJoint D a ℓ₀ z / seedContextMass D a ℓ₀)
  have hc : c ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hsource
  have hcTop : c ≠ ⊤ := ENNReal.ofReal_ne_top
  have hle : c • seedLawGivenWinner D a z ≤ seedContextMarginal D a ℓ₀ := by
    unfold seedContextMarginal
    exact Finset.single_le_sum (fun z _ => Measure.zero_le _)
      (Finset.mem_univ z)
  exact klDiv_ne_top_of_pos_smul_le _ _ c hc hcTop hle

private theorem clusterSeed_klDiv_ne_top {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D) (g b : K.κ) (z : α × β)
    (hz : 0 < K.Q g z * K.sigma b z) :
    klDiv (clusterSeedLawGivenWinner K b z)
      (clusterSeedContextMarginal K g b) ≠ ⊤ := by
  have hP : 0 < scalarWinnerProb K g b := by
    unfold scalarWinnerProb
    apply Finset.sum_pos'
    · intro z _
      exact mul_nonneg ((K.Q_isContact g).1.nonneg z)
        (raceSigma_nonneg K b z)
    · exact ⟨z, Finset.mem_univ z, hz⟩
  have hsource : 0 < scalarSource K g b z := by
    unfold scalarSource
    exact div_pos hz hP
  have hsigma : 0 < K.sigma b z :=
    lt_of_le_of_ne (raceSigma_nonneg K b z)
      (Ne.symm (mul_ne_zero_iff.mp hz.ne').2)
  letI : IsFiniteMeasure (clusterSeedLawGivenWinner K b z) := by
    constructor
    unfold clusterSeedLawGivenWinner
    rw [if_neg hsigma.ne', Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top
      (ENNReal.inv_lt_top.mpr (ENNReal.ofReal_pos.mpr hsigma))
      (measure_lt_top _ _)
  letI : IsFiniteMeasure (clusterSeedContextMarginal K g b) := by
    unfold clusterSeedContextMarginal
    apply isFiniteMeasure_finset_mixture
    intro z' hweight
    have hnum : K.Q g z' * K.sigma b z' ≠ 0 := by
      intro hzero
      apply hweight
      unfold scalarSource
      rw [hzero]
      simp
    have hsigma' : 0 < K.sigma b z' :=
      lt_of_le_of_ne (raceSigma_nonneg K b z')
        (Ne.symm (mul_ne_zero_iff.mp hnum).2)
    unfold clusterSeedLawGivenWinner
    rw [if_neg hsigma'.ne', Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top
      (ENNReal.inv_lt_top.mpr (ENNReal.ofReal_pos.mpr hsigma'))
      (measure_lt_top _ _)
  let c : ℝ≥0∞ := ENNReal.ofReal (scalarSource K g b z)
  have hc : c ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hsource
  have hcTop : c ≠ ⊤ := ENNReal.ofReal_ne_top
  have hle : c • clusterSeedLawGivenWinner K b z ≤
      clusterSeedContextMarginal K g b := by
    unfold clusterSeedContextMarginal
    exact Finset.single_le_sum (fun z _ => Measure.zero_le _)
      (Finset.mem_univ z)
  exact klDiv_ne_top_of_pos_smul_le _ _ c hc hcTop hle

private theorem losingClockLaw_isProbability {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D) (b : K.κ) (z : α × β)
    (hz : z ∈ support p) (u : ℝ) :
    IsProbabilityMeasure (losingClockLaw K b z u) := by
  letI : IsProbabilityMeasure (expMeasure 1) :=
    isProbabilityMeasure_expMeasure zero_lt_one
  letI (c : losingIndex K b) : IsProbabilityMeasure
      ((expMeasure 1).map
        (fun e => u * (K.sigma c.1 z / K.sigma b z) + e)) := by
    apply Measure.isProbabilityMeasure_map
    exact (measurable_const.add measurable_id).aemeasurable
  unfold losingClockLaw
  infer_instance

private theorem losingClock_klDiv_ne_top {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D) (g b : K.κ) (u : ℝ)
    (z : α × β) (hz : 0 < coneSource K g b u z) :
    klDiv (losingClockLaw K b z u) (losingClockMarginal K g b u) ≠ ⊤ := by
  have hQne : K.Q g z ≠ 0 := by
    intro hQ
    apply hz.ne'
    unfold coneSource
    simp [hQ]
  have hzSupp : z ∈ support p := by
    by_contra hsupp
    exact hQne ((K.Q_isContact g).2.1 z hsupp)
  letI : IsProbabilityMeasure (losingClockLaw K b z u) :=
    losingClockLaw_isProbability K b z hzSupp u
  letI : IsFiniteMeasure (losingClockMarginal K g b u) := by
    unfold losingClockMarginal
    apply isFiniteMeasure_finset_mixture
    intro z' hweight
    have hQne' : K.Q g z' ≠ 0 := by
      intro hQ
      apply hweight
      unfold coneSource
      simp [hQ]
    have hzSupp' : z' ∈ support p := by
      by_contra hsupp
      exact hQne' ((K.Q_isContact g).2.1 z' hsupp)
    letI : IsProbabilityMeasure (losingClockLaw K b z' u) :=
      losingClockLaw_isProbability K b z' hzSupp' u
    exact measure_lt_top _ _
  let c : ℝ≥0∞ := ENNReal.ofReal (coneSource K g b u z)
  have hc : c ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hz
  have hcTop : c ≠ ⊤ := ENNReal.ofReal_ne_top
  have hle : c • losingClockLaw K b z u ≤ losingClockMarginal K g b u := by
    unfold losingClockMarginal
    exact Finset.single_le_sum (fun z _ => Measure.zero_le _)
      (Finset.mem_univ z)
  exact klDiv_ne_top_of_pos_smul_le _ _ c hc hcTop hle

/-! ### Lemma 7.4: exact race-law leaves -/

/- The published `Seed` race calibration is phrased for a `SeedSetup`.  The
cluster race only needs its underlying finite positive-weight theorem, which
we derive here from the same public exponential-clock API. -/

private noncomputable def weightedWinner {κ : Type} [Fintype κ]
    [Nonempty κ] (t : κ → ℝ) (G : κ → ℝ) : κ :=
  Classical.choose (Finite.exists_max fun c => Real.log (t c) + G c)

private noncomputable def weightedValue {κ : Type}
    (t : κ → ℝ) (G : κ → ℝ) (c : κ) : ℝ :=
  Real.log (t c) + G c

private noncomputable def weightedLexWinner {κ : Type} [Fintype κ]
    [DecidableEq κ] [Nonempty κ] (t : κ → ℝ) (G : κ → ℝ) : κ :=
  lexMax (fun G c => weightedValue t G c) G

private noncomputable def weightedLexScore {κ : Type} [Fintype κ]
    [DecidableEq κ] [Nonempty κ] (t : κ → ℝ) (G : κ → ℝ) : ℝ :=
  ∑ a, if weightedLexWinner t G = a then weightedValue t G a else 0

private noncomputable def weightedExcess {κ : Type} [Fintype κ]
    [DecidableEq κ] [Nonempty κ] (t : κ → ℝ) (G : κ → ℝ) (i : κ) : ℝ :=
  Real.exp (-(weightedValue t G i)) -
    Real.exp (-(weightedLexScore t G))

private lemma weightedWinner_max {κ : Type} [Fintype κ] [Nonempty κ]
    (t : κ → ℝ) (G : κ → ℝ) (c : κ) :
    weightedValue t G c ≤ weightedValue t G (weightedWinner t G) := by
  exact Classical.choose_spec
    (Finite.exists_max fun c => Real.log (t c) + G c) c

private lemma weightedWinner_eq_lex_of_noTie
    {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (t : κ → ℝ) (G : κ → ℝ)
    (htie : ∀ a b, a ≠ b → weightedValue t G a ≠ weightedValue t G b) :
    weightedWinner t G = weightedLexWinner t G := by
  have hleft := lexMax_max (fun G c => weightedValue t G c) G
    (weightedWinner t G)
  have hright := weightedWinner_max t G (weightedLexWinner t G)
  have hvalue : weightedValue t G (weightedWinner t G) =
      weightedValue t G (weightedLexWinner t G) :=
    le_antisymm hleft hright
  by_contra hne
  exact htie _ _ hne hvalue

private lemma weighted_seed_tie_null
    {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (t : κ → ℝ) (a b : κ) (hab : a ≠ b) :
    seedLaw κ {G | weightedValue t G a = weightedValue t G b} = 0 := by
  rw [seedLaw_eq_pi_gumbel1]
  simpa [weightedValue] using pi_affine_tie_null gumbel1 a b hab
    (Real.log (t a)) (Real.log (t b))

private lemma weighted_ae_no_ties
    {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (t : κ → ℝ) :
    ∀ᵐ G ∂(seedLaw κ), ∀ a b, a ≠ b →
      weightedValue t G a ≠ weightedValue t G b := by
  have hpair (a b : κ) :
      ∀ᵐ G ∂(seedLaw κ), a ≠ b →
        weightedValue t G a ≠ weightedValue t G b := by
    by_cases hab : a = b
    · exact Filter.Eventually.of_forall fun _ hne => (hne hab).elim
    · have hae := measure_eq_zero_iff_ae_notMem.mp
        (weighted_seed_tie_null t a b hab)
      filter_upwards [hae] with G hG
      intro _
      simpa only [Set.mem_ofPred_eq] using hG
  exact ae_forall_fintype fun a => ae_forall_fintype fun b => hpair a b

private lemma weightedWinner_ae_eq_lex
    {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (t : κ → ℝ) :
    (fun G => weightedWinner t G) =ᵐ[seedLaw κ]
      fun G => weightedLexWinner t G := by
  filter_upwards [weighted_ae_no_ties t] with G hG
  exact weightedWinner_eq_lex_of_noTie t G hG

private lemma weightedValue_clock_lt_iff
    {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (t : κ → ℝ) (ht : ∀ i, 0 < t i) (a b : κ)
    (E : κ → ℝ) (hE : ∀ i, 0 < E i) :
    weightedValue t (fun i => -Real.log (E i)) b <
        weightedValue t (fun i => -Real.log (E i)) a ↔
      E a / t a < E b / t b := by
  have hscore (i : κ) :
      weightedValue t (fun j => -Real.log (E j)) i =
        Real.log (t i / E i) := by
    unfold weightedValue
    rw [Real.log_div (ht i).ne' (hE i).ne']
    ring
  rw [hscore b, hscore a]
  have hratioB : 0 < t b / E b := div_pos (ht b) (hE b)
  have hratioA : 0 < t a / E a := div_pos (ht a) (hE a)
  have hclockB : 0 < E b / t b := div_pos (hE b) (ht b)
  have hclockA : 0 < E a / t a := div_pos (hE a) (ht a)
  have hinvB : (E b / t b)⁻¹ = t b / E b := by field_simp
  have hinvA : (E a / t a)⁻¹ = t a / E a := by field_simp
  constructor
  · intro hlog
    have hratio : t b / E b < t a / E a := by
      rw [← Real.exp_log hratioB, ← Real.exp_log hratioA]
      exact Real.exp_lt_exp.mpr hlog
    rw [← hinvB, ← hinvA] at hratio
    exact (inv_lt_inv₀ hclockB hclockA).1 hratio
  · intro hclock
    have hinv : (E b / t b)⁻¹ < (E a / t a)⁻¹ :=
      (inv_lt_inv₀ hclockB hclockA).2 hclock
    rw [hinvB, hinvA] at hinv
    exact Real.strictMonoOn_log (Set.mem_Ioi.mpr hratioB)
      (Set.mem_Ioi.mpr hratioA) hinv

private lemma weightedLexWinner_clock_iff
    {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (t : κ → ℝ) (ht : ∀ i, 0 < t i)
    (E : κ → ℝ) (hE : ∀ i, 0 < E i) (a : κ)
    (htie : ∀ b, b ≠ a →
      weightedValue t (fun i => -Real.log (E i)) b ≠
        weightedValue t (fun i => -Real.log (E i)) a) :
    weightedLexWinner t (fun i => -Real.log (E i)) = a ↔
      strictClockWin t a E := by
  constructor
  · intro hlex b hba
    have hle := lexMax_max (fun G i => weightedValue t G i)
      (fun i => -Real.log (E i)) b
    change weightedValue t (fun i => -Real.log (E i)) b ≤
      weightedValue t (fun i => -Real.log (E i))
        (weightedLexWinner t (fun i => -Real.log (E i))) at hle
    rw [hlex] at hle
    have hlt : weightedValue t (fun i => -Real.log (E i)) b <
        weightedValue t (fun i => -Real.log (E i)) a := by
      rcases lt_trichotomy
          (weightedValue t (fun i => -Real.log (E i)) b)
          (weightedValue t (fun i => -Real.log (E i)) a) with hlt | heq | hgt
      · exact hlt
      · exact (htie b hba heq).elim
      · exact (not_lt_of_ge hle hgt).elim
    exact (weightedValue_clock_lt_iff t ht a b E hE).1 hlt
  · intro hstrict
    by_contra hne
    have hmax := lexMax_max (fun G i => weightedValue t G i)
      (fun i => -Real.log (E i)) a
    change weightedValue t (fun i => -Real.log (E i)) a ≤
      weightedValue t (fun i => -Real.log (E i))
        (weightedLexWinner t (fun i => -Real.log (E i))) at hmax
    have hlt := (weightedValue_clock_lt_iff t ht a
      (weightedLexWinner t (fun i => -Real.log (E i))) E hE).2
        (hstrict _ hne)
    exact (not_lt_of_ge hmax) hlt

private lemma seedLaw_weightedLexWinner_measure
    {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (t : κ → ℝ) (ht : ∀ i, 0 < t i) (htotal : ∑ i, t i = 1)
    (a : κ) :
    seedLaw κ {G | weightedLexWinner t G = a} = ENNReal.ofReal (t a) := by
  letI : MeasurableSpace κ := ⊤
  letI : IsProbabilityMeasure (expMeasure 1) :=
    isProbabilityMeasure_expMeasure zero_lt_one
  let F : (κ → ℝ) → (κ → ℝ) := fun E i => -Real.log (E i)
  have hF : Measurable F := measurable_pi_lambda _ fun i =>
    (Real.measurable_log.comp (measurable_pi_apply i)).neg
  have hlex : Measurable (fun G => weightedLexWinner t G) := by
    unfold weightedLexWinner
    apply measurable_lexMax
    intro b
    exact measurable_const.add (measurable_pi_apply b)
  have hset : MeasurableSet {G | weightedLexWinner t G = a} :=
    measurableSet_singleton a |>.preimage hlex
  unfold seedLaw
  rw [Measure.map_apply hF hset]
  have hone : ∀ᵐ x : ℝ ∂(expMeasure 1), 0 < x := by
    have hnot := measure_eq_zero_iff_ae_notMem.mp expMeasure_one_Iic_zero
    filter_upwards [hnot] with x hx
    simpa only [Set.mem_Iic, not_le] using hx
  have hpos : ∀ᵐ E ∂(clockLaw κ), ∀ i, 0 < E i := by
    unfold clockLaw
    exact ae_forall_fintype fun i =>
      Measure.tendsto_eval_ae_ae.eventually hone
  have htieSeed := weighted_ae_no_ties t
  change ∀ᵐ G ∂((clockLaw κ).map F), ∀ a b, a ≠ b →
    weightedValue t G a ≠ weightedValue t G b at htieSeed
  have htieClock : ∀ᵐ E ∂(clockLaw κ), ∀ a b, a ≠ b →
      weightedValue t (F E) a ≠ weightedValue t (F E) b :=
    ae_of_ae_map hF.aemeasurable htieSeed
  have hae : ∀ᵐ E ∂(clockLaw κ),
      E ∈ F ⁻¹' {G | weightedLexWinner t G = a} ↔
        E ∈ {E | strictClockWin t a E} := by
    filter_upwards [hpos, htieClock] with E hE htie
    change weightedLexWinner t (F E) = a ↔ strictClockWin t a E
    exact weightedLexWinner_clock_iff t ht E hE a
      (fun b hba => htie b a hba)
  calc
    clockLaw κ (F ⁻¹' {G | weightedLexWinner t G = a}) =
        clockLaw κ {E | strictClockWin t a E} :=
      measure_congr (hae.mono fun E h => propext h)
    _ = ENNReal.ofReal (t a) := by
      unfold clockLaw
      exact pi_exp_strictClockWin t ht htotal a

private theorem weightedWinner_probability_measure
    {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (t : κ → ℝ) (ht : ∀ i, 0 < t i) (htotal : ∑ i, t i = 1)
    (a : κ) :
    seedLaw κ {G | weightedWinner t G = a} = ENNReal.ofReal (t a) := by
  have hae : ∀ᵐ G ∂(seedLaw κ),
      G ∈ {G | weightedWinner t G = a} ↔
        G ∈ {G | weightedLexWinner t G = a} := by
    filter_upwards [weightedWinner_ae_eq_lex t] with G hG
    rw [hG]
  calc
    seedLaw κ {G | weightedWinner t G = a} =
        seedLaw κ {G | weightedLexWinner t G = a} :=
      measure_congr (hae.mono fun G h => propext h)
    _ = ENNReal.ofReal (t a) :=
      seedLaw_weightedLexWinner_measure t ht htotal a

/-- Label-winner calibration under the original shared-Gumbel seed.  This is
the normalization used by `seedLawGivenWinner`. -/
private theorem label_winner_probability_measure {p : α × β → ℝ}
    (D : SeedSetup p) (a : D.L.ι) (z : α × β)
    (hz : z ∈ support p) :
    seedLaw D.L.ι {ε | winner D ε z = a} =
      ENNReal.ofReal (D.post a z) := by
  have hp : 0 < p z :=
    lt_of_le_of_ne (D.isPMF.nonneg z)
      (Ne.symm (by simpa [support] using hz))
  have hae : ∀ᵐ ε ∂(seedLaw D.L.ι),
      ε ∈ {ε | winner D ε z = a} ↔
        ε ∈ {ε | lexWinner D ε z = a} := by
    filter_upwards [winner_ae_eq_lexWinner D] with ε hε
    rw [hε]
  calc
    seedLaw D.L.ι {ε | winner D ε z = a} =
        seedLaw D.L.ι {ε | lexWinner D ε z = a} :=
      measure_congr (hae.mono fun ε h => propext h)
    _ = ENNReal.ofReal (D.post a z) :=
      seedLaw_lexWinner_measure D z hp a

/-- The cluster race has winner probability `σ_b(z)`; this normalizes the
restricted grouped seed law. -/
private theorem cluster_winner_probability_measure {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D) (b : K.κ) (z : α × β)
    (hz : z ∈ support p) :
    seedLaw K.κ {G | groupedClusterWinner K G z = b} =
      ENNReal.ofReal (K.sigma b z) := by
  change seedLaw K.κ
      {G | weightedWinner (fun c => K.sigma c z) G = b} =
        ENNReal.ofReal (K.sigma b z)
  exact weightedWinner_probability_measure (fun c => K.sigma c z)
    (fun c => K.sigma_pos c z hz) (raceSigma_sum_eq_one K z hz) b

private lemma expMeasure_one_tilt {t : ℝ} (ht : 0 < t) :
    (expMeasure 1).withDensity
        (fun y => ENNReal.ofReal
          (Real.exp (-((1 / t - 1) * y)))) =
      ENNReal.ofReal t • expMeasure (1 / t) := by
  have hpdf (r : ℝ) : Measurable (gammaPDF 1 r) := by
    unfold gammaPDF
    exact ENNReal.measurable_ofReal.comp (measurable_gammaPDFReal 1 r)
  have hweight : Measurable
      (fun y : ℝ => ENNReal.ofReal
        (Real.exp (-((1 / t - 1) * y)))) := by fun_prop
  unfold expMeasure gammaMeasure
  rw [← withDensity_mul volume (hpdf 1) hweight,
    ← withDensity_smul (μ := volume) (ENNReal.ofReal t) (hpdf (1 / t))]
  apply withDensity_congr_ae
  filter_upwards [] with y
  rw [Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
  simp only [gammaPDF_eq, Real.rpow_one, Real.Gamma_one, div_one,
    sub_self, Real.rpow_zero, mul_one, one_mul]
  by_cases hy : 0 ≤ y
  · simp only [if_pos hy]
    rw [← ENNReal.ofReal_mul (Real.exp_nonneg _),
      ← ENNReal.ofReal_mul ht.le]
    congr 1
    rw [← Real.exp_add]
    congr 1
    field_simp [ht.ne']
    ring
  · simp [if_neg hy]

private lemma map_div_expMeasure {t : ℝ} (ht : 0 < t) :
    Measure.map (fun x : ℝ => x / t) (expMeasure (1 / t)) =
      expMeasure 1 := by
  letI : IsProbabilityMeasure (expMeasure (1 / t)) :=
    isProbabilityMeasure_expMeasure (one_div_pos.mpr ht)
  letI : IsProbabilityMeasure (expMeasure 1) :=
    isProbabilityMeasure_expMeasure zero_lt_one
  letI : IsProbabilityMeasure
      (Measure.map (fun x : ℝ => x / t) (expMeasure (1 / t))) :=
    Measure.isProbabilityMeasure_map (measurable_id.div_const t).aemeasurable
  apply Measure.eq_of_cdf
  ext x
  rw [cdf_eq_real, cdf_eq_real, measureReal_def, measureReal_def,
    Measure.map_apply (f := fun y : ℝ => y / t)
      (measurable_id.div_const t) measurableSet_Iic]
  rw [show (fun y : ℝ => y / t) ⁻¹' Set.Iic x = Set.Iic (t * x) by
    ext y
    simp only [Set.mem_preimage, Set.mem_Iic]
    exact (div_le_iff₀ ht).trans (by ring_nf)]
  rw [← ofReal_cdf (expMeasure (1 / t)) (t * x),
    ← ofReal_cdf (expMeasure 1) x,
    ENNReal.toReal_ofReal (cdf_nonneg _ _),
    ENNReal.toReal_ofReal (cdf_nonneg _ _)]
  rw [cdf_expMeasure_eq (one_div_pos.mpr ht), cdf_expMeasure_eq zero_lt_one]
  by_cases hx : 0 ≤ x
  · rw [if_pos hx, if_pos (mul_nonneg ht.le hx)]
    congr 2
    field_simp [ht.ne']
  · have htx : ¬ 0 ≤ t * x := by nlinarith
    rw [if_neg hx, if_neg htx]

/- Scaling and memorylessness in the orientation used by the within-cluster
excess vector. -/
private lemma map_div_expMeasure_one {t : ℝ} (ht : 0 < t) :
    Measure.map (fun x : ℝ => x / t) (expMeasure 1) = expMeasure t := by
  letI : IsProbabilityMeasure (expMeasure 1) :=
    isProbabilityMeasure_expMeasure zero_lt_one
  letI : IsProbabilityMeasure (expMeasure t) :=
    isProbabilityMeasure_expMeasure ht
  letI : IsProbabilityMeasure
      (Measure.map (fun x : ℝ => x / t) (expMeasure 1)) :=
    Measure.isProbabilityMeasure_map (measurable_id.div_const t).aemeasurable
  apply Measure.eq_of_cdf
  ext x
  rw [cdf_eq_real, cdf_eq_real, measureReal_def, measureReal_def,
    Measure.map_apply (f := fun y : ℝ => y / t)
      (measurable_id.div_const t) measurableSet_Iic]
  rw [show (fun y : ℝ => y / t) ⁻¹' Set.Iic x = Set.Iic (t * x) by
    ext y
    simp only [Set.mem_preimage, Set.mem_Iic]
    exact (div_le_iff₀ ht).trans (by ring_nf)]
  rw [← ofReal_cdf (expMeasure 1) (t * x),
    ← ofReal_cdf (expMeasure t) x,
    ENNReal.toReal_ofReal (cdf_nonneg _ _),
    ENNReal.toReal_ofReal (cdf_nonneg _ _)]
  rw [cdf_expMeasure_eq zero_lt_one, cdf_expMeasure_eq ht]
  by_cases hx : 0 ≤ x
  · rw [if_pos hx, if_pos (mul_nonneg ht.le hx)]
    congr 2
    ring
  · have htx : ¬ 0 ≤ t * x := by nlinarith
    rw [if_neg hx, if_neg htx]

private lemma map_sub_restrict_expMeasure_one {a : ℝ} (ha : 0 ≤ a) :
    Measure.map (fun x : ℝ => x - a)
        ((expMeasure 1).restrict (Set.Ioi a)) =
      ENNReal.ofReal (Real.exp (-a)) • expMeasure 1 := by
  let ν : Measure ℝ := expMeasure 1
  letI : IsProbabilityMeasure ν :=
    isProbabilityMeasure_expMeasure zero_lt_one
  apply Measure.ext_of_Iic
  intro x
  have hpre : (fun y : ℝ => y - a) ⁻¹' Set.Iic x = Set.Iic (x + a) := by
    ext y
    simp only [Set.mem_preimage, Set.mem_Iic]
    constructor <;> intro h <;> linarith
  rw [Measure.map_apply (by fun_prop) measurableSet_Iic, hpre,
    Measure.restrict_apply measurableSet_Iic,
    Measure.smul_apply, smul_eq_mul]
  by_cases hx : 0 ≤ x
  · have hxa : a ≤ x + a := by linarith
    have hxapos : 0 ≤ x + a := ha.trans hxa
    have hIoc : ν (Set.Ioc a (x + a)) =
        ENNReal.ofReal (cdf ν (x + a) - cdf ν a) := by
      calc
        ν (Set.Ioc a (x + a)) = (cdf ν).measure (Set.Ioc a (x + a)) := by
          rw [measure_cdf]
        _ = ENNReal.ofReal (cdf ν (x + a) - cdf ν a) :=
          StieltjesFunction.measure_Ioc (cdf ν) a (x + a)
    rw [Set.inter_comm (Set.Iic (x + a)), Set.Ioi_inter_Iic,
      hIoc, ← ofReal_cdf ν x]
    dsimp [ν]
    rw [cdf_expMeasure_eq zero_lt_one,
      cdf_expMeasure_eq zero_lt_one,
      cdf_expMeasure_eq zero_lt_one]
    simp only [if_pos hxapos, if_pos ha, if_pos hx, one_mul]
    have hnonneg : 0 ≤ 1 - Real.exp (-x) :=
      sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by linarith))
    rw [← ENNReal.ofReal_mul (Real.exp_nonneg (-a))]
    congr 1
    rw [show -(x + a) = -a + -x by ring, Real.exp_add]
    ring
  · have hxneg : x < 0 := lt_of_not_ge hx
    have hnot : ¬a < x + a := by linarith
    rw [Set.inter_comm (Set.Iic (x + a)), Set.Ioi_inter_Iic,
      Set.Ioc_eq_empty hnot, measure_empty, ← ofReal_cdf ν x]
    dsimp [ν]
    rw [cdf_expMeasure_eq zero_lt_one, if_neg (not_le.mpr hxneg)]
    simp

private lemma map_scaled_excess_restrict_expMeasure_one
    {t u : ℝ} (ht : 0 < t) (hu : 0 ≤ u) :
    Measure.map (fun x : ℝ => x / t - u)
        ((expMeasure 1).restrict (Set.Ioi (t * u))) =
      ENNReal.ofReal (Real.exp (-(t * u))) • expMeasure t := by
  have htu : 0 ≤ t * u := mul_nonneg ht.le hu
  calc
    Measure.map (fun x : ℝ => x / t - u)
        ((expMeasure 1).restrict (Set.Ioi (t * u))) =
        Measure.map ((fun y : ℝ => y / t) ∘ (fun x : ℝ => x - t * u))
          ((expMeasure 1).restrict (Set.Ioi (t * u))) := by
      congr 1
      funext x
      dsimp only [Function.comp_apply]
      field_simp [ht.ne']
    _ = Measure.map (fun y : ℝ => y / t)
        (Measure.map (fun x : ℝ => x - t * u)
          ((expMeasure 1).restrict (Set.Ioi (t * u)))) :=
      (Measure.map_map (measurable_id.div_const t)
        (measurable_id.sub_const (t * u))).symm
    _ = Measure.map (fun y : ℝ => y / t)
        (ENNReal.ofReal (Real.exp (-(t * u))) • expMeasure 1) := by
      rw [map_sub_restrict_expMeasure_one htu]
    _ = ENNReal.ofReal (Real.exp (-(t * u))) •
        Measure.map (fun y : ℝ => y / t) (expMeasure 1) := by
      rw [Measure.map_smul]
    _ = ENNReal.ofReal (Real.exp (-(t * u))) • expMeasure t := by
      rw [map_div_expMeasure_one ht]

private noncomputable def weightedLosingExcessLaw
    {κ : Type} [Fintype κ] [DecidableEq κ]
    (t : κ → ℝ) (a : κ) : Measure ({i : κ // i ≠ a} → ℝ) :=
  Measure.pi fun i : {i : κ // i ≠ a} => expMeasure (t i.1)

private lemma map_losing_scaled_excess
    {κ : Type} [Fintype κ] [DecidableEq κ]
    (t : κ → ℝ) (ht : ∀ i, 0 < t i) (a : κ)
    {u : ℝ} (hu : 0 ≤ u) :
    Measure.map
        (fun E : {i : κ // i ≠ a} → ℝ =>
          fun i => E i / t i.1 - u)
        ((Measure.pi (fun _ : {i : κ // i ≠ a} => expMeasure 1)).restrict
          (Set.pi Set.univ
            (fun i : {i : κ // i ≠ a} => Set.Ioi (t i.1 * u)))) =
      (∏ i : {i : κ // i ≠ a},
          ENNReal.ofReal (Real.exp (-(t i.1 * u)))) •
        weightedLosingExcessLaw t a := by
  let d : {i : κ // i ≠ a} → ℝ≥0∞ := fun i =>
    ENNReal.ofReal (Real.exp (-(t i.1 * u)))
  letI : IsProbabilityMeasure (expMeasure 1) :=
    isProbabilityMeasure_expMeasure zero_lt_one
  letI (i : {i : κ // i ≠ a}) : IsProbabilityMeasure
      (expMeasure (t i.1)) := isProbabilityMeasure_expMeasure (ht i.1)
  have hmap :
      Measure.map
          (fun E : {i : κ // i ≠ a} → ℝ =>
            fun i => E i / t i.1 - u)
          (Measure.pi (fun i : {i : κ // i ≠ a} =>
            (expMeasure 1).restrict (Set.Ioi (t i.1 * u)))) =
        Measure.pi (fun i : {i : κ // i ≠ a} =>
          Measure.map (fun x : ℝ => x / t i.1 - u)
            ((expMeasure 1).restrict (Set.Ioi (t i.1 * u)))) := by
    exact Measure.pi_map_pi fun (i : {i : κ // i ≠ a}) =>
      ((measurable_id.div_const (t i.1)).sub_const u).aemeasurable
  have hcoord (i : {i : κ // i ≠ a}) :
      Measure.map (fun x : ℝ => x / t i.1 - u)
          ((expMeasure 1).restrict (Set.Ioi (t i.1 * u))) =
        d i • expMeasure (t i.1) := by
    exact map_scaled_excess_restrict_expMeasure_one (ht i.1) hu
  letI (i : {i : κ // i ≠ a}) : IsFiniteMeasure
      (d i • expMeasure (t i.1)) := ⟨by simp [d]⟩
  have hscaled :
      Measure.pi (fun i : {i : κ // i ≠ a} =>
          d i • expMeasure (t i.1)) =
        (∏ i : {i : κ // i ≠ a}, d i) •
          weightedLosingExcessLaw t a := by
    unfold weightedLosingExcessLaw
    apply Measure.pi_eq
    intro s hs
    rw [Measure.smul_apply, smul_eq_mul, Measure.pi_pi]
    simp_rw [Measure.smul_apply, smul_eq_mul]
    rw [Finset.prod_mul_distrib]
  rw [Measure.restrict_pi_pi, hmap]
  calc
    Measure.pi (fun i : {i : κ // i ≠ a} =>
        Measure.map (fun x : ℝ => x / t i.1 - u)
          ((expMeasure 1).restrict (Set.Ioi (t i.1 * u)))) =
        Measure.pi (fun i : {i : κ // i ≠ a} =>
          d i • expMeasure (t i.1)) := by
      congr 1
      funext i
      exact hcoord i
    _ = (∏ i : {i : κ // i ≠ a}, d i) •
        weightedLosingExcessLaw t a := hscaled

private lemma map_eval_restrict_strictClockWin
    {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (t : κ → ℝ) (ht : ∀ i, 0 < t i) (htotal : ∑ i, t i = 1)
    (a : κ) :
    Measure.map (fun E : κ → ℝ => E a)
        ((clockLaw κ).restrict {E | strictClockWin t a E}) =
      ENNReal.ofReal (t a) • expMeasure (1 / t a) := by
  letI : ∀ _ : κ, IsProbabilityMeasure (expMeasure 1) :=
    fun _ => isProbabilityMeasure_expMeasure zero_lt_one
  letI : IsProbabilityMeasure (expMeasure 1) :=
    isProbabilityMeasure_expMeasure zero_lt_one
  let e : Option {i : κ // i ≠ a} ≃ κ := Equiv.optionSubtypeNe a
  let f := (MeasurableEquiv.piOptionEquivProd
    (fun _ : Option {i : κ // i ≠ a} => ℝ)).symm
  let g := MeasurableEquiv.piCongrLeft (fun _ : κ => ℝ) e
  let q := (Measure.pi (fun _ : {i : κ // i ≠ a} => expMeasure 1)).prod
    (expMeasure 1)
  have hfirst :
      Measure.map f q =
        Measure.pi (fun _ : Option {i : κ // i ≠ a} => expMeasure 1) := by
    dsimp [f, q]
    exact Measure.pi_map_piOptionEquivProd
      (fun _ : Option {i : κ // i ≠ a} => expMeasure 1)
  have hsecond :
      Measure.map g
          (Measure.pi (fun _ : Option {i : κ // i ≠ a} => expMeasure 1)) =
        Measure.pi (fun _ : κ => expMeasure 1) := by
    dsimp [g]
    simpa [e] using Measure.pi_map_piCongrLeft e
      (fun _ : κ => expMeasure 1)
  have hmap : Measure.map (g ∘ f) q =
      Measure.pi (fun _ : κ => expMeasure 1) := by
    calc
      Measure.map (g ∘ f) q = Measure.map g (Measure.map f q) :=
        (Measure.map_map g.measurable f.measurable).symm
      _ = _ := by rw [hfirst, hsecond]
  have hwin : MeasurableSet {E : κ → ℝ | strictClockWin t a E} := by
    unfold strictClockWin
    measurability
  have hcoord (xy : ({i : κ // i ≠ a} → ℝ) × ℝ) :
      (g (f xy)) a = xy.2 := by
    have hf_pair := (MeasurableEquiv.piOptionEquivProd
      (fun _ : Option {i : κ // i ≠ a} => ℝ)).apply_symm_apply xy
    have hf_none : f xy none = xy.2 := congrArg Prod.snd hf_pair
    dsimp [g]
    rw [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]
    simp [e, hf_none]
  have hsectionWin (y : ℝ) :
      (fun x : {i : κ // i ≠ a} → ℝ => (x, y)) ⁻¹'
          ((g ∘ f) ⁻¹' {E : κ → ℝ | strictClockWin t a E}) =
        Set.pi Set.univ
          (fun i : {i : κ // i ≠ a} => Set.Ioi (t i.1 / t a * y)) := by
    ext x
    have hf_pair := (MeasurableEquiv.piOptionEquivProd
      (fun _ : Option {i : κ // i ≠ a} => ℝ)).apply_symm_apply (x, y)
    have hf_some (i : {i : κ // i ≠ a}) : f (x, y) (some i) = x i :=
      congrFun (congrArg Prod.fst hf_pair) i
    have hf_none : f (x, y) none = y := congrArg Prod.snd hf_pair
    have he_i (i : {i : κ // i ≠ a}) : (g (f (x, y))) i.1 = x i := by
      dsimp [g]
      rw [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]
      simp [e, Equiv.optionSubtypeNe_symm_of_ne i.2, hf_some]
    have he_a : (g (f (x, y))) a = y := by
      dsimp [g]
      rw [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]
      simp [e, hf_none]
    simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ,
      true_implies, Set.mem_Ioi]
    constructor
    · intro h i
      have hrel := h i.1 i.2
      change g (f (x, y)) a / t a < g (f (x, y)) i.1 / t i.1 at hrel
      rw [he_a, he_i] at hrel
      have hcross : y * t i.1 < x i * t a :=
        (div_lt_div_iff₀ (ht a) (ht i.1)).1 hrel
      have hdiv : t i.1 * y / t a < x i :=
        (div_lt_iff₀ (ht a)).2 (by nlinarith)
      simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hdiv
    · intro h b hba
      let i : {i : κ // i ≠ a} := ⟨b, hba⟩
      have hdiv := h i
      change t b / t a * y < x i at hdiv
      have hdiv' : t b * y / t a < x i := by
        simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hdiv
      have hcross : y * t b < x i * t a := by
        have := (div_lt_iff₀ (ht a)).1 hdiv'
        nlinarith
      change g (f (x, y)) a / t a < g (f (x, y)) b / t b
      have hib := he_i i
      change g (f (x, y)) b = x i at hib
      rw [he_a, hib]
      exact (div_lt_div_iff₀ (ht a) (ht b)).2 hcross
  have hsplit := Fintype.sum_eq_add_sum_subtype_ne t a
  have hsubsum : (∑ i : {i : κ // i ≠ a}, t i.1) = 1 - t a := by
    linarith
  have hratio : (∑ i : {i : κ // i ≠ a}, t i.1 / t a) =
      1 / t a - 1 := by
    rw [← Finset.sum_div, hsubsum]
    field_simp [(ht a).ne']
  have hypos : ∀ᵐ y : ℝ ∂(expMeasure 1), 0 < y := by
    have hnot := measure_eq_zero_iff_ae_notMem.mp expMeasure_one_Iic_zero
    filter_upwards [hnot] with y hy
    simpa only [Set.mem_Iic, not_le] using hy
  have hprod : ∀ᵐ y : ℝ ∂(expMeasure 1),
      (∏ i : {i : κ // i ≠ a},
          expMeasure 1 (Set.Ioi (t i.1 / t a * y))) =
        ENNReal.ofReal (Real.exp (-((1 / t a - 1) * y))) := by
    filter_upwards [hypos] with y hy
    simp_rw [expMeasure_one_Ioi _
      (mul_nonneg (div_nonneg (ht _).le (ht a).le) hy.le)]
    rw [← ENNReal.ofReal_prod_of_nonneg
      (fun i _ => Real.exp_nonneg (-(t i.1 / t a * y))), ← Real.exp_sum]
    congr 2
    rw [Finset.sum_neg_distrib, ← Finset.sum_mul, hratio]
  have hclock :
      Measure.map (fun E : κ → ℝ => E a)
          ((clockLaw κ).restrict {E | strictClockWin t a E}) =
        (expMeasure 1).withDensity
          (fun y => ENNReal.ofReal
            (Real.exp (-((1 / t a - 1) * y)))) := by
    unfold clockLaw
    rw [← hmap, Measure.restrict_map (g.measurable.comp f.measurable) hwin,
      Measure.map_map (measurable_pi_apply a) (g.measurable.comp f.measurable)]
    have hmapcoord :
        Measure.map ((fun E : κ → ℝ => E a) ∘ (g ∘ f))
            (q.restrict ((g ∘ f) ⁻¹' {E : κ → ℝ | strictClockWin t a E})) =
          Measure.map Prod.snd
            (q.restrict ((g ∘ f) ⁻¹' {E : κ → ℝ | strictClockWin t a E})) := by
      apply Measure.map_congr
      exact Filter.Eventually.of_forall fun xy => hcoord xy
    rw [hmapcoord]
    ext s hs
    rw [Measure.map_apply measurable_snd hs,
      Measure.restrict_apply (measurable_snd hs)]
    have hset : MeasurableSet
        (Prod.snd ⁻¹' s ∩
          (g ∘ f) ⁻¹' {E : κ → ℝ | strictClockWin t a E}) :=
      (measurable_snd hs).inter (hwin.preimage (g.measurable.comp f.measurable))
    rw [Measure.prod_apply_symm hset]
    have hsections : ∀ᵐ y : ℝ ∂(expMeasure 1),
        Measure.pi (fun _ : {i : κ // i ≠ a} => expMeasure 1)
            ((fun x : {i : κ // i ≠ a} → ℝ => (x, y)) ⁻¹'
              (Prod.snd ⁻¹' s ∩
                (g ∘ f) ⁻¹'
                  {E : κ → ℝ | strictClockWin t a E})) =
          s.indicator (fun y => ENNReal.ofReal
            (Real.exp (-((1 / t a - 1) * y)))) y := by
      filter_upwards [hprod] with y hpy
      by_cases hys : y ∈ s
      · have hsec :
            (fun x : {i : κ // i ≠ a} → ℝ => (x, y)) ⁻¹'
                (Prod.snd ⁻¹' s ∩
                  (g ∘ f) ⁻¹'
                    {E : κ → ℝ | strictClockWin t a E}) =
              Set.pi Set.univ
                (fun i : {i : κ // i ≠ a} =>
                  Set.Ioi (t i.1 / t a * y)) := by
            ext x
            simp only [Set.mem_preimage, Set.mem_inter_iff]
            have hmem :
                (g ∘ f) (x, y) ∈
                    {E : κ → ℝ | strictClockWin t a E} ↔
                  x ∈ Set.pi Set.univ
                    (fun i : {i : κ // i ≠ a} =>
                      Set.Ioi (t i.1 / t a * y)) :=
              Set.ext_iff.mp (hsectionWin y) x
            simpa only [hys, true_and] using hmem
        rw [hsec, Measure.pi_pi, hpy, Set.indicator_of_mem hys]
      · have hsec :
            (fun x : {i : κ // i ≠ a} → ℝ => (x, y)) ⁻¹'
                (Prod.snd ⁻¹' s ∩
                  (g ∘ f) ⁻¹'
                    {E : κ → ℝ | strictClockWin t a E}) = ∅ := by
            ext x
            simp [hys]
        rw [hsec, measure_empty, Set.indicator_of_notMem hys]
    rw [lintegral_congr_ae hsections, lintegral_indicator hs,
      ← withDensity_apply _ hs]
  rw [hclock, expMeasure_one_tilt (ht a)]

private lemma weightedWinner_clock_law
    {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (t : κ → ℝ) (ht : ∀ i, 0 < t i) (htotal : ∑ i, t i = 1)
    (a : κ) :
    Measure.map (fun G : κ → ℝ => Real.exp (-G a))
        ((ENNReal.ofReal (t a))⁻¹ •
          (seedLaw κ).restrict {G | weightedWinner t G = a}) =
      expMeasure (1 / t a) := by
  letI : MeasurableSpace κ := ⊤
  letI : IsProbabilityMeasure (expMeasure 1) :=
    isProbabilityMeasure_expMeasure zero_lt_one
  letI : ∀ _ : κ, SigmaFinite (expMeasure 1) := fun _ => inferInstance
  let F : (κ → ℝ) → (κ → ℝ) := fun E i => -Real.log (E i)
  let R : (κ → ℝ) → ℝ := fun G => Real.exp (-G a)
  have hF : Measurable F := measurable_pi_lambda _ fun i =>
    (Real.measurable_log.comp (measurable_pi_apply i)).neg
  have hR : Measurable R :=
    Real.measurable_exp.comp (measurable_pi_apply a).neg
  have hlex : Measurable (fun G => weightedLexWinner t G) := by
    unfold weightedLexWinner
    apply measurable_lexMax
    intro b
    exact measurable_const.add (measurable_pi_apply b)
  have hlexSet : MeasurableSet {G | weightedLexWinner t G = a} :=
    measurableSet_singleton a |>.preimage hlex
  have hwinnerLex :
      {G | weightedWinner t G = a} =ᵐ[seedLaw κ]
        {G | weightedLexWinner t G = a} := by
    filter_upwards [weightedWinner_ae_eq_lex t] with G hG
    apply propext
    change (weightedWinner t G = a ↔ weightedLexWinner t G = a)
    rw [hG]
  have hone : ∀ᵐ x : ℝ ∂(expMeasure 1), 0 < x := by
    have hnot := measure_eq_zero_iff_ae_notMem.mp expMeasure_one_Iic_zero
    filter_upwards [hnot] with x hx
    simpa only [Set.mem_Iic, not_le] using hx
  have hpos : ∀ᵐ E ∂(clockLaw κ), ∀ i, 0 < E i := by
    unfold clockLaw
    exact ae_forall_fintype fun i =>
      Measure.tendsto_eval_ae_ae.eventually hone
  have htieSeed := weighted_ae_no_ties t
  change ∀ᵐ G ∂((clockLaw κ).map F), ∀ a b, a ≠ b →
    weightedValue t G a ≠ weightedValue t G b at htieSeed
  have htieClock : ∀ᵐ E ∂(clockLaw κ), ∀ a b, a ≠ b →
      weightedValue t (F E) a ≠ weightedValue t (F E) b :=
    ae_of_ae_map hF.aemeasurable htieSeed
  have hpre :
      F ⁻¹' {G | weightedLexWinner t G = a} =ᵐ[clockLaw κ]
        {E | strictClockWin t a E} := by
    filter_upwards [hpos, htieClock] with E hE htie
    apply propext
    change (weightedLexWinner t (F E) = a ↔ strictClockWin t a E)
    exact weightedLexWinner_clock_iff t ht E hE a
      (fun b hba => htie b a hba)
  have hseedClock :
      (seedLaw κ).restrict {G | weightedLexWinner t G = a} =
        Measure.map F ((clockLaw κ).restrict {E | strictClockWin t a E}) := by
    unfold seedLaw
    rw [Measure.restrict_map hF hlexSet,
      Measure.restrict_congr_set hpre]
  have hraw :
      (R ∘ F) =ᵐ[(clockLaw κ).restrict {E | strictClockWin t a E}]
        fun E => E a := by
    filter_upwards [ae_restrict_of_ae hpos] with E hE
    dsimp only [R, F, Function.comp_apply]
    rw [neg_neg, Real.exp_log (hE a)]
  have hunscaled :
      Measure.map R ((seedLaw κ).restrict {G | weightedWinner t G = a}) =
        ENNReal.ofReal (t a) • expMeasure (1 / t a) := by
    calc
      Measure.map R ((seedLaw κ).restrict {G | weightedWinner t G = a}) =
          Measure.map R
            ((seedLaw κ).restrict {G | weightedLexWinner t G = a}) := by
        rw [Measure.restrict_congr_set hwinnerLex]
      _ = Measure.map R
          (Measure.map F
            ((clockLaw κ).restrict {E | strictClockWin t a E})) := by
        rw [hseedClock]
      _ = Measure.map (R ∘ F)
          ((clockLaw κ).restrict {E | strictClockWin t a E}) :=
        Measure.map_map hR hF
      _ = Measure.map (fun E : κ → ℝ => E a)
          ((clockLaw κ).restrict {E | strictClockWin t a E}) :=
        Measure.map_congr hraw
      _ = ENNReal.ofReal (t a) • expMeasure (1 / t a) :=
        map_eval_restrict_strictClockWin t ht htotal a
  change Measure.map R
      ((ENNReal.ofReal (t a))⁻¹ •
        (seedLaw κ).restrict {G | weightedWinner t G = a}) = _
  rw [Measure.map_smul, hunscaled, smul_smul,
    ENNReal.inv_mul_cancel (ENNReal.ofReal_ne_zero_iff.mpr (ht a))
      ENNReal.ofReal_ne_top,
    one_smul]

private lemma weightedWinner_raw_restrict_law
    {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (t : κ → ℝ) (ht : ∀ i, 0 < t i) (htotal : ∑ i, t i = 1)
    (a : κ) :
    Measure.map (fun G : κ → ℝ => Real.exp (-G a))
        ((seedLaw κ).restrict {G | weightedWinner t G = a}) =
      ENNReal.ofReal (t a) • expMeasure (1 / t a) := by
  have h := weightedWinner_clock_law t ht htotal a
  have hscaled := congrArg (fun μ : Measure ℝ => ENNReal.ofReal (t a) • μ) h
  simpa only [Measure.map_smul, smul_smul,
    ENNReal.mul_inv_cancel (ENNReal.ofReal_ne_zero_iff.mpr (ht a))
      ENNReal.ofReal_ne_top,
    one_smul] using hscaled

private noncomputable def insertWinnerZero
    {κ : Type} [DecidableEq κ] (a : κ)
    (r : {i : κ // i ≠ a} → ℝ) : κ → ℝ :=
  fun i => if h : i = a then 0 else r ⟨i, h⟩

private lemma insertWinnerZero_measurable
    {κ : Type} [Fintype κ] [DecidableEq κ] (a : κ) :
    Measurable (insertWinnerZero a) := by
  apply measurable_pi_lambda
  intro i
  by_cases h : i = a
  · simpa [insertWinnerZero, h] using
      (measurable_const : Measurable (fun _ : {j : κ // j ≠ a} → ℝ => (0 : ℝ)))
  · simpa [insertWinnerZero, h] using
      (measurable_pi_apply (⟨i, h⟩ : {j : κ // j ≠ a}))

/- On a fixed strict-winner cell, the scaled minimum has law
`t_a • Exp(1)` and is independent of the full excess vector. -/
private theorem clock_min_excess_restrict_factorization
    {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (t : κ → ℝ) (ht : ∀ i, 0 < t i) (htotal : ∑ i, t i = 1)
    (a : κ) :
    Measure.map
        (fun E : κ → ℝ =>
          (E a / t a, fun i => E i / t i - E a / t a))
        ((clockLaw κ).restrict {E | strictClockWin t a E}) =
      (ENNReal.ofReal (t a) • expMeasure 1).prod
        (Measure.map (insertWinnerZero a) (weightedLosingExcessLaw t a)) := by
  letI : IsProbabilityMeasure (expMeasure 1) :=
    isProbabilityMeasure_expMeasure zero_lt_one
  letI (i : {i : κ // i ≠ a}) : IsProbabilityMeasure
      (expMeasure (t i.1)) := isProbabilityMeasure_expMeasure (ht i.1)
  let e : Option {i : κ // i ≠ a} ≃ κ := Equiv.optionSubtypeNe a
  let f := (MeasurableEquiv.piOptionEquivProd
    (fun _ : Option {i : κ // i ≠ a} => ℝ)).symm
  let g := MeasurableEquiv.piCongrLeft (fun _ : κ => ℝ) e
  let loseμ : Measure ({i : κ // i ≠ a} → ℝ) :=
    Measure.pi fun _ : {i : κ // i ≠ a} => expMeasure 1
  let q := loseμ.prod (expMeasure 1)
  let P := (g ∘ f) ⁻¹' {E : κ → ℝ | strictClockWin t a E}
  let J : (({i : κ // i ≠ a} → ℝ) × ℝ) → ℝ × (κ → ℝ) :=
    fun xy =>
      (xy.2 / t a,
        insertWinnerZero a (fun i => xy.1 i / t i.1 - xy.2 / t a))
  have hfirst :
      Measure.map f q =
        Measure.pi (fun _ : Option {i : κ // i ≠ a} => expMeasure 1) := by
    dsimp [f, q, loseμ]
    exact Measure.pi_map_piOptionEquivProd
      (fun _ : Option {i : κ // i ≠ a} => expMeasure 1)
  have hsecond :
      Measure.map g
          (Measure.pi (fun _ : Option {i : κ // i ≠ a} => expMeasure 1)) =
        Measure.pi (fun _ : κ => expMeasure 1) := by
    dsimp [g]
    simpa [e] using Measure.pi_map_piCongrLeft e
      (fun _ : κ => expMeasure 1)
  have hmap : Measure.map (g ∘ f) q = clockLaw κ := by
    unfold clockLaw
    calc
      Measure.map (g ∘ f) q = Measure.map g (Measure.map f q) :=
        (Measure.map_map g.measurable f.measurable).symm
      _ = _ := by rw [hfirst, hsecond]
  have hcoordA (xy : ({i : κ // i ≠ a} → ℝ) × ℝ) :
      (g (f xy)) a = xy.2 := by
    have hfPair := (MeasurableEquiv.piOptionEquivProd
      (fun _ : Option {i : κ // i ≠ a} => ℝ)).apply_symm_apply xy
    have hfNone : f xy none = xy.2 := congrArg Prod.snd hfPair
    dsimp [g]
    rw [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]
    simp [e, hfNone]
  have hcoordNe (xy : ({i : κ // i ≠ a} → ℝ) × ℝ)
      (i : {i : κ // i ≠ a}) : (g (f xy)) i.1 = xy.1 i := by
    have hfPair := (MeasurableEquiv.piOptionEquivProd
      (fun _ : Option {i : κ // i ≠ a} => ℝ)).apply_symm_apply xy
    have hfSome : f xy (some i) = xy.1 i :=
      congrFun (congrArg Prod.fst hfPair) i
    dsimp [g]
    rw [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]
    simp [e, Equiv.optionSubtypeNe_symm_of_ne i.2, hfSome]
  have hwin : MeasurableSet {E : κ → ℝ | strictClockWin t a E} := by
    unfold strictClockWin
    measurability
  have hP : MeasurableSet P :=
    hwin.preimage (g.measurable.comp f.measurable)
  have hsectionP (y : ℝ) :
      (fun x : {i : κ // i ≠ a} → ℝ => (x, y)) ⁻¹' P =
        Set.pi Set.univ
          (fun i : {i : κ // i ≠ a} =>
            Set.Ioi (t i.1 / t a * y)) := by
    ext x
    simp only [P, Set.mem_preimage, Set.mem_setOf_eq, strictClockWin,
      Set.mem_pi, Set.mem_univ, true_implies, Function.comp_apply,
      Set.mem_Ioi]
    constructor
    · intro h i
      have hrel := h i.1 i.2
      rw [hcoordA, hcoordNe (x, y) i] at hrel
      have hcross : y * t i.1 < x i * t a :=
        (div_lt_div_iff₀ (ht a) (ht i.1)).1 hrel
      have hdiv : t i.1 * y / t a < x i :=
        (div_lt_iff₀ (ht a)).2 (by nlinarith)
      simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hdiv
    · intro h b hba
      let i : {i : κ // i ≠ a} := ⟨b, hba⟩
      have hdiv := h i
      change t b / t a * y < x i at hdiv
      have hdiv' : t b * y / t a < x i := by
        simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hdiv
      have hcross : y * t b < x i * t a := by
        have := (div_lt_iff₀ (ht a)).1 hdiv'
        nlinarith
      rw [hcoordA, hcoordNe (x, y) i]
      exact (div_lt_div_iff₀ (ht a) (ht b)).2 hcross
  have hJ : Measurable J := by
    have hy : Measurable
        (fun xy : ({i : κ // i ≠ a} → ℝ) × ℝ => xy.2) := measurable_snd
    have hlose : Measurable
        (fun xy : ({i : κ // i ≠ a} → ℝ) × ℝ =>
          fun i => xy.1 i / t i.1 - xy.2 / t a) := by
      apply measurable_pi_lambda
      intro i
      have hxi : Measurable
          (fun xy : ({i : κ // i ≠ a} → ℝ) × ℝ => xy.1 i) :=
        (measurable_pi_apply i).comp measurable_fst
      exact (hxi.div_const (t i.1)).sub (hy.div_const (t a))
    apply Measurable.prodMk
    · exact hy.div_const (t a)
    · exact (insertWinnerZero_measurable a).comp hlose
  have horig : Measurable (fun E : κ → ℝ =>
      (E a / t a, fun i => E i / t i - E a / t a)) := by
    have hea : Measurable (fun E : κ → ℝ => E a) := measurable_pi_apply a
    apply Measurable.prodMk
    · exact hea.div_const (t a)
    · apply measurable_pi_lambda
      intro i
      have hei : Measurable (fun E : κ → ℝ => E i) := measurable_pi_apply i
      exact (hei.div_const (t i)).sub (hea.div_const (t a))
  have hJcomp :
      (fun E : κ → ℝ =>
        (E a / t a, fun i => E i / t i - E a / t a)) ∘ (g ∘ f) = J := by
    funext xy
    apply Prod.ext
    · simp only [Function.comp_apply, J]
      rw [hcoordA]
    · funext i
      by_cases hi : i = a
      · subst i
        simp [J, insertWinnerZero, hcoordA]
      · simp only [Function.comp_apply, J, insertWinnerZero, hi, dite_false]
        rw [hcoordNe xy ⟨i, hi⟩, hcoordA]
  have hsplit :
      Measure.map
          (fun E : κ → ℝ =>
            (E a / t a, fun i => E i / t i - E a / t a))
          ((clockLaw κ).restrict {E | strictClockWin t a E}) =
        Measure.map J (q.restrict P) := by
    rw [← hmap, Measure.restrict_map
      (g.measurable.comp f.measurable) hwin,
      Measure.map_map horig (g.measurable.comp f.measurable), hJcomp]
  have hminLaw :
      Measure.map (fun E : κ → ℝ => E a / t a)
          ((clockLaw κ).restrict {E | strictClockWin t a E}) =
        ENNReal.ofReal (t a) • expMeasure 1 := by
    calc
      Measure.map (fun E : κ → ℝ => E a / t a)
          ((clockLaw κ).restrict {E | strictClockWin t a E}) =
          Measure.map (fun y : ℝ => y / t a)
            (Measure.map (fun E : κ → ℝ => E a)
              ((clockLaw κ).restrict {E | strictClockWin t a E})) := by
        exact (Measure.map_map (measurable_id.div_const (t a))
          (measurable_pi_apply a)).symm
      _ = Measure.map (fun y : ℝ => y / t a)
          (ENNReal.ofReal (t a) • expMeasure (1 / t a)) := by
        rw [map_eval_restrict_strictClockWin t ht htotal a]
      _ = ENNReal.ofReal (t a) •
          Measure.map (fun y : ℝ => y / t a) (expMeasure (1 / t a)) := by
        rw [Measure.map_smul]
      _ = ENNReal.ofReal (t a) • expMeasure 1 := by
        rw [map_div_expMeasure (ht a)]
  have hminSplit :
      Measure.map
          (fun xy : ({i : κ // i ≠ a} → ℝ) × ℝ => xy.2 / t a)
          (q.restrict P) =
        ENNReal.ofReal (t a) • expMeasure 1 := by
    calc
      Measure.map
          (fun xy : ({i : κ // i ≠ a} → ℝ) × ℝ => xy.2 / t a)
          (q.restrict P) =
          Measure.map (fun E : κ → ℝ => E a / t a)
            ((clockLaw κ).restrict {E | strictClockWin t a E}) := by
        rw [← hmap, Measure.restrict_map
          (g.measurable.comp f.measurable) hwin,
          Measure.map_map
            ((measurable_pi_apply a).div_const (t a))
            (g.measurable.comp f.measurable)]
        apply Measure.map_congr
        filter_upwards [] with xy
        dsimp only [Function.comp_apply]
        rw [hcoordA]
      _ = ENNReal.ofReal (t a) • expMeasure 1 := hminLaw
  rw [hsplit]
  let ρ : Measure ({i : κ // i ≠ a} → ℝ) :=
    weightedLosingExcessLaw t a
  let embed : ({i : κ // i ≠ a} → ℝ) → κ → ℝ := insertWinnerZero a
  let ρfull : Measure (κ → ℝ) := Measure.map embed ρ
  have hρprob : IsProbabilityMeasure ρ := by
    dsimp [ρ, weightedLosingExcessLaw]
    infer_instance
  letI : IsProbabilityMeasure ρ := hρprob
  have hembed : Measurable embed := insertWinnerZero_measurable a
  letI : IsProbabilityMeasure ρfull := by
    dsimp [ρfull]
    exact Measure.isProbabilityMeasure_map hembed.aemeasurable
  change Measure.map J (q.restrict P) =
    (ENNReal.ofReal (t a) • expMeasure 1).prod ρfull
  apply Measure.ext_prod
  intro s r hs hr
  let first : (({i : κ // i ≠ a} → ℝ) × ℝ) → ℝ :=
    fun xy => xy.2 / t a
  let B : Set (({i : κ // i ≠ a} → ℝ) × ℝ) := first ⁻¹' s ∩ P
  let A : Set (({i : κ // i ≠ a} → ℝ) × ℝ) := J ⁻¹' (s ×ˢ r) ∩ P
  have hfirstMeas : Measurable first := measurable_snd.div_const (t a)
  have hB : MeasurableSet B :=
    (hs.preimage hfirstMeas).inter hP
  have hA : MeasurableSet A :=
    ((hs.prod hr).preimage hJ).inter hP
  have hone : ∀ᵐ y : ℝ ∂(expMeasure 1), 0 < y := by
    have hnot := measure_eq_zero_iff_ae_notMem.mp expMeasure_one_Iic_zero
    filter_upwards [hnot] with y hy
    simpa only [Set.mem_Iic, not_le] using hy
  have hsections : ∀ᵐ y : ℝ ∂(expMeasure 1),
      loseμ ((fun x : {i : κ // i ≠ a} → ℝ => (x, y)) ⁻¹' A) =
        ρfull r *
          loseμ ((fun x : {i : κ // i ≠ a} → ℝ => (x, y)) ⁻¹' B) := by
    filter_upwards [hone] with y hy
    by_cases hys : y / t a ∈ s
    · let u : ℝ := y / t a
      let loseMap : ({i : κ // i ≠ a} → ℝ) →
          ({i : κ // i ≠ a} → ℝ) :=
        fun x i => x i / t i.1 - u
      let orth : Set ({i : κ // i ≠ a} → ℝ) :=
        Set.pi Set.univ
          (fun i : {i : κ // i ≠ a} => Set.Ioi (t i.1 * u))
      let rpre : Set ({i : κ // i ≠ a} → ℝ) := embed ⁻¹' r
      have hu : 0 ≤ u := div_nonneg hy.le (ht a).le
      have hloseMap : Measurable loseMap := by
        apply measurable_pi_lambda
        intro i
        have hxi : Measurable
            (fun x : {j : κ // j ≠ a} → ℝ => x i) := measurable_pi_apply i
        exact (hxi.div_const (t i.1)).sub_const u
      have horth : MeasurableSet orth := by
        apply MeasurableSet.univ_pi
        intro i
        exact measurableSet_Ioi
      have hrpre : MeasurableSet rpre := hr.preimage hembed
      have hPsec :
          (fun x : {i : κ // i ≠ a} → ℝ => (x, y)) ⁻¹' P = orth := by
        rw [hsectionP]
        congr 1
        funext i
        congr 1
        dsimp only [u]
        field_simp [(ht a).ne']
      have hAsec :
          (fun x : {i : κ // i ≠ a} → ℝ => (x, y)) ⁻¹' A =
            loseMap ⁻¹' rpre ∩ orth := by
        ext x
        have hpiff : (x, y) ∈ P ↔ x ∈ orth := by
          exact Set.ext_iff.mp hPsec x
        simp only [A, Set.mem_preimage, Set.mem_inter_iff,
          Set.mem_prod, J, rpre, embed, loseMap]
        dsimp only [u]
        simpa only [hys, true_and, hpiff]
      have hBsec :
          (fun x : {i : κ // i ≠ a} → ℝ => (x, y)) ⁻¹' B = orth := by
        ext x
        have hpiff : (x, y) ∈ P ↔ x ∈ orth := by
          exact Set.ext_iff.mp hPsec x
        simp only [B, Set.mem_preimage, Set.mem_inter_iff, first]
        simpa only [hys, true_and, hpiff]
      have hlaw := map_losing_scaled_excess t ht a hu
      change Measure.map loseMap (loseμ.restrict orth) =
          (∏ i : {i : κ // i ≠ a},
            ENNReal.ofReal (Real.exp (-(t i.1 * u)))) • ρ at hlaw
      have hlawR := congrArg (fun μ : Measure ({i : κ // i ≠ a} → ℝ) =>
        μ rpre) hlaw
      rw [Measure.map_apply hloseMap hrpre,
        Measure.restrict_apply (hrpre.preimage hloseMap),
        Measure.smul_apply, smul_eq_mul] at hlawR
      have horthMass : loseμ orth =
          ∏ i : {i : κ // i ≠ a},
            ENNReal.ofReal (Real.exp (-(t i.1 * u))) := by
        have hlawU := congrArg
          (fun μ : Measure ({i : κ // i ≠ a} → ℝ) => μ Set.univ) hlaw
        rw [Measure.map_apply hloseMap MeasurableSet.univ] at hlawU
        simp only [Set.preimage_univ] at hlawU
        rw [Measure.restrict_apply MeasurableSet.univ,
          Measure.smul_apply, smul_eq_mul, measure_univ, mul_one] at hlawU
        simpa using hlawU
      have hρfull : ρfull r = ρ rpre := by
        dsimp only [ρfull]
        rw [Measure.map_apply hembed hr]
      rw [hAsec, hBsec, hlawR, horthMass, hρfull]
      ac_rfl
    · have hAempty :
          (fun x : {i : κ // i ≠ a} → ℝ => (x, y)) ⁻¹' A = ∅ := by
        ext x
        simp [A, J, hys]
      have hBempty :
          (fun x : {i : κ // i ≠ a} → ℝ => (x, y)) ⁻¹' B = ∅ := by
        ext x
        simp [B, first, hys]
      rw [hAempty, hBempty, measure_empty, mul_zero]
  rw [Measure.map_apply hJ (hs.prod hr),
    Measure.restrict_apply ((hs.prod hr).preimage hJ)]
  change q A = _
  rw [Measure.prod_apply_symm hA, lintegral_congr_ae hsections,
    lintegral_const_mul _ (measurable_measure_prodMk_right hB),
    ← Measure.prod_apply_symm hB]
  have hqB : q B = (ENNReal.ofReal (t a) • expMeasure 1) s := by
    calc
      q B = (q.restrict P) (first ⁻¹' s) := by
        rw [Measure.restrict_apply (hs.preimage hfirstMeas)]
      _ = Measure.map first (q.restrict P) s := by
        rw [Measure.map_apply hfirstMeas hs]
      _ = (ENNReal.ofReal (t a) • expMeasure 1) s := by
        change Measure.map
            (fun xy : ({i : κ // i ≠ a} → ℝ) × ℝ => xy.2 / t a)
            (q.restrict P) s = _
        rw [hminSplit]
  rw [Measure.prod_prod, hqB]
  ac_rfl

private lemma weightedLexScore_measurable
    {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (t : κ → ℝ) : Measurable (weightedLexScore t) := by
  letI : MeasurableSpace κ := ⊤
  have hlex : Measurable (fun G => weightedLexWinner t G) := by
    unfold weightedLexWinner
    apply measurable_lexMax
    intro b
    exact measurable_const.add (measurable_pi_apply b)
  unfold weightedLexScore weightedValue
  apply Finset.measurable_sum
  intro a _
  exact Measurable.ite
    (measurableSet_singleton a |>.preimage hlex)
    (measurable_const.add (measurable_pi_apply a)) measurable_const

private lemma weightedExcess_measurable
    {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (t : κ → ℝ) : Measurable (weightedExcess t) := by
  apply measurable_pi_lambda
  intro i
  unfold weightedExcess weightedValue
  exact (Real.measurable_exp.comp
      (measurable_const.add (measurable_pi_apply i)).neg).sub
    (Real.measurable_exp.comp (weightedLexScore_measurable t).neg)

private lemma weightedLexScore_eq_value
    {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (t : κ → ℝ) (G : κ → ℝ) :
    weightedLexScore t G = weightedValue t G (weightedLexWinner t G) := by
  unfold weightedLexScore
  rw [Finset.sum_eq_single (weightedLexWinner t G)]
  · simp
  · intro b _ hba
    simp [Ne.symm hba]
  · simp

private lemma weightedLexScore_eq_winnerValue
    {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (t : κ → ℝ) (G : κ → ℝ) :
    weightedLexScore t G = weightedValue t G (weightedWinner t G) := by
  rw [weightedLexScore_eq_value]
  exact le_antisymm
    (weightedWinner_max t G (weightedLexWinner t G))
    (lexMax_max (fun G c => weightedValue t G c) G (weightedWinner t G))

private lemma weightedLexScore_law
    {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (t : κ → ℝ) (ht : ∀ i, 0 < t i) (htotal : ∑ i, t i = 1) :
    Measure.map (weightedLexScore t) (seedLaw κ) = gumbel1 := by
  letI : MeasurableSpace κ := ⊤
  let H : (κ → ℝ) → ℝ := weightedLexScore t
  let Y : (κ → ℝ) → ℝ := fun G => Real.exp (-H G)
  have hH : Measurable H := weightedLexScore_measurable t
  have hY : Measurable Y := Real.measurable_exp.comp hH.neg
  have hlex : Measurable (fun G => weightedLexWinner t G) := by
    unfold weightedLexWinner
    apply measurable_lexMax
    intro b
    exact measurable_const.add (measurable_pi_apply b)
  have hlexSet (a : κ) : MeasurableSet {G | weightedLexWinner t G = a} :=
    measurableSet_singleton a |>.preimage hlex
  have hwinnerLex : ∀ a : κ,
      {G | weightedWinner t G = a} =ᵐ[seedLaw κ]
        {G | weightedLexWinner t G = a} := by
    intro a
    filter_upwards [weightedWinner_ae_eq_lex t] with G hG
    apply propext
    change (weightedWinner t G = a ↔ weightedLexWinner t G = a)
    rw [hG]
  have hpart (a : κ) :
      Measure.map Y
          ((seedLaw κ).restrict {G | weightedLexWinner t G = a}) =
        ENNReal.ofReal (t a) • expMeasure 1 := by
    have hraw :
        Measure.map (fun G : κ → ℝ => Real.exp (-G a))
            ((seedLaw κ).restrict {G | weightedLexWinner t G = a}) =
          ENNReal.ofReal (t a) • expMeasure (1 / t a) := by
      rw [← Measure.restrict_congr_set (hwinnerLex a)]
      exact weightedWinner_raw_restrict_law t ht htotal a
    have hdiv :
        Measure.map (fun G : κ → ℝ => Real.exp (-G a) / t a)
            ((seedLaw κ).restrict {G | weightedLexWinner t G = a}) =
          ENNReal.ofReal (t a) • expMeasure 1 := by
      calc
        Measure.map (fun G : κ → ℝ => Real.exp (-G a) / t a)
            ((seedLaw κ).restrict {G | weightedLexWinner t G = a}) =
            Measure.map (fun x : ℝ => x / t a)
              (Measure.map (fun G : κ → ℝ => Real.exp (-G a))
                ((seedLaw κ).restrict {G | weightedLexWinner t G = a})) := by
          simpa only [Function.comp_def, id_eq] using
            (Measure.map_map (measurable_id.div_const (t a))
              (Real.measurable_exp.comp (measurable_pi_apply a).neg)).symm
        _ = Measure.map (fun x : ℝ => x / t a)
            (ENNReal.ofReal (t a) • expMeasure (1 / t a)) := by rw [hraw]
        _ = ENNReal.ofReal (t a) •
            Measure.map (fun x : ℝ => x / t a) (expMeasure (1 / t a)) := by
          rw [Measure.map_smul]
        _ = ENNReal.ofReal (t a) • expMeasure 1 := by
          rw [map_div_expMeasure (ht a)]
    calc
      Measure.map Y
          ((seedLaw κ).restrict {G | weightedLexWinner t G = a}) =
          Measure.map (fun G : κ → ℝ => Real.exp (-G a) / t a)
            ((seedLaw κ).restrict {G | weightedLexWinner t G = a}) := by
        apply Measure.map_congr
        filter_upwards [ae_restrict_mem (hlexSet a)] with G hGa
        dsimp only [Y, H]
        rw [weightedLexScore_eq_value, hGa]
        unfold weightedValue
        rw [neg_add_rev, Real.exp_add]
        have hlog : Real.exp (-Real.log (t a)) = 1 / t a := by
          rw [Real.exp_neg, Real.exp_log (ht a)]
          rw [one_div]
        rw [hlog]
        simp [div_eq_mul_inv]
      _ = ENNReal.ofReal (t a) • expMeasure 1 := hdiv
  have hdisj : Pairwise (fun a b : κ => Disjoint
      {G : κ → ℝ | weightedLexWinner t G = a}
      {G : κ → ℝ | weightedLexWinner t G = b}) := by
    intro a b hab
    rw [Set.disjoint_left]
    intro G ha hb
    exact hab (ha.symm.trans hb)
  have hunion : (⋃ a : κ,
      {G : κ → ℝ | weightedLexWinner t G = a}) = Set.univ := by
    ext G
    simp
  have hdecomp : seedLaw κ = Measure.sum fun a : κ =>
      (seedLaw κ).restrict {G | weightedLexWinner t G = a} := by
    calc
      seedLaw κ = (seedLaw κ).restrict Set.univ := by rw [Measure.restrict_univ]
      _ = (seedLaw κ).restrict
          (⋃ a : κ, {G : κ → ℝ | weightedLexWinner t G = a}) := by
        rw [hunion]
      _ = Measure.sum fun a : κ =>
          (seedLaw κ).restrict {G | weightedLexWinner t G = a} :=
        Measure.restrict_iUnion hdisj hlexSet
  have hmapY : Measure.map Y (seedLaw κ) = expMeasure 1 := by
    rw [hdecomp, Measure.map_sum hY.aemeasurable]
    simp_rw [hpart]
    ext s hs
    rw [Measure.sum_apply _ hs]
    simp only [Measure.smul_apply, smul_eq_mul, tsum_fintype]
    rw [← Finset.sum_mul]
    have hof : ∑ a, ENNReal.ofReal (t a) = 1 := by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun a _ => (ht a).le), htotal]
      norm_num
    rw [hof, one_mul]
  calc
    Measure.map H (seedLaw κ) =
        Measure.map ((-Real.log) ∘ Y) (seedLaw κ) := by
      apply Measure.map_congr
      filter_upwards [] with G
      dsimp only [Y, Function.comp_apply, Pi.neg_apply]
      rw [Real.log_exp]
      ring
    _ = Measure.map (-Real.log)
        (Measure.map Y (seedLaw κ)) := by
      exact (Measure.map_map Real.measurable_log.neg hY).symm
    _ = gumbel1 := by
      rw [hmapY]
      rfl

/- The one-block independence statement behind Lemma 7.2(a).  It is proved
by partitioning the exponential clocks according to their strict winner and
then summing the fixed-cell factorization above. -/
private theorem weighted_score_excess_factorization
    {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (t : κ → ℝ) (ht : ∀ i, 0 < t i) (htotal : ∑ i, t i = 1) :
    Measure.map
        (fun G : κ → ℝ => (weightedLexScore t G, weightedExcess t G))
        (seedLaw κ) =
      (Measure.map (weightedLexScore t) (seedLaw κ)).prod
        (Measure.map (weightedExcess t) (seedLaw κ)) := by
  letI : MeasurableSpace κ := ⊤
  letI : IsProbabilityMeasure (expMeasure 1) :=
    isProbabilityMeasure_expMeasure zero_lt_one
  letI : ∀ _ : κ, SigmaFinite (expMeasure 1) := fun _ => inferInstance
  let H : (κ → ℝ) → ℝ := weightedLexScore t
  let R : (κ → ℝ) → (κ → ℝ) := weightedExcess t
  let J : (κ → ℝ) → ℝ × (κ → ℝ) := fun G => (H G, R G)
  let F : (κ → ℝ) → (κ → ℝ) := fun E i => -Real.log (E i)
  let ρ : κ → Measure (κ → ℝ) := fun a =>
    Measure.map (insertWinnerZero a) (weightedLosingExcessLaw t a)
  letI (a : κ) : IsProbabilityMeasure (ρ a) := by
    letI (i : {i : κ // i ≠ a}) : IsProbabilityMeasure
        (expMeasure (t i.1)) := isProbabilityMeasure_expMeasure (ht i.1)
    dsimp [ρ, weightedLosingExcessLaw]
    exact Measure.isProbabilityMeasure_map
      (insertWinnerZero_measurable a).aemeasurable
  let η : Measure (κ → ℝ) := Measure.sum fun a : κ =>
    ENNReal.ofReal (t a) • ρ a
  have hH : Measurable H := weightedLexScore_measurable t
  have hR : Measurable R := weightedExcess_measurable t
  have hJ : Measurable J := hH.prodMk hR
  have hF : Measurable F := measurable_pi_lambda _ fun i =>
    (Real.measurable_log.comp (measurable_pi_apply i)).neg
  have hlex : Measurable (fun G => weightedLexWinner t G) := by
    unfold weightedLexWinner
    apply measurable_lexMax
    intro b
    exact measurable_const.add (measurable_pi_apply b)
  have hlexSet (a : κ) : MeasurableSet {G | weightedLexWinner t G = a} :=
    measurableSet_singleton a |>.preimage hlex
  have hpart (a : κ) :
      Measure.map J
          ((seedLaw κ).restrict {G | weightedLexWinner t G = a}) =
        (ENNReal.ofReal (t a) • gumbel1).prod (ρ a) := by
    let C : (κ → ℝ) → ℝ × (κ → ℝ) := fun E =>
      (E a / t a, fun i => E i / t i - E a / t a)
    let P : ℝ × (κ → ℝ) → ℝ × (κ → ℝ) :=
      Prod.map (-Real.log) id
    have hC : Measurable C := by
      have hea : Measurable (fun E : κ → ℝ => E a) := measurable_pi_apply a
      apply Measurable.prodMk
      · exact hea.div_const (t a)
      · apply measurable_pi_lambda
        intro i
        have hei : Measurable (fun E : κ → ℝ => E i) := measurable_pi_apply i
        exact (hei.div_const (t i)).sub (hea.div_const (t a))
    have hP : Measurable P := Real.measurable_log.neg.prodMap measurable_id
    have hpos : ∀ᵐ E ∂(clockLaw κ), ∀ i, 0 < E i := by
      unfold clockLaw
      have hone : ∀ᵐ x : ℝ ∂(expMeasure 1), 0 < x := by
        have hnot := measure_eq_zero_iff_ae_notMem.mp expMeasure_one_Iic_zero
        filter_upwards [hnot] with x hx
        simpa only [Set.mem_Iic, not_le] using hx
      exact ae_forall_fintype fun i =>
        Measure.tendsto_eval_ae_ae.eventually hone
    have htieSeed := weighted_ae_no_ties t
    change ∀ᵐ G ∂((clockLaw κ).map F), ∀ b c, b ≠ c →
      weightedValue t G b ≠ weightedValue t G c at htieSeed
    have htieClock : ∀ᵐ E ∂(clockLaw κ), ∀ b c, b ≠ c →
        weightedValue t (F E) b ≠ weightedValue t (F E) c :=
      ae_of_ae_map hF.aemeasurable htieSeed
    have hpre :
        F ⁻¹' {G | weightedLexWinner t G = a} =ᵐ[clockLaw κ]
          {E | strictClockWin t a E} := by
      filter_upwards [hpos, htieClock] with E hE htie
      apply propext
      change (weightedLexWinner t (F E) = a ↔ strictClockWin t a E)
      exact weightedLexWinner_clock_iff t ht E hE a
        (fun b hba => htie b a hba)
    have hseedClock :
        (seedLaw κ).restrict {G | weightedLexWinner t G = a} =
          Measure.map F
            ((clockLaw κ).restrict {E | strictClockWin t a E}) := by
      unfold seedLaw
      rw [Measure.restrict_map hF (hlexSet a),
        Measure.restrict_congr_set hpre]
    have hcomp :
        (J ∘ F) =ᵐ[(clockLaw κ).restrict {E | strictClockWin t a E}]
          P ∘ C := by
      filter_upwards [ae_restrict_of_ae hpos,
        ae_restrict_of_ae htieClock,
        ae_restrict_mem (show MeasurableSet
          {E : κ → ℝ | strictClockWin t a E} by
            unfold strictClockWin
            measurability)] with E hE htie hwin
      have hlexa : weightedLexWinner t (F E) = a :=
        (weightedLexWinner_clock_iff t ht E hE a
          (fun b hba => htie b a hba)).2 hwin
      apply Prod.ext
      · dsimp only [J, H, F, P, C, Function.comp_apply, Prod.map_apply,
          id_eq]
        rw [weightedLexScore_eq_value, hlexa]
        unfold weightedValue
        change Real.log (t a) - Real.log (E a) =
          -Real.log (E a / t a)
        rw [Real.log_div (hE a).ne' (ht a).ne']
        ring
      · funext i
        dsimp only [J, R, F, P, C, Function.comp_apply, Prod.map_apply,
          id_eq]
        unfold weightedExcess
        have hi :
            Real.exp
                (-(weightedValue t (fun j => -Real.log (E j)) i)) =
              E i / t i := by
          unfold weightedValue
          rw [show -(Real.log (t i) + -Real.log (E i)) =
              -Real.log (t i) + Real.log (E i) by ring,
            Real.exp_add, Real.exp_neg, Real.exp_log (ht i),
            Real.exp_log (hE i)]
          ring
        have ha :
            Real.exp
                (-(weightedLexScore t (fun j => -Real.log (E j)))) =
              E a / t a := by
          rw [weightedLexScore_eq_value, hlexa]
          unfold weightedValue
          rw [show -(Real.log (t a) + -Real.log (E a)) =
              -Real.log (t a) + Real.log (E a) by ring,
            Real.exp_add, Real.exp_neg, Real.exp_log (ht a),
            Real.exp_log (hE a)]
          ring
        rw [hi, ha]
    calc
      Measure.map J
          ((seedLaw κ).restrict {G | weightedLexWinner t G = a}) =
          Measure.map J
            (Measure.map F
              ((clockLaw κ).restrict {E | strictClockWin t a E})) := by
        rw [hseedClock]
      _ = Measure.map (J ∘ F)
          ((clockLaw κ).restrict {E | strictClockWin t a E}) :=
        Measure.map_map hJ hF
      _ = Measure.map (P ∘ C)
          ((clockLaw κ).restrict {E | strictClockWin t a E}) :=
        Measure.map_congr hcomp
      _ = Measure.map P
          (Measure.map C
            ((clockLaw κ).restrict {E | strictClockWin t a E})) :=
        (Measure.map_map hP hC).symm
      _ = Measure.map P
          ((ENNReal.ofReal (t a) • expMeasure 1).prod (ρ a)) := by
        rw [clock_min_excess_restrict_factorization t ht htotal a]
      _ = (Measure.map (-Real.log)
            (ENNReal.ofReal (t a) • expMeasure 1)).prod
          (Measure.map id (ρ a)) := by
        exact (Measure.map_prod_map
          (ENNReal.ofReal (t a) • expMeasure 1) (ρ a)
          Real.measurable_log.neg measurable_id).symm
      _ = (ENNReal.ofReal (t a) • gumbel1).prod (ρ a) := by
        rw [Measure.map_smul, Measure.map_id]
        rfl
  have hdisj : Pairwise (fun a b : κ => Disjoint
      {G : κ → ℝ | weightedLexWinner t G = a}
      {G : κ → ℝ | weightedLexWinner t G = b}) := by
    intro a b hab
    rw [Set.disjoint_left]
    intro G ha hb
    exact hab (ha.symm.trans hb)
  have hunion : (⋃ a : κ,
      {G : κ → ℝ | weightedLexWinner t G = a}) = Set.univ := by
    ext G
    simp
  have hdecomp : seedLaw κ = Measure.sum fun a : κ =>
      (seedLaw κ).restrict {G | weightedLexWinner t G = a} := by
    calc
      seedLaw κ = (seedLaw κ).restrict Set.univ := by
        rw [Measure.restrict_univ]
      _ = (seedLaw κ).restrict
          (⋃ a : κ, {G : κ → ℝ | weightedLexWinner t G = a}) := by
        rw [hunion]
      _ = Measure.sum fun a : κ =>
          (seedLaw κ).restrict {G | weightedLexWinner t G = a} :=
        Measure.restrict_iUnion hdisj hlexSet
  have hjoint : Measure.map J (seedLaw κ) = gumbel1.prod η := by
    rw [hdecomp, Measure.map_sum hJ.aemeasurable]
    calc
      Measure.sum (fun a : κ => Measure.map J
          ((seedLaw κ).restrict {G | weightedLexWinner t G = a})) =
          Measure.sum (fun a : κ =>
            (ENNReal.ofReal (t a) • gumbel1).prod (ρ a)) := by
        congr 1
        funext a
        exact hpart a
      _ = Measure.sum (fun a : κ =>
          ENNReal.ofReal (t a) • gumbel1.prod (ρ a)) := by
        congr 1
        funext a
        rw [Measure.prod_smul_left]
      _ =
          Measure.sum (fun a : κ =>
            gumbel1.prod (ENNReal.ofReal (t a) • ρ a)) := by
        congr 1
        funext a
        rw [Measure.prod_smul_right]
      _ = gumbel1.prod η := by
        dsimp only [η]
        rw [Measure.prod_sum_right]
  have hsecond : Measure.map R (seedLaw κ) = η := by
    calc
      Measure.map R (seedLaw κ) =
          Measure.map Prod.snd (Measure.map J (seedLaw κ)) := by
        rw [Measure.map_map measurable_snd hJ]
        rfl
      _ = Measure.map Prod.snd (gumbel1.prod η) := by rw [hjoint]
      _ = η := by
        rw [Measure.map_snd_prod, measure_univ, one_smul]
  change Measure.map J (seedLaw κ) =
    (Measure.map H (seedLaw κ)).prod (Measure.map R (seedLaw κ))
  rw [hjoint, weightedLexScore_law t ht htotal, hsecond]

/-- Lemma 7.4 / equation (7.1): after conditioning on the cluster winner,
the raw winning clock is exponential with mean `σ_b(z)`.  Multiplication by
`Q_g(z)σ_b(z)` gives the exact joint context density used by `raceScalar`. -/
private theorem exact_winner_clock_law {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D) (b : K.κ) (z : α × β)
    (hz : z ∈ support p) :
    Measure.map (fun G : K.κ → ℝ => Real.exp (-G b))
        (clusterSeedLawGivenWinner K b z) =
      K.clockLawGiven b z := by
  have hs := K.sigma_pos b z hz
  unfold clusterSeedLawGivenWinner Clustering.clockLawGiven
  rw [if_neg hs.ne']
  change Measure.map (fun G : K.κ → ℝ => Real.exp (-G b))
      ((ENNReal.ofReal (K.sigma b z))⁻¹ •
        (seedLaw K.κ).restrict
          {G | weightedWinner (fun c => K.sigma c z) G = b}) =
    expMeasure (1 / K.sigma b z)
  exact weightedWinner_clock_law (fun c => K.sigma c z)
    (fun c => K.sigma_pos c z hz) (raceSigma_sum_eq_one K z hz) b

/-! ### Lemmas 7.2 and 7.3: grouping and winner entropy -/

private noncomputable def withinClusterWeight {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D) (c : K.κ)
    (u : clusterFiber K c) : ℝ :=
  D.L.prior u.1 / K.s c

private lemma withinClusterWeight_pos {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D) (c : K.κ)
    (u : clusterFiber K c) : 0 < withinClusterWeight K c u := by
  exact div_pos (D.prior_pos u.1) (clusterMass_pos K c)

private lemma withinClusterWeight_sum {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D) (c : K.κ) :
    ∑ u : clusterFiber K c, withinClusterWeight K c u = 1 := by
  unfold withinClusterWeight
  rw [← Finset.sum_div]
  have hnum : (∑ u : clusterFiber K c, D.L.prior u.1) = K.s c := by
    unfold Clustering.s
    simpa using
      (Finset.sum_subtype_eq_sum_filter
        (s := (Finset.univ : Finset D.L.ι)) D.L.prior
        (p := fun ℓ => K.cl ℓ = c))
  rw [hnum, div_self (clusterMass_pos K c).ne']

private lemma groupedG_eq_weightedLexScore {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D) (ε : D.L.ι → ℝ) (c : K.κ) :
    groupedG K ε c =
      weightedLexScore (withinClusterWeight K c) (fun u => ε u.1) := by
  rw [weightedLexScore_eq_winnerValue]
  rfl

/- Reindex the iid label seeds by their cluster fibres.  This is the
measure-theoretic independence input for both parts of Lemma 7.2(a). -/
private lemma grouped_block_law {p : α × β → ℝ} {D : SeedSetup p}
    (K : Clustering D) :
    Measure.map (fun ε : D.L.ι → ℝ =>
        fun c : K.κ => fun u : clusterFiber K c => ε u.1)
        (seedLaw D.L.ι) =
      Measure.pi (fun c : K.κ => seedLaw (clusterFiber K c)) := by
  let e : (Σ c : K.κ, clusterFiber K c) ≃ D.L.ι :=
    Equiv.sigmaFiberEquiv K.cl
  let reindex : (D.L.ι → ℝ) ≃ᵐ
      ((u : Σ c : K.κ, clusterFiber K c) → ℝ) :=
    MeasurableEquiv.piCongrLeft
      (fun _ : Σ c : K.κ, clusterFiber K c => ℝ) e.symm
  let curry :
      (((u : Σ c : K.κ, clusterFiber K c) → ℝ)) ≃ᵐ
        ((c : K.κ) → clusterFiber K c → ℝ) :=
    MeasurableEquiv.piCurry
      (fun (_c : K.κ) (_u : clusterFiber K _c) => ℝ)
  have hfun :
      (fun ε : D.L.ι → ℝ =>
          fun c : K.κ => fun u : clusterFiber K c => ε u.1) =
        curry ∘ reindex := by
    funext ε c u
    change ε u.1 = reindex ε ⟨c, u⟩
    change ε u.1 =
      (MeasurableEquiv.piCongrLeft
        (fun _ : Σ c : K.κ, clusterFiber K c => ℝ) e.symm ε) ⟨c, u⟩
    conv_rhs => rw [← e.symm_apply_apply ⟨c, u⟩]
    rw [MeasurableEquiv.piCongrLeft_apply_apply]
    rfl
  have hreindex :
      Measure.map reindex (Measure.pi (fun _ : D.L.ι => gumbel1)) =
        Measure.pi (fun _ : Σ c : K.κ, clusterFiber K c => gumbel1) := by
    simpa [reindex, e] using
      (Measure.pi_map_piCongrLeft e.symm
        (fun _ : Σ c : K.κ, clusterFiber K c => gumbel1))
  have hcurry :
      Measure.map curry
          (Measure.pi (fun _ : Σ c : K.κ, clusterFiber K c => gumbel1)) =
        Measure.pi (fun c : K.κ => seedLaw (clusterFiber K c)) := by
    simpa only [Measure.infinitePi_eq_pi, seedLaw_eq_pi_gumbel1] using
      (Measure.infinitePi_map_piCurry
        (μ := fun (_c : K.κ) (_u : clusterFiber K _c) => gumbel1))
  rw [hfun, ← Measure.map_map curry.measurable reindex.measurable,
    seedLaw_eq_pi_gumbel1, hreindex, hcurry]

/-- Lemma 7.2(a), first part: the grouped maxima are iid standard Gumbels. -/
private theorem grouped_gumbel_law {p : α × β → ℝ} {D : SeedSetup p}
    (K : Clustering D) :
    Measure.map (groupedG K) (seedLaw D.L.ι) = seedLaw K.κ := by
  let block : (D.L.ι → ℝ) →
      ((c : K.κ) → clusterFiber K c → ℝ) :=
    fun ε c u => ε u.1
  let score : (((c : K.κ) → clusterFiber K c → ℝ)) → K.κ → ℝ :=
    fun ξ c => weightedLexScore (withinClusterWeight K c) (ξ c)
  have hblock : Measurable block := by
    apply measurable_pi_lambda
    intro c
    apply measurable_pi_lambda
    intro u
    exact measurable_pi_apply u.1
  have hscoreCoord (c : K.κ) :
      Measurable (fun ξ : clusterFiber K c → ℝ =>
        weightedLexScore (withinClusterWeight K c) ξ) :=
    weightedLexScore_measurable (withinClusterWeight K c)
  have hscore : Measurable score := by
    apply measurable_pi_lambda
    intro c
    exact (hscoreCoord c).comp (measurable_pi_apply c)
  have hG : groupedG K = score ∘ block := by
    funext ε c
    exact groupedG_eq_weightedLexScore K ε c
  letI (c : K.κ) : IsProbabilityMeasure
      (Measure.map
        (fun ξ : clusterFiber K c → ℝ =>
          weightedLexScore (withinClusterWeight K c) ξ)
        (seedLaw (clusterFiber K c))) :=
    Measure.isProbabilityMeasure_map (hscoreCoord c).aemeasurable
  have hpi :
      Measure.map score
          (Measure.pi (fun c : K.κ => seedLaw (clusterFiber K c))) =
        Measure.pi (fun c : K.κ =>
          Measure.map
            (fun ξ : clusterFiber K c → ℝ =>
              weightedLexScore (withinClusterWeight K c) ξ)
            (seedLaw (clusterFiber K c))) := by
    simpa only [Measure.infinitePi_eq_pi] using
      (Measure.infinitePi_map_pi
        (μ := fun c : K.κ => seedLaw (clusterFiber K c))
        (f := fun c ξ => weightedLexScore (withinClusterWeight K c) ξ)
        (fun c => hscoreCoord c))
  calc
    Measure.map (groupedG K) (seedLaw D.L.ι) =
        Measure.map (score ∘ block) (seedLaw D.L.ι) := by rw [hG]
    _ = Measure.map score (Measure.map block (seedLaw D.L.ι)) :=
      (Measure.map_map hscore hblock).symm
    _ = Measure.map score
        (Measure.pi (fun c : K.κ => seedLaw (clusterFiber K c))) := by
      rw [grouped_block_law K]
    _ = Measure.pi (fun c : K.κ =>
        Measure.map
          (fun ξ : clusterFiber K c → ℝ =>
            weightedLexScore (withinClusterWeight K c) ξ)
          (seedLaw (clusterFiber K c))) := hpi
    _ = Measure.pi (fun _ : K.κ => gumbel1) := by
      congr 1
      funext c
      exact weightedLexScore_law (withinClusterWeight K c)
        (withinClusterWeight_pos K c) (withinClusterWeight_sum K c)
    _ = seedLaw K.κ := (seedLaw_eq_pi_gumbel1 K.κ).symm

/-- Lemma 7.2(a), factorization part: the grouped maxima are independent of
the full within-cluster residual vectors (which include the winners). -/
private theorem grouped_seed_factorization {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D) :
    Measure.map (fun ε => (groupedG K ε, groupedResidual K ε))
        (seedLaw D.L.ι) =
      (seedLaw K.κ).prod
        (Measure.map (groupedResidual K) (seedLaw D.L.ι)) := by
  let Block : Type := (c : K.κ) → clusterFiber K c → ℝ
  let Ambient : Type := D.L.ι → ℝ
  let Residual : Type := (c : K.κ) → clusterFiber K c → ℝ
  let block : (D.L.ι → ℝ) → Block :=
    fun ε c u => ε u.1
  let S : (c : K.κ) → (clusterFiber K c → ℝ) → ℝ :=
    fun c ξ => weightedLexScore (withinClusterWeight K c) ξ
  let X : (c : K.κ) → (clusterFiber K c → ℝ) →
      (clusterFiber K c → ℝ) :=
    fun c ξ => weightedExcess (withinClusterWeight K c) ξ
  let embed : (c : K.κ) → (clusterFiber K c → ℝ) → Ambient :=
    fun c r ℓ => if h : K.cl ℓ = c then r ⟨ℓ, h⟩ else 0
  let T : (c : K.κ) → (clusterFiber K c → ℝ) → Ambient :=
    fun c ξ => embed c (X c ξ)
  let U : Block → (K.κ → ℝ × Ambient) :=
    fun ξ c => (S c (ξ c), T c (ξ c))
  let separate : (K.κ → ℝ × Ambient) →
      (K.κ → ℝ) × (K.κ → Ambient) :=
    fun q => (fun c => (q c).1, fun c => (q c).2)
  let decode : (K.κ → Ambient) → Residual :=
    fun q c u => q c u.1
  let Q : ((K.κ → ℝ) × (K.κ → Ambient)) →
      ((K.κ → ℝ) × Residual) := Prod.map id decode
  let target : (D.L.ι → ℝ) → (K.κ → ℝ) × Residual :=
    fun ε => (groupedG K ε, groupedResidual K ε)
  let μ : K.κ → Measure ℝ := fun c =>
    Measure.map (S c) (seedLaw (clusterFiber K c))
  let ν : K.κ → Measure Ambient := fun c =>
    Measure.map (T c) (seedLaw (clusterFiber K c))
  let N : Measure Residual := Measure.map decode (Measure.pi ν)
  have hblock : Measurable block := by
    apply measurable_pi_lambda
    intro c
    apply measurable_pi_lambda
    intro u
    exact measurable_pi_apply u.1
  have hS (c : K.κ) : Measurable (S c) :=
    weightedLexScore_measurable (withinClusterWeight K c)
  have hX (c : K.κ) : Measurable (X c) :=
    weightedExcess_measurable (withinClusterWeight K c)
  have hembed (c : K.κ) : Measurable (embed c) := by
    apply measurable_pi_lambda
    intro ℓ
    by_cases h : K.cl ℓ = c
    · simpa [embed, h] using
        (measurable_pi_apply
          (⟨ℓ, h⟩ : clusterFiber K c))
    · simpa [embed, h] using
        (measurable_const : Measurable
          (fun _ : clusterFiber K c → ℝ => (0 : ℝ)))
  have hT (c : K.κ) : Measurable (T c) :=
    (hembed c).comp (hX c)
  have hU : Measurable U := by
    apply measurable_pi_lambda
    intro c
    exact ((hS c).prodMk (hT c)).comp (measurable_pi_apply c)
  have hseparate : Measurable separate := by
    apply Measurable.prodMk
    · apply measurable_pi_lambda
      intro c
      exact measurable_fst.comp (measurable_pi_apply c)
    · apply measurable_pi_lambda
      intro c
      exact measurable_snd.comp (measurable_pi_apply c)
  have hdecode : Measurable decode := by
    apply measurable_pi_lambda
    intro c
    apply measurable_pi_lambda
    intro u
    exact (measurable_pi_apply u.1).comp (measurable_pi_apply c)
  have hQ : Measurable Q := measurable_id.prodMap hdecode
  letI (c : K.κ) : IsProbabilityMeasure (μ c) := by
    dsimp only [μ]
    exact Measure.isProbabilityMeasure_map (hS c).aemeasurable
  letI (c : K.κ) : IsProbabilityMeasure (ν c) := by
    dsimp only [ν]
    exact Measure.isProbabilityMeasure_map (hT c).aemeasurable
  have hfactor (c : K.κ) :
      Measure.map (fun ξ => (S c ξ, T c ξ))
          (seedLaw (clusterFiber K c)) =
        (μ c).prod (ν c) := by
    have hbase := weighted_score_excess_factorization
      (withinClusterWeight K c) (withinClusterWeight_pos K c)
      (withinClusterWeight_sum K c)
    change Measure.map (fun ξ => (S c ξ, X c ξ))
        (seedLaw (clusterFiber K c)) =
      (Measure.map (S c) (seedLaw (clusterFiber K c))).prod
        (Measure.map (X c) (seedLaw (clusterFiber K c))) at hbase
    calc
      Measure.map (fun ξ => (S c ξ, T c ξ))
          (seedLaw (clusterFiber K c)) =
          Measure.map (Prod.map id (embed c))
            (Measure.map (fun ξ => (S c ξ, X c ξ))
              (seedLaw (clusterFiber K c))) := by
        rw [Measure.map_map (measurable_id.prodMap (hembed c))
          ((hS c).prodMk (hX c))]
        rfl
      _ = Measure.map (Prod.map id (embed c))
          ((Measure.map (S c) (seedLaw (clusterFiber K c))).prod
            (Measure.map (X c) (seedLaw (clusterFiber K c)))) := by
        rw [hbase]
      _ = (Measure.map id
            (Measure.map (S c) (seedLaw (clusterFiber K c)))).prod
          (Measure.map (embed c)
            (Measure.map (X c) (seedLaw (clusterFiber K c)))) := by
        exact (Measure.map_prod_map
          (Measure.map (S c) (seedLaw (clusterFiber K c)))
          (Measure.map (X c) (seedLaw (clusterFiber K c)))
          measurable_id (hembed c)).symm
      _ = (μ c).prod (ν c) := by
        rw [Measure.map_id, Measure.map_map (hembed c) (hX c)]
        rfl
  have hmapU :
      Measure.map U
          (Measure.pi (fun c : K.κ => seedLaw (clusterFiber K c))) =
        Measure.pi (fun c : K.κ => (μ c).prod (ν c)) := by
    letI (c : K.κ) : IsProbabilityMeasure
        (Measure.map (fun ξ => (S c ξ, T c ξ))
          (seedLaw (clusterFiber K c))) :=
      Measure.isProbabilityMeasure_map ((hS c).prodMk (hT c)).aemeasurable
    calc
      Measure.map U
          (Measure.pi (fun c : K.κ => seedLaw (clusterFiber K c))) =
          Measure.pi (fun c : K.κ =>
            Measure.map (fun ξ => (S c ξ, T c ξ))
              (seedLaw (clusterFiber K c))) := by
        simpa only [U, Measure.infinitePi_eq_pi] using
          (Measure.infinitePi_map_pi
            (μ := fun c : K.κ => seedLaw (clusterFiber K c))
            (f := fun c ξ => (S c ξ, T c ξ))
            (fun c => (hS c).prodMk (hT c)))
      _ = Measure.pi (fun c : K.κ => (μ c).prod (ν c)) := by
        congr 1
        funext c
        exact hfactor c
  have hseparateLaw :
      Measure.map separate
          (Measure.pi (fun c : K.κ => (μ c).prod (ν c))) =
        (Measure.pi μ).prod (Measure.pi ν) := by
    change Measure.map
        (MeasurableEquiv.arrowProdEquivProdArrow ℝ Ambient K.κ)
        (Measure.pi (fun c : K.κ => (μ c).prod (ν c))) =
      (Measure.pi μ).prod (Measure.pi ν)
    exact (measurePreserving_arrowProdEquivProdArrow
      ℝ Ambient K.κ μ ν).map_eq
  have hμlaw : Measure.pi μ = seedLaw K.κ := by
    calc
      Measure.pi μ = Measure.pi (fun _ : K.κ => gumbel1) := by
        congr 1
        funext c
        dsimp only [μ, S]
        exact weightedLexScore_law (withinClusterWeight K c)
          (withinClusterWeight_pos K c) (withinClusterWeight_sum K c)
      _ = seedLaw K.κ := (seedLaw_eq_pi_gumbel1 K.κ).symm
  have hQprod :
      Measure.map Q ((Measure.pi μ).prod (Measure.pi ν)) =
        (Measure.pi μ).prod N := by
    calc
      Measure.map Q ((Measure.pi μ).prod (Measure.pi ν)) =
          (Measure.map id (Measure.pi μ)).prod
            (Measure.map decode (Measure.pi ν)) := by
        exact (Measure.map_prod_map (Measure.pi μ) (Measure.pi ν)
          measurable_id hdecode).symm
      _ = (Measure.pi μ).prod N := by
        rw [Measure.map_id]
  have hscore (ε : D.L.ι → ℝ) (c : K.κ) :
      S c (block ε c) = groupedG K ε c := by
    dsimp only [S, block]
    exact (groupedG_eq_weightedLexScore K ε c).symm
  have hresidual (ε : D.L.ι → ℝ) (c : K.κ)
      (u : clusterFiber K c) :
      X c (block ε c) u = groupedResidual K ε c u := by
    dsimp only [X, block]
    unfold weightedExcess weightedValue groupedResidual withinClusterWeight
    rw [groupedG_eq_weightedLexScore]
    rfl
  have htarget : target = Q ∘ separate ∘ U ∘ block := by
    funext ε
    apply Prod.ext
    · funext c
      dsimp only [target, Q, separate, U, Function.comp_apply,
        Prod.map_apply, id_eq]
      exact (hscore ε c).symm
    · funext c u
      dsimp only [target, Q, separate, U, decode, T, embed,
        Function.comp_apply, Prod.map_apply, id_eq]
      rw [dif_pos u.2]
      simpa using (hresidual ε c u).symm
  have htargetMeas : Measurable target := by
    rw [htarget]
    exact hQ.comp (hseparate.comp (hU.comp hblock))
  have hjoint : Measure.map target (seedLaw D.L.ι) =
      (seedLaw K.κ).prod N := by
    calc
      Measure.map target (seedLaw D.L.ι) =
          Measure.map Q
            (Measure.map separate
              (Measure.map U
                (Measure.map block (seedLaw D.L.ι)))) := by
        rw [Measure.map_map hU hblock,
          Measure.map_map hseparate (hU.comp hblock),
          Measure.map_map hQ (hseparate.comp (hU.comp hblock))]
        rw [htarget]
      _ = Measure.map Q
          (Measure.map separate
            (Measure.map U
              (Measure.pi
                (fun c : K.κ => seedLaw (clusterFiber K c))))) := by
        rw [grouped_block_law K]
      _ = Measure.map Q
          (Measure.map separate
            (Measure.pi (fun c : K.κ => (μ c).prod (ν c)))) := by
        rw [hmapU]
      _ = Measure.map Q ((Measure.pi μ).prod (Measure.pi ν)) := by
        rw [hseparateLaw]
      _ = (Measure.pi μ).prod N := hQprod
      _ = (seedLaw K.κ).prod N := by rw [hμlaw]
  have hsecond : Measure.map (groupedResidual K) (seedLaw D.L.ι) = N := by
    calc
      Measure.map (groupedResidual K) (seedLaw D.L.ι) =
          Measure.map Prod.snd
            (Measure.map target (seedLaw D.L.ι)) := by
        rw [Measure.map_map measurable_snd htargetMeas]
        rfl
      _ = Measure.map Prod.snd ((seedLaw K.κ).prod N) := by rw [hjoint]
      _ = N := by
        rw [Measure.map_snd_prod, measure_univ, one_smul]
  change Measure.map target (seedLaw D.L.ι) =
    (seedLaw K.κ).prod
      (Measure.map (groupedResidual K) (seedLaw D.L.ι))
  rw [hjoint, hsecond]

private noncomputable def groupedPair {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D) (ε : D.L.ι → ℝ) :
    (K.κ → ℝ) × ((c : K.κ) → clusterFiber K c → ℝ) :=
  (groupedG K ε, groupedResidual K ε)

private noncomputable def groupedReconstruct {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D)
    (q : (K.κ → ℝ) × ((c : K.κ) → clusterFiber K c → ℝ))
    (ℓ : D.L.ι) : ℝ :=
  -Real.log ((D.L.prior ℓ / K.s (K.cl ℓ)) *
    (q.2 (K.cl ℓ) ⟨ℓ, rfl⟩ + Real.exp (-q.1 (K.cl ℓ))))

private lemma groupedPair_measurable {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D) : Measurable (groupedPair K) := by
  have hG : Measurable (groupedG K) := by
    apply measurable_pi_lambda
    intro c
    have hblock : Measurable
        (fun ε : D.L.ι → ℝ => fun u : clusterFiber K c => ε u.1) := by
      apply measurable_pi_lambda
      intro u
      exact measurable_pi_apply u.1
    have hs := (weightedLexScore_measurable (withinClusterWeight K c)).comp hblock
    convert hs using 1
    funext ε
    exact groupedG_eq_weightedLexScore K ε c
  have hR : Measurable (groupedResidual K) := by
    apply measurable_pi_lambda
    intro c
    apply measurable_pi_lambda
    intro u
    have hε : Measurable (fun ε : D.L.ι → ℝ => ε u.1) :=
      measurable_pi_apply u.1
    have hGc : Measurable (fun ε : D.L.ι → ℝ => groupedG K ε c) :=
      (measurable_pi_apply c).comp hG
    unfold groupedResidual
    exact (Real.measurable_exp.comp (measurable_const.add hε).neg).sub
      (Real.measurable_exp.comp hGc.neg)
  exact hG.prodMk hR

private lemma groupedReconstruct_measurable {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D) :
    Measurable (groupedReconstruct K) := by
  apply measurable_pi_lambda
  intro ℓ
  let c : K.κ := K.cl ℓ
  let u : clusterFiber K c := ⟨ℓ, rfl⟩
  have hG : Measurable
      (fun q : (K.κ → ℝ) × ((c : K.κ) → clusterFiber K c → ℝ) =>
        q.1 c) := (measurable_pi_apply c).comp measurable_fst
  have hR : Measurable
      (fun q : (K.κ → ℝ) × ((c : K.κ) → clusterFiber K c → ℝ) =>
        q.2 c u) :=
    by
      have hc : Measurable
          (fun q : (K.κ → ℝ) × ((c : K.κ) → clusterFiber K c → ℝ) =>
            q.2 c) := (measurable_pi_apply c).comp measurable_snd
      exact (measurable_pi_apply u).comp hc
  unfold groupedReconstruct
  exact (Real.measurable_log.comp
    (measurable_const.mul
      (hR.add (Real.measurable_exp.comp hG.neg)))).neg

private lemma groupedReconstruct_pair {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D) (ε : D.L.ι → ℝ) :
    groupedReconstruct K (groupedPair K ε) = ε := by
  funext ℓ
  let t : ℝ := D.L.prior ℓ / K.s (K.cl ℓ)
  have ht : 0 < t := div_pos (D.prior_pos ℓ) (clusterMass_pos K (K.cl ℓ))
  have hclock :
      t * (Real.exp (-(Real.log t + ε ℓ)) -
          Real.exp (-(groupedG K ε (K.cl ℓ))) +
          Real.exp (-(groupedG K ε (K.cl ℓ)))) =
        Real.exp (-ε ℓ) := by
    rw [sub_add_cancel]
    rw [show -(Real.log t + ε ℓ) = -Real.log t + -ε ℓ by ring,
      Real.exp_add, Real.exp_neg, Real.exp_log ht]
    field_simp
  unfold groupedReconstruct groupedPair groupedResidual
  change -Real.log
      (t * (Real.exp (-(Real.log t + ε ℓ)) -
        Real.exp (-(groupedG K ε (K.cl ℓ))) +
        Real.exp (-(groupedG K ε (K.cl ℓ))))) = ε ℓ
  rw [hclock, Real.log_exp]
  ring

private lemma klDiv_map_groupedPair {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D)
    (μ ν : Measure (D.L.ι → ℝ)) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    klDiv (Measure.map (groupedPair K) μ)
        (Measure.map (groupedPair K) ν) = klDiv μ ν := by
  have hpair := groupedPair_measurable K
  have hreconstruct := groupedReconstruct_measurable K
  have hleft (ξ : Measure (D.L.ι → ℝ)) :
      Measure.map (groupedReconstruct K)
          (Measure.map (groupedPair K) ξ) = ξ := by
    calc
      Measure.map (groupedReconstruct K)
          (Measure.map (groupedPair K) ξ) =
          Measure.map (groupedReconstruct K ∘ groupedPair K) ξ :=
        Measure.map_map hreconstruct hpair
      _ = Measure.map id ξ := by
        congr 1
        funext ε
        exact groupedReconstruct_pair K ε
      _ = ξ := Measure.map_id
  apply le_antisymm
  · exact klDiv_map_le μ ν hpair
  · calc
      klDiv μ ν =
          klDiv
            (Measure.map (groupedReconstruct K)
              (Measure.map (groupedPair K) μ))
            (Measure.map (groupedReconstruct K)
              (Measure.map (groupedPair K) ν)) := by
        rw [hleft μ, hleft ν]
      _ ≤ klDiv (Measure.map (groupedPair K) μ)
          (Measure.map (groupedPair K) ν) :=
        klDiv_map_le _ _ hreconstruct

/-- Lemma 7.2(b): away from the null tie set, maximizing first inside each
cluster and then over clusters gives exactly the original label winner. -/
private theorem grouped_winner_agrees_ae {p : α × β → ℝ}
    (D : SeedSetup p) (K : Clustering D) :
    (fun ε => winner D ε) =ᵐ[seedLaw D.L.ι]
      fun ε => groupedLabelWinner K ε := by
  filter_upwards [ae_no_race_ties D] with ε hties
  funext z
  by_cases hz : z ∈ support p
  · simp only [groupedLabelWinner, hz, if_true]
    let ℓ := winner D ε z
    let c := K.cl ℓ
    let b := groupedClusterWinner K (groupedG K ε) z
    let w := groupedWithinWinner K ε b
    have hscore (i : D.L.ι) :
        raceValue D z ε i =
          Real.log (K.sigma (K.cl i) z) +
            (Real.log (D.L.prior i / K.s (K.cl i)) + ε i) := by
      unfold raceValue
      rw [K.post_eq_sigma_mul i z hz,
        Real.log_mul (K.sigma_pos (K.cl i) z hz).ne'
          (div_pos (D.prior_pos i) (clusterMass_pos K (K.cl i))).ne']
      ring
    have hinner :
        Real.log (D.L.prior ℓ / K.s c) + ε ℓ ≤ groupedG K ε c := by
      exact Classical.choose_spec
        (Finite.exists_max fun u : clusterFiber K c =>
          Real.log (D.L.prior u.1 / K.s c) + ε u.1) ⟨ℓ, rfl⟩
    have houter :
        Real.log (K.sigma c z) + groupedG K ε c ≤
          Real.log (K.sigma b z) + groupedG K ε b := by
      exact Classical.choose_spec
        (Finite.exists_max fun d : K.κ =>
          Real.log (K.sigma d z) + groupedG K ε d) c
    have hwcl : K.cl w.1 = b := w.2
    have hchosen : raceValue D z ε ℓ ≤ raceValue D z ε w.1 := by
      rw [hscore ℓ, hscore w.1, hwcl]
      calc
        Real.log (K.sigma c z) +
            (Real.log (D.L.prior ℓ / K.s c) + ε ℓ) ≤
            Real.log (K.sigma c z) + groupedG K ε c :=
          by linarith
        _ ≤ Real.log (K.sigma b z) + groupedG K ε b := houter
        _ = Real.log (K.sigma b z) +
            (Real.log (D.L.prior w.1 / K.s b) + ε w.1) := by
          rfl
    have hmax : raceValue D z ε w.1 ≤ raceValue D z ε ℓ := by
      exact weightedWinner_max
        (fun i : D.L.ι => D.post i z) ε w.1
    have heq : raceValue D z ε ℓ = raceValue D z ε w.1 :=
      le_antisymm hchosen hmax
    have hlabel : ℓ = w.1 := by
      by_contra hne
      exact hties z ℓ w.1 hne heq
    exact hlabel
  · simp [groupedLabelWinner, hz]

private noncomputable def groupedClusterLexWinner {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D) (G : K.κ → ℝ)
    (z : α × β) : K.κ :=
  weightedLexWinner (fun c => K.sigma c z) G

private def groupedClusterEvent {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D) (b : K.κ) (z : α × β) :
    Set (K.κ → ℝ) :=
  {G | groupedClusterLexWinner K G z = b}

private def groupedResidualEvent {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D) (a : D.L.ι) :
    Set ((c : K.κ) → clusterFiber K c → ℝ) :=
  {R | R (K.cl a) ⟨a, rfl⟩ = 0}

private lemma groupedClusterEvent_measurable {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D) (b : K.κ) (z : α × β) :
    MeasurableSet (groupedClusterEvent K b z) := by
  letI : MeasurableSpace K.κ := ⊤
  apply (measurableSet_singleton b).preimage
  unfold groupedClusterLexWinner weightedLexWinner
  apply measurable_lexMax
  intro c
  exact measurable_const.add (measurable_pi_apply c)

private lemma groupedResidualEvent_measurable {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D) (a : D.L.ι) :
    MeasurableSet (groupedResidualEvent K a) := by
  apply measurableSet_eq_fun
  · exact (measurable_pi_apply (⟨a, rfl⟩ : clusterFiber K (K.cl a))).comp
      (measurable_pi_apply (K.cl a))
  · exact measurable_const

private lemma groupedWithinWinner_ae_iff_residual_zero
    {p : α × β → ℝ} {D : SeedSetup p} (K : Clustering D)
    (a : D.L.ι) :
    (fun ε => groupedWithinWinner K ε (K.cl a) =
        (⟨a, rfl⟩ : clusterFiber K (K.cl a))) =ᵐ[seedLaw D.L.ι]
      fun ε => groupedResidual K ε (K.cl a) ⟨a, rfl⟩ = 0 := by
  let t : D.L.ι → ℝ := fun ℓ => D.L.prior ℓ / K.s (K.cl ℓ)
  filter_upwards [weighted_ae_no_ties t] with ε htie
  apply propext
  constructor
  · intro ha
    unfold groupedResidual
    have hvalue :
        Real.log (D.L.prior a / K.s (K.cl a)) + ε a =
          groupedG K ε (K.cl a) := by
      unfold groupedG
      rw [ha]
    rw [hvalue, sub_self]
  · intro hz
    have hexp :
        Real.exp (-(Real.log (D.L.prior a / K.s (K.cl a)) + ε a)) =
          Real.exp (-(groupedG K ε (K.cl a))) := sub_eq_zero.mp hz
    have hvalue :
        Real.log (D.L.prior a / K.s (K.cl a)) + ε a =
          groupedG K ε (K.cl a) := by
      have hneg := Real.exp_injective hexp
      linarith
    let w := groupedWithinWinner K ε (K.cl a)
    have hchosen :
        groupedG K ε (K.cl a) =
          Real.log (D.L.prior w.1 / K.s (K.cl w.1)) + ε w.1 := by
      unfold groupedG
      rw [w.property]
    by_contra hne
    have hvalNe : a ≠ w.1 := by
      intro haw
      apply hne
      apply Subtype.ext
      exact haw.symm
    have hdistinct := htie a w.1 hvalNe
    apply hdistinct
    simpa only [weightedValue, t] using hvalue.trans hchosen

private lemma labelWinnerEvent_ae_grouped_product
    {p : α × β → ℝ} (D : SeedSetup p) (K : Clustering D)
    (a : D.L.ι) (z : α × β) (hz : z ∈ support p) :
    {ε | winner D ε z = a} =ᵐ[seedLaw D.L.ι]
      groupedPair K ⁻¹'
        (groupedClusterEvent K (K.cl a) z ×ˢ groupedResidualEvent K a) := by
  have hG : Measurable (groupedG K) :=
    measurable_fst.comp (groupedPair_measurable K)
  have hclusterSeed := weightedWinner_ae_eq_lex
    (fun c : K.κ => K.sigma c z)
  have hclusterMap :
      (fun G => groupedClusterWinner K G z) =ᵐ[seedLaw K.κ]
        fun G => groupedClusterLexWinner K G z := by
    change (fun G => weightedWinner (fun c : K.κ => K.sigma c z) G) =ᵐ[
      seedLaw K.κ] fun G => weightedLexWinner (fun c => K.sigma c z) G
    exact hclusterSeed
  have hclusterMapped :
      (fun G => groupedClusterWinner K G z) =ᵐ[
        Measure.map (groupedG K) (seedLaw D.L.ι)]
          fun G => groupedClusterLexWinner K G z := by
    rw [grouped_gumbel_law K]
    exact hclusterMap
  have hcluster : ∀ᵐ ε ∂(seedLaw D.L.ι),
      groupedClusterWinner K (groupedG K ε) z =
        groupedClusterLexWinner K (groupedG K ε) z :=
    ae_of_ae_map hG.aemeasurable hclusterMapped
  filter_upwards [grouped_winner_agrees_ae D K,
    groupedWithinWinner_ae_iff_residual_zero K a,
    hcluster] with ε hw hwithin hclusterEq
  apply propext
  have hwz := congrFun hw z
  let B := groupedClusterWinner K (groupedG K ε) z
  let BL := groupedClusterLexWinner K (groupedG K ε) z
  have hBBL : B = BL := hclusterEq
  change (winner D ε z = a ↔
    groupedClusterLexWinner K (groupedG K ε) z = K.cl a ∧
      groupedResidual K ε (K.cl a) ⟨a, rfl⟩ = 0)
  constructor
  · intro hwin
    have hlabel : (groupedWithinWinner K ε B).1 = a := by
      have hgrouped : groupedLabelWinner K ε z = a := hwz.symm.trans hwin
      simpa only [groupedLabelWinner, hz, if_true] using hgrouped
    have hB : B = K.cl a := by
      calc
        B = K.cl (groupedWithinWinner K ε B).1 :=
          (groupedWithinWinner K ε B).2.symm
        _ = K.cl a := congrArg K.cl hlabel
    have hW : groupedWithinWinner K ε (K.cl a) =
        (⟨a, rfl⟩ : clusterFiber K (K.cl a)) := by
      have hlabel' := hlabel
      rw [hB] at hlabel'
      apply Subtype.ext
      exact hlabel'
    have hR : groupedResidual K ε (K.cl a) ⟨a, rfl⟩ = 0 :=
      hwithin.mp hW
    exact ⟨hBBL.symm.trans hB, hR⟩
  · intro hprod
    have hB : B = K.cl a := hBBL.trans hprod.1
    have hW : groupedWithinWinner K ε (K.cl a) =
        (⟨a, rfl⟩ : clusterFiber K (K.cl a)) :=
      hwithin.mpr hprod.2
    have hgrouped : groupedLabelWinner K ε z = a := by
      simp only [groupedLabelWinner, hz, if_true]
      change (groupedWithinWinner K ε B).1 = a
      rw [hB]
      exact congrArg Subtype.val hW
    exact hwz.trans hgrouped

private lemma klDiv_prod_same_right
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (μ ν : Measure Ω) (ρ : Measure Ξ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsProbabilityMeasure ρ] :
    klDiv (μ.prod ρ) (ν.prod ρ) = klDiv μ ν := by
  simpa only [Measure.compProd_const] using
    (klDiv_compProd_left μ ν (Kernel.const Ω ρ))

private lemma klDiv_map_measurableEquiv
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (e : A ≃ᵐ B) (μ ν : Measure A)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    klDiv (Measure.map e μ) (Measure.map e ν) = klDiv μ ν := by
  apply le_antisymm
  · exact klDiv_map_le μ ν e.measurable
  · calc
      klDiv μ ν =
          klDiv (Measure.map e.symm (Measure.map e μ))
            (Measure.map e.symm (Measure.map e ν)) := by
              rw [Measure.map_map e.symm.measurable e.measurable,
                Measure.map_map e.symm.measurable e.measurable]
              simp
      _ ≤ klDiv (Measure.map e μ) (Measure.map e ν) :=
        klDiv_map_le _ _ e.symm.measurable

private lemma klDiv_prod_eq_add
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (μ ν : Measure A) (ρ η : Measure B)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    [IsProbabilityMeasure ρ] [IsProbabilityMeasure η] :
    klDiv (μ.prod ρ) (ν.prod η) = klDiv μ ν + klDiv ρ η := by
  have hchain : klDiv (μ.prod ρ) (ν.prod η) =
      klDiv μ ν + klDiv (μ.prod ρ) (μ.prod η) := by
    simpa only [Measure.compProd_const] using
      (klDiv_compProd_eq_add μ ν
        (Kernel.const A ρ) (Kernel.const A η))
  calc
    klDiv (μ.prod ρ) (ν.prod η) =
        klDiv μ ν + klDiv (μ.prod ρ) (μ.prod η) := hchain
    _ = klDiv μ ν +
        klDiv (Measure.map Prod.swap (μ.prod ρ))
          (Measure.map Prod.swap (μ.prod η)) := by
      congr 1
      have hfun :
          ((MeasurableEquiv.prodComm : A × B ≃ᵐ B × A) : A × B → B × A) =
            Prod.swap := by
        funext x
        rfl
      rw [← hfun]
      exact (klDiv_map_measurableEquiv MeasurableEquiv.prodComm
        (μ.prod ρ) (μ.prod η)).symm
    _ = klDiv μ ν + klDiv (ρ.prod μ) (η.prod μ) := by
      rw [Measure.prod_swap, Measure.prod_swap]
    _ = klDiv μ ν + klDiv ρ η := by
      rw [klDiv_prod_same_right ρ η μ]

private theorem klDiv_pi_eq_sum
    {I : Type u} [Fintype I]
    (μ ν : I → Measure ℝ)
    (hμ : ∀ i, IsProbabilityMeasure (μ i))
    (hν : ∀ i, IsProbabilityMeasure (ν i)) :
    klDiv (Measure.pi μ) (Measure.pi ν) = ∑ i, klDiv (μ i) (ν i) := by
  let P : ∀ (J : Type u) [Fintype J], Prop := fun J _ =>
    ∀ (μ ν : J → Measure ℝ),
      (∀ j, IsProbabilityMeasure (μ j)) →
      (∀ j, IsProbabilityMeasure (ν j)) →
      klDiv (Measure.pi μ) (Measure.pi ν) = ∑ j, klDiv (μ j) (ν j)
  apply Fintype.induction_empty_option (P := P)
      (fun J J' _ e ih μ ν hμ hν => ?_)
      (by
        intro μ ν hμ hν
        rw [Measure.pi_of_empty μ, Measure.pi_of_empty ν, klDiv_self]
        simp)
      (fun J _ ih μ ν hμ hν => ?_)
      I μ ν hμ hν
  · let μ' : J → Measure ℝ := fun j => μ (e j)
    let ν' : J → Measure ℝ := fun j => ν (e j)
    letI : Fintype J := Fintype.ofEquiv J' e.symm
    letI (j : J) : IsProbabilityMeasure (μ' j) := hμ (e j)
    letI (j : J) : IsProbabilityMeasure (ν' j) := hν (e j)
    have hmapμ :
        (Measure.pi μ').map
          (MeasurableEquiv.piCongrLeft (fun _ : J' => ℝ) e) =
          Measure.pi μ := by
      exact Measure.pi_map_piCongrLeft e μ
    have hmapν :
        (Measure.pi ν').map
          (MeasurableEquiv.piCongrLeft (fun _ : J' => ℝ) e) =
          Measure.pi ν := by
      exact Measure.pi_map_piCongrLeft e ν
    calc
      klDiv (Measure.pi μ) (Measure.pi ν) =
          klDiv (Measure.pi μ') (Measure.pi ν') := by
        rw [← hmapμ, ← hmapν,
          klDiv_map_measurableEquiv
            (MeasurableEquiv.piCongrLeft (fun _ : J' => ℝ) e)]
      _ = ∑ j, klDiv (μ' j) (ν' j) :=
        ih μ' ν' (fun _ => inferInstance) (fun _ => inferInstance)
      _ = ∑ j, klDiv (μ j) (ν j) := by
        exact e.sum_comp (fun j => klDiv (μ j) (ν j))
  · let μSome : J → Measure ℝ := fun j => μ (some j)
    let νSome : J → Measure ℝ := fun j => ν (some j)
    letI (j : J) : IsProbabilityMeasure (μSome j) := hμ (some j)
    letI (j : J) : IsProbabilityMeasure (νSome j) := hν (some j)
    letI : IsProbabilityMeasure (μ none) := hμ none
    letI : IsProbabilityMeasure (ν none) := hν none
    let e := (MeasurableEquiv.piOptionEquivProd (fun _ : Option J => ℝ)).symm
    have hmapμ :
        ((Measure.pi μSome).prod (μ none)).map e = Measure.pi μ := by
      exact Measure.pi_map_piOptionEquivProd μ
    have hmapν :
        ((Measure.pi νSome).prod (ν none)).map e = Measure.pi ν := by
      exact Measure.pi_map_piOptionEquivProd ν
    calc
      klDiv (Measure.pi μ) (Measure.pi ν) =
          klDiv ((Measure.pi μSome).prod (μ none))
            ((Measure.pi νSome).prod (ν none)) := by
        rw [← hmapμ, ← hmapν, klDiv_map_measurableEquiv e]
      _ = klDiv (Measure.pi μSome) (Measure.pi νSome) +
          klDiv (μ none) (ν none) := klDiv_prod_eq_add _ _ _ _
      _ = (∑ j, klDiv (μSome j) (νSome j)) +
          klDiv (μ none) (ν none) := by
        rw [ih μSome νSome (fun _ => inferInstance) (fun _ => inferInstance)]
      _ = ∑ j, klDiv (μ j) (ν j) := by
        simp [μSome, νSome, add_comm]

/-- Mathlib's chain rule currently packages the conditional term as a KL
between two composition-products.  For finite Markov kernels on a standard
measurable space, its kernel Radon--Nikodym derivative gives the usual
pointwise-integral form. -/
private lemma klDiv_compProd_same_left_eq_lintegral
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace.CountableOrCountablyGenerated X Y]
    (μ : Measure X) (κ η : Kernel X Y)
    [IsProbabilityMeasure μ] [IsMarkovKernel κ] [IsMarkovKernel η]
    (hac : ∀ x, κ x ≪ η x) :
    klDiv (μ ⊗ₘ κ) (μ ⊗ₘ η) =
      ∫⁻ x, klDiv (κ x) (η x) ∂μ := by
  have hjointac : μ ⊗ₘ κ ≪ μ ⊗ₘ η :=
    Measure.AbsolutelyContinuous.compProd_right (ae_of_all μ hac)
  have hkernel : η.withDensity (κ.rnDeriv η) = κ := by
    ext x
    rw [Kernel.withDensity_rnDeriv_eq (hac x)]
  letI : IsFiniteKernel (η.withDensity (κ.rnDeriv η)) :=
    hkernel.symm ▸ (inferInstance : IsFiniteKernel κ)
  have hjoint : μ ⊗ₘ κ =
      (μ ⊗ₘ η).withDensity (fun p => κ.rnDeriv η p.1 p.2) := by
    calc
      μ ⊗ₘ κ = μ ⊗ₘ (η.withDensity (κ.rnDeriv η)) := by rw [hkernel]
      _ = (μ ⊗ₘ η).withDensity (fun p => κ.rnDeriv η p.1 p.2) :=
        Measure.compProd_withDensity (by fun_prop)
  have hrn : (μ ⊗ₘ κ).rnDeriv (μ ⊗ₘ η) =ᵐ[μ ⊗ₘ η]
      fun p => κ.rnDeriv η p.1 p.2 := by
    rw [hjoint]
    exact Measure.rnDeriv_withDensity _ (by fun_prop)
  rw [klDiv_eq_lintegral_klFun_of_ac hjointac]
  calc
    (∫⁻ p, ENNReal.ofReal
        (klFun (((μ ⊗ₘ κ).rnDeriv (μ ⊗ₘ η) p).toReal)) ∂(μ ⊗ₘ η)) =
        ∫⁻ p, ENNReal.ofReal
          (klFun ((κ.rnDeriv η p.1 p.2).toReal)) ∂(μ ⊗ₘ η) := by
      exact lintegral_congr_ae (hrn.fun_comp fun r =>
        ENNReal.ofReal (klFun r.toReal))
    _ = ∫⁻ x, ∫⁻ y, ENNReal.ofReal
          (klFun ((κ.rnDeriv η x y).toReal)) ∂η x ∂μ := by
      rw [Measure.lintegral_compProd]
      fun_prop
    _ = ∫⁻ x, klDiv (κ x) (η x) ∂μ := by
      apply lintegral_congr
      intro x
      rw [klDiv_eq_lintegral_klFun_of_ac (hac x)]
      exact lintegral_congr_ae
        ((Kernel.rnDeriv_eq_rnDeriv_measure
          (κ := κ) (η := η) (a := x)).fun_comp
            fun r => ENNReal.ofReal (klFun r.toReal))

private lemma toReal_klDiv_compProd_same_left_eq_integral
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace.CountableOrCountablyGenerated X Y]
    (μ : Measure X) (κ η : Kernel X Y)
    [IsProbabilityMeasure μ] [IsMarkovKernel κ] [IsMarkovKernel η]
    (hac : ∀ x, κ x ≪ η x)
    (hfinite : ∀ x, klDiv (κ x) (η x) ≠ ⊤) :
    (klDiv (μ ⊗ₘ κ) (μ ⊗ₘ η)).toReal =
      ∫ x, (klDiv (κ x) (η x)).toReal ∂μ := by
  have hpoint (x : X) :
      klDiv (κ x) (η x) =
        ∫⁻ y, ENNReal.ofReal
          (klFun ((κ.rnDeriv η x y).toReal)) ∂η x := by
    rw [klDiv_eq_lintegral_klFun_of_ac (hac x)]
    exact lintegral_congr_ae
      ((Kernel.rnDeriv_eq_rnDeriv_measure
        (κ := κ) (η := η) (a := x)).fun_comp
          fun r => ENNReal.ofReal (klFun r.toReal)).symm
  have hmeas : Measurable (fun x => klDiv (κ x) (η x)) := by
    simp_rw [hpoint]
    exact Measurable.lintegral_kernel_prod_right (by fun_prop)
  rw [klDiv_compProd_same_left_eq_lintegral μ κ η hac]
  exact (integral_toReal hmeas.aemeasurable
    (ae_of_all μ fun x => lt_top_iff_ne_top.mpr (hfinite x))).symm

private lemma llr_chain_ae
    {Ω : Type*} [MeasurableSpace Ω]
    (P M Q : Measure Ω) [IsFiniteMeasure P] [IsFiniteMeasure M]
    [IsFiniteMeasure Q] (hPM : P ≪ M) (hMQ : M ≪ Q) :
    llr P Q =ᵐ[P] fun x => llr P M x + llr M Q x := by
  have hPQ : P ≪ Q := hPM.trans hMQ
  have hmul := Measure.rnDeriv_mul_rnDeriv hPM (κ := Q)
  filter_upwards [hPQ.ae_le hmul,
    Measure.rnDeriv_pos hPM,
    hPM.ae_le (Measure.rnDeriv_pos hMQ),
    hPM.ae_le (Measure.rnDeriv_lt_top P M),
    hPM.ae_le (hMQ.ae_le (Measure.rnDeriv_lt_top M Q))] with
      x hmulX hPMpos hMQpos hPMtop hMQtop
  unfold llr
  rw [← hmulX, Pi.mul_apply, ENNReal.toReal_mul, Real.log_mul]
  · exact (ENNReal.toReal_pos hPMpos.ne' hPMtop.ne).ne'
  · exact (ENNReal.toReal_pos hMQpos.ne' hMQtop.ne).ne'

private theorem finite_mixture_golden_le
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (r : ι → ℝ) (P : ι → Measure Ω) (M Q : Measure Ω)
    (hr : IsPMF r)
    (hP : ∀ i, IsProbabilityMeasure (P i))
    (hMprob : IsProbabilityMeasure M) (hQprob : IsProbabilityMeasure Q)
    (hM : M = ∑ i, ENNReal.ofReal (r i) • P i)
    (hPMfinite : ∀ i, 0 < r i → klDiv (P i) M ≠ ⊤)
    (hPQfinite : ∀ i, 0 < r i → klDiv (P i) Q ≠ ⊤) :
    (∑ i, r i * (klDiv (P i) M).toReal) ≤
      ∑ i, r i * (klDiv (P i) Q).toReal := by
  letI (i : ι) : IsProbabilityMeasure (P i) := hP i
  letI : IsProbabilityMeasure M := hMprob
  letI : IsProbabilityMeasure Q := hQprob
  have hMQ : M ≪ Q := by
    intro s hQs
    rw [hM, Measure.finsetSum_apply]
    apply Finset.sum_eq_zero
    intro i _
    rw [Measure.smul_apply, smul_eq_mul]
    by_cases hri : r i = 0
    · simp [hri]
    · have hriPos : 0 < r i :=
        lt_of_le_of_ne (hr.nonneg i) (Ne.symm hri)
      have hiQ : P i ≪ Q :=
        (klDiv_ne_top_iff.mp (hPQfinite i hriPos)).1
      rw [hiQ hQs]
      simp
  have hchain (i : ι) (hi : 0 < r i) :
      llr (P i) Q =ᵐ[P i]
        fun x => llr (P i) M x + llr M Q x := by
    exact llr_chain_ae (P i) M Q
      (klDiv_ne_top_iff.mp (hPMfinite i hi)).1 hMQ
  have hMQintegrableP (i : ι) (hi : 0 < r i) :
      Integrable (llr M Q) (P i) := by
    have hPMint := (klDiv_ne_top_iff.mp (hPMfinite i hi)).2
    have hPQint := (klDiv_ne_top_iff.mp (hPQfinite i hi)).2
    have hsum : Integrable
        (fun x => llr (P i) M x + llr M Q x) (P i) := by
      exact hPQint.congr (hchain i hi)
    exact (integrable_add_iff_integrable_right' hPMint).mp hsum
  have hMQintegrable : Integrable (llr M Q) M := by
    have hmix : Integrable (llr M Q)
        (∑ i, ENNReal.ofReal (r i) • P i) := by
      rw [integrable_finsetSum_measure]
      intro i _
      by_cases hri : r i = 0
      · simp [hri]
      · exact (hMQintegrableP i
          (lt_of_le_of_ne (hr.nonneg i) (Ne.symm hri))).smul_measure
            ENNReal.ofReal_ne_top
    simpa only [← hM] using hmix
  have hterm (i : ι) (hriPos : 0 < r i) :
      (klDiv (P i) Q).toReal =
        (klDiv (P i) M).toReal + ∫ x, llr M Q x ∂P i := by
    have hPMdata := klDiv_ne_top_iff.mp (hPMfinite i hriPos)
    have hPQdata := klDiv_ne_top_iff.mp (hPQfinite i hriPos)
    rw [toReal_klDiv hPQdata.1 hPQdata.2,
      toReal_klDiv hPMdata.1 hPMdata.2]
    rw [integral_congr_ae (hchain i hriPos),
      integral_add hPMdata.2 (hMQintegrableP i hriPos)]
    simp only [probReal_univ]
    ring
  have hintegral :
      ∫ x, llr M Q x ∂M =
        ∑ i, r i * ∫ x, llr M Q x ∂P i := by
    calc
      (∫ x, llr M Q x ∂M) =
          ∫ x, llr M Q x ∂(∑ i, ENNReal.ofReal (r i) • P i) :=
        congrArg (fun μ => ∫ x, llr M Q x ∂μ) hM
      _ = ∑ i, ∫ x, llr M Q x ∂(ENNReal.ofReal (r i) • P i) := by
        apply integral_finsetSum_measure
        intro i _
        by_cases hri : r i = 0
        · simp [hri]
        · exact (hMQintegrableP i
            (lt_of_le_of_ne (hr.nonneg i) (Ne.symm hri))).smul_measure
              ENNReal.ofReal_ne_top
      _ = ∑ i, r i * ∫ x, llr M Q x ∂P i := by
        apply Finset.sum_congr rfl
        intro i _
        rw [integral_smul_measure, smul_eq_mul,
          ENNReal.toReal_ofReal (hr.nonneg i)]
  have hMQvalue : (klDiv M Q).toReal = ∫ x, llr M Q x ∂M := by
    rw [toReal_klDiv hMQ hMQintegrable]
    simp
  have hgolden :
      (∑ i, r i * (klDiv (P i) Q).toReal) =
        (∑ i, r i * (klDiv (P i) M).toReal) + (klDiv M Q).toReal := by
    calc
      (∑ i, r i * (klDiv (P i) Q).toReal) =
          ∑ i, (r i * (klDiv (P i) M).toReal +
            r i * ∫ x, llr M Q x ∂P i) := by
        apply Finset.sum_congr rfl
        intro i _
        by_cases hri : r i = 0
        · simp [hri]
        · rw [hterm i (lt_of_le_of_ne (hr.nonneg i) (Ne.symm hri))]
          ring
      _ = (∑ i, r i * (klDiv (P i) M).toReal) +
          ∑ i, r i * ∫ x, llr M Q x ∂P i := by
        rw [Finset.sum_add_distrib]
      _ = (∑ i, r i * (klDiv (P i) M).toReal) +
          (klDiv M Q).toReal := by rw [← hintegral, ← hMQvalue]
  rw [hgolden]
  exact le_add_of_nonneg_right ENNReal.toReal_nonneg

private noncomputable def groupedResidualLaw {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D) :
    Measure ((c : K.κ) → clusterFiber K c → ℝ) :=
  Measure.map (groupedResidual K) (seedLaw D.L.ι)

private lemma grouped_winner_restrict_factorization
    {p : α × β → ℝ} (D : SeedSetup p) (K : Clustering D)
    (a : D.L.ι) (z : α × β) (hz : z ∈ support p) :
    Measure.map (groupedPair K)
        ((seedLaw D.L.ι).restrict {ε | winner D ε z = a}) =
      ((seedLaw K.κ).restrict (groupedClusterEvent K (K.cl a) z)).prod
        ((groupedResidualLaw K).restrict (groupedResidualEvent K a)) := by
  let C := groupedClusterEvent K (K.cl a) z
  let W := groupedResidualEvent K a
  have hC : MeasurableSet C := groupedClusterEvent_measurable K (K.cl a) z
  have hW : MeasurableSet W := groupedResidualEvent_measurable K a
  have hpair : Measurable (groupedPair K) := groupedPair_measurable K
  letI : IsProbabilityMeasure (groupedResidualLaw K) := by
    unfold groupedResidualLaw
    exact Measure.isProbabilityMeasure_map
      (measurable_snd.comp hpair).aemeasurable
  have hevent := labelWinnerEvent_ae_grouped_product D K a z hz
  have hfac : Measure.map (groupedPair K) (seedLaw D.L.ι) =
      (seedLaw K.κ).prod (groupedResidualLaw K) := by
    change Measure.map (fun ε => (groupedG K ε, groupedResidual K ε))
        (seedLaw D.L.ι) =
      (seedLaw K.κ).prod
        (Measure.map (groupedResidual K) (seedLaw D.L.ι))
    exact grouped_seed_factorization K
  calc
    Measure.map (groupedPair K)
        ((seedLaw D.L.ι).restrict {ε | winner D ε z = a}) =
        Measure.map (groupedPair K)
          ((seedLaw D.L.ι).restrict
            (groupedPair K ⁻¹' (C ×ˢ W))) := by
      rw [Measure.restrict_congr_set hevent]
    _ = (Measure.map (groupedPair K) (seedLaw D.L.ι)).restrict
        (C ×ˢ W) := (Measure.restrict_map hpair (hC.prod hW)).symm
    _ = ((seedLaw K.κ).prod (groupedResidualLaw K)).restrict
        (C ×ˢ W) := by
      rw [hfac]
    _ = ((seedLaw K.κ).restrict C).prod
        ((groupedResidualLaw K).restrict W) :=
      (Measure.prod_restrict C W).symm

private lemma clusterSeedLawGivenWinner_eq_lex_restrict
    {p : α × β → ℝ} {D : SeedSetup p} (K : Clustering D)
    (b : K.κ) (z : α × β) (hz : z ∈ support p) :
    clusterSeedLawGivenWinner K b z =
      (ENNReal.ofReal (K.sigma b z))⁻¹ •
        (seedLaw K.κ).restrict (groupedClusterEvent K b z) := by
  have hs := K.sigma_pos b z hz
  have hae :
      {G | groupedClusterWinner K G z = b} =ᵐ[seedLaw K.κ]
        groupedClusterEvent K b z := by
    filter_upwards [weightedWinner_ae_eq_lex
      (fun c : K.κ => K.sigma c z)] with G hG
    apply propext
    change (groupedClusterWinner K G z = b ↔
      groupedClusterLexWinner K G z = b)
    change (weightedWinner (fun c : K.κ => K.sigma c z) G = b ↔
      weightedLexWinner (fun c : K.κ => K.sigma c z) G = b)
    rw [hG]
  unfold clusterSeedLawGivenWinner
  rw [if_neg hs.ne', Measure.restrict_congr_set hae]

private lemma groupedClusterEvent_measure
    {p : α × β → ℝ} {D : SeedSetup p} (K : Clustering D)
    (b : K.κ) (z : α × β) (hz : z ∈ support p) :
    seedLaw K.κ (groupedClusterEvent K b z) =
      ENNReal.ofReal (K.sigma b z) := by
  have hae :
      {G | groupedClusterWinner K G z = b} =ᵐ[seedLaw K.κ]
        groupedClusterEvent K b z := by
    filter_upwards [weightedWinner_ae_eq_lex
      (fun c : K.κ => K.sigma c z)] with G hG
    apply propext
    change (groupedClusterWinner K G z = b ↔
      groupedClusterLexWinner K G z = b)
    change (weightedWinner (fun c : K.κ => K.sigma c z) G = b ↔
      weightedLexWinner (fun c => K.sigma c z) G = b)
    rw [hG]
  calc
    seedLaw K.κ (groupedClusterEvent K b z) =
        seedLaw K.κ {G | groupedClusterWinner K G z = b} :=
      (measure_congr hae).symm
    _ = ENNReal.ofReal (K.sigma b z) :=
      cluster_winner_probability_measure K b z hz

private lemma groupedResidualEvent_measure
    {p : α × β → ℝ} (D : SeedSetup p) (K : Clustering D)
    (a : D.L.ι) :
    groupedResidualLaw K (groupedResidualEvent K a) =
      ENNReal.ofReal (D.L.prior a / K.s (K.cl a)) := by
  have hsum : (∑ z, p z) ≠ 0 := by
    have htotal : ∑ z, p z = 1 := by
      simpa [mass] using D.isPMF.total
    rw [htotal]
    norm_num
  obtain ⟨z, _, hpz⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum
  have hz : z ∈ support p := by
    simpa [support] using hpz
  have hpair : Measurable (groupedPair K) := groupedPair_measurable K
  letI : IsProbabilityMeasure (groupedResidualLaw K) := by
    unfold groupedResidualLaw
    exact Measure.isProbabilityMeasure_map
      (measurable_snd.comp hpair).aemeasurable
  have hfactor := grouped_winner_restrict_factorization D K a z hz
  have hmass := congrArg
    (fun μ : Measure ((K.κ → ℝ) ×
      ((c : K.κ) → clusterFiber K c → ℝ)) => μ Set.univ) hfactor
  rw [Measure.map_apply hpair MeasurableSet.univ, Set.preimage_univ,
    Measure.restrict_apply_univ, ← Set.univ_prod_univ,
    Measure.prod_prod, Measure.restrict_apply_univ,
    Measure.restrict_apply_univ,
    label_winner_probability_measure D a z hz,
    groupedClusterEvent_measure K (K.cl a) z hz] at hmass
  have hsigma : 0 < ENNReal.ofReal (K.sigma (K.cl a) z) :=
    ENNReal.ofReal_pos.mpr (K.sigma_pos (K.cl a) z hz)
  have hsigmaTop : ENNReal.ofReal (K.sigma (K.cl a) z) ≠ ⊤ :=
    ENNReal.ofReal_ne_top
  rw [K.post_eq_sigma_mul a z hz,
    ENNReal.ofReal_mul (K.sigma_pos (K.cl a) z hz).le] at hmass
  have hcancel := congrArg
    (fun x : ℝ≥0∞ => (ENNReal.ofReal (K.sigma (K.cl a) z))⁻¹ * x) hmass
  symm
  simpa only [ENNReal.inv_mul_cancel_left hsigma.ne' hsigmaTop] using hcancel

private noncomputable def groupedResidualLawGivenLabel
    {p : α × β → ℝ} {D : SeedSetup p} (K : Clustering D)
    (a : D.L.ι) : Measure ((c : K.κ) → clusterFiber K c → ℝ) :=
  (ENNReal.ofReal (D.L.prior a / K.s (K.cl a)))⁻¹ •
    (groupedResidualLaw K).restrict (groupedResidualEvent K a)

private lemma groupedResidualLawGivenLabel_isProbability
    {p : α × β → ℝ} (D : SeedSetup p) (K : Clustering D)
    (a : D.L.ι) : IsProbabilityMeasure (groupedResidualLawGivenLabel K a) := by
  constructor
  have hweight : 0 < D.L.prior a / K.s (K.cl a) :=
    div_pos (D.prior_pos a) (clusterMass_pos K (K.cl a))
  unfold groupedResidualLawGivenLabel
  rw [Measure.smul_apply, smul_eq_mul, Measure.restrict_apply_univ,
    groupedResidualEvent_measure D K a,
    ENNReal.inv_mul_cancel
      (ENNReal.ofReal_pos.mpr hweight).ne' ENNReal.ofReal_ne_top]

private lemma map_seedLawGivenWinner_groupedPair
    {p : α × β → ℝ} (D : SeedSetup p) (K : Clustering D)
    (a : D.L.ι) (z : α × β) (hz : z ∈ support p) :
    Measure.map (groupedPair K) (seedLawGivenWinner D a z) =
      (clusterSeedLawGivenWinner K (K.cl a) z).prod
        (groupedResidualLawGivenLabel K a) := by
  have hsigma : 0 < K.sigma (K.cl a) z :=
    K.sigma_pos (K.cl a) z hz
  have hweight : 0 < D.L.prior a / K.s (K.cl a) :=
    div_pos (D.prior_pos a) (clusterMass_pos K (K.cl a))
  have hpost : 0 < D.post a z := by
    rw [K.post_eq_sigma_mul a z hz]
    exact mul_pos hsigma hweight
  have hpair : Measurable (groupedPair K) := groupedPair_measurable K
  letI : IsProbabilityMeasure (groupedResidualLaw K) := by
    unfold groupedResidualLaw
    exact Measure.isProbabilityMeasure_map
      (measurable_snd.comp hpair).aemeasurable
  unfold seedLawGivenWinner
  rw [if_neg hpost.ne', Measure.map_smul,
    grouped_winner_restrict_factorization D K a z hz,
    clusterSeedLawGivenWinner_eq_lex_restrict K (K.cl a) z hz,
    groupedResidualLawGivenLabel,
    Measure.prod_smul_left, Measure.prod_smul_right, smul_smul,
    K.post_eq_sigma_mul a z hz,
    ENNReal.ofReal_mul hsigma.le,
    ENNReal.mul_inv
      (Or.inl (ENNReal.ofReal_pos.mpr hsigma).ne')
      (Or.inl ENNReal.ofReal_ne_top)]

private noncomputable def labelWithinWeight
    {p : α × β → ℝ} {D : SeedSetup p} (K : Clustering D)
    (a : D.L.ι) : ℝ :=
  D.L.prior a / K.s (K.cl a)

private lemma labelWithinWeight_pos
    {p : α × β → ℝ} {D : SeedSetup p} (K : Clustering D)
    (a : D.L.ι) : 0 < labelWithinWeight K a :=
  div_pos (D.prior_pos a) (clusterMass_pos K (K.cl a))

private lemma clusterMass_mul_labelWithinWeight
    {p : α × β → ℝ} {D : SeedSetup p} (K : Clustering D)
    (a : D.L.ι) :
    K.s (K.cl a) * labelWithinWeight K a = D.L.prior a := by
  unfold labelWithinWeight
  exact mul_div_cancel₀ (D.L.prior a) (clusterMass_pos K (K.cl a)).ne'

private lemma labelWithinWeight_fiber_sum
    {p : α × β → ℝ} {D : SeedSetup p} (K : Clustering D)
    (c : K.κ) :
    ∑ a ∈ univ.filter (fun a => K.cl a = c), labelWithinWeight K a = 1 := by
  calc
    (∑ a ∈ univ.filter (fun a => K.cl a = c), labelWithinWeight K a) =
        ∑ a ∈ univ.filter (fun a => K.cl a = c), D.L.prior a / K.s c := by
      apply Finset.sum_congr rfl
      intro a ha
      unfold labelWithinWeight
      rw [(Finset.mem_filter.mp ha).2]
    _ = (∑ a ∈ univ.filter (fun a => K.cl a = c), D.L.prior a) /
        K.s c := by rw [Finset.sum_div]
    _ = 1 := by
      change K.s c / K.s c = 1
      rw [div_self (clusterMass_pos K c).ne']

private lemma component_eq_clusterQ
    {p : α × β → ℝ} {D : SeedSetup p} (K : Clustering D)
    (a : D.L.ι) : D.L.comp a = K.Q (K.cl a) := by
  unfold Clustering.Q
  apply (K.spec _ _).mp
  exact (Classical.choose_spec (K.surj (K.cl a))).symm

private lemma seedContextJoint_cluster_factor
    {p : α × β → ℝ} (D : SeedSetup p) (K : Clustering D)
    (a ℓ₀ : D.L.ι) (z : α × β) :
    seedContextJoint D a ℓ₀ z =
      labelWithinWeight K a * labelWithinWeight K ℓ₀ *
        (K.s (K.cl ℓ₀) * K.Q (K.cl ℓ₀) z *
          K.sigma (K.cl a) z) := by
  by_cases hz : z ∈ support p
  · unfold seedContextJoint Latent.joint
    simp only [Prod.fst, Prod.snd]
    rw [component_eq_clusterQ K ℓ₀, K.post_eq_sigma_mul a z hz]
    rw [show D.L.prior a / K.s (K.cl a) = labelWithinWeight K a by rfl]
    rw [← clusterMass_mul_labelWithinWeight K ℓ₀]
    ring
  · have hQ : K.Q (K.cl ℓ₀) z = 0 :=
      (K.Q_isContact (K.cl ℓ₀)).2.1 z hz
    unfold seedContextJoint Latent.joint
    simp only [Prod.fst, Prod.snd]
    rw [component_eq_clusterQ K ℓ₀, hQ]
    ring

private lemma seedContextMass_cluster_factor
    {p : α × β → ℝ} (D : SeedSetup p) (K : Clustering D)
    (a ℓ₀ : D.L.ι) :
    seedContextMass D a ℓ₀ =
      labelWithinWeight K a * labelWithinWeight K ℓ₀ *
        scalarContextMass K (K.cl ℓ₀) (K.cl a) := by
  unfold seedContextMass scalarContextMass scalarWinnerProb
  simp_rw [seedContextJoint_cluster_factor D K]
  rw [← Finset.mul_sum]
  congr 1
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum]

private lemma scalarWinnerProb_pos_for_grouping
    {p : α × β → ℝ} {D : SeedSetup p} (K : Clustering D)
    (g b : K.κ) : 0 < scalarWinnerProb K g b := by
  have hsum : (∑ z, K.Q g z) ≠ 0 := by
    have htotal : ∑ z, K.Q g z = 1 := by
      simpa [mass] using (K.Q_isContact g).1.total
    rw [htotal]
    norm_num
  obtain ⟨z, _, hQz⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum
  have hQpos : 0 < K.Q g z :=
    lt_of_le_of_ne ((K.Q_isContact g).1.nonneg z) (Ne.symm hQz)
  have hz : z ∈ support p := by
    by_contra hz
    exact hQz ((K.Q_isContact g).2.1 z hz)
  unfold scalarWinnerProb
  apply Finset.sum_pos'
  · intro z _
    exact mul_nonneg ((K.Q_isContact g).1.nonneg z)
      (raceSigma_nonneg K b z)
  · exact ⟨z, Finset.mem_univ z, mul_pos hQpos (K.sigma_pos b z hz)⟩

private lemma seedContextSource_eq_scalarSource
    {p : α × β → ℝ} (D : SeedSetup p) (K : Clustering D)
    (a ℓ₀ : D.L.ι) (z : α × β) :
    seedContextJoint D a ℓ₀ z / seedContextMass D a ℓ₀ =
      scalarSource K (K.cl ℓ₀) (K.cl a) z := by
  rw [seedContextJoint_cluster_factor D K,
    seedContextMass_cluster_factor D K]
  unfold scalarContextMass scalarSource
  have hwa := (labelWithinWeight_pos K a).ne'
  have hw₀ := (labelWithinWeight_pos K ℓ₀).ne'
  have hs := (clusterMass_pos K (K.cl ℓ₀)).ne'
  have hP :=
    (scalarWinnerProb_pos_for_grouping K (K.cl ℓ₀) (K.cl a)).ne'
  field_simp [hwa, hw₀, hs, hP]
  <;> ring

private lemma map_seedContextMarginal_groupedPair
    {p : α × β → ℝ} (D : SeedSetup p) (K : Clustering D)
    (a ℓ₀ : D.L.ι) :
    Measure.map (groupedPair K) (seedContextMarginal D a ℓ₀) =
      (clusterSeedContextMarginal K (K.cl ℓ₀) (K.cl a)).prod
        (groupedResidualLawGivenLabel K a) := by
  have hpair : Measurable (groupedPair K) := groupedPair_measurable K
  letI : IsProbabilityMeasure (groupedResidualLawGivenLabel K a) :=
    groupedResidualLawGivenLabel_isProbability D K a
  unfold seedContextMarginal
  calc
    Measure.map (groupedPair K)
        (∑ z, ENNReal.ofReal
          (seedContextJoint D a ℓ₀ z / seedContextMass D a ℓ₀) •
            seedLawGivenWinner D a z) =
        ∑ z, Measure.map (groupedPair K)
          (ENNReal.ofReal
            (seedContextJoint D a ℓ₀ z / seedContextMass D a ℓ₀) •
              seedLawGivenWinner D a z) :=
      Measure.map_finset_sum' hpair.aemeasurable
    _ = ∑ z, ENNReal.ofReal
          (scalarSource K (K.cl ℓ₀) (K.cl a) z) •
        ((clusterSeedLawGivenWinner K (K.cl a) z).prod
          (groupedResidualLawGivenLabel K a)) := by
      apply Finset.sum_congr rfl
      intro z _
      rw [Measure.map_smul, seedContextSource_eq_scalarSource D K a ℓ₀ z]
      by_cases hz : z ∈ support p
      · rw [map_seedLawGivenWinner_groupedPair D K a z hz]
      · have hQ : K.Q (K.cl ℓ₀) z = 0 :=
          (K.Q_isContact (K.cl ℓ₀)).2.1 z hz
        simp [scalarSource, hQ]
    _ = ∑ z,
        (ENNReal.ofReal (scalarSource K (K.cl ℓ₀) (K.cl a) z) •
          clusterSeedLawGivenWinner K (K.cl a) z).prod
            (groupedResidualLawGivenLabel K a) := by
      apply Finset.sum_congr rfl
      intro z _
      rw [Measure.prod_smul_left]
    _ = (∑ z, ENNReal.ofReal
          (scalarSource K (K.cl ℓ₀) (K.cl a) z) •
            clusterSeedLawGivenWinner K (K.cl a) z).prod
          (groupedResidualLawGivenLabel K a) := by
      simpa only [Measure.sum_fintype] using
        (Measure.prod_sum_left
          (fun z => ENNReal.ofReal
            (scalarSource K (K.cl ℓ₀) (K.cl a) z) •
              clusterSeedLawGivenWinner K (K.cl a) z)
          (groupedResidualLawGivenLabel K a)).symm
    _ = (clusterSeedContextMarginal K (K.cl ℓ₀) (K.cl a)).prod
          (groupedResidualLawGivenLabel K a) := by
      rfl

private lemma seedLawGivenWinner_isProbability
    {p : α × β → ℝ} (D : SeedSetup p) (a : D.L.ι) (z : α × β) :
    IsProbabilityMeasure (seedLawGivenWinner D a z) := by
  by_cases hpost : D.post a z = 0
  · unfold seedLawGivenWinner
    rw [if_pos hpost]
    infer_instance
  · have hz : z ∈ support p := by
      by_contra hz
      have hp : p z = 0 := by simpa [support] using hz
      apply hpost
      unfold SeedSetup.post
      simp [hp]
    have hpostPos : 0 < D.post a z :=
      lt_of_le_of_ne (racePost_nonneg D a z) (Ne.symm hpost)
    constructor
    unfold seedLawGivenWinner
    rw [if_neg hpost, Measure.smul_apply, smul_eq_mul,
      Measure.restrict_apply_univ,
      label_winner_probability_measure D a z hz,
      ENNReal.inv_mul_cancel
        (ENNReal.ofReal_pos.mpr hpostPos).ne' ENNReal.ofReal_ne_top]

private lemma clusterSeedLawGivenWinner_isProbability
    {p : α × β → ℝ} {D : SeedSetup p} (K : Clustering D)
    (b : K.κ) (z : α × β) :
    IsProbabilityMeasure (clusterSeedLawGivenWinner K b z) := by
  by_cases hsigma : K.sigma b z = 0
  · unfold clusterSeedLawGivenWinner
    rw [if_pos hsigma]
    infer_instance
  · have hz : z ∈ support p := by
      by_contra hz
      have hp : p z = 0 := by simpa [support] using hz
      apply hsigma
      unfold Clustering.sigma SeedSetup.post
      simp [hp]
    have hsigmaPos : 0 < K.sigma b z :=
      lt_of_le_of_ne (raceSigma_nonneg K b z) (Ne.symm hsigma)
    constructor
    unfold clusterSeedLawGivenWinner
    rw [if_neg hsigma, Measure.smul_apply, smul_eq_mul,
      Measure.restrict_apply_univ,
      cluster_winner_probability_measure K b z hz,
      ENNReal.inv_mul_cancel
        (ENNReal.ofReal_pos.mpr hsigmaPos).ne' ENNReal.ofReal_ne_top]

private lemma scalarSource_isPMF_for_grouping
    {p : α × β → ℝ} {D : SeedSetup p} (K : Clustering D)
    (g b : K.κ) : IsPMF (scalarSource K g b) := by
  have hP := scalarWinnerProb_pos_for_grouping K g b
  constructor
  · intro z
    unfold scalarSource
    exact div_nonneg
      (mul_nonneg ((K.Q_isContact g).1.nonneg z)
        (raceSigma_nonneg K b z)) hP.le
  · unfold mass scalarSource
    rw [← Finset.sum_div]
    change scalarWinnerProb K g b / scalarWinnerProb K g b = 1
    exact div_self hP.ne'

private lemma seedContextMarginal_isProbability
    {p : α × β → ℝ} (D : SeedSetup p) (a ℓ₀ : D.L.ι) :
    IsProbabilityMeasure (seedContextMarginal D a ℓ₀) := by
  letI (z : α × β) : IsProbabilityMeasure (seedLawGivenWinner D a z) :=
    seedLawGivenWinner_isProbability D a z
  constructor
  unfold seedContextMarginal
  rw [show (∑ z, ENNReal.ofReal
      (seedContextJoint D a ℓ₀ z / seedContextMass D a ℓ₀) •
        seedLawGivenWinner D a z) Set.univ =
      ∑ z, (ENNReal.ofReal
        (seedContextJoint D a ℓ₀ z / seedContextMass D a ℓ₀) •
          seedLawGivenWinner D a z) Set.univ by simp]
  simp only [Measure.smul_apply, smul_eq_mul, measure_univ, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg
    (fun z _ => (seedSource_isPMF D a ℓ₀).nonneg z)]
  have htotal :
      ∑ z, seedContextJoint D a ℓ₀ z / seedContextMass D a ℓ₀ = 1 := by
    simpa [mass] using (seedSource_isPMF D a ℓ₀).total
  rw [htotal]
  norm_num

private lemma clusterSeedContextMarginal_isProbability
    {p : α × β → ℝ} {D : SeedSetup p} (K : Clustering D)
    (g b : K.κ) :
    IsProbabilityMeasure (clusterSeedContextMarginal K g b) := by
  letI (z : α × β) :
      IsProbabilityMeasure (clusterSeedLawGivenWinner K b z) :=
    clusterSeedLawGivenWinner_isProbability K b z
  constructor
  unfold clusterSeedContextMarginal
  rw [show (∑ z, ENNReal.ofReal (scalarSource K g b z) •
      clusterSeedLawGivenWinner K b z) Set.univ =
      ∑ z, (ENNReal.ofReal (scalarSource K g b z) •
        clusterSeedLawGivenWinner K b z) Set.univ by simp]
  simp only [Measure.smul_apply, smul_eq_mul, measure_univ, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg
    (fun z _ => (scalarSource_isPMF_for_grouping K g b).nonneg z)]
  have htotal : ∑ z, scalarSource K g b z = 1 := by
    simpa [mass] using (scalarSource_isPMF_for_grouping K g b).total
  rw [htotal]
  norm_num

private lemma seedCluster_klDiv_eq
    {p : α × β → ℝ} (D : SeedSetup p) (K : Clustering D)
    (a ℓ₀ : D.L.ι) (z : α × β) (hz : z ∈ support p) :
    klDiv (seedLawGivenWinner D a z) (seedContextMarginal D a ℓ₀) =
      klDiv (clusterSeedLawGivenWinner K (K.cl a) z)
        (clusterSeedContextMarginal K (K.cl ℓ₀) (K.cl a)) := by
  letI : IsProbabilityMeasure (seedLawGivenWinner D a z) :=
    seedLawGivenWinner_isProbability D a z
  letI : IsProbabilityMeasure (seedContextMarginal D a ℓ₀) :=
    seedContextMarginal_isProbability D a ℓ₀
  letI : IsProbabilityMeasure
      (clusterSeedLawGivenWinner K (K.cl a) z) :=
    clusterSeedLawGivenWinner_isProbability K (K.cl a) z
  letI : IsProbabilityMeasure
      (clusterSeedContextMarginal K (K.cl ℓ₀) (K.cl a)) :=
    clusterSeedContextMarginal_isProbability K (K.cl ℓ₀) (K.cl a)
  letI : IsProbabilityMeasure (groupedResidualLawGivenLabel K a) :=
    groupedResidualLawGivenLabel_isProbability D K a
  calc
    klDiv (seedLawGivenWinner D a z) (seedContextMarginal D a ℓ₀) =
        klDiv (Measure.map (groupedPair K) (seedLawGivenWinner D a z))
          (Measure.map (groupedPair K) (seedContextMarginal D a ℓ₀)) :=
      (klDiv_map_groupedPair K _ _).symm
    _ = klDiv
        ((clusterSeedLawGivenWinner K (K.cl a) z).prod
          (groupedResidualLawGivenLabel K a))
        ((clusterSeedContextMarginal K (K.cl ℓ₀) (K.cl a)).prod
          (groupedResidualLawGivenLabel K a)) := by
      rw [map_seedLawGivenWinner_groupedPair D K a z hz,
        map_seedContextMarginal_groupedPair D K a ℓ₀]
    _ = klDiv (clusterSeedLawGivenWinner K (K.cl a) z)
        (clusterSeedContextMarginal K (K.cl ℓ₀) (K.cl a)) :=
      klDiv_prod_same_right _ _ _

private lemma seedCluster_condMI_summand
    {p : α × β → ℝ} (D : SeedSetup p) (K : Clustering D)
    (a ℓ₀ : D.L.ι) (z : α × β) :
    seedContextJoint D a ℓ₀ z *
        (klDiv (seedLawGivenWinner D a z)
          (seedContextMarginal D a ℓ₀)).toReal =
      labelWithinWeight K a * labelWithinWeight K ℓ₀ *
        (K.s (K.cl ℓ₀) * K.Q (K.cl ℓ₀) z *
          K.sigma (K.cl a) z *
            (klDiv (clusterSeedLawGivenWinner K (K.cl a) z)
              (clusterSeedContextMarginal K (K.cl ℓ₀) (K.cl a))).toReal) := by
  by_cases hz : z ∈ support p
  · rw [seedContextJoint_cluster_factor D K,
      seedCluster_klDiv_eq D K a ℓ₀ z hz]
    ring
  · have hQ : K.Q (K.cl ℓ₀) z = 0 :=
      (K.Q_isContact (K.cl ℓ₀)).2.1 z hz
    rw [seedContextJoint_cluster_factor D K, hQ]
    ring

private lemma sum_labelWithinWeight_comp
    {p : α × β → ℝ} {D : SeedSetup p} (K : Clustering D)
    (F : K.κ → ℝ) :
    ∑ a, labelWithinWeight K a * F (K.cl a) = ∑ c, F c := by
  calc
    (∑ a, labelWithinWeight K a * F (K.cl a)) =
        ∑ c, push K.cl (labelWithinWeight K) c * F c :=
      (sum_push_mul K.cl (labelWithinWeight K) F).symm
    _ = ∑ c, F c := by
      apply Finset.sum_congr rfl
      intro c _
      have hpush : push K.cl (labelWithinWeight K) c = 1 := by
        unfold push
        exact labelWithinWeight_fiber_sum K c
      rw [hpush, one_mul]

private lemma sum_labelWithinWeight_pair
    {p : α × β → ℝ} {D : SeedSetup p} (K : Clustering D)
    (F : K.κ → K.κ → ℝ) :
    ∑ a, ∑ ℓ₀,
        labelWithinWeight K a * labelWithinWeight K ℓ₀ *
          F (K.cl ℓ₀) (K.cl a) =
      ∑ b, ∑ g, F g b := by
  calc
    (∑ a, ∑ ℓ₀,
        labelWithinWeight K a * labelWithinWeight K ℓ₀ *
          F (K.cl ℓ₀) (K.cl a)) =
        ∑ a, labelWithinWeight K a *
          (∑ ℓ₀, labelWithinWeight K ℓ₀ *
            F (K.cl ℓ₀) (K.cl a)) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ℓ₀ _
      ring
    _ = ∑ a, labelWithinWeight K a *
          (∑ g, F g (K.cl a)) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [sum_labelWithinWeight_comp K (fun g => F g (K.cl a))]
    _ = ∑ b, ∑ g, F g b :=
      sum_labelWithinWeight_comp K (fun b => ∑ g, F g b)

/-- Lemma 7.2(c): after the independent within-cluster variables are removed,
the label-seed leak is exactly the grouped-Gumbel leak. -/
private theorem race_grouping_identity {p : α × β → ℝ}
    (D : SeedSetup p) (K : Clustering D) :
    raceSeedLeak D = raceClusterLeak K := by
  unfold raceSeedLeak raceClusterLeak condMIcts
  apply congrArg (fun x : ℝ => x / Real.log 2)
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  simp_rw [seedCluster_condMI_summand D K]
  simpa only [Finset.mul_sum] using
    (sum_labelWithinWeight_pair K (fun g b =>
      ∑ z, K.s g * K.Q g z * K.sigma b z *
        (klDiv (clusterSeedLawGivenWinner K b z)
          (clusterSeedContextMarginal K g b)).toReal))

/-- Lemma 7.2(d), already finite in `stoch_to_det.Quotient`: replica information and
mismatch both descend exactly to clusters. -/
private theorem cluster_replica_identities {p : α × β → ℝ}
    (D : SeedSetup p) (K : Clustering D) :
    K.Sinfo = bZ D ∧
      K.dMis = ∑ z, p z * (1 - ∑ c, K.sigma c z ^ 2) := by
  exact ⟨K.Sinfo_eq_bZ, K.dMis_eq⟩

private lemma balance_p_mul_post {p : α × β → ℝ}
    (D : SeedSetup p) (l : D.L.ι) (z : α × β) :
    p z * D.post l z = D.L.prior l * D.L.comp l z := by
  unfold SeedSetup.post
  by_cases hpz : p z = 0
  · have hle : D.L.prior l * D.L.comp l z ≤
        ∑ v, D.L.prior v * D.L.comp v z := by
      simpa using (Finset.single_le_sum
        (s := (Finset.univ : Finset D.L.ι))
        (fun v _ => mul_nonneg (D.L.prior_isPMF.nonneg v)
          ((D.L.comp_isPMF v).nonneg z))
        (Finset.mem_univ l))
    rw [D.L.mixture z, hpz] at hle
    have hzero : D.L.prior l * D.L.comp l z = 0 :=
      le_antisymm hle
        (mul_nonneg (D.L.prior_isPMF.nonneg l)
          ((D.L.comp_isPMF l).nonneg z))
    simp [hpz, hzero]
  · field_simp

private lemma balance_comp_eq_zero_of_p_eq_zero {p : α × β → ℝ}
    (D : SeedSetup p) (l : D.L.ι) (z : α × β) (hpz : p z = 0) :
    D.L.comp l z = 0 := by
  have hprod := balance_p_mul_post D l z
  have hprod0 : D.L.prior l * D.L.comp l z = 0 := by
    calc
      D.L.prior l * D.L.comp l z = p z * D.post l z := hprod.symm
      _ = 0 := by rw [hpz]; simp
  exact (mul_eq_zero.mp hprod0).resolve_left (D.prior_pos l).ne'

private lemma balance_sum_comp_mul_post {p : α × β → ℝ}
    (D : SeedSetup p) (l₀ : D.L.ι) (z : α × β) :
    (∑ l₁, D.L.comp l₀ z * D.post l₁ z) = D.L.comp l₀ z := by
  by_cases hpz : p z = 0
  · simp [balance_comp_eq_zero_of_p_eq_zero D l₀ z hpz]
  · rw [← Finset.mul_sum, sum_post_of_pos D z
      (lt_of_le_of_ne (D.isPMF.nonneg z) (Ne.symm hpz)), mul_one]

private lemma balance_resamplePrior_nonneg {p : α × β → ℝ}
    (D : SeedSetup p) (l₀ l₁ : D.L.ι) :
    0 ≤ resamplePrior D l₀ l₁ := by
  unfold resamplePrior
  exact Finset.sum_nonneg fun z _ =>
    mul_nonneg ((D.L.comp_isPMF l₀).nonneg z) (post_nonneg D l₁ z)

private lemma balance_sum_resamplePrior {p : α × β → ℝ}
    (D : SeedSetup p) (l₀ : D.L.ι) :
    ∑ l₁, resamplePrior D l₀ l₁ = 1 := by
  unfold resamplePrior
  calc
    (∑ l₁, ∑ z, D.L.comp l₀ z * D.post l₁ z) =
        ∑ z, ∑ l₁, D.L.comp l₀ z * D.post l₁ z := Finset.sum_comm
    _ = ∑ z, D.L.comp l₀ z := by
      apply Finset.sum_congr rfl
      intro z _
      exact balance_sum_comp_mul_post D l₀ z
    _ = 1 := by simpa [mass] using (D.L.comp_isPMF l₀).total

private lemma balance_seedContextMass_eq {p : α × β → ℝ}
    (D : SeedSetup p) (a l₀ : D.L.ι) :
    seedContextMass D a l₀ =
      D.L.prior l₀ * resamplePrior D l₀ a := by
  unfold seedContextMass seedContextJoint Latent.joint resamplePrior
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  ring

private lemma balance_resamplePrior_pos {p : α × β → ℝ}
    (D : SeedSetup p) (l₀ a : D.L.ι) :
    0 < resamplePrior D l₀ a := by
  have hmass := seedContextMass_pos D a l₀
  rw [balance_seedContextMass_eq D a l₀] at hmass
  by_contra h
  have hnonpos : resamplePrior D l₀ a ≤ 0 := le_of_not_gt h
  have hprod : D.L.prior l₀ * resamplePrior D l₀ a ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (D.prior_pos l₀).le hnonpos
  exact (not_lt_of_ge hprod) hmass

private noncomputable def balanceWinnerProb {p : α × β → ℝ}
    (D : SeedSetup p) (A : α × β → D.L.ι) (l₀ a : D.L.ι) : ℝ :=
  ∑ z, if A z = a then D.L.comp l₀ z else 0

private lemma balanceWinnerProb_nonneg {p : α × β → ℝ}
    (D : SeedSetup p) (A : α × β → D.L.ι) (l₀ a : D.L.ι) :
    0 ≤ balanceWinnerProb D A l₀ a := by
  unfold balanceWinnerProb
  exact Finset.sum_nonneg fun z _ => by
    by_cases h : A z = a
    · simp [h, (D.L.comp_isPMF l₀).nonneg z]
    · simp [h]

private lemma balance_sum_winnerProb {p : α × β → ℝ}
    (D : SeedSetup p) (A : α × β → D.L.ι) (l₀ : D.L.ι) :
    ∑ a, balanceWinnerProb D A l₀ a = 1 := by
  unfold balanceWinnerProb
  rw [Finset.sum_comm]
  calc
    (∑ z, ∑ a, if A z = a then D.L.comp l₀ z else 0) =
        ∑ z, D.L.comp l₀ z := by simp
    _ = 1 := by simpa [mass] using (D.L.comp_isPMF l₀).total

private lemma balanceWinnerProb_eq_push {p : α × β → ℝ}
    (D : SeedSetup p) (A : α × β → D.L.ι) (l₀ a : D.L.ι) :
    balanceWinnerProb D A l₀ a = push A (D.L.comp l₀) a := by
  unfold balanceWinnerProb push
  rw [Finset.sum_filter]

private lemma balance_winnerEvent_ae_lex {p : α × β → ℝ}
    (D : SeedSetup p) (a : D.L.ι) (z : α × β) :
    {ε | winner D ε z = a} =ᵐ[seedLaw D.L.ι]
      {ε | lexWinner D ε z = a} := by
  filter_upwards [winner_ae_eq_lexWinner D] with ε hε
  apply propext
  change (winner D ε z = a ↔ lexWinner D ε z = a)
  rw [congrFun hε z]

private lemma balance_lexWinnerEvent_measurable {p : α × β → ℝ}
    (D : SeedSetup p) (a : D.L.ι) (z : α × β) :
    MeasurableSet {ε | lexWinner D ε z = a} := by
  letI : MeasurableSpace D.L.ι := ⊤
  have hlex : Measurable (fun ε => lexWinner D ε z) := by
    unfold lexWinner
    apply measurable_lexMax
    intro b
    exact measurable_const.add (measurable_pi_apply b)
  exact measurableSet_singleton a |>.preimage hlex

private lemma balance_seedLawGivenWinner_eq_lex {p : α × β → ℝ}
    (D : SeedSetup p) (a : D.L.ι) (z : α × β)
    (hpost : 0 < D.post a z) :
    seedLawGivenWinner D a z =
      (ENNReal.ofReal (D.post a z))⁻¹ •
        (seedLaw D.L.ι).restrict {ε | lexWinner D ε z = a} := by
  unfold seedLawGivenWinner
  rw [if_neg hpost.ne',
    Measure.restrict_congr_set (balance_winnerEvent_ae_lex D a z)]

private lemma balance_seedWinner_klDiv_seedLaw {p : α × β → ℝ}
    (D : SeedSetup p) (a : D.L.ι) (z : α × β)
    (hpost : 0 < D.post a z) :
    (klDiv (seedLawGivenWinner D a z) (seedLaw D.L.ι)).toReal =
        Real.log (1 / D.post a z) ∧
      klDiv (seedLawGivenWinner D a z) (seedLaw D.L.ι) ≠ ⊤ := by
  let ν : Measure (D.L.ι → ℝ) := seedLaw D.L.ι
  let μ : Measure (D.L.ι → ℝ) := seedLawGivenWinner D a z
  let s : Set (D.L.ι → ℝ) := {ε | lexWinner D ε z = a}
  let c : ℝ≥0∞ := (ENNReal.ofReal (D.post a z))⁻¹
  letI : IsProbabilityMeasure ν := by
    dsimp only [ν]
    infer_instance
  letI : IsProbabilityMeasure μ := by
    dsimp only [μ]
    exact seedLawGivenWinner_isProbability D a z
  have hs : MeasurableSet s := balance_lexWinnerEvent_measurable D a z
  have hμ : μ = c • ν.restrict s := by
    dsimp only [μ, c, ν, s]
    exact balance_seedLawGivenWinner_eq_lex D a z hpost
  have hcTop : c ≠ ⊤ := by
    exact (ENNReal.inv_lt_top.mpr (ENNReal.ofReal_pos.mpr hpost)).ne
  have hμν : μ ≪ ν := by
    rw [hμ]
    exact Measure.absolutelyContinuous_restrict.smul_left c
  have hrn : μ.rnDeriv ν =ᵐ[ν]
      (fun x => c • s.indicator (fun _ => (1 : ℝ≥0∞)) x) := by
    rw [hμ]
    exact (Measure.rnDeriv_smul_left_of_ne_top (ν.restrict s) ν hcTop).trans
      ((Measure.rnDeriv_restrict_self ν hs).const_smul c)
  have hmem : ∀ᵐ x ∂μ, x ∈ s := by
    rw [hμ]
    exact Measure.ae_smul_measure (ae_restrict_mem hs) c
  have hllr : llr μ ν =ᵐ[μ]
      fun _ => Real.log (1 / D.post a z) := by
    filter_upwards [hμν.ae_le hrn, hmem] with x hx hxs
    rw [llr, hx]
    simp [Set.indicator_of_mem hxs, c, ENNReal.toReal_inv,
      ENNReal.toReal_ofReal hpost.le]
  have hint : Integrable (llr μ ν) μ := by
    exact (integrable_const (Real.log (1 / D.post a z))).congr hllr.symm
  have hvalue : (klDiv μ ν).toReal = Real.log (1 / D.post a z) := by
    rw [toReal_klDiv_of_measure_eq hμν (by simp), integral_congr_ae hllr]
    simp
  exact ⟨hvalue, klDiv_ne_top hμν hint⟩

private theorem balance_finite_mixture_golden_eq
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (r : ι → ℝ) (P : ι → Measure Ω) (M Q : Measure Ω)
    (hr : IsPMF r)
    (hP : ∀ i, IsProbabilityMeasure (P i))
    (hMprob : IsProbabilityMeasure M) (hQprob : IsProbabilityMeasure Q)
    (hM : M = ∑ i, ENNReal.ofReal (r i) • P i)
    (hPMfinite : ∀ i, 0 < r i → klDiv (P i) M ≠ ⊤)
    (hPQfinite : ∀ i, 0 < r i → klDiv (P i) Q ≠ ⊤) :
    (∑ i, r i * (klDiv (P i) Q).toReal) =
      (∑ i, r i * (klDiv (P i) M).toReal) + (klDiv M Q).toReal := by
  letI (i : ι) : IsProbabilityMeasure (P i) := hP i
  letI : IsProbabilityMeasure M := hMprob
  letI : IsProbabilityMeasure Q := hQprob
  have hMQ : M ≪ Q := by
    intro s hQs
    rw [hM, Measure.finsetSum_apply]
    apply Finset.sum_eq_zero
    intro i _
    rw [Measure.smul_apply, smul_eq_mul]
    by_cases hri : r i = 0
    · simp [hri]
    · have hriPos : 0 < r i :=
        lt_of_le_of_ne (hr.nonneg i) (Ne.symm hri)
      have hiQ : P i ≪ Q :=
        (klDiv_ne_top_iff.mp (hPQfinite i hriPos)).1
      rw [hiQ hQs]
      simp
  have hchain (i : ι) (hi : 0 < r i) :
      llr (P i) Q =ᵐ[P i]
        fun x => llr (P i) M x + llr M Q x := by
    exact llr_chain_ae (P i) M Q
      (klDiv_ne_top_iff.mp (hPMfinite i hi)).1 hMQ
  have hMQintegrableP (i : ι) (hi : 0 < r i) :
      Integrable (llr M Q) (P i) := by
    have hPMint := (klDiv_ne_top_iff.mp (hPMfinite i hi)).2
    have hPQint := (klDiv_ne_top_iff.mp (hPQfinite i hi)).2
    have hsum : Integrable
        (fun x => llr (P i) M x + llr M Q x) (P i) := by
      exact hPQint.congr (hchain i hi)
    exact (integrable_add_iff_integrable_right' hPMint).mp hsum
  have hMQintegrable : Integrable (llr M Q) M := by
    have hmix : Integrable (llr M Q)
        (∑ i, ENNReal.ofReal (r i) • P i) := by
      rw [integrable_finsetSum_measure]
      intro i _
      by_cases hri : r i = 0
      · simp [hri]
      · exact (hMQintegrableP i
          (lt_of_le_of_ne (hr.nonneg i) (Ne.symm hri))).smul_measure
            ENNReal.ofReal_ne_top
    simpa only [← hM] using hmix
  have hterm (i : ι) (hriPos : 0 < r i) :
      (klDiv (P i) Q).toReal =
        (klDiv (P i) M).toReal + ∫ x, llr M Q x ∂P i := by
    have hPMdata := klDiv_ne_top_iff.mp (hPMfinite i hriPos)
    have hPQdata := klDiv_ne_top_iff.mp (hPQfinite i hriPos)
    rw [toReal_klDiv hPQdata.1 hPQdata.2,
      toReal_klDiv hPMdata.1 hPMdata.2]
    rw [integral_congr_ae (hchain i hriPos),
      integral_add hPMdata.2 (hMQintegrableP i hriPos)]
    simp only [probReal_univ]
    ring
  have hintegral :
      ∫ x, llr M Q x ∂M =
        ∑ i, r i * ∫ x, llr M Q x ∂P i := by
    calc
      (∫ x, llr M Q x ∂M) =
          ∫ x, llr M Q x ∂(∑ i, ENNReal.ofReal (r i) • P i) :=
        congrArg (fun μ => ∫ x, llr M Q x ∂μ) hM
      _ = ∑ i, ∫ x, llr M Q x ∂(ENNReal.ofReal (r i) • P i) := by
        apply integral_finsetSum_measure
        intro i _
        by_cases hri : r i = 0
        · simp [hri]
        · exact (hMQintegrableP i
            (lt_of_le_of_ne (hr.nonneg i) (Ne.symm hri))).smul_measure
              ENNReal.ofReal_ne_top
      _ = ∑ i, r i * ∫ x, llr M Q x ∂P i := by
        apply Finset.sum_congr rfl
        intro i _
        rw [integral_smul_measure, smul_eq_mul,
          ENNReal.toReal_ofReal (hr.nonneg i)]
  have hMQvalue : (klDiv M Q).toReal = ∫ x, llr M Q x ∂M := by
    rw [toReal_klDiv hMQ hMQintegrable]
    simp
  calc
    (∑ i, r i * (klDiv (P i) Q).toReal) =
        ∑ i, (r i * (klDiv (P i) M).toReal +
          r i * ∫ x, llr M Q x ∂P i) := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hri : r i = 0
      · simp [hri]
      · rw [hterm i (lt_of_le_of_ne (hr.nonneg i) (Ne.symm hri))]
        ring
    _ = (∑ i, r i * (klDiv (P i) M).toReal) +
        ∑ i, r i * ∫ x, llr M Q x ∂P i := by
      rw [Finset.sum_add_distrib]
    _ = (∑ i, r i * (klDiv (P i) M).toReal) +
        (klDiv M Q).toReal := by rw [← hintegral, ← hMQvalue]

private lemma balance_seed_context_golden {p : α × β → ℝ}
    (D : SeedSetup p) (a l₀ : D.L.ι) :
    (∑ z, (seedContextJoint D a l₀ z / seedContextMass D a l₀) *
        (klDiv (seedLawGivenWinner D a z)
          (seedContextMarginal D a l₀)).toReal) =
      (∑ z, (seedContextJoint D a l₀ z / seedContextMass D a l₀) *
        Real.log (1 / D.post a z)) -
      (klDiv (seedContextMarginal D a l₀) (seedLaw D.L.ι)).toReal := by
  let r : α × β → ℝ := fun z =>
    seedContextJoint D a l₀ z / seedContextMass D a l₀
  let P : α × β → Measure (D.L.ι → ℝ) := fun z =>
    seedLawGivenWinner D a z
  let M : Measure (D.L.ι → ℝ) := seedContextMarginal D a l₀
  let Q : Measure (D.L.ι → ℝ) := seedLaw D.L.ι
  have hmass := seedContextMass_pos D a l₀
  have hjoint_of_pos (z : α × β) (hz : 0 < r z) :
      0 < seedContextJoint D a l₀ z := by
    have heq : seedContextJoint D a l₀ z =
        r z * seedContextMass D a l₀ := by
      dsimp only [r]
      field_simp [hmass.ne']
    rw [heq]
    exact mul_pos hz hmass
  have hpost_of_pos (z : α × β) (hz : 0 < r z) :
      0 < D.post a z := by
    have hjoint := hjoint_of_pos z hz
    have hpostNe : D.post a z ≠ 0 := by
      intro hpost
      unfold seedContextJoint at hjoint
      simp [hpost] at hjoint
    exact lt_of_le_of_ne (post_nonneg D a z) (Ne.symm hpostNe)
  have hgold := balance_finite_mixture_golden_eq r P M Q
    (seedSource_isPMF D a l₀)
    (fun z => seedLawGivenWinner_isProbability D a z)
    (seedContextMarginal_isProbability D a l₀)
    (inferInstance : IsProbabilityMeasure (seedLaw D.L.ι))
    rfl
    (fun z hz => seedWinner_klDiv_ne_top D a l₀ z
      (hjoint_of_pos z hz))
    (fun z hz => (balance_seedWinner_klDiv_seedLaw D a z
      (hpost_of_pos z hz)).2)
  have hreference :
      (∑ z, r z * (klDiv (P z) Q).toReal) =
        ∑ z, r z * Real.log (1 / D.post a z) := by
    apply Finset.sum_congr rfl
    intro z _
    by_cases hz : r z = 0
    · simp [hz]
    · have hzpos : 0 < r z :=
        lt_of_le_of_ne ((seedSource_isPMF D a l₀).nonneg z) (Ne.symm hz)
      rw [(balance_seedWinner_klDiv_seedLaw D a z
        (hpost_of_pos z hzpos)).1]
  dsimp only [r, P, M, Q] at hgold hreference ⊢
  rw [hreference] at hgold
  linarith

private noncomputable def balanceRestrictionCostNats {p : α × β → ℝ}
    (D : SeedSetup p) : ℝ :=
  ∑ a, ∑ l₀, ∑ z,
    seedContextJoint D a l₀ z * Real.log (1 / D.post a z)

private noncomputable def balanceMarginalCostNats {p : α × β → ℝ}
    (D : SeedSetup p) : ℝ :=
  ∑ a, ∑ l₀, seedContextMass D a l₀ *
    (klDiv (seedContextMarginal D a l₀) (seedLaw D.L.ι)).toReal

private lemma balance_raceSeedLeak_decomp {p : α × β → ℝ}
    (D : SeedSetup p) :
    raceSeedLeak D =
      (balanceRestrictionCostNats D - balanceMarginalCostNats D) /
        Real.log 2 := by
  unfold raceSeedLeak condMIcts
  rw [Fintype.sum_prod_type]
  apply congrArg (fun x : ℝ => x / Real.log 2)
  unfold balanceRestrictionCostNats balanceMarginalCostNats
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro l₀ _
  have hmass := seedContextMass_pos D a l₀
  have hscale (F : α × β → ℝ) :
      seedContextMass D a l₀ *
          (∑ z, (seedContextJoint D a l₀ z /
            seedContextMass D a l₀) * F z) =
        ∑ z, seedContextJoint D a l₀ z * F z := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro z _
    field_simp [hmass.ne']
  have hgold := congrArg (fun x : ℝ => seedContextMass D a l₀ * x)
    (balance_seed_context_golden D a l₀)
  rw [mul_sub,
    hscale (fun z => (klDiv (seedLawGivenWinner D a z)
      (seedContextMarginal D a l₀)).toReal),
    hscale (fun z => Real.log (1 / D.post a z))] at hgold
  exact hgold

private lemma balance_sum_seedContextJoint_l₀ {p : α × β → ℝ}
    (D : SeedSetup p) (a : D.L.ι) (z : α × β) :
    ∑ l₀, seedContextJoint D a l₀ z = p z * D.post a z := by
  unfold seedContextJoint Latent.joint
  rw [← Finset.sum_mul, D.L.mixture z]

private lemma balance_push_joint_fiber {p : α × β → ℝ}
    (D : SeedSetup p) (z : α × β) :
    push (fun q : D.L.ι × (α × β) => q.1)
        (fun q => if q.2 = z then D.L.joint q else 0) =
      fun l => D.L.joint (l, z) := by
  funext l
  unfold push
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  simp

private lemma balance_H_joint_fiber {p : α × β → ℝ}
    (D : SeedSetup p) (z : α × β) :
    Real.log 2 * H (fun l => D.L.joint (l, z)) =
      ∑ a, p z * D.post a z * Real.log (1 / D.post a z) := by
  have hmass : mass (fun l => D.L.joint (l, z)) = p z := by
    unfold mass Latent.joint
    exact D.L.mixture z
  unfold H
  rw [hmass, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  by_cases hpz : p z = 0
  · have hcomp := balance_comp_eq_zero_of_p_eq_zero D a z hpz
    simp [Latent.joint, hpz, hcomp]
  · have hpzPos : 0 < p z :=
      lt_of_le_of_ne (D.isPMF.nonneg z) (Ne.symm hpz)
    have hpost : 0 < D.post a z := post_pos_contact D a z hpzPos
    have hjoint : D.L.joint (a, z) = p z * D.post a z := by
      unfold Latent.joint
      exact (balance_p_mul_post D a z).symm
    have hratio : p z / (p z * D.post a z) = 1 / D.post a z := by
      field_simp [hpz, hpost.ne']
    change Real.log 2 *
        (D.L.joint (a, z) * lg (p z / D.L.joint (a, z))) = _
    rw [hjoint, hratio, lg_eq_log_div]
    field_simp [(Real.log_pos one_lt_two).ne']

private lemma balance_condH_joint_eq_fibers {p : α × β → ℝ}
    (D : SeedSetup p) :
    condH (fun q : D.L.ι × (α × β) => q.1) (fun q => q.2)
        D.L.joint =
      ∑ z, H (fun l => D.L.joint (l, z)) := by
  rw [condH_eq_sum_H_fibers D.L.joint_isPMF]
  simp_rw [balance_push_joint_fiber D]

private lemma balance_restrictionCost_eq_condH {p : α × β → ℝ}
    (D : SeedSetup p) :
    balanceRestrictionCostNats D =
      Real.log 2 *
        condH (fun q : D.L.ι × (α × β) => q.1) (fun q => q.2)
          D.L.joint := by
  unfold balanceRestrictionCostNats
  calc
    (∑ a, ∑ l₀, ∑ z,
        seedContextJoint D a l₀ z * Real.log (1 / D.post a z)) =
        ∑ a, ∑ z, ∑ l₀,
          seedContextJoint D a l₀ z * Real.log (1 / D.post a z) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
    _ = ∑ z, ∑ a, ∑ l₀,
          seedContextJoint D a l₀ z * Real.log (1 / D.post a z) :=
      Finset.sum_comm
    _ = ∑ z, ∑ a,
        p z * D.post a z * Real.log (1 / D.post a z) := by
      apply Finset.sum_congr rfl
      intro z _
      apply Finset.sum_congr rfl
      intro a _
      rw [← Finset.sum_mul, balance_sum_seedContextJoint_l₀ D a z]
    _ = ∑ z, Real.log 2 * H (fun l => D.L.joint (l, z)) := by
      apply Finset.sum_congr rfl
      intro z _
      exact (balance_H_joint_fiber D z).symm
    _ = Real.log 2 * ∑ z, H (fun l => D.L.joint (l, z)) := by
      rw [Finset.mul_sum]
    _ = Real.log 2 *
        condH (fun q : D.L.ι × (α × β) => q.1) (fun q => q.2)
          D.L.joint := by rw [balance_condH_joint_eq_fibers D]

private noncomputable def balanceDensityReal {p : α × β → ℝ}
    (D : SeedSetup p) (l₀ a : D.L.ι) (ε : D.L.ι → ℝ) : ℝ :=
  balanceWinnerProb D (lexWinner D ε) l₀ a / resamplePrior D l₀ a

private noncomputable def balanceDensity {p : α × β → ℝ}
    (D : SeedSetup p) (l₀ a : D.L.ι) (ε : D.L.ι → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (balanceDensityReal D l₀ a ε)

private lemma balanceDensityReal_nonneg {p : α × β → ℝ}
    (D : SeedSetup p) (l₀ a : D.L.ι) (ε : D.L.ι → ℝ) :
    0 ≤ balanceDensityReal D l₀ a ε := by
  unfold balanceDensityReal
  exact div_nonneg (balanceWinnerProb_nonneg D _ l₀ a)
    (balance_resamplePrior_pos D l₀ a).le

private lemma balanceDensity_measurable {p : α × β → ℝ}
    (D : SeedSetup p) (l₀ a : D.L.ι) :
    Measurable (balanceDensity D l₀ a) := by
  unfold balanceDensity balanceDensityReal balanceWinnerProb
  apply ENNReal.measurable_ofReal.comp
  apply Measurable.div_const
  apply Finset.measurable_sum
  intro z _
  exact Measurable.ite (balance_lexWinnerEvent_measurable D a z)
    measurable_const measurable_const

private lemma balance_integrable_lex_code {p : α × β → ℝ}
    (D : SeedSetup p) (F : ((α × β) → D.L.ι) → ℝ) :
    Integrable (fun ε => F (lexWinner D ε)) (seedLaw D.L.ι) := by
  have hbase := integrable_winner_code D F
  apply hbase.congr
  filter_upwards [winner_ae_eq_lexWinner D] with ε hε
  rw [hε]

private lemma balance_integral_winnerProb {p : α × β → ℝ}
    (D : SeedSetup p) (l₀ a : D.L.ι) :
    (∫ ε, balanceWinnerProb D (lexWinner D ε) l₀ a
        ∂(seedLaw D.L.ι)) = resamplePrior D l₀ a := by
  have hae :
      (fun ε => balanceWinnerProb D (lexWinner D ε) l₀ a) =ᵐ[
        seedLaw D.L.ι]
        fun ε => balanceWinnerProb D (winner D ε) l₀ a := by
    filter_upwards [winner_ae_eq_lexWinner D] with ε hε
    rw [hε]
  rw [integral_congr_ae hae]
  unfold balanceWinnerProb resamplePrior
  calc
    (∫ ε, ∑ z, (if winner D ε z = a then D.L.comp l₀ z else 0)
        ∂(seedLaw D.L.ι)) =
        ∑ z, ∫ ε, (if winner D ε z = a then D.L.comp l₀ z else 0)
          ∂(seedLaw D.L.ι) := by
      rw [integral_finsetSum Finset.univ]
      intro z _
      let F : ((α × β) → D.L.ι) → ℝ := fun A =>
        if A z = a then D.L.comp l₀ z else 0
      simpa only [F] using integrable_winner_code D F
    _ = ∑ z, D.L.comp l₀ z * D.post a z := by
      apply Finset.sum_congr rfl
      intro z _
      exact integral_winner_component D z a l₀

private noncomputable def balanceTermDensity {p : α × β → ℝ}
    (D : SeedSetup p) (l₀ a : D.L.ι) (z : α × β)
    (ε : D.L.ι → ℝ) : ℝ≥0∞ :=
  if lexWinner D ε z = a then
    ENNReal.ofReal (D.L.comp l₀ z / resamplePrior D l₀ a)
  else 0

private lemma balanceTermDensity_measurable {p : α × β → ℝ}
    (D : SeedSetup p) (l₀ a : D.L.ι) (z : α × β) :
    Measurable (balanceTermDensity D l₀ a z) := by
  unfold balanceTermDensity
  exact Measurable.ite (balance_lexWinnerEvent_measurable D a z)
    measurable_const measurable_const

private lemma balanceDensity_eq_sum_terms {p : α × β → ℝ}
    (D : SeedSetup p) (l₀ a : D.L.ι) (ε : D.L.ι → ℝ) :
    balanceDensity D l₀ a ε =
      ∑ z, balanceTermDensity D l₀ a z ε := by
  unfold balanceDensity balanceDensityReal balanceWinnerProb
  rw [Finset.sum_div]
  rw [ENNReal.ofReal_sum_of_nonneg]
  · apply Finset.sum_congr rfl
    intro z _
    unfold balanceTermDensity
    by_cases hz : lexWinner D ε z = a
    · simp [hz]
    · simp [hz]
  · intro z _
    by_cases hz : lexWinner D ε z = a
    · simp [hz]
      exact div_nonneg ((D.L.comp_isPMF l₀).nonneg z)
        (balance_resamplePrior_pos D l₀ a).le
    · simp [hz]

private lemma balance_context_mixture_term {p : α × β → ℝ}
    (D : SeedSetup p) (a l₀ : D.L.ι) (z : α × β) :
    ENNReal.ofReal
          (seedContextJoint D a l₀ z / seedContextMass D a l₀) •
        seedLawGivenWinner D a z =
      ENNReal.ofReal (D.L.comp l₀ z / resamplePrior D l₀ a) •
        (seedLaw D.L.ι).restrict {ε | lexWinner D ε z = a} := by
  by_cases hpz : p z = 0
  · have hcomp := balance_comp_eq_zero_of_p_eq_zero D l₀ z hpz
    have hjoint : seedContextJoint D a l₀ z = 0 := by
      unfold seedContextJoint Latent.joint
      simp [hcomp]
    simp [hjoint, hcomp]
  · have hpzPos : 0 < p z :=
      lt_of_le_of_ne (D.isPMF.nonneg z) (Ne.symm hpz)
    have hpost : 0 < D.post a z := post_pos_contact D a z hpzPos
    rw [balance_seedLawGivenWinner_eq_lex D a z hpost, smul_smul]
    congr 1
    rw [← ENNReal.ofReal_inv_of_pos hpost,
      ← ENNReal.ofReal_mul ((seedSource_isPMF D a l₀).nonneg z)]
    congr 1
    rw [balance_seedContextMass_eq D a l₀]
    unfold seedContextJoint Latent.joint
    field_simp [(D.prior_pos l₀).ne',
      (balance_resamplePrior_pos D l₀ a).ne', hpost.ne']
    <;> ring

private lemma balance_term_measure_eq_withDensity {p : α × β → ℝ}
    (D : SeedSetup p) (l₀ a : D.L.ι) (z : α × β) :
    ENNReal.ofReal (D.L.comp l₀ z / resamplePrior D l₀ a) •
        (seedLaw D.L.ι).restrict {ε | lexWinner D ε z = a} =
      (seedLaw D.L.ι).withDensity (balanceTermDensity D l₀ a z) := by
  let s : Set (D.L.ι → ℝ) := {ε | lexWinner D ε z = a}
  let c : ℝ≥0∞ := ENNReal.ofReal
    (D.L.comp l₀ z / resamplePrior D l₀ a)
  have hs : MeasurableSet s := balance_lexWinnerEvent_measurable D a z
  have hdensity : balanceTermDensity D l₀ a z =
      fun ε => c • s.indicator (fun _ => (1 : ℝ≥0∞)) ε := by
    funext ε
    unfold balanceTermDensity
    by_cases hε : lexWinner D ε z = a
    · simp [s, c, hε]
    · simp [s, c, hε]
  change c • (seedLaw D.L.ι).restrict s =
    (seedLaw D.L.ι).withDensity (balanceTermDensity D l₀ a z)
  rw [hdensity]
  change c • (seedLaw D.L.ι).restrict s =
    (seedLaw D.L.ι).withDensity
      (c • s.indicator (fun _ => (1 : ℝ≥0∞)))
  calc
    c • (seedLaw D.L.ι).restrict s =
        c • (seedLaw D.L.ι).withDensity
          (s.indicator (fun _ => (1 : ℝ≥0∞))) :=
      congrArg (fun μ : Measure (D.L.ι → ℝ) => c • μ)
        (withDensity_indicator_one hs).symm
    _ = (seedLaw D.L.ι).withDensity
        (c • s.indicator (fun _ => (1 : ℝ≥0∞))) :=
      (withDensity_smul c (measurable_one.indicator hs)).symm

private lemma balance_withDensity_finset_sum
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (ν : Measure Ω) (f : ι → Ω → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    ν.withDensity (fun x => ∑ i, f i x) =
      ∑ i, ν.withDensity (f i) := by
  ext s hs
  rw [Measure.finsetSum_apply]
  simp_rw [withDensity_apply _ hs]
  exact lintegral_finsetSum Finset.univ fun i _ => hf i

private lemma balance_seedContextMarginal_eq_withDensity {p : α × β → ℝ}
    (D : SeedSetup p) (a l₀ : D.L.ι) :
    seedContextMarginal D a l₀ =
      (seedLaw D.L.ι).withDensity (balanceDensity D l₀ a) := by
  unfold seedContextMarginal
  calc
    (∑ z, ENNReal.ofReal
        (seedContextJoint D a l₀ z / seedContextMass D a l₀) •
          seedLawGivenWinner D a z) =
        ∑ z, ENNReal.ofReal
          (D.L.comp l₀ z / resamplePrior D l₀ a) •
            (seedLaw D.L.ι).restrict {ε | lexWinner D ε z = a} := by
      apply Finset.sum_congr rfl
      intro z _
      exact balance_context_mixture_term D a l₀ z
    _ = ∑ z, (seedLaw D.L.ι).withDensity
          (balanceTermDensity D l₀ a z) := by
      apply Finset.sum_congr rfl
      intro z _
      exact balance_term_measure_eq_withDensity D l₀ a z
    _ = (seedLaw D.L.ι).withDensity
          (fun ε => ∑ z, balanceTermDensity D l₀ a z ε) := by
      exact (balance_withDensity_finset_sum (seedLaw D.L.ι)
        (balanceTermDensity D l₀ a)
        (fun z => balanceTermDensity_measurable D l₀ a z)).symm
    _ = (seedLaw D.L.ι).withDensity (balanceDensity D l₀ a) := by
      congr 1
      funext ε
      exact (balanceDensity_eq_sum_terms D l₀ a ε).symm

private lemma balance_contextMarginal_klDiv_eq_integral {p : α × β → ℝ}
    (D : SeedSetup p) (a l₀ : D.L.ι) :
    (klDiv (seedContextMarginal D a l₀) (seedLaw D.L.ι)).toReal =
      ∫ ε, klFun (balanceDensityReal D l₀ a ε) ∂(seedLaw D.L.ι) := by
  let M : Measure (D.L.ι → ℝ) := seedContextMarginal D a l₀
  let Q : Measure (D.L.ι → ℝ) := seedLaw D.L.ι
  letI : IsProbabilityMeasure M := by
    dsimp only [M]
    exact seedContextMarginal_isProbability D a l₀
  letI : IsProbabilityMeasure Q := by
    dsimp only [Q]
    infer_instance
  have hM : M = Q.withDensity (balanceDensity D l₀ a) := by
    dsimp only [M, Q]
    exact balance_seedContextMarginal_eq_withDensity D a l₀
  have hac : M ≪ Q := by
    rw [hM]
    exact withDensity_absolutelyContinuous Q _
  have hrn : M.rnDeriv Q =ᵐ[Q] balanceDensity D l₀ a := by
    rw [hM]
    exact Measure.rnDeriv_withDensity Q (balanceDensity_measurable D l₀ a)
  rw [toReal_klDiv_eq_integral_klFun hac]
  apply integral_congr_ae
  filter_upwards [hrn] with ε hε
  rw [hε]
  unfold balanceDensity
  rw [ENNReal.toReal_ofReal (balanceDensityReal_nonneg D l₀ a ε)]

private lemma balance_contextMarginal_weighted_KL {p : α × β → ℝ}
    (D : SeedSetup p) (a l₀ : D.L.ι) :
    seedContextMass D a l₀ *
        (klDiv (seedContextMarginal D a l₀) (seedLaw D.L.ι)).toReal =
      D.L.prior l₀ *
        ((∫ ε, balanceWinnerProb D (lexWinner D ε) l₀ a *
            Real.log (balanceWinnerProb D (lexWinner D ε) l₀ a)
              ∂(seedLaw D.L.ι)) -
          resamplePrior D l₀ a * Real.log (resamplePrior D l₀ a)) := by
  let r : ℝ := resamplePrior D l₀ a
  let f : (D.L.ι → ℝ) → ℝ := fun ε =>
    balanceWinnerProb D (lexWinner D ε) l₀ a
  have hr : 0 < r := balance_resamplePrior_pos D l₀ a
  have hg : Integrable (fun ε => klFun (f ε / r)) (seedLaw D.L.ι) := by
    simpa only [f, r] using balance_integrable_lex_code D
      (fun A => klFun (balanceWinnerProb D A l₀ a /
        resamplePrior D l₀ a))
  have hflogf : Integrable (fun ε => f ε * Real.log (f ε))
      (seedLaw D.L.ι) := by
    simpa only [f] using balance_integrable_lex_code D
      (fun A => balanceWinnerProb D A l₀ a *
        Real.log (balanceWinnerProb D A l₀ a))
  have hflogr : Integrable (fun ε => f ε * Real.log r)
      (seedLaw D.L.ι) := by
    simpa only [f, r] using balance_integrable_lex_code D
      (fun A => balanceWinnerProb D A l₀ a *
        Real.log (resamplePrior D l₀ a))
  have hf : Integrable f (seedLaw D.L.ι) := by
    simpa only [f] using balance_integrable_lex_code D
      (fun A => balanceWinnerProb D A l₀ a)
  have hpoint (ε : D.L.ι → ℝ) :
      r * klFun (f ε / r) =
        f ε * Real.log (f ε) - f ε * Real.log r + r - f ε := by
    by_cases hf0 : f ε = 0
    · simp [hf0, klFun]
    · rw [klFun, Real.log_div hf0 hr.ne']
      field_simp [hr.ne']
      <;> ring
  rw [balance_seedContextMass_eq D a l₀,
    balance_contextMarginal_klDiv_eq_integral D a l₀]
  dsimp only [balanceDensityReal]
  rw [mul_assoc]
  apply congrArg (fun x : ℝ => D.L.prior l₀ * x)
  change r * (∫ ε, klFun (f ε / r) ∂(seedLaw D.L.ι)) = _
  calc
    r * (∫ ε, klFun (f ε / r) ∂(seedLaw D.L.ι)) =
        ∫ ε, r * klFun (f ε / r) ∂(seedLaw D.L.ι) := by
      rw [integral_const_mul]
    _ = ∫ ε, (f ε * Real.log (f ε) - f ε * Real.log r + r - f ε)
        ∂(seedLaw D.L.ι) := by
      exact integral_congr_ae (ae_of_all _ hpoint)
    _ = (∫ ε, f ε * Real.log (f ε) ∂(seedLaw D.L.ι)) -
        (∫ ε, f ε * Real.log r ∂(seedLaw D.L.ι)) + r -
        (∫ ε, f ε ∂(seedLaw D.L.ι)) := by
      calc
        _ = (∫ ε, f ε * Real.log (f ε) - f ε * Real.log r + r
              ∂(seedLaw D.L.ι)) -
            (∫ ε, f ε ∂(seedLaw D.L.ι)) := by
          exact integral_sub ((hflogf.sub hflogr).add (integrable_const r)) hf
        _ = ((∫ ε, f ε * Real.log (f ε) - f ε * Real.log r
                ∂(seedLaw D.L.ι)) +
              (∫ _ε, r ∂(seedLaw D.L.ι))) -
            (∫ ε, f ε ∂(seedLaw D.L.ι)) := by
          apply congrArg (fun x : ℝ => x - ∫ ε, f ε ∂(seedLaw D.L.ι))
          exact integral_add (hflogf.sub hflogr) (integrable_const r)
        _ = ((∫ ε, f ε * Real.log (f ε) - f ε * Real.log r
                ∂(seedLaw D.L.ι)) + r) -
            (∫ ε, f ε ∂(seedLaw D.L.ι)) := by
          simp
        _ = _ := by
          rw [integral_sub hflogf hflogr]
    _ = (∫ ε, f ε * Real.log (f ε) ∂(seedLaw D.L.ι)) -
        r * Real.log r := by
      rw [integral_mul_const, show (∫ ε, f ε ∂(seedLaw D.L.ι)) = r by
        simpa only [f, r] using balance_integral_winnerProb D l₀ a]
      ring

private lemma balanceWinnerProb_isPMF {p : α × β → ℝ}
    (D : SeedSetup p) (A : (α × β) → D.L.ι) (l₀ : D.L.ι) :
    IsPMF (balanceWinnerProb D A l₀) := by
  constructor
  · exact balanceWinnerProb_nonneg D A l₀
  · simpa only [mass] using balance_sum_winnerProb D A l₀

private lemma balance_resamplePrior_isPMF {p : α × β → ℝ}
    (D : SeedSetup p) (l₀ : D.L.ι) : IsPMF (resamplePrior D l₀) := by
  constructor
  · exact balance_resamplePrior_nonneg D l₀
  · simpa only [mass] using balance_sum_resamplePrior D l₀

private lemma balance_H_eq_neg_sum_mul_log
    {X : Type*} [Fintype X] (q : X → ℝ) (hq : IsPMF q) :
    Real.log 2 * H q = -∑ x, q x * Real.log (q x) := by
  unfold H
  rw [hq.total, Finset.mul_sum]
  calc
    (∑ x, Real.log 2 * (q x * lg (1 / q x))) =
        ∑ x, -(q x * Real.log (q x)) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [lg_eq_log_div, one_div, Real.log_inv]
      field_simp [(Real.log_pos one_lt_two).ne']
    _ = -∑ x, q x * Real.log (q x) := by
      rw [Finset.sum_neg_distrib]

private lemma balance_sum_integral_winnerProb_mul_log {p : α × β → ℝ}
    (D : SeedSetup p) (l₀ : D.L.ι) :
    (∑ a, ∫ ε, balanceWinnerProb D (lexWinner D ε) l₀ a *
        Real.log (balanceWinnerProb D (lexWinner D ε) l₀ a)
          ∂(seedLaw D.L.ι)) =
      (-Real.log 2) *
        (∫ ε, H (balanceWinnerProb D (lexWinner D ε) l₀)
          ∂(seedLaw D.L.ι)) := by
  have hterm (a : D.L.ι) : Integrable
      (fun ε => balanceWinnerProb D (lexWinner D ε) l₀ a *
        Real.log (balanceWinnerProb D (lexWinner D ε) l₀ a))
      (seedLaw D.L.ι) := by
    simpa using balance_integrable_lex_code D
      (fun A => balanceWinnerProb D A l₀ a *
        Real.log (balanceWinnerProb D A l₀ a))
  calc
    (∑ a, ∫ ε, balanceWinnerProb D (lexWinner D ε) l₀ a *
        Real.log (balanceWinnerProb D (lexWinner D ε) l₀ a)
          ∂(seedLaw D.L.ι)) =
        ∫ ε, ∑ a, balanceWinnerProb D (lexWinner D ε) l₀ a *
          Real.log (balanceWinnerProb D (lexWinner D ε) l₀ a)
            ∂(seedLaw D.L.ι) := by
      rw [integral_finsetSum Finset.univ]
      exact fun a _ => hterm a
    _ = ∫ ε, (-Real.log 2) *
          H (balanceWinnerProb D (lexWinner D ε) l₀)
            ∂(seedLaw D.L.ι) := by
      apply integral_congr_ae
      filter_upwards [] with ε
      have hH := balance_H_eq_neg_sum_mul_log
        (balanceWinnerProb D (lexWinner D ε) l₀)
        (balanceWinnerProb_isPMF D (lexWinner D ε) l₀)
      linarith
    _ = _ := by rw [integral_const_mul]

private lemma balance_marginalCost_per_label {p : α × β → ℝ}
    (D : SeedSetup p) (l₀ : D.L.ι) :
    (∑ a, seedContextMass D a l₀ *
        (klDiv (seedContextMarginal D a l₀)
          (seedLaw D.L.ι)).toReal) =
      Real.log 2 * D.L.prior l₀ *
        (H (resamplePrior D l₀) -
          ∫ ε, H (balanceWinnerProb D (lexWinner D ε) l₀)
            ∂(seedLaw D.L.ι)) := by
  have hresample := balance_H_eq_neg_sum_mul_log
    (resamplePrior D l₀) (balance_resamplePrior_isPMF D l₀)
  have hsum :
      (∑ a, resamplePrior D l₀ a * Real.log (resamplePrior D l₀ a)) =
        -Real.log 2 * H (resamplePrior D l₀) := by
    linarith
  calc
    (∑ a, seedContextMass D a l₀ *
        (klDiv (seedContextMarginal D a l₀)
          (seedLaw D.L.ι)).toReal) =
        ∑ a, D.L.prior l₀ *
          ((∫ ε, balanceWinnerProb D (lexWinner D ε) l₀ a *
              Real.log (balanceWinnerProb D (lexWinner D ε) l₀ a)
                ∂(seedLaw D.L.ι)) -
            resamplePrior D l₀ a * Real.log (resamplePrior D l₀ a)) := by
      apply Finset.sum_congr rfl
      intro a _
      exact balance_contextMarginal_weighted_KL D a l₀
    _ = D.L.prior l₀ *
        ((∑ a, ∫ ε, balanceWinnerProb D (lexWinner D ε) l₀ a *
            Real.log (balanceWinnerProb D (lexWinner D ε) l₀ a)
              ∂(seedLaw D.L.ι)) -
          ∑ a, resamplePrior D l₀ a * Real.log (resamplePrior D l₀ a)) := by
      rw [← Finset.mul_sum, Finset.sum_sub_distrib]
    _ = _ := by
      rw [balance_sum_integral_winnerProb_mul_log D l₀, hsum]
      ring

private lemma balance_marginalCost_eq_entropy_sums {p : α × β → ℝ}
    (D : SeedSetup p) :
    balanceMarginalCostNats D =
      Real.log 2 *
        ((∑ l₀, D.L.prior l₀ * H (resamplePrior D l₀)) -
          ∑ l₀, D.L.prior l₀ *
            (∫ ε, H (balanceWinnerProb D (lexWinner D ε) l₀)
              ∂(seedLaw D.L.ι))) := by
  unfold balanceMarginalCostNats
  calc
    (∑ a, ∑ l₀, seedContextMass D a l₀ *
        (klDiv (seedContextMarginal D a l₀)
          (seedLaw D.L.ι)).toReal) =
        ∑ l₀, ∑ a, seedContextMass D a l₀ *
          (klDiv (seedContextMarginal D a l₀)
            (seedLaw D.L.ι)).toReal := Finset.sum_comm
    _ = ∑ l₀, Real.log 2 * D.L.prior l₀ *
        (H (resamplePrior D l₀) -
          ∫ ε, H (balanceWinnerProb D (lexWinner D ε) l₀)
            ∂(seedLaw D.L.ι)) := by
      apply Finset.sum_congr rfl
      intro l₀ _
      exact balance_marginalCost_per_label D l₀
    _ = _ := by
      rw [mul_sub, Finset.mul_sum, Finset.mul_sum,
        ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro l₀ _
      ring

private lemma balance_push_winner_fiber {p : α × β → ℝ}
    (D : SeedSetup p) (A : (α × β) → D.L.ι) (l₀ : D.L.ι) :
    push (fun q : D.L.ι × (α × β) => A q.2)
        (fun q => if q.1 = l₀ then D.L.joint q else 0) =
      fun a => D.L.prior l₀ * balanceWinnerProb D A l₀ a := by
  funext a
  unfold push balanceWinnerProb Latent.joint
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  simp only [Prod.fst, Prod.snd]
  rw [Finset.mul_sum]
  change (∑ l, ∑ z,
      if A z = a then
        if l = l₀ then D.L.prior l * D.L.comp l z else 0
      else 0) =
    ∑ z, D.L.prior l₀ * (if A z = a then D.L.comp l₀ z else 0)
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z _
  by_cases hz : A z = a
  · simp [hz]
  · simp [hz]

private lemma balance_winner_condH_eq_entropy_sum {p : α × β → ℝ}
    (D : SeedSetup p) (A : (α × β) → D.L.ι) :
    condH (fun q : D.L.ι × (α × β) => A q.2) Prod.fst
        D.L.joint =
      ∑ l₀, D.L.prior l₀ * H (balanceWinnerProb D A l₀) := by
  rw [condH_eq_sum_H_fibers D.L.joint_isPMF]
  simp_rw [balance_push_winner_fiber D A]
  apply Finset.sum_congr rfl
  intro l₀ _
  exact H_smul (balanceWinnerProb_isPMF D A l₀).isFinMeas
    (D.L.prior_isPMF.nonneg l₀)

private lemma balance_raceWinnerEntropy_eq_entropy_sum {p : α × β → ℝ}
    (D : SeedSetup p) :
    raceWinnerEntropy D =
      ∑ l₀, D.L.prior l₀ *
        (∫ ε, H (balanceWinnerProb D (lexWinner D ε) l₀)
          ∂(seedLaw D.L.ι)) := by
  have hterm (l₀ : D.L.ι) : Integrable
      (fun ε => D.L.prior l₀ *
        H (balanceWinnerProb D (lexWinner D ε) l₀))
      (seedLaw D.L.ι) := by
    simpa using balance_integrable_lex_code D
      (fun A => D.L.prior l₀ * H (balanceWinnerProb D A l₀))
  unfold raceWinnerEntropy
  calc
    (∫ ε, condH (fun w => winner D ε w.2) Prod.fst D.L.joint
        ∂(seedLaw D.L.ι)) =
        ∫ ε, ∑ l₀, D.L.prior l₀ *
          H (balanceWinnerProb D (lexWinner D ε) l₀)
            ∂(seedLaw D.L.ι) := by
      apply integral_congr_ae
      filter_upwards [winner_ae_eq_lexWinner D] with ε hε
      rw [balance_winner_condH_eq_entropy_sum D (winner D ε), hε]
    _ = ∑ l₀, ∫ ε, D.L.prior l₀ *
          H (balanceWinnerProb D (lexWinner D ε) l₀)
            ∂(seedLaw D.L.ι) := by
      rw [integral_finsetSum Finset.univ]
      exact fun l₀ _ => hterm l₀
    _ = _ := by
      apply Finset.sum_congr rfl
      intro l₀ _
      rw [integral_const_mul]

private lemma balance_sum_replica_l₂ {p : α × β → ℝ}
    (D : SeedSetup p) (l₀ l₁ : D.L.ι) (z : α × β) :
    (∑ l₂, replicaLaw D (l₀, l₁, l₂, z)) =
      p z * D.post l₀ z * D.post l₁ z := by
  by_cases hpz : p z = 0
  · simp [replicaLaw, hpz]
  · have hpost := sum_post_of_pos D z
      (lt_of_le_of_ne (D.isPMF.nonneg z) (Ne.symm hpz))
    change (∑ l₂, p z * D.post l₀ z * D.post l₁ z * D.post l₂ z) =
      p z * D.post l₀ z * D.post l₁ z
    rw [← Finset.mul_sum, hpost, mul_one]

private lemma balance_sum_replica_domain {p : α × β → ℝ}
    (D : SeedSetup p)
    (F : D.L.ι × D.L.ι × D.L.ι × (α × β) → ℝ) :
    (∑ u, F u) = ∑ l₀, ∑ l₁, ∑ l₂, ∑ z, F (l₀, l₁, l₂, z) := by
  calc
    (∑ u, F u) = ∑ l₀, ∑ u : D.L.ι × D.L.ι × (α × β), F (l₀, u) := by
      rw [Fintype.sum_prod_type]
    _ = ∑ l₀, ∑ l₁, ∑ u : D.L.ι × (α × β), F (l₀, l₁, u) := by
      apply Finset.sum_congr rfl
      intro l₀ _
      rw [Fintype.sum_prod_type]
    _ = ∑ l₀, ∑ l₁, ∑ l₂, ∑ z, F (l₀, l₁, l₂, z) := by
      apply Finset.sum_congr rfl
      intro l₀ _
      apply Finset.sum_congr rfl
      intro l₁ _
      rw [Fintype.sum_prod_type]

private lemma balance_push_replica_l₁_fiber {p : α × β → ℝ}
    (D : SeedSetup p) (a : D.L.ι) :
    push (fun u : D.L.ι × D.L.ι × D.L.ι × (α × β) => u.1)
        (fun u => if u.2.1 = a then replicaLaw D u else 0) =
      fun b => D.L.prior a * resamplePrior D a b := by
  funext b
  unfold push
  rw [Finset.sum_filter, balance_sum_replica_domain D]
  change (∑ l₀, ∑ l₁, ∑ l₂, ∑ z,
      if l₀ = b then
        if l₁ = a then replicaLaw D (l₀, l₁, l₂, z) else 0
      else 0) = _
  have hcollapse :
      (∑ l₀, ∑ l₁, ∑ l₂, ∑ z,
        if l₀ = b then
          if l₁ = a then replicaLaw D (l₀, l₁, l₂, z) else 0
        else 0) =
      ∑ l₂, ∑ z, replicaLaw D (b, a, l₂, z) := by
    calc
      _ = ∑ l₁, ∑ l₂, ∑ z,
          if b = b then
            if l₁ = a then replicaLaw D (b, l₁, l₂, z) else 0
          else 0 := by
        apply Fintype.sum_eq_single b
        intro l₀ hl₀
        simp [hl₀]
      _ = ∑ l₁, ∑ l₂, ∑ z,
          if l₁ = a then replicaLaw D (b, l₁, l₂, z) else 0 := by simp
      _ = ∑ l₂, ∑ z,
          if a = a then replicaLaw D (b, a, l₂, z) else 0 := by
        apply Fintype.sum_eq_single a
        intro l₁ hl₁
        simp [hl₁]
      _ = ∑ l₂, ∑ z, replicaLaw D (b, a, l₂, z) := by simp
  rw [hcollapse, Finset.sum_comm]
  simp_rw [balance_sum_replica_l₂ D]
  unfold resamplePrior
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  calc
    p z * D.post b z * D.post a z =
        (p z * D.post a z) * D.post b z := by ring
    _ = (D.L.prior a * D.L.comp a z) * D.post b z := by
      rw [balance_p_mul_post D a z]
    _ = D.L.prior a * (D.L.comp a z * D.post b z) := by ring

private lemma balance_replica_condH_eq_resampleEntropies {p : α × β → ℝ}
    (D : SeedSetup p) :
    condH
        (fun u : D.L.ι × D.L.ι × D.L.ι × (α × β) => u.1)
        (fun u => u.2.1) (replicaLaw D) =
      ∑ a, D.L.prior a * H (resamplePrior D a) := by
  rw [condH_eq_sum_H_fibers (replicaLaw_isPMF D)]
  simp_rw [balance_push_replica_l₁_fiber D]
  apply Finset.sum_congr rfl
  intro a _
  exact H_smul (balance_resamplePrior_isPMF D a).isFinMeas
    (D.L.prior_isPMF.nonneg a)

private lemma balance_marginalCost_eq_condH_sub {p : α × β → ℝ}
    (D : SeedSetup p) :
    balanceMarginalCostNats D =
      Real.log 2 *
        (condH
            (fun u : D.L.ι × D.L.ι × D.L.ι × (α × β) => u.1)
            (fun u => u.2.1) (replicaLaw D) -
          raceWinnerEntropy D) := by
  rw [balance_marginalCost_eq_entropy_sums D,
    balance_replica_condH_eq_resampleEntropies D,
    balance_raceWinnerEntropy_eq_entropy_sum D]

/-- Lemma 7.3 before quotienting: winner calibration and the entropy chain
rule give `H(A|ε,L₀)=I(L₁;Z|L₀)+I(ε;Z|A,L₀)`. -/
private theorem raceSeedLeak_entropy_balance {p : α × β → ℝ}
    (D : SeedSetup p) :
    raceSeedLeak D = raceWinnerEntropy D +
        condH (fun q : D.L.ι × (α × β) => q.1) (fun q => q.2)
          D.L.joint -
        condH
          (fun u : D.L.ι × D.L.ι × D.L.ι × (α × β) => u.1)
          (fun u => u.2.1) (replicaLaw D) := by
  rw [balance_raceSeedLeak_decomp D,
    balance_restrictionCost_eq_condH D,
    balance_marginalCost_eq_condH_sub D]
  field_simp [(Real.log_pos one_lt_two).ne']
  ring

private theorem label_winner_entropy_identity {p : α × β → ℝ}
    (D : SeedSetup p) :
    raceWinnerEntropy D = bZ D + raceSeedLeak D := by
  rw [bZ_eq_condH_sub D, raceSeedLeak_entropy_balance D]
  ring

private theorem race_winner_entropy_identity {p : α × β → ℝ}
    (D : SeedSetup p) (K : Clustering D) :
    raceWinnerEntropy D = K.Sinfo + raceSeedLeak D := by
  rw [label_winner_entropy_identity D, K.Sinfo_eq_bZ]

/-! ### Theorem 8.1: the scalar channel -/

/-- The information in one positive `(g,b)` context, in nats. -/
private noncomputable def scalarContextInfoNats {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D) (g b : K.κ) : ℝ :=
  ∑ z, scalarSource K g b z *
    (klDiv (K.clockLawGiven b z) (scalarClockMarginal K g b)).toReal

/-- `C_{gb}=D(ν_{gb} ‖ Q_g)` in nats. -/
private noncomputable def scalarSourceKLNats {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D) (g b : K.κ) : ℝ :=
  ∑ z, scalarSource K g b z *
    Real.log (scalarSource K g b z / K.Q g z)

private theorem scalarWinnerProb_pos {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D) (g b : K.κ) :
    0 < scalarWinnerProb K g b := by
  have hsum : (∑ z, K.Q g z) ≠ 0 := by
    have htotal : ∑ z, K.Q g z = 1 := by
      simpa [mass] using (K.Q_isContact g).1.total
    rw [htotal]
    norm_num
  obtain ⟨z, _, hQz⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum
  have hQpos : 0 < K.Q g z :=
    lt_of_le_of_ne ((K.Q_isContact g).1.nonneg z) (Ne.symm hQz)
  have hz : z ∈ support p := by
    by_contra hz
    exact hQz ((K.Q_isContact g).2.1 z hz)
  unfold scalarWinnerProb
  apply Finset.sum_pos'
  · intro z _
    exact mul_nonneg ((K.Q_isContact g).1.nonneg z)
      (raceSigma_nonneg K b z)
  · exact ⟨z, Finset.mem_univ z, mul_pos hQpos (K.sigma_pos b z hz)⟩

private theorem scalarContextMass_pos {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D) (g b : K.κ) :
    0 < scalarContextMass K g b := by
  exact mul_pos (clusterMass_pos K g) (scalarWinnerProb_pos K g b)

private theorem scalarSource_isPMF {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D) (g b : K.κ) :
    IsPMF (scalarSource K g b) := by
  have hP := scalarWinnerProb_pos K g b
  constructor
  · intro z
    unfold scalarSource
    exact div_nonneg
      (mul_nonneg ((K.Q_isContact g).1.nonneg z)
        (raceSigma_nonneg K b z)) hP.le
  · unfold mass scalarSource
    rw [← Finset.sum_div]
    change scalarWinnerProb K g b / scalarWinnerProb K g b = 1
    exact div_self hP.ne'

private theorem sum_scalarWinnerProb {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D) (g : K.κ) :
    ∑ b, scalarWinnerProb K g b = 1 := by
  unfold scalarWinnerProb
  rw [Finset.sum_comm]
  calc
    (∑ z, ∑ b, K.Q g z * K.sigma b z) =
        ∑ z, K.Q g z * ∑ b, K.sigma b z := by
      apply Finset.sum_congr rfl
      intro z _
      rw [Finset.mul_sum]
    _ = ∑ z, K.Q g z := by
      apply Finset.sum_congr rfl
      intro z _
      by_cases hz : z ∈ support p
      · rw [raceSigma_sum_eq_one K z hz, mul_one]
      · have hQ : K.Q g z = 0 := (K.Q_isContact g).2.1 z hz
        simp [hQ]
    _ = 1 := by simpa [mass] using (K.Q_isContact g).1.total

private theorem scalarSourceKLNats_nonneg {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D) (g b : K.κ) :
    0 ≤ scalarSourceKLNats K g b := by
  unfold scalarSourceKLNats
  apply gibbs_nonneg (scalarSource_isPMF K g b) (K.Q_isContact g).1
  intro z hz hQ
  exact hz (by simp [scalarSource, hQ])

private lemma MI_mul_log_two_eq_log_sum
    {A Γ Δ : Type*} [Fintype A] [Fintype Γ] [Fintype Δ]
    [DecidableEq Γ] [DecidableEq Δ]
    {m : A → ℝ} (hm : IsPMF m) (f : A → Γ) (g : A → Δ) :
    Real.log 2 * MI f g m =
      ∑ z, push (fun a => (f a, g a)) m z *
        Real.log
          (push (fun a => (f a, g a)) m z /
            (push f m z.1 * push g m z.2)) := by
  let r : Γ × Δ → ℝ := push (fun a => (f a, g a)) m
  let rx : Γ → ℝ := push Prod.fst r
  let ry : Δ → ℝ := push Prod.snd r
  let s : Γ × Δ → ℝ := fun z => rx z.1 * ry z.2
  have hr : IsPMF r := isPMF_push hm
  have hrx : IsPMF rx := isPMF_push hr
  have hry : IsPMF ry := isPMF_push hr
  have hsupp : ∀ z, r z ≠ 0 → s z ≠ 0 := by
    intro z hz
    have hrpos : 0 < r z := lt_of_le_of_ne (hr.nonneg z) (Ne.symm hz)
    have hxle : r z ≤ rx z.1 := by
      dsimp [rx]
      unfold push
      exact Finset.single_le_sum (fun w _ => hr.nonneg w) (by simp)
    have hyle : r z ≤ ry z.2 := by
      dsimp [ry]
      unfold push
      exact Finset.single_le_sum (fun w _ => hr.nonneg w) (by simp)
    dsimp [s]
    exact mul_ne_zero (lt_of_lt_of_le hrpos hxle).ne'
      (lt_of_lt_of_le hrpos hyle).ne'
  have hrx_eq : rx = push f m := by
    dsimp [rx, r]
    simpa [Function.comp_def] using
      (push_push (fun a => (f a, g a)) Prod.fst m)
  have hry_eq : ry = push g m := by
    dsimp [ry, r]
    simpa [Function.comp_def] using
      (push_push (fun a => (f a, g a)) Prod.snd m)
  have hMIent : MI f g m = H rx + H ry - H r := by
    unfold MI Hvar
    rw [hrx_eq, hry_eq]
  have hliftx : ∑ x, Real.negMulLog (rx x) =
      ∑ z, r z * (-Real.log (rx z.1)) := by
    calc
      (∑ x, Real.negMulLog (rx x)) =
          ∑ x, rx x * (-Real.log (rx x)) := by
        apply Finset.sum_congr rfl
        intro x _
        rw [Real.negMulLog]
        ring
      _ = ∑ z, r z * (-Real.log (rx z.1)) :=
        sum_push_mul Prod.fst r _
  have hlifty : ∑ y, Real.negMulLog (ry y) =
      ∑ z, r z * (-Real.log (ry z.2)) := by
    calc
      (∑ y, Real.negMulLog (ry y)) =
          ∑ y, ry y * (-Real.log (ry y)) := by
        apply Finset.sum_congr rfl
        intro y _
        rw [Real.negMulLog]
        ring
      _ = ∑ z, r z * (-Real.log (ry z.2)) :=
        sum_push_mul Prod.snd r _
  have hliftr : ∑ z, Real.negMulLog (r z) =
      ∑ z, r z * (-Real.log (r z)) := by
    apply Finset.sum_congr rfl
    intro z _
    rw [Real.negMulLog]
    ring
  have hEntropyKL :
      (∑ x, Real.negMulLog (rx x)) + (∑ y, Real.negMulLog (ry y)) -
          ∑ z, Real.negMulLog (r z) =
        ∑ z, r z * Real.log (r z / s z) := by
    rw [hliftx, hlifty, hliftr, ← Finset.sum_add_distrib,
      ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro z _
    by_cases hz : r z = 0
    · simp [hz]
    · have hsz := hsupp z hz
      dsimp [s] at hsz ⊢
      have hx0 : rx z.1 ≠ 0 := (mul_ne_zero_iff.mp hsz).1
      have hy0 : ry z.2 ≠ 0 := (mul_ne_zero_iff.mp hsz).2
      rw [Real.log_div hz hsz, Real.log_mul hx0 hy0]
      ring
  have hEr := H_eq_negMulLog hr.isFinMeas
  have hErx := H_eq_negMulLog hrx.isFinMeas
  have hEry := H_eq_negMulLog hry.isFinMeas
  rw [hr.total, Real.log_one, mul_zero, zero_add] at hEr
  rw [hrx.total, Real.log_one, mul_zero, zero_add] at hErx
  rw [hry.total, Real.log_one, mul_zero, zero_add] at hEry
  calc
    Real.log 2 * MI f g m = Real.log 2 * (H rx + H ry - H r) := by
      rw [hMIent]
    _ = Real.log 2 * H rx + Real.log 2 * H ry - Real.log 2 * H r := by
      ring
    _ = (∑ x, Real.negMulLog (rx x)) +
        (∑ y, Real.negMulLog (ry y)) -
          ∑ z, Real.negMulLog (r z) := by rw [hErx, hEry, hEr]
    _ = ∑ z, r z * Real.log (r z / s z) := hEntropyKL
    _ = ∑ z, push (fun a => (f a, g a)) m z *
        Real.log
          (push (fun a => (f a, g a)) m z /
            (push f m z.1 * push g m z.2)) := by
      dsimp only [s]
      rw [hrx_eq, hry_eq]

private lemma scalar_condMI_eq_sum_MI_fibers
    {A Γ Δ E : Type*} [Fintype A] [Fintype Γ] [Fintype Δ]
    [Fintype E] [DecidableEq Γ] [DecidableEq Δ] [DecidableEq E]
    {m : A → ℝ} (hm : IsPMF m) (f : A → Γ) (g : A → Δ)
    (h : A → E) :
    condMI f g h m =
      ∑ e, MI f g (fun a => if h a = e then m a else 0) := by
  let mh : E → A → ℝ := fun e a => if h a = e then m a else 0
  have hF := Hvar_pair_eq_sum_fibers hm f h
  have hG := Hvar_pair_eq_sum_fibers hm g h
  have hFG := Hvar_pair_eq_sum_fibers hm (fun a => (f a, g a)) h
  change Hvar (fun a => (f a, h a)) m = Hvar h m +
    ∑ e, H (push f (mh e)) at hF
  change Hvar (fun a => (g a, h a)) m = Hvar h m +
    ∑ e, H (push g (mh e)) at hG
  change Hvar (fun a => ((f a, g a), h a)) m = Hvar h m +
    ∑ e, H (push (fun a => (f a, g a)) (mh e)) at hFG
  have hAssoc : Hvar (fun a => (f a, g a, h a)) m =
      Hvar (fun a => ((f a, g a), h a)) m := by
    simpa using Hvar_equiv hm (fun a => ((f a, g a), h a))
      (Equiv.prodAssoc Γ Δ E)
  unfold condMI
  rw [hF, hG, hAssoc, hFG]
  simp only [MI, Hvar, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  ring

private lemma race_push_id
    {A : Type*} [Fintype A] [DecidableEq A] (m : A → ℝ) :
    push (fun a => a) m = m := by
  funext a
  unfold push
  apply Finset.sum_eq_single a
  · intro b hb hba
    exact (hba (Finset.mem_filter.mp hb).2).elim
  · intro ha
    exact (ha (by simp)).elim

private lemma race_MI_eq_joint_push
    {A Γ Δ : Type*} [Fintype A] [Fintype Γ] [Fintype Δ]
    [DecidableEq Γ] [DecidableEq Δ]
    (m : A → ℝ) (f : A → Γ) (g : A → Δ) :
    MI f g m =
      MI Prod.fst Prod.snd (push (fun a => (f a, g a)) m) := by
  unfold MI Hvar
  rw [push_push, push_push, race_push_id]
  rfl

/-- The explicit conditional law of `(B,Z)` given `C₀=g`. -/
private noncomputable def scalarPosteriorJoint {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D) (g : K.κ) :
    K.κ × (α × β) → ℝ :=
  fun bz => K.Q g bz.2 * K.sigma bz.1 bz.2

private lemma scalarPosteriorJoint_isPMF {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D) (g : K.κ) :
    IsPMF (scalarPosteriorJoint K g) := by
  constructor
  · intro bz
    exact mul_nonneg ((K.Q_isContact g).1.nonneg bz.2)
      (raceSigma_nonneg K bz.1 bz.2)
  · unfold mass scalarPosteriorJoint
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    calc
      (∑ z, ∑ b, K.Q g z * K.sigma b z) = ∑ z, K.Q g z := by
        apply Finset.sum_congr rfl
        intro z _
        by_cases hz : z ∈ support p
        · rw [← Finset.mul_sum, raceSigma_sum_eq_one K z hz, mul_one]
        · have hQ : K.Q g z = 0 := (K.Q_isContact g).2.1 z hz
          simp [hQ]
      _ = 1 := by simpa [mass] using (K.Q_isContact g).1.total

private lemma push_scalarPosteriorJoint_fst {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D) (g : K.κ) :
    push Prod.fst (scalarPosteriorJoint K g) = scalarWinnerProb K g := by
  funext b
  unfold push scalarPosteriorJoint scalarWinnerProb
  simp_rw [Finset.sum_filter]
  rw [Fintype.sum_prod_type]
  simp

private lemma push_scalarPosteriorJoint_snd {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D) (g : K.κ) :
    push Prod.snd (scalarPosteriorJoint K g) = K.Q g := by
  funext z
  unfold push scalarPosteriorJoint
  simp_rw [Finset.sum_filter]
  change (∑ bz : K.κ × (α × β),
    if bz.2 = z then K.Q g bz.2 * K.sigma bz.1 bz.2 else 0) = K.Q g z
  rw [show (∑ bz : K.κ × (α × β),
      if bz.2 = z then K.Q g bz.2 * K.sigma bz.1 bz.2 else 0) =
      ∑ b, ∑ z', if z' = z then K.Q g z' * K.sigma b z' else 0 by
        exact Fintype.sum_prod_type _]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  by_cases hz : z ∈ support p
  · rw [← Finset.mul_sum, raceSigma_sum_eq_one K z hz, mul_one]
  · have hQ : K.Q g z = 0 := (K.Q_isContact g).2.1 z hz
    simp [hQ]

private lemma push_replica_cluster_fiber_pair {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D) (g : K.κ) :
    push
        (fun u : D.L.ι × D.L.ι × D.L.ι × (α × β) =>
          (K.cl u.2.1, u.2.2.2))
        (fun u => if K.cl u.1 = g then replicaLaw D u else 0) =
      fun bz => K.s g * scalarPosteriorJoint K g bz := by
  funext bz
  rcases bz with ⟨b, z⟩
  unfold push
  rw [Finset.sum_filter]
  rw [Fintype.sum_prod_type_right, Fintype.sum_prod_type_right,
    Fintype.sum_prod_type_right]
  unfold replicaLaw scalarPosteriorJoint
  change
    (∑ z', ∑ ℓ₂, ∑ ℓ₁, ∑ ℓ₀,
      if (K.cl ℓ₁, z') = (b, z) then
        (if K.cl ℓ₀ = g then
          p z' * D.post ℓ₀ z' * D.post ℓ₁ z' * D.post ℓ₂ z' else 0)
      else 0) = K.s g * (K.Q g z * K.sigma b z)
  calc
    (∑ z', ∑ ℓ₂, ∑ ℓ₁, ∑ ℓ₀,
      if (K.cl ℓ₁, z') = (b, z) then
        (if K.cl ℓ₀ = g then
          p z' * D.post ℓ₀ z' * D.post ℓ₁ z' * D.post ℓ₂ z' else 0)
      else 0) =
        ∑ z', if z' = z then
          (∑ ℓ₂, ∑ ℓ₁, ∑ ℓ₀,
            if K.cl ℓ₁ = b then
              (if K.cl ℓ₀ = g then
                p z' * D.post ℓ₀ z' * D.post ℓ₁ z' * D.post ℓ₂ z'
              else 0)
            else 0)
          else 0 := by
            apply Finset.sum_congr rfl
            intro z' _
            by_cases hz' : z' = z <;> simp [Prod.mk.injEq, hz']
    _ = ∑ ℓ₂, ∑ ℓ₁, ∑ ℓ₀,
          if K.cl ℓ₁ = b then
            (if K.cl ℓ₀ = g then
              p z * D.post ℓ₀ z * D.post ℓ₁ z * D.post ℓ₂ z else 0)
          else 0 := by
            rw [Fintype.sum_ite_eq']
    _ = K.s g * (K.Q g z * K.sigma b z) := by
      by_cases hp : p z = 0
      · have hz : z ∉ support p := by simp [support, hp]
        have hQ : K.Q g z = 0 := (K.Q_isContact g).2.1 z hz
        simp [hp, hQ]
      · have hpPos : 0 < p z :=
          lt_of_le_of_ne (D.isPMF.nonneg z) (Ne.symm hp)
        have hsum₂ (ℓ₀ ℓ₁ : D.L.ι) :
            (∑ ℓ₂, p z * D.post ℓ₀ z * D.post ℓ₁ z * D.post ℓ₂ z) =
              p z * D.post ℓ₀ z * D.post ℓ₁ z := by
          calc
            (∑ ℓ₂, p z * D.post ℓ₀ z * D.post ℓ₁ z * D.post ℓ₂ z) =
                (p z * D.post ℓ₀ z * D.post ℓ₁ z) *
                  (∑ ℓ₂, D.post ℓ₂ z) := by rw [Finset.mul_sum]
            _ = _ := by rw [sum_post_of_pos D z hpPos, mul_one]
        have hsource (ℓ₁ : D.L.ι) :
            (∑ ℓ₀, if K.cl ℓ₀ = g then
              p z * D.post ℓ₀ z * D.post ℓ₁ z else 0) =
                K.s g * K.Q g z * D.post ℓ₁ z := by
          calc
            (∑ ℓ₀, if K.cl ℓ₀ = g then
              p z * D.post ℓ₀ z * D.post ℓ₁ z else 0) =
                (∑ ℓ₀, if K.cl ℓ₀ = g then
                  p z * D.post ℓ₀ z else 0) * D.post ℓ₁ z := by
                    rw [Finset.sum_mul]
                    apply Finset.sum_congr rfl
                    intro ℓ₀ _
                    by_cases hℓ₀ : K.cl ℓ₀ = g <;> simp [hℓ₀]
            _ = p z * K.sigma g z * D.post ℓ₁ z := by
              congr 1
              unfold Clustering.sigma
              rw [Finset.mul_sum, Finset.sum_filter]
            _ = K.s g * K.Q g z * D.post ℓ₁ z := by
              rw [← clusterWeight_eq_pSigma K g z]
        calc
          (∑ ℓ₂, ∑ ℓ₁, ∑ ℓ₀,
            if K.cl ℓ₁ = b then
              (if K.cl ℓ₀ = g then
                p z * D.post ℓ₀ z * D.post ℓ₁ z * D.post ℓ₂ z else 0)
            else 0) =
              ∑ ℓ₁, ∑ ℓ₀, ∑ ℓ₂,
                if K.cl ℓ₁ = b then
                  (if K.cl ℓ₀ = g then
                    p z * D.post ℓ₀ z * D.post ℓ₁ z * D.post ℓ₂ z else 0)
                  else 0 := by
                    rw [Finset.sum_comm]
                    apply Finset.sum_congr rfl
                    intro ℓ₁ _
                    exact Finset.sum_comm
          _ = ∑ ℓ₁, if K.cl ℓ₁ = b then
                (∑ ℓ₀, if K.cl ℓ₀ = g then
                  p z * D.post ℓ₀ z * D.post ℓ₁ z else 0)
              else 0 := by
                apply Finset.sum_congr rfl
                intro ℓ₁ _
                by_cases h₁ : K.cl ℓ₁ = b
                · simp only [h₁, if_true]
                  apply Finset.sum_congr rfl
                  intro ℓ₀ _
                  by_cases h₀ : K.cl ℓ₀ = g
                  · simp only [h₀, if_true]
                    exact hsum₂ ℓ₀ ℓ₁
                  · simp [h₀]
                · simp [h₁]
          _ = ∑ ℓ₁, if K.cl ℓ₁ = b then
                K.s g * K.Q g z * D.post ℓ₁ z else 0 := by
                apply Finset.sum_congr rfl
                intro ℓ₁ _
                by_cases h₁ : K.cl ℓ₁ = b <;> simp [h₁, hsource ℓ₁]
          _ = (K.s g * K.Q g z) *
                (∑ ℓ ∈ univ.filter (fun ℓ => K.cl ℓ = b), D.post ℓ z) := by
                rw [Finset.mul_sum, Finset.sum_filter]
          _ = K.s g * (K.Q g z * K.sigma b z) := by
                unfold Clustering.sigma
                ring

private lemma Sinfo_eq_scalarPosterior_MI {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D) :
    K.Sinfo = ∑ g, K.s g *
      MI Prod.fst Prod.snd (scalarPosteriorJoint K g) := by
  unfold Clustering.Sinfo
  rw [scalar_condMI_eq_sum_MI_fibers (replicaLaw_isPMF D)]
  apply Finset.sum_congr rfl
  intro g _
  let fiber : D.L.ι × D.L.ι × D.L.ι × (α × β) → ℝ :=
    fun u => if K.cl u.1 = g then replicaLaw D u else 0
  calc
    MI (fun u : D.L.ι × D.L.ι × D.L.ι × (α × β) => K.cl u.2.1)
        (fun u => u.2.2.2) fiber =
        MI Prod.fst Prod.snd
          (push (fun u : D.L.ι × D.L.ι × D.L.ι × (α × β) =>
            (K.cl u.2.1, u.2.2.2)) fiber) :=
      race_MI_eq_joint_push fiber (fun u => K.cl u.2.1) (fun u => u.2.2.2)
    _ = MI Prod.fst Prod.snd
        (fun bz => K.s g * scalarPosteriorJoint K g bz) := by
      rw [show fiber =
        (fun u => if K.cl u.1 = g then replicaLaw D u else 0) by rfl,
        push_replica_cluster_fiber_pair K g]
    _ = K.s g * MI Prod.fst Prod.snd (scalarPosteriorJoint K g) := by
      exact MI_smul (scalarPosteriorJoint_isPMF K g).isFinMeas
        Prod.fst Prod.snd (clusterMass_nonneg K g)

private lemma scalarSource_weighted_eq_MI_nats {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D) (g : K.κ) :
    (∑ b, scalarWinnerProb K g b * scalarSourceKLNats K g b) =
      Real.log 2 * MI Prod.fst Prod.snd (scalarPosteriorJoint K g) := by
  have hjointPush :
      push (fun bz : K.κ × (α × β) => (bz.1, bz.2))
          (scalarPosteriorJoint K g) = scalarPosteriorJoint K g := by
    simpa only using race_push_id (scalarPosteriorJoint K g)
  have hMI := MI_mul_log_two_eq_log_sum
    (scalarPosteriorJoint_isPMF K g) (@Prod.fst K.κ (α × β))
      (@Prod.snd K.κ (α × β))
  rw [hjointPush, push_scalarPosteriorJoint_fst K g,
    push_scalarPosteriorJoint_snd K g] at hMI
  have hMI' :
      Real.log 2 * MI Prod.fst Prod.snd (scalarPosteriorJoint K g) =
        ∑ b, ∑ z, scalarPosteriorJoint K g (b, z) *
          Real.log
            (scalarPosteriorJoint K g (b, z) /
              (scalarWinnerProb K g b * K.Q g z)) := by
    calc
      Real.log 2 * MI Prod.fst Prod.snd (scalarPosteriorJoint K g) =
          ∑ bz, scalarPosteriorJoint K g bz *
            Real.log
              (scalarPosteriorJoint K g bz /
                (scalarWinnerProb K g bz.1 * K.Q g bz.2)) := hMI
      _ = _ := Fintype.sum_prod_type _
  have hterm (b : K.κ) (z : α × β) :
      scalarWinnerProb K g b *
          (scalarSource K g b z *
            Real.log (scalarSource K g b z / K.Q g z)) =
        scalarPosteriorJoint K g (b, z) *
          Real.log
            (scalarPosteriorJoint K g (b, z) /
              (scalarWinnerProb K g b * K.Q g z)) := by
    unfold scalarSource scalarPosteriorJoint
    have hP : scalarWinnerProb K g b ≠ 0 :=
      (scalarWinnerProb_pos K g b).ne'
    by_cases hQ : K.Q g z = 0
    · simp [hQ]
    · have hcoeff :
          scalarWinnerProb K g b *
              (K.Q g z * K.sigma b z / scalarWinnerProb K g b) =
            K.Q g z * K.sigma b z := by
          field_simp
      have harg :
          (K.Q g z * K.sigma b z / scalarWinnerProb K g b) / K.Q g z =
            (K.Q g z * K.sigma b z) /
              (scalarWinnerProb K g b * K.Q g z) := by
          field_simp
      rw [← mul_assoc, hcoeff, harg]
  calc
    (∑ b, scalarWinnerProb K g b * scalarSourceKLNats K g b) =
        ∑ b, ∑ z, scalarWinnerProb K g b *
          (scalarSource K g b z *
            Real.log (scalarSource K g b z / K.Q g z)) := by
      unfold scalarSourceKLNats
      apply Finset.sum_congr rfl
      intro b _
      rw [Finset.mul_sum]
    _ = ∑ b, ∑ z, scalarPosteriorJoint K g (b, z) *
          Real.log
            (scalarPosteriorJoint K g (b, z) /
              (scalarWinnerProb K g b * K.Q g z)) := by
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.sum_congr rfl
      intro z _
      exact hterm b z
    _ = Real.log 2 * MI Prod.fst Prod.snd (scalarPosteriorJoint K g) :=
      hMI'.symm

private noncomputable def scalarLogExpDensity (n : ℝ) : ℝ :=
  Real.exp (n - Real.exp n)

private lemma integrableOn_abs_log_mul_exp_neg_Ioi :
    IntegrableOn (fun t : ℝ => |Real.log t| * Real.exp (-t)) (Set.Ioi 0) := by
  let f : ℝ → ℝ := fun t => |Real.log t| * Real.exp (-t)
  have hf_meas : StronglyMeasurable f := by
    dsimp [f]
    exact ((continuous_abs.measurable.comp Real.measurable_log).mul
      (Real.measurable_exp.comp measurable_id.neg)).stronglyMeasurable
  have hneglog_int : IntegrableOn (fun t : ℝ => -Real.log t) (Set.Ioc 0 1) := by
    have hlog_int : IntegrableOn Real.log (Set.Ioc (0 : ℝ) 1) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1
        intervalIntegral.intervalIntegrable_log'
    exact hlog_int.neg
  have hlow_point (t : ℝ) (ht : t ∈ Set.Ioc (0 : ℝ) 1) :
      f t ≤ -Real.log t := by
    have hlog : Real.log t ≤ 0 := Real.log_nonpos ht.1.le ht.2
    have hexp : Real.exp (-t) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by linarith [ht.1])
    dsimp [f]
    rw [abs_of_nonpos hlog]
    exact mul_le_of_le_one_right (neg_nonneg.mpr hlog) hexp
  have hf_low : IntegrableOn f (Set.Ioc (0 : ℝ) 1) := by
    refine Integrable.mono_nonneg hneglog_int
      hf_meas.aestronglyMeasurable.restrict
      (ae_of_all _ fun t => mul_nonneg (abs_nonneg _) (Real.exp_nonneg _)) ?_
    rw [ae_restrict_iff' measurableSet_Ioc]
    exact ae_of_all _ hlow_point
  have hderiv (t : ℝ) :
      HasDerivAt (fun x : ℝ => -x * Real.exp (-x))
        ((t - 1) * Real.exp (-t)) t := by
    have hraw := (hasDerivAt_id t).neg.mul (hasDerivAt_id t).neg.exp
    refine (hraw.congr_of_eventuallyEq ?_).congr_deriv ?_
    · filter_upwards with x
      rfl
    · simp
      ring
  have htop : Filter.Tendsto (fun t : ℝ => -t * Real.exp (-t))
      Filter.atTop (nhds 0) := by
    simpa [pow_one] using
      (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).neg
  have hmajor_high : IntegrableOn
      (fun t : ℝ => (t - 1) * Real.exp (-t)) (Set.Ioi 1) := by
    exact integrableOn_Ioi_deriv_of_nonneg'
      (a := (1 : ℝ)) (l := (0 : ℝ))
      (g := fun t : ℝ => -t * Real.exp (-t))
      (g' := fun t : ℝ => (t - 1) * Real.exp (-t))
      (fun t _ => hderiv t)
      (fun t ht => mul_nonneg (sub_nonneg.mpr ht.le)
        (Real.exp_nonneg _)) htop
  have hhigh_point (t : ℝ) (ht : t ∈ Set.Ioi (1 : ℝ)) :
      f t ≤ (t - 1) * Real.exp (-t) := by
    have htpos : 0 < t := zero_lt_one.trans ht
    have hlog_nonneg : 0 ≤ Real.log t := Real.log_nonneg ht.le
    have hlog_le : Real.log t ≤ t - 1 :=
      Real.log_le_sub_one_of_pos htpos
    dsimp [f]
    rw [abs_of_nonneg hlog_nonneg]
    exact mul_le_mul_of_nonneg_right hlog_le (Real.exp_nonneg _)
  have hf_high : IntegrableOn f (Set.Ioi (1 : ℝ)) := by
    refine Integrable.mono_nonneg hmajor_high
      hf_meas.aestronglyMeasurable.restrict
      (ae_of_all _ fun t => mul_nonneg (abs_nonneg _) (Real.exp_nonneg _)) ?_
    rw [ae_restrict_iff' measurableSet_Ioi]
    exact ae_of_all _ hhigh_point
  rw [← Set.Ioc_union_Ioi_eq_Ioi zero_le_one]
  exact hf_low.union hf_high

private lemma scalarLogExpDensity_integrable : Integrable scalarLogExpDensity := by
  have hg : IntegrableOn (fun t : ℝ => Real.exp (-t)) (Set.Ioi 0) := by
    simpa only [show (1 : ℝ) - 1 = 0 by norm_num, Real.rpow_zero, mul_one]
      using (Real.GammaIntegral_convergent (s := (1 : ℝ)) (by norm_num))
  have hchange :=
    (integrableOn_image_iff_integrableOn_abs_deriv_smul
      (s := Set.univ) (f := Real.exp) (f' := Real.exp)
      MeasurableSet.univ
      (fun n _ => (Real.hasDerivAt_exp n).hasDerivWithinAt)
      (fun _ _ _ _ hxy => Real.exp_injective hxy)
      (fun t : ℝ => Real.exp (-t))).mp (by
        rw [Set.image_univ, Real.range_exp]
        exact hg)
  have hchange' : Integrable
      (fun n : ℝ => Real.exp n * Real.exp (-Real.exp n)) := by
    simpa only [IntegrableOn, Measure.restrict_univ,
      abs_of_pos (Real.exp_pos _), smul_eq_mul] using hchange
  change Integrable (fun n : ℝ => Real.exp (n - Real.exp n))
  convert hchange' using 1
  funext n
  rw [← Real.exp_add]
  simp only [sub_eq_add_neg]

private lemma scalarLogExpDensity_integral_eq_one :
    ∫ n : ℝ, scalarLogExpDensity n = 1 := by
  have hchange := integral_image_eq_integral_abs_deriv_smul
    (s := Set.univ) (f := Real.exp) (f' := Real.exp) MeasurableSet.univ
    (fun n _ => (Real.hasDerivAt_exp n).hasDerivWithinAt)
    (fun _ _ _ _ hxy => Real.exp_injective hxy)
    (fun t : ℝ => Real.exp (-t))
  rw [Set.image_univ, Real.range_exp] at hchange
  have hchange' : (∫ t : ℝ in Set.Ioi 0, Real.exp (-t)) =
      ∫ n : ℝ, Real.exp n * Real.exp (-Real.exp n) := by
    simpa only [Measure.restrict_univ, abs_of_pos (Real.exp_pos _),
      smul_eq_mul] using hchange
  have hvalue : ∫ t : ℝ in Set.Ioi 0, Real.exp (-t) = 1 := by
    simpa using (Real.integral_rpow_mul_exp_neg_mul_Ioi
      (a := (1 : ℝ)) (r := (1 : ℝ)) (by norm_num) (by norm_num))
  calc
    (∫ n : ℝ, scalarLogExpDensity n) =
        ∫ n : ℝ, Real.exp n * Real.exp (-Real.exp n) := by
      apply integral_congr_ae
      filter_upwards with n
      simp only [scalarLogExpDensity]
      rw [← Real.exp_add]
      simp only [sub_eq_add_neg]
    _ = ∫ t : ℝ in Set.Ioi 0, Real.exp (-t) := hchange'.symm
    _ = 1 := hvalue

private lemma scalarLogExpDensity_abs_integrable :
    Integrable (fun n : ℝ => |n| * scalarLogExpDensity n) := by
  have hchange :=
    (integrableOn_image_iff_integrableOn_abs_deriv_smul
      (s := Set.univ) (f := Real.exp) (f' := Real.exp)
      MeasurableSet.univ
      (fun n _ => (Real.hasDerivAt_exp n).hasDerivWithinAt)
      (fun _ _ _ _ hxy => Real.exp_injective hxy)
      (fun t : ℝ => |Real.log t| * Real.exp (-t))).mp (by
        rw [Set.image_univ, Real.range_exp]
        exact integrableOn_abs_log_mul_exp_neg_Ioi)
  have hchange' : Integrable
      (fun n : ℝ => Real.exp n *
        (|Real.log (Real.exp n)| * Real.exp (-Real.exp n))) := by
    simpa only [IntegrableOn, Measure.restrict_univ,
      abs_of_pos (Real.exp_pos _), smul_eq_mul] using hchange
  change Integrable (fun n : ℝ => |n| * Real.exp (n - Real.exp n))
  convert hchange' using 1
  funext n
  simp only [Real.log_exp]
  rw [show Real.exp n * (|n| * Real.exp (-Real.exp n)) =
      |n| * (Real.exp n * Real.exp (-Real.exp n)) by ring,
    ← Real.exp_add]
  simp only [sub_eq_add_neg]

private lemma scalarLogExpDensity_abs_integral_le :
    (∫ n : ℝ, |n| * scalarLogExpDensity n) ≤ 2 := by
  have hchange := integral_image_eq_integral_abs_deriv_smul
    (s := Set.univ) (f := Real.exp) (f' := Real.exp) MeasurableSet.univ
    (fun n _ => (Real.hasDerivAt_exp n).hasDerivWithinAt)
    (fun _ _ _ _ hxy => Real.exp_injective hxy)
    (fun t : ℝ => |Real.log t| * Real.exp (-t))
  rw [Set.image_univ, Real.range_exp] at hchange
  have hchange' :
      (∫ t : ℝ in Set.Ioi 0, |Real.log t| * Real.exp (-t)) =
        ∫ n : ℝ, Real.exp n *
          (|Real.log (Real.exp n)| * Real.exp (-Real.exp n)) := by
    simpa only [Measure.restrict_univ, abs_of_pos (Real.exp_pos _),
      smul_eq_mul] using hchange
  calc
    (∫ n : ℝ, |n| * scalarLogExpDensity n) =
        ∫ n : ℝ, Real.exp n *
          (|Real.log (Real.exp n)| * Real.exp (-Real.exp n)) := by
      apply integral_congr_ae
      filter_upwards with n
      simp only [Real.log_exp, scalarLogExpDensity]
      rw [show Real.exp n * (|n| * Real.exp (-Real.exp n)) =
          |n| * (Real.exp n * Real.exp (-Real.exp n)) by ring,
        ← Real.exp_add]
      simp only [sub_eq_add_neg]
    _ = ∫ t : ℝ in Set.Ioi 0, |Real.log t| * Real.exp (-t) :=
      hchange'.symm
    _ ≤ 2 := abs_log_exp_integral_le

private lemma scalarLogExpDensity_abs_integral_eq_1771 :
    (∫ n : ℝ, |n| * scalarLogExpDensity n) = logExpAbsMoment := by
  have hchange := integral_image_eq_integral_abs_deriv_smul
    (s := Set.univ) (f := Real.exp) (f' := Real.exp) MeasurableSet.univ
    (fun n _ => (Real.hasDerivAt_exp n).hasDerivWithinAt)
    (fun _ _ _ _ hxy => Real.exp_injective hxy)
    (fun t : ℝ => |Real.log t| * Real.exp (-t))
  rw [Set.image_univ, Real.range_exp] at hchange
  have hchange' :
      (∫ t : ℝ in Set.Ioi 0, |Real.log t| * Real.exp (-t)) =
        ∫ n : ℝ, Real.exp n *
          (|Real.log (Real.exp n)| * Real.exp (-Real.exp n)) := by
    simpa only [Measure.restrict_univ, abs_of_pos (Real.exp_pos _),
      smul_eq_mul] using hchange
  calc
    (∫ n : ℝ, |n| * scalarLogExpDensity n) =
        ∫ n : ℝ, Real.exp n *
          (|Real.log (Real.exp n)| * Real.exp (-Real.exp n)) := by
      apply integral_congr_ae
      filter_upwards with n
      simp only [Real.log_exp, scalarLogExpDensity]
      rw [show Real.exp n * (|n| * Real.exp (-Real.exp n)) =
          |n| * (Real.exp n * Real.exp (-Real.exp n)) by ring,
        ← Real.exp_add]
      simp only [sub_eq_add_neg]
    _ = ∫ t : ℝ in Set.Ioi 0, |Real.log t| * Real.exp (-t) :=
      hchange'.symm
    _ = logExpAbsMoment := rfl

private lemma scalarLogExpDensity_entropy_integrable :
    Integrable (fun n : ℝ => Real.negMulLog (scalarLogExpDensity n)) := by
  have hfirst : Integrable
      (fun n : ℝ => Real.exp n * scalarLogExpDensity n) := by
    have hg : IntegrableOn (fun t : ℝ => t * Real.exp (-t)) (Set.Ioi 0) := by
      simpa only [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one, mul_comm]
        using (Real.GammaIntegral_convergent (s := (2 : ℝ)) (by norm_num))
    have hchange :=
      (integrableOn_image_iff_integrableOn_abs_deriv_smul
        (s := Set.univ) (f := Real.exp) (f' := Real.exp)
        MeasurableSet.univ
        (fun n _ => (Real.hasDerivAt_exp n).hasDerivWithinAt)
        (fun _ _ _ _ hxy => Real.exp_injective hxy)
        (fun t : ℝ => t * Real.exp (-t))).mp (by
          rw [Set.image_univ, Real.range_exp]
          exact hg)
    have hchange' : Integrable
        (fun n : ℝ => Real.exp n *
          (Real.exp n * Real.exp (-Real.exp n))) := by
      simpa only [IntegrableOn, Measure.restrict_univ,
        abs_of_pos (Real.exp_pos _), smul_eq_mul] using hchange
    change Integrable
      (fun n : ℝ => Real.exp n * Real.exp (n - Real.exp n))
    convert hchange' using 1
    funext n
    rw [show n - Real.exp n = n + -Real.exp n by ring, Real.exp_add]
  have hsecond : Integrable
      (fun n : ℝ => n * scalarLogExpDensity n) := by
    refine scalarLogExpDensity_abs_integrable.mono' ?_ ?_
    · change AEStronglyMeasurable
        (fun n : ℝ => n * Real.exp (n - Real.exp n))
      fun_prop
    filter_upwards with n
    change ‖n * Real.exp (n - Real.exp n)‖ ≤
      |n| * Real.exp (n - Real.exp n)
    rw [Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (Real.exp_nonneg _)]
  refine (hfirst.sub hsecond).congr (ae_of_all _ fun n => ?_)
  change Real.exp n * Real.exp (n - Real.exp n) -
      n * Real.exp (n - Real.exp n) =
    Real.negMulLog (Real.exp (n - Real.exp n))
  rw [Real.negMulLog, Real.log_exp]
  ring

private lemma scalarLogExpDensity_nonneg (n : ℝ) :
    0 ≤ scalarLogExpDensity n := Real.exp_nonneg _

private lemma scalarLogExpDensity_pos (n : ℝ) :
    0 < scalarLogExpDensity n := Real.exp_pos _

private lemma scalarShiftDensity_integrable (x : ℝ) :
    Integrable (fun w : ℝ => scalarLogExpDensity (w - x)) := by
  simpa only [sub_eq_add_neg] using
    scalarLogExpDensity_integrable.comp_add_right (-x)

private lemma scalarShiftDensity_integral_eq_one (x : ℝ) :
    ∫ w : ℝ, scalarLogExpDensity (w - x) = 1 := by
  calc
    (∫ w : ℝ, scalarLogExpDensity (w - x)) =
        ∫ n : ℝ, scalarLogExpDensity n := by
      simpa only [sub_eq_add_neg] using
        integral_add_right_eq_self scalarLogExpDensity (-x)
    _ = 1 := scalarLogExpDensity_integral_eq_one

private lemma scalarShiftDensity_entropy_integrable (x : ℝ) :
    Integrable
      (fun w : ℝ => Real.negMulLog (scalarLogExpDensity (w - x))) := by
  simpa only [sub_eq_add_neg] using
    scalarLogExpDensity_entropy_integrable.comp_add_right (-x)

private lemma scalarShiftDensity_entropy_integral (x : ℝ) :
    (∫ w : ℝ, Real.negMulLog (scalarLogExpDensity (w - x))) =
      diffEntropy scalarLogExpDensity := by
  unfold diffEntropy
  simpa only [sub_eq_add_neg] using
    integral_add_right_eq_self
      (fun n : ℝ => Real.negMulLog (scalarLogExpDensity n)) (-x)

private lemma scalarShiftDensity_abs_integrable (x : ℝ) :
    Integrable (fun w : ℝ => |w| * scalarLogExpDensity (w - x)) := by
  have hbase0 := scalarLogExpDensity_abs_integrable.add
    (scalarLogExpDensity_integrable.const_mul |x|)
  have hbase : Integrable
      (fun n : ℝ => (|n| + |x|) * scalarLogExpDensity n) := by
    refine hbase0.congr (ae_of_all _ fun n => ?_)
    simp only [Pi.add_apply]
    ring
  have hshift : Integrable
      (fun w : ℝ => (|w - x| + |x|) * scalarLogExpDensity (w - x)) := by
    simpa only [sub_eq_add_neg] using hbase.comp_add_right (-x)
  refine hshift.mono' ?_ ?_
  · change AEStronglyMeasurable
      (fun w : ℝ => |w| * Real.exp ((w - x) - Real.exp (w - x)))
    fun_prop
  filter_upwards with w
  rw [Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (scalarLogExpDensity_nonneg _)]
  exact mul_le_mul_of_nonneg_right
    (by
      simpa only [sub_add_cancel, abs_abs] using abs_add_le (w - x) x)
    (scalarLogExpDensity_nonneg _)

private lemma scalarShiftDensity_abs_integral_le (x : ℝ) :
    (∫ w : ℝ, |w| * scalarLogExpDensity (w - x)) ≤ |x| + 2 := by
  have hbase0 := scalarLogExpDensity_abs_integrable.add
    (scalarLogExpDensity_integrable.const_mul |x|)
  have hbase : Integrable
      (fun n : ℝ => (|n| + |x|) * scalarLogExpDensity n) := by
    refine hbase0.congr (ae_of_all _ fun n => ?_)
    simp only [Pi.add_apply]
    ring
  have hupper : Integrable
      (fun w : ℝ => (|w - x| + |x|) * scalarLogExpDensity (w - x)) := by
    simpa only [sub_eq_add_neg] using hbase.comp_add_right (-x)
  calc
    (∫ w : ℝ, |w| * scalarLogExpDensity (w - x)) ≤
        ∫ w : ℝ,
          (|w - x| + |x|) * scalarLogExpDensity (w - x) := by
      apply integral_mono (scalarShiftDensity_abs_integrable x) hupper
      intro w
      exact mul_le_mul_of_nonneg_right
        (by
          simpa only [sub_add_cancel] using abs_add_le (w - x) x)
        (scalarLogExpDensity_nonneg _)
    _ = (∫ n : ℝ,
          (|n| + |x|) * scalarLogExpDensity n) := by
      simpa only [sub_eq_add_neg] using
        integral_add_right_eq_self
          (fun n : ℝ => (|n| + |x|) * scalarLogExpDensity n) (-x)
    _ = (∫ n : ℝ, |n| * scalarLogExpDensity n) + |x| := by
      calc
        (∫ n : ℝ, (|n| + |x|) * scalarLogExpDensity n) =
            ∫ n : ℝ, |n| * scalarLogExpDensity n +
              |x| * scalarLogExpDensity n := by
          apply integral_congr_ae
          filter_upwards with n
          ring
        _ = (∫ n : ℝ, |n| * scalarLogExpDensity n) +
            ∫ n : ℝ, |x| * scalarLogExpDensity n := by
          exact integral_add scalarLogExpDensity_abs_integrable
            (scalarLogExpDensity_integrable.const_mul |x|)
        _ = (∫ n : ℝ, |n| * scalarLogExpDensity n) + |x| := by
          rw [integral_const_mul, scalarLogExpDensity_integral_eq_one, mul_one]
    _ ≤ |x| + 2 := by
      linarith [scalarLogExpDensity_abs_integral_le]

private lemma scalarShiftDensity_abs_integral_le_1771 (x : ℝ) :
    (∫ w : ℝ, |w| * scalarLogExpDensity (w - x)) ≤
      |x| + logExpAbsMoment := by
  have hbase0 := scalarLogExpDensity_abs_integrable.add
    (scalarLogExpDensity_integrable.const_mul |x|)
  have hbase : Integrable
      (fun n : ℝ => (|n| + |x|) * scalarLogExpDensity n) := by
    refine hbase0.congr (ae_of_all _ fun n => ?_)
    simp only [Pi.add_apply]
    ring
  have hupper : Integrable
      (fun w : ℝ => (|w - x| + |x|) * scalarLogExpDensity (w - x)) := by
    simpa only [sub_eq_add_neg] using hbase.comp_add_right (-x)
  calc
    (∫ w : ℝ, |w| * scalarLogExpDensity (w - x)) ≤
        ∫ w : ℝ,
          (|w - x| + |x|) * scalarLogExpDensity (w - x) := by
      apply integral_mono (scalarShiftDensity_abs_integrable x) hupper
      intro w
      exact mul_le_mul_of_nonneg_right
        (by simpa only [sub_add_cancel] using abs_add_le (w - x) x)
        (scalarLogExpDensity_nonneg _)
    _ = (∫ n : ℝ,
          (|n| + |x|) * scalarLogExpDensity n) := by
      simpa only [sub_eq_add_neg] using
        integral_add_right_eq_self
          (fun n : ℝ => (|n| + |x|) * scalarLogExpDensity n) (-x)
    _ = (∫ n : ℝ, |n| * scalarLogExpDensity n) + |x| := by
      calc
        (∫ n : ℝ, (|n| + |x|) * scalarLogExpDensity n) =
            ∫ n : ℝ, |n| * scalarLogExpDensity n +
              |x| * scalarLogExpDensity n := by
          apply integral_congr_ae
          filter_upwards with n
          ring
        _ = (∫ n : ℝ, |n| * scalarLogExpDensity n) +
            ∫ n : ℝ, |x| * scalarLogExpDensity n := by
          exact integral_add scalarLogExpDensity_abs_integrable
            (scalarLogExpDensity_integrable.const_mul |x|)
        _ = (∫ n : ℝ, |n| * scalarLogExpDensity n) + |x| := by
          rw [integral_const_mul, scalarLogExpDensity_integral_eq_one, mul_one]
    _ = |x| + logExpAbsMoment := by
      rw [scalarLogExpDensity_abs_integral_eq_1771]
      ring

private noncomputable def scalarDensityMeasure (f : ℝ → ℝ) : Measure ℝ :=
  volume.withDensity (fun x => ENNReal.ofReal (f x))

private noncomputable def scalarLogExpMeasure : Measure ℝ :=
  scalarDensityMeasure scalarLogExpDensity

private lemma scalarDensityMeasure_apply {f : ℝ → ℝ}
    (hf : Integrable f) (hnonneg : ∀ x, 0 ≤ f x)
    {s : Set ℝ} (hs : MeasurableSet s) :
    scalarDensityMeasure f s = ENNReal.ofReal (∫ x in s, f x) := by
  unfold scalarDensityMeasure
  calc
    (volume.withDensity (fun x => ENNReal.ofReal (f x))) s =
        ∫⁻ x in s, ENNReal.ofReal (f x) :=
      withDensity_apply _ hs
    _ = ENNReal.ofReal (∫ x in s, f x) :=
      (ofReal_integral_eq_lintegral_ofReal hf.integrableOn
        (ae_restrict_of_forall_mem hs fun x _ => hnonneg x)).symm

private lemma scalarLogExpMeasure_isProbability :
    IsProbabilityMeasure scalarLogExpMeasure := by
  constructor
  unfold scalarLogExpMeasure
  rw [scalarDensityMeasure_apply scalarLogExpDensity_integrable
    scalarLogExpDensity_nonneg MeasurableSet.univ,
    Measure.restrict_univ, scalarLogExpDensity_integral_eq_one]
  norm_num

private lemma scalarLogExpMeasure_eq_comap_exp :
    scalarLogExpMeasure = Measure.comap Real.exp (expMeasure 1) := by
  let hemb : MeasurableEmbedding Real.exp :=
    Real.isOpenEmbedding_exp.measurableEmbedding
  have hg : IntegrableOn (fun t : ℝ => Real.exp (-t)) (Set.Ioi 0) := by
    simpa only [show (1 : ℝ) - 1 = 0 by norm_num, Real.rpow_zero, mul_one]
      using (Real.GammaIntegral_convergent (s := (1 : ℝ)) (by norm_num))
  apply Measure.ext
  intro s hs
  rw [scalarLogExpMeasure, scalarDensityMeasure_apply
    scalarLogExpDensity_integrable scalarLogExpDensity_nonneg hs]
  have himage : Real.exp '' s ⊆ Set.Ioi (0 : ℝ) := by
    rintro t ⟨n, _, rfl⟩
    exact Real.exp_pos n
  have himageMeas : MeasurableSet (Real.exp '' s) :=
    hemb.measurableSet_image.2 hs
  have hpdfint : IntegrableOn (exponentialPDFReal 1) (Real.exp '' s) := by
    refine (hg.mono_set himage).congr_fun ?_ himageMeas
    intro t ht
    have htpos : 0 < t := himage ht
    unfold exponentialPDFReal gammaPDFReal
    rw [if_pos htpos.le]
    norm_num
  change ENNReal.ofReal (∫ n in s, scalarLogExpDensity n) =
    (volume.withDensity
      (fun t => ENNReal.ofReal (exponentialPDFReal 1 t))).comap Real.exp s
  rw [hemb.withDensity_ofReal_comap_apply_eq_integral_abs_deriv_mul
    hs (ae_of_all _ fun t _ => exponentialPDFReal_nonneg zero_lt_one t)
    hpdfint (fun n _ => (Real.hasDerivAt_exp n).hasDerivWithinAt)]
  congr 1
  apply setIntegral_congr_fun hs
  intro n _
  simp only [abs_of_pos (Real.exp_pos n), scalarLogExpDensity,
    exponentialPDFReal, gammaPDFReal, if_pos (Real.exp_pos n).le,
    one_div, Real.one_rpow, Real.Gamma_one, div_one, sub_self,
    Real.rpow_zero, mul_one, one_mul, neg_mul]
  rw [← Real.exp_add]
  congr 1

private lemma scalarLogExpMeasure_map_exp :
    Measure.map Real.exp scalarLogExpMeasure = expMeasure 1 := by
  let hemb : MeasurableEmbedding Real.exp :=
    Real.isOpenEmbedding_exp.measurableEmbedding
  rw [scalarLogExpMeasure_eq_comap_exp, hemb.map_comap]
  apply Measure.restrict_eq_self_of_ae_mem
  rw [ae_iff]
  change expMeasure 1 ((Set.range Real.exp)ᶜ) = 0
  rw [Real.range_exp]
  simpa only [Set.compl_Ioi] using expMeasure_one_Iic_zero

private lemma scalarLogExpMeasure_map_add (x : ℝ) :
    Measure.map (fun n : ℝ => x + n) scalarLogExpMeasure =
      scalarDensityMeasure (fun w => scalarLogExpDensity (w - x)) := by
  let e : ℝ ≃ᵐ ℝ := (Homeomorph.addRight x).symm.toMeasurableEquiv
  have he' : ∀ w, HasDerivAt e ((fun _ => 1) w) w :=
    fun w => (hasDerivAt_id w).sub_const x
  rw [show (fun n : ℝ => x + n) = (fun n => n + x) by
    funext n
    ring]
  change scalarLogExpMeasure.map e.symm =
    scalarDensityMeasure (fun w => scalarLogExpDensity (w - x))
  apply Measure.ext
  intro s hs
  rw [scalarDensityMeasure_apply (scalarShiftDensity_integrable x)
    (fun w => scalarLogExpDensity_nonneg _) hs]
  unfold scalarLogExpMeasure scalarDensityMeasure
  rw [e.withDensity_ofReal_map_symm_apply_eq_integral_abs_deriv_mul'
    hs he'
    (ae_of_all _ scalarLogExpDensity_nonneg)
    scalarLogExpDensity_integrable]
  simp [e, Homeomorph.addRight, ← sub_eq_add_neg]

private lemma map_mul_expMeasure_one {s : ℝ} (hs : 0 < s) :
    Measure.map (fun t : ℝ => s * t) (expMeasure 1) =
      expMeasure (1 / s) := by
  rw [← map_div_expMeasure hs,
    Measure.map_map (by fun_prop) (by fun_prop)]
  calc
    Measure.map ((fun t : ℝ => s * t) ∘ fun u => u / s)
        (expMeasure (1 / s)) =
        Measure.map id (expMeasure (1 / s)) := by
      apply Measure.map_congr
      filter_upwards with u
      dsimp only [Function.comp_apply, id_eq]
      field_simp [hs.ne']
    _ = expMeasure (1 / s) := Measure.map_id

private lemma map_log_div_expMeasure_eq_shiftDensity {s P : ℝ}
    (hs : 0 < s) (hP : 0 < P) :
    Measure.map (fun u : ℝ => Real.log (u / P)) (expMeasure (1 / s)) =
      scalarDensityMeasure
        (fun w => scalarLogExpDensity (w - Real.log (s / P))) := by
  calc
    Measure.map (fun u : ℝ => Real.log (u / P)) (expMeasure (1 / s)) =
        Measure.map (fun u : ℝ => Real.log (u / P))
          (Measure.map (fun t : ℝ => s * t) (expMeasure 1)) := by
      rw [map_mul_expMeasure_one hs]
    _ = Measure.map
          ((fun u : ℝ => Real.log (u / P)) ∘ fun t : ℝ => s * t)
          (expMeasure 1) := by
      rw [Measure.map_map (by fun_prop) (by fun_prop)]
    _ = Measure.map
          ((fun u : ℝ => Real.log (u / P)) ∘
            (fun t : ℝ => s * t) ∘ Real.exp)
          scalarLogExpMeasure := by
      rw [← scalarLogExpMeasure_map_exp,
        Measure.map_map (by fun_prop) (by fun_prop)]
      rfl
    _ = Measure.map (fun n : ℝ => Real.log (s / P) + n)
          scalarLogExpMeasure := by
      apply Measure.map_congr
      filter_upwards with n
      dsimp only [Function.comp_apply]
      rw [show s * Real.exp n / P = (s / P) * Real.exp n by ring,
        Real.log_mul (div_ne_zero hs.ne' hP.ne') (Real.exp_ne_zero n),
        Real.log_exp]
    _ = scalarDensityMeasure
          (fun w => scalarLogExpDensity (w - Real.log (s / P))) :=
      scalarLogExpMeasure_map_add (Real.log (s / P))

private lemma ae_pos_expMeasure {r : ℝ} (hr : 0 < r) :
    ∀ᵐ u ∂expMeasure r, 0 < u := by
  letI : IsProbabilityMeasure (expMeasure r) :=
    isProbabilityMeasure_expMeasure hr
  rw [ae_iff]
  rw [show {u : ℝ | ¬ 0 < u} = Set.Iic 0 by
    ext u
    simp]
  have hreal : (expMeasure r).real (Set.Iic 0) = 0 := by
    rw [← cdf_eq_real]
    simpa using cdf_expMeasure_eq hr 0
  exact (measureReal_eq_zero_iff).mp hreal

private lemma map_reconstruct_log_div {P : ℝ} (hP : 0 < P)
    (Pμ : Measure ℝ) (hμpos : ∀ᵐ u ∂Pμ, 0 < u) :
    Measure.map (fun w : ℝ => P * Real.exp w)
        (Measure.map (fun u : ℝ => Real.log (u / P)) Pμ) = Pμ := by
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  calc
    Measure.map
        ((fun w : ℝ => P * Real.exp w) ∘
          fun u : ℝ => Real.log (u / P)) Pμ =
        Measure.map id Pμ := by
      apply Measure.map_congr
      filter_upwards [hμpos] with u hu
      dsimp only [Function.comp_apply, id_eq]
      rw [Real.exp_log (div_pos hu hP)]
      field_simp [hP.ne']
    _ = Pμ := Measure.map_id

private lemma klDiv_map_log_div_eq {P : ℝ} (hP : 0 < P)
    (Pμ Mμ : Measure ℝ) [IsFiniteMeasure Pμ] [IsFiniteMeasure Mμ]
    (hPμpos : ∀ᵐ u ∂Pμ, 0 < u)
    (hMμpos : ∀ᵐ u ∂Mμ, 0 < u) :
    klDiv
        (Measure.map (fun u : ℝ => Real.log (u / P)) Pμ)
        (Measure.map (fun u : ℝ => Real.log (u / P)) Mμ) =
      klDiv Pμ Mμ := by
  apply le_antisymm
  · exact klDiv_map_le Pμ Mμ (by fun_prop)
  · have h := klDiv_map_le
      (Measure.map (fun u : ℝ => Real.log (u / P)) Pμ)
      (Measure.map (fun u : ℝ => Real.log (u / P)) Mμ)
      (show Measurable (fun w : ℝ => P * Real.exp w) by fun_prop)
    rw [map_reconstruct_log_div hP Pμ hPμpos,
      map_reconstruct_log_div hP Mμ hMμpos] at h
    exact h

private lemma ae_pos_finset_mixture { ι : Type* } [Fintype ι]
    (r : ι → ℝ) (P : ι → Measure ℝ)
    (hPpos : ∀ i, ∀ᵐ u ∂P i, 0 < u) :
    ∀ᵐ u ∂(∑ i, ENNReal.ofReal (r i) • P i), 0 < u := by
  rw [ae_iff, Measure.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro i _
  rw [Measure.smul_apply, smul_eq_mul, (ae_iff.mp (hPpos i)), mul_zero]

private noncomputable def scalarMixtureDensity { ι : Type* } [Fintype ι]
    (r X : ι → ℝ) (w : ℝ) : ℝ :=
  ∑ i, r i * scalarLogExpDensity (w - X i)

private lemma scalarMixtureDensity_nonneg { ι : Type* } [Fintype ι]
    {r X : ι → ℝ} (hr : IsPMF r) (w : ℝ) :
    0 ≤ scalarMixtureDensity r X w := by
  unfold scalarMixtureDensity
  exact Finset.sum_nonneg fun i _ =>
    mul_nonneg (hr.nonneg i) (scalarLogExpDensity_nonneg _)

private lemma scalarMixtureDensity_pos { ι : Type* } [Fintype ι]
    {r X : ι → ℝ} (hr : IsPMF r) (w : ℝ) :
    0 < scalarMixtureDensity r X w := by
  have hsum : (∑ i, r i) ≠ 0 := by
    have htotal : ∑ i, r i = 1 := by simpa [mass] using hr.total
    rw [htotal]
    norm_num
  obtain ⟨i, _, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum
  unfold scalarMixtureDensity
  apply Finset.sum_pos'
  · intro j _
    exact mul_nonneg (hr.nonneg j) (scalarLogExpDensity_nonneg _)
  · exact ⟨i, Finset.mem_univ i,
      mul_pos (lt_of_le_of_ne (hr.nonneg i) (Ne.symm hi))
        (scalarLogExpDensity_pos _)⟩

private lemma scalarMixtureDensity_integrable { ι : Type* } [Fintype ι]
    {r X : ι → ℝ} : Integrable (scalarMixtureDensity r X) := by
  unfold scalarMixtureDensity
  exact integrable_finsetSum Finset.univ fun i _ =>
    (scalarShiftDensity_integrable (X i)).const_mul (r i)

private lemma scalarMixtureDensity_integral_eq_one
    { ι : Type* } [Fintype ι] {r X : ι → ℝ} (hr : IsPMF r) :
    ∫ w : ℝ, scalarMixtureDensity r X w = 1 := by
  unfold scalarMixtureDensity
  rw [integral_finsetSum Finset.univ]
  · calc
      (∑ i, ∫ w : ℝ, r i * scalarLogExpDensity (w - X i)) =
          ∑ i, r i := by
        apply Finset.sum_congr rfl
        intro i _
        rw [integral_const_mul, scalarShiftDensity_integral_eq_one, mul_one]
      _ = 1 := by simpa [mass] using hr.total
  · intro i _
    exact (scalarShiftDensity_integrable (X i)).const_mul (r i)

private lemma scalarMixtureDensity_le_one
    { ι : Type* } [Fintype ι] {r X : ι → ℝ} (hr : IsPMF r) (w : ℝ) :
    scalarMixtureDensity r X w ≤ 1 := by
  unfold scalarMixtureDensity
  calc
    (∑ i, r i * scalarLogExpDensity (w - X i)) ≤ ∑ i, r i * 1 := by
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_left _ (hr.nonneg i)
      exact Real.exp_le_one_iff.mpr (by
        linarith [Real.add_one_le_exp (w - X i)])
    _ = 1 := by simpa [mass] using hr.total

private lemma scalarMixtureDensity_abs_integrable
    { ι : Type* } [Fintype ι] {r X : ι → ℝ} :
    Integrable (fun w : ℝ => |w| * scalarMixtureDensity r X w) := by
  have hsum : Integrable
      (fun w : ℝ => ∑ i, r i * (|w| * scalarLogExpDensity (w - X i))) := by
    exact integrable_finsetSum Finset.univ fun i _ =>
      (scalarShiftDensity_abs_integrable (X i)).const_mul (r i)
  refine hsum.congr (ae_of_all _ fun w => ?_)
  unfold scalarMixtureDensity
  change (∑ i, r i * (|w| * scalarLogExpDensity (w - X i))) =
    |w| * ∑ i, r i * scalarLogExpDensity (w - X i)
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

private lemma scalarMixtureDensity_abs_integral_le
    { ι : Type* } [Fintype ι] {r X : ι → ℝ} (hr : IsPMF r) :
    (∫ w : ℝ, |w| * scalarMixtureDensity r X w) ≤
      ∑ i, r i * (|X i| + 2) := by
  have heq : (fun w : ℝ => |w| * scalarMixtureDensity r X w) =
      fun w => ∑ i, r i * (|w| * scalarLogExpDensity (w - X i)) := by
    funext w
    unfold scalarMixtureDensity
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [heq, integral_finsetSum Finset.univ]
  · apply Finset.sum_le_sum
    intro i _
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left (scalarShiftDensity_abs_integral_le (X i))
      (hr.nonneg i)
  · intro i _
    exact (scalarShiftDensity_abs_integrable (X i)).const_mul (r i)

private lemma scalarMixtureDensity_abs_integral_le_1771
    { ι : Type* } [Fintype ι] {r X : ι → ℝ} (hr : IsPMF r) :
    (∫ w : ℝ, |w| * scalarMixtureDensity r X w) ≤
      ∑ i, r i * (|X i| + logExpAbsMoment) := by
  have heq : (fun w : ℝ => |w| * scalarMixtureDensity r X w) =
      fun w => ∑ i, r i * (|w| * scalarLogExpDensity (w - X i)) := by
    funext w
    unfold scalarMixtureDensity
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [heq, integral_finsetSum Finset.univ]
  · apply Finset.sum_le_sum
    intro i _
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left
      (scalarShiftDensity_abs_integral_le_1771 (X i)) (hr.nonneg i)
  · intro i _
    exact (scalarShiftDensity_abs_integrable (X i)).const_mul (r i)

private lemma negMulLog_finset_sum_le { ι : Type* } [Fintype ι]
    (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) :
    Real.negMulLog (∑ i, a i) ≤ ∑ i, Real.negMulLog (a i) := by
  rw [Real.negMulLog]
  calc
    (-∑ i, a i) * Real.log (∑ i, a i) =
        ∑ i, (-a i * Real.log (∑ j, a j)) := by
      rw [← Finset.sum_mul, Finset.sum_neg_distrib]
    _ ≤ ∑ i, Real.negMulLog (a i) := by
      apply Finset.sum_le_sum
      intro i _
      rw [Real.negMulLog]
      by_cases hi : a i = 0
      · simp [hi]
      · have hipos : 0 < a i := lt_of_le_of_ne (ha i) (Ne.symm hi)
        have hile : a i ≤ ∑ j, a j :=
          Finset.single_le_sum (fun j _ => ha j) (Finset.mem_univ i)
        have hlog := Real.log_le_log hipos hile
        nlinarith

private lemma scalarMixtureDensity_entropy_integrable
    { ι : Type* } [Fintype ι] {r X : ι → ℝ} (hr : IsPMF r) :
    Integrable (fun w : ℝ => Real.negMulLog (scalarMixtureDensity r X w)) := by
  have hterm (i : ι) : Integrable
      (fun w : ℝ => Real.negMulLog
        (r i * scalarLogExpDensity (w - X i))) := by
    have hfirst := (scalarShiftDensity_integrable (X i)).mul_const
      (Real.negMulLog (r i))
    have hsecond := (scalarShiftDensity_entropy_integrable (X i)).const_mul (r i)
    refine (hfirst.add hsecond).congr (ae_of_all _ fun w => ?_)
    change scalarLogExpDensity (w - X i) * Real.negMulLog (r i) +
        r i * Real.negMulLog (scalarLogExpDensity (w - X i)) =
      Real.negMulLog (r i * scalarLogExpDensity (w - X i))
    rw [Real.negMulLog_mul]
  have hmajor : Integrable
      (fun w : ℝ => ∑ i,
        Real.negMulLog (r i * scalarLogExpDensity (w - X i))) :=
    integrable_finsetSum Finset.univ fun i _ => hterm i
  refine Integrable.mono_nonneg hmajor ?_
    (ae_of_all _ fun w => Real.negMulLog_nonneg
      (scalarMixtureDensity_nonneg hr w) (scalarMixtureDensity_le_one hr w)) ?_
  · change AEStronglyMeasurable
      (fun w : ℝ => Real.negMulLog
        (∑ i, r i * Real.exp ((w - X i) - Real.exp (w - X i))))
    fun_prop
  · filter_upwards with w
    unfold scalarMixtureDensity
    exact negMulLog_finset_sum_le
      (fun i => r i * scalarLogExpDensity (w - X i))
      (fun i => mul_nonneg (hr.nonneg i) (scalarLogExpDensity_nonneg _))

private lemma scalarDensityMeasure_isProbability {f : ℝ → ℝ}
    (hf : Integrable f) (hnonneg : ∀ x, 0 ≤ f x)
    (htotal : ∫ x : ℝ, f x = 1) :
    IsProbabilityMeasure (scalarDensityMeasure f) := by
  constructor
  rw [scalarDensityMeasure_apply hf hnonneg MeasurableSet.univ,
    Measure.restrict_univ, htotal]
  norm_num

private lemma scalarDensityMeasure_finset_mixture
    { ι : Type* } [Fintype ι] {r X : ι → ℝ} (hr : IsPMF r) :
    scalarDensityMeasure (scalarMixtureDensity r X) =
      ∑ i, ENNReal.ofReal (r i) •
        scalarDensityMeasure (fun w => scalarLogExpDensity (w - X i)) := by
  apply Measure.ext
  intro s hs
  rw [scalarDensityMeasure_apply scalarMixtureDensity_integrable
    (scalarMixtureDensity_nonneg hr) hs, Measure.finsetSum_apply,
    show (∫ w in s, scalarMixtureDensity r X w) =
        ∑ i, ∫ w in s, r i * scalarLogExpDensity (w - X i) by
      unfold scalarMixtureDensity
      rw [integral_finsetSum Finset.univ]
      intro i _
      exact ((scalarShiftDensity_integrable (X i)).const_mul (r i)).integrableOn]
  rw [ENNReal.ofReal_sum_of_nonneg]
  · apply Finset.sum_congr rfl
    intro i _
    rw [Measure.smul_apply, smul_eq_mul,
      scalarDensityMeasure_apply (scalarShiftDensity_integrable (X i))
        (fun w => scalarLogExpDensity_nonneg _) hs,
      integral_const_mul, ← ENNReal.ofReal_mul (hr.nonneg i)]
  · intro i _
    exact integral_nonneg fun w =>
      mul_nonneg (hr.nonneg i) (scalarLogExpDensity_nonneg _)

private lemma scalarDensityMeasure_eq_withDensity_div
    {f g : ℝ → ℝ} (hf : Measurable f) (hg : Measurable g)
    (hfnonneg : ∀ x, 0 ≤ f x) (hgpos : ∀ x, 0 < g x) :
    scalarDensityMeasure f =
      (scalarDensityMeasure g).withDensity
        (fun x => ENNReal.ofReal (f x / g x)) := by
  have hgd : Measurable (fun x => ENNReal.ofReal (g x)) := hg.ennreal_ofReal
  have hratio : Measurable (fun x => ENNReal.ofReal (f x / g x)) :=
    (hf.div hg).ennreal_ofReal
  unfold scalarDensityMeasure
  calc
    volume.withDensity (fun x => ENNReal.ofReal (f x)) =
        volume.withDensity
          ((fun x => ENNReal.ofReal (g x)) *
            fun x => ENNReal.ofReal (f x / g x)) := by
      apply withDensity_congr_ae
      filter_upwards with x
      simp only [Pi.mul_apply]
      rw [← ENNReal.ofReal_mul (hgpos x).le]
      congr 1
      field_simp [(hgpos x).ne']
    _ = (volume.withDensity (fun x => ENNReal.ofReal (g x))).withDensity
          (fun x => ENNReal.ofReal (f x / g x)) :=
      withDensity_mul volume hgd hratio

private lemma scalarDensityMeasure_llr_ae
    {f g : ℝ → ℝ} (hf : Measurable f) (hg : Measurable g)
    (hfnonneg : ∀ x, 0 ≤ f x) (hfpos : ∀ x, 0 < f x)
    (hgpos : ∀ x, 0 < g x)
    [IsFiniteMeasure (scalarDensityMeasure f)]
    [IsFiniteMeasure (scalarDensityMeasure g)] :
    llr (scalarDensityMeasure f) (scalarDensityMeasure g) =ᵐ[
      scalarDensityMeasure f] fun x => Real.log (f x / g x) := by
  have hgd : Measurable (fun x => ENNReal.ofReal (g x)) := hg.ennreal_ofReal
  have hratio : Measurable (fun x => ENNReal.ofReal (f x / g x)) :=
    (hf.div hg).ennreal_ofReal
  have hmeasure := scalarDensityMeasure_eq_withDensity_div hf hg hfnonneg hgpos
  have hvolg : volume ≪ scalarDensityMeasure g := by
    unfold scalarDensityMeasure
    apply withDensity_absolutelyContinuous' hgd.aemeasurable
    exact ae_of_all _ fun x => ENNReal.ofReal_ne_zero_iff.mpr (hgpos x)
  have hfg : scalarDensityMeasure f ≪ scalarDensityMeasure g :=
    (withDensity_absolutelyContinuous _ _).trans hvolg
  have hrn : (scalarDensityMeasure f).rnDeriv (scalarDensityMeasure g) =ᵐ[
      scalarDensityMeasure g] fun x => ENNReal.ofReal (f x / g x) := by
    rw [hmeasure]
    exact Measure.rnDeriv_withDensity _ hratio
  filter_upwards [hfg.ae_le hrn] with x hx
  rw [llr, hx, ENNReal.toReal_ofReal (div_nonneg (hfnonneg x) (hgpos x).le)]

private lemma scalarDensityMeasure_klDiv_eq_integral
    {f g : ℝ → ℝ} (hf : Measurable f) (hg : Measurable g)
    (hfint : Integrable f) (hgint : Integrable g)
    (hfnonneg : ∀ x, 0 ≤ f x) (hfpos : ∀ x, 0 < f x)
    (hgpos : ∀ x, 0 < g x)
    (hftotal : ∫ x : ℝ, f x = 1) (hgtotal : ∫ x : ℝ, g x = 1) :
    (klDiv (scalarDensityMeasure f) (scalarDensityMeasure g)).toReal =
      ∫ x : ℝ, f x * Real.log (f x / g x) := by
  letI : IsProbabilityMeasure (scalarDensityMeasure f) :=
    scalarDensityMeasure_isProbability hfint hfnonneg hftotal
  letI : IsProbabilityMeasure (scalarDensityMeasure g) :=
    scalarDensityMeasure_isProbability hgint (fun x => (hgpos x).le) hgtotal
  have hgd : Measurable (fun x => ENNReal.ofReal (g x)) := hg.ennreal_ofReal
  have hvolg : volume ≪ scalarDensityMeasure g := by
    unfold scalarDensityMeasure
    apply withDensity_absolutelyContinuous' hgd.aemeasurable
    exact ae_of_all _ fun x => ENNReal.ofReal_ne_zero_iff.mpr (hgpos x)
  have hfg : scalarDensityMeasure f ≪ scalarDensityMeasure g :=
    (withDensity_absolutelyContinuous _ _).trans hvolg
  have hllr := scalarDensityMeasure_llr_ae hf hg hfnonneg hfpos hgpos
  rw [toReal_klDiv_of_measure_eq hfg (by simp), integral_congr_ae hllr]
  unfold scalarDensityMeasure
  rw [integral_withDensity_eq_integral_toReal_smul hf.ennreal_ofReal
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards with x
  rw [ENNReal.toReal_ofReal (hfnonneg x)]
  simp only [smul_eq_mul]

private lemma scalarMixture_klDiv_eq_entropy
    { ι : Type* } [Fintype ι] {r X : ι → ℝ} (hr : IsPMF r)
    (hfinite : ∀ i, 0 < r i →
      klDiv
        (scalarDensityMeasure (fun w => scalarLogExpDensity (w - X i)))
        (scalarDensityMeasure (scalarMixtureDensity r X)) ≠ ⊤) :
    (∑ i, r i *
      (klDiv
        (scalarDensityMeasure (fun w => scalarLogExpDensity (w - X i)))
        (scalarDensityMeasure (scalarMixtureDensity r X))).toReal) =
      diffEntropy (scalarMixtureDensity r X) -
        diffEntropy scalarLogExpDensity := by
  have hfmeas (i : ι) : Measurable
      (fun w : ℝ => scalarLogExpDensity (w - X i)) := by
    unfold scalarLogExpDensity
    fun_prop
  have hFmeas : Measurable (scalarMixtureDensity r X) := by
    unfold scalarMixtureDensity scalarLogExpDensity
    fun_prop
  letI (i : ι) : IsProbabilityMeasure
      (scalarDensityMeasure (fun w => scalarLogExpDensity (w - X i))) :=
    scalarDensityMeasure_isProbability (scalarShiftDensity_integrable (X i))
      (fun w => scalarLogExpDensity_nonneg _)
      (scalarShiftDensity_integral_eq_one (X i))
  letI : IsProbabilityMeasure
      (scalarDensityMeasure (scalarMixtureDensity r X)) :=
    scalarDensityMeasure_isProbability scalarMixtureDensity_integrable
      (scalarMixtureDensity_nonneg hr)
      (scalarMixtureDensity_integral_eq_one hr)
  have hKLvalue (i : ι) :
      (klDiv
        (scalarDensityMeasure (fun w => scalarLogExpDensity (w - X i)))
        (scalarDensityMeasure (scalarMixtureDensity r X))).toReal =
      ∫ w : ℝ, scalarLogExpDensity (w - X i) *
        Real.log (scalarLogExpDensity (w - X i) /
          scalarMixtureDensity r X w) := by
    exact scalarDensityMeasure_klDiv_eq_integral (hfmeas i) hFmeas
      (scalarShiftDensity_integrable (X i)) scalarMixtureDensity_integrable
      (fun w => scalarLogExpDensity_nonneg _)
      (fun w => scalarLogExpDensity_pos _)
      (scalarMixtureDensity_pos hr)
      (scalarShiftDensity_integral_eq_one (X i))
      (scalarMixtureDensity_integral_eq_one hr)
  have hselfInt (i : ι) : Integrable
      (fun w : ℝ => scalarLogExpDensity (w - X i) *
        Real.log (scalarLogExpDensity (w - X i))) := by
    refine (scalarShiftDensity_entropy_integrable (X i)).neg.congr
      (ae_of_all _ fun w => ?_)
    change -Real.negMulLog (scalarLogExpDensity (w - X i)) =
      scalarLogExpDensity (w - X i) *
        Real.log (scalarLogExpDensity (w - X i))
    rw [Real.negMulLog]
    ring
  have hselfValue (i : ι) :
      (∫ w : ℝ, scalarLogExpDensity (w - X i) *
        Real.log (scalarLogExpDensity (w - X i))) =
      -diffEntropy scalarLogExpDensity := by
    calc
      (∫ w : ℝ, scalarLogExpDensity (w - X i) *
          Real.log (scalarLogExpDensity (w - X i))) =
          -∫ w : ℝ, Real.negMulLog
            (scalarLogExpDensity (w - X i)) := by
        rw [← integral_neg]
        apply integral_congr_ae
        filter_upwards with w
        rw [Real.negMulLog]
        ring
      _ = -diffEntropy scalarLogExpDensity := by
        rw [scalarShiftDensity_entropy_integral]
  have hratioInt (i : ι) (hi : 0 < r i) : Integrable
      (fun w : ℝ => scalarLogExpDensity (w - X i) *
        Real.log (scalarLogExpDensity (w - X i) /
          scalarMixtureDensity r X w)) := by
    have hllrInt := (klDiv_ne_top_iff.mp (hfinite i hi)).2
    have hllrAE := scalarDensityMeasure_llr_ae (hfmeas i) hFmeas
      (fun w => scalarLogExpDensity_nonneg _)
      (fun w => scalarLogExpDensity_pos _)
      (scalarMixtureDensity_pos hr)
    have hratioMeasure : Integrable
        (fun w : ℝ => Real.log (scalarLogExpDensity (w - X i) /
          scalarMixtureDensity r X w))
        (scalarDensityMeasure (fun w => scalarLogExpDensity (w - X i))) := by
      rw [← integrable_congr hllrAE]
      exact hllrInt
    unfold scalarDensityMeasure at hratioMeasure
    rw [integrable_withDensity_iff (hfmeas i).ennreal_ofReal
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)] at hratioMeasure
    refine hratioMeasure.congr (ae_of_all _ fun w => ?_)
    change Real.log (scalarLogExpDensity (w - X i) /
        scalarMixtureDensity r X w) *
        (ENNReal.ofReal (scalarLogExpDensity (w - X i))).toReal =
      scalarLogExpDensity (w - X i) *
        Real.log (scalarLogExpDensity (w - X i) /
          scalarMixtureDensity r X w)
    rw [ENNReal.toReal_ofReal (scalarLogExpDensity_nonneg _)]
    ring
  have hcrossInt (i : ι) (hi : 0 < r i) : Integrable
      (fun w : ℝ => scalarLogExpDensity (w - X i) *
        Real.log (scalarMixtureDensity r X w)) := by
    refine ((hselfInt i).sub (hratioInt i hi)).congr
      (ae_of_all _ fun w => ?_)
    change scalarLogExpDensity (w - X i) *
          Real.log (scalarLogExpDensity (w - X i)) -
        scalarLogExpDensity (w - X i) *
          Real.log (scalarLogExpDensity (w - X i) /
            scalarMixtureDensity r X w) =
      scalarLogExpDensity (w - X i) *
        Real.log (scalarMixtureDensity r X w)
    rw [Real.log_div (scalarLogExpDensity_pos _).ne'
      (scalarMixtureDensity_pos hr w).ne']
    ring
  have hweightedCrossInt (i : ι) : Integrable
      (fun w : ℝ => r i *
        (scalarLogExpDensity (w - X i) *
          Real.log (scalarMixtureDensity r X w))) := by
    by_cases hi : r i = 0
    · simp [hi]
    · exact (hcrossInt i
        (lt_of_le_of_ne (hr.nonneg i) (Ne.symm hi))).const_mul (r i)
  have hcrossSum :
      (∑ i, r i * (∫ w : ℝ, scalarLogExpDensity (w - X i) *
        Real.log (scalarMixtureDensity r X w))) =
      ∫ w : ℝ, scalarMixtureDensity r X w *
        Real.log (scalarMixtureDensity r X w) := by
    calc
      (∑ i, r i * (∫ w : ℝ, scalarLogExpDensity (w - X i) *
          Real.log (scalarMixtureDensity r X w))) =
          ∑ i, ∫ w : ℝ, r i *
            (scalarLogExpDensity (w - X i) *
              Real.log (scalarMixtureDensity r X w)) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [integral_const_mul]
      _ = ∫ w : ℝ, ∑ i, r i *
            (scalarLogExpDensity (w - X i) *
              Real.log (scalarMixtureDensity r X w)) := by
        rw [integral_finsetSum Finset.univ]
        exact fun i _ => hweightedCrossInt i
      _ = ∫ w : ℝ, scalarMixtureDensity r X w *
          Real.log (scalarMixtureDensity r X w) := by
        apply integral_congr_ae
        filter_upwards with w
        unfold scalarMixtureDensity
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _
        ring
  have hFlogValue :
      (∫ w : ℝ, scalarMixtureDensity r X w *
        Real.log (scalarMixtureDensity r X w)) =
      -diffEntropy (scalarMixtureDensity r X) := by
    calc
      (∫ w : ℝ, scalarMixtureDensity r X w *
          Real.log (scalarMixtureDensity r X w)) =
          -∫ w : ℝ, Real.negMulLog (scalarMixtureDensity r X w) := by
        rw [← integral_neg]
        apply integral_congr_ae
        filter_upwards with w
        rw [Real.negMulLog]
        ring
      _ = -diffEntropy (scalarMixtureDensity r X) := rfl
  calc
    (∑ i, r i *
        (klDiv
          (scalarDensityMeasure (fun w => scalarLogExpDensity (w - X i)))
          (scalarDensityMeasure (scalarMixtureDensity r X))).toReal) =
        ∑ i, r i *
          (-diffEntropy scalarLogExpDensity -
            (∫ w : ℝ, scalarLogExpDensity (w - X i) *
              Real.log (scalarMixtureDensity r X w))) := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : r i = 0
      · simp [hi]
      · rw [hKLvalue i]
        have hiPos : 0 < r i := lt_of_le_of_ne (hr.nonneg i) (Ne.symm hi)
        rw [show (∫ w : ℝ, scalarLogExpDensity (w - X i) *
              Real.log (scalarLogExpDensity (w - X i) /
                scalarMixtureDensity r X w)) =
            (∫ w : ℝ, scalarLogExpDensity (w - X i) *
              Real.log (scalarLogExpDensity (w - X i))) -
            ∫ w : ℝ, scalarLogExpDensity (w - X i) *
              Real.log (scalarMixtureDensity r X w) by
          rw [← integral_sub (hselfInt i) (hcrossInt i hiPos)]
          apply integral_congr_ae
          filter_upwards with w
          rw [Real.log_div (scalarLogExpDensity_pos _).ne'
            (scalarMixtureDensity_pos hr w).ne']
          ring,
          hselfValue i]
    _ = diffEntropy (scalarMixtureDensity r X) -
        diffEntropy scalarLogExpDensity := by
      calc
        (∑ i, r i *
            (-diffEntropy scalarLogExpDensity -
              (∫ w : ℝ, scalarLogExpDensity (w - X i) *
                Real.log (scalarMixtureDensity r X w)))) =
            ∑ i, (r i * (-diffEntropy scalarLogExpDensity) -
              r i * (∫ w : ℝ, scalarLogExpDensity (w - X i) *
                Real.log (scalarMixtureDensity r X w))) := by
          apply Finset.sum_congr rfl
          intro i _
          ring
        _ = (∑ i, r i) * (-diffEntropy scalarLogExpDensity) -
            ∑ i, r i * (∫ w : ℝ,
              scalarLogExpDensity (w - X i) *
                Real.log (scalarMixtureDensity r X w)) := by
          rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
        _ = diffEntropy (scalarMixtureDensity r X) -
            diffEntropy scalarLogExpDensity := by
          rw [show (∑ i, r i) = 1 by simpa [mass] using hr.total,
            one_mul, hcrossSum, hFlogValue]
          ring

/-- The off-diagonal context bound. Under the
log-clock bijection this is `W=X+N`; `diffEntropy_log_exp`,
the exact log-exponential moment, `diffEntropy_le_of_abs_le`, and
`offdiag_context_bound_nats_1771` supply the analytic estimate. -/
private theorem scalar_offdiag_context_1771 {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D) (g b : K.κ) (hbg : b ≠ g) :
    scalarContextInfoNats K g b ≤ scalarSourceKLNats K g b + cOff1771 := by
  let P0 : ℝ := scalarWinnerProb K g b
  let r : α × β → ℝ := scalarSource K g b
  let X : α × β → ℝ := fun z => Real.log (K.sigma b z / P0)
  let Q0 : Measure ℝ := expMeasure (1 / P0)
  let Pz : α × β → Measure ℝ := fun z =>
    if r z = 0 then Q0 else K.clockLawGiven b z
  let W : ℝ → ℝ := fun u => Real.log (u / P0)
  let M0 : Measure ℝ := scalarClockMarginal K g b
  let F : ℝ → ℝ := scalarMixtureDensity r X
  let C : ℝ := scalarSourceKLNats K g b
  have hP0 : 0 < P0 := by
    simpa only [P0] using scalarWinnerProb_pos K g b
  have hr : IsPMF r := by
    simpa only [r] using scalarSource_isPMF K g b
  have hrtotal : ∑ z, r z = 1 := by
    simpa [mass] using hr.total
  have hCnonneg : 0 ≤ C := by
    simpa only [C] using scalarSourceKLNats_nonneg K g b
  have hQtotal : ∑ z, K.Q g z = 1 := by
    simpa [mass] using (K.Q_isContact g).1.total
  have hnum_eq (z : α × β) :
      K.Q g z * K.sigma b z = r z * P0 := by
    dsimp only [r, P0]
    unfold scalarSource
    rw [div_mul_cancel₀ _ (scalarWinnerProb_pos K g b).ne']
  have hnum_pos (z : α × β) (hz : 0 < r z) :
      0 < K.Q g z * K.sigma b z := by
    rw [hnum_eq z]
    exact mul_pos hz hP0
  have hsigma_pos (z : α × β) (hz : 0 < r z) :
      0 < K.sigma b z := by
    have hnum := hnum_pos z hz
    exact lt_of_le_of_ne (raceSigma_nonneg K b z)
      (Ne.symm (mul_ne_zero_iff.mp hnum.ne').2)
  have hQzero (z : α × β) (hz : r z = 0) : K.Q g z = 0 := by
    by_contra hQ
    have hQpos : 0 < K.Q g z :=
      lt_of_le_of_ne ((K.Q_isContact g).1.nonneg z) (Ne.symm hQ)
    have hzsupport : z ∈ support p := by
      by_contra hzs
      exact hQ ((K.Q_isContact g).2.1 z hzs)
    have hsigma : 0 < K.sigma b z := K.sigma_pos b z hzsupport
    have hrpos : 0 < r z := by
      dsimp only [r]
      unfold scalarSource
      exact div_pos (mul_pos hQpos hsigma) hP0
    exact (ne_of_gt hrpos) hz
  have hQ0prob : IsProbabilityMeasure Q0 := by
    dsimp only [Q0]
    exact isProbabilityMeasure_expMeasure (one_div_pos.mpr hP0)
  have hPzprob (z : α × β) : IsProbabilityMeasure (Pz z) := by
    by_cases hz : r z = 0
    · simpa only [Pz, if_pos hz] using hQ0prob
    · simp only [Pz, if_neg hz]
      unfold Clustering.clockLawGiven
      exact isProbabilityMeasure_expMeasure
        (one_div_pos.mpr (hsigma_pos z
          (lt_of_le_of_ne (hr.nonneg z) (Ne.symm hz))))
  letI (z : α × β) : IsProbabilityMeasure (Pz z) := hPzprob z
  have hmix : M0 = ∑ z, ENNReal.ofReal (r z) • Pz z := by
    dsimp only [M0]
    unfold scalarClockMarginal
    change (∑ z, ENNReal.ofReal (r z) • K.clockLawGiven b z) = _
    apply Finset.sum_congr rfl
    intro z _
    by_cases hz : r z = 0 <;> simp [Pz, hz]
  have hMprob : IsProbabilityMeasure M0 := by
    constructor
    rw [hmix]
    rw [show (∑ z, ENNReal.ofReal (r z) • Pz z) Set.univ =
        ∑ z, (ENNReal.ofReal (r z) • Pz z) Set.univ by simp]
    simp only [Measure.smul_apply, smul_eq_mul, measure_univ, mul_one]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun z _ => hr.nonneg z), hrtotal]
    norm_num
  letI : IsProbabilityMeasure M0 := hMprob
  have hPzpos (z : α × β) : ∀ᵐ u ∂Pz z, 0 < u := by
    by_cases hz : r z = 0
    · simp only [Pz, if_pos hz, Q0]
      exact ae_pos_expMeasure (one_div_pos.mpr hP0)
    · simp only [Pz, if_neg hz]
      unfold Clustering.clockLawGiven
      exact ae_pos_expMeasure (one_div_pos.mpr
        (hsigma_pos z (lt_of_le_of_ne (hr.nonneg z) (Ne.symm hz))))
  have hMpos : ∀ᵐ u ∂M0, 0 < u := by
    rw [hmix]
    exact ae_pos_finset_mixture r Pz hPzpos
  have hmapPz (z : α × β) (hz : 0 < r z) :
      Measure.map W (Pz z) =
        scalarDensityMeasure (fun w => scalarLogExpDensity (w - X z)) := by
    simp only [Pz, if_neg hz.ne', W, X]
    unfold Clustering.clockLawGiven
    exact map_log_div_expMeasure_eq_shiftDensity (hsigma_pos z hz) hP0
  have hmapM : Measure.map W M0 = scalarDensityMeasure F := by
    calc
      Measure.map W M0 =
          Measure.map W (∑ z, ENNReal.ofReal (r z) • Pz z) := by rw [← hmix]
      _ = ∑ z, Measure.map W (ENNReal.ofReal (r z) • Pz z) :=
        Measure.map_finset_sum' (by fun_prop)
      _ = ∑ z, ENNReal.ofReal (r z) •
          scalarDensityMeasure (fun w => scalarLogExpDensity (w - X z)) := by
        apply Finset.sum_congr rfl
        intro z _
        rw [Measure.map_smul]
        by_cases hz : r z = 0
        · simp [hz]
        · rw [hmapPz z (lt_of_le_of_ne (hr.nonneg z) (Ne.symm hz))]
      _ = scalarDensityMeasure F := by
        dsimp only [F]
        exact (scalarDensityMeasure_finset_mixture hr).symm
  have hKLmap (z : α × β) (hz : 0 < r z) :
      klDiv
          (scalarDensityMeasure (fun w => scalarLogExpDensity (w - X z)))
          (scalarDensityMeasure F) =
        klDiv (Pz z) M0 := by
    have h := klDiv_map_log_div_eq hP0 (Pz z) M0 (hPzpos z) hMpos
    change klDiv (Measure.map W (Pz z)) (Measure.map W M0) =
      klDiv (Pz z) M0 at h
    rw [hmapPz z hz, hmapM] at h
    exact h
  have hfiniteW (z : α × β) (hz : 0 < r z) :
      klDiv
          (scalarDensityMeasure (fun w => scalarLogExpDensity (w - X z)))
          (scalarDensityMeasure F) ≠ ⊤ := by
    rw [hKLmap z hz]
    simp only [Pz, if_neg hz.ne', M0]
    exact scalarClock_klDiv_ne_top K g b z (hnum_pos z hz)
  have hcontextEq : scalarContextInfoNats K g b =
      diffEntropy F - diffEntropy scalarLogExpDensity := by
    unfold scalarContextInfoNats
    calc
      (∑ z, r z *
          (klDiv (K.clockLawGiven b z) (scalarClockMarginal K g b)).toReal) =
          ∑ z, r z * (klDiv (Pz z) M0).toReal := by
        apply Finset.sum_congr rfl
        intro z _
        by_cases hz : r z = 0
        · simp [hz]
        · simp [Pz, M0, hz]
      _ = ∑ z, r z *
          (klDiv
            (scalarDensityMeasure (fun w => scalarLogExpDensity (w - X z)))
            (scalarDensityMeasure F)).toReal := by
        apply Finset.sum_congr rfl
        intro z _
        by_cases hz : r z = 0
        · simp [hz]
        · rw [hKLmap z (lt_of_le_of_ne (hr.nonneg z) (Ne.symm hz))]
      _ = diffEntropy F - diffEntropy scalarLogExpDensity := by
        dsimp only [F]
        exact scalarMixture_klDiv_eq_entropy hr hfiniteW
  have hratio (z : α × β) (hz : 0 < r z) :
      r z / K.Q g z = K.sigma b z / P0 := by
    have hnum := hnum_pos z hz
    have hQne : K.Q g z ≠ 0 := (mul_ne_zero_iff.mp hnum.ne').1
    field_simp [hQne, hP0.ne']
    rw [← hnum_eq z]
  have hCeq : C = ∑ z, r z * X z := by
    dsimp only [C, X]
    unfold scalarSourceKLNats
    change (∑ z, r z * Real.log (r z / K.Q g z)) =
      ∑ z, r z * Real.log (K.sigma b z / P0)
    apply Finset.sum_congr rfl
    intro z _
    by_cases hz : r z = 0
    · simp [hz]
    · rw [hratio z (lt_of_le_of_ne (hr.nonneg z) (Ne.symm hz))]
  have hexpTerm (z : α × β) :
      r z * Real.exp (-X z) = K.Q g z := by
    by_cases hz : r z = 0
    · simp [hz, hQzero z hz]
    · have hzpos : 0 < r z :=
        lt_of_le_of_ne (hr.nonneg z) (Ne.symm hz)
      have hsigma := hsigma_pos z hzpos
      dsimp only [X]
      rw [Real.exp_neg, Real.exp_log (div_pos hsigma hP0)]
      field_simp [hsigma.ne', hP0.ne']
      nlinarith [hnum_eq z]
  have hexpSum : ∑ z, r z * Real.exp (-X z) = 1 := by
    calc
      (∑ z, r z * Real.exp (-X z)) = ∑ z, K.Q g z := by
        apply Finset.sum_congr rfl
        intro z _
        exact hexpTerm z
      _ = 1 := hQtotal
  let negPart : ℝ := ∑ z, r z * max (-X z) 0
  have hnegPart : negPart ≤ 1 / Real.exp 1 := by
    dsimp only [negPart]
    calc
      (∑ z, r z * max (-X z) 0) ≤
          ∑ z, r z * (Real.exp (-X z) / Real.exp 1) := by
        apply Finset.sum_le_sum
        intro z _
        apply mul_le_mul_of_nonneg_left _ (hr.nonneg z)
        simpa only [Real.log_exp] using
          log_pos_part_le_div_exp_one (Real.exp (-X z)) (Real.exp_pos _)
      _ = ∑ z, (r z * Real.exp (-X z)) / Real.exp 1 := by
        apply Finset.sum_congr rfl
        intro z _
        ring
      _ = (∑ z, r z * Real.exp (-X z)) / Real.exp 1 := by
        rw [Finset.sum_div]
      _ = 1 / Real.exp 1 := by rw [hexpSum]
  have habspoint (x : ℝ) : |x| = x + 2 * max (-x) 0 := by
    by_cases hx : 0 ≤ x
    · rw [abs_of_nonneg hx, max_eq_right (neg_nonpos.mpr hx)]
      ring
    · have hxle : x ≤ 0 := le_of_not_ge hx
      rw [abs_of_nonpos hxle, max_eq_left (neg_nonneg.mpr hxle)]
      ring
  have habsX : (∑ z, r z * |X z|) ≤ C + 2 / Real.exp 1 := by
    calc
      (∑ z, r z * |X z|) =
          ∑ z, (r z * X z + 2 * (r z * max (-X z) 0)) := by
        apply Finset.sum_congr rfl
        intro z _
        rw [habspoint]
        ring
      _ = (∑ z, r z * X z) + 2 * negPart := by
        rw [Finset.sum_add_distrib, Finset.mul_sum]
      _ = C + 2 * negPart := by rw [← hCeq]
      _ ≤ C + 2 / Real.exp 1 := by
        have hmul := mul_le_mul_of_nonneg_left hnegPart (by norm_num : (0 : ℝ) ≤ 2)
        calc
          C + 2 * negPart ≤ C + 2 * (1 / Real.exp 1) :=
            add_le_add_right hmul C
          _ = C + 2 / Real.exp 1 := by ring
  have habsF : (∫ w : ℝ, |w| * F w) ≤ C + alpha1771 := by
    calc
      (∫ w : ℝ, |w| * F w) ≤
          ∑ z, r z * (|X z| + logExpAbsMoment) := by
        dsimp only [F]
        exact scalarMixtureDensity_abs_integral_le_1771 hr
      _ = (∑ z, r z * |X z|) + logExpAbsMoment := by
        calc
          (∑ z, r z * (|X z| + logExpAbsMoment)) =
              (∑ z, r z * |X z|) +
                logExpAbsMoment * ∑ z, r z := by
            rw [Finset.mul_sum, ← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro z _
            ring
          _ = (∑ z, r z * |X z|) + logExpAbsMoment := by
            rw [hrtotal]
            ring
      _ ≤ C + alpha1771 := by
        unfold alpha1771
        linarith
  have hFentropy : diffEntropy F ≤
      Real.log (2 * Real.exp 1 * (C + alpha1771)) := by
    apply diffEntropy_le_of_abs_le
    · exact scalarMixtureDensity_nonneg hr
    · exact scalarMixtureDensity_integrable
    · exact scalarMixtureDensity_integral_eq_one hr
    · exact scalarMixtureDensity_entropy_integrable hr
    · exact scalarMixtureDensity_abs_integrable
    · linarith [one_lt_alpha1771]
    · exact habsF
  have hnoise : diffEntropy scalarLogExpDensity =
      Real.eulerMascheroniConstant + 1 := by
    unfold scalarLogExpDensity
    exact diffEntropy_log_exp
  change scalarContextInfoNats K g b ≤ C + cOff1771
  rw [hcontextEq, hnoise]
  calc
    diffEntropy F - (Real.eulerMascheroniConstant + 1) ≤
        Real.log (2 * Real.exp 1 * (C + alpha1771)) -
          (Real.eulerMascheroniConstant + 1) := by linarith
    _ ≤ C + cOff1771 := by
      simpa only [add_comm] using offdiag_context_bound_nats_1771 hCnonneg

private theorem scalar_offdiag_context {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D) (g b : K.κ) (hbg : b ≠ g) :
    scalarContextInfoNats K g b ≤ scalarSourceKLNats K g b + cZero := by
  exact (scalar_offdiag_context_1771 K g b hbg).trans
    (add_le_add_right cOff1771_le_cZero _)

private lemma expMeasure_klDiv_ne_top {s q : ℝ} (hs : 0 < s) (hq : 0 < q) :
    klDiv (expMeasure (1 / s)) (expMeasure (1 / q)) ≠ ⊤ := by
  by_cases hsq : s = q
  · subst q
    letI : IsProbabilityMeasure (expMeasure (1 / s)) :=
      isProbabilityMeasure_expMeasure (one_div_pos.mpr hs)
    rw [klDiv_self]
    exact ENNReal.zero_ne_top
  · intro htop
    have hvalue := klDiv_expMeasure hs hq
    rw [htop, ENNReal.toReal_top] at hvalue
    have hratioPos : 0 < s / q := div_pos hs hq
    have hratioNe : s / q ≠ 1 := by
      intro hratio
      exact hsq ((div_eq_one_iff_eq hq.ne').mp hratio)
    have hstrict := Real.log_lt_sub_one_of_pos hratioPos hratioNe
    have hlog : Real.log (q / s) = -Real.log (s / q) := by
      rw [Real.log_div hq.ne' hs.ne', Real.log_div hs.ne' hq.ne']
      ring
    rw [hlog] at hvalue
    linarith

/-- The diagonal context bound, obtained from the
golden formula, `klDiv_expMeasure`, and `diag_context_arith`. -/
private theorem scalar_diag_context {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D) (g : K.κ) :
    scalarWinnerProb K g g * scalarContextInfoNats K g g ≤
      1 - scalarWinnerProb K g g := by
  let P0 : ℝ := scalarWinnerProb K g g
  let r : α × β → ℝ := scalarSource K g g
  let Q0 : Measure ℝ := expMeasure (1 / P0)
  let Pz : α × β → Measure ℝ := fun z =>
    if r z = 0 then Q0 else K.clockLawGiven g z
  let invR : ℝ := ∑ z, r z * (K.sigma g z / P0)
  have hP0 : 0 < P0 := by
    simpa only [P0] using scalarWinnerProb_pos K g g
  have hr : IsPMF r := by
    simpa only [r] using scalarSource_isPMF K g g
  have hrtotal : ∑ z, r z = 1 := by
    simpa [mass] using hr.total
  have hnum_eq (z : α × β) :
      K.Q g z * K.sigma g z = r z * P0 := by
    dsimp only [r, P0]
    unfold scalarSource
    rw [div_mul_cancel₀ _ (scalarWinnerProb_pos K g g).ne']
  have hnum_pos (z : α × β) (hz : 0 < r z) :
      0 < K.Q g z * K.sigma g z := by
    rw [hnum_eq z]
    exact mul_pos hz hP0
  have hsigma_pos (z : α × β) (hz : 0 < r z) :
      0 < K.sigma g z := by
    have hnum := hnum_pos z hz
    exact lt_of_le_of_ne (raceSigma_nonneg K g z)
      (Ne.symm (mul_ne_zero_iff.mp hnum.ne').2)
  have hQ0prob : IsProbabilityMeasure Q0 := by
    dsimp only [Q0]
    exact isProbabilityMeasure_expMeasure (one_div_pos.mpr hP0)
  have hPzprob (z : α × β) : IsProbabilityMeasure (Pz z) := by
    by_cases hz : r z = 0
    · simpa only [Pz, if_pos hz] using hQ0prob
    · simp only [Pz, if_neg hz]
      unfold Clustering.clockLawGiven
      exact isProbabilityMeasure_expMeasure
        (one_div_pos.mpr (hsigma_pos z
          (lt_of_le_of_ne (hr.nonneg z) (Ne.symm hz))))
  letI (z : α × β) : IsProbabilityMeasure (Pz z) := hPzprob z
  have hmix : scalarClockMarginal K g g =
      ∑ z, ENNReal.ofReal (r z) • Pz z := by
    unfold scalarClockMarginal
    change (∑ z, ENNReal.ofReal (r z) • K.clockLawGiven g z) = _
    apply Finset.sum_congr rfl
    intro z _
    by_cases hz : r z = 0
    · simp [Pz, hz]
    · simp [Pz, hz]
  have hMprob : IsProbabilityMeasure (scalarClockMarginal K g g) := by
    constructor
    rw [hmix]
    rw [show (∑ z, ENNReal.ofReal (r z) • Pz z) Set.univ =
        ∑ z, (ENNReal.ofReal (r z) • Pz z) Set.univ by simp]
    simp only [Measure.smul_apply, smul_eq_mul, measure_univ, mul_one]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun z _ => hr.nonneg z), hrtotal]
    norm_num
  have hPMfinite (z : α × β) (hz : 0 < r z) :
      klDiv (Pz z) (scalarClockMarginal K g g) ≠ ⊤ := by
    simp only [Pz, if_neg hz.ne']
    exact scalarClock_klDiv_ne_top K g g z (hnum_pos z hz)
  have hPQfinite (z : α × β) (hz : 0 < r z) :
      klDiv (Pz z) Q0 ≠ ⊤ := by
    simp only [Pz, if_neg hz.ne']
    unfold Clustering.clockLawGiven
    simpa only [Q0] using
      expMeasure_klDiv_ne_top (hsigma_pos z hz) hP0
  have hgolden : scalarContextInfoNats K g g ≤
      ∑ z, r z * (klDiv (Pz z) Q0).toReal := by
    unfold scalarContextInfoNats
    change (∑ z, r z *
      (klDiv (K.clockLawGiven g z) (scalarClockMarginal K g g)).toReal) ≤ _
    calc
      (∑ z, r z *
          (klDiv (K.clockLawGiven g z)
            (scalarClockMarginal K g g)).toReal) =
          ∑ z, r z *
            (klDiv (Pz z) (scalarClockMarginal K g g)).toReal := by
        apply Finset.sum_congr rfl
        intro z _
        by_cases hz : r z = 0
        · simp [hz]
        · simp [Pz, hz]
      _ ≤ ∑ z, r z * (klDiv (Pz z) Q0).toReal :=
        finite_mixture_golden_le r Pz (scalarClockMarginal K g g) Q0
          hr hPzprob hMprob hQ0prob hmix hPMfinite hPQfinite
  have hreference_term (z : α × β) :
      r z * (klDiv (Pz z) Q0).toReal =
        -(r z * Real.log (r z / K.Q g z)) +
          r z * (K.sigma g z / P0) - r z := by
    by_cases hz : r z = 0
    · simp [hz]
    · have hrz : 0 < r z :=
        lt_of_le_of_ne (hr.nonneg z) (Ne.symm hz)
      have hnum := hnum_pos z hrz
      have hQne : K.Q g z ≠ 0 := (mul_ne_zero_iff.mp hnum.ne').1
      have hsigma := hsigma_pos z hrz
      have hratio : r z / K.Q g z = K.sigma g z / P0 := by
        field_simp [hQne, hP0.ne']
        rw [← hnum_eq z]
      have hlog :
          Real.log (P0 / K.sigma g z) =
            -Real.log (r z / K.Q g z) := by
        rw [hratio, Real.log_div hP0.ne' hsigma.ne',
          Real.log_div hsigma.ne' hP0.ne']
        ring
      simp only [Pz, if_neg hz]
      dsimp only [Q0]
      unfold Clustering.clockLawGiven
      rw [klDiv_expMeasure hsigma hP0, hlog]
      ring
  have hreference : (∑ z, r z * (klDiv (Pz z) Q0).toReal) =
      -scalarSourceKLNats K g g + invR - 1 := by
    calc
      (∑ z, r z * (klDiv (Pz z) Q0).toReal) =
          ∑ z, (-(r z * Real.log (r z / K.Q g z)) +
            r z * (K.sigma g z / P0) - r z) := by
        apply Finset.sum_congr rfl
        intro z _
        exact hreference_term z
      _ = -scalarSourceKLNats K g g + invR - 1 := by
        rw [Finset.sum_sub_distrib, Finset.sum_add_distrib,
          Finset.sum_neg_distrib, hrtotal]
        dsimp only [invR]
        unfold scalarSourceKLNats
        change -(∑ z, r z * Real.log (r z / K.Q g z)) +
            (∑ z, r z * (K.sigma g z / P0)) - 1 = _
        rfl
  have hsigma_le_one (z : α × β) (hz : r z ≠ 0) :
      K.sigma g z ≤ 1 := by
    have hrz : 0 < r z := lt_of_le_of_ne (hr.nonneg z) (Ne.symm hz)
    have hnum := hnum_pos z hrz
    have hQne : K.Q g z ≠ 0 := (mul_ne_zero_iff.mp hnum.ne').1
    have hzsupport : z ∈ support p := by
      by_contra hzs
      exact hQne ((K.Q_isContact g).2.1 z hzs)
    have hsingle : K.sigma g z ≤ ∑ c, K.sigma c z :=
      Finset.single_le_sum (fun c _ => raceSigma_nonneg K c z)
        (Finset.mem_univ g)
    rwa [raceSigma_sum_eq_one K z hzsupport] at hsingle
  have hinv : invR ≤ 1 / P0 := by
    dsimp only [invR]
    calc
      (∑ z, r z * (K.sigma g z / P0)) ≤
          ∑ z, r z * (1 / P0) := by
        apply Finset.sum_le_sum
        intro z _
        by_cases hz : r z = 0
        · simp [hz]
        · exact mul_le_mul_of_nonneg_left
            ((div_le_div_iff_of_pos_right hP0).2 (hsigma_le_one z hz))
            (hr.nonneg z)
      _ = 1 / P0 := by
        calc
          (∑ z, r z * (1 / P0)) = (∑ z, r z) * (1 / P0) := by
            exact (Finset.sum_mul (Finset.univ : Finset (α × β)) r
              (1 / P0)).symm
          _ = 1 / P0 := by rw [hrtotal, one_mul]
  have hcontext : scalarContextInfoNats K g g ≤
      -scalarSourceKLNats K g g + invR - 1 :=
    hgolden.trans_eq hreference
  change P0 * scalarContextInfoNats K g g ≤ 1 - P0
  calc
    P0 * scalarContextInfoNats K g g ≤
        P0 * (-scalarSourceKLNats K g g + invR - 1) :=
      mul_le_mul_of_nonneg_left hcontext hP0.le
    _ ≤ 1 - P0 :=
      diag_context_arith hP0 (scalarSourceKLNats_nonneg K g g) hinv

/-- Expanding `condMIcts` and normalizing each positive context gives the
weighted sum of the per-context informations. -/
private theorem scalar_context_decomposition_nats {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D) :
    raceScalar K * Real.log 2 =
      ∑ g, K.s g * ∑ b,
        scalarWinnerProb K g b * scalarContextInfoNats K g b := by
  have hlog : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
  unfold raceScalar condMIcts
  rw [div_mul_cancel₀ _ hlog, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro g _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  unfold scalarContextInfoNats
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  unfold scalarSource
  have hP := (scalarWinnerProb_pos K g b).ne'
  field_simp

/-- The finite mixture identity
`∑_b P(B=b|g)D(ν_{gb}‖Q_g)=I(B;Z|C₀=g)`, followed by cluster
calibration.  The right side is converted from bits to nats. -/
private theorem scalar_source_mixture_identity {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D) :
    (∑ g, K.s g * ∑ b,
      scalarWinnerProb K g b * scalarSourceKLNats K g b) =
        K.Sinfo * Real.log 2 := by
  rw [Sinfo_eq_scalarPosterior_MI K]
  simp_rw [scalarSource_weighted_eq_MI_nats K]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro g _
  ring

/-- Cluster calibration for the mismatch event `B ≠ C₀`. -/
private theorem scalar_mismatch_calibration {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D) :
    (∑ g, K.s g * ∑ b ∈ univ.erase g, scalarWinnerProb K g b) =
      K.dMis := by
  calc
    (∑ g, K.s g * ∑ b ∈ univ.erase g, scalarWinnerProb K g b) =
        ∑ g, ∑ b ∈ univ.erase g, ∑ z,
          K.s g * K.Q g z * K.sigma b z := by
      unfold scalarWinnerProb
      apply Finset.sum_congr rfl
      intro g _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z _
      ring
    _ = ∑ g, ∑ b ∈ univ.erase g, ∑ z,
        p z * K.sigma g z * K.sigma b z := by
      apply Finset.sum_congr rfl
      intro g _
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.sum_congr rfl
      intro z _
      rw [← clusterWeight_eq_pSigma K g z]
    _ = ∑ z, ∑ g, ∑ b ∈ univ.erase g,
        p z * K.sigma g z * K.sigma b z := by
      calc
        (∑ g, ∑ b ∈ univ.erase g, ∑ z,
          p z * K.sigma g z * K.sigma b z) =
            ∑ g, ∑ z, ∑ b ∈ univ.erase g,
              p z * K.sigma g z * K.sigma b z := by
          apply Finset.sum_congr rfl
          intro g _
          rw [Finset.sum_comm]
        _ = _ := by rw [Finset.sum_comm]
    _ = ∑ z, p z *
        (∑ g, K.sigma g z *
          ∑ b ∈ univ.erase g, K.sigma b z) := by
      apply Finset.sum_congr rfl
      intro z _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro g _
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      ring
    _ = ∑ z, p z * (1 - ∑ b, K.sigma b z ^ 2) := by
      apply Finset.sum_congr rfl
      intro z _
      by_cases hp : p z = 0
      · simp [hp]
      · have hz : z ∈ support p := by simpa [support] using hp
        have hsum := raceSigma_sum_eq_one K z hz
        have hrow (g : K.κ) :
            (∑ b ∈ univ.erase g, K.sigma b z) =
              1 - K.sigma g z := by
          have herase := Finset.sum_erase_add (univ : Finset K.κ)
            (fun b => K.sigma b z) (Finset.mem_univ g)
          linarith
        have hoff :
            (∑ g, K.sigma g z *
              ∑ b ∈ univ.erase g, K.sigma b z) =
                1 - ∑ b, K.sigma b z ^ 2 := by
          calc
            (∑ g, K.sigma g z *
              ∑ b ∈ univ.erase g, K.sigma b z) =
                ∑ g, K.sigma g z * (1 - K.sigma g z) := by
              apply Finset.sum_congr rfl
              intro g _
              rw [hrow g]
            _ = (∑ g, K.sigma g z) - ∑ g, K.sigma g z ^ 2 := by
              rw [← Finset.sum_sub_distrib]
              apply Finset.sum_congr rfl
              intro g _
              ring
            _ = 1 - ∑ g, K.sigma g z ^ 2 := by rw [hsum]
        rw [hoff]
    _ = K.dMis := K.dMis_eq.symm

/-- Assembly of the off-diagonal, diagonal, mixture, and calibration
identities, still in nats. -/
private theorem scalar_assembly_nats {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D) :
    raceScalar K * Real.log 2 ≤
      K.Sinfo * Real.log 2 + (1 + cZero) * K.dMis := by
  have hcontext (g : K.κ) :
      (∑ b, scalarWinnerProb K g b * scalarContextInfoNats K g b) ≤
        (∑ b, scalarWinnerProb K g b * scalarSourceKLNats K g b) +
          (1 + cZero) *
            ∑ b ∈ univ.erase g, scalarWinnerProb K g b := by
    have hoff :
        (∑ b ∈ univ.erase g,
          scalarWinnerProb K g b * scalarContextInfoNats K g b) ≤
        ∑ b ∈ univ.erase g,
          scalarWinnerProb K g b *
            (scalarSourceKLNats K g b + cZero) := by
      apply Finset.sum_le_sum
      intro b hb
      exact mul_le_mul_of_nonneg_left
        (scalar_offdiag_context K g b (Finset.mem_erase.mp hb).1)
        (scalarWinnerProb_pos K g b).le
    have hdiag := scalar_diag_context K g
    have hdiagC :
        0 ≤ scalarWinnerProb K g g * scalarSourceKLNats K g g :=
      mul_nonneg (scalarWinnerProb_pos K g g).le
        (scalarSourceKLNats_nonneg K g g)
    have hIerase := Finset.sum_erase_add (univ : Finset K.κ)
      (fun b => scalarWinnerProb K g b * scalarContextInfoNats K g b)
      (Finset.mem_univ g)
    have hCerase := Finset.sum_erase_add (univ : Finset K.κ)
      (fun b => scalarWinnerProb K g b * scalarSourceKLNats K g b)
      (Finset.mem_univ g)
    have hPerase := Finset.sum_erase_add (univ : Finset K.κ)
      (fun b => scalarWinnerProb K g b) (Finset.mem_univ g)
    have hPsum := sum_scalarWinnerProb K g
    have hoffExpand :
        (∑ b ∈ univ.erase g,
          scalarWinnerProb K g b *
            (scalarSourceKLNats K g b + cZero)) =
          (∑ b ∈ univ.erase g,
            scalarWinnerProb K g b * scalarSourceKLNats K g b) +
          cZero * ∑ b ∈ univ.erase g, scalarWinnerProb K g b := by
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      ring
    rw [hoffExpand] at hoff
    nlinarith
  calc
    raceScalar K * Real.log 2 =
        ∑ g, K.s g * ∑ b,
          scalarWinnerProb K g b * scalarContextInfoNats K g b :=
      scalar_context_decomposition_nats K
    _ ≤ ∑ g, K.s g *
        ((∑ b, scalarWinnerProb K g b * scalarSourceKLNats K g b) +
          (1 + cZero) *
            ∑ b ∈ univ.erase g, scalarWinnerProb K g b) := by
      apply Finset.sum_le_sum
      intro g _
      exact mul_le_mul_of_nonneg_left (hcontext g) (clusterMass_nonneg K g)
    _ = (∑ g, K.s g * ∑ b,
          scalarWinnerProb K g b * scalarSourceKLNats K g b) +
        (1 + cZero) *
          ∑ g, K.s g * ∑ b ∈ univ.erase g, scalarWinnerProb K g b := by
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro g _
      ring
    _ = K.Sinfo * Real.log 2 + (1 + cZero) * K.dMis := by
      rw [scalar_source_mixture_identity K, scalar_mismatch_calibration K]

private theorem race_scalar_le {p : α × β → ℝ} {D : SeedSetup p}
    (K : Clustering D) :
    raceScalar K ≤ K.Sinfo + kappa * K.dMis := by
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hmul : raceScalar K * Real.log 2 ≤
      (K.Sinfo + kappa * K.dMis) * Real.log 2 := by
    calc
    raceScalar K * Real.log 2 ≤
        K.Sinfo * Real.log 2 + (1 + cZero) * K.dMis :=
      scalar_assembly_nats K
    _ = (K.Sinfo + kappa * K.dMis) * Real.log 2 := by
      have hk : 1 + cZero = kappa * Real.log 2 := by
        rw [kappa_mul_log_two]
        unfold cZero
        ring
      rw [hk]
      ring
  exact le_of_mul_le_mul_right hmul hlog

private theorem scalar_assembly_nats_1771 {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D) :
    raceScalar K * Real.log 2 ≤
      K.Sinfo * Real.log 2 + (1 + cOff1771) * K.dMis := by
  have hcontext (g : K.κ) :
      (∑ b, scalarWinnerProb K g b * scalarContextInfoNats K g b) ≤
        (∑ b, scalarWinnerProb K g b * scalarSourceKLNats K g b) +
          (1 + cOff1771) *
            ∑ b ∈ univ.erase g, scalarWinnerProb K g b := by
    have hoff :
        (∑ b ∈ univ.erase g,
          scalarWinnerProb K g b * scalarContextInfoNats K g b) ≤
        ∑ b ∈ univ.erase g,
          scalarWinnerProb K g b *
            (scalarSourceKLNats K g b + cOff1771) := by
      apply Finset.sum_le_sum
      intro b hb
      exact mul_le_mul_of_nonneg_left
        (scalar_offdiag_context_1771 K g b (Finset.mem_erase.mp hb).1)
        (scalarWinnerProb_pos K g b).le
    have hdiag := scalar_diag_context K g
    have hdiagC :
        0 ≤ scalarWinnerProb K g g * scalarSourceKLNats K g g :=
      mul_nonneg (scalarWinnerProb_pos K g g).le
        (scalarSourceKLNats_nonneg K g g)
    have hIerase := Finset.sum_erase_add (univ : Finset K.κ)
      (fun b => scalarWinnerProb K g b * scalarContextInfoNats K g b)
      (Finset.mem_univ g)
    have hCerase := Finset.sum_erase_add (univ : Finset K.κ)
      (fun b => scalarWinnerProb K g b * scalarSourceKLNats K g b)
      (Finset.mem_univ g)
    have hPerase := Finset.sum_erase_add (univ : Finset K.κ)
      (fun b => scalarWinnerProb K g b) (Finset.mem_univ g)
    have hPsum := sum_scalarWinnerProb K g
    have hoffExpand :
        (∑ b ∈ univ.erase g,
          scalarWinnerProb K g b *
            (scalarSourceKLNats K g b + cOff1771)) =
          (∑ b ∈ univ.erase g,
            scalarWinnerProb K g b * scalarSourceKLNats K g b) +
          cOff1771 * ∑ b ∈ univ.erase g, scalarWinnerProb K g b := by
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      ring
    rw [hoffExpand] at hoff
    nlinarith
  calc
    raceScalar K * Real.log 2 =
        ∑ g, K.s g * ∑ b,
          scalarWinnerProb K g b * scalarContextInfoNats K g b :=
      scalar_context_decomposition_nats K
    _ ≤ ∑ g, K.s g *
        ((∑ b, scalarWinnerProb K g b * scalarSourceKLNats K g b) +
          (1 + cOff1771) *
            ∑ b ∈ univ.erase g, scalarWinnerProb K g b) := by
      apply Finset.sum_le_sum
      intro g _
      exact mul_le_mul_of_nonneg_left (hcontext g) (clusterMass_nonneg K g)
    _ = (∑ g, K.s g * ∑ b,
          scalarWinnerProb K g b * scalarSourceKLNats K g b) +
        (1 + cOff1771) *
          ∑ g, K.s g * ∑ b ∈ univ.erase g, scalarWinnerProb K g b := by
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro g _
      ring
    _ = K.Sinfo * Real.log 2 + (1 + cOff1771) * K.dMis := by
      rw [scalar_source_mixture_identity K, scalar_mismatch_calibration K]

private theorem race_scalar_le_1771 {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D) :
    raceScalar K ≤ K.Sinfo + kappa1771 * K.dMis := by
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hk : 1 + cOff1771 = kappa1771 * Real.log 2 := by
    unfold kappa1771
    field_simp [hlog.ne']
  have hmul : raceScalar K * Real.log 2 ≤
      (K.Sinfo + kappa1771 * K.dMis) * Real.log 2 := by
    calc
      raceScalar K * Real.log 2 ≤
          K.Sinfo * Real.log 2 + (1 + cOff1771) * K.dMis :=
        scalar_assembly_nats_1771 K
      _ = (K.Sinfo + kappa1771 * K.dMis) * Real.log 2 := by
        rw [hk]
        ring
  exact le_of_mul_le_mul_right hmul hlog

/-! ### Lemma 7.5 and Theorem 10.1: the losing-vector cone -/

private lemma shifted_exp_klDiv_ne_top {a : ℝ} (ha : 0 ≤ a) :
    klDiv ((expMeasure 1).map (fun x => a + x)) (expMeasure 1) ≠ ⊤ := by
  letI : IsProbabilityMeasure (expMeasure 1) :=
    isProbabilityMeasure_expMeasure zero_lt_one
  by_cases hzero : a = 0
  · simpa [hzero] using ENNReal.zero_ne_top
  · intro htop
    have hpos : 0 < a := lt_of_le_of_ne ha (Ne.symm hzero)
    have hvalue := shifted_exp_klDiv ha
    rw [htop, ENNReal.toReal_top] at hvalue
    linarith

/-- Step 1 of Theorem 10.1.  This is the actual product-measure KL
additivity statement: every coordinate is priced against the same unshifted
product reference before the coordinate sum is collapsed by
`product_shift_klDiv`. -/
private theorem losing_product_klDiv {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D) (b : K.κ) (z : α × β)
    (hz : z ∈ support p) (u : ℝ) (hu : 0 ≤ u) :
    (klDiv (losingClockLaw K b z u) (losingReference K b)).toReal =
      u * (1 / K.sigma b z - 1) := by
  let μ : losingIndex K b → Measure ℝ := fun c =>
    (expMeasure 1).map
      (fun e => u * (K.sigma c.1 z / K.sigma b z) + e)
  let ν : losingIndex K b → Measure ℝ := fun _ => expMeasure 1
  have hsb : 0 < K.sigma b z := K.sigma_pos b z hz
  have hshift (c : losingIndex K b) :
      0 ≤ u * (K.sigma c.1 z / K.sigma b z) :=
    mul_nonneg hu (div_nonneg (K.sigma_pos c.1 z hz).le hsb.le)
  have hμ (c : losingIndex K b) : IsProbabilityMeasure (μ c) := by
    unfold μ
    letI : IsProbabilityMeasure (expMeasure 1) :=
      isProbabilityMeasure_expMeasure zero_lt_one
    exact Measure.isProbabilityMeasure_map
      (measurable_const.add measurable_id).aemeasurable
  have hν (c : losingIndex K b) : IsProbabilityMeasure (ν c) := by
    unfold ν
    exact isProbabilityMeasure_expMeasure zero_lt_one
  have hpi : klDiv (Measure.pi μ) (Measure.pi ν) =
      ∑ c, klDiv (μ c) (ν c) := klDiv_pi_eq_sum μ ν hμ hν
  have hfinite (c : losingIndex K b) : klDiv (μ c) (ν c) ≠ ⊤ := by
    unfold μ ν
    exact shifted_exp_klDiv_ne_top (hshift c)
  calc
    (klDiv (losingClockLaw K b z u) (losingReference K b)).toReal =
        (klDiv (Measure.pi μ) (Measure.pi ν)).toReal := by
      rfl
    _ = (∑ c, klDiv (μ c) (ν c)).toReal := by rw [hpi]
    _ = ∑ c, (klDiv (μ c) (ν c)).toReal := by
      exact ENNReal.toReal_sum (fun c _ => hfinite c)
    _ = ∑ c : losingIndex K b,
        u * (K.sigma c.1 z / K.sigma b z) := by
      apply Finset.sum_congr rfl
      intro c _
      unfold μ ν
      exact shifted_exp_klDiv (hshift c)
    _ = ∑ c ∈ univ.erase b,
        u * (K.sigma c z / K.sigma b z) := by
      exact (Finset.sum_subtype (univ.erase b) (by simp)
        (fun c => u * (K.sigma c z / K.sigma b z))).symm
    _ = u * (1 / K.sigma b z - 1) := product_shift_klDiv b hz hu

private theorem losingReference_klDiv_ne_top {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D) (b : K.κ) (z : α × β)
    (hz : z ∈ support p) (u : ℝ) (hu : 0 ≤ u) :
    klDiv (losingClockLaw K b z u) (losingReference K b) ≠ ⊤ := by
  let μ : losingIndex K b → Measure ℝ := fun c =>
    (expMeasure 1).map
      (fun e => u * (K.sigma c.1 z / K.sigma b z) + e)
  let ν : losingIndex K b → Measure ℝ := fun _ => expMeasure 1
  have hsb : 0 < K.sigma b z := K.sigma_pos b z hz
  have hshift (c : losingIndex K b) :
      0 ≤ u * (K.sigma c.1 z / K.sigma b z) :=
    mul_nonneg hu (div_nonneg (K.sigma_pos c.1 z hz).le hsb.le)
  have hμ (c : losingIndex K b) : IsProbabilityMeasure (μ c) := by
    unfold μ
    letI : IsProbabilityMeasure (expMeasure 1) :=
      isProbabilityMeasure_expMeasure zero_lt_one
    exact Measure.isProbabilityMeasure_map
      (measurable_const.add measurable_id).aemeasurable
  have hν (c : losingIndex K b) : IsProbabilityMeasure (ν c) := by
    unfold ν
    exact isProbabilityMeasure_expMeasure zero_lt_one
  change klDiv (Measure.pi μ) (Measure.pi ν) ≠ ⊤
  rw [klDiv_pi_eq_sum μ ν hμ hν]
  exact ENNReal.sum_ne_top.mpr fun c _ =>
    shifted_exp_klDiv_ne_top (hshift c)

private lemma losingClockLaw_isProbability_all {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D) (b : K.κ) (z : α × β)
    (u : ℝ) : IsProbabilityMeasure (losingClockLaw K b z u) := by
  letI : IsProbabilityMeasure (expMeasure 1) :=
    isProbabilityMeasure_expMeasure zero_lt_one
  letI (c : losingIndex K b) : IsProbabilityMeasure
      ((expMeasure 1).map
        (fun e => u * (K.sigma c.1 z / K.sigma b z) + e)) := by
    exact Measure.isProbabilityMeasure_map
      (measurable_const.add measurable_id).aemeasurable
  unfold losingClockLaw
  infer_instance

private lemma losingReference_isProbability {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D) (b : K.κ) :
    IsProbabilityMeasure (losingReference K b) := by
  letI : IsProbabilityMeasure (expMeasure 1) :=
    isProbabilityMeasure_expMeasure zero_lt_one
  unfold losingReference
  infer_instance

private lemma losingClockMarginal_isProbability {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D) (g b : K.κ) (u : ℝ) :
    IsProbabilityMeasure (losingClockMarginal K g b u) := by
  letI (z : α × β) : IsProbabilityMeasure (losingClockLaw K b z u) :=
    losingClockLaw_isProbability_all K b z u
  constructor
  unfold losingClockMarginal
  rw [show (∑ z, ENNReal.ofReal (coneSource K g b u z) •
      losingClockLaw K b z u) Set.univ =
      ∑ z, (ENNReal.ofReal (coneSource K g b u z) •
        losingClockLaw K b z u) Set.univ by simp]
  simp only [Measure.smul_apply, smul_eq_mul, measure_univ, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg
    (fun z _ => (coneSource_isPMF K g b u).nonneg z)]
  have htotal : ∑ z, coneSource K g b u z = 1 := by
    simpa [mass] using (coneSource_isPMF K g b u).total
  rw [htotal]
  norm_num

/-- Step 2, stated against `losingClockMarginal`, the true conditional
mixture.  This is the golden formula with its nonnegative marginal-reference
KL discarded. -/
private theorem cone_true_mixture_golden {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D) (g b : K.κ)
    (u : ℝ) (hu : 0 ≤ u) :
    coneContextInfoNats K g b u ≤
      ∑ z, coneSource K g b u z *
        (klDiv (losingClockLaw K b z u) (losingReference K b)).toReal := by
  unfold coneContextInfoNats
  apply finite_mixture_golden_le
      (coneSource K g b u)
      (fun z => losingClockLaw K b z u)
      (losingClockMarginal K g b u) (losingReference K b)
      (coneSource_isPMF K g b u)
      (fun z => losingClockLaw_isProbability_all K b z u)
      (losingClockMarginal_isProbability K g b u)
      (losingReference_isProbability K b)
      rfl
  · intro z hz
    exact losingClock_klDiv_ne_top K g b u z hz
  · intro z hz
    have hQne : K.Q g z ≠ 0 := by
      intro hQ
      apply hz.ne'
      unfold coneSource
      simp [hQ]
    have hzSupp : z ∈ support p := by
      by_contra hsupp
      exact hQne ((K.Q_isContact g).2.1 z hsupp)
    exact losingReference_klDiv_ne_top K b z hzSupp u hu

/-- Combining the product KL with the golden formula gives (10.2). -/
private theorem cone_context_bound {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D) (g b : K.κ)
    (u : ℝ) (hu : 0 ≤ u) :
    coneContextInfoNats K g b u ≤
      ∑ z, coneSource K g b u z *
        (u * (1 / K.sigma b z - 1)) := by
  calc
    coneContextInfoNats K g b u ≤
        ∑ z, coneSource K g b u z *
          (klDiv (losingClockLaw K b z u) (losingReference K b)).toReal :=
      cone_true_mixture_golden K g b u hu
    _ = ∑ z, coneSource K g b u z *
        (u * (1 / K.sigma b z - 1)) := by
      apply Finset.sum_congr rfl
      intro z _
      by_cases hz : z ∈ support p
      · rw [losing_product_klDiv K b z hz u hu]
      · have hQ : K.Q g z = 0 := (K.Q_isContact g).2.1 z hz
        simp [coneSource, hQ]

/-- The finite mismatch charge appearing after the `u` integral has been
evaluated. -/
private noncomputable def coneCharge {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D) : ℝ :=
  ∑ g, K.s g * ∑ z, K.Q g z * (1 - ∑ b, K.sigma b z ^ 2)

private theorem cluster_mixture {p : α × β → ℝ} {D : SeedSetup p}
    (K : Clustering D) (z : α × β) :
    ∑ g, K.s g * K.Q g z = p z := by
  have hfiber (g : K.κ) :
      K.s g * K.Q g z =
        ∑ ℓ ∈ univ.filter (fun ℓ => K.cl ℓ = g),
          D.L.prior ℓ * D.L.comp ℓ z := by
    unfold Clustering.s Clustering.Q
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro ℓ hℓ
    have hcl : K.cl ℓ =
        K.cl (Classical.choose (K.surj g)) := by
      exact (Finset.mem_filter.mp hℓ).2.trans
        (Classical.choose_spec (K.surj g)).symm
    have hcomp : D.L.comp ℓ =
        D.L.comp (Classical.choose (K.surj g)) :=
      (K.spec _ _).mp hcl
    rw [hcomp]
  calc
    (∑ g, K.s g * K.Q g z) =
        ∑ g, ∑ ℓ ∈ univ.filter (fun ℓ => K.cl ℓ = g),
          D.L.prior ℓ * D.L.comp ℓ z := by
      apply Finset.sum_congr rfl
      intro g _
      exact hfiber g
    _ = ∑ ℓ, D.L.prior ℓ * D.L.comp ℓ z := by
      simpa using Finset.sum_fiberwise (univ : Finset D.L.ι) K.cl
        (fun ℓ => D.L.prior ℓ * D.L.comp ℓ z)
    _ = p z := D.L.mixture z

private theorem cluster_weight_eq {p : α × β → ℝ} {D : SeedSetup p}
    (K : Clustering D) (g : K.κ) (z : α × β) :
    K.s g * K.Q g z = p z * K.sigma g z := by
  exact clusterWeight_eq_pSigma K g z

/-- Step 3: integrate the exact joint density using `exp_integral_sq`; the
factor `s²(1/s-1)` becomes `s-s²` before summing over `b`. -/
private theorem integratedConeNats_le_charge {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D) :
    integratedConeNats K ≤ coneCharge K := by
  have hterm (g b : K.κ) (z : α × β) :
      IntegrableOn
        (fun u : ℝ => K.Q g z * Real.exp (-u / K.sigma b z) *
          (u * (1 / K.sigma b z - 1))) (Set.Ioi 0) := by
    by_cases hz : z ∈ support p
    · have hs := K.sigma_pos b z hz
      have hbase : IntegrableOn
          (fun u : ℝ => u * Real.exp (-u / K.sigma b z))
          (Set.Ioi 0) :=
        .of_integral_ne_zero (by rw [exp_integral_sq hs]; positivity)
      have hscaled := hbase.const_mul
        (K.Q g z * (1 / K.sigma b z - 1))
      exact hscaled.congr (Filter.Eventually.of_forall fun u => by ring)
    · have hQ : K.Q g z = 0 := (K.Q_isContact g).2.1 z hz
      simp [hQ]
  have hcontext (g b : K.κ) :
      (∫ u in Set.Ioi (0 : ℝ),
          coneContextDensity K g b u * coneContextInfoNats K g b u) ≤
        ∑ z, K.Q g z * (K.sigma b z - K.sigma b z ^ 2) := by
    let upper : ℝ → ℝ := fun u =>
      ∑ z, K.Q g z * Real.exp (-u / K.sigma b z) *
        (u * (1 / K.sigma b z - 1))
    have hupper : IntegrableOn upper (Set.Ioi 0) := by
      dsimp only [upper]
      exact integrable_finsetSum univ fun z _ => hterm g b z
    have hpoint (u : ℝ) (hu : 0 ≤ u) :
        coneContextDensity K g b u * coneContextInfoNats K g b u ≤
          upper u := by
      calc
        coneContextDensity K g b u * coneContextInfoNats K g b u ≤
            coneContextDensity K g b u *
              (∑ z, coneSource K g b u z *
                (u * (1 / K.sigma b z - 1))) :=
          mul_le_mul_of_nonneg_left (cone_context_bound K g b u hu)
            (coneContextDensity_pos K g b u).le
        _ = upper u := by
          dsimp only [upper]
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro z _
          unfold coneSource
          field_simp [(coneContextDensity_pos K g b u).ne']
    calc
      (∫ u in Set.Ioi (0 : ℝ),
          coneContextDensity K g b u * coneContextInfoNats K g b u) ≤
          ∫ u in Set.Ioi (0 : ℝ), upper u := by
        apply integral_mono_of_nonneg
        · exact Filter.Eventually.of_forall fun u => mul_nonneg
            (coneContextDensity_pos K g b u).le
            (coneContextInfoNats_nonneg K g b u)
        · exact hupper
        · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
          exact hpoint u hu.le
      _ = ∑ z, K.Q g z * (K.sigma b z - K.sigma b z ^ 2) := by
        dsimp only [upper]
        rw [integral_finsetSum univ]
        · apply Finset.sum_congr rfl
          intro z _
          by_cases hz : z ∈ support p
          · have hs := K.sigma_pos b z hz
            calc
              (∫ u in Set.Ioi (0 : ℝ),
                  K.Q g z * Real.exp (-u / K.sigma b z) *
                    (u * (1 / K.sigma b z - 1))) =
                  (K.Q g z * (1 / K.sigma b z - 1)) *
                    ∫ u in Set.Ioi (0 : ℝ),
                      u * Real.exp (-u / K.sigma b z) := by
                rw [← integral_const_mul]
                apply setIntegral_congr_fun measurableSet_Ioi
                intro u _
                ring
              _ = (K.Q g z * (1 / K.sigma b z - 1)) *
                    K.sigma b z ^ 2 := by
                rw [exp_integral_sq hs]
              _ = K.Q g z * (K.sigma b z - K.sigma b z ^ 2) := by
                field_simp [hs.ne']
                <;> ring
          · have hQ : K.Q g z = 0 := (K.Q_isContact g).2.1 z hz
            simp [hQ]
        · exact fun z _ => hterm g b z
  unfold integratedConeNats coneCharge
  apply Finset.sum_le_sum
  intro g _
  apply mul_le_mul_of_nonneg_left _ (clusterMass_nonneg K g)
  calc
    (∑ b, ∫ u in Set.Ioi (0 : ℝ),
        coneContextDensity K g b u * coneContextInfoNats K g b u) ≤
        ∑ b, ∑ z,
          K.Q g z * (K.sigma b z - K.sigma b z ^ 2) :=
      Finset.sum_le_sum fun b _ => hcontext g b
    _ = ∑ z, K.Q g z * (1 - ∑ b, K.sigma b z ^ 2) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro z _
      by_cases hz : z ∈ support p
      · have hsum := raceSigma_sum_eq_one K z hz
        rw [← Finset.mul_sum, Finset.sum_sub_distrib, hsum]
      · have hQ : K.Q g z = 0 := (K.Q_isContact g).2.1 z hz
        simp [hQ]

/-- The cluster mixture reconstructs `p`, after which `K.dMis_eq` is exactly
the charge produced by the cone integral. -/
private theorem coneCharge_eq_dMis {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D) :
    coneCharge K = K.dMis := by
  calc
    coneCharge K =
        ∑ z, (∑ g, K.s g * K.Q g z) *
          (1 - ∑ b, K.sigma b z ^ 2) := by
      unfold coneCharge
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro z _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro g _
      ring
    _ = ∑ z, p z * (1 - ∑ b, K.sigma b z ^ 2) := by
      apply Finset.sum_congr rfl
      intro z _
      rw [cluster_mixture K z]
    _ = K.dMis := K.dMis_eq.symm

private noncomputable def clusterClockSplit {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D) (b : K.κ) :
    (K.κ → ℝ) → ℝ × (losingIndex K b → ℝ) :=
  fun G => (Real.exp (-G b), fun c => Real.exp (-G c.1))

private noncomputable def clusterClockJoin {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D) (b : K.κ) :
    (ℝ × (losingIndex K b → ℝ)) → K.κ → ℝ :=
  fun uv c => if h : c = b then -Real.log uv.1 else -Real.log (uv.2 ⟨c, h⟩)

private lemma clusterClockSplit_measurable {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D) (b : K.κ) :
    Measurable (clusterClockSplit K b) := by
  apply Measurable.prodMk
  · exact Real.measurable_exp.comp (measurable_pi_apply b).neg
  · apply measurable_pi_lambda
    intro c
    exact Real.measurable_exp.comp (measurable_pi_apply c.1).neg

private lemma clusterClockJoin_measurable {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D) (b : K.κ) :
    Measurable (clusterClockJoin K b) := by
  apply measurable_pi_lambda
  intro c
  by_cases h : c = b
  · simp only [clusterClockJoin, h, dite_true]
    fun_prop
  · simp only [clusterClockJoin, h, dite_false]
    fun_prop

private lemma clusterClockJoin_split {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D) (b : K.κ) (G : K.κ → ℝ) :
    clusterClockJoin K b (clusterClockSplit K b G) = G := by
  funext c
  by_cases h : c = b
  · subst c
    simp [clusterClockJoin, clusterClockSplit]
  · simp [clusterClockJoin, clusterClockSplit, h]

private noncomputable def raceLosingKernel {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D) (b : K.κ) (z : α × β) :
    Kernel ℝ (losingIndex K b → ℝ) :=
  ((Kernel.id : Kernel ℝ ℝ).prod
      (Kernel.const ℝ (losingReference K b))).map
    (fun ue c => ue.1 * (K.sigma c.1 z / K.sigma b z) + ue.2 c)

private lemma raceLosingKernel_apply {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D) (b : K.κ) (z : α × β) (u : ℝ) :
    raceLosingKernel K b z u = losingClockLaw K b z u := by
  letI : IsProbabilityMeasure (expMeasure 1) :=
    isProbabilityMeasure_expMeasure zero_lt_one
  letI : IsProbabilityMeasure (losingReference K b) := by
    unfold losingReference
    infer_instance
  let r : losingIndex K b → ℝ := fun c =>
    K.sigma c.1 z / K.sigma b z
  change
    (((Kernel.id : Kernel ℝ ℝ).prod
        (Kernel.const ℝ (Measure.pi fun _ : losingIndex K b => expMeasure 1))).map
      (fun ue c => ue.1 * r c + ue.2 c)) u =
      Measure.pi fun c : losingIndex K b =>
        (expMeasure 1).map (fun e => u * r c + e)
  rw [Kernel.map_apply _ (by fun_prop), Kernel.prod_apply,
    Kernel.id_apply, Kernel.const_apply, Measure.dirac_prod,
    Measure.map_map (by fun_prop) (by fun_prop)]
  change Measure.map (fun x c => u * r c + x c)
      (Measure.pi fun _ : losingIndex K b => expMeasure 1) = _
  rw [Measure.pi_map_pi fun c => (by fun_prop :
    AEMeasurable
      (fun e : ℝ => u * r c + e)
      (expMeasure 1))]

private lemma raceLosingKernel_isMarkov {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D) (b : K.κ) (z : α × β) :
    IsMarkovKernel (raceLosingKernel K b z) := by
  refine ⟨fun u => ?_⟩
  rw [raceLosingKernel_apply K b z u]
  exact losingClockLaw_isProbability_all K b z u

private lemma coneSource_measurable {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D) (g b : K.κ) (z : α × β) :
    Measurable (fun u => coneSource K g b u z) := by
  unfold coneSource coneContextDensity
  fun_prop

private noncomputable def raceContextKernel {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D) (g b : K.κ) :
    Kernel ℝ (losingIndex K b → ℝ) :=
  letI (z : α × β) : IsMarkovKernel (raceLosingKernel K b z) :=
    raceLosingKernel_isMarkov K b z
  Kernel.sum fun z =>
    (raceLosingKernel K b z).withDensity
      (fun u _ => ENNReal.ofReal (coneSource K g b u z))

private lemma raceContextKernel_apply {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D) (g b : K.κ) (u : ℝ) :
    raceContextKernel K g b u = losingClockMarginal K g b u := by
  letI (z : α × β) : IsMarkovKernel (raceLosingKernel K b z) :=
    raceLosingKernel_isMarkov K b z
  unfold raceContextKernel losingClockMarginal
  rw [Kernel.sum_apply, Measure.sum_fintype]
  apply Finset.sum_congr rfl
  intro z _
  have hweight : Measurable (Function.uncurry
      (fun u (_ : losingIndex K b → ℝ) =>
        ENNReal.ofReal (coneSource K g b u z))) :=
    ENNReal.measurable_ofReal.comp
      ((coneSource_measurable K g b z).comp measurable_fst)
  rw [Kernel.withDensity_apply _ hweight, withDensity_const,
    raceLosingKernel_apply]

private lemma raceContextKernel_isMarkov {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D) (g b : K.κ) :
    IsMarkovKernel (raceContextKernel K g b) := by
  refine ⟨fun u => ?_⟩
  rw [raceContextKernel_apply K g b u]
  exact losingClockMarginal_isProbability K g b u

private lemma weightedWinner_clock_restrict_map
    {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (t : κ → ℝ) (ht : ∀ i, 0 < t i) (a : κ) :
    Measure.map (fun G : κ → ℝ => fun i => Real.exp (-G i))
        ((seedLaw κ).restrict {G | weightedWinner t G = a}) =
      (clockLaw κ).restrict {E | strictClockWin t a E} := by
  letI : MeasurableSpace κ := ⊤
  letI : IsProbabilityMeasure (expMeasure 1) :=
    isProbabilityMeasure_expMeasure zero_lt_one
  letI : ∀ _ : κ, SigmaFinite (expMeasure 1) := fun _ => inferInstance
  let F : (κ → ℝ) → (κ → ℝ) := fun E i => -Real.log (E i)
  let C : (κ → ℝ) → (κ → ℝ) := fun G i => Real.exp (-G i)
  have hF : Measurable F := measurable_pi_lambda _ fun i =>
    (Real.measurable_log.comp (measurable_pi_apply i)).neg
  have hC : Measurable C := measurable_pi_lambda _ fun i =>
    Real.measurable_exp.comp (measurable_pi_apply i).neg
  have hlex : Measurable (fun G => weightedLexWinner t G) := by
    unfold weightedLexWinner
    apply measurable_lexMax
    intro i
    exact measurable_const.add (measurable_pi_apply i)
  have hlexSet : MeasurableSet {G | weightedLexWinner t G = a} :=
    measurableSet_singleton a |>.preimage hlex
  have hwinnerLex :
      {G | weightedWinner t G = a} =ᵐ[seedLaw κ]
        {G | weightedLexWinner t G = a} := by
    filter_upwards [weightedWinner_ae_eq_lex t] with G hG
    apply propext
    change (weightedWinner t G = a ↔ weightedLexWinner t G = a)
    rw [hG]
  have hone : ∀ᵐ x : ℝ ∂(expMeasure 1), 0 < x := by
    have hnot := measure_eq_zero_iff_ae_notMem.mp expMeasure_one_Iic_zero
    filter_upwards [hnot] with x hx
    simpa only [Set.mem_Iic, not_le] using hx
  have hpos : ∀ᵐ E ∂(clockLaw κ), ∀ i, 0 < E i := by
    unfold clockLaw
    exact ae_forall_fintype fun i =>
      Measure.tendsto_eval_ae_ae.eventually hone
  have htieSeed := weighted_ae_no_ties t
  change ∀ᵐ G ∂((clockLaw κ).map F), ∀ i j, i ≠ j →
    weightedValue t G i ≠ weightedValue t G j at htieSeed
  have htieClock : ∀ᵐ E ∂(clockLaw κ), ∀ i j, i ≠ j →
      weightedValue t (F E) i ≠ weightedValue t (F E) j :=
    ae_of_ae_map hF.aemeasurable htieSeed
  have hpre :
      F ⁻¹' {G | weightedLexWinner t G = a} =ᵐ[clockLaw κ]
        {E | strictClockWin t a E} := by
    filter_upwards [hpos, htieClock] with E hE htie
    apply propext
    change (weightedLexWinner t (F E) = a ↔ strictClockWin t a E)
    exact weightedLexWinner_clock_iff t ht E hE a
      (fun i hia => htie i a hia)
  have hseedClock :
      (seedLaw κ).restrict {G | weightedLexWinner t G = a} =
        Measure.map F ((clockLaw κ).restrict {E | strictClockWin t a E}) := by
    unfold seedLaw
    rw [Measure.restrict_map hF hlexSet,
      Measure.restrict_congr_set hpre]
  have hCF : C ∘ F =ᵐ[(clockLaw κ).restrict {E | strictClockWin t a E}] id := by
    filter_upwards [ae_restrict_of_ae hpos] with E hE
    funext i
    dsimp only [C, F, Function.comp_apply, id_eq]
    rw [neg_neg, Real.exp_log (hE i)]
  calc
    Measure.map C ((seedLaw κ).restrict {G | weightedWinner t G = a}) =
        Measure.map C
          ((seedLaw κ).restrict {G | weightedLexWinner t G = a}) := by
      rw [Measure.restrict_congr_set hwinnerLex]
    _ = Measure.map C
        (Measure.map F
          ((clockLaw κ).restrict {E | strictClockWin t a E})) := by
      rw [hseedClock]
    _ = Measure.map (C ∘ F)
        ((clockLaw κ).restrict {E | strictClockWin t a E}) :=
      Measure.map_map hC hF
    _ = Measure.map id
        ((clockLaw κ).restrict {E | strictClockWin t a E}) :=
      Measure.map_congr hCF
    _ = (clockLaw κ).restrict {E | strictClockWin t a E} :=
      Measure.map_id

private lemma map_mul_expMeasure {t : ℝ} (ht : 0 < t) :
    Measure.map (fun x : ℝ => t * x) (expMeasure t) = expMeasure 1 := by
  simpa [div_eq_mul_inv, ht.ne', mul_comm] using
    (map_div_expMeasure (t := 1 / t) (one_div_pos.mpr ht))

private lemma map_weightedLosingExcess_scale
    {κ : Type} [Fintype κ] [DecidableEq κ]
    (t : κ → ℝ) (ht : ∀ i, 0 < t i) (a : κ) :
    Measure.map
        (fun R : {i : κ // i ≠ a} → ℝ => fun i => t i.1 * R i)
        (weightedLosingExcessLaw t a) =
      Measure.pi fun _ : {i : κ // i ≠ a} => expMeasure 1 := by
  letI (i : {i : κ // i ≠ a}) : IsProbabilityMeasure (expMeasure (t i.1)) :=
    isProbabilityMeasure_expMeasure (ht i.1)
  let r : {i : κ // i ≠ a} → ℝ := fun i => t i.1
  unfold weightedLosingExcessLaw
  change Measure.map (fun R i => r i * R i)
      (Measure.pi fun i : {i : κ // i ≠ a} => expMeasure (r i)) = _
  rw [Measure.pi_map_pi fun i => (by fun_prop :
    AEMeasurable (fun x : ℝ => r i * x) (expMeasure (r i)))]
  congr 1
  funext i
  exact map_mul_expMeasure (ht i.1)

/-- Reassemble a distinguished clock and the remaining coordinates into one
full clock vector. -/
private noncomputable def winnerClockJoin
    {κ : Type} [DecidableEq κ] (a : κ)
    (sr : ℝ × ({i : κ // i ≠ a} → ℝ)) : κ → ℝ :=
  fun i => if h : i = a then sr.1 else sr.2 ⟨i, h⟩

private lemma winnerClockJoin_measurable
    {κ : Type} [Fintype κ] [DecidableEq κ] (a : κ) :
    Measurable (winnerClockJoin a) := by
  apply measurable_pi_lambda
  intro i
  by_cases hi : i = a
  · simp only [winnerClockJoin, hi, dite_true]
    exact measurable_fst
  · simp only [winnerClockJoin, hi, dite_false]
    exact (measurable_pi_apply (⟨i, hi⟩ : {j : κ // j ≠ a})).comp measurable_snd

/-- A fresh distinguished `Exp(1)` clock together with fresh iid losing
clocks is just the original iid clock vector. -/
private lemma winnerClockJoin_law
    {κ : Type} [Fintype κ] [DecidableEq κ] (a : κ) :
    Measure.map (winnerClockJoin a)
        ((expMeasure 1).prod
          (Measure.pi fun _ : {i : κ // i ≠ a} => expMeasure 1)) =
      clockLaw κ := by
  letI : IsProbabilityMeasure (expMeasure 1) :=
    isProbabilityMeasure_expMeasure zero_lt_one
  let loseμ : Measure ({i : κ // i ≠ a} → ℝ) :=
    Measure.pi fun _ : {i : κ // i ≠ a} => expMeasure 1
  letI : IsProbabilityMeasure loseμ := by
    dsimp [loseμ]
    infer_instance
  let e : Option {i : κ // i ≠ a} ≃ κ := Equiv.optionSubtypeNe a
  let f := (MeasurableEquiv.piOptionEquivProd
    (fun _ : Option {i : κ // i ≠ a} => ℝ)).symm
  let g := MeasurableEquiv.piCongrLeft (fun _ : κ => ℝ) e
  let q := loseμ.prod (expMeasure 1)
  have hfirst :
      Measure.map f q =
        Measure.pi (fun _ : Option {i : κ // i ≠ a} => expMeasure 1) := by
    dsimp [f, q, loseμ]
    exact Measure.pi_map_piOptionEquivProd
      (fun _ : Option {i : κ // i ≠ a} => expMeasure 1)
  have hsecond :
      Measure.map g
          (Measure.pi (fun _ : Option {i : κ // i ≠ a} => expMeasure 1)) =
        Measure.pi (fun _ : κ => expMeasure 1) := by
    dsimp [g]
    simpa [e] using Measure.pi_map_piCongrLeft e
      (fun _ : κ => expMeasure 1)
  have hmap : Measure.map (g ∘ f) q = clockLaw κ := by
    unfold clockLaw
    calc
      Measure.map (g ∘ f) q = Measure.map g (Measure.map f q) :=
        (Measure.map_map g.measurable f.measurable).symm
      _ = _ := by rw [hfirst, hsecond]
  have hjoinSwap : winnerClockJoin a ∘ Prod.swap = g ∘ f := by
    funext xy i
    have hfPair := (MeasurableEquiv.piOptionEquivProd
      (fun _ : Option {j : κ // j ≠ a} => ℝ)).apply_symm_apply xy
    by_cases hi : i = a
    · subst i
      have hfNone : f xy none = xy.2 := congrArg Prod.snd hfPair
      dsimp only [Function.comp_apply, winnerClockJoin]
      simp only [dite_true]
      dsimp [g]
      rw [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]
      simp [e, hfNone]
    · have hfSome : f xy (some ⟨i, hi⟩) = xy.1 ⟨i, hi⟩ :=
        congrFun (congrArg Prod.fst hfPair) ⟨i, hi⟩
      dsimp only [Function.comp_apply, winnerClockJoin]
      simp only [hi, dite_false]
      dsimp [g]
      rw [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]
      simp [e, Equiv.optionSubtypeNe_symm_of_ne hi, hfSome]
  change Measure.map (winnerClockJoin a) ((expMeasure 1).prod loseμ) = _
  calc
    Measure.map (winnerClockJoin a) ((expMeasure 1).prod loseμ) =
        Measure.map (winnerClockJoin a) (Measure.map Prod.swap q) := by
      rw [Measure.prod_swap]
    _ = Measure.map (winnerClockJoin a ∘ Prod.swap) q :=
      Measure.map_map (winnerClockJoin_measurable a) measurable_swap
    _ = Measure.map (g ∘ f) q := by rw [hjoinSwap]
    _ = clockLaw κ := hmap

/-- On the cell where `a` wins, remove the common weighted-race minimum from
every losing raw clock and retain that minimum in coordinate `a`. -/
private noncomputable def winnerResidualClock
    {κ : Type} [DecidableEq κ] (t : κ → ℝ) (a : κ)
    (E : κ → ℝ) : κ → ℝ :=
  fun i => if _h : i = a then E a / t a else E i - t i * (E a / t a)

private lemma winnerResidualClock_measurable
    {κ : Type} [Fintype κ] [DecidableEq κ]
    (t : κ → ℝ) (a : κ) :
    Measurable (winnerResidualClock t a) := by
  have hea : Measurable (fun E : κ → ℝ => E a) := measurable_pi_apply a
  have hratio : Measurable (fun E : κ → ℝ => E a / t a) :=
    hea.div measurable_const
  apply measurable_pi_lambda
  intro i
  by_cases hi : i = a
  · simpa only [winnerResidualClock, hi, dite_true] using hratio
  · have hei : Measurable (fun E : κ → ℝ => E i) := measurable_pi_apply i
    have hmul : Measurable (fun E : κ → ℝ => t i * (E a / t a)) := by
      fun_prop
    simp only [winnerResidualClock, hi, dite_false]
    exact hei.sub hmul

/-- Fixed-winner exponential memorylessness in full-vector form.  The
residual vector consists of fresh iid `Exp(1)` clocks, with total mass equal
to the probability `t a` of the winner cell. -/
private theorem winnerResidualClock_restrict_law
    {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (t : κ → ℝ) (ht : ∀ i, 0 < t i) (htotal : ∑ i, t i = 1)
    (a : κ) :
    Measure.map (winnerResidualClock t a)
        ((clockLaw κ).restrict {E | strictClockWin t a E}) =
      ENNReal.ofReal (t a) • clockLaw κ := by
  let ρ : Measure ({i : κ // i ≠ a} → ℝ) :=
    weightedLosingExcessLaw t a
  let loseμ : Measure ({i : κ // i ≠ a} → ℝ) :=
    Measure.pi fun _ : {i : κ // i ≠ a} => expMeasure 1
  let A : Measure ℝ := ENNReal.ofReal (t a) • expMeasure 1
  let embed : ({i : κ // i ≠ a} → ℝ) → κ → ℝ := insertWinnerZero a
  let norm : (κ → ℝ) → ℝ × (κ → ℝ) := fun E =>
    (E a / t a, fun i => E i / t i - E a / t a)
  let out : (ℝ × (κ → ℝ)) → κ → ℝ := fun sr i =>
    if i = a then sr.1 else t i * sr.2 i
  let assemble : (ℝ × ({i : κ // i ≠ a} → ℝ)) → κ → ℝ := fun sr i =>
    if h : i = a then sr.1 else t i * sr.2 ⟨i, h⟩
  let loseScale : ({i : κ // i ≠ a} → ℝ) →
      ({i : κ // i ≠ a} → ℝ) := fun R i => t i.1 * R i
  let scale : (ℝ × ({i : κ // i ≠ a} → ℝ)) →
      ℝ × ({i : κ // i ≠ a} → ℝ) := Prod.map id loseScale
  have hnorm : Measurable norm := by fun_prop
  have hout : Measurable out := by
    apply measurable_pi_lambda
    intro i
    by_cases hi : i = a
    · simpa only [out, hi, if_true] using
        (measurable_fst : Measurable
          (fun sr : ℝ × (κ → ℝ) => sr.1))
    · have hcoord : Measurable
          (fun sr : ℝ × (κ → ℝ) => sr.2 i) :=
        (measurable_pi_apply i).comp measurable_snd
      have hmul : Measurable (fun sr : ℝ × (κ → ℝ) => t i * sr.2 i) := by
        fun_prop
      simpa only [out, hi, if_false] using hmul
  have hembed : Measurable embed := insertWinnerZero_measurable a
  have hassemble : Measurable assemble := by
    apply measurable_pi_lambda
    intro i
    by_cases hi : i = a
    · simpa only [assemble, hi, dite_true] using
        (measurable_fst : Measurable
          (fun sr : ℝ × ({j : κ // j ≠ a} → ℝ) => sr.1))
    · have hcoord : Measurable
          (fun sr : ℝ × ({j : κ // j ≠ a} → ℝ) => sr.2 ⟨i, hi⟩) :=
        (measurable_pi_apply (⟨i, hi⟩ : {j : κ // j ≠ a})).comp measurable_snd
      have hmul : Measurable
          (fun sr : ℝ × ({j : κ // j ≠ a} → ℝ) => t i * sr.2 ⟨i, hi⟩) := by
        fun_prop
      simpa only [assemble, hi, dite_false] using hmul
  have hloseScale : Measurable loseScale := by fun_prop
  have hscale : Measurable scale := measurable_id.prodMap hloseScale
  have hresidualNorm : winnerResidualClock t a = out ∘ norm := by
    funext E i
    by_cases hi : i = a
    · subst i
      simp [winnerResidualClock, out, norm]
    · simp only [winnerResidualClock, hi, dite_false, Function.comp_apply,
        out, norm, if_false]
      field_simp [(ht i).ne', (ht a).ne']
  have houtEmbed : out ∘ Prod.map id embed = assemble := by
    funext sr i
    by_cases hi : i = a
    · subst i
      simp [out, assemble]
    · simp [out, assemble, embed, insertWinnerZero, hi]
  have hassembleScale : assemble = winnerClockJoin a ∘ scale := by
    funext sr i
    by_cases hi : i = a
    · subst i
      simp [assemble, winnerClockJoin, scale]
    · simp [assemble, winnerClockJoin, scale, loseScale, hi]
  letI : IsProbabilityMeasure (expMeasure 1) :=
    isProbabilityMeasure_expMeasure zero_lt_one
  letI (i : {i : κ // i ≠ a}) : IsProbabilityMeasure
      (expMeasure (t i.1)) := isProbabilityMeasure_expMeasure (ht i.1)
  letI : IsProbabilityMeasure ρ := by
    dsimp [ρ, weightedLosingExcessLaw]
    infer_instance
  letI : IsProbabilityMeasure loseμ := by
    dsimp [loseμ]
    infer_instance
  letI : SFinite A := by
    dsimp [A]
    infer_instance
  have hscaleLaw : Measure.map scale (A.prod ρ) = A.prod loseμ := by
    calc
      Measure.map scale (A.prod ρ) =
          (Measure.map id A).prod (Measure.map loseScale ρ) := by
        exact (Measure.map_prod_map A ρ measurable_id hloseScale).symm
      _ = A.prod loseμ := by
        rw [Measure.map_id]
        congr 1
        dsimp only [loseScale, ρ, loseμ]
        exact map_weightedLosingExcess_scale t ht a
  have hAprod : A.prod loseμ =
      ENNReal.ofReal (t a) • ((expMeasure 1).prod loseμ) := by
    dsimp only [A]
    rw [Measure.prod_smul_left]
  calc
    Measure.map (winnerResidualClock t a)
        ((clockLaw κ).restrict {E | strictClockWin t a E}) =
        Measure.map out
          (Measure.map norm
            ((clockLaw κ).restrict {E | strictClockWin t a E})) := by
      rw [hresidualNorm]
      exact (Measure.map_map hout hnorm).symm
    _ = Measure.map out
        (A.prod (Measure.map embed ρ)) := by
      rw [clock_min_excess_restrict_factorization t ht htotal a]
    _ = Measure.map assemble (A.prod ρ) := by
      calc
        Measure.map out (A.prod (Measure.map embed ρ)) =
            Measure.map out ((Measure.map id A).prod (Measure.map embed ρ)) := by
          rw [Measure.map_id]
        _ = Measure.map out
            (Measure.map (Prod.map id embed) (A.prod ρ)) := by
          rw [← Measure.map_prod_map A ρ measurable_id hembed]
        _ = Measure.map (out ∘ Prod.map id embed) (A.prod ρ) :=
          Measure.map_map hout (measurable_id.prodMap hembed)
        _ = Measure.map assemble (A.prod ρ) := by rw [houtEmbed]
    _ = Measure.map (winnerClockJoin a) (Measure.map scale (A.prod ρ)) := by
      rw [hassembleScale]
      exact (Measure.map_map (winnerClockJoin_measurable a) hscale).symm
    _ = Measure.map (winnerClockJoin a) (A.prod loseμ) := by
      rw [hscaleLaw]
    _ = Measure.map (winnerClockJoin a)
        (ENNReal.ofReal (t a) • ((expMeasure 1).prod loseμ)) := by
      rw [hAprod]
    _ = ENNReal.ofReal (t a) •
        Measure.map (winnerClockJoin a) ((expMeasure 1).prod loseμ) := by
      rw [Measure.map_smul]
    _ = ENNReal.ofReal (t a) • clockLaw κ := by
      rw [show Measure.map (winnerClockJoin a)
          ((expMeasure 1).prod loseμ) = clockLaw κ by
        dsimp only [loseμ]
        exact winnerClockJoin_law a]

@[simp] private lemma winnerResidualClock_apply_winner
    {κ : Type} [DecidableEq κ] (t : κ → ℝ) (a : κ) (E : κ → ℝ) :
    winnerResidualClock t a E a = E a / t a := by
  simp [winnerResidualClock]

private lemma winnerResidualClock_apply_loser
    {κ : Type} [DecidableEq κ] (t : κ → ℝ) (a i : κ)
    (hi : i ≠ a) (E : κ → ℝ) :
    winnerResidualClock t a E i = E i - t i * (E a / t a) := by
  simp [winnerResidualClock, hi]

/-- Raw-clock reconstruction from the fresh residual vector. -/
private lemma winnerResidualClock_reconstruct
    {κ : Type} [DecidableEq κ] (t : κ → ℝ) (ht : ∀ i, 0 < t i)
    (a i : κ) (E : κ → ℝ) :
    E i = t i * winnerResidualClock t a E a +
      if i = a then 0 else winnerResidualClock t a E i := by
  by_cases hi : i = a
  · subst i
    rw [winnerResidualClock_apply_winner]
    simp
    field_simp [(ht a).ne']
  · rw [winnerResidualClock_apply_winner,
      winnerResidualClock_apply_loser t a i hi E]
    simp [hi]

/-- The residual transformation preserves the total raw clock.  Hence every
simplex-normalized coordinate may use the same denominator before and after
conditioning on the winner. -/
private lemma sum_winnerResidualClock
    {κ : Type} [Fintype κ] [DecidableEq κ]
    (t : κ → ℝ) (ht : ∀ i, 0 < t i) (htotal : ∑ i, t i = 1)
    (a : κ) (E : κ → ℝ) :
    ∑ i, winnerResidualClock t a E i = ∑ i, E i := by
  let W : κ → ℝ := winnerResidualClock t a E
  let m : ℝ := E a / t a
  have hWwinner : W a = m := by
    dsimp only [W, m]
    exact winnerResidualClock_apply_winner t a E
  have hWloser (i : κ) (hi : i ∈ (univ : Finset κ).erase a) :
      W i = E i - t i * m := by
    have hne : i ≠ a := by
      simpa using (Finset.mem_erase.mp hi).1
    dsimp only [W, m]
    exact winnerResidualClock_apply_loser t a i hne E
  have htErase : (∑ i ∈ (univ : Finset κ).erase a, t i) = 1 - t a := by
    have h := Finset.sum_erase_add (univ : Finset κ) t (Finset.mem_univ a)
    rw [htotal] at h
    linarith
  have hEa : t a * m = E a := by
    dsimp only [m]
    field_simp [(ht a).ne']
  have hWErase := Finset.sum_erase_add (univ : Finset κ) W
    (Finset.mem_univ a)
  have hEErase := Finset.sum_erase_add (univ : Finset κ) E
    (Finset.mem_univ a)
  calc
    (∑ i, winnerResidualClock t a E i) =
        (∑ i ∈ (univ : Finset κ).erase a, W i) + W a := by
      change (∑ i, W i) = _
      exact hWErase.symm
    _ = (∑ i ∈ (univ : Finset κ).erase a, (E i - t i * m)) + m := by
      rw [hWwinner]
      apply congrArg (fun x : ℝ => x + m)
      apply Finset.sum_congr rfl
      exact hWloser
    _ = (∑ i ∈ (univ : Finset κ).erase a, E i) -
          (∑ i ∈ (univ : Finset κ).erase a, t i) * m + m := by
      rw [Finset.sum_sub_distrib, Finset.sum_mul]
    _ = (∑ i ∈ (univ : Finset κ).erase a, E i) + E a := by
      rw [htErase, ← hEa]
      ring
    _ = ∑ i, E i := hEErase

private lemma normalized_winner_eq_residual
    {κ : Type} [Fintype κ] [DecidableEq κ]
    (t : κ → ℝ) (ht : ∀ i, 0 < t i) (htotal : ∑ i, t i = 1)
    (a : κ) (E : κ → ℝ) :
    E a / (∑ i, E i) =
      t a * (winnerResidualClock t a E a /
        ∑ i, winnerResidualClock t a E i) := by
  have hEa : E a = t a * winnerResidualClock t a E a := by
    simpa using winnerResidualClock_reconstruct t ht a a E
  rw [hEa, ← sum_winnerResidualClock t ht htotal a E]
  ring

private lemma normalized_loser_eq_residual
    {κ : Type} [Fintype κ] [DecidableEq κ]
    (t : κ → ℝ) (ht : ∀ i, 0 < t i) (htotal : ∑ i, t i = 1)
    (a i : κ) (hi : i ≠ a) (E : κ → ℝ) :
    E i / (∑ j, E j) =
      (t i * winnerResidualClock t a E a + winnerResidualClock t a E i) /
        ∑ j, winnerResidualClock t a E j := by
  have hEi := winnerResidualClock_reconstruct t ht a i E
  simp only [hi, if_false] at hEi
  rw [hEi, ← sum_winnerResidualClock t ht htotal a E]

private lemma weighted_ratio_loser_eq_residual
    {κ : Type} [DecidableEq κ]
    (t : κ → ℝ) (ht : ∀ i, 0 < t i)
    (a i : κ) (hi : i ≠ a) (E : κ → ℝ) :
    (E a / t a) * t i / E i =
      t i * winnerResidualClock t a E a /
        (t i * winnerResidualClock t a E a + winnerResidualClock t a E i) := by
  have hEi := winnerResidualClock_reconstruct t ht a i E
  simp only [hi, if_false] at hEi
  rw [hEi, winnerResidualClock_apply_winner]
  ring

/-! ### Normalized clock moments on the fixed-winner cells -/

/-- A strict weighted-clock winner is also the lexicographic minimizer used
by the normalized shared-race quantities. Strictness makes the tie-break
irrelevant. -/
private lemma clockArgmin_eq_of_strictClockWin
    {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (t E : κ → ℝ) (a : κ) (ha : strictClockWin t a E) :
    SharedRace.clockArgmin t E = a := by
  by_contra hne
  have hmax := lexMax_max (fun E i => -(E i / t i)) E a
  have hstrict := ha (SharedRace.clockArgmin t E) hne
  change -(E a / t a) ≤
    -(E (SharedRace.clockArgmin t E) /
      t (SharedRace.clockArgmin t E)) at hmax
  linarith

private lemma rawRaceMin_eq_of_strictClockWin
    {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (t E : κ → ℝ) (a : κ) (ha : strictClockWin t a E) :
    SharedRace.rawRaceMin t E = E a / t a := by
  unfold SharedRace.rawRaceMin
  rw [clockArgmin_eq_of_strictClockWin t E a ha]

/-- On a fixed winner cell, the normalized race minimum is the normalized
winner coordinate of the fresh residual clock. -/
private lemma normRaceMin_eq_residual
    {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (t : κ → ℝ) (ht : ∀ i, 0 < t i) (htotal : ∑ i, t i = 1)
    (a : κ) (E : κ → ℝ) (ha : strictClockWin t a E) :
    SharedRace.normRaceMin t E =
      SharedRace.normClock (winnerResidualClock t a E) a := by
  unfold SharedRace.normRaceMin SharedRace.normClock SharedRace.clockTotal
  rw [rawRaceMin_eq_of_strictClockWin t E a ha,
    winnerResidualClock_apply_winner,
    sum_winnerResidualClock t ht htotal a E]

/-- The original winning normalized coordinate is its prior mass times the
fresh residual normalized coordinate. -/
private lemma normClock_winner_eq_residual
    {κ : Type} [Fintype κ] [DecidableEq κ]
    (t : κ → ℝ) (ht : ∀ i, 0 < t i) (htotal : ∑ i, t i = 1)
    (a : κ) (E : κ → ℝ) :
    SharedRace.normClock E a =
      t a * SharedRace.normClock (winnerResidualClock t a E) a := by
  unfold SharedRace.normClock SharedRace.clockTotal
  exact normalized_winner_eq_residual t ht htotal a E

/-- The original losing normalized coordinate after removing the common
race minimum. -/
private lemma normClock_loser_eq_residual
    {κ : Type} [Fintype κ] [DecidableEq κ]
    (t : κ → ℝ) (ht : ∀ i, 0 < t i) (htotal : ∑ i, t i = 1)
    (a i : κ) (hi : i ≠ a) (E : κ → ℝ) :
    SharedRace.normClock E i =
      (t i * winnerResidualClock t a E a +
          winnerResidualClock t a E i) /
        SharedRace.clockTotal (winnerResidualClock t a E) := by
  unfold SharedRace.normClock SharedRace.clockTotal
  exact normalized_loser_eq_residual t ht htotal a i hi E

/-- The shared-race ratio on a losing coordinate, written in the
fresh residual clocks. -/
private lemma raceRatio_loser_eq_residual
    {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (t : κ → ℝ) (ht : ∀ i, 0 < t i)
    (a i : κ) (hi : i ≠ a) (E : κ → ℝ)
    (ha : strictClockWin t a E) :
    SharedRace.raceRatio t E i =
      t i * winnerResidualClock t a E a /
        (t i * winnerResidualClock t a E a +
          winnerResidualClock t a E i) := by
  unfold SharedRace.raceRatio
  rw [rawRaceMin_eq_of_strictClockWin t E a ha]
  exact weighted_ratio_loser_eq_residual t ht a i hi E

private lemma measurable_clockArgmin_fixed
    {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    [MeasurableSpace κ] [MeasurableSingletonClass κ]
    (t : κ → ℝ) : Measurable (SharedRace.clockArgmin t) := by
  unfold SharedRace.clockArgmin
  apply measurable_lexMax
  intro i
  change Measurable (fun E : κ → ℝ => -(E i / t i))
  fun_prop

private lemma measurable_rawRaceMin_fixed
    {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (t : κ → ℝ) : Measurable (SharedRace.rawRaceMin t) := by
  letI : MeasurableSpace κ := ⊤
  let a : (κ → ℝ) → κ := SharedRace.clockArgmin t
  let v : (κ → ℝ) → ℝ := fun E =>
    ∑ i, if a E = i then E i / t i else 0
  have ha : Measurable a := measurable_clockArgmin_fixed t
  have hv : Measurable v := by
    dsimp only [v]
    apply Finset.measurable_sum
    intro i _
    exact Measurable.ite
      (measurableSet_singleton i |>.preimage ha)
      (by
        change Measurable (fun E : κ → ℝ => E i / t i)
        fun_prop)
      measurable_const
  have heq : SharedRace.rawRaceMin t = v := by
    funext E
    unfold SharedRace.rawRaceMin
    dsimp only [v, a]
    simp
  rw [heq]
  exact hv

private lemma measurable_normRaceMin_fixed
    {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (t : κ → ℝ) : Measurable (SharedRace.normRaceMin t) := by
  unfold SharedRace.normRaceMin
  exact (measurable_rawRaceMin_fixed t).div SharedRace.measurable_clockTotal

private lemma measurable_raceRatio_fixed
    {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (t : κ → ℝ) (i : κ) : Measurable (fun E => SharedRace.raceRatio t E i) := by
  unfold SharedRace.raceRatio
  exact ((measurable_rawRaceMin_fixed t).mul measurable_const).div
    (measurable_pi_apply i)

namespace SharedRace

/-- The one-coordinate moment whose finite sum controls the normalized race
partition function. -/
noncomputable def clockCoordinateIntegrand
    {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (t : κ → ℝ) (i : κ) (E : κ → ℝ) : ℝ :=
  raceRatio t E i ^ 2 *
    Real.exp ((Fintype.card κ : ℝ) * SharedRace.logTwo *
      (normClock E i - normRaceMin t E))

lemma measurable_clockCoordinateIntegrand
    {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (t : κ → ℝ) (i : κ) : Measurable (clockCoordinateIntegrand t i) := by
  unfold clockCoordinateIntegrand normClock
  exact ((measurable_raceRatio_fixed t i).pow_const 2).mul
    (Real.measurable_exp.comp
      (measurable_const.mul
        (((measurable_pi_apply i).div measurable_clockTotal).sub
          (measurable_normRaceMin_fixed t))))

/-- The one-coordinate normalized race moment is integrable.  The proof uses
only positivity of the clocks and the uniform bounds `raceRatio ≤ 1` and
`normClock ≤ 1`. -/
theorem clockCoordinateIntegrand_integrable
    {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (t : κ → ℝ) (ht : ∀ i, 0 < t i) (i : κ) :
    Integrable (clockCoordinateIntegrand t i) (clockLaw κ) := by
  let C : ℝ := Real.exp
    ((Fintype.card κ : ℝ) * SharedRace.logTwo)
  have hstrong : AEStronglyMeasurable
      (clockCoordinateIntegrand t i) (clockLaw κ) :=
    (measurable_clockCoordinateIntegrand t i).aestronglyMeasurable
  apply Integrable.of_bound hstrong C
  filter_upwards [ae_clockLaw_pos (κ := κ)] with E hE
  have hratio0 : 0 < raceRatio t E i := raceRatio_pos t E ht hE i
  have hratio1 : raceRatio t E i ≤ 1 := raceRatio_le_one t E ht hE i
  have hsq : raceRatio t E i ^ 2 ≤ 1 := by nlinarith
  have hmin0 : 0 ≤ normRaceMin t E := by
    unfold normRaceMin
    exact div_nonneg (rawRaceMin_pos t E ht hE).le (clockTotal_pos E hE).le
  have hcoord1 : normClock E i ≤ 1 := normClock_le_one E hE i
  have hdiff : normClock E i - normRaceMin t E ≤ 1 := by linarith
  have hc0 : 0 ≤ (Fintype.card κ : ℝ) * SharedRace.logTwo :=
    mul_nonneg (by positivity) SharedRace.L_pos.le
  have hexp :
      Real.exp ((Fintype.card κ : ℝ) * SharedRace.logTwo *
          (normClock E i - normRaceMin t E)) ≤ C := by
    apply Real.exp_le_exp.mpr
    exact mul_le_of_le_one_right hc0 hdiff
  rw [Real.norm_eq_abs, abs_of_nonneg]
  · exact (mul_le_mul_of_nonneg_right hsq (Real.exp_nonneg _)).trans
      (by simpa only [one_mul] using hexp)
  · exact mul_nonneg (sq_nonneg _) (Real.exp_nonneg _)

end SharedRace

private lemma strictClockWin_measurableSet
    {κ : Type} [Fintype κ] [DecidableEq κ]
    (t : κ → ℝ) (a : κ) :
    MeasurableSet {E : κ → ℝ | strictClockWin t a E} := by
  unfold strictClockWin
  measurability

private lemma strictClockWin_pairwise_disjoint
    {κ : Type} [Fintype κ] [DecidableEq κ]
    (t : κ → ℝ) : Pairwise fun a b : κ => Disjoint
      {E : κ → ℝ | strictClockWin t a E}
      {E : κ → ℝ | strictClockWin t b E} := by
  intro a b hab
  rw [Set.disjoint_left]
  intro E ha hb
  have hab' := ha b hab.symm
  have hba' := hb a hab
  linarith

/-- The strict winner cells exhaust iid exponential clocks up to a null set.
This is the measure-level partition used by all subsequent cellwise moment
identities. -/
private theorem clockLaw_eq_sum_restrict_strictClockWin
    {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (t : κ → ℝ) (ht : ∀ i, 0 < t i) (htotal : ∑ i, t i = 1) :
    clockLaw κ = Measure.sum fun a : κ =>
      (clockLaw κ).restrict {E | strictClockWin t a E} := by
  letI : IsProbabilityMeasure (expMeasure 1) :=
    isProbabilityMeasure_expMeasure zero_lt_one
  letI : IsProbabilityMeasure (clockLaw κ) := by
    unfold clockLaw
    infer_instance
  let S : κ → Set (κ → ℝ) := fun a => {E | strictClockWin t a E}
  have hS (a : κ) : MeasurableSet (S a) :=
    strictClockWin_measurableSet t a
  have hdisj : Pairwise fun a b => Disjoint (S a) (S b) :=
    strictClockWin_pairwise_disjoint t
  have hcell (a : κ) : clockLaw κ (S a) = ENNReal.ofReal (t a) := by
    unfold clockLaw S
    exact pi_exp_strictClockWin t ht htotal a
  have hmass : clockLaw κ (⋃ a, S a) = 1 := by
    rw [measure_iUnion hdisj hS, tsum_fintype]
    simp_rw [hcell]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun a _ => (ht a).le), htotal]
    norm_num
  have hUnion : ∀ᵐ E ∂(clockLaw κ), E ∈ ⋃ a, S a :=
    (mem_ae_iff_prob_eq_one (MeasurableSet.iUnion hS)).2 hmass
  calc
    clockLaw κ = (clockLaw κ).restrict (⋃ a, S a) :=
      (Measure.restrict_eq_self_of_ae_mem hUnion).symm
    _ = Measure.sum fun a : κ => (clockLaw κ).restrict (S a) :=
      Measure.restrict_iUnion hdisj hS

private lemma integral_clock_eq_sum_strictClockWin
    {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (t : κ → ℝ) (ht : ∀ i, 0 < t i) (htotal : ∑ i, t i = 1)
    (f : (κ → ℝ) → ℝ) (hf : Integrable f (clockLaw κ)) :
    (∫ E, f E ∂(clockLaw κ)) =
      ∑ a, ∫ E, f E
        ∂((clockLaw κ).restrict {E | strictClockWin t a E}) := by
  have hdecomp := clockLaw_eq_sum_restrict_strictClockWin t ht htotal
  have hsumInt : Integrable f (Measure.sum fun a : κ =>
      (clockLaw κ).restrict {E | strictClockWin t a E}) := by
    rw [← hdecomp]
    exact hf
  calc
    (∫ E, f E ∂(clockLaw κ)) =
        ∫ E, f E ∂(Measure.sum fun a : κ =>
          (clockLaw κ).restrict {E | strictClockWin t a E}) :=
      congrArg (fun μ : Measure (κ → ℝ) => ∫ E, f E ∂μ) hdecomp
    _ = ∑ a, ∫ E, f E
          ∂((clockLaw κ).restrict {E | strictClockWin t a E}) := by
      simpa only [tsum_fintype] using integral_sum_measure hsumInt

/-- Integrating a measurable residual-clock statistic on one strict winner
cell gives the winner mass times its expectation under fresh iid clocks. -/
private lemma integral_comp_winnerResidualClock
    {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (t : κ → ℝ) (ht : ∀ i, 0 < t i) (htotal : ∑ i, t i = 1)
    (a : κ) (f : (κ → ℝ) → ℝ) (hf : Measurable f) :
    (∫ E, f (winnerResidualClock t a E)
        ∂((clockLaw κ).restrict {E | strictClockWin t a E})) =
      t a * ∫ W, f W ∂(clockLaw κ) := by
  have hmap := winnerResidualClock_restrict_law t ht htotal a
  calc
    (∫ E, f (winnerResidualClock t a E)
        ∂((clockLaw κ).restrict {E | strictClockWin t a E})) =
        ∫ W, f W ∂Measure.map (winnerResidualClock t a)
          ((clockLaw κ).restrict {E | strictClockWin t a E}) :=
      (integral_map (winnerResidualClock_measurable t a).aemeasurable
        hf.aestronglyMeasurable).symm
    _ = ∫ W, f W ∂ENNReal.ofReal (t a) • clockLaw κ := by rw [hmap]
    _ = (ENNReal.ofReal (t a)).toReal • ∫ W, f W ∂clockLaw κ := by
      rw [integral_smul_measure]
    _ = t a * ∫ W, f W ∂clockLaw κ := by
      rw [ENNReal.toReal_ofReal (ht a).le]
      rfl

/-- Integrability companion to `integral_comp_winnerResidualClock`. -/
private lemma integrable_comp_winnerResidualClock
    {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (t : κ → ℝ) (ht : ∀ i, 0 < t i) (htotal : ∑ i, t i = 1)
    (a : κ) (f : (κ → ℝ) → ℝ) (hf : Integrable f (clockLaw κ)) :
    Integrable (fun E => f (winnerResidualClock t a E))
      ((clockLaw κ).restrict {E | strictClockWin t a E}) := by
  have hmap := winnerResidualClock_restrict_law t ht htotal a
  have hscaled : Integrable f (ENNReal.ofReal (t a) • clockLaw κ) :=
    hf.smul_measure (by simp)
  rw [← hmap] at hscaled
  exact hscaled.comp_measurable (winnerResidualClock_measurable t a)

private lemma clockCoordinateIntegrand_winner_eq
    {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (t : κ → ℝ) (ht : ∀ i, 0 < t i) (htotal : ∑ i, t i = 1)
    (a : κ) (E : κ → ℝ) (hE : ∀ i, 0 < E i)
    (ha : strictClockWin t a E) :
    SharedRace.clockCoordinateIntegrand t a E =
      Real.exp ((-SharedRace.logTwo * (1 - t a)) *
        ((Fintype.card κ : ℝ) *
          SharedRace.normClock (winnerResidualClock t a E) a)) := by
  have hratio : SharedRace.raceRatio t E a = 1 := by
    unfold SharedRace.raceRatio
    rw [rawRaceMin_eq_of_strictClockWin t E a ha]
    field_simp [(ht a).ne', (hE a).ne']
  rw [SharedRace.clockCoordinateIntegrand, hratio, one_pow, one_mul,
    normClock_winner_eq_residual t ht htotal a E,
    normRaceMin_eq_residual t ht htotal a E ha]
  congr 1
  ring

/-- Exact winning-cell contribution to the one-coordinate moment. -/
private theorem clockCoordinate_winnerCell_integral_eq
    {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (t : κ → ℝ) (ht : ∀ i, 0 < t i) (htotal : ∑ i, t i = 1)
    (hk : 2 ≤ Fintype.card κ) (a : κ) :
    (∫ E, SharedRace.clockCoordinateIntegrand t a E
        ∂((clockLaw κ).restrict {E | strictClockWin t a E})) =
      t a * SharedRace.betaOneExpMoment (Fintype.card κ)
        (-SharedRace.logTwo * (1 - t a)) := by
  let f : (κ → ℝ) → ℝ := fun W =>
    Real.exp ((-SharedRace.logTwo * (1 - t a)) *
      ((Fintype.card κ : ℝ) * SharedRace.normClock W a))
  have hf : Measurable f := by
    dsimp only [f]
    exact Real.measurable_exp.comp
      (measurable_const.mul
        (measurable_const.mul (SharedRace.measurable_normClock a)))
  have hpoint :
      (fun E => SharedRace.clockCoordinateIntegrand t a E) =ᵐ[
        (clockLaw κ).restrict {E | strictClockWin t a E}]
      fun E => f (winnerResidualClock t a E) := by
    filter_upwards [ae_restrict_of_ae (SharedRace.ae_clockLaw_pos (κ := κ)),
      ae_restrict_mem (strictClockWin_measurableSet t a)] with E hE ha
    exact clockCoordinateIntegrand_winner_eq t ht htotal a E hE ha
  calc
    (∫ E, SharedRace.clockCoordinateIntegrand t a E
        ∂((clockLaw κ).restrict {E | strictClockWin t a E})) =
        ∫ E, f (winnerResidualClock t a E)
          ∂((clockLaw κ).restrict {E | strictClockWin t a E}) :=
      integral_congr_ae hpoint
    _ = t a * ∫ W, f W ∂clockLaw κ :=
      integral_comp_winnerResidualClock t ht htotal a f hf
    _ = t a * SharedRace.betaOneExpMoment (Fintype.card κ)
          (-SharedRace.logTwo * (1 - t a)) := by
      congr 1
      exact SharedRace.clockLaw_scaledNormClock_expMoment_eq a hk
        (-SharedRace.logTwo * (1 - t a))

/-- Exact winning normalized-clock first moment on one strict winner cell.
This is retained for the later row identity
`E[U_argmin] = (sum_i t_i^2) / k`. -/
private theorem normClock_winnerCell_integral_eq
    {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (t : κ → ℝ) (ht : ∀ i, 0 < t i) (htotal : ∑ i, t i = 1)
    (a : κ) :
    (∫ E, SharedRace.normClock E a
        ∂((clockLaw κ).restrict {E | strictClockWin t a E})) =
      t a ^ 2 / (Fintype.card κ : ℝ) := by
  let f : (κ → ℝ) → ℝ := fun W =>
    t a * SharedRace.normClock W a
  have hf : Measurable f :=
    measurable_const.mul (SharedRace.measurable_normClock a)
  have hpoint :
      (fun E => SharedRace.normClock E a) =ᵐ[
        (clockLaw κ).restrict {E | strictClockWin t a E}]
      fun E => f (winnerResidualClock t a E) := by
    filter_upwards [] with E
    exact normClock_winner_eq_residual t ht htotal a E
  calc
    (∫ E, SharedRace.normClock E a
        ∂((clockLaw κ).restrict {E | strictClockWin t a E})) =
        ∫ E, f (winnerResidualClock t a E)
          ∂((clockLaw κ).restrict {E | strictClockWin t a E}) :=
      integral_congr_ae hpoint
    _ = t a * ∫ W, f W ∂clockLaw κ :=
      integral_comp_winnerResidualClock t ht htotal a f hf
    _ = t a * (t a * ∫ W, SharedRace.normClock W a ∂clockLaw κ) := by
      rw [integral_const_mul]
    _ = t a * (t a * (1 / (Fintype.card κ : ℝ))) := by
      rw [SharedRace.integral_normClock a]
    _ = t a ^ 2 / (Fintype.card κ : ℝ) := by ring

private lemma measurable_normClock_clockArgmin
    {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (t : κ → ℝ) : Measurable
      (fun E : κ → ℝ =>
        SharedRace.normClock E (SharedRace.clockArgmin t E)) := by
  letI : MeasurableSpace κ := ⊤
  let a : (κ → ℝ) → κ := SharedRace.clockArgmin t
  let f : (κ → ℝ) → ℝ := fun E =>
    ∑ i, if a E = i then SharedRace.normClock E i else 0
  have ha : Measurable a := measurable_clockArgmin_fixed t
  have hf : Measurable f := by
    dsimp only [f]
    apply Finset.measurable_sum
    intro i _hi
    exact Measurable.ite
      (measurableSet_singleton i |>.preimage ha)
      (SharedRace.measurable_normClock i) measurable_const
  have heq : (fun E : κ → ℝ =>
      SharedRace.normClock E (SharedRace.clockArgmin t E)) = f := by
    funext E
    dsimp only [f, a]
    simp
  rw [heq]
  exact hf

private lemma integrable_normClock_clockArgmin
    {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (t : κ → ℝ) : Integrable
      (fun E : κ → ℝ =>
        SharedRace.normClock E (SharedRace.clockArgmin t E))
      (clockLaw κ) := by
  apply Integrable.of_bound
    (measurable_normClock_clockArgmin t).aestronglyMeasurable 1
  filter_upwards [SharedRace.ae_clockLaw_pos (κ := κ)] with E hE
  have hnonneg : 0 ≤
      SharedRace.normClock E (SharedRace.clockArgmin t E) :=
    SharedRace.normClock_nonneg E hE (SharedRace.clockArgmin t E)
  rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
  exact SharedRace.normClock_le_one E hE (SharedRace.clockArgmin t E)

namespace SharedRace

/-- The normalized clock selected by a positive PMF race has first moment
`(sum_i r_i^2) / k`.  This is the row moment needed by the reference-loss
assembly. -/
theorem integral_normClock_clockArgmin_eq
    {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (r : κ → ℝ) (hr : ∀ i, 0 < r i) (hrtotal : ∑ i, r i = 1) :
    (∫ E : κ → ℝ, normClock E (clockArgmin r E) ∂clockLaw κ) =
      (∑ i, r i ^ 2) / (Fintype.card κ : ℝ) := by
  rw [integral_clock_eq_sum_strictClockWin r hr hrtotal
    (fun E : κ → ℝ => normClock E (clockArgmin r E))
    (integrable_normClock_clockArgmin r)]
  apply (Finset.sum_congr rfl fun a _ => ?_).trans
    (Finset.sum_div (s := (univ : Finset κ))
      (f := fun a => r a ^ 2) (Fintype.card κ : ℝ)).symm
  calc
    (∫ E : κ → ℝ, normClock E (clockArgmin r E)
        ∂((clockLaw κ).restrict {E | strictClockWin r a E})) =
        ∫ E : κ → ℝ, normClock E a
          ∂((clockLaw κ).restrict {E | strictClockWin r a E}) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem (strictClockWin_measurableSet r a)]
        with E hwin
      rw [clockArgmin_eq_of_strictClockWin r E a hwin]
    _ = r a ^ 2 / (Fintype.card κ : ℝ) :=
      normClock_winnerCell_integral_eq r hr hrtotal a

private lemma integrable_normRaceMin_cell
    {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (π : κ → ℝ) (hπ : ∀ i, 0 < π i) (hπtotal : ∑ i, π i = 1)
    (a : κ) :
    Integrable (normRaceMin π)
      ((clockLaw κ).restrict {E | strictClockWin π a E}) := by
  have hcomp := integrable_comp_winnerResidualClock π hπ hπtotal a
    (fun W : κ → ℝ => normClock W a) (integrable_normClock a)
  apply hcomp.congr
  filter_upwards [ae_restrict_mem (strictClockWin_measurableSet π a)]
    with E hwin
  rw [normRaceMin_eq_residual π hπ hπtotal a E hwin]

private theorem integral_normRaceMin_cell_eq
    {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (π : κ → ℝ) (hπ : ∀ i, 0 < π i) (hπtotal : ∑ i, π i = 1)
    (a : κ) :
    (∫ E : κ → ℝ, normRaceMin π E
        ∂((clockLaw κ).restrict {E | strictClockWin π a E})) =
      π a / (Fintype.card κ : ℝ) := by
  calc
    (∫ E : κ → ℝ, normRaceMin π E
        ∂((clockLaw κ).restrict {E | strictClockWin π a E})) =
        ∫ E : κ → ℝ, normClock (winnerResidualClock π a E) a
          ∂((clockLaw κ).restrict {E | strictClockWin π a E}) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem (strictClockWin_measurableSet π a)]
        with E hwin
      rw [normRaceMin_eq_residual π hπ hπtotal a E hwin]
    _ = π a * ∫ W : κ → ℝ, normClock W a ∂clockLaw κ :=
      integral_comp_winnerResidualClock π hπ hπtotal a
        (fun W : κ → ℝ => normClock W a) (measurable_normClock a)
    _ = π a * (1 / (Fintype.card κ : ℝ)) := by
      rw [integral_normClock a]
    _ = π a / (Fintype.card κ : ℝ) := by ring

/-- Integrability and exact mean of the normalized weighted race minimum. -/
theorem integrable_normRaceMin
    {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (π : κ → ℝ) (hπ : ∀ i, 0 < π i) (hπtotal : ∑ i, π i = 1) :
    Integrable (normRaceMin π) (clockLaw κ) := by
  have hsum : Integrable (normRaceMin π)
      (Measure.sum fun a : κ =>
        (clockLaw κ).restrict {E | strictClockWin π a E}) :=
    integrable_sum_measure
      (fun a => integrable_normRaceMin_cell π hπ hπtotal a)
      Summable.of_finite
  rw [← clockLaw_eq_sum_restrict_strictClockWin π hπ hπtotal] at hsum
  exact hsum

theorem integral_normRaceMin_eq_inv_card
    {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (π : κ → ℝ) (hπ : ∀ i, 0 < π i) (hπtotal : ∑ i, π i = 1) :
    (∫ E : κ → ℝ, normRaceMin π E ∂clockLaw κ) =
      1 / (Fintype.card κ : ℝ) := by
  rw [integral_clock_eq_sum_strictClockWin π hπ hπtotal
    (normRaceMin π) (integrable_normRaceMin π hπ hπtotal)]
  simp_rw [integral_normRaceMin_cell_eq π hπ hπtotal]
  rw [← Finset.sum_div, hπtotal]

private lemma integrable_log_normRaceMin_cell
    {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (π : κ → ℝ) (hπ : ∀ i, 0 < π i) (hπtotal : ∑ i, π i = 1)
    (hk : 2 ≤ Fintype.card κ) (a : κ) :
    Integrable (fun E : κ → ℝ => Real.log (normRaceMin π E))
      ((clockLaw κ).restrict {E | strictClockWin π a E}) := by
  have hcomp := integrable_comp_winnerResidualClock π hπ hπtotal a
    (fun W : κ → ℝ => Real.log (normClock W a))
    (integrable_log_normClock a hk)
  apply hcomp.congr
  filter_upwards [ae_restrict_mem (strictClockWin_measurableSet π a)]
    with E hwin
  rw [normRaceMin_eq_residual π hπ hπtotal a E hwin]

private theorem integral_log_normRaceMin_cell_eq
    {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (π : κ → ℝ) (hπ : ∀ i, 0 < π i) (hπtotal : ∑ i, π i = 1)
    (hk : 2 ≤ Fintype.card κ) (a : κ) :
    (∫ E : κ → ℝ, Real.log (normRaceMin π E)
        ∂((clockLaw κ).restrict {E | strictClockWin π a E})) =
      π a * normClockLogIntegral (Fintype.card κ) := by
  calc
    (∫ E : κ → ℝ, Real.log (normRaceMin π E)
        ∂((clockLaw κ).restrict {E | strictClockWin π a E})) =
        ∫ E : κ → ℝ,
          Real.log (normClock (winnerResidualClock π a E) a)
          ∂((clockLaw κ).restrict {E | strictClockWin π a E}) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem (strictClockWin_measurableSet π a)]
        with E hwin
      rw [normRaceMin_eq_residual π hπ hπtotal a E hwin]
    _ = π a * ∫ W : κ → ℝ, Real.log (normClock W a) ∂clockLaw κ :=
      integral_comp_winnerResidualClock π hπ hπtotal a
        (fun W : κ → ℝ => Real.log (normClock W a))
        (Real.measurable_log.comp (measurable_normClock a))
    _ = π a * normClockLogIntegral (Fintype.card κ) := by
      rw [integral_log_normClock_eq_normClockLogIntegral a hk]

/-- The normalized minimum of a positive PMF race has the same logarithmic
mean as any normalized iid clock coordinate. -/
theorem integrable_log_normRaceMin
    {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (π : κ → ℝ) (hπ : ∀ i, 0 < π i) (hπtotal : ∑ i, π i = 1)
    (hk : 2 ≤ Fintype.card κ) :
    Integrable (fun E : κ → ℝ => Real.log (normRaceMin π E))
      (clockLaw κ) := by
  have hsum : Integrable (fun E : κ → ℝ => Real.log (normRaceMin π E))
      (Measure.sum fun a : κ =>
        (clockLaw κ).restrict {E | strictClockWin π a E}) :=
    integrable_sum_measure
      (fun a => integrable_log_normRaceMin_cell π hπ hπtotal hk a)
      Summable.of_finite
  rw [← clockLaw_eq_sum_restrict_strictClockWin π hπ hπtotal] at hsum
  exact hsum

theorem integral_log_normRaceMin_eq_normClockLogIntegral
    {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (π : κ → ℝ) (hπ : ∀ i, 0 < π i) (hπtotal : ∑ i, π i = 1)
    (hk : 2 ≤ Fintype.card κ) :
    (∫ E : κ → ℝ, Real.log (normRaceMin π E) ∂clockLaw κ) =
      normClockLogIntegral (Fintype.card κ) := by
  rw [integral_clock_eq_sum_strictClockWin π hπ hπtotal
    (fun E : κ → ℝ => Real.log (normRaceMin π E))
    (integrable_log_normRaceMin π hπ hπtotal hk)]
  simp_rw [integral_log_normRaceMin_cell_eq π hπ hπtotal hk]
  rw [← Finset.sum_mul, hπtotal, one_mul]

private lemma integrable_log_mul_normClock
    {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (c : ℝ) (hc : 0 < c) (a : κ) (hk : 2 ≤ Fintype.card κ) :
    Integrable (fun W : κ → ℝ => Real.log (c * normClock W a))
      (clockLaw κ) := by
  have heq : (fun W : κ → ℝ => Real.log (c * normClock W a)) =ᵐ[clockLaw κ]
      fun W => Real.log c + Real.log (normClock W a) := by
    filter_upwards [ae_clockLaw_pos (κ := κ)] with W hW
    rw [Real.log_mul hc.ne'
      ((normClock_nonneg W hW a).lt_of_ne' (by
        unfold normClock
        exact div_ne_zero (hW a).ne' (clockTotal_pos W hW).ne')).ne']
  have hconst : Integrable (fun _ : κ → ℝ => Real.log c) (clockLaw κ) :=
    integrable_const (Real.log c)
  exact (hconst.add (integrable_log_normClock a hk)).congr heq.symm

private lemma integral_log_mul_normClock_eq
    {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (c : ℝ) (hc : 0 < c) (a : κ) (hk : 2 ≤ Fintype.card κ) :
    (∫ W : κ → ℝ, Real.log (c * normClock W a) ∂clockLaw κ) =
      Real.log c + normClockLogIntegral (Fintype.card κ) := by
  have heq : (fun W : κ → ℝ => Real.log (c * normClock W a)) =ᵐ[clockLaw κ]
      fun W => Real.log c + Real.log (normClock W a) := by
    filter_upwards [ae_clockLaw_pos (κ := κ)] with W hW
    rw [Real.log_mul hc.ne'
      ((normClock_nonneg W hW a).lt_of_ne' (by
        unfold normClock
        exact div_ne_zero (hW a).ne' (clockTotal_pos W hW).ne')).ne']
  have hconst : Integrable (fun _ : κ → ℝ => Real.log c) (clockLaw κ) :=
    integrable_const (Real.log c)
  rw [integral_congr_ae heq,
    integral_add hconst (integrable_log_normClock a hk),
    integral_const,
    integral_log_normClock_eq_normClockLogIntegral a hk]
  simp [Measure.real]

private lemma integrable_log_normClock_argmin_cell
    {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (r : κ → ℝ) (hr : ∀ i, 0 < r i) (hrtotal : ∑ i, r i = 1)
    (hk : 2 ≤ Fintype.card κ) (a : κ) :
    Integrable
      (fun E : κ → ℝ => Real.log (normClock E (clockArgmin r E)))
      ((clockLaw κ).restrict {E | strictClockWin r a E}) := by
  have hcomp := integrable_comp_winnerResidualClock r hr hrtotal a
    (fun W : κ → ℝ => Real.log (r a * normClock W a))
    (integrable_log_mul_normClock (r a) (hr a) a hk)
  apply hcomp.congr
  filter_upwards [ae_restrict_mem (strictClockWin_measurableSet r a)]
    with E hwin
  rw [clockArgmin_eq_of_strictClockWin r E a hwin,
    normClock_winner_eq_residual r hr hrtotal a E]

private theorem integral_log_normClock_argmin_cell_eq
    {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (r : κ → ℝ) (hr : ∀ i, 0 < r i) (hrtotal : ∑ i, r i = 1)
    (hk : 2 ≤ Fintype.card κ) (a : κ) :
    (∫ E : κ → ℝ, Real.log (normClock E (clockArgmin r E))
        ∂((clockLaw κ).restrict {E | strictClockWin r a E})) =
      r a * (Real.log (r a) +
        normClockLogIntegral (Fintype.card κ)) := by
  calc
    (∫ E : κ → ℝ, Real.log (normClock E (clockArgmin r E))
        ∂((clockLaw κ).restrict {E | strictClockWin r a E})) =
        ∫ E : κ → ℝ,
          Real.log (r a * normClock (winnerResidualClock r a E) a)
          ∂((clockLaw κ).restrict {E | strictClockWin r a E}) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem (strictClockWin_measurableSet r a)]
        with E hwin
      rw [clockArgmin_eq_of_strictClockWin r E a hwin,
        normClock_winner_eq_residual r hr hrtotal a E]
    _ = r a * ∫ W : κ → ℝ,
        Real.log (r a * normClock W a) ∂clockLaw κ :=
      integral_comp_winnerResidualClock r hr hrtotal a
        (fun W : κ → ℝ => Real.log (r a * normClock W a))
        (Real.measurable_log.comp
          (measurable_const.mul (measurable_normClock a)))
    _ = r a * (Real.log (r a) +
        normClockLogIntegral (Fintype.card κ)) := by
      rw [integral_log_mul_normClock_eq (r a) (hr a) a hk]

/-- Integrability of the logarithmic normalized winning coordinate. -/
theorem integrable_log_normClock_clockArgmin
    {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (r : κ → ℝ) (hr : ∀ i, 0 < r i) (hrtotal : ∑ i, r i = 1)
    (hk : 2 ≤ Fintype.card κ) :
    Integrable
      (fun E : κ → ℝ => Real.log (normClock E (clockArgmin r E)))
      (clockLaw κ) := by
  have hsum : Integrable
      (fun E : κ → ℝ => Real.log (normClock E (clockArgmin r E)))
      (Measure.sum fun a : κ =>
        (clockLaw κ).restrict {E | strictClockWin r a E}) :=
    integrable_sum_measure
      (fun a => integrable_log_normClock_argmin_cell r hr hrtotal hk a)
      Summable.of_finite
  rw [← clockLaw_eq_sum_restrict_strictClockWin r hr hrtotal] at hsum
  exact hsum

/-- The logarithmic winning-clock row moment.  The universal common clock
moment is left symbolic because it cancels against the normalized race
minimum in the reference ratio. -/
theorem integral_log_normClock_clockArgmin_eq
    {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (r : κ → ℝ) (hr : ∀ i, 0 < r i) (hrtotal : ∑ i, r i = 1)
    (hk : 2 ≤ Fintype.card κ) :
    (∫ E : κ → ℝ, Real.log (normClock E (clockArgmin r E))
        ∂clockLaw κ) =
      ∑ i, r i * (Real.log (r i) +
        normClockLogIntegral (Fintype.card κ)) := by
  rw [integral_clock_eq_sum_strictClockWin r hr hrtotal
    (fun E : κ → ℝ => Real.log (normClock E (clockArgmin r E)))
    (integrable_log_normClock_clockArgmin r hr hrtotal hk)]
  exact Finset.sum_congr rfl fun a _ =>
    integral_log_normClock_argmin_cell_eq r hr hrtotal hk a

private lemma measurable_log_coordinate_clockArgmin
    {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (π r : κ → ℝ) : Measurable
      (fun E : κ → ℝ => Real.log (π (clockArgmin r E))) := by
  letI : MeasurableSpace κ := ⊤
  exact (measurable_of_finite fun i : κ => Real.log (π i)).comp
    (measurable_clockArgmin_fixed r)

private lemma integrable_log_coordinate_clockArgmin
    {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (π r : κ → ℝ) : Integrable
      (fun E : κ → ℝ => Real.log (π (clockArgmin r E)))
      (clockLaw κ) := by
  let C : ℝ := ∑ i, |Real.log (π i)|
  apply Integrable.of_bound
    (measurable_log_coordinate_clockArgmin π r).aestronglyMeasurable C
  filter_upwards [] with E
  rw [Real.norm_eq_abs]
  exact Finset.single_le_sum (fun i _ => abs_nonneg (Real.log (π i)))
    (Finset.mem_univ (clockArgmin r E))

private theorem integral_log_coordinate_clockArgmin_eq
    {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (π r : κ → ℝ) (hr : ∀ i, 0 < r i) (hrtotal : ∑ i, r i = 1) :
    (∫ E : κ → ℝ, Real.log (π (clockArgmin r E)) ∂clockLaw κ) =
      ∑ i, r i * Real.log (π i) := by
  rw [integral_clock_eq_sum_strictClockWin r hr hrtotal
    (fun E : κ → ℝ => Real.log (π (clockArgmin r E)))
    (integrable_log_coordinate_clockArgmin π r)]
  apply Finset.sum_congr rfl
  intro a _ha
  calc
    (∫ E : κ → ℝ, Real.log (π (clockArgmin r E))
        ∂((clockLaw κ).restrict {E | strictClockWin r a E})) =
        ∫ _E : κ → ℝ, Real.log (π a)
          ∂((clockLaw κ).restrict {E | strictClockWin r a E}) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem (strictClockWin_measurableSet r a)]
        with E hwin
      rw [clockArgmin_eq_of_strictClockWin r E a hwin]
    _ = r a * ∫ _W : κ → ℝ, Real.log (π a) ∂clockLaw κ :=
      integral_comp_winnerResidualClock r hr hrtotal a
        (fun _W : κ → ℝ => Real.log (π a)) measurable_const
    _ = r a * Real.log (π a) := by simp [Measure.real]

private lemma log_raceRatio_clockArgmin_identity
    {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (π r E : κ → ℝ) (hπ : ∀ i, 0 < π i) (hE : ∀ i, 0 < E i) :
    Real.log (raceRatio π E (clockArgmin r E)) =
      Real.log (normRaceMin π E) +
        Real.log (π (clockArgmin r E)) -
          Real.log (normClock E (clockArgmin r E)) := by
  let a : κ := clockArgmin r E
  have hraw : 0 < rawRaceMin π E := rawRaceMin_pos π E hπ hE
  have htotal : 0 < clockTotal E := clockTotal_pos E hE
  have hcoord : 0 < E a := hE a
  have hprior : 0 < π a := hπ a
  change Real.log (raceRatio π E a) =
    Real.log (normRaceMin π E) + Real.log (π a) -
      Real.log (normClock E a)
  unfold raceRatio normRaceMin normClock
  rw [Real.log_div (mul_ne_zero hraw.ne' hprior.ne') hcoord.ne',
    Real.log_mul hraw.ne' hprior.ne',
    Real.log_div hraw.ne' htotal.ne',
    Real.log_div hcoord.ne' htotal.ne']
  ring

/-- The logarithmic reference ratio at the winner of an independent positive
row race is integrable. -/
theorem integrable_log_raceRatio_clockArgmin
    {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (π r : κ → ℝ) (hπ : ∀ i, 0 < π i) (hπtotal : ∑ i, π i = 1)
    (hr : ∀ i, 0 < r i) (hrtotal : ∑ i, r i = 1)
    (hk : 2 ≤ Fintype.card κ) :
    Integrable
      (fun E : κ → ℝ => Real.log (raceRatio π E (clockArgmin r E)))
      (clockLaw κ) := by
  have hmin := integrable_log_normRaceMin π hπ hπtotal hk
  have hprior := integrable_log_coordinate_clockArgmin π r
  have hwin := integrable_log_normClock_clockArgmin r hr hrtotal hk
  have hrhs : Integrable (fun E : κ → ℝ =>
      Real.log (normRaceMin π E) + Real.log (π (clockArgmin r E)) -
        Real.log (normClock E (clockArgmin r E))) (clockLaw κ) :=
    (hmin.add hprior).sub hwin
  apply hrhs.congr
  filter_upwards [ae_clockLaw_pos (κ := κ)] with E hE
  exact (log_raceRatio_clockArgmin_identity π r E hπ hE).symm

/-- Exact row identity for the logarithmic winning reference ratio.  The
common normalized-clock logarithmic moment cancels, leaving the finite
cross-entropy expression. -/
theorem integral_log_raceRatio_clockArgmin_eq
    {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (π r : κ → ℝ) (hπ : ∀ i, 0 < π i) (hπtotal : ∑ i, π i = 1)
    (hr : ∀ i, 0 < r i) (hrtotal : ∑ i, r i = 1)
    (hk : 2 ≤ Fintype.card κ) :
    (∫ E : κ → ℝ,
      Real.log (raceRatio π E (clockArgmin r E)) ∂clockLaw κ) =
      ∑ i, r i * Real.log (π i / r i) := by
  have hmin := integrable_log_normRaceMin π hπ hπtotal hk
  have hprior := integrable_log_coordinate_clockArgmin π r
  have hwin := integrable_log_normClock_clockArgmin r hr hrtotal hk
  have hpoint : (fun E : κ → ℝ =>
      Real.log (raceRatio π E (clockArgmin r E))) =ᵐ[clockLaw κ]
      fun E => Real.log (normRaceMin π E) +
        Real.log (π (clockArgmin r E)) -
          Real.log (normClock E (clockArgmin r E)) := by
    filter_upwards [ae_clockLaw_pos (κ := κ)] with E hE
    exact log_raceRatio_clockArgmin_identity π r E hπ hE
  have houter :
      (∫ E : κ → ℝ,
        (Real.log (normRaceMin π E) + Real.log (π (clockArgmin r E))) -
          Real.log (normClock E (clockArgmin r E)) ∂clockLaw κ) =
        (∫ E : κ → ℝ,
          Real.log (normRaceMin π E) + Real.log (π (clockArgmin r E))
          ∂clockLaw κ) -
        ∫ E : κ → ℝ, Real.log (normClock E (clockArgmin r E))
          ∂clockLaw κ := by
    simpa only [Pi.add_apply, Pi.sub_apply] using
      integral_sub (hmin.add hprior) hwin
  have hinner :
      (∫ E : κ → ℝ,
        Real.log (normRaceMin π E) + Real.log (π (clockArgmin r E))
        ∂clockLaw κ) =
        (∫ E : κ → ℝ, Real.log (normRaceMin π E) ∂clockLaw κ) +
        ∫ E : κ → ℝ, Real.log (π (clockArgmin r E)) ∂clockLaw κ := by
    simpa only [Pi.add_apply] using integral_add hmin hprior
  rw [integral_congr_ae hpoint, houter, hinner,
    integral_log_normRaceMin_eq_normClockLogIntegral π hπ hπtotal hk,
    integral_log_coordinate_clockArgmin_eq π r hr hrtotal,
    integral_log_normClock_clockArgmin_eq r hr hrtotal hk]
  have hlog (i : κ) : Real.log (π i / r i) =
      Real.log (π i) - Real.log (r i) :=
    Real.log_div (hπ i).ne' (hr i).ne'
  simp_rw [hlog, mul_add, mul_sub, Finset.sum_add_distrib,
    Finset.sum_sub_distrib]
  rw [← Finset.sum_mul, hrtotal, one_mul]
  ring

/-- Measurability of the normalized race partition function. -/
theorem measurable_normRaceZ
    {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (π : κ → ℝ) : Measurable (normRaceZ π) := by
  unfold normRaceZ
  apply Finset.measurable_sum
  intro i _hi
  exact ((measurable_raceRatio_fixed π i).pow_const 2).mul
    (Real.measurable_exp.comp
      (measurable_const.mul (measurable_normClock i)))

private lemma one_le_normRaceZ
    {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (π E : κ → ℝ) (hπ : ∀ i, 0 < π i) (hE : ∀ i, 0 < E i) :
    1 ≤ normRaceZ π E := by
  let a : κ := clockArgmin π E
  have hterm : 1 ≤ (raceRatio π E a) ^ 2 *
      Real.exp ((Fintype.card κ : ℝ) * SharedRace.logTwo *
        normClock E a) := by
    rw [raceRatio_argmin π E hπ hE, one_pow, one_mul]
    apply Real.one_le_exp
    exact mul_nonneg
      (mul_nonneg (by positivity) SharedRace.L_pos.le)
      (normClock_nonneg E hE a)
  exact hterm.trans (Finset.single_le_sum
    (f := fun i => (raceRatio π E i) ^ 2 *
      Real.exp ((Fintype.card κ : ℝ) * SharedRace.logTwo *
        normClock E i))
    (fun i _ => mul_nonneg (sq_nonneg _) (Real.exp_nonneg _))
    (Finset.mem_univ a))

/-- The normalized partition-function logarithm is integrable under iid
exponential clocks. -/
theorem integrable_log_normRaceZ
    {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (π : κ → ℝ) (hπ : ∀ i, 0 < π i) :
    Integrable (fun E : κ → ℝ => Real.log (normRaceZ π E))
      (clockLaw κ) := by
  let B : ℝ := (Fintype.card κ : ℝ) *
    Real.exp ((Fintype.card κ : ℝ) * SharedRace.logTwo)
  let C : ℝ := Real.log B
  have hBpos : 0 < B := by
    dsimp only [B]
    positivity
  apply Integrable.of_bound
    (Real.measurable_log.comp (measurable_normRaceZ π)).aestronglyMeasurable C
  filter_upwards [ae_clockLaw_pos (κ := κ)] with E hE
  have hZone : 1 ≤ normRaceZ π E := one_le_normRaceZ π E hπ hE
  have hZpos : 0 < normRaceZ π E := zero_lt_one.trans_le hZone
  have hZle : normRaceZ π E ≤ B := by
    simpa only [B] using normRaceZ_le π E hπ hE
  have hlogle : Real.log (normRaceZ π E) ≤ C := by
    dsimp only [C]
    exact Real.strictMonoOn_log.monotoneOn hZpos hBpos hZle
  change |Real.log (normRaceZ π E)| ≤ C
  rw [abs_of_nonneg (Real.log_nonneg hZone)]
  exact hlogle

/-- Clock-law specialization of the logarithmic tangent, conditional only on
the coordinate estimates supplied by the winner/loser analysis. -/
theorem normalizedRaceLogIntegral_le_of_coordinate
    {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (π : κ → ℝ) (hπ : IsPMF π) (hπpos : ∀ i, 0 < π i)
    (hk : 2 ≤ Fintype.card κ)
    (hcoord : ∀ i,
      (∫ E : κ → ℝ, clockCoordinateIntegrand π i E ∂clockLaw κ) ≤ π i) :
    (∫ E : κ → ℝ, Real.log (normRaceZ π E) ∂clockLaw κ) ≤
      SharedRace.logTwo := by
  have hπtotal : ∑ i, π i = 1 := by simpa [mass] using hπ.total
  have htint := integrable_normRaceMin π hπpos hπtotal
  have htmean :
      (∫ E : κ → ℝ, (Fintype.card κ : ℝ) *
        SharedRace.logTwo * normRaceMin π E ∂clockLaw κ) =
        SharedRace.logTwo := by
    rw [integral_const_mul,
      integral_normRaceMin_eq_inv_card π hπpos hπtotal]
    have hkne : (Fintype.card κ : ℝ) ≠ 0 := by positivity
    field_simp [hkne]
  apply normalizedRaceLogIntegral_le (clockLaw κ) π hπ
    (fun E i => raceRatio π E i) (fun E i => normClock E i)
    (normRaceMin π)
  · filter_upwards [ae_clockLaw_pos (κ := κ)] with E hE
    simpa only [normRaceZ] using normRaceZ_pos π E hπpos hE
  · simpa only [normRaceZ] using integrable_log_normRaceZ π hπpos
  · exact htint
  · exact htmean
  · intro i
    change Integrable (clockCoordinateIntegrand π i) (clockLaw κ)
    exact clockCoordinateIntegrand_integrable π hπpos i
  · intro i
    change (∫ E : κ → ℝ,
      clockCoordinateIntegrand π i E ∂clockLaw κ) ≤ π i
    exact hcoord i

/-- Integrability of the clock-row reference loss at the row winner. -/
theorem integrable_log_inv_referencePMF_clockArgmin
    {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (π r : κ → ℝ) (hπ : IsPMF π) (hπpos : ∀ i, 0 < π i)
    (hr : IsPMF r) (hrpos : ∀ i, 0 < r i)
    (hk : 2 ≤ Fintype.card κ) :
    Integrable (fun E : κ → ℝ =>
      Real.log (1 / referencePMF π E (clockArgmin r E)))
      (clockLaw κ) := by
  have hπtotal : ∑ i, π i = 1 := by simpa [mass] using hπ.total
  have hrtotal : ∑ i, r i = 1 := by simpa [mass] using hr.total
  have hZ := integrable_log_normRaceZ π hπpos
  have hratio := integrable_log_raceRatio_clockArgmin
    π r hπpos hπtotal hrpos hrtotal hk
  have hclock := integrable_normClock_clockArgmin r
  have hrhs : Integrable (fun E : κ → ℝ =>
      Real.log (normRaceZ π E) -
        2 * Real.log (raceRatio π E (clockArgmin r E)) -
          (Fintype.card κ : ℝ) * SharedRace.logTwo *
            normClock E (clockArgmin r E)) (clockLaw κ) :=
    (hZ.sub (hratio.const_mul 2)).sub
      (hclock.const_mul
        ((Fintype.card κ : ℝ) * SharedRace.logTwo))
  apply hrhs.congr
  filter_upwards [ae_clockLaw_pos (κ := κ)] with E hE
  exact (log_inv_referencePMF π E hπpos hE (clockArgmin r E)).symm

/-- Row-wise reference-loss bound, conditional only on the coordinate
moments.  All logarithmic and winning-clock identities are discharged by the
literal clock law. -/
theorem referenceLossIntegral_le_of_coordinate
    {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (π r : κ → ℝ) (hπ : IsPMF π) (hπpos : ∀ i, 0 < π i)
    (hr : IsPMF r) (hrpos : ∀ i, 0 < r i)
    (hk : 2 ≤ Fintype.card κ)
    (hcoord : ∀ i,
      (∫ E : κ → ℝ, clockCoordinateIntegrand π i E ∂clockLaw κ) ≤ π i) :
    (∫ E : κ → ℝ,
      Real.log (1 / referencePMF π E (clockArgmin r E)) ∂clockLaw κ) ≤
      2 * (∑ i, r i * Real.log (r i / π i)) +
        SharedRace.logTwo * (1 - ∑ i, r i ^ 2) := by
  have hπtotal : ∑ i, π i = 1 := by simpa [mass] using hπ.total
  have hrtotal : ∑ i, r i = 1 := by simpa [mass] using hr.total
  apply referenceLossIntegral_le (clockLaw κ) π r id (clockArgmin r)
    hπpos (ae_clockLaw_pos (κ := κ))
    (integrable_log_normRaceZ π hπpos)
    (integrable_log_raceRatio_clockArgmin
      π r hπpos hπtotal hrpos hrtotal hk)
    (integrable_normClock_clockArgmin r)
    (normalizedRaceLogIntegral_le_of_coordinate π hπ hπpos hk hcoord)
  · simpa only [id_eq] using
      integral_log_raceRatio_clockArgmin_eq
        π r hπpos hπtotal hrpos hrtotal hk
  · simpa only [id_eq] using
      integral_normClock_clockArgmin_eq r hrpos hrtotal

private lemma lexMax_eq_of_le_iff
    {Ω Ω' ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (F : Ω → ι → ℝ) (G : Ω' → ι → ℝ) (ω : Ω) (ω' : Ω')
    (hord : ∀ a b, F ω a ≤ F ω b ↔ G ω' a ≤ G ω' b) :
    lexMax F ω = lexMax G ω' := by
  let a : ι := lexMax G ω'
  apply (lexMax_eq_iff F ω a).2
  have ha : List.argmax (G ω') Finset.univ.toList = some a :=
    (lexMax_eq_iff G ω' a).1 rfl
  rw [List.argmax_eq_some_iff] at ha ⊢
  refine ⟨ha.1, ?_, ?_⟩
  · intro b hb
    exact (hord b a).2 (ha.2.1 b hb)
  · intro b hb hFab
    exact ha.2.2 b hb ((hord a b).1 hFab)

/-- The shared lexicographic tie-break is preserved exactly by the
exponential-clock/Gumbel change of variables. -/
theorem weightedLexWinner_clock_eq_argmin
    {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (t E : κ → ℝ) (ht : ∀ i, 0 < t i) (hE : ∀ i, 0 < E i) :
    weightedLexWinner t (fun i => -Real.log (E i)) = clockArgmin t E := by
  let Fs : (κ → ℝ) → κ → ℝ := fun G i => Real.log (t i) + G i
  let Fc : (κ → ℝ) → κ → ℝ := fun W i => -(W i / t i)
  change lexMax Fs (fun i => -Real.log (E i)) = lexMax Fc E
  apply lexMax_eq_of_le_iff Fs Fc (fun i => -Real.log (E i)) E
  intro a b
  have hscore (i : κ) :
      Fs (fun j => -Real.log (E j)) i = -Real.log (E i / t i) := by
    dsimp only [Fs]
    rw [Real.log_div (hE i).ne' (ht i).ne']
    ring
  have hra (i : κ) : 0 < E i / t i := div_pos (hE i) (ht i)
  rw [hscore a, hscore b]
  change -Real.log (E a / t a) ≤ -Real.log (E b / t b) ↔
    -(E a / t a) ≤ -(E b / t b)
  rw [neg_le_neg_iff, neg_le_neg_iff]
  exact Real.strictMonoOn_log.le_iff_le (hra b) (hra a)

private lemma measurable_sharedEntropy_integrand
    {Ω : Type u} {κ : Type} [Fintype Ω] [Fintype κ]
    [DecidableEq Ω] [DecidableEq κ] [Nonempty κ]
    (μ : Ω → ℝ) (r : Ω → κ → ℝ) :
    Measurable (fun G : κ → ℝ => H (push (sharedWinner r G) μ)) := by
  letI : MeasurableSpace κ := ⊤
  let A : (κ → ℝ) → (Ω → κ) := fun G z => sharedWinner r G z
  let F : (Ω → κ) → ℝ := fun a => H (push a μ)
  have hA : Measurable A := by
    apply measurable_pi_lambda
    intro z
    dsimp only [A, sharedWinner, weightedLexWinner]
    apply measurable_lexMax
    intro i
    exact measurable_const.add (measurable_pi_apply i)
  have hF : Measurable F := measurable_of_finite F
  exact hF.comp hA

/-- The Gumbel and exponential-clock formulations of shared-race entropy
agree.  Positivity is needed only on posterior rows in the source support. -/
theorem sharedRaceEntropy_eq_clockSharedRaceEntropy
    {Ω : Type u} {κ : Type} [Fintype Ω] [Fintype κ]
    [DecidableEq Ω] [DecidableEq κ] [Nonempty κ]
    {μ : Ω → ℝ} {r : Ω → κ → ℝ}
    (hrpos : ∀ z, μ z ≠ 0 → ∀ i, 0 < r z i) :
    sharedRaceEntropy μ r = clockSharedRaceEntropy μ r := by
  let F : (κ → ℝ) → (κ → ℝ) := fun E i => -Real.log (E i)
  have hF : Measurable F := measurable_pi_lambda _ fun i =>
    (Real.measurable_log.comp (measurable_pi_apply i)).neg
  have hg : AEStronglyMeasurable
      (fun G : κ → ℝ => H (push (sharedWinner r G) μ)) (seedLaw κ) :=
    (measurable_sharedEntropy_integrand μ r).aestronglyMeasurable
  have hpush : ∀ᵐ E ∂clockLaw κ,
      push (sharedWinner r (F E)) μ =
        push (fun z => clockArgmin (r z) E) μ := by
    filter_upwards [ae_clockLaw_pos (κ := κ)] with E hE
    funext i
    unfold push
    simp_rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro z _hz
    by_cases hz : μ z = 0
    · simp [hz]
    · have hw := weightedLexWinner_clock_eq_argmin
        (r z) E (hrpos z hz) hE
      have heq : sharedWinner r (F E) z = clockArgmin (r z) E := by
        simpa only [sharedWinner, F] using hw
      rw [heq]
  unfold sharedRaceEntropy clockSharedRaceEntropy seedLaw
  rw [integral_map hF.aemeasurable hg]
  apply integral_congr_ae
  filter_upwards [hpush] with E hE
  rw [hE]

end SharedRace

private lemma winnerResidualClock_pos
    {κ : Type} [Fintype κ] [DecidableEq κ]
    (t : κ → ℝ) (ht : ∀ i, 0 < t i) (a : κ) (E : κ → ℝ)
    (hE : ∀ i, 0 < E i) (ha : strictClockWin t a E) :
    ∀ i, 0 < winnerResidualClock t a E i := by
  intro i
  by_cases hi : i = a
  · subst i
    rw [winnerResidualClock_apply_winner]
    exact div_pos (hE a) (ht a)
  · have hstrict := ha i hi
    have hscaled : (E a / t a) * t i < E i :=
      (lt_div_iff₀ (ht i)).mp hstrict
    rw [winnerResidualClock_apply_loser t a i hi E]
    nlinarith

private lemma pmf_coordinate_lt_one_of_ne
    {κ : Type} [Fintype κ] [DecidableEq κ]
    (t : κ → ℝ) (ht : ∀ i, 0 < t i) (htotal : ∑ i, t i = 1)
    (i a : κ) (hia : a ≠ i) : t i < 1 := by
  have haMem : a ∈ (univ : Finset κ).erase i := by simp [hia]
  have haLe : t a ≤ ∑ b ∈ (univ : Finset κ).erase i, t b :=
    Finset.single_le_sum (fun b _ => (ht b).le) haMem
  have hrest : 0 < ∑ b ∈ (univ : Finset κ).erase i, t b :=
    (ht a).trans_le haLe
  have hsplit := Finset.sum_erase_add (univ : Finset κ) t
    (Finset.mem_univ i)
  rw [htotal] at hsplit
  linarith

private lemma mobius_pairRatio
    {p u v : ℝ} (hp : 0 < p) (hu : 0 < u) (hv : 0 < v) :
    SharedRace.mobius p (u / (u + v)) =
      p * u / (p * u + v) := by
  have huv : 0 < u + v := add_pos hu hv
  have hpv : 0 < p * u + v := add_pos (mul_pos hp hu) hv
  have hforward :
      p * (u / (u + v)) + 1 - u / (u + v) =
        (p * u + v) / (u + v) := by
    field_simp [huv.ne']
    ring
  unfold SharedRace.mobius
  rw [hforward]
  field_simp [huv.ne', hpv.ne']

private lemma loser_normalized_difference_identity
    {p u v s : ℝ} (hp : 0 < p) (hu : 0 < u) (hv : 0 < v)
    (hs : 0 < s) :
    (p * u + v) / s - u / s =
      ((u + v) / s) *
        ((p - p * u / (p * u + v)) /
          (p + (1 - p) * (p * u / (p * u + v)))) := by
  have huv : 0 < u + v := add_pos hu hv
  have hpv : 0 < p * u + v := add_pos (mul_pos hp hu) hv
  have hqden :
      p + (1 - p) * (p * u / (p * u + v)) =
        p * (u + v) / (p * u + v) := by
    field_simp [hpv.ne']
    ring
  have hqdenPos : 0 < p + (1 - p) * (p * u / (p * u + v)) := by
    rw [hqden]
    positivity
  rw [hqden]
  field_simp [hs.ne', hpv.ne', huv.ne', hp.ne']

/-- Pointwise form of a losing coordinate after the fixed-winner residual
transformation.  The split of the two distinguished fresh clocks is sent
through the Möbius map, while their normalized sum carries the shape-two
beta exponent. -/
private lemma clockCoordinateIntegrand_loser_eq
    {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (t : κ → ℝ) (ht : ∀ i, 0 < t i) (htotal : ∑ i, t i = 1)
    (a i : κ) (hai : a ≠ i) (E : κ → ℝ) (hE : ∀ j, 0 < E j)
    (ha : strictClockWin t a E) :
    SharedRace.clockCoordinateIntegrand t i E =
      let W := winnerResidualClock t a E
      let v := W a / (W a + W i)
      let x := SharedRace.mobius (t i) v
      x ^ 2 * Real.exp
        ((Fintype.card κ : ℝ) *
          ((W a + W i) / SharedRace.clockTotal W) *
            SharedRace.loserExponent (t i) x) := by
  let W : κ → ℝ := winnerResidualClock t a E
  let v : ℝ := W a / (W a + W i)
  let x : ℝ := SharedRace.mobius (t i) v
  have hW : ∀ j, 0 < W j :=
    winnerResidualClock_pos t ht a E hE ha
  have hx : x = t i * W a / (t i * W a + W i) := by
    dsimp only [x, v]
    exact mobius_pairRatio (ht i) (hW a) (hW i)
  have hratio : SharedRace.raceRatio t E i = x := by
    rw [raceRatio_loser_eq_residual t ht a i hai.symm E ha]
    exact hx.symm
  have htotalW : 0 < SharedRace.clockTotal W :=
    SharedRace.clockTotal_pos W hW
  have hdiff :
      SharedRace.normClock E i - SharedRace.normRaceMin t E =
        ((W a + W i) / SharedRace.clockTotal W) *
          ((t i - x) / (t i + (1 - t i) * x)) := by
    rw [normClock_loser_eq_residual t ht htotal a i hai.symm E,
      normRaceMin_eq_residual t ht htotal a E ha]
    unfold SharedRace.normClock
    change
      (t i * W a + W i) / SharedRace.clockTotal W -
          W a / SharedRace.clockTotal W = _
    calc
      (t i * W a + W i) / SharedRace.clockTotal W -
          W a / SharedRace.clockTotal W =
          ((W a + W i) / SharedRace.clockTotal W) *
            ((t i - t i * W a / (t i * W a + W i)) /
              (t i + (1 - t i) *
                (t i * W a / (t i * W a + W i)))) :=
        loser_normalized_difference_identity (ht i) (hW a) (hW i) htotalW
      _ = ((W a + W i) / SharedRace.clockTotal W) *
          ((t i - x) / (t i + (1 - t i) * x)) := by rw [hx]
  dsimp only
  rw [SharedRace.clockCoordinateIntegrand, hratio, hdiff]
  unfold SharedRace.loserExponent
  congr 2
  ring

/-- Fresh-clock integrand common to every losing winner cell for a fixed
target coordinate. -/
private noncomputable def freshLoserCoordinateIntegrand
    {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (p : ℝ) (a i : κ) (W : κ → ℝ) : ℝ :=
  let v := W a / (W a + W i)
  let x := SharedRace.mobius p v
  x ^ 2 * Real.exp
    ((Fintype.card κ : ℝ) *
      ((W a + W i) / SharedRace.clockTotal W) *
        SharedRace.loserExponent p x)

private lemma pairMobiusIntegrand_comp_eq_freshLoser
    {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (p : ℝ) (a i : κ) (W : κ → ℝ) :
    SharedRace.pairMobiusIntegrand p
        ((Fintype.card κ : ℝ) * (W a + W i) /
            SharedRace.clockTotal W,
          W a / (W a + W i)) =
      freshLoserCoordinateIntegrand p a i W := by
  unfold SharedRace.pairMobiusIntegrand
    freshLoserCoordinateIntegrand
  dsimp only
  congr 2
  ring

private lemma measurable_freshLoserCoordinateIntegrand
    {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (p : ℝ) (a i : κ) : Measurable (freshLoserCoordinateIntegrand p a i) := by
  let v : (κ → ℝ) → ℝ := fun W => W a / (W a + W i)
  let x : (κ → ℝ) → ℝ := fun W => SharedRace.mobius p (v W)
  have hv : Measurable v := by
    dsimp only [v]
    fun_prop
  have hx : Measurable x := by
    dsimp only [x]
    unfold SharedRace.mobius
    fun_prop
  have hpair : Measurable (fun W : κ → ℝ =>
      (W a + W i) / SharedRace.clockTotal W) :=
    ((measurable_pi_apply a).add (measurable_pi_apply i)).div
      SharedRace.measurable_clockTotal
  have hloser : Measurable (fun W =>
      SharedRace.loserExponent p (x W)) := by
    unfold SharedRace.loserExponent
    fun_prop
  have hexponent : Measurable (fun W =>
      (Fintype.card κ : ℝ) *
        ((W a + W i) / SharedRace.clockTotal W) *
          SharedRace.loserExponent p (x W)) :=
    (measurable_const.mul hpair).mul hloser
  unfold freshLoserCoordinateIntegrand
  change Measurable (fun W => x W ^ 2 * Real.exp
    ((Fintype.card κ : ℝ) *
      ((W a + W i) / SharedRace.clockTotal W) *
        SharedRace.loserExponent p (x W)))
  exact (hx.pow_const 2).mul (Real.measurable_exp.comp hexponent)

/-- The fresh losing-pair statistic is integrable.  This is obtained from
the already bounded coordinate statistic on any positive-mass losing cell
and the exact residual-clock pushforward. -/
private lemma integrable_freshLoserCoordinateIntegrand
    {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (t : κ → ℝ) (ht : ∀ i, 0 < t i) (htotal : ∑ i, t i = 1)
    (a i : κ) (hai : a ≠ i) :
    Integrable (freshLoserCoordinateIntegrand (t i) a i) (clockLaw κ) := by
  let cell : Set (κ → ℝ) := {E | strictClockWin t a E}
  let f := freshLoserCoordinateIntegrand (t i) a i
  have hcoord : Integrable (SharedRace.clockCoordinateIntegrand t i)
      ((clockLaw κ).restrict cell) :=
    (SharedRace.clockCoordinateIntegrand_integrable t ht i).mono_measure
      Measure.restrict_le_self
  have hpoint :
      (fun E => SharedRace.clockCoordinateIntegrand t i E) =ᵐ[
        (clockLaw κ).restrict cell]
      fun E => f (winnerResidualClock t a E) := by
    filter_upwards [ae_restrict_of_ae (SharedRace.ae_clockLaw_pos (κ := κ)),
      ae_restrict_mem (strictClockWin_measurableSet t a)] with E hE ha
    simpa only [f, freshLoserCoordinateIntegrand] using
      clockCoordinateIntegrand_loser_eq t ht htotal a i hai E hE ha
  have hcomp : Integrable (fun E => f (winnerResidualClock t a E))
      ((clockLaw κ).restrict cell) := hcoord.congr hpoint
  have hmap := winnerResidualClock_restrict_law t ht htotal a
  have hfstrong : AEStronglyMeasurable f
      (Measure.map (winnerResidualClock t a) ((clockLaw κ).restrict cell)) := by
    exact (measurable_freshLoserCoordinateIntegrand (t i) a i).aestronglyMeasurable
  have hscaled : Integrable f (ENNReal.ofReal (t a) • clockLaw κ) := by
    rw [← hmap]
    exact (integrable_map_measure hfstrong
      (winnerResidualClock_measurable t a).aemeasurable).2 hcomp
  have hmass : ENNReal.ofReal (t a) ≠ 0 := by
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (ht a))
  exact (integrable_smul_measure
    hmass (by simp)).1 hscaled

/-- Exact fresh losing-pair moment in the nondegenerate `k ≥ 3` branch. -/
private theorem integral_freshLoserCoordinate_eq_beta
    {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (a i : κ) (hai : a ≠ i) (hk : 3 ≤ Fintype.card κ) :
    (∫ W, freshLoserCoordinateIntegrand p a i W ∂clockLaw κ) =
      ∫ v : ℝ in 0..1,
        SharedRace.loserBetaIntegrand (Fintype.card κ) p
          (SharedRace.mobius p v) := by
  calc
    (∫ W, freshLoserCoordinateIntegrand p a i W ∂clockLaw κ) =
        ∫ W, SharedRace.pairMobiusIntegrand p
          ((Fintype.card κ : ℝ) * (W a + W i) /
              SharedRace.clockTotal W,
            W a / (W a + W i)) ∂clockLaw κ := by
      apply MeasureTheory.integral_congr_ae
      exact Filter.Eventually.of_forall fun W =>
        (pairMobiusIntegrand_comp_eq_freshLoser p a i W).symm
    _ = _ :=
      SharedRace.integral_pairMobiusIntegrand_clockLaw_eq_beta
        a i hai hk hp0 hp1

/-- Exact fresh losing-pair moment in the degenerate two-label branch. -/
private theorem integral_freshLoserCoordinate_eq_degenerate
    {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (p : ℝ) (a i : κ) (hai : a ≠ i) (hk : Fintype.card κ = 2) :
    (∫ W, freshLoserCoordinateIntegrand p a i W ∂clockLaw κ) =
      ∫ v : ℝ in 0..1,
        SharedRace.loserDegenerateIntegrand p
          (SharedRace.mobius p v) := by
  calc
    (∫ W, freshLoserCoordinateIntegrand p a i W ∂clockLaw κ) =
        ∫ W, SharedRace.pairMobiusIntegrand p
          ((Fintype.card κ : ℝ) * (W a + W i) /
              SharedRace.clockTotal W,
            W a / (W a + W i)) ∂clockLaw κ := by
      apply MeasureTheory.integral_congr_ae
      exact Filter.Eventually.of_forall fun W =>
        (pairMobiusIntegrand_comp_eq_freshLoser p a i W).symm
    _ = _ :=
      SharedRace.integral_pairMobiusIntegrand_clockLaw_eq_degenerate
        a i hai hk p

private theorem clockCoordinate_loserCell_integral_eq_fresh
    {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (t : κ → ℝ) (ht : ∀ i, 0 < t i) (htotal : ∑ i, t i = 1)
    (a i : κ) (hai : a ≠ i) :
    (∫ E, SharedRace.clockCoordinateIntegrand t i E
        ∂((clockLaw κ).restrict {E | strictClockWin t a E})) =
      t a * ∫ W, freshLoserCoordinateIntegrand (t i) a i W
        ∂clockLaw κ := by
  have hpoint :
      (fun E => SharedRace.clockCoordinateIntegrand t i E) =ᵐ[
        (clockLaw κ).restrict {E | strictClockWin t a E}]
      fun E => freshLoserCoordinateIntegrand (t i) a i
        (winnerResidualClock t a E) := by
    filter_upwards [ae_restrict_of_ae (SharedRace.ae_clockLaw_pos (κ := κ)),
      ae_restrict_mem (strictClockWin_measurableSet t a)] with E hE ha
    simpa only [freshLoserCoordinateIntegrand] using
      clockCoordinateIntegrand_loser_eq t ht htotal a i hai E hE ha
  calc
    (∫ E, SharedRace.clockCoordinateIntegrand t i E
        ∂((clockLaw κ).restrict {E | strictClockWin t a E})) =
        ∫ E, freshLoserCoordinateIntegrand (t i) a i
            (winnerResidualClock t a E)
          ∂((clockLaw κ).restrict {E | strictClockWin t a E}) :=
      integral_congr_ae hpoint
    _ = t a * ∫ W, freshLoserCoordinateIntegrand (t i) a i W
          ∂clockLaw κ :=
      integral_comp_winnerResidualClock t ht htotal a
        (freshLoserCoordinateIntegrand (t i) a i)
        (measurable_freshLoserCoordinateIntegrand (t i) a i)

/-- Finite winner-cell bookkeeping for a coordinate, once the common fresh
loser moment has been identified. -/
private theorem clockCoordinate_integral_eq_of_loserMoment
    {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (t : κ → ℝ) (ht : ∀ i, 0 < t i) (htotal : ∑ i, t i = 1)
    (hk : 2 ≤ Fintype.card κ) (i : κ) (J : ℝ)
    (hJ : ∀ a, a ≠ i →
      (∫ W, freshLoserCoordinateIntegrand (t i) a i W ∂clockLaw κ) = J) :
    (∫ E, SharedRace.clockCoordinateIntegrand t i E ∂clockLaw κ) =
      t i * SharedRace.betaOneExpMoment (Fintype.card κ)
          (-SharedRace.logTwo * (1 - t i)) +
        (1 - t i) * J := by
  have hpartition := integral_clock_eq_sum_strictClockWin t ht htotal
    (SharedRace.clockCoordinateIntegrand t i)
    (SharedRace.clockCoordinateIntegrand_integrable t ht i)
  have hiMem : i ∈ (univ : Finset κ) := Finset.mem_univ i
  have hsplit := Finset.sum_erase_add (univ : Finset κ)
    (fun a => ∫ E, SharedRace.clockCoordinateIntegrand t i E
      ∂((clockLaw κ).restrict {E | strictClockWin t a E})) hiMem
  have hloserSum :
      (∑ a ∈ (univ : Finset κ).erase i,
        ∫ E, SharedRace.clockCoordinateIntegrand t i E
          ∂((clockLaw κ).restrict {E | strictClockWin t a E})) =
        (∑ a ∈ (univ : Finset κ).erase i, t a) * J := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a ha
    have hai : a ≠ i := (Finset.mem_erase.mp ha).1
    rw [clockCoordinate_loserCell_integral_eq_fresh t ht htotal a i hai,
      hJ a hai]
  have htErase : (∑ a ∈ (univ : Finset κ).erase i, t a) = 1 - t i := by
    have h := Finset.sum_erase_add (univ : Finset κ) t hiMem
    rw [htotal] at h
    linarith
  rw [hpartition, ← hsplit, hloserSum, htErase,
    clockCoordinate_winnerCell_integral_eq t ht htotal hk i]
  ring

/-- Once the fresh losing pair has the shape-two beta integral, the scalar
allocation theorem closes the coordinate estimate for `k ≥ 3`. -/
private theorem clockCoordinate_integral_le_of_betaLoserMoment
    {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (t : κ → ℝ) (ht : ∀ i, 0 < t i) (htotal : ∑ i, t i = 1)
    (hk : 3 ≤ Fintype.card κ) (i : κ)
    (hJ : ∀ a, a ≠ i →
      (∫ W, freshLoserCoordinateIntegrand (t i) a i W ∂clockLaw κ) =
        ∫ v : ℝ in 0..1,
          SharedRace.loserBetaIntegrand (Fintype.card κ) (t i)
            (SharedRace.mobius (t i) v)) :
    (∫ E, SharedRace.clockCoordinateIntegrand t i E ∂clockLaw κ) ≤
      t i := by
  have hkTwo : 2 ≤ Fintype.card κ := by omega
  obtain ⟨a, hai⟩ := Fintype.exists_ne_of_one_lt_card
    (show 1 < Fintype.card κ by omega) i
  have htiOne : t i < 1 :=
    pmf_coordinate_lt_one_of_ne t ht htotal i a hai
  rw [clockCoordinate_integral_eq_of_loserMoment t ht htotal hkTwo i
    (∫ v : ℝ in 0..1,
      SharedRace.loserBetaIntegrand (Fintype.card κ) (t i)
        (SharedRace.mobius (t i) v)) hJ]
  exact SharedRace.betaCoordinateContribution_le
    (Fintype.card κ) hk (ht i) htiOne

/-- Degenerate two-coordinate companion of
`clockCoordinate_integral_le_of_betaLoserMoment`. -/
private theorem clockCoordinate_integral_le_of_twoLoserMoment
    {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (t : κ → ℝ) (ht : ∀ i, 0 < t i) (htotal : ∑ i, t i = 1)
    (hk : Fintype.card κ = 2) (i : κ)
    (hJ : ∀ a, a ≠ i →
      (∫ W, freshLoserCoordinateIntegrand (t i) a i W ∂clockLaw κ) =
        ∫ v : ℝ in 0..1,
          SharedRace.loserDegenerateIntegrand (t i)
            (SharedRace.mobius (t i) v)) :
    (∫ E, SharedRace.clockCoordinateIntegrand t i E ∂clockLaw κ) ≤
      t i := by
  have hkTwo : 2 ≤ Fintype.card κ := hk.ge
  obtain ⟨a, hai⟩ := Fintype.exists_ne_of_one_lt_card
    (show 1 < Fintype.card κ by omega) i
  have htiOne : t i < 1 :=
    pmf_coordinate_lt_one_of_ne t ht htotal i a hai
  rw [clockCoordinate_integral_eq_of_loserMoment t ht htotal hkTwo i
    (∫ v : ℝ in 0..1,
      SharedRace.loserDegenerateIntegrand (t i)
        (SharedRace.mobius (t i) v)) hJ, hk]
  exact SharedRace.twoCoordinateContribution_le (ht i) htiOne

namespace SharedRace

/-- The normalized shared-race reference moment is bounded by its PMF
coordinate.  The proof partitions by the winning clock, evaluates the common
fresh losing pair through the exact pair-clock law, and invokes the scalar
beta allocation theorem (including its separate two-label branch). -/
theorem clockCoordinateIntegral_le
    {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (t : κ → ℝ) (ht : IsPMF t) (htpos : ∀ i, 0 < t i)
    (hk : 2 ≤ Fintype.card κ) (i : κ) :
    (∫ E : κ → ℝ, clockCoordinateIntegrand t i E ∂clockLaw κ) ≤ t i := by
  have htotal : ∑ j, t j = 1 := by
    simpa only [mass] using ht.total
  by_cases hkTwo : Fintype.card κ = 2
  · apply clockCoordinate_integral_le_of_twoLoserMoment
      t htpos htotal hkTwo i
    intro a hai
    exact integral_freshLoserCoordinate_eq_degenerate
      (t i) a i hai hkTwo
  · have hkThree : 3 ≤ Fintype.card κ := by omega
    apply clockCoordinate_integral_le_of_betaLoserMoment
      t htpos htotal hkThree i
    intro a hai
    have htiOne : t i < 1 :=
      pmf_coordinate_lt_one_of_ne t htpos htotal i a hai
    exact integral_freshLoserCoordinate_eq_beta
      (t i) (htpos i) htiOne a i hai hkThree

end SharedRace

private lemma compProd_raceLosingKernel_eq_map {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D) (b : K.κ) (z : α × β)
    (μ : Measure ℝ) [SFinite μ] :
    μ ⊗ₘ raceLosingKernel K b z =
      Measure.map
        (fun ue : ℝ × (losingIndex K b → ℝ) =>
          (ue.1, fun c => ue.1 * (K.sigma c.1 z / K.sigma b z) + ue.2 c))
        (μ.prod (losingReference K b)) := by
  letI : IsProbabilityMeasure (expMeasure 1) :=
    isProbabilityMeasure_expMeasure zero_lt_one
  letI : IsProbabilityMeasure (losingReference K b) := by
    unfold losingReference
    infer_instance
  letI : IsMarkovKernel (raceLosingKernel K b z) :=
    raceLosingKernel_isMarkov K b z
  let r : losingIndex K b → ℝ := fun c =>
    K.sigma c.1 z / K.sigma b z
  change μ ⊗ₘ raceLosingKernel K b z =
    Measure.map
      (fun ue : ℝ × (losingIndex K b → ℝ) =>
        (ue.1, fun c => ue.1 * r c + ue.2 c))
      (μ.prod (losingReference K b))
  apply Measure.ext
  intro s hs
  rw [Measure.compProd_apply hs,
    Measure.map_apply (by fun_prop) hs,
    Measure.prod_apply (hs.preimage (by fun_prop))]
  apply lintegral_congr
  intro u
  rw [raceLosingKernel_apply]
  change (Measure.pi fun c : losingIndex K b =>
      (expMeasure 1).map (fun e => u * r c + e)) (Prod.mk u ⁻¹' s) = _
  rw [← Measure.pi_map_pi fun c => (by fun_prop :
    AEMeasurable (fun e : ℝ => u * r c + e) (expMeasure 1))]
  unfold losingReference
  rw [Measure.map_apply (by fun_prop) (measurable_prodMk_left hs)]
  congr 1

private lemma rawClockSplit_restrict_factorization {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D) (b : K.κ) (z : α × β)
    (hz : z ∈ support p) :
    Measure.map
        (fun E : K.κ → ℝ => (E b, fun c : losingIndex K b => E c.1))
        ((clockLaw K.κ).restrict
          {E | strictClockWin (fun c => K.sigma c z) b E}) =
      ENNReal.ofReal (K.sigma b z) •
        (K.clockLawGiven b z ⊗ₘ raceLosingKernel K b z) := by
  let t : K.κ → ℝ := fun c => K.sigma c z
  have ht : ∀ c, 0 < t c := fun c => K.sigma_pos c z hz
  have htotal : ∑ c, t c = 1 := raceSigma_sum_eq_one K z hz
  have htb : 0 < t b := ht b
  let ρ : Measure (losingIndex K b → ℝ) :=
    weightedLosingExcessLaw t b
  let embed : (losingIndex K b → ℝ) → K.κ → ℝ := insertWinnerZero b
  let norm : (K.κ → ℝ) → ℝ × (K.κ → ℝ) := fun E =>
    (E b / t b, fun c => E c / t c - E b / t b)
  let raw : (K.κ → ℝ) → ℝ × (losingIndex K b → ℝ) := fun E =>
    (E b, fun c => E c.1)
  let reconstruct : (ℝ × (K.κ → ℝ)) →
      ℝ × (losingIndex K b → ℝ) := fun sr =>
    (t b * sr.1, fun c => t c.1 * (sr.2 c.1 + sr.1))
  let rawLose : (ℝ × (losingIndex K b → ℝ)) →
      ℝ × (losingIndex K b → ℝ) := fun sr =>
    (t b * sr.1, fun c => t c.1 * (sr.2 c + sr.1))
  let scale : (ℝ × (losingIndex K b → ℝ)) →
      ℝ × (losingIndex K b → ℝ) := fun sr =>
    (t b * sr.1, fun c => t c.1 * sr.2 c)
  let shift : (ℝ × (losingIndex K b → ℝ)) →
      ℝ × (losingIndex K b → ℝ) := fun ue =>
    (ue.1, fun c => ue.1 * (t c.1 / t b) + ue.2 c)
  have hnorm : Measurable norm := by fun_prop
  have hraw : Measurable raw := by fun_prop
  have hreconstruct : Measurable reconstruct := by fun_prop
  have hembed : Measurable embed := insertWinnerZero_measurable b
  have hrawLose : Measurable rawLose := by fun_prop
  have hscale : Measurable scale := by fun_prop
  have hshift : Measurable shift := by fun_prop
  have hraw_norm : raw = reconstruct ∘ norm := by
    funext E
    apply Prod.ext
    · dsimp only [raw, reconstruct, norm, Function.comp_apply]
      field_simp [htb.ne']
    · funext c
      dsimp only [raw, reconstruct, norm, Function.comp_apply]
      field_simp [htb.ne', (ht c.1).ne']
      ring
  have hrec_embed : reconstruct ∘ Prod.map id embed = rawLose := by
    funext sr
    apply Prod.ext
    · rfl
    · funext c
      simp [reconstruct, rawLose, embed, insertWinnerZero, c.2]
  have hlose_scale : rawLose = shift ∘ scale := by
    funext sr
    apply Prod.ext
    · rfl
    · funext c
      dsimp only [rawLose, shift, scale, Function.comp_apply]
      field_simp [htb.ne']
      ring
  have hscale_eq : scale = Prod.map (fun s : ℝ => t b * s)
      (fun R : losingIndex K b → ℝ => fun c => t c.1 * R c) := by
    funext sr
    rfl
  letI : IsProbabilityMeasure (expMeasure 1) :=
    isProbabilityMeasure_expMeasure zero_lt_one
  letI (c : losingIndex K b) : IsProbabilityMeasure (expMeasure (t c.1)) :=
    isProbabilityMeasure_expMeasure (ht c.1)
  letI : IsProbabilityMeasure ρ := by
    dsimp [ρ, weightedLosingExcessLaw]
    infer_instance
  letI : IsProbabilityMeasure (losingReference K b) := by
    unfold losingReference
    infer_instance
  letI : IsProbabilityMeasure (K.clockLawGiven b z) := by
    unfold Clustering.clockLawGiven
    exact isProbabilityMeasure_expMeasure (one_div_pos.mpr htb)
  letI : IsMarkovKernel (raceLosingKernel K b z) :=
    raceLosingKernel_isMarkov K b z
  let A : Measure ℝ := ENNReal.ofReal (t b) • expMeasure 1
  have hfirst : Measure.map (fun s : ℝ => t b * s) A =
      ENNReal.ofReal (t b) • K.clockLawGiven b z := by
    dsimp [A]
    rw [Measure.map_smul, map_mul_expMeasure_one htb]
    rfl
  have hsecond : Measure.map
      (fun R : losingIndex K b → ℝ => fun c => t c.1 * R c) ρ =
      losingReference K b := by
    dsimp [ρ, losingReference]
    exact map_weightedLosingExcess_scale t ht b
  change Measure.map raw
      ((clockLaw K.κ).restrict {E | strictClockWin t b E}) = _
  calc
    Measure.map raw
        ((clockLaw K.κ).restrict {E | strictClockWin t b E}) =
        Measure.map reconstruct
          (Measure.map norm
            ((clockLaw K.κ).restrict {E | strictClockWin t b E})) := by
      rw [hraw_norm, Measure.map_map hreconstruct hnorm]
    _ = Measure.map reconstruct
        (A.prod (Measure.map embed ρ)) := by
      rw [clock_min_excess_restrict_factorization t ht htotal b]
    _ = Measure.map rawLose (A.prod ρ) := by
      calc
        Measure.map reconstruct (A.prod (Measure.map embed ρ)) =
            Measure.map reconstruct
              ((Measure.map id A).prod (Measure.map embed ρ)) := by
          rw [Measure.map_id]
        _ = Measure.map reconstruct
            (Measure.map (Prod.map id embed) (A.prod ρ)) := by
          rw [← Measure.map_prod_map A ρ measurable_id hembed]
        _ = Measure.map (reconstruct ∘ Prod.map id embed) (A.prod ρ) :=
          Measure.map_map hreconstruct (measurable_id.prodMap hembed)
        _ = Measure.map rawLose (A.prod ρ) := by rw [hrec_embed]
    _ = Measure.map shift (Measure.map scale (A.prod ρ)) := by
      rw [hlose_scale, Measure.map_map hshift hscale]
    _ = Measure.map shift
        ((Measure.map (fun s : ℝ => t b * s) A).prod
          (Measure.map
            (fun R : losingIndex K b → ℝ => fun c => t c.1 * R c) ρ)) := by
      rw [hscale_eq, Measure.map_prod_map A ρ (by fun_prop) (by fun_prop)]
    _ = Measure.map shift
        ((ENNReal.ofReal (t b) • K.clockLawGiven b z).prod
          (losingReference K b)) := by
      rw [hfirst, hsecond]
    _ = Measure.map shift
        (ENNReal.ofReal (t b) •
          ((K.clockLawGiven b z).prod (losingReference K b))) := by
      rw [Measure.prod_smul_left]
    _ = ENNReal.ofReal (t b) •
        Measure.map shift
          ((K.clockLawGiven b z).prod (losingReference K b)) := by
      rw [Measure.map_smul]
    _ = ENNReal.ofReal (K.sigma b z) •
        (K.clockLawGiven b z ⊗ₘ raceLosingKernel K b z) := by
      rw [compProd_raceLosingKernel_eq_map]

private lemma clusterSeed_split_factorization {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D) (b : K.κ) (z : α × β)
    (hz : z ∈ support p) :
    Measure.map (clusterClockSplit K b)
        (clusterSeedLawGivenWinner K b z) =
      K.clockLawGiven b z ⊗ₘ raceLosingKernel K b z := by
  have hs : 0 < K.sigma b z := K.sigma_pos b z hz
  let C : (K.κ → ℝ) → (K.κ → ℝ) := fun G c => Real.exp (-G c)
  let raw : (K.κ → ℝ) → ℝ × (losingIndex K b → ℝ) := fun E =>
    (E b, fun c => E c.1)
  have hC : Measurable C := by fun_prop
  have hraw : Measurable raw := by fun_prop
  have hsplit : clusterClockSplit K b = raw ∘ C := by
    rfl
  have hcell :
      {G : K.κ → ℝ | groupedClusterWinner K G z = b} =
        {G | weightedWinner (fun c => K.sigma c z) G = b} := by
    rfl
  unfold clusterSeedLawGivenWinner
  rw [if_neg hs.ne', Measure.map_smul]
  rw [hcell]
  calc
    (ENNReal.ofReal (K.sigma b z))⁻¹ •
        Measure.map (clusterClockSplit K b)
          ((seedLaw K.κ).restrict
            {G | weightedWinner (fun c => K.sigma c z) G = b}) =
        (ENNReal.ofReal (K.sigma b z))⁻¹ •
          Measure.map raw
            (Measure.map C
              ((seedLaw K.κ).restrict
                {G | weightedWinner (fun c => K.sigma c z) G = b})) := by
      rw [hsplit, Measure.map_map hraw hC]
    _ = (ENNReal.ofReal (K.sigma b z))⁻¹ •
        Measure.map raw
          ((clockLaw K.κ).restrict
            {E | strictClockWin (fun c => K.sigma c z) b E}) := by
      rw [weightedWinner_clock_restrict_map
        (fun c => K.sigma c z) (fun c => K.sigma_pos c z hz) b]
    _ = (ENNReal.ofReal (K.sigma b z))⁻¹ •
        (ENNReal.ofReal (K.sigma b z) •
          (K.clockLawGiven b z ⊗ₘ raceLosingKernel K b z)) := by
      rw [rawClockSplit_restrict_factorization K b z hz]
    _ = K.clockLawGiven b z ⊗ₘ raceLosingKernel K b z := by
      rw [smul_smul, ENNReal.inv_mul_cancel
        (ENNReal.ofReal_ne_zero_iff.mpr hs) ENNReal.ofReal_ne_top, one_smul]

private noncomputable def raceClockTilt {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D) (b : K.κ) (z : α × β)
    (u : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal
    (Real.exp (-((1 / K.sigma b z - 1) * u)))

private lemma raceClockTilt_measurable {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D) (b : K.κ) (z : α × β) :
    Measurable (raceClockTilt K b z) := by
  unfold raceClockTilt
  fun_prop

private lemma scalarClock_weighted_eq_withDensity {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D) (g b : K.κ) (z : α × β) :
    ENNReal.ofReal (scalarSource K g b z) • K.clockLawGiven b z =
      (expMeasure 1).withDensity (fun u =>
        ENNReal.ofReal (K.Q g z / scalarWinnerProb K g b) *
          raceClockTilt K b z u) := by
  have hP : 0 < scalarWinnerProb K g b := scalarWinnerProb_pos K g b
  by_cases hQ : K.Q g z = 0
  · simp [scalarSource, raceClockTilt, hQ]
  · have hz : z ∈ support p := by
      by_contra hz
      exact hQ ((K.Q_isContact g).2.1 z hz)
    have hs : 0 < K.sigma b z := K.sigma_pos b z hz
    have hQnonneg : 0 ≤ K.Q g z := (K.Q_isContact g).1.nonneg z
    have hcoeff :
        ENNReal.ofReal (scalarSource K g b z) =
          ENNReal.ofReal (K.Q g z / scalarWinnerProb K g b) *
            ENNReal.ofReal (K.sigma b z) := by
      rw [← ENNReal.ofReal_mul (div_nonneg hQnonneg hP.le)]
      congr 1
      unfold scalarSource
      ring
    have htilt :
        (expMeasure 1).withDensity (raceClockTilt K b z) =
          ENNReal.ofReal (K.sigma b z) • K.clockLawGiven b z := by
      unfold raceClockTilt Clustering.clockLawGiven
      exact expMeasure_one_tilt hs
    calc
      ENNReal.ofReal (scalarSource K g b z) • K.clockLawGiven b z =
          (ENNReal.ofReal (K.Q g z / scalarWinnerProb K g b) *
            ENNReal.ofReal (K.sigma b z)) • K.clockLawGiven b z := by
        rw [hcoeff]
      _ = ENNReal.ofReal (K.Q g z / scalarWinnerProb K g b) •
          (ENNReal.ofReal (K.sigma b z) • K.clockLawGiven b z) := by
        rw [smul_smul]
      _ = ENNReal.ofReal (K.Q g z / scalarWinnerProb K g b) •
          (expMeasure 1).withDensity (raceClockTilt K b z) := by
        rw [htilt]
      _ = (expMeasure 1).withDensity (fun u =>
          ENNReal.ofReal (K.Q g z / scalarWinnerProb K g b) *
            raceClockTilt K b z u) := by
        rw [← MeasureTheory.withDensity_smul
          (μ := expMeasure 1)
          (ENNReal.ofReal (K.Q g z / scalarWinnerProb K g b))
          (raceClockTilt_measurable K b z)]
        congr 1

private noncomputable def raceContextClockDensity {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D) (g b : K.κ) (u : ℝ) : ℝ≥0∞ :=
  ∑ z, ENNReal.ofReal (K.Q g z / scalarWinnerProb K g b) *
    raceClockTilt K b z u

private lemma raceContextClockDensity_measurable {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D) (g b : K.κ) :
    Measurable (raceContextClockDensity K g b) := by
  unfold raceContextClockDensity
  apply Finset.measurable_sum
  intro z _
  exact measurable_const.mul (raceClockTilt_measurable K b z)

private lemma scalarClockMarginal_eq_withDensity {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D) (g b : K.κ) :
    scalarClockMarginal K g b =
      (expMeasure 1).withDensity (raceContextClockDensity K g b) := by
  let f : (α × β) → ℝ → ℝ≥0∞ := fun z u =>
    ENNReal.ofReal (K.Q g z / scalarWinnerProb K g b) *
      raceClockTilt K b z u
  have hf : ∀ z, Measurable (f z) := fun z =>
    measurable_const.mul (raceClockTilt_measurable K b z)
  unfold scalarClockMarginal
  simp_rw [scalarClock_weighted_eq_withDensity K g b]
  change (∑ z, (expMeasure 1).withDensity (f z)) = _
  rw [← Measure.sum_fintype,
    ← MeasureTheory.withDensity_tsum (μ := expMeasure 1) hf]
  congr 1
  funext u
  rw [tsum_fintype]
  simp only [f, Finset.sum_apply, raceContextClockDensity]

private lemma raceClockTilt_real_eq {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D) (b : K.κ) (z : α × β)
    (u : ℝ) :
    Real.exp (-((1 / K.sigma b z - 1) * u)) =
      Real.exp u * Real.exp (-u / K.sigma b z) := by
  rw [← Real.exp_add]
  congr 1
  ring

private lemma raceContextClockDensity_eq {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D) (g b : K.κ) (u : ℝ) :
    raceContextClockDensity K g b u =
      ENNReal.ofReal
        (Real.exp u / scalarWinnerProb K g b * coneContextDensity K g b u) := by
  have hP : 0 < scalarWinnerProb K g b := scalarWinnerProb_pos K g b
  calc
    raceContextClockDensity K g b u =
        ∑ z, ENNReal.ofReal
          ((K.Q g z / scalarWinnerProb K g b) *
            Real.exp (-((1 / K.sigma b z - 1) * u))) := by
      unfold raceContextClockDensity raceClockTilt
      apply Finset.sum_congr rfl
      intro z _
      rw [ENNReal.ofReal_mul
        (div_nonneg ((K.Q_isContact g).1.nonneg z) hP.le)]
    _ = ENNReal.ofReal
        (∑ z, (K.Q g z / scalarWinnerProb K g b) *
          Real.exp (-((1 / K.sigma b z - 1) * u))) := by
      rw [ENNReal.ofReal_sum_of_nonneg]
      intro z _
      exact mul_nonneg
        (div_nonneg ((K.Q_isContact g).1.nonneg z) hP.le)
        (Real.exp_nonneg _)
    _ = ENNReal.ofReal
        (Real.exp u / scalarWinnerProb K g b *
          coneContextDensity K g b u) := by
      congr 1
      unfold coneContextDensity
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z _
      rw [raceClockTilt_real_eq K b z u]
      ring

private lemma raceContextClockDensity_mul_coneSource {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D) (g b : K.κ) (u : ℝ)
    (z : α × β) :
    raceContextClockDensity K g b u *
        ENNReal.ofReal (coneSource K g b u z) =
      ENNReal.ofReal (K.Q g z / scalarWinnerProb K g b) *
        raceClockTilt K b z u := by
  have hP : 0 < scalarWinnerProb K g b := scalarWinnerProb_pos K g b
  have hD : 0 < coneContextDensity K g b u :=
    coneContextDensity_pos K g b u
  have hQ : 0 ≤ K.Q g z := (K.Q_isContact g).1.nonneg z
  rw [raceContextClockDensity_eq K g b u]
  unfold coneSource raceClockTilt
  rw [← ENNReal.ofReal_mul
    (mul_nonneg (div_nonneg (Real.exp_nonneg _) hP.le) hD.le),
    ← ENNReal.ofReal_mul (div_nonneg hQ hP.le)]
  congr 1
  rw [raceClockTilt_real_eq K b z u]
  field_simp [hP.ne', hD.ne']

private lemma scalarClockMarginal_withDensity_coneSource
    {p : α × β → ℝ} {D : SeedSetup p} (K : Clustering D)
    (g b : K.κ) (z : α × β) :
    (scalarClockMarginal K g b).withDensity
        (fun u => ENNReal.ofReal (coneSource K g b u z)) =
      ENNReal.ofReal (scalarSource K g b z) • K.clockLawGiven b z := by
  have hcone : Measurable
      (fun u => ENNReal.ofReal (coneSource K g b u z)) :=
    ENNReal.measurable_ofReal.comp (coneSource_measurable K g b z)
  rw [scalarClockMarginal_eq_withDensity K g b,
    ← MeasureTheory.withDensity_mul (expMeasure 1)
      (raceContextClockDensity_measurable K g b) hcone]
  calc
    (expMeasure 1).withDensity
        (raceContextClockDensity K g b *
          fun u => ENNReal.ofReal (coneSource K g b u z)) =
        (expMeasure 1).withDensity (fun u =>
          ENNReal.ofReal (K.Q g z / scalarWinnerProb K g b) *
            raceClockTilt K b z u) := by
      apply MeasureTheory.withDensity_congr_ae
      exact Filter.Eventually.of_forall fun u =>
        raceContextClockDensity_mul_coneSource K g b u z
    _ = ENNReal.ofReal (scalarSource K g b z) •
        K.clockLawGiven b z :=
      (scalarClock_weighted_eq_withDensity K g b z).symm

private lemma withDensity_fst_compProd
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (κ : Kernel X Y) [SFinite μ] [IsSFiniteKernel κ]
    (f : X → ℝ≥0∞) (hf : Measurable f) :
    (μ ⊗ₘ κ).withDensity (fun xy => f xy.1) =
      (μ.withDensity f) ⊗ₘ κ := by
  ext s hs
  rw [MeasureTheory.withDensity_apply _ hs,
    ← MeasureTheory.lintegral_indicator hs,
    Measure.lintegral_compProd
      (show Measurable
          (fun xy => s.indicator (fun a => f a.1) xy) from
        (show Measurable (fun a : X × Y => f a.1) from
          hf.comp measurable_fst).indicator hs),
    Measure.compProd_apply hs,
    MeasureTheory.lintegral_withDensity_eq_lintegral_mul μ hf
      (Kernel.measurable_kernel_prodMk_left hs)]
  apply lintegral_congr
  intro x
  change (∫⁻ y, s.indicator (fun a => f a.1) (x, y) ∂κ x) =
    f x * κ x (Prod.mk x ⁻¹' s)
  calc
    (∫⁻ y, s.indicator (fun a => f a.1) (x, y) ∂κ x) =
        ∫⁻ y, f x * (Prod.mk x ⁻¹' s).indicator 1 y ∂κ x := by
      apply lintegral_congr
      intro y
      by_cases hxy : (x, y) ∈ s <;> simp [Set.indicator, hxy]
    _ = f x * ∫⁻ y, (Prod.mk x ⁻¹' s).indicator 1 y ∂κ x := by
      rw [MeasureTheory.lintegral_const_mul]
      exact (measurable_const.indicator (measurable_prodMk_left hs))
    _ = f x * κ x (Prod.mk x ⁻¹' s) := by
      rw [MeasureTheory.lintegral_indicator_one (measurable_prodMk_left hs)]

private lemma clockLawGiven_sFinite {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D) (b : K.κ) (z : α × β) :
    SFinite (K.clockLawGiven b z) := by
  unfold Clustering.clockLawGiven expMeasure gammaMeasure
  infer_instance

private lemma scalarClockMarginal_sFinite {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D) (g b : K.κ) :
    SFinite (scalarClockMarginal K g b) := by
  letI (z : α × β) : SFinite (K.clockLawGiven b z) :=
    clockLawGiven_sFinite K b z
  unfold scalarClockMarginal
  rw [← Measure.sum_fintype]
  infer_instance

private lemma clusterSeedContext_split_factorization {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D) (g b : K.κ) :
    Measure.map (clusterClockSplit K b)
        (clusterSeedContextMarginal K g b) =
      scalarClockMarginal K g b ⊗ₘ raceContextKernel K g b := by
  letI (z : α × β) : IsMarkovKernel (raceLosingKernel K b z) :=
    raceLosingKernel_isMarkov K b z
  letI (z : α × β) : IsSFiniteKernel
      ((raceLosingKernel K b z).withDensity
        (fun u (_ : losingIndex K b → ℝ) =>
          ENNReal.ofReal (coneSource K g b u z))) :=
    Kernel.IsSFiniteKernel.withDensity _ fun _ _ => ENNReal.ofReal_ne_top
  letI (z : α × β) : SFinite (K.clockLawGiven b z) :=
    clockLawGiven_sFinite K b z
  letI : SFinite (scalarClockMarginal K g b) :=
    scalarClockMarginal_sFinite K g b
  have hsplit := clusterClockSplit_measurable K b
  unfold clusterSeedContextMarginal
  calc
    Measure.map (clusterClockSplit K b)
        (∑ z, ENNReal.ofReal (scalarSource K g b z) •
          clusterSeedLawGivenWinner K b z) =
        ∑ z, Measure.map (clusterClockSplit K b)
          (ENNReal.ofReal (scalarSource K g b z) •
            clusterSeedLawGivenWinner K b z) :=
      Measure.map_finset_sum' hsplit.aemeasurable
    _ = ∑ z, ENNReal.ofReal (scalarSource K g b z) •
        (K.clockLawGiven b z ⊗ₘ raceLosingKernel K b z) := by
      apply Finset.sum_congr rfl
      intro z _
      rw [Measure.map_smul]
      by_cases hsource : scalarSource K g b z = 0
      · simp [hsource]
      · have hnum : K.Q g z * K.sigma b z ≠ 0 := by
          intro hzero
          apply hsource
          unfold scalarSource
          rw [hzero]
          simp
        have hz : z ∈ support p := by
          by_contra hz
          exact (mul_ne_zero_iff.mp hnum).1
            ((K.Q_isContact g).2.1 z hz)
        rw [clusterSeed_split_factorization K b z hz]
    _ = ∑ z,
        (scalarClockMarginal K g b).withDensity
            (fun u => ENNReal.ofReal (coneSource K g b u z)) ⊗ₘ
          raceLosingKernel K b z := by
      apply Finset.sum_congr rfl
      intro z _
      rw [scalarClockMarginal_withDensity_coneSource K g b z,
        Measure.compProd_smul_left]
    _ = Measure.sum fun z =>
        (scalarClockMarginal K g b).withDensity
            (fun u => ENNReal.ofReal (coneSource K g b u z)) ⊗ₘ
          raceLosingKernel K b z := by
      rw [Measure.sum_fintype]
    _ = Measure.sum fun z =>
        scalarClockMarginal K g b ⊗ₘ
          (raceLosingKernel K b z).withDensity
            (fun u (_ : losingIndex K b → ℝ) =>
              ENNReal.ofReal (coneSource K g b u z)) := by
      congr 1
      funext z
      have hweight : Measurable (Function.uncurry
          (fun u (_ : losingIndex K b → ℝ) =>
            ENNReal.ofReal (coneSource K g b u z))) :=
        ENNReal.measurable_ofReal.comp
          ((coneSource_measurable K g b z).comp measurable_fst)
      rw [Measure.compProd_withDensity hweight]
      exact (withDensity_fst_compProd
        (scalarClockMarginal K g b) (raceLosingKernel K b z)
        (fun u => ENNReal.ofReal (coneSource K g b u z))
        (ENNReal.measurable_ofReal.comp
          (coneSource_measurable K g b z))).symm
    _ = scalarClockMarginal K g b ⊗ₘ
        Kernel.sum (fun z =>
          (raceLosingKernel K b z).withDensity
            (fun u (_ : losingIndex K b → ℝ) =>
              ENNReal.ofReal (coneSource K g b u z))) := by
      rw [Measure.compProd_sum_right]
    _ = scalarClockMarginal K g b ⊗ₘ raceContextKernel K g b := by
      rfl

private lemma scalarClockMarginal_eq_volumeDensity {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D) (g b : K.κ) :
    scalarClockMarginal K g b =
      volume.withDensity (fun u =>
        exponentialPDF 1 u * raceContextClockDensity K g b u) := by
  rw [scalarClockMarginal_eq_withDensity K g b]
  change (volume.withDensity (exponentialPDF 1)).withDensity
      (raceContextClockDensity K g b) = _
  rw [← MeasureTheory.withDensity_mul volume
    (f := exponentialPDF 1) (g := raceContextClockDensity K g b)
    (measurable_exponentialPDFReal 1).ennreal_ofReal
    (raceContextClockDensity_measurable K g b)]
  congr 1

private lemma scaled_scalarClockMarginal_eq_coneDensity {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D) (g b : K.κ) :
    ENNReal.ofReal (scalarWinnerProb K g b) • scalarClockMarginal K g b =
      (volume.restrict (Set.Ioi (0 : ℝ))).withDensity
        (fun u => ENNReal.ofReal (coneContextDensity K g b u)) := by
  have hP : 0 < scalarWinnerProb K g b := scalarWinnerProb_pos K g b
  have hpdf : Measurable (exponentialPDF 1) :=
    (measurable_exponentialPDFReal 1).ennreal_ofReal
  have hcontext : Measurable (raceContextClockDensity K g b) :=
    raceContextClockDensity_measurable K g b
  have hdensity :
      (fun u => ENNReal.ofReal (scalarWinnerProb K g b) *
        (exponentialPDF 1 u * raceContextClockDensity K g b u)) =ᵐ[volume]
      Set.indicator (Set.Ioi (0 : ℝ))
        (fun u => ENNReal.ofReal (coneContextDensity K g b u)) := by
    filter_upwards [MeasureTheory.volume.ae_ne (0 : ℝ)] with u hu
    rcases lt_or_gt_of_ne hu with huNeg | huPos
    · rw [exponentialPDF_of_neg huNeg]
      have hnot : ¬0 < u := not_lt_of_ge huNeg.le
      simp [Set.indicator, hnot]
    · rw [exponentialPDF_of_nonneg huPos.le,
        raceContextClockDensity_eq K g b u]
      simp only [one_mul]
      have huMem : u ∈ Set.Ioi (0 : ℝ) := huPos
      rw [Set.indicator_of_mem huMem]
      rw [← ENNReal.ofReal_mul (Real.exp_nonneg _),
        ← ENNReal.ofReal_mul hP.le]
      congr 1
      field_simp [hP.ne']
      rw [← Real.exp_add]
      ring_nf
      simp
  rw [scalarClockMarginal_eq_volumeDensity K g b]
  calc
    ENNReal.ofReal (scalarWinnerProb K g b) •
        volume.withDensity (fun u =>
          exponentialPDF 1 u * raceContextClockDensity K g b u) =
        volume.withDensity (fun u =>
          ENNReal.ofReal (scalarWinnerProb K g b) *
            (exponentialPDF 1 u * raceContextClockDensity K g b u)) := by
      change ENNReal.ofReal (scalarWinnerProb K g b) •
          volume.withDensity
            (exponentialPDF 1 * raceContextClockDensity K g b) =
        volume.withDensity
          (ENNReal.ofReal (scalarWinnerProb K g b) •
            (exponentialPDF 1 * raceContextClockDensity K g b))
      exact (MeasureTheory.withDensity_smul
        (μ := volume) (ENNReal.ofReal (scalarWinnerProb K g b))
        (hpdf.mul hcontext)).symm
    _ = volume.withDensity
        (Set.indicator (Set.Ioi (0 : ℝ))
          (fun u => ENNReal.ofReal (coneContextDensity K g b u))) :=
      MeasureTheory.withDensity_congr_ae hdensity
    _ = (volume.restrict (Set.Ioi (0 : ℝ))).withDensity
        (fun u => ENNReal.ofReal (coneContextDensity K g b u)) := by
      rw [MeasureTheory.withDensity_indicator measurableSet_Ioi]

private lemma scalarClockMarginal_isProbability {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D) (g b : K.κ) :
    IsProbabilityMeasure (scalarClockMarginal K g b) := by
  letI : IsProbabilityMeasure (clusterSeedContextMarginal K g b) :=
    clusterSeedContextMarginal_isProbability K g b
  letI : IsMarkovKernel (raceContextKernel K g b) :=
    raceContextKernel_isMarkov K g b
  letI : SFinite (scalarClockMarginal K g b) :=
    scalarClockMarginal_sFinite K g b
  letI : IsProbabilityMeasure
      (Measure.map (clusterClockSplit K b)
        (clusterSeedContextMarginal K g b)) :=
    Measure.isProbabilityMeasure_map
      (clusterClockSplit_measurable K b).aemeasurable
  letI : IsProbabilityMeasure
      (scalarClockMarginal K g b ⊗ₘ raceContextKernel K g b) := by
    rw [← clusterSeedContext_split_factorization K g b]
    infer_instance
  constructor
  rw [← Measure.compProd_apply_univ
    (μ := scalarClockMarginal K g b) (κ := raceContextKernel K g b)]
  exact measure_univ

private lemma klDiv_map_clusterClockSplit_eq {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D) (b : K.κ)
    (μ ν : Measure (K.κ → ℝ)) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    klDiv (Measure.map (clusterClockSplit K b) μ)
        (Measure.map (clusterClockSplit K b) ν) =
      klDiv μ ν := by
  apply le_antisymm
  · exact klDiv_map_le μ ν (clusterClockSplit_measurable K b)
  · calc
      klDiv μ ν =
          klDiv
            (Measure.map (clusterClockJoin K b)
              (Measure.map (clusterClockSplit K b) μ))
            (Measure.map (clusterClockJoin K b)
              (Measure.map (clusterClockSplit K b) ν)) := by
        rw [Measure.map_map (clusterClockJoin_measurable K b)
            (clusterClockSplit_measurable K b),
          Measure.map_map (clusterClockJoin_measurable K b)
            (clusterClockSplit_measurable K b)]
        have hcomp : clusterClockJoin K b ∘ clusterClockSplit K b = id := by
          funext G
          exact clusterClockJoin_split K b G
        rw [hcomp, Measure.map_id, Measure.map_id]
      _ ≤ klDiv (Measure.map (clusterClockSplit K b) μ)
          (Measure.map (clusterClockSplit K b) ν) :=
        klDiv_map_le _ _ (clusterClockJoin_measurable K b)

private noncomputable def clusterContextInfoNats {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D) (g b : K.κ) : ℝ :=
  ∑ z, scalarSource K g b z *
    (klDiv (clusterSeedLawGivenWinner K b z)
      (clusterSeedContextMarginal K g b)).toReal

private lemma clusterSeed_context_klDiv_split {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D) (g b : K.κ) (z : α × β)
    (hz : 0 < K.Q g z * K.sigma b z) :
    (klDiv (clusterSeedLawGivenWinner K b z)
        (clusterSeedContextMarginal K g b)).toReal =
      (klDiv (K.clockLawGiven b z)
        (scalarClockMarginal K g b)).toReal +
      ∫ u, (klDiv (losingClockLaw K b z u)
          (losingClockMarginal K g b u)).toReal
        ∂K.clockLawGiven b z := by
  have hQ : 0 < K.Q g z :=
    lt_of_le_of_ne ((K.Q_isContact g).1.nonneg z)
      (Ne.symm (mul_ne_zero_iff.mp hz.ne').1)
  have hsigma : 0 < K.sigma b z :=
    lt_of_le_of_ne (raceSigma_nonneg K b z)
      (Ne.symm (mul_ne_zero_iff.mp hz.ne').2)
  have hzSupp : z ∈ support p := by
    by_contra hzSupp
    exact hQ.ne' ((K.Q_isContact g).2.1 z hzSupp)
  have hcone (u : ℝ) : 0 < coneSource K g b u z := by
    unfold coneSource
    exact div_pos (mul_pos hQ (Real.exp_pos _))
      (coneContextDensity_pos K g b u)
  letI : IsProbabilityMeasure (clusterSeedLawGivenWinner K b z) :=
    clusterSeedLawGivenWinner_isProbability K b z
  letI : IsProbabilityMeasure (clusterSeedContextMarginal K g b) :=
    clusterSeedContextMarginal_isProbability K g b
  letI : IsProbabilityMeasure (K.clockLawGiven b z) := by
    unfold Clustering.clockLawGiven
    exact isProbabilityMeasure_expMeasure (one_div_pos.mpr hsigma)
  letI : IsProbabilityMeasure (scalarClockMarginal K g b) :=
    scalarClockMarginal_isProbability K g b
  letI : IsMarkovKernel (raceLosingKernel K b z) :=
    raceLosingKernel_isMarkov K b z
  letI : IsMarkovKernel (raceContextKernel K g b) :=
    raceContextKernel_isMarkov K g b
  have hac (u : ℝ) :
      raceLosingKernel K b z u ≪ raceContextKernel K g b u := by
    rw [raceLosingKernel_apply K b z u,
      raceContextKernel_apply K g b u]
    exact (klDiv_ne_top_iff.mp
      (losingClock_klDiv_ne_top K g b u z (hcone u))).1
  have hpointFinite (u : ℝ) :
      klDiv (raceLosingKernel K b z u)
          (raceContextKernel K g b u) ≠ ⊤ := by
    rw [raceLosingKernel_apply K b z u,
      raceContextKernel_apply K g b u]
    exact losingClock_klDiv_ne_top K g b u z (hcone u)
  have hchain :
      klDiv (clusterSeedLawGivenWinner K b z)
          (clusterSeedContextMarginal K g b) =
        klDiv (K.clockLawGiven b z) (scalarClockMarginal K g b) +
          klDiv
            (K.clockLawGiven b z ⊗ₘ raceLosingKernel K b z)
            (K.clockLawGiven b z ⊗ₘ raceContextKernel K g b) := by
    calc
      klDiv (clusterSeedLawGivenWinner K b z)
          (clusterSeedContextMarginal K g b) =
          klDiv
            (Measure.map (clusterClockSplit K b)
              (clusterSeedLawGivenWinner K b z))
            (Measure.map (clusterClockSplit K b)
              (clusterSeedContextMarginal K g b)) :=
        (klDiv_map_clusterClockSplit_eq K b _ _).symm
      _ = klDiv
            (K.clockLawGiven b z ⊗ₘ raceLosingKernel K b z)
            (scalarClockMarginal K g b ⊗ₘ raceContextKernel K g b) := by
        rw [clusterSeed_split_factorization K b z hzSupp,
          clusterSeedContext_split_factorization K g b]
      _ = klDiv (K.clockLawGiven b z) (scalarClockMarginal K g b) +
          klDiv
            (K.clockLawGiven b z ⊗ₘ raceLosingKernel K b z)
            (K.clockLawGiven b z ⊗ₘ raceContextKernel K g b) :=
        klDiv_compProd_eq_add _ _ _ _
  have haddFinite :
      klDiv (K.clockLawGiven b z) (scalarClockMarginal K g b) +
          klDiv
            (K.clockLawGiven b z ⊗ₘ raceLosingKernel K b z)
            (K.clockLawGiven b z ⊗ₘ raceContextKernel K g b) ≠ ⊤ := by
    rw [← hchain]
    exact clusterSeed_klDiv_ne_top K g b z hz
  have hfinite := ENNReal.add_ne_top.mp haddFinite
  calc
    (klDiv (clusterSeedLawGivenWinner K b z)
        (clusterSeedContextMarginal K g b)).toReal =
        (klDiv (K.clockLawGiven b z) (scalarClockMarginal K g b) +
          klDiv
            (K.clockLawGiven b z ⊗ₘ raceLosingKernel K b z)
            (K.clockLawGiven b z ⊗ₘ raceContextKernel K g b)).toReal := by
      rw [hchain]
    _ = (klDiv (K.clockLawGiven b z)
          (scalarClockMarginal K g b)).toReal +
        (klDiv
          (K.clockLawGiven b z ⊗ₘ raceLosingKernel K b z)
          (K.clockLawGiven b z ⊗ₘ raceContextKernel K g b)).toReal :=
      ENNReal.toReal_add hfinite.1 hfinite.2
    _ = (klDiv (K.clockLawGiven b z)
          (scalarClockMarginal K g b)).toReal +
        ∫ u, (klDiv (losingClockLaw K b z u)
            (losingClockMarginal K g b u)).toReal
          ∂K.clockLawGiven b z := by
      rw [toReal_klDiv_compProd_same_left_eq_integral
        (K.clockLawGiven b z) (raceLosingKernel K b z)
        (raceContextKernel K g b) hac hpointFinite]
      apply congrArg (fun x : ℝ =>
        (klDiv (K.clockLawGiven b z)
          (scalarClockMarginal K g b)).toReal + x)
      apply integral_congr_ae
      filter_upwards with u
      rw [raceLosingKernel_apply K b z u,
        raceContextKernel_apply K g b u]

private lemma klDiv_kernel_measurable
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace.CountableOrCountablyGenerated X Y]
    (κ η : Kernel X Y) [IsMarkovKernel κ] [IsMarkovKernel η]
    (hac : ∀ x, κ x ≪ η x) :
    Measurable (fun x => klDiv (κ x) (η x)) := by
  have hpoint (x : X) :
      klDiv (κ x) (η x) =
        ∫⁻ y, ENNReal.ofReal
          (klFun ((κ.rnDeriv η x y).toReal)) ∂η x := by
    rw [klDiv_eq_lintegral_klFun_of_ac (hac x)]
    exact lintegral_congr_ae
      ((Kernel.rnDeriv_eq_rnDeriv_measure
        (κ := κ) (η := η) (a := x)).fun_comp
          fun r => ENNReal.ofReal (klFun r.toReal)).symm
  simp_rw [hpoint]
  exact Measurable.lintegral_kernel_prod_right (by fun_prop)

private lemma losingClock_klDiv_toReal_integrable {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D) (g b : K.κ) (z : α × β)
    (hz : 0 < K.Q g z * K.sigma b z) :
    Integrable
      (fun u => (klDiv (losingClockLaw K b z u)
        (losingClockMarginal K g b u)).toReal)
      (K.clockLawGiven b z) := by
  have hQ : 0 < K.Q g z :=
    lt_of_le_of_ne ((K.Q_isContact g).1.nonneg z)
      (Ne.symm (mul_ne_zero_iff.mp hz.ne').1)
  have hsigma : 0 < K.sigma b z :=
    lt_of_le_of_ne (raceSigma_nonneg K b z)
      (Ne.symm (mul_ne_zero_iff.mp hz.ne').2)
  have hzSupp : z ∈ support p := by
    by_contra hzSupp
    exact hQ.ne' ((K.Q_isContact g).2.1 z hzSupp)
  have hcone (u : ℝ) : 0 < coneSource K g b u z := by
    unfold coneSource
    exact div_pos (mul_pos hQ (Real.exp_pos _))
      (coneContextDensity_pos K g b u)
  letI : IsProbabilityMeasure (clusterSeedLawGivenWinner K b z) :=
    clusterSeedLawGivenWinner_isProbability K b z
  letI : IsProbabilityMeasure (clusterSeedContextMarginal K g b) :=
    clusterSeedContextMarginal_isProbability K g b
  letI : IsProbabilityMeasure (K.clockLawGiven b z) := by
    unfold Clustering.clockLawGiven
    exact isProbabilityMeasure_expMeasure (one_div_pos.mpr hsigma)
  letI : IsProbabilityMeasure (scalarClockMarginal K g b) :=
    scalarClockMarginal_isProbability K g b
  letI : IsMarkovKernel (raceLosingKernel K b z) :=
    raceLosingKernel_isMarkov K b z
  letI : IsMarkovKernel (raceContextKernel K g b) :=
    raceContextKernel_isMarkov K g b
  have hac (u : ℝ) :
      raceLosingKernel K b z u ≪ raceContextKernel K g b u := by
    rw [raceLosingKernel_apply K b z u,
      raceContextKernel_apply K g b u]
    exact (klDiv_ne_top_iff.mp
      (losingClock_klDiv_ne_top K g b u z (hcone u))).1
  have hjointFinite :
      klDiv
          (K.clockLawGiven b z ⊗ₘ raceLosingKernel K b z)
          (scalarClockMarginal K g b ⊗ₘ raceContextKernel K g b) ≠ ⊤ := by
    rw [← clusterSeed_split_factorization K b z hzSupp,
      ← clusterSeedContext_split_factorization K g b,
      klDiv_map_clusterClockSplit_eq K b]
    exact clusterSeed_klDiv_ne_top K g b z hz
  have hcondFinite :
      klDiv
          (K.clockLawGiven b z ⊗ₘ raceLosingKernel K b z)
          (K.clockLawGiven b z ⊗ₘ raceContextKernel K g b) ≠ ⊤ := by
    rw [klDiv_compProd_eq_add] at hjointFinite
    exact (ENNReal.add_ne_top.mp hjointFinite).2
  have hmeas : Measurable (fun u =>
      klDiv (raceLosingKernel K b z u) (raceContextKernel K g b u)) :=
    klDiv_kernel_measurable
      (raceLosingKernel K b z) (raceContextKernel K g b) hac
  have hlintegral :
      (∫⁻ u, klDiv (raceLosingKernel K b z u)
        (raceContextKernel K g b u) ∂K.clockLawGiven b z) ≠ ⊤ := by
    rw [← klDiv_compProd_same_left_eq_lintegral
      (K.clockLawGiven b z) (raceLosingKernel K b z)
      (raceContextKernel K g b) hac]
    exact hcondFinite
  have hint := integrable_toReal_of_lintegral_ne_top
    hmeas.aemeasurable hlintegral
  simpa only [raceLosingKernel_apply, raceContextKernel_apply] using hint

private noncomputable def losingContextKLNats {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D) (g b : K.κ)
    (z : α × β) (u : ℝ) : ℝ :=
  (klDiv (losingClockLaw K b z u)
    (losingClockMarginal K g b u)).toReal

private lemma coneContextInfo_integral_eq_source_sum {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D) (g b : K.κ) :
    (∫ u, coneContextInfoNats K g b u ∂scalarClockMarginal K g b) =
      ∑ z, scalarSource K g b z *
        ∫ u, losingContextKLNats K g b z u ∂K.clockLawGiven b z := by
  have hP : 0 < scalarWinnerProb K g b := scalarWinnerProb_pos K g b
  have hQzero_of_source_zero (z : α × β)
      (hsource : scalarSource K g b z = 0) : K.Q g z = 0 := by
    by_contra hQzero
    have hQ : 0 < K.Q g z :=
      lt_of_le_of_ne ((K.Q_isContact g).1.nonneg z) (Ne.symm hQzero)
    have hzSupp : z ∈ support p := by
      by_contra hzSupp
      exact hQ.ne' ((K.Q_isContact g).2.1 z hzSupp)
    have hsigma : 0 < K.sigma b z := K.sigma_pos b z hzSupp
    have hsourcePos : 0 < scalarSource K g b z := by
      unfold scalarSource
      exact div_pos (mul_pos hQ hsigma) hP
    exact hsourcePos.ne' hsource
  have hint (z : α × β) : Integrable
      (fun u => coneSource K g b u z * losingContextKLNats K g b z u)
      (scalarClockMarginal K g b) := by
    by_cases hsource : scalarSource K g b z = 0
    · have hQzero := hQzero_of_source_zero z hsource
      simp [coneSource, hQzero]
    · have hnum : K.Q g z * K.sigma b z ≠ 0 := by
        intro hnum
        apply hsource
        unfold scalarSource
        rw [hnum]
        simp
      have hz : 0 < K.Q g z * K.sigma b z :=
        lt_of_le_of_ne
          (mul_nonneg ((K.Q_isContact g).1.nonneg z)
            (raceSigma_nonneg K b z))
          (Ne.symm hnum)
      have hf : Integrable (losingContextKLNats K g b z)
          (K.clockLawGiven b z) := by
        unfold losingContextKLNats
        exact losingClock_klDiv_toReal_integrable K g b z hz
      have hdensity : Measurable
          (fun u => ENNReal.ofReal (coneSource K g b u z)) :=
        ENNReal.measurable_ofReal.comp (coneSource_measurable K g b z)
      have hfDensity : Integrable (losingContextKLNats K g b z)
          ((scalarClockMarginal K g b).withDensity
            (fun u => ENNReal.ofReal (coneSource K g b u z))) := by
        rw [scalarClockMarginal_withDensity_coneSource K g b z]
        exact hf.smul_measure ENNReal.ofReal_ne_top
      have hweighted :=
        (integrable_withDensity_iff_integrable_smul' hdensity
          (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)).mp
          hfDensity
      exact hweighted.congr (Filter.Eventually.of_forall fun u => by
        change (ENNReal.ofReal (coneSource K g b u z)).toReal *
            losingContextKLNats K g b z u =
          coneSource K g b u z * losingContextKLNats K g b z u
        rw [ENNReal.toReal_ofReal ((coneSource_isPMF K g b u).nonneg z)]
        )
  have hterm (z : α × β) :
      (∫ u, coneSource K g b u z * losingContextKLNats K g b z u
          ∂scalarClockMarginal K g b) =
        scalarSource K g b z *
          ∫ u, losingContextKLNats K g b z u ∂K.clockLawGiven b z := by
    have hdensity : Measurable
        (fun u => ENNReal.ofReal (coneSource K g b u z)) :=
      ENNReal.measurable_ofReal.comp (coneSource_measurable K g b z)
    calc
      (∫ u, coneSource K g b u z * losingContextKLNats K g b z u
          ∂scalarClockMarginal K g b) =
          ∫ u, losingContextKLNats K g b z u
            ∂(scalarClockMarginal K g b).withDensity
              (fun u => ENNReal.ofReal (coneSource K g b u z)) := by
        rw [integral_withDensity_eq_integral_toReal_smul hdensity
          (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
        apply integral_congr_ae
        filter_upwards with u
        rw [ENNReal.toReal_ofReal ((coneSource_isPMF K g b u).nonneg z)]
        rfl
      _ = ∫ u, losingContextKLNats K g b z u
          ∂ENNReal.ofReal (scalarSource K g b z) • K.clockLawGiven b z := by
        rw [scalarClockMarginal_withDensity_coneSource K g b z]
      _ = (ENNReal.ofReal (scalarSource K g b z)).toReal •
          ∫ u, losingContextKLNats K g b z u ∂K.clockLawGiven b z := by
        rw [integral_smul_measure]
      _ = scalarSource K g b z *
          ∫ u, losingContextKLNats K g b z u ∂K.clockLawGiven b z := by
        rw [ENNReal.toReal_ofReal ((scalarSource_isPMF K g b).nonneg z)]
        rfl
  change (∫ u, ∑ z, coneSource K g b u z *
      losingContextKLNats K g b z u ∂scalarClockMarginal K g b) = _
  rw [integral_finsetSum univ (fun z _ => hint z)]
  exact Finset.sum_congr rfl fun z _ => hterm z

private lemma clusterContextInfo_split {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D) (g b : K.κ) :
    clusterContextInfoNats K g b =
      scalarContextInfoNats K g b +
        ∫ u, coneContextInfoNats K g b u ∂scalarClockMarginal K g b := by
  rw [coneContextInfo_integral_eq_source_sum K g b]
  unfold clusterContextInfoNats scalarContextInfoNats
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro z _
  by_cases hsource : scalarSource K g b z = 0
  · simp [hsource]
  · have hnum : K.Q g z * K.sigma b z ≠ 0 := by
      intro hnum
      apply hsource
      unfold scalarSource
      rw [hnum]
      simp
    have hz : 0 < K.Q g z * K.sigma b z :=
      lt_of_le_of_ne
        (mul_nonneg ((K.Q_isContact g).1.nonneg z)
          (raceSigma_nonneg K b z))
        (Ne.symm hnum)
    rw [clusterSeed_context_klDiv_split K g b z hz]
    unfold losingContextKLNats
    ring

private lemma scalarCone_integral_density {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D) (g b : K.κ) :
    scalarWinnerProb K g b *
        ∫ u, coneContextInfoNats K g b u ∂scalarClockMarginal K g b =
      ∫ u in Set.Ioi (0 : ℝ),
        coneContextDensity K g b u * coneContextInfoNats K g b u := by
  have hP : 0 ≤ scalarWinnerProb K g b :=
    (scalarWinnerProb_pos K g b).le
  have hdensity : Measurable
      (fun u => ENNReal.ofReal (coneContextDensity K g b u)) := by
    apply ENNReal.measurable_ofReal.comp
    unfold coneContextDensity
    fun_prop
  calc
    scalarWinnerProb K g b *
        ∫ u, coneContextInfoNats K g b u ∂scalarClockMarginal K g b =
        (ENNReal.ofReal (scalarWinnerProb K g b)).toReal •
          ∫ u, coneContextInfoNats K g b u
            ∂scalarClockMarginal K g b := by
      rw [ENNReal.toReal_ofReal hP]
      rfl
    _ = ∫ u, coneContextInfoNats K g b u
        ∂ENNReal.ofReal (scalarWinnerProb K g b) •
          scalarClockMarginal K g b := by
      rw [integral_smul_measure]
    _ = ∫ u, coneContextInfoNats K g b u
        ∂(volume.restrict (Set.Ioi (0 : ℝ))).withDensity
          (fun u => ENNReal.ofReal (coneContextDensity K g b u)) := by
      rw [scaled_scalarClockMarginal_eq_coneDensity K g b]
    _ = ∫ u, (ENNReal.ofReal
          (coneContextDensity K g b u)).toReal •
            coneContextInfoNats K g b u
        ∂volume.restrict (Set.Ioi (0 : ℝ)) := by
      rw [integral_withDensity_eq_integral_toReal_smul hdensity
        (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    _ = ∫ u in Set.Ioi (0 : ℝ),
        coneContextDensity K g b u * coneContextInfoNats K g b u := by
      apply integral_congr_ae
      filter_upwards with u
      rw [ENNReal.toReal_ofReal (coneContextDensity_pos K g b u).le]
      rfl

private lemma cluster_context_decomposition_nats {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D) :
    raceClusterLeak K * Real.log 2 =
      ∑ g, K.s g * ∑ b,
        scalarWinnerProb K g b * clusterContextInfoNats K g b := by
  have hlog : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
  unfold raceClusterLeak condMIcts
  rw [div_mul_cancel₀ _ hlog, Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro g _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  unfold clusterContextInfoNats
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  unfold scalarSource
  have hP := (scalarWinnerProb_pos K g b).ne'
  field_simp

private lemma cluster_scalar_cone_nats {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D) :
    raceClusterLeak K * Real.log 2 =
      raceScalar K * Real.log 2 + integratedConeNats K := by
  calc
    raceClusterLeak K * Real.log 2 =
        ∑ g, K.s g * ∑ b,
          scalarWinnerProb K g b * clusterContextInfoNats K g b :=
      cluster_context_decomposition_nats K
    _ = (∑ g, K.s g * ∑ b,
          scalarWinnerProb K g b * scalarContextInfoNats K g b) +
        ∑ g, K.s g * ∑ b,
          scalarWinnerProb K g b *
            ∫ u, coneContextInfoNats K g b u
              ∂scalarClockMarginal K g b := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro g _
      rw [← mul_add, ← Finset.sum_add_distrib]
      apply congrArg (fun x : ℝ => K.s g * x)
      apply Finset.sum_congr rfl
      intro b _
      rw [clusterContextInfo_split K g b]
      ring
    _ = raceScalar K * Real.log 2 + integratedConeNats K := by
      rw [← scalar_context_decomposition_nats K]
      apply congrArg (fun x : ℝ => raceScalar K * Real.log 2 + x)
      unfold integratedConeNats
      apply Finset.sum_congr rfl
      intro g _
      apply congrArg (fun x : ℝ => K.s g * x)
      apply Finset.sum_congr rfl
      intro b _
      exact scalarCone_integral_density K g b

/-- The measure-theoretic chain rule for `G̃ ↔ X* ↔ (U,X*₋B)`, with the
second term represented by the exact conditional integral above. -/
private theorem cluster_clock_chain_split {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D) :
    raceClusterLeak K = raceScalar K + integratedConeNats K / Real.log 2 := by
  have hlog : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
  apply mul_right_cancel₀ hlog
  rw [add_mul, div_mul_cancel₀ _ hlog]
  exact cluster_scalar_cone_nats K

/-- The winner raw clock is a deterministic statistic of the grouped clock
vector.  Equivalently, the exact chain split and positivity of its losing
channel remainder give the data-processing inequality. -/
private theorem scalar_le_clusterLeak {p : α × β → ℝ}
    {D : SeedSetup p} (K : Clustering D) :
    raceScalar K ≤ raceClusterLeak K := by
  rw [cluster_clock_chain_split K]
  exact le_add_of_nonneg_right
    (div_nonneg (integratedConeNats_nonneg K) (Real.log_pos one_lt_two).le)

private theorem raceCone_nonneg {p : α × β → ℝ} (D : SeedSetup p)
    (K : Clustering D) : 0 ≤ raceCone K := by
  unfold raceCone
  rw [race_grouping_identity D K]
  exact sub_nonneg.mpr (scalar_le_clusterLeak K)

private theorem raceCone_eq_integrated {p : α × β → ℝ}
    (D : SeedSetup p) (K : Clustering D) :
    raceCone K * Real.log 2 = integratedConeNats K := by
  have hlog : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
  unfold raceCone
  rw [race_grouping_identity D K, cluster_clock_chain_split K]
  field_simp
  ring

private theorem race_cone_le_nats {p : α × β → ℝ}
    (D : SeedSetup p) (K : Clustering D) :
    raceCone K * Real.log 2 ≤ K.dMis := by
  calc
    raceCone K * Real.log 2 = integratedConeNats K :=
      raceCone_eq_integrated D K
    _ ≤ coneCharge K := integratedConeNats_le_charge K
    _ = K.dMis := coneCharge_eq_dMis K

/-! ### The fixed-seed cell-residual link -/

/-- The deterministic winner partition of one contact component.  Zero-mass
cells use the totalized `componentCellLaw`; their prior coefficient is zero. -/
private noncomputable def componentPartitionLatent {p : α × β → ℝ}
    (D : SeedSetup p) (ε : D.L.ι → ℝ) (b : D.L.ι) :
    Latent (D.L.comp b) where
  ι := D.L.ι
  fin := D.L.fin
  dec := D.L.dec
  prior := fun a => componentCellMass D ε a b
  comp := fun a => componentCellLaw D ε a b
  prior_isPMF := by
    constructor
    · exact fun a => componentCellMass_nonneg D ε a b
    · unfold mass componentCellMass cell
      calc
        (∑ a, ∑ z ∈ univ.filter (fun z => winner D ε z = a),
            D.L.comp b z) = ∑ z, D.L.comp b z :=
          Finset.sum_fiberwise univ (winner D ε) (D.L.comp b)
        _ = 1 := by simpa [mass] using (D.L.comp_isPMF b).total
  comp_isPMF := fun a => (cellSourceLatent D ε a).comp_isPMF b
  mixture := by
    intro z
    let a₀ := winner D ε z
    calc
      (∑ a, componentCellMass D ε a b * componentCellLaw D ε a b z) =
          componentCellMass D ε a₀ b * componentCellLaw D ε a₀ b z := by
        apply Finset.sum_eq_single a₀
        · intro a _ ha
          by_cases hm : componentCellMass D ε a b = 0
          · simp [hm]
          · have hwin : winner D ε z ≠ a := by
              exact fun h => ha h.symm
            simp [componentCellLaw, componentCellRaw, hm, hwin]
        · intro ha
          exact (ha (Finset.mem_univ a₀)).elim
      _ = D.L.comp b z := by
        by_cases hm : componentCellMass D ε a₀ b = 0
        · have hzmem : z ∈ cell D ε a₀ := by simp [cell, a₀]
          have hz0 : D.L.comp b z = 0 :=
            (Finset.sum_eq_zero_iff_of_nonneg
              (fun z _ => (D.L.comp_isPMF b).nonneg z)).1 hm z hzmem
          simp [hm, hz0]
        · simp only [componentCellLaw, componentCellRaw, hm, if_false, a₀,
            if_true]
          have hm' : componentCellMass D ε (winner D ε z) b ≠ 0 := by
            simpa only [a₀] using hm
          field_simp [hm']

private lemma componentPartition_mass_mul_law {p : α × β → ℝ}
    (D : SeedSetup p) (ε : D.L.ι → ℝ) (a b : D.L.ι) (z : α × β) :
    componentCellMass D ε a b * componentCellLaw D ε a b z =
      if winner D ε z = a then D.L.comp b z else 0 := by
  by_cases hm : componentCellMass D ε a b = 0
  · by_cases hw : winner D ε z = a
    · have hzmem : z ∈ cell D ε a := by simp [cell, hw]
      have hz0 : D.L.comp b z = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg
          (fun z _ => (D.L.comp_isPMF b).nonneg z)).1 hm z hzmem
      simp [hm, hw, hz0]
    · simp [hm, hw]
  · simp only [componentCellLaw, componentCellRaw, hm, if_false]
    by_cases hw : winner D ε z = a
    · simp only [hw, if_true]
      field_simp
    · simp [hw]

/-- Lemma 2.8(b) for the deterministic winner partition of one contact. -/
private theorem component_partition_fusion {p : α × β → ℝ}
    (D : SeedSetup p) (ε : D.L.ι → ℝ) (b : D.L.ι) :
    (∑ a, componentCellMass D ε a b *
      Gdef (support p) D.w (componentCellRaw D ε a b)) =
      3 * MI (fun q : D.L.ι × (α × β) => q.1) (fun q => q.2)
          (componentPartitionLatent D ε b).joint
        - 2 * MI (fun q : D.L.ι × (α × β) => q.1) (fun q => q.2.1)
          (componentPartitionLatent D ε b).joint
        - 2 * MI (fun q : D.L.ι × (α × β) => q.1) (fun q => q.2.2)
          (componentPartitionLatent D ε b).joint := by
  let V := componentPartitionLatent D ε b
  have hcontact := D.contact b (D.prior_pos b).ne'
  have hbase : Gdef (support p) D.w (D.L.comp b) = 0 :=
    (Gdef_eq_zero_iff D.feasible (D.L.comp_isPMF b) hcontact.2.1).2 hcontact
  have hfusion := Gdef_fusion D.feasible.1 (D.L.comp_isPMF b)
    hcontact.2.1 V
  change (∑ a, componentCellMass D ε a b *
      Gdef (support p) D.w (componentCellLaw D ε a b)) -
      Gdef (support p) D.w (D.L.comp b) = _ at hfusion
  rw [hbase, sub_zero] at hfusion
  calc
    (∑ a, componentCellMass D ε a b *
        Gdef (support p) D.w (componentCellRaw D ε a b)) =
        ∑ a, componentCellMass D ε a b *
          Gdef (support p) D.w (componentCellLaw D ε a b) := by
      apply Finset.sum_congr rfl
      intro a _
      by_cases hm : componentCellMass D ε a b = 0
      · simp [hm]
      · have hlaw : componentCellLaw D ε a b = componentCellRaw D ε a b := by
          funext z
          simp [componentCellLaw, hm]
        rw [hlaw]
    _ = _ := hfusion

/-- Conditional mutual information as the sum over its unnormalized finite
conditioning fibres. -/
private lemma race_condMI_eq_sum_MI_fibers
    {A Γ Δ K : Type*} [Fintype A] [Fintype Γ] [Fintype Δ] [Fintype K]
    [DecidableEq Γ] [DecidableEq Δ] [DecidableEq K]
    {m : A → ℝ} (hm : IsPMF m) (f : A → Γ) (g : A → Δ) (h : A → K) :
    condMI f g h m = ∑ k, MI f g (fun a => if h a = k then m a else 0) := by
  let mh : K → A → ℝ := fun k a => if h a = k then m a else 0
  have hF := Hvar_pair_eq_sum_fibers hm f h
  have hG := Hvar_pair_eq_sum_fibers hm g h
  have hFG := Hvar_pair_eq_sum_fibers hm (fun a => (f a, g a)) h
  change Hvar (fun a => (f a, h a)) m = Hvar h m +
    ∑ k, H (push f (mh k)) at hF
  change Hvar (fun a => (g a, h a)) m = Hvar h m +
    ∑ k, H (push g (mh k)) at hG
  change Hvar (fun a => ((f a, g a), h a)) m = Hvar h m +
    ∑ k, H (push (fun a => (f a, g a)) (mh k)) at hFG
  have hAssoc : Hvar (fun a => (f a, g a, h a)) m =
      Hvar (fun a => ((f a, g a), h a)) m := by
    simpa using Hvar_equiv hm (fun a => ((f a, g a), h a))
      (Equiv.prodAssoc Γ Δ K)
  unfold condMI
  rw [hF, hG, hAssoc, hFG]
  simp only [MI, Hvar, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  ring

/-- Mutual information depends only on the pushed joint law. -/
private lemma race_MI_eq_of_pair_push_eq
    {A A' Γ Δ : Type*} [Fintype A] [Fintype A'] [Fintype Γ] [Fintype Δ]
    [DecidableEq Γ] [DecidableEq Δ]
    (m : A → ℝ) (n : A' → ℝ) (f : A → Γ) (g : A → Δ)
    (f' : A' → Γ) (g' : A' → Δ)
    (hpair : push (fun a => (f a, g a)) m =
      push (fun a => (f' a, g' a)) n) :
    MI f g m = MI f' g' n := by
  have hf : push f m = push f' n := by
    calc
      push f m = push Prod.fst (push (fun a => (f a, g a)) m) := by
        symm
        simpa [Function.comp_def] using
          (push_push (fun a => (f a, g a)) Prod.fst m)
      _ = push Prod.fst (push (fun a => (f' a, g' a)) n) := by rw [hpair]
      _ = push f' n := by
        simpa [Function.comp_def] using
          (push_push (fun a => (f' a, g' a)) Prod.fst n)
  have hg : push g m = push g' n := by
    calc
      push g m = push Prod.snd (push (fun a => (f a, g a)) m) := by
        symm
        simpa [Function.comp_def] using
          (push_push (fun a => (f a, g a)) Prod.snd m)
      _ = push Prod.snd (push (fun a => (f' a, g' a)) n) := by rw [hpair]
      _ = push g' n := by
        simpa [Function.comp_def] using
          (push_push (fun a => (f' a, g' a)) Prod.snd n)
  unfold MI Hvar
  rw [hf, hg, hpair]

/-- Conditioning on the original component label turns the winner into the
deterministic partition latent above. -/
private theorem winner_condMI_eq_componentPartitions
    {p : α × β → ℝ} {Γ : Type*} [Fintype Γ] [DecidableEq Γ]
    (D : SeedSetup p) (ε : D.L.ι → ℝ) (g : α × β → Γ) :
    condMI (fun q : D.L.ι × (α × β) => winner D ε q.2)
        (fun q => g q.2) Prod.fst D.L.joint =
      ∑ b, D.L.prior b *
        MI (fun q : D.L.ι × (α × β) => q.1) (fun q => g q.2)
          (componentPartitionLatent D ε b).joint := by
  rw [race_condMI_eq_sum_MI_fibers D.L.joint_isPMF]
  apply Finset.sum_congr rfl
  intro b _
  let V := componentPartitionLatent D ε b
  let m : D.L.ι × (α × β) → ℝ := fun q =>
    if q.1 = b then D.L.joint q else 0
  let n : D.L.ι × (α × β) → ℝ := fun q =>
    D.L.prior b * V.joint q
  have hpair :
      push (fun q : D.L.ι × (α × β) => (winner D ε q.2, g q.2)) m =
        push (fun q : D.L.ι × (α × β) => (q.1, g q.2)) n := by
    funext y
    rcases y with ⟨a, c⟩
    unfold push m n
    simp only [Finset.sum_filter, Fintype.sum_prod_type, Prod.mk.injEq]
    dsimp only [V, componentPartitionLatent, Latent.joint]
    simp_rw [componentPartition_mass_mul_law D ε]
    let common : ℝ := ∑ x₁, ∑ x₂,
      if winner D ε (x₁, x₂) = a ∧ g (x₁, x₂) = c then
        D.L.prior b * D.L.comp b (x₁, x₂) else 0
    trans common
    · dsimp only [common]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x₁ _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x₂ _
      by_cases hcond : winner D ε (x₁, x₂) = a ∧ g (x₁, x₂) = c <;>
        simp [hcond]
    · symm
      dsimp only [common]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x₁ _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x₂ _
      by_cases hw : winner D ε (x₁, x₂) = a <;>
        by_cases hg : g (x₁, x₂) = c <;> simp [hw, hg]
  have hMI := race_MI_eq_of_pair_push_eq m n
    (fun q : D.L.ι × (α × β) => winner D ε q.2) (fun q => g q.2)
    (fun q : D.L.ι × (α × β) => q.1) (fun q => g q.2) hpair
  have hscale := MI_smul V.joint_isPMF.isFinMeas
    (fun q : D.L.ι × (α × β) => q.1) (fun q => g q.2)
    (D.L.prior_isPMF.nonneg b)
  change MI (fun q : D.L.ι × (α × β) => winner D ε q.2)
      (fun q => g q.2) m = _
  rw [hMI]
  change MI (fun q : D.L.ι × (α × β) => q.1) (fun q => g q.2)
      (fun q => D.L.prior b * V.joint q) = _
  exact hscale

private noncomputable def fixedWinnerIZ {p : α × β → ℝ}
    (D : SeedSetup p) (ε : D.L.ι → ℝ) : ℝ :=
  condMI (fun q : D.L.ι × (α × β) => winner D ε q.2)
    (fun q => q.2) Prod.fst D.L.joint

private noncomputable def fixedWinnerIX {p : α × β → ℝ}
    (D : SeedSetup p) (ε : D.L.ι → ℝ) : ℝ :=
  condMI (fun q : D.L.ι × (α × β) => winner D ε q.2)
    (fun q => q.2.1) Prod.fst D.L.joint

private noncomputable def fixedWinnerIY {p : α × β → ℝ}
    (D : SeedSetup p) (ε : D.L.ι → ℝ) : ℝ :=
  condMI (fun q : D.L.ι × (α × β) => winner D ε q.2)
    (fun q => q.2.2) Prod.fst D.L.joint

/-- The identity form of Theorem 5.7 at a fixed seed, rederived here because
the corresponding helper in `stoch_to_det.Seed` is intentionally private. -/
private theorem fixed_seed_rcell_identity {p : α × β → ℝ}
    (D : SeedSetup p) (ε : D.L.ι → ℝ) :
    raceCellIntegrand D ε =
      3 * fixedWinnerIZ D ε - 2 * fixedWinnerIX D ε -
        2 * fixedWinnerIY D ε := by
  have hZ := winner_condMI_eq_componentPartitions D ε
    (fun z : α × β => z)
  have hX := winner_condMI_eq_componentPartitions D ε
    (fun z : α × β => z.1)
  have hY := winner_condMI_eq_componentPartitions D ε
    (fun z : α × β => z.2)
  change fixedWinnerIZ D ε =
      ∑ b, D.L.prior b *
        MI (fun q : D.L.ι × (α × β) => q.1) (fun q => q.2)
          (componentPartitionLatent D ε b).joint at hZ
  change fixedWinnerIX D ε =
      ∑ b, D.L.prior b *
        MI (fun q : D.L.ι × (α × β) => q.1) (fun q => q.2.1)
          (componentPartitionLatent D ε b).joint at hX
  change fixedWinnerIY D ε =
      ∑ b, D.L.prior b *
        MI (fun q : D.L.ι × (α × β) => q.1) (fun q => q.2.2)
          (componentPartitionLatent D ε b).joint at hY
  unfold raceCellIntegrand
  change (∑ a, ∑ b, D.L.prior b * componentCellMass D ε a b *
      Gdef (support p) D.w (componentCellRaw D ε a b)) = _
  calc
    (∑ a, ∑ b, D.L.prior b * componentCellMass D ε a b *
        Gdef (support p) D.w (componentCellRaw D ε a b)) =
        ∑ b, D.L.prior b * ∑ a, componentCellMass D ε a b *
          Gdef (support p) D.w (componentCellRaw D ε a b) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro b _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ = ∑ b, D.L.prior b *
        (3 * MI (fun q : D.L.ι × (α × β) => q.1) (fun q => q.2)
            (componentPartitionLatent D ε b).joint
          - 2 * MI (fun q : D.L.ι × (α × β) => q.1) (fun q => q.2.1)
            (componentPartitionLatent D ε b).joint
          - 2 * MI (fun q : D.L.ι × (α × β) => q.1) (fun q => q.2.2)
            (componentPartitionLatent D ε b).joint) := by
      apply Finset.sum_congr rfl
      intro b _
      rw [component_partition_fusion D ε b]
    _ = 3 * fixedWinnerIZ D ε - 2 * fixedWinnerIX D ε -
        2 * fixedWinnerIY D ε := by
      rw [hZ, hX, hY]
      simp_rw [mul_sub]
      rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib,
        Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      apply congrArg₂ (fun x y : ℝ => x - y)
      · apply congrArg₂ (fun x y : ℝ => x - y)
        · apply Finset.sum_congr rfl
          intro b _
          ring
        · apply Finset.sum_congr rfl
          intro b _
          ring
      · apply Finset.sum_congr rfl
        intro b _
        ring

/-- Conditional `I(A;Z|L₀) ≤ H(A|L₀)` for the fixed-seed finite law. -/
private theorem fixed_seed_info_le_entropy {p : α × β → ℝ}
    (D : SeedSetup p) (ε : D.L.ι → ℝ) :
    fixedWinnerIZ D ε ≤
      condH (fun q : D.L.ι × (α × β) => winner D ε q.2)
        Prod.fst D.L.joint := by
  let f : D.L.ι × (α × β) → D.L.ι :=
    fun q => winner D ε q.2
  let g : D.L.ι × (α × β) → α × β := fun q => q.2
  let h : D.L.ι × (α × β) → D.L.ι := Prod.fst
  let dropF : D.L.ι × ((α × β) × D.L.ι) → (α × β) × D.L.ι :=
    Prod.snd
  have hmono := Hvar_comp_le D.L.joint_isPMF
    (fun q => (f q, g q, h q)) dropF
  change Hvar (fun q => (g q, h q)) D.L.joint ≤
    Hvar (fun q => (f q, g q, h q)) D.L.joint at hmono
  unfold fixedWinnerIZ condMI condH
  dsimp only [f, g, h] at hmono ⊢
  linarith

private theorem fixed_seed_rcell_le {p : α × β → ℝ}
    (D : SeedSetup p) (ε : D.L.ι → ℝ) :
    raceCellIntegrand D ε ≤
      3 * condH (fun q : D.L.ι × (α × β) => winner D ε q.2)
        Prod.fst D.L.joint := by
  have hX : 0 ≤ fixedWinnerIX D ε := by
    unfold fixedWinnerIX
    exact condMI_nonneg D.L.joint_isPMF _ _ _
  have hY : 0 ≤ fixedWinnerIY D ε := by
    unfold fixedWinnerIY
    exact condMI_nonneg D.L.joint_isPMF _ _ _
  rw [fixed_seed_rcell_identity D ε]
  nlinarith [fixed_seed_info_le_entropy D ε]

/-- Measurability/boundedness of the finite winner-code residual integrand. -/
private theorem integrable_raceCellIntegrand {p : α × β → ℝ}
    (D : SeedSetup p) :
    Integrable (raceCellIntegrand D) (seedLaw D.L.ι) := by
  let F : ((α × β) → D.L.ι) → ℝ := fun A =>
    ∑ a, ∑ b, D.L.prior b *
      (∑ z ∈ Finset.univ.filter (fun z => A z = a), D.L.comp b z) *
      Gdef (support p) D.w (fun z =>
        if A z = a then
          D.L.comp b z /
            ∑ z' ∈ Finset.univ.filter (fun z' => A z' = a), D.L.comp b z'
        else 0)
  have h := integrable_winner_code D F
  unfold raceCellIntegrand
  simpa only [F, cell] using h

/-- Measurability/boundedness of the finite conditional-entropy integrand. -/
private theorem integrable_raceWinnerEntropy {p : α × β → ℝ}
    (D : SeedSetup p) :
    Integrable
      (fun ε => condH
        (fun q : D.L.ι × (α × β) => winner D ε q.2)
        Prod.fst D.L.joint)
      (seedLaw D.L.ι) := by
  let F : ((α × β) → D.L.ι) → ℝ := fun A =>
    condH (fun q : D.L.ι × (α × β) => A q.2) Prod.fst D.L.joint
  simpa only [F] using integrable_winner_code D F

private theorem race_rcell_le {p : α × β → ℝ} (D : SeedSetup p) :
    Rcell D ≤ 3 * raceWinnerEntropy D := by
  let hfun := fun ε => condH
    (fun q : D.L.ι × (α × β) => winner D ε q.2)
    Prod.fst D.L.joint
  have hR := integrable_raceCellIntegrand D
  have hH : Integrable (fun ε => 3 * hfun ε) (seedLaw D.L.ι) :=
    (integrable_raceWinnerEntropy D).const_mul 3
  calc
    Rcell D = ∫ ε, raceCellIntegrand D ε ∂(seedLaw D.L.ι) := by
      rfl
    _ ≤ ∫ ε, 3 * hfun ε ∂(seedLaw D.L.ι) :=
      integral_mono hR hH (fixed_seed_rcell_le D)
    _ = 3 * raceWinnerEntropy D := by
      rw [integral_const_mul]
      rfl

/-! ### Direct bridge from the all-label shared-race bound

The analytic theorem is stated for one finite source law and one posterior
vector at each source atom.  The duplicate quotient supplies exactly such a
problem in every `C₀ = g` context.  The lemmas below transport its shared
cluster race back to the original label race, without passing through the
scalar/cone KL decomposition.
-/

private lemma sharedRace_sharedWinner_eq_groupedClusterLexWinner
    {p : α × β → ℝ} {D : SeedSetup p} (K : Clustering D)
    (G : K.κ → ℝ) (z : α × β) :
    SharedRace.sharedWinner (fun z c => K.sigma c z) G z =
      groupedClusterLexWinner K G z := by
  rfl

private lemma groupedClusterWinner_ae_eq_lex_after_grouping
    {p : α × β → ℝ} (D : SeedSetup p) (K : Clustering D) :
    (fun ε => groupedClusterWinner K (groupedG K ε)) =ᵐ[seedLaw D.L.ι]
      fun ε => groupedClusterLexWinner K (groupedG K ε) := by
  have hG : Measurable (groupedG K) :=
    measurable_fst.comp (groupedPair_measurable K)
  have hseed : ∀ᵐ G ∂(seedLaw K.κ),
      ∀ z, groupedClusterWinner K G z = groupedClusterLexWinner K G z := by
    apply ae_forall_fintype
    intro z
    change (fun G => weightedWinner (fun c : K.κ => K.sigma c z) G) =ᵐ[
      seedLaw K.κ] fun G => weightedLexWinner (fun c : K.κ => K.sigma c z) G
    exact weightedWinner_ae_eq_lex (fun c : K.κ => K.sigma c z)
  have hmapped : ∀ᵐ G ∂(Measure.map (groupedG K) (seedLaw D.L.ι)),
      ∀ z, groupedClusterWinner K G z = groupedClusterLexWinner K G z := by
    rw [grouped_gumbel_law K]
    exact hseed
  have hpull := ae_of_ae_map hG.aemeasurable hmapped
  filter_upwards [hpull] with ε hε
  funext z
  exact hε z

private lemma fixed_seed_label_cluster_entropy_eq
    {p : α × β → ℝ} (D : SeedSetup p) (K : Clustering D)
    (ε : D.L.ι → ℝ)
    (hlabel : lexWinner D ε = groupedLabelWinner K ε)
    (hcluster : groupedClusterWinner K (groupedG K ε) =
      groupedClusterLexWinner K (groupedG K ε))
    (l₀ : D.L.ι) :
    H (balanceWinnerProb D (lexWinner D ε) l₀) =
      H (push
        (SharedRace.sharedWinner (fun z c => K.sigma c z) (groupedG K ε))
        (K.Q (K.cl l₀))) := by
  let f : (α × β) → K.κ :=
    SharedRace.sharedWinner (fun z c => K.sigma c z) (groupedG K ε)
  let u : K.κ → D.L.ι := fun c => (groupedWithinWinner K ε c).1
  have hleft : Function.LeftInverse K.cl u := by
    intro c
    exact (groupedWithinWinner K ε c).2
  have hpoint (z : α × β) (hz : z ∈ support p) :
      lexWinner D ε z = u (f z) := by
    rw [congrFun hlabel z]
    simp only [groupedLabelWinner, hz, if_true, u, f]
    rw [congrFun hcluster z]
    rw [sharedRace_sharedWinner_eq_groupedClusterLexWinner K]
  have hpush :
      push (lexWinner D ε) (D.L.comp l₀) =
        push (u ∘ f) (D.L.comp l₀) := by
    funext a
    unfold push
    simp_rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro z _
    by_cases hz : z ∈ support p
    · rw [hpoint z hz]
      rfl
    · have hpz : p z = 0 := by simpa [support] using hz
      have hzero : D.L.comp l₀ z = 0 :=
        (component_eq_zero_iff D l₀ z).2 hpz
      simp [hzero]
  calc
    H (balanceWinnerProb D (lexWinner D ε) l₀) =
        Hvar (lexWinner D ε) (D.L.comp l₀) := by
      have hbalance : balanceWinnerProb D (lexWinner D ε) l₀ =
          push (lexWinner D ε) (D.L.comp l₀) := by
        funext a
        exact balanceWinnerProb_eq_push D (lexWinner D ε) l₀ a
      rw [hbalance]
      rfl
    _ = Hvar (u ∘ f) (D.L.comp l₀) := by
      unfold Hvar
      rw [hpush]
    _ = Hvar f (D.L.comp l₀) :=
      Hvar_eq_of_leftInverse (D.L.comp_isPMF l₀) f u K.cl hleft
    _ = Hvar f (K.Q (K.cl l₀)) := by
      rw [component_eq_clusterQ K l₀]
    _ = H (push
        (SharedRace.sharedWinner (fun z c => K.sigma c z) (groupedG K ε))
        (K.Q (K.cl l₀))) := by
      rfl

private lemma label_context_entropy_eq_sharedRaceEntropy
    {p : α × β → ℝ} (D : SeedSetup p) (K : Clustering D)
    (l₀ : D.L.ι) :
    (∫ ε, H (balanceWinnerProb D (lexWinner D ε) l₀)
        ∂(seedLaw D.L.ι)) =
      SharedRace.sharedRaceEntropy (K.Q (K.cl l₀))
        (fun z c => K.sigma c z) := by
  letI : MeasurableSpace K.κ := ⊤
  have hlabel :
      (fun ε => lexWinner D ε) =ᵐ[seedLaw D.L.ι]
        fun ε => groupedLabelWinner K ε :=
    (winner_ae_eq_lexWinner D).symm.trans (grouped_winner_agrees_ae D K)
  have hcluster := groupedClusterWinner_ae_eq_lex_after_grouping D K
  let F : (K.κ → ℝ) → ℝ := fun G =>
    H (push (SharedRace.sharedWinner (fun z c => K.sigma c z) G)
      (K.Q (K.cl l₀)))
  have hshared : Measurable
      (fun G : K.κ → ℝ =>
        SharedRace.sharedWinner (fun z c => K.sigma c z) G) := by
    apply measurable_pi_lambda
    intro z
    unfold SharedRace.sharedWinner SharedRace.weightedLexWinner
    apply measurable_lexMax
    intro c
    exact measurable_const.add (measurable_pi_apply c)
  have hF : Measurable F := by
    exact (measurable_of_finite
      (fun A : (α × β) → K.κ => H (push A (K.Q (K.cl l₀))))).comp
        hshared
  have hG : Measurable (groupedG K) :=
    measurable_fst.comp (groupedPair_measurable K)
  calc
    (∫ ε, H (balanceWinnerProb D (lexWinner D ε) l₀)
        ∂(seedLaw D.L.ι)) =
        ∫ ε, F (groupedG K ε) ∂(seedLaw D.L.ι) := by
      apply integral_congr_ae
      filter_upwards [hlabel, hcluster] with ε hlabelε hclusterε
      exact fixed_seed_label_cluster_entropy_eq D K ε hlabelε hclusterε l₀
    _ = ∫ G, F G ∂(Measure.map (groupedG K) (seedLaw D.L.ι)) := by
      exact (integral_map hG.aemeasurable hF.aestronglyMeasurable).symm
    _ = ∫ G, F G ∂(seedLaw K.κ) := by
      rw [grouped_gumbel_law K]
    _ = SharedRace.sharedRaceEntropy (K.Q (K.cl l₀))
        (fun z c => K.sigma c z) := by
      rfl

private theorem raceWinnerEntropy_eq_sharedRaceEntropy_sum
    {p : α × β → ℝ} (D : SeedSetup p) (K : Clustering D) :
    raceWinnerEntropy D =
      ∑ g, K.s g * SharedRace.sharedRaceEntropy (K.Q g)
        (fun z c => K.sigma c z) := by
  rw [balance_raceWinnerEntropy_eq_entropy_sum D]
  simp_rw [label_context_entropy_eq_sharedRaceEntropy D K]
  let F : K.κ → ℝ := fun g =>
    SharedRace.sharedRaceEntropy (K.Q g) (fun z c => K.sigma c z)
  change (∑ l₀, D.L.prior l₀ * F (K.cl l₀)) = ∑ g, K.s g * F g
  calc
    (∑ l₀, D.L.prior l₀ * F (K.cl l₀)) =
        ∑ g, ∑ l₀ ∈ univ.filter (fun l₀ => K.cl l₀ = g),
          D.L.prior l₀ * F (K.cl l₀) := by
      symm
      simpa using Finset.sum_fiberwise (univ : Finset D.L.ι) K.cl
        (fun l₀ => D.L.prior l₀ * F (K.cl l₀))
    _ = ∑ g, K.s g * F g := by
      apply Finset.sum_congr rfl
      intro g _
      unfold Clustering.s
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro l₀ hl₀
      rw [(Finset.mem_filter.mp hl₀).2]

private lemma clusterPosterior_isPMF_of_Q_support
    {p : α × β → ℝ} {D : SeedSetup p} (K : Clustering D)
    (g : K.κ) (z : α × β) (hz : K.Q g z ≠ 0) :
    IsPMF (fun c => K.sigma c z) := by
  have hzsupport : z ∈ support p := by
    by_contra hzs
    exact hz ((K.Q_isContact g).2.1 z hzs)
  constructor
  · exact fun c => raceSigma_nonneg K c z
  · simpa [mass] using raceSigma_sum_eq_one K z hzsupport

private lemma clusterPosterior_pos_of_Q_support
    {p : α × β → ℝ} {D : SeedSetup p} (K : Clustering D)
    (g : K.κ) (z : α × β) (hz : K.Q g z ≠ 0) (c : K.κ) :
    0 < K.sigma c z := by
  apply K.sigma_pos c z
  by_contra hzs
  exact hz ((K.Q_isContact g).2.1 z hzs)

private lemma push_sharedRace_posteriorJoint_swap
    {p : α × β → ℝ} {D : SeedSetup p} (K : Clustering D)
    (g : K.κ) :
    push (fun zi : (α × β) × K.κ => (zi.2, zi.1))
        (SharedRace.posteriorJoint (K.Q g) (fun z c => K.sigma c z)) =
      scalarPosteriorJoint K g := by
  funext bz
  rcases bz with ⟨b, z⟩
  unfold push SharedRace.posteriorJoint scalarPosteriorJoint
  simp_rw [Finset.sum_filter]
  rw [Fintype.sum_prod_type]
  simp only [Prod.mk.injEq]
  calc
    (∑ x, ∑ c, if c = b ∧ x = z then K.Q g x * K.sigma c x else 0) =
        ∑ c, if c = b ∧ z = z then K.Q g z * K.sigma c z else 0 := by
      apply Fintype.sum_eq_single z
      intro x hx
      simp [hx]
    _ = K.Q g z * K.sigma b z := by
      rw [Finset.sum_eq_single b]
      · simp
      · intro c _ hc
        simp [hc]
      · simp

private lemma sharedRace_posterior_MI_eq_scalarPosterior_MI
    {p : α × β → ℝ} {D : SeedSetup p} (K : Clustering D)
    (g : K.κ) :
    MI Prod.fst Prod.snd
        (SharedRace.posteriorJoint (K.Q g) (fun z c => K.sigma c z)) =
      MI Prod.fst Prod.snd (scalarPosteriorJoint K g) := by
  let m : ((α × β) × K.κ) → ℝ :=
    SharedRace.posteriorJoint (K.Q g) (fun z c => K.sigma c z)
  have hm : IsPMF m := SharedRace.posteriorJoint_isPMF_of_support
    (K.Q_isContact g).1 (clusterPosterior_isPMF_of_Q_support K g)
  calc
    MI Prod.fst Prod.snd m = MI Prod.snd Prod.fst m :=
      MI_comm hm Prod.fst Prod.snd
    _ = MI Prod.fst Prod.snd
        (push (fun zi : (α × β) × K.κ => (zi.2, zi.1)) m) :=
      race_MI_eq_joint_push m Prod.snd Prod.fst
    _ = MI Prod.fst Prod.snd (scalarPosteriorJoint K g) := by
      rw [show push (fun zi : (α × β) × K.κ => (zi.2, zi.1)) m =
          scalarPosteriorJoint K g by
        exact push_sharedRace_posteriorJoint_swap K g]

private theorem sharedRaceEntropy_context_le
    {p : α × β → ℝ} {D : SeedSetup p} (K : Clustering D)
    (h : SharedRace.HasSharedRaceBound (α × β) K.κ) (g : K.κ) :
    SharedRace.sharedRaceEntropy (K.Q g) (fun z c => K.sigma c z) ≤
      2 * MI Prod.fst Prod.snd (scalarPosteriorJoint K g) +
        ∑ z, K.Q g z * (1 - ∑ c, K.sigma c z ^ 2) := by
  have hg := h (K.Q g) (fun z c => K.sigma c z)
    (K.Q_isContact g).1
    (clusterPosterior_isPMF_of_Q_support K g)
    (clusterPosterior_pos_of_Q_support K g)
  rw [sharedRace_posterior_MI_eq_scalarPosterior_MI K g] at hg
  simpa only [SharedRace.categoricalMismatch] using hg

private theorem raceWinnerEntropy_le_of_sharedRaceBound
    {p : α × β → ℝ} (D : SeedSetup p) (K : Clustering D)
    (h : SharedRace.HasSharedRaceBound (α × β) K.κ) :
    raceWinnerEntropy D ≤ 2 * K.Sinfo + K.dMis := by
  calc
    raceWinnerEntropy D =
        ∑ g, K.s g * SharedRace.sharedRaceEntropy (K.Q g)
          (fun z c => K.sigma c z) :=
      raceWinnerEntropy_eq_sharedRaceEntropy_sum D K
    _ ≤ ∑ g, K.s g *
        (2 * MI Prod.fst Prod.snd (scalarPosteriorJoint K g) +
          ∑ z, K.Q g z * (1 - ∑ c, K.sigma c z ^ 2)) := by
      apply Finset.sum_le_sum
      intro g _
      exact mul_le_mul_of_nonneg_left (sharedRaceEntropy_context_le K h g)
        (clusterMass_nonneg K g)
    _ = 2 * K.Sinfo + K.dMis := by
      rw [Sinfo_eq_scalarPosterior_MI K, ← coneCharge_eq_dMis K]
      unfold coneCharge
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro g _
      ring

private noncomputable def concreteRaceQuantities {p : α × β → ℝ}
    (D : SeedSetup p) (K : Clustering D) : RaceQuantities D K :=
  {
    seedLeak := raceSeedLeak D
    scalar := raceScalar K
    cone := raceCone K
    winnerEntropy := raceWinnerEntropy D
    chain_split := race_chain_split K
    winner_entropy_identity := race_winner_entropy_identity D K
    seedLeak_nonneg := raceSeedLeak_nonneg D
    scalar_nonneg := raceScalar_nonneg K
    cone_nonneg := raceCone_nonneg D K
    scalar_le := race_scalar_le K
    cone_le_nats := race_cone_le_nats D K
    rcell_le := race_rcell_le D
  }

/-- The concrete seed-level construction supplies every field of
`RaceQuantities`, concentrating its measure-theoretic implementation here. -/
theorem exists_raceQuantities {p : α × β → ℝ} (D : SeedSetup p)
    (K : Clustering D) : Nonempty (RaceQuantities D K) :=
  ⟨concreteRaceQuantities D K⟩

/-- The concrete race quantities satisfy the joint seed bound as soon as the
universal all-label shared-race theorem is available.  This is the direct
bridge used by the `C < 96` ledger. -/
theorem exists_raceQuantities_joint {p : α × β → ℝ} (D : SeedSetup p)
    (K : Clustering D)
    (h : SharedRace.HasSharedRaceBound (α × β) K.κ) :
    ∃ R : RaceQuantities D K, R.seedLeak ≤ K.Sinfo + K.dMis := by
  refine ⟨concreteRaceQuantities D K, ?_⟩
  change raceSeedLeak D ≤ K.Sinfo + K.dMis
  have hwinner := raceWinnerEntropy_le_of_sharedRaceBound D K h
  rw [race_winner_entropy_identity D K] at hwinner
  linarith

/-- The same race construction equipped with the sharpened scalar estimate. -/
theorem exists_raceQuantities1771 {p : α × β → ℝ} (D : SeedSetup p)
    (K : Clustering D) : Nonempty (RaceQuantities1771 D K) := by
  exact ⟨{
    toRaceQuantities := {
      seedLeak := raceSeedLeak D
      scalar := raceScalar K
      cone := raceCone K
      winnerEntropy := raceWinnerEntropy D
      chain_split := race_chain_split K
      winner_entropy_identity := race_winner_entropy_identity D K
      seedLeak_nonneg := raceSeedLeak_nonneg D
      scalar_nonneg := raceScalar_nonneg K
      cone_nonneg := raceCone_nonneg D K
      scalar_le := race_scalar_le K
      cone_le_nats := race_cone_le_nats D K
      rcell_le := race_rcell_le D
    }
    scalar_le_1771 := race_scalar_le_1771 K
  }⟩

end stoch_to_det
