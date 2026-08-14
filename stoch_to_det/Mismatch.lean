import stoch_to_det.Floor
import stoch_to_det.Quotient

/-!
# §9. The mismatch charge


One theorem: the mismatch probability `d = P(C₁ ≠ C₀)` is charged to `M` and
`S`,
`d ≤ M/c_* + (2 ln 2 / δ_*²) S`.

## Scope

Despite sitting after the race machinery, Theorem 9.1 involves no seed and no
measure theory. Its inputs are:

* the exact conditional-KL expansion (9.1) of `S = I(C₁;Z ∣ C₀)` over the
  disjoint events `{C₀=c, C₁=d}` — a `Finset.sum` identity;
* `stoch_to_det.Floor.nearcollision_floor` (Theorem 6.2) for the near pairs;
* `stoch_to_det.Toolkit.bhattacharyya_le` (T3) for the far pairs.

So §9 is independent of §§7-8-10-11; together with §6 it forms a finite block
that produces both `c_*` and `δ_*`.

The near/far dichotomy is total only because every `Q_c` has full support on
the connected `𝒮` (Lemma 2.6). That is where the connectedness reduction of §3
enters the constant, and why the reduction to connected supports comes first
.
-/

namespace stoch_to_det

open Finset

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
variable {p : α × β → ℝ} {D : SeedSetup p} (K : Clustering D)

/-- The replica-pair mass `J_{cd} := P(C₀=c, C₁=d) = ∑_z p σ_c σ_d`, symmetric
in `c, d`. -/
noncomputable def pairMass (c d : K.κ) : ℝ := ∑ z, p z * K.sigma c z * K.sigma d z

/-- The overlap law `r_{cd} := p σ_c σ_d / J_{cd}`, symmetric in `c, d`. -/
noncomputable def overlapLaw (c d : K.κ) (z : α × β) : ℝ :=
  p z * K.sigma c z * K.sigma d z / pairMass K c d

private lemma Q_isPMF (c : K.κ) : IsPMF (K.Q c) :=
  (K.Q_isContact c).1

private lemma Q_supported (c : K.κ) : Supported (support p) (K.Q c) :=
  (K.Q_isContact c).2.1

private lemma comp_eq_Q (c : K.κ) (ℓ : D.L.ι) (hℓ : K.cl ℓ = c) :
    D.L.comp ℓ = K.Q c := by
  rw [Clustering.Q]
  apply (K.spec ℓ (Classical.choose (K.surj c))).mp
  exact hℓ.trans (Classical.choose_spec (K.surj c)).symm

private lemma s_pos (c : K.κ) : 0 < K.s c := by
  obtain ⟨ℓ, hℓ⟩ := K.surj c
  unfold Clustering.s
  apply sum_pos'
  · intro i _
    exact D.L.prior_isPMF.nonneg i
  · exact ⟨ℓ, by simp [hℓ], D.prior_pos ℓ⟩

private lemma sigma_nonneg (c : K.κ) (z : α × β) : 0 ≤ K.sigma c z := by
  unfold Clustering.sigma
  apply sum_nonneg
  intro ℓ _
  unfold SeedSetup.post
  exact div_nonneg
    (mul_nonneg (D.L.prior_isPMF.nonneg ℓ) ((D.L.comp_isPMF ℓ).nonneg z))
    (D.isPMF.nonneg z)

private lemma p_mul_sigma (c : K.κ) (z : α × β) :
    p z * K.sigma c z = K.s c * K.Q c z := by
  by_cases hpz : p z = 0
  · have hz : z ∉ support p := by simpa [support, hpz]
    have hQz := Q_supported K c z hz
    simp [hpz, hQz]
  · unfold Clustering.sigma SeedSetup.post
    rw [mul_sum]
    calc
      ∑ ℓ ∈ univ.filter (fun ℓ => K.cl ℓ = c),
          p z * (D.L.prior ℓ * D.L.comp ℓ z / p z) =
          ∑ ℓ ∈ univ.filter (fun ℓ => K.cl ℓ = c),
            D.L.prior ℓ * D.L.comp ℓ z := by
              apply sum_congr rfl
              intro ℓ _
              field_simp
      _ = ∑ ℓ ∈ univ.filter (fun ℓ => K.cl ℓ = c),
            D.L.prior ℓ * K.Q c z := by
              apply sum_congr rfl
              intro ℓ hℓ
              rw [comp_eq_Q K c ℓ (mem_filter.mp hℓ).2]
      _ = K.s c * K.Q c z := by
              rw [Clustering.s, sum_mul]

private lemma sum_sigma_eq_one (z : α × β) (hz : p z ≠ 0) :
    ∑ c, K.sigma c z = 1 := by
  calc
    ∑ c, K.sigma c z = ∑ ℓ, D.post ℓ z := by
      exact sum_fiberwise univ K.cl (fun ℓ => D.post ℓ z)
    _ = (∑ ℓ, D.L.prior ℓ * D.L.comp ℓ z) / p z := by
      simp only [SeedSetup.post, sum_div]
    _ = p z / p z := by rw [D.L.mixture]
    _ = 1 := div_self hz

private lemma pairMass_pos (c d : K.κ) : 0 < pairMass K c d := by
  have hex : ∃ z, K.Q c z ≠ 0 := by
    by_contra h
    push Not at h
    have htotal := (Q_isPMF K c).total
    simp [mass, h] at htotal
  obtain ⟨z, hQz⟩ := hex
  have hz : z ∈ support p := by
    by_contra hz
    exact hQz (Q_supported K c z hz)
  have hpz_ne : p z ≠ 0 := by simpa [support] using hz
  have hpz : 0 < p z := lt_of_le_of_ne (D.isPMF.nonneg z) (Ne.symm hpz_ne)
  unfold pairMass
  apply sum_pos'
  · intro z _
    exact mul_nonneg (mul_nonneg (D.isPMF.nonneg z) (sigma_nonneg K c z))
      (sigma_nonneg K d z)
  · exact ⟨z, mem_univ z,
      mul_pos (mul_pos hpz (K.sigma_pos c z hz)) (K.sigma_pos d z hz)⟩

private lemma pairMass_nonneg (c d : K.κ) : 0 ≤ pairMass K c d :=
  (pairMass_pos K c d).le

private lemma sum_pairMass_right (c : K.κ) : ∑ d, pairMass K c d = K.s c := by
  unfold pairMass
  rw [sum_comm]
  simp_rw [← mul_sum]
  calc
    ∑ z, p z * K.sigma c z * ∑ d, K.sigma d z =
        ∑ z, p z * K.sigma c z := by
          apply sum_congr rfl
          intro z _
          by_cases hz : p z = 0
          · simp [hz]
          · rw [sum_sigma_eq_one K z hz]
            ring
    _ = ∑ z, K.s c * K.Q c z := by
          apply sum_congr rfl
          intro z _
          exact p_mul_sigma K c z
    _ = K.s c := by
          rw [← mul_sum]
          have htotal : ∑ z, K.Q c z = 1 := by
            simpa [mass] using (Q_isPMF K c).total
          rw [htotal, mul_one]

private lemma overlapLaw_isPMF (c d : K.κ) : IsPMF (overlapLaw K c d) := by
  constructor
  · intro z
    exact div_nonneg
      (mul_nonneg (mul_nonneg (D.isPMF.nonneg z) (sigma_nonneg K c z))
        (sigma_nonneg K d z))
      (pairMass_nonneg K c d)
  · unfold mass overlapLaw pairMass
    rw [← sum_div]
    exact div_self (pairMass_pos K c d).ne'

private lemma overlapLaw_absCont_Q (c d : K.κ) :
    AbsCont (overlapLaw K c d) (K.Q c) := by
  intro z hQz
  have hzero := p_mul_sigma K c z
  rw [hQz, mul_zero] at hzero
  unfold overlapLaw
  calc
    p z * K.sigma c z * K.sigma d z / pairMass K c d =
        (p z * K.sigma c z) * K.sigma d z / pairMass K c d := by ring
    _ = 0 := by rw [hzero]; simp

private noncomputable def clusterTripleLaw : K.κ × ((α × β) × K.κ) → ℝ :=
  fun v => p v.2.1 * K.sigma v.2.2 v.2.1 * K.sigma v.1 v.2.1

private lemma ite_and_zero (a b : Prop) [Decidable a] [Decidable b] (x : ℝ) :
    (if a ∧ b then x else 0) = if a then (if b then x else 0) else 0 := by
  by_cases ha : a <;> by_cases hb : b <;> simp [ha, hb]

private lemma sum_pair_ite (x : α) (y : β) (f : α → β → ℝ) :
    (∑ x', ∑ y', if x' = x then (if y' = y then f x' y' else 0) else 0) = f x y := by
  rw [sum_eq_single x]
  · simp
  · intro x' _ hx'
    simp [hx']
  · simp

private lemma sum_post_eq_one (z : α × β) (hz : p z ≠ 0) :
    ∑ ℓ, D.post ℓ z = 1 := by
  calc
    ∑ ℓ, D.post ℓ z = (∑ ℓ, D.L.prior ℓ * D.L.comp ℓ z) / p z := by
      simp only [SeedSetup.post, sum_div]
    _ = p z / p z := by rw [D.L.mixture]
    _ = 1 := div_self hz

private lemma sum_replica_third (i j : D.L.ι) (z : α × β) (hz : p z ≠ 0) :
    (∑ k, p z * D.post i z * D.post j z * D.post k z) =
      p z * D.post i z * D.post j z := by
  calc
    ∑ k, p z * D.post i z * D.post j z * D.post k z =
        ∑ k, (p z * D.post i z * D.post j z) * D.post k z := by
          rfl
    _ = (p z * D.post i z * D.post j z) * ∑ k, D.post k z := by
          rw [mul_sum]
    _ = p z * D.post i z * D.post j z := by
          rw [sum_post_eq_one (D := D) z hz, mul_one]

private lemma sum_cluster_replica (c d : K.κ) (z : α × β) :
    (∑ i ∈ univ.filter (fun i => K.cl i = c),
      ∑ j ∈ univ.filter (fun j => K.cl j = d),
        p z * D.post i z * D.post j z) =
      p z * K.sigma c z * K.sigma d z := by
  unfold Clustering.sigma
  calc
    ∑ i ∈ univ.filter (fun i => K.cl i = c),
        ∑ j ∈ univ.filter (fun j => K.cl j = d), p z * D.post i z * D.post j z =
        ∑ i ∈ univ.filter (fun i => K.cl i = c),
          (p z * D.post i z) *
            ∑ j ∈ univ.filter (fun j => K.cl j = d), D.post j z := by
              apply sum_congr rfl
              intro i _
              rw [mul_sum]
    _ = (∑ i ∈ univ.filter (fun i => K.cl i = c), p z * D.post i z) *
          ∑ j ∈ univ.filter (fun j => K.cl j = d), D.post j z := by
            rw [sum_mul]
    _ = (p z * ∑ i ∈ univ.filter (fun i => K.cl i = c), D.post i z) *
          ∑ j ∈ univ.filter (fun j => K.cl j = d), D.post j z := by
            have hfactor :
                (∑ i ∈ univ.filter (fun i => K.cl i = c), p z * D.post i z) =
                  p z * ∑ i ∈ univ.filter (fun i => K.cl i = c), D.post i z := by
              rw [mul_sum]
            rw [hfactor]
    _ = p z * (∑ i ∈ univ.filter (fun i => K.cl i = c), D.post i z) *
          ∑ j ∈ univ.filter (fun j => K.cl j = d), D.post j z := by ring

private lemma sum_cluster_replica_ite (c d : K.κ) (z : α × β) :
    (∑ i, if K.cl i = c then
      ∑ j, if K.cl j = d then p z * D.post i z * D.post j z else 0 else 0) =
      p z * K.sigma c z * K.sigma d z := by
  simpa only [sum_filter] using sum_cluster_replica K c d z

private lemma push_clusterTriple :
    push (fun u => (K.cl u.2.1, u.2.2.2, K.cl u.1)) (replicaLaw D) =
      clusterTripleLaw K := by
  funext v
  rcases v with ⟨d, ⟨x, y⟩, c⟩
  unfold push replicaLaw clusterTripleLaw
  simp only [sum_filter, Fintype.sum_prod_type, mem_univ, if_true, Prod.mk.injEq]
  by_cases hz : p (x, y) = 0
  · simp_rw [and_assoc, and_left_comm, and_comm, ite_and_zero]
    simp [hz]
  · simp_rw [and_assoc, and_left_comm, and_comm]
    simp_rw [ite_and_zero]
    simp_rw [sum_pair_ite x y]
    simp_rw [Finset.sum_ite_irrel]
    simp_rw [sum_replica_third (D := D) _ _ (x, y) hz]
    simp only [sum_const_zero]
    exact sum_cluster_replica_ite K c d (x, y)

private lemma Sinfo_eq_clusterTriple_condMI :
    K.Sinfo = condMI (fun v => v.1) (fun v => v.2.1) (fun v => v.2.2)
      (clusterTripleLaw K) := by
  rw [← push_clusterTriple K]
  unfold Clustering.Sinfo condMI Hvar
  simp [push_push, Function.comp_def]

private lemma push_clusterTriple_pair :
    push (fun v => (v.1, v.2.2)) (clusterTripleLaw K) =
      fun v => pairMass K v.2 v.1 := by
  funext v
  rcases v with ⟨d, c⟩
  unfold push clusterTripleLaw pairMass
  simp only [sum_filter, Fintype.sum_prod_type, Prod.mk.injEq]
  simp_rw [ite_and_zero]
  simp_rw [Finset.sum_ite_irrel]
  simp [Finset.sum_ite_eq, Finset.sum_ite_eq', mem_univ]

private lemma push_clusterTriple_zc :
    push (fun v => (v.2.1, v.2.2)) (clusterTripleLaw K) =
      fun v => p v.1 * K.sigma v.2 v.1 := by
  funext v
  rcases v with ⟨⟨x, y⟩, c⟩
  unfold push clusterTripleLaw
  simp only [sum_filter, Fintype.sum_prod_type, Prod.mk.injEq]
  simp_rw [ite_and_zero]
  simp_rw [Finset.sum_ite_irrel]
  simp [Finset.sum_ite_eq, Finset.sum_ite_eq', mem_univ]
  by_cases hz : p (x, y) = 0
  · simp [hz]
  · rw [← mul_sum, sum_sigma_eq_one K (x, y) hz, mul_one]

private lemma push_clusterTriple_all :
    push (fun v => (v.1, v.2.1, v.2.2)) (clusterTripleLaw K) =
      clusterTripleLaw K := by
  have hid : (fun v : K.κ × ((α × β) × K.κ) => (v.1, v.2.1, v.2.2)) = id := by
    funext v
    rcases v with ⟨d, z, c⟩
    rfl
  rw [hid]
  funext v
  unfold push
  apply sum_eq_single v
  · intro w hw hne
    exact (hne (mem_filter.mp hw).2).elim
  · intro hv
    exact (hv (by simp)).elim

private lemma push_clusterTriple_c :
    push (fun v => v.2.2) (clusterTripleLaw K) = K.s := by
  calc
    push (fun v => v.2.2) (clusterTripleLaw K) =
        push Prod.snd (push (fun v => (v.1, v.2.2)) (clusterTripleLaw K)) := by
          rw [push_push]
          rfl
    _ = push Prod.snd (fun v => pairMass K v.2 v.1) := by
          rw [push_clusterTriple_pair K]
    _ = K.s := by
          funext c
          unfold push
          simp only [sum_filter, Fintype.sum_prod_type]
          simp [Finset.sum_ite_eq', mem_univ, sum_pairMass_right K c]

private lemma clusterTripleLaw_isPMF : IsPMF (clusterTripleLaw K) := by
  rw [← push_clusterTriple K]
  exact isPMF_push (replicaLaw_isPMF D)

private lemma H_eq_sum_lg_inv {ω : Type*} [Fintype ω] {m : ω → ℝ} (hm : IsPMF m) :
    H m = ∑ a, m a * lg (1 / m a) := by
  unfold H
  rw [hm.total]

private lemma H_push_eq_sum_lg_inv {ω ξ : Type*} [Fintype ω] [Fintype ξ]
    [DecidableEq ξ] {m : ω → ℝ} (hm : IsPMF m) (f : ω → ξ) :
    H (push f m) = ∑ a, m a * lg (1 / push f m (f a)) := by
  rw [H_eq_sum_lg_inv (isPMF_push hm)]
  exact sum_push_mul f m (fun x => lg (1 / push f m x))

private lemma push_id_eq {ω : Type*} [Fintype ω] [DecidableEq ω] (m : ω → ℝ) :
    push id m = m := by
  funext a
  unfold push
  apply sum_eq_single a
  · intro b hb hba
    have heq : b = a := by simpa using (mem_filter.mp hb).2
    exact (hba heq).elim
  · intro ha
    exact (ha (by simp)).elim

private lemma pairMass_mul_KL (c d : K.κ) :
    pairMass K c d * KL (overlapLaw K c d) (K.Q c) =
      ∑ z, p z * K.sigma c z * K.sigma d z *
        lg (overlapLaw K c d z / K.Q c z) := by
  unfold KL
  rw [mul_sum]
  apply sum_congr rfl
  intro z _
  unfold overlapLaw
  field_simp [(pairMass_pos K c d).ne']

private lemma overlap_log_identity (c d : K.κ) (z : α × β) :
    p z * K.sigma c z * K.sigma d z * lg (overlapLaw K c d z / K.Q c z) =
      p z * K.sigma c z * K.sigma d z *
        (lg (1 / pairMass K c d) + lg (1 / (p z * K.sigma c z)) -
          lg (1 / (p z * K.sigma c z * K.sigma d z)) - lg (1 / K.s c)) := by
  by_cases hz : p z = 0
  · simp [hz]
  · have hpz : 0 < p z := lt_of_le_of_ne (D.isPMF.nonneg z) (Ne.symm hz)
    have hzsupp : z ∈ support p := by simpa [support] using hz
    have hsc := s_pos K c
    have hsigc := K.sigma_pos c z hzsupp
    have hsigd := K.sigma_pos d z hzsupp
    have ha : 0 < p z * K.sigma c z := mul_pos hpz hsigc
    have ht : 0 < p z * K.sigma c z * K.sigma d z := mul_pos ha hsigd
    have hj := pairMass_pos K c d
    have hcal := p_mul_sigma K c z
    have hq : 0 < K.Q c z := by
      nlinarith [hsc, ha]
    have hlogcal : Real.log (p z * K.sigma c z) =
        Real.log (K.s c) + Real.log (K.Q c z) := by
      rw [hcal, Real.log_mul hsc.ne' hq.ne']
    have hlog2 : Real.log (2 : ℝ) ≠ 0 := Real.log_ne_zero.mpr (by norm_num)
    congr 1
    unfold overlapLaw
    simp only [lg_eq_log_div]
    rw [Real.log_div (div_ne_zero ht.ne' hj.ne') hq.ne',
      Real.log_div ht.ne' hj.ne', Real.log_div one_ne_zero hj.ne',
      Real.log_div one_ne_zero ha.ne', Real.log_div one_ne_zero ht.ne',
      Real.log_div one_ne_zero hsc.ne', Real.log_one, hlogcal]
    field_simp [hlog2]
    ring

private lemma sum_clusterTriple_expand
    (f : K.κ × ((α × β) × K.κ) → ℝ) :
    (∑ v, f v) = ∑ d, ∑ z, ∑ c, f (d, z, c) := by
  rw [Fintype.sum_prod_type]
  apply sum_congr rfl
  intro d _
  rw [Fintype.sum_prod_type]

private lemma sum_triple_reorder (f : K.κ → (α × β) → K.κ → ℝ) :
    (∑ d, ∑ z, ∑ c, f d z c) = ∑ c, ∑ d, ∑ z, f d z c := by
  calc
    ∑ d, ∑ z, ∑ c, f d z c = ∑ d, ∑ c, ∑ z, f d z c := by
      apply sum_congr rfl
      intro d _
      rw [sum_comm]
    _ = ∑ c, ∑ d, ∑ z, f d z c := by rw [sum_comm]

lemma pairMass_comm (c d : K.κ) : pairMass K c d = pairMass K d c := by
  simp only [pairMass]
  apply sum_congr rfl
  intro z _
  ring

private lemma overlapLaw_comm (c d : K.κ) : overlapLaw K c d = overlapLaw K d c := by
  funext z
  unfold overlapLaw
  rw [pairMass_comm K c d]
  congr 1
  ring

private lemma overlapLaw_absCont_Q_right (c d : K.κ) :
    AbsCont (overlapLaw K c d) (K.Q d) := by
  intro z hQz
  have hzero := p_mul_sigma K d z
  rw [hQz, mul_zero] at hzero
  unfold overlapLaw
  calc
    p z * K.sigma c z * K.sigma d z / pairMass K c d =
        (p z * K.sigma d z) * K.sigma c z / pairMass K c d := by ring
    _ = 0 := by rw [hzero]; simp

private lemma KL_nonneg_local {P Q : α × β → ℝ} (hP : IsPMF P) (hQ : IsPMF Q)
    (hac : AbsCont P Q) : 0 ≤ KL P Q := by
  have hnats := gibbs_nonneg hP hQ (fun z hz => fun hQz => hz (hac z hQz))
  rw [KL]
  change 0 ≤ ∑ z, P z * (Real.log (P z / Q z) / Real.log 2)
  simp_rw [← mul_div_assoc]
  rw [← sum_div]
  exact div_nonneg hnats (Real.log_pos (by norm_num)).le

private lemma Q_pos_of_mem_support (c : K.κ) (z : α × β) (hz : z ∈ support p) :
    0 < K.Q c z := by
  have hpz_ne : p z ≠ 0 := by simpa [support] using hz
  have hpz : 0 < p z := lt_of_le_of_ne (D.isPMF.nonneg z) (Ne.symm hpz_ne)
  have hleft : 0 < p z * K.sigma c z := mul_pos hpz (K.sigma_pos c z hz)
  have hcal := p_mul_sigma K c z
  have hs := s_pos K c
  have hQnonneg := (Q_isPMF K c).nonneg z
  nlinarith

private lemma BC_Q_pos (c d : K.κ) : 0 < BC (K.Q c) (K.Q d) := by
  have hex : ∃ z, K.Q c z ≠ 0 := by
    by_contra h
    push Not at h
    have htotal := (Q_isPMF K c).total
    simp [mass, h] at htotal
  obtain ⟨z, hQz⟩ := hex
  have hz : z ∈ support p := by
    by_contra hz
    exact hQz (Q_supported K c z hz)
  unfold BC
  apply sum_pos'
  · intro w _
    exact Real.sqrt_nonneg _
  · exact ⟨z, mem_univ z,
      Real.sqrt_pos.2 (mul_pos (Q_pos_of_mem_support K c z hz)
        (Q_pos_of_mem_support K d z hz))⟩

/-- **(9.1)**: the exact conditional-KL expansion
`S = ∑_{c,d} J_{cd} D(r_{cd} ‖ Q_c)`, every term nonnegative. -/
theorem Sinfo_eq_sum_KL :
    K.Sinfo = ∑ c, ∑ d, pairMass K c d * KL (overlapLaw K c d) (K.Q c) := by
  rw [Sinfo_eq_clusterTriple_condMI K]
  have hr := clusterTripleLaw_isPMF K
  unfold condMI Hvar
  rw [H_push_eq_sum_lg_inv hr (fun v => (v.1, v.2.2)),
    H_push_eq_sum_lg_inv hr (fun v => (v.2.1, v.2.2)),
    H_push_eq_sum_lg_inv hr (fun v => (v.1, v.2.1, v.2.2)),
    H_push_eq_sum_lg_inv hr (fun v => v.2.2),
    push_clusterTriple_pair K, push_clusterTriple_zc K,
    push_clusterTriple_all K, push_clusterTriple_c K]
  rw [← sum_add_distrib, ← sum_sub_distrib, ← sum_sub_distrib]
  simp_rw [pairMass_mul_KL K]
  rw [sum_clusterTriple_expand K]
  rw [sum_triple_reorder K]
  apply sum_congr rfl
  intro c _
  apply sum_congr rfl
  intro d _
  apply sum_congr rfl
  intro z _
  simp only [clusterTripleLaw]
  rw [overlap_log_identity K c d z]
  ring

/-- A pair of distinct clusters is **near** when its laws are within `δ_*` in
total variation, and **far** otherwise. -/
def IsNear (c d : K.κ) : Prop := TV (K.Q c) (K.Q d) ≤ deltaStar

noncomputable instance (c d : K.κ) : Decidable (IsNear K c d) := Classical.dec _

private noncomputable def labelFiberBase (i : D.L.ι) : D.L.ι × (α × β) → ℝ :=
  fun w => if w.1 = i then D.L.comp i w.2 else 0

private lemma labelFiberBase_eq_push (i : D.L.ι) :
    labelFiberBase (D := D) i = push (fun z => (i, z)) (D.L.comp i) := by
  funext w
  rcases w with ⟨j, z⟩
  unfold labelFiberBase push
  by_cases hji : j = i
  · subst j
    simp only [if_true]
    symm
    apply sum_eq_single z
    · intro z' hz' hne
      have heq : z' = z := by simpa using (mem_filter.mp hz').2
      exact (hne heq).elim
    · intro hz
      exact (hz (by simp)).elim
  · simp only [if_neg hji]
    symm
    apply sum_eq_zero
    intro z' hz'
    have heq : i = j := congrArg Prod.fst (mem_filter.mp hz').2
    exact (hji heq.symm).elim

private lemma labelFiberBase_isFinMeas (i : D.L.ι) :
    IsFinMeas (labelFiberBase (D := D) i) := by
  rw [labelFiberBase_eq_push (D := D) i]
  exact isFinMeas_push (D.L.comp_isPMF i).isFinMeas

private lemma MI_labelFiberBase_eq_Ixy (i : D.L.ι) :
    MI (fun w : D.L.ι × (α × β) => w.2.1) (fun w => w.2.2)
      (labelFiberBase (D := D) i) = Ixy (D.L.comp i) := by
  rw [labelFiberBase_eq_push (D := D) i]
  unfold MI Hvar Ixy
  simp only [push_push, Function.comp_def]
  have hid : (fun z : α × β => (z.1, z.2)) = id := by
    funext z
    exact Prod.eta z
  rw [hid, push_id_eq]

private lemma MI_label_joint_fiber (i : D.L.ι) :
    MI (fun w : D.L.ι × (α × β) => w.2.1) (fun w => w.2.2)
      (fun w => if w.1 = i then D.L.joint w else 0) =
        D.L.prior i * Ixy (D.L.comp i) := by
  have hmeasure : (fun w : D.L.ι × (α × β) =>
      if w.1 = i then D.L.joint w else 0) =
      fun w => D.L.prior i * labelFiberBase (D := D) i w := by
    funext w
    rcases w with ⟨j, z⟩
    by_cases hji : j = i
    · subst j
      simp [Latent.joint, labelFiberBase]
    · simp [hji, Latent.joint, labelFiberBase]
  rw [hmeasure]
  rw [MI_smul (labelFiberBase_isFinMeas (D := D) i)
    (fun w : D.L.ι × (α × β) => w.2.1) (fun w => w.2.2)
    (D.L.prior_isPMF.nonneg i)]
  rw [MI_labelFiberBase_eq_Ixy (D := D) i]

private lemma M_eq_sum_prior_Ixy :
    D.M = ∑ i, D.L.prior i * Ixy (D.L.comp i) := by
  let mh : D.L.ι → (D.L.ι × (α × β) → ℝ) :=
    fun i w => if w.1 = i then D.L.joint w else 0
  have hj := D.L.joint_isPMF
  have hX := Hvar_pair_eq_sum_fibers hj (fun w => w.2.1) (fun w => w.1)
  have hY := Hvar_pair_eq_sum_fibers hj (fun w => w.2.2) (fun w => w.1)
  have hXY := Hvar_pair_eq_sum_fibers hj (fun w => (w.2.1, w.2.2)) (fun w => w.1)
  change Hvar (fun w => (w.2.1, w.1)) D.L.joint =
    Hvar (fun w => w.1) D.L.joint + ∑ i, H (push (fun w => w.2.1) (mh i)) at hX
  change Hvar (fun w => (w.2.2, w.1)) D.L.joint =
    Hvar (fun w => w.1) D.L.joint + ∑ i, H (push (fun w => w.2.2) (mh i)) at hY
  change Hvar (fun w => ((w.2.1, w.2.2), w.1)) D.L.joint =
    Hvar (fun w => w.1) D.L.joint +
      ∑ i, H (push (fun w => (w.2.1, w.2.2)) (mh i)) at hXY
  have hAssoc : Hvar (fun w => (w.2.1, w.2.2, w.1)) D.L.joint =
      Hvar (fun w => ((w.2.1, w.2.2), w.1)) D.L.joint := by
    simpa using Hvar_equiv hj (fun w => ((w.2.1, w.2.2), w.1))
      (Equiv.prodAssoc α β D.L.ι)
  have hEq : D.M = ∑ i,
      MI (fun w : D.L.ι × (α × β) => w.2.1) (fun w => w.2.2) (mh i) := by
    unfold SeedSetup.M condMI
    rw [hX, hY, hAssoc, hXY]
    simp only [MI, Hvar, sum_add_distrib, sum_sub_distrib]
    ring
  rw [hEq]
  apply sum_congr rfl
  intro i _
  exact MI_label_joint_fiber (D := D) i

private lemma M_eq_sum_s_Ixy : D.M = ∑ c, K.s c * Ixy (K.Q c) := by
  rw [M_eq_sum_prior_Ixy (D := D)]
  calc
    ∑ i, D.L.prior i * Ixy (D.L.comp i) =
        ∑ c, ∑ i ∈ univ.filter (fun i => K.cl i = c),
          D.L.prior i * Ixy (D.L.comp i) := by
            symm
            exact sum_fiberwise univ K.cl (fun i => D.L.prior i * Ixy (D.L.comp i))
    _ = ∑ c, ∑ i ∈ univ.filter (fun i => K.cl i = c),
          D.L.prior i * Ixy (K.Q c) := by
            apply sum_congr rfl
            intro c _
            apply sum_congr rfl
            intro i hi
            rw [comp_eq_Q K c i (mem_filter.mp hi).2]
    _ = ∑ c, K.s c * Ixy (K.Q c) := by
            apply sum_congr rfl
            intro c _
            rw [Clustering.s, sum_mul]

private lemma Ixy_nonneg_local {q : α × β → ℝ} (hq : IsPMF q) : 0 ≤ Ixy q := by
  have h := MI_nonneg hq Prod.fst Prod.snd
  unfold MI Hvar at h
  have hid : (fun z : α × β => (z.1, z.2)) = id := by
    funext z
    exact Prod.eta z
  rw [hid, push_id_eq] at h
  simpa [Ixy] using h

private lemma far_pair_KL (c d : K.κ) (hfar : ¬ IsNear K c d) :
    deltaStar ^ 2 / Real.log 2 ≤
      KL (overlapLaw K c d) (K.Q c) + KL (overlapLaw K c d) (K.Q d) := by
  have hQc := Q_isPMF K c
  have hQd := Q_isPMF K d
  have hr := overlapLaw_isPMF K c d
  have hbh := bhattacharyya_le hQc hQd hr
    (overlapLaw_absCont_Q K c d) (overlapLaw_absCont_Q_right K c d)
  have htv : TV (K.Q c) (K.Q d) ≤
      Real.sqrt (1 - BC (K.Q c) (K.Q d) ^ 2) := by
    simpa [TV, tvDist] using tv_le_bhattacharyya hQc hQd
  have hdelta_tv : deltaStar < TV (K.Q c) (K.Q d) := by
    exact lt_of_not_ge hfar
  have hsqrt_pos : 0 < Real.sqrt (1 - BC (K.Q c) (K.Q d) ^ 2) :=
    lt_of_lt_of_le (deltaStar_pos.trans hdelta_tv) htv
  have harg_pos : 0 < 1 - BC (K.Q c) (K.Q d) ^ 2 := Real.sqrt_pos.mp hsqrt_pos
  have htv_nonneg : 0 ≤ TV (K.Q c) (K.Q d) := by
    unfold TV
    positivity
  have htv_sq : TV (K.Q c) (K.Q d) ^ 2 ≤ 1 - BC (K.Q c) (K.Q d) ^ 2 := by
    have hsqrt_sq := Real.sq_sqrt harg_pos.le
    nlinarith
  have hdelta_sq : deltaStar ^ 2 < TV (K.Q c) (K.Q d) ^ 2 := by
    nlinarith [deltaStar_pos]
  have hB := BC_Q_pos K c d
  have hlog_bound := Real.log_le_sub_one_of_pos (sq_pos_of_pos hB)
  have hdelta_log : deltaStar ^ 2 ≤ -Real.log (BC (K.Q c) (K.Q d) ^ 2) := by
    nlinarith
  have hdelta_logB : deltaStar ^ 2 ≤ -2 * Real.log (BC (K.Q c) (K.Q d)) := by
    rw [Real.log_pow] at hdelta_log
    norm_num at hdelta_log ⊢
    exact hdelta_log
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  calc
    deltaStar ^ 2 / Real.log 2 ≤
        (-2 * Real.log (BC (K.Q c) (K.Q d))) / Real.log 2 :=
      (div_le_div_iff_of_pos_right hlog2).2 hdelta_logB
    _ = -2 * lg (BC (K.Q c) (K.Q d)) := by
      rw [lg_eq_log_div]
      ring
    _ ≤ KL (overlapLaw K c d) (K.Q c) + KL (overlapLaw K c d) (K.Q d) := hbh

/-- The near part of the charge: clusters incident to a near
pair are individually expensive, so `M` pays for them.
`∑_{(c,d) near} J_{cd} ≤ M / c_*`. -/
theorem near_charge :
    ∑ c, ∑ d ∈ univ.filter (fun d => c ≠ d ∧ IsNear K c d), pairMass K c d
      ≤ D.M / cStar := by
  let Incident : K.κ → Prop := fun c => ∃ d, c ≠ d ∧ IsNear K c d
  letI : DecidablePred Incident := fun c => Classical.dec _
  have hfloor (c : K.κ) (hc : Incident c) : cStar ≤ Ixy (K.Q c) := by
    obtain ⟨d, hcd, hnear⟩ := hc
    have hQne : K.Q c ≠ K.Q d := fun h => hcd (K.Q_injective h)
    exact (nearcollision_floor D.feasible D.conn (K.Q_isContact c) (K.Q_isContact d)
      hQne hnear).2.2.1
  have hpay : cStar * (∑ c ∈ univ.filter Incident, K.s c) ≤ D.M := by
    calc
      cStar * (∑ c ∈ univ.filter Incident, K.s c) =
          ∑ c ∈ univ.filter Incident, cStar * K.s c := by rw [mul_sum]
      _ ≤ ∑ c ∈ univ.filter Incident, K.s c * Ixy (K.Q c) := by
        apply sum_le_sum
        intro c hc
        simpa [mul_comm] using
          mul_le_mul_of_nonneg_left (hfloor c (mem_filter.mp hc).2) (s_pos K c).le
      _ ≤ ∑ c, K.s c * Ixy (K.Q c) := by
        exact sum_le_univ_sum_of_nonneg fun c =>
          mul_nonneg (s_pos K c).le (Ixy_nonneg_local (Q_isPMF K c))
      _ = D.M := (M_eq_sum_s_Ixy K).symm
  have hmass : (∑ c ∈ univ.filter Incident, K.s c) ≤ D.M / cStar := by
    apply (le_div_iff₀ cStar_pos).2
    simpa [mul_comm] using hpay
  have hnear_incident :
      (∑ c, ∑ d ∈ univ.filter (fun d => c ≠ d ∧ IsNear K c d), pairMass K c d) ≤
        ∑ c ∈ univ.filter Incident, K.s c := by
    rw [sum_filter]
    apply sum_le_sum
    intro c _
    by_cases hc : Incident c
    · rw [if_pos hc]
      calc
        ∑ d ∈ univ.filter (fun d => c ≠ d ∧ IsNear K c d), pairMass K c d ≤
            ∑ d, pairMass K c d :=
          sum_le_univ_sum_of_nonneg fun d => pairMass_nonneg K c d
        _ = K.s c := sum_pairMass_right K c
    · rw [if_neg hc]
      have hzero :
          (∑ d ∈ univ.filter (fun d => c ≠ d ∧ IsNear K c d), pairMass K c d) = 0 := by
        apply sum_eq_zero
        intro d hd
        exact (hc ⟨d, (mem_filter.mp hd).2⟩).elim
      rw [hzero]
  exact hnear_incident.trans hmass

/-- The far part of the charge: a far pair costs
`δ_*²/ln 2` inside the exact sum (9.1), by Bhattacharyya.
`2 ∑_{{c,d} far} J_{cd} ≤ (2 ln 2/δ_*²) S`. -/
theorem far_charge :
    ∑ c, ∑ d ∈ univ.filter (fun d => c ≠ d ∧ ¬ IsNear K c d), pairMass K c d
      ≤ 2 * Real.log 2 / deltaStar ^ 2 * K.Sinfo := by
  let a : ℝ := deltaStar ^ 2 / Real.log 2
  let F : ℝ :=
    ∑ c, ∑ d ∈ univ.filter (fun d => c ≠ d ∧ ¬ IsNear K c d), pairMass K c d
  let A₁ : ℝ :=
    ∑ c, ∑ d ∈ univ.filter (fun d => c ≠ d ∧ ¬ IsNear K c d),
      pairMass K c d * KL (overlapLaw K c d) (K.Q c)
  let A₂ : ℝ :=
    ∑ c, ∑ d ∈ univ.filter (fun d => c ≠ d ∧ ¬ IsNear K c d),
      pairMass K c d * KL (overlapLaw K c d) (K.Q d)
  have hA₁ : A₁ ≤ K.Sinfo := by
    dsimp [A₁]
    rw [Sinfo_eq_sum_KL K]
    apply sum_le_sum
    intro c _
    exact sum_le_univ_sum_of_nonneg fun d =>
      mul_nonneg (pairMass_nonneg K c d)
        (KL_nonneg_local (overlapLaw_isPMF K c d) (Q_isPMF K c)
          (overlapLaw_absCont_Q K c d))
  have hall₂ : (∑ c, ∑ d, pairMass K c d * KL (overlapLaw K c d) (K.Q d)) =
      K.Sinfo := by
    rw [Sinfo_eq_sum_KL K]
    rw [sum_comm]
    apply sum_congr rfl
    intro c _
    apply sum_congr rfl
    intro d _
    rw [pairMass_comm K d c, overlapLaw_comm K d c]
  have hA₂ : A₂ ≤ K.Sinfo := by
    calc
      A₂ ≤ ∑ c, ∑ d, pairMass K c d * KL (overlapLaw K c d) (K.Q d) := by
        dsimp [A₂]
        apply sum_le_sum
        intro c _
        exact sum_le_univ_sum_of_nonneg fun d =>
          mul_nonneg (pairMass_nonneg K c d)
            (KL_nonneg_local (overlapLaw_isPMF K c d) (Q_isPMF K d)
              (overlapLaw_absCont_Q_right K c d))
      _ = K.Sinfo := hall₂
  have hcost : a * F ≤ A₁ + A₂ := by
    calc
      a * F = ∑ c, ∑ d ∈ univ.filter (fun d => c ≠ d ∧ ¬ IsNear K c d),
          a * pairMass K c d := by
            dsimp [F]
            rw [mul_sum]
            apply sum_congr rfl
            intro c _
            rw [mul_sum]
      _ ≤ ∑ c, ∑ d ∈ univ.filter (fun d => c ≠ d ∧ ¬ IsNear K c d),
          pairMass K c d *
            (KL (overlapLaw K c d) (K.Q c) + KL (overlapLaw K c d) (K.Q d)) := by
            apply sum_le_sum
            intro c _
            apply sum_le_sum
            intro d hd
            have hfar := (mem_filter.mp hd).2.2
            simpa [a, mul_comm] using
              mul_le_mul_of_nonneg_left (far_pair_KL K c d hfar)
                (pairMass_nonneg K c d)
      _ = A₁ + A₂ := by
            dsimp [A₁, A₂]
            simp_rw [mul_add, sum_add_distrib]
  have htotal : a * F ≤ 2 * K.Sinfo := by linarith
  have ha : 0 < a := by
    exact div_pos (sq_pos_of_pos deltaStar_pos) (Real.log_pos (by norm_num))
  change F ≤ 2 * Real.log 2 / deltaStar ^ 2 * K.Sinfo
  apply (mul_le_mul_iff_of_pos_left ha).mp
  calc
    a * F ≤ 2 * K.Sinfo := htotal
    _ = a * (2 * Real.log 2 / deltaStar ^ 2 * K.Sinfo) := by
      dsimp [a]
      field_simp [deltaStar_pos.ne', (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne']

private lemma dMis_eq_sum_pairMass :
    K.dMis = ∑ c, ∑ d ∈ univ.filter (fun d => c ≠ d), pairMass K c d := by
  rw [K.dMis_eq]
  unfold pairMass
  calc
    ∑ z, p z * (1 - ∑ c, K.sigma c z ^ 2) =
        ∑ z, ∑ c, ∑ d ∈ univ.filter (fun d => c ≠ d),
          p z * K.sigma c z * K.sigma d z := by
            apply sum_congr rfl
            intro z _
            by_cases hz : p z = 0
            · simp [hz]
            · have hsum := sum_sigma_eq_one K z hz
              have hrow (c : K.κ) :
                  (∑ d ∈ univ.filter (fun d => c ≠ d), K.sigma d z) =
                    1 - K.sigma c z := by
                rw [Finset.filter_ne]
                have herase := Finset.sum_erase_add (univ : Finset K.κ)
                  (fun d => K.sigma d z) (mem_univ c)
                linarith
              calc
                p z * (1 - ∑ c, K.sigma c z ^ 2) =
                    ∑ c, p z * K.sigma c z * (1 - K.sigma c z) := by
                      calc
                        p z * (1 - ∑ c, K.sigma c z ^ 2) =
                            p z * (∑ c, K.sigma c z) -
                              p z * (∑ c, K.sigma c z ^ 2) := by rw [hsum]; ring
                        _ = (∑ c, p z * K.sigma c z) -
                              ∑ c, p z * K.sigma c z ^ 2 := by rw [mul_sum, mul_sum]
                        _ = ∑ c, p z * K.sigma c z * (1 - K.sigma c z) := by
                              rw [← sum_sub_distrib]
                              apply sum_congr rfl
                              intro c _
                              ring
                _ = ∑ c, ∑ d ∈ univ.filter (fun d => c ≠ d),
                    p z * K.sigma c z * K.sigma d z := by
                      apply sum_congr rfl
                      intro c _
                      rw [← hrow c, mul_sum]
    _ = ∑ c, ∑ d ∈ univ.filter (fun d => c ≠ d),
        ∑ z, p z * K.sigma c z * K.sigma d z := by
          rw [sum_comm]
          apply sum_congr rfl
          intro c _
          rw [sum_comm]

/-- **Theorem 9.1** (the exact global charge), in bits:
`d ≤ M/c_* + (2 ln 2 / δ_*²) S`. -/
theorem mismatch_charge :
    K.dMis ≤ D.M / cStar + 2 * Real.log 2 / deltaStar ^ 2 * K.Sinfo := by
  rw [dMis_eq_sum_pairMass K]
  calc
    ∑ c, ∑ d ∈ univ.filter (fun d => c ≠ d), pairMass K c d =
        (∑ c, ∑ d ∈ univ.filter (fun d => c ≠ d ∧ IsNear K c d), pairMass K c d) +
          ∑ c, ∑ d ∈ univ.filter (fun d => c ≠ d ∧ ¬ IsNear K c d), pairMass K c d := by
            rw [← sum_add_distrib]
            apply sum_congr rfl
            intro c _
            simp only [sum_filter, ← sum_add_distrib]
            apply sum_congr rfl
            intro d _
            by_cases hcd : c ≠ d
            · by_cases hn : IsNear K c d <;> simp [hcd, hn]
            · simp [hcd]
    _ ≤ D.M / cStar + 2 * Real.log 2 / deltaStar ^ 2 * K.Sinfo :=
      add_le_add (near_charge K) (far_charge K)

/-- The form §10 consumes: `d/ln 2 ≤ K_orth (M + S)`, using
that `1/(c_* ln 2) = N = K_orth` dominates `2/δ_*² ≈ 1.1 × 10¹⁰`. -/
theorem mismatch_charge_Korth :
    K.dMis / Real.log 2 ≤ Korth * (D.M + K.Sinfo) := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hS : 0 ≤ K.Sinfo := by
    unfold Clustering.Sinfo
    exact condMI_nonneg (replicaLaw_isPMF D) (fun u => K.cl u.2.1)
      (fun u => u.2.2.2) (fun u => K.cl u.1)
  have hcoef : 2 / deltaStar ^ 2 ≤ Korth := by
    norm_num [deltaStar, Korth, N]
  calc
    K.dMis / Real.log 2 ≤
        (D.M / cStar + 2 * Real.log 2 / deltaStar ^ 2 * K.Sinfo) / Real.log 2 :=
      (div_le_div_iff_of_pos_right hlog).2 (mismatch_charge K)
    _ = D.M / (cStar * Real.log 2) + 2 / deltaStar ^ 2 * K.Sinfo := by
      field_simp [hlog.ne', cStar_pos.ne', deltaStar_pos.ne']
    _ = Korth * D.M + 2 / deltaStar ^ 2 * K.Sinfo := by
      rw [show D.M / (cStar * Real.log 2) =
          (1 / (cStar * Real.log 2)) * D.M by ring,
        one_div_cStar_mul_log_two]
    _ ≤ Korth * D.M + Korth * K.Sinfo := by
      exact add_le_add (le_refl _) (mul_le_mul_of_nonneg_right hcoef hS)
    _ = Korth * (D.M + K.Sinfo) := by ring

/-! ## Parametric Hellinger mismatch charge -/

/-- Squared-Hellinger near relation at an arbitrary threshold. -/
def IsHNearAt (δ : ℝ) (c d : K.κ) : Prop :=
  hellingerSq (K.Q c) (K.Q d) ≤ δ

noncomputable instance instDecidableIsHNearAt (δ : ℝ) (c d : K.κ) :
    Decidable (IsHNearAt K δ c d) := Classical.dec _

/-- A Hellinger-far pair pays at least `δ / log 2` in the two directed KL
charges. -/
theorem far_pair_KL_of_not_hnear (δ : ℝ) (c d : K.κ)
    (hfar : ¬ IsHNearAt K δ c d) :
    δ / Real.log 2 ≤
      KL (overlapLaw K c d) (K.Q c) + KL (overlapLaw K c d) (K.Q d) := by
  have hQc := Q_isPMF K c
  have hQd := Q_isPMF K d
  have hr := overlapLaw_isPMF K c d
  have hbh := bhattacharyya_le hQc hQd hr
    (overlapLaw_absCont_Q K c d) (overlapLaw_absCont_Q_right K c d)
  have hdelta : δ < hellingerSq (K.Q c) (K.Q d) :=
    lt_of_not_ge hfar
  have hhell := hellingerSq_eq_two_mul_one_sub_BC hQc hQd
  have hB : 0 < BC (K.Q c) (K.Q d) := BC_Q_pos K c d
  have hlog_bound := Real.log_le_sub_one_of_pos hB
  have hdelta_log :
      δ ≤ -2 * Real.log (BC (K.Q c) (K.Q d)) := by
    rw [hhell] at hdelta
    linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  calc
    δ / Real.log 2 ≤
        (-2 * Real.log (BC (K.Q c) (K.Q d))) / Real.log 2 :=
      (div_le_div_iff_of_pos_right hlog2).2 hdelta_log
    _ = -2 * lg (BC (K.Q c) (K.Q d)) := by
      rw [lg_eq_log_div]
      ring
    _ ≤ KL (overlapLaw K c d) (K.Q c) +
        KL (overlapLaw K c d) (K.Q d) := hbh

/-- Near pairs at threshold `δ` are paid for by any positive information floor
valid for each incident first component. -/
theorem near_charge_of_hellinger_floor (δ F : ℝ) (hF : 0 < F)
    (hfloor : ∀ c d : K.κ, c ≠ d → IsHNearAt K δ c d → F ≤ Ixy (K.Q c)) :
    ∑ c, ∑ d ∈ univ.filter (fun d => c ≠ d ∧ IsHNearAt K δ c d), pairMass K c d
      ≤ D.M / F := by
  let Incident : K.κ → Prop := fun c => ∃ d, c ≠ d ∧ IsHNearAt K δ c d
  letI : DecidablePred Incident := fun c => Classical.dec _
  have hfloor_c (c : K.κ) (hc : Incident c) : F ≤ Ixy (K.Q c) := by
    obtain ⟨d, hcd, hnear⟩ := hc
    exact hfloor c d hcd hnear
  have hpay : F * (∑ c ∈ univ.filter Incident, K.s c) ≤ D.M := by
    calc
      F * (∑ c ∈ univ.filter Incident, K.s c) =
          ∑ c ∈ univ.filter Incident, F * K.s c := by
            rw [mul_sum]
      _ ≤ ∑ c ∈ univ.filter Incident, K.s c * Ixy (K.Q c) := by
        apply sum_le_sum
        intro c hc
        simpa [mul_comm] using
          mul_le_mul_of_nonneg_left (hfloor_c c (mem_filter.mp hc).2) (s_pos K c).le
      _ ≤ ∑ c, K.s c * Ixy (K.Q c) := by
        exact sum_le_univ_sum_of_nonneg fun c =>
          mul_nonneg (s_pos K c).le (Ixy_nonneg_local (Q_isPMF K c))
      _ = D.M := (M_eq_sum_s_Ixy K).symm
  have hmass : (∑ c ∈ univ.filter Incident, K.s c) ≤ D.M / F := by
    apply (le_div_iff₀ hF).2
    simpa [mul_comm] using hpay
  have hnear_incident :
      (∑ c, ∑ d ∈ univ.filter (fun d => c ≠ d ∧ IsHNearAt K δ c d),
        pairMass K c d) ≤ ∑ c ∈ univ.filter Incident, K.s c := by
    rw [sum_filter]
    apply sum_le_sum
    intro c _
    by_cases hc : Incident c
    · rw [if_pos hc]
      calc
        ∑ d ∈ univ.filter (fun d => c ≠ d ∧ IsHNearAt K δ c d), pairMass K c d ≤
            ∑ d, pairMass K c d :=
          sum_le_univ_sum_of_nonneg fun d => pairMass_nonneg K c d
        _ = K.s c := sum_pairMass_right K c
    · rw [if_neg hc]
      have hzero :
          (∑ d ∈ univ.filter (fun d => c ≠ d ∧ IsHNearAt K δ c d),
            pairMass K c d) = 0 := by
        apply sum_eq_zero
        intro d hd
        exact (hc ⟨d, (mem_filter.mp hd).2⟩).elim
      rw [hzero]
  exact hnear_incident.trans hmass

/-- Far pairs at a positive squared-Hellinger threshold `δ` are paid for at
cost `δ / log 2`; ordered pairs cause the factor two. -/
theorem far_charge_of_hellinger (δ : ℝ) (hδ : 0 < δ) :
    ∑ c, ∑ d ∈ univ.filter (fun d => c ≠ d ∧ ¬ IsHNearAt K δ c d), pairMass K c d
      ≤ 2 * Real.log 2 / δ * K.Sinfo := by
  let a : ℝ := δ / Real.log 2
  let Fmass : ℝ :=
    ∑ c, ∑ d ∈ univ.filter (fun d => c ≠ d ∧ ¬ IsHNearAt K δ c d), pairMass K c d
  let A₁ : ℝ :=
    ∑ c, ∑ d ∈ univ.filter (fun d => c ≠ d ∧ ¬ IsHNearAt K δ c d),
      pairMass K c d * KL (overlapLaw K c d) (K.Q c)
  let A₂ : ℝ :=
    ∑ c, ∑ d ∈ univ.filter (fun d => c ≠ d ∧ ¬ IsHNearAt K δ c d),
      pairMass K c d * KL (overlapLaw K c d) (K.Q d)
  have hA₁ : A₁ ≤ K.Sinfo := by
    dsimp [A₁]
    rw [Sinfo_eq_sum_KL K]
    apply sum_le_sum
    intro c _
    exact sum_le_univ_sum_of_nonneg fun d =>
      mul_nonneg (pairMass_nonneg K c d)
        (KL_nonneg_local (overlapLaw_isPMF K c d) (Q_isPMF K c)
          (overlapLaw_absCont_Q K c d))
  have hall₂ : (∑ c, ∑ d,
      pairMass K c d * KL (overlapLaw K c d) (K.Q d)) = K.Sinfo := by
    rw [Sinfo_eq_sum_KL K, sum_comm]
    apply sum_congr rfl
    intro c _
    apply sum_congr rfl
    intro d _
    rw [pairMass_comm K d c, overlapLaw_comm K d c]
  have hA₂ : A₂ ≤ K.Sinfo := by
    calc
      A₂ ≤ ∑ c, ∑ d,
          pairMass K c d * KL (overlapLaw K c d) (K.Q d) := by
        dsimp [A₂]
        apply sum_le_sum
        intro c _
        exact sum_le_univ_sum_of_nonneg fun d =>
          mul_nonneg (pairMass_nonneg K c d)
            (KL_nonneg_local (overlapLaw_isPMF K c d) (Q_isPMF K d)
              (overlapLaw_absCont_Q_right K c d))
      _ = K.Sinfo := hall₂
  have hcost : a * Fmass ≤ A₁ + A₂ := by
    calc
      a * Fmass = ∑ c, ∑ d ∈ univ.filter
          (fun d => c ≠ d ∧ ¬ IsHNearAt K δ c d), a * pairMass K c d := by
            dsimp [Fmass]
            rw [mul_sum]
            apply sum_congr rfl
            intro c _
            rw [mul_sum]
      _ ≤ ∑ c, ∑ d ∈ univ.filter
          (fun d => c ≠ d ∧ ¬ IsHNearAt K δ c d),
          pairMass K c d *
            (KL (overlapLaw K c d) (K.Q c) +
              KL (overlapLaw K c d) (K.Q d)) := by
            apply sum_le_sum
            intro c _
            apply sum_le_sum
            intro d hd
            have hfar := (mem_filter.mp hd).2.2
            simpa [a, mul_comm] using
              mul_le_mul_of_nonneg_left (far_pair_KL_of_not_hnear K δ c d hfar)
                (pairMass_nonneg K c d)
      _ = A₁ + A₂ := by
            dsimp [A₁, A₂]
            simp_rw [mul_add, sum_add_distrib]
  have htotal : a * Fmass ≤ 2 * K.Sinfo := by linarith
  have ha : 0 < a := div_pos hδ (Real.log_pos one_lt_two)
  change Fmass ≤ 2 * Real.log 2 / δ * K.Sinfo
  apply (mul_le_mul_iff_of_pos_left ha).mp
  calc
    a * Fmass ≤ 2 * K.Sinfo := htotal
    _ = a * (2 * Real.log 2 / δ * K.Sinfo) := by
      dsimp [a]
      field_simp [hδ.ne', (Real.log_pos one_lt_two).ne']

/-- Parametric Hellinger near/far mismatch charge. -/
theorem mismatch_charge_of_hellinger_floor (δ F : ℝ)
    (hδ : 0 < δ) (hF : 0 < F)
    (hfloor : ∀ c d : K.κ, c ≠ d → IsHNearAt K δ c d → F ≤ Ixy (K.Q c)) :
    K.dMis ≤ D.M / F + 2 * Real.log 2 / δ * K.Sinfo := by
  rw [dMis_eq_sum_pairMass K]
  calc
    ∑ c, ∑ d ∈ univ.filter (fun d => c ≠ d), pairMass K c d =
        (∑ c, ∑ d ∈ univ.filter
          (fun d => c ≠ d ∧ IsHNearAt K δ c d), pairMass K c d) +
        ∑ c, ∑ d ∈ univ.filter
          (fun d => c ≠ d ∧ ¬ IsHNearAt K δ c d), pairMass K c d := by
            rw [← sum_add_distrib]
            apply sum_congr rfl
            intro c _
            simp only [sum_filter, ← sum_add_distrib]
            apply sum_congr rfl
            intro d _
            by_cases hcd : c ≠ d
            · by_cases hn : IsHNearAt K δ c d <;> simp [hcd, hn]
            · simp [hcd]
    _ ≤ D.M / F + 2 * Real.log 2 / δ * K.Sinfo :=
      add_le_add (near_charge_of_hellinger_floor K δ F hF hfloor)
        (far_charge_of_hellinger K δ hδ)

/-! ## Improved Hellinger mismatch charge -/

/-- The improved near relation uses squared Hellinger distance directly. -/
def IsHNear (c d : K.κ) : Prop :=
  hellingerSq (K.Q c) (K.Q d) ≤ delta1771

noncomputable instance instDecidableIsHNear (c d : K.κ) :
    Decidable (IsHNear K c d) := Classical.dec _

private lemma far_pair_KL_1771 (c d : K.κ) (hfar : ¬ IsHNear K c d) :
    delta1771 / Real.log 2 ≤
      KL (overlapLaw K c d) (K.Q c) + KL (overlapLaw K c d) (K.Q d) := by
  have hQc := Q_isPMF K c
  have hQd := Q_isPMF K d
  have hr := overlapLaw_isPMF K c d
  have hbh := bhattacharyya_le hQc hQd hr
    (overlapLaw_absCont_Q K c d) (overlapLaw_absCont_Q_right K c d)
  have hdelta : delta1771 < hellingerSq (K.Q c) (K.Q d) :=
    lt_of_not_ge hfar
  have hhell := hellingerSq_eq_two_mul_one_sub_BC hQc hQd
  have hB : 0 < BC (K.Q c) (K.Q d) := BC_Q_pos K c d
  have hlog_bound := Real.log_le_sub_one_of_pos hB
  have hdelta_log :
      delta1771 ≤ -2 * Real.log (BC (K.Q c) (K.Q d)) := by
    rw [hhell] at hdelta
    linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  calc
    delta1771 / Real.log 2 ≤
        (-2 * Real.log (BC (K.Q c) (K.Q d))) / Real.log 2 :=
      (div_le_div_iff_of_pos_right hlog2).2 hdelta_log
    _ = -2 * lg (BC (K.Q c) (K.Q d)) := by
      rw [lg_eq_log_div]
      ring
    _ ≤ KL (overlapLaw K c d) (K.Q c) +
        KL (overlapLaw K c d) (K.Q d) := hbh

/-- Near pairs are paid for by the improved component-information floor. -/
theorem near_charge_1771 :
    ∑ c, ∑ d ∈ univ.filter (fun d => c ≠ d ∧ IsHNear K c d), pairMass K c d
      ≤ D.M / infoFloor1771 := by
  let Incident : K.κ → Prop := fun c => ∃ d, c ≠ d ∧ IsHNear K c d
  letI : DecidablePred Incident := fun c => Classical.dec _
  have hfloor (c : K.κ) (hc : Incident c) : infoFloor1771 ≤ Ixy (K.Q c) := by
    obtain ⟨d, hcd, hnear⟩ := hc
    have hQne : K.Q c ≠ K.Q d := fun h => hcd (K.Q_injective h)
    exact (nearcollision_floor_hellinger D.feasible D.conn
      (K.Q_isContact c) (K.Q_isContact d) hQne hnear).2.2.1
  have hpay : infoFloor1771 *
      (∑ c ∈ univ.filter Incident, K.s c) ≤ D.M := by
    calc
      infoFloor1771 * (∑ c ∈ univ.filter Incident, K.s c) =
          ∑ c ∈ univ.filter Incident, infoFloor1771 * K.s c := by
            rw [mul_sum]
      _ ≤ ∑ c ∈ univ.filter Incident, K.s c * Ixy (K.Q c) := by
        apply sum_le_sum
        intro c hc
        simpa [mul_comm] using
          mul_le_mul_of_nonneg_left (hfloor c (mem_filter.mp hc).2) (s_pos K c).le
      _ ≤ ∑ c, K.s c * Ixy (K.Q c) := by
        exact sum_le_univ_sum_of_nonneg fun c =>
          mul_nonneg (s_pos K c).le (Ixy_nonneg_local (Q_isPMF K c))
      _ = D.M := (M_eq_sum_s_Ixy K).symm
  have hmass : (∑ c ∈ univ.filter Incident, K.s c) ≤
      D.M / infoFloor1771 := by
    apply (le_div_iff₀ infoFloor1771_pos).2
    simpa [mul_comm] using hpay
  have hnear_incident :
      (∑ c, ∑ d ∈ univ.filter (fun d => c ≠ d ∧ IsHNear K c d),
        pairMass K c d) ≤ ∑ c ∈ univ.filter Incident, K.s c := by
    rw [sum_filter]
    apply sum_le_sum
    intro c _
    by_cases hc : Incident c
    · rw [if_pos hc]
      calc
        ∑ d ∈ univ.filter (fun d => c ≠ d ∧ IsHNear K c d), pairMass K c d ≤
            ∑ d, pairMass K c d :=
          sum_le_univ_sum_of_nonneg fun d => pairMass_nonneg K c d
        _ = K.s c := sum_pairMass_right K c
    · rw [if_neg hc]
      have hzero :
          (∑ d ∈ univ.filter (fun d => c ≠ d ∧ IsHNear K c d),
            pairMass K c d) = 0 := by
        apply sum_eq_zero
        intro d hd
        exact (hc ⟨d, (mem_filter.mp hd).2⟩).elim
      rw [hzero]
  exact hnear_incident.trans hmass

/-- Far pairs are paid for at cost `delta1771 / log 2`; ordered pairs cause
the factor two in the resulting coefficient. -/
theorem far_charge_1771 :
    ∑ c, ∑ d ∈ univ.filter (fun d => c ≠ d ∧ ¬ IsHNear K c d), pairMass K c d
      ≤ 2 * Real.log 2 / delta1771 * K.Sinfo := by
  let a : ℝ := delta1771 / Real.log 2
  let F : ℝ :=
    ∑ c, ∑ d ∈ univ.filter (fun d => c ≠ d ∧ ¬ IsHNear K c d), pairMass K c d
  let A₁ : ℝ :=
    ∑ c, ∑ d ∈ univ.filter (fun d => c ≠ d ∧ ¬ IsHNear K c d),
      pairMass K c d * KL (overlapLaw K c d) (K.Q c)
  let A₂ : ℝ :=
    ∑ c, ∑ d ∈ univ.filter (fun d => c ≠ d ∧ ¬ IsHNear K c d),
      pairMass K c d * KL (overlapLaw K c d) (K.Q d)
  have hA₁ : A₁ ≤ K.Sinfo := by
    dsimp [A₁]
    rw [Sinfo_eq_sum_KL K]
    apply sum_le_sum
    intro c _
    exact sum_le_univ_sum_of_nonneg fun d =>
      mul_nonneg (pairMass_nonneg K c d)
        (KL_nonneg_local (overlapLaw_isPMF K c d) (Q_isPMF K c)
          (overlapLaw_absCont_Q K c d))
  have hall₂ : (∑ c, ∑ d,
      pairMass K c d * KL (overlapLaw K c d) (K.Q d)) = K.Sinfo := by
    rw [Sinfo_eq_sum_KL K, sum_comm]
    apply sum_congr rfl
    intro c _
    apply sum_congr rfl
    intro d _
    rw [pairMass_comm K d c, overlapLaw_comm K d c]
  have hA₂ : A₂ ≤ K.Sinfo := by
    calc
      A₂ ≤ ∑ c, ∑ d,
          pairMass K c d * KL (overlapLaw K c d) (K.Q d) := by
        dsimp [A₂]
        apply sum_le_sum
        intro c _
        exact sum_le_univ_sum_of_nonneg fun d =>
          mul_nonneg (pairMass_nonneg K c d)
            (KL_nonneg_local (overlapLaw_isPMF K c d) (Q_isPMF K d)
              (overlapLaw_absCont_Q_right K c d))
      _ = K.Sinfo := hall₂
  have hcost : a * F ≤ A₁ + A₂ := by
    calc
      a * F = ∑ c, ∑ d ∈ univ.filter
          (fun d => c ≠ d ∧ ¬ IsHNear K c d), a * pairMass K c d := by
            dsimp [F]
            rw [mul_sum]
            apply sum_congr rfl
            intro c _
            rw [mul_sum]
      _ ≤ ∑ c, ∑ d ∈ univ.filter
          (fun d => c ≠ d ∧ ¬ IsHNear K c d),
          pairMass K c d *
            (KL (overlapLaw K c d) (K.Q c) +
              KL (overlapLaw K c d) (K.Q d)) := by
            apply sum_le_sum
            intro c _
            apply sum_le_sum
            intro d hd
            have hfar := (mem_filter.mp hd).2.2
            simpa [a, mul_comm] using
              mul_le_mul_of_nonneg_left (far_pair_KL_1771 K c d hfar)
                (pairMass_nonneg K c d)
      _ = A₁ + A₂ := by
            dsimp [A₁, A₂]
            simp_rw [mul_add, sum_add_distrib]
  have htotal : a * F ≤ 2 * K.Sinfo := by linarith
  have ha : 0 < a :=
    div_pos delta1771_pos (Real.log_pos one_lt_two)
  change F ≤ 2 * Real.log 2 / delta1771 * K.Sinfo
  apply (mul_le_mul_iff_of_pos_left ha).mp
  calc
    a * F ≤ 2 * K.Sinfo := htotal
    _ = a * (2 * Real.log 2 / delta1771 * K.Sinfo) := by
      dsimp [a]
      field_simp [delta1771_pos.ne', (Real.log_pos one_lt_two).ne']

/-- **Theorem 9.1 (improved)**: the Hellinger near/far split with the exact
constants consumed by the `1771` seed ledger. -/
theorem mismatch_charge_1771 :
    K.dMis ≤ D.M / infoFloor1771 +
      2 * Real.log 2 / delta1771 * K.Sinfo := by
  rw [dMis_eq_sum_pairMass K]
  calc
    ∑ c, ∑ d ∈ univ.filter (fun d => c ≠ d), pairMass K c d =
        (∑ c, ∑ d ∈ univ.filter
          (fun d => c ≠ d ∧ IsHNear K c d), pairMass K c d) +
        ∑ c, ∑ d ∈ univ.filter
          (fun d => c ≠ d ∧ ¬ IsHNear K c d), pairMass K c d := by
            rw [← sum_add_distrib]
            apply sum_congr rfl
            intro c _
            simp only [sum_filter, ← sum_add_distrib]
            apply sum_congr rfl
            intro d _
            by_cases hcd : c ≠ d
            · by_cases hn : IsHNear K c d <;> simp [hcd, hn]
            · simp [hcd]
    _ ≤ D.M / infoFloor1771 +
        2 * Real.log 2 / delta1771 * K.Sinfo :=
      add_le_add (near_charge_1771 K) (far_charge_1771 K)

end stoch_to_det
