import stoch_to_det.DomFloorCore

namespace stoch_to_det

open Finset

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

private lemma joint_pos_marginals_price {q : α × β → ℝ} (hq : IsPMF q)
    {z : α × β} (hz : 0 < q z) :
    0 < mX q z.1 ∧ 0 < mY q z.2 := by
  have hxle : q z ≤ mX q z.1 := by
    change q z ≤ push Prod.fst q z.1
    unfold push
    exact Finset.single_le_sum (fun u _ => hq.nonneg u) (by simp)
  have hyle : q z ≤ mY q z.2 := by
    change q z ≤ push Prod.snd q z.2
    unfold push
    exact Finset.single_le_sum (fun u _ => hq.nonneg u) (by simp)
  exact ⟨hz.trans_le hxle, hz.trans_le hyle⟩

private lemma abs_density_identity
    {q : α × β → ℝ} (hq : IsPMF q) (z : α × β)
    (f : α → ℝ) (g : β → ℝ) :
    let μ := mX q z.1 * mY q z.2
    let r := q z / μ
    let s := Real.sqrt (mX q z.1) * |f z.1| *
      (Real.sqrt (mY q z.2) * |g z.2|)
    |q z - μ| * |f z.1| * |g z.2| =
      Real.sqrt μ * |r - 1| * s := by
  dsimp
  have hqX : IsPMF (mX q) := isPMF_push hq
  have hqY : IsPMF (mY q) := isPMF_push hq
  have hμ0 : 0 ≤ mX q z.1 * mY q z.2 :=
    mul_nonneg (hqX.nonneg z.1) (hqY.nonneg z.2)
  by_cases hμ : mX q z.1 * mY q z.2 = 0
  · have hqz : q z = 0 := by
      by_contra hn
      have hqpos : 0 < q z := lt_of_le_of_ne (hq.nonneg z) (Ne.symm hn)
      obtain ⟨hxpos, hypos⟩ := joint_pos_marginals_price hq hqpos
      exact (mul_ne_zero hxpos.ne' hypos.ne') hμ
    simp [hμ, hqz]
  · have hμpos : 0 < mX q z.1 * mY q z.2 := lt_of_le_of_ne hμ0 (Ne.symm hμ)
    have hdiff : q z - mX q z.1 * mY q z.2 =
        (mX q z.1 * mY q z.2) *
          (q z / (mX q z.1 * mY q z.2) - 1) := by
      rw [mul_sub, mul_one, mul_div_cancel₀ _ hμ]
    have hsqrt : Real.sqrt (mX q z.1 * mY q z.2) =
        Real.sqrt (mX q z.1) * Real.sqrt (mY q z.2) := by
      exact Real.sqrt_mul (hqX.nonneg z.1) (mY q z.2)
    rw [hdiff, abs_mul, abs_of_pos hμpos, hsqrt]
    have hxy : mX q z.1 * mY q z.2 =
        (Real.sqrt (mX q z.1) * Real.sqrt (mY q z.2)) *
          (Real.sqrt (mX q z.1) * Real.sqrt (mY q z.2)) := by
      calc
        mX q z.1 * mY q z.2 =
            (Real.sqrt (mX q z.1)) ^ 2 * (Real.sqrt (mY q z.2)) ^ 2 := by
              rw [Real.sq_sqrt (hqX.nonneg z.1), Real.sq_sqrt (hqY.nonneg z.2)]
        _ = _ := by ring
    rw [hxy]
    ring

private lemma s_rpow_four_thirds
    {qx qy fx gy : ℝ} (hqx : 0 ≤ qx) (hqy : 0 ≤ qy) :
    (Real.sqrt qx * |fx| * (Real.sqrt qy * |gy|)) ^ ((4 : ℝ) / 3) =
      (qx * fx ^ 2) ^ ((2 : ℝ) / 3) *
        (qy * gy ^ 2) ^ ((2 : ℝ) / 3) := by
  let s : ℝ := Real.sqrt qx * |fx| * (Real.sqrt qy * |gy|)
  have hs0 : 0 ≤ s := by dsimp [s]; positivity
  have hs2 : s ^ 2 = (qx * fx ^ 2) * (qy * gy ^ 2) := by
    dsimp [s]
    rw [show (Real.sqrt qx * |fx| * (Real.sqrt qy * |gy|)) ^ 2 =
        (Real.sqrt qx) ^ 2 * |fx| ^ 2 * ((Real.sqrt qy) ^ 2 * |gy| ^ 2) by ring,
      Real.sq_sqrt hqx, Real.sq_sqrt hqy, sq_abs, sq_abs]
  calc
    s ^ ((4 : ℝ) / 3) = (s ^ 2) ^ ((2 : ℝ) / 3) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hs0]
      norm_num
    _ = ((qx * fx ^ 2) * (qy * gy ^ 2)) ^ ((2 : ℝ) / 3) := by rw [hs2]
    _ = (qx * fx ^ 2) ^ ((2 : ℝ) / 3) *
        (qy * gy ^ 2) ^ ((2 : ℝ) / 3) := by
      rw [Real.mul_rpow (mul_nonneg hqx (sq_nonneg fx))
        (mul_nonneg hqy (sq_nonneg gy))]

/-- Price-dual aggregation of the calibrated pointwise scalar estimate. -/
theorem contact_correlation_price
    {S : Finset (α × β)} {w q : α × β → ℝ}
    (hq : IsPMF q) (hw : Feasible S w) (hcontact : IsContact S w q)
    {f : α → ℝ} {g : β → ℝ}
    (hf0 : ∑ x, mX q x * f x = 0)
    (hg0 : ∑ y, mY q y * g y = 0)
    (hf2 : ∑ x, mX q x * f x ^ 2 = 1)
    (hg2 : ∑ y, mY q y * g y ^ 2 = 1)
    (hcell : ∀ μc sc rc : ℝ, 0 ≤ μc → 0 ≤ sc → 0 ≤ rc →
      Real.sqrt μc * |rc - 1| * sc ≤
        (167/1000 : ℝ) * (μc ^ ((1:ℝ)/3) * rc * sc ^ ((4:ℝ)/3))
          + (1/20 : ℝ) * sc^2 + (687/100 : ℝ) * (μc * phi rc))
    (hK : Knat q ≤ (9/400 : ℝ) * Real.log 2) :
    (∑ z, q z * f z.1 * g z.2) ≤ (217/1000 : ℝ) + (6183/40000 : ℝ) * Real.log 2 := by
  classical
  let μ : α × β → ℝ := fun z => mX q z.1 * mY q z.2
  let r : α × β → ℝ := fun z => q z / μ z
  let s : α × β → ℝ := fun z => Real.sqrt (mX q z.1) * |f z.1| *
    (Real.sqrt (mY q z.2) * |g z.2|)
  let W : α × β → ℝ := fun z => μ z ^ ((1 : ℝ) / 3) * r z * s z ^ ((4 : ℝ) / 3)
  let V : α × β → ℝ := fun z => s z ^ 2
  let K : α × β → ℝ := fun z => μ z * phi (r z)
  let R : α × β → ℝ := fun z => |q z - μ z| * |f z.1| * |g z.2|
  have hqX : IsPMF (mX q) := isPMF_push hq
  have hqY : IsPMF (mY q) := isPMF_push hq
  have hμ0 : ∀ z, 0 ≤ μ z := fun z => mul_nonneg (hqX.nonneg z.1) (hqY.nonneg z.2)
  have hr0 : ∀ z, 0 ≤ r z := fun z => div_nonneg (hq.nonneg z) (hμ0 z)
  have hs0 : ∀ z, 0 ≤ s z := fun z => by dsimp [s]; positivity
  have hmu_fg : (∑ z, μ z * f z.1 * g z.2) = 0 := by
    rw [Fintype.sum_prod_type]
    calc
      (∑ x, ∑ y, μ (x, y) * f x * g y) =
          ∑ x, (mX q x * f x) * (∑ y, mY q y * g y) := by
            apply Finset.sum_congr rfl
            intro x _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro y _
            dsimp [μ]
            ring
      _ = (∑ x, mX q x * f x) * (∑ y, mY q y * g y) := by rw [Finset.sum_mul]
      _ = 0 := by rw [hf0, hg0]; norm_num
  have hcorr : (∑ z, q z * f z.1 * g z.2) =
      ∑ z, (q z - μ z) * f z.1 * g z.2 := by
    calc
      (∑ z, q z * f z.1 * g z.2) =
          (∑ z, (q z - μ z) * f z.1 * g z.2) +
            ∑ z, μ z * f z.1 * g z.2 := by
              rw [← Finset.sum_add_distrib]
              apply Finset.sum_congr rfl
              intro z _
              ring
      _ = ∑ z, (q z - μ z) * f z.1 * g z.2 := by rw [hmu_fg, add_zero]
  have hsigned : (∑ z, (q z - μ z) * f z.1 * g z.2) ≤ ∑ z, R z := by
    apply Finset.sum_le_sum
    intro z _
    calc
      (q z - μ z) * f z.1 * g z.2 ≤ |(q z - μ z) * f z.1 * g z.2| := le_abs_self _
      _ = R z := by dsimp [R]; rw [abs_mul, abs_mul]
  have hRcell : ∀ z, R z ≤
      (167/1000 : ℝ) * W z + (1/20 : ℝ) * V z + (687/100 : ℝ) * K z := by
    intro z
    rw [show R z = Real.sqrt (μ z) * |r z - 1| * s z by
      simpa [R, μ, r, s] using abs_density_identity hq z f g]
    exact hcell (μ z) (s z) (r z) (hμ0 z) (hs0 z) (hr0 z)
  have hRsum : (∑ z, R z) ≤
      (167/1000 : ℝ) * (∑ z, W z) +
        (1/20 : ℝ) * (∑ z, V z) +
          (687/100 : ℝ) * (∑ z, K z) := by
    calc
      (∑ z, R z) ≤ ∑ z, ((167/1000 : ℝ) * W z + (1/20 : ℝ) * V z +
          (687/100 : ℝ) * K z) := Finset.sum_le_sum fun z _ => hRcell z
      _ = _ := by simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  have hV : (∑ z, V z) = 1 := by
    rw [Fintype.sum_prod_type]
    calc
      (∑ x, ∑ y, V (x, y)) =
          ∑ x, (mX q x * f x ^ 2) * (∑ y, mY q y * g y ^ 2) := by
            apply Finset.sum_congr rfl
            intro x _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro y _
            dsimp [V, s]
            rw [show (Real.sqrt (mX q x) * |f x| *
                (Real.sqrt (mY q y) * |g y|)) ^ 2 =
                (Real.sqrt (mX q x)) ^ 2 * |f x| ^ 2 *
                  ((Real.sqrt (mY q y)) ^ 2 * |g y| ^ 2) by ring,
              Real.sq_sqrt (hqX.nonneg x), Real.sq_sqrt (hqY.nonneg y),
              sq_abs, sq_abs]
      _ = 1 := by rw [hg2]; simpa using hf2
  have hKsum : (∑ z, K z) = Knat q := by simp [K, Knat, μ, r, phi]
  let u : α → ℝ := fun x => mX q x * f x ^ 2
  let v : β → ℝ := fun y => mY q y * g y ^ 2
  have hu : IsPMF u := by
    constructor
    · intro x
      exact mul_nonneg (hqX.nonneg x) (sq_nonneg (f x))
    · simpa [mass, u] using hf2
  have hv : IsPMF v := by
    constructor
    · intro y
      exact mul_nonneg (hqY.nonneg y) (sq_nonneg (g y))
    · simpa [mass, v] using hg2
  have hWcell : ∀ z, W z ≤ if z ∈ S then w z * s z ^ ((4 : ℝ) / 3) else 0 := by
    intro z
    by_cases hzS : z ∈ S
    · rw [if_pos hzS]
      by_cases hμ : μ z = 0
      · have hr : r z = 0 := by simp [r, hμ]
        have hright : 0 ≤ w z * s z ^ ((4 : ℝ) / 3) :=
          mul_nonneg (hw.1 z hzS).le (Real.rpow_nonneg (hs0 z) _)
        simpa [W, hr] using hright
      · have hμpos : 0 < μ z := lt_of_le_of_ne (hμ0 z) (Ne.symm hμ)
        have hxne : mX q z.1 ≠ 0 := by
          intro hx
          apply hμ
          simp [μ, hx]
        have hyne : mY q z.2 ≠ 0 := by
          intro hy
          apply hμ
          simp [μ, hy]
        have hxpos : 0 < mX q z.1 := lt_of_le_of_ne (hqX.nonneg z.1) (Ne.symm hxne)
        have hypos : 0 < mY q z.2 := lt_of_le_of_ne (hqY.nonneg z.2) (Ne.symm hyne)
        have hμpow : μ z ^ ((2 : ℝ) / 3) =
            mX q z.1 ^ ((2 : ℝ) / 3) * mY q z.2 ^ ((2 : ℝ) / 3) := by
          dsimp [μ]
          rw [Real.mul_rpow hxpos.le hypos.le]
        have hprod : μ z ^ ((1 : ℝ) / 3) * μ z ^ ((2 : ℝ) / 3) = μ z := by
          rw [← Real.rpow_add hμpos]
          norm_num
        have hqform : q z = w z * μ z ^ ((2 : ℝ) / 3) := by
          rw [hcontact.2.2 z hzS, hμpow]
          ring
        have hbase : μ z ^ ((1 : ℝ) / 3) * r z = w z := by
          dsimp [r]
          rw [hqform]
          calc
            μ z ^ ((1 : ℝ) / 3) * (w z * μ z ^ ((2 : ℝ) / 3) / μ z) =
                w z * (μ z ^ ((1 : ℝ) / 3) * μ z ^ ((2 : ℝ) / 3)) / μ z := by ring
            _ = w z := by rw [hprod, mul_comm]; exact mul_div_cancel_left₀ (w z) hμ
        dsimp [W]
        rw [hbase]
    · rw [if_neg hzS]
      have hqz := hcontact.2.1 z hzS
      simp [W, r, hqz]
  have hWsumS : (∑ z, W z) ≤ ∑ z ∈ S, w z * s z ^ ((4 : ℝ) / 3) := by
    calc
      (∑ z, W z) ≤ ∑ z, if z ∈ S then w z * s z ^ ((4 : ℝ) / 3) else 0 :=
        Finset.sum_le_sum fun z _ => hWcell z
      _ = ∑ z ∈ S, w z * s z ^ ((4 : ℝ) / 3) := by simp
  have hsPow : ∀ z, s z ^ ((4 : ℝ) / 3) =
      u z.1 ^ ((2 : ℝ) / 3) * v z.2 ^ ((2 : ℝ) / 3) := by
    intro z
    simpa [s, u, v] using s_rpow_four_thirds (hqX.nonneg z.1) (hqY.nonneg z.2)
  have hLambda : (∑ z ∈ S, w z * s z ^ ((4 : ℝ) / 3)) = Lambda S w u v := by
    unfold Lambda
    apply Finset.sum_congr rfl
    intro z _
    rw [hsPow z]
    ring
  have hW : (∑ z, W z) ≤ 1 := by
    exact hWsumS.trans (by rw [hLambda]; exact hw.2 u v hu hv)
  have hlog0 : 0 ≤ Real.log 2 := (Real.log_pos one_lt_two).le
  rw [hcorr]
  calc
    (∑ z, (q z - μ z) * f z.1 * g z.2) ≤ ∑ z, R z := hsigned
    _ ≤ (167/1000 : ℝ) * (∑ z, W z) + (1/20 : ℝ) * (∑ z, V z) +
        (687/100 : ℝ) * (∑ z, K z) := hRsum
    _ ≤ (167/1000 : ℝ) * 1 + (1/20 : ℝ) * 1 +
        (687/100 : ℝ) * ((9/400 : ℝ) * Real.log 2) := by
      rw [hV, hKsum]
      gcongr
    _ = (217/1000 : ℝ) + (6183/40000 : ℝ) * Real.log 2 := by ring

end stoch_to_det
