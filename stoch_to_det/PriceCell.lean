import stoch_to_det.PhiBounds

namespace stoch_to_det

private lemma rpow_pow_eq_pow
    {x w : ℝ} (hx : 0 ≤ x) (n k : ℕ)
    (hw : w * (n : ℝ) = (k : ℝ)) :
    (x ^ w) ^ n = x ^ k := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx, hw, Real.rpow_natCast]

private lemma le_geom3_of_pow
    {x p₁ p₂ p₃ w₁ w₂ w₃ : ℝ} {n a b c : ℕ}
    (hp₁ : 0 ≤ p₁) (hp₂ : 0 ≤ p₂) (hp₃ : 0 ≤ p₃)
    (hn : n ≠ 0)
    (hw₁ : w₁ * (n : ℝ) = (a : ℝ))
    (hw₂ : w₂ * (n : ℝ) = (b : ℝ))
    (hw₃ : w₃ * (n : ℝ) = (c : ℝ))
    (hpow : x ^ n ≤ p₁ ^ a * p₂ ^ b * p₃ ^ c) :
    x ≤ p₁ ^ w₁ * p₂ ^ w₂ * p₃ ^ w₃ := by
  apply le_of_pow_le_pow_left₀ hn (by positivity)
  calc
    x ^ n ≤ p₁ ^ a * p₂ ^ b * p₃ ^ c := hpow
    _ = (p₁ ^ w₁ * p₂ ^ w₂ * p₃ ^ w₃) ^ n := by
      rw [mul_pow, mul_pow,
        rpow_pow_eq_pow hp₁ n a hw₁,
        rpow_pow_eq_pow hp₂ n b hw₂,
        rpow_pow_eq_pow hp₃ n c hw₃]

private lemma le_geom2_of_pow
    {x p₁ p₂ w₁ w₂ : ℝ} {n a b : ℕ}
    (hp₁ : 0 ≤ p₁) (hp₂ : 0 ≤ p₂)
    (hn : n ≠ 0)
    (hw₁ : w₁ * (n : ℝ) = (a : ℝ))
    (hw₂ : w₂ * (n : ℝ) = (b : ℝ))
    (hpow : x ^ n ≤ p₁ ^ a * p₂ ^ b) :
    x ≤ p₁ ^ w₁ * p₂ ^ w₂ := by
  apply le_of_pow_le_pow_left₀ hn (by positivity)
  calc
    x ^ n ≤ p₁ ^ a * p₂ ^ b := hpow
    _ = (p₁ ^ w₁ * p₂ ^ w₂) ^ n := by
      rw [mul_pow,
        rpow_pow_eq_pow hp₁ n a hw₁,
        rpow_pow_eq_pow hp₂ n b hw₂]

private lemma sqrt_pow_four {x : ℝ} (hx : 0 ≤ x) :
    (Real.sqrt x) ^ 4 = x ^ 2 := by
  calc
    (Real.sqrt x) ^ 4 = ((Real.sqrt x) ^ 2) ^ 2 := by ring
    _ = x ^ 2 := by rw [Real.sq_sqrt hx]

private lemma sqrt_pow_eight {x : ℝ} (hx : 0 ≤ x) :
    (Real.sqrt x) ^ 8 = x ^ 4 := by
  calc
    (Real.sqrt x) ^ 8 = ((Real.sqrt x) ^ 2) ^ 4 := by ring
    _ = x ^ 4 := by rw [Real.sq_sqrt hx]

private lemma sqrt_pow_sixteen {x : ℝ} (hx : 0 ≤ x) :
    (Real.sqrt x) ^ 16 = x ^ 8 := by
  calc
    (Real.sqrt x) ^ 16 = ((Real.sqrt x) ^ 2) ^ 8 := by ring
    _ = x ^ 8 := by rw [Real.sq_sqrt hx]

private lemma abs_pow_four (x : ℝ) : |x| ^ 4 = x ^ 4 := by
  rw [← abs_pow, abs_of_nonneg (by positivity : 0 ≤ x ^ 4)]

private lemma abs_pow_eight (x : ℝ) : |x| ^ 8 = x ^ 8 := by
  rw [← abs_pow, abs_of_nonneg (by positivity : 0 ≤ x ^ 8)]

private lemma abs_pow_sixteen (x : ℝ) : |x| ^ 16 = x ^ 16 := by
  rw [← abs_pow, abs_of_nonneg (by positivity : 0 ≤ x ^ 16)]

theorem price_cell_of_zones
    (hz1 : ∀ r : ℝ, 0 ≤ r → r ≤ 1/5 → (r - 1)^2 ≤ (687/500 : ℝ) * phi r)
    (hz2 : ∀ r : ℝ, 1/5 ≤ r → r ≤ 9/20 → (1 - r)^16 ≤ (934 : ℝ) * r^3 * phi r ^ 7)
    (hz3 : ∀ r : ℝ, 9/20 ≤ r → r ≤ 12 → (r - 1)^8 ≤ (217/10 : ℝ) * r^3 * phi r ^ 3)
    (hz4 : ∀ r : ℝ, 12 ≤ r → r ≤ 90 → (r - 1)^16 ≤ (147/10 : ℝ) * r^9 * phi r ^ 5)
    (hz5 : ∀ r : ℝ, 90 ≤ r → (r - 1)^4 ≤ (303/1000 : ℝ) * r^3 * phi r)
    {μ s r : ℝ} (hμ : 0 ≤ μ) (hs : 0 ≤ s) (hr : 0 ≤ r) :
    Real.sqrt μ * |r - 1| * s ≤
      (167/1000 : ℝ) * (μ ^ ((1:ℝ)/3) * r * s ^ ((4:ℝ)/3))
        + (1/20 : ℝ) * s^2 + (687/100 : ℝ) * (μ * phi r) := by
  let X : ℝ := Real.sqrt μ * |r - 1| * s
  let W : ℝ := (167/1000 : ℝ) * (μ ^ ((1:ℝ)/3) * r * s ^ ((4:ℝ)/3))
  let V : ℝ := (1/20 : ℝ) * s^2
  let K : ℝ := (687/100 : ℝ) * (μ * phi r)
  change X ≤ W + V + K
  have hphi : 0 ≤ phi r := phi_nonneg hr
  have hX : 0 ≤ X := by
    dsimp [X]
    positivity
  have hW : 0 ≤ W := by
    dsimp [W]
    positivity
  have hV : 0 ≤ V := by
    dsimp [V]
    positivity
  have hK : 0 ≤ K := by
    dsimp [K]
    positivity
  by_cases hr1 : r ≤ (1/5 : ℝ)
  · have hz := hz1 r hr hr1
    have hscale : 0 ≤ μ * s ^ 2 := mul_nonneg hμ (sq_nonneg s)
    have hsq : X ^ 2 ≤ 4 * V * K := by
      calc
        X ^ 2 = μ * s ^ 2 * (r - 1) ^ 2 := by
          dsimp [X]
          rw [mul_pow, mul_pow, Real.sq_sqrt hμ, sq_abs]
          ring
        _ ≤ μ * s ^ 2 * ((687/500 : ℝ) * phi r) :=
          mul_le_mul_of_nonneg_left hz hscale
        _ = 4 * V * K := by
          dsimp [V, K]
          ring
    have hvk : 4 * V * K ≤ (V + K) ^ 2 := by
      nlinarith [sq_nonneg (V - K)]
    have hxvk : X ≤ V + K :=
      le_of_pow_le_pow_left₀ (by norm_num) (add_nonneg hV hK) (hsq.trans hvk)
    linarith
  · by_cases hr2 : r ≤ (9/20 : ℝ)
    · have hr2lo : (1/5 : ℝ) ≤ r := by linarith
      let p₁ : ℝ := (16/3 : ℝ) * W
      let p₂ : ℝ := (8/3 : ℝ) * V
      let p₃ : ℝ := (16/7 : ℝ) * K
      let C₂ : ℝ :=
        ((16/3 : ℝ) * (167/1000 : ℝ)) ^ 3 *
        ((8/3 : ℝ) * (1/20 : ℝ)) ^ 6 *
        ((16/7 : ℝ) * (687/100 : ℝ)) ^ 7
      have hp₁ : 0 ≤ p₁ := by dsimp [p₁]; positivity
      have hp₂ : 0 ≤ p₂ := by dsimp [p₂]; positivity
      have hp₃ : 0 ≤ p₃ := by dsimp [p₃]; positivity
      have hC₂ : (934 : ℝ) ≤ C₂ := by
        dsimp [C₂]
        norm_num
      have hzone : (r - 1) ^ 16 ≤ C₂ * r ^ 3 * phi r ^ 7 := by
        calc
          (r - 1) ^ 16 = (1 - r) ^ 16 := by ring
          _ ≤ (934 : ℝ) * r ^ 3 * phi r ^ 7 := hz2 r hr2lo hr2
          _ = (934 : ℝ) * (r ^ 3 * phi r ^ 7) := by ring
          _ ≤ C₂ * (r ^ 3 * phi r ^ 7) :=
            mul_le_mul_of_nonneg_right hC₂
              (mul_nonneg (pow_nonneg hr 3) (pow_nonneg hphi 7))
          _ = C₂ * r ^ 3 * phi r ^ 7 := by ring
      have hμpow : (μ ^ ((1 : ℝ) / 3)) ^ 3 = μ := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hμ]
        norm_num
      have hspow : (s ^ ((4 : ℝ) / 3)) ^ 3 = s ^ 4 :=
        rpow_pow_eq_pow hs 3 4 (by norm_num)
      have hprod : p₁ ^ 3 * p₂ ^ 6 * p₃ ^ 7 =
          C₂ * μ ^ 8 * r ^ 3 * s ^ 16 * phi r ^ 7 := by
        dsimp [p₁, p₂, p₃, W, V, K, C₂]
        simp only [mul_pow, hμpow, hspow]
        ring
      have hXpow : X ^ 16 = μ ^ 8 * s ^ 16 * (r - 1) ^ 16 := by
        dsimp [X]
        simp only [mul_pow, sqrt_pow_sixteen hμ, abs_pow_sixteen]
        ring
      have hpow : X ^ 16 ≤ p₁ ^ 3 * p₂ ^ 6 * p₃ ^ 7 := by
        calc
          X ^ 16 = μ ^ 8 * s ^ 16 * (r - 1) ^ 16 := hXpow
          _ ≤ μ ^ 8 * s ^ 16 * (C₂ * r ^ 3 * phi r ^ 7) :=
            mul_le_mul_of_nonneg_left hzone
              (mul_nonneg (pow_nonneg hμ 8) (pow_nonneg hs 16))
          _ = p₁ ^ 3 * p₂ ^ 6 * p₃ ^ 7 := by rw [hprod]; ring
      have hxgm : X ≤
          p₁ ^ ((3 : ℝ) / 16) * p₂ ^ ((3 : ℝ) / 8) * p₃ ^ ((7 : ℝ) / 16) := by
        exact le_geom3_of_pow hp₁ hp₂ hp₃ (by norm_num)
          (by norm_num) (by norm_num) (by norm_num) hpow
      have hgm :
          p₁ ^ ((3 : ℝ) / 16) * p₂ ^ ((3 : ℝ) / 8) * p₃ ^ ((7 : ℝ) / 16) ≤
            W + V + K := by
        calc
          p₁ ^ ((3 : ℝ) / 16) * p₂ ^ ((3 : ℝ) / 8) * p₃ ^ ((7 : ℝ) / 16) ≤
              ((3 : ℝ) / 16) * p₁ + ((3 : ℝ) / 8) * p₂ + ((7 : ℝ) / 16) * p₃ :=
            Real.geom_mean_le_arith_mean3_weighted
              (by norm_num) (by norm_num) (by norm_num) hp₁ hp₂ hp₃ (by norm_num)
          _ = W + V + K := by dsimp [p₁, p₂, p₃]; ring
      exact hxgm.trans hgm
    · by_cases hr3 : r ≤ (12 : ℝ)
      · have hr3lo : (9/20 : ℝ) ≤ r := by linarith
        let p₁ : ℝ := (8/3 : ℝ) * W
        let p₂ : ℝ := (4 : ℝ) * V
        let p₃ : ℝ := (8/3 : ℝ) * K
        let C₃ : ℝ :=
          ((8/3 : ℝ) * (167/1000 : ℝ)) ^ 3 *
          ((4 : ℝ) * (1/20 : ℝ)) ^ 2 *
          ((8/3 : ℝ) * (687/100 : ℝ)) ^ 3
        have hp₁ : 0 ≤ p₁ := by dsimp [p₁]; positivity
        have hp₂ : 0 ≤ p₂ := by dsimp [p₂]; positivity
        have hp₃ : 0 ≤ p₃ := by dsimp [p₃]; positivity
        have hC₃ : (217/10 : ℝ) ≤ C₃ := by
          dsimp [C₃]
          norm_num
        have hzone : (r - 1) ^ 8 ≤ C₃ * r ^ 3 * phi r ^ 3 := by
          calc
            (r - 1) ^ 8 ≤ (217/10 : ℝ) * r ^ 3 * phi r ^ 3 := hz3 r hr3lo hr3
            _ = (217/10 : ℝ) * (r ^ 3 * phi r ^ 3) := by ring
            _ ≤ C₃ * (r ^ 3 * phi r ^ 3) :=
              mul_le_mul_of_nonneg_right hC₃
                (mul_nonneg (pow_nonneg hr 3) (pow_nonneg hphi 3))
            _ = C₃ * r ^ 3 * phi r ^ 3 := by ring
        have hμpow : (μ ^ ((1 : ℝ) / 3)) ^ 3 = μ := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hμ]
          norm_num
        have hspow : (s ^ ((4 : ℝ) / 3)) ^ 3 = s ^ 4 :=
          rpow_pow_eq_pow hs 3 4 (by norm_num)
        have hprod : p₁ ^ 3 * p₂ ^ 2 * p₃ ^ 3 =
            C₃ * μ ^ 4 * r ^ 3 * s ^ 8 * phi r ^ 3 := by
          dsimp [p₁, p₂, p₃, W, V, K, C₃]
          simp only [mul_pow, hμpow, hspow]
          ring
        have hXpow : X ^ 8 = μ ^ 4 * s ^ 8 * (r - 1) ^ 8 := by
          dsimp [X]
          simp only [mul_pow, sqrt_pow_eight hμ, abs_pow_eight]
          ring
        have hpow : X ^ 8 ≤ p₁ ^ 3 * p₂ ^ 2 * p₃ ^ 3 := by
          calc
            X ^ 8 = μ ^ 4 * s ^ 8 * (r - 1) ^ 8 := hXpow
            _ ≤ μ ^ 4 * s ^ 8 * (C₃ * r ^ 3 * phi r ^ 3) :=
              mul_le_mul_of_nonneg_left hzone
                (mul_nonneg (pow_nonneg hμ 4) (pow_nonneg hs 8))
            _ = p₁ ^ 3 * p₂ ^ 2 * p₃ ^ 3 := by rw [hprod]; ring
        have hxgm : X ≤
            p₁ ^ ((3 : ℝ) / 8) * p₂ ^ ((1 : ℝ) / 4) * p₃ ^ ((3 : ℝ) / 8) := by
          exact le_geom3_of_pow hp₁ hp₂ hp₃ (by norm_num)
            (by norm_num) (by norm_num) (by norm_num) hpow
        have hgm :
            p₁ ^ ((3 : ℝ) / 8) * p₂ ^ ((1 : ℝ) / 4) * p₃ ^ ((3 : ℝ) / 8) ≤
              W + V + K := by
          calc
            p₁ ^ ((3 : ℝ) / 8) * p₂ ^ ((1 : ℝ) / 4) * p₃ ^ ((3 : ℝ) / 8) ≤
                ((3 : ℝ) / 8) * p₁ + ((1 : ℝ) / 4) * p₂ + ((3 : ℝ) / 8) * p₃ :=
              Real.geom_mean_le_arith_mean3_weighted
                (by norm_num) (by norm_num) (by norm_num) hp₁ hp₂ hp₃ (by norm_num)
            _ = W + V + K := by dsimp [p₁, p₂, p₃]; ring
        exact hxgm.trans hgm
      · by_cases hr4 : r ≤ (90 : ℝ)
        · have hr4lo : (12 : ℝ) ≤ r := by linarith
          let p₁ : ℝ := (16/9 : ℝ) * W
          let p₂ : ℝ := (8 : ℝ) * V
          let p₃ : ℝ := (16/5 : ℝ) * K
          let C₄ : ℝ :=
            ((16/9 : ℝ) * (167/1000 : ℝ)) ^ 9 *
            ((8 : ℝ) * (1/20 : ℝ)) ^ 2 *
            ((16/5 : ℝ) * (687/100 : ℝ)) ^ 5
          have hp₁ : 0 ≤ p₁ := by dsimp [p₁]; positivity
          have hp₂ : 0 ≤ p₂ := by dsimp [p₂]; positivity
          have hp₃ : 0 ≤ p₃ := by dsimp [p₃]; positivity
          have hC₄ : (147/10 : ℝ) ≤ C₄ := by
            dsimp [C₄]
            norm_num
          have hzone : (r - 1) ^ 16 ≤ C₄ * r ^ 9 * phi r ^ 5 := by
            calc
              (r - 1) ^ 16 ≤ (147/10 : ℝ) * r ^ 9 * phi r ^ 5 := hz4 r hr4lo hr4
              _ = (147/10 : ℝ) * (r ^ 9 * phi r ^ 5) := by ring
              _ ≤ C₄ * (r ^ 9 * phi r ^ 5) :=
                mul_le_mul_of_nonneg_right hC₄
                  (mul_nonneg (pow_nonneg hr 9) (pow_nonneg hphi 5))
              _ = C₄ * r ^ 9 * phi r ^ 5 := by ring
          have hμpow : (μ ^ ((1 : ℝ) / 3)) ^ 9 = μ ^ 3 :=
            rpow_pow_eq_pow hμ 9 3 (by norm_num)
          have hspow : (s ^ ((4 : ℝ) / 3)) ^ 9 = s ^ 12 :=
            rpow_pow_eq_pow hs 9 12 (by norm_num)
          have hprod : p₁ ^ 9 * p₂ ^ 2 * p₃ ^ 5 =
              C₄ * μ ^ 8 * r ^ 9 * s ^ 16 * phi r ^ 5 := by
            dsimp [p₁, p₂, p₃, W, V, K, C₄]
            simp only [mul_pow, hμpow, hspow]
            ring
          have hXpow : X ^ 16 = μ ^ 8 * s ^ 16 * (r - 1) ^ 16 := by
            dsimp [X]
            simp only [mul_pow, sqrt_pow_sixteen hμ, abs_pow_sixteen]
            ring
          have hpow : X ^ 16 ≤ p₁ ^ 9 * p₂ ^ 2 * p₃ ^ 5 := by
            calc
              X ^ 16 = μ ^ 8 * s ^ 16 * (r - 1) ^ 16 := hXpow
              _ ≤ μ ^ 8 * s ^ 16 * (C₄ * r ^ 9 * phi r ^ 5) :=
                mul_le_mul_of_nonneg_left hzone
                  (mul_nonneg (pow_nonneg hμ 8) (pow_nonneg hs 16))
              _ = p₁ ^ 9 * p₂ ^ 2 * p₃ ^ 5 := by rw [hprod]; ring
          have hxgm : X ≤
              p₁ ^ ((9 : ℝ) / 16) * p₂ ^ ((1 : ℝ) / 8) * p₃ ^ ((5 : ℝ) / 16) := by
            exact le_geom3_of_pow hp₁ hp₂ hp₃ (by norm_num)
              (by norm_num) (by norm_num) (by norm_num) hpow
          have hgm :
              p₁ ^ ((9 : ℝ) / 16) * p₂ ^ ((1 : ℝ) / 8) * p₃ ^ ((5 : ℝ) / 16) ≤
                W + V + K := by
            calc
              p₁ ^ ((9 : ℝ) / 16) * p₂ ^ ((1 : ℝ) / 8) * p₃ ^ ((5 : ℝ) / 16) ≤
                  ((9 : ℝ) / 16) * p₁ + ((1 : ℝ) / 8) * p₂ + ((5 : ℝ) / 16) * p₃ :=
                Real.geom_mean_le_arith_mean3_weighted
                  (by norm_num) (by norm_num) (by norm_num) hp₁ hp₂ hp₃ (by norm_num)
              _ = W + V + K := by dsimp [p₁, p₂, p₃]; ring
          exact hxgm.trans hgm
        · have hr5lo : (90 : ℝ) ≤ r := by linarith
          let p₁ : ℝ := (4/3 : ℝ) * W
          let p₂ : ℝ := (4 : ℝ) * K
          let C₅ : ℝ :=
            ((4/3 : ℝ) * (167/1000 : ℝ)) ^ 3 *
            ((4 : ℝ) * (687/100 : ℝ))
          have hp₁ : 0 ≤ p₁ := by dsimp [p₁]; positivity
          have hp₂ : 0 ≤ p₂ := by dsimp [p₂]; positivity
          have hC₅ : (303/1000 : ℝ) ≤ C₅ := by
            dsimp [C₅]
            norm_num
          have hzone : (r - 1) ^ 4 ≤ C₅ * r ^ 3 * phi r := by
            calc
              (r - 1) ^ 4 ≤ (303/1000 : ℝ) * r ^ 3 * phi r := hz5 r hr5lo
              _ = (303/1000 : ℝ) * (r ^ 3 * phi r) := by ring
              _ ≤ C₅ * (r ^ 3 * phi r) :=
                mul_le_mul_of_nonneg_right hC₅
                  (mul_nonneg (pow_nonneg hr 3) hphi)
              _ = C₅ * r ^ 3 * phi r := by ring
          have hμpow : (μ ^ ((1 : ℝ) / 3)) ^ 3 = μ := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul hμ]
            norm_num
          have hspow : (s ^ ((4 : ℝ) / 3)) ^ 3 = s ^ 4 :=
            rpow_pow_eq_pow hs 3 4 (by norm_num)
          have hprod : p₁ ^ 3 * p₂ =
              C₅ * μ ^ 2 * r ^ 3 * s ^ 4 * phi r := by
            dsimp [p₁, p₂, W, K, C₅]
            simp only [mul_pow, hμpow, hspow]
            ring
          have hXpow : X ^ 4 = μ ^ 2 * s ^ 4 * (r - 1) ^ 4 := by
            dsimp [X]
            simp only [mul_pow, sqrt_pow_four hμ, abs_pow_four]
            ring
          have hpow : X ^ 4 ≤ p₁ ^ 3 * p₂ := by
            calc
              X ^ 4 = μ ^ 2 * s ^ 4 * (r - 1) ^ 4 := hXpow
              _ ≤ μ ^ 2 * s ^ 4 * (C₅ * r ^ 3 * phi r) :=
                mul_le_mul_of_nonneg_left hzone
                  (mul_nonneg (pow_nonneg hμ 2) (pow_nonneg hs 4))
              _ = p₁ ^ 3 * p₂ := by rw [hprod]; ring
          have hxgm : X ≤ p₁ ^ ((3 : ℝ) / 4) * p₂ ^ ((1 : ℝ) / 4) := by
            exact le_geom2_of_pow (n := 4) (a := 3) (b := 1) hp₁ hp₂ (by norm_num)
              (by norm_num) (by norm_num) (by simpa using hpow)
          have hgm : p₁ ^ ((3 : ℝ) / 4) * p₂ ^ ((1 : ℝ) / 4) ≤ W + K := by
            calc
              p₁ ^ ((3 : ℝ) / 4) * p₂ ^ ((1 : ℝ) / 4) ≤
                  ((3 : ℝ) / 4) * p₁ + ((1 : ℝ) / 4) * p₂ :=
                Real.geom_mean_le_arith_mean2_weighted
                  (by norm_num) (by norm_num) hp₁ hp₂ (by norm_num)
              _ = W + K := by dsimp [p₁, p₂]; ring
          exact hxgm.trans (by linarith)

end stoch_to_det
