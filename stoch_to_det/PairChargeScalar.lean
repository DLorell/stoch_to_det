import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-! Exact rational certificates for continuous common-contact pair charging. -/
namespace stoch_to_det

noncomputable def pairSecantN (r : ℝ) : ℝ := 4 - 16*r + 8*r^2 - r^3
noncomputable def pairSecantD (r : ℝ) : ℝ := (4-r)*(2-4*r+r^2)
noncomputable def pairSecantDistance (r : ℝ) : ℝ := 6*r-2*r^2
noncomputable def pairEntropyCost (t : ℝ) : ℝ :=
  let v := (59 : ℝ)/200*t^6
  (31 : ℝ)/100*t^4 + v-v^2/2+v^3/3
noncomputable def pairChargePolynomial (t r : ℝ) : ℝ :=
  16*(t^3*pairSecantN r-pairEntropyCost t*pairSecantD r) +
  (79 : ℝ)/100*(pairSecantDistance r+(pairSecantDistance r)^2/4)*pairSecantD r -
  pairSecantD r

private theorem pair_charge_interval_1 {r : ℝ}
    (hlo : 0 ≤ r) (hhi : r ≤ (1 : ℝ) / 20) :
    0 ≤ pairChargePolynomial ((69 : ℝ) / 100) r := by
  let x : ℝ := (r-(0))/(((1 : ℝ) / 20)-(0))
  have hx0 : 0 ≤ x := by
    dsimp [x]
    exact div_nonneg (sub_nonneg.mpr hlo) (by norm_num)
  have hx1 : x ≤ 1 := by
    dsimp [x]
    apply (div_le_iff₀ (by norm_num)).2
    linarith
  have hid : (4000000000000000000000000000000000000000000000 : ℝ) * pairChargePolynomial ((69 : ℝ) / 100) r =
      75045005215679279081332280076384693074368000 * x ^ 0 * (1-x) ^ 7 +
      742270873422991034672676079026099573549709600 * x ^ 1 * (1-x) ^ 6 +
      2677313503521720545525781923252709848469215520 * x ^ 2 * (1-x) ^ 5 +
      4827994390234305480396662587728643703192484313 * x ^ 3 * (1-x) ^ 4 +
      4760963311631062391935722896236003541469094052 * x ^ 4 * (1-x) ^ 3 +
      2529868549388959089302849091075831841260615478 * x ^ 5 * (1-x) ^ 2 +
      630568102491541451223000741716583218315490052 * x ^ 6 * (1-x) ^ 1 +
      43756107344998063393650083451106183325358233 * x ^ 7 * (1-x) ^ 0 := by
    dsimp [x, pairChargePolynomial, pairSecantN, pairSecantD,
      pairSecantDistance, pairEntropyCost]
    ring
  have hsum : 0 ≤
      75045005215679279081332280076384693074368000 * x ^ 0 * (1-x) ^ 7 +
      742270873422991034672676079026099573549709600 * x ^ 1 * (1-x) ^ 6 +
      2677313503521720545525781923252709848469215520 * x ^ 2 * (1-x) ^ 5 +
      4827994390234305480396662587728643703192484313 * x ^ 3 * (1-x) ^ 4 +
      4760963311631062391935722896236003541469094052 * x ^ 4 * (1-x) ^ 3 +
      2529868549388959089302849091075831841260615478 * x ^ 5 * (1-x) ^ 2 +
      630568102491541451223000741716583218315490052 * x ^ 6 * (1-x) ^ 1 +
      43756107344998063393650083451106183325358233 * x ^ 7 * (1-x) ^ 0 := by
    positivity
  nlinarith only [hid, hsum]

private theorem pair_charge_interval_2 {r : ℝ}
    (hlo : (1 : ℝ) / 20 ≤ r) (hhi : r ≤ (1 : ℝ) / 10) :
    0 ≤ pairChargePolynomial ((33 : ℝ) / 50) r := by
  let x : ℝ := (r-((1 : ℝ) / 20))/(((1 : ℝ) / 10)-((1 : ℝ) / 20))
  have hx0 : 0 ≤ x := by
    dsimp [x]
    exact div_nonneg (sub_nonneg.mpr hlo) (by norm_num)
  have hx1 : x ≤ 1 := by
    dsimp [x]
    apply (div_le_iff₀ (by norm_num)).2
    linarith
  have hid : (15258789062500000000000000000000000000000 : ℝ) * pairChargePolynomial ((33 : ℝ) / 50) r =
      424424959309877830383223535762087737217 * x ^ 0 * (1-x) ^ 7 +
      5420459881188854085062245319311414141290 * x ^ 1 * (1-x) ^ 6 +
      22226273960825858270825912666051718118474 * x ^ 2 * (1-x) ^ 5 +
      44532480053343748037251719967412123952352 * x ^ 3 * (1-x) ^ 4 +
      49432675402116027271450929593686526647873 * x ^ 4 * (1-x) ^ 3 +
      30971652053918361533969516348436647776454 * x ^ 5 * (1-x) ^ 2 +
      10195615453685069487853686370737491513548 * x ^ 6 * (1-x) ^ 1 +
      1354397778068335329718551781077638147016 * x ^ 7 * (1-x) ^ 0 := by
    dsimp [x, pairChargePolynomial, pairSecantN, pairSecantD,
      pairSecantDistance, pairEntropyCost]
    ring
  have hsum : 0 ≤
      424424959309877830383223535762087737217 * x ^ 0 * (1-x) ^ 7 +
      5420459881188854085062245319311414141290 * x ^ 1 * (1-x) ^ 6 +
      22226273960825858270825912666051718118474 * x ^ 2 * (1-x) ^ 5 +
      44532480053343748037251719967412123952352 * x ^ 3 * (1-x) ^ 4 +
      49432675402116027271450929593686526647873 * x ^ 4 * (1-x) ^ 3 +
      30971652053918361533969516348436647776454 * x ^ 5 * (1-x) ^ 2 +
      10195615453685069487853686370737491513548 * x ^ 6 * (1-x) ^ 1 +
      1354397778068335329718551781077638147016 * x ^ 7 * (1-x) ^ 0 := by
    positivity
  nlinarith only [hid, hsum]

private theorem pair_charge_interval_3 {r : ℝ}
    (hlo : (1 : ℝ) / 10 ≤ r) (hhi : r ≤ (9 : ℝ) / 50) :
    0 ≤ pairChargePolynomial ((31 : ℝ) / 50) r := by
  let x : ℝ := (r-((1 : ℝ) / 10))/(((9 : ℝ) / 50)-((1 : ℝ) / 10))
  have hx0 : 0 ≤ x := by
    dsimp [x]
    exact div_nonneg (sub_nonneg.mpr hlo) (by norm_num)
  have hx1 : x ≤ 1 := by
    dsimp [x]
    apply (div_le_iff₀ (by norm_num)).2
    linarith
  have hid : (715255737304687500000000000000000000000000 : ℝ) * pairChargePolynomial ((31 : ℝ) / 50) r =
      140830815463693378779338391853825939677375 * x ^ 0 * (1-x) ^ 7 +
      1273577871433571614650334122455572975239325 * x ^ 1 * (1-x) ^ 6 +
      4456683264587611120289361763638824371962835 * x ^ 2 * (1-x) ^ 5 +
      8088887694522200205080293026033154795218121 * x ^ 3 * (1-x) ^ 4 +
      8334242029908759903157393201971927077322509 * x ^ 4 * (1-x) ^ 3 +
      4889891621937551416495133478201846284922151 * x ^ 5 * (1-x) ^ 2 +
      1504845099717644378839086628183064932629409 * x ^ 6 * (1-x) ^ 1 +
      184244009934385544839419358957068266212531 * x ^ 7 * (1-x) ^ 0 := by
    dsimp [x, pairChargePolynomial, pairSecantN, pairSecantD,
      pairSecantDistance, pairEntropyCost]
    ring
  have hsum : 0 ≤
      140830815463693378779338391853825939677375 * x ^ 0 * (1-x) ^ 7 +
      1273577871433571614650334122455572975239325 * x ^ 1 * (1-x) ^ 6 +
      4456683264587611120289361763638824371962835 * x ^ 2 * (1-x) ^ 5 +
      8088887694522200205080293026033154795218121 * x ^ 3 * (1-x) ^ 4 +
      8334242029908759903157393201971927077322509 * x ^ 4 * (1-x) ^ 3 +
      4889891621937551416495133478201846284922151 * x ^ 5 * (1-x) ^ 2 +
      1504845099717644378839086628183064932629409 * x ^ 6 * (1-x) ^ 1 +
      184244009934385544839419358957068266212531 * x ^ 7 * (1-x) ^ 0 := by
    positivity
  nlinarith only [hid, hsum]

theorem pair_secant_denominator_pos {r : ℝ}
    (_hlo : 0 ≤ r) (hhi : r ≤ (9 : ℝ)/50) : 0 < pairSecantD r := by
  unfold pairSecantD
  have h1 : 0 < 4-r := by linarith
  have h2 : 0 < 2-4*r+r^2 := by nlinarith [sq_nonneg r]
  exact mul_pos h1 h2

private theorem pair_charge_from_polynomial {r K t : ℝ}
    (hD : 0 < pairSecantD r)
    (hK : t^3*(pairSecantN r/pairSecantD r)-pairEntropyCost t ≤ K)
    (hP : 0 ≤ pairChargePolynomial t r) :
    1 ≤ 16*K + (79 : ℝ)/100*
      (pairSecantDistance r+(pairSecantDistance r)^2/4) := by
  have heq : t^3*(pairSecantN r/pairSecantD r)-pairEntropyCost t =
      (t^3*pairSecantN r-pairEntropyCost t*pairSecantD r)/pairSecantD r := by
    field_simp
  rw [heq] at hK
  have hmul := (div_le_iff₀ hD).mp hK
  unfold pairChargePolynomial at hP
  have hh : 1*pairSecantD r ≤
      (16*K + (79 : ℝ)/100*
        (pairSecantDistance r+(pairSecantDistance r)^2/4))*pairSecantD r := by
    nlinarith only [hmul, hP]
  exact (mul_le_mul_iff_left₀ hD).mp hh

/-- Three entropy-floor evaluations suffice for the uniform pair charge.
The contact/secant and information inequalities are supplied separately. -/
theorem pair_charge_scalar {r K : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r ≤ (9 : ℝ)/50)
    (h69 : ((69 : ℝ)/100)^3*(pairSecantN r/pairSecantD r) -
      pairEntropyCost ((69 : ℝ)/100) ≤ K)
    (h66 : ((33 : ℝ)/50)^3*(pairSecantN r/pairSecantD r) -
      pairEntropyCost ((33 : ℝ)/50) ≤ K)
    (h62 : ((31 : ℝ)/50)^3*(pairSecantN r/pairSecantD r) -
      pairEntropyCost ((31 : ℝ)/50) ≤ K) :
    1 ≤ 16*K + (79 : ℝ)/100*
      (pairSecantDistance r+(pairSecantDistance r)^2/4) := by
  have hD := pair_secant_denominator_pos hr0 hr1
  by_cases h1 : r ≤ (1 : ℝ)/20
  · exact pair_charge_from_polynomial hD h69 (pair_charge_interval_1 hr0 h1)
  · have hh1 : (1 : ℝ)/20 ≤ r := (lt_of_not_ge h1).le
    by_cases h2 : r ≤ (1 : ℝ)/10
    · exact pair_charge_from_polynomial hD h66 (pair_charge_interval_2 hh1 h2)
    · have hh2 : (1 : ℝ)/10 ≤ r := (lt_of_not_ge h2).le
      exact pair_charge_from_polynomial hD h62 (pair_charge_interval_3 hh2 hr1)

/-- Nine alternating Taylor terms bound the powered-race normalization. -/
noncomputable def poweredRaceJ4Upper : ℝ :=
  1/3 - 1/14 + 1/33 - 1/60 + 1/95 - 1/138 + 1/189 - 1/248 + 1/315

theorem powered_race_final_constant_lt :
    11 + 3*poweredRaceJ4Upper*((1 : ℝ)+16/2+2*(79/100)) < (9999 : ℝ)/500 := by
  norm_num [poweredRaceJ4Upper]

end stoch_to_det
