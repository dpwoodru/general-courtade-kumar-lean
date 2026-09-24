import GeneralCK.PureGapDoubleCapLowTailDiagonalQuantitative

/-! Exact rational algebra behind the uniform near-zero contact-loss
estimate. The analytic and contact hypotheses will be discharged separately. -/

namespace GeneralCK

theorem doubleCapLowTail_uniform_secant_abstract
    {m d k bc bY p q δ den : ℝ}
    (hm : 0 < m) (hd : 0 < d) (hmd : m ≤ d)
    (hk : 49 / 50 ≤ k) (hbc : 207 / 100 ≤ bc)
    (hp : 99 / 50 ≤ p) (hq : 99 / 50 ≤ q)
    (hby : 0 < bY) (hden : 0 < den)
    (hδ : 0 ≤ δ)
    (hsep : δ * k ^ 2 * bc ≤ (5 / 2) * m * d * bY)
    (hDenLower : d ^ 2 * p * q * bY ≤ den) :
    4 * δ / den ≤ 4 / 3 := by
  have hk0 : 0 < k := by linarith
  have hbc0 : 0 < bc := by linarith
  have hp0 : 0 < p := by linarith
  have hq0 : 0 < q := by linarith
  have hKbc : 0 < k ^ 2 * bc := mul_pos (sq_pos_of_pos hk0) hbc0
  have hKsq : (49 / 50 : ℝ) ^ 2 ≤ k ^ 2 := by nlinarith [hk]
  have hKB : (49 / 50 : ℝ) ^ 2 * (207 / 100) ≤ k ^ 2 * bc :=
    (mul_le_mul_of_nonneg_left hbc (by norm_num :
      (0 : ℝ) ≤ (49 / 50) ^ 2)).trans
      (mul_le_mul_of_nonneg_right hKsq hbc0.le)
  have hPQ : (99 / 50 : ℝ) ^ 2 ≤ p * q := by
    have h1 := mul_le_mul_of_nonneg_left hq
      (by norm_num : (0 : ℝ) ≤ 99 / 50)
    have h2 := mul_le_mul_of_nonneg_right hp hq0.le
    nlinarith only [h1, h2]
  have hProd : (15 / 2 : ℝ) ≤ (k ^ 2 * bc) * (p * q) := by
    have hConst : (15 / 2 : ℝ) ≤
        ((49 / 50 : ℝ) ^ 2 * (207 / 100)) * ((99 / 50 : ℝ) ^ 2) := by
      norm_num
    have h1 := mul_le_mul_of_nonneg_left hPQ
      (by norm_num : (0 : ℝ) ≤ (49 / 50) ^ 2 * (207 / 100))
    have h2 := mul_le_mul_of_nonneg_right hKB
      (mul_nonneg hp0.le hq0.le)
    nlinarith only [hConst, h1, h2]
  have hTen : 10 * m ≤ (4 / 3) * (k ^ 2 * bc) * (p * q) * d := by
    have h1 := mul_le_mul_of_nonneg_left hmd
      (by norm_num : (0 : ℝ) ≤ 10)
    have h2 := mul_le_mul_of_nonneg_right hProd
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4 / 3) hd.le)
    nlinarith only [h1, h2]
  have hTenScaled : 10 * m * d * bY ≤
      (4 / 3) * (k ^ 2 * bc) * (d ^ 2 * p * q * bY) := by
    have h := mul_le_mul_of_nonneg_right hTen
      (mul_nonneg hd.le hby.le)
    nlinarith only [h]
  have hDenScaled : (4 / 3) * (k ^ 2 * bc) *
      (d ^ 2 * p * q * bY) ≤ (4 / 3) * (k ^ 2 * bc) * den :=
    mul_le_mul_of_nonneg_left hDenLower
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4 / 3) hKbc.le)
  have hSepScaled : 4 * δ * (k ^ 2 * bc) ≤ 10 * m * d * bY := by
    nlinarith [hsep]
  have hCross : 4 * δ * (k ^ 2 * bc) ≤
      (4 / 3) * (k ^ 2 * bc) * den :=
    (hSepScaled.trans hTenScaled).trans hDenScaled
  have hNumerator : 4 * δ ≤ (4 / 3) * den := by
    by_contra h
    have hStrict : (4 / 3) * den < 4 * δ := lt_of_not_ge h
    have hStrictMul := mul_lt_mul_of_pos_right hStrict hKbc
    nlinarith only [hCross, hStrictMul]
  exact (div_le_iff₀ hden).mpr hNumerator

#print axioms doubleCapLowTail_uniform_secant_abstract

end GeneralCK
