import GeneralCK.PureGapDoubleCapLowTailHighBiasAnchors
import GeneralCK.PureGapDoubleCapLowTailDiagonalBias

/-! A quantitative coincident-contact slope lower bound in the near-zero
double-cap tail. -/

namespace GeneralCK

open Certificates.Reflection Reflection

theorem doubleCapLowTail_diagonal_slope_ge_four_thirds {y : ℝ}
    (hy : 49 / 50 ≤ y) (hy1 : y < 1) :
    4 / 3 ≤ doubleCapSlopeBiasExpression y y := by
  have hy0 : 0 < y := by linarith
  have hd : 0 < 1 - y := by linarith
  have hD : 0 < 1 - y ^ 2 := by nlinarith
  have hA := doubleCapLowTail_A_ge_207 hy hy1
  have hB := doubleCapLowTail_B_ge_207 hy hy1
  have hApos : 0 < SmallMean.A y := by linarith
  have hBpos : 0 < biasB y := by linarith
  have hDen : 0 < (1 - y ^ 2) * SmallMean.A y * biasB y :=
    mul_pos (mul_pos hD hApos) hBpos
  have hE := doubleCapLowTail_E_le_five_fourths_gap_B hy hy1
  have hNum : 2 * y * biasE y ≤
      (5 / 2) * y * (1 - y) * biasB y := by
    have h := mul_le_mul_of_nonneg_left hE (by linarith : 0 ≤ 2 * y)
    nlinarith only [h]
  have hAProduct : (207 / 100) * (1 + y) ≤
      SmallMean.A y * (1 + y) :=
    mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1 + y)
  have hCoef : (5 / 2) * y ≤
      (2 / 3) * (1 + y) * SmallMean.A y := by
    nlinarith [hAProduct, hy1.le]
  have hScaled := mul_le_mul_of_nonneg_right hCoef
    (mul_nonneg hd.le hBpos.le)
  have hDenBound : (5 / 2) * y * (1 - y) * biasB y ≤
      (2 / 3) * ((1 - y ^ 2) * SmallMean.A y * biasB y) := by
    nlinarith only [hScaled]
  have hFraction : 2 * y * biasE y /
      ((1 - y ^ 2) * SmallMean.A y * biasB y) ≤ 2 / 3 := by
    apply (div_le_iff₀ hDen).mpr
    linarith only [hNum, hDenBound]
  rw [doubleCapSlopeBiasExpression_diagonal hy0 hy1]
  linarith only [hFraction]

#print axioms doubleCapLowTail_diagonal_slope_ge_four_thirds

end GeneralCK
