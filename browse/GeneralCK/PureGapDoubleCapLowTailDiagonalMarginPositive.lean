import GeneralCK.PureGapDoubleCapLowTailDiagonalMarginDerivative
import GeneralCK.Certificates.MixedConstants

/-! A rationally bounded positive diagonal margin for the low double-cap tail. -/

namespace GeneralCK

open Certificates.Reflection Reflection

private theorem biasE_upper_near_one {y : ℝ} (hy : 0 ≤ y) (hy1 : y < 1) :
    biasE y ≤ (1 - y) * SmallMean.A y + (1 - y) / (1 + y) := by
  have hp : 0 < 1 + y := by linarith
  have hm : 0 < 1 - y := by linarith
  have hlog := Real.log_le_sub_one_of_pos (div_pos (by norm_num : (0 : ℝ) < 2) hp)
  have hlog' : Real.log 2 - Real.log (1 + y) ≤ (1 - y) / (1 + y) := by
    rw [Real.log_div (by norm_num : (2 : ℝ) ≠ 0) hp.ne'] at hlog
    have hfrac : 2 / (1 + y) - 1 = (1 - y) / (1 + y) := by
      field_simp [hp.ne']
      ring
    simpa only [hfrac] using hlog
  have heq : biasE y = (1 - y) * SmallMean.A y +
      (Real.log 2 - Real.log (1 + y)) := by
    unfold biasE SmallMean.A
    rw [Real.log_div hp.ne' hm.ne']
    ring
  rw [heq]
  linarith only [hlog']

theorem doubleCapDiagonalMargin_pos_three_quarters {y : ℝ}
    (hy : 3 / 4 ≤ y) (hy1 : y < 1) :
    0 < doubleCapDiagonalMargin y := by
  have hy0 : 0 ≤ y := by linarith
  have hD : 0 < 1 - y ^ 2 := by nlinarith
  have hlogD := Real.log_le_sub_one_of_pos hD
  have hL : (2 / 3 : ℝ) ≤ Real.log 2 := by
    linarith [Certificates.Mixed.log_two_gt_69]
  have hy2 : (9 / 16 : ℝ) ≤ y ^ 2 := by
    nlinarith [hy, sq_nonneg (y - 3 / 4)]
  have hB : (91 / 96 : ℝ) ≤ biasB y := by
    simp only [biasB]
    have hlogD' : Real.log (1 - y * y) ≤ -(y * y) := by
      have htemp := hlogD
      simp only [pow_two] at htemp
      linarith only [htemp]
    have hy2' : (9 / 16 : ℝ) ≤ y * y := by simpa only [pow_two] using hy2
    nlinarith only [hlogD', hL, hy2']
  have hA : (57 / 64 : ℝ) ≤ SmallMean.A y := by
    have hseries := SmallMean.A_ge_linear_cubic hy0 hy1
    have hy3 : (27 / 64 : ℝ) ≤ y ^ 3 := by
      have hpoly : 0 ≤ y ^ 2 + (3 / 4 : ℝ) * y + 9 / 16 := by
        positivity
      nlinarith [mul_nonneg (sub_nonneg.mpr hy) hpoly]
    linarith only [hseries, hy, hy3]
  have hcoef : (43 / 48 : ℝ) ≤ (1 + y) * biasB y - y := by
    have hprod := mul_le_mul_of_nonneg_left hB (by linarith : 0 ≤ 1 + y)
    nlinarith only [hprod, hy1.le]
  have hcoefpos : 0 ≤ (1 + y) * biasB y - y := by linarith
  have hcore : (1 / 2 : ℝ) < SmallMean.A y *
      ((1 + y) * biasB y - y) := by
    have hprodA := mul_le_mul_of_nonneg_right hA hcoefpos
    have hprodC := mul_le_mul_of_nonneg_left hcoef
      (by norm_num : (0 : ℝ) ≤ 57 / 64)
    nlinarith only [hprodA, hprodC]
  have hfrac : y / (1 + y) ≤ (1 / 2 : ℝ) := by
    apply (div_le_iff₀ (by linarith : 0 < 1 + y)).2
    linarith only [hy1.le]
  have hE := biasE_upper_near_one hy0 hy1
  have hmargin : 0 < (1 - y) *
      (SmallMean.A y * ((1 + y) * biasB y - y) - y / (1 + y)) :=
    mul_pos (by linarith) (by linarith only [hcore, hfrac])
  have hmul := mul_le_mul_of_nonneg_left hE hy0
  have hident : (1 - y ^ 2) * SmallMean.A y * biasB y -
      y * ((1 - y) * SmallMean.A y + (1 - y) / (1 + y)) =
      (1 - y) *
        (SmallMean.A y * ((1 + y) * biasB y - y) - y / (1 + y)) := by
    ring
  unfold doubleCapDiagonalMargin
  nlinarith only [hmul, hmargin, hident]

#print axioms doubleCapDiagonalMargin_pos_three_quarters

end GeneralCK
