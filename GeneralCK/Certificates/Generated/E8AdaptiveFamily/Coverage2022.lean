import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0101
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0102
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0235

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2022

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

private theorem outside_20220 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-31/80) (13/80) (1/80) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (3/8 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+3/8)]
  have himSq : (3/20 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-3/20)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_20222 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-31/80) (3/16) (1/80) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (3/8 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+3/8)]
  have himSq : (7/40 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-7/40)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_202230 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-59/160) (29/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (29/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+29/80)]
  have himSq : (7/40 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-7/40)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_202232 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-59/160) (31/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (29/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+29/80)]
  have himSq : (3/16 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-3/16)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_2022330 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-23/64) (61/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (57/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+57/160)]
  have himSq : (3/16 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-3/16)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_2022332 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-23/64) (63/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (57/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+57/160)]
  have himSq : (31/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-31/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_2022333 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-113/320) (63/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (7/20 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+7/20)]
  have himSq : (31/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-31/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-3/8) (7/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (-3/8 : ℝ) with hx2022 | hx2022
  · rcases le_total tau.im (7/40 : ℝ) with hy2022 | hy2022
    · have hs20220 : InSquare (-31/80) (13/80) (1/80) tau := by
        convert childLL hs hx2022 hy2022 using 1 <;> norm_num
      exact (outside_20220 htau hs20220).elim
    · have hs20222 : InSquare (-31/80) (3/16) (1/80) tau := by
        convert childUL hs hx2022 hy2022 using 1 <;> norm_num
      exact (outside_20222 htau hs20222).elim
  · rcases le_total tau.im (7/40 : ℝ) with hy2022 | hy2022
    · have hs20221 : InSquare (-29/80) (13/80) (1/80) tau := by
        convert childLR hs hx2022 hy2022 using 1 <;> norm_num
      rcases le_total tau.re (-29/80 : ℝ) with hx20221 | hx20221
      · rcases le_total tau.im (13/80 : ℝ) with hy20221 | hy20221
        · have hs202210 : InSquare (-59/160) (5/32) (1/160) tau := by
            convert childLL hs20221 hx20221 hy20221 using 1 <;> norm_num
          exact Batch0101.cell0812.sound htau (by
            simp only [Batch0101.cell0812, Batch0101.tau0812, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs202210 (by positivity) using 1 <;> norm_num)
        · have hs202212 : InSquare (-59/160) (27/160) (1/160) tau := by
            convert childUL hs20221 hx20221 hy20221 using 1 <;> norm_num
          exact Batch0101.cell0814.sound htau (by
            simp only [Batch0101.cell0814, Batch0101.tau0814, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs202212 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (13/80 : ℝ) with hy20221 | hy20221
        · have hs202211 : InSquare (-57/160) (5/32) (1/160) tau := by
            convert childLR hs20221 hx20221 hy20221 using 1 <;> norm_num
          exact Batch0101.cell0813.sound htau (by
            simp only [Batch0101.cell0813, Batch0101.tau0813, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs202211 (by positivity) using 1 <;> norm_num)
        · have hs202213 : InSquare (-57/160) (27/160) (1/160) tau := by
            convert childUR hs20221 hx20221 hy20221 using 1 <;> norm_num
          exact Batch0101.cell0815.sound htau (by
            simp only [Batch0101.cell0815, Batch0101.tau0815, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs202213 (by positivity) using 1 <;> norm_num)
    · have hs20223 : InSquare (-29/80) (3/16) (1/80) tau := by
        convert childUR hs hx2022 hy2022 using 1 <;> norm_num
      rcases le_total tau.re (-29/80 : ℝ) with hx20223 | hx20223
      · rcases le_total tau.im (3/16 : ℝ) with hy20223 | hy20223
        · have hs202230 : InSquare (-59/160) (29/160) (1/160) tau := by
            convert childLL hs20223 hx20223 hy20223 using 1 <;> norm_num
          exact (outside_202230 htau hs202230).elim
        · have hs202232 : InSquare (-59/160) (31/160) (1/160) tau := by
            convert childUL hs20223 hx20223 hy20223 using 1 <;> norm_num
          exact (outside_202232 htau hs202232).elim
      · rcases le_total tau.im (3/16 : ℝ) with hy20223 | hy20223
        · have hs202231 : InSquare (-57/160) (29/160) (1/160) tau := by
            convert childLR hs20223 hx20223 hy20223 using 1 <;> norm_num
          exact Batch0102.cell0816.sound htau (by
            simp only [Batch0102.cell0816, Batch0102.tau0816, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs202231 (by positivity) using 1 <;> norm_num)
        · have hs202233 : InSquare (-57/160) (31/160) (1/160) tau := by
            convert childUR hs20223 hx20223 hy20223 using 1 <;> norm_num
          rcases le_total tau.re (-57/160 : ℝ) with hx202233 | hx202233
          · rcases le_total tau.im (31/160 : ℝ) with hy202233 | hy202233
            · have hs2022330 : InSquare (-23/64) (61/320) (1/320) tau := by
                convert childLL hs202233 hx202233 hy202233 using 1 <;> norm_num
              exact (outside_2022330 htau hs2022330).elim
            · have hs2022332 : InSquare (-23/64) (63/320) (1/320) tau := by
                convert childUL hs202233 hx202233 hy202233 using 1 <;> norm_num
              exact (outside_2022332 htau hs2022332).elim
          · rcases le_total tau.im (31/160 : ℝ) with hy202233 | hy202233
            · have hs2022331 : InSquare (-113/320) (61/320) (1/320) tau := by
                convert childLR hs202233 hx202233 hy202233 using 1 <;> norm_num
              exact Batch0235.cell1882.sound htau (by
                simp only [Batch0235.cell1882, Batch0235.tau1882, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2022331 (by positivity) using 1 <;> norm_num)
            · have hs2022333 : InSquare (-113/320) (63/320) (1/320) tau := by
                convert childUR hs202233 hx202233 hy202233 using 1 <;> norm_num
              exact (outside_2022333 htau hs2022333).elim

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2022
