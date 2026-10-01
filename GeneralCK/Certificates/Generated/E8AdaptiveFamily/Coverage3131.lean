import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0128
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0129
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0130

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3131

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

private theorem outside_313111 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (63/160) (17/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (31/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-31/80)]
  have himSq : (1/10 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-1/10)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_313113 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (63/160) (19/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (31/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-31/80)]
  have himSq : (9/80 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-9/80)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_313131 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (63/160) (21/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (31/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-31/80)]
  have himSq : (1/8 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-1/8)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_313133 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (63/160) (23/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (31/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-31/80)]
  have himSq : (11/80 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-11/80)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (3/8) (1/8) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (3/8 : ℝ) with hx3131 | hx3131
  · rcases le_total tau.im (1/8 : ℝ) with hy3131 | hy3131
    · have hs31310 : InSquare (29/80) (9/80) (1/80) tau := by
        convert childLL hs hx3131 hy3131 using 1 <;> norm_num
      rcases le_total tau.re (29/80 : ℝ) with hx31310 | hx31310
      · rcases le_total tau.im (9/80 : ℝ) with hy31310 | hy31310
        · have hs313100 : InSquare (57/160) (17/160) (1/160) tau := by
            convert childLL hs31310 hx31310 hy31310 using 1 <;> norm_num
          exact Batch0128.cell1030.sound htau (by
            simp only [Batch0128.cell1030, Batch0128.tau1030, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs313100 (by positivity) using 1 <;> norm_num)
        · have hs313102 : InSquare (57/160) (19/160) (1/160) tau := by
            convert childUL hs31310 hx31310 hy31310 using 1 <;> norm_num
          exact Batch0129.cell1032.sound htau (by
            simp only [Batch0129.cell1032, Batch0129.tau1032, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs313102 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (9/80 : ℝ) with hy31310 | hy31310
        · have hs313101 : InSquare (59/160) (17/160) (1/160) tau := by
            convert childLR hs31310 hx31310 hy31310 using 1 <;> norm_num
          exact Batch0128.cell1031.sound htau (by
            simp only [Batch0128.cell1031, Batch0128.tau1031, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs313101 (by positivity) using 1 <;> norm_num)
        · have hs313103 : InSquare (59/160) (19/160) (1/160) tau := by
            convert childUR hs31310 hx31310 hy31310 using 1 <;> norm_num
          exact Batch0129.cell1033.sound htau (by
            simp only [Batch0129.cell1033, Batch0129.tau1033, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs313103 (by positivity) using 1 <;> norm_num)
    · have hs31312 : InSquare (29/80) (11/80) (1/80) tau := by
        convert childUL hs hx3131 hy3131 using 1 <;> norm_num
      rcases le_total tau.re (29/80 : ℝ) with hx31312 | hx31312
      · rcases le_total tau.im (11/80 : ℝ) with hy31312 | hy31312
        · have hs313120 : InSquare (57/160) (21/160) (1/160) tau := by
            convert childLL hs31312 hx31312 hy31312 using 1 <;> norm_num
          exact Batch0129.cell1036.sound htau (by
            simp only [Batch0129.cell1036, Batch0129.tau1036, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs313120 (by positivity) using 1 <;> norm_num)
        · have hs313122 : InSquare (57/160) (23/160) (1/160) tau := by
            convert childUL hs31312 hx31312 hy31312 using 1 <;> norm_num
          exact Batch0129.cell1038.sound htau (by
            simp only [Batch0129.cell1038, Batch0129.tau1038, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs313122 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (11/80 : ℝ) with hy31312 | hy31312
        · have hs313121 : InSquare (59/160) (21/160) (1/160) tau := by
            convert childLR hs31312 hx31312 hy31312 using 1 <;> norm_num
          exact Batch0129.cell1037.sound htau (by
            simp only [Batch0129.cell1037, Batch0129.tau1037, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs313121 (by positivity) using 1 <;> norm_num)
        · have hs313123 : InSquare (59/160) (23/160) (1/160) tau := by
            convert childUR hs31312 hx31312 hy31312 using 1 <;> norm_num
          exact Batch0129.cell1039.sound htau (by
            simp only [Batch0129.cell1039, Batch0129.tau1039, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs313123 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (1/8 : ℝ) with hy3131 | hy3131
    · have hs31311 : InSquare (31/80) (9/80) (1/80) tau := by
        convert childLR hs hx3131 hy3131 using 1 <;> norm_num
      rcases le_total tau.re (31/80 : ℝ) with hx31311 | hx31311
      · rcases le_total tau.im (9/80 : ℝ) with hy31311 | hy31311
        · have hs313110 : InSquare (61/160) (17/160) (1/160) tau := by
            convert childLL hs31311 hx31311 hy31311 using 1 <;> norm_num
          exact Batch0129.cell1034.sound htau (by
            simp only [Batch0129.cell1034, Batch0129.tau1034, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs313110 (by positivity) using 1 <;> norm_num)
        · have hs313112 : InSquare (61/160) (19/160) (1/160) tau := by
            convert childUL hs31311 hx31311 hy31311 using 1 <;> norm_num
          exact Batch0129.cell1035.sound htau (by
            simp only [Batch0129.cell1035, Batch0129.tau1035, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs313112 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (9/80 : ℝ) with hy31311 | hy31311
        · have hs313111 : InSquare (63/160) (17/160) (1/160) tau := by
            convert childLR hs31311 hx31311 hy31311 using 1 <;> norm_num
          exact (outside_313111 htau hs313111).elim
        · have hs313113 : InSquare (63/160) (19/160) (1/160) tau := by
            convert childUR hs31311 hx31311 hy31311 using 1 <;> norm_num
          exact (outside_313113 htau hs313113).elim
    · have hs31313 : InSquare (31/80) (11/80) (1/80) tau := by
        convert childUR hs hx3131 hy3131 using 1 <;> norm_num
      rcases le_total tau.re (31/80 : ℝ) with hx31313 | hx31313
      · rcases le_total tau.im (11/80 : ℝ) with hy31313 | hy31313
        · have hs313130 : InSquare (61/160) (21/160) (1/160) tau := by
            convert childLL hs31313 hx31313 hy31313 using 1 <;> norm_num
          exact Batch0130.cell1040.sound htau (by
            simp only [Batch0130.cell1040, Batch0130.tau1040, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs313130 (by positivity) using 1 <;> norm_num)
        · have hs313132 : InSquare (61/160) (23/160) (1/160) tau := by
            convert childUL hs31313 hx31313 hy31313 using 1 <;> norm_num
          exact Batch0130.cell1041.sound htau (by
            simp only [Batch0130.cell1041, Batch0130.tau1041, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs313132 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (11/80 : ℝ) with hy31313 | hy31313
        · have hs313131 : InSquare (63/160) (21/160) (1/160) tau := by
            convert childLR hs31313 hx31313 hy31313 using 1 <;> norm_num
          exact (outside_313131 htau hs313131).elim
        · have hs313133 : InSquare (63/160) (23/160) (1/160) tau := by
            convert childUR hs31313 hx31313 hy31313 using 1 <;> norm_num
          exact (outside_313133 htau hs313133).elim

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3131
