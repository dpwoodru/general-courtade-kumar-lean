import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0033
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0117
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0118

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2312

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-3/40) (11/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (-3/40 : ℝ) with hx2312 | hx2312
  · rcases le_total tau.im (11/40 : ℝ) with hy2312 | hy2312
    · have hs23120 : InSquare (-7/80) (21/80) (1/80) tau := by
        convert childLL hs hx2312 hy2312 using 1 <;> norm_num
      exact Batch0033.cell0265.sound htau (by
        simp only [Batch0033.cell0265, Batch0033.tau0265, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs23120 (by positivity) using 1 <;> norm_num)
    · have hs23122 : InSquare (-7/80) (23/80) (1/80) tau := by
        convert childUL hs hx2312 hy2312 using 1 <;> norm_num
      rcases le_total tau.re (-7/80 : ℝ) with hx23122 | hx23122
      · rcases le_total tau.im (23/80 : ℝ) with hy23122 | hy23122
        · have hs231220 : InSquare (-3/32) (9/32) (1/160) tau := by
            convert childLL hs23122 hx23122 hy23122 using 1 <;> norm_num
          exact Batch0117.cell0938.sound htau (by
            simp only [Batch0117.cell0938, Batch0117.tau0938, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs231220 (by positivity) using 1 <;> norm_num)
        · have hs231222 : InSquare (-3/32) (47/160) (1/160) tau := by
            convert childUL hs23122 hx23122 hy23122 using 1 <;> norm_num
          exact Batch0117.cell0940.sound htau (by
            simp only [Batch0117.cell0940, Batch0117.tau0940, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs231222 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (23/80 : ℝ) with hy23122 | hy23122
        · have hs231221 : InSquare (-13/160) (9/32) (1/160) tau := by
            convert childLR hs23122 hx23122 hy23122 using 1 <;> norm_num
          exact Batch0117.cell0939.sound htau (by
            simp only [Batch0117.cell0939, Batch0117.tau0939, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs231221 (by positivity) using 1 <;> norm_num)
        · have hs231223 : InSquare (-13/160) (47/160) (1/160) tau := by
            convert childUR hs23122 hx23122 hy23122 using 1 <;> norm_num
          exact Batch0117.cell0941.sound htau (by
            simp only [Batch0117.cell0941, Batch0117.tau0941, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs231223 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (11/40 : ℝ) with hy2312 | hy2312
    · have hs23121 : InSquare (-1/16) (21/80) (1/80) tau := by
        convert childLR hs hx2312 hy2312 using 1 <;> norm_num
      exact Batch0033.cell0266.sound htau (by
        simp only [Batch0033.cell0266, Batch0033.tau0266, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs23121 (by positivity) using 1 <;> norm_num)
    · have hs23123 : InSquare (-1/16) (23/80) (1/80) tau := by
        convert childUR hs hx2312 hy2312 using 1 <;> norm_num
      rcases le_total tau.re (-1/16 : ℝ) with hx23123 | hx23123
      · rcases le_total tau.im (23/80 : ℝ) with hy23123 | hy23123
        · have hs231230 : InSquare (-11/160) (9/32) (1/160) tau := by
            convert childLL hs23123 hx23123 hy23123 using 1 <;> norm_num
          exact Batch0117.cell0942.sound htau (by
            simp only [Batch0117.cell0942, Batch0117.tau0942, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs231230 (by positivity) using 1 <;> norm_num)
        · have hs231232 : InSquare (-11/160) (47/160) (1/160) tau := by
            convert childUL hs23123 hx23123 hy23123 using 1 <;> norm_num
          exact Batch0118.cell0944.sound htau (by
            simp only [Batch0118.cell0944, Batch0118.tau0944, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs231232 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (23/80 : ℝ) with hy23123 | hy23123
        · have hs231231 : InSquare (-9/160) (9/32) (1/160) tau := by
            convert childLR hs23123 hx23123 hy23123 using 1 <;> norm_num
          exact Batch0117.cell0943.sound htau (by
            simp only [Batch0117.cell0943, Batch0117.tau0943, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs231231 (by positivity) using 1 <;> norm_num)
        · have hs231233 : InSquare (-9/160) (47/160) (1/160) tau := by
            convert childUR hs23123 hx23123 hy23123 using 1 <;> norm_num
          exact Batch0118.cell0945.sound htau (by
            simp only [Batch0118.cell0945, Batch0118.tau0945, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs231233 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2312
