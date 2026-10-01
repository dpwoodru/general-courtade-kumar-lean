import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0039
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0040
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0125

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3122

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (9/40) (7/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (9/40 : ℝ) with hx3122 | hx3122
  · rcases le_total tau.im (7/40 : ℝ) with hy3122 | hy3122
    · have hs31220 : InSquare (17/80) (13/80) (1/80) tau := by
        convert childLL hs hx3122 hy3122 using 1 <;> norm_num
      exact Batch0039.cell0319.sound htau (by
        simp only [Batch0039.cell0319, Batch0039.tau0319, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs31220 (by positivity) using 1 <;> norm_num)
    · have hs31222 : InSquare (17/80) (3/16) (1/80) tau := by
        convert childUL hs hx3122 hy3122 using 1 <;> norm_num
      exact Batch0040.cell0321.sound htau (by
        simp only [Batch0040.cell0321, Batch0040.tau0321, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs31222 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (7/40 : ℝ) with hy3122 | hy3122
    · have hs31221 : InSquare (19/80) (13/80) (1/80) tau := by
        convert childLR hs hx3122 hy3122 using 1 <;> norm_num
      exact Batch0040.cell0320.sound htau (by
        simp only [Batch0040.cell0320, Batch0040.tau0320, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs31221 (by positivity) using 1 <;> norm_num)
    · have hs31223 : InSquare (19/80) (3/16) (1/80) tau := by
        convert childUR hs hx3122 hy3122 using 1 <;> norm_num
      rcases le_total tau.re (19/80 : ℝ) with hx31223 | hx31223
      · rcases le_total tau.im (3/16 : ℝ) with hy31223 | hy31223
        · have hs312230 : InSquare (37/160) (29/160) (1/160) tau := by
            convert childLL hs31223 hx31223 hy31223 using 1 <;> norm_num
          exact Batch0125.cell1002.sound htau (by
            simp only [Batch0125.cell1002, Batch0125.tau1002, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs312230 (by positivity) using 1 <;> norm_num)
        · have hs312232 : InSquare (37/160) (31/160) (1/160) tau := by
            convert childUL hs31223 hx31223 hy31223 using 1 <;> norm_num
          exact Batch0125.cell1004.sound htau (by
            simp only [Batch0125.cell1004, Batch0125.tau1004, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs312232 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (3/16 : ℝ) with hy31223 | hy31223
        · have hs312231 : InSquare (39/160) (29/160) (1/160) tau := by
            convert childLR hs31223 hx31223 hy31223 using 1 <;> norm_num
          exact Batch0125.cell1003.sound htau (by
            simp only [Batch0125.cell1003, Batch0125.tau1003, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs312231 (by positivity) using 1 <;> norm_num)
        · have hs312233 : InSquare (39/160) (31/160) (1/160) tau := by
            convert childUR hs31223 hx31223 hy31223 using 1 <;> norm_num
          exact Batch0125.cell1005.sound htau (by
            simp only [Batch0125.cell1005, Batch0125.tau1005, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs312233 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3122
