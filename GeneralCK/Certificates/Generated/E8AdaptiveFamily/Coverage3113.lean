import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0038
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0123
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0124
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0125

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3113

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (3/8) (3/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (3/8 : ℝ) with hx3113 | hx3113
  · rcases le_total tau.im (3/40 : ℝ) with hy3113 | hy3113
    · have hs31130 : InSquare (29/80) (1/16) (1/80) tau := by
        convert childLL hs hx3113 hy3113 using 1 <;> norm_num
      exact Batch0038.cell0310.sound htau (by
        simp only [Batch0038.cell0310, Batch0038.tau0310, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs31130 (by positivity) using 1 <;> norm_num)
    · have hs31132 : InSquare (29/80) (7/80) (1/80) tau := by
        convert childUL hs hx3113 hy3113 using 1 <;> norm_num
      rcases le_total tau.re (29/80 : ℝ) with hx31132 | hx31132
      · rcases le_total tau.im (7/80 : ℝ) with hy31132 | hy31132
        · have hs311320 : InSquare (57/160) (13/160) (1/160) tau := by
            convert childLL hs31132 hx31132 hy31132 using 1 <;> norm_num
          exact Batch0124.cell0994.sound htau (by
            simp only [Batch0124.cell0994, Batch0124.tau0994, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs311320 (by positivity) using 1 <;> norm_num)
        · have hs311322 : InSquare (57/160) (3/32) (1/160) tau := by
            convert childUL hs31132 hx31132 hy31132 using 1 <;> norm_num
          exact Batch0124.cell0996.sound htau (by
            simp only [Batch0124.cell0996, Batch0124.tau0996, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs311322 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (7/80 : ℝ) with hy31132 | hy31132
        · have hs311321 : InSquare (59/160) (13/160) (1/160) tau := by
            convert childLR hs31132 hx31132 hy31132 using 1 <;> norm_num
          exact Batch0124.cell0995.sound htau (by
            simp only [Batch0124.cell0995, Batch0124.tau0995, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs311321 (by positivity) using 1 <;> norm_num)
        · have hs311323 : InSquare (59/160) (3/32) (1/160) tau := by
            convert childUR hs31132 hx31132 hy31132 using 1 <;> norm_num
          exact Batch0124.cell0997.sound htau (by
            simp only [Batch0124.cell0997, Batch0124.tau0997, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs311323 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (3/40 : ℝ) with hy3113 | hy3113
    · have hs31131 : InSquare (31/80) (1/16) (1/80) tau := by
        convert childLR hs hx3113 hy3113 using 1 <;> norm_num
      rcases le_total tau.re (31/80 : ℝ) with hx31131 | hx31131
      · rcases le_total tau.im (1/16 : ℝ) with hy31131 | hy31131
        · have hs311310 : InSquare (61/160) (9/160) (1/160) tau := by
            convert childLL hs31131 hx31131 hy31131 using 1 <;> norm_num
          exact Batch0123.cell0990.sound htau (by
            simp only [Batch0123.cell0990, Batch0123.tau0990, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs311310 (by positivity) using 1 <;> norm_num)
        · have hs311312 : InSquare (61/160) (11/160) (1/160) tau := by
            convert childUL hs31131 hx31131 hy31131 using 1 <;> norm_num
          exact Batch0124.cell0992.sound htau (by
            simp only [Batch0124.cell0992, Batch0124.tau0992, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs311312 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (1/16 : ℝ) with hy31131 | hy31131
        · have hs311311 : InSquare (63/160) (9/160) (1/160) tau := by
            convert childLR hs31131 hx31131 hy31131 using 1 <;> norm_num
          exact Batch0123.cell0991.sound htau (by
            simp only [Batch0123.cell0991, Batch0123.tau0991, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs311311 (by positivity) using 1 <;> norm_num)
        · have hs311313 : InSquare (63/160) (11/160) (1/160) tau := by
            convert childUR hs31131 hx31131 hy31131 using 1 <;> norm_num
          exact Batch0124.cell0993.sound htau (by
            simp only [Batch0124.cell0993, Batch0124.tau0993, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs311313 (by positivity) using 1 <;> norm_num)
    · have hs31133 : InSquare (31/80) (7/80) (1/80) tau := by
        convert childUR hs hx3113 hy3113 using 1 <;> norm_num
      rcases le_total tau.re (31/80 : ℝ) with hx31133 | hx31133
      · rcases le_total tau.im (7/80 : ℝ) with hy31133 | hy31133
        · have hs311330 : InSquare (61/160) (13/160) (1/160) tau := by
            convert childLL hs31133 hx31133 hy31133 using 1 <;> norm_num
          exact Batch0124.cell0998.sound htau (by
            simp only [Batch0124.cell0998, Batch0124.tau0998, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs311330 (by positivity) using 1 <;> norm_num)
        · have hs311332 : InSquare (61/160) (3/32) (1/160) tau := by
            convert childUL hs31133 hx31133 hy31133 using 1 <;> norm_num
          exact Batch0125.cell1000.sound htau (by
            simp only [Batch0125.cell1000, Batch0125.tau1000, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs311332 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (7/80 : ℝ) with hy31133 | hy31133
        · have hs311331 : InSquare (63/160) (13/160) (1/160) tau := by
            convert childLR hs31133 hx31133 hy31133 using 1 <;> norm_num
          exact Batch0124.cell0999.sound htau (by
            simp only [Batch0124.cell0999, Batch0124.tau0999, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs311331 (by positivity) using 1 <;> norm_num)
        · have hs311333 : InSquare (63/160) (3/32) (1/160) tau := by
            convert childUR hs31133 hx31133 hy31133 using 1 <;> norm_num
          exact Batch0125.cell1001.sound htau (by
            simp only [Batch0125.cell1001, Batch0125.tau1001, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs311333 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3113
