import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0037
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0038
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0123

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3111

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (3/8) (1/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (3/8 : ℝ) with hx3111 | hx3111
  · rcases le_total tau.im (1/40 : ℝ) with hy3111 | hy3111
    · have hs31110 : InSquare (29/80) (1/80) (1/80) tau := by
        convert childLL hs hx3111 hy3111 using 1 <;> norm_num
      exact Batch0037.cell0303.sound htau (by
        simp only [Batch0037.cell0303, Batch0037.tau0303, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs31110 (by positivity) using 1 <;> norm_num)
    · have hs31112 : InSquare (29/80) (3/80) (1/80) tau := by
        convert childUL hs hx3111 hy3111 using 1 <;> norm_num
      exact Batch0038.cell0305.sound htau (by
        simp only [Batch0038.cell0305, Batch0038.tau0305, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs31112 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (1/40 : ℝ) with hy3111 | hy3111
    · have hs31111 : InSquare (31/80) (1/80) (1/80) tau := by
        convert childLR hs hx3111 hy3111 using 1 <;> norm_num
      exact Batch0038.cell0304.sound htau (by
        simp only [Batch0038.cell0304, Batch0038.tau0304, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs31111 (by positivity) using 1 <;> norm_num)
    · have hs31113 : InSquare (31/80) (3/80) (1/80) tau := by
        convert childUR hs hx3111 hy3111 using 1 <;> norm_num
      rcases le_total tau.re (31/80 : ℝ) with hx31113 | hx31113
      · rcases le_total tau.im (3/80 : ℝ) with hy31113 | hy31113
        · have hs311130 : InSquare (61/160) (1/32) (1/160) tau := by
            convert childLL hs31113 hx31113 hy31113 using 1 <;> norm_num
          exact Batch0123.cell0986.sound htau (by
            simp only [Batch0123.cell0986, Batch0123.tau0986, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs311130 (by positivity) using 1 <;> norm_num)
        · have hs311132 : InSquare (61/160) (7/160) (1/160) tau := by
            convert childUL hs31113 hx31113 hy31113 using 1 <;> norm_num
          exact Batch0123.cell0988.sound htau (by
            simp only [Batch0123.cell0988, Batch0123.tau0988, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs311132 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (3/80 : ℝ) with hy31113 | hy31113
        · have hs311131 : InSquare (63/160) (1/32) (1/160) tau := by
            convert childLR hs31113 hx31113 hy31113 using 1 <;> norm_num
          exact Batch0123.cell0987.sound htau (by
            simp only [Batch0123.cell0987, Batch0123.tau0987, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs311131 (by positivity) using 1 <;> norm_num)
        · have hs311133 : InSquare (63/160) (7/160) (1/160) tau := by
            convert childUR hs31113 hx31113 hy31113 using 1 <;> norm_num
          exact Batch0123.cell0989.sound htau (by
            simp only [Batch0123.cell0989, Batch0123.tau0989, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs311133 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3111
