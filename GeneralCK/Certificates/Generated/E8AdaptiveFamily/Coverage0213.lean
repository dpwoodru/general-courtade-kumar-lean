import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0010

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0213

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-9/40) (-1/8) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (-9/40 : ℝ) with hx0213 | hx0213
  · rcases le_total tau.im (-1/8 : ℝ) with hy0213 | hy0213
    · have hs02130 : InSquare (-19/80) (-11/80) (1/80) tau := by
        convert childLL hs hx0213 hy0213 using 1 <;> norm_num
      exact Batch0010.cell0081.sound htau (by
        simp only [Batch0010.cell0081, Batch0010.tau0081, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs02130 (by positivity) using 1 <;> norm_num)
    · have hs02132 : InSquare (-19/80) (-9/80) (1/80) tau := by
        convert childUL hs hx0213 hy0213 using 1 <;> norm_num
      exact Batch0010.cell0083.sound htau (by
        simp only [Batch0010.cell0083, Batch0010.tau0083, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs02132 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (-1/8 : ℝ) with hy0213 | hy0213
    · have hs02131 : InSquare (-17/80) (-11/80) (1/80) tau := by
        convert childLR hs hx0213 hy0213 using 1 <;> norm_num
      exact Batch0010.cell0082.sound htau (by
        simp only [Batch0010.cell0082, Batch0010.tau0082, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs02131 (by positivity) using 1 <;> norm_num)
    · have hs02133 : InSquare (-17/80) (-9/80) (1/80) tau := by
        convert childUR hs hx0213 hy0213 using 1 <;> norm_num
      exact Batch0010.cell0084.sound htau (by
        simp only [Batch0010.cell0084, Batch0010.tau0084, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs02133 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0213
