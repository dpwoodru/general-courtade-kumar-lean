import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0012
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0013

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0231

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-9/40) (-3/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (-9/40 : ℝ) with hx0231 | hx0231
  · rcases le_total tau.im (-3/40 : ℝ) with hy0231 | hy0231
    · have hs02310 : InSquare (-19/80) (-7/80) (1/80) tau := by
        convert childLL hs hx0231 hy0231 using 1 <;> norm_num
      exact Batch0012.cell0101.sound htau (by
        simp only [Batch0012.cell0101, Batch0012.tau0101, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs02310 (by positivity) using 1 <;> norm_num)
    · have hs02312 : InSquare (-19/80) (-1/16) (1/80) tau := by
        convert childUL hs hx0231 hy0231 using 1 <;> norm_num
      exact Batch0012.cell0103.sound htau (by
        simp only [Batch0012.cell0103, Batch0012.tau0103, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs02312 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (-3/40 : ℝ) with hy0231 | hy0231
    · have hs02311 : InSquare (-17/80) (-7/80) (1/80) tau := by
        convert childLR hs hx0231 hy0231 using 1 <;> norm_num
      exact Batch0012.cell0102.sound htau (by
        simp only [Batch0012.cell0102, Batch0012.tau0102, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs02311 (by positivity) using 1 <;> norm_num)
    · have hs02313 : InSquare (-17/80) (-1/16) (1/80) tau := by
        convert childUR hs hx0231 hy0231 using 1 <;> norm_num
      exact Batch0013.cell0104.sound htau (by
        simp only [Batch0013.cell0104, Batch0013.tau0104, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs02313 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0231
