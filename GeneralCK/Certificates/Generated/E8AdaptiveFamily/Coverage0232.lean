import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0013

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0232

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-11/40) (-1/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (-11/40 : ℝ) with hx0232 | hx0232
  · rcases le_total tau.im (-1/40 : ℝ) with hy0232 | hy0232
    · have hs02320 : InSquare (-23/80) (-3/80) (1/80) tau := by
        convert childLL hs hx0232 hy0232 using 1 <;> norm_num
      exact Batch0013.cell0105.sound htau (by
        simp only [Batch0013.cell0105, Batch0013.tau0105, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs02320 (by positivity) using 1 <;> norm_num)
    · have hs02322 : InSquare (-23/80) (-1/80) (1/80) tau := by
        convert childUL hs hx0232 hy0232 using 1 <;> norm_num
      exact Batch0013.cell0107.sound htau (by
        simp only [Batch0013.cell0107, Batch0013.tau0107, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs02322 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (-1/40 : ℝ) with hy0232 | hy0232
    · have hs02321 : InSquare (-21/80) (-3/80) (1/80) tau := by
        convert childLR hs hx0232 hy0232 using 1 <;> norm_num
      exact Batch0013.cell0106.sound htau (by
        simp only [Batch0013.cell0106, Batch0013.tau0106, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs02321 (by positivity) using 1 <;> norm_num)
    · have hs02323 : InSquare (-21/80) (-1/80) (1/80) tau := by
        convert childUR hs hx0232 hy0232 using 1 <;> norm_num
      exact Batch0013.cell0108.sound htau (by
        simp only [Batch0013.cell0108, Batch0013.tau0108, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs02323 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0232
