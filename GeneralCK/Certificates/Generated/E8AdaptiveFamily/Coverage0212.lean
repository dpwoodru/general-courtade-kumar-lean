import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0009
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0010

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0212

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-11/40) (-1/8) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (-11/40 : ℝ) with hx0212 | hx0212
  · rcases le_total tau.im (-1/8 : ℝ) with hy0212 | hy0212
    · have hs02120 : InSquare (-23/80) (-11/80) (1/80) tau := by
        convert childLL hs hx0212 hy0212 using 1 <;> norm_num
      exact Batch0009.cell0077.sound htau (by
        simp only [Batch0009.cell0077, Batch0009.tau0077, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs02120 (by positivity) using 1 <;> norm_num)
    · have hs02122 : InSquare (-23/80) (-9/80) (1/80) tau := by
        convert childUL hs hx0212 hy0212 using 1 <;> norm_num
      exact Batch0009.cell0079.sound htau (by
        simp only [Batch0009.cell0079, Batch0009.tau0079, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs02122 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (-1/8 : ℝ) with hy0212 | hy0212
    · have hs02121 : InSquare (-21/80) (-11/80) (1/80) tau := by
        convert childLR hs hx0212 hy0212 using 1 <;> norm_num
      exact Batch0009.cell0078.sound htau (by
        simp only [Batch0009.cell0078, Batch0009.tau0078, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs02121 (by positivity) using 1 <;> norm_num)
    · have hs02123 : InSquare (-21/80) (-9/80) (1/80) tau := by
        convert childUR hs hx0212 hy0212 using 1 <;> norm_num
      exact Batch0010.cell0080.sound htau (by
        simp only [Batch0010.cell0080, Batch0010.tau0080, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs02123 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0212
