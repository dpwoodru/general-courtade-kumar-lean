import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0012

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0230

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-11/40) (-3/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (-11/40 : ℝ) with hx0230 | hx0230
  · rcases le_total tau.im (-3/40 : ℝ) with hy0230 | hy0230
    · have hs02300 : InSquare (-23/80) (-7/80) (1/80) tau := by
        convert childLL hs hx0230 hy0230 using 1 <;> norm_num
      exact Batch0012.cell0097.sound htau (by
        simp only [Batch0012.cell0097, Batch0012.tau0097, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs02300 (by positivity) using 1 <;> norm_num)
    · have hs02302 : InSquare (-23/80) (-1/16) (1/80) tau := by
        convert childUL hs hx0230 hy0230 using 1 <;> norm_num
      exact Batch0012.cell0099.sound htau (by
        simp only [Batch0012.cell0099, Batch0012.tau0099, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs02302 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (-3/40 : ℝ) with hy0230 | hy0230
    · have hs02301 : InSquare (-21/80) (-7/80) (1/80) tau := by
        convert childLR hs hx0230 hy0230 using 1 <;> norm_num
      exact Batch0012.cell0098.sound htau (by
        simp only [Batch0012.cell0098, Batch0012.tau0098, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs02301 (by positivity) using 1 <;> norm_num)
    · have hs02303 : InSquare (-21/80) (-1/16) (1/80) tau := by
        convert childUR hs hx0230 hy0230 using 1 <;> norm_num
      exact Batch0012.cell0100.sound htau (by
        simp only [Batch0012.cell0100, Batch0012.tau0100, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs02303 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0230
