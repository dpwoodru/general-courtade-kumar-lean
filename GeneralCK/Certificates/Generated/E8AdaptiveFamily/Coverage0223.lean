import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0011
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0012

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0223

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-13/40) (-1/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (-13/40 : ℝ) with hx0223 | hx0223
  · rcases le_total tau.im (-1/40 : ℝ) with hy0223 | hy0223
    · have hs02230 : InSquare (-27/80) (-3/80) (1/80) tau := by
        convert childLL hs hx0223 hy0223 using 1 <;> norm_num
      exact Batch0011.cell0093.sound htau (by
        simp only [Batch0011.cell0093, Batch0011.tau0093, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs02230 (by positivity) using 1 <;> norm_num)
    · have hs02232 : InSquare (-27/80) (-1/80) (1/80) tau := by
        convert childUL hs hx0223 hy0223 using 1 <;> norm_num
      exact Batch0011.cell0095.sound htau (by
        simp only [Batch0011.cell0095, Batch0011.tau0095, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs02232 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (-1/40 : ℝ) with hy0223 | hy0223
    · have hs02231 : InSquare (-5/16) (-3/80) (1/80) tau := by
        convert childLR hs hx0223 hy0223 using 1 <;> norm_num
      exact Batch0011.cell0094.sound htau (by
        simp only [Batch0011.cell0094, Batch0011.tau0094, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs02231 (by positivity) using 1 <;> norm_num)
    · have hs02233 : InSquare (-5/16) (-1/80) (1/80) tau := by
        convert childUR hs hx0223 hy0223 using 1 <;> norm_num
      exact Batch0012.cell0096.sound htau (by
        simp only [Batch0012.cell0096, Batch0012.tau0096, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs02233 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0223
