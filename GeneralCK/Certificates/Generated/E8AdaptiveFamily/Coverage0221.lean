import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0010
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0011

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0221

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-13/40) (-3/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (-13/40 : ℝ) with hx0221 | hx0221
  · rcases le_total tau.im (-3/40 : ℝ) with hy0221 | hy0221
    · have hs02210 : InSquare (-27/80) (-7/80) (1/80) tau := by
        convert childLL hs hx0221 hy0221 using 1 <;> norm_num
      exact Batch0010.cell0086.sound htau (by
        simp only [Batch0010.cell0086, Batch0010.tau0086, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs02210 (by positivity) using 1 <;> norm_num)
    · have hs02212 : InSquare (-27/80) (-1/16) (1/80) tau := by
        convert childUL hs hx0221 hy0221 using 1 <;> norm_num
      exact Batch0011.cell0088.sound htau (by
        simp only [Batch0011.cell0088, Batch0011.tau0088, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs02212 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (-3/40 : ℝ) with hy0221 | hy0221
    · have hs02211 : InSquare (-5/16) (-7/80) (1/80) tau := by
        convert childLR hs hx0221 hy0221 using 1 <;> norm_num
      exact Batch0010.cell0087.sound htau (by
        simp only [Batch0010.cell0087, Batch0010.tau0087, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs02211 (by positivity) using 1 <;> norm_num)
    · have hs02213 : InSquare (-5/16) (-1/16) (1/80) tau := by
        convert childUR hs hx0221 hy0221 using 1 <;> norm_num
      exact Batch0011.cell0089.sound htau (by
        simp only [Batch0011.cell0089, Batch0011.tau0089, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs02213 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0221
