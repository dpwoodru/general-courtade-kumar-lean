import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0033
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0034

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3023

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (3/40) (7/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (3/40 : ℝ) with hx3023 | hx3023
  · rcases le_total tau.im (7/40 : ℝ) with hy3023 | hy3023
    · have hs30230 : InSquare (1/16) (13/80) (1/80) tau := by
        convert childLL hs hx3023 hy3023 using 1 <;> norm_num
      exact Batch0033.cell0271.sound htau (by
        simp only [Batch0033.cell0271, Batch0033.tau0271, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs30230 (by positivity) using 1 <;> norm_num)
    · have hs30232 : InSquare (1/16) (3/16) (1/80) tau := by
        convert childUL hs hx3023 hy3023 using 1 <;> norm_num
      exact Batch0034.cell0273.sound htau (by
        simp only [Batch0034.cell0273, Batch0034.tau0273, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs30232 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (7/40 : ℝ) with hy3023 | hy3023
    · have hs30231 : InSquare (7/80) (13/80) (1/80) tau := by
        convert childLR hs hx3023 hy3023 using 1 <;> norm_num
      exact Batch0034.cell0272.sound htau (by
        simp only [Batch0034.cell0272, Batch0034.tau0272, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs30231 (by positivity) using 1 <;> norm_num)
    · have hs30233 : InSquare (7/80) (3/16) (1/80) tau := by
        convert childUR hs hx3023 hy3023 using 1 <;> norm_num
      exact Batch0034.cell0274.sound htau (by
        simp only [Batch0034.cell0274, Batch0034.tau0274, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs30233 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3023
