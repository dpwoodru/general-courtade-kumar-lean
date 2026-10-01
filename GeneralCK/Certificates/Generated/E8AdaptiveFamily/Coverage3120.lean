import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0038
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0039

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3120

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (9/40) (1/8) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (9/40 : ℝ) with hx3120 | hx3120
  · rcases le_total tau.im (1/8 : ℝ) with hy3120 | hy3120
    · have hs31200 : InSquare (17/80) (9/80) (1/80) tau := by
        convert childLL hs hx3120 hy3120 using 1 <;> norm_num
      exact Batch0038.cell0311.sound htau (by
        simp only [Batch0038.cell0311, Batch0038.tau0311, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs31200 (by positivity) using 1 <;> norm_num)
    · have hs31202 : InSquare (17/80) (11/80) (1/80) tau := by
        convert childUL hs hx3120 hy3120 using 1 <;> norm_num
      exact Batch0039.cell0313.sound htau (by
        simp only [Batch0039.cell0313, Batch0039.tau0313, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs31202 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (1/8 : ℝ) with hy3120 | hy3120
    · have hs31201 : InSquare (19/80) (9/80) (1/80) tau := by
        convert childLR hs hx3120 hy3120 using 1 <;> norm_num
      exact Batch0039.cell0312.sound htau (by
        simp only [Batch0039.cell0312, Batch0039.tau0312, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs31201 (by positivity) using 1 <;> norm_num)
    · have hs31203 : InSquare (19/80) (11/80) (1/80) tau := by
        convert childUR hs hx3120 hy3120 using 1 <;> norm_num
      exact Batch0039.cell0314.sound htau (by
        simp only [Batch0039.cell0314, Batch0039.tau0314, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs31203 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3120
