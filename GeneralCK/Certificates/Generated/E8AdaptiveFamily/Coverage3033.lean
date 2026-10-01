import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0035

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3033

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (7/40) (7/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (7/40 : ℝ) with hx3033 | hx3033
  · rcases le_total tau.im (7/40 : ℝ) with hy3033 | hy3033
    · have hs30330 : InSquare (13/80) (13/80) (1/80) tau := by
        convert childLL hs hx3033 hy3033 using 1 <;> norm_num
      exact Batch0035.cell0283.sound htau (by
        simp only [Batch0035.cell0283, Batch0035.tau0283, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs30330 (by positivity) using 1 <;> norm_num)
    · have hs30332 : InSquare (13/80) (3/16) (1/80) tau := by
        convert childUL hs hx3033 hy3033 using 1 <;> norm_num
      exact Batch0035.cell0285.sound htau (by
        simp only [Batch0035.cell0285, Batch0035.tau0285, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs30332 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (7/40 : ℝ) with hy3033 | hy3033
    · have hs30331 : InSquare (3/16) (13/80) (1/80) tau := by
        convert childLR hs hx3033 hy3033 using 1 <;> norm_num
      exact Batch0035.cell0284.sound htau (by
        simp only [Batch0035.cell0284, Batch0035.tau0284, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs30331 (by positivity) using 1 <;> norm_num)
    · have hs30333 : InSquare (3/16) (3/16) (1/80) tau := by
        convert childUR hs hx3033 hy3033 using 1 <;> norm_num
      exact Batch0035.cell0286.sound htau (by
        simp only [Batch0035.cell0286, Batch0035.tau0286, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs30333 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3033
