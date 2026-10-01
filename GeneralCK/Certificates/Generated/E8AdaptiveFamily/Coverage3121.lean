import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0039

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3121

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (11/40) (1/8) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (11/40 : ℝ) with hx3121 | hx3121
  · rcases le_total tau.im (1/8 : ℝ) with hy3121 | hy3121
    · have hs31210 : InSquare (21/80) (9/80) (1/80) tau := by
        convert childLL hs hx3121 hy3121 using 1 <;> norm_num
      exact Batch0039.cell0315.sound htau (by
        simp only [Batch0039.cell0315, Batch0039.tau0315, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs31210 (by positivity) using 1 <;> norm_num)
    · have hs31212 : InSquare (21/80) (11/80) (1/80) tau := by
        convert childUL hs hx3121 hy3121 using 1 <;> norm_num
      exact Batch0039.cell0317.sound htau (by
        simp only [Batch0039.cell0317, Batch0039.tau0317, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs31212 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (1/8 : ℝ) with hy3121 | hy3121
    · have hs31211 : InSquare (23/80) (9/80) (1/80) tau := by
        convert childLR hs hx3121 hy3121 using 1 <;> norm_num
      exact Batch0039.cell0316.sound htau (by
        simp only [Batch0039.cell0316, Batch0039.tau0316, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs31211 (by positivity) using 1 <;> norm_num)
    · have hs31213 : InSquare (23/80) (11/80) (1/80) tau := by
        convert childUR hs hx3121 hy3121 using 1 <;> norm_num
      exact Batch0039.cell0318.sound htau (by
        simp only [Batch0039.cell0318, Batch0039.tau0318, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs31213 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3121
