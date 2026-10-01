import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0036
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0037

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3103

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (11/40) (3/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (11/40 : ℝ) with hx3103 | hx3103
  · rcases le_total tau.im (3/40 : ℝ) with hy3103 | hy3103
    · have hs31030 : InSquare (21/80) (1/16) (1/80) tau := by
        convert childLL hs hx3103 hy3103 using 1 <;> norm_num
      exact Batch0036.cell0295.sound htau (by
        simp only [Batch0036.cell0295, Batch0036.tau0295, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs31030 (by positivity) using 1 <;> norm_num)
    · have hs31032 : InSquare (21/80) (7/80) (1/80) tau := by
        convert childUL hs hx3103 hy3103 using 1 <;> norm_num
      exact Batch0037.cell0297.sound htau (by
        simp only [Batch0037.cell0297, Batch0037.tau0297, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs31032 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (3/40 : ℝ) with hy3103 | hy3103
    · have hs31031 : InSquare (23/80) (1/16) (1/80) tau := by
        convert childLR hs hx3103 hy3103 using 1 <;> norm_num
      exact Batch0037.cell0296.sound htau (by
        simp only [Batch0037.cell0296, Batch0037.tau0296, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs31031 (by positivity) using 1 <;> norm_num)
    · have hs31033 : InSquare (23/80) (7/80) (1/80) tau := by
        convert childUR hs hx3103 hy3103 using 1 <;> norm_num
      exact Batch0037.cell0298.sound htau (by
        simp only [Batch0037.cell0298, Batch0037.tau0298, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs31033 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3103
