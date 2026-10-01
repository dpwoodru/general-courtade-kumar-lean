import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0035
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0036

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3101

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (11/40) (1/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (11/40 : ℝ) with hx3101 | hx3101
  · rcases le_total tau.im (1/40 : ℝ) with hy3101 | hy3101
    · have hs31010 : InSquare (21/80) (1/80) (1/80) tau := by
        convert childLL hs hx3101 hy3101 using 1 <;> norm_num
      exact Batch0035.cell0287.sound htau (by
        simp only [Batch0035.cell0287, Batch0035.tau0287, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs31010 (by positivity) using 1 <;> norm_num)
    · have hs31012 : InSquare (21/80) (3/80) (1/80) tau := by
        convert childUL hs hx3101 hy3101 using 1 <;> norm_num
      exact Batch0036.cell0289.sound htau (by
        simp only [Batch0036.cell0289, Batch0036.tau0289, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs31012 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (1/40 : ℝ) with hy3101 | hy3101
    · have hs31011 : InSquare (23/80) (1/80) (1/80) tau := by
        convert childLR hs hx3101 hy3101 using 1 <;> norm_num
      exact Batch0036.cell0288.sound htau (by
        simp only [Batch0036.cell0288, Batch0036.tau0288, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs31011 (by positivity) using 1 <;> norm_num)
    · have hs31013 : InSquare (23/80) (3/80) (1/80) tau := by
        convert childUR hs hx3101 hy3101 using 1 <;> norm_num
      exact Batch0036.cell0290.sound htau (by
        simp only [Batch0036.cell0290, Batch0036.tau0290, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs31013 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3101
