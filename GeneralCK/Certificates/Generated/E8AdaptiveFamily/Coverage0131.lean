import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0007

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0131

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-1/40) (-11/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (-1/40 : ℝ) with hx0131 | hx0131
  · rcases le_total tau.im (-11/40 : ℝ) with hy0131 | hy0131
    · have hs01310 : InSquare (-3/80) (-23/80) (1/80) tau := by
        convert childLL hs hx0131 hy0131 using 1 <;> norm_num
      exact Batch0007.cell0060.sound htau (by
        simp only [Batch0007.cell0060, Batch0007.tau0060, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs01310 (by positivity) using 1 <;> norm_num)
    · have hs01312 : InSquare (-3/80) (-21/80) (1/80) tau := by
        convert childUL hs hx0131 hy0131 using 1 <;> norm_num
      exact Batch0007.cell0062.sound htau (by
        simp only [Batch0007.cell0062, Batch0007.tau0062, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs01312 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (-11/40 : ℝ) with hy0131 | hy0131
    · have hs01311 : InSquare (-1/80) (-23/80) (1/80) tau := by
        convert childLR hs hx0131 hy0131 using 1 <;> norm_num
      exact Batch0007.cell0061.sound htau (by
        simp only [Batch0007.cell0061, Batch0007.tau0061, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs01311 (by positivity) using 1 <;> norm_num)
    · have hs01313 : InSquare (-1/80) (-21/80) (1/80) tau := by
        convert childUR hs hx0131 hy0131 using 1 <;> norm_num
      exact Batch0007.cell0063.sound htau (by
        simp only [Batch0007.cell0063, Batch0007.tau0063, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs01313 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0131
