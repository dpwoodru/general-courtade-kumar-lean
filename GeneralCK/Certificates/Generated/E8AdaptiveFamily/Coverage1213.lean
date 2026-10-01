import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0019
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0020

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1213

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (7/40) (-1/8) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (7/40 : ℝ) with hx1213 | hx1213
  · rcases le_total tau.im (-1/8 : ℝ) with hy1213 | hy1213
    · have hs12130 : InSquare (13/80) (-11/80) (1/80) tau := by
        convert childLL hs hx1213 hy1213 using 1 <;> norm_num
      exact Batch0019.cell0157.sound htau (by
        simp only [Batch0019.cell0157, Batch0019.tau0157, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs12130 (by positivity) using 1 <;> norm_num)
    · have hs12132 : InSquare (13/80) (-9/80) (1/80) tau := by
        convert childUL hs hx1213 hy1213 using 1 <;> norm_num
      exact Batch0019.cell0159.sound htau (by
        simp only [Batch0019.cell0159, Batch0019.tau0159, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs12132 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (-1/8 : ℝ) with hy1213 | hy1213
    · have hs12131 : InSquare (3/16) (-11/80) (1/80) tau := by
        convert childLR hs hx1213 hy1213 using 1 <;> norm_num
      exact Batch0019.cell0158.sound htau (by
        simp only [Batch0019.cell0158, Batch0019.tau0158, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs12131 (by positivity) using 1 <;> norm_num)
    · have hs12133 : InSquare (3/16) (-9/80) (1/80) tau := by
        convert childUR hs hx1213 hy1213 using 1 <;> norm_num
      exact Batch0020.cell0160.sound htau (by
        simp only [Batch0020.cell0160, Batch0020.tau0160, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs12133 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1213
