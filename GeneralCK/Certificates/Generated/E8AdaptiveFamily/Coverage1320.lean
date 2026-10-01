import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0021
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0022

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1320

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (9/40) (-3/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (9/40 : ℝ) with hx1320 | hx1320
  · rcases le_total tau.im (-3/40 : ℝ) with hy1320 | hy1320
    · have hs13200 : InSquare (17/80) (-7/80) (1/80) tau := by
        convert childLL hs hx1320 hy1320 using 1 <;> norm_num
      exact Batch0021.cell0174.sound htau (by
        simp only [Batch0021.cell0174, Batch0021.tau0174, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs13200 (by positivity) using 1 <;> norm_num)
    · have hs13202 : InSquare (17/80) (-1/16) (1/80) tau := by
        convert childUL hs hx1320 hy1320 using 1 <;> norm_num
      exact Batch0022.cell0176.sound htau (by
        simp only [Batch0022.cell0176, Batch0022.tau0176, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs13202 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (-3/40 : ℝ) with hy1320 | hy1320
    · have hs13201 : InSquare (19/80) (-7/80) (1/80) tau := by
        convert childLR hs hx1320 hy1320 using 1 <;> norm_num
      exact Batch0021.cell0175.sound htau (by
        simp only [Batch0021.cell0175, Batch0021.tau0175, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs13201 (by positivity) using 1 <;> norm_num)
    · have hs13203 : InSquare (19/80) (-1/16) (1/80) tau := by
        convert childUR hs hx1320 hy1320 using 1 <;> norm_num
      exact Batch0022.cell0177.sound htau (by
        simp only [Batch0022.cell0177, Batch0022.tau0177, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs13203 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1320
