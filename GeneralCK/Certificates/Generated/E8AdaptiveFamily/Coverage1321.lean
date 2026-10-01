import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0022

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1321

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (11/40) (-3/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (11/40 : ℝ) with hx1321 | hx1321
  · rcases le_total tau.im (-3/40 : ℝ) with hy1321 | hy1321
    · have hs13210 : InSquare (21/80) (-7/80) (1/80) tau := by
        convert childLL hs hx1321 hy1321 using 1 <;> norm_num
      exact Batch0022.cell0178.sound htau (by
        simp only [Batch0022.cell0178, Batch0022.tau0178, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs13210 (by positivity) using 1 <;> norm_num)
    · have hs13212 : InSquare (21/80) (-1/16) (1/80) tau := by
        convert childUL hs hx1321 hy1321 using 1 <;> norm_num
      exact Batch0022.cell0180.sound htau (by
        simp only [Batch0022.cell0180, Batch0022.tau0180, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs13212 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (-3/40 : ℝ) with hy1321 | hy1321
    · have hs13211 : InSquare (23/80) (-7/80) (1/80) tau := by
        convert childLR hs hx1321 hy1321 using 1 <;> norm_num
      exact Batch0022.cell0179.sound htau (by
        simp only [Batch0022.cell0179, Batch0022.tau0179, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs13211 (by positivity) using 1 <;> norm_num)
    · have hs13213 : InSquare (23/80) (-1/16) (1/80) tau := by
        convert childUR hs hx1321 hy1321 using 1 <;> norm_num
      exact Batch0022.cell0181.sound htau (by
        simp only [Batch0022.cell0181, Batch0022.tau0181, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs13213 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1321
