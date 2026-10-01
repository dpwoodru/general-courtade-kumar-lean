import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0022
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0023

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1323

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (11/40) (-1/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (11/40 : ℝ) with hx1323 | hx1323
  · rcases le_total tau.im (-1/40 : ℝ) with hy1323 | hy1323
    · have hs13230 : InSquare (21/80) (-3/80) (1/80) tau := by
        convert childLL hs hx1323 hy1323 using 1 <;> norm_num
      exact Batch0022.cell0182.sound htau (by
        simp only [Batch0022.cell0182, Batch0022.tau0182, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs13230 (by positivity) using 1 <;> norm_num)
    · have hs13232 : InSquare (21/80) (-1/80) (1/80) tau := by
        convert childUL hs hx1323 hy1323 using 1 <;> norm_num
      exact Batch0023.cell0184.sound htau (by
        simp only [Batch0023.cell0184, Batch0023.tau0184, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs13232 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (-1/40 : ℝ) with hy1323 | hy1323
    · have hs13231 : InSquare (23/80) (-3/80) (1/80) tau := by
        convert childLR hs hx1323 hy1323 using 1 <;> norm_num
      exact Batch0022.cell0183.sound htau (by
        simp only [Batch0022.cell0183, Batch0022.tau0183, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs13231 (by positivity) using 1 <;> norm_num)
    · have hs13233 : InSquare (23/80) (-1/80) (1/80) tau := by
        convert childUR hs hx1323 hy1323 using 1 <;> norm_num
      exact Batch0023.cell0185.sound htau (by
        simp only [Batch0023.cell0185, Batch0023.tau0185, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs13233 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1323
