import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0023
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0024

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1332

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (13/40) (-1/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (13/40 : ℝ) with hx1332 | hx1332
  · rcases le_total tau.im (-1/40 : ℝ) with hy1332 | hy1332
    · have hs13320 : InSquare (5/16) (-3/80) (1/80) tau := by
        convert childLL hs hx1332 hy1332 using 1 <;> norm_num
      exact Batch0023.cell0191.sound htau (by
        simp only [Batch0023.cell0191, Batch0023.tau0191, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs13320 (by positivity) using 1 <;> norm_num)
    · have hs13322 : InSquare (5/16) (-1/80) (1/80) tau := by
        convert childUL hs hx1332 hy1332 using 1 <;> norm_num
      exact Batch0024.cell0193.sound htau (by
        simp only [Batch0024.cell0193, Batch0024.tau0193, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs13322 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (-1/40 : ℝ) with hy1332 | hy1332
    · have hs13321 : InSquare (27/80) (-3/80) (1/80) tau := by
        convert childLR hs hx1332 hy1332 using 1 <;> norm_num
      exact Batch0024.cell0192.sound htau (by
        simp only [Batch0024.cell0192, Batch0024.tau0192, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs13321 (by positivity) using 1 <;> norm_num)
    · have hs13323 : InSquare (27/80) (-1/80) (1/80) tau := by
        convert childUR hs hx1332 hy1332 using 1 <;> norm_num
      exact Batch0024.cell0194.sound htau (by
        simp only [Batch0024.cell0194, Batch0024.tau0194, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs13323 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1332
