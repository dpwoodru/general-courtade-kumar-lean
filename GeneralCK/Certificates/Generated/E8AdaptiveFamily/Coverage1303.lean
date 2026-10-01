import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0021

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1303

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (11/40) (-1/8) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (11/40 : ℝ) with hx1303 | hx1303
  · rcases le_total tau.im (-1/8 : ℝ) with hy1303 | hy1303
    · have hs13030 : InSquare (21/80) (-11/80) (1/80) tau := by
        convert childLL hs hx1303 hy1303 using 1 <;> norm_num
      exact Batch0021.cell0169.sound htau (by
        simp only [Batch0021.cell0169, Batch0021.tau0169, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs13030 (by positivity) using 1 <;> norm_num)
    · have hs13032 : InSquare (21/80) (-9/80) (1/80) tau := by
        convert childUL hs hx1303 hy1303 using 1 <;> norm_num
      exact Batch0021.cell0171.sound htau (by
        simp only [Batch0021.cell0171, Batch0021.tau0171, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs13032 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (-1/8 : ℝ) with hy1303 | hy1303
    · have hs13031 : InSquare (23/80) (-11/80) (1/80) tau := by
        convert childLR hs hx1303 hy1303 using 1 <;> norm_num
      exact Batch0021.cell0170.sound htau (by
        simp only [Batch0021.cell0170, Batch0021.tau0170, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs13031 (by positivity) using 1 <;> norm_num)
    · have hs13033 : InSquare (23/80) (-9/80) (1/80) tau := by
        convert childUR hs hx1303 hy1303 using 1 <;> norm_num
      exact Batch0021.cell0172.sound htau (by
        simp only [Batch0021.cell0172, Batch0021.tau0172, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs13033 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1303
