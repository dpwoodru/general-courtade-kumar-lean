import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0020
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0021

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1302

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (9/40) (-1/8) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (9/40 : ℝ) with hx1302 | hx1302
  · rcases le_total tau.im (-1/8 : ℝ) with hy1302 | hy1302
    · have hs13020 : InSquare (17/80) (-11/80) (1/80) tau := by
        convert childLL hs hx1302 hy1302 using 1 <;> norm_num
      exact Batch0020.cell0165.sound htau (by
        simp only [Batch0020.cell0165, Batch0020.tau0165, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs13020 (by positivity) using 1 <;> norm_num)
    · have hs13022 : InSquare (17/80) (-9/80) (1/80) tau := by
        convert childUL hs hx1302 hy1302 using 1 <;> norm_num
      exact Batch0020.cell0167.sound htau (by
        simp only [Batch0020.cell0167, Batch0020.tau0167, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs13022 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (-1/8 : ℝ) with hy1302 | hy1302
    · have hs13021 : InSquare (19/80) (-11/80) (1/80) tau := by
        convert childLR hs hx1302 hy1302 using 1 <;> norm_num
      exact Batch0020.cell0166.sound htau (by
        simp only [Batch0020.cell0166, Batch0020.tau0166, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs13021 (by positivity) using 1 <;> norm_num)
    · have hs13023 : InSquare (19/80) (-9/80) (1/80) tau := by
        convert childUR hs hx1302 hy1302 using 1 <;> norm_num
      exact Batch0021.cell0168.sound htau (by
        simp only [Batch0021.cell0168, Batch0021.tau0168, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs13023 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1302
