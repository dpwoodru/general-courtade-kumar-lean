import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0016

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1022

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (1/40) (-9/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (1/40 : ℝ) with hx1022 | hx1022
  · rcases le_total tau.im (-9/40 : ℝ) with hy1022 | hy1022
    · have hs10220 : InSquare (1/80) (-19/80) (1/80) tau := by
        convert childLL hs hx1022 hy1022 using 1 <;> norm_num
      exact Batch0016.cell0131.sound htau (by
        simp only [Batch0016.cell0131, Batch0016.tau0131, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs10220 (by positivity) using 1 <;> norm_num)
    · have hs10222 : InSquare (1/80) (-17/80) (1/80) tau := by
        convert childUL hs hx1022 hy1022 using 1 <;> norm_num
      exact Batch0016.cell0133.sound htau (by
        simp only [Batch0016.cell0133, Batch0016.tau0133, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs10222 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (-9/40 : ℝ) with hy1022 | hy1022
    · have hs10221 : InSquare (3/80) (-19/80) (1/80) tau := by
        convert childLR hs hx1022 hy1022 using 1 <;> norm_num
      exact Batch0016.cell0132.sound htau (by
        simp only [Batch0016.cell0132, Batch0016.tau0132, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs10221 (by positivity) using 1 <;> norm_num)
    · have hs10223 : InSquare (3/80) (-17/80) (1/80) tau := by
        convert childUR hs hx1022 hy1022 using 1 <;> norm_num
      exact Batch0016.cell0134.sound htau (by
        simp only [Batch0016.cell0134, Batch0016.tau0134, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs10223 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1022
