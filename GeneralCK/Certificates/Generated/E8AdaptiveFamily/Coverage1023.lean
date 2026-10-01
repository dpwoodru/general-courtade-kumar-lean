import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0016
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0017

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1023

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (3/40) (-9/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (3/40 : ℝ) with hx1023 | hx1023
  · rcases le_total tau.im (-9/40 : ℝ) with hy1023 | hy1023
    · have hs10230 : InSquare (1/16) (-19/80) (1/80) tau := by
        convert childLL hs hx1023 hy1023 using 1 <;> norm_num
      exact Batch0016.cell0135.sound htau (by
        simp only [Batch0016.cell0135, Batch0016.tau0135, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs10230 (by positivity) using 1 <;> norm_num)
    · have hs10232 : InSquare (1/16) (-17/80) (1/80) tau := by
        convert childUL hs hx1023 hy1023 using 1 <;> norm_num
      exact Batch0017.cell0137.sound htau (by
        simp only [Batch0017.cell0137, Batch0017.tau0137, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs10232 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (-9/40 : ℝ) with hy1023 | hy1023
    · have hs10231 : InSquare (7/80) (-19/80) (1/80) tau := by
        convert childLR hs hx1023 hy1023 using 1 <;> norm_num
      exact Batch0017.cell0136.sound htau (by
        simp only [Batch0017.cell0136, Batch0017.tau0136, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs10231 (by positivity) using 1 <;> norm_num)
    · have hs10233 : InSquare (7/80) (-17/80) (1/80) tau := by
        convert childUR hs hx1023 hy1023 using 1 <;> norm_num
      exact Batch0017.cell0138.sound htau (by
        simp only [Batch0017.cell0138, Batch0017.tau0138, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs10233 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1023
