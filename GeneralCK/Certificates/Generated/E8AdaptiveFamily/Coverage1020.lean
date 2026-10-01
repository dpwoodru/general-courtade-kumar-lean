import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0015
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0016

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1020

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (1/40) (-11/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (1/40 : ℝ) with hx1020 | hx1020
  · rcases le_total tau.im (-11/40 : ℝ) with hy1020 | hy1020
    · have hs10200 : InSquare (1/80) (-23/80) (1/80) tau := by
        convert childLL hs hx1020 hy1020 using 1 <;> norm_num
      exact Batch0015.cell0125.sound htau (by
        simp only [Batch0015.cell0125, Batch0015.tau0125, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs10200 (by positivity) using 1 <;> norm_num)
    · have hs10202 : InSquare (1/80) (-21/80) (1/80) tau := by
        convert childUL hs hx1020 hy1020 using 1 <;> norm_num
      exact Batch0015.cell0127.sound htau (by
        simp only [Batch0015.cell0127, Batch0015.tau0127, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs10202 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (-11/40 : ℝ) with hy1020 | hy1020
    · have hs10201 : InSquare (3/80) (-23/80) (1/80) tau := by
        convert childLR hs hx1020 hy1020 using 1 <;> norm_num
      exact Batch0015.cell0126.sound htau (by
        simp only [Batch0015.cell0126, Batch0015.tau0126, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs10201 (by positivity) using 1 <;> norm_num)
    · have hs10203 : InSquare (3/80) (-21/80) (1/80) tau := by
        convert childUR hs hx1020 hy1020 using 1 <;> norm_num
      exact Batch0016.cell0128.sound htau (by
        simp only [Batch0016.cell0128, Batch0016.tau0128, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs10203 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1020
