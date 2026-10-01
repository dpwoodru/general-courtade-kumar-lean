import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0036

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3102

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (9/40) (3/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (9/40 : ℝ) with hx3102 | hx3102
  · rcases le_total tau.im (3/40 : ℝ) with hy3102 | hy3102
    · have hs31020 : InSquare (17/80) (1/16) (1/80) tau := by
        convert childLL hs hx3102 hy3102 using 1 <;> norm_num
      exact Batch0036.cell0291.sound htau (by
        simp only [Batch0036.cell0291, Batch0036.tau0291, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs31020 (by positivity) using 1 <;> norm_num)
    · have hs31022 : InSquare (17/80) (7/80) (1/80) tau := by
        convert childUL hs hx3102 hy3102 using 1 <;> norm_num
      exact Batch0036.cell0293.sound htau (by
        simp only [Batch0036.cell0293, Batch0036.tau0293, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs31022 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (3/40 : ℝ) with hy3102 | hy3102
    · have hs31021 : InSquare (19/80) (1/16) (1/80) tau := by
        convert childLR hs hx3102 hy3102 using 1 <;> norm_num
      exact Batch0036.cell0292.sound htau (by
        simp only [Batch0036.cell0292, Batch0036.tau0292, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs31021 (by positivity) using 1 <;> norm_num)
    · have hs31023 : InSquare (19/80) (7/80) (1/80) tau := by
        convert childUR hs hx3102 hy3102 using 1 <;> norm_num
      exact Batch0036.cell0294.sound htau (by
        simp only [Batch0036.cell0294, Batch0036.tau0294, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs31023 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3102
