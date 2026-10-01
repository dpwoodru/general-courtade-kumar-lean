import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0034
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0035

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3032

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (1/8) (7/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (1/8 : ℝ) with hx3032 | hx3032
  · rcases le_total tau.im (7/40 : ℝ) with hy3032 | hy3032
    · have hs30320 : InSquare (9/80) (13/80) (1/80) tau := by
        convert childLL hs hx3032 hy3032 using 1 <;> norm_num
      exact Batch0034.cell0279.sound htau (by
        simp only [Batch0034.cell0279, Batch0034.tau0279, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs30320 (by positivity) using 1 <;> norm_num)
    · have hs30322 : InSquare (9/80) (3/16) (1/80) tau := by
        convert childUL hs hx3032 hy3032 using 1 <;> norm_num
      exact Batch0035.cell0281.sound htau (by
        simp only [Batch0035.cell0281, Batch0035.tau0281, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs30322 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (7/40 : ℝ) with hy3032 | hy3032
    · have hs30321 : InSquare (11/80) (13/80) (1/80) tau := by
        convert childLR hs hx3032 hy3032 using 1 <;> norm_num
      exact Batch0035.cell0280.sound htau (by
        simp only [Batch0035.cell0280, Batch0035.tau0280, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs30321 (by positivity) using 1 <;> norm_num)
    · have hs30323 : InSquare (11/80) (3/16) (1/80) tau := by
        convert childUR hs hx3032 hy3032 using 1 <;> norm_num
      exact Batch0035.cell0282.sound htau (by
        simp only [Batch0035.cell0282, Batch0035.tau0282, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs30323 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3032
