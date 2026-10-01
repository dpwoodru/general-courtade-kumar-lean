import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0034

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3031

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (7/40) (1/8) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (7/40 : ℝ) with hx3031 | hx3031
  · rcases le_total tau.im (1/8 : ℝ) with hy3031 | hy3031
    · have hs30310 : InSquare (13/80) (9/80) (1/80) tau := by
        convert childLL hs hx3031 hy3031 using 1 <;> norm_num
      exact Batch0034.cell0275.sound htau (by
        simp only [Batch0034.cell0275, Batch0034.tau0275, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs30310 (by positivity) using 1 <;> norm_num)
    · have hs30312 : InSquare (13/80) (11/80) (1/80) tau := by
        convert childUL hs hx3031 hy3031 using 1 <;> norm_num
      exact Batch0034.cell0277.sound htau (by
        simp only [Batch0034.cell0277, Batch0034.tau0277, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs30312 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (1/8 : ℝ) with hy3031 | hy3031
    · have hs30311 : InSquare (3/16) (9/80) (1/80) tau := by
        convert childLR hs hx3031 hy3031 using 1 <;> norm_num
      exact Batch0034.cell0276.sound htau (by
        simp only [Batch0034.cell0276, Batch0034.tau0276, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs30311 (by positivity) using 1 <;> norm_num)
    · have hs30313 : InSquare (3/16) (11/80) (1/80) tau := by
        convert childUR hs hx3031 hy3031 using 1 <;> norm_num
      exact Batch0034.cell0278.sound htau (by
        simp only [Batch0034.cell0278, Batch0034.tau0278, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs30313 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3031
