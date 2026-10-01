import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0041

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3201

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (3/40) (9/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (3/40 : ℝ) with hx3201 | hx3201
  · rcases le_total tau.im (9/40 : ℝ) with hy3201 | hy3201
    · have hs32010 : InSquare (1/16) (17/80) (1/80) tau := by
        convert childLL hs hx3201 hy3201 using 1 <;> norm_num
      exact Batch0041.cell0328.sound htau (by
        simp only [Batch0041.cell0328, Batch0041.tau0328, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs32010 (by positivity) using 1 <;> norm_num)
    · have hs32012 : InSquare (1/16) (19/80) (1/80) tau := by
        convert childUL hs hx3201 hy3201 using 1 <;> norm_num
      exact Batch0041.cell0330.sound htau (by
        simp only [Batch0041.cell0330, Batch0041.tau0330, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs32012 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (9/40 : ℝ) with hy3201 | hy3201
    · have hs32011 : InSquare (7/80) (17/80) (1/80) tau := by
        convert childLR hs hx3201 hy3201 using 1 <;> norm_num
      exact Batch0041.cell0329.sound htau (by
        simp only [Batch0041.cell0329, Batch0041.tau0329, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs32011 (by positivity) using 1 <;> norm_num)
    · have hs32013 : InSquare (7/80) (19/80) (1/80) tau := by
        convert childUR hs hx3201 hy3201 using 1 <;> norm_num
      exact Batch0041.cell0331.sound htau (by
        simp only [Batch0041.cell0331, Batch0041.tau0331, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs32013 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3201
