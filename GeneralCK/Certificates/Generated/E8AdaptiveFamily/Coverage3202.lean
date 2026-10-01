import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0041

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3202

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (1/40) (11/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (1/40 : ℝ) with hx3202 | hx3202
  · rcases le_total tau.im (11/40 : ℝ) with hy3202 | hy3202
    · have hs32020 : InSquare (1/80) (21/80) (1/80) tau := by
        convert childLL hs hx3202 hy3202 using 1 <;> norm_num
      exact Batch0041.cell0332.sound htau (by
        simp only [Batch0041.cell0332, Batch0041.tau0332, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs32020 (by positivity) using 1 <;> norm_num)
    · have hs32022 : InSquare (1/80) (23/80) (1/80) tau := by
        convert childUL hs hx3202 hy3202 using 1 <;> norm_num
      exact Batch0041.cell0334.sound htau (by
        simp only [Batch0041.cell0334, Batch0041.tau0334, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs32022 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (11/40 : ℝ) with hy3202 | hy3202
    · have hs32021 : InSquare (3/80) (21/80) (1/80) tau := by
        convert childLR hs hx3202 hy3202 using 1 <;> norm_num
      exact Batch0041.cell0333.sound htau (by
        simp only [Batch0041.cell0333, Batch0041.tau0333, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs32021 (by positivity) using 1 <;> norm_num)
    · have hs32023 : InSquare (3/80) (23/80) (1/80) tau := by
        convert childUR hs hx3202 hy3202 using 1 <;> norm_num
      exact Batch0041.cell0335.sound htau (by
        simp only [Batch0041.cell0335, Batch0041.tau0335, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs32023 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3202
