import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0040

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3200

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (1/40) (9/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (1/40 : ℝ) with hx3200 | hx3200
  · rcases le_total tau.im (9/40 : ℝ) with hy3200 | hy3200
    · have hs32000 : InSquare (1/80) (17/80) (1/80) tau := by
        convert childLL hs hx3200 hy3200 using 1 <;> norm_num
      exact Batch0040.cell0324.sound htau (by
        simp only [Batch0040.cell0324, Batch0040.tau0324, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs32000 (by positivity) using 1 <;> norm_num)
    · have hs32002 : InSquare (1/80) (19/80) (1/80) tau := by
        convert childUL hs hx3200 hy3200 using 1 <;> norm_num
      exact Batch0040.cell0326.sound htau (by
        simp only [Batch0040.cell0326, Batch0040.tau0326, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs32002 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (9/40 : ℝ) with hy3200 | hy3200
    · have hs32001 : InSquare (3/80) (17/80) (1/80) tau := by
        convert childLR hs hx3200 hy3200 using 1 <;> norm_num
      exact Batch0040.cell0325.sound htau (by
        simp only [Batch0040.cell0325, Batch0040.tau0325, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs32001 (by positivity) using 1 <;> norm_num)
    · have hs32003 : InSquare (3/80) (19/80) (1/80) tau := by
        convert childUR hs hx3200 hy3200 using 1 <;> norm_num
      exact Batch0040.cell0327.sound htau (by
        simp only [Batch0040.cell0327, Batch0040.tau0327, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs32003 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3200
