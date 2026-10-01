import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0030

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2123

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-1/8) (7/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (-1/8 : ℝ) with hx2123 | hx2123
  · rcases le_total tau.im (7/40 : ℝ) with hy2123 | hy2123
    · have hs21230 : InSquare (-11/80) (13/80) (1/80) tau := by
        convert childLL hs hx2123 hy2123 using 1 <;> norm_num
      exact Batch0030.cell0243.sound htau (by
        simp only [Batch0030.cell0243, Batch0030.tau0243, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs21230 (by positivity) using 1 <;> norm_num)
    · have hs21232 : InSquare (-11/80) (3/16) (1/80) tau := by
        convert childUL hs hx2123 hy2123 using 1 <;> norm_num
      exact Batch0030.cell0245.sound htau (by
        simp only [Batch0030.cell0245, Batch0030.tau0245, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs21232 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (7/40 : ℝ) with hy2123 | hy2123
    · have hs21231 : InSquare (-9/80) (13/80) (1/80) tau := by
        convert childLR hs hx2123 hy2123 using 1 <;> norm_num
      exact Batch0030.cell0244.sound htau (by
        simp only [Batch0030.cell0244, Batch0030.tau0244, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs21231 (by positivity) using 1 <;> norm_num)
    · have hs21233 : InSquare (-9/80) (3/16) (1/80) tau := by
        convert childUR hs hx2123 hy2123 using 1 <;> norm_num
      exact Batch0030.cell0246.sound htau (by
        simp only [Batch0030.cell0246, Batch0030.tau0246, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs21233 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2123
