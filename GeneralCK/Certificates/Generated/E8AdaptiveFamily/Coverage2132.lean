import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0030
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0031

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2132

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-3/40) (7/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (-3/40 : ℝ) with hx2132 | hx2132
  · rcases le_total tau.im (7/40 : ℝ) with hy2132 | hy2132
    · have hs21320 : InSquare (-7/80) (13/80) (1/80) tau := by
        convert childLL hs hx2132 hy2132 using 1 <;> norm_num
      exact Batch0030.cell0247.sound htau (by
        simp only [Batch0030.cell0247, Batch0030.tau0247, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs21320 (by positivity) using 1 <;> norm_num)
    · have hs21322 : InSquare (-7/80) (3/16) (1/80) tau := by
        convert childUL hs hx2132 hy2132 using 1 <;> norm_num
      exact Batch0031.cell0249.sound htau (by
        simp only [Batch0031.cell0249, Batch0031.tau0249, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs21322 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (7/40 : ℝ) with hy2132 | hy2132
    · have hs21321 : InSquare (-1/16) (13/80) (1/80) tau := by
        convert childLR hs hx2132 hy2132 using 1 <;> norm_num
      exact Batch0031.cell0248.sound htau (by
        simp only [Batch0031.cell0248, Batch0031.tau0248, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs21321 (by positivity) using 1 <;> norm_num)
    · have hs21323 : InSquare (-1/16) (3/16) (1/80) tau := by
        convert childUR hs hx2132 hy2132 using 1 <;> norm_num
      exact Batch0031.cell0250.sound htau (by
        simp only [Batch0031.cell0250, Batch0031.tau0250, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs21323 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2132
