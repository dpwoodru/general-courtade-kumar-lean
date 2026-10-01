import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0029
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0030

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2122

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-7/40) (7/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (-7/40 : ℝ) with hx2122 | hx2122
  · rcases le_total tau.im (7/40 : ℝ) with hy2122 | hy2122
    · have hs21220 : InSquare (-3/16) (13/80) (1/80) tau := by
        convert childLL hs hx2122 hy2122 using 1 <;> norm_num
      exact Batch0029.cell0239.sound htau (by
        simp only [Batch0029.cell0239, Batch0029.tau0239, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs21220 (by positivity) using 1 <;> norm_num)
    · have hs21222 : InSquare (-3/16) (3/16) (1/80) tau := by
        convert childUL hs hx2122 hy2122 using 1 <;> norm_num
      exact Batch0030.cell0241.sound htau (by
        simp only [Batch0030.cell0241, Batch0030.tau0241, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs21222 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (7/40 : ℝ) with hy2122 | hy2122
    · have hs21221 : InSquare (-13/80) (13/80) (1/80) tau := by
        convert childLR hs hx2122 hy2122 using 1 <;> norm_num
      exact Batch0030.cell0240.sound htau (by
        simp only [Batch0030.cell0240, Batch0030.tau0240, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs21221 (by positivity) using 1 <;> norm_num)
    · have hs21223 : InSquare (-13/80) (3/16) (1/80) tau := by
        convert childUR hs hx2122 hy2122 using 1 <;> norm_num
      exact Batch0030.cell0242.sound htau (by
        simp only [Batch0030.cell0242, Batch0030.tau0242, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs21223 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2122
