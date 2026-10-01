import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0031
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0032

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2301

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-1/8) (9/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (-1/8 : ℝ) with hx2301 | hx2301
  · rcases le_total tau.im (9/40 : ℝ) with hy2301 | hy2301
    · have hs23010 : InSquare (-11/80) (17/80) (1/80) tau := by
        convert childLL hs hx2301 hy2301 using 1 <;> norm_num
      exact Batch0031.cell0253.sound htau (by
        simp only [Batch0031.cell0253, Batch0031.tau0253, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs23010 (by positivity) using 1 <;> norm_num)
    · have hs23012 : InSquare (-11/80) (19/80) (1/80) tau := by
        convert childUL hs hx2301 hy2301 using 1 <;> norm_num
      exact Batch0031.cell0255.sound htau (by
        simp only [Batch0031.cell0255, Batch0031.tau0255, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs23012 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (9/40 : ℝ) with hy2301 | hy2301
    · have hs23011 : InSquare (-9/80) (17/80) (1/80) tau := by
        convert childLR hs hx2301 hy2301 using 1 <;> norm_num
      exact Batch0031.cell0254.sound htau (by
        simp only [Batch0031.cell0254, Batch0031.tau0254, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs23011 (by positivity) using 1 <;> norm_num)
    · have hs23013 : InSquare (-9/80) (19/80) (1/80) tau := by
        convert childUR hs hx2301 hy2301 using 1 <;> norm_num
      exact Batch0032.cell0256.sound htau (by
        simp only [Batch0032.cell0256, Batch0032.tau0256, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs23013 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2301
