import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0026

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2010

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-11/40) (1/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (-11/40 : ℝ) with hx2010 | hx2010
  · rcases le_total tau.im (1/40 : ℝ) with hy2010 | hy2010
    · have hs20100 : InSquare (-23/80) (1/80) (1/80) tau := by
        convert childLL hs hx2010 hy2010 using 1 <;> norm_num
      exact Batch0026.cell0210.sound htau (by
        simp only [Batch0026.cell0210, Batch0026.tau0210, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs20100 (by positivity) using 1 <;> norm_num)
    · have hs20102 : InSquare (-23/80) (3/80) (1/80) tau := by
        convert childUL hs hx2010 hy2010 using 1 <;> norm_num
      exact Batch0026.cell0212.sound htau (by
        simp only [Batch0026.cell0212, Batch0026.tau0212, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs20102 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (1/40 : ℝ) with hy2010 | hy2010
    · have hs20101 : InSquare (-21/80) (1/80) (1/80) tau := by
        convert childLR hs hx2010 hy2010 using 1 <;> norm_num
      exact Batch0026.cell0211.sound htau (by
        simp only [Batch0026.cell0211, Batch0026.tau0211, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs20101 (by positivity) using 1 <;> norm_num)
    · have hs20103 : InSquare (-21/80) (3/80) (1/80) tau := by
        convert childUR hs hx2010 hy2010 using 1 <;> norm_num
      exact Batch0026.cell0213.sound htau (by
        simp only [Batch0026.cell0213, Batch0026.tau0213, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs20103 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2010
