import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0026
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0027

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2012

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-11/40) (3/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (-11/40 : ℝ) with hx2012 | hx2012
  · rcases le_total tau.im (3/40 : ℝ) with hy2012 | hy2012
    · have hs20120 : InSquare (-23/80) (1/16) (1/80) tau := by
        convert childLL hs hx2012 hy2012 using 1 <;> norm_num
      exact Batch0026.cell0214.sound htau (by
        simp only [Batch0026.cell0214, Batch0026.tau0214, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs20120 (by positivity) using 1 <;> norm_num)
    · have hs20122 : InSquare (-23/80) (7/80) (1/80) tau := by
        convert childUL hs hx2012 hy2012 using 1 <;> norm_num
      exact Batch0027.cell0216.sound htau (by
        simp only [Batch0027.cell0216, Batch0027.tau0216, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs20122 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (3/40 : ℝ) with hy2012 | hy2012
    · have hs20121 : InSquare (-21/80) (1/16) (1/80) tau := by
        convert childLR hs hx2012 hy2012 using 1 <;> norm_num
      exact Batch0026.cell0215.sound htau (by
        simp only [Batch0026.cell0215, Batch0026.tau0215, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs20121 (by positivity) using 1 <;> norm_num)
    · have hs20123 : InSquare (-21/80) (7/80) (1/80) tau := by
        convert childUR hs hx2012 hy2012 using 1 <;> norm_num
      exact Batch0027.cell0217.sound htau (by
        simp only [Batch0027.cell0217, Batch0027.tau0217, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs20123 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2012
