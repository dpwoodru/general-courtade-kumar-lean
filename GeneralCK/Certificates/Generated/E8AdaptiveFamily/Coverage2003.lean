import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0025
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0026

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2003

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-13/40) (3/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (-13/40 : ℝ) with hx2003 | hx2003
  · rcases le_total tau.im (3/40 : ℝ) with hy2003 | hy2003
    · have hs20030 : InSquare (-27/80) (1/16) (1/80) tau := by
        convert childLL hs hx2003 hy2003 using 1 <;> norm_num
      exact Batch0025.cell0206.sound htau (by
        simp only [Batch0025.cell0206, Batch0025.tau0206, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs20030 (by positivity) using 1 <;> norm_num)
    · have hs20032 : InSquare (-27/80) (7/80) (1/80) tau := by
        convert childUL hs hx2003 hy2003 using 1 <;> norm_num
      exact Batch0026.cell0208.sound htau (by
        simp only [Batch0026.cell0208, Batch0026.tau0208, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs20032 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (3/40 : ℝ) with hy2003 | hy2003
    · have hs20031 : InSquare (-5/16) (1/16) (1/80) tau := by
        convert childLR hs hx2003 hy2003 using 1 <;> norm_num
      exact Batch0025.cell0207.sound htau (by
        simp only [Batch0025.cell0207, Batch0025.tau0207, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs20031 (by positivity) using 1 <;> norm_num)
    · have hs20033 : InSquare (-5/16) (7/80) (1/80) tau := by
        convert childUR hs hx2003 hy2003 using 1 <;> norm_num
      exact Batch0026.cell0209.sound htau (by
        simp only [Batch0026.cell0209, Batch0026.tau0209, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs20033 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2003
