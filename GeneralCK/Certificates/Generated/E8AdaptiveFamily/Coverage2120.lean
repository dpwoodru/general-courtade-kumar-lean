import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0029

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2120

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-7/40) (1/8) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (-7/40 : ℝ) with hx2120 | hx2120
  · rcases le_total tau.im (1/8 : ℝ) with hy2120 | hy2120
    · have hs21200 : InSquare (-3/16) (9/80) (1/80) tau := by
        convert childLL hs hx2120 hy2120 using 1 <;> norm_num
      exact Batch0029.cell0235.sound htau (by
        simp only [Batch0029.cell0235, Batch0029.tau0235, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs21200 (by positivity) using 1 <;> norm_num)
    · have hs21202 : InSquare (-3/16) (11/80) (1/80) tau := by
        convert childUL hs hx2120 hy2120 using 1 <;> norm_num
      exact Batch0029.cell0237.sound htau (by
        simp only [Batch0029.cell0237, Batch0029.tau0237, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs21202 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (1/8 : ℝ) with hy2120 | hy2120
    · have hs21201 : InSquare (-13/80) (9/80) (1/80) tau := by
        convert childLR hs hx2120 hy2120 using 1 <;> norm_num
      exact Batch0029.cell0236.sound htau (by
        simp only [Batch0029.cell0236, Batch0029.tau0236, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs21201 (by positivity) using 1 <;> norm_num)
    · have hs21203 : InSquare (-13/80) (11/80) (1/80) tau := by
        convert childUR hs hx2120 hy2120 using 1 <;> norm_num
      exact Batch0029.cell0238.sound htau (by
        simp only [Batch0029.cell0238, Batch0029.tau0238, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs21203 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2120
