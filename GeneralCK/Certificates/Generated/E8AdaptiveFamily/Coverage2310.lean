import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0032

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2310

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-3/40) (9/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (-3/40 : ℝ) with hx2310 | hx2310
  · rcases le_total tau.im (9/40 : ℝ) with hy2310 | hy2310
    · have hs23100 : InSquare (-7/80) (17/80) (1/80) tau := by
        convert childLL hs hx2310 hy2310 using 1 <;> norm_num
      exact Batch0032.cell0257.sound htau (by
        simp only [Batch0032.cell0257, Batch0032.tau0257, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs23100 (by positivity) using 1 <;> norm_num)
    · have hs23102 : InSquare (-7/80) (19/80) (1/80) tau := by
        convert childUL hs hx2310 hy2310 using 1 <;> norm_num
      exact Batch0032.cell0259.sound htau (by
        simp only [Batch0032.cell0259, Batch0032.tau0259, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs23102 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (9/40 : ℝ) with hy2310 | hy2310
    · have hs23101 : InSquare (-1/16) (17/80) (1/80) tau := by
        convert childLR hs hx2310 hy2310 using 1 <;> norm_num
      exact Batch0032.cell0258.sound htau (by
        simp only [Batch0032.cell0258, Batch0032.tau0258, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs23101 (by positivity) using 1 <;> norm_num)
    · have hs23103 : InSquare (-1/16) (19/80) (1/80) tau := by
        convert childUR hs hx2310 hy2310 using 1 <;> norm_num
      exact Batch0032.cell0260.sound htau (by
        simp only [Batch0032.cell0260, Batch0032.tau0260, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs23103 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2310
