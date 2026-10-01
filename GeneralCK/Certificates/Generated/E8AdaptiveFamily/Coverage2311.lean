import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0032
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0033

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2311

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-1/40) (9/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (-1/40 : ℝ) with hx2311 | hx2311
  · rcases le_total tau.im (9/40 : ℝ) with hy2311 | hy2311
    · have hs23110 : InSquare (-3/80) (17/80) (1/80) tau := by
        convert childLL hs hx2311 hy2311 using 1 <;> norm_num
      exact Batch0032.cell0261.sound htau (by
        simp only [Batch0032.cell0261, Batch0032.tau0261, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs23110 (by positivity) using 1 <;> norm_num)
    · have hs23112 : InSquare (-3/80) (19/80) (1/80) tau := by
        convert childUL hs hx2311 hy2311 using 1 <;> norm_num
      exact Batch0032.cell0263.sound htau (by
        simp only [Batch0032.cell0263, Batch0032.tau0263, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs23112 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (9/40 : ℝ) with hy2311 | hy2311
    · have hs23111 : InSquare (-1/80) (17/80) (1/80) tau := by
        convert childLR hs hx2311 hy2311 using 1 <;> norm_num
      exact Batch0032.cell0262.sound htau (by
        simp only [Batch0032.cell0262, Batch0032.tau0262, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs23111 (by positivity) using 1 <;> norm_num)
    · have hs23113 : InSquare (-1/80) (19/80) (1/80) tau := by
        convert childUR hs hx2311 hy2311 using 1 <;> norm_num
      exact Batch0033.cell0264.sound htau (by
        simp only [Batch0033.cell0264, Batch0033.tau0264, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs23113 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2311
