import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0033

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2313

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-1/40) (11/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (-1/40 : ℝ) with hx2313 | hx2313
  · rcases le_total tau.im (11/40 : ℝ) with hy2313 | hy2313
    · have hs23130 : InSquare (-3/80) (21/80) (1/80) tau := by
        convert childLL hs hx2313 hy2313 using 1 <;> norm_num
      exact Batch0033.cell0267.sound htau (by
        simp only [Batch0033.cell0267, Batch0033.tau0267, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs23130 (by positivity) using 1 <;> norm_num)
    · have hs23132 : InSquare (-3/80) (23/80) (1/80) tau := by
        convert childUL hs hx2313 hy2313 using 1 <;> norm_num
      exact Batch0033.cell0269.sound htau (by
        simp only [Batch0033.cell0269, Batch0033.tau0269, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs23132 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (11/40 : ℝ) with hy2313 | hy2313
    · have hs23131 : InSquare (-1/80) (21/80) (1/80) tau := by
        convert childLR hs hx2313 hy2313 using 1 <;> norm_num
      exact Batch0033.cell0268.sound htau (by
        simp only [Batch0033.cell0268, Batch0033.tau0268, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs23131 (by positivity) using 1 <;> norm_num)
    · have hs23133 : InSquare (-1/80) (23/80) (1/80) tau := by
        convert childUR hs hx2313 hy2313 using 1 <;> norm_num
      exact Batch0033.cell0270.sound htau (by
        simp only [Batch0033.cell0270, Batch0033.tau0270, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs23133 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2313
