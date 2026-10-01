import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0027

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2013

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-9/40) (3/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (-9/40 : ℝ) with hx2013 | hx2013
  · rcases le_total tau.im (3/40 : ℝ) with hy2013 | hy2013
    · have hs20130 : InSquare (-19/80) (1/16) (1/80) tau := by
        convert childLL hs hx2013 hy2013 using 1 <;> norm_num
      exact Batch0027.cell0218.sound htau (by
        simp only [Batch0027.cell0218, Batch0027.tau0218, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs20130 (by positivity) using 1 <;> norm_num)
    · have hs20132 : InSquare (-19/80) (7/80) (1/80) tau := by
        convert childUL hs hx2013 hy2013 using 1 <;> norm_num
      exact Batch0027.cell0220.sound htau (by
        simp only [Batch0027.cell0220, Batch0027.tau0220, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs20132 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (3/40 : ℝ) with hy2013 | hy2013
    · have hs20131 : InSquare (-17/80) (1/16) (1/80) tau := by
        convert childLR hs hx2013 hy2013 using 1 <;> norm_num
      exact Batch0027.cell0219.sound htau (by
        simp only [Batch0027.cell0219, Batch0027.tau0219, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs20131 (by positivity) using 1 <;> norm_num)
    · have hs20133 : InSquare (-17/80) (7/80) (1/80) tau := by
        convert childUR hs hx2013 hy2013 using 1 <;> norm_num
      exact Batch0027.cell0221.sound htau (by
        simp only [Batch0027.cell0221, Batch0027.tau0221, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs20133 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2013
