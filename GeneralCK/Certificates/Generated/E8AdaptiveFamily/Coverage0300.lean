import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0013
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0014

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0300

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-7/40) (-7/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (-7/40 : ℝ) with hx0300 | hx0300
  · rcases le_total tau.im (-7/40 : ℝ) with hy0300 | hy0300
    · have hs03000 : InSquare (-3/16) (-3/16) (1/80) tau := by
        convert childLL hs hx0300 hy0300 using 1 <;> norm_num
      exact Batch0013.cell0109.sound htau (by
        simp only [Batch0013.cell0109, Batch0013.tau0109, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs03000 (by positivity) using 1 <;> norm_num)
    · have hs03002 : InSquare (-3/16) (-13/80) (1/80) tau := by
        convert childUL hs hx0300 hy0300 using 1 <;> norm_num
      exact Batch0013.cell0111.sound htau (by
        simp only [Batch0013.cell0111, Batch0013.tau0111, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs03002 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (-7/40 : ℝ) with hy0300 | hy0300
    · have hs03001 : InSquare (-13/80) (-3/16) (1/80) tau := by
        convert childLR hs hx0300 hy0300 using 1 <;> norm_num
      exact Batch0013.cell0110.sound htau (by
        simp only [Batch0013.cell0110, Batch0013.tau0110, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs03001 (by positivity) using 1 <;> norm_num)
    · have hs03003 : InSquare (-13/80) (-13/80) (1/80) tau := by
        convert childUR hs hx0300 hy0300 using 1 <;> norm_num
      exact Batch0014.cell0112.sound htau (by
        simp only [Batch0014.cell0112, Batch0014.tau0112, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs03003 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0300
