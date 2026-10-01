import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0014
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0015

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0302

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-7/40) (-1/8) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (-7/40 : ℝ) with hx0302 | hx0302
  · rcases le_total tau.im (-1/8 : ℝ) with hy0302 | hy0302
    · have hs03020 : InSquare (-3/16) (-11/80) (1/80) tau := by
        convert childLL hs hx0302 hy0302 using 1 <;> norm_num
      exact Batch0014.cell0117.sound htau (by
        simp only [Batch0014.cell0117, Batch0014.tau0117, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs03020 (by positivity) using 1 <;> norm_num)
    · have hs03022 : InSquare (-3/16) (-9/80) (1/80) tau := by
        convert childUL hs hx0302 hy0302 using 1 <;> norm_num
      exact Batch0014.cell0119.sound htau (by
        simp only [Batch0014.cell0119, Batch0014.tau0119, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs03022 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (-1/8 : ℝ) with hy0302 | hy0302
    · have hs03021 : InSquare (-13/80) (-11/80) (1/80) tau := by
        convert childLR hs hx0302 hy0302 using 1 <;> norm_num
      exact Batch0014.cell0118.sound htau (by
        simp only [Batch0014.cell0118, Batch0014.tau0118, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs03021 (by positivity) using 1 <;> norm_num)
    · have hs03023 : InSquare (-13/80) (-9/80) (1/80) tau := by
        convert childUR hs hx0302 hy0302 using 1 <;> norm_num
      exact Batch0015.cell0120.sound htau (by
        simp only [Batch0015.cell0120, Batch0015.tau0120, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs03023 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0302
