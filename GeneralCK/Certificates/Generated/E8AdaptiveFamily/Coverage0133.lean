import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0008

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0133

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-1/40) (-9/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (-1/40 : ℝ) with hx0133 | hx0133
  · rcases le_total tau.im (-9/40 : ℝ) with hy0133 | hy0133
    · have hs01330 : InSquare (-3/80) (-19/80) (1/80) tau := by
        convert childLL hs hx0133 hy0133 using 1 <;> norm_num
      exact Batch0008.cell0068.sound htau (by
        simp only [Batch0008.cell0068, Batch0008.tau0068, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs01330 (by positivity) using 1 <;> norm_num)
    · have hs01332 : InSquare (-3/80) (-17/80) (1/80) tau := by
        convert childUL hs hx0133 hy0133 using 1 <;> norm_num
      exact Batch0008.cell0070.sound htau (by
        simp only [Batch0008.cell0070, Batch0008.tau0070, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs01332 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (-9/40 : ℝ) with hy0133 | hy0133
    · have hs01331 : InSquare (-1/80) (-19/80) (1/80) tau := by
        convert childLR hs hx0133 hy0133 using 1 <;> norm_num
      exact Batch0008.cell0069.sound htau (by
        simp only [Batch0008.cell0069, Batch0008.tau0069, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs01331 (by positivity) using 1 <;> norm_num)
    · have hs01333 : InSquare (-1/80) (-17/80) (1/80) tau := by
        convert childUR hs hx0133 hy0133 using 1 <;> norm_num
      exact Batch0008.cell0071.sound htau (by
        simp only [Batch0008.cell0071, Batch0008.tau0071, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs01333 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0133
