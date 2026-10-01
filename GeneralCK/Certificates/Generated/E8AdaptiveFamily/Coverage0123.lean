import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0006
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0007

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0123

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-1/8) (-9/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (-1/8 : ℝ) with hx0123 | hx0123
  · rcases le_total tau.im (-9/40 : ℝ) with hy0123 | hy0123
    · have hs01230 : InSquare (-11/80) (-19/80) (1/80) tau := by
        convert childLL hs hx0123 hy0123 using 1 <;> norm_num
      exact Batch0006.cell0054.sound htau (by
        simp only [Batch0006.cell0054, Batch0006.tau0054, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs01230 (by positivity) using 1 <;> norm_num)
    · have hs01232 : InSquare (-11/80) (-17/80) (1/80) tau := by
        convert childUL hs hx0123 hy0123 using 1 <;> norm_num
      exact Batch0007.cell0056.sound htau (by
        simp only [Batch0007.cell0056, Batch0007.tau0056, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs01232 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (-9/40 : ℝ) with hy0123 | hy0123
    · have hs01231 : InSquare (-9/80) (-19/80) (1/80) tau := by
        convert childLR hs hx0123 hy0123 using 1 <;> norm_num
      exact Batch0006.cell0055.sound htau (by
        simp only [Batch0006.cell0055, Batch0006.tau0055, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs01231 (by positivity) using 1 <;> norm_num)
    · have hs01233 : InSquare (-9/80) (-17/80) (1/80) tau := by
        convert childUR hs hx0123 hy0123 using 1 <;> norm_num
      exact Batch0007.cell0057.sound htau (by
        simp only [Batch0007.cell0057, Batch0007.tau0057, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs01233 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0123
