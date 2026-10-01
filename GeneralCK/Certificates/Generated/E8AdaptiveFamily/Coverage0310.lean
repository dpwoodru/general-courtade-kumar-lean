import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0015

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0310

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-3/40) (-7/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (-3/40 : ℝ) with hx0310 | hx0310
  · rcases le_total tau.im (-7/40 : ℝ) with hy0310 | hy0310
    · have hs03100 : InSquare (-7/80) (-3/16) (1/80) tau := by
        convert childLL hs hx0310 hy0310 using 1 <;> norm_num
      exact Batch0015.cell0121.sound htau (by
        simp only [Batch0015.cell0121, Batch0015.tau0121, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs03100 (by positivity) using 1 <;> norm_num)
    · have hs03102 : InSquare (-7/80) (-13/80) (1/80) tau := by
        convert childUL hs hx0310 hy0310 using 1 <;> norm_num
      exact Batch0015.cell0123.sound htau (by
        simp only [Batch0015.cell0123, Batch0015.tau0123, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs03102 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (-7/40 : ℝ) with hy0310 | hy0310
    · have hs03101 : InSquare (-1/16) (-3/16) (1/80) tau := by
        convert childLR hs hx0310 hy0310 using 1 <;> norm_num
      exact Batch0015.cell0122.sound htau (by
        simp only [Batch0015.cell0122, Batch0015.tau0122, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs03101 (by positivity) using 1 <;> norm_num)
    · have hs03103 : InSquare (-1/16) (-13/80) (1/80) tau := by
        convert childUR hs hx0310 hy0310 using 1 <;> norm_num
      exact Batch0015.cell0124.sound htau (by
        simp only [Batch0015.cell0124, Batch0015.tau0124, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs03103 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0310
