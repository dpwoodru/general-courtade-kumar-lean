import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0008

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0132

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-3/40) (-9/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (-3/40 : ℝ) with hx0132 | hx0132
  · rcases le_total tau.im (-9/40 : ℝ) with hy0132 | hy0132
    · have hs01320 : InSquare (-7/80) (-19/80) (1/80) tau := by
        convert childLL hs hx0132 hy0132 using 1 <;> norm_num
      exact Batch0008.cell0064.sound htau (by
        simp only [Batch0008.cell0064, Batch0008.tau0064, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs01320 (by positivity) using 1 <;> norm_num)
    · have hs01322 : InSquare (-7/80) (-17/80) (1/80) tau := by
        convert childUL hs hx0132 hy0132 using 1 <;> norm_num
      exact Batch0008.cell0066.sound htau (by
        simp only [Batch0008.cell0066, Batch0008.tau0066, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs01322 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (-9/40 : ℝ) with hy0132 | hy0132
    · have hs01321 : InSquare (-1/16) (-19/80) (1/80) tau := by
        convert childLR hs hx0132 hy0132 using 1 <;> norm_num
      exact Batch0008.cell0065.sound htau (by
        simp only [Batch0008.cell0065, Batch0008.tau0065, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs01321 (by positivity) using 1 <;> norm_num)
    · have hs01323 : InSquare (-1/16) (-17/80) (1/80) tau := by
        convert childUR hs hx0132 hy0132 using 1 <;> norm_num
      exact Batch0008.cell0067.sound htau (by
        simp only [Batch0008.cell0067, Batch0008.tau0067, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs01323 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0132
