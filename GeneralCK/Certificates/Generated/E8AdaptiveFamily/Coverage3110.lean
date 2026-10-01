import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0037

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3110

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (13/40) (1/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (13/40 : ℝ) with hx3110 | hx3110
  · rcases le_total tau.im (1/40 : ℝ) with hy3110 | hy3110
    · have hs31100 : InSquare (5/16) (1/80) (1/80) tau := by
        convert childLL hs hx3110 hy3110 using 1 <;> norm_num
      exact Batch0037.cell0299.sound htau (by
        simp only [Batch0037.cell0299, Batch0037.tau0299, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs31100 (by positivity) using 1 <;> norm_num)
    · have hs31102 : InSquare (5/16) (3/80) (1/80) tau := by
        convert childUL hs hx3110 hy3110 using 1 <;> norm_num
      exact Batch0037.cell0301.sound htau (by
        simp only [Batch0037.cell0301, Batch0037.tau0301, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs31102 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (1/40 : ℝ) with hy3110 | hy3110
    · have hs31101 : InSquare (27/80) (1/80) (1/80) tau := by
        convert childLR hs hx3110 hy3110 using 1 <;> norm_num
      exact Batch0037.cell0300.sound htau (by
        simp only [Batch0037.cell0300, Batch0037.tau0300, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs31101 (by positivity) using 1 <;> norm_num)
    · have hs31103 : InSquare (27/80) (3/80) (1/80) tau := by
        convert childUR hs hx3110 hy3110 using 1 <;> norm_num
      exact Batch0037.cell0302.sound htau (by
        simp only [Batch0037.cell0302, Batch0037.tau0302, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs31103 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3110
