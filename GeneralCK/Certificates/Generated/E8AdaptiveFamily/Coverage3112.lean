import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0038

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3112

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (13/40) (3/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (13/40 : ℝ) with hx3112 | hx3112
  · rcases le_total tau.im (3/40 : ℝ) with hy3112 | hy3112
    · have hs31120 : InSquare (5/16) (1/16) (1/80) tau := by
        convert childLL hs hx3112 hy3112 using 1 <;> norm_num
      exact Batch0038.cell0306.sound htau (by
        simp only [Batch0038.cell0306, Batch0038.tau0306, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs31120 (by positivity) using 1 <;> norm_num)
    · have hs31122 : InSquare (5/16) (7/80) (1/80) tau := by
        convert childUL hs hx3112 hy3112 using 1 <;> norm_num
      exact Batch0038.cell0308.sound htau (by
        simp only [Batch0038.cell0308, Batch0038.tau0308, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs31122 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (3/40 : ℝ) with hy3112 | hy3112
    · have hs31121 : InSquare (27/80) (1/16) (1/80) tau := by
        convert childLR hs hx3112 hy3112 using 1 <;> norm_num
      exact Batch0038.cell0307.sound htau (by
        simp only [Batch0038.cell0307, Batch0038.tau0307, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs31121 (by positivity) using 1 <;> norm_num)
    · have hs31123 : InSquare (27/80) (7/80) (1/80) tau := by
        convert childUR hs hx3112 hy3112 using 1 <;> norm_num
      exact Batch0038.cell0309.sound htau (by
        simp only [Batch0038.cell0309, Batch0038.tau0309, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs31123 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3112
