import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0042

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3210

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (1/8) (9/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (1/8 : ℝ) with hx3210 | hx3210
  · rcases le_total tau.im (9/40 : ℝ) with hy3210 | hy3210
    · have hs32100 : InSquare (9/80) (17/80) (1/80) tau := by
        convert childLL hs hx3210 hy3210 using 1 <;> norm_num
      exact Batch0042.cell0338.sound htau (by
        simp only [Batch0042.cell0338, Batch0042.tau0338, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs32100 (by positivity) using 1 <;> norm_num)
    · have hs32102 : InSquare (9/80) (19/80) (1/80) tau := by
        convert childUL hs hx3210 hy3210 using 1 <;> norm_num
      exact Batch0042.cell0340.sound htau (by
        simp only [Batch0042.cell0340, Batch0042.tau0340, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs32102 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (9/40 : ℝ) with hy3210 | hy3210
    · have hs32101 : InSquare (11/80) (17/80) (1/80) tau := by
        convert childLR hs hx3210 hy3210 using 1 <;> norm_num
      exact Batch0042.cell0339.sound htau (by
        simp only [Batch0042.cell0339, Batch0042.tau0339, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs32101 (by positivity) using 1 <;> norm_num)
    · have hs32103 : InSquare (11/80) (19/80) (1/80) tau := by
        convert childUR hs hx3210 hy3210 using 1 <;> norm_num
      exact Batch0042.cell0341.sound htau (by
        simp only [Batch0042.cell0341, Batch0042.tau0341, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs32103 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3210
