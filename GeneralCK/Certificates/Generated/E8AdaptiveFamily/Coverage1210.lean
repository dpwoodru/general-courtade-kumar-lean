import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0018
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0019

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1210

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (1/8) (-7/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (1/8 : ℝ) with hx1210 | hx1210
  · rcases le_total tau.im (-7/40 : ℝ) with hy1210 | hy1210
    · have hs12100 : InSquare (9/80) (-3/16) (1/80) tau := by
        convert childLL hs hx1210 hy1210 using 1 <;> norm_num
      exact Batch0018.cell0149.sound htau (by
        simp only [Batch0018.cell0149, Batch0018.tau0149, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs12100 (by positivity) using 1 <;> norm_num)
    · have hs12102 : InSquare (9/80) (-13/80) (1/80) tau := by
        convert childUL hs hx1210 hy1210 using 1 <;> norm_num
      exact Batch0018.cell0151.sound htau (by
        simp only [Batch0018.cell0151, Batch0018.tau0151, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs12102 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (-7/40 : ℝ) with hy1210 | hy1210
    · have hs12101 : InSquare (11/80) (-3/16) (1/80) tau := by
        convert childLR hs hx1210 hy1210 using 1 <;> norm_num
      exact Batch0018.cell0150.sound htau (by
        simp only [Batch0018.cell0150, Batch0018.tau0150, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs12101 (by positivity) using 1 <;> norm_num)
    · have hs12103 : InSquare (11/80) (-13/80) (1/80) tau := by
        convert childUR hs hx1210 hy1210 using 1 <;> norm_num
      exact Batch0019.cell0152.sound htau (by
        simp only [Batch0019.cell0152, Batch0019.tau0152, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs12103 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1210
