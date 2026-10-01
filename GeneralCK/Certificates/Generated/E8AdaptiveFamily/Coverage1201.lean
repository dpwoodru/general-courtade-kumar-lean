import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0018

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1201

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (3/40) (-7/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (3/40 : ℝ) with hx1201 | hx1201
  · rcases le_total tau.im (-7/40 : ℝ) with hy1201 | hy1201
    · have hs12010 : InSquare (1/16) (-3/16) (1/80) tau := by
        convert childLL hs hx1201 hy1201 using 1 <;> norm_num
      exact Batch0018.cell0145.sound htau (by
        simp only [Batch0018.cell0145, Batch0018.tau0145, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs12010 (by positivity) using 1 <;> norm_num)
    · have hs12012 : InSquare (1/16) (-13/80) (1/80) tau := by
        convert childUL hs hx1201 hy1201 using 1 <;> norm_num
      exact Batch0018.cell0147.sound htau (by
        simp only [Batch0018.cell0147, Batch0018.tau0147, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs12012 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (-7/40 : ℝ) with hy1201 | hy1201
    · have hs12011 : InSquare (7/80) (-3/16) (1/80) tau := by
        convert childLR hs hx1201 hy1201 using 1 <;> norm_num
      exact Batch0018.cell0146.sound htau (by
        simp only [Batch0018.cell0146, Batch0018.tau0146, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs12011 (by positivity) using 1 <;> norm_num)
    · have hs12013 : InSquare (7/80) (-13/80) (1/80) tau := by
        convert childUR hs hx1201 hy1201 using 1 <;> norm_num
      exact Batch0018.cell0148.sound htau (by
        simp only [Batch0018.cell0148, Batch0018.tau0148, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs12013 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1201
