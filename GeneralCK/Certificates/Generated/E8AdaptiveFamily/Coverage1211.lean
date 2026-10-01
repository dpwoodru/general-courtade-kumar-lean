import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0019

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1211

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (7/40) (-7/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (7/40 : ℝ) with hx1211 | hx1211
  · rcases le_total tau.im (-7/40 : ℝ) with hy1211 | hy1211
    · have hs12110 : InSquare (13/80) (-3/16) (1/80) tau := by
        convert childLL hs hx1211 hy1211 using 1 <;> norm_num
      exact Batch0019.cell0153.sound htau (by
        simp only [Batch0019.cell0153, Batch0019.tau0153, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs12110 (by positivity) using 1 <;> norm_num)
    · have hs12112 : InSquare (13/80) (-13/80) (1/80) tau := by
        convert childUL hs hx1211 hy1211 using 1 <;> norm_num
      exact Batch0019.cell0155.sound htau (by
        simp only [Batch0019.cell0155, Batch0019.tau0155, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs12112 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (-7/40 : ℝ) with hy1211 | hy1211
    · have hs12111 : InSquare (3/16) (-3/16) (1/80) tau := by
        convert childLR hs hx1211 hy1211 using 1 <;> norm_num
      exact Batch0019.cell0154.sound htau (by
        simp only [Batch0019.cell0154, Batch0019.tau0154, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs12111 (by positivity) using 1 <;> norm_num)
    · have hs12113 : InSquare (3/16) (-13/80) (1/80) tau := by
        convert childUR hs hx1211 hy1211 using 1 <;> norm_num
      exact Batch0019.cell0156.sound htau (by
        simp only [Batch0019.cell0156, Batch0019.tau0156, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs12113 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1211
