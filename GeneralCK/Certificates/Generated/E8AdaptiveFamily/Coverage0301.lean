import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0014

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0301

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-1/8) (-7/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (-1/8 : ℝ) with hx0301 | hx0301
  · rcases le_total tau.im (-7/40 : ℝ) with hy0301 | hy0301
    · have hs03010 : InSquare (-11/80) (-3/16) (1/80) tau := by
        convert childLL hs hx0301 hy0301 using 1 <;> norm_num
      exact Batch0014.cell0113.sound htau (by
        simp only [Batch0014.cell0113, Batch0014.tau0113, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs03010 (by positivity) using 1 <;> norm_num)
    · have hs03012 : InSquare (-11/80) (-13/80) (1/80) tau := by
        convert childUL hs hx0301 hy0301 using 1 <;> norm_num
      exact Batch0014.cell0115.sound htau (by
        simp only [Batch0014.cell0115, Batch0014.tau0115, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs03012 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (-7/40 : ℝ) with hy0301 | hy0301
    · have hs03011 : InSquare (-9/80) (-3/16) (1/80) tau := by
        convert childLR hs hx0301 hy0301 using 1 <;> norm_num
      exact Batch0014.cell0114.sound htau (by
        simp only [Batch0014.cell0114, Batch0014.tau0114, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs03011 (by positivity) using 1 <;> norm_num)
    · have hs03013 : InSquare (-9/80) (-13/80) (1/80) tau := by
        convert childUR hs hx0301 hy0301 using 1 <;> norm_num
      exact Batch0014.cell0116.sound htau (by
        simp only [Batch0014.cell0116, Batch0014.tau0116, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs03013 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0301
