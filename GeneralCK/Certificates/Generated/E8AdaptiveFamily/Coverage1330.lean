import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0023

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1330

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (13/40) (-3/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (13/40 : ℝ) with hx1330 | hx1330
  · rcases le_total tau.im (-3/40 : ℝ) with hy1330 | hy1330
    · have hs13300 : InSquare (5/16) (-7/80) (1/80) tau := by
        convert childLL hs hx1330 hy1330 using 1 <;> norm_num
      exact Batch0023.cell0186.sound htau (by
        simp only [Batch0023.cell0186, Batch0023.tau0186, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs13300 (by positivity) using 1 <;> norm_num)
    · have hs13302 : InSquare (5/16) (-1/16) (1/80) tau := by
        convert childUL hs hx1330 hy1330 using 1 <;> norm_num
      exact Batch0023.cell0188.sound htau (by
        simp only [Batch0023.cell0188, Batch0023.tau0188, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs13302 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (-3/40 : ℝ) with hy1330 | hy1330
    · have hs13301 : InSquare (27/80) (-7/80) (1/80) tau := by
        convert childLR hs hx1330 hy1330 using 1 <;> norm_num
      exact Batch0023.cell0187.sound htau (by
        simp only [Batch0023.cell0187, Batch0023.tau0187, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs13301 (by positivity) using 1 <;> norm_num)
    · have hs13303 : InSquare (27/80) (-1/16) (1/80) tau := by
        convert childUR hs hx1330 hy1330 using 1 <;> norm_num
      exact Batch0023.cell0189.sound htau (by
        simp only [Batch0023.cell0189, Batch0023.tau0189, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs13303 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1330
