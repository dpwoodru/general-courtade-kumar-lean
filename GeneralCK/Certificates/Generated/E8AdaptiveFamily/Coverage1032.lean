import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0017

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1032

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (1/8) (-9/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (1/8 : ℝ) with hx1032 | hx1032
  · rcases le_total tau.im (-9/40 : ℝ) with hy1032 | hy1032
    · have hs10320 : InSquare (9/80) (-19/80) (1/80) tau := by
        convert childLL hs hx1032 hy1032 using 1 <;> norm_num
      exact Batch0017.cell0139.sound htau (by
        simp only [Batch0017.cell0139, Batch0017.tau0139, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs10320 (by positivity) using 1 <;> norm_num)
    · have hs10322 : InSquare (9/80) (-17/80) (1/80) tau := by
        convert childUL hs hx1032 hy1032 using 1 <;> norm_num
      exact Batch0017.cell0141.sound htau (by
        simp only [Batch0017.cell0141, Batch0017.tau0141, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs10322 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (-9/40 : ℝ) with hy1032 | hy1032
    · have hs10321 : InSquare (11/80) (-19/80) (1/80) tau := by
        convert childLR hs hx1032 hy1032 using 1 <;> norm_num
      exact Batch0017.cell0140.sound htau (by
        simp only [Batch0017.cell0140, Batch0017.tau0140, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs10321 (by positivity) using 1 <;> norm_num)
    · have hs10323 : InSquare (11/80) (-17/80) (1/80) tau := by
        convert childUR hs hx1032 hy1032 using 1 <;> norm_num
      exact Batch0017.cell0142.sound htau (by
        simp only [Batch0017.cell0142, Batch0017.tau0142, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs10323 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1032
