import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0020
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0086
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0087

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1300

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (9/40) (-7/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (9/40 : ℝ) with hx1300 | hx1300
  · rcases le_total tau.im (-7/40 : ℝ) with hy1300 | hy1300
    · have hs13000 : InSquare (17/80) (-3/16) (1/80) tau := by
        convert childLL hs hx1300 hy1300 using 1 <;> norm_num
      exact Batch0020.cell0161.sound htau (by
        simp only [Batch0020.cell0161, Batch0020.tau0161, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs13000 (by positivity) using 1 <;> norm_num)
    · have hs13002 : InSquare (17/80) (-13/80) (1/80) tau := by
        convert childUL hs hx1300 hy1300 using 1 <;> norm_num
      exact Batch0020.cell0162.sound htau (by
        simp only [Batch0020.cell0162, Batch0020.tau0162, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs13002 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (-7/40 : ℝ) with hy1300 | hy1300
    · have hs13001 : InSquare (19/80) (-3/16) (1/80) tau := by
        convert childLR hs hx1300 hy1300 using 1 <;> norm_num
      rcases le_total tau.re (19/80 : ℝ) with hx13001 | hx13001
      · rcases le_total tau.im (-3/16 : ℝ) with hy13001 | hy13001
        · have hs130010 : InSquare (37/160) (-31/160) (1/160) tau := by
            convert childLL hs13001 hx13001 hy13001 using 1 <;> norm_num
          exact Batch0086.cell0695.sound htau (by
            simp only [Batch0086.cell0695, Batch0086.tau0695, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs130010 (by positivity) using 1 <;> norm_num)
        · have hs130012 : InSquare (37/160) (-29/160) (1/160) tau := by
            convert childUL hs13001 hx13001 hy13001 using 1 <;> norm_num
          exact Batch0087.cell0697.sound htau (by
            simp only [Batch0087.cell0697, Batch0087.tau0697, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs130012 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-3/16 : ℝ) with hy13001 | hy13001
        · have hs130011 : InSquare (39/160) (-31/160) (1/160) tau := by
            convert childLR hs13001 hx13001 hy13001 using 1 <;> norm_num
          exact Batch0087.cell0696.sound htau (by
            simp only [Batch0087.cell0696, Batch0087.tau0696, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs130011 (by positivity) using 1 <;> norm_num)
        · have hs130013 : InSquare (39/160) (-29/160) (1/160) tau := by
            convert childUR hs13001 hx13001 hy13001 using 1 <;> norm_num
          exact Batch0087.cell0698.sound htau (by
            simp only [Batch0087.cell0698, Batch0087.tau0698, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs130013 (by positivity) using 1 <;> norm_num)
    · have hs13003 : InSquare (19/80) (-13/80) (1/80) tau := by
        convert childUR hs hx1300 hy1300 using 1 <;> norm_num
      exact Batch0020.cell0163.sound htau (by
        simp only [Batch0020.cell0163, Batch0020.tau0163, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs13003 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1300
