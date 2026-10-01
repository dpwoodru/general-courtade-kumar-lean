import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0021
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0091
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0092

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1312

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (13/40) (-1/8) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (13/40 : ℝ) with hx1312 | hx1312
  · rcases le_total tau.im (-1/8 : ℝ) with hy1312 | hy1312
    · have hs13120 : InSquare (5/16) (-11/80) (1/80) tau := by
        convert childLL hs hx1312 hy1312 using 1 <;> norm_num
      rcases le_total tau.re (5/16 : ℝ) with hx13120 | hx13120
      · rcases le_total tau.im (-11/80 : ℝ) with hy13120 | hy13120
        · have hs131200 : InSquare (49/160) (-23/160) (1/160) tau := by
            convert childLL hs13120 hx13120 hy13120 using 1 <;> norm_num
          exact Batch0091.cell0732.sound htau (by
            simp only [Batch0091.cell0732, Batch0091.tau0732, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs131200 (by positivity) using 1 <;> norm_num)
        · have hs131202 : InSquare (49/160) (-21/160) (1/160) tau := by
            convert childUL hs13120 hx13120 hy13120 using 1 <;> norm_num
          exact Batch0091.cell0734.sound htau (by
            simp only [Batch0091.cell0734, Batch0091.tau0734, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs131202 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-11/80 : ℝ) with hy13120 | hy13120
        · have hs131201 : InSquare (51/160) (-23/160) (1/160) tau := by
            convert childLR hs13120 hx13120 hy13120 using 1 <;> norm_num
          exact Batch0091.cell0733.sound htau (by
            simp only [Batch0091.cell0733, Batch0091.tau0733, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs131201 (by positivity) using 1 <;> norm_num)
        · have hs131203 : InSquare (51/160) (-21/160) (1/160) tau := by
            convert childUR hs13120 hx13120 hy13120 using 1 <;> norm_num
          exact Batch0091.cell0735.sound htau (by
            simp only [Batch0091.cell0735, Batch0091.tau0735, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs131203 (by positivity) using 1 <;> norm_num)
    · have hs13122 : InSquare (5/16) (-9/80) (1/80) tau := by
        convert childUL hs hx1312 hy1312 using 1 <;> norm_num
      exact Batch0021.cell0173.sound htau (by
        simp only [Batch0021.cell0173, Batch0021.tau0173, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs13122 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (-1/8 : ℝ) with hy1312 | hy1312
    · have hs13121 : InSquare (27/80) (-11/80) (1/80) tau := by
        convert childLR hs hx1312 hy1312 using 1 <;> norm_num
      rcases le_total tau.re (27/80 : ℝ) with hx13121 | hx13121
      · rcases le_total tau.im (-11/80 : ℝ) with hy13121 | hy13121
        · have hs131210 : InSquare (53/160) (-23/160) (1/160) tau := by
            convert childLL hs13121 hx13121 hy13121 using 1 <;> norm_num
          exact Batch0092.cell0736.sound htau (by
            simp only [Batch0092.cell0736, Batch0092.tau0736, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs131210 (by positivity) using 1 <;> norm_num)
        · have hs131212 : InSquare (53/160) (-21/160) (1/160) tau := by
            convert childUL hs13121 hx13121 hy13121 using 1 <;> norm_num
          exact Batch0092.cell0738.sound htau (by
            simp only [Batch0092.cell0738, Batch0092.tau0738, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs131212 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-11/80 : ℝ) with hy13121 | hy13121
        · have hs131211 : InSquare (11/32) (-23/160) (1/160) tau := by
            convert childLR hs13121 hx13121 hy13121 using 1 <;> norm_num
          exact Batch0092.cell0737.sound htau (by
            simp only [Batch0092.cell0737, Batch0092.tau0737, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs131211 (by positivity) using 1 <;> norm_num)
        · have hs131213 : InSquare (11/32) (-21/160) (1/160) tau := by
            convert childUR hs13121 hx13121 hy13121 using 1 <;> norm_num
          exact Batch0092.cell0739.sound htau (by
            simp only [Batch0092.cell0739, Batch0092.tau0739, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs131213 (by positivity) using 1 <;> norm_num)
    · have hs13123 : InSquare (27/80) (-9/80) (1/80) tau := by
        convert childUR hs hx1312 hy1312 using 1 <;> norm_num
      rcases le_total tau.re (27/80 : ℝ) with hx13123 | hx13123
      · rcases le_total tau.im (-9/80 : ℝ) with hy13123 | hy13123
        · have hs131230 : InSquare (53/160) (-19/160) (1/160) tau := by
            convert childLL hs13123 hx13123 hy13123 using 1 <;> norm_num
          exact Batch0092.cell0740.sound htau (by
            simp only [Batch0092.cell0740, Batch0092.tau0740, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs131230 (by positivity) using 1 <;> norm_num)
        · have hs131232 : InSquare (53/160) (-17/160) (1/160) tau := by
            convert childUL hs13123 hx13123 hy13123 using 1 <;> norm_num
          exact Batch0092.cell0742.sound htau (by
            simp only [Batch0092.cell0742, Batch0092.tau0742, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs131232 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-9/80 : ℝ) with hy13123 | hy13123
        · have hs131231 : InSquare (11/32) (-19/160) (1/160) tau := by
            convert childLR hs13123 hx13123 hy13123 using 1 <;> norm_num
          exact Batch0092.cell0741.sound htau (by
            simp only [Batch0092.cell0741, Batch0092.tau0741, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs131231 (by positivity) using 1 <;> norm_num)
        · have hs131233 : InSquare (11/32) (-17/160) (1/160) tau := by
            convert childUR hs13123 hx13123 hy13123 using 1 <;> norm_num
          exact Batch0092.cell0743.sound htau (by
            simp only [Batch0092.cell0743, Batch0092.tau0743, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs131233 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1312
