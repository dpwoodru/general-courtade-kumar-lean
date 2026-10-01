import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0130
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0131
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0132

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3132

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (13/40) (7/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (13/40 : ℝ) with hx3132 | hx3132
  · rcases le_total tau.im (7/40 : ℝ) with hy3132 | hy3132
    · have hs31320 : InSquare (5/16) (13/80) (1/80) tau := by
        convert childLL hs hx3132 hy3132 using 1 <;> norm_num
      rcases le_total tau.re (5/16 : ℝ) with hx31320 | hx31320
      · rcases le_total tau.im (13/80 : ℝ) with hy31320 | hy31320
        · have hs313200 : InSquare (49/160) (5/32) (1/160) tau := by
            convert childLL hs31320 hx31320 hy31320 using 1 <;> norm_num
          exact Batch0130.cell1042.sound htau (by
            simp only [Batch0130.cell1042, Batch0130.tau1042, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs313200 (by positivity) using 1 <;> norm_num)
        · have hs313202 : InSquare (49/160) (27/160) (1/160) tau := by
            convert childUL hs31320 hx31320 hy31320 using 1 <;> norm_num
          exact Batch0130.cell1044.sound htau (by
            simp only [Batch0130.cell1044, Batch0130.tau1044, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs313202 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (13/80 : ℝ) with hy31320 | hy31320
        · have hs313201 : InSquare (51/160) (5/32) (1/160) tau := by
            convert childLR hs31320 hx31320 hy31320 using 1 <;> norm_num
          exact Batch0130.cell1043.sound htau (by
            simp only [Batch0130.cell1043, Batch0130.tau1043, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs313201 (by positivity) using 1 <;> norm_num)
        · have hs313203 : InSquare (51/160) (27/160) (1/160) tau := by
            convert childUR hs31320 hx31320 hy31320 using 1 <;> norm_num
          exact Batch0130.cell1045.sound htau (by
            simp only [Batch0130.cell1045, Batch0130.tau1045, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs313203 (by positivity) using 1 <;> norm_num)
    · have hs31322 : InSquare (5/16) (3/16) (1/80) tau := by
        convert childUL hs hx3132 hy3132 using 1 <;> norm_num
      rcases le_total tau.re (5/16 : ℝ) with hx31322 | hx31322
      · rcases le_total tau.im (3/16 : ℝ) with hy31322 | hy31322
        · have hs313220 : InSquare (49/160) (29/160) (1/160) tau := by
            convert childLL hs31322 hx31322 hy31322 using 1 <;> norm_num
          exact Batch0131.cell1050.sound htau (by
            simp only [Batch0131.cell1050, Batch0131.tau1050, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs313220 (by positivity) using 1 <;> norm_num)
        · have hs313222 : InSquare (49/160) (31/160) (1/160) tau := by
            convert childUL hs31322 hx31322 hy31322 using 1 <;> norm_num
          exact Batch0131.cell1052.sound htau (by
            simp only [Batch0131.cell1052, Batch0131.tau1052, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs313222 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (3/16 : ℝ) with hy31322 | hy31322
        · have hs313221 : InSquare (51/160) (29/160) (1/160) tau := by
            convert childLR hs31322 hx31322 hy31322 using 1 <;> norm_num
          exact Batch0131.cell1051.sound htau (by
            simp only [Batch0131.cell1051, Batch0131.tau1051, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs313221 (by positivity) using 1 <;> norm_num)
        · have hs313223 : InSquare (51/160) (31/160) (1/160) tau := by
            convert childUR hs31322 hx31322 hy31322 using 1 <;> norm_num
          exact Batch0131.cell1053.sound htau (by
            simp only [Batch0131.cell1053, Batch0131.tau1053, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs313223 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (7/40 : ℝ) with hy3132 | hy3132
    · have hs31321 : InSquare (27/80) (13/80) (1/80) tau := by
        convert childLR hs hx3132 hy3132 using 1 <;> norm_num
      rcases le_total tau.re (27/80 : ℝ) with hx31321 | hx31321
      · rcases le_total tau.im (13/80 : ℝ) with hy31321 | hy31321
        · have hs313210 : InSquare (53/160) (5/32) (1/160) tau := by
            convert childLL hs31321 hx31321 hy31321 using 1 <;> norm_num
          exact Batch0130.cell1046.sound htau (by
            simp only [Batch0130.cell1046, Batch0130.tau1046, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs313210 (by positivity) using 1 <;> norm_num)
        · have hs313212 : InSquare (53/160) (27/160) (1/160) tau := by
            convert childUL hs31321 hx31321 hy31321 using 1 <;> norm_num
          exact Batch0131.cell1048.sound htau (by
            simp only [Batch0131.cell1048, Batch0131.tau1048, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs313212 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (13/80 : ℝ) with hy31321 | hy31321
        · have hs313211 : InSquare (11/32) (5/32) (1/160) tau := by
            convert childLR hs31321 hx31321 hy31321 using 1 <;> norm_num
          exact Batch0130.cell1047.sound htau (by
            simp only [Batch0130.cell1047, Batch0130.tau1047, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs313211 (by positivity) using 1 <;> norm_num)
        · have hs313213 : InSquare (11/32) (27/160) (1/160) tau := by
            convert childUR hs31321 hx31321 hy31321 using 1 <;> norm_num
          exact Batch0131.cell1049.sound htau (by
            simp only [Batch0131.cell1049, Batch0131.tau1049, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs313213 (by positivity) using 1 <;> norm_num)
    · have hs31323 : InSquare (27/80) (3/16) (1/80) tau := by
        convert childUR hs hx3132 hy3132 using 1 <;> norm_num
      rcases le_total tau.re (27/80 : ℝ) with hx31323 | hx31323
      · rcases le_total tau.im (3/16 : ℝ) with hy31323 | hy31323
        · have hs313230 : InSquare (53/160) (29/160) (1/160) tau := by
            convert childLL hs31323 hx31323 hy31323 using 1 <;> norm_num
          exact Batch0131.cell1054.sound htau (by
            simp only [Batch0131.cell1054, Batch0131.tau1054, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs313230 (by positivity) using 1 <;> norm_num)
        · have hs313232 : InSquare (53/160) (31/160) (1/160) tau := by
            convert childUL hs31323 hx31323 hy31323 using 1 <;> norm_num
          exact Batch0132.cell1056.sound htau (by
            simp only [Batch0132.cell1056, Batch0132.tau1056, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs313232 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (3/16 : ℝ) with hy31323 | hy31323
        · have hs313231 : InSquare (11/32) (29/160) (1/160) tau := by
            convert childLR hs31323 hx31323 hy31323 using 1 <;> norm_num
          exact Batch0131.cell1055.sound htau (by
            simp only [Batch0131.cell1055, Batch0131.tau1055, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs313231 (by positivity) using 1 <;> norm_num)
        · have hs313233 : InSquare (11/32) (31/160) (1/160) tau := by
            convert childUR hs31323 hx31323 hy31323 using 1 <;> norm_num
          exact Batch0132.cell1057.sound htau (by
            simp only [Batch0132.cell1057, Batch0132.tau1057, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs313233 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3132
