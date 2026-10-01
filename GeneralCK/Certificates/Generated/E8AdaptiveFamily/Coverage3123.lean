import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0040
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0125
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0126
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0127

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3123

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (11/40) (7/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (11/40 : ℝ) with hx3123 | hx3123
  · rcases le_total tau.im (7/40 : ℝ) with hy3123 | hy3123
    · have hs31230 : InSquare (21/80) (13/80) (1/80) tau := by
        convert childLL hs hx3123 hy3123 using 1 <;> norm_num
      exact Batch0040.cell0322.sound htau (by
        simp only [Batch0040.cell0322, Batch0040.tau0322, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs31230 (by positivity) using 1 <;> norm_num)
    · have hs31232 : InSquare (21/80) (3/16) (1/80) tau := by
        convert childUL hs hx3123 hy3123 using 1 <;> norm_num
      rcases le_total tau.re (21/80 : ℝ) with hx31232 | hx31232
      · rcases le_total tau.im (3/16 : ℝ) with hy31232 | hy31232
        · have hs312320 : InSquare (41/160) (29/160) (1/160) tau := by
            convert childLL hs31232 hx31232 hy31232 using 1 <;> norm_num
          exact Batch0126.cell1010.sound htau (by
            simp only [Batch0126.cell1010, Batch0126.tau1010, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs312320 (by positivity) using 1 <;> norm_num)
        · have hs312322 : InSquare (41/160) (31/160) (1/160) tau := by
            convert childUL hs31232 hx31232 hy31232 using 1 <;> norm_num
          exact Batch0126.cell1012.sound htau (by
            simp only [Batch0126.cell1012, Batch0126.tau1012, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs312322 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (3/16 : ℝ) with hy31232 | hy31232
        · have hs312321 : InSquare (43/160) (29/160) (1/160) tau := by
            convert childLR hs31232 hx31232 hy31232 using 1 <;> norm_num
          exact Batch0126.cell1011.sound htau (by
            simp only [Batch0126.cell1011, Batch0126.tau1011, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs312321 (by positivity) using 1 <;> norm_num)
        · have hs312323 : InSquare (43/160) (31/160) (1/160) tau := by
            convert childUR hs31232 hx31232 hy31232 using 1 <;> norm_num
          exact Batch0126.cell1013.sound htau (by
            simp only [Batch0126.cell1013, Batch0126.tau1013, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs312323 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (7/40 : ℝ) with hy3123 | hy3123
    · have hs31231 : InSquare (23/80) (13/80) (1/80) tau := by
        convert childLR hs hx3123 hy3123 using 1 <;> norm_num
      rcases le_total tau.re (23/80 : ℝ) with hx31231 | hx31231
      · rcases le_total tau.im (13/80 : ℝ) with hy31231 | hy31231
        · have hs312310 : InSquare (9/32) (5/32) (1/160) tau := by
            convert childLL hs31231 hx31231 hy31231 using 1 <;> norm_num
          exact Batch0125.cell1006.sound htau (by
            simp only [Batch0125.cell1006, Batch0125.tau1006, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs312310 (by positivity) using 1 <;> norm_num)
        · have hs312312 : InSquare (9/32) (27/160) (1/160) tau := by
            convert childUL hs31231 hx31231 hy31231 using 1 <;> norm_num
          exact Batch0126.cell1008.sound htau (by
            simp only [Batch0126.cell1008, Batch0126.tau1008, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs312312 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (13/80 : ℝ) with hy31231 | hy31231
        · have hs312311 : InSquare (47/160) (5/32) (1/160) tau := by
            convert childLR hs31231 hx31231 hy31231 using 1 <;> norm_num
          exact Batch0125.cell1007.sound htau (by
            simp only [Batch0125.cell1007, Batch0125.tau1007, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs312311 (by positivity) using 1 <;> norm_num)
        · have hs312313 : InSquare (47/160) (27/160) (1/160) tau := by
            convert childUR hs31231 hx31231 hy31231 using 1 <;> norm_num
          exact Batch0126.cell1009.sound htau (by
            simp only [Batch0126.cell1009, Batch0126.tau1009, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs312313 (by positivity) using 1 <;> norm_num)
    · have hs31233 : InSquare (23/80) (3/16) (1/80) tau := by
        convert childUR hs hx3123 hy3123 using 1 <;> norm_num
      rcases le_total tau.re (23/80 : ℝ) with hx31233 | hx31233
      · rcases le_total tau.im (3/16 : ℝ) with hy31233 | hy31233
        · have hs312330 : InSquare (9/32) (29/160) (1/160) tau := by
            convert childLL hs31233 hx31233 hy31233 using 1 <;> norm_num
          exact Batch0126.cell1014.sound htau (by
            simp only [Batch0126.cell1014, Batch0126.tau1014, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs312330 (by positivity) using 1 <;> norm_num)
        · have hs312332 : InSquare (9/32) (31/160) (1/160) tau := by
            convert childUL hs31233 hx31233 hy31233 using 1 <;> norm_num
          exact Batch0127.cell1016.sound htau (by
            simp only [Batch0127.cell1016, Batch0127.tau1016, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs312332 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (3/16 : ℝ) with hy31233 | hy31233
        · have hs312331 : InSquare (47/160) (29/160) (1/160) tau := by
            convert childLR hs31233 hx31233 hy31233 using 1 <;> norm_num
          exact Batch0126.cell1015.sound htau (by
            simp only [Batch0126.cell1015, Batch0126.tau1015, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs312331 (by positivity) using 1 <;> norm_num)
        · have hs312333 : InSquare (47/160) (31/160) (1/160) tau := by
            convert childUR hs31233 hx31233 hy31233 using 1 <;> norm_num
          exact Batch0127.cell1017.sound htau (by
            simp only [Batch0127.cell1017, Batch0127.tau1017, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs312333 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3123
