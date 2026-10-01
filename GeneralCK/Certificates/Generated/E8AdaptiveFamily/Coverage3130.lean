import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0040
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0127
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0128

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3130

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (13/40) (1/8) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (13/40 : ℝ) with hx3130 | hx3130
  · rcases le_total tau.im (1/8 : ℝ) with hy3130 | hy3130
    · have hs31300 : InSquare (5/16) (9/80) (1/80) tau := by
        convert childLL hs hx3130 hy3130 using 1 <;> norm_num
      exact Batch0040.cell0323.sound htau (by
        simp only [Batch0040.cell0323, Batch0040.tau0323, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs31300 (by positivity) using 1 <;> norm_num)
    · have hs31302 : InSquare (5/16) (11/80) (1/80) tau := by
        convert childUL hs hx3130 hy3130 using 1 <;> norm_num
      rcases le_total tau.re (5/16 : ℝ) with hx31302 | hx31302
      · rcases le_total tau.im (11/80 : ℝ) with hy31302 | hy31302
        · have hs313020 : InSquare (49/160) (21/160) (1/160) tau := by
            convert childLL hs31302 hx31302 hy31302 using 1 <;> norm_num
          exact Batch0127.cell1022.sound htau (by
            simp only [Batch0127.cell1022, Batch0127.tau1022, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs313020 (by positivity) using 1 <;> norm_num)
        · have hs313022 : InSquare (49/160) (23/160) (1/160) tau := by
            convert childUL hs31302 hx31302 hy31302 using 1 <;> norm_num
          exact Batch0128.cell1024.sound htau (by
            simp only [Batch0128.cell1024, Batch0128.tau1024, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs313022 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (11/80 : ℝ) with hy31302 | hy31302
        · have hs313021 : InSquare (51/160) (21/160) (1/160) tau := by
            convert childLR hs31302 hx31302 hy31302 using 1 <;> norm_num
          exact Batch0127.cell1023.sound htau (by
            simp only [Batch0127.cell1023, Batch0127.tau1023, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs313021 (by positivity) using 1 <;> norm_num)
        · have hs313023 : InSquare (51/160) (23/160) (1/160) tau := by
            convert childUR hs31302 hx31302 hy31302 using 1 <;> norm_num
          exact Batch0128.cell1025.sound htau (by
            simp only [Batch0128.cell1025, Batch0128.tau1025, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs313023 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (1/8 : ℝ) with hy3130 | hy3130
    · have hs31301 : InSquare (27/80) (9/80) (1/80) tau := by
        convert childLR hs hx3130 hy3130 using 1 <;> norm_num
      rcases le_total tau.re (27/80 : ℝ) with hx31301 | hx31301
      · rcases le_total tau.im (9/80 : ℝ) with hy31301 | hy31301
        · have hs313010 : InSquare (53/160) (17/160) (1/160) tau := by
            convert childLL hs31301 hx31301 hy31301 using 1 <;> norm_num
          exact Batch0127.cell1018.sound htau (by
            simp only [Batch0127.cell1018, Batch0127.tau1018, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs313010 (by positivity) using 1 <;> norm_num)
        · have hs313012 : InSquare (53/160) (19/160) (1/160) tau := by
            convert childUL hs31301 hx31301 hy31301 using 1 <;> norm_num
          exact Batch0127.cell1020.sound htau (by
            simp only [Batch0127.cell1020, Batch0127.tau1020, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs313012 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (9/80 : ℝ) with hy31301 | hy31301
        · have hs313011 : InSquare (11/32) (17/160) (1/160) tau := by
            convert childLR hs31301 hx31301 hy31301 using 1 <;> norm_num
          exact Batch0127.cell1019.sound htau (by
            simp only [Batch0127.cell1019, Batch0127.tau1019, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs313011 (by positivity) using 1 <;> norm_num)
        · have hs313013 : InSquare (11/32) (19/160) (1/160) tau := by
            convert childUR hs31301 hx31301 hy31301 using 1 <;> norm_num
          exact Batch0127.cell1021.sound htau (by
            simp only [Batch0127.cell1021, Batch0127.tau1021, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs313013 (by positivity) using 1 <;> norm_num)
    · have hs31303 : InSquare (27/80) (11/80) (1/80) tau := by
        convert childUR hs hx3130 hy3130 using 1 <;> norm_num
      rcases le_total tau.re (27/80 : ℝ) with hx31303 | hx31303
      · rcases le_total tau.im (11/80 : ℝ) with hy31303 | hy31303
        · have hs313030 : InSquare (53/160) (21/160) (1/160) tau := by
            convert childLL hs31303 hx31303 hy31303 using 1 <;> norm_num
          exact Batch0128.cell1026.sound htau (by
            simp only [Batch0128.cell1026, Batch0128.tau1026, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs313030 (by positivity) using 1 <;> norm_num)
        · have hs313032 : InSquare (53/160) (23/160) (1/160) tau := by
            convert childUL hs31303 hx31303 hy31303 using 1 <;> norm_num
          exact Batch0128.cell1028.sound htau (by
            simp only [Batch0128.cell1028, Batch0128.tau1028, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs313032 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (11/80 : ℝ) with hy31303 | hy31303
        · have hs313031 : InSquare (11/32) (21/160) (1/160) tau := by
            convert childLR hs31303 hx31303 hy31303 using 1 <;> norm_num
          exact Batch0128.cell1027.sound htau (by
            simp only [Batch0128.cell1027, Batch0128.tau1027, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs313031 (by positivity) using 1 <;> norm_num)
        · have hs313033 : InSquare (11/32) (23/160) (1/160) tau := by
            convert childUR hs31303 hx31303 hy31303 using 1 <;> norm_num
          exact Batch0128.cell1029.sound htau (by
            simp only [Batch0128.cell1029, Batch0128.tau1029, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs313033 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3130
