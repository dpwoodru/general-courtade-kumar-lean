import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0042
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0132
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0133

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3203

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (3/40) (11/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (3/40 : ℝ) with hx3203 | hx3203
  · rcases le_total tau.im (11/40 : ℝ) with hy3203 | hy3203
    · have hs32030 : InSquare (1/16) (21/80) (1/80) tau := by
        convert childLL hs hx3203 hy3203 using 1 <;> norm_num
      exact Batch0042.cell0336.sound htau (by
        simp only [Batch0042.cell0336, Batch0042.tau0336, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs32030 (by positivity) using 1 <;> norm_num)
    · have hs32032 : InSquare (1/16) (23/80) (1/80) tau := by
        convert childUL hs hx3203 hy3203 using 1 <;> norm_num
      rcases le_total tau.re (1/16 : ℝ) with hx32032 | hx32032
      · rcases le_total tau.im (23/80 : ℝ) with hy32032 | hy32032
        · have hs320320 : InSquare (9/160) (9/32) (1/160) tau := by
            convert childLL hs32032 hx32032 hy32032 using 1 <;> norm_num
          exact Batch0132.cell1063.sound htau (by
            simp only [Batch0132.cell1063, Batch0132.tau1063, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs320320 (by positivity) using 1 <;> norm_num)
        · have hs320322 : InSquare (9/160) (47/160) (1/160) tau := by
            convert childUL hs32032 hx32032 hy32032 using 1 <;> norm_num
          exact Batch0133.cell1065.sound htau (by
            simp only [Batch0133.cell1065, Batch0133.tau1065, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs320322 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (23/80 : ℝ) with hy32032 | hy32032
        · have hs320321 : InSquare (11/160) (9/32) (1/160) tau := by
            convert childLR hs32032 hx32032 hy32032 using 1 <;> norm_num
          exact Batch0133.cell1064.sound htau (by
            simp only [Batch0133.cell1064, Batch0133.tau1064, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs320321 (by positivity) using 1 <;> norm_num)
        · have hs320323 : InSquare (11/160) (47/160) (1/160) tau := by
            convert childUR hs32032 hx32032 hy32032 using 1 <;> norm_num
          exact Batch0133.cell1066.sound htau (by
            simp only [Batch0133.cell1066, Batch0133.tau1066, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs320323 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (11/40 : ℝ) with hy3203 | hy3203
    · have hs32031 : InSquare (7/80) (21/80) (1/80) tau := by
        convert childLR hs hx3203 hy3203 using 1 <;> norm_num
      exact Batch0042.cell0337.sound htau (by
        simp only [Batch0042.cell0337, Batch0042.tau0337, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs32031 (by positivity) using 1 <;> norm_num)
    · have hs32033 : InSquare (7/80) (23/80) (1/80) tau := by
        convert childUR hs hx3203 hy3203 using 1 <;> norm_num
      rcases le_total tau.re (7/80 : ℝ) with hx32033 | hx32033
      · rcases le_total tau.im (23/80 : ℝ) with hy32033 | hy32033
        · have hs320330 : InSquare (13/160) (9/32) (1/160) tau := by
            convert childLL hs32033 hx32033 hy32033 using 1 <;> norm_num
          exact Batch0133.cell1067.sound htau (by
            simp only [Batch0133.cell1067, Batch0133.tau1067, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs320330 (by positivity) using 1 <;> norm_num)
        · have hs320332 : InSquare (13/160) (47/160) (1/160) tau := by
            convert childUL hs32033 hx32033 hy32033 using 1 <;> norm_num
          exact Batch0133.cell1069.sound htau (by
            simp only [Batch0133.cell1069, Batch0133.tau1069, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs320332 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (23/80 : ℝ) with hy32033 | hy32033
        · have hs320331 : InSquare (3/32) (9/32) (1/160) tau := by
            convert childLR hs32033 hx32033 hy32033 using 1 <;> norm_num
          exact Batch0133.cell1068.sound htau (by
            simp only [Batch0133.cell1068, Batch0133.tau1068, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs320331 (by positivity) using 1 <;> norm_num)
        · have hs320333 : InSquare (3/32) (47/160) (1/160) tau := by
            convert childUR hs32033 hx32033 hy32033 using 1 <;> norm_num
          exact Batch0133.cell1070.sound htau (by
            simp only [Batch0133.cell1070, Batch0133.tau1070, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs320333 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3203
