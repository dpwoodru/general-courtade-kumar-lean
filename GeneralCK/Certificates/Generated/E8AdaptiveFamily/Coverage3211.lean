import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0042
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0133
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0134

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3211

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (7/40) (9/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (7/40 : ℝ) with hx3211 | hx3211
  · rcases le_total tau.im (9/40 : ℝ) with hy3211 | hy3211
    · have hs32110 : InSquare (13/80) (17/80) (1/80) tau := by
        convert childLL hs hx3211 hy3211 using 1 <;> norm_num
      exact Batch0042.cell0342.sound htau (by
        simp only [Batch0042.cell0342, Batch0042.tau0342, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs32110 (by positivity) using 1 <;> norm_num)
    · have hs32112 : InSquare (13/80) (19/80) (1/80) tau := by
        convert childUL hs hx3211 hy3211 using 1 <;> norm_num
      rcases le_total tau.re (13/80 : ℝ) with hx32112 | hx32112
      · rcases le_total tau.im (19/80 : ℝ) with hy32112 | hy32112
        · have hs321120 : InSquare (5/32) (37/160) (1/160) tau := by
            convert childLL hs32112 hx32112 hy32112 using 1 <;> norm_num
          exact Batch0133.cell1071.sound htau (by
            simp only [Batch0133.cell1071, Batch0133.tau1071, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs321120 (by positivity) using 1 <;> norm_num)
        · have hs321122 : InSquare (5/32) (39/160) (1/160) tau := by
            convert childUL hs32112 hx32112 hy32112 using 1 <;> norm_num
          exact Batch0134.cell1073.sound htau (by
            simp only [Batch0134.cell1073, Batch0134.tau1073, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs321122 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (19/80 : ℝ) with hy32112 | hy32112
        · have hs321121 : InSquare (27/160) (37/160) (1/160) tau := by
            convert childLR hs32112 hx32112 hy32112 using 1 <;> norm_num
          exact Batch0134.cell1072.sound htau (by
            simp only [Batch0134.cell1072, Batch0134.tau1072, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs321121 (by positivity) using 1 <;> norm_num)
        · have hs321123 : InSquare (27/160) (39/160) (1/160) tau := by
            convert childUR hs32112 hx32112 hy32112 using 1 <;> norm_num
          exact Batch0134.cell1074.sound htau (by
            simp only [Batch0134.cell1074, Batch0134.tau1074, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs321123 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (9/40 : ℝ) with hy3211 | hy3211
    · have hs32111 : InSquare (3/16) (17/80) (1/80) tau := by
        convert childLR hs hx3211 hy3211 using 1 <;> norm_num
      exact Batch0042.cell0343.sound htau (by
        simp only [Batch0042.cell0343, Batch0042.tau0343, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs32111 (by positivity) using 1 <;> norm_num)
    · have hs32113 : InSquare (3/16) (19/80) (1/80) tau := by
        convert childUR hs hx3211 hy3211 using 1 <;> norm_num
      rcases le_total tau.re (3/16 : ℝ) with hx32113 | hx32113
      · rcases le_total tau.im (19/80 : ℝ) with hy32113 | hy32113
        · have hs321130 : InSquare (29/160) (37/160) (1/160) tau := by
            convert childLL hs32113 hx32113 hy32113 using 1 <;> norm_num
          exact Batch0134.cell1075.sound htau (by
            simp only [Batch0134.cell1075, Batch0134.tau1075, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs321130 (by positivity) using 1 <;> norm_num)
        · have hs321132 : InSquare (29/160) (39/160) (1/160) tau := by
            convert childUL hs32113 hx32113 hy32113 using 1 <;> norm_num
          exact Batch0134.cell1077.sound htau (by
            simp only [Batch0134.cell1077, Batch0134.tau1077, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs321132 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (19/80 : ℝ) with hy32113 | hy32113
        · have hs321131 : InSquare (31/160) (37/160) (1/160) tau := by
            convert childLR hs32113 hx32113 hy32113 using 1 <;> norm_num
          exact Batch0134.cell1076.sound htau (by
            simp only [Batch0134.cell1076, Batch0134.tau1076, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs321131 (by positivity) using 1 <;> norm_num)
        · have hs321133 : InSquare (31/160) (39/160) (1/160) tau := by
            convert childUR hs32113 hx32113 hy32113 using 1 <;> norm_num
          exact Batch0134.cell1078.sound htau (by
            simp only [Batch0134.cell1078, Batch0134.tau1078, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs321133 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3211
