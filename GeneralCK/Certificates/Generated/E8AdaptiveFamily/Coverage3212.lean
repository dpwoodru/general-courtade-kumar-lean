import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0134
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0135
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0136

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3212

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (1/8) (11/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (1/8 : ℝ) with hx3212 | hx3212
  · rcases le_total tau.im (11/40 : ℝ) with hy3212 | hy3212
    · have hs32120 : InSquare (9/80) (21/80) (1/80) tau := by
        convert childLL hs hx3212 hy3212 using 1 <;> norm_num
      rcases le_total tau.re (9/80 : ℝ) with hx32120 | hx32120
      · rcases le_total tau.im (21/80 : ℝ) with hy32120 | hy32120
        · have hs321200 : InSquare (17/160) (41/160) (1/160) tau := by
            convert childLL hs32120 hx32120 hy32120 using 1 <;> norm_num
          exact Batch0134.cell1079.sound htau (by
            simp only [Batch0134.cell1079, Batch0134.tau1079, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs321200 (by positivity) using 1 <;> norm_num)
        · have hs321202 : InSquare (17/160) (43/160) (1/160) tau := by
            convert childUL hs32120 hx32120 hy32120 using 1 <;> norm_num
          exact Batch0135.cell1081.sound htau (by
            simp only [Batch0135.cell1081, Batch0135.tau1081, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs321202 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (21/80 : ℝ) with hy32120 | hy32120
        · have hs321201 : InSquare (19/160) (41/160) (1/160) tau := by
            convert childLR hs32120 hx32120 hy32120 using 1 <;> norm_num
          exact Batch0135.cell1080.sound htau (by
            simp only [Batch0135.cell1080, Batch0135.tau1080, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs321201 (by positivity) using 1 <;> norm_num)
        · have hs321203 : InSquare (19/160) (43/160) (1/160) tau := by
            convert childUR hs32120 hx32120 hy32120 using 1 <;> norm_num
          exact Batch0135.cell1082.sound htau (by
            simp only [Batch0135.cell1082, Batch0135.tau1082, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs321203 (by positivity) using 1 <;> norm_num)
    · have hs32122 : InSquare (9/80) (23/80) (1/80) tau := by
        convert childUL hs hx3212 hy3212 using 1 <;> norm_num
      rcases le_total tau.re (9/80 : ℝ) with hx32122 | hx32122
      · rcases le_total tau.im (23/80 : ℝ) with hy32122 | hy32122
        · have hs321220 : InSquare (17/160) (9/32) (1/160) tau := by
            convert childLL hs32122 hx32122 hy32122 using 1 <;> norm_num
          exact Batch0135.cell1087.sound htau (by
            simp only [Batch0135.cell1087, Batch0135.tau1087, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs321220 (by positivity) using 1 <;> norm_num)
        · have hs321222 : InSquare (17/160) (47/160) (1/160) tau := by
            convert childUL hs32122 hx32122 hy32122 using 1 <;> norm_num
          exact Batch0136.cell1089.sound htau (by
            simp only [Batch0136.cell1089, Batch0136.tau1089, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs321222 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (23/80 : ℝ) with hy32122 | hy32122
        · have hs321221 : InSquare (19/160) (9/32) (1/160) tau := by
            convert childLR hs32122 hx32122 hy32122 using 1 <;> norm_num
          exact Batch0136.cell1088.sound htau (by
            simp only [Batch0136.cell1088, Batch0136.tau1088, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs321221 (by positivity) using 1 <;> norm_num)
        · have hs321223 : InSquare (19/160) (47/160) (1/160) tau := by
            convert childUR hs32122 hx32122 hy32122 using 1 <;> norm_num
          exact Batch0136.cell1090.sound htau (by
            simp only [Batch0136.cell1090, Batch0136.tau1090, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs321223 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (11/40 : ℝ) with hy3212 | hy3212
    · have hs32121 : InSquare (11/80) (21/80) (1/80) tau := by
        convert childLR hs hx3212 hy3212 using 1 <;> norm_num
      rcases le_total tau.re (11/80 : ℝ) with hx32121 | hx32121
      · rcases le_total tau.im (21/80 : ℝ) with hy32121 | hy32121
        · have hs321210 : InSquare (21/160) (41/160) (1/160) tau := by
            convert childLL hs32121 hx32121 hy32121 using 1 <;> norm_num
          exact Batch0135.cell1083.sound htau (by
            simp only [Batch0135.cell1083, Batch0135.tau1083, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs321210 (by positivity) using 1 <;> norm_num)
        · have hs321212 : InSquare (21/160) (43/160) (1/160) tau := by
            convert childUL hs32121 hx32121 hy32121 using 1 <;> norm_num
          exact Batch0135.cell1085.sound htau (by
            simp only [Batch0135.cell1085, Batch0135.tau1085, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs321212 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (21/80 : ℝ) with hy32121 | hy32121
        · have hs321211 : InSquare (23/160) (41/160) (1/160) tau := by
            convert childLR hs32121 hx32121 hy32121 using 1 <;> norm_num
          exact Batch0135.cell1084.sound htau (by
            simp only [Batch0135.cell1084, Batch0135.tau1084, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs321211 (by positivity) using 1 <;> norm_num)
        · have hs321213 : InSquare (23/160) (43/160) (1/160) tau := by
            convert childUR hs32121 hx32121 hy32121 using 1 <;> norm_num
          exact Batch0135.cell1086.sound htau (by
            simp only [Batch0135.cell1086, Batch0135.tau1086, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs321213 (by positivity) using 1 <;> norm_num)
    · have hs32123 : InSquare (11/80) (23/80) (1/80) tau := by
        convert childUR hs hx3212 hy3212 using 1 <;> norm_num
      rcases le_total tau.re (11/80 : ℝ) with hx32123 | hx32123
      · rcases le_total tau.im (23/80 : ℝ) with hy32123 | hy32123
        · have hs321230 : InSquare (21/160) (9/32) (1/160) tau := by
            convert childLL hs32123 hx32123 hy32123 using 1 <;> norm_num
          exact Batch0136.cell1091.sound htau (by
            simp only [Batch0136.cell1091, Batch0136.tau1091, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs321230 (by positivity) using 1 <;> norm_num)
        · have hs321232 : InSquare (21/160) (47/160) (1/160) tau := by
            convert childUL hs32123 hx32123 hy32123 using 1 <;> norm_num
          exact Batch0136.cell1093.sound htau (by
            simp only [Batch0136.cell1093, Batch0136.tau1093, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs321232 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (23/80 : ℝ) with hy32123 | hy32123
        · have hs321231 : InSquare (23/160) (9/32) (1/160) tau := by
            convert childLR hs32123 hx32123 hy32123 using 1 <;> norm_num
          exact Batch0136.cell1092.sound htau (by
            simp only [Batch0136.cell1092, Batch0136.tau1092, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs321231 (by positivity) using 1 <;> norm_num)
        · have hs321233 : InSquare (23/160) (47/160) (1/160) tau := by
            convert childUR hs32123 hx32123 hy32123 using 1 <;> norm_num
          exact Batch0136.cell1094.sound htau (by
            simp only [Batch0136.cell1094, Batch0136.tau1094, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs321233 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3212
