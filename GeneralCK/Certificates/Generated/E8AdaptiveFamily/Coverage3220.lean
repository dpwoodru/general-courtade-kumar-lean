import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0138
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0139
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0140

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3220

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (1/40) (13/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (1/40 : ℝ) with hx3220 | hx3220
  · rcases le_total tau.im (13/40 : ℝ) with hy3220 | hy3220
    · have hs32200 : InSquare (1/80) (5/16) (1/80) tau := by
        convert childLL hs hx3220 hy3220 using 1 <;> norm_num
      rcases le_total tau.re (1/80 : ℝ) with hx32200 | hx32200
      · rcases le_total tau.im (5/16 : ℝ) with hy32200 | hy32200
        · have hs322000 : InSquare (1/160) (49/160) (1/160) tau := by
            convert childLL hs32200 hx32200 hy32200 using 1 <;> norm_num
          exact Batch0138.cell1111.sound htau (by
            simp only [Batch0138.cell1111, Batch0138.tau1111, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs322000 (by positivity) using 1 <;> norm_num)
        · have hs322002 : InSquare (1/160) (51/160) (1/160) tau := by
            convert childUL hs32200 hx32200 hy32200 using 1 <;> norm_num
          exact Batch0139.cell1113.sound htau (by
            simp only [Batch0139.cell1113, Batch0139.tau1113, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs322002 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (5/16 : ℝ) with hy32200 | hy32200
        · have hs322001 : InSquare (3/160) (49/160) (1/160) tau := by
            convert childLR hs32200 hx32200 hy32200 using 1 <;> norm_num
          exact Batch0139.cell1112.sound htau (by
            simp only [Batch0139.cell1112, Batch0139.tau1112, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs322001 (by positivity) using 1 <;> norm_num)
        · have hs322003 : InSquare (3/160) (51/160) (1/160) tau := by
            convert childUR hs32200 hx32200 hy32200 using 1 <;> norm_num
          exact Batch0139.cell1114.sound htau (by
            simp only [Batch0139.cell1114, Batch0139.tau1114, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs322003 (by positivity) using 1 <;> norm_num)
    · have hs32202 : InSquare (1/80) (27/80) (1/80) tau := by
        convert childUL hs hx3220 hy3220 using 1 <;> norm_num
      rcases le_total tau.re (1/80 : ℝ) with hx32202 | hx32202
      · rcases le_total tau.im (27/80 : ℝ) with hy32202 | hy32202
        · have hs322020 : InSquare (1/160) (53/160) (1/160) tau := by
            convert childLL hs32202 hx32202 hy32202 using 1 <;> norm_num
          exact Batch0139.cell1119.sound htau (by
            simp only [Batch0139.cell1119, Batch0139.tau1119, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs322020 (by positivity) using 1 <;> norm_num)
        · have hs322022 : InSquare (1/160) (11/32) (1/160) tau := by
            convert childUL hs32202 hx32202 hy32202 using 1 <;> norm_num
          exact Batch0140.cell1121.sound htau (by
            simp only [Batch0140.cell1121, Batch0140.tau1121, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs322022 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (27/80 : ℝ) with hy32202 | hy32202
        · have hs322021 : InSquare (3/160) (53/160) (1/160) tau := by
            convert childLR hs32202 hx32202 hy32202 using 1 <;> norm_num
          exact Batch0140.cell1120.sound htau (by
            simp only [Batch0140.cell1120, Batch0140.tau1120, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs322021 (by positivity) using 1 <;> norm_num)
        · have hs322023 : InSquare (3/160) (11/32) (1/160) tau := by
            convert childUR hs32202 hx32202 hy32202 using 1 <;> norm_num
          exact Batch0140.cell1122.sound htau (by
            simp only [Batch0140.cell1122, Batch0140.tau1122, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs322023 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (13/40 : ℝ) with hy3220 | hy3220
    · have hs32201 : InSquare (3/80) (5/16) (1/80) tau := by
        convert childLR hs hx3220 hy3220 using 1 <;> norm_num
      rcases le_total tau.re (3/80 : ℝ) with hx32201 | hx32201
      · rcases le_total tau.im (5/16 : ℝ) with hy32201 | hy32201
        · have hs322010 : InSquare (1/32) (49/160) (1/160) tau := by
            convert childLL hs32201 hx32201 hy32201 using 1 <;> norm_num
          exact Batch0139.cell1115.sound htau (by
            simp only [Batch0139.cell1115, Batch0139.tau1115, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs322010 (by positivity) using 1 <;> norm_num)
        · have hs322012 : InSquare (1/32) (51/160) (1/160) tau := by
            convert childUL hs32201 hx32201 hy32201 using 1 <;> norm_num
          exact Batch0139.cell1117.sound htau (by
            simp only [Batch0139.cell1117, Batch0139.tau1117, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs322012 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (5/16 : ℝ) with hy32201 | hy32201
        · have hs322011 : InSquare (7/160) (49/160) (1/160) tau := by
            convert childLR hs32201 hx32201 hy32201 using 1 <;> norm_num
          exact Batch0139.cell1116.sound htau (by
            simp only [Batch0139.cell1116, Batch0139.tau1116, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs322011 (by positivity) using 1 <;> norm_num)
        · have hs322013 : InSquare (7/160) (51/160) (1/160) tau := by
            convert childUR hs32201 hx32201 hy32201 using 1 <;> norm_num
          exact Batch0139.cell1118.sound htau (by
            simp only [Batch0139.cell1118, Batch0139.tau1118, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs322013 (by positivity) using 1 <;> norm_num)
    · have hs32203 : InSquare (3/80) (27/80) (1/80) tau := by
        convert childUR hs hx3220 hy3220 using 1 <;> norm_num
      rcases le_total tau.re (3/80 : ℝ) with hx32203 | hx32203
      · rcases le_total tau.im (27/80 : ℝ) with hy32203 | hy32203
        · have hs322030 : InSquare (1/32) (53/160) (1/160) tau := by
            convert childLL hs32203 hx32203 hy32203 using 1 <;> norm_num
          exact Batch0140.cell1123.sound htau (by
            simp only [Batch0140.cell1123, Batch0140.tau1123, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs322030 (by positivity) using 1 <;> norm_num)
        · have hs322032 : InSquare (1/32) (11/32) (1/160) tau := by
            convert childUL hs32203 hx32203 hy32203 using 1 <;> norm_num
          exact Batch0140.cell1125.sound htau (by
            simp only [Batch0140.cell1125, Batch0140.tau1125, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs322032 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (27/80 : ℝ) with hy32203 | hy32203
        · have hs322031 : InSquare (7/160) (53/160) (1/160) tau := by
            convert childLR hs32203 hx32203 hy32203 using 1 <;> norm_num
          exact Batch0140.cell1124.sound htau (by
            simp only [Batch0140.cell1124, Batch0140.tau1124, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs322031 (by positivity) using 1 <;> norm_num)
        · have hs322033 : InSquare (7/160) (11/32) (1/160) tau := by
            convert childUR hs32203 hx32203 hy32203 using 1 <;> norm_num
          exact Batch0140.cell1126.sound htau (by
            simp only [Batch0140.cell1126, Batch0140.tau1126, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs322033 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3220
