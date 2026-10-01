import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0082
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0083
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0084

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1122

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (9/40) (-9/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (9/40 : ℝ) with hx1122 | hx1122
  · rcases le_total tau.im (-9/40 : ℝ) with hy1122 | hy1122
    · have hs11220 : InSquare (17/80) (-19/80) (1/80) tau := by
        convert childLL hs hx1122 hy1122 using 1 <;> norm_num
      rcases le_total tau.re (17/80 : ℝ) with hx11220 | hx11220
      · rcases le_total tau.im (-19/80 : ℝ) with hy11220 | hy11220
        · have hs112200 : InSquare (33/160) (-39/160) (1/160) tau := by
            convert childLL hs11220 hx11220 hy11220 using 1 <;> norm_num
          exact Batch0082.cell0658.sound htau (by
            simp only [Batch0082.cell0658, Batch0082.tau0658, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs112200 (by positivity) using 1 <;> norm_num)
        · have hs112202 : InSquare (33/160) (-37/160) (1/160) tau := by
            convert childUL hs11220 hx11220 hy11220 using 1 <;> norm_num
          exact Batch0082.cell0660.sound htau (by
            simp only [Batch0082.cell0660, Batch0082.tau0660, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs112202 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-19/80 : ℝ) with hy11220 | hy11220
        · have hs112201 : InSquare (7/32) (-39/160) (1/160) tau := by
            convert childLR hs11220 hx11220 hy11220 using 1 <;> norm_num
          exact Batch0082.cell0659.sound htau (by
            simp only [Batch0082.cell0659, Batch0082.tau0659, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs112201 (by positivity) using 1 <;> norm_num)
        · have hs112203 : InSquare (7/32) (-37/160) (1/160) tau := by
            convert childUR hs11220 hx11220 hy11220 using 1 <;> norm_num
          exact Batch0082.cell0661.sound htau (by
            simp only [Batch0082.cell0661, Batch0082.tau0661, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs112203 (by positivity) using 1 <;> norm_num)
    · have hs11222 : InSquare (17/80) (-17/80) (1/80) tau := by
        convert childUL hs hx1122 hy1122 using 1 <;> norm_num
      rcases le_total tau.re (17/80 : ℝ) with hx11222 | hx11222
      · rcases le_total tau.im (-17/80 : ℝ) with hy11222 | hy11222
        · have hs112220 : InSquare (33/160) (-7/32) (1/160) tau := by
            convert childLL hs11222 hx11222 hy11222 using 1 <;> norm_num
          exact Batch0083.cell0666.sound htau (by
            simp only [Batch0083.cell0666, Batch0083.tau0666, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs112220 (by positivity) using 1 <;> norm_num)
        · have hs112222 : InSquare (33/160) (-33/160) (1/160) tau := by
            convert childUL hs11222 hx11222 hy11222 using 1 <;> norm_num
          exact Batch0083.cell0668.sound htau (by
            simp only [Batch0083.cell0668, Batch0083.tau0668, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs112222 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-17/80 : ℝ) with hy11222 | hy11222
        · have hs112221 : InSquare (7/32) (-7/32) (1/160) tau := by
            convert childLR hs11222 hx11222 hy11222 using 1 <;> norm_num
          exact Batch0083.cell0667.sound htau (by
            simp only [Batch0083.cell0667, Batch0083.tau0667, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs112221 (by positivity) using 1 <;> norm_num)
        · have hs112223 : InSquare (7/32) (-33/160) (1/160) tau := by
            convert childUR hs11222 hx11222 hy11222 using 1 <;> norm_num
          exact Batch0083.cell0669.sound htau (by
            simp only [Batch0083.cell0669, Batch0083.tau0669, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs112223 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (-9/40 : ℝ) with hy1122 | hy1122
    · have hs11221 : InSquare (19/80) (-19/80) (1/80) tau := by
        convert childLR hs hx1122 hy1122 using 1 <;> norm_num
      rcases le_total tau.re (19/80 : ℝ) with hx11221 | hx11221
      · rcases le_total tau.im (-19/80 : ℝ) with hy11221 | hy11221
        · have hs112210 : InSquare (37/160) (-39/160) (1/160) tau := by
            convert childLL hs11221 hx11221 hy11221 using 1 <;> norm_num
          exact Batch0082.cell0662.sound htau (by
            simp only [Batch0082.cell0662, Batch0082.tau0662, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs112210 (by positivity) using 1 <;> norm_num)
        · have hs112212 : InSquare (37/160) (-37/160) (1/160) tau := by
            convert childUL hs11221 hx11221 hy11221 using 1 <;> norm_num
          exact Batch0083.cell0664.sound htau (by
            simp only [Batch0083.cell0664, Batch0083.tau0664, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs112212 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-19/80 : ℝ) with hy11221 | hy11221
        · have hs112211 : InSquare (39/160) (-39/160) (1/160) tau := by
            convert childLR hs11221 hx11221 hy11221 using 1 <;> norm_num
          exact Batch0082.cell0663.sound htau (by
            simp only [Batch0082.cell0663, Batch0082.tau0663, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs112211 (by positivity) using 1 <;> norm_num)
        · have hs112213 : InSquare (39/160) (-37/160) (1/160) tau := by
            convert childUR hs11221 hx11221 hy11221 using 1 <;> norm_num
          exact Batch0083.cell0665.sound htau (by
            simp only [Batch0083.cell0665, Batch0083.tau0665, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs112213 (by positivity) using 1 <;> norm_num)
    · have hs11223 : InSquare (19/80) (-17/80) (1/80) tau := by
        convert childUR hs hx1122 hy1122 using 1 <;> norm_num
      rcases le_total tau.re (19/80 : ℝ) with hx11223 | hx11223
      · rcases le_total tau.im (-17/80 : ℝ) with hy11223 | hy11223
        · have hs112230 : InSquare (37/160) (-7/32) (1/160) tau := by
            convert childLL hs11223 hx11223 hy11223 using 1 <;> norm_num
          exact Batch0083.cell0670.sound htau (by
            simp only [Batch0083.cell0670, Batch0083.tau0670, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs112230 (by positivity) using 1 <;> norm_num)
        · have hs112232 : InSquare (37/160) (-33/160) (1/160) tau := by
            convert childUL hs11223 hx11223 hy11223 using 1 <;> norm_num
          exact Batch0084.cell0672.sound htau (by
            simp only [Batch0084.cell0672, Batch0084.tau0672, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs112232 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-17/80 : ℝ) with hy11223 | hy11223
        · have hs112231 : InSquare (39/160) (-7/32) (1/160) tau := by
            convert childLR hs11223 hx11223 hy11223 using 1 <;> norm_num
          exact Batch0083.cell0671.sound htau (by
            simp only [Batch0083.cell0671, Batch0083.tau0671, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs112231 (by positivity) using 1 <;> norm_num)
        · have hs112233 : InSquare (39/160) (-33/160) (1/160) tau := by
            convert childUR hs11223 hx11223 hy11223 using 1 <;> norm_num
          exact Batch0084.cell0673.sound htau (by
            simp only [Batch0084.cell0673, Batch0084.tau0673, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs112233 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1122
