import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0011
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0069

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0222

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-3/8) (-1/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (-3/8 : ℝ) with hx0222 | hx0222
  · rcases le_total tau.im (-1/40 : ℝ) with hy0222 | hy0222
    · have hs02220 : InSquare (-31/80) (-3/80) (1/80) tau := by
        convert childLL hs hx0222 hy0222 using 1 <;> norm_num
      rcases le_total tau.re (-31/80 : ℝ) with hx02220 | hx02220
      · rcases le_total tau.im (-3/80 : ℝ) with hy02220 | hy02220
        · have hs022200 : InSquare (-63/160) (-7/160) (1/160) tau := by
            convert childLL hs02220 hx02220 hy02220 using 1 <;> norm_num
          exact Batch0069.cell0554.sound htau (by
            simp only [Batch0069.cell0554, Batch0069.tau0554, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs022200 (by positivity) using 1 <;> norm_num)
        · have hs022202 : InSquare (-63/160) (-1/32) (1/160) tau := by
            convert childUL hs02220 hx02220 hy02220 using 1 <;> norm_num
          exact Batch0069.cell0556.sound htau (by
            simp only [Batch0069.cell0556, Batch0069.tau0556, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs022202 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-3/80 : ℝ) with hy02220 | hy02220
        · have hs022201 : InSquare (-61/160) (-7/160) (1/160) tau := by
            convert childLR hs02220 hx02220 hy02220 using 1 <;> norm_num
          exact Batch0069.cell0555.sound htau (by
            simp only [Batch0069.cell0555, Batch0069.tau0555, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs022201 (by positivity) using 1 <;> norm_num)
        · have hs022203 : InSquare (-61/160) (-1/32) (1/160) tau := by
            convert childUR hs02220 hx02220 hy02220 using 1 <;> norm_num
          exact Batch0069.cell0557.sound htau (by
            simp only [Batch0069.cell0557, Batch0069.tau0557, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs022203 (by positivity) using 1 <;> norm_num)
    · have hs02222 : InSquare (-31/80) (-1/80) (1/80) tau := by
        convert childUL hs hx0222 hy0222 using 1 <;> norm_num
      exact Batch0011.cell0091.sound htau (by
        simp only [Batch0011.cell0091, Batch0011.tau0091, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs02222 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (-1/40 : ℝ) with hy0222 | hy0222
    · have hs02221 : InSquare (-29/80) (-3/80) (1/80) tau := by
        convert childLR hs hx0222 hy0222 using 1 <;> norm_num
      exact Batch0011.cell0090.sound htau (by
        simp only [Batch0011.cell0090, Batch0011.tau0090, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs02221 (by positivity) using 1 <;> norm_num)
    · have hs02223 : InSquare (-29/80) (-1/80) (1/80) tau := by
        convert childUR hs hx0222 hy0222 using 1 <;> norm_num
      exact Batch0011.cell0092.sound htau (by
        simp only [Batch0011.cell0092, Batch0011.tau0092, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs02223 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0222
