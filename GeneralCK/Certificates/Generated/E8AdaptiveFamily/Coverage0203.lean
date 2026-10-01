import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0009
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0064
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0065

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0203

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-13/40) (-1/8) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (-13/40 : ℝ) with hx0203 | hx0203
  · rcases le_total tau.im (-1/8 : ℝ) with hy0203 | hy0203
    · have hs02030 : InSquare (-27/80) (-11/80) (1/80) tau := by
        convert childLL hs hx0203 hy0203 using 1 <;> norm_num
      rcases le_total tau.re (-27/80 : ℝ) with hx02030 | hx02030
      · rcases le_total tau.im (-11/80 : ℝ) with hy02030 | hy02030
        · have hs020300 : InSquare (-11/32) (-23/160) (1/160) tau := by
            convert childLL hs02030 hx02030 hy02030 using 1 <;> norm_num
          exact Batch0064.cell0514.sound htau (by
            simp only [Batch0064.cell0514, Batch0064.tau0514, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs020300 (by positivity) using 1 <;> norm_num)
        · have hs020302 : InSquare (-11/32) (-21/160) (1/160) tau := by
            convert childUL hs02030 hx02030 hy02030 using 1 <;> norm_num
          exact Batch0064.cell0516.sound htau (by
            simp only [Batch0064.cell0516, Batch0064.tau0516, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs020302 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-11/80 : ℝ) with hy02030 | hy02030
        · have hs020301 : InSquare (-53/160) (-23/160) (1/160) tau := by
            convert childLR hs02030 hx02030 hy02030 using 1 <;> norm_num
          exact Batch0064.cell0515.sound htau (by
            simp only [Batch0064.cell0515, Batch0064.tau0515, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs020301 (by positivity) using 1 <;> norm_num)
        · have hs020303 : InSquare (-53/160) (-21/160) (1/160) tau := by
            convert childUR hs02030 hx02030 hy02030 using 1 <;> norm_num
          exact Batch0064.cell0517.sound htau (by
            simp only [Batch0064.cell0517, Batch0064.tau0517, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs020303 (by positivity) using 1 <;> norm_num)
    · have hs02032 : InSquare (-27/80) (-9/80) (1/80) tau := by
        convert childUL hs hx0203 hy0203 using 1 <;> norm_num
      rcases le_total tau.re (-27/80 : ℝ) with hx02032 | hx02032
      · rcases le_total tau.im (-9/80 : ℝ) with hy02032 | hy02032
        · have hs020320 : InSquare (-11/32) (-19/160) (1/160) tau := by
            convert childLL hs02032 hx02032 hy02032 using 1 <;> norm_num
          exact Batch0065.cell0522.sound htau (by
            simp only [Batch0065.cell0522, Batch0065.tau0522, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs020320 (by positivity) using 1 <;> norm_num)
        · have hs020322 : InSquare (-11/32) (-17/160) (1/160) tau := by
            convert childUL hs02032 hx02032 hy02032 using 1 <;> norm_num
          exact Batch0065.cell0524.sound htau (by
            simp only [Batch0065.cell0524, Batch0065.tau0524, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs020322 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-9/80 : ℝ) with hy02032 | hy02032
        · have hs020321 : InSquare (-53/160) (-19/160) (1/160) tau := by
            convert childLR hs02032 hx02032 hy02032 using 1 <;> norm_num
          exact Batch0065.cell0523.sound htau (by
            simp only [Batch0065.cell0523, Batch0065.tau0523, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs020321 (by positivity) using 1 <;> norm_num)
        · have hs020323 : InSquare (-53/160) (-17/160) (1/160) tau := by
            convert childUR hs02032 hx02032 hy02032 using 1 <;> norm_num
          exact Batch0065.cell0525.sound htau (by
            simp only [Batch0065.cell0525, Batch0065.tau0525, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs020323 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (-1/8 : ℝ) with hy0203 | hy0203
    · have hs02031 : InSquare (-5/16) (-11/80) (1/80) tau := by
        convert childLR hs hx0203 hy0203 using 1 <;> norm_num
      rcases le_total tau.re (-5/16 : ℝ) with hx02031 | hx02031
      · rcases le_total tau.im (-11/80 : ℝ) with hy02031 | hy02031
        · have hs020310 : InSquare (-51/160) (-23/160) (1/160) tau := by
            convert childLL hs02031 hx02031 hy02031 using 1 <;> norm_num
          exact Batch0064.cell0518.sound htau (by
            simp only [Batch0064.cell0518, Batch0064.tau0518, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs020310 (by positivity) using 1 <;> norm_num)
        · have hs020312 : InSquare (-51/160) (-21/160) (1/160) tau := by
            convert childUL hs02031 hx02031 hy02031 using 1 <;> norm_num
          exact Batch0065.cell0520.sound htau (by
            simp only [Batch0065.cell0520, Batch0065.tau0520, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs020312 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-11/80 : ℝ) with hy02031 | hy02031
        · have hs020311 : InSquare (-49/160) (-23/160) (1/160) tau := by
            convert childLR hs02031 hx02031 hy02031 using 1 <;> norm_num
          exact Batch0064.cell0519.sound htau (by
            simp only [Batch0064.cell0519, Batch0064.tau0519, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs020311 (by positivity) using 1 <;> norm_num)
        · have hs020313 : InSquare (-49/160) (-21/160) (1/160) tau := by
            convert childUR hs02031 hx02031 hy02031 using 1 <;> norm_num
          exact Batch0065.cell0521.sound htau (by
            simp only [Batch0065.cell0521, Batch0065.tau0521, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs020313 (by positivity) using 1 <;> norm_num)
    · have hs02033 : InSquare (-5/16) (-9/80) (1/80) tau := by
        convert childUR hs hx0203 hy0203 using 1 <;> norm_num
      exact Batch0009.cell0072.sound htau (by
        simp only [Batch0009.cell0072, Batch0009.tau0072, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs02033 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0203
