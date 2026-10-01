import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0009
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0065
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0066
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0067

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0210

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-11/40) (-7/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (-11/40 : ℝ) with hx0210 | hx0210
  · rcases le_total tau.im (-7/40 : ℝ) with hy0210 | hy0210
    · have hs02100 : InSquare (-23/80) (-3/16) (1/80) tau := by
        convert childLL hs hx0210 hy0210 using 1 <;> norm_num
      rcases le_total tau.re (-23/80 : ℝ) with hx02100 | hx02100
      · rcases le_total tau.im (-3/16 : ℝ) with hy02100 | hy02100
        · have hs021000 : InSquare (-47/160) (-31/160) (1/160) tau := by
            convert childLL hs02100 hx02100 hy02100 using 1 <;> norm_num
          exact Batch0065.cell0526.sound htau (by
            simp only [Batch0065.cell0526, Batch0065.tau0526, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs021000 (by positivity) using 1 <;> norm_num)
        · have hs021002 : InSquare (-47/160) (-29/160) (1/160) tau := by
            convert childUL hs02100 hx02100 hy02100 using 1 <;> norm_num
          exact Batch0066.cell0528.sound htau (by
            simp only [Batch0066.cell0528, Batch0066.tau0528, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs021002 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-3/16 : ℝ) with hy02100 | hy02100
        · have hs021001 : InSquare (-9/32) (-31/160) (1/160) tau := by
            convert childLR hs02100 hx02100 hy02100 using 1 <;> norm_num
          exact Batch0065.cell0527.sound htau (by
            simp only [Batch0065.cell0527, Batch0065.tau0527, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs021001 (by positivity) using 1 <;> norm_num)
        · have hs021003 : InSquare (-9/32) (-29/160) (1/160) tau := by
            convert childUR hs02100 hx02100 hy02100 using 1 <;> norm_num
          exact Batch0066.cell0529.sound htau (by
            simp only [Batch0066.cell0529, Batch0066.tau0529, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs021003 (by positivity) using 1 <;> norm_num)
    · have hs02102 : InSquare (-23/80) (-13/80) (1/80) tau := by
        convert childUL hs hx0210 hy0210 using 1 <;> norm_num
      rcases le_total tau.re (-23/80 : ℝ) with hx02102 | hx02102
      · rcases le_total tau.im (-13/80 : ℝ) with hy02102 | hy02102
        · have hs021020 : InSquare (-47/160) (-27/160) (1/160) tau := by
            convert childLL hs02102 hx02102 hy02102 using 1 <;> norm_num
          exact Batch0066.cell0534.sound htau (by
            simp only [Batch0066.cell0534, Batch0066.tau0534, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs021020 (by positivity) using 1 <;> norm_num)
        · have hs021022 : InSquare (-47/160) (-5/32) (1/160) tau := by
            convert childUL hs02102 hx02102 hy02102 using 1 <;> norm_num
          exact Batch0067.cell0536.sound htau (by
            simp only [Batch0067.cell0536, Batch0067.tau0536, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs021022 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-13/80 : ℝ) with hy02102 | hy02102
        · have hs021021 : InSquare (-9/32) (-27/160) (1/160) tau := by
            convert childLR hs02102 hx02102 hy02102 using 1 <;> norm_num
          exact Batch0066.cell0535.sound htau (by
            simp only [Batch0066.cell0535, Batch0066.tau0535, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs021021 (by positivity) using 1 <;> norm_num)
        · have hs021023 : InSquare (-9/32) (-5/32) (1/160) tau := by
            convert childUR hs02102 hx02102 hy02102 using 1 <;> norm_num
          exact Batch0067.cell0537.sound htau (by
            simp only [Batch0067.cell0537, Batch0067.tau0537, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs021023 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (-7/40 : ℝ) with hy0210 | hy0210
    · have hs02101 : InSquare (-21/80) (-3/16) (1/80) tau := by
        convert childLR hs hx0210 hy0210 using 1 <;> norm_num
      rcases le_total tau.re (-21/80 : ℝ) with hx02101 | hx02101
      · rcases le_total tau.im (-3/16 : ℝ) with hy02101 | hy02101
        · have hs021010 : InSquare (-43/160) (-31/160) (1/160) tau := by
            convert childLL hs02101 hx02101 hy02101 using 1 <;> norm_num
          exact Batch0066.cell0530.sound htau (by
            simp only [Batch0066.cell0530, Batch0066.tau0530, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs021010 (by positivity) using 1 <;> norm_num)
        · have hs021012 : InSquare (-43/160) (-29/160) (1/160) tau := by
            convert childUL hs02101 hx02101 hy02101 using 1 <;> norm_num
          exact Batch0066.cell0532.sound htau (by
            simp only [Batch0066.cell0532, Batch0066.tau0532, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs021012 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-3/16 : ℝ) with hy02101 | hy02101
        · have hs021011 : InSquare (-41/160) (-31/160) (1/160) tau := by
            convert childLR hs02101 hx02101 hy02101 using 1 <;> norm_num
          exact Batch0066.cell0531.sound htau (by
            simp only [Batch0066.cell0531, Batch0066.tau0531, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs021011 (by positivity) using 1 <;> norm_num)
        · have hs021013 : InSquare (-41/160) (-29/160) (1/160) tau := by
            convert childUR hs02101 hx02101 hy02101 using 1 <;> norm_num
          exact Batch0066.cell0533.sound htau (by
            simp only [Batch0066.cell0533, Batch0066.tau0533, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs021013 (by positivity) using 1 <;> norm_num)
    · have hs02103 : InSquare (-21/80) (-13/80) (1/80) tau := by
        convert childUR hs hx0210 hy0210 using 1 <;> norm_num
      exact Batch0009.cell0073.sound htau (by
        simp only [Batch0009.cell0073, Batch0009.tau0073, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs02103 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0210
