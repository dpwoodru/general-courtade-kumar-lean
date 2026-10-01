import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0007
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0059
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0060

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0130

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-3/40) (-11/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (-3/40 : ℝ) with hx0130 | hx0130
  · rcases le_total tau.im (-11/40 : ℝ) with hy0130 | hy0130
    · have hs01300 : InSquare (-7/80) (-23/80) (1/80) tau := by
        convert childLL hs hx0130 hy0130 using 1 <;> norm_num
      rcases le_total tau.re (-7/80 : ℝ) with hx01300 | hx01300
      · rcases le_total tau.im (-23/80 : ℝ) with hy01300 | hy01300
        · have hs013000 : InSquare (-3/32) (-47/160) (1/160) tau := by
            convert childLL hs01300 hx01300 hy01300 using 1 <;> norm_num
          exact Batch0059.cell0473.sound htau (by
            simp only [Batch0059.cell0473, Batch0059.tau0473, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs013000 (by positivity) using 1 <;> norm_num)
        · have hs013002 : InSquare (-3/32) (-9/32) (1/160) tau := by
            convert childUL hs01300 hx01300 hy01300 using 1 <;> norm_num
          exact Batch0059.cell0475.sound htau (by
            simp only [Batch0059.cell0475, Batch0059.tau0475, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs013002 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-23/80 : ℝ) with hy01300 | hy01300
        · have hs013001 : InSquare (-13/160) (-47/160) (1/160) tau := by
            convert childLR hs01300 hx01300 hy01300 using 1 <;> norm_num
          exact Batch0059.cell0474.sound htau (by
            simp only [Batch0059.cell0474, Batch0059.tau0474, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs013001 (by positivity) using 1 <;> norm_num)
        · have hs013003 : InSquare (-13/160) (-9/32) (1/160) tau := by
            convert childUR hs01300 hx01300 hy01300 using 1 <;> norm_num
          exact Batch0059.cell0476.sound htau (by
            simp only [Batch0059.cell0476, Batch0059.tau0476, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs013003 (by positivity) using 1 <;> norm_num)
    · have hs01302 : InSquare (-7/80) (-21/80) (1/80) tau := by
        convert childUL hs hx0130 hy0130 using 1 <;> norm_num
      exact Batch0007.cell0058.sound htau (by
        simp only [Batch0007.cell0058, Batch0007.tau0058, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs01302 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (-11/40 : ℝ) with hy0130 | hy0130
    · have hs01301 : InSquare (-1/16) (-23/80) (1/80) tau := by
        convert childLR hs hx0130 hy0130 using 1 <;> norm_num
      rcases le_total tau.re (-1/16 : ℝ) with hx01301 | hx01301
      · rcases le_total tau.im (-23/80 : ℝ) with hy01301 | hy01301
        · have hs013010 : InSquare (-11/160) (-47/160) (1/160) tau := by
            convert childLL hs01301 hx01301 hy01301 using 1 <;> norm_num
          exact Batch0059.cell0477.sound htau (by
            simp only [Batch0059.cell0477, Batch0059.tau0477, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs013010 (by positivity) using 1 <;> norm_num)
        · have hs013012 : InSquare (-11/160) (-9/32) (1/160) tau := by
            convert childUL hs01301 hx01301 hy01301 using 1 <;> norm_num
          exact Batch0059.cell0479.sound htau (by
            simp only [Batch0059.cell0479, Batch0059.tau0479, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs013012 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-23/80 : ℝ) with hy01301 | hy01301
        · have hs013011 : InSquare (-9/160) (-47/160) (1/160) tau := by
            convert childLR hs01301 hx01301 hy01301 using 1 <;> norm_num
          exact Batch0059.cell0478.sound htau (by
            simp only [Batch0059.cell0478, Batch0059.tau0478, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs013011 (by positivity) using 1 <;> norm_num)
        · have hs013013 : InSquare (-9/160) (-9/32) (1/160) tau := by
            convert childUR hs01301 hx01301 hy01301 using 1 <;> norm_num
          exact Batch0060.cell0480.sound htau (by
            simp only [Batch0060.cell0480, Batch0060.tau0480, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs013013 (by positivity) using 1 <;> norm_num)
    · have hs01303 : InSquare (-1/16) (-21/80) (1/80) tau := by
        convert childUR hs hx0130 hy0130 using 1 <;> norm_num
      exact Batch0007.cell0059.sound htau (by
        simp only [Batch0007.cell0059, Batch0007.tau0059, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs01303 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0130
