import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0009
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0067

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0211

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-9/40) (-7/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (-9/40 : ℝ) with hx0211 | hx0211
  · rcases le_total tau.im (-7/40 : ℝ) with hy0211 | hy0211
    · have hs02110 : InSquare (-19/80) (-3/16) (1/80) tau := by
        convert childLL hs hx0211 hy0211 using 1 <;> norm_num
      rcases le_total tau.re (-19/80 : ℝ) with hx02110 | hx02110
      · rcases le_total tau.im (-3/16 : ℝ) with hy02110 | hy02110
        · have hs021100 : InSquare (-39/160) (-31/160) (1/160) tau := by
            convert childLL hs02110 hx02110 hy02110 using 1 <;> norm_num
          exact Batch0067.cell0538.sound htau (by
            simp only [Batch0067.cell0538, Batch0067.tau0538, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs021100 (by positivity) using 1 <;> norm_num)
        · have hs021102 : InSquare (-39/160) (-29/160) (1/160) tau := by
            convert childUL hs02110 hx02110 hy02110 using 1 <;> norm_num
          exact Batch0067.cell0540.sound htau (by
            simp only [Batch0067.cell0540, Batch0067.tau0540, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs021102 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-3/16 : ℝ) with hy02110 | hy02110
        · have hs021101 : InSquare (-37/160) (-31/160) (1/160) tau := by
            convert childLR hs02110 hx02110 hy02110 using 1 <;> norm_num
          exact Batch0067.cell0539.sound htau (by
            simp only [Batch0067.cell0539, Batch0067.tau0539, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs021101 (by positivity) using 1 <;> norm_num)
        · have hs021103 : InSquare (-37/160) (-29/160) (1/160) tau := by
            convert childUR hs02110 hx02110 hy02110 using 1 <;> norm_num
          exact Batch0067.cell0541.sound htau (by
            simp only [Batch0067.cell0541, Batch0067.tau0541, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs021103 (by positivity) using 1 <;> norm_num)
    · have hs02112 : InSquare (-19/80) (-13/80) (1/80) tau := by
        convert childUL hs hx0211 hy0211 using 1 <;> norm_num
      exact Batch0009.cell0075.sound htau (by
        simp only [Batch0009.cell0075, Batch0009.tau0075, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs02112 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (-7/40 : ℝ) with hy0211 | hy0211
    · have hs02111 : InSquare (-17/80) (-3/16) (1/80) tau := by
        convert childLR hs hx0211 hy0211 using 1 <;> norm_num
      exact Batch0009.cell0074.sound htau (by
        simp only [Batch0009.cell0074, Batch0009.tau0074, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs02111 (by positivity) using 1 <;> norm_num)
    · have hs02113 : InSquare (-17/80) (-13/80) (1/80) tau := by
        convert childUR hs hx0211 hy0211 using 1 <;> norm_num
      exact Batch0009.cell0076.sound htau (by
        simp only [Batch0009.cell0076, Batch0009.tau0076, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs02113 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0211
