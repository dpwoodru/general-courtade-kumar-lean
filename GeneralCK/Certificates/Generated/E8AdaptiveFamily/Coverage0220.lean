import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0010
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0067
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0068
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0069

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0220

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-3/8) (-3/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (-3/8 : ℝ) with hx0220 | hx0220
  · rcases le_total tau.im (-3/40 : ℝ) with hy0220 | hy0220
    · have hs02200 : InSquare (-31/80) (-7/80) (1/80) tau := by
        convert childLL hs hx0220 hy0220 using 1 <;> norm_num
      rcases le_total tau.re (-31/80 : ℝ) with hx02200 | hx02200
      · rcases le_total tau.im (-7/80 : ℝ) with hy02200 | hy02200
        · have hs022000 : InSquare (-63/160) (-3/32) (1/160) tau := by
            convert childLL hs02200 hx02200 hy02200 using 1 <;> norm_num
          exact Batch0067.cell0542.sound htau (by
            simp only [Batch0067.cell0542, Batch0067.tau0542, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs022000 (by positivity) using 1 <;> norm_num)
        · have hs022002 : InSquare (-63/160) (-13/160) (1/160) tau := by
            convert childUL hs02200 hx02200 hy02200 using 1 <;> norm_num
          exact Batch0068.cell0544.sound htau (by
            simp only [Batch0068.cell0544, Batch0068.tau0544, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs022002 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-7/80 : ℝ) with hy02200 | hy02200
        · have hs022001 : InSquare (-61/160) (-3/32) (1/160) tau := by
            convert childLR hs02200 hx02200 hy02200 using 1 <;> norm_num
          exact Batch0067.cell0543.sound htau (by
            simp only [Batch0067.cell0543, Batch0067.tau0543, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs022001 (by positivity) using 1 <;> norm_num)
        · have hs022003 : InSquare (-61/160) (-13/160) (1/160) tau := by
            convert childUR hs02200 hx02200 hy02200 using 1 <;> norm_num
          exact Batch0068.cell0545.sound htau (by
            simp only [Batch0068.cell0545, Batch0068.tau0545, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs022003 (by positivity) using 1 <;> norm_num)
    · have hs02202 : InSquare (-31/80) (-1/16) (1/80) tau := by
        convert childUL hs hx0220 hy0220 using 1 <;> norm_num
      rcases le_total tau.re (-31/80 : ℝ) with hx02202 | hx02202
      · rcases le_total tau.im (-1/16 : ℝ) with hy02202 | hy02202
        · have hs022020 : InSquare (-63/160) (-11/160) (1/160) tau := by
            convert childLL hs02202 hx02202 hy02202 using 1 <;> norm_num
          exact Batch0068.cell0550.sound htau (by
            simp only [Batch0068.cell0550, Batch0068.tau0550, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs022020 (by positivity) using 1 <;> norm_num)
        · have hs022022 : InSquare (-63/160) (-9/160) (1/160) tau := by
            convert childUL hs02202 hx02202 hy02202 using 1 <;> norm_num
          exact Batch0069.cell0552.sound htau (by
            simp only [Batch0069.cell0552, Batch0069.tau0552, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs022022 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-1/16 : ℝ) with hy02202 | hy02202
        · have hs022021 : InSquare (-61/160) (-11/160) (1/160) tau := by
            convert childLR hs02202 hx02202 hy02202 using 1 <;> norm_num
          exact Batch0068.cell0551.sound htau (by
            simp only [Batch0068.cell0551, Batch0068.tau0551, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs022021 (by positivity) using 1 <;> norm_num)
        · have hs022023 : InSquare (-61/160) (-9/160) (1/160) tau := by
            convert childUR hs02202 hx02202 hy02202 using 1 <;> norm_num
          exact Batch0069.cell0553.sound htau (by
            simp only [Batch0069.cell0553, Batch0069.tau0553, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs022023 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (-3/40 : ℝ) with hy0220 | hy0220
    · have hs02201 : InSquare (-29/80) (-7/80) (1/80) tau := by
        convert childLR hs hx0220 hy0220 using 1 <;> norm_num
      rcases le_total tau.re (-29/80 : ℝ) with hx02201 | hx02201
      · rcases le_total tau.im (-7/80 : ℝ) with hy02201 | hy02201
        · have hs022010 : InSquare (-59/160) (-3/32) (1/160) tau := by
            convert childLL hs02201 hx02201 hy02201 using 1 <;> norm_num
          exact Batch0068.cell0546.sound htau (by
            simp only [Batch0068.cell0546, Batch0068.tau0546, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs022010 (by positivity) using 1 <;> norm_num)
        · have hs022012 : InSquare (-59/160) (-13/160) (1/160) tau := by
            convert childUL hs02201 hx02201 hy02201 using 1 <;> norm_num
          exact Batch0068.cell0548.sound htau (by
            simp only [Batch0068.cell0548, Batch0068.tau0548, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs022012 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-7/80 : ℝ) with hy02201 | hy02201
        · have hs022011 : InSquare (-57/160) (-3/32) (1/160) tau := by
            convert childLR hs02201 hx02201 hy02201 using 1 <;> norm_num
          exact Batch0068.cell0547.sound htau (by
            simp only [Batch0068.cell0547, Batch0068.tau0547, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs022011 (by positivity) using 1 <;> norm_num)
        · have hs022013 : InSquare (-57/160) (-13/160) (1/160) tau := by
            convert childUR hs02201 hx02201 hy02201 using 1 <;> norm_num
          exact Batch0068.cell0549.sound htau (by
            simp only [Batch0068.cell0549, Batch0068.tau0549, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs022013 (by positivity) using 1 <;> norm_num)
    · have hs02203 : InSquare (-29/80) (-1/16) (1/80) tau := by
        convert childUR hs hx0220 hy0220 using 1 <;> norm_num
      exact Batch0010.cell0085.sound htau (by
        simp only [Batch0010.cell0085, Batch0010.tau0085, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs02203 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0220
