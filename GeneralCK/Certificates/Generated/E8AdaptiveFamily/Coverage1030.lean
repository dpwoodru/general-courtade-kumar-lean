import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0075
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0076
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0077

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1030

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (1/8) (-11/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (1/8 : ℝ) with hx1030 | hx1030
  · rcases le_total tau.im (-11/40 : ℝ) with hy1030 | hy1030
    · have hs10300 : InSquare (9/80) (-23/80) (1/80) tau := by
        convert childLL hs hx1030 hy1030 using 1 <;> norm_num
      rcases le_total tau.re (9/80 : ℝ) with hx10300 | hx10300
      · rcases le_total tau.im (-23/80 : ℝ) with hy10300 | hy10300
        · have hs103000 : InSquare (17/160) (-47/160) (1/160) tau := by
            convert childLL hs10300 hx10300 hy10300 using 1 <;> norm_num
          exact Batch0075.cell0606.sound htau (by
            simp only [Batch0075.cell0606, Batch0075.tau0606, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs103000 (by positivity) using 1 <;> norm_num)
        · have hs103002 : InSquare (17/160) (-9/32) (1/160) tau := by
            convert childUL hs10300 hx10300 hy10300 using 1 <;> norm_num
          exact Batch0076.cell0608.sound htau (by
            simp only [Batch0076.cell0608, Batch0076.tau0608, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs103002 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-23/80 : ℝ) with hy10300 | hy10300
        · have hs103001 : InSquare (19/160) (-47/160) (1/160) tau := by
            convert childLR hs10300 hx10300 hy10300 using 1 <;> norm_num
          exact Batch0075.cell0607.sound htau (by
            simp only [Batch0075.cell0607, Batch0075.tau0607, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs103001 (by positivity) using 1 <;> norm_num)
        · have hs103003 : InSquare (19/160) (-9/32) (1/160) tau := by
            convert childUR hs10300 hx10300 hy10300 using 1 <;> norm_num
          exact Batch0076.cell0609.sound htau (by
            simp only [Batch0076.cell0609, Batch0076.tau0609, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs103003 (by positivity) using 1 <;> norm_num)
    · have hs10302 : InSquare (9/80) (-21/80) (1/80) tau := by
        convert childUL hs hx1030 hy1030 using 1 <;> norm_num
      rcases le_total tau.re (9/80 : ℝ) with hx10302 | hx10302
      · rcases le_total tau.im (-21/80 : ℝ) with hy10302 | hy10302
        · have hs103020 : InSquare (17/160) (-43/160) (1/160) tau := by
            convert childLL hs10302 hx10302 hy10302 using 1 <;> norm_num
          exact Batch0076.cell0614.sound htau (by
            simp only [Batch0076.cell0614, Batch0076.tau0614, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs103020 (by positivity) using 1 <;> norm_num)
        · have hs103022 : InSquare (17/160) (-41/160) (1/160) tau := by
            convert childUL hs10302 hx10302 hy10302 using 1 <;> norm_num
          exact Batch0077.cell0616.sound htau (by
            simp only [Batch0077.cell0616, Batch0077.tau0616, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs103022 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-21/80 : ℝ) with hy10302 | hy10302
        · have hs103021 : InSquare (19/160) (-43/160) (1/160) tau := by
            convert childLR hs10302 hx10302 hy10302 using 1 <;> norm_num
          exact Batch0076.cell0615.sound htau (by
            simp only [Batch0076.cell0615, Batch0076.tau0615, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs103021 (by positivity) using 1 <;> norm_num)
        · have hs103023 : InSquare (19/160) (-41/160) (1/160) tau := by
            convert childUR hs10302 hx10302 hy10302 using 1 <;> norm_num
          exact Batch0077.cell0617.sound htau (by
            simp only [Batch0077.cell0617, Batch0077.tau0617, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs103023 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (-11/40 : ℝ) with hy1030 | hy1030
    · have hs10301 : InSquare (11/80) (-23/80) (1/80) tau := by
        convert childLR hs hx1030 hy1030 using 1 <;> norm_num
      rcases le_total tau.re (11/80 : ℝ) with hx10301 | hx10301
      · rcases le_total tau.im (-23/80 : ℝ) with hy10301 | hy10301
        · have hs103010 : InSquare (21/160) (-47/160) (1/160) tau := by
            convert childLL hs10301 hx10301 hy10301 using 1 <;> norm_num
          exact Batch0076.cell0610.sound htau (by
            simp only [Batch0076.cell0610, Batch0076.tau0610, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs103010 (by positivity) using 1 <;> norm_num)
        · have hs103012 : InSquare (21/160) (-9/32) (1/160) tau := by
            convert childUL hs10301 hx10301 hy10301 using 1 <;> norm_num
          exact Batch0076.cell0612.sound htau (by
            simp only [Batch0076.cell0612, Batch0076.tau0612, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs103012 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-23/80 : ℝ) with hy10301 | hy10301
        · have hs103011 : InSquare (23/160) (-47/160) (1/160) tau := by
            convert childLR hs10301 hx10301 hy10301 using 1 <;> norm_num
          exact Batch0076.cell0611.sound htau (by
            simp only [Batch0076.cell0611, Batch0076.tau0611, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs103011 (by positivity) using 1 <;> norm_num)
        · have hs103013 : InSquare (23/160) (-9/32) (1/160) tau := by
            convert childUR hs10301 hx10301 hy10301 using 1 <;> norm_num
          exact Batch0076.cell0613.sound htau (by
            simp only [Batch0076.cell0613, Batch0076.tau0613, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs103013 (by positivity) using 1 <;> norm_num)
    · have hs10303 : InSquare (11/80) (-21/80) (1/80) tau := by
        convert childUR hs hx1030 hy1030 using 1 <;> norm_num
      rcases le_total tau.re (11/80 : ℝ) with hx10303 | hx10303
      · rcases le_total tau.im (-21/80 : ℝ) with hy10303 | hy10303
        · have hs103030 : InSquare (21/160) (-43/160) (1/160) tau := by
            convert childLL hs10303 hx10303 hy10303 using 1 <;> norm_num
          exact Batch0077.cell0618.sound htau (by
            simp only [Batch0077.cell0618, Batch0077.tau0618, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs103030 (by positivity) using 1 <;> norm_num)
        · have hs103032 : InSquare (21/160) (-41/160) (1/160) tau := by
            convert childUL hs10303 hx10303 hy10303 using 1 <;> norm_num
          exact Batch0077.cell0620.sound htau (by
            simp only [Batch0077.cell0620, Batch0077.tau0620, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs103032 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-21/80 : ℝ) with hy10303 | hy10303
        · have hs103031 : InSquare (23/160) (-43/160) (1/160) tau := by
            convert childLR hs10303 hx10303 hy10303 using 1 <;> norm_num
          exact Batch0077.cell0619.sound htau (by
            simp only [Batch0077.cell0619, Batch0077.tau0619, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs103031 (by positivity) using 1 <;> norm_num)
        · have hs103033 : InSquare (23/160) (-41/160) (1/160) tau := by
            convert childUR hs10303 hx10303 hy10303 using 1 <;> norm_num
          exact Batch0077.cell0621.sound htau (by
            simp only [Batch0077.cell0621, Batch0077.tau0621, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs103033 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1030
