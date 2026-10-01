import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0077
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0078
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0079

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1031

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (7/40) (-11/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (7/40 : ℝ) with hx1031 | hx1031
  · rcases le_total tau.im (-11/40 : ℝ) with hy1031 | hy1031
    · have hs10310 : InSquare (13/80) (-23/80) (1/80) tau := by
        convert childLL hs hx1031 hy1031 using 1 <;> norm_num
      rcases le_total tau.re (13/80 : ℝ) with hx10310 | hx10310
      · rcases le_total tau.im (-23/80 : ℝ) with hy10310 | hy10310
        · have hs103100 : InSquare (5/32) (-47/160) (1/160) tau := by
            convert childLL hs10310 hx10310 hy10310 using 1 <;> norm_num
          exact Batch0077.cell0622.sound htau (by
            simp only [Batch0077.cell0622, Batch0077.tau0622, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs103100 (by positivity) using 1 <;> norm_num)
        · have hs103102 : InSquare (5/32) (-9/32) (1/160) tau := by
            convert childUL hs10310 hx10310 hy10310 using 1 <;> norm_num
          exact Batch0078.cell0624.sound htau (by
            simp only [Batch0078.cell0624, Batch0078.tau0624, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs103102 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-23/80 : ℝ) with hy10310 | hy10310
        · have hs103101 : InSquare (27/160) (-47/160) (1/160) tau := by
            convert childLR hs10310 hx10310 hy10310 using 1 <;> norm_num
          exact Batch0077.cell0623.sound htau (by
            simp only [Batch0077.cell0623, Batch0077.tau0623, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs103101 (by positivity) using 1 <;> norm_num)
        · have hs103103 : InSquare (27/160) (-9/32) (1/160) tau := by
            convert childUR hs10310 hx10310 hy10310 using 1 <;> norm_num
          exact Batch0078.cell0625.sound htau (by
            simp only [Batch0078.cell0625, Batch0078.tau0625, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs103103 (by positivity) using 1 <;> norm_num)
    · have hs10312 : InSquare (13/80) (-21/80) (1/80) tau := by
        convert childUL hs hx1031 hy1031 using 1 <;> norm_num
      rcases le_total tau.re (13/80 : ℝ) with hx10312 | hx10312
      · rcases le_total tau.im (-21/80 : ℝ) with hy10312 | hy10312
        · have hs103120 : InSquare (5/32) (-43/160) (1/160) tau := by
            convert childLL hs10312 hx10312 hy10312 using 1 <;> norm_num
          exact Batch0078.cell0630.sound htau (by
            simp only [Batch0078.cell0630, Batch0078.tau0630, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs103120 (by positivity) using 1 <;> norm_num)
        · have hs103122 : InSquare (5/32) (-41/160) (1/160) tau := by
            convert childUL hs10312 hx10312 hy10312 using 1 <;> norm_num
          exact Batch0079.cell0632.sound htau (by
            simp only [Batch0079.cell0632, Batch0079.tau0632, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs103122 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-21/80 : ℝ) with hy10312 | hy10312
        · have hs103121 : InSquare (27/160) (-43/160) (1/160) tau := by
            convert childLR hs10312 hx10312 hy10312 using 1 <;> norm_num
          exact Batch0078.cell0631.sound htau (by
            simp only [Batch0078.cell0631, Batch0078.tau0631, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs103121 (by positivity) using 1 <;> norm_num)
        · have hs103123 : InSquare (27/160) (-41/160) (1/160) tau := by
            convert childUR hs10312 hx10312 hy10312 using 1 <;> norm_num
          exact Batch0079.cell0633.sound htau (by
            simp only [Batch0079.cell0633, Batch0079.tau0633, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs103123 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (-11/40 : ℝ) with hy1031 | hy1031
    · have hs10311 : InSquare (3/16) (-23/80) (1/80) tau := by
        convert childLR hs hx1031 hy1031 using 1 <;> norm_num
      rcases le_total tau.re (3/16 : ℝ) with hx10311 | hx10311
      · rcases le_total tau.im (-23/80 : ℝ) with hy10311 | hy10311
        · have hs103110 : InSquare (29/160) (-47/160) (1/160) tau := by
            convert childLL hs10311 hx10311 hy10311 using 1 <;> norm_num
          exact Batch0078.cell0626.sound htau (by
            simp only [Batch0078.cell0626, Batch0078.tau0626, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs103110 (by positivity) using 1 <;> norm_num)
        · have hs103112 : InSquare (29/160) (-9/32) (1/160) tau := by
            convert childUL hs10311 hx10311 hy10311 using 1 <;> norm_num
          exact Batch0078.cell0628.sound htau (by
            simp only [Batch0078.cell0628, Batch0078.tau0628, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs103112 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-23/80 : ℝ) with hy10311 | hy10311
        · have hs103111 : InSquare (31/160) (-47/160) (1/160) tau := by
            convert childLR hs10311 hx10311 hy10311 using 1 <;> norm_num
          exact Batch0078.cell0627.sound htau (by
            simp only [Batch0078.cell0627, Batch0078.tau0627, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs103111 (by positivity) using 1 <;> norm_num)
        · have hs103113 : InSquare (31/160) (-9/32) (1/160) tau := by
            convert childUR hs10311 hx10311 hy10311 using 1 <;> norm_num
          exact Batch0078.cell0629.sound htau (by
            simp only [Batch0078.cell0629, Batch0078.tau0629, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs103113 (by positivity) using 1 <;> norm_num)
    · have hs10313 : InSquare (3/16) (-21/80) (1/80) tau := by
        convert childUR hs hx1031 hy1031 using 1 <;> norm_num
      rcases le_total tau.re (3/16 : ℝ) with hx10313 | hx10313
      · rcases le_total tau.im (-21/80 : ℝ) with hy10313 | hy10313
        · have hs103130 : InSquare (29/160) (-43/160) (1/160) tau := by
            convert childLL hs10313 hx10313 hy10313 using 1 <;> norm_num
          exact Batch0079.cell0634.sound htau (by
            simp only [Batch0079.cell0634, Batch0079.tau0634, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs103130 (by positivity) using 1 <;> norm_num)
        · have hs103132 : InSquare (29/160) (-41/160) (1/160) tau := by
            convert childUL hs10313 hx10313 hy10313 using 1 <;> norm_num
          exact Batch0079.cell0636.sound htau (by
            simp only [Batch0079.cell0636, Batch0079.tau0636, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs103132 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-21/80 : ℝ) with hy10313 | hy10313
        · have hs103131 : InSquare (31/160) (-43/160) (1/160) tau := by
            convert childLR hs10313 hx10313 hy10313 using 1 <;> norm_num
          exact Batch0079.cell0635.sound htau (by
            simp only [Batch0079.cell0635, Batch0079.tau0635, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs103131 (by positivity) using 1 <;> norm_num)
        · have hs103133 : InSquare (31/160) (-41/160) (1/160) tau := by
            convert childUR hs10313 hx10313 hy10313 using 1 <;> norm_num
          exact Batch0079.cell0637.sound htau (by
            simp only [Batch0079.cell0637, Batch0079.tau0637, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs103133 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1031
