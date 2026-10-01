import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0016
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0074
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0075

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1021

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (3/40) (-11/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (3/40 : ℝ) with hx1021 | hx1021
  · rcases le_total tau.im (-11/40 : ℝ) with hy1021 | hy1021
    · have hs10210 : InSquare (1/16) (-23/80) (1/80) tau := by
        convert childLL hs hx1021 hy1021 using 1 <;> norm_num
      rcases le_total tau.re (1/16 : ℝ) with hx10210 | hx10210
      · rcases le_total tau.im (-23/80 : ℝ) with hy10210 | hy10210
        · have hs102100 : InSquare (9/160) (-47/160) (1/160) tau := by
            convert childLL hs10210 hx10210 hy10210 using 1 <;> norm_num
          exact Batch0074.cell0598.sound htau (by
            simp only [Batch0074.cell0598, Batch0074.tau0598, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs102100 (by positivity) using 1 <;> norm_num)
        · have hs102102 : InSquare (9/160) (-9/32) (1/160) tau := by
            convert childUL hs10210 hx10210 hy10210 using 1 <;> norm_num
          exact Batch0075.cell0600.sound htau (by
            simp only [Batch0075.cell0600, Batch0075.tau0600, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs102102 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-23/80 : ℝ) with hy10210 | hy10210
        · have hs102101 : InSquare (11/160) (-47/160) (1/160) tau := by
            convert childLR hs10210 hx10210 hy10210 using 1 <;> norm_num
          exact Batch0074.cell0599.sound htau (by
            simp only [Batch0074.cell0599, Batch0074.tau0599, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs102101 (by positivity) using 1 <;> norm_num)
        · have hs102103 : InSquare (11/160) (-9/32) (1/160) tau := by
            convert childUR hs10210 hx10210 hy10210 using 1 <;> norm_num
          exact Batch0075.cell0601.sound htau (by
            simp only [Batch0075.cell0601, Batch0075.tau0601, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs102103 (by positivity) using 1 <;> norm_num)
    · have hs10212 : InSquare (1/16) (-21/80) (1/80) tau := by
        convert childUL hs hx1021 hy1021 using 1 <;> norm_num
      exact Batch0016.cell0129.sound htau (by
        simp only [Batch0016.cell0129, Batch0016.tau0129, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs10212 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (-11/40 : ℝ) with hy1021 | hy1021
    · have hs10211 : InSquare (7/80) (-23/80) (1/80) tau := by
        convert childLR hs hx1021 hy1021 using 1 <;> norm_num
      rcases le_total tau.re (7/80 : ℝ) with hx10211 | hx10211
      · rcases le_total tau.im (-23/80 : ℝ) with hy10211 | hy10211
        · have hs102110 : InSquare (13/160) (-47/160) (1/160) tau := by
            convert childLL hs10211 hx10211 hy10211 using 1 <;> norm_num
          exact Batch0075.cell0602.sound htau (by
            simp only [Batch0075.cell0602, Batch0075.tau0602, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs102110 (by positivity) using 1 <;> norm_num)
        · have hs102112 : InSquare (13/160) (-9/32) (1/160) tau := by
            convert childUL hs10211 hx10211 hy10211 using 1 <;> norm_num
          exact Batch0075.cell0604.sound htau (by
            simp only [Batch0075.cell0604, Batch0075.tau0604, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs102112 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-23/80 : ℝ) with hy10211 | hy10211
        · have hs102111 : InSquare (3/32) (-47/160) (1/160) tau := by
            convert childLR hs10211 hx10211 hy10211 using 1 <;> norm_num
          exact Batch0075.cell0603.sound htau (by
            simp only [Batch0075.cell0603, Batch0075.tau0603, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs102111 (by positivity) using 1 <;> norm_num)
        · have hs102113 : InSquare (3/32) (-9/32) (1/160) tau := by
            convert childUR hs10211 hx10211 hy10211 using 1 <;> norm_num
          exact Batch0075.cell0605.sound htau (by
            simp only [Batch0075.cell0605, Batch0075.tau0605, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs102113 (by positivity) using 1 <;> norm_num)
    · have hs10213 : InSquare (7/80) (-21/80) (1/80) tau := by
        convert childUR hs hx1021 hy1021 using 1 <;> norm_num
      exact Batch0016.cell0130.sound htau (by
        simp only [Batch0016.cell0130, Batch0016.tau0130, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs10213 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1021
