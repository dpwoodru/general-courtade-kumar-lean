import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0023
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0094
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0095

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1331

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (3/8) (-3/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (3/8 : ℝ) with hx1331 | hx1331
  · rcases le_total tau.im (-3/40 : ℝ) with hy1331 | hy1331
    · have hs13310 : InSquare (29/80) (-7/80) (1/80) tau := by
        convert childLL hs hx1331 hy1331 using 1 <;> norm_num
      rcases le_total tau.re (29/80 : ℝ) with hx13310 | hx13310
      · rcases le_total tau.im (-7/80 : ℝ) with hy13310 | hy13310
        · have hs133100 : InSquare (57/160) (-3/32) (1/160) tau := by
            convert childLL hs13310 hx13310 hy13310 using 1 <;> norm_num
          exact Batch0094.cell0756.sound htau (by
            simp only [Batch0094.cell0756, Batch0094.tau0756, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs133100 (by positivity) using 1 <;> norm_num)
        · have hs133102 : InSquare (57/160) (-13/160) (1/160) tau := by
            convert childUL hs13310 hx13310 hy13310 using 1 <;> norm_num
          exact Batch0094.cell0758.sound htau (by
            simp only [Batch0094.cell0758, Batch0094.tau0758, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs133102 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-7/80 : ℝ) with hy13310 | hy13310
        · have hs133101 : InSquare (59/160) (-3/32) (1/160) tau := by
            convert childLR hs13310 hx13310 hy13310 using 1 <;> norm_num
          exact Batch0094.cell0757.sound htau (by
            simp only [Batch0094.cell0757, Batch0094.tau0757, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs133101 (by positivity) using 1 <;> norm_num)
        · have hs133103 : InSquare (59/160) (-13/160) (1/160) tau := by
            convert childUR hs13310 hx13310 hy13310 using 1 <;> norm_num
          exact Batch0094.cell0759.sound htau (by
            simp only [Batch0094.cell0759, Batch0094.tau0759, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs133103 (by positivity) using 1 <;> norm_num)
    · have hs13312 : InSquare (29/80) (-1/16) (1/80) tau := by
        convert childUL hs hx1331 hy1331 using 1 <;> norm_num
      exact Batch0023.cell0190.sound htau (by
        simp only [Batch0023.cell0190, Batch0023.tau0190, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs13312 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (-3/40 : ℝ) with hy1331 | hy1331
    · have hs13311 : InSquare (31/80) (-7/80) (1/80) tau := by
        convert childLR hs hx1331 hy1331 using 1 <;> norm_num
      rcases le_total tau.re (31/80 : ℝ) with hx13311 | hx13311
      · rcases le_total tau.im (-7/80 : ℝ) with hy13311 | hy13311
        · have hs133110 : InSquare (61/160) (-3/32) (1/160) tau := by
            convert childLL hs13311 hx13311 hy13311 using 1 <;> norm_num
          exact Batch0095.cell0760.sound htau (by
            simp only [Batch0095.cell0760, Batch0095.tau0760, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs133110 (by positivity) using 1 <;> norm_num)
        · have hs133112 : InSquare (61/160) (-13/160) (1/160) tau := by
            convert childUL hs13311 hx13311 hy13311 using 1 <;> norm_num
          exact Batch0095.cell0762.sound htau (by
            simp only [Batch0095.cell0762, Batch0095.tau0762, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs133112 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-7/80 : ℝ) with hy13311 | hy13311
        · have hs133111 : InSquare (63/160) (-3/32) (1/160) tau := by
            convert childLR hs13311 hx13311 hy13311 using 1 <;> norm_num
          exact Batch0095.cell0761.sound htau (by
            simp only [Batch0095.cell0761, Batch0095.tau0761, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs133111 (by positivity) using 1 <;> norm_num)
        · have hs133113 : InSquare (63/160) (-13/160) (1/160) tau := by
            convert childUR hs13311 hx13311 hy13311 using 1 <;> norm_num
          exact Batch0095.cell0763.sound htau (by
            simp only [Batch0095.cell0763, Batch0095.tau0763, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs133113 (by positivity) using 1 <;> norm_num)
    · have hs13313 : InSquare (31/80) (-1/16) (1/80) tau := by
        convert childUR hs hx1331 hy1331 using 1 <;> norm_num
      rcases le_total tau.re (31/80 : ℝ) with hx13313 | hx13313
      · rcases le_total tau.im (-1/16 : ℝ) with hy13313 | hy13313
        · have hs133130 : InSquare (61/160) (-11/160) (1/160) tau := by
            convert childLL hs13313 hx13313 hy13313 using 1 <;> norm_num
          exact Batch0095.cell0764.sound htau (by
            simp only [Batch0095.cell0764, Batch0095.tau0764, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs133130 (by positivity) using 1 <;> norm_num)
        · have hs133132 : InSquare (61/160) (-9/160) (1/160) tau := by
            convert childUL hs13313 hx13313 hy13313 using 1 <;> norm_num
          exact Batch0095.cell0766.sound htau (by
            simp only [Batch0095.cell0766, Batch0095.tau0766, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs133132 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-1/16 : ℝ) with hy13313 | hy13313
        · have hs133131 : InSquare (63/160) (-11/160) (1/160) tau := by
            convert childLR hs13313 hx13313 hy13313 using 1 <;> norm_num
          exact Batch0095.cell0765.sound htau (by
            simp only [Batch0095.cell0765, Batch0095.tau0765, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs133131 (by positivity) using 1 <;> norm_num)
        · have hs133133 : InSquare (63/160) (-9/160) (1/160) tau := by
            convert childUR hs13313 hx13313 hy13313 using 1 <;> norm_num
          exact Batch0095.cell0767.sound htau (by
            simp only [Batch0095.cell0767, Batch0095.tau0767, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs133133 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1331
