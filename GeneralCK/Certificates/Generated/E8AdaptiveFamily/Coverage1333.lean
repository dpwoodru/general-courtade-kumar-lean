import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0024
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0096

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1333

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (3/8) (-1/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (3/8 : ℝ) with hx1333 | hx1333
  · rcases le_total tau.im (-1/40 : ℝ) with hy1333 | hy1333
    · have hs13330 : InSquare (29/80) (-3/80) (1/80) tau := by
        convert childLL hs hx1333 hy1333 using 1 <;> norm_num
      exact Batch0024.cell0195.sound htau (by
        simp only [Batch0024.cell0195, Batch0024.tau0195, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs13330 (by positivity) using 1 <;> norm_num)
    · have hs13332 : InSquare (29/80) (-1/80) (1/80) tau := by
        convert childUL hs hx1333 hy1333 using 1 <;> norm_num
      exact Batch0024.cell0196.sound htau (by
        simp only [Batch0024.cell0196, Batch0024.tau0196, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs13332 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (-1/40 : ℝ) with hy1333 | hy1333
    · have hs13331 : InSquare (31/80) (-3/80) (1/80) tau := by
        convert childLR hs hx1333 hy1333 using 1 <;> norm_num
      rcases le_total tau.re (31/80 : ℝ) with hx13331 | hx13331
      · rcases le_total tau.im (-3/80 : ℝ) with hy13331 | hy13331
        · have hs133310 : InSquare (61/160) (-7/160) (1/160) tau := by
            convert childLL hs13331 hx13331 hy13331 using 1 <;> norm_num
          exact Batch0096.cell0768.sound htau (by
            simp only [Batch0096.cell0768, Batch0096.tau0768, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs133310 (by positivity) using 1 <;> norm_num)
        · have hs133312 : InSquare (61/160) (-1/32) (1/160) tau := by
            convert childUL hs13331 hx13331 hy13331 using 1 <;> norm_num
          exact Batch0096.cell0770.sound htau (by
            simp only [Batch0096.cell0770, Batch0096.tau0770, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs133312 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-3/80 : ℝ) with hy13331 | hy13331
        · have hs133311 : InSquare (63/160) (-7/160) (1/160) tau := by
            convert childLR hs13331 hx13331 hy13331 using 1 <;> norm_num
          exact Batch0096.cell0769.sound htau (by
            simp only [Batch0096.cell0769, Batch0096.tau0769, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs133311 (by positivity) using 1 <;> norm_num)
        · have hs133313 : InSquare (63/160) (-1/32) (1/160) tau := by
            convert childUR hs13331 hx13331 hy13331 using 1 <;> norm_num
          exact Batch0096.cell0771.sound htau (by
            simp only [Batch0096.cell0771, Batch0096.tau0771, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs133313 (by positivity) using 1 <;> norm_num)
    · have hs13333 : InSquare (31/80) (-1/80) (1/80) tau := by
        convert childUR hs hx1333 hy1333 using 1 <;> norm_num
      exact Batch0024.cell0197.sound htau (by
        simp only [Batch0024.cell0197, Batch0024.tau0197, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs13333 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1333
