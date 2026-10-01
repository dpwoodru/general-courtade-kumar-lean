import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0017
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0018
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0079
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0080

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1033

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (7/40) (-9/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (7/40 : ℝ) with hx1033 | hx1033
  · rcases le_total tau.im (-9/40 : ℝ) with hy1033 | hy1033
    · have hs10330 : InSquare (13/80) (-19/80) (1/80) tau := by
        convert childLL hs hx1033 hy1033 using 1 <;> norm_num
      rcases le_total tau.re (13/80 : ℝ) with hx10330 | hx10330
      · rcases le_total tau.im (-19/80 : ℝ) with hy10330 | hy10330
        · have hs103300 : InSquare (5/32) (-39/160) (1/160) tau := by
            convert childLL hs10330 hx10330 hy10330 using 1 <;> norm_num
          exact Batch0079.cell0638.sound htau (by
            simp only [Batch0079.cell0638, Batch0079.tau0638, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs103300 (by positivity) using 1 <;> norm_num)
        · have hs103302 : InSquare (5/32) (-37/160) (1/160) tau := by
            convert childUL hs10330 hx10330 hy10330 using 1 <;> norm_num
          exact Batch0080.cell0640.sound htau (by
            simp only [Batch0080.cell0640, Batch0080.tau0640, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs103302 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-19/80 : ℝ) with hy10330 | hy10330
        · have hs103301 : InSquare (27/160) (-39/160) (1/160) tau := by
            convert childLR hs10330 hx10330 hy10330 using 1 <;> norm_num
          exact Batch0079.cell0639.sound htau (by
            simp only [Batch0079.cell0639, Batch0079.tau0639, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs103301 (by positivity) using 1 <;> norm_num)
        · have hs103303 : InSquare (27/160) (-37/160) (1/160) tau := by
            convert childUR hs10330 hx10330 hy10330 using 1 <;> norm_num
          exact Batch0080.cell0641.sound htau (by
            simp only [Batch0080.cell0641, Batch0080.tau0641, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs103303 (by positivity) using 1 <;> norm_num)
    · have hs10332 : InSquare (13/80) (-17/80) (1/80) tau := by
        convert childUL hs hx1033 hy1033 using 1 <;> norm_num
      exact Batch0017.cell0143.sound htau (by
        simp only [Batch0017.cell0143, Batch0017.tau0143, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs10332 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (-9/40 : ℝ) with hy1033 | hy1033
    · have hs10331 : InSquare (3/16) (-19/80) (1/80) tau := by
        convert childLR hs hx1033 hy1033 using 1 <;> norm_num
      rcases le_total tau.re (3/16 : ℝ) with hx10331 | hx10331
      · rcases le_total tau.im (-19/80 : ℝ) with hy10331 | hy10331
        · have hs103310 : InSquare (29/160) (-39/160) (1/160) tau := by
            convert childLL hs10331 hx10331 hy10331 using 1 <;> norm_num
          exact Batch0080.cell0642.sound htau (by
            simp only [Batch0080.cell0642, Batch0080.tau0642, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs103310 (by positivity) using 1 <;> norm_num)
        · have hs103312 : InSquare (29/160) (-37/160) (1/160) tau := by
            convert childUL hs10331 hx10331 hy10331 using 1 <;> norm_num
          exact Batch0080.cell0644.sound htau (by
            simp only [Batch0080.cell0644, Batch0080.tau0644, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs103312 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-19/80 : ℝ) with hy10331 | hy10331
        · have hs103311 : InSquare (31/160) (-39/160) (1/160) tau := by
            convert childLR hs10331 hx10331 hy10331 using 1 <;> norm_num
          exact Batch0080.cell0643.sound htau (by
            simp only [Batch0080.cell0643, Batch0080.tau0643, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs103311 (by positivity) using 1 <;> norm_num)
        · have hs103313 : InSquare (31/160) (-37/160) (1/160) tau := by
            convert childUR hs10331 hx10331 hy10331 using 1 <;> norm_num
          exact Batch0080.cell0645.sound htau (by
            simp only [Batch0080.cell0645, Batch0080.tau0645, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs103313 (by positivity) using 1 <;> norm_num)
    · have hs10333 : InSquare (3/16) (-17/80) (1/80) tau := by
        convert childUR hs hx1033 hy1033 using 1 <;> norm_num
      exact Batch0018.cell0144.sound htau (by
        simp only [Batch0018.cell0144, Batch0018.tau0144, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs10333 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1033
