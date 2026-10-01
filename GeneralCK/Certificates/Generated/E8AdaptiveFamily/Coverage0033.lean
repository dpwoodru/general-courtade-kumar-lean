import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0047
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0048
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0049

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0033

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-9/40) (-9/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (-9/40 : ℝ) with hx0033 | hx0033
  · rcases le_total tau.im (-9/40 : ℝ) with hy0033 | hy0033
    · have hs00330 : InSquare (-19/80) (-19/80) (1/80) tau := by
        convert childLL hs hx0033 hy0033 using 1 <;> norm_num
      rcases le_total tau.re (-19/80 : ℝ) with hx00330 | hx00330
      · rcases le_total tau.im (-19/80 : ℝ) with hy00330 | hy00330
        · have hs003300 : InSquare (-39/160) (-39/160) (1/160) tau := by
            convert childLL hs00330 hx00330 hy00330 using 1 <;> norm_num
          exact Batch0047.cell0377.sound htau (by
            simp only [Batch0047.cell0377, Batch0047.tau0377, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs003300 (by positivity) using 1 <;> norm_num)
        · have hs003302 : InSquare (-39/160) (-37/160) (1/160) tau := by
            convert childUL hs00330 hx00330 hy00330 using 1 <;> norm_num
          exact Batch0047.cell0379.sound htau (by
            simp only [Batch0047.cell0379, Batch0047.tau0379, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs003302 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-19/80 : ℝ) with hy00330 | hy00330
        · have hs003301 : InSquare (-37/160) (-39/160) (1/160) tau := by
            convert childLR hs00330 hx00330 hy00330 using 1 <;> norm_num
          exact Batch0047.cell0378.sound htau (by
            simp only [Batch0047.cell0378, Batch0047.tau0378, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs003301 (by positivity) using 1 <;> norm_num)
        · have hs003303 : InSquare (-37/160) (-37/160) (1/160) tau := by
            convert childUR hs00330 hx00330 hy00330 using 1 <;> norm_num
          exact Batch0047.cell0380.sound htau (by
            simp only [Batch0047.cell0380, Batch0047.tau0380, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs003303 (by positivity) using 1 <;> norm_num)
    · have hs00332 : InSquare (-19/80) (-17/80) (1/80) tau := by
        convert childUL hs hx0033 hy0033 using 1 <;> norm_num
      rcases le_total tau.re (-19/80 : ℝ) with hx00332 | hx00332
      · rcases le_total tau.im (-17/80 : ℝ) with hy00332 | hy00332
        · have hs003320 : InSquare (-39/160) (-7/32) (1/160) tau := by
            convert childLL hs00332 hx00332 hy00332 using 1 <;> norm_num
          exact Batch0048.cell0385.sound htau (by
            simp only [Batch0048.cell0385, Batch0048.tau0385, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs003320 (by positivity) using 1 <;> norm_num)
        · have hs003322 : InSquare (-39/160) (-33/160) (1/160) tau := by
            convert childUL hs00332 hx00332 hy00332 using 1 <;> norm_num
          exact Batch0048.cell0387.sound htau (by
            simp only [Batch0048.cell0387, Batch0048.tau0387, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs003322 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-17/80 : ℝ) with hy00332 | hy00332
        · have hs003321 : InSquare (-37/160) (-7/32) (1/160) tau := by
            convert childLR hs00332 hx00332 hy00332 using 1 <;> norm_num
          exact Batch0048.cell0386.sound htau (by
            simp only [Batch0048.cell0386, Batch0048.tau0386, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs003321 (by positivity) using 1 <;> norm_num)
        · have hs003323 : InSquare (-37/160) (-33/160) (1/160) tau := by
            convert childUR hs00332 hx00332 hy00332 using 1 <;> norm_num
          exact Batch0048.cell0388.sound htau (by
            simp only [Batch0048.cell0388, Batch0048.tau0388, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs003323 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (-9/40 : ℝ) with hy0033 | hy0033
    · have hs00331 : InSquare (-17/80) (-19/80) (1/80) tau := by
        convert childLR hs hx0033 hy0033 using 1 <;> norm_num
      rcases le_total tau.re (-17/80 : ℝ) with hx00331 | hx00331
      · rcases le_total tau.im (-19/80 : ℝ) with hy00331 | hy00331
        · have hs003310 : InSquare (-7/32) (-39/160) (1/160) tau := by
            convert childLL hs00331 hx00331 hy00331 using 1 <;> norm_num
          exact Batch0047.cell0381.sound htau (by
            simp only [Batch0047.cell0381, Batch0047.tau0381, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs003310 (by positivity) using 1 <;> norm_num)
        · have hs003312 : InSquare (-7/32) (-37/160) (1/160) tau := by
            convert childUL hs00331 hx00331 hy00331 using 1 <;> norm_num
          exact Batch0047.cell0383.sound htau (by
            simp only [Batch0047.cell0383, Batch0047.tau0383, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs003312 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-19/80 : ℝ) with hy00331 | hy00331
        · have hs003311 : InSquare (-33/160) (-39/160) (1/160) tau := by
            convert childLR hs00331 hx00331 hy00331 using 1 <;> norm_num
          exact Batch0047.cell0382.sound htau (by
            simp only [Batch0047.cell0382, Batch0047.tau0382, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs003311 (by positivity) using 1 <;> norm_num)
        · have hs003313 : InSquare (-33/160) (-37/160) (1/160) tau := by
            convert childUR hs00331 hx00331 hy00331 using 1 <;> norm_num
          exact Batch0048.cell0384.sound htau (by
            simp only [Batch0048.cell0384, Batch0048.tau0384, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs003313 (by positivity) using 1 <;> norm_num)
    · have hs00333 : InSquare (-17/80) (-17/80) (1/80) tau := by
        convert childUR hs hx0033 hy0033 using 1 <;> norm_num
      rcases le_total tau.re (-17/80 : ℝ) with hx00333 | hx00333
      · rcases le_total tau.im (-17/80 : ℝ) with hy00333 | hy00333
        · have hs003330 : InSquare (-7/32) (-7/32) (1/160) tau := by
            convert childLL hs00333 hx00333 hy00333 using 1 <;> norm_num
          exact Batch0048.cell0389.sound htau (by
            simp only [Batch0048.cell0389, Batch0048.tau0389, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs003330 (by positivity) using 1 <;> norm_num)
        · have hs003332 : InSquare (-7/32) (-33/160) (1/160) tau := by
            convert childUL hs00333 hx00333 hy00333 using 1 <;> norm_num
          exact Batch0048.cell0391.sound htau (by
            simp only [Batch0048.cell0391, Batch0048.tau0391, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs003332 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-17/80 : ℝ) with hy00333 | hy00333
        · have hs003331 : InSquare (-33/160) (-7/32) (1/160) tau := by
            convert childLR hs00333 hx00333 hy00333 using 1 <;> norm_num
          exact Batch0048.cell0390.sound htau (by
            simp only [Batch0048.cell0390, Batch0048.tau0390, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs003331 (by positivity) using 1 <;> norm_num)
        · have hs003333 : InSquare (-33/160) (-33/160) (1/160) tau := by
            convert childUR hs00333 hx00333 hy00333 using 1 <;> norm_num
          exact Batch0049.cell0392.sound htau (by
            simp only [Batch0049.cell0392, Batch0049.tau0392, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs003333 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0033
