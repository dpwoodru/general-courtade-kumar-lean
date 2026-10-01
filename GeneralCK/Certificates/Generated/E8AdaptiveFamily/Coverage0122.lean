import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0006
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0058
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0059

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0122

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-7/40) (-9/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (-7/40 : ℝ) with hx0122 | hx0122
  · rcases le_total tau.im (-9/40 : ℝ) with hy0122 | hy0122
    · have hs01220 : InSquare (-3/16) (-19/80) (1/80) tau := by
        convert childLL hs hx0122 hy0122 using 1 <;> norm_num
      rcases le_total tau.re (-3/16 : ℝ) with hx01220 | hx01220
      · rcases le_total tau.im (-19/80 : ℝ) with hy01220 | hy01220
        · have hs012200 : InSquare (-31/160) (-39/160) (1/160) tau := by
            convert childLL hs01220 hx01220 hy01220 using 1 <;> norm_num
          exact Batch0058.cell0465.sound htau (by
            simp only [Batch0058.cell0465, Batch0058.tau0465, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs012200 (by positivity) using 1 <;> norm_num)
        · have hs012202 : InSquare (-31/160) (-37/160) (1/160) tau := by
            convert childUL hs01220 hx01220 hy01220 using 1 <;> norm_num
          exact Batch0058.cell0467.sound htau (by
            simp only [Batch0058.cell0467, Batch0058.tau0467, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs012202 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-19/80 : ℝ) with hy01220 | hy01220
        · have hs012201 : InSquare (-29/160) (-39/160) (1/160) tau := by
            convert childLR hs01220 hx01220 hy01220 using 1 <;> norm_num
          exact Batch0058.cell0466.sound htau (by
            simp only [Batch0058.cell0466, Batch0058.tau0466, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs012201 (by positivity) using 1 <;> norm_num)
        · have hs012203 : InSquare (-29/160) (-37/160) (1/160) tau := by
            convert childUR hs01220 hx01220 hy01220 using 1 <;> norm_num
          exact Batch0058.cell0468.sound htau (by
            simp only [Batch0058.cell0468, Batch0058.tau0468, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs012203 (by positivity) using 1 <;> norm_num)
    · have hs01222 : InSquare (-3/16) (-17/80) (1/80) tau := by
        convert childUL hs hx0122 hy0122 using 1 <;> norm_num
      exact Batch0006.cell0052.sound htau (by
        simp only [Batch0006.cell0052, Batch0006.tau0052, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs01222 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (-9/40 : ℝ) with hy0122 | hy0122
    · have hs01221 : InSquare (-13/80) (-19/80) (1/80) tau := by
        convert childLR hs hx0122 hy0122 using 1 <;> norm_num
      rcases le_total tau.re (-13/80 : ℝ) with hx01221 | hx01221
      · rcases le_total tau.im (-19/80 : ℝ) with hy01221 | hy01221
        · have hs012210 : InSquare (-27/160) (-39/160) (1/160) tau := by
            convert childLL hs01221 hx01221 hy01221 using 1 <;> norm_num
          exact Batch0058.cell0469.sound htau (by
            simp only [Batch0058.cell0469, Batch0058.tau0469, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs012210 (by positivity) using 1 <;> norm_num)
        · have hs012212 : InSquare (-27/160) (-37/160) (1/160) tau := by
            convert childUL hs01221 hx01221 hy01221 using 1 <;> norm_num
          exact Batch0058.cell0471.sound htau (by
            simp only [Batch0058.cell0471, Batch0058.tau0471, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs012212 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-19/80 : ℝ) with hy01221 | hy01221
        · have hs012211 : InSquare (-5/32) (-39/160) (1/160) tau := by
            convert childLR hs01221 hx01221 hy01221 using 1 <;> norm_num
          exact Batch0058.cell0470.sound htau (by
            simp only [Batch0058.cell0470, Batch0058.tau0470, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs012211 (by positivity) using 1 <;> norm_num)
        · have hs012213 : InSquare (-5/32) (-37/160) (1/160) tau := by
            convert childUR hs01221 hx01221 hy01221 using 1 <;> norm_num
          exact Batch0059.cell0472.sound htau (by
            simp only [Batch0059.cell0472, Batch0059.tau0472, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs012213 (by positivity) using 1 <;> norm_num)
    · have hs01223 : InSquare (-13/80) (-17/80) (1/80) tau := by
        convert childUR hs hx0122 hy0122 using 1 <;> norm_num
      exact Batch0006.cell0053.sound htau (by
        simp only [Batch0006.cell0053, Batch0006.tau0053, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs01223 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0122
