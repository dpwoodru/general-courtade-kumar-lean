import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0054
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0055
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0056

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0120

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-7/40) (-11/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (-7/40 : ℝ) with hx0120 | hx0120
  · rcases le_total tau.im (-11/40 : ℝ) with hy0120 | hy0120
    · have hs01200 : InSquare (-3/16) (-23/80) (1/80) tau := by
        convert childLL hs hx0120 hy0120 using 1 <;> norm_num
      rcases le_total tau.re (-3/16 : ℝ) with hx01200 | hx01200
      · rcases le_total tau.im (-23/80 : ℝ) with hy01200 | hy01200
        · have hs012000 : InSquare (-31/160) (-47/160) (1/160) tau := by
            convert childLL hs01200 hx01200 hy01200 using 1 <;> norm_num
          exact Batch0054.cell0433.sound htau (by
            simp only [Batch0054.cell0433, Batch0054.tau0433, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs012000 (by positivity) using 1 <;> norm_num)
        · have hs012002 : InSquare (-31/160) (-9/32) (1/160) tau := by
            convert childUL hs01200 hx01200 hy01200 using 1 <;> norm_num
          exact Batch0054.cell0435.sound htau (by
            simp only [Batch0054.cell0435, Batch0054.tau0435, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs012002 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-23/80 : ℝ) with hy01200 | hy01200
        · have hs012001 : InSquare (-29/160) (-47/160) (1/160) tau := by
            convert childLR hs01200 hx01200 hy01200 using 1 <;> norm_num
          exact Batch0054.cell0434.sound htau (by
            simp only [Batch0054.cell0434, Batch0054.tau0434, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs012001 (by positivity) using 1 <;> norm_num)
        · have hs012003 : InSquare (-29/160) (-9/32) (1/160) tau := by
            convert childUR hs01200 hx01200 hy01200 using 1 <;> norm_num
          exact Batch0054.cell0436.sound htau (by
            simp only [Batch0054.cell0436, Batch0054.tau0436, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs012003 (by positivity) using 1 <;> norm_num)
    · have hs01202 : InSquare (-3/16) (-21/80) (1/80) tau := by
        convert childUL hs hx0120 hy0120 using 1 <;> norm_num
      rcases le_total tau.re (-3/16 : ℝ) with hx01202 | hx01202
      · rcases le_total tau.im (-21/80 : ℝ) with hy01202 | hy01202
        · have hs012020 : InSquare (-31/160) (-43/160) (1/160) tau := by
            convert childLL hs01202 hx01202 hy01202 using 1 <;> norm_num
          exact Batch0055.cell0441.sound htau (by
            simp only [Batch0055.cell0441, Batch0055.tau0441, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs012020 (by positivity) using 1 <;> norm_num)
        · have hs012022 : InSquare (-31/160) (-41/160) (1/160) tau := by
            convert childUL hs01202 hx01202 hy01202 using 1 <;> norm_num
          exact Batch0055.cell0443.sound htau (by
            simp only [Batch0055.cell0443, Batch0055.tau0443, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs012022 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-21/80 : ℝ) with hy01202 | hy01202
        · have hs012021 : InSquare (-29/160) (-43/160) (1/160) tau := by
            convert childLR hs01202 hx01202 hy01202 using 1 <;> norm_num
          exact Batch0055.cell0442.sound htau (by
            simp only [Batch0055.cell0442, Batch0055.tau0442, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs012021 (by positivity) using 1 <;> norm_num)
        · have hs012023 : InSquare (-29/160) (-41/160) (1/160) tau := by
            convert childUR hs01202 hx01202 hy01202 using 1 <;> norm_num
          exact Batch0055.cell0444.sound htau (by
            simp only [Batch0055.cell0444, Batch0055.tau0444, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs012023 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (-11/40 : ℝ) with hy0120 | hy0120
    · have hs01201 : InSquare (-13/80) (-23/80) (1/80) tau := by
        convert childLR hs hx0120 hy0120 using 1 <;> norm_num
      rcases le_total tau.re (-13/80 : ℝ) with hx01201 | hx01201
      · rcases le_total tau.im (-23/80 : ℝ) with hy01201 | hy01201
        · have hs012010 : InSquare (-27/160) (-47/160) (1/160) tau := by
            convert childLL hs01201 hx01201 hy01201 using 1 <;> norm_num
          exact Batch0054.cell0437.sound htau (by
            simp only [Batch0054.cell0437, Batch0054.tau0437, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs012010 (by positivity) using 1 <;> norm_num)
        · have hs012012 : InSquare (-27/160) (-9/32) (1/160) tau := by
            convert childUL hs01201 hx01201 hy01201 using 1 <;> norm_num
          exact Batch0054.cell0439.sound htau (by
            simp only [Batch0054.cell0439, Batch0054.tau0439, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs012012 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-23/80 : ℝ) with hy01201 | hy01201
        · have hs012011 : InSquare (-5/32) (-47/160) (1/160) tau := by
            convert childLR hs01201 hx01201 hy01201 using 1 <;> norm_num
          exact Batch0054.cell0438.sound htau (by
            simp only [Batch0054.cell0438, Batch0054.tau0438, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs012011 (by positivity) using 1 <;> norm_num)
        · have hs012013 : InSquare (-5/32) (-9/32) (1/160) tau := by
            convert childUR hs01201 hx01201 hy01201 using 1 <;> norm_num
          exact Batch0055.cell0440.sound htau (by
            simp only [Batch0055.cell0440, Batch0055.tau0440, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs012013 (by positivity) using 1 <;> norm_num)
    · have hs01203 : InSquare (-13/80) (-21/80) (1/80) tau := by
        convert childUR hs hx0120 hy0120 using 1 <;> norm_num
      rcases le_total tau.re (-13/80 : ℝ) with hx01203 | hx01203
      · rcases le_total tau.im (-21/80 : ℝ) with hy01203 | hy01203
        · have hs012030 : InSquare (-27/160) (-43/160) (1/160) tau := by
            convert childLL hs01203 hx01203 hy01203 using 1 <;> norm_num
          exact Batch0055.cell0445.sound htau (by
            simp only [Batch0055.cell0445, Batch0055.tau0445, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs012030 (by positivity) using 1 <;> norm_num)
        · have hs012032 : InSquare (-27/160) (-41/160) (1/160) tau := by
            convert childUL hs01203 hx01203 hy01203 using 1 <;> norm_num
          exact Batch0055.cell0447.sound htau (by
            simp only [Batch0055.cell0447, Batch0055.tau0447, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs012032 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-21/80 : ℝ) with hy01203 | hy01203
        · have hs012031 : InSquare (-5/32) (-43/160) (1/160) tau := by
            convert childLR hs01203 hx01203 hy01203 using 1 <;> norm_num
          exact Batch0055.cell0446.sound htau (by
            simp only [Batch0055.cell0446, Batch0055.tau0446, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs012031 (by positivity) using 1 <;> norm_num)
        · have hs012033 : InSquare (-5/32) (-41/160) (1/160) tau := by
            convert childUR hs01203 hx01203 hy01203 using 1 <;> norm_num
          exact Batch0056.cell0448.sound htau (by
            simp only [Batch0056.cell0448, Batch0056.tau0448, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs012033 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0120
