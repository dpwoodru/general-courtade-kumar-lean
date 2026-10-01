import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0069
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0070
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0071

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1002

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (1/40) (-13/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (1/40 : ℝ) with hx1002 | hx1002
  · rcases le_total tau.im (-13/40 : ℝ) with hy1002 | hy1002
    · have hs10020 : InSquare (1/80) (-27/80) (1/80) tau := by
        convert childLL hs hx1002 hy1002 using 1 <;> norm_num
      rcases le_total tau.re (1/80 : ℝ) with hx10020 | hx10020
      · rcases le_total tau.im (-27/80 : ℝ) with hy10020 | hy10020
        · have hs100200 : InSquare (1/160) (-11/32) (1/160) tau := by
            convert childLL hs10020 hx10020 hy10020 using 1 <;> norm_num
          exact Batch0069.cell0559.sound htau (by
            simp only [Batch0069.cell0559, Batch0069.tau0559, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs100200 (by positivity) using 1 <;> norm_num)
        · have hs100202 : InSquare (1/160) (-53/160) (1/160) tau := by
            convert childUL hs10020 hx10020 hy10020 using 1 <;> norm_num
          exact Batch0070.cell0561.sound htau (by
            simp only [Batch0070.cell0561, Batch0070.tau0561, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs100202 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-27/80 : ℝ) with hy10020 | hy10020
        · have hs100201 : InSquare (3/160) (-11/32) (1/160) tau := by
            convert childLR hs10020 hx10020 hy10020 using 1 <;> norm_num
          exact Batch0070.cell0560.sound htau (by
            simp only [Batch0070.cell0560, Batch0070.tau0560, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs100201 (by positivity) using 1 <;> norm_num)
        · have hs100203 : InSquare (3/160) (-53/160) (1/160) tau := by
            convert childUR hs10020 hx10020 hy10020 using 1 <;> norm_num
          exact Batch0070.cell0562.sound htau (by
            simp only [Batch0070.cell0562, Batch0070.tau0562, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs100203 (by positivity) using 1 <;> norm_num)
    · have hs10022 : InSquare (1/80) (-5/16) (1/80) tau := by
        convert childUL hs hx1002 hy1002 using 1 <;> norm_num
      rcases le_total tau.re (1/80 : ℝ) with hx10022 | hx10022
      · rcases le_total tau.im (-5/16 : ℝ) with hy10022 | hy10022
        · have hs100220 : InSquare (1/160) (-51/160) (1/160) tau := by
            convert childLL hs10022 hx10022 hy10022 using 1 <;> norm_num
          exact Batch0070.cell0567.sound htau (by
            simp only [Batch0070.cell0567, Batch0070.tau0567, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs100220 (by positivity) using 1 <;> norm_num)
        · have hs100222 : InSquare (1/160) (-49/160) (1/160) tau := by
            convert childUL hs10022 hx10022 hy10022 using 1 <;> norm_num
          exact Batch0071.cell0569.sound htau (by
            simp only [Batch0071.cell0569, Batch0071.tau0569, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs100222 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-5/16 : ℝ) with hy10022 | hy10022
        · have hs100221 : InSquare (3/160) (-51/160) (1/160) tau := by
            convert childLR hs10022 hx10022 hy10022 using 1 <;> norm_num
          exact Batch0071.cell0568.sound htau (by
            simp only [Batch0071.cell0568, Batch0071.tau0568, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs100221 (by positivity) using 1 <;> norm_num)
        · have hs100223 : InSquare (3/160) (-49/160) (1/160) tau := by
            convert childUR hs10022 hx10022 hy10022 using 1 <;> norm_num
          exact Batch0071.cell0570.sound htau (by
            simp only [Batch0071.cell0570, Batch0071.tau0570, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs100223 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (-13/40 : ℝ) with hy1002 | hy1002
    · have hs10021 : InSquare (3/80) (-27/80) (1/80) tau := by
        convert childLR hs hx1002 hy1002 using 1 <;> norm_num
      rcases le_total tau.re (3/80 : ℝ) with hx10021 | hx10021
      · rcases le_total tau.im (-27/80 : ℝ) with hy10021 | hy10021
        · have hs100210 : InSquare (1/32) (-11/32) (1/160) tau := by
            convert childLL hs10021 hx10021 hy10021 using 1 <;> norm_num
          exact Batch0070.cell0563.sound htau (by
            simp only [Batch0070.cell0563, Batch0070.tau0563, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs100210 (by positivity) using 1 <;> norm_num)
        · have hs100212 : InSquare (1/32) (-53/160) (1/160) tau := by
            convert childUL hs10021 hx10021 hy10021 using 1 <;> norm_num
          exact Batch0070.cell0565.sound htau (by
            simp only [Batch0070.cell0565, Batch0070.tau0565, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs100212 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-27/80 : ℝ) with hy10021 | hy10021
        · have hs100211 : InSquare (7/160) (-11/32) (1/160) tau := by
            convert childLR hs10021 hx10021 hy10021 using 1 <;> norm_num
          exact Batch0070.cell0564.sound htau (by
            simp only [Batch0070.cell0564, Batch0070.tau0564, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs100211 (by positivity) using 1 <;> norm_num)
        · have hs100213 : InSquare (7/160) (-53/160) (1/160) tau := by
            convert childUR hs10021 hx10021 hy10021 using 1 <;> norm_num
          exact Batch0070.cell0566.sound htau (by
            simp only [Batch0070.cell0566, Batch0070.tau0566, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs100213 (by positivity) using 1 <;> norm_num)
    · have hs10023 : InSquare (3/80) (-5/16) (1/80) tau := by
        convert childUR hs hx1002 hy1002 using 1 <;> norm_num
      rcases le_total tau.re (3/80 : ℝ) with hx10023 | hx10023
      · rcases le_total tau.im (-5/16 : ℝ) with hy10023 | hy10023
        · have hs100230 : InSquare (1/32) (-51/160) (1/160) tau := by
            convert childLL hs10023 hx10023 hy10023 using 1 <;> norm_num
          exact Batch0071.cell0571.sound htau (by
            simp only [Batch0071.cell0571, Batch0071.tau0571, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs100230 (by positivity) using 1 <;> norm_num)
        · have hs100232 : InSquare (1/32) (-49/160) (1/160) tau := by
            convert childUL hs10023 hx10023 hy10023 using 1 <;> norm_num
          exact Batch0071.cell0573.sound htau (by
            simp only [Batch0071.cell0573, Batch0071.tau0573, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs100232 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-5/16 : ℝ) with hy10023 | hy10023
        · have hs100231 : InSquare (7/160) (-51/160) (1/160) tau := by
            convert childLR hs10023 hx10023 hy10023 using 1 <;> norm_num
          exact Batch0071.cell0572.sound htau (by
            simp only [Batch0071.cell0572, Batch0071.tau0572, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs100231 (by positivity) using 1 <;> norm_num)
        · have hs100233 : InSquare (7/160) (-49/160) (1/160) tau := by
            convert childUR hs10023 hx10023 hy10023 using 1 <;> norm_num
          exact Batch0071.cell0574.sound htau (by
            simp only [Batch0071.cell0574, Batch0071.tau0574, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs100233 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1002
