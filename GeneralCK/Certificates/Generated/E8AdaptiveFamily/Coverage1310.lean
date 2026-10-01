import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0088
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0089
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0090

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1310

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (13/40) (-7/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (13/40 : ℝ) with hx1310 | hx1310
  · rcases le_total tau.im (-7/40 : ℝ) with hy1310 | hy1310
    · have hs13100 : InSquare (5/16) (-3/16) (1/80) tau := by
        convert childLL hs hx1310 hy1310 using 1 <;> norm_num
      rcases le_total tau.re (5/16 : ℝ) with hx13100 | hx13100
      · rcases le_total tau.im (-3/16 : ℝ) with hy13100 | hy13100
        · have hs131000 : InSquare (49/160) (-31/160) (1/160) tau := by
            convert childLL hs13100 hx13100 hy13100 using 1 <;> norm_num
          exact Batch0088.cell0711.sound htau (by
            simp only [Batch0088.cell0711, Batch0088.tau0711, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs131000 (by positivity) using 1 <;> norm_num)
        · have hs131002 : InSquare (49/160) (-29/160) (1/160) tau := by
            convert childUL hs13100 hx13100 hy13100 using 1 <;> norm_num
          exact Batch0089.cell0713.sound htau (by
            simp only [Batch0089.cell0713, Batch0089.tau0713, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs131002 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-3/16 : ℝ) with hy13100 | hy13100
        · have hs131001 : InSquare (51/160) (-31/160) (1/160) tau := by
            convert childLR hs13100 hx13100 hy13100 using 1 <;> norm_num
          exact Batch0089.cell0712.sound htau (by
            simp only [Batch0089.cell0712, Batch0089.tau0712, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs131001 (by positivity) using 1 <;> norm_num)
        · have hs131003 : InSquare (51/160) (-29/160) (1/160) tau := by
            convert childUR hs13100 hx13100 hy13100 using 1 <;> norm_num
          exact Batch0089.cell0714.sound htau (by
            simp only [Batch0089.cell0714, Batch0089.tau0714, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs131003 (by positivity) using 1 <;> norm_num)
    · have hs13102 : InSquare (5/16) (-13/80) (1/80) tau := by
        convert childUL hs hx1310 hy1310 using 1 <;> norm_num
      rcases le_total tau.re (5/16 : ℝ) with hx13102 | hx13102
      · rcases le_total tau.im (-13/80 : ℝ) with hy13102 | hy13102
        · have hs131020 : InSquare (49/160) (-27/160) (1/160) tau := by
            convert childLL hs13102 hx13102 hy13102 using 1 <;> norm_num
          exact Batch0089.cell0719.sound htau (by
            simp only [Batch0089.cell0719, Batch0089.tau0719, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs131020 (by positivity) using 1 <;> norm_num)
        · have hs131022 : InSquare (49/160) (-5/32) (1/160) tau := by
            convert childUL hs13102 hx13102 hy13102 using 1 <;> norm_num
          exact Batch0090.cell0721.sound htau (by
            simp only [Batch0090.cell0721, Batch0090.tau0721, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs131022 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-13/80 : ℝ) with hy13102 | hy13102
        · have hs131021 : InSquare (51/160) (-27/160) (1/160) tau := by
            convert childLR hs13102 hx13102 hy13102 using 1 <;> norm_num
          exact Batch0090.cell0720.sound htau (by
            simp only [Batch0090.cell0720, Batch0090.tau0720, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs131021 (by positivity) using 1 <;> norm_num)
        · have hs131023 : InSquare (51/160) (-5/32) (1/160) tau := by
            convert childUR hs13102 hx13102 hy13102 using 1 <;> norm_num
          exact Batch0090.cell0722.sound htau (by
            simp only [Batch0090.cell0722, Batch0090.tau0722, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs131023 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (-7/40 : ℝ) with hy1310 | hy1310
    · have hs13101 : InSquare (27/80) (-3/16) (1/80) tau := by
        convert childLR hs hx1310 hy1310 using 1 <;> norm_num
      rcases le_total tau.re (27/80 : ℝ) with hx13101 | hx13101
      · rcases le_total tau.im (-3/16 : ℝ) with hy13101 | hy13101
        · have hs131010 : InSquare (53/160) (-31/160) (1/160) tau := by
            convert childLL hs13101 hx13101 hy13101 using 1 <;> norm_num
          exact Batch0089.cell0715.sound htau (by
            simp only [Batch0089.cell0715, Batch0089.tau0715, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs131010 (by positivity) using 1 <;> norm_num)
        · have hs131012 : InSquare (53/160) (-29/160) (1/160) tau := by
            convert childUL hs13101 hx13101 hy13101 using 1 <;> norm_num
          exact Batch0089.cell0717.sound htau (by
            simp only [Batch0089.cell0717, Batch0089.tau0717, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs131012 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-3/16 : ℝ) with hy13101 | hy13101
        · have hs131011 : InSquare (11/32) (-31/160) (1/160) tau := by
            convert childLR hs13101 hx13101 hy13101 using 1 <;> norm_num
          exact Batch0089.cell0716.sound htau (by
            simp only [Batch0089.cell0716, Batch0089.tau0716, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs131011 (by positivity) using 1 <;> norm_num)
        · have hs131013 : InSquare (11/32) (-29/160) (1/160) tau := by
            convert childUR hs13101 hx13101 hy13101 using 1 <;> norm_num
          exact Batch0089.cell0718.sound htau (by
            simp only [Batch0089.cell0718, Batch0089.tau0718, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs131013 (by positivity) using 1 <;> norm_num)
    · have hs13103 : InSquare (27/80) (-13/80) (1/80) tau := by
        convert childUR hs hx1310 hy1310 using 1 <;> norm_num
      rcases le_total tau.re (27/80 : ℝ) with hx13103 | hx13103
      · rcases le_total tau.im (-13/80 : ℝ) with hy13103 | hy13103
        · have hs131030 : InSquare (53/160) (-27/160) (1/160) tau := by
            convert childLL hs13103 hx13103 hy13103 using 1 <;> norm_num
          exact Batch0090.cell0723.sound htau (by
            simp only [Batch0090.cell0723, Batch0090.tau0723, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs131030 (by positivity) using 1 <;> norm_num)
        · have hs131032 : InSquare (53/160) (-5/32) (1/160) tau := by
            convert childUL hs13103 hx13103 hy13103 using 1 <;> norm_num
          exact Batch0090.cell0725.sound htau (by
            simp only [Batch0090.cell0725, Batch0090.tau0725, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs131032 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-13/80 : ℝ) with hy13103 | hy13103
        · have hs131031 : InSquare (11/32) (-27/160) (1/160) tau := by
            convert childLR hs13103 hx13103 hy13103 using 1 <;> norm_num
          exact Batch0090.cell0724.sound htau (by
            simp only [Batch0090.cell0724, Batch0090.tau0724, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs131031 (by positivity) using 1 <;> norm_num)
        · have hs131033 : InSquare (11/32) (-5/32) (1/160) tau := by
            convert childUR hs13103 hx13103 hy13103 using 1 <;> norm_num
          exact Batch0090.cell0726.sound htau (by
            simp only [Batch0090.cell0726, Batch0090.tau0726, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs131033 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1310
