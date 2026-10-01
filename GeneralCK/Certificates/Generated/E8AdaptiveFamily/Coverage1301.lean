import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0020
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0087
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0088

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1301

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (11/40) (-7/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (11/40 : ℝ) with hx1301 | hx1301
  · rcases le_total tau.im (-7/40 : ℝ) with hy1301 | hy1301
    · have hs13010 : InSquare (21/80) (-3/16) (1/80) tau := by
        convert childLL hs hx1301 hy1301 using 1 <;> norm_num
      rcases le_total tau.re (21/80 : ℝ) with hx13010 | hx13010
      · rcases le_total tau.im (-3/16 : ℝ) with hy13010 | hy13010
        · have hs130100 : InSquare (41/160) (-31/160) (1/160) tau := by
            convert childLL hs13010 hx13010 hy13010 using 1 <;> norm_num
          exact Batch0087.cell0699.sound htau (by
            simp only [Batch0087.cell0699, Batch0087.tau0699, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs130100 (by positivity) using 1 <;> norm_num)
        · have hs130102 : InSquare (41/160) (-29/160) (1/160) tau := by
            convert childUL hs13010 hx13010 hy13010 using 1 <;> norm_num
          exact Batch0087.cell0701.sound htau (by
            simp only [Batch0087.cell0701, Batch0087.tau0701, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs130102 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-3/16 : ℝ) with hy13010 | hy13010
        · have hs130101 : InSquare (43/160) (-31/160) (1/160) tau := by
            convert childLR hs13010 hx13010 hy13010 using 1 <;> norm_num
          exact Batch0087.cell0700.sound htau (by
            simp only [Batch0087.cell0700, Batch0087.tau0700, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs130101 (by positivity) using 1 <;> norm_num)
        · have hs130103 : InSquare (43/160) (-29/160) (1/160) tau := by
            convert childUR hs13010 hx13010 hy13010 using 1 <;> norm_num
          exact Batch0087.cell0702.sound htau (by
            simp only [Batch0087.cell0702, Batch0087.tau0702, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs130103 (by positivity) using 1 <;> norm_num)
    · have hs13012 : InSquare (21/80) (-13/80) (1/80) tau := by
        convert childUL hs hx1301 hy1301 using 1 <;> norm_num
      exact Batch0020.cell0164.sound htau (by
        simp only [Batch0020.cell0164, Batch0020.tau0164, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs13012 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (-7/40 : ℝ) with hy1301 | hy1301
    · have hs13011 : InSquare (23/80) (-3/16) (1/80) tau := by
        convert childLR hs hx1301 hy1301 using 1 <;> norm_num
      rcases le_total tau.re (23/80 : ℝ) with hx13011 | hx13011
      · rcases le_total tau.im (-3/16 : ℝ) with hy13011 | hy13011
        · have hs130110 : InSquare (9/32) (-31/160) (1/160) tau := by
            convert childLL hs13011 hx13011 hy13011 using 1 <;> norm_num
          exact Batch0087.cell0703.sound htau (by
            simp only [Batch0087.cell0703, Batch0087.tau0703, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs130110 (by positivity) using 1 <;> norm_num)
        · have hs130112 : InSquare (9/32) (-29/160) (1/160) tau := by
            convert childUL hs13011 hx13011 hy13011 using 1 <;> norm_num
          exact Batch0088.cell0705.sound htau (by
            simp only [Batch0088.cell0705, Batch0088.tau0705, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs130112 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-3/16 : ℝ) with hy13011 | hy13011
        · have hs130111 : InSquare (47/160) (-31/160) (1/160) tau := by
            convert childLR hs13011 hx13011 hy13011 using 1 <;> norm_num
          exact Batch0088.cell0704.sound htau (by
            simp only [Batch0088.cell0704, Batch0088.tau0704, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs130111 (by positivity) using 1 <;> norm_num)
        · have hs130113 : InSquare (47/160) (-29/160) (1/160) tau := by
            convert childUR hs13011 hx13011 hy13011 using 1 <;> norm_num
          exact Batch0088.cell0706.sound htau (by
            simp only [Batch0088.cell0706, Batch0088.tau0706, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs130113 (by positivity) using 1 <;> norm_num)
    · have hs13013 : InSquare (23/80) (-13/80) (1/80) tau := by
        convert childUR hs hx1301 hy1301 using 1 <;> norm_num
      rcases le_total tau.re (23/80 : ℝ) with hx13013 | hx13013
      · rcases le_total tau.im (-13/80 : ℝ) with hy13013 | hy13013
        · have hs130130 : InSquare (9/32) (-27/160) (1/160) tau := by
            convert childLL hs13013 hx13013 hy13013 using 1 <;> norm_num
          exact Batch0088.cell0707.sound htau (by
            simp only [Batch0088.cell0707, Batch0088.tau0707, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs130130 (by positivity) using 1 <;> norm_num)
        · have hs130132 : InSquare (9/32) (-5/32) (1/160) tau := by
            convert childUL hs13013 hx13013 hy13013 using 1 <;> norm_num
          exact Batch0088.cell0709.sound htau (by
            simp only [Batch0088.cell0709, Batch0088.tau0709, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs130132 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-13/80 : ℝ) with hy13013 | hy13013
        · have hs130131 : InSquare (47/160) (-27/160) (1/160) tau := by
            convert childLR hs13013 hx13013 hy13013 using 1 <;> norm_num
          exact Batch0088.cell0708.sound htau (by
            simp only [Batch0088.cell0708, Batch0088.tau0708, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs130131 (by positivity) using 1 <;> norm_num)
        · have hs130133 : InSquare (47/160) (-5/32) (1/160) tau := by
            convert childUR hs13013 hx13013 hy13013 using 1 <;> norm_num
          exact Batch0088.cell0710.sound htau (by
            simp only [Batch0088.cell0710, Batch0088.tau0710, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs130133 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1301
