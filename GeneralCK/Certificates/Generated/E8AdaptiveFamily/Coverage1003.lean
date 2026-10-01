import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0071
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0072
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0073
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0202
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0203

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1003

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (3/40) (-13/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (3/40 : ℝ) with hx1003 | hx1003
  · rcases le_total tau.im (-13/40 : ℝ) with hy1003 | hy1003
    · have hs10030 : InSquare (1/16) (-27/80) (1/80) tau := by
        convert childLL hs hx1003 hy1003 using 1 <;> norm_num
      rcases le_total tau.re (1/16 : ℝ) with hx10030 | hx10030
      · rcases le_total tau.im (-27/80 : ℝ) with hy10030 | hy10030
        · have hs100300 : InSquare (9/160) (-11/32) (1/160) tau := by
            convert childLL hs10030 hx10030 hy10030 using 1 <;> norm_num
          exact Batch0071.cell0575.sound htau (by
            simp only [Batch0071.cell0575, Batch0071.tau0575, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs100300 (by positivity) using 1 <;> norm_num)
        · have hs100302 : InSquare (9/160) (-53/160) (1/160) tau := by
            convert childUL hs10030 hx10030 hy10030 using 1 <;> norm_num
          exact Batch0072.cell0576.sound htau (by
            simp only [Batch0072.cell0576, Batch0072.tau0576, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs100302 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-27/80 : ℝ) with hy10030 | hy10030
        · have hs100301 : InSquare (11/160) (-11/32) (1/160) tau := by
            convert childLR hs10030 hx10030 hy10030 using 1 <;> norm_num
          rcases le_total tau.re (11/160 : ℝ) with hx100301 | hx100301
          · rcases le_total tau.im (-11/32 : ℝ) with hy100301 | hy100301
            · have hs1003010 : InSquare (21/320) (-111/320) (1/320) tau := by
                convert childLL hs100301 hx100301 hy100301 using 1 <;> norm_num
              exact Batch0202.cell1617.sound htau (by
                simp only [Batch0202.cell1617, Batch0202.tau1617, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1003010 (by positivity) using 1 <;> norm_num)
            · have hs1003012 : InSquare (21/320) (-109/320) (1/320) tau := by
                convert childUL hs100301 hx100301 hy100301 using 1 <;> norm_num
              exact Batch0202.cell1619.sound htau (by
                simp only [Batch0202.cell1619, Batch0202.tau1619, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1003012 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-11/32 : ℝ) with hy100301 | hy100301
            · have hs1003011 : InSquare (23/320) (-111/320) (1/320) tau := by
                convert childLR hs100301 hx100301 hy100301 using 1 <;> norm_num
              exact Batch0202.cell1618.sound htau (by
                simp only [Batch0202.cell1618, Batch0202.tau1618, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1003011 (by positivity) using 1 <;> norm_num)
            · have hs1003013 : InSquare (23/320) (-109/320) (1/320) tau := by
                convert childUR hs100301 hx100301 hy100301 using 1 <;> norm_num
              exact Batch0202.cell1620.sound htau (by
                simp only [Batch0202.cell1620, Batch0202.tau1620, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1003013 (by positivity) using 1 <;> norm_num)
        · have hs100303 : InSquare (11/160) (-53/160) (1/160) tau := by
            convert childUR hs10030 hx10030 hy10030 using 1 <;> norm_num
          exact Batch0072.cell0577.sound htau (by
            simp only [Batch0072.cell0577, Batch0072.tau0577, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs100303 (by positivity) using 1 <;> norm_num)
    · have hs10032 : InSquare (1/16) (-5/16) (1/80) tau := by
        convert childUL hs hx1003 hy1003 using 1 <;> norm_num
      rcases le_total tau.re (1/16 : ℝ) with hx10032 | hx10032
      · rcases le_total tau.im (-5/16 : ℝ) with hy10032 | hy10032
        · have hs100320 : InSquare (9/160) (-51/160) (1/160) tau := by
            convert childLL hs10032 hx10032 hy10032 using 1 <;> norm_num
          exact Batch0072.cell0580.sound htau (by
            simp only [Batch0072.cell0580, Batch0072.tau0580, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs100320 (by positivity) using 1 <;> norm_num)
        · have hs100322 : InSquare (9/160) (-49/160) (1/160) tau := by
            convert childUL hs10032 hx10032 hy10032 using 1 <;> norm_num
          exact Batch0072.cell0582.sound htau (by
            simp only [Batch0072.cell0582, Batch0072.tau0582, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs100322 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-5/16 : ℝ) with hy10032 | hy10032
        · have hs100321 : InSquare (11/160) (-51/160) (1/160) tau := by
            convert childLR hs10032 hx10032 hy10032 using 1 <;> norm_num
          exact Batch0072.cell0581.sound htau (by
            simp only [Batch0072.cell0581, Batch0072.tau0581, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs100321 (by positivity) using 1 <;> norm_num)
        · have hs100323 : InSquare (11/160) (-49/160) (1/160) tau := by
            convert childUR hs10032 hx10032 hy10032 using 1 <;> norm_num
          exact Batch0072.cell0583.sound htau (by
            simp only [Batch0072.cell0583, Batch0072.tau0583, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs100323 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (-13/40 : ℝ) with hy1003 | hy1003
    · have hs10031 : InSquare (7/80) (-27/80) (1/80) tau := by
        convert childLR hs hx1003 hy1003 using 1 <;> norm_num
      rcases le_total tau.re (7/80 : ℝ) with hx10031 | hx10031
      · rcases le_total tau.im (-27/80 : ℝ) with hy10031 | hy10031
        · have hs100310 : InSquare (13/160) (-11/32) (1/160) tau := by
            convert childLL hs10031 hx10031 hy10031 using 1 <;> norm_num
          rcases le_total tau.re (13/160 : ℝ) with hx100310 | hx100310
          · rcases le_total tau.im (-11/32 : ℝ) with hy100310 | hy100310
            · have hs1003100 : InSquare (5/64) (-111/320) (1/320) tau := by
                convert childLL hs100310 hx100310 hy100310 using 1 <;> norm_num
              exact Batch0202.cell1621.sound htau (by
                simp only [Batch0202.cell1621, Batch0202.tau1621, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1003100 (by positivity) using 1 <;> norm_num)
            · have hs1003102 : InSquare (5/64) (-109/320) (1/320) tau := by
                convert childUL hs100310 hx100310 hy100310 using 1 <;> norm_num
              exact Batch0202.cell1623.sound htau (by
                simp only [Batch0202.cell1623, Batch0202.tau1623, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1003102 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-11/32 : ℝ) with hy100310 | hy100310
            · have hs1003101 : InSquare (27/320) (-111/320) (1/320) tau := by
                convert childLR hs100310 hx100310 hy100310 using 1 <;> norm_num
              exact Batch0202.cell1622.sound htau (by
                simp only [Batch0202.cell1622, Batch0202.tau1622, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1003101 (by positivity) using 1 <;> norm_num)
            · have hs1003103 : InSquare (27/320) (-109/320) (1/320) tau := by
                convert childUR hs100310 hx100310 hy100310 using 1 <;> norm_num
              exact Batch0203.cell1624.sound htau (by
                simp only [Batch0203.cell1624, Batch0203.tau1624, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1003103 (by positivity) using 1 <;> norm_num)
        · have hs100312 : InSquare (13/160) (-53/160) (1/160) tau := by
            convert childUL hs10031 hx10031 hy10031 using 1 <;> norm_num
          exact Batch0072.cell0578.sound htau (by
            simp only [Batch0072.cell0578, Batch0072.tau0578, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs100312 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-27/80 : ℝ) with hy10031 | hy10031
        · have hs100311 : InSquare (3/32) (-11/32) (1/160) tau := by
            convert childLR hs10031 hx10031 hy10031 using 1 <;> norm_num
          rcases le_total tau.re (3/32 : ℝ) with hx100311 | hx100311
          · rcases le_total tau.im (-11/32 : ℝ) with hy100311 | hy100311
            · have hs1003110 : InSquare (29/320) (-111/320) (1/320) tau := by
                convert childLL hs100311 hx100311 hy100311 using 1 <;> norm_num
              exact Batch0203.cell1625.sound htau (by
                simp only [Batch0203.cell1625, Batch0203.tau1625, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1003110 (by positivity) using 1 <;> norm_num)
            · have hs1003112 : InSquare (29/320) (-109/320) (1/320) tau := by
                convert childUL hs100311 hx100311 hy100311 using 1 <;> norm_num
              exact Batch0203.cell1627.sound htau (by
                simp only [Batch0203.cell1627, Batch0203.tau1627, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1003112 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-11/32 : ℝ) with hy100311 | hy100311
            · have hs1003111 : InSquare (31/320) (-111/320) (1/320) tau := by
                convert childLR hs100311 hx100311 hy100311 using 1 <;> norm_num
              exact Batch0203.cell1626.sound htau (by
                simp only [Batch0203.cell1626, Batch0203.tau1626, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1003111 (by positivity) using 1 <;> norm_num)
            · have hs1003113 : InSquare (31/320) (-109/320) (1/320) tau := by
                convert childUR hs100311 hx100311 hy100311 using 1 <;> norm_num
              exact Batch0203.cell1628.sound htau (by
                simp only [Batch0203.cell1628, Batch0203.tau1628, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1003113 (by positivity) using 1 <;> norm_num)
        · have hs100313 : InSquare (3/32) (-53/160) (1/160) tau := by
            convert childUR hs10031 hx10031 hy10031 using 1 <;> norm_num
          exact Batch0072.cell0579.sound htau (by
            simp only [Batch0072.cell0579, Batch0072.tau0579, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs100313 (by positivity) using 1 <;> norm_num)
    · have hs10033 : InSquare (7/80) (-5/16) (1/80) tau := by
        convert childUR hs hx1003 hy1003 using 1 <;> norm_num
      rcases le_total tau.re (7/80 : ℝ) with hx10033 | hx10033
      · rcases le_total tau.im (-5/16 : ℝ) with hy10033 | hy10033
        · have hs100330 : InSquare (13/160) (-51/160) (1/160) tau := by
            convert childLL hs10033 hx10033 hy10033 using 1 <;> norm_num
          exact Batch0073.cell0584.sound htau (by
            simp only [Batch0073.cell0584, Batch0073.tau0584, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs100330 (by positivity) using 1 <;> norm_num)
        · have hs100332 : InSquare (13/160) (-49/160) (1/160) tau := by
            convert childUL hs10033 hx10033 hy10033 using 1 <;> norm_num
          exact Batch0073.cell0586.sound htau (by
            simp only [Batch0073.cell0586, Batch0073.tau0586, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs100332 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-5/16 : ℝ) with hy10033 | hy10033
        · have hs100331 : InSquare (3/32) (-51/160) (1/160) tau := by
            convert childLR hs10033 hx10033 hy10033 using 1 <;> norm_num
          exact Batch0073.cell0585.sound htau (by
            simp only [Batch0073.cell0585, Batch0073.tau0585, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs100331 (by positivity) using 1 <;> norm_num)
        · have hs100333 : InSquare (3/32) (-49/160) (1/160) tau := by
            convert childUR hs10033 hx10033 hy10033 using 1 <;> norm_num
          exact Batch0073.cell0587.sound htau (by
            simp only [Batch0073.cell0587, Batch0073.tau0587, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs100333 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1003
