import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0074
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0210
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0211
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0212
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0213
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0214
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0215
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0216
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0217
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0397
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0398

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1013

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (7/40) (-13/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (7/40 : ℝ) with hx1013 | hx1013
  · rcases le_total tau.im (-13/40 : ℝ) with hy1013 | hy1013
    · have hs10130 : InSquare (13/80) (-27/80) (1/80) tau := by
        convert childLL hs hx1013 hy1013 using 1 <;> norm_num
      rcases le_total tau.re (13/80 : ℝ) with hx10130 | hx10130
      · rcases le_total tau.im (-27/80 : ℝ) with hy10130 | hy10130
        · have hs101300 : InSquare (5/32) (-11/32) (1/160) tau := by
            convert childLL hs10130 hx10130 hy10130 using 1 <;> norm_num
          rcases le_total tau.re (5/32 : ℝ) with hx101300 | hx101300
          · rcases le_total tau.im (-11/32 : ℝ) with hy101300 | hy101300
            · have hs1013000 : InSquare (49/320) (-111/320) (1/320) tau := by
                convert childLL hs101300 hx101300 hy101300 using 1 <;> norm_num
              exact Batch0210.cell1683.sound htau (by
                simp only [Batch0210.cell1683, Batch0210.tau1683, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1013000 (by positivity) using 1 <;> norm_num)
            · have hs1013002 : InSquare (49/320) (-109/320) (1/320) tau := by
                convert childUL hs101300 hx101300 hy101300 using 1 <;> norm_num
              exact Batch0210.cell1685.sound htau (by
                simp only [Batch0210.cell1685, Batch0210.tau1685, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1013002 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-11/32 : ℝ) with hy101300 | hy101300
            · have hs1013001 : InSquare (51/320) (-111/320) (1/320) tau := by
                convert childLR hs101300 hx101300 hy101300 using 1 <;> norm_num
              exact Batch0210.cell1684.sound htau (by
                simp only [Batch0210.cell1684, Batch0210.tau1684, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1013001 (by positivity) using 1 <;> norm_num)
            · have hs1013003 : InSquare (51/320) (-109/320) (1/320) tau := by
                convert childUR hs101300 hx101300 hy101300 using 1 <;> norm_num
              exact Batch0210.cell1686.sound htau (by
                simp only [Batch0210.cell1686, Batch0210.tau1686, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1013003 (by positivity) using 1 <;> norm_num)
        · have hs101302 : InSquare (5/32) (-53/160) (1/160) tau := by
            convert childUL hs10130 hx10130 hy10130 using 1 <;> norm_num
          rcases le_total tau.re (5/32 : ℝ) with hx101302 | hx101302
          · rcases le_total tau.im (-53/160 : ℝ) with hy101302 | hy101302
            · have hs1013020 : InSquare (49/320) (-107/320) (1/320) tau := by
                convert childLL hs101302 hx101302 hy101302 using 1 <;> norm_num
              exact Batch0211.cell1691.sound htau (by
                simp only [Batch0211.cell1691, Batch0211.tau1691, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1013020 (by positivity) using 1 <;> norm_num)
            · have hs1013022 : InSquare (49/320) (-21/64) (1/320) tau := by
                convert childUL hs101302 hx101302 hy101302 using 1 <;> norm_num
              exact Batch0211.cell1693.sound htau (by
                simp only [Batch0211.cell1693, Batch0211.tau1693, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1013022 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-53/160 : ℝ) with hy101302 | hy101302
            · have hs1013021 : InSquare (51/320) (-107/320) (1/320) tau := by
                convert childLR hs101302 hx101302 hy101302 using 1 <;> norm_num
              exact Batch0211.cell1692.sound htau (by
                simp only [Batch0211.cell1692, Batch0211.tau1692, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1013021 (by positivity) using 1 <;> norm_num)
            · have hs1013023 : InSquare (51/320) (-21/64) (1/320) tau := by
                convert childUR hs101302 hx101302 hy101302 using 1 <;> norm_num
              exact Batch0211.cell1694.sound htau (by
                simp only [Batch0211.cell1694, Batch0211.tau1694, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1013023 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-27/80 : ℝ) with hy10130 | hy10130
        · have hs101301 : InSquare (27/160) (-11/32) (1/160) tau := by
            convert childLR hs10130 hx10130 hy10130 using 1 <;> norm_num
          rcases le_total tau.re (27/160 : ℝ) with hx101301 | hx101301
          · rcases le_total tau.im (-11/32 : ℝ) with hy101301 | hy101301
            · have hs1013010 : InSquare (53/320) (-111/320) (1/320) tau := by
                convert childLL hs101301 hx101301 hy101301 using 1 <;> norm_num
              exact Batch0210.cell1687.sound htau (by
                simp only [Batch0210.cell1687, Batch0210.tau1687, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1013010 (by positivity) using 1 <;> norm_num)
            · have hs1013012 : InSquare (53/320) (-109/320) (1/320) tau := by
                convert childUL hs101301 hx101301 hy101301 using 1 <;> norm_num
              exact Batch0211.cell1689.sound htau (by
                simp only [Batch0211.cell1689, Batch0211.tau1689, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1013012 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-11/32 : ℝ) with hy101301 | hy101301
            · have hs1013011 : InSquare (11/64) (-111/320) (1/320) tau := by
                convert childLR hs101301 hx101301 hy101301 using 1 <;> norm_num
              exact Batch0211.cell1688.sound htau (by
                simp only [Batch0211.cell1688, Batch0211.tau1688, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1013011 (by positivity) using 1 <;> norm_num)
            · have hs1013013 : InSquare (11/64) (-109/320) (1/320) tau := by
                convert childUR hs101301 hx101301 hy101301 using 1 <;> norm_num
              exact Batch0211.cell1690.sound htau (by
                simp only [Batch0211.cell1690, Batch0211.tau1690, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1013013 (by positivity) using 1 <;> norm_num)
        · have hs101303 : InSquare (27/160) (-53/160) (1/160) tau := by
            convert childUR hs10130 hx10130 hy10130 using 1 <;> norm_num
          rcases le_total tau.re (27/160 : ℝ) with hx101303 | hx101303
          · rcases le_total tau.im (-53/160 : ℝ) with hy101303 | hy101303
            · have hs1013030 : InSquare (53/320) (-107/320) (1/320) tau := by
                convert childLL hs101303 hx101303 hy101303 using 1 <;> norm_num
              exact Batch0211.cell1695.sound htau (by
                simp only [Batch0211.cell1695, Batch0211.tau1695, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1013030 (by positivity) using 1 <;> norm_num)
            · have hs1013032 : InSquare (53/320) (-21/64) (1/320) tau := by
                convert childUL hs101303 hx101303 hy101303 using 1 <;> norm_num
              exact Batch0212.cell1697.sound htau (by
                simp only [Batch0212.cell1697, Batch0212.tau1697, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1013032 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-53/160 : ℝ) with hy101303 | hy101303
            · have hs1013031 : InSquare (11/64) (-107/320) (1/320) tau := by
                convert childLR hs101303 hx101303 hy101303 using 1 <;> norm_num
              exact Batch0212.cell1696.sound htau (by
                simp only [Batch0212.cell1696, Batch0212.tau1696, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1013031 (by positivity) using 1 <;> norm_num)
            · have hs1013033 : InSquare (11/64) (-21/64) (1/320) tau := by
                convert childUR hs101303 hx101303 hy101303 using 1 <;> norm_num
              exact Batch0212.cell1698.sound htau (by
                simp only [Batch0212.cell1698, Batch0212.tau1698, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1013033 (by positivity) using 1 <;> norm_num)
    · have hs10132 : InSquare (13/80) (-5/16) (1/80) tau := by
        convert childUL hs hx1013 hy1013 using 1 <;> norm_num
      rcases le_total tau.re (13/80 : ℝ) with hx10132 | hx10132
      · rcases le_total tau.im (-5/16 : ℝ) with hy10132 | hy10132
        · have hs101320 : InSquare (5/32) (-51/160) (1/160) tau := by
            convert childLL hs10132 hx10132 hy10132 using 1 <;> norm_num
          rcases le_total tau.re (5/32 : ℝ) with hx101320 | hx101320
          · rcases le_total tau.im (-51/160 : ℝ) with hy101320 | hy101320
            · have hs1013200 : InSquare (49/320) (-103/320) (1/320) tau := by
                convert childLL hs101320 hx101320 hy101320 using 1 <;> norm_num
              exact Batch0214.cell1713.sound htau (by
                simp only [Batch0214.cell1713, Batch0214.tau1713, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1013200 (by positivity) using 1 <;> norm_num)
            · have hs1013202 : InSquare (49/320) (-101/320) (1/320) tau := by
                convert childUL hs101320 hx101320 hy101320 using 1 <;> norm_num
              exact Batch0214.cell1715.sound htau (by
                simp only [Batch0214.cell1715, Batch0214.tau1715, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1013202 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-51/160 : ℝ) with hy101320 | hy101320
            · have hs1013201 : InSquare (51/320) (-103/320) (1/320) tau := by
                convert childLR hs101320 hx101320 hy101320 using 1 <;> norm_num
              exact Batch0214.cell1714.sound htau (by
                simp only [Batch0214.cell1714, Batch0214.tau1714, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1013201 (by positivity) using 1 <;> norm_num)
            · have hs1013203 : InSquare (51/320) (-101/320) (1/320) tau := by
                convert childUR hs101320 hx101320 hy101320 using 1 <;> norm_num
              exact Batch0214.cell1716.sound htau (by
                simp only [Batch0214.cell1716, Batch0214.tau1716, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1013203 (by positivity) using 1 <;> norm_num)
        · have hs101322 : InSquare (5/32) (-49/160) (1/160) tau := by
            convert childUL hs10132 hx10132 hy10132 using 1 <;> norm_num
          exact Batch0074.cell0596.sound htau (by
            simp only [Batch0074.cell0596, Batch0074.tau0596, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs101322 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-5/16 : ℝ) with hy10132 | hy10132
        · have hs101321 : InSquare (27/160) (-51/160) (1/160) tau := by
            convert childLR hs10132 hx10132 hy10132 using 1 <;> norm_num
          rcases le_total tau.re (27/160 : ℝ) with hx101321 | hx101321
          · rcases le_total tau.im (-51/160 : ℝ) with hy101321 | hy101321
            · have hs1013210 : InSquare (53/320) (-103/320) (1/320) tau := by
                convert childLL hs101321 hx101321 hy101321 using 1 <;> norm_num
              exact Batch0214.cell1717.sound htau (by
                simp only [Batch0214.cell1717, Batch0214.tau1717, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1013210 (by positivity) using 1 <;> norm_num)
            · have hs1013212 : InSquare (53/320) (-101/320) (1/320) tau := by
                convert childUL hs101321 hx101321 hy101321 using 1 <;> norm_num
              exact Batch0214.cell1719.sound htau (by
                simp only [Batch0214.cell1719, Batch0214.tau1719, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1013212 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-51/160 : ℝ) with hy101321 | hy101321
            · have hs1013211 : InSquare (11/64) (-103/320) (1/320) tau := by
                convert childLR hs101321 hx101321 hy101321 using 1 <;> norm_num
              exact Batch0214.cell1718.sound htau (by
                simp only [Batch0214.cell1718, Batch0214.tau1718, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1013211 (by positivity) using 1 <;> norm_num)
            · have hs1013213 : InSquare (11/64) (-101/320) (1/320) tau := by
                convert childUR hs101321 hx101321 hy101321 using 1 <;> norm_num
              exact Batch0215.cell1720.sound htau (by
                simp only [Batch0215.cell1720, Batch0215.tau1720, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1013213 (by positivity) using 1 <;> norm_num)
        · have hs101323 : InSquare (27/160) (-49/160) (1/160) tau := by
            convert childUR hs10132 hx10132 hy10132 using 1 <;> norm_num
          exact Batch0074.cell0597.sound htau (by
            simp only [Batch0074.cell0597, Batch0074.tau0597, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs101323 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (-13/40 : ℝ) with hy1013 | hy1013
    · have hs10131 : InSquare (3/16) (-27/80) (1/80) tau := by
        convert childLR hs hx1013 hy1013 using 1 <;> norm_num
      rcases le_total tau.re (3/16 : ℝ) with hx10131 | hx10131
      · rcases le_total tau.im (-27/80 : ℝ) with hy10131 | hy10131
        · have hs101310 : InSquare (29/160) (-11/32) (1/160) tau := by
            convert childLL hs10131 hx10131 hy10131 using 1 <;> norm_num
          rcases le_total tau.re (29/160 : ℝ) with hx101310 | hx101310
          · rcases le_total tau.im (-11/32 : ℝ) with hy101310 | hy101310
            · have hs1013100 : InSquare (57/320) (-111/320) (1/320) tau := by
                convert childLL hs101310 hx101310 hy101310 using 1 <;> norm_num
              exact Batch0212.cell1699.sound htau (by
                simp only [Batch0212.cell1699, Batch0212.tau1699, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1013100 (by positivity) using 1 <;> norm_num)
            · have hs1013102 : InSquare (57/320) (-109/320) (1/320) tau := by
                convert childUL hs101310 hx101310 hy101310 using 1 <;> norm_num
              exact Batch0212.cell1701.sound htau (by
                simp only [Batch0212.cell1701, Batch0212.tau1701, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1013102 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-11/32 : ℝ) with hy101310 | hy101310
            · have hs1013101 : InSquare (59/320) (-111/320) (1/320) tau := by
                convert childLR hs101310 hx101310 hy101310 using 1 <;> norm_num
              exact Batch0212.cell1700.sound htau (by
                simp only [Batch0212.cell1700, Batch0212.tau1700, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1013101 (by positivity) using 1 <;> norm_num)
            · have hs1013103 : InSquare (59/320) (-109/320) (1/320) tau := by
                convert childUR hs101310 hx101310 hy101310 using 1 <;> norm_num
              exact Batch0212.cell1702.sound htau (by
                simp only [Batch0212.cell1702, Batch0212.tau1702, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1013103 (by positivity) using 1 <;> norm_num)
        · have hs101312 : InSquare (29/160) (-53/160) (1/160) tau := by
            convert childUL hs10131 hx10131 hy10131 using 1 <;> norm_num
          rcases le_total tau.re (29/160 : ℝ) with hx101312 | hx101312
          · rcases le_total tau.im (-53/160 : ℝ) with hy101312 | hy101312
            · have hs1013120 : InSquare (57/320) (-107/320) (1/320) tau := by
                convert childLL hs101312 hx101312 hy101312 using 1 <;> norm_num
              exact Batch0213.cell1705.sound htau (by
                simp only [Batch0213.cell1705, Batch0213.tau1705, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1013120 (by positivity) using 1 <;> norm_num)
            · have hs1013122 : InSquare (57/320) (-21/64) (1/320) tau := by
                convert childUL hs101312 hx101312 hy101312 using 1 <;> norm_num
              exact Batch0213.cell1707.sound htau (by
                simp only [Batch0213.cell1707, Batch0213.tau1707, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1013122 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-53/160 : ℝ) with hy101312 | hy101312
            · have hs1013121 : InSquare (59/320) (-107/320) (1/320) tau := by
                convert childLR hs101312 hx101312 hy101312 using 1 <;> norm_num
              exact Batch0213.cell1706.sound htau (by
                simp only [Batch0213.cell1706, Batch0213.tau1706, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1013121 (by positivity) using 1 <;> norm_num)
            · have hs1013123 : InSquare (59/320) (-21/64) (1/320) tau := by
                convert childUR hs101312 hx101312 hy101312 using 1 <;> norm_num
              exact Batch0213.cell1708.sound htau (by
                simp only [Batch0213.cell1708, Batch0213.tau1708, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1013123 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-27/80 : ℝ) with hy10131 | hy10131
        · have hs101311 : InSquare (31/160) (-11/32) (1/160) tau := by
            convert childLR hs10131 hx10131 hy10131 using 1 <;> norm_num
          rcases le_total tau.re (31/160 : ℝ) with hx101311 | hx101311
          · rcases le_total tau.im (-11/32 : ℝ) with hy101311 | hy101311
            · have hs1013110 : InSquare (61/320) (-111/320) (1/320) tau := by
                convert childLL hs101311 hx101311 hy101311 using 1 <;> norm_num
              rcases le_total tau.re (61/320 : ℝ) with hx1013110 | hx1013110
              · rcases le_total tau.im (-111/320 : ℝ) with hy1013110 | hy1013110
                · have hs10131100 : InSquare (121/640) (-223/640) (1/640) tau := by
                    convert childLL hs1013110 hx1013110 hy1013110 using 1 <;> norm_num
                  exact Batch0397.cell3181.sound htau (by
                    simp only [Batch0397.cell3181, Batch0397.tau3181, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10131100 (by positivity) using 1 <;> norm_num)
                · have hs10131102 : InSquare (121/640) (-221/640) (1/640) tau := by
                    convert childUL hs1013110 hx1013110 hy1013110 using 1 <;> norm_num
                  exact Batch0397.cell3183.sound htau (by
                    simp only [Batch0397.cell3183, Batch0397.tau3183, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10131102 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-111/320 : ℝ) with hy1013110 | hy1013110
                · have hs10131101 : InSquare (123/640) (-223/640) (1/640) tau := by
                    convert childLR hs1013110 hx1013110 hy1013110 using 1 <;> norm_num
                  exact Batch0397.cell3182.sound htau (by
                    simp only [Batch0397.cell3182, Batch0397.tau3182, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10131101 (by positivity) using 1 <;> norm_num)
                · have hs10131103 : InSquare (123/640) (-221/640) (1/640) tau := by
                    convert childUR hs1013110 hx1013110 hy1013110 using 1 <;> norm_num
                  exact Batch0398.cell3184.sound htau (by
                    simp only [Batch0398.cell3184, Batch0398.tau3184, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10131103 (by positivity) using 1 <;> norm_num)
            · have hs1013112 : InSquare (61/320) (-109/320) (1/320) tau := by
                convert childUL hs101311 hx101311 hy101311 using 1 <;> norm_num
              exact Batch0212.cell1703.sound htau (by
                simp only [Batch0212.cell1703, Batch0212.tau1703, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1013112 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-11/32 : ℝ) with hy101311 | hy101311
            · have hs1013111 : InSquare (63/320) (-111/320) (1/320) tau := by
                convert childLR hs101311 hx101311 hy101311 using 1 <;> norm_num
              rcases le_total tau.re (63/320 : ℝ) with hx1013111 | hx1013111
              · rcases le_total tau.im (-111/320 : ℝ) with hy1013111 | hy1013111
                · have hs10131110 : InSquare (25/128) (-223/640) (1/640) tau := by
                    convert childLL hs1013111 hx1013111 hy1013111 using 1 <;> norm_num
                  exact Batch0398.cell3185.sound htau (by
                    simp only [Batch0398.cell3185, Batch0398.tau3185, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10131110 (by positivity) using 1 <;> norm_num)
                · have hs10131112 : InSquare (25/128) (-221/640) (1/640) tau := by
                    convert childUL hs1013111 hx1013111 hy1013111 using 1 <;> norm_num
                  exact Batch0398.cell3187.sound htau (by
                    simp only [Batch0398.cell3187, Batch0398.tau3187, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10131112 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-111/320 : ℝ) with hy1013111 | hy1013111
                · have hs10131111 : InSquare (127/640) (-223/640) (1/640) tau := by
                    convert childLR hs1013111 hx1013111 hy1013111 using 1 <;> norm_num
                  exact Batch0398.cell3186.sound htau (by
                    simp only [Batch0398.cell3186, Batch0398.tau3186, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10131111 (by positivity) using 1 <;> norm_num)
                · have hs10131113 : InSquare (127/640) (-221/640) (1/640) tau := by
                    convert childUR hs1013111 hx1013111 hy1013111 using 1 <;> norm_num
                  exact Batch0398.cell3188.sound htau (by
                    simp only [Batch0398.cell3188, Batch0398.tau3188, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10131113 (by positivity) using 1 <;> norm_num)
            · have hs1013113 : InSquare (63/320) (-109/320) (1/320) tau := by
                convert childUR hs101311 hx101311 hy101311 using 1 <;> norm_num
              exact Batch0213.cell1704.sound htau (by
                simp only [Batch0213.cell1704, Batch0213.tau1704, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1013113 (by positivity) using 1 <;> norm_num)
        · have hs101313 : InSquare (31/160) (-53/160) (1/160) tau := by
            convert childUR hs10131 hx10131 hy10131 using 1 <;> norm_num
          rcases le_total tau.re (31/160 : ℝ) with hx101313 | hx101313
          · rcases le_total tau.im (-53/160 : ℝ) with hy101313 | hy101313
            · have hs1013130 : InSquare (61/320) (-107/320) (1/320) tau := by
                convert childLL hs101313 hx101313 hy101313 using 1 <;> norm_num
              exact Batch0213.cell1709.sound htau (by
                simp only [Batch0213.cell1709, Batch0213.tau1709, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1013130 (by positivity) using 1 <;> norm_num)
            · have hs1013132 : InSquare (61/320) (-21/64) (1/320) tau := by
                convert childUL hs101313 hx101313 hy101313 using 1 <;> norm_num
              exact Batch0213.cell1711.sound htau (by
                simp only [Batch0213.cell1711, Batch0213.tau1711, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1013132 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-53/160 : ℝ) with hy101313 | hy101313
            · have hs1013131 : InSquare (63/320) (-107/320) (1/320) tau := by
                convert childLR hs101313 hx101313 hy101313 using 1 <;> norm_num
              exact Batch0213.cell1710.sound htau (by
                simp only [Batch0213.cell1710, Batch0213.tau1710, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1013131 (by positivity) using 1 <;> norm_num)
            · have hs1013133 : InSquare (63/320) (-21/64) (1/320) tau := by
                convert childUR hs101313 hx101313 hy101313 using 1 <;> norm_num
              exact Batch0214.cell1712.sound htau (by
                simp only [Batch0214.cell1712, Batch0214.tau1712, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1013133 (by positivity) using 1 <;> norm_num)
    · have hs10133 : InSquare (3/16) (-5/16) (1/80) tau := by
        convert childUR hs hx1013 hy1013 using 1 <;> norm_num
      rcases le_total tau.re (3/16 : ℝ) with hx10133 | hx10133
      · rcases le_total tau.im (-5/16 : ℝ) with hy10133 | hy10133
        · have hs101330 : InSquare (29/160) (-51/160) (1/160) tau := by
            convert childLL hs10133 hx10133 hy10133 using 1 <;> norm_num
          rcases le_total tau.re (29/160 : ℝ) with hx101330 | hx101330
          · rcases le_total tau.im (-51/160 : ℝ) with hy101330 | hy101330
            · have hs1013300 : InSquare (57/320) (-103/320) (1/320) tau := by
                convert childLL hs101330 hx101330 hy101330 using 1 <;> norm_num
              exact Batch0215.cell1721.sound htau (by
                simp only [Batch0215.cell1721, Batch0215.tau1721, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1013300 (by positivity) using 1 <;> norm_num)
            · have hs1013302 : InSquare (57/320) (-101/320) (1/320) tau := by
                convert childUL hs101330 hx101330 hy101330 using 1 <;> norm_num
              exact Batch0215.cell1723.sound htau (by
                simp only [Batch0215.cell1723, Batch0215.tau1723, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1013302 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-51/160 : ℝ) with hy101330 | hy101330
            · have hs1013301 : InSquare (59/320) (-103/320) (1/320) tau := by
                convert childLR hs101330 hx101330 hy101330 using 1 <;> norm_num
              exact Batch0215.cell1722.sound htau (by
                simp only [Batch0215.cell1722, Batch0215.tau1722, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1013301 (by positivity) using 1 <;> norm_num)
            · have hs1013303 : InSquare (59/320) (-101/320) (1/320) tau := by
                convert childUR hs101330 hx101330 hy101330 using 1 <;> norm_num
              exact Batch0215.cell1724.sound htau (by
                simp only [Batch0215.cell1724, Batch0215.tau1724, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1013303 (by positivity) using 1 <;> norm_num)
        · have hs101332 : InSquare (29/160) (-49/160) (1/160) tau := by
            convert childUL hs10133 hx10133 hy10133 using 1 <;> norm_num
          rcases le_total tau.re (29/160 : ℝ) with hx101332 | hx101332
          · rcases le_total tau.im (-49/160 : ℝ) with hy101332 | hy101332
            · have hs1013320 : InSquare (57/320) (-99/320) (1/320) tau := by
                convert childLL hs101332 hx101332 hy101332 using 1 <;> norm_num
              exact Batch0216.cell1729.sound htau (by
                simp only [Batch0216.cell1729, Batch0216.tau1729, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1013320 (by positivity) using 1 <;> norm_num)
            · have hs1013322 : InSquare (57/320) (-97/320) (1/320) tau := by
                convert childUL hs101332 hx101332 hy101332 using 1 <;> norm_num
              exact Batch0216.cell1731.sound htau (by
                simp only [Batch0216.cell1731, Batch0216.tau1731, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1013322 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-49/160 : ℝ) with hy101332 | hy101332
            · have hs1013321 : InSquare (59/320) (-99/320) (1/320) tau := by
                convert childLR hs101332 hx101332 hy101332 using 1 <;> norm_num
              exact Batch0216.cell1730.sound htau (by
                simp only [Batch0216.cell1730, Batch0216.tau1730, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1013321 (by positivity) using 1 <;> norm_num)
            · have hs1013323 : InSquare (59/320) (-97/320) (1/320) tau := by
                convert childUR hs101332 hx101332 hy101332 using 1 <;> norm_num
              exact Batch0216.cell1732.sound htau (by
                simp only [Batch0216.cell1732, Batch0216.tau1732, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1013323 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-5/16 : ℝ) with hy10133 | hy10133
        · have hs101331 : InSquare (31/160) (-51/160) (1/160) tau := by
            convert childLR hs10133 hx10133 hy10133 using 1 <;> norm_num
          rcases le_total tau.re (31/160 : ℝ) with hx101331 | hx101331
          · rcases le_total tau.im (-51/160 : ℝ) with hy101331 | hy101331
            · have hs1013310 : InSquare (61/320) (-103/320) (1/320) tau := by
                convert childLL hs101331 hx101331 hy101331 using 1 <;> norm_num
              exact Batch0215.cell1725.sound htau (by
                simp only [Batch0215.cell1725, Batch0215.tau1725, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1013310 (by positivity) using 1 <;> norm_num)
            · have hs1013312 : InSquare (61/320) (-101/320) (1/320) tau := by
                convert childUL hs101331 hx101331 hy101331 using 1 <;> norm_num
              exact Batch0215.cell1727.sound htau (by
                simp only [Batch0215.cell1727, Batch0215.tau1727, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1013312 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-51/160 : ℝ) with hy101331 | hy101331
            · have hs1013311 : InSquare (63/320) (-103/320) (1/320) tau := by
                convert childLR hs101331 hx101331 hy101331 using 1 <;> norm_num
              exact Batch0215.cell1726.sound htau (by
                simp only [Batch0215.cell1726, Batch0215.tau1726, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1013311 (by positivity) using 1 <;> norm_num)
            · have hs1013313 : InSquare (63/320) (-101/320) (1/320) tau := by
                convert childUR hs101331 hx101331 hy101331 using 1 <;> norm_num
              exact Batch0216.cell1728.sound htau (by
                simp only [Batch0216.cell1728, Batch0216.tau1728, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1013313 (by positivity) using 1 <;> norm_num)
        · have hs101333 : InSquare (31/160) (-49/160) (1/160) tau := by
            convert childUR hs10133 hx10133 hy10133 using 1 <;> norm_num
          rcases le_total tau.re (31/160 : ℝ) with hx101333 | hx101333
          · rcases le_total tau.im (-49/160 : ℝ) with hy101333 | hy101333
            · have hs1013330 : InSquare (61/320) (-99/320) (1/320) tau := by
                convert childLL hs101333 hx101333 hy101333 using 1 <;> norm_num
              exact Batch0216.cell1733.sound htau (by
                simp only [Batch0216.cell1733, Batch0216.tau1733, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1013330 (by positivity) using 1 <;> norm_num)
            · have hs1013332 : InSquare (61/320) (-97/320) (1/320) tau := by
                convert childUL hs101333 hx101333 hy101333 using 1 <;> norm_num
              exact Batch0216.cell1735.sound htau (by
                simp only [Batch0216.cell1735, Batch0216.tau1735, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1013332 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-49/160 : ℝ) with hy101333 | hy101333
            · have hs1013331 : InSquare (63/320) (-99/320) (1/320) tau := by
                convert childLR hs101333 hx101333 hy101333 using 1 <;> norm_num
              exact Batch0216.cell1734.sound htau (by
                simp only [Batch0216.cell1734, Batch0216.tau1734, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1013331 (by positivity) using 1 <;> norm_num)
            · have hs1013333 : InSquare (63/320) (-97/320) (1/320) tau := by
                convert childUR hs101333 hx101333 hy101333 using 1 <;> norm_num
              exact Batch0217.cell1736.sound htau (by
                simp only [Batch0217.cell1736, Batch0217.tau1736, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1013333 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1013
