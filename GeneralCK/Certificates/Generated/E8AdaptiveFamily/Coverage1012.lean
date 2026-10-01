import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0073
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0074
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0206
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0207
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0208
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0209
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0210

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1012

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (1/8) (-13/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (1/8 : ℝ) with hx1012 | hx1012
  · rcases le_total tau.im (-13/40 : ℝ) with hy1012 | hy1012
    · have hs10120 : InSquare (9/80) (-27/80) (1/80) tau := by
        convert childLL hs hx1012 hy1012 using 1 <;> norm_num
      rcases le_total tau.re (9/80 : ℝ) with hx10120 | hx10120
      · rcases le_total tau.im (-27/80 : ℝ) with hy10120 | hy10120
        · have hs101200 : InSquare (17/160) (-11/32) (1/160) tau := by
            convert childLL hs10120 hx10120 hy10120 using 1 <;> norm_num
          rcases le_total tau.re (17/160 : ℝ) with hx101200 | hx101200
          · rcases le_total tau.im (-11/32 : ℝ) with hy101200 | hy101200
            · have hs1012000 : InSquare (33/320) (-111/320) (1/320) tau := by
                convert childLL hs101200 hx101200 hy101200 using 1 <;> norm_num
              exact Batch0206.cell1651.sound htau (by
                simp only [Batch0206.cell1651, Batch0206.tau1651, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1012000 (by positivity) using 1 <;> norm_num)
            · have hs1012002 : InSquare (33/320) (-109/320) (1/320) tau := by
                convert childUL hs101200 hx101200 hy101200 using 1 <;> norm_num
              exact Batch0206.cell1653.sound htau (by
                simp only [Batch0206.cell1653, Batch0206.tau1653, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1012002 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-11/32 : ℝ) with hy101200 | hy101200
            · have hs1012001 : InSquare (7/64) (-111/320) (1/320) tau := by
                convert childLR hs101200 hx101200 hy101200 using 1 <;> norm_num
              exact Batch0206.cell1652.sound htau (by
                simp only [Batch0206.cell1652, Batch0206.tau1652, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1012001 (by positivity) using 1 <;> norm_num)
            · have hs1012003 : InSquare (7/64) (-109/320) (1/320) tau := by
                convert childUR hs101200 hx101200 hy101200 using 1 <;> norm_num
              exact Batch0206.cell1654.sound htau (by
                simp only [Batch0206.cell1654, Batch0206.tau1654, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1012003 (by positivity) using 1 <;> norm_num)
        · have hs101202 : InSquare (17/160) (-53/160) (1/160) tau := by
            convert childUL hs10120 hx10120 hy10120 using 1 <;> norm_num
          exact Batch0073.cell0588.sound htau (by
            simp only [Batch0073.cell0588, Batch0073.tau0588, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs101202 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-27/80 : ℝ) with hy10120 | hy10120
        · have hs101201 : InSquare (19/160) (-11/32) (1/160) tau := by
            convert childLR hs10120 hx10120 hy10120 using 1 <;> norm_num
          rcases le_total tau.re (19/160 : ℝ) with hx101201 | hx101201
          · rcases le_total tau.im (-11/32 : ℝ) with hy101201 | hy101201
            · have hs1012010 : InSquare (37/320) (-111/320) (1/320) tau := by
                convert childLL hs101201 hx101201 hy101201 using 1 <;> norm_num
              exact Batch0206.cell1655.sound htau (by
                simp only [Batch0206.cell1655, Batch0206.tau1655, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1012010 (by positivity) using 1 <;> norm_num)
            · have hs1012012 : InSquare (37/320) (-109/320) (1/320) tau := by
                convert childUL hs101201 hx101201 hy101201 using 1 <;> norm_num
              exact Batch0207.cell1657.sound htau (by
                simp only [Batch0207.cell1657, Batch0207.tau1657, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1012012 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-11/32 : ℝ) with hy101201 | hy101201
            · have hs1012011 : InSquare (39/320) (-111/320) (1/320) tau := by
                convert childLR hs101201 hx101201 hy101201 using 1 <;> norm_num
              exact Batch0207.cell1656.sound htau (by
                simp only [Batch0207.cell1656, Batch0207.tau1656, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1012011 (by positivity) using 1 <;> norm_num)
            · have hs1012013 : InSquare (39/320) (-109/320) (1/320) tau := by
                convert childUR hs101201 hx101201 hy101201 using 1 <;> norm_num
              exact Batch0207.cell1658.sound htau (by
                simp only [Batch0207.cell1658, Batch0207.tau1658, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1012013 (by positivity) using 1 <;> norm_num)
        · have hs101203 : InSquare (19/160) (-53/160) (1/160) tau := by
            convert childUR hs10120 hx10120 hy10120 using 1 <;> norm_num
          rcases le_total tau.re (19/160 : ℝ) with hx101203 | hx101203
          · rcases le_total tau.im (-53/160 : ℝ) with hy101203 | hy101203
            · have hs1012030 : InSquare (37/320) (-107/320) (1/320) tau := by
                convert childLL hs101203 hx101203 hy101203 using 1 <;> norm_num
              exact Batch0207.cell1659.sound htau (by
                simp only [Batch0207.cell1659, Batch0207.tau1659, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1012030 (by positivity) using 1 <;> norm_num)
            · have hs1012032 : InSquare (37/320) (-21/64) (1/320) tau := by
                convert childUL hs101203 hx101203 hy101203 using 1 <;> norm_num
              exact Batch0207.cell1661.sound htau (by
                simp only [Batch0207.cell1661, Batch0207.tau1661, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1012032 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-53/160 : ℝ) with hy101203 | hy101203
            · have hs1012031 : InSquare (39/320) (-107/320) (1/320) tau := by
                convert childLR hs101203 hx101203 hy101203 using 1 <;> norm_num
              exact Batch0207.cell1660.sound htau (by
                simp only [Batch0207.cell1660, Batch0207.tau1660, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1012031 (by positivity) using 1 <;> norm_num)
            · have hs1012033 : InSquare (39/320) (-21/64) (1/320) tau := by
                convert childUR hs101203 hx101203 hy101203 using 1 <;> norm_num
              exact Batch0207.cell1662.sound htau (by
                simp only [Batch0207.cell1662, Batch0207.tau1662, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1012033 (by positivity) using 1 <;> norm_num)
    · have hs10122 : InSquare (9/80) (-5/16) (1/80) tau := by
        convert childUL hs hx1012 hy1012 using 1 <;> norm_num
      rcases le_total tau.re (9/80 : ℝ) with hx10122 | hx10122
      · rcases le_total tau.im (-5/16 : ℝ) with hy10122 | hy10122
        · have hs101220 : InSquare (17/160) (-51/160) (1/160) tau := by
            convert childLL hs10122 hx10122 hy10122 using 1 <;> norm_num
          exact Batch0073.cell0589.sound htau (by
            simp only [Batch0073.cell0589, Batch0073.tau0589, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs101220 (by positivity) using 1 <;> norm_num)
        · have hs101222 : InSquare (17/160) (-49/160) (1/160) tau := by
            convert childUL hs10122 hx10122 hy10122 using 1 <;> norm_num
          exact Batch0073.cell0591.sound htau (by
            simp only [Batch0073.cell0591, Batch0073.tau0591, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs101222 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-5/16 : ℝ) with hy10122 | hy10122
        · have hs101221 : InSquare (19/160) (-51/160) (1/160) tau := by
            convert childLR hs10122 hx10122 hy10122 using 1 <;> norm_num
          exact Batch0073.cell0590.sound htau (by
            simp only [Batch0073.cell0590, Batch0073.tau0590, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs101221 (by positivity) using 1 <;> norm_num)
        · have hs101223 : InSquare (19/160) (-49/160) (1/160) tau := by
            convert childUR hs10122 hx10122 hy10122 using 1 <;> norm_num
          exact Batch0074.cell0592.sound htau (by
            simp only [Batch0074.cell0592, Batch0074.tau0592, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs101223 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (-13/40 : ℝ) with hy1012 | hy1012
    · have hs10121 : InSquare (11/80) (-27/80) (1/80) tau := by
        convert childLR hs hx1012 hy1012 using 1 <;> norm_num
      rcases le_total tau.re (11/80 : ℝ) with hx10121 | hx10121
      · rcases le_total tau.im (-27/80 : ℝ) with hy10121 | hy10121
        · have hs101210 : InSquare (21/160) (-11/32) (1/160) tau := by
            convert childLL hs10121 hx10121 hy10121 using 1 <;> norm_num
          rcases le_total tau.re (21/160 : ℝ) with hx101210 | hx101210
          · rcases le_total tau.im (-11/32 : ℝ) with hy101210 | hy101210
            · have hs1012100 : InSquare (41/320) (-111/320) (1/320) tau := by
                convert childLL hs101210 hx101210 hy101210 using 1 <;> norm_num
              exact Batch0207.cell1663.sound htau (by
                simp only [Batch0207.cell1663, Batch0207.tau1663, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1012100 (by positivity) using 1 <;> norm_num)
            · have hs1012102 : InSquare (41/320) (-109/320) (1/320) tau := by
                convert childUL hs101210 hx101210 hy101210 using 1 <;> norm_num
              exact Batch0208.cell1665.sound htau (by
                simp only [Batch0208.cell1665, Batch0208.tau1665, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1012102 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-11/32 : ℝ) with hy101210 | hy101210
            · have hs1012101 : InSquare (43/320) (-111/320) (1/320) tau := by
                convert childLR hs101210 hx101210 hy101210 using 1 <;> norm_num
              exact Batch0208.cell1664.sound htau (by
                simp only [Batch0208.cell1664, Batch0208.tau1664, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1012101 (by positivity) using 1 <;> norm_num)
            · have hs1012103 : InSquare (43/320) (-109/320) (1/320) tau := by
                convert childUR hs101210 hx101210 hy101210 using 1 <;> norm_num
              exact Batch0208.cell1666.sound htau (by
                simp only [Batch0208.cell1666, Batch0208.tau1666, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1012103 (by positivity) using 1 <;> norm_num)
        · have hs101212 : InSquare (21/160) (-53/160) (1/160) tau := by
            convert childUL hs10121 hx10121 hy10121 using 1 <;> norm_num
          rcases le_total tau.re (21/160 : ℝ) with hx101212 | hx101212
          · rcases le_total tau.im (-53/160 : ℝ) with hy101212 | hy101212
            · have hs1012120 : InSquare (41/320) (-107/320) (1/320) tau := by
                convert childLL hs101212 hx101212 hy101212 using 1 <;> norm_num
              exact Batch0208.cell1671.sound htau (by
                simp only [Batch0208.cell1671, Batch0208.tau1671, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1012120 (by positivity) using 1 <;> norm_num)
            · have hs1012122 : InSquare (41/320) (-21/64) (1/320) tau := by
                convert childUL hs101212 hx101212 hy101212 using 1 <;> norm_num
              exact Batch0209.cell1673.sound htau (by
                simp only [Batch0209.cell1673, Batch0209.tau1673, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1012122 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-53/160 : ℝ) with hy101212 | hy101212
            · have hs1012121 : InSquare (43/320) (-107/320) (1/320) tau := by
                convert childLR hs101212 hx101212 hy101212 using 1 <;> norm_num
              exact Batch0209.cell1672.sound htau (by
                simp only [Batch0209.cell1672, Batch0209.tau1672, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1012121 (by positivity) using 1 <;> norm_num)
            · have hs1012123 : InSquare (43/320) (-21/64) (1/320) tau := by
                convert childUR hs101212 hx101212 hy101212 using 1 <;> norm_num
              exact Batch0209.cell1674.sound htau (by
                simp only [Batch0209.cell1674, Batch0209.tau1674, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1012123 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-27/80 : ℝ) with hy10121 | hy10121
        · have hs101211 : InSquare (23/160) (-11/32) (1/160) tau := by
            convert childLR hs10121 hx10121 hy10121 using 1 <;> norm_num
          rcases le_total tau.re (23/160 : ℝ) with hx101211 | hx101211
          · rcases le_total tau.im (-11/32 : ℝ) with hy101211 | hy101211
            · have hs1012110 : InSquare (9/64) (-111/320) (1/320) tau := by
                convert childLL hs101211 hx101211 hy101211 using 1 <;> norm_num
              exact Batch0208.cell1667.sound htau (by
                simp only [Batch0208.cell1667, Batch0208.tau1667, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1012110 (by positivity) using 1 <;> norm_num)
            · have hs1012112 : InSquare (9/64) (-109/320) (1/320) tau := by
                convert childUL hs101211 hx101211 hy101211 using 1 <;> norm_num
              exact Batch0208.cell1669.sound htau (by
                simp only [Batch0208.cell1669, Batch0208.tau1669, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1012112 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-11/32 : ℝ) with hy101211 | hy101211
            · have hs1012111 : InSquare (47/320) (-111/320) (1/320) tau := by
                convert childLR hs101211 hx101211 hy101211 using 1 <;> norm_num
              exact Batch0208.cell1668.sound htau (by
                simp only [Batch0208.cell1668, Batch0208.tau1668, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1012111 (by positivity) using 1 <;> norm_num)
            · have hs1012113 : InSquare (47/320) (-109/320) (1/320) tau := by
                convert childUR hs101211 hx101211 hy101211 using 1 <;> norm_num
              exact Batch0208.cell1670.sound htau (by
                simp only [Batch0208.cell1670, Batch0208.tau1670, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1012113 (by positivity) using 1 <;> norm_num)
        · have hs101213 : InSquare (23/160) (-53/160) (1/160) tau := by
            convert childUR hs10121 hx10121 hy10121 using 1 <;> norm_num
          rcases le_total tau.re (23/160 : ℝ) with hx101213 | hx101213
          · rcases le_total tau.im (-53/160 : ℝ) with hy101213 | hy101213
            · have hs1012130 : InSquare (9/64) (-107/320) (1/320) tau := by
                convert childLL hs101213 hx101213 hy101213 using 1 <;> norm_num
              exact Batch0209.cell1675.sound htau (by
                simp only [Batch0209.cell1675, Batch0209.tau1675, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1012130 (by positivity) using 1 <;> norm_num)
            · have hs1012132 : InSquare (9/64) (-21/64) (1/320) tau := by
                convert childUL hs101213 hx101213 hy101213 using 1 <;> norm_num
              exact Batch0209.cell1677.sound htau (by
                simp only [Batch0209.cell1677, Batch0209.tau1677, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1012132 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-53/160 : ℝ) with hy101213 | hy101213
            · have hs1012131 : InSquare (47/320) (-107/320) (1/320) tau := by
                convert childLR hs101213 hx101213 hy101213 using 1 <;> norm_num
              exact Batch0209.cell1676.sound htau (by
                simp only [Batch0209.cell1676, Batch0209.tau1676, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1012131 (by positivity) using 1 <;> norm_num)
            · have hs1012133 : InSquare (47/320) (-21/64) (1/320) tau := by
                convert childUR hs101213 hx101213 hy101213 using 1 <;> norm_num
              exact Batch0209.cell1678.sound htau (by
                simp only [Batch0209.cell1678, Batch0209.tau1678, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1012133 (by positivity) using 1 <;> norm_num)
    · have hs10123 : InSquare (11/80) (-5/16) (1/80) tau := by
        convert childUR hs hx1012 hy1012 using 1 <;> norm_num
      rcases le_total tau.re (11/80 : ℝ) with hx10123 | hx10123
      · rcases le_total tau.im (-5/16 : ℝ) with hy10123 | hy10123
        · have hs101230 : InSquare (21/160) (-51/160) (1/160) tau := by
            convert childLL hs10123 hx10123 hy10123 using 1 <;> norm_num
          exact Batch0074.cell0593.sound htau (by
            simp only [Batch0074.cell0593, Batch0074.tau0593, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs101230 (by positivity) using 1 <;> norm_num)
        · have hs101232 : InSquare (21/160) (-49/160) (1/160) tau := by
            convert childUL hs10123 hx10123 hy10123 using 1 <;> norm_num
          exact Batch0074.cell0594.sound htau (by
            simp only [Batch0074.cell0594, Batch0074.tau0594, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs101232 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-5/16 : ℝ) with hy10123 | hy10123
        · have hs101231 : InSquare (23/160) (-51/160) (1/160) tau := by
            convert childLR hs10123 hx10123 hy10123 using 1 <;> norm_num
          rcases le_total tau.re (23/160 : ℝ) with hx101231 | hx101231
          · rcases le_total tau.im (-51/160 : ℝ) with hy101231 | hy101231
            · have hs1012310 : InSquare (9/64) (-103/320) (1/320) tau := by
                convert childLL hs101231 hx101231 hy101231 using 1 <;> norm_num
              exact Batch0209.cell1679.sound htau (by
                simp only [Batch0209.cell1679, Batch0209.tau1679, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1012310 (by positivity) using 1 <;> norm_num)
            · have hs1012312 : InSquare (9/64) (-101/320) (1/320) tau := by
                convert childUL hs101231 hx101231 hy101231 using 1 <;> norm_num
              exact Batch0210.cell1681.sound htau (by
                simp only [Batch0210.cell1681, Batch0210.tau1681, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1012312 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-51/160 : ℝ) with hy101231 | hy101231
            · have hs1012311 : InSquare (47/320) (-103/320) (1/320) tau := by
                convert childLR hs101231 hx101231 hy101231 using 1 <;> norm_num
              exact Batch0210.cell1680.sound htau (by
                simp only [Batch0210.cell1680, Batch0210.tau1680, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1012311 (by positivity) using 1 <;> norm_num)
            · have hs1012313 : InSquare (47/320) (-101/320) (1/320) tau := by
                convert childUR hs101231 hx101231 hy101231 using 1 <;> norm_num
              exact Batch0210.cell1682.sound htau (by
                simp only [Batch0210.cell1682, Batch0210.tau1682, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1012313 (by positivity) using 1 <;> norm_num)
        · have hs101233 : InSquare (23/160) (-49/160) (1/160) tau := by
            convert childUR hs10123 hx10123 hy10123 using 1 <;> norm_num
          exact Batch0074.cell0595.sound htau (by
            simp only [Batch0074.cell0595, Batch0074.tau0595, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs101233 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1012
