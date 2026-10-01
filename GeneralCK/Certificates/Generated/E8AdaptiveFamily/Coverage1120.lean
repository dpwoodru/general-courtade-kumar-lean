import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0080
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0081
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0222
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0223
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0224
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0225

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1120

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (9/40) (-11/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (9/40 : ℝ) with hx1120 | hx1120
  · rcases le_total tau.im (-11/40 : ℝ) with hy1120 | hy1120
    · have hs11200 : InSquare (17/80) (-23/80) (1/80) tau := by
        convert childLL hs hx1120 hy1120 using 1 <;> norm_num
      rcases le_total tau.re (17/80 : ℝ) with hx11200 | hx11200
      · rcases le_total tau.im (-23/80 : ℝ) with hy11200 | hy11200
        · have hs112000 : InSquare (33/160) (-47/160) (1/160) tau := by
            convert childLL hs11200 hx11200 hy11200 using 1 <;> norm_num
          rcases le_total tau.re (33/160 : ℝ) with hx112000 | hx112000
          · rcases le_total tau.im (-47/160 : ℝ) with hy112000 | hy112000
            · have hs1120000 : InSquare (13/64) (-19/64) (1/320) tau := by
                convert childLL hs112000 hx112000 hy112000 using 1 <;> norm_num
              exact Batch0222.cell1781.sound htau (by
                simp only [Batch0222.cell1781, Batch0222.tau1781, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1120000 (by positivity) using 1 <;> norm_num)
            · have hs1120002 : InSquare (13/64) (-93/320) (1/320) tau := by
                convert childUL hs112000 hx112000 hy112000 using 1 <;> norm_num
              exact Batch0222.cell1783.sound htau (by
                simp only [Batch0222.cell1783, Batch0222.tau1783, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1120002 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-47/160 : ℝ) with hy112000 | hy112000
            · have hs1120001 : InSquare (67/320) (-19/64) (1/320) tau := by
                convert childLR hs112000 hx112000 hy112000 using 1 <;> norm_num
              exact Batch0222.cell1782.sound htau (by
                simp only [Batch0222.cell1782, Batch0222.tau1782, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1120001 (by positivity) using 1 <;> norm_num)
            · have hs1120003 : InSquare (67/320) (-93/320) (1/320) tau := by
                convert childUR hs112000 hx112000 hy112000 using 1 <;> norm_num
              exact Batch0223.cell1784.sound htau (by
                simp only [Batch0223.cell1784, Batch0223.tau1784, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1120003 (by positivity) using 1 <;> norm_num)
        · have hs112002 : InSquare (33/160) (-9/32) (1/160) tau := by
            convert childUL hs11200 hx11200 hy11200 using 1 <;> norm_num
          exact Batch0080.cell0646.sound htau (by
            simp only [Batch0080.cell0646, Batch0080.tau0646, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs112002 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-23/80 : ℝ) with hy11200 | hy11200
        · have hs112001 : InSquare (7/32) (-47/160) (1/160) tau := by
            convert childLR hs11200 hx11200 hy11200 using 1 <;> norm_num
          rcases le_total tau.re (7/32 : ℝ) with hx112001 | hx112001
          · rcases le_total tau.im (-47/160 : ℝ) with hy112001 | hy112001
            · have hs1120010 : InSquare (69/320) (-19/64) (1/320) tau := by
                convert childLL hs112001 hx112001 hy112001 using 1 <;> norm_num
              exact Batch0223.cell1785.sound htau (by
                simp only [Batch0223.cell1785, Batch0223.tau1785, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1120010 (by positivity) using 1 <;> norm_num)
            · have hs1120012 : InSquare (69/320) (-93/320) (1/320) tau := by
                convert childUL hs112001 hx112001 hy112001 using 1 <;> norm_num
              exact Batch0223.cell1787.sound htau (by
                simp only [Batch0223.cell1787, Batch0223.tau1787, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1120012 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-47/160 : ℝ) with hy112001 | hy112001
            · have hs1120011 : InSquare (71/320) (-19/64) (1/320) tau := by
                convert childLR hs112001 hx112001 hy112001 using 1 <;> norm_num
              exact Batch0223.cell1786.sound htau (by
                simp only [Batch0223.cell1786, Batch0223.tau1786, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1120011 (by positivity) using 1 <;> norm_num)
            · have hs1120013 : InSquare (71/320) (-93/320) (1/320) tau := by
                convert childUR hs112001 hx112001 hy112001 using 1 <;> norm_num
              exact Batch0223.cell1788.sound htau (by
                simp only [Batch0223.cell1788, Batch0223.tau1788, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1120013 (by positivity) using 1 <;> norm_num)
        · have hs112003 : InSquare (7/32) (-9/32) (1/160) tau := by
            convert childUR hs11200 hx11200 hy11200 using 1 <;> norm_num
          exact Batch0080.cell0647.sound htau (by
            simp only [Batch0080.cell0647, Batch0080.tau0647, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs112003 (by positivity) using 1 <;> norm_num)
    · have hs11202 : InSquare (17/80) (-21/80) (1/80) tau := by
        convert childUL hs hx1120 hy1120 using 1 <;> norm_num
      rcases le_total tau.re (17/80 : ℝ) with hx11202 | hx11202
      · rcases le_total tau.im (-21/80 : ℝ) with hy11202 | hy11202
        · have hs112020 : InSquare (33/160) (-43/160) (1/160) tau := by
            convert childLL hs11202 hx11202 hy11202 using 1 <;> norm_num
          exact Batch0081.cell0648.sound htau (by
            simp only [Batch0081.cell0648, Batch0081.tau0648, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs112020 (by positivity) using 1 <;> norm_num)
        · have hs112022 : InSquare (33/160) (-41/160) (1/160) tau := by
            convert childUL hs11202 hx11202 hy11202 using 1 <;> norm_num
          exact Batch0081.cell0650.sound htau (by
            simp only [Batch0081.cell0650, Batch0081.tau0650, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs112022 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-21/80 : ℝ) with hy11202 | hy11202
        · have hs112021 : InSquare (7/32) (-43/160) (1/160) tau := by
            convert childLR hs11202 hx11202 hy11202 using 1 <;> norm_num
          exact Batch0081.cell0649.sound htau (by
            simp only [Batch0081.cell0649, Batch0081.tau0649, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs112021 (by positivity) using 1 <;> norm_num)
        · have hs112023 : InSquare (7/32) (-41/160) (1/160) tau := by
            convert childUR hs11202 hx11202 hy11202 using 1 <;> norm_num
          exact Batch0081.cell0651.sound htau (by
            simp only [Batch0081.cell0651, Batch0081.tau0651, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs112023 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (-11/40 : ℝ) with hy1120 | hy1120
    · have hs11201 : InSquare (19/80) (-23/80) (1/80) tau := by
        convert childLR hs hx1120 hy1120 using 1 <;> norm_num
      rcases le_total tau.re (19/80 : ℝ) with hx11201 | hx11201
      · rcases le_total tau.im (-23/80 : ℝ) with hy11201 | hy11201
        · have hs112010 : InSquare (37/160) (-47/160) (1/160) tau := by
            convert childLL hs11201 hx11201 hy11201 using 1 <;> norm_num
          rcases le_total tau.re (37/160 : ℝ) with hx112010 | hx112010
          · rcases le_total tau.im (-47/160 : ℝ) with hy112010 | hy112010
            · have hs1120100 : InSquare (73/320) (-19/64) (1/320) tau := by
                convert childLL hs112010 hx112010 hy112010 using 1 <;> norm_num
              exact Batch0223.cell1789.sound htau (by
                simp only [Batch0223.cell1789, Batch0223.tau1789, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1120100 (by positivity) using 1 <;> norm_num)
            · have hs1120102 : InSquare (73/320) (-93/320) (1/320) tau := by
                convert childUL hs112010 hx112010 hy112010 using 1 <;> norm_num
              exact Batch0223.cell1791.sound htau (by
                simp only [Batch0223.cell1791, Batch0223.tau1791, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1120102 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-47/160 : ℝ) with hy112010 | hy112010
            · have hs1120101 : InSquare (15/64) (-19/64) (1/320) tau := by
                convert childLR hs112010 hx112010 hy112010 using 1 <;> norm_num
              exact Batch0223.cell1790.sound htau (by
                simp only [Batch0223.cell1790, Batch0223.tau1790, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1120101 (by positivity) using 1 <;> norm_num)
            · have hs1120103 : InSquare (15/64) (-93/320) (1/320) tau := by
                convert childUR hs112010 hx112010 hy112010 using 1 <;> norm_num
              exact Batch0224.cell1792.sound htau (by
                simp only [Batch0224.cell1792, Batch0224.tau1792, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1120103 (by positivity) using 1 <;> norm_num)
        · have hs112012 : InSquare (37/160) (-9/32) (1/160) tau := by
            convert childUL hs11201 hx11201 hy11201 using 1 <;> norm_num
          rcases le_total tau.re (37/160 : ℝ) with hx112012 | hx112012
          · rcases le_total tau.im (-9/32 : ℝ) with hy112012 | hy112012
            · have hs1120120 : InSquare (73/320) (-91/320) (1/320) tau := by
                convert childLL hs112012 hx112012 hy112012 using 1 <;> norm_num
              exact Batch0224.cell1797.sound htau (by
                simp only [Batch0224.cell1797, Batch0224.tau1797, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1120120 (by positivity) using 1 <;> norm_num)
            · have hs1120122 : InSquare (73/320) (-89/320) (1/320) tau := by
                convert childUL hs112012 hx112012 hy112012 using 1 <;> norm_num
              exact Batch0224.cell1799.sound htau (by
                simp only [Batch0224.cell1799, Batch0224.tau1799, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1120122 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-9/32 : ℝ) with hy112012 | hy112012
            · have hs1120121 : InSquare (15/64) (-91/320) (1/320) tau := by
                convert childLR hs112012 hx112012 hy112012 using 1 <;> norm_num
              exact Batch0224.cell1798.sound htau (by
                simp only [Batch0224.cell1798, Batch0224.tau1798, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1120121 (by positivity) using 1 <;> norm_num)
            · have hs1120123 : InSquare (15/64) (-89/320) (1/320) tau := by
                convert childUR hs112012 hx112012 hy112012 using 1 <;> norm_num
              exact Batch0225.cell1800.sound htau (by
                simp only [Batch0225.cell1800, Batch0225.tau1800, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1120123 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-23/80 : ℝ) with hy11201 | hy11201
        · have hs112011 : InSquare (39/160) (-47/160) (1/160) tau := by
            convert childLR hs11201 hx11201 hy11201 using 1 <;> norm_num
          rcases le_total tau.re (39/160 : ℝ) with hx112011 | hx112011
          · rcases le_total tau.im (-47/160 : ℝ) with hy112011 | hy112011
            · have hs1120110 : InSquare (77/320) (-19/64) (1/320) tau := by
                convert childLL hs112011 hx112011 hy112011 using 1 <;> norm_num
              exact Batch0224.cell1793.sound htau (by
                simp only [Batch0224.cell1793, Batch0224.tau1793, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1120110 (by positivity) using 1 <;> norm_num)
            · have hs1120112 : InSquare (77/320) (-93/320) (1/320) tau := by
                convert childUL hs112011 hx112011 hy112011 using 1 <;> norm_num
              exact Batch0224.cell1795.sound htau (by
                simp only [Batch0224.cell1795, Batch0224.tau1795, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1120112 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-47/160 : ℝ) with hy112011 | hy112011
            · have hs1120111 : InSquare (79/320) (-19/64) (1/320) tau := by
                convert childLR hs112011 hx112011 hy112011 using 1 <;> norm_num
              exact Batch0224.cell1794.sound htau (by
                simp only [Batch0224.cell1794, Batch0224.tau1794, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1120111 (by positivity) using 1 <;> norm_num)
            · have hs1120113 : InSquare (79/320) (-93/320) (1/320) tau := by
                convert childUR hs112011 hx112011 hy112011 using 1 <;> norm_num
              exact Batch0224.cell1796.sound htau (by
                simp only [Batch0224.cell1796, Batch0224.tau1796, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1120113 (by positivity) using 1 <;> norm_num)
        · have hs112013 : InSquare (39/160) (-9/32) (1/160) tau := by
            convert childUR hs11201 hx11201 hy11201 using 1 <;> norm_num
          rcases le_total tau.re (39/160 : ℝ) with hx112013 | hx112013
          · rcases le_total tau.im (-9/32 : ℝ) with hy112013 | hy112013
            · have hs1120130 : InSquare (77/320) (-91/320) (1/320) tau := by
                convert childLL hs112013 hx112013 hy112013 using 1 <;> norm_num
              exact Batch0225.cell1801.sound htau (by
                simp only [Batch0225.cell1801, Batch0225.tau1801, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1120130 (by positivity) using 1 <;> norm_num)
            · have hs1120132 : InSquare (77/320) (-89/320) (1/320) tau := by
                convert childUL hs112013 hx112013 hy112013 using 1 <;> norm_num
              exact Batch0225.cell1803.sound htau (by
                simp only [Batch0225.cell1803, Batch0225.tau1803, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1120132 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-9/32 : ℝ) with hy112013 | hy112013
            · have hs1120131 : InSquare (79/320) (-91/320) (1/320) tau := by
                convert childLR hs112013 hx112013 hy112013 using 1 <;> norm_num
              exact Batch0225.cell1802.sound htau (by
                simp only [Batch0225.cell1802, Batch0225.tau1802, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1120131 (by positivity) using 1 <;> norm_num)
            · have hs1120133 : InSquare (79/320) (-89/320) (1/320) tau := by
                convert childUR hs112013 hx112013 hy112013 using 1 <;> norm_num
              exact Batch0225.cell1804.sound htau (by
                simp only [Batch0225.cell1804, Batch0225.tau1804, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1120133 (by positivity) using 1 <;> norm_num)
    · have hs11203 : InSquare (19/80) (-21/80) (1/80) tau := by
        convert childUR hs hx1120 hy1120 using 1 <;> norm_num
      rcases le_total tau.re (19/80 : ℝ) with hx11203 | hx11203
      · rcases le_total tau.im (-21/80 : ℝ) with hy11203 | hy11203
        · have hs112030 : InSquare (37/160) (-43/160) (1/160) tau := by
            convert childLL hs11203 hx11203 hy11203 using 1 <;> norm_num
          exact Batch0081.cell0652.sound htau (by
            simp only [Batch0081.cell0652, Batch0081.tau0652, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs112030 (by positivity) using 1 <;> norm_num)
        · have hs112032 : InSquare (37/160) (-41/160) (1/160) tau := by
            convert childUL hs11203 hx11203 hy11203 using 1 <;> norm_num
          exact Batch0081.cell0654.sound htau (by
            simp only [Batch0081.cell0654, Batch0081.tau0654, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs112032 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-21/80 : ℝ) with hy11203 | hy11203
        · have hs112031 : InSquare (39/160) (-43/160) (1/160) tau := by
            convert childLR hs11203 hx11203 hy11203 using 1 <;> norm_num
          exact Batch0081.cell0653.sound htau (by
            simp only [Batch0081.cell0653, Batch0081.tau0653, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs112031 (by positivity) using 1 <;> norm_num)
        · have hs112033 : InSquare (39/160) (-41/160) (1/160) tau := by
            convert childUR hs11203 hx11203 hy11203 using 1 <;> norm_num
          exact Batch0081.cell0655.sound htau (by
            simp only [Batch0081.cell0655, Batch0081.tau0655, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs112033 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1120
