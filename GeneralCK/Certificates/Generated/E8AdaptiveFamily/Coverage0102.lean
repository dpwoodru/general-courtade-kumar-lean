import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0049
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0170
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0171
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0172
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0173
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0174
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0175
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0176
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0177
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0339
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0340

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0102

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-7/40) (-13/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (-7/40 : ℝ) with hx0102 | hx0102
  · rcases le_total tau.im (-13/40 : ℝ) with hy0102 | hy0102
    · have hs01020 : InSquare (-3/16) (-27/80) (1/80) tau := by
        convert childLL hs hx0102 hy0102 using 1 <;> norm_num
      rcases le_total tau.re (-3/16 : ℝ) with hx01020 | hx01020
      · rcases le_total tau.im (-27/80 : ℝ) with hy01020 | hy01020
        · have hs010200 : InSquare (-31/160) (-11/32) (1/160) tau := by
            convert childLL hs01020 hx01020 hy01020 using 1 <;> norm_num
          rcases le_total tau.re (-31/160 : ℝ) with hx010200 | hx010200
          · rcases le_total tau.im (-11/32 : ℝ) with hy010200 | hy010200
            · have hs0102000 : InSquare (-63/320) (-111/320) (1/320) tau := by
                convert childLL hs010200 hx010200 hy010200 using 1 <;> norm_num
              rcases le_total tau.re (-63/320 : ℝ) with hx0102000 | hx0102000
              · rcases le_total tau.im (-111/320 : ℝ) with hy0102000 | hy0102000
                · have hs01020000 : InSquare (-127/640) (-223/640) (1/640) tau := by
                    convert childLL hs0102000 hx0102000 hy0102000 using 1 <;> norm_num
                  exact Batch0339.cell2713.sound htau (by
                    simp only [Batch0339.cell2713, Batch0339.tau2713, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01020000 (by positivity) using 1 <;> norm_num)
                · have hs01020002 : InSquare (-127/640) (-221/640) (1/640) tau := by
                    convert childUL hs0102000 hx0102000 hy0102000 using 1 <;> norm_num
                  exact Batch0339.cell2715.sound htau (by
                    simp only [Batch0339.cell2715, Batch0339.tau2715, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01020002 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-111/320 : ℝ) with hy0102000 | hy0102000
                · have hs01020001 : InSquare (-25/128) (-223/640) (1/640) tau := by
                    convert childLR hs0102000 hx0102000 hy0102000 using 1 <;> norm_num
                  exact Batch0339.cell2714.sound htau (by
                    simp only [Batch0339.cell2714, Batch0339.tau2714, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01020001 (by positivity) using 1 <;> norm_num)
                · have hs01020003 : InSquare (-25/128) (-221/640) (1/640) tau := by
                    convert childUR hs0102000 hx0102000 hy0102000 using 1 <;> norm_num
                  exact Batch0339.cell2716.sound htau (by
                    simp only [Batch0339.cell2716, Batch0339.tau2716, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01020003 (by positivity) using 1 <;> norm_num)
            · have hs0102002 : InSquare (-63/320) (-109/320) (1/320) tau := by
                convert childUL hs010200 hx010200 hy010200 using 1 <;> norm_num
              exact Batch0170.cell1366.sound htau (by
                simp only [Batch0170.cell1366, Batch0170.tau1366, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0102002 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-11/32 : ℝ) with hy010200 | hy010200
            · have hs0102001 : InSquare (-61/320) (-111/320) (1/320) tau := by
                convert childLR hs010200 hx010200 hy010200 using 1 <;> norm_num
              rcases le_total tau.re (-61/320 : ℝ) with hx0102001 | hx0102001
              · rcases le_total tau.im (-111/320 : ℝ) with hy0102001 | hy0102001
                · have hs01020010 : InSquare (-123/640) (-223/640) (1/640) tau := by
                    convert childLL hs0102001 hx0102001 hy0102001 using 1 <;> norm_num
                  exact Batch0339.cell2717.sound htau (by
                    simp only [Batch0339.cell2717, Batch0339.tau2717, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01020010 (by positivity) using 1 <;> norm_num)
                · have hs01020012 : InSquare (-123/640) (-221/640) (1/640) tau := by
                    convert childUL hs0102001 hx0102001 hy0102001 using 1 <;> norm_num
                  exact Batch0339.cell2719.sound htau (by
                    simp only [Batch0339.cell2719, Batch0339.tau2719, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01020012 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-111/320 : ℝ) with hy0102001 | hy0102001
                · have hs01020011 : InSquare (-121/640) (-223/640) (1/640) tau := by
                    convert childLR hs0102001 hx0102001 hy0102001 using 1 <;> norm_num
                  exact Batch0339.cell2718.sound htau (by
                    simp only [Batch0339.cell2718, Batch0339.tau2718, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01020011 (by positivity) using 1 <;> norm_num)
                · have hs01020013 : InSquare (-121/640) (-221/640) (1/640) tau := by
                    convert childUR hs0102001 hx0102001 hy0102001 using 1 <;> norm_num
                  exact Batch0340.cell2720.sound htau (by
                    simp only [Batch0340.cell2720, Batch0340.tau2720, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01020013 (by positivity) using 1 <;> norm_num)
            · have hs0102003 : InSquare (-61/320) (-109/320) (1/320) tau := by
                convert childUR hs010200 hx010200 hy010200 using 1 <;> norm_num
              exact Batch0170.cell1367.sound htau (by
                simp only [Batch0170.cell1367, Batch0170.tau1367, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0102003 (by positivity) using 1 <;> norm_num)
        · have hs010202 : InSquare (-31/160) (-53/160) (1/160) tau := by
            convert childUL hs01020 hx01020 hy01020 using 1 <;> norm_num
          rcases le_total tau.re (-31/160 : ℝ) with hx010202 | hx010202
          · rcases le_total tau.im (-53/160 : ℝ) with hy010202 | hy010202
            · have hs0102020 : InSquare (-63/320) (-107/320) (1/320) tau := by
                convert childLL hs010202 hx010202 hy010202 using 1 <;> norm_num
              exact Batch0171.cell1372.sound htau (by
                simp only [Batch0171.cell1372, Batch0171.tau1372, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0102020 (by positivity) using 1 <;> norm_num)
            · have hs0102022 : InSquare (-63/320) (-21/64) (1/320) tau := by
                convert childUL hs010202 hx010202 hy010202 using 1 <;> norm_num
              exact Batch0171.cell1374.sound htau (by
                simp only [Batch0171.cell1374, Batch0171.tau1374, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0102022 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-53/160 : ℝ) with hy010202 | hy010202
            · have hs0102021 : InSquare (-61/320) (-107/320) (1/320) tau := by
                convert childLR hs010202 hx010202 hy010202 using 1 <;> norm_num
              exact Batch0171.cell1373.sound htau (by
                simp only [Batch0171.cell1373, Batch0171.tau1373, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0102021 (by positivity) using 1 <;> norm_num)
            · have hs0102023 : InSquare (-61/320) (-21/64) (1/320) tau := by
                convert childUR hs010202 hx010202 hy010202 using 1 <;> norm_num
              exact Batch0171.cell1375.sound htau (by
                simp only [Batch0171.cell1375, Batch0171.tau1375, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0102023 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-27/80 : ℝ) with hy01020 | hy01020
        · have hs010201 : InSquare (-29/160) (-11/32) (1/160) tau := by
            convert childLR hs01020 hx01020 hy01020 using 1 <;> norm_num
          rcases le_total tau.re (-29/160 : ℝ) with hx010201 | hx010201
          · rcases le_total tau.im (-11/32 : ℝ) with hy010201 | hy010201
            · have hs0102010 : InSquare (-59/320) (-111/320) (1/320) tau := by
                convert childLL hs010201 hx010201 hy010201 using 1 <;> norm_num
              exact Batch0171.cell1368.sound htau (by
                simp only [Batch0171.cell1368, Batch0171.tau1368, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0102010 (by positivity) using 1 <;> norm_num)
            · have hs0102012 : InSquare (-59/320) (-109/320) (1/320) tau := by
                convert childUL hs010201 hx010201 hy010201 using 1 <;> norm_num
              exact Batch0171.cell1370.sound htau (by
                simp only [Batch0171.cell1370, Batch0171.tau1370, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0102012 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-11/32 : ℝ) with hy010201 | hy010201
            · have hs0102011 : InSquare (-57/320) (-111/320) (1/320) tau := by
                convert childLR hs010201 hx010201 hy010201 using 1 <;> norm_num
              exact Batch0171.cell1369.sound htau (by
                simp only [Batch0171.cell1369, Batch0171.tau1369, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0102011 (by positivity) using 1 <;> norm_num)
            · have hs0102013 : InSquare (-57/320) (-109/320) (1/320) tau := by
                convert childUR hs010201 hx010201 hy010201 using 1 <;> norm_num
              exact Batch0171.cell1371.sound htau (by
                simp only [Batch0171.cell1371, Batch0171.tau1371, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0102013 (by positivity) using 1 <;> norm_num)
        · have hs010203 : InSquare (-29/160) (-53/160) (1/160) tau := by
            convert childUR hs01020 hx01020 hy01020 using 1 <;> norm_num
          rcases le_total tau.re (-29/160 : ℝ) with hx010203 | hx010203
          · rcases le_total tau.im (-53/160 : ℝ) with hy010203 | hy010203
            · have hs0102030 : InSquare (-59/320) (-107/320) (1/320) tau := by
                convert childLL hs010203 hx010203 hy010203 using 1 <;> norm_num
              exact Batch0172.cell1376.sound htau (by
                simp only [Batch0172.cell1376, Batch0172.tau1376, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0102030 (by positivity) using 1 <;> norm_num)
            · have hs0102032 : InSquare (-59/320) (-21/64) (1/320) tau := by
                convert childUL hs010203 hx010203 hy010203 using 1 <;> norm_num
              exact Batch0172.cell1378.sound htau (by
                simp only [Batch0172.cell1378, Batch0172.tau1378, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0102032 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-53/160 : ℝ) with hy010203 | hy010203
            · have hs0102031 : InSquare (-57/320) (-107/320) (1/320) tau := by
                convert childLR hs010203 hx010203 hy010203 using 1 <;> norm_num
              exact Batch0172.cell1377.sound htau (by
                simp only [Batch0172.cell1377, Batch0172.tau1377, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0102031 (by positivity) using 1 <;> norm_num)
            · have hs0102033 : InSquare (-57/320) (-21/64) (1/320) tau := by
                convert childUR hs010203 hx010203 hy010203 using 1 <;> norm_num
              exact Batch0172.cell1379.sound htau (by
                simp only [Batch0172.cell1379, Batch0172.tau1379, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0102033 (by positivity) using 1 <;> norm_num)
    · have hs01022 : InSquare (-3/16) (-5/16) (1/80) tau := by
        convert childUL hs hx0102 hy0102 using 1 <;> norm_num
      rcases le_total tau.re (-3/16 : ℝ) with hx01022 | hx01022
      · rcases le_total tau.im (-5/16 : ℝ) with hy01022 | hy01022
        · have hs010220 : InSquare (-31/160) (-51/160) (1/160) tau := by
            convert childLL hs01022 hx01022 hy01022 using 1 <;> norm_num
          rcases le_total tau.re (-31/160 : ℝ) with hx010220 | hx010220
          · rcases le_total tau.im (-51/160 : ℝ) with hy010220 | hy010220
            · have hs0102200 : InSquare (-63/320) (-103/320) (1/320) tau := by
                convert childLL hs010220 hx010220 hy010220 using 1 <;> norm_num
              exact Batch0174.cell1396.sound htau (by
                simp only [Batch0174.cell1396, Batch0174.tau1396, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0102200 (by positivity) using 1 <;> norm_num)
            · have hs0102202 : InSquare (-63/320) (-101/320) (1/320) tau := by
                convert childUL hs010220 hx010220 hy010220 using 1 <;> norm_num
              exact Batch0174.cell1398.sound htau (by
                simp only [Batch0174.cell1398, Batch0174.tau1398, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0102202 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-51/160 : ℝ) with hy010220 | hy010220
            · have hs0102201 : InSquare (-61/320) (-103/320) (1/320) tau := by
                convert childLR hs010220 hx010220 hy010220 using 1 <;> norm_num
              exact Batch0174.cell1397.sound htau (by
                simp only [Batch0174.cell1397, Batch0174.tau1397, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0102201 (by positivity) using 1 <;> norm_num)
            · have hs0102203 : InSquare (-61/320) (-101/320) (1/320) tau := by
                convert childUR hs010220 hx010220 hy010220 using 1 <;> norm_num
              exact Batch0174.cell1399.sound htau (by
                simp only [Batch0174.cell1399, Batch0174.tau1399, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0102203 (by positivity) using 1 <;> norm_num)
        · have hs010222 : InSquare (-31/160) (-49/160) (1/160) tau := by
            convert childUL hs01022 hx01022 hy01022 using 1 <;> norm_num
          rcases le_total tau.re (-31/160 : ℝ) with hx010222 | hx010222
          · rcases le_total tau.im (-49/160 : ℝ) with hy010222 | hy010222
            · have hs0102220 : InSquare (-63/320) (-99/320) (1/320) tau := by
                convert childLL hs010222 hx010222 hy010222 using 1 <;> norm_num
              exact Batch0175.cell1404.sound htau (by
                simp only [Batch0175.cell1404, Batch0175.tau1404, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0102220 (by positivity) using 1 <;> norm_num)
            · have hs0102222 : InSquare (-63/320) (-97/320) (1/320) tau := by
                convert childUL hs010222 hx010222 hy010222 using 1 <;> norm_num
              exact Batch0175.cell1406.sound htau (by
                simp only [Batch0175.cell1406, Batch0175.tau1406, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0102222 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-49/160 : ℝ) with hy010222 | hy010222
            · have hs0102221 : InSquare (-61/320) (-99/320) (1/320) tau := by
                convert childLR hs010222 hx010222 hy010222 using 1 <;> norm_num
              exact Batch0175.cell1405.sound htau (by
                simp only [Batch0175.cell1405, Batch0175.tau1405, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0102221 (by positivity) using 1 <;> norm_num)
            · have hs0102223 : InSquare (-61/320) (-97/320) (1/320) tau := by
                convert childUR hs010222 hx010222 hy010222 using 1 <;> norm_num
              exact Batch0175.cell1407.sound htau (by
                simp only [Batch0175.cell1407, Batch0175.tau1407, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0102223 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-5/16 : ℝ) with hy01022 | hy01022
        · have hs010221 : InSquare (-29/160) (-51/160) (1/160) tau := by
            convert childLR hs01022 hx01022 hy01022 using 1 <;> norm_num
          rcases le_total tau.re (-29/160 : ℝ) with hx010221 | hx010221
          · rcases le_total tau.im (-51/160 : ℝ) with hy010221 | hy010221
            · have hs0102210 : InSquare (-59/320) (-103/320) (1/320) tau := by
                convert childLL hs010221 hx010221 hy010221 using 1 <;> norm_num
              exact Batch0175.cell1400.sound htau (by
                simp only [Batch0175.cell1400, Batch0175.tau1400, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0102210 (by positivity) using 1 <;> norm_num)
            · have hs0102212 : InSquare (-59/320) (-101/320) (1/320) tau := by
                convert childUL hs010221 hx010221 hy010221 using 1 <;> norm_num
              exact Batch0175.cell1402.sound htau (by
                simp only [Batch0175.cell1402, Batch0175.tau1402, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0102212 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-51/160 : ℝ) with hy010221 | hy010221
            · have hs0102211 : InSquare (-57/320) (-103/320) (1/320) tau := by
                convert childLR hs010221 hx010221 hy010221 using 1 <;> norm_num
              exact Batch0175.cell1401.sound htau (by
                simp only [Batch0175.cell1401, Batch0175.tau1401, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0102211 (by positivity) using 1 <;> norm_num)
            · have hs0102213 : InSquare (-57/320) (-101/320) (1/320) tau := by
                convert childUR hs010221 hx010221 hy010221 using 1 <;> norm_num
              exact Batch0175.cell1403.sound htau (by
                simp only [Batch0175.cell1403, Batch0175.tau1403, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0102213 (by positivity) using 1 <;> norm_num)
        · have hs010223 : InSquare (-29/160) (-49/160) (1/160) tau := by
            convert childUR hs01022 hx01022 hy01022 using 1 <;> norm_num
          rcases le_total tau.re (-29/160 : ℝ) with hx010223 | hx010223
          · rcases le_total tau.im (-49/160 : ℝ) with hy010223 | hy010223
            · have hs0102230 : InSquare (-59/320) (-99/320) (1/320) tau := by
                convert childLL hs010223 hx010223 hy010223 using 1 <;> norm_num
              exact Batch0176.cell1408.sound htau (by
                simp only [Batch0176.cell1408, Batch0176.tau1408, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0102230 (by positivity) using 1 <;> norm_num)
            · have hs0102232 : InSquare (-59/320) (-97/320) (1/320) tau := by
                convert childUL hs010223 hx010223 hy010223 using 1 <;> norm_num
              exact Batch0176.cell1410.sound htau (by
                simp only [Batch0176.cell1410, Batch0176.tau1410, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0102232 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-49/160 : ℝ) with hy010223 | hy010223
            · have hs0102231 : InSquare (-57/320) (-99/320) (1/320) tau := by
                convert childLR hs010223 hx010223 hy010223 using 1 <;> norm_num
              exact Batch0176.cell1409.sound htau (by
                simp only [Batch0176.cell1409, Batch0176.tau1409, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0102231 (by positivity) using 1 <;> norm_num)
            · have hs0102233 : InSquare (-57/320) (-97/320) (1/320) tau := by
                convert childUR hs010223 hx010223 hy010223 using 1 <;> norm_num
              exact Batch0176.cell1411.sound htau (by
                simp only [Batch0176.cell1411, Batch0176.tau1411, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0102233 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (-13/40 : ℝ) with hy0102 | hy0102
    · have hs01021 : InSquare (-13/80) (-27/80) (1/80) tau := by
        convert childLR hs hx0102 hy0102 using 1 <;> norm_num
      rcases le_total tau.re (-13/80 : ℝ) with hx01021 | hx01021
      · rcases le_total tau.im (-27/80 : ℝ) with hy01021 | hy01021
        · have hs010210 : InSquare (-27/160) (-11/32) (1/160) tau := by
            convert childLL hs01021 hx01021 hy01021 using 1 <;> norm_num
          rcases le_total tau.re (-27/160 : ℝ) with hx010210 | hx010210
          · rcases le_total tau.im (-11/32 : ℝ) with hy010210 | hy010210
            · have hs0102100 : InSquare (-11/64) (-111/320) (1/320) tau := by
                convert childLL hs010210 hx010210 hy010210 using 1 <;> norm_num
              exact Batch0172.cell1380.sound htau (by
                simp only [Batch0172.cell1380, Batch0172.tau1380, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0102100 (by positivity) using 1 <;> norm_num)
            · have hs0102102 : InSquare (-11/64) (-109/320) (1/320) tau := by
                convert childUL hs010210 hx010210 hy010210 using 1 <;> norm_num
              exact Batch0172.cell1382.sound htau (by
                simp only [Batch0172.cell1382, Batch0172.tau1382, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0102102 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-11/32 : ℝ) with hy010210 | hy010210
            · have hs0102101 : InSquare (-53/320) (-111/320) (1/320) tau := by
                convert childLR hs010210 hx010210 hy010210 using 1 <;> norm_num
              exact Batch0172.cell1381.sound htau (by
                simp only [Batch0172.cell1381, Batch0172.tau1381, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0102101 (by positivity) using 1 <;> norm_num)
            · have hs0102103 : InSquare (-53/320) (-109/320) (1/320) tau := by
                convert childUR hs010210 hx010210 hy010210 using 1 <;> norm_num
              exact Batch0172.cell1383.sound htau (by
                simp only [Batch0172.cell1383, Batch0172.tau1383, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0102103 (by positivity) using 1 <;> norm_num)
        · have hs010212 : InSquare (-27/160) (-53/160) (1/160) tau := by
            convert childUL hs01021 hx01021 hy01021 using 1 <;> norm_num
          rcases le_total tau.re (-27/160 : ℝ) with hx010212 | hx010212
          · rcases le_total tau.im (-53/160 : ℝ) with hy010212 | hy010212
            · have hs0102120 : InSquare (-11/64) (-107/320) (1/320) tau := by
                convert childLL hs010212 hx010212 hy010212 using 1 <;> norm_num
              exact Batch0173.cell1388.sound htau (by
                simp only [Batch0173.cell1388, Batch0173.tau1388, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0102120 (by positivity) using 1 <;> norm_num)
            · have hs0102122 : InSquare (-11/64) (-21/64) (1/320) tau := by
                convert childUL hs010212 hx010212 hy010212 using 1 <;> norm_num
              exact Batch0173.cell1390.sound htau (by
                simp only [Batch0173.cell1390, Batch0173.tau1390, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0102122 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-53/160 : ℝ) with hy010212 | hy010212
            · have hs0102121 : InSquare (-53/320) (-107/320) (1/320) tau := by
                convert childLR hs010212 hx010212 hy010212 using 1 <;> norm_num
              exact Batch0173.cell1389.sound htau (by
                simp only [Batch0173.cell1389, Batch0173.tau1389, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0102121 (by positivity) using 1 <;> norm_num)
            · have hs0102123 : InSquare (-53/320) (-21/64) (1/320) tau := by
                convert childUR hs010212 hx010212 hy010212 using 1 <;> norm_num
              exact Batch0173.cell1391.sound htau (by
                simp only [Batch0173.cell1391, Batch0173.tau1391, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0102123 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-27/80 : ℝ) with hy01021 | hy01021
        · have hs010211 : InSquare (-5/32) (-11/32) (1/160) tau := by
            convert childLR hs01021 hx01021 hy01021 using 1 <;> norm_num
          rcases le_total tau.re (-5/32 : ℝ) with hx010211 | hx010211
          · rcases le_total tau.im (-11/32 : ℝ) with hy010211 | hy010211
            · have hs0102110 : InSquare (-51/320) (-111/320) (1/320) tau := by
                convert childLL hs010211 hx010211 hy010211 using 1 <;> norm_num
              exact Batch0173.cell1384.sound htau (by
                simp only [Batch0173.cell1384, Batch0173.tau1384, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0102110 (by positivity) using 1 <;> norm_num)
            · have hs0102112 : InSquare (-51/320) (-109/320) (1/320) tau := by
                convert childUL hs010211 hx010211 hy010211 using 1 <;> norm_num
              exact Batch0173.cell1386.sound htau (by
                simp only [Batch0173.cell1386, Batch0173.tau1386, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0102112 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-11/32 : ℝ) with hy010211 | hy010211
            · have hs0102111 : InSquare (-49/320) (-111/320) (1/320) tau := by
                convert childLR hs010211 hx010211 hy010211 using 1 <;> norm_num
              exact Batch0173.cell1385.sound htau (by
                simp only [Batch0173.cell1385, Batch0173.tau1385, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0102111 (by positivity) using 1 <;> norm_num)
            · have hs0102113 : InSquare (-49/320) (-109/320) (1/320) tau := by
                convert childUR hs010211 hx010211 hy010211 using 1 <;> norm_num
              exact Batch0173.cell1387.sound htau (by
                simp only [Batch0173.cell1387, Batch0173.tau1387, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0102113 (by positivity) using 1 <;> norm_num)
        · have hs010213 : InSquare (-5/32) (-53/160) (1/160) tau := by
            convert childUR hs01021 hx01021 hy01021 using 1 <;> norm_num
          rcases le_total tau.re (-5/32 : ℝ) with hx010213 | hx010213
          · rcases le_total tau.im (-53/160 : ℝ) with hy010213 | hy010213
            · have hs0102130 : InSquare (-51/320) (-107/320) (1/320) tau := by
                convert childLL hs010213 hx010213 hy010213 using 1 <;> norm_num
              exact Batch0174.cell1392.sound htau (by
                simp only [Batch0174.cell1392, Batch0174.tau1392, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0102130 (by positivity) using 1 <;> norm_num)
            · have hs0102132 : InSquare (-51/320) (-21/64) (1/320) tau := by
                convert childUL hs010213 hx010213 hy010213 using 1 <;> norm_num
              exact Batch0174.cell1394.sound htau (by
                simp only [Batch0174.cell1394, Batch0174.tau1394, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0102132 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-53/160 : ℝ) with hy010213 | hy010213
            · have hs0102131 : InSquare (-49/320) (-107/320) (1/320) tau := by
                convert childLR hs010213 hx010213 hy010213 using 1 <;> norm_num
              exact Batch0174.cell1393.sound htau (by
                simp only [Batch0174.cell1393, Batch0174.tau1393, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0102131 (by positivity) using 1 <;> norm_num)
            · have hs0102133 : InSquare (-49/320) (-21/64) (1/320) tau := by
                convert childUR hs010213 hx010213 hy010213 using 1 <;> norm_num
              exact Batch0174.cell1395.sound htau (by
                simp only [Batch0174.cell1395, Batch0174.tau1395, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0102133 (by positivity) using 1 <;> norm_num)
    · have hs01023 : InSquare (-13/80) (-5/16) (1/80) tau := by
        convert childUR hs hx0102 hy0102 using 1 <;> norm_num
      rcases le_total tau.re (-13/80 : ℝ) with hx01023 | hx01023
      · rcases le_total tau.im (-5/16 : ℝ) with hy01023 | hy01023
        · have hs010230 : InSquare (-27/160) (-51/160) (1/160) tau := by
            convert childLL hs01023 hx01023 hy01023 using 1 <;> norm_num
          rcases le_total tau.re (-27/160 : ℝ) with hx010230 | hx010230
          · rcases le_total tau.im (-51/160 : ℝ) with hy010230 | hy010230
            · have hs0102300 : InSquare (-11/64) (-103/320) (1/320) tau := by
                convert childLL hs010230 hx010230 hy010230 using 1 <;> norm_num
              exact Batch0176.cell1412.sound htau (by
                simp only [Batch0176.cell1412, Batch0176.tau1412, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0102300 (by positivity) using 1 <;> norm_num)
            · have hs0102302 : InSquare (-11/64) (-101/320) (1/320) tau := by
                convert childUL hs010230 hx010230 hy010230 using 1 <;> norm_num
              exact Batch0176.cell1414.sound htau (by
                simp only [Batch0176.cell1414, Batch0176.tau1414, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0102302 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-51/160 : ℝ) with hy010230 | hy010230
            · have hs0102301 : InSquare (-53/320) (-103/320) (1/320) tau := by
                convert childLR hs010230 hx010230 hy010230 using 1 <;> norm_num
              exact Batch0176.cell1413.sound htau (by
                simp only [Batch0176.cell1413, Batch0176.tau1413, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0102301 (by positivity) using 1 <;> norm_num)
            · have hs0102303 : InSquare (-53/320) (-101/320) (1/320) tau := by
                convert childUR hs010230 hx010230 hy010230 using 1 <;> norm_num
              exact Batch0176.cell1415.sound htau (by
                simp only [Batch0176.cell1415, Batch0176.tau1415, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0102303 (by positivity) using 1 <;> norm_num)
        · have hs010232 : InSquare (-27/160) (-49/160) (1/160) tau := by
            convert childUL hs01023 hx01023 hy01023 using 1 <;> norm_num
          exact Batch0049.cell0393.sound htau (by
            simp only [Batch0049.cell0393, Batch0049.tau0393, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs010232 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-5/16 : ℝ) with hy01023 | hy01023
        · have hs010231 : InSquare (-5/32) (-51/160) (1/160) tau := by
            convert childLR hs01023 hx01023 hy01023 using 1 <;> norm_num
          rcases le_total tau.re (-5/32 : ℝ) with hx010231 | hx010231
          · rcases le_total tau.im (-51/160 : ℝ) with hy010231 | hy010231
            · have hs0102310 : InSquare (-51/320) (-103/320) (1/320) tau := by
                convert childLL hs010231 hx010231 hy010231 using 1 <;> norm_num
              exact Batch0177.cell1416.sound htau (by
                simp only [Batch0177.cell1416, Batch0177.tau1416, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0102310 (by positivity) using 1 <;> norm_num)
            · have hs0102312 : InSquare (-51/320) (-101/320) (1/320) tau := by
                convert childUL hs010231 hx010231 hy010231 using 1 <;> norm_num
              exact Batch0177.cell1418.sound htau (by
                simp only [Batch0177.cell1418, Batch0177.tau1418, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0102312 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-51/160 : ℝ) with hy010231 | hy010231
            · have hs0102311 : InSquare (-49/320) (-103/320) (1/320) tau := by
                convert childLR hs010231 hx010231 hy010231 using 1 <;> norm_num
              exact Batch0177.cell1417.sound htau (by
                simp only [Batch0177.cell1417, Batch0177.tau1417, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0102311 (by positivity) using 1 <;> norm_num)
            · have hs0102313 : InSquare (-49/320) (-101/320) (1/320) tau := by
                convert childUR hs010231 hx010231 hy010231 using 1 <;> norm_num
              exact Batch0177.cell1419.sound htau (by
                simp only [Batch0177.cell1419, Batch0177.tau1419, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0102313 (by positivity) using 1 <;> norm_num)
        · have hs010233 : InSquare (-5/32) (-49/160) (1/160) tau := by
            convert childUR hs01023 hx01023 hy01023 using 1 <;> norm_num
          exact Batch0049.cell0394.sound htau (by
            simp only [Batch0049.cell0394, Batch0049.tau0394, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs010233 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0102
