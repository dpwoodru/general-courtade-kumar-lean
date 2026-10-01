import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0118
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0253
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0254
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0255
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0256
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0257
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0258
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0259
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0260
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0402
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0403

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2320

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-7/40) (13/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (-7/40 : ℝ) with hx2320 | hx2320
  · rcases le_total tau.im (13/40 : ℝ) with hy2320 | hy2320
    · have hs23200 : InSquare (-3/16) (5/16) (1/80) tau := by
        convert childLL hs hx2320 hy2320 using 1 <;> norm_num
      rcases le_total tau.re (-3/16 : ℝ) with hx23200 | hx23200
      · rcases le_total tau.im (5/16 : ℝ) with hy23200 | hy23200
        · have hs232000 : InSquare (-31/160) (49/160) (1/160) tau := by
            convert childLL hs23200 hx23200 hy23200 using 1 <;> norm_num
          rcases le_total tau.re (-31/160 : ℝ) with hx232000 | hx232000
          · rcases le_total tau.im (49/160 : ℝ) with hy232000 | hy232000
            · have hs2320000 : InSquare (-63/320) (97/320) (1/320) tau := by
                convert childLL hs232000 hx232000 hy232000 using 1 <;> norm_num
              exact Batch0253.cell2027.sound htau (by
                simp only [Batch0253.cell2027, Batch0253.tau2027, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2320000 (by positivity) using 1 <;> norm_num)
            · have hs2320002 : InSquare (-63/320) (99/320) (1/320) tau := by
                convert childUL hs232000 hx232000 hy232000 using 1 <;> norm_num
              exact Batch0253.cell2029.sound htau (by
                simp only [Batch0253.cell2029, Batch0253.tau2029, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2320002 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (49/160 : ℝ) with hy232000 | hy232000
            · have hs2320001 : InSquare (-61/320) (97/320) (1/320) tau := by
                convert childLR hs232000 hx232000 hy232000 using 1 <;> norm_num
              exact Batch0253.cell2028.sound htau (by
                simp only [Batch0253.cell2028, Batch0253.tau2028, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2320001 (by positivity) using 1 <;> norm_num)
            · have hs2320003 : InSquare (-61/320) (99/320) (1/320) tau := by
                convert childUR hs232000 hx232000 hy232000 using 1 <;> norm_num
              exact Batch0253.cell2030.sound htau (by
                simp only [Batch0253.cell2030, Batch0253.tau2030, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2320003 (by positivity) using 1 <;> norm_num)
        · have hs232002 : InSquare (-31/160) (51/160) (1/160) tau := by
            convert childUL hs23200 hx23200 hy23200 using 1 <;> norm_num
          rcases le_total tau.re (-31/160 : ℝ) with hx232002 | hx232002
          · rcases le_total tau.im (51/160 : ℝ) with hy232002 | hy232002
            · have hs2320020 : InSquare (-63/320) (101/320) (1/320) tau := by
                convert childLL hs232002 hx232002 hy232002 using 1 <;> norm_num
              exact Batch0254.cell2035.sound htau (by
                simp only [Batch0254.cell2035, Batch0254.tau2035, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2320020 (by positivity) using 1 <;> norm_num)
            · have hs2320022 : InSquare (-63/320) (103/320) (1/320) tau := by
                convert childUL hs232002 hx232002 hy232002 using 1 <;> norm_num
              exact Batch0254.cell2037.sound htau (by
                simp only [Batch0254.cell2037, Batch0254.tau2037, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2320022 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (51/160 : ℝ) with hy232002 | hy232002
            · have hs2320021 : InSquare (-61/320) (101/320) (1/320) tau := by
                convert childLR hs232002 hx232002 hy232002 using 1 <;> norm_num
              exact Batch0254.cell2036.sound htau (by
                simp only [Batch0254.cell2036, Batch0254.tau2036, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2320021 (by positivity) using 1 <;> norm_num)
            · have hs2320023 : InSquare (-61/320) (103/320) (1/320) tau := by
                convert childUR hs232002 hx232002 hy232002 using 1 <;> norm_num
              exact Batch0254.cell2038.sound htau (by
                simp only [Batch0254.cell2038, Batch0254.tau2038, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2320023 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (5/16 : ℝ) with hy23200 | hy23200
        · have hs232001 : InSquare (-29/160) (49/160) (1/160) tau := by
            convert childLR hs23200 hx23200 hy23200 using 1 <;> norm_num
          rcases le_total tau.re (-29/160 : ℝ) with hx232001 | hx232001
          · rcases le_total tau.im (49/160 : ℝ) with hy232001 | hy232001
            · have hs2320010 : InSquare (-59/320) (97/320) (1/320) tau := by
                convert childLL hs232001 hx232001 hy232001 using 1 <;> norm_num
              exact Batch0253.cell2031.sound htau (by
                simp only [Batch0253.cell2031, Batch0253.tau2031, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2320010 (by positivity) using 1 <;> norm_num)
            · have hs2320012 : InSquare (-59/320) (99/320) (1/320) tau := by
                convert childUL hs232001 hx232001 hy232001 using 1 <;> norm_num
              exact Batch0254.cell2033.sound htau (by
                simp only [Batch0254.cell2033, Batch0254.tau2033, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2320012 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (49/160 : ℝ) with hy232001 | hy232001
            · have hs2320011 : InSquare (-57/320) (97/320) (1/320) tau := by
                convert childLR hs232001 hx232001 hy232001 using 1 <;> norm_num
              exact Batch0254.cell2032.sound htau (by
                simp only [Batch0254.cell2032, Batch0254.tau2032, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2320011 (by positivity) using 1 <;> norm_num)
            · have hs2320013 : InSquare (-57/320) (99/320) (1/320) tau := by
                convert childUR hs232001 hx232001 hy232001 using 1 <;> norm_num
              exact Batch0254.cell2034.sound htau (by
                simp only [Batch0254.cell2034, Batch0254.tau2034, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2320013 (by positivity) using 1 <;> norm_num)
        · have hs232003 : InSquare (-29/160) (51/160) (1/160) tau := by
            convert childUR hs23200 hx23200 hy23200 using 1 <;> norm_num
          rcases le_total tau.re (-29/160 : ℝ) with hx232003 | hx232003
          · rcases le_total tau.im (51/160 : ℝ) with hy232003 | hy232003
            · have hs2320030 : InSquare (-59/320) (101/320) (1/320) tau := by
                convert childLL hs232003 hx232003 hy232003 using 1 <;> norm_num
              exact Batch0254.cell2039.sound htau (by
                simp only [Batch0254.cell2039, Batch0254.tau2039, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2320030 (by positivity) using 1 <;> norm_num)
            · have hs2320032 : InSquare (-59/320) (103/320) (1/320) tau := by
                convert childUL hs232003 hx232003 hy232003 using 1 <;> norm_num
              exact Batch0255.cell2041.sound htau (by
                simp only [Batch0255.cell2041, Batch0255.tau2041, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2320032 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (51/160 : ℝ) with hy232003 | hy232003
            · have hs2320031 : InSquare (-57/320) (101/320) (1/320) tau := by
                convert childLR hs232003 hx232003 hy232003 using 1 <;> norm_num
              exact Batch0255.cell2040.sound htau (by
                simp only [Batch0255.cell2040, Batch0255.tau2040, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2320031 (by positivity) using 1 <;> norm_num)
            · have hs2320033 : InSquare (-57/320) (103/320) (1/320) tau := by
                convert childUR hs232003 hx232003 hy232003 using 1 <;> norm_num
              exact Batch0255.cell2042.sound htau (by
                simp only [Batch0255.cell2042, Batch0255.tau2042, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2320033 (by positivity) using 1 <;> norm_num)
    · have hs23202 : InSquare (-3/16) (27/80) (1/80) tau := by
        convert childUL hs hx2320 hy2320 using 1 <;> norm_num
      rcases le_total tau.re (-3/16 : ℝ) with hx23202 | hx23202
      · rcases le_total tau.im (27/80 : ℝ) with hy23202 | hy23202
        · have hs232020 : InSquare (-31/160) (53/160) (1/160) tau := by
            convert childLL hs23202 hx23202 hy23202 using 1 <;> norm_num
          rcases le_total tau.re (-31/160 : ℝ) with hx232020 | hx232020
          · rcases le_total tau.im (53/160 : ℝ) with hy232020 | hy232020
            · have hs2320200 : InSquare (-63/320) (21/64) (1/320) tau := by
                convert childLL hs232020 hx232020 hy232020 using 1 <;> norm_num
              exact Batch0256.cell2051.sound htau (by
                simp only [Batch0256.cell2051, Batch0256.tau2051, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2320200 (by positivity) using 1 <;> norm_num)
            · have hs2320202 : InSquare (-63/320) (107/320) (1/320) tau := by
                convert childUL hs232020 hx232020 hy232020 using 1 <;> norm_num
              exact Batch0256.cell2053.sound htau (by
                simp only [Batch0256.cell2053, Batch0256.tau2053, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2320202 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (53/160 : ℝ) with hy232020 | hy232020
            · have hs2320201 : InSquare (-61/320) (21/64) (1/320) tau := by
                convert childLR hs232020 hx232020 hy232020 using 1 <;> norm_num
              exact Batch0256.cell2052.sound htau (by
                simp only [Batch0256.cell2052, Batch0256.tau2052, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2320201 (by positivity) using 1 <;> norm_num)
            · have hs2320203 : InSquare (-61/320) (107/320) (1/320) tau := by
                convert childUR hs232020 hx232020 hy232020 using 1 <;> norm_num
              exact Batch0256.cell2054.sound htau (by
                simp only [Batch0256.cell2054, Batch0256.tau2054, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2320203 (by positivity) using 1 <;> norm_num)
        · have hs232022 : InSquare (-31/160) (11/32) (1/160) tau := by
            convert childUL hs23202 hx23202 hy23202 using 1 <;> norm_num
          rcases le_total tau.re (-31/160 : ℝ) with hx232022 | hx232022
          · rcases le_total tau.im (11/32 : ℝ) with hy232022 | hy232022
            · have hs2320220 : InSquare (-63/320) (109/320) (1/320) tau := by
                convert childLL hs232022 hx232022 hy232022 using 1 <;> norm_num
              exact Batch0257.cell2059.sound htau (by
                simp only [Batch0257.cell2059, Batch0257.tau2059, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2320220 (by positivity) using 1 <;> norm_num)
            · have hs2320222 : InSquare (-63/320) (111/320) (1/320) tau := by
                convert childUL hs232022 hx232022 hy232022 using 1 <;> norm_num
              rcases le_total tau.re (-63/320 : ℝ) with hx2320222 | hx2320222
              · rcases le_total tau.im (111/320 : ℝ) with hy2320222 | hy2320222
                · have hs23202220 : InSquare (-127/640) (221/640) (1/640) tau := by
                    convert childLL hs2320222 hx2320222 hy2320222 using 1 <;> norm_num
                  exact Batch0402.cell3219.sound htau (by
                    simp only [Batch0402.cell3219, Batch0402.tau3219, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23202220 (by positivity) using 1 <;> norm_num)
                · have hs23202222 : InSquare (-127/640) (223/640) (1/640) tau := by
                    convert childUL hs2320222 hx2320222 hy2320222 using 1 <;> norm_num
                  exact Batch0402.cell3221.sound htau (by
                    simp only [Batch0402.cell3221, Batch0402.tau3221, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23202222 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (111/320 : ℝ) with hy2320222 | hy2320222
                · have hs23202221 : InSquare (-25/128) (221/640) (1/640) tau := by
                    convert childLR hs2320222 hx2320222 hy2320222 using 1 <;> norm_num
                  exact Batch0402.cell3220.sound htau (by
                    simp only [Batch0402.cell3220, Batch0402.tau3220, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23202221 (by positivity) using 1 <;> norm_num)
                · have hs23202223 : InSquare (-25/128) (223/640) (1/640) tau := by
                    convert childUR hs2320222 hx2320222 hy2320222 using 1 <;> norm_num
                  exact Batch0402.cell3222.sound htau (by
                    simp only [Batch0402.cell3222, Batch0402.tau3222, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23202223 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (11/32 : ℝ) with hy232022 | hy232022
            · have hs2320221 : InSquare (-61/320) (109/320) (1/320) tau := by
                convert childLR hs232022 hx232022 hy232022 using 1 <;> norm_num
              exact Batch0257.cell2060.sound htau (by
                simp only [Batch0257.cell2060, Batch0257.tau2060, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2320221 (by positivity) using 1 <;> norm_num)
            · have hs2320223 : InSquare (-61/320) (111/320) (1/320) tau := by
                convert childUR hs232022 hx232022 hy232022 using 1 <;> norm_num
              rcases le_total tau.re (-61/320 : ℝ) with hx2320223 | hx2320223
              · rcases le_total tau.im (111/320 : ℝ) with hy2320223 | hy2320223
                · have hs23202230 : InSquare (-123/640) (221/640) (1/640) tau := by
                    convert childLL hs2320223 hx2320223 hy2320223 using 1 <;> norm_num
                  exact Batch0402.cell3223.sound htau (by
                    simp only [Batch0402.cell3223, Batch0402.tau3223, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23202230 (by positivity) using 1 <;> norm_num)
                · have hs23202232 : InSquare (-123/640) (223/640) (1/640) tau := by
                    convert childUL hs2320223 hx2320223 hy2320223 using 1 <;> norm_num
                  exact Batch0403.cell3225.sound htau (by
                    simp only [Batch0403.cell3225, Batch0403.tau3225, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23202232 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (111/320 : ℝ) with hy2320223 | hy2320223
                · have hs23202231 : InSquare (-121/640) (221/640) (1/640) tau := by
                    convert childLR hs2320223 hx2320223 hy2320223 using 1 <;> norm_num
                  exact Batch0403.cell3224.sound htau (by
                    simp only [Batch0403.cell3224, Batch0403.tau3224, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23202231 (by positivity) using 1 <;> norm_num)
                · have hs23202233 : InSquare (-121/640) (223/640) (1/640) tau := by
                    convert childUR hs2320223 hx2320223 hy2320223 using 1 <;> norm_num
                  exact Batch0403.cell3226.sound htau (by
                    simp only [Batch0403.cell3226, Batch0403.tau3226, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23202233 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (27/80 : ℝ) with hy23202 | hy23202
        · have hs232021 : InSquare (-29/160) (53/160) (1/160) tau := by
            convert childLR hs23202 hx23202 hy23202 using 1 <;> norm_num
          rcases le_total tau.re (-29/160 : ℝ) with hx232021 | hx232021
          · rcases le_total tau.im (53/160 : ℝ) with hy232021 | hy232021
            · have hs2320210 : InSquare (-59/320) (21/64) (1/320) tau := by
                convert childLL hs232021 hx232021 hy232021 using 1 <;> norm_num
              exact Batch0256.cell2055.sound htau (by
                simp only [Batch0256.cell2055, Batch0256.tau2055, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2320210 (by positivity) using 1 <;> norm_num)
            · have hs2320212 : InSquare (-59/320) (107/320) (1/320) tau := by
                convert childUL hs232021 hx232021 hy232021 using 1 <;> norm_num
              exact Batch0257.cell2057.sound htau (by
                simp only [Batch0257.cell2057, Batch0257.tau2057, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2320212 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (53/160 : ℝ) with hy232021 | hy232021
            · have hs2320211 : InSquare (-57/320) (21/64) (1/320) tau := by
                convert childLR hs232021 hx232021 hy232021 using 1 <;> norm_num
              exact Batch0257.cell2056.sound htau (by
                simp only [Batch0257.cell2056, Batch0257.tau2056, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2320211 (by positivity) using 1 <;> norm_num)
            · have hs2320213 : InSquare (-57/320) (107/320) (1/320) tau := by
                convert childUR hs232021 hx232021 hy232021 using 1 <;> norm_num
              exact Batch0257.cell2058.sound htau (by
                simp only [Batch0257.cell2058, Batch0257.tau2058, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2320213 (by positivity) using 1 <;> norm_num)
        · have hs232023 : InSquare (-29/160) (11/32) (1/160) tau := by
            convert childUR hs23202 hx23202 hy23202 using 1 <;> norm_num
          rcases le_total tau.re (-29/160 : ℝ) with hx232023 | hx232023
          · rcases le_total tau.im (11/32 : ℝ) with hy232023 | hy232023
            · have hs2320230 : InSquare (-59/320) (109/320) (1/320) tau := by
                convert childLL hs232023 hx232023 hy232023 using 1 <;> norm_num
              exact Batch0257.cell2061.sound htau (by
                simp only [Batch0257.cell2061, Batch0257.tau2061, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2320230 (by positivity) using 1 <;> norm_num)
            · have hs2320232 : InSquare (-59/320) (111/320) (1/320) tau := by
                convert childUL hs232023 hx232023 hy232023 using 1 <;> norm_num
              exact Batch0257.cell2063.sound htau (by
                simp only [Batch0257.cell2063, Batch0257.tau2063, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2320232 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (11/32 : ℝ) with hy232023 | hy232023
            · have hs2320231 : InSquare (-57/320) (109/320) (1/320) tau := by
                convert childLR hs232023 hx232023 hy232023 using 1 <;> norm_num
              exact Batch0257.cell2062.sound htau (by
                simp only [Batch0257.cell2062, Batch0257.tau2062, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2320231 (by positivity) using 1 <;> norm_num)
            · have hs2320233 : InSquare (-57/320) (111/320) (1/320) tau := by
                convert childUR hs232023 hx232023 hy232023 using 1 <;> norm_num
              exact Batch0258.cell2064.sound htau (by
                simp only [Batch0258.cell2064, Batch0258.tau2064, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2320233 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (13/40 : ℝ) with hy2320 | hy2320
    · have hs23201 : InSquare (-13/80) (5/16) (1/80) tau := by
        convert childLR hs hx2320 hy2320 using 1 <;> norm_num
      rcases le_total tau.re (-13/80 : ℝ) with hx23201 | hx23201
      · rcases le_total tau.im (5/16 : ℝ) with hy23201 | hy23201
        · have hs232010 : InSquare (-27/160) (49/160) (1/160) tau := by
            convert childLL hs23201 hx23201 hy23201 using 1 <;> norm_num
          exact Batch0118.cell0946.sound htau (by
            simp only [Batch0118.cell0946, Batch0118.tau0946, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs232010 (by positivity) using 1 <;> norm_num)
        · have hs232012 : InSquare (-27/160) (51/160) (1/160) tau := by
            convert childUL hs23201 hx23201 hy23201 using 1 <;> norm_num
          rcases le_total tau.re (-27/160 : ℝ) with hx232012 | hx232012
          · rcases le_total tau.im (51/160 : ℝ) with hy232012 | hy232012
            · have hs2320120 : InSquare (-11/64) (101/320) (1/320) tau := by
                convert childLL hs232012 hx232012 hy232012 using 1 <;> norm_num
              exact Batch0255.cell2043.sound htau (by
                simp only [Batch0255.cell2043, Batch0255.tau2043, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2320120 (by positivity) using 1 <;> norm_num)
            · have hs2320122 : InSquare (-11/64) (103/320) (1/320) tau := by
                convert childUL hs232012 hx232012 hy232012 using 1 <;> norm_num
              exact Batch0255.cell2045.sound htau (by
                simp only [Batch0255.cell2045, Batch0255.tau2045, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2320122 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (51/160 : ℝ) with hy232012 | hy232012
            · have hs2320121 : InSquare (-53/320) (101/320) (1/320) tau := by
                convert childLR hs232012 hx232012 hy232012 using 1 <;> norm_num
              exact Batch0255.cell2044.sound htau (by
                simp only [Batch0255.cell2044, Batch0255.tau2044, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2320121 (by positivity) using 1 <;> norm_num)
            · have hs2320123 : InSquare (-53/320) (103/320) (1/320) tau := by
                convert childUR hs232012 hx232012 hy232012 using 1 <;> norm_num
              exact Batch0255.cell2046.sound htau (by
                simp only [Batch0255.cell2046, Batch0255.tau2046, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2320123 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (5/16 : ℝ) with hy23201 | hy23201
        · have hs232011 : InSquare (-5/32) (49/160) (1/160) tau := by
            convert childLR hs23201 hx23201 hy23201 using 1 <;> norm_num
          exact Batch0118.cell0947.sound htau (by
            simp only [Batch0118.cell0947, Batch0118.tau0947, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs232011 (by positivity) using 1 <;> norm_num)
        · have hs232013 : InSquare (-5/32) (51/160) (1/160) tau := by
            convert childUR hs23201 hx23201 hy23201 using 1 <;> norm_num
          rcases le_total tau.re (-5/32 : ℝ) with hx232013 | hx232013
          · rcases le_total tau.im (51/160 : ℝ) with hy232013 | hy232013
            · have hs2320130 : InSquare (-51/320) (101/320) (1/320) tau := by
                convert childLL hs232013 hx232013 hy232013 using 1 <;> norm_num
              exact Batch0255.cell2047.sound htau (by
                simp only [Batch0255.cell2047, Batch0255.tau2047, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2320130 (by positivity) using 1 <;> norm_num)
            · have hs2320132 : InSquare (-51/320) (103/320) (1/320) tau := by
                convert childUL hs232013 hx232013 hy232013 using 1 <;> norm_num
              exact Batch0256.cell2049.sound htau (by
                simp only [Batch0256.cell2049, Batch0256.tau2049, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2320132 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (51/160 : ℝ) with hy232013 | hy232013
            · have hs2320131 : InSquare (-49/320) (101/320) (1/320) tau := by
                convert childLR hs232013 hx232013 hy232013 using 1 <;> norm_num
              exact Batch0256.cell2048.sound htau (by
                simp only [Batch0256.cell2048, Batch0256.tau2048, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2320131 (by positivity) using 1 <;> norm_num)
            · have hs2320133 : InSquare (-49/320) (103/320) (1/320) tau := by
                convert childUR hs232013 hx232013 hy232013 using 1 <;> norm_num
              exact Batch0256.cell2050.sound htau (by
                simp only [Batch0256.cell2050, Batch0256.tau2050, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2320133 (by positivity) using 1 <;> norm_num)
    · have hs23203 : InSquare (-13/80) (27/80) (1/80) tau := by
        convert childUR hs hx2320 hy2320 using 1 <;> norm_num
      rcases le_total tau.re (-13/80 : ℝ) with hx23203 | hx23203
      · rcases le_total tau.im (27/80 : ℝ) with hy23203 | hy23203
        · have hs232030 : InSquare (-27/160) (53/160) (1/160) tau := by
            convert childLL hs23203 hx23203 hy23203 using 1 <;> norm_num
          rcases le_total tau.re (-27/160 : ℝ) with hx232030 | hx232030
          · rcases le_total tau.im (53/160 : ℝ) with hy232030 | hy232030
            · have hs2320300 : InSquare (-11/64) (21/64) (1/320) tau := by
                convert childLL hs232030 hx232030 hy232030 using 1 <;> norm_num
              exact Batch0258.cell2065.sound htau (by
                simp only [Batch0258.cell2065, Batch0258.tau2065, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2320300 (by positivity) using 1 <;> norm_num)
            · have hs2320302 : InSquare (-11/64) (107/320) (1/320) tau := by
                convert childUL hs232030 hx232030 hy232030 using 1 <;> norm_num
              exact Batch0258.cell2067.sound htau (by
                simp only [Batch0258.cell2067, Batch0258.tau2067, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2320302 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (53/160 : ℝ) with hy232030 | hy232030
            · have hs2320301 : InSquare (-53/320) (21/64) (1/320) tau := by
                convert childLR hs232030 hx232030 hy232030 using 1 <;> norm_num
              exact Batch0258.cell2066.sound htau (by
                simp only [Batch0258.cell2066, Batch0258.tau2066, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2320301 (by positivity) using 1 <;> norm_num)
            · have hs2320303 : InSquare (-53/320) (107/320) (1/320) tau := by
                convert childUR hs232030 hx232030 hy232030 using 1 <;> norm_num
              exact Batch0258.cell2068.sound htau (by
                simp only [Batch0258.cell2068, Batch0258.tau2068, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2320303 (by positivity) using 1 <;> norm_num)
        · have hs232032 : InSquare (-27/160) (11/32) (1/160) tau := by
            convert childUL hs23203 hx23203 hy23203 using 1 <;> norm_num
          rcases le_total tau.re (-27/160 : ℝ) with hx232032 | hx232032
          · rcases le_total tau.im (11/32 : ℝ) with hy232032 | hy232032
            · have hs2320320 : InSquare (-11/64) (109/320) (1/320) tau := by
                convert childLL hs232032 hx232032 hy232032 using 1 <;> norm_num
              exact Batch0259.cell2073.sound htau (by
                simp only [Batch0259.cell2073, Batch0259.tau2073, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2320320 (by positivity) using 1 <;> norm_num)
            · have hs2320322 : InSquare (-11/64) (111/320) (1/320) tau := by
                convert childUL hs232032 hx232032 hy232032 using 1 <;> norm_num
              exact Batch0259.cell2075.sound htau (by
                simp only [Batch0259.cell2075, Batch0259.tau2075, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2320322 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (11/32 : ℝ) with hy232032 | hy232032
            · have hs2320321 : InSquare (-53/320) (109/320) (1/320) tau := by
                convert childLR hs232032 hx232032 hy232032 using 1 <;> norm_num
              exact Batch0259.cell2074.sound htau (by
                simp only [Batch0259.cell2074, Batch0259.tau2074, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2320321 (by positivity) using 1 <;> norm_num)
            · have hs2320323 : InSquare (-53/320) (111/320) (1/320) tau := by
                convert childUR hs232032 hx232032 hy232032 using 1 <;> norm_num
              exact Batch0259.cell2076.sound htau (by
                simp only [Batch0259.cell2076, Batch0259.tau2076, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2320323 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (27/80 : ℝ) with hy23203 | hy23203
        · have hs232031 : InSquare (-5/32) (53/160) (1/160) tau := by
            convert childLR hs23203 hx23203 hy23203 using 1 <;> norm_num
          rcases le_total tau.re (-5/32 : ℝ) with hx232031 | hx232031
          · rcases le_total tau.im (53/160 : ℝ) with hy232031 | hy232031
            · have hs2320310 : InSquare (-51/320) (21/64) (1/320) tau := by
                convert childLL hs232031 hx232031 hy232031 using 1 <;> norm_num
              exact Batch0258.cell2069.sound htau (by
                simp only [Batch0258.cell2069, Batch0258.tau2069, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2320310 (by positivity) using 1 <;> norm_num)
            · have hs2320312 : InSquare (-51/320) (107/320) (1/320) tau := by
                convert childUL hs232031 hx232031 hy232031 using 1 <;> norm_num
              exact Batch0258.cell2071.sound htau (by
                simp only [Batch0258.cell2071, Batch0258.tau2071, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2320312 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (53/160 : ℝ) with hy232031 | hy232031
            · have hs2320311 : InSquare (-49/320) (21/64) (1/320) tau := by
                convert childLR hs232031 hx232031 hy232031 using 1 <;> norm_num
              exact Batch0258.cell2070.sound htau (by
                simp only [Batch0258.cell2070, Batch0258.tau2070, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2320311 (by positivity) using 1 <;> norm_num)
            · have hs2320313 : InSquare (-49/320) (107/320) (1/320) tau := by
                convert childUR hs232031 hx232031 hy232031 using 1 <;> norm_num
              exact Batch0259.cell2072.sound htau (by
                simp only [Batch0259.cell2072, Batch0259.tau2072, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2320313 (by positivity) using 1 <;> norm_num)
        · have hs232033 : InSquare (-5/32) (11/32) (1/160) tau := by
            convert childUR hs23203 hx23203 hy23203 using 1 <;> norm_num
          rcases le_total tau.re (-5/32 : ℝ) with hx232033 | hx232033
          · rcases le_total tau.im (11/32 : ℝ) with hy232033 | hy232033
            · have hs2320330 : InSquare (-51/320) (109/320) (1/320) tau := by
                convert childLL hs232033 hx232033 hy232033 using 1 <;> norm_num
              exact Batch0259.cell2077.sound htau (by
                simp only [Batch0259.cell2077, Batch0259.tau2077, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2320330 (by positivity) using 1 <;> norm_num)
            · have hs2320332 : InSquare (-51/320) (111/320) (1/320) tau := by
                convert childUL hs232033 hx232033 hy232033 using 1 <;> norm_num
              exact Batch0259.cell2079.sound htau (by
                simp only [Batch0259.cell2079, Batch0259.tau2079, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2320332 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (11/32 : ℝ) with hy232033 | hy232033
            · have hs2320331 : InSquare (-49/320) (109/320) (1/320) tau := by
                convert childLR hs232033 hx232033 hy232033 using 1 <;> norm_num
              exact Batch0259.cell2078.sound htau (by
                simp only [Batch0259.cell2078, Batch0259.tau2078, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2320331 (by positivity) using 1 <;> norm_num)
            · have hs2320333 : InSquare (-49/320) (111/320) (1/320) tau := by
                convert childUR hs232033 hx232033 hy232033 using 1 <;> norm_num
              exact Batch0260.cell2080.sound htau (by
                simp only [Batch0260.cell2080, Batch0260.tau2080, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2320333 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2320
