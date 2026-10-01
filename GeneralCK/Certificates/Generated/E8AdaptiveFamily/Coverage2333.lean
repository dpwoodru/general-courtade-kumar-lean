import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0123
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0272
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0273
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0274
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0275
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0276
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0277
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0431
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0432
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0433
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0434
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0435
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0436
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0437
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0438
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0439
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0440

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2333

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-1/40) (3/8) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (-1/40 : ℝ) with hx2333 | hx2333
  · rcases le_total tau.im (3/8 : ℝ) with hy2333 | hy2333
    · have hs23330 : InSquare (-3/80) (29/80) (1/80) tau := by
        convert childLL hs hx2333 hy2333 using 1 <;> norm_num
      rcases le_total tau.re (-3/80 : ℝ) with hx23330 | hx23330
      · rcases le_total tau.im (29/80 : ℝ) with hy23330 | hy23330
        · have hs233300 : InSquare (-7/160) (57/160) (1/160) tau := by
            convert childLL hs23330 hx23330 hy23330 using 1 <;> norm_num
          rcases le_total tau.re (-7/160 : ℝ) with hx233300 | hx233300
          · rcases le_total tau.im (57/160 : ℝ) with hy233300 | hy233300
            · have hs2333000 : InSquare (-3/64) (113/320) (1/320) tau := by
                convert childLL hs233300 hx233300 hy233300 using 1 <;> norm_num
              exact Batch0272.cell2182.sound htau (by
                simp only [Batch0272.cell2182, Batch0272.tau2182, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2333000 (by positivity) using 1 <;> norm_num)
            · have hs2333002 : InSquare (-3/64) (23/64) (1/320) tau := by
                convert childUL hs233300 hx233300 hy233300 using 1 <;> norm_num
              exact Batch0273.cell2184.sound htau (by
                simp only [Batch0273.cell2184, Batch0273.tau2184, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2333002 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (57/160 : ℝ) with hy233300 | hy233300
            · have hs2333001 : InSquare (-13/320) (113/320) (1/320) tau := by
                convert childLR hs233300 hx233300 hy233300 using 1 <;> norm_num
              exact Batch0272.cell2183.sound htau (by
                simp only [Batch0272.cell2183, Batch0272.tau2183, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2333001 (by positivity) using 1 <;> norm_num)
            · have hs2333003 : InSquare (-13/320) (23/64) (1/320) tau := by
                convert childUR hs233300 hx233300 hy233300 using 1 <;> norm_num
              exact Batch0273.cell2185.sound htau (by
                simp only [Batch0273.cell2185, Batch0273.tau2185, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2333003 (by positivity) using 1 <;> norm_num)
        · have hs233302 : InSquare (-7/160) (59/160) (1/160) tau := by
            convert childUL hs23330 hx23330 hy23330 using 1 <;> norm_num
          rcases le_total tau.re (-7/160 : ℝ) with hx233302 | hx233302
          · rcases le_total tau.im (59/160 : ℝ) with hy233302 | hy233302
            · have hs2333020 : InSquare (-3/64) (117/320) (1/320) tau := by
                convert childLL hs233302 hx233302 hy233302 using 1 <;> norm_num
              exact Batch0273.cell2190.sound htau (by
                simp only [Batch0273.cell2190, Batch0273.tau2190, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2333020 (by positivity) using 1 <;> norm_num)
            · have hs2333022 : InSquare (-3/64) (119/320) (1/320) tau := by
                convert childUL hs233302 hx233302 hy233302 using 1 <;> norm_num
              exact Batch0274.cell2192.sound htau (by
                simp only [Batch0274.cell2192, Batch0274.tau2192, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2333022 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (59/160 : ℝ) with hy233302 | hy233302
            · have hs2333021 : InSquare (-13/320) (117/320) (1/320) tau := by
                convert childLR hs233302 hx233302 hy233302 using 1 <;> norm_num
              exact Batch0273.cell2191.sound htau (by
                simp only [Batch0273.cell2191, Batch0273.tau2191, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2333021 (by positivity) using 1 <;> norm_num)
            · have hs2333023 : InSquare (-13/320) (119/320) (1/320) tau := by
                convert childUR hs233302 hx233302 hy233302 using 1 <;> norm_num
              exact Batch0274.cell2193.sound htau (by
                simp only [Batch0274.cell2193, Batch0274.tau2193, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2333023 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (29/80 : ℝ) with hy23330 | hy23330
        · have hs233301 : InSquare (-1/32) (57/160) (1/160) tau := by
            convert childLR hs23330 hx23330 hy23330 using 1 <;> norm_num
          rcases le_total tau.re (-1/32 : ℝ) with hx233301 | hx233301
          · rcases le_total tau.im (57/160 : ℝ) with hy233301 | hy233301
            · have hs2333010 : InSquare (-11/320) (113/320) (1/320) tau := by
                convert childLL hs233301 hx233301 hy233301 using 1 <;> norm_num
              exact Batch0273.cell2186.sound htau (by
                simp only [Batch0273.cell2186, Batch0273.tau2186, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2333010 (by positivity) using 1 <;> norm_num)
            · have hs2333012 : InSquare (-11/320) (23/64) (1/320) tau := by
                convert childUL hs233301 hx233301 hy233301 using 1 <;> norm_num
              exact Batch0273.cell2188.sound htau (by
                simp only [Batch0273.cell2188, Batch0273.tau2188, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2333012 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (57/160 : ℝ) with hy233301 | hy233301
            · have hs2333011 : InSquare (-9/320) (113/320) (1/320) tau := by
                convert childLR hs233301 hx233301 hy233301 using 1 <;> norm_num
              exact Batch0273.cell2187.sound htau (by
                simp only [Batch0273.cell2187, Batch0273.tau2187, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2333011 (by positivity) using 1 <;> norm_num)
            · have hs2333013 : InSquare (-9/320) (23/64) (1/320) tau := by
                convert childUR hs233301 hx233301 hy233301 using 1 <;> norm_num
              exact Batch0273.cell2189.sound htau (by
                simp only [Batch0273.cell2189, Batch0273.tau2189, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2333013 (by positivity) using 1 <;> norm_num)
        · have hs233303 : InSquare (-1/32) (59/160) (1/160) tau := by
            convert childUR hs23330 hx23330 hy23330 using 1 <;> norm_num
          rcases le_total tau.re (-1/32 : ℝ) with hx233303 | hx233303
          · rcases le_total tau.im (59/160 : ℝ) with hy233303 | hy233303
            · have hs2333030 : InSquare (-11/320) (117/320) (1/320) tau := by
                convert childLL hs233303 hx233303 hy233303 using 1 <;> norm_num
              exact Batch0274.cell2194.sound htau (by
                simp only [Batch0274.cell2194, Batch0274.tau2194, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2333030 (by positivity) using 1 <;> norm_num)
            · have hs2333032 : InSquare (-11/320) (119/320) (1/320) tau := by
                convert childUL hs233303 hx233303 hy233303 using 1 <;> norm_num
              exact Batch0274.cell2196.sound htau (by
                simp only [Batch0274.cell2196, Batch0274.tau2196, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2333032 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (59/160 : ℝ) with hy233303 | hy233303
            · have hs2333031 : InSquare (-9/320) (117/320) (1/320) tau := by
                convert childLR hs233303 hx233303 hy233303 using 1 <;> norm_num
              exact Batch0274.cell2195.sound htau (by
                simp only [Batch0274.cell2195, Batch0274.tau2195, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2333031 (by positivity) using 1 <;> norm_num)
            · have hs2333033 : InSquare (-9/320) (119/320) (1/320) tau := by
                convert childUR hs233303 hx233303 hy233303 using 1 <;> norm_num
              exact Batch0274.cell2197.sound htau (by
                simp only [Batch0274.cell2197, Batch0274.tau2197, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2333033 (by positivity) using 1 <;> norm_num)
    · have hs23332 : InSquare (-3/80) (31/80) (1/80) tau := by
        convert childUL hs hx2333 hy2333 using 1 <;> norm_num
      rcases le_total tau.re (-3/80 : ℝ) with hx23332 | hx23332
      · rcases le_total tau.im (31/80 : ℝ) with hy23332 | hy23332
        · have hs233320 : InSquare (-7/160) (61/160) (1/160) tau := by
            convert childLL hs23332 hx23332 hy23332 using 1 <;> norm_num
          rcases le_total tau.re (-7/160 : ℝ) with hx233320 | hx233320
          · rcases le_total tau.im (61/160 : ℝ) with hy233320 | hy233320
            · have hs2333200 : InSquare (-3/64) (121/320) (1/320) tau := by
                convert childLL hs233320 hx233320 hy233320 using 1 <;> norm_num
              exact Batch0276.cell2210.sound htau (by
                simp only [Batch0276.cell2210, Batch0276.tau2210, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2333200 (by positivity) using 1 <;> norm_num)
            · have hs2333202 : InSquare (-3/64) (123/320) (1/320) tau := by
                convert childUL hs233320 hx233320 hy233320 using 1 <;> norm_num
              rcases le_total tau.re (-3/64 : ℝ) with hx2333202 | hx2333202
              · rcases le_total tau.im (123/320 : ℝ) with hy2333202 | hy2333202
                · have hs23332020 : InSquare (-31/640) (49/128) (1/640) tau := by
                    convert childLL hs2333202 hx2333202 hy2333202 using 1 <;> norm_num
                  exact Batch0431.cell3448.sound htau (by
                    simp only [Batch0431.cell3448, Batch0431.tau3448, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23332020 (by positivity) using 1 <;> norm_num)
                · have hs23332022 : InSquare (-31/640) (247/640) (1/640) tau := by
                    convert childUL hs2333202 hx2333202 hy2333202 using 1 <;> norm_num
                  exact Batch0431.cell3450.sound htau (by
                    simp only [Batch0431.cell3450, Batch0431.tau3450, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23332022 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (123/320 : ℝ) with hy2333202 | hy2333202
                · have hs23332021 : InSquare (-29/640) (49/128) (1/640) tau := by
                    convert childLR hs2333202 hx2333202 hy2333202 using 1 <;> norm_num
                  exact Batch0431.cell3449.sound htau (by
                    simp only [Batch0431.cell3449, Batch0431.tau3449, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23332021 (by positivity) using 1 <;> norm_num)
                · have hs23332023 : InSquare (-29/640) (247/640) (1/640) tau := by
                    convert childUR hs2333202 hx2333202 hy2333202 using 1 <;> norm_num
                  exact Batch0431.cell3451.sound htau (by
                    simp only [Batch0431.cell3451, Batch0431.tau3451, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23332023 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (61/160 : ℝ) with hy233320 | hy233320
            · have hs2333201 : InSquare (-13/320) (121/320) (1/320) tau := by
                convert childLR hs233320 hx233320 hy233320 using 1 <;> norm_num
              exact Batch0276.cell2211.sound htau (by
                simp only [Batch0276.cell2211, Batch0276.tau2211, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2333201 (by positivity) using 1 <;> norm_num)
            · have hs2333203 : InSquare (-13/320) (123/320) (1/320) tau := by
                convert childUR hs233320 hx233320 hy233320 using 1 <;> norm_num
              rcases le_total tau.re (-13/320 : ℝ) with hx2333203 | hx2333203
              · rcases le_total tau.im (123/320 : ℝ) with hy2333203 | hy2333203
                · have hs23332030 : InSquare (-27/640) (49/128) (1/640) tau := by
                    convert childLL hs2333203 hx2333203 hy2333203 using 1 <;> norm_num
                  exact Batch0431.cell3452.sound htau (by
                    simp only [Batch0431.cell3452, Batch0431.tau3452, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23332030 (by positivity) using 1 <;> norm_num)
                · have hs23332032 : InSquare (-27/640) (247/640) (1/640) tau := by
                    convert childUL hs2333203 hx2333203 hy2333203 using 1 <;> norm_num
                  exact Batch0431.cell3454.sound htau (by
                    simp only [Batch0431.cell3454, Batch0431.tau3454, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23332032 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (123/320 : ℝ) with hy2333203 | hy2333203
                · have hs23332031 : InSquare (-5/128) (49/128) (1/640) tau := by
                    convert childLR hs2333203 hx2333203 hy2333203 using 1 <;> norm_num
                  exact Batch0431.cell3453.sound htau (by
                    simp only [Batch0431.cell3453, Batch0431.tau3453, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23332031 (by positivity) using 1 <;> norm_num)
                · have hs23332033 : InSquare (-5/128) (247/640) (1/640) tau := by
                    convert childUR hs2333203 hx2333203 hy2333203 using 1 <;> norm_num
                  exact Batch0431.cell3455.sound htau (by
                    simp only [Batch0431.cell3455, Batch0431.tau3455, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23332033 (by positivity) using 1 <;> norm_num)
        · have hs233322 : InSquare (-7/160) (63/160) (1/160) tau := by
            convert childUL hs23332 hx23332 hy23332 using 1 <;> norm_num
          rcases le_total tau.re (-7/160 : ℝ) with hx233322 | hx233322
          · rcases le_total tau.im (63/160 : ℝ) with hy233322 | hy233322
            · have hs2333220 : InSquare (-3/64) (25/64) (1/320) tau := by
                convert childLL hs233322 hx233322 hy233322 using 1 <;> norm_num
              rcases le_total tau.re (-3/64 : ℝ) with hx2333220 | hx2333220
              · rcases le_total tau.im (25/64 : ℝ) with hy2333220 | hy2333220
                · have hs23332200 : InSquare (-31/640) (249/640) (1/640) tau := by
                    convert childLL hs2333220 hx2333220 hy2333220 using 1 <;> norm_num
                  exact Batch0432.cell3460.sound htau (by
                    simp only [Batch0432.cell3460, Batch0432.tau3460, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23332200 (by positivity) using 1 <;> norm_num)
                · have hs23332202 : InSquare (-31/640) (251/640) (1/640) tau := by
                    convert childUL hs2333220 hx2333220 hy2333220 using 1 <;> norm_num
                  exact Batch0432.cell3462.sound htau (by
                    simp only [Batch0432.cell3462, Batch0432.tau3462, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23332202 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (25/64 : ℝ) with hy2333220 | hy2333220
                · have hs23332201 : InSquare (-29/640) (249/640) (1/640) tau := by
                    convert childLR hs2333220 hx2333220 hy2333220 using 1 <;> norm_num
                  exact Batch0432.cell3461.sound htau (by
                    simp only [Batch0432.cell3461, Batch0432.tau3461, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23332201 (by positivity) using 1 <;> norm_num)
                · have hs23332203 : InSquare (-29/640) (251/640) (1/640) tau := by
                    convert childUR hs2333220 hx2333220 hy2333220 using 1 <;> norm_num
                  exact Batch0432.cell3463.sound htau (by
                    simp only [Batch0432.cell3463, Batch0432.tau3463, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23332203 (by positivity) using 1 <;> norm_num)
            · have hs2333222 : InSquare (-3/64) (127/320) (1/320) tau := by
                convert childUL hs233322 hx233322 hy233322 using 1 <;> norm_num
              rcases le_total tau.re (-3/64 : ℝ) with hx2333222 | hx2333222
              · rcases le_total tau.im (127/320 : ℝ) with hy2333222 | hy2333222
                · have hs23332220 : InSquare (-31/640) (253/640) (1/640) tau := by
                    convert childLL hs2333222 hx2333222 hy2333222 using 1 <;> norm_num
                  exact Batch0433.cell3468.sound htau (by
                    simp only [Batch0433.cell3468, Batch0433.tau3468, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23332220 (by positivity) using 1 <;> norm_num)
                · have hs23332222 : InSquare (-31/640) (51/128) (1/640) tau := by
                    convert childUL hs2333222 hx2333222 hy2333222 using 1 <;> norm_num
                  exact Batch0433.cell3470.sound htau (by
                    simp only [Batch0433.cell3470, Batch0433.tau3470, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23332222 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (127/320 : ℝ) with hy2333222 | hy2333222
                · have hs23332221 : InSquare (-29/640) (253/640) (1/640) tau := by
                    convert childLR hs2333222 hx2333222 hy2333222 using 1 <;> norm_num
                  exact Batch0433.cell3469.sound htau (by
                    simp only [Batch0433.cell3469, Batch0433.tau3469, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23332221 (by positivity) using 1 <;> norm_num)
                · have hs23332223 : InSquare (-29/640) (51/128) (1/640) tau := by
                    convert childUR hs2333222 hx2333222 hy2333222 using 1 <;> norm_num
                  exact Batch0433.cell3471.sound htau (by
                    simp only [Batch0433.cell3471, Batch0433.tau3471, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23332223 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (63/160 : ℝ) with hy233322 | hy233322
            · have hs2333221 : InSquare (-13/320) (25/64) (1/320) tau := by
                convert childLR hs233322 hx233322 hy233322 using 1 <;> norm_num
              rcases le_total tau.re (-13/320 : ℝ) with hx2333221 | hx2333221
              · rcases le_total tau.im (25/64 : ℝ) with hy2333221 | hy2333221
                · have hs23332210 : InSquare (-27/640) (249/640) (1/640) tau := by
                    convert childLL hs2333221 hx2333221 hy2333221 using 1 <;> norm_num
                  exact Batch0433.cell3464.sound htau (by
                    simp only [Batch0433.cell3464, Batch0433.tau3464, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23332210 (by positivity) using 1 <;> norm_num)
                · have hs23332212 : InSquare (-27/640) (251/640) (1/640) tau := by
                    convert childUL hs2333221 hx2333221 hy2333221 using 1 <;> norm_num
                  exact Batch0433.cell3466.sound htau (by
                    simp only [Batch0433.cell3466, Batch0433.tau3466, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23332212 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (25/64 : ℝ) with hy2333221 | hy2333221
                · have hs23332211 : InSquare (-5/128) (249/640) (1/640) tau := by
                    convert childLR hs2333221 hx2333221 hy2333221 using 1 <;> norm_num
                  exact Batch0433.cell3465.sound htau (by
                    simp only [Batch0433.cell3465, Batch0433.tau3465, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23332211 (by positivity) using 1 <;> norm_num)
                · have hs23332213 : InSquare (-5/128) (251/640) (1/640) tau := by
                    convert childUR hs2333221 hx2333221 hy2333221 using 1 <;> norm_num
                  exact Batch0433.cell3467.sound htau (by
                    simp only [Batch0433.cell3467, Batch0433.tau3467, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23332213 (by positivity) using 1 <;> norm_num)
            · have hs2333223 : InSquare (-13/320) (127/320) (1/320) tau := by
                convert childUR hs233322 hx233322 hy233322 using 1 <;> norm_num
              rcases le_total tau.re (-13/320 : ℝ) with hx2333223 | hx2333223
              · rcases le_total tau.im (127/320 : ℝ) with hy2333223 | hy2333223
                · have hs23332230 : InSquare (-27/640) (253/640) (1/640) tau := by
                    convert childLL hs2333223 hx2333223 hy2333223 using 1 <;> norm_num
                  exact Batch0434.cell3472.sound htau (by
                    simp only [Batch0434.cell3472, Batch0434.tau3472, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23332230 (by positivity) using 1 <;> norm_num)
                · have hs23332232 : InSquare (-27/640) (51/128) (1/640) tau := by
                    convert childUL hs2333223 hx2333223 hy2333223 using 1 <;> norm_num
                  exact Batch0434.cell3474.sound htau (by
                    simp only [Batch0434.cell3474, Batch0434.tau3474, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23332232 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (127/320 : ℝ) with hy2333223 | hy2333223
                · have hs23332231 : InSquare (-5/128) (253/640) (1/640) tau := by
                    convert childLR hs2333223 hx2333223 hy2333223 using 1 <;> norm_num
                  exact Batch0434.cell3473.sound htau (by
                    simp only [Batch0434.cell3473, Batch0434.tau3473, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23332231 (by positivity) using 1 <;> norm_num)
                · have hs23332233 : InSquare (-5/128) (51/128) (1/640) tau := by
                    convert childUR hs2333223 hx2333223 hy2333223 using 1 <;> norm_num
                  exact Batch0434.cell3475.sound htau (by
                    simp only [Batch0434.cell3475, Batch0434.tau3475, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23332233 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (31/80 : ℝ) with hy23332 | hy23332
        · have hs233321 : InSquare (-1/32) (61/160) (1/160) tau := by
            convert childLR hs23332 hx23332 hy23332 using 1 <;> norm_num
          rcases le_total tau.re (-1/32 : ℝ) with hx233321 | hx233321
          · rcases le_total tau.im (61/160 : ℝ) with hy233321 | hy233321
            · have hs2333210 : InSquare (-11/320) (121/320) (1/320) tau := by
                convert childLL hs233321 hx233321 hy233321 using 1 <;> norm_num
              exact Batch0276.cell2212.sound htau (by
                simp only [Batch0276.cell2212, Batch0276.tau2212, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2333210 (by positivity) using 1 <;> norm_num)
            · have hs2333212 : InSquare (-11/320) (123/320) (1/320) tau := by
                convert childUL hs233321 hx233321 hy233321 using 1 <;> norm_num
              rcases le_total tau.re (-11/320 : ℝ) with hx2333212 | hx2333212
              · rcases le_total tau.im (123/320 : ℝ) with hy2333212 | hy2333212
                · have hs23332120 : InSquare (-23/640) (49/128) (1/640) tau := by
                    convert childLL hs2333212 hx2333212 hy2333212 using 1 <;> norm_num
                  exact Batch0432.cell3456.sound htau (by
                    simp only [Batch0432.cell3456, Batch0432.tau3456, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23332120 (by positivity) using 1 <;> norm_num)
                · have hs23332122 : InSquare (-23/640) (247/640) (1/640) tau := by
                    convert childUL hs2333212 hx2333212 hy2333212 using 1 <;> norm_num
                  exact Batch0432.cell3458.sound htau (by
                    simp only [Batch0432.cell3458, Batch0432.tau3458, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23332122 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (123/320 : ℝ) with hy2333212 | hy2333212
                · have hs23332121 : InSquare (-21/640) (49/128) (1/640) tau := by
                    convert childLR hs2333212 hx2333212 hy2333212 using 1 <;> norm_num
                  exact Batch0432.cell3457.sound htau (by
                    simp only [Batch0432.cell3457, Batch0432.tau3457, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23332121 (by positivity) using 1 <;> norm_num)
                · have hs23332123 : InSquare (-21/640) (247/640) (1/640) tau := by
                    convert childUR hs2333212 hx2333212 hy2333212 using 1 <;> norm_num
                  exact Batch0432.cell3459.sound htau (by
                    simp only [Batch0432.cell3459, Batch0432.tau3459, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23332123 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (61/160 : ℝ) with hy233321 | hy233321
            · have hs2333211 : InSquare (-9/320) (121/320) (1/320) tau := by
                convert childLR hs233321 hx233321 hy233321 using 1 <;> norm_num
              exact Batch0276.cell2213.sound htau (by
                simp only [Batch0276.cell2213, Batch0276.tau2213, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2333211 (by positivity) using 1 <;> norm_num)
            · have hs2333213 : InSquare (-9/320) (123/320) (1/320) tau := by
                convert childUR hs233321 hx233321 hy233321 using 1 <;> norm_num
              exact Batch0276.cell2214.sound htau (by
                simp only [Batch0276.cell2214, Batch0276.tau2214, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2333213 (by positivity) using 1 <;> norm_num)
        · have hs233323 : InSquare (-1/32) (63/160) (1/160) tau := by
            convert childUR hs23332 hx23332 hy23332 using 1 <;> norm_num
          rcases le_total tau.re (-1/32 : ℝ) with hx233323 | hx233323
          · rcases le_total tau.im (63/160 : ℝ) with hy233323 | hy233323
            · have hs2333230 : InSquare (-11/320) (25/64) (1/320) tau := by
                convert childLL hs233323 hx233323 hy233323 using 1 <;> norm_num
              rcases le_total tau.re (-11/320 : ℝ) with hx2333230 | hx2333230
              · rcases le_total tau.im (25/64 : ℝ) with hy2333230 | hy2333230
                · have hs23332300 : InSquare (-23/640) (249/640) (1/640) tau := by
                    convert childLL hs2333230 hx2333230 hy2333230 using 1 <;> norm_num
                  exact Batch0434.cell3476.sound htau (by
                    simp only [Batch0434.cell3476, Batch0434.tau3476, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23332300 (by positivity) using 1 <;> norm_num)
                · have hs23332302 : InSquare (-23/640) (251/640) (1/640) tau := by
                    convert childUL hs2333230 hx2333230 hy2333230 using 1 <;> norm_num
                  exact Batch0434.cell3478.sound htau (by
                    simp only [Batch0434.cell3478, Batch0434.tau3478, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23332302 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (25/64 : ℝ) with hy2333230 | hy2333230
                · have hs23332301 : InSquare (-21/640) (249/640) (1/640) tau := by
                    convert childLR hs2333230 hx2333230 hy2333230 using 1 <;> norm_num
                  exact Batch0434.cell3477.sound htau (by
                    simp only [Batch0434.cell3477, Batch0434.tau3477, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23332301 (by positivity) using 1 <;> norm_num)
                · have hs23332303 : InSquare (-21/640) (251/640) (1/640) tau := by
                    convert childUR hs2333230 hx2333230 hy2333230 using 1 <;> norm_num
                  exact Batch0434.cell3479.sound htau (by
                    simp only [Batch0434.cell3479, Batch0434.tau3479, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23332303 (by positivity) using 1 <;> norm_num)
            · have hs2333232 : InSquare (-11/320) (127/320) (1/320) tau := by
                convert childUL hs233323 hx233323 hy233323 using 1 <;> norm_num
              rcases le_total tau.re (-11/320 : ℝ) with hx2333232 | hx2333232
              · rcases le_total tau.im (127/320 : ℝ) with hy2333232 | hy2333232
                · have hs23332320 : InSquare (-23/640) (253/640) (1/640) tau := by
                    convert childLL hs2333232 hx2333232 hy2333232 using 1 <;> norm_num
                  exact Batch0435.cell3484.sound htau (by
                    simp only [Batch0435.cell3484, Batch0435.tau3484, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23332320 (by positivity) using 1 <;> norm_num)
                · have hs23332322 : InSquare (-23/640) (51/128) (1/640) tau := by
                    convert childUL hs2333232 hx2333232 hy2333232 using 1 <;> norm_num
                  exact Batch0435.cell3486.sound htau (by
                    simp only [Batch0435.cell3486, Batch0435.tau3486, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23332322 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (127/320 : ℝ) with hy2333232 | hy2333232
                · have hs23332321 : InSquare (-21/640) (253/640) (1/640) tau := by
                    convert childLR hs2333232 hx2333232 hy2333232 using 1 <;> norm_num
                  exact Batch0435.cell3485.sound htau (by
                    simp only [Batch0435.cell3485, Batch0435.tau3485, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23332321 (by positivity) using 1 <;> norm_num)
                · have hs23332323 : InSquare (-21/640) (51/128) (1/640) tau := by
                    convert childUR hs2333232 hx2333232 hy2333232 using 1 <;> norm_num
                  exact Batch0435.cell3487.sound htau (by
                    simp only [Batch0435.cell3487, Batch0435.tau3487, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23332323 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (63/160 : ℝ) with hy233323 | hy233323
            · have hs2333231 : InSquare (-9/320) (25/64) (1/320) tau := by
                convert childLR hs233323 hx233323 hy233323 using 1 <;> norm_num
              rcases le_total tau.re (-9/320 : ℝ) with hx2333231 | hx2333231
              · rcases le_total tau.im (25/64 : ℝ) with hy2333231 | hy2333231
                · have hs23332310 : InSquare (-19/640) (249/640) (1/640) tau := by
                    convert childLL hs2333231 hx2333231 hy2333231 using 1 <;> norm_num
                  exact Batch0435.cell3480.sound htau (by
                    simp only [Batch0435.cell3480, Batch0435.tau3480, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23332310 (by positivity) using 1 <;> norm_num)
                · have hs23332312 : InSquare (-19/640) (251/640) (1/640) tau := by
                    convert childUL hs2333231 hx2333231 hy2333231 using 1 <;> norm_num
                  exact Batch0435.cell3482.sound htau (by
                    simp only [Batch0435.cell3482, Batch0435.tau3482, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23332312 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (25/64 : ℝ) with hy2333231 | hy2333231
                · have hs23332311 : InSquare (-17/640) (249/640) (1/640) tau := by
                    convert childLR hs2333231 hx2333231 hy2333231 using 1 <;> norm_num
                  exact Batch0435.cell3481.sound htau (by
                    simp only [Batch0435.cell3481, Batch0435.tau3481, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23332311 (by positivity) using 1 <;> norm_num)
                · have hs23332313 : InSquare (-17/640) (251/640) (1/640) tau := by
                    convert childUR hs2333231 hx2333231 hy2333231 using 1 <;> norm_num
                  exact Batch0435.cell3483.sound htau (by
                    simp only [Batch0435.cell3483, Batch0435.tau3483, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23332313 (by positivity) using 1 <;> norm_num)
            · have hs2333233 : InSquare (-9/320) (127/320) (1/320) tau := by
                convert childUR hs233323 hx233323 hy233323 using 1 <;> norm_num
              rcases le_total tau.re (-9/320 : ℝ) with hx2333233 | hx2333233
              · rcases le_total tau.im (127/320 : ℝ) with hy2333233 | hy2333233
                · have hs23332330 : InSquare (-19/640) (253/640) (1/640) tau := by
                    convert childLL hs2333233 hx2333233 hy2333233 using 1 <;> norm_num
                  exact Batch0436.cell3488.sound htau (by
                    simp only [Batch0436.cell3488, Batch0436.tau3488, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23332330 (by positivity) using 1 <;> norm_num)
                · have hs23332332 : InSquare (-19/640) (51/128) (1/640) tau := by
                    convert childUL hs2333233 hx2333233 hy2333233 using 1 <;> norm_num
                  exact Batch0436.cell3490.sound htau (by
                    simp only [Batch0436.cell3490, Batch0436.tau3490, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23332332 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (127/320 : ℝ) with hy2333233 | hy2333233
                · have hs23332331 : InSquare (-17/640) (253/640) (1/640) tau := by
                    convert childLR hs2333233 hx2333233 hy2333233 using 1 <;> norm_num
                  exact Batch0436.cell3489.sound htau (by
                    simp only [Batch0436.cell3489, Batch0436.tau3489, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23332331 (by positivity) using 1 <;> norm_num)
                · have hs23332333 : InSquare (-17/640) (51/128) (1/640) tau := by
                    convert childUR hs2333233 hx2333233 hy2333233 using 1 <;> norm_num
                  exact Batch0436.cell3491.sound htau (by
                    simp only [Batch0436.cell3491, Batch0436.tau3491, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23332333 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (3/8 : ℝ) with hy2333 | hy2333
    · have hs23331 : InSquare (-1/80) (29/80) (1/80) tau := by
        convert childLR hs hx2333 hy2333 using 1 <;> norm_num
      rcases le_total tau.re (-1/80 : ℝ) with hx23331 | hx23331
      · rcases le_total tau.im (29/80 : ℝ) with hy23331 | hy23331
        · have hs233310 : InSquare (-3/160) (57/160) (1/160) tau := by
            convert childLL hs23331 hx23331 hy23331 using 1 <;> norm_num
          rcases le_total tau.re (-3/160 : ℝ) with hx233310 | hx233310
          · rcases le_total tau.im (57/160 : ℝ) with hy233310 | hy233310
            · have hs2333100 : InSquare (-7/320) (113/320) (1/320) tau := by
                convert childLL hs233310 hx233310 hy233310 using 1 <;> norm_num
              exact Batch0274.cell2198.sound htau (by
                simp only [Batch0274.cell2198, Batch0274.tau2198, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2333100 (by positivity) using 1 <;> norm_num)
            · have hs2333102 : InSquare (-7/320) (23/64) (1/320) tau := by
                convert childUL hs233310 hx233310 hy233310 using 1 <;> norm_num
              exact Batch0275.cell2200.sound htau (by
                simp only [Batch0275.cell2200, Batch0275.tau2200, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2333102 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (57/160 : ℝ) with hy233310 | hy233310
            · have hs2333101 : InSquare (-1/64) (113/320) (1/320) tau := by
                convert childLR hs233310 hx233310 hy233310 using 1 <;> norm_num
              exact Batch0274.cell2199.sound htau (by
                simp only [Batch0274.cell2199, Batch0274.tau2199, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2333101 (by positivity) using 1 <;> norm_num)
            · have hs2333103 : InSquare (-1/64) (23/64) (1/320) tau := by
                convert childUR hs233310 hx233310 hy233310 using 1 <;> norm_num
              exact Batch0275.cell2201.sound htau (by
                simp only [Batch0275.cell2201, Batch0275.tau2201, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2333103 (by positivity) using 1 <;> norm_num)
        · have hs233312 : InSquare (-3/160) (59/160) (1/160) tau := by
            convert childUL hs23331 hx23331 hy23331 using 1 <;> norm_num
          rcases le_total tau.re (-3/160 : ℝ) with hx233312 | hx233312
          · rcases le_total tau.im (59/160 : ℝ) with hy233312 | hy233312
            · have hs2333120 : InSquare (-7/320) (117/320) (1/320) tau := by
                convert childLL hs233312 hx233312 hy233312 using 1 <;> norm_num
              exact Batch0275.cell2202.sound htau (by
                simp only [Batch0275.cell2202, Batch0275.tau2202, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2333120 (by positivity) using 1 <;> norm_num)
            · have hs2333122 : InSquare (-7/320) (119/320) (1/320) tau := by
                convert childUL hs233312 hx233312 hy233312 using 1 <;> norm_num
              exact Batch0275.cell2204.sound htau (by
                simp only [Batch0275.cell2204, Batch0275.tau2204, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2333122 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (59/160 : ℝ) with hy233312 | hy233312
            · have hs2333121 : InSquare (-1/64) (117/320) (1/320) tau := by
                convert childLR hs233312 hx233312 hy233312 using 1 <;> norm_num
              exact Batch0275.cell2203.sound htau (by
                simp only [Batch0275.cell2203, Batch0275.tau2203, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2333121 (by positivity) using 1 <;> norm_num)
            · have hs2333123 : InSquare (-1/64) (119/320) (1/320) tau := by
                convert childUR hs233312 hx233312 hy233312 using 1 <;> norm_num
              exact Batch0275.cell2205.sound htau (by
                simp only [Batch0275.cell2205, Batch0275.tau2205, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2333123 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (29/80 : ℝ) with hy23331 | hy23331
        · have hs233311 : InSquare (-1/160) (57/160) (1/160) tau := by
            convert childLR hs23331 hx23331 hy23331 using 1 <;> norm_num
          exact Batch0123.cell0985.sound htau (by
            simp only [Batch0123.cell0985, Batch0123.tau0985, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs233311 (by positivity) using 1 <;> norm_num)
        · have hs233313 : InSquare (-1/160) (59/160) (1/160) tau := by
            convert childUR hs23331 hx23331 hy23331 using 1 <;> norm_num
          rcases le_total tau.re (-1/160 : ℝ) with hx233313 | hx233313
          · rcases le_total tau.im (59/160 : ℝ) with hy233313 | hy233313
            · have hs2333130 : InSquare (-3/320) (117/320) (1/320) tau := by
                convert childLL hs233313 hx233313 hy233313 using 1 <;> norm_num
              exact Batch0275.cell2206.sound htau (by
                simp only [Batch0275.cell2206, Batch0275.tau2206, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2333130 (by positivity) using 1 <;> norm_num)
            · have hs2333132 : InSquare (-3/320) (119/320) (1/320) tau := by
                convert childUL hs233313 hx233313 hy233313 using 1 <;> norm_num
              exact Batch0276.cell2208.sound htau (by
                simp only [Batch0276.cell2208, Batch0276.tau2208, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2333132 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (59/160 : ℝ) with hy233313 | hy233313
            · have hs2333131 : InSquare (-1/320) (117/320) (1/320) tau := by
                convert childLR hs233313 hx233313 hy233313 using 1 <;> norm_num
              exact Batch0275.cell2207.sound htau (by
                simp only [Batch0275.cell2207, Batch0275.tau2207, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2333131 (by positivity) using 1 <;> norm_num)
            · have hs2333133 : InSquare (-1/320) (119/320) (1/320) tau := by
                convert childUR hs233313 hx233313 hy233313 using 1 <;> norm_num
              exact Batch0276.cell2209.sound htau (by
                simp only [Batch0276.cell2209, Batch0276.tau2209, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2333133 (by positivity) using 1 <;> norm_num)
    · have hs23333 : InSquare (-1/80) (31/80) (1/80) tau := by
        convert childUR hs hx2333 hy2333 using 1 <;> norm_num
      rcases le_total tau.re (-1/80 : ℝ) with hx23333 | hx23333
      · rcases le_total tau.im (31/80 : ℝ) with hy23333 | hy23333
        · have hs233330 : InSquare (-3/160) (61/160) (1/160) tau := by
            convert childLL hs23333 hx23333 hy23333 using 1 <;> norm_num
          rcases le_total tau.re (-3/160 : ℝ) with hx233330 | hx233330
          · rcases le_total tau.im (61/160 : ℝ) with hy233330 | hy233330
            · have hs2333300 : InSquare (-7/320) (121/320) (1/320) tau := by
                convert childLL hs233330 hx233330 hy233330 using 1 <;> norm_num
              exact Batch0276.cell2215.sound htau (by
                simp only [Batch0276.cell2215, Batch0276.tau2215, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2333300 (by positivity) using 1 <;> norm_num)
            · have hs2333302 : InSquare (-7/320) (123/320) (1/320) tau := by
                convert childUL hs233330 hx233330 hy233330 using 1 <;> norm_num
              exact Batch0277.cell2217.sound htau (by
                simp only [Batch0277.cell2217, Batch0277.tau2217, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2333302 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (61/160 : ℝ) with hy233330 | hy233330
            · have hs2333301 : InSquare (-1/64) (121/320) (1/320) tau := by
                convert childLR hs233330 hx233330 hy233330 using 1 <;> norm_num
              exact Batch0277.cell2216.sound htau (by
                simp only [Batch0277.cell2216, Batch0277.tau2216, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2333301 (by positivity) using 1 <;> norm_num)
            · have hs2333303 : InSquare (-1/64) (123/320) (1/320) tau := by
                convert childUR hs233330 hx233330 hy233330 using 1 <;> norm_num
              exact Batch0277.cell2218.sound htau (by
                simp only [Batch0277.cell2218, Batch0277.tau2218, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2333303 (by positivity) using 1 <;> norm_num)
        · have hs233332 : InSquare (-3/160) (63/160) (1/160) tau := by
            convert childUL hs23333 hx23333 hy23333 using 1 <;> norm_num
          rcases le_total tau.re (-3/160 : ℝ) with hx233332 | hx233332
          · rcases le_total tau.im (63/160 : ℝ) with hy233332 | hy233332
            · have hs2333320 : InSquare (-7/320) (25/64) (1/320) tau := by
                convert childLL hs233332 hx233332 hy233332 using 1 <;> norm_num
              rcases le_total tau.re (-7/320 : ℝ) with hx2333320 | hx2333320
              · rcases le_total tau.im (25/64 : ℝ) with hy2333320 | hy2333320
                · have hs23333200 : InSquare (-3/128) (249/640) (1/640) tau := by
                    convert childLL hs2333320 hx2333320 hy2333320 using 1 <;> norm_num
                  exact Batch0436.cell3492.sound htau (by
                    simp only [Batch0436.cell3492, Batch0436.tau3492, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23333200 (by positivity) using 1 <;> norm_num)
                · have hs23333202 : InSquare (-3/128) (251/640) (1/640) tau := by
                    convert childUL hs2333320 hx2333320 hy2333320 using 1 <;> norm_num
                  exact Batch0436.cell3494.sound htau (by
                    simp only [Batch0436.cell3494, Batch0436.tau3494, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23333202 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (25/64 : ℝ) with hy2333320 | hy2333320
                · have hs23333201 : InSquare (-13/640) (249/640) (1/640) tau := by
                    convert childLR hs2333320 hx2333320 hy2333320 using 1 <;> norm_num
                  exact Batch0436.cell3493.sound htau (by
                    simp only [Batch0436.cell3493, Batch0436.tau3493, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23333201 (by positivity) using 1 <;> norm_num)
                · have hs23333203 : InSquare (-13/640) (251/640) (1/640) tau := by
                    convert childUR hs2333320 hx2333320 hy2333320 using 1 <;> norm_num
                  exact Batch0436.cell3495.sound htau (by
                    simp only [Batch0436.cell3495, Batch0436.tau3495, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23333203 (by positivity) using 1 <;> norm_num)
            · have hs2333322 : InSquare (-7/320) (127/320) (1/320) tau := by
                convert childUL hs233332 hx233332 hy233332 using 1 <;> norm_num
              rcases le_total tau.re (-7/320 : ℝ) with hx2333322 | hx2333322
              · rcases le_total tau.im (127/320 : ℝ) with hy2333322 | hy2333322
                · have hs23333220 : InSquare (-3/128) (253/640) (1/640) tau := by
                    convert childLL hs2333322 hx2333322 hy2333322 using 1 <;> norm_num
                  exact Batch0437.cell3500.sound htau (by
                    simp only [Batch0437.cell3500, Batch0437.tau3500, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23333220 (by positivity) using 1 <;> norm_num)
                · have hs23333222 : InSquare (-3/128) (51/128) (1/640) tau := by
                    convert childUL hs2333322 hx2333322 hy2333322 using 1 <;> norm_num
                  exact Batch0437.cell3502.sound htau (by
                    simp only [Batch0437.cell3502, Batch0437.tau3502, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23333222 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (127/320 : ℝ) with hy2333322 | hy2333322
                · have hs23333221 : InSquare (-13/640) (253/640) (1/640) tau := by
                    convert childLR hs2333322 hx2333322 hy2333322 using 1 <;> norm_num
                  exact Batch0437.cell3501.sound htau (by
                    simp only [Batch0437.cell3501, Batch0437.tau3501, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23333221 (by positivity) using 1 <;> norm_num)
                · have hs23333223 : InSquare (-13/640) (51/128) (1/640) tau := by
                    convert childUR hs2333322 hx2333322 hy2333322 using 1 <;> norm_num
                  exact Batch0437.cell3503.sound htau (by
                    simp only [Batch0437.cell3503, Batch0437.tau3503, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23333223 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (63/160 : ℝ) with hy233332 | hy233332
            · have hs2333321 : InSquare (-1/64) (25/64) (1/320) tau := by
                convert childLR hs233332 hx233332 hy233332 using 1 <;> norm_num
              rcases le_total tau.re (-1/64 : ℝ) with hx2333321 | hx2333321
              · rcases le_total tau.im (25/64 : ℝ) with hy2333321 | hy2333321
                · have hs23333210 : InSquare (-11/640) (249/640) (1/640) tau := by
                    convert childLL hs2333321 hx2333321 hy2333321 using 1 <;> norm_num
                  exact Batch0437.cell3496.sound htau (by
                    simp only [Batch0437.cell3496, Batch0437.tau3496, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23333210 (by positivity) using 1 <;> norm_num)
                · have hs23333212 : InSquare (-11/640) (251/640) (1/640) tau := by
                    convert childUL hs2333321 hx2333321 hy2333321 using 1 <;> norm_num
                  exact Batch0437.cell3498.sound htau (by
                    simp only [Batch0437.cell3498, Batch0437.tau3498, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23333212 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (25/64 : ℝ) with hy2333321 | hy2333321
                · have hs23333211 : InSquare (-9/640) (249/640) (1/640) tau := by
                    convert childLR hs2333321 hx2333321 hy2333321 using 1 <;> norm_num
                  exact Batch0437.cell3497.sound htau (by
                    simp only [Batch0437.cell3497, Batch0437.tau3497, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23333211 (by positivity) using 1 <;> norm_num)
                · have hs23333213 : InSquare (-9/640) (251/640) (1/640) tau := by
                    convert childUR hs2333321 hx2333321 hy2333321 using 1 <;> norm_num
                  exact Batch0437.cell3499.sound htau (by
                    simp only [Batch0437.cell3499, Batch0437.tau3499, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23333213 (by positivity) using 1 <;> norm_num)
            · have hs2333323 : InSquare (-1/64) (127/320) (1/320) tau := by
                convert childUR hs233332 hx233332 hy233332 using 1 <;> norm_num
              rcases le_total tau.re (-1/64 : ℝ) with hx2333323 | hx2333323
              · rcases le_total tau.im (127/320 : ℝ) with hy2333323 | hy2333323
                · have hs23333230 : InSquare (-11/640) (253/640) (1/640) tau := by
                    convert childLL hs2333323 hx2333323 hy2333323 using 1 <;> norm_num
                  exact Batch0438.cell3504.sound htau (by
                    simp only [Batch0438.cell3504, Batch0438.tau3504, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23333230 (by positivity) using 1 <;> norm_num)
                · have hs23333232 : InSquare (-11/640) (51/128) (1/640) tau := by
                    convert childUL hs2333323 hx2333323 hy2333323 using 1 <;> norm_num
                  exact Batch0438.cell3506.sound htau (by
                    simp only [Batch0438.cell3506, Batch0438.tau3506, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23333232 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (127/320 : ℝ) with hy2333323 | hy2333323
                · have hs23333231 : InSquare (-9/640) (253/640) (1/640) tau := by
                    convert childLR hs2333323 hx2333323 hy2333323 using 1 <;> norm_num
                  exact Batch0438.cell3505.sound htau (by
                    simp only [Batch0438.cell3505, Batch0438.tau3505, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23333231 (by positivity) using 1 <;> norm_num)
                · have hs23333233 : InSquare (-9/640) (51/128) (1/640) tau := by
                    convert childUR hs2333323 hx2333323 hy2333323 using 1 <;> norm_num
                  exact Batch0438.cell3507.sound htau (by
                    simp only [Batch0438.cell3507, Batch0438.tau3507, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23333233 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (31/80 : ℝ) with hy23333 | hy23333
        · have hs233331 : InSquare (-1/160) (61/160) (1/160) tau := by
            convert childLR hs23333 hx23333 hy23333 using 1 <;> norm_num
          rcases le_total tau.re (-1/160 : ℝ) with hx233331 | hx233331
          · rcases le_total tau.im (61/160 : ℝ) with hy233331 | hy233331
            · have hs2333310 : InSquare (-3/320) (121/320) (1/320) tau := by
                convert childLL hs233331 hx233331 hy233331 using 1 <;> norm_num
              exact Batch0277.cell2219.sound htau (by
                simp only [Batch0277.cell2219, Batch0277.tau2219, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2333310 (by positivity) using 1 <;> norm_num)
            · have hs2333312 : InSquare (-3/320) (123/320) (1/320) tau := by
                convert childUL hs233331 hx233331 hy233331 using 1 <;> norm_num
              exact Batch0277.cell2221.sound htau (by
                simp only [Batch0277.cell2221, Batch0277.tau2221, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2333312 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (61/160 : ℝ) with hy233331 | hy233331
            · have hs2333311 : InSquare (-1/320) (121/320) (1/320) tau := by
                convert childLR hs233331 hx233331 hy233331 using 1 <;> norm_num
              exact Batch0277.cell2220.sound htau (by
                simp only [Batch0277.cell2220, Batch0277.tau2220, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2333311 (by positivity) using 1 <;> norm_num)
            · have hs2333313 : InSquare (-1/320) (123/320) (1/320) tau := by
                convert childUR hs233331 hx233331 hy233331 using 1 <;> norm_num
              exact Batch0277.cell2222.sound htau (by
                simp only [Batch0277.cell2222, Batch0277.tau2222, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2333313 (by positivity) using 1 <;> norm_num)
        · have hs233333 : InSquare (-1/160) (63/160) (1/160) tau := by
            convert childUR hs23333 hx23333 hy23333 using 1 <;> norm_num
          rcases le_total tau.re (-1/160 : ℝ) with hx233333 | hx233333
          · rcases le_total tau.im (63/160 : ℝ) with hy233333 | hy233333
            · have hs2333330 : InSquare (-3/320) (25/64) (1/320) tau := by
                convert childLL hs233333 hx233333 hy233333 using 1 <;> norm_num
              rcases le_total tau.re (-3/320 : ℝ) with hx2333330 | hx2333330
              · rcases le_total tau.im (25/64 : ℝ) with hy2333330 | hy2333330
                · have hs23333300 : InSquare (-7/640) (249/640) (1/640) tau := by
                    convert childLL hs2333330 hx2333330 hy2333330 using 1 <;> norm_num
                  exact Batch0438.cell3508.sound htau (by
                    simp only [Batch0438.cell3508, Batch0438.tau3508, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23333300 (by positivity) using 1 <;> norm_num)
                · have hs23333302 : InSquare (-7/640) (251/640) (1/640) tau := by
                    convert childUL hs2333330 hx2333330 hy2333330 using 1 <;> norm_num
                  exact Batch0438.cell3510.sound htau (by
                    simp only [Batch0438.cell3510, Batch0438.tau3510, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23333302 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (25/64 : ℝ) with hy2333330 | hy2333330
                · have hs23333301 : InSquare (-1/128) (249/640) (1/640) tau := by
                    convert childLR hs2333330 hx2333330 hy2333330 using 1 <;> norm_num
                  exact Batch0438.cell3509.sound htau (by
                    simp only [Batch0438.cell3509, Batch0438.tau3509, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23333301 (by positivity) using 1 <;> norm_num)
                · have hs23333303 : InSquare (-1/128) (251/640) (1/640) tau := by
                    convert childUR hs2333330 hx2333330 hy2333330 using 1 <;> norm_num
                  exact Batch0438.cell3511.sound htau (by
                    simp only [Batch0438.cell3511, Batch0438.tau3511, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23333303 (by positivity) using 1 <;> norm_num)
            · have hs2333332 : InSquare (-3/320) (127/320) (1/320) tau := by
                convert childUL hs233333 hx233333 hy233333 using 1 <;> norm_num
              rcases le_total tau.re (-3/320 : ℝ) with hx2333332 | hx2333332
              · rcases le_total tau.im (127/320 : ℝ) with hy2333332 | hy2333332
                · have hs23333320 : InSquare (-7/640) (253/640) (1/640) tau := by
                    convert childLL hs2333332 hx2333332 hy2333332 using 1 <;> norm_num
                  exact Batch0439.cell3516.sound htau (by
                    simp only [Batch0439.cell3516, Batch0439.tau3516, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23333320 (by positivity) using 1 <;> norm_num)
                · have hs23333322 : InSquare (-7/640) (51/128) (1/640) tau := by
                    convert childUL hs2333332 hx2333332 hy2333332 using 1 <;> norm_num
                  exact Batch0439.cell3518.sound htau (by
                    simp only [Batch0439.cell3518, Batch0439.tau3518, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23333322 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (127/320 : ℝ) with hy2333332 | hy2333332
                · have hs23333321 : InSquare (-1/128) (253/640) (1/640) tau := by
                    convert childLR hs2333332 hx2333332 hy2333332 using 1 <;> norm_num
                  exact Batch0439.cell3517.sound htau (by
                    simp only [Batch0439.cell3517, Batch0439.tau3517, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23333321 (by positivity) using 1 <;> norm_num)
                · have hs23333323 : InSquare (-1/128) (51/128) (1/640) tau := by
                    convert childUR hs2333332 hx2333332 hy2333332 using 1 <;> norm_num
                  exact Batch0439.cell3519.sound htau (by
                    simp only [Batch0439.cell3519, Batch0439.tau3519, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23333323 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (63/160 : ℝ) with hy233333 | hy233333
            · have hs2333331 : InSquare (-1/320) (25/64) (1/320) tau := by
                convert childLR hs233333 hx233333 hy233333 using 1 <;> norm_num
              rcases le_total tau.re (-1/320 : ℝ) with hx2333331 | hx2333331
              · rcases le_total tau.im (25/64 : ℝ) with hy2333331 | hy2333331
                · have hs23333310 : InSquare (-3/640) (249/640) (1/640) tau := by
                    convert childLL hs2333331 hx2333331 hy2333331 using 1 <;> norm_num
                  exact Batch0439.cell3512.sound htau (by
                    simp only [Batch0439.cell3512, Batch0439.tau3512, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23333310 (by positivity) using 1 <;> norm_num)
                · have hs23333312 : InSquare (-3/640) (251/640) (1/640) tau := by
                    convert childUL hs2333331 hx2333331 hy2333331 using 1 <;> norm_num
                  exact Batch0439.cell3514.sound htau (by
                    simp only [Batch0439.cell3514, Batch0439.tau3514, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23333312 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (25/64 : ℝ) with hy2333331 | hy2333331
                · have hs23333311 : InSquare (-1/640) (249/640) (1/640) tau := by
                    convert childLR hs2333331 hx2333331 hy2333331 using 1 <;> norm_num
                  exact Batch0439.cell3513.sound htau (by
                    simp only [Batch0439.cell3513, Batch0439.tau3513, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23333311 (by positivity) using 1 <;> norm_num)
                · have hs23333313 : InSquare (-1/640) (251/640) (1/640) tau := by
                    convert childUR hs2333331 hx2333331 hy2333331 using 1 <;> norm_num
                  exact Batch0439.cell3515.sound htau (by
                    simp only [Batch0439.cell3515, Batch0439.tau3515, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23333313 (by positivity) using 1 <;> norm_num)
            · have hs2333333 : InSquare (-1/320) (127/320) (1/320) tau := by
                convert childUR hs233333 hx233333 hy233333 using 1 <;> norm_num
              rcases le_total tau.re (-1/320 : ℝ) with hx2333333 | hx2333333
              · rcases le_total tau.im (127/320 : ℝ) with hy2333333 | hy2333333
                · have hs23333330 : InSquare (-3/640) (253/640) (1/640) tau := by
                    convert childLL hs2333333 hx2333333 hy2333333 using 1 <;> norm_num
                  exact Batch0440.cell3520.sound htau (by
                    simp only [Batch0440.cell3520, Batch0440.tau3520, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23333330 (by positivity) using 1 <;> norm_num)
                · have hs23333332 : InSquare (-3/640) (51/128) (1/640) tau := by
                    convert childUL hs2333333 hx2333333 hy2333333 using 1 <;> norm_num
                  exact Batch0440.cell3522.sound htau (by
                    simp only [Batch0440.cell3522, Batch0440.tau3522, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23333332 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (127/320 : ℝ) with hy2333333 | hy2333333
                · have hs23333331 : InSquare (-1/640) (253/640) (1/640) tau := by
                    convert childLR hs2333333 hx2333333 hy2333333 using 1 <;> norm_num
                  exact Batch0440.cell3521.sound htau (by
                    simp only [Batch0440.cell3521, Batch0440.tau3521, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23333331 (by positivity) using 1 <;> norm_num)
                · have hs23333333 : InSquare (-1/640) (51/128) (1/640) tau := by
                    convert childUR hs2333333 hx2333333 hy2333333 using 1 <;> norm_num
                  exact Batch0440.cell3523.sound htau (by
                    simp only [Batch0440.cell3523, Batch0440.tau3523, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23333333 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2333
