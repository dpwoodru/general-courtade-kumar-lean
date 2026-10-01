import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0142
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0279
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0280
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0281
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0282
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0283
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0284
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0440
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0441
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0442
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0443
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0444
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0445
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0446
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0447
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0448
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0449

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3222

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (1/40) (3/8) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (1/40 : ℝ) with hx3222 | hx3222
  · rcases le_total tau.im (3/8 : ℝ) with hy3222 | hy3222
    · have hs32220 : InSquare (1/80) (29/80) (1/80) tau := by
        convert childLL hs hx3222 hy3222 using 1 <;> norm_num
      rcases le_total tau.re (1/80 : ℝ) with hx32220 | hx32220
      · rcases le_total tau.im (29/80 : ℝ) with hy32220 | hy32220
        · have hs322200 : InSquare (1/160) (57/160) (1/160) tau := by
            convert childLL hs32220 hx32220 hy32220 using 1 <;> norm_num
          exact Batch0142.cell1140.sound htau (by
            simp only [Batch0142.cell1140, Batch0142.tau1140, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs322200 (by positivity) using 1 <;> norm_num)
        · have hs322202 : InSquare (1/160) (59/160) (1/160) tau := by
            convert childUL hs32220 hx32220 hy32220 using 1 <;> norm_num
          rcases le_total tau.re (1/160 : ℝ) with hx322202 | hx322202
          · rcases le_total tau.im (59/160 : ℝ) with hy322202 | hy322202
            · have hs3222020 : InSquare (1/320) (117/320) (1/320) tau := by
                convert childLL hs322202 hx322202 hy322202 using 1 <;> norm_num
              exact Batch0280.cell2240.sound htau (by
                simp only [Batch0280.cell2240, Batch0280.tau2240, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3222020 (by positivity) using 1 <;> norm_num)
            · have hs3222022 : InSquare (1/320) (119/320) (1/320) tau := by
                convert childUL hs322202 hx322202 hy322202 using 1 <;> norm_num
              exact Batch0280.cell2242.sound htau (by
                simp only [Batch0280.cell2242, Batch0280.tau2242, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3222022 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (59/160 : ℝ) with hy322202 | hy322202
            · have hs3222021 : InSquare (3/320) (117/320) (1/320) tau := by
                convert childLR hs322202 hx322202 hy322202 using 1 <;> norm_num
              exact Batch0280.cell2241.sound htau (by
                simp only [Batch0280.cell2241, Batch0280.tau2241, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3222021 (by positivity) using 1 <;> norm_num)
            · have hs3222023 : InSquare (3/320) (119/320) (1/320) tau := by
                convert childUR hs322202 hx322202 hy322202 using 1 <;> norm_num
              exact Batch0280.cell2243.sound htau (by
                simp only [Batch0280.cell2243, Batch0280.tau2243, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3222023 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (29/80 : ℝ) with hy32220 | hy32220
        · have hs322201 : InSquare (3/160) (57/160) (1/160) tau := by
            convert childLR hs32220 hx32220 hy32220 using 1 <;> norm_num
          rcases le_total tau.re (3/160 : ℝ) with hx322201 | hx322201
          · rcases le_total tau.im (57/160 : ℝ) with hy322201 | hy322201
            · have hs3222010 : InSquare (1/64) (113/320) (1/320) tau := by
                convert childLL hs322201 hx322201 hy322201 using 1 <;> norm_num
              exact Batch0279.cell2236.sound htau (by
                simp only [Batch0279.cell2236, Batch0279.tau2236, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3222010 (by positivity) using 1 <;> norm_num)
            · have hs3222012 : InSquare (1/64) (23/64) (1/320) tau := by
                convert childUL hs322201 hx322201 hy322201 using 1 <;> norm_num
              exact Batch0279.cell2238.sound htau (by
                simp only [Batch0279.cell2238, Batch0279.tau2238, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3222012 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (57/160 : ℝ) with hy322201 | hy322201
            · have hs3222011 : InSquare (7/320) (113/320) (1/320) tau := by
                convert childLR hs322201 hx322201 hy322201 using 1 <;> norm_num
              exact Batch0279.cell2237.sound htau (by
                simp only [Batch0279.cell2237, Batch0279.tau2237, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3222011 (by positivity) using 1 <;> norm_num)
            · have hs3222013 : InSquare (7/320) (23/64) (1/320) tau := by
                convert childUR hs322201 hx322201 hy322201 using 1 <;> norm_num
              exact Batch0279.cell2239.sound htau (by
                simp only [Batch0279.cell2239, Batch0279.tau2239, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3222013 (by positivity) using 1 <;> norm_num)
        · have hs322203 : InSquare (3/160) (59/160) (1/160) tau := by
            convert childUR hs32220 hx32220 hy32220 using 1 <;> norm_num
          rcases le_total tau.re (3/160 : ℝ) with hx322203 | hx322203
          · rcases le_total tau.im (59/160 : ℝ) with hy322203 | hy322203
            · have hs3222030 : InSquare (1/64) (117/320) (1/320) tau := by
                convert childLL hs322203 hx322203 hy322203 using 1 <;> norm_num
              exact Batch0280.cell2244.sound htau (by
                simp only [Batch0280.cell2244, Batch0280.tau2244, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3222030 (by positivity) using 1 <;> norm_num)
            · have hs3222032 : InSquare (1/64) (119/320) (1/320) tau := by
                convert childUL hs322203 hx322203 hy322203 using 1 <;> norm_num
              exact Batch0280.cell2246.sound htau (by
                simp only [Batch0280.cell2246, Batch0280.tau2246, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3222032 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (59/160 : ℝ) with hy322203 | hy322203
            · have hs3222031 : InSquare (7/320) (117/320) (1/320) tau := by
                convert childLR hs322203 hx322203 hy322203 using 1 <;> norm_num
              exact Batch0280.cell2245.sound htau (by
                simp only [Batch0280.cell2245, Batch0280.tau2245, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3222031 (by positivity) using 1 <;> norm_num)
            · have hs3222033 : InSquare (7/320) (119/320) (1/320) tau := by
                convert childUR hs322203 hx322203 hy322203 using 1 <;> norm_num
              exact Batch0280.cell2247.sound htau (by
                simp only [Batch0280.cell2247, Batch0280.tau2247, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3222033 (by positivity) using 1 <;> norm_num)
    · have hs32222 : InSquare (1/80) (31/80) (1/80) tau := by
        convert childUL hs hx3222 hy3222 using 1 <;> norm_num
      rcases le_total tau.re (1/80 : ℝ) with hx32222 | hx32222
      · rcases le_total tau.im (31/80 : ℝ) with hy32222 | hy32222
        · have hs322220 : InSquare (1/160) (61/160) (1/160) tau := by
            convert childLL hs32222 hx32222 hy32222 using 1 <;> norm_num
          rcases le_total tau.re (1/160 : ℝ) with hx322220 | hx322220
          · rcases le_total tau.im (61/160 : ℝ) with hy322220 | hy322220
            · have hs3222200 : InSquare (1/320) (121/320) (1/320) tau := by
                convert childLL hs322220 hx322220 hy322220 using 1 <;> norm_num
              exact Batch0283.cell2264.sound htau (by
                simp only [Batch0283.cell2264, Batch0283.tau2264, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3222200 (by positivity) using 1 <;> norm_num)
            · have hs3222202 : InSquare (1/320) (123/320) (1/320) tau := by
                convert childUL hs322220 hx322220 hy322220 using 1 <;> norm_num
              exact Batch0283.cell2266.sound htau (by
                simp only [Batch0283.cell2266, Batch0283.tau2266, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3222202 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (61/160 : ℝ) with hy322220 | hy322220
            · have hs3222201 : InSquare (3/320) (121/320) (1/320) tau := by
                convert childLR hs322220 hx322220 hy322220 using 1 <;> norm_num
              exact Batch0283.cell2265.sound htau (by
                simp only [Batch0283.cell2265, Batch0283.tau2265, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3222201 (by positivity) using 1 <;> norm_num)
            · have hs3222203 : InSquare (3/320) (123/320) (1/320) tau := by
                convert childUR hs322220 hx322220 hy322220 using 1 <;> norm_num
              exact Batch0283.cell2267.sound htau (by
                simp only [Batch0283.cell2267, Batch0283.tau2267, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3222203 (by positivity) using 1 <;> norm_num)
        · have hs322222 : InSquare (1/160) (63/160) (1/160) tau := by
            convert childUL hs32222 hx32222 hy32222 using 1 <;> norm_num
          rcases le_total tau.re (1/160 : ℝ) with hx322222 | hx322222
          · rcases le_total tau.im (63/160 : ℝ) with hy322222 | hy322222
            · have hs3222220 : InSquare (1/320) (25/64) (1/320) tau := by
                convert childLL hs322222 hx322222 hy322222 using 1 <;> norm_num
              rcases le_total tau.re (1/320 : ℝ) with hx3222220 | hx3222220
              · rcases le_total tau.im (25/64 : ℝ) with hy3222220 | hy3222220
                · have hs32222200 : InSquare (1/640) (249/640) (1/640) tau := by
                    convert childLL hs3222220 hx3222220 hy3222220 using 1 <;> norm_num
                  exact Batch0440.cell3524.sound htau (by
                    simp only [Batch0440.cell3524, Batch0440.tau3524, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32222200 (by positivity) using 1 <;> norm_num)
                · have hs32222202 : InSquare (1/640) (251/640) (1/640) tau := by
                    convert childUL hs3222220 hx3222220 hy3222220 using 1 <;> norm_num
                  exact Batch0440.cell3526.sound htau (by
                    simp only [Batch0440.cell3526, Batch0440.tau3526, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32222202 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (25/64 : ℝ) with hy3222220 | hy3222220
                · have hs32222201 : InSquare (3/640) (249/640) (1/640) tau := by
                    convert childLR hs3222220 hx3222220 hy3222220 using 1 <;> norm_num
                  exact Batch0440.cell3525.sound htau (by
                    simp only [Batch0440.cell3525, Batch0440.tau3525, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32222201 (by positivity) using 1 <;> norm_num)
                · have hs32222203 : InSquare (3/640) (251/640) (1/640) tau := by
                    convert childUR hs3222220 hx3222220 hy3222220 using 1 <;> norm_num
                  exact Batch0440.cell3527.sound htau (by
                    simp only [Batch0440.cell3527, Batch0440.tau3527, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32222203 (by positivity) using 1 <;> norm_num)
            · have hs3222222 : InSquare (1/320) (127/320) (1/320) tau := by
                convert childUL hs322222 hx322222 hy322222 using 1 <;> norm_num
              rcases le_total tau.re (1/320 : ℝ) with hx3222222 | hx3222222
              · rcases le_total tau.im (127/320 : ℝ) with hy3222222 | hy3222222
                · have hs32222220 : InSquare (1/640) (253/640) (1/640) tau := by
                    convert childLL hs3222222 hx3222222 hy3222222 using 1 <;> norm_num
                  exact Batch0441.cell3532.sound htau (by
                    simp only [Batch0441.cell3532, Batch0441.tau3532, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32222220 (by positivity) using 1 <;> norm_num)
                · have hs32222222 : InSquare (1/640) (51/128) (1/640) tau := by
                    convert childUL hs3222222 hx3222222 hy3222222 using 1 <;> norm_num
                  exact Batch0441.cell3534.sound htau (by
                    simp only [Batch0441.cell3534, Batch0441.tau3534, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32222222 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (127/320 : ℝ) with hy3222222 | hy3222222
                · have hs32222221 : InSquare (3/640) (253/640) (1/640) tau := by
                    convert childLR hs3222222 hx3222222 hy3222222 using 1 <;> norm_num
                  exact Batch0441.cell3533.sound htau (by
                    simp only [Batch0441.cell3533, Batch0441.tau3533, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32222221 (by positivity) using 1 <;> norm_num)
                · have hs32222223 : InSquare (3/640) (51/128) (1/640) tau := by
                    convert childUR hs3222222 hx3222222 hy3222222 using 1 <;> norm_num
                  exact Batch0441.cell3535.sound htau (by
                    simp only [Batch0441.cell3535, Batch0441.tau3535, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32222223 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (63/160 : ℝ) with hy322222 | hy322222
            · have hs3222221 : InSquare (3/320) (25/64) (1/320) tau := by
                convert childLR hs322222 hx322222 hy322222 using 1 <;> norm_num
              rcases le_total tau.re (3/320 : ℝ) with hx3222221 | hx3222221
              · rcases le_total tau.im (25/64 : ℝ) with hy3222221 | hy3222221
                · have hs32222210 : InSquare (1/128) (249/640) (1/640) tau := by
                    convert childLL hs3222221 hx3222221 hy3222221 using 1 <;> norm_num
                  exact Batch0441.cell3528.sound htau (by
                    simp only [Batch0441.cell3528, Batch0441.tau3528, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32222210 (by positivity) using 1 <;> norm_num)
                · have hs32222212 : InSquare (1/128) (251/640) (1/640) tau := by
                    convert childUL hs3222221 hx3222221 hy3222221 using 1 <;> norm_num
                  exact Batch0441.cell3530.sound htau (by
                    simp only [Batch0441.cell3530, Batch0441.tau3530, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32222212 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (25/64 : ℝ) with hy3222221 | hy3222221
                · have hs32222211 : InSquare (7/640) (249/640) (1/640) tau := by
                    convert childLR hs3222221 hx3222221 hy3222221 using 1 <;> norm_num
                  exact Batch0441.cell3529.sound htau (by
                    simp only [Batch0441.cell3529, Batch0441.tau3529, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32222211 (by positivity) using 1 <;> norm_num)
                · have hs32222213 : InSquare (7/640) (251/640) (1/640) tau := by
                    convert childUR hs3222221 hx3222221 hy3222221 using 1 <;> norm_num
                  exact Batch0441.cell3531.sound htau (by
                    simp only [Batch0441.cell3531, Batch0441.tau3531, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32222213 (by positivity) using 1 <;> norm_num)
            · have hs3222223 : InSquare (3/320) (127/320) (1/320) tau := by
                convert childUR hs322222 hx322222 hy322222 using 1 <;> norm_num
              rcases le_total tau.re (3/320 : ℝ) with hx3222223 | hx3222223
              · rcases le_total tau.im (127/320 : ℝ) with hy3222223 | hy3222223
                · have hs32222230 : InSquare (1/128) (253/640) (1/640) tau := by
                    convert childLL hs3222223 hx3222223 hy3222223 using 1 <;> norm_num
                  exact Batch0442.cell3536.sound htau (by
                    simp only [Batch0442.cell3536, Batch0442.tau3536, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32222230 (by positivity) using 1 <;> norm_num)
                · have hs32222232 : InSquare (1/128) (51/128) (1/640) tau := by
                    convert childUL hs3222223 hx3222223 hy3222223 using 1 <;> norm_num
                  exact Batch0442.cell3538.sound htau (by
                    simp only [Batch0442.cell3538, Batch0442.tau3538, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32222232 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (127/320 : ℝ) with hy3222223 | hy3222223
                · have hs32222231 : InSquare (7/640) (253/640) (1/640) tau := by
                    convert childLR hs3222223 hx3222223 hy3222223 using 1 <;> norm_num
                  exact Batch0442.cell3537.sound htau (by
                    simp only [Batch0442.cell3537, Batch0442.tau3537, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32222231 (by positivity) using 1 <;> norm_num)
                · have hs32222233 : InSquare (7/640) (51/128) (1/640) tau := by
                    convert childUR hs3222223 hx3222223 hy3222223 using 1 <;> norm_num
                  exact Batch0442.cell3539.sound htau (by
                    simp only [Batch0442.cell3539, Batch0442.tau3539, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32222233 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (31/80 : ℝ) with hy32222 | hy32222
        · have hs322221 : InSquare (3/160) (61/160) (1/160) tau := by
            convert childLR hs32222 hx32222 hy32222 using 1 <;> norm_num
          rcases le_total tau.re (3/160 : ℝ) with hx322221 | hx322221
          · rcases le_total tau.im (61/160 : ℝ) with hy322221 | hy322221
            · have hs3222210 : InSquare (1/64) (121/320) (1/320) tau := by
                convert childLL hs322221 hx322221 hy322221 using 1 <;> norm_num
              exact Batch0283.cell2268.sound htau (by
                simp only [Batch0283.cell2268, Batch0283.tau2268, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3222210 (by positivity) using 1 <;> norm_num)
            · have hs3222212 : InSquare (1/64) (123/320) (1/320) tau := by
                convert childUL hs322221 hx322221 hy322221 using 1 <;> norm_num
              exact Batch0283.cell2270.sound htau (by
                simp only [Batch0283.cell2270, Batch0283.tau2270, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3222212 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (61/160 : ℝ) with hy322221 | hy322221
            · have hs3222211 : InSquare (7/320) (121/320) (1/320) tau := by
                convert childLR hs322221 hx322221 hy322221 using 1 <;> norm_num
              exact Batch0283.cell2269.sound htau (by
                simp only [Batch0283.cell2269, Batch0283.tau2269, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3222211 (by positivity) using 1 <;> norm_num)
            · have hs3222213 : InSquare (7/320) (123/320) (1/320) tau := by
                convert childUR hs322221 hx322221 hy322221 using 1 <;> norm_num
              exact Batch0283.cell2271.sound htau (by
                simp only [Batch0283.cell2271, Batch0283.tau2271, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3222213 (by positivity) using 1 <;> norm_num)
        · have hs322223 : InSquare (3/160) (63/160) (1/160) tau := by
            convert childUR hs32222 hx32222 hy32222 using 1 <;> norm_num
          rcases le_total tau.re (3/160 : ℝ) with hx322223 | hx322223
          · rcases le_total tau.im (63/160 : ℝ) with hy322223 | hy322223
            · have hs3222230 : InSquare (1/64) (25/64) (1/320) tau := by
                convert childLL hs322223 hx322223 hy322223 using 1 <;> norm_num
              rcases le_total tau.re (1/64 : ℝ) with hx3222230 | hx3222230
              · rcases le_total tau.im (25/64 : ℝ) with hy3222230 | hy3222230
                · have hs32222300 : InSquare (9/640) (249/640) (1/640) tau := by
                    convert childLL hs3222230 hx3222230 hy3222230 using 1 <;> norm_num
                  exact Batch0442.cell3540.sound htau (by
                    simp only [Batch0442.cell3540, Batch0442.tau3540, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32222300 (by positivity) using 1 <;> norm_num)
                · have hs32222302 : InSquare (9/640) (251/640) (1/640) tau := by
                    convert childUL hs3222230 hx3222230 hy3222230 using 1 <;> norm_num
                  exact Batch0442.cell3542.sound htau (by
                    simp only [Batch0442.cell3542, Batch0442.tau3542, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32222302 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (25/64 : ℝ) with hy3222230 | hy3222230
                · have hs32222301 : InSquare (11/640) (249/640) (1/640) tau := by
                    convert childLR hs3222230 hx3222230 hy3222230 using 1 <;> norm_num
                  exact Batch0442.cell3541.sound htau (by
                    simp only [Batch0442.cell3541, Batch0442.tau3541, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32222301 (by positivity) using 1 <;> norm_num)
                · have hs32222303 : InSquare (11/640) (251/640) (1/640) tau := by
                    convert childUR hs3222230 hx3222230 hy3222230 using 1 <;> norm_num
                  exact Batch0442.cell3543.sound htau (by
                    simp only [Batch0442.cell3543, Batch0442.tau3543, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32222303 (by positivity) using 1 <;> norm_num)
            · have hs3222232 : InSquare (1/64) (127/320) (1/320) tau := by
                convert childUL hs322223 hx322223 hy322223 using 1 <;> norm_num
              rcases le_total tau.re (1/64 : ℝ) with hx3222232 | hx3222232
              · rcases le_total tau.im (127/320 : ℝ) with hy3222232 | hy3222232
                · have hs32222320 : InSquare (9/640) (253/640) (1/640) tau := by
                    convert childLL hs3222232 hx3222232 hy3222232 using 1 <;> norm_num
                  exact Batch0443.cell3548.sound htau (by
                    simp only [Batch0443.cell3548, Batch0443.tau3548, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32222320 (by positivity) using 1 <;> norm_num)
                · have hs32222322 : InSquare (9/640) (51/128) (1/640) tau := by
                    convert childUL hs3222232 hx3222232 hy3222232 using 1 <;> norm_num
                  exact Batch0443.cell3550.sound htau (by
                    simp only [Batch0443.cell3550, Batch0443.tau3550, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32222322 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (127/320 : ℝ) with hy3222232 | hy3222232
                · have hs32222321 : InSquare (11/640) (253/640) (1/640) tau := by
                    convert childLR hs3222232 hx3222232 hy3222232 using 1 <;> norm_num
                  exact Batch0443.cell3549.sound htau (by
                    simp only [Batch0443.cell3549, Batch0443.tau3549, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32222321 (by positivity) using 1 <;> norm_num)
                · have hs32222323 : InSquare (11/640) (51/128) (1/640) tau := by
                    convert childUR hs3222232 hx3222232 hy3222232 using 1 <;> norm_num
                  exact Batch0443.cell3551.sound htau (by
                    simp only [Batch0443.cell3551, Batch0443.tau3551, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32222323 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (63/160 : ℝ) with hy322223 | hy322223
            · have hs3222231 : InSquare (7/320) (25/64) (1/320) tau := by
                convert childLR hs322223 hx322223 hy322223 using 1 <;> norm_num
              rcases le_total tau.re (7/320 : ℝ) with hx3222231 | hx3222231
              · rcases le_total tau.im (25/64 : ℝ) with hy3222231 | hy3222231
                · have hs32222310 : InSquare (13/640) (249/640) (1/640) tau := by
                    convert childLL hs3222231 hx3222231 hy3222231 using 1 <;> norm_num
                  exact Batch0443.cell3544.sound htau (by
                    simp only [Batch0443.cell3544, Batch0443.tau3544, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32222310 (by positivity) using 1 <;> norm_num)
                · have hs32222312 : InSquare (13/640) (251/640) (1/640) tau := by
                    convert childUL hs3222231 hx3222231 hy3222231 using 1 <;> norm_num
                  exact Batch0443.cell3546.sound htau (by
                    simp only [Batch0443.cell3546, Batch0443.tau3546, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32222312 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (25/64 : ℝ) with hy3222231 | hy3222231
                · have hs32222311 : InSquare (3/128) (249/640) (1/640) tau := by
                    convert childLR hs3222231 hx3222231 hy3222231 using 1 <;> norm_num
                  exact Batch0443.cell3545.sound htau (by
                    simp only [Batch0443.cell3545, Batch0443.tau3545, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32222311 (by positivity) using 1 <;> norm_num)
                · have hs32222313 : InSquare (3/128) (251/640) (1/640) tau := by
                    convert childUR hs3222231 hx3222231 hy3222231 using 1 <;> norm_num
                  exact Batch0443.cell3547.sound htau (by
                    simp only [Batch0443.cell3547, Batch0443.tau3547, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32222313 (by positivity) using 1 <;> norm_num)
            · have hs3222233 : InSquare (7/320) (127/320) (1/320) tau := by
                convert childUR hs322223 hx322223 hy322223 using 1 <;> norm_num
              rcases le_total tau.re (7/320 : ℝ) with hx3222233 | hx3222233
              · rcases le_total tau.im (127/320 : ℝ) with hy3222233 | hy3222233
                · have hs32222330 : InSquare (13/640) (253/640) (1/640) tau := by
                    convert childLL hs3222233 hx3222233 hy3222233 using 1 <;> norm_num
                  exact Batch0444.cell3552.sound htau (by
                    simp only [Batch0444.cell3552, Batch0444.tau3552, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32222330 (by positivity) using 1 <;> norm_num)
                · have hs32222332 : InSquare (13/640) (51/128) (1/640) tau := by
                    convert childUL hs3222233 hx3222233 hy3222233 using 1 <;> norm_num
                  exact Batch0444.cell3554.sound htau (by
                    simp only [Batch0444.cell3554, Batch0444.tau3554, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32222332 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (127/320 : ℝ) with hy3222233 | hy3222233
                · have hs32222331 : InSquare (3/128) (253/640) (1/640) tau := by
                    convert childLR hs3222233 hx3222233 hy3222233 using 1 <;> norm_num
                  exact Batch0444.cell3553.sound htau (by
                    simp only [Batch0444.cell3553, Batch0444.tau3553, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32222331 (by positivity) using 1 <;> norm_num)
                · have hs32222333 : InSquare (3/128) (51/128) (1/640) tau := by
                    convert childUR hs3222233 hx3222233 hy3222233 using 1 <;> norm_num
                  exact Batch0444.cell3555.sound htau (by
                    simp only [Batch0444.cell3555, Batch0444.tau3555, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32222333 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (3/8 : ℝ) with hy3222 | hy3222
    · have hs32221 : InSquare (3/80) (29/80) (1/80) tau := by
        convert childLR hs hx3222 hy3222 using 1 <;> norm_num
      rcases le_total tau.re (3/80 : ℝ) with hx32221 | hx32221
      · rcases le_total tau.im (29/80 : ℝ) with hy32221 | hy32221
        · have hs322210 : InSquare (1/32) (57/160) (1/160) tau := by
            convert childLL hs32221 hx32221 hy32221 using 1 <;> norm_num
          rcases le_total tau.re (1/32 : ℝ) with hx322210 | hx322210
          · rcases le_total tau.im (57/160 : ℝ) with hy322210 | hy322210
            · have hs3222100 : InSquare (9/320) (113/320) (1/320) tau := by
                convert childLL hs322210 hx322210 hy322210 using 1 <;> norm_num
              exact Batch0281.cell2248.sound htau (by
                simp only [Batch0281.cell2248, Batch0281.tau2248, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3222100 (by positivity) using 1 <;> norm_num)
            · have hs3222102 : InSquare (9/320) (23/64) (1/320) tau := by
                convert childUL hs322210 hx322210 hy322210 using 1 <;> norm_num
              exact Batch0281.cell2250.sound htau (by
                simp only [Batch0281.cell2250, Batch0281.tau2250, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3222102 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (57/160 : ℝ) with hy322210 | hy322210
            · have hs3222101 : InSquare (11/320) (113/320) (1/320) tau := by
                convert childLR hs322210 hx322210 hy322210 using 1 <;> norm_num
              exact Batch0281.cell2249.sound htau (by
                simp only [Batch0281.cell2249, Batch0281.tau2249, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3222101 (by positivity) using 1 <;> norm_num)
            · have hs3222103 : InSquare (11/320) (23/64) (1/320) tau := by
                convert childUR hs322210 hx322210 hy322210 using 1 <;> norm_num
              exact Batch0281.cell2251.sound htau (by
                simp only [Batch0281.cell2251, Batch0281.tau2251, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3222103 (by positivity) using 1 <;> norm_num)
        · have hs322212 : InSquare (1/32) (59/160) (1/160) tau := by
            convert childUL hs32221 hx32221 hy32221 using 1 <;> norm_num
          rcases le_total tau.re (1/32 : ℝ) with hx322212 | hx322212
          · rcases le_total tau.im (59/160 : ℝ) with hy322212 | hy322212
            · have hs3222120 : InSquare (9/320) (117/320) (1/320) tau := by
                convert childLL hs322212 hx322212 hy322212 using 1 <;> norm_num
              exact Batch0282.cell2256.sound htau (by
                simp only [Batch0282.cell2256, Batch0282.tau2256, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3222120 (by positivity) using 1 <;> norm_num)
            · have hs3222122 : InSquare (9/320) (119/320) (1/320) tau := by
                convert childUL hs322212 hx322212 hy322212 using 1 <;> norm_num
              exact Batch0282.cell2258.sound htau (by
                simp only [Batch0282.cell2258, Batch0282.tau2258, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3222122 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (59/160 : ℝ) with hy322212 | hy322212
            · have hs3222121 : InSquare (11/320) (117/320) (1/320) tau := by
                convert childLR hs322212 hx322212 hy322212 using 1 <;> norm_num
              exact Batch0282.cell2257.sound htau (by
                simp only [Batch0282.cell2257, Batch0282.tau2257, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3222121 (by positivity) using 1 <;> norm_num)
            · have hs3222123 : InSquare (11/320) (119/320) (1/320) tau := by
                convert childUR hs322212 hx322212 hy322212 using 1 <;> norm_num
              exact Batch0282.cell2259.sound htau (by
                simp only [Batch0282.cell2259, Batch0282.tau2259, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3222123 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (29/80 : ℝ) with hy32221 | hy32221
        · have hs322211 : InSquare (7/160) (57/160) (1/160) tau := by
            convert childLR hs32221 hx32221 hy32221 using 1 <;> norm_num
          rcases le_total tau.re (7/160 : ℝ) with hx322211 | hx322211
          · rcases le_total tau.im (57/160 : ℝ) with hy322211 | hy322211
            · have hs3222110 : InSquare (13/320) (113/320) (1/320) tau := by
                convert childLL hs322211 hx322211 hy322211 using 1 <;> norm_num
              exact Batch0281.cell2252.sound htau (by
                simp only [Batch0281.cell2252, Batch0281.tau2252, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3222110 (by positivity) using 1 <;> norm_num)
            · have hs3222112 : InSquare (13/320) (23/64) (1/320) tau := by
                convert childUL hs322211 hx322211 hy322211 using 1 <;> norm_num
              exact Batch0281.cell2254.sound htau (by
                simp only [Batch0281.cell2254, Batch0281.tau2254, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3222112 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (57/160 : ℝ) with hy322211 | hy322211
            · have hs3222111 : InSquare (3/64) (113/320) (1/320) tau := by
                convert childLR hs322211 hx322211 hy322211 using 1 <;> norm_num
              exact Batch0281.cell2253.sound htau (by
                simp only [Batch0281.cell2253, Batch0281.tau2253, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3222111 (by positivity) using 1 <;> norm_num)
            · have hs3222113 : InSquare (3/64) (23/64) (1/320) tau := by
                convert childUR hs322211 hx322211 hy322211 using 1 <;> norm_num
              exact Batch0281.cell2255.sound htau (by
                simp only [Batch0281.cell2255, Batch0281.tau2255, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3222113 (by positivity) using 1 <;> norm_num)
        · have hs322213 : InSquare (7/160) (59/160) (1/160) tau := by
            convert childUR hs32221 hx32221 hy32221 using 1 <;> norm_num
          rcases le_total tau.re (7/160 : ℝ) with hx322213 | hx322213
          · rcases le_total tau.im (59/160 : ℝ) with hy322213 | hy322213
            · have hs3222130 : InSquare (13/320) (117/320) (1/320) tau := by
                convert childLL hs322213 hx322213 hy322213 using 1 <;> norm_num
              exact Batch0282.cell2260.sound htau (by
                simp only [Batch0282.cell2260, Batch0282.tau2260, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3222130 (by positivity) using 1 <;> norm_num)
            · have hs3222132 : InSquare (13/320) (119/320) (1/320) tau := by
                convert childUL hs322213 hx322213 hy322213 using 1 <;> norm_num
              exact Batch0282.cell2262.sound htau (by
                simp only [Batch0282.cell2262, Batch0282.tau2262, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3222132 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (59/160 : ℝ) with hy322213 | hy322213
            · have hs3222131 : InSquare (3/64) (117/320) (1/320) tau := by
                convert childLR hs322213 hx322213 hy322213 using 1 <;> norm_num
              exact Batch0282.cell2261.sound htau (by
                simp only [Batch0282.cell2261, Batch0282.tau2261, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3222131 (by positivity) using 1 <;> norm_num)
            · have hs3222133 : InSquare (3/64) (119/320) (1/320) tau := by
                convert childUR hs322213 hx322213 hy322213 using 1 <;> norm_num
              exact Batch0282.cell2263.sound htau (by
                simp only [Batch0282.cell2263, Batch0282.tau2263, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3222133 (by positivity) using 1 <;> norm_num)
    · have hs32223 : InSquare (3/80) (31/80) (1/80) tau := by
        convert childUR hs hx3222 hy3222 using 1 <;> norm_num
      rcases le_total tau.re (3/80 : ℝ) with hx32223 | hx32223
      · rcases le_total tau.im (31/80 : ℝ) with hy32223 | hy32223
        · have hs322230 : InSquare (1/32) (61/160) (1/160) tau := by
            convert childLL hs32223 hx32223 hy32223 using 1 <;> norm_num
          rcases le_total tau.re (1/32 : ℝ) with hx322230 | hx322230
          · rcases le_total tau.im (61/160 : ℝ) with hy322230 | hy322230
            · have hs3222300 : InSquare (9/320) (121/320) (1/320) tau := by
                convert childLL hs322230 hx322230 hy322230 using 1 <;> norm_num
              exact Batch0284.cell2272.sound htau (by
                simp only [Batch0284.cell2272, Batch0284.tau2272, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3222300 (by positivity) using 1 <;> norm_num)
            · have hs3222302 : InSquare (9/320) (123/320) (1/320) tau := by
                convert childUL hs322230 hx322230 hy322230 using 1 <;> norm_num
              exact Batch0284.cell2274.sound htau (by
                simp only [Batch0284.cell2274, Batch0284.tau2274, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3222302 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (61/160 : ℝ) with hy322230 | hy322230
            · have hs3222301 : InSquare (11/320) (121/320) (1/320) tau := by
                convert childLR hs322230 hx322230 hy322230 using 1 <;> norm_num
              exact Batch0284.cell2273.sound htau (by
                simp only [Batch0284.cell2273, Batch0284.tau2273, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3222301 (by positivity) using 1 <;> norm_num)
            · have hs3222303 : InSquare (11/320) (123/320) (1/320) tau := by
                convert childUR hs322230 hx322230 hy322230 using 1 <;> norm_num
              rcases le_total tau.re (11/320 : ℝ) with hx3222303 | hx3222303
              · rcases le_total tau.im (123/320 : ℝ) with hy3222303 | hy3222303
                · have hs32223030 : InSquare (21/640) (49/128) (1/640) tau := by
                    convert childLL hs3222303 hx3222303 hy3222303 using 1 <;> norm_num
                  exact Batch0444.cell3556.sound htau (by
                    simp only [Batch0444.cell3556, Batch0444.tau3556, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32223030 (by positivity) using 1 <;> norm_num)
                · have hs32223032 : InSquare (21/640) (247/640) (1/640) tau := by
                    convert childUL hs3222303 hx3222303 hy3222303 using 1 <;> norm_num
                  exact Batch0444.cell3558.sound htau (by
                    simp only [Batch0444.cell3558, Batch0444.tau3558, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32223032 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (123/320 : ℝ) with hy3222303 | hy3222303
                · have hs32223031 : InSquare (23/640) (49/128) (1/640) tau := by
                    convert childLR hs3222303 hx3222303 hy3222303 using 1 <;> norm_num
                  exact Batch0444.cell3557.sound htau (by
                    simp only [Batch0444.cell3557, Batch0444.tau3557, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32223031 (by positivity) using 1 <;> norm_num)
                · have hs32223033 : InSquare (23/640) (247/640) (1/640) tau := by
                    convert childUR hs3222303 hx3222303 hy3222303 using 1 <;> norm_num
                  exact Batch0444.cell3559.sound htau (by
                    simp only [Batch0444.cell3559, Batch0444.tau3559, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32223033 (by positivity) using 1 <;> norm_num)
        · have hs322232 : InSquare (1/32) (63/160) (1/160) tau := by
            convert childUL hs32223 hx32223 hy32223 using 1 <;> norm_num
          rcases le_total tau.re (1/32 : ℝ) with hx322232 | hx322232
          · rcases le_total tau.im (63/160 : ℝ) with hy322232 | hy322232
            · have hs3222320 : InSquare (9/320) (25/64) (1/320) tau := by
                convert childLL hs322232 hx322232 hy322232 using 1 <;> norm_num
              rcases le_total tau.re (9/320 : ℝ) with hx3222320 | hx3222320
              · rcases le_total tau.im (25/64 : ℝ) with hy3222320 | hy3222320
                · have hs32223200 : InSquare (17/640) (249/640) (1/640) tau := by
                    convert childLL hs3222320 hx3222320 hy3222320 using 1 <;> norm_num
                  exact Batch0446.cell3568.sound htau (by
                    simp only [Batch0446.cell3568, Batch0446.tau3568, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32223200 (by positivity) using 1 <;> norm_num)
                · have hs32223202 : InSquare (17/640) (251/640) (1/640) tau := by
                    convert childUL hs3222320 hx3222320 hy3222320 using 1 <;> norm_num
                  exact Batch0446.cell3570.sound htau (by
                    simp only [Batch0446.cell3570, Batch0446.tau3570, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32223202 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (25/64 : ℝ) with hy3222320 | hy3222320
                · have hs32223201 : InSquare (19/640) (249/640) (1/640) tau := by
                    convert childLR hs3222320 hx3222320 hy3222320 using 1 <;> norm_num
                  exact Batch0446.cell3569.sound htau (by
                    simp only [Batch0446.cell3569, Batch0446.tau3569, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32223201 (by positivity) using 1 <;> norm_num)
                · have hs32223203 : InSquare (19/640) (251/640) (1/640) tau := by
                    convert childUR hs3222320 hx3222320 hy3222320 using 1 <;> norm_num
                  exact Batch0446.cell3571.sound htau (by
                    simp only [Batch0446.cell3571, Batch0446.tau3571, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32223203 (by positivity) using 1 <;> norm_num)
            · have hs3222322 : InSquare (9/320) (127/320) (1/320) tau := by
                convert childUL hs322232 hx322232 hy322232 using 1 <;> norm_num
              rcases le_total tau.re (9/320 : ℝ) with hx3222322 | hx3222322
              · rcases le_total tau.im (127/320 : ℝ) with hy3222322 | hy3222322
                · have hs32223220 : InSquare (17/640) (253/640) (1/640) tau := by
                    convert childLL hs3222322 hx3222322 hy3222322 using 1 <;> norm_num
                  exact Batch0447.cell3576.sound htau (by
                    simp only [Batch0447.cell3576, Batch0447.tau3576, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32223220 (by positivity) using 1 <;> norm_num)
                · have hs32223222 : InSquare (17/640) (51/128) (1/640) tau := by
                    convert childUL hs3222322 hx3222322 hy3222322 using 1 <;> norm_num
                  exact Batch0447.cell3578.sound htau (by
                    simp only [Batch0447.cell3578, Batch0447.tau3578, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32223222 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (127/320 : ℝ) with hy3222322 | hy3222322
                · have hs32223221 : InSquare (19/640) (253/640) (1/640) tau := by
                    convert childLR hs3222322 hx3222322 hy3222322 using 1 <;> norm_num
                  exact Batch0447.cell3577.sound htau (by
                    simp only [Batch0447.cell3577, Batch0447.tau3577, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32223221 (by positivity) using 1 <;> norm_num)
                · have hs32223223 : InSquare (19/640) (51/128) (1/640) tau := by
                    convert childUR hs3222322 hx3222322 hy3222322 using 1 <;> norm_num
                  exact Batch0447.cell3579.sound htau (by
                    simp only [Batch0447.cell3579, Batch0447.tau3579, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32223223 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (63/160 : ℝ) with hy322232 | hy322232
            · have hs3222321 : InSquare (11/320) (25/64) (1/320) tau := by
                convert childLR hs322232 hx322232 hy322232 using 1 <;> norm_num
              rcases le_total tau.re (11/320 : ℝ) with hx3222321 | hx3222321
              · rcases le_total tau.im (25/64 : ℝ) with hy3222321 | hy3222321
                · have hs32223210 : InSquare (21/640) (249/640) (1/640) tau := by
                    convert childLL hs3222321 hx3222321 hy3222321 using 1 <;> norm_num
                  exact Batch0446.cell3572.sound htau (by
                    simp only [Batch0446.cell3572, Batch0446.tau3572, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32223210 (by positivity) using 1 <;> norm_num)
                · have hs32223212 : InSquare (21/640) (251/640) (1/640) tau := by
                    convert childUL hs3222321 hx3222321 hy3222321 using 1 <;> norm_num
                  exact Batch0446.cell3574.sound htau (by
                    simp only [Batch0446.cell3574, Batch0446.tau3574, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32223212 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (25/64 : ℝ) with hy3222321 | hy3222321
                · have hs32223211 : InSquare (23/640) (249/640) (1/640) tau := by
                    convert childLR hs3222321 hx3222321 hy3222321 using 1 <;> norm_num
                  exact Batch0446.cell3573.sound htau (by
                    simp only [Batch0446.cell3573, Batch0446.tau3573, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32223211 (by positivity) using 1 <;> norm_num)
                · have hs32223213 : InSquare (23/640) (251/640) (1/640) tau := by
                    convert childUR hs3222321 hx3222321 hy3222321 using 1 <;> norm_num
                  exact Batch0446.cell3575.sound htau (by
                    simp only [Batch0446.cell3575, Batch0446.tau3575, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32223213 (by positivity) using 1 <;> norm_num)
            · have hs3222323 : InSquare (11/320) (127/320) (1/320) tau := by
                convert childUR hs322232 hx322232 hy322232 using 1 <;> norm_num
              rcases le_total tau.re (11/320 : ℝ) with hx3222323 | hx3222323
              · rcases le_total tau.im (127/320 : ℝ) with hy3222323 | hy3222323
                · have hs32223230 : InSquare (21/640) (253/640) (1/640) tau := by
                    convert childLL hs3222323 hx3222323 hy3222323 using 1 <;> norm_num
                  exact Batch0447.cell3580.sound htau (by
                    simp only [Batch0447.cell3580, Batch0447.tau3580, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32223230 (by positivity) using 1 <;> norm_num)
                · have hs32223232 : InSquare (21/640) (51/128) (1/640) tau := by
                    convert childUL hs3222323 hx3222323 hy3222323 using 1 <;> norm_num
                  exact Batch0447.cell3582.sound htau (by
                    simp only [Batch0447.cell3582, Batch0447.tau3582, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32223232 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (127/320 : ℝ) with hy3222323 | hy3222323
                · have hs32223231 : InSquare (23/640) (253/640) (1/640) tau := by
                    convert childLR hs3222323 hx3222323 hy3222323 using 1 <;> norm_num
                  exact Batch0447.cell3581.sound htau (by
                    simp only [Batch0447.cell3581, Batch0447.tau3581, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32223231 (by positivity) using 1 <;> norm_num)
                · have hs32223233 : InSquare (23/640) (51/128) (1/640) tau := by
                    convert childUR hs3222323 hx3222323 hy3222323 using 1 <;> norm_num
                  exact Batch0447.cell3583.sound htau (by
                    simp only [Batch0447.cell3583, Batch0447.tau3583, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32223233 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (31/80 : ℝ) with hy32223 | hy32223
        · have hs322231 : InSquare (7/160) (61/160) (1/160) tau := by
            convert childLR hs32223 hx32223 hy32223 using 1 <;> norm_num
          rcases le_total tau.re (7/160 : ℝ) with hx322231 | hx322231
          · rcases le_total tau.im (61/160 : ℝ) with hy322231 | hy322231
            · have hs3222310 : InSquare (13/320) (121/320) (1/320) tau := by
                convert childLL hs322231 hx322231 hy322231 using 1 <;> norm_num
              exact Batch0284.cell2275.sound htau (by
                simp only [Batch0284.cell2275, Batch0284.tau2275, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3222310 (by positivity) using 1 <;> norm_num)
            · have hs3222312 : InSquare (13/320) (123/320) (1/320) tau := by
                convert childUL hs322231 hx322231 hy322231 using 1 <;> norm_num
              rcases le_total tau.re (13/320 : ℝ) with hx3222312 | hx3222312
              · rcases le_total tau.im (123/320 : ℝ) with hy3222312 | hy3222312
                · have hs32223120 : InSquare (5/128) (49/128) (1/640) tau := by
                    convert childLL hs3222312 hx3222312 hy3222312 using 1 <;> norm_num
                  exact Batch0445.cell3560.sound htau (by
                    simp only [Batch0445.cell3560, Batch0445.tau3560, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32223120 (by positivity) using 1 <;> norm_num)
                · have hs32223122 : InSquare (5/128) (247/640) (1/640) tau := by
                    convert childUL hs3222312 hx3222312 hy3222312 using 1 <;> norm_num
                  exact Batch0445.cell3562.sound htau (by
                    simp only [Batch0445.cell3562, Batch0445.tau3562, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32223122 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (123/320 : ℝ) with hy3222312 | hy3222312
                · have hs32223121 : InSquare (27/640) (49/128) (1/640) tau := by
                    convert childLR hs3222312 hx3222312 hy3222312 using 1 <;> norm_num
                  exact Batch0445.cell3561.sound htau (by
                    simp only [Batch0445.cell3561, Batch0445.tau3561, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32223121 (by positivity) using 1 <;> norm_num)
                · have hs32223123 : InSquare (27/640) (247/640) (1/640) tau := by
                    convert childUR hs3222312 hx3222312 hy3222312 using 1 <;> norm_num
                  exact Batch0445.cell3563.sound htau (by
                    simp only [Batch0445.cell3563, Batch0445.tau3563, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32223123 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (61/160 : ℝ) with hy322231 | hy322231
            · have hs3222311 : InSquare (3/64) (121/320) (1/320) tau := by
                convert childLR hs322231 hx322231 hy322231 using 1 <;> norm_num
              exact Batch0284.cell2276.sound htau (by
                simp only [Batch0284.cell2276, Batch0284.tau2276, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3222311 (by positivity) using 1 <;> norm_num)
            · have hs3222313 : InSquare (3/64) (123/320) (1/320) tau := by
                convert childUR hs322231 hx322231 hy322231 using 1 <;> norm_num
              rcases le_total tau.re (3/64 : ℝ) with hx3222313 | hx3222313
              · rcases le_total tau.im (123/320 : ℝ) with hy3222313 | hy3222313
                · have hs32223130 : InSquare (29/640) (49/128) (1/640) tau := by
                    convert childLL hs3222313 hx3222313 hy3222313 using 1 <;> norm_num
                  exact Batch0445.cell3564.sound htau (by
                    simp only [Batch0445.cell3564, Batch0445.tau3564, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32223130 (by positivity) using 1 <;> norm_num)
                · have hs32223132 : InSquare (29/640) (247/640) (1/640) tau := by
                    convert childUL hs3222313 hx3222313 hy3222313 using 1 <;> norm_num
                  exact Batch0445.cell3566.sound htau (by
                    simp only [Batch0445.cell3566, Batch0445.tau3566, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32223132 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (123/320 : ℝ) with hy3222313 | hy3222313
                · have hs32223131 : InSquare (31/640) (49/128) (1/640) tau := by
                    convert childLR hs3222313 hx3222313 hy3222313 using 1 <;> norm_num
                  exact Batch0445.cell3565.sound htau (by
                    simp only [Batch0445.cell3565, Batch0445.tau3565, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32223131 (by positivity) using 1 <;> norm_num)
                · have hs32223133 : InSquare (31/640) (247/640) (1/640) tau := by
                    convert childUR hs3222313 hx3222313 hy3222313 using 1 <;> norm_num
                  exact Batch0445.cell3567.sound htau (by
                    simp only [Batch0445.cell3567, Batch0445.tau3567, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32223133 (by positivity) using 1 <;> norm_num)
        · have hs322233 : InSquare (7/160) (63/160) (1/160) tau := by
            convert childUR hs32223 hx32223 hy32223 using 1 <;> norm_num
          rcases le_total tau.re (7/160 : ℝ) with hx322233 | hx322233
          · rcases le_total tau.im (63/160 : ℝ) with hy322233 | hy322233
            · have hs3222330 : InSquare (13/320) (25/64) (1/320) tau := by
                convert childLL hs322233 hx322233 hy322233 using 1 <;> norm_num
              rcases le_total tau.re (13/320 : ℝ) with hx3222330 | hx3222330
              · rcases le_total tau.im (25/64 : ℝ) with hy3222330 | hy3222330
                · have hs32223300 : InSquare (5/128) (249/640) (1/640) tau := by
                    convert childLL hs3222330 hx3222330 hy3222330 using 1 <;> norm_num
                  exact Batch0448.cell3584.sound htau (by
                    simp only [Batch0448.cell3584, Batch0448.tau3584, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32223300 (by positivity) using 1 <;> norm_num)
                · have hs32223302 : InSquare (5/128) (251/640) (1/640) tau := by
                    convert childUL hs3222330 hx3222330 hy3222330 using 1 <;> norm_num
                  exact Batch0448.cell3586.sound htau (by
                    simp only [Batch0448.cell3586, Batch0448.tau3586, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32223302 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (25/64 : ℝ) with hy3222330 | hy3222330
                · have hs32223301 : InSquare (27/640) (249/640) (1/640) tau := by
                    convert childLR hs3222330 hx3222330 hy3222330 using 1 <;> norm_num
                  exact Batch0448.cell3585.sound htau (by
                    simp only [Batch0448.cell3585, Batch0448.tau3585, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32223301 (by positivity) using 1 <;> norm_num)
                · have hs32223303 : InSquare (27/640) (251/640) (1/640) tau := by
                    convert childUR hs3222330 hx3222330 hy3222330 using 1 <;> norm_num
                  exact Batch0448.cell3587.sound htau (by
                    simp only [Batch0448.cell3587, Batch0448.tau3587, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32223303 (by positivity) using 1 <;> norm_num)
            · have hs3222332 : InSquare (13/320) (127/320) (1/320) tau := by
                convert childUL hs322233 hx322233 hy322233 using 1 <;> norm_num
              rcases le_total tau.re (13/320 : ℝ) with hx3222332 | hx3222332
              · rcases le_total tau.im (127/320 : ℝ) with hy3222332 | hy3222332
                · have hs32223320 : InSquare (5/128) (253/640) (1/640) tau := by
                    convert childLL hs3222332 hx3222332 hy3222332 using 1 <;> norm_num
                  exact Batch0449.cell3592.sound htau (by
                    simp only [Batch0449.cell3592, Batch0449.tau3592, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32223320 (by positivity) using 1 <;> norm_num)
                · have hs32223322 : InSquare (5/128) (51/128) (1/640) tau := by
                    convert childUL hs3222332 hx3222332 hy3222332 using 1 <;> norm_num
                  exact Batch0449.cell3594.sound htau (by
                    simp only [Batch0449.cell3594, Batch0449.tau3594, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32223322 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (127/320 : ℝ) with hy3222332 | hy3222332
                · have hs32223321 : InSquare (27/640) (253/640) (1/640) tau := by
                    convert childLR hs3222332 hx3222332 hy3222332 using 1 <;> norm_num
                  exact Batch0449.cell3593.sound htau (by
                    simp only [Batch0449.cell3593, Batch0449.tau3593, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32223321 (by positivity) using 1 <;> norm_num)
                · have hs32223323 : InSquare (27/640) (51/128) (1/640) tau := by
                    convert childUR hs3222332 hx3222332 hy3222332 using 1 <;> norm_num
                  exact Batch0449.cell3595.sound htau (by
                    simp only [Batch0449.cell3595, Batch0449.tau3595, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32223323 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (63/160 : ℝ) with hy322233 | hy322233
            · have hs3222331 : InSquare (3/64) (25/64) (1/320) tau := by
                convert childLR hs322233 hx322233 hy322233 using 1 <;> norm_num
              rcases le_total tau.re (3/64 : ℝ) with hx3222331 | hx3222331
              · rcases le_total tau.im (25/64 : ℝ) with hy3222331 | hy3222331
                · have hs32223310 : InSquare (29/640) (249/640) (1/640) tau := by
                    convert childLL hs3222331 hx3222331 hy3222331 using 1 <;> norm_num
                  exact Batch0448.cell3588.sound htau (by
                    simp only [Batch0448.cell3588, Batch0448.tau3588, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32223310 (by positivity) using 1 <;> norm_num)
                · have hs32223312 : InSquare (29/640) (251/640) (1/640) tau := by
                    convert childUL hs3222331 hx3222331 hy3222331 using 1 <;> norm_num
                  exact Batch0448.cell3590.sound htau (by
                    simp only [Batch0448.cell3590, Batch0448.tau3590, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32223312 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (25/64 : ℝ) with hy3222331 | hy3222331
                · have hs32223311 : InSquare (31/640) (249/640) (1/640) tau := by
                    convert childLR hs3222331 hx3222331 hy3222331 using 1 <;> norm_num
                  exact Batch0448.cell3589.sound htau (by
                    simp only [Batch0448.cell3589, Batch0448.tau3589, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32223311 (by positivity) using 1 <;> norm_num)
                · have hs32223313 : InSquare (31/640) (251/640) (1/640) tau := by
                    convert childUR hs3222331 hx3222331 hy3222331 using 1 <;> norm_num
                  exact Batch0448.cell3591.sound htau (by
                    simp only [Batch0448.cell3591, Batch0448.tau3591, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32223313 (by positivity) using 1 <;> norm_num)
            · have hs3222333 : InSquare (3/64) (127/320) (1/320) tau := by
                convert childUR hs322233 hx322233 hy322233 using 1 <;> norm_num
              rcases le_total tau.re (3/64 : ℝ) with hx3222333 | hx3222333
              · rcases le_total tau.im (127/320 : ℝ) with hy3222333 | hy3222333
                · have hs32223330 : InSquare (29/640) (253/640) (1/640) tau := by
                    convert childLL hs3222333 hx3222333 hy3222333 using 1 <;> norm_num
                  exact Batch0449.cell3596.sound htau (by
                    simp only [Batch0449.cell3596, Batch0449.tau3596, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32223330 (by positivity) using 1 <;> norm_num)
                · have hs32223332 : InSquare (29/640) (51/128) (1/640) tau := by
                    convert childUL hs3222333 hx3222333 hy3222333 using 1 <;> norm_num
                  exact Batch0449.cell3598.sound htau (by
                    simp only [Batch0449.cell3598, Batch0449.tau3598, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32223332 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (127/320 : ℝ) with hy3222333 | hy3222333
                · have hs32223331 : InSquare (31/640) (253/640) (1/640) tau := by
                    convert childLR hs3222333 hx3222333 hy3222333 using 1 <;> norm_num
                  exact Batch0449.cell3597.sound htau (by
                    simp only [Batch0449.cell3597, Batch0449.tau3597, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32223331 (by positivity) using 1 <;> norm_num)
                · have hs32223333 : InSquare (31/640) (51/128) (1/640) tau := by
                    convert childUR hs3222333 hx3222333 hy3222333 using 1 <;> norm_num
                  exact Batch0449.cell3599.sound htau (by
                    simp only [Batch0449.cell3599, Batch0449.tau3599, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32223333 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3222
