import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0147
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0148
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0303
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0304
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0305

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3302

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (9/40) (11/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (9/40 : ℝ) with hx3302 | hx3302
  · rcases le_total tau.im (11/40 : ℝ) with hy3302 | hy3302
    · have hs33020 : InSquare (17/80) (21/80) (1/80) tau := by
        convert childLL hs hx3302 hy3302 using 1 <;> norm_num
      rcases le_total tau.re (17/80 : ℝ) with hx33020 | hx33020
      · rcases le_total tau.im (21/80 : ℝ) with hy33020 | hy33020
        · have hs330200 : InSquare (33/160) (41/160) (1/160) tau := by
            convert childLL hs33020 hx33020 hy33020 using 1 <;> norm_num
          exact Batch0147.cell1182.sound htau (by
            simp only [Batch0147.cell1182, Batch0147.tau1182, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs330200 (by positivity) using 1 <;> norm_num)
        · have hs330202 : InSquare (33/160) (43/160) (1/160) tau := by
            convert childUL hs33020 hx33020 hy33020 using 1 <;> norm_num
          exact Batch0148.cell1184.sound htau (by
            simp only [Batch0148.cell1184, Batch0148.tau1184, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs330202 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (21/80 : ℝ) with hy33020 | hy33020
        · have hs330201 : InSquare (7/32) (41/160) (1/160) tau := by
            convert childLR hs33020 hx33020 hy33020 using 1 <;> norm_num
          exact Batch0147.cell1183.sound htau (by
            simp only [Batch0147.cell1183, Batch0147.tau1183, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs330201 (by positivity) using 1 <;> norm_num)
        · have hs330203 : InSquare (7/32) (43/160) (1/160) tau := by
            convert childUR hs33020 hx33020 hy33020 using 1 <;> norm_num
          exact Batch0148.cell1185.sound htau (by
            simp only [Batch0148.cell1185, Batch0148.tau1185, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs330203 (by positivity) using 1 <;> norm_num)
    · have hs33022 : InSquare (17/80) (23/80) (1/80) tau := by
        convert childUL hs hx3302 hy3302 using 1 <;> norm_num
      rcases le_total tau.re (17/80 : ℝ) with hx33022 | hx33022
      · rcases le_total tau.im (23/80 : ℝ) with hy33022 | hy33022
        · have hs330220 : InSquare (33/160) (9/32) (1/160) tau := by
            convert childLL hs33022 hx33022 hy33022 using 1 <;> norm_num
          exact Batch0148.cell1190.sound htau (by
            simp only [Batch0148.cell1190, Batch0148.tau1190, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs330220 (by positivity) using 1 <;> norm_num)
        · have hs330222 : InSquare (33/160) (47/160) (1/160) tau := by
            convert childUL hs33022 hx33022 hy33022 using 1 <;> norm_num
          rcases le_total tau.re (33/160 : ℝ) with hx330222 | hx330222
          · rcases le_total tau.im (47/160 : ℝ) with hy330222 | hy330222
            · have hs3302220 : InSquare (13/64) (93/320) (1/320) tau := by
                convert childLL hs330222 hx330222 hy330222 using 1 <;> norm_num
              exact Batch0303.cell2424.sound htau (by
                simp only [Batch0303.cell2424, Batch0303.tau2424, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3302220 (by positivity) using 1 <;> norm_num)
            · have hs3302222 : InSquare (13/64) (19/64) (1/320) tau := by
                convert childUL hs330222 hx330222 hy330222 using 1 <;> norm_num
              exact Batch0303.cell2426.sound htau (by
                simp only [Batch0303.cell2426, Batch0303.tau2426, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3302222 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (47/160 : ℝ) with hy330222 | hy330222
            · have hs3302221 : InSquare (67/320) (93/320) (1/320) tau := by
                convert childLR hs330222 hx330222 hy330222 using 1 <;> norm_num
              exact Batch0303.cell2425.sound htau (by
                simp only [Batch0303.cell2425, Batch0303.tau2425, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3302221 (by positivity) using 1 <;> norm_num)
            · have hs3302223 : InSquare (67/320) (19/64) (1/320) tau := by
                convert childUR hs330222 hx330222 hy330222 using 1 <;> norm_num
              exact Batch0303.cell2427.sound htau (by
                simp only [Batch0303.cell2427, Batch0303.tau2427, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3302223 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (23/80 : ℝ) with hy33022 | hy33022
        · have hs330221 : InSquare (7/32) (9/32) (1/160) tau := by
            convert childLR hs33022 hx33022 hy33022 using 1 <;> norm_num
          exact Batch0148.cell1191.sound htau (by
            simp only [Batch0148.cell1191, Batch0148.tau1191, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs330221 (by positivity) using 1 <;> norm_num)
        · have hs330223 : InSquare (7/32) (47/160) (1/160) tau := by
            convert childUR hs33022 hx33022 hy33022 using 1 <;> norm_num
          rcases le_total tau.re (7/32 : ℝ) with hx330223 | hx330223
          · rcases le_total tau.im (47/160 : ℝ) with hy330223 | hy330223
            · have hs3302230 : InSquare (69/320) (93/320) (1/320) tau := by
                convert childLL hs330223 hx330223 hy330223 using 1 <;> norm_num
              exact Batch0303.cell2428.sound htau (by
                simp only [Batch0303.cell2428, Batch0303.tau2428, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3302230 (by positivity) using 1 <;> norm_num)
            · have hs3302232 : InSquare (69/320) (19/64) (1/320) tau := by
                convert childUL hs330223 hx330223 hy330223 using 1 <;> norm_num
              exact Batch0303.cell2430.sound htau (by
                simp only [Batch0303.cell2430, Batch0303.tau2430, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3302232 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (47/160 : ℝ) with hy330223 | hy330223
            · have hs3302231 : InSquare (71/320) (93/320) (1/320) tau := by
                convert childLR hs330223 hx330223 hy330223 using 1 <;> norm_num
              exact Batch0303.cell2429.sound htau (by
                simp only [Batch0303.cell2429, Batch0303.tau2429, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3302231 (by positivity) using 1 <;> norm_num)
            · have hs3302233 : InSquare (71/320) (19/64) (1/320) tau := by
                convert childUR hs330223 hx330223 hy330223 using 1 <;> norm_num
              exact Batch0303.cell2431.sound htau (by
                simp only [Batch0303.cell2431, Batch0303.tau2431, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3302233 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (11/40 : ℝ) with hy3302 | hy3302
    · have hs33021 : InSquare (19/80) (21/80) (1/80) tau := by
        convert childLR hs hx3302 hy3302 using 1 <;> norm_num
      rcases le_total tau.re (19/80 : ℝ) with hx33021 | hx33021
      · rcases le_total tau.im (21/80 : ℝ) with hy33021 | hy33021
        · have hs330210 : InSquare (37/160) (41/160) (1/160) tau := by
            convert childLL hs33021 hx33021 hy33021 using 1 <;> norm_num
          exact Batch0148.cell1186.sound htau (by
            simp only [Batch0148.cell1186, Batch0148.tau1186, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs330210 (by positivity) using 1 <;> norm_num)
        · have hs330212 : InSquare (37/160) (43/160) (1/160) tau := by
            convert childUL hs33021 hx33021 hy33021 using 1 <;> norm_num
          exact Batch0148.cell1188.sound htau (by
            simp only [Batch0148.cell1188, Batch0148.tau1188, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs330212 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (21/80 : ℝ) with hy33021 | hy33021
        · have hs330211 : InSquare (39/160) (41/160) (1/160) tau := by
            convert childLR hs33021 hx33021 hy33021 using 1 <;> norm_num
          exact Batch0148.cell1187.sound htau (by
            simp only [Batch0148.cell1187, Batch0148.tau1187, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs330211 (by positivity) using 1 <;> norm_num)
        · have hs330213 : InSquare (39/160) (43/160) (1/160) tau := by
            convert childUR hs33021 hx33021 hy33021 using 1 <;> norm_num
          exact Batch0148.cell1189.sound htau (by
            simp only [Batch0148.cell1189, Batch0148.tau1189, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs330213 (by positivity) using 1 <;> norm_num)
    · have hs33023 : InSquare (19/80) (23/80) (1/80) tau := by
        convert childUR hs hx3302 hy3302 using 1 <;> norm_num
      rcases le_total tau.re (19/80 : ℝ) with hx33023 | hx33023
      · rcases le_total tau.im (23/80 : ℝ) with hy33023 | hy33023
        · have hs330230 : InSquare (37/160) (9/32) (1/160) tau := by
            convert childLL hs33023 hx33023 hy33023 using 1 <;> norm_num
          rcases le_total tau.re (37/160 : ℝ) with hx330230 | hx330230
          · rcases le_total tau.im (9/32 : ℝ) with hy330230 | hy330230
            · have hs3302300 : InSquare (73/320) (89/320) (1/320) tau := by
                convert childLL hs330230 hx330230 hy330230 using 1 <;> norm_num
              exact Batch0304.cell2432.sound htau (by
                simp only [Batch0304.cell2432, Batch0304.tau2432, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3302300 (by positivity) using 1 <;> norm_num)
            · have hs3302302 : InSquare (73/320) (91/320) (1/320) tau := by
                convert childUL hs330230 hx330230 hy330230 using 1 <;> norm_num
              exact Batch0304.cell2434.sound htau (by
                simp only [Batch0304.cell2434, Batch0304.tau2434, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3302302 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (9/32 : ℝ) with hy330230 | hy330230
            · have hs3302301 : InSquare (15/64) (89/320) (1/320) tau := by
                convert childLR hs330230 hx330230 hy330230 using 1 <;> norm_num
              exact Batch0304.cell2433.sound htau (by
                simp only [Batch0304.cell2433, Batch0304.tau2433, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3302301 (by positivity) using 1 <;> norm_num)
            · have hs3302303 : InSquare (15/64) (91/320) (1/320) tau := by
                convert childUR hs330230 hx330230 hy330230 using 1 <;> norm_num
              exact Batch0304.cell2435.sound htau (by
                simp only [Batch0304.cell2435, Batch0304.tau2435, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3302303 (by positivity) using 1 <;> norm_num)
        · have hs330232 : InSquare (37/160) (47/160) (1/160) tau := by
            convert childUL hs33023 hx33023 hy33023 using 1 <;> norm_num
          rcases le_total tau.re (37/160 : ℝ) with hx330232 | hx330232
          · rcases le_total tau.im (47/160 : ℝ) with hy330232 | hy330232
            · have hs3302320 : InSquare (73/320) (93/320) (1/320) tau := by
                convert childLL hs330232 hx330232 hy330232 using 1 <;> norm_num
              exact Batch0305.cell2440.sound htau (by
                simp only [Batch0305.cell2440, Batch0305.tau2440, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3302320 (by positivity) using 1 <;> norm_num)
            · have hs3302322 : InSquare (73/320) (19/64) (1/320) tau := by
                convert childUL hs330232 hx330232 hy330232 using 1 <;> norm_num
              exact Batch0305.cell2442.sound htau (by
                simp only [Batch0305.cell2442, Batch0305.tau2442, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3302322 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (47/160 : ℝ) with hy330232 | hy330232
            · have hs3302321 : InSquare (15/64) (93/320) (1/320) tau := by
                convert childLR hs330232 hx330232 hy330232 using 1 <;> norm_num
              exact Batch0305.cell2441.sound htau (by
                simp only [Batch0305.cell2441, Batch0305.tau2441, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3302321 (by positivity) using 1 <;> norm_num)
            · have hs3302323 : InSquare (15/64) (19/64) (1/320) tau := by
                convert childUR hs330232 hx330232 hy330232 using 1 <;> norm_num
              exact Batch0305.cell2443.sound htau (by
                simp only [Batch0305.cell2443, Batch0305.tau2443, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3302323 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (23/80 : ℝ) with hy33023 | hy33023
        · have hs330231 : InSquare (39/160) (9/32) (1/160) tau := by
            convert childLR hs33023 hx33023 hy33023 using 1 <;> norm_num
          rcases le_total tau.re (39/160 : ℝ) with hx330231 | hx330231
          · rcases le_total tau.im (9/32 : ℝ) with hy330231 | hy330231
            · have hs3302310 : InSquare (77/320) (89/320) (1/320) tau := by
                convert childLL hs330231 hx330231 hy330231 using 1 <;> norm_num
              exact Batch0304.cell2436.sound htau (by
                simp only [Batch0304.cell2436, Batch0304.tau2436, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3302310 (by positivity) using 1 <;> norm_num)
            · have hs3302312 : InSquare (77/320) (91/320) (1/320) tau := by
                convert childUL hs330231 hx330231 hy330231 using 1 <;> norm_num
              exact Batch0304.cell2438.sound htau (by
                simp only [Batch0304.cell2438, Batch0304.tau2438, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3302312 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (9/32 : ℝ) with hy330231 | hy330231
            · have hs3302311 : InSquare (79/320) (89/320) (1/320) tau := by
                convert childLR hs330231 hx330231 hy330231 using 1 <;> norm_num
              exact Batch0304.cell2437.sound htau (by
                simp only [Batch0304.cell2437, Batch0304.tau2437, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3302311 (by positivity) using 1 <;> norm_num)
            · have hs3302313 : InSquare (79/320) (91/320) (1/320) tau := by
                convert childUR hs330231 hx330231 hy330231 using 1 <;> norm_num
              exact Batch0304.cell2439.sound htau (by
                simp only [Batch0304.cell2439, Batch0304.tau2439, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3302313 (by positivity) using 1 <;> norm_num)
        · have hs330233 : InSquare (39/160) (47/160) (1/160) tau := by
            convert childUR hs33023 hx33023 hy33023 using 1 <;> norm_num
          rcases le_total tau.re (39/160 : ℝ) with hx330233 | hx330233
          · rcases le_total tau.im (47/160 : ℝ) with hy330233 | hy330233
            · have hs3302330 : InSquare (77/320) (93/320) (1/320) tau := by
                convert childLL hs330233 hx330233 hy330233 using 1 <;> norm_num
              exact Batch0305.cell2444.sound htau (by
                simp only [Batch0305.cell2444, Batch0305.tau2444, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3302330 (by positivity) using 1 <;> norm_num)
            · have hs3302332 : InSquare (77/320) (19/64) (1/320) tau := by
                convert childUL hs330233 hx330233 hy330233 using 1 <;> norm_num
              exact Batch0305.cell2446.sound htau (by
                simp only [Batch0305.cell2446, Batch0305.tau2446, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3302332 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (47/160 : ℝ) with hy330233 | hy330233
            · have hs3302331 : InSquare (79/320) (93/320) (1/320) tau := by
                convert childLR hs330233 hx330233 hy330233 using 1 <;> norm_num
              exact Batch0305.cell2445.sound htau (by
                simp only [Batch0305.cell2445, Batch0305.tau2445, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3302331 (by positivity) using 1 <;> norm_num)
            · have hs3302333 : InSquare (79/320) (19/64) (1/320) tau := by
                convert childUR hs330233 hx330233 hy330233 using 1 <;> norm_num
              exact Batch0305.cell2447.sound htau (by
                simp only [Batch0305.cell2447, Batch0305.tau2447, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3302333 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3302
