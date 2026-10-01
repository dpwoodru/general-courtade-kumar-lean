import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0050
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0185
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0186
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0187
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0188
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0189
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0190
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0351
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0352
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0353
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0354
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0355
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0356
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0357
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0358
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0359
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0360

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0111

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-1/40) (-3/8) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (-1/40 : ℝ) with hx0111 | hx0111
  · rcases le_total tau.im (-3/8 : ℝ) with hy0111 | hy0111
    · have hs01110 : InSquare (-3/80) (-31/80) (1/80) tau := by
        convert childLL hs hx0111 hy0111 using 1 <;> norm_num
      rcases le_total tau.re (-3/80 : ℝ) with hx01110 | hx01110
      · rcases le_total tau.im (-31/80 : ℝ) with hy01110 | hy01110
        · have hs011100 : InSquare (-7/160) (-63/160) (1/160) tau := by
            convert childLL hs01110 hx01110 hy01110 using 1 <;> norm_num
          rcases le_total tau.re (-7/160 : ℝ) with hx011100 | hx011100
          · rcases le_total tau.im (-63/160 : ℝ) with hy011100 | hy011100
            · have hs0111000 : InSquare (-3/64) (-127/320) (1/320) tau := by
                convert childLL hs011100 hx011100 hy011100 using 1 <;> norm_num
              rcases le_total tau.re (-3/64 : ℝ) with hx0111000 | hx0111000
              · rcases le_total tau.im (-127/320 : ℝ) with hy0111000 | hy0111000
                · have hs01110000 : InSquare (-31/640) (-51/128) (1/640) tau := by
                    convert childLL hs0111000 hx0111000 hy0111000 using 1 <;> norm_num
                  exact Batch0351.cell2808.sound htau (by
                    simp only [Batch0351.cell2808, Batch0351.tau2808, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01110000 (by positivity) using 1 <;> norm_num)
                · have hs01110002 : InSquare (-31/640) (-253/640) (1/640) tau := by
                    convert childUL hs0111000 hx0111000 hy0111000 using 1 <;> norm_num
                  exact Batch0351.cell2810.sound htau (by
                    simp only [Batch0351.cell2810, Batch0351.tau2810, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01110002 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-127/320 : ℝ) with hy0111000 | hy0111000
                · have hs01110001 : InSquare (-29/640) (-51/128) (1/640) tau := by
                    convert childLR hs0111000 hx0111000 hy0111000 using 1 <;> norm_num
                  exact Batch0351.cell2809.sound htau (by
                    simp only [Batch0351.cell2809, Batch0351.tau2809, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01110001 (by positivity) using 1 <;> norm_num)
                · have hs01110003 : InSquare (-29/640) (-253/640) (1/640) tau := by
                    convert childUR hs0111000 hx0111000 hy0111000 using 1 <;> norm_num
                  exact Batch0351.cell2811.sound htau (by
                    simp only [Batch0351.cell2811, Batch0351.tau2811, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01110003 (by positivity) using 1 <;> norm_num)
            · have hs0111002 : InSquare (-3/64) (-25/64) (1/320) tau := by
                convert childUL hs011100 hx011100 hy011100 using 1 <;> norm_num
              rcases le_total tau.re (-3/64 : ℝ) with hx0111002 | hx0111002
              · rcases le_total tau.im (-25/64 : ℝ) with hy0111002 | hy0111002
                · have hs01110020 : InSquare (-31/640) (-251/640) (1/640) tau := by
                    convert childLL hs0111002 hx0111002 hy0111002 using 1 <;> norm_num
                  exact Batch0352.cell2816.sound htau (by
                    simp only [Batch0352.cell2816, Batch0352.tau2816, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01110020 (by positivity) using 1 <;> norm_num)
                · have hs01110022 : InSquare (-31/640) (-249/640) (1/640) tau := by
                    convert childUL hs0111002 hx0111002 hy0111002 using 1 <;> norm_num
                  exact Batch0352.cell2818.sound htau (by
                    simp only [Batch0352.cell2818, Batch0352.tau2818, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01110022 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-25/64 : ℝ) with hy0111002 | hy0111002
                · have hs01110021 : InSquare (-29/640) (-251/640) (1/640) tau := by
                    convert childLR hs0111002 hx0111002 hy0111002 using 1 <;> norm_num
                  exact Batch0352.cell2817.sound htau (by
                    simp only [Batch0352.cell2817, Batch0352.tau2817, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01110021 (by positivity) using 1 <;> norm_num)
                · have hs01110023 : InSquare (-29/640) (-249/640) (1/640) tau := by
                    convert childUR hs0111002 hx0111002 hy0111002 using 1 <;> norm_num
                  exact Batch0352.cell2819.sound htau (by
                    simp only [Batch0352.cell2819, Batch0352.tau2819, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01110023 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-63/160 : ℝ) with hy011100 | hy011100
            · have hs0111001 : InSquare (-13/320) (-127/320) (1/320) tau := by
                convert childLR hs011100 hx011100 hy011100 using 1 <;> norm_num
              rcases le_total tau.re (-13/320 : ℝ) with hx0111001 | hx0111001
              · rcases le_total tau.im (-127/320 : ℝ) with hy0111001 | hy0111001
                · have hs01110010 : InSquare (-27/640) (-51/128) (1/640) tau := by
                    convert childLL hs0111001 hx0111001 hy0111001 using 1 <;> norm_num
                  exact Batch0351.cell2812.sound htau (by
                    simp only [Batch0351.cell2812, Batch0351.tau2812, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01110010 (by positivity) using 1 <;> norm_num)
                · have hs01110012 : InSquare (-27/640) (-253/640) (1/640) tau := by
                    convert childUL hs0111001 hx0111001 hy0111001 using 1 <;> norm_num
                  exact Batch0351.cell2814.sound htau (by
                    simp only [Batch0351.cell2814, Batch0351.tau2814, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01110012 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-127/320 : ℝ) with hy0111001 | hy0111001
                · have hs01110011 : InSquare (-5/128) (-51/128) (1/640) tau := by
                    convert childLR hs0111001 hx0111001 hy0111001 using 1 <;> norm_num
                  exact Batch0351.cell2813.sound htau (by
                    simp only [Batch0351.cell2813, Batch0351.tau2813, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01110011 (by positivity) using 1 <;> norm_num)
                · have hs01110013 : InSquare (-5/128) (-253/640) (1/640) tau := by
                    convert childUR hs0111001 hx0111001 hy0111001 using 1 <;> norm_num
                  exact Batch0351.cell2815.sound htau (by
                    simp only [Batch0351.cell2815, Batch0351.tau2815, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01110013 (by positivity) using 1 <;> norm_num)
            · have hs0111003 : InSquare (-13/320) (-25/64) (1/320) tau := by
                convert childUR hs011100 hx011100 hy011100 using 1 <;> norm_num
              rcases le_total tau.re (-13/320 : ℝ) with hx0111003 | hx0111003
              · rcases le_total tau.im (-25/64 : ℝ) with hy0111003 | hy0111003
                · have hs01110030 : InSquare (-27/640) (-251/640) (1/640) tau := by
                    convert childLL hs0111003 hx0111003 hy0111003 using 1 <;> norm_num
                  exact Batch0352.cell2820.sound htau (by
                    simp only [Batch0352.cell2820, Batch0352.tau2820, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01110030 (by positivity) using 1 <;> norm_num)
                · have hs01110032 : InSquare (-27/640) (-249/640) (1/640) tau := by
                    convert childUL hs0111003 hx0111003 hy0111003 using 1 <;> norm_num
                  exact Batch0352.cell2822.sound htau (by
                    simp only [Batch0352.cell2822, Batch0352.tau2822, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01110032 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-25/64 : ℝ) with hy0111003 | hy0111003
                · have hs01110031 : InSquare (-5/128) (-251/640) (1/640) tau := by
                    convert childLR hs0111003 hx0111003 hy0111003 using 1 <;> norm_num
                  exact Batch0352.cell2821.sound htau (by
                    simp only [Batch0352.cell2821, Batch0352.tau2821, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01110031 (by positivity) using 1 <;> norm_num)
                · have hs01110033 : InSquare (-5/128) (-249/640) (1/640) tau := by
                    convert childUR hs0111003 hx0111003 hy0111003 using 1 <;> norm_num
                  exact Batch0352.cell2823.sound htau (by
                    simp only [Batch0352.cell2823, Batch0352.tau2823, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01110033 (by positivity) using 1 <;> norm_num)
        · have hs011102 : InSquare (-7/160) (-61/160) (1/160) tau := by
            convert childUL hs01110 hx01110 hy01110 using 1 <;> norm_num
          rcases le_total tau.re (-7/160 : ℝ) with hx011102 | hx011102
          · rcases le_total tau.im (-61/160 : ℝ) with hy011102 | hy011102
            · have hs0111020 : InSquare (-3/64) (-123/320) (1/320) tau := by
                convert childLL hs011102 hx011102 hy011102 using 1 <;> norm_num
              rcases le_total tau.re (-3/64 : ℝ) with hx0111020 | hx0111020
              · rcases le_total tau.im (-123/320 : ℝ) with hy0111020 | hy0111020
                · have hs01110200 : InSquare (-31/640) (-247/640) (1/640) tau := by
                    convert childLL hs0111020 hx0111020 hy0111020 using 1 <;> norm_num
                  exact Batch0355.cell2840.sound htau (by
                    simp only [Batch0355.cell2840, Batch0355.tau2840, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01110200 (by positivity) using 1 <;> norm_num)
                · have hs01110202 : InSquare (-31/640) (-49/128) (1/640) tau := by
                    convert childUL hs0111020 hx0111020 hy0111020 using 1 <;> norm_num
                  exact Batch0355.cell2842.sound htau (by
                    simp only [Batch0355.cell2842, Batch0355.tau2842, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01110202 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-123/320 : ℝ) with hy0111020 | hy0111020
                · have hs01110201 : InSquare (-29/640) (-247/640) (1/640) tau := by
                    convert childLR hs0111020 hx0111020 hy0111020 using 1 <;> norm_num
                  exact Batch0355.cell2841.sound htau (by
                    simp only [Batch0355.cell2841, Batch0355.tau2841, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01110201 (by positivity) using 1 <;> norm_num)
                · have hs01110203 : InSquare (-29/640) (-49/128) (1/640) tau := by
                    convert childUR hs0111020 hx0111020 hy0111020 using 1 <;> norm_num
                  exact Batch0355.cell2843.sound htau (by
                    simp only [Batch0355.cell2843, Batch0355.tau2843, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01110203 (by positivity) using 1 <;> norm_num)
            · have hs0111022 : InSquare (-3/64) (-121/320) (1/320) tau := by
                convert childUL hs011102 hx011102 hy011102 using 1 <;> norm_num
              exact Batch0185.cell1487.sound htau (by
                simp only [Batch0185.cell1487, Batch0185.tau1487, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0111022 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-61/160 : ℝ) with hy011102 | hy011102
            · have hs0111021 : InSquare (-13/320) (-123/320) (1/320) tau := by
                convert childLR hs011102 hx011102 hy011102 using 1 <;> norm_num
              rcases le_total tau.re (-13/320 : ℝ) with hx0111021 | hx0111021
              · rcases le_total tau.im (-123/320 : ℝ) with hy0111021 | hy0111021
                · have hs01110210 : InSquare (-27/640) (-247/640) (1/640) tau := by
                    convert childLL hs0111021 hx0111021 hy0111021 using 1 <;> norm_num
                  exact Batch0355.cell2844.sound htau (by
                    simp only [Batch0355.cell2844, Batch0355.tau2844, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01110210 (by positivity) using 1 <;> norm_num)
                · have hs01110212 : InSquare (-27/640) (-49/128) (1/640) tau := by
                    convert childUL hs0111021 hx0111021 hy0111021 using 1 <;> norm_num
                  exact Batch0355.cell2846.sound htau (by
                    simp only [Batch0355.cell2846, Batch0355.tau2846, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01110212 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-123/320 : ℝ) with hy0111021 | hy0111021
                · have hs01110211 : InSquare (-5/128) (-247/640) (1/640) tau := by
                    convert childLR hs0111021 hx0111021 hy0111021 using 1 <;> norm_num
                  exact Batch0355.cell2845.sound htau (by
                    simp only [Batch0355.cell2845, Batch0355.tau2845, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01110211 (by positivity) using 1 <;> norm_num)
                · have hs01110213 : InSquare (-5/128) (-49/128) (1/640) tau := by
                    convert childUR hs0111021 hx0111021 hy0111021 using 1 <;> norm_num
                  exact Batch0355.cell2847.sound htau (by
                    simp only [Batch0355.cell2847, Batch0355.tau2847, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01110213 (by positivity) using 1 <;> norm_num)
            · have hs0111023 : InSquare (-13/320) (-121/320) (1/320) tau := by
                convert childUR hs011102 hx011102 hy011102 using 1 <;> norm_num
              exact Batch0186.cell1488.sound htau (by
                simp only [Batch0186.cell1488, Batch0186.tau1488, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0111023 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-31/80 : ℝ) with hy01110 | hy01110
        · have hs011101 : InSquare (-1/32) (-63/160) (1/160) tau := by
            convert childLR hs01110 hx01110 hy01110 using 1 <;> norm_num
          rcases le_total tau.re (-1/32 : ℝ) with hx011101 | hx011101
          · rcases le_total tau.im (-63/160 : ℝ) with hy011101 | hy011101
            · have hs0111010 : InSquare (-11/320) (-127/320) (1/320) tau := by
                convert childLL hs011101 hx011101 hy011101 using 1 <;> norm_num
              rcases le_total tau.re (-11/320 : ℝ) with hx0111010 | hx0111010
              · rcases le_total tau.im (-127/320 : ℝ) with hy0111010 | hy0111010
                · have hs01110100 : InSquare (-23/640) (-51/128) (1/640) tau := by
                    convert childLL hs0111010 hx0111010 hy0111010 using 1 <;> norm_num
                  exact Batch0353.cell2824.sound htau (by
                    simp only [Batch0353.cell2824, Batch0353.tau2824, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01110100 (by positivity) using 1 <;> norm_num)
                · have hs01110102 : InSquare (-23/640) (-253/640) (1/640) tau := by
                    convert childUL hs0111010 hx0111010 hy0111010 using 1 <;> norm_num
                  exact Batch0353.cell2826.sound htau (by
                    simp only [Batch0353.cell2826, Batch0353.tau2826, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01110102 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-127/320 : ℝ) with hy0111010 | hy0111010
                · have hs01110101 : InSquare (-21/640) (-51/128) (1/640) tau := by
                    convert childLR hs0111010 hx0111010 hy0111010 using 1 <;> norm_num
                  exact Batch0353.cell2825.sound htau (by
                    simp only [Batch0353.cell2825, Batch0353.tau2825, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01110101 (by positivity) using 1 <;> norm_num)
                · have hs01110103 : InSquare (-21/640) (-253/640) (1/640) tau := by
                    convert childUR hs0111010 hx0111010 hy0111010 using 1 <;> norm_num
                  exact Batch0353.cell2827.sound htau (by
                    simp only [Batch0353.cell2827, Batch0353.tau2827, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01110103 (by positivity) using 1 <;> norm_num)
            · have hs0111012 : InSquare (-11/320) (-25/64) (1/320) tau := by
                convert childUL hs011101 hx011101 hy011101 using 1 <;> norm_num
              rcases le_total tau.re (-11/320 : ℝ) with hx0111012 | hx0111012
              · rcases le_total tau.im (-25/64 : ℝ) with hy0111012 | hy0111012
                · have hs01110120 : InSquare (-23/640) (-251/640) (1/640) tau := by
                    convert childLL hs0111012 hx0111012 hy0111012 using 1 <;> norm_num
                  exact Batch0354.cell2832.sound htau (by
                    simp only [Batch0354.cell2832, Batch0354.tau2832, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01110120 (by positivity) using 1 <;> norm_num)
                · have hs01110122 : InSquare (-23/640) (-249/640) (1/640) tau := by
                    convert childUL hs0111012 hx0111012 hy0111012 using 1 <;> norm_num
                  exact Batch0354.cell2834.sound htau (by
                    simp only [Batch0354.cell2834, Batch0354.tau2834, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01110122 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-25/64 : ℝ) with hy0111012 | hy0111012
                · have hs01110121 : InSquare (-21/640) (-251/640) (1/640) tau := by
                    convert childLR hs0111012 hx0111012 hy0111012 using 1 <;> norm_num
                  exact Batch0354.cell2833.sound htau (by
                    simp only [Batch0354.cell2833, Batch0354.tau2833, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01110121 (by positivity) using 1 <;> norm_num)
                · have hs01110123 : InSquare (-21/640) (-249/640) (1/640) tau := by
                    convert childUR hs0111012 hx0111012 hy0111012 using 1 <;> norm_num
                  exact Batch0354.cell2835.sound htau (by
                    simp only [Batch0354.cell2835, Batch0354.tau2835, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01110123 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-63/160 : ℝ) with hy011101 | hy011101
            · have hs0111011 : InSquare (-9/320) (-127/320) (1/320) tau := by
                convert childLR hs011101 hx011101 hy011101 using 1 <;> norm_num
              rcases le_total tau.re (-9/320 : ℝ) with hx0111011 | hx0111011
              · rcases le_total tau.im (-127/320 : ℝ) with hy0111011 | hy0111011
                · have hs01110110 : InSquare (-19/640) (-51/128) (1/640) tau := by
                    convert childLL hs0111011 hx0111011 hy0111011 using 1 <;> norm_num
                  exact Batch0353.cell2828.sound htau (by
                    simp only [Batch0353.cell2828, Batch0353.tau2828, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01110110 (by positivity) using 1 <;> norm_num)
                · have hs01110112 : InSquare (-19/640) (-253/640) (1/640) tau := by
                    convert childUL hs0111011 hx0111011 hy0111011 using 1 <;> norm_num
                  exact Batch0353.cell2830.sound htau (by
                    simp only [Batch0353.cell2830, Batch0353.tau2830, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01110112 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-127/320 : ℝ) with hy0111011 | hy0111011
                · have hs01110111 : InSquare (-17/640) (-51/128) (1/640) tau := by
                    convert childLR hs0111011 hx0111011 hy0111011 using 1 <;> norm_num
                  exact Batch0353.cell2829.sound htau (by
                    simp only [Batch0353.cell2829, Batch0353.tau2829, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01110111 (by positivity) using 1 <;> norm_num)
                · have hs01110113 : InSquare (-17/640) (-253/640) (1/640) tau := by
                    convert childUR hs0111011 hx0111011 hy0111011 using 1 <;> norm_num
                  exact Batch0353.cell2831.sound htau (by
                    simp only [Batch0353.cell2831, Batch0353.tau2831, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01110113 (by positivity) using 1 <;> norm_num)
            · have hs0111013 : InSquare (-9/320) (-25/64) (1/320) tau := by
                convert childUR hs011101 hx011101 hy011101 using 1 <;> norm_num
              rcases le_total tau.re (-9/320 : ℝ) with hx0111013 | hx0111013
              · rcases le_total tau.im (-25/64 : ℝ) with hy0111013 | hy0111013
                · have hs01110130 : InSquare (-19/640) (-251/640) (1/640) tau := by
                    convert childLL hs0111013 hx0111013 hy0111013 using 1 <;> norm_num
                  exact Batch0354.cell2836.sound htau (by
                    simp only [Batch0354.cell2836, Batch0354.tau2836, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01110130 (by positivity) using 1 <;> norm_num)
                · have hs01110132 : InSquare (-19/640) (-249/640) (1/640) tau := by
                    convert childUL hs0111013 hx0111013 hy0111013 using 1 <;> norm_num
                  exact Batch0354.cell2838.sound htau (by
                    simp only [Batch0354.cell2838, Batch0354.tau2838, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01110132 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-25/64 : ℝ) with hy0111013 | hy0111013
                · have hs01110131 : InSquare (-17/640) (-251/640) (1/640) tau := by
                    convert childLR hs0111013 hx0111013 hy0111013 using 1 <;> norm_num
                  exact Batch0354.cell2837.sound htau (by
                    simp only [Batch0354.cell2837, Batch0354.tau2837, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01110131 (by positivity) using 1 <;> norm_num)
                · have hs01110133 : InSquare (-17/640) (-249/640) (1/640) tau := by
                    convert childUR hs0111013 hx0111013 hy0111013 using 1 <;> norm_num
                  exact Batch0354.cell2839.sound htau (by
                    simp only [Batch0354.cell2839, Batch0354.tau2839, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01110133 (by positivity) using 1 <;> norm_num)
        · have hs011103 : InSquare (-1/32) (-61/160) (1/160) tau := by
            convert childUR hs01110 hx01110 hy01110 using 1 <;> norm_num
          rcases le_total tau.re (-1/32 : ℝ) with hx011103 | hx011103
          · rcases le_total tau.im (-61/160 : ℝ) with hy011103 | hy011103
            · have hs0111030 : InSquare (-11/320) (-123/320) (1/320) tau := by
                convert childLL hs011103 hx011103 hy011103 using 1 <;> norm_num
              rcases le_total tau.re (-11/320 : ℝ) with hx0111030 | hx0111030
              · rcases le_total tau.im (-123/320 : ℝ) with hy0111030 | hy0111030
                · have hs01110300 : InSquare (-23/640) (-247/640) (1/640) tau := by
                    convert childLL hs0111030 hx0111030 hy0111030 using 1 <;> norm_num
                  exact Batch0356.cell2848.sound htau (by
                    simp only [Batch0356.cell2848, Batch0356.tau2848, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01110300 (by positivity) using 1 <;> norm_num)
                · have hs01110302 : InSquare (-23/640) (-49/128) (1/640) tau := by
                    convert childUL hs0111030 hx0111030 hy0111030 using 1 <;> norm_num
                  exact Batch0356.cell2850.sound htau (by
                    simp only [Batch0356.cell2850, Batch0356.tau2850, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01110302 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-123/320 : ℝ) with hy0111030 | hy0111030
                · have hs01110301 : InSquare (-21/640) (-247/640) (1/640) tau := by
                    convert childLR hs0111030 hx0111030 hy0111030 using 1 <;> norm_num
                  exact Batch0356.cell2849.sound htau (by
                    simp only [Batch0356.cell2849, Batch0356.tau2849, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01110301 (by positivity) using 1 <;> norm_num)
                · have hs01110303 : InSquare (-21/640) (-49/128) (1/640) tau := by
                    convert childUR hs0111030 hx0111030 hy0111030 using 1 <;> norm_num
                  exact Batch0356.cell2851.sound htau (by
                    simp only [Batch0356.cell2851, Batch0356.tau2851, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01110303 (by positivity) using 1 <;> norm_num)
            · have hs0111032 : InSquare (-11/320) (-121/320) (1/320) tau := by
                convert childUL hs011103 hx011103 hy011103 using 1 <;> norm_num
              exact Batch0186.cell1490.sound htau (by
                simp only [Batch0186.cell1490, Batch0186.tau1490, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0111032 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-61/160 : ℝ) with hy011103 | hy011103
            · have hs0111031 : InSquare (-9/320) (-123/320) (1/320) tau := by
                convert childLR hs011103 hx011103 hy011103 using 1 <;> norm_num
              exact Batch0186.cell1489.sound htau (by
                simp only [Batch0186.cell1489, Batch0186.tau1489, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0111031 (by positivity) using 1 <;> norm_num)
            · have hs0111033 : InSquare (-9/320) (-121/320) (1/320) tau := by
                convert childUR hs011103 hx011103 hy011103 using 1 <;> norm_num
              exact Batch0186.cell1491.sound htau (by
                simp only [Batch0186.cell1491, Batch0186.tau1491, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0111033 (by positivity) using 1 <;> norm_num)
    · have hs01112 : InSquare (-3/80) (-29/80) (1/80) tau := by
        convert childUL hs hx0111 hy0111 using 1 <;> norm_num
      rcases le_total tau.re (-3/80 : ℝ) with hx01112 | hx01112
      · rcases le_total tau.im (-29/80 : ℝ) with hy01112 | hy01112
        · have hs011120 : InSquare (-7/160) (-59/160) (1/160) tau := by
            convert childLL hs01112 hx01112 hy01112 using 1 <;> norm_num
          rcases le_total tau.re (-7/160 : ℝ) with hx011120 | hx011120
          · rcases le_total tau.im (-59/160 : ℝ) with hy011120 | hy011120
            · have hs0111200 : InSquare (-3/64) (-119/320) (1/320) tau := by
                convert childLL hs011120 hx011120 hy011120 using 1 <;> norm_num
              exact Batch0187.cell1500.sound htau (by
                simp only [Batch0187.cell1500, Batch0187.tau1500, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0111200 (by positivity) using 1 <;> norm_num)
            · have hs0111202 : InSquare (-3/64) (-117/320) (1/320) tau := by
                convert childUL hs011120 hx011120 hy011120 using 1 <;> norm_num
              exact Batch0187.cell1502.sound htau (by
                simp only [Batch0187.cell1502, Batch0187.tau1502, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0111202 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-59/160 : ℝ) with hy011120 | hy011120
            · have hs0111201 : InSquare (-13/320) (-119/320) (1/320) tau := by
                convert childLR hs011120 hx011120 hy011120 using 1 <;> norm_num
              exact Batch0187.cell1501.sound htau (by
                simp only [Batch0187.cell1501, Batch0187.tau1501, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0111201 (by positivity) using 1 <;> norm_num)
            · have hs0111203 : InSquare (-13/320) (-117/320) (1/320) tau := by
                convert childUR hs011120 hx011120 hy011120 using 1 <;> norm_num
              exact Batch0187.cell1503.sound htau (by
                simp only [Batch0187.cell1503, Batch0187.tau1503, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0111203 (by positivity) using 1 <;> norm_num)
        · have hs011122 : InSquare (-7/160) (-57/160) (1/160) tau := by
            convert childUL hs01112 hx01112 hy01112 using 1 <;> norm_num
          rcases le_total tau.re (-7/160 : ℝ) with hx011122 | hx011122
          · rcases le_total tau.im (-57/160 : ℝ) with hy011122 | hy011122
            · have hs0111220 : InSquare (-3/64) (-23/64) (1/320) tau := by
                convert childLL hs011122 hx011122 hy011122 using 1 <;> norm_num
              exact Batch0188.cell1508.sound htau (by
                simp only [Batch0188.cell1508, Batch0188.tau1508, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0111220 (by positivity) using 1 <;> norm_num)
            · have hs0111222 : InSquare (-3/64) (-113/320) (1/320) tau := by
                convert childUL hs011122 hx011122 hy011122 using 1 <;> norm_num
              exact Batch0188.cell1510.sound htau (by
                simp only [Batch0188.cell1510, Batch0188.tau1510, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0111222 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-57/160 : ℝ) with hy011122 | hy011122
            · have hs0111221 : InSquare (-13/320) (-23/64) (1/320) tau := by
                convert childLR hs011122 hx011122 hy011122 using 1 <;> norm_num
              exact Batch0188.cell1509.sound htau (by
                simp only [Batch0188.cell1509, Batch0188.tau1509, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0111221 (by positivity) using 1 <;> norm_num)
            · have hs0111223 : InSquare (-13/320) (-113/320) (1/320) tau := by
                convert childUR hs011122 hx011122 hy011122 using 1 <;> norm_num
              exact Batch0188.cell1511.sound htau (by
                simp only [Batch0188.cell1511, Batch0188.tau1511, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0111223 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-29/80 : ℝ) with hy01112 | hy01112
        · have hs011121 : InSquare (-1/32) (-59/160) (1/160) tau := by
            convert childLR hs01112 hx01112 hy01112 using 1 <;> norm_num
          rcases le_total tau.re (-1/32 : ℝ) with hx011121 | hx011121
          · rcases le_total tau.im (-59/160 : ℝ) with hy011121 | hy011121
            · have hs0111210 : InSquare (-11/320) (-119/320) (1/320) tau := by
                convert childLL hs011121 hx011121 hy011121 using 1 <;> norm_num
              exact Batch0188.cell1504.sound htau (by
                simp only [Batch0188.cell1504, Batch0188.tau1504, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0111210 (by positivity) using 1 <;> norm_num)
            · have hs0111212 : InSquare (-11/320) (-117/320) (1/320) tau := by
                convert childUL hs011121 hx011121 hy011121 using 1 <;> norm_num
              exact Batch0188.cell1506.sound htau (by
                simp only [Batch0188.cell1506, Batch0188.tau1506, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0111212 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-59/160 : ℝ) with hy011121 | hy011121
            · have hs0111211 : InSquare (-9/320) (-119/320) (1/320) tau := by
                convert childLR hs011121 hx011121 hy011121 using 1 <;> norm_num
              exact Batch0188.cell1505.sound htau (by
                simp only [Batch0188.cell1505, Batch0188.tau1505, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0111211 (by positivity) using 1 <;> norm_num)
            · have hs0111213 : InSquare (-9/320) (-117/320) (1/320) tau := by
                convert childUR hs011121 hx011121 hy011121 using 1 <;> norm_num
              exact Batch0188.cell1507.sound htau (by
                simp only [Batch0188.cell1507, Batch0188.tau1507, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0111213 (by positivity) using 1 <;> norm_num)
        · have hs011123 : InSquare (-1/32) (-57/160) (1/160) tau := by
            convert childUR hs01112 hx01112 hy01112 using 1 <;> norm_num
          rcases le_total tau.re (-1/32 : ℝ) with hx011123 | hx011123
          · rcases le_total tau.im (-57/160 : ℝ) with hy011123 | hy011123
            · have hs0111230 : InSquare (-11/320) (-23/64) (1/320) tau := by
                convert childLL hs011123 hx011123 hy011123 using 1 <;> norm_num
              exact Batch0189.cell1512.sound htau (by
                simp only [Batch0189.cell1512, Batch0189.tau1512, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0111230 (by positivity) using 1 <;> norm_num)
            · have hs0111232 : InSquare (-11/320) (-113/320) (1/320) tau := by
                convert childUL hs011123 hx011123 hy011123 using 1 <;> norm_num
              exact Batch0189.cell1514.sound htau (by
                simp only [Batch0189.cell1514, Batch0189.tau1514, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0111232 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-57/160 : ℝ) with hy011123 | hy011123
            · have hs0111231 : InSquare (-9/320) (-23/64) (1/320) tau := by
                convert childLR hs011123 hx011123 hy011123 using 1 <;> norm_num
              exact Batch0189.cell1513.sound htau (by
                simp only [Batch0189.cell1513, Batch0189.tau1513, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0111231 (by positivity) using 1 <;> norm_num)
            · have hs0111233 : InSquare (-9/320) (-113/320) (1/320) tau := by
                convert childUR hs011123 hx011123 hy011123 using 1 <;> norm_num
              exact Batch0189.cell1515.sound htau (by
                simp only [Batch0189.cell1515, Batch0189.tau1515, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0111233 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (-3/8 : ℝ) with hy0111 | hy0111
    · have hs01111 : InSquare (-1/80) (-31/80) (1/80) tau := by
        convert childLR hs hx0111 hy0111 using 1 <;> norm_num
      rcases le_total tau.re (-1/80 : ℝ) with hx01111 | hx01111
      · rcases le_total tau.im (-31/80 : ℝ) with hy01111 | hy01111
        · have hs011110 : InSquare (-3/160) (-63/160) (1/160) tau := by
            convert childLL hs01111 hx01111 hy01111 using 1 <;> norm_num
          rcases le_total tau.re (-3/160 : ℝ) with hx011110 | hx011110
          · rcases le_total tau.im (-63/160 : ℝ) with hy011110 | hy011110
            · have hs0111100 : InSquare (-7/320) (-127/320) (1/320) tau := by
                convert childLL hs011110 hx011110 hy011110 using 1 <;> norm_num
              rcases le_total tau.re (-7/320 : ℝ) with hx0111100 | hx0111100
              · rcases le_total tau.im (-127/320 : ℝ) with hy0111100 | hy0111100
                · have hs01111000 : InSquare (-3/128) (-51/128) (1/640) tau := by
                    convert childLL hs0111100 hx0111100 hy0111100 using 1 <;> norm_num
                  exact Batch0356.cell2852.sound htau (by
                    simp only [Batch0356.cell2852, Batch0356.tau2852, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01111000 (by positivity) using 1 <;> norm_num)
                · have hs01111002 : InSquare (-3/128) (-253/640) (1/640) tau := by
                    convert childUL hs0111100 hx0111100 hy0111100 using 1 <;> norm_num
                  exact Batch0356.cell2854.sound htau (by
                    simp only [Batch0356.cell2854, Batch0356.tau2854, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01111002 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-127/320 : ℝ) with hy0111100 | hy0111100
                · have hs01111001 : InSquare (-13/640) (-51/128) (1/640) tau := by
                    convert childLR hs0111100 hx0111100 hy0111100 using 1 <;> norm_num
                  exact Batch0356.cell2853.sound htau (by
                    simp only [Batch0356.cell2853, Batch0356.tau2853, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01111001 (by positivity) using 1 <;> norm_num)
                · have hs01111003 : InSquare (-13/640) (-253/640) (1/640) tau := by
                    convert childUR hs0111100 hx0111100 hy0111100 using 1 <;> norm_num
                  exact Batch0356.cell2855.sound htau (by
                    simp only [Batch0356.cell2855, Batch0356.tau2855, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01111003 (by positivity) using 1 <;> norm_num)
            · have hs0111102 : InSquare (-7/320) (-25/64) (1/320) tau := by
                convert childUL hs011110 hx011110 hy011110 using 1 <;> norm_num
              rcases le_total tau.re (-7/320 : ℝ) with hx0111102 | hx0111102
              · rcases le_total tau.im (-25/64 : ℝ) with hy0111102 | hy0111102
                · have hs01111020 : InSquare (-3/128) (-251/640) (1/640) tau := by
                    convert childLL hs0111102 hx0111102 hy0111102 using 1 <;> norm_num
                  exact Batch0357.cell2860.sound htau (by
                    simp only [Batch0357.cell2860, Batch0357.tau2860, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01111020 (by positivity) using 1 <;> norm_num)
                · have hs01111022 : InSquare (-3/128) (-249/640) (1/640) tau := by
                    convert childUL hs0111102 hx0111102 hy0111102 using 1 <;> norm_num
                  exact Batch0357.cell2862.sound htau (by
                    simp only [Batch0357.cell2862, Batch0357.tau2862, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01111022 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-25/64 : ℝ) with hy0111102 | hy0111102
                · have hs01111021 : InSquare (-13/640) (-251/640) (1/640) tau := by
                    convert childLR hs0111102 hx0111102 hy0111102 using 1 <;> norm_num
                  exact Batch0357.cell2861.sound htau (by
                    simp only [Batch0357.cell2861, Batch0357.tau2861, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01111021 (by positivity) using 1 <;> norm_num)
                · have hs01111023 : InSquare (-13/640) (-249/640) (1/640) tau := by
                    convert childUR hs0111102 hx0111102 hy0111102 using 1 <;> norm_num
                  exact Batch0357.cell2863.sound htau (by
                    simp only [Batch0357.cell2863, Batch0357.tau2863, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01111023 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-63/160 : ℝ) with hy011110 | hy011110
            · have hs0111101 : InSquare (-1/64) (-127/320) (1/320) tau := by
                convert childLR hs011110 hx011110 hy011110 using 1 <;> norm_num
              rcases le_total tau.re (-1/64 : ℝ) with hx0111101 | hx0111101
              · rcases le_total tau.im (-127/320 : ℝ) with hy0111101 | hy0111101
                · have hs01111010 : InSquare (-11/640) (-51/128) (1/640) tau := by
                    convert childLL hs0111101 hx0111101 hy0111101 using 1 <;> norm_num
                  exact Batch0357.cell2856.sound htau (by
                    simp only [Batch0357.cell2856, Batch0357.tau2856, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01111010 (by positivity) using 1 <;> norm_num)
                · have hs01111012 : InSquare (-11/640) (-253/640) (1/640) tau := by
                    convert childUL hs0111101 hx0111101 hy0111101 using 1 <;> norm_num
                  exact Batch0357.cell2858.sound htau (by
                    simp only [Batch0357.cell2858, Batch0357.tau2858, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01111012 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-127/320 : ℝ) with hy0111101 | hy0111101
                · have hs01111011 : InSquare (-9/640) (-51/128) (1/640) tau := by
                    convert childLR hs0111101 hx0111101 hy0111101 using 1 <;> norm_num
                  exact Batch0357.cell2857.sound htau (by
                    simp only [Batch0357.cell2857, Batch0357.tau2857, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01111011 (by positivity) using 1 <;> norm_num)
                · have hs01111013 : InSquare (-9/640) (-253/640) (1/640) tau := by
                    convert childUR hs0111101 hx0111101 hy0111101 using 1 <;> norm_num
                  exact Batch0357.cell2859.sound htau (by
                    simp only [Batch0357.cell2859, Batch0357.tau2859, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01111013 (by positivity) using 1 <;> norm_num)
            · have hs0111103 : InSquare (-1/64) (-25/64) (1/320) tau := by
                convert childUR hs011110 hx011110 hy011110 using 1 <;> norm_num
              rcases le_total tau.re (-1/64 : ℝ) with hx0111103 | hx0111103
              · rcases le_total tau.im (-25/64 : ℝ) with hy0111103 | hy0111103
                · have hs01111030 : InSquare (-11/640) (-251/640) (1/640) tau := by
                    convert childLL hs0111103 hx0111103 hy0111103 using 1 <;> norm_num
                  exact Batch0358.cell2864.sound htau (by
                    simp only [Batch0358.cell2864, Batch0358.tau2864, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01111030 (by positivity) using 1 <;> norm_num)
                · have hs01111032 : InSquare (-11/640) (-249/640) (1/640) tau := by
                    convert childUL hs0111103 hx0111103 hy0111103 using 1 <;> norm_num
                  exact Batch0358.cell2866.sound htau (by
                    simp only [Batch0358.cell2866, Batch0358.tau2866, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01111032 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-25/64 : ℝ) with hy0111103 | hy0111103
                · have hs01111031 : InSquare (-9/640) (-251/640) (1/640) tau := by
                    convert childLR hs0111103 hx0111103 hy0111103 using 1 <;> norm_num
                  exact Batch0358.cell2865.sound htau (by
                    simp only [Batch0358.cell2865, Batch0358.tau2865, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01111031 (by positivity) using 1 <;> norm_num)
                · have hs01111033 : InSquare (-9/640) (-249/640) (1/640) tau := by
                    convert childUR hs0111103 hx0111103 hy0111103 using 1 <;> norm_num
                  exact Batch0358.cell2867.sound htau (by
                    simp only [Batch0358.cell2867, Batch0358.tau2867, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01111033 (by positivity) using 1 <;> norm_num)
        · have hs011112 : InSquare (-3/160) (-61/160) (1/160) tau := by
            convert childUL hs01111 hx01111 hy01111 using 1 <;> norm_num
          rcases le_total tau.re (-3/160 : ℝ) with hx011112 | hx011112
          · rcases le_total tau.im (-61/160 : ℝ) with hy011112 | hy011112
            · have hs0111120 : InSquare (-7/320) (-123/320) (1/320) tau := by
                convert childLL hs011112 hx011112 hy011112 using 1 <;> norm_num
              exact Batch0186.cell1492.sound htau (by
                simp only [Batch0186.cell1492, Batch0186.tau1492, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0111120 (by positivity) using 1 <;> norm_num)
            · have hs0111122 : InSquare (-7/320) (-121/320) (1/320) tau := by
                convert childUL hs011112 hx011112 hy011112 using 1 <;> norm_num
              exact Batch0186.cell1494.sound htau (by
                simp only [Batch0186.cell1494, Batch0186.tau1494, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0111122 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-61/160 : ℝ) with hy011112 | hy011112
            · have hs0111121 : InSquare (-1/64) (-123/320) (1/320) tau := by
                convert childLR hs011112 hx011112 hy011112 using 1 <;> norm_num
              exact Batch0186.cell1493.sound htau (by
                simp only [Batch0186.cell1493, Batch0186.tau1493, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0111121 (by positivity) using 1 <;> norm_num)
            · have hs0111123 : InSquare (-1/64) (-121/320) (1/320) tau := by
                convert childUR hs011112 hx011112 hy011112 using 1 <;> norm_num
              exact Batch0186.cell1495.sound htau (by
                simp only [Batch0186.cell1495, Batch0186.tau1495, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0111123 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-31/80 : ℝ) with hy01111 | hy01111
        · have hs011111 : InSquare (-1/160) (-63/160) (1/160) tau := by
            convert childLR hs01111 hx01111 hy01111 using 1 <;> norm_num
          rcases le_total tau.re (-1/160 : ℝ) with hx011111 | hx011111
          · rcases le_total tau.im (-63/160 : ℝ) with hy011111 | hy011111
            · have hs0111110 : InSquare (-3/320) (-127/320) (1/320) tau := by
                convert childLL hs011111 hx011111 hy011111 using 1 <;> norm_num
              rcases le_total tau.re (-3/320 : ℝ) with hx0111110 | hx0111110
              · rcases le_total tau.im (-127/320 : ℝ) with hy0111110 | hy0111110
                · have hs01111100 : InSquare (-7/640) (-51/128) (1/640) tau := by
                    convert childLL hs0111110 hx0111110 hy0111110 using 1 <;> norm_num
                  exact Batch0358.cell2868.sound htau (by
                    simp only [Batch0358.cell2868, Batch0358.tau2868, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01111100 (by positivity) using 1 <;> norm_num)
                · have hs01111102 : InSquare (-7/640) (-253/640) (1/640) tau := by
                    convert childUL hs0111110 hx0111110 hy0111110 using 1 <;> norm_num
                  exact Batch0358.cell2870.sound htau (by
                    simp only [Batch0358.cell2870, Batch0358.tau2870, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01111102 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-127/320 : ℝ) with hy0111110 | hy0111110
                · have hs01111101 : InSquare (-1/128) (-51/128) (1/640) tau := by
                    convert childLR hs0111110 hx0111110 hy0111110 using 1 <;> norm_num
                  exact Batch0358.cell2869.sound htau (by
                    simp only [Batch0358.cell2869, Batch0358.tau2869, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01111101 (by positivity) using 1 <;> norm_num)
                · have hs01111103 : InSquare (-1/128) (-253/640) (1/640) tau := by
                    convert childUR hs0111110 hx0111110 hy0111110 using 1 <;> norm_num
                  exact Batch0358.cell2871.sound htau (by
                    simp only [Batch0358.cell2871, Batch0358.tau2871, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01111103 (by positivity) using 1 <;> norm_num)
            · have hs0111112 : InSquare (-3/320) (-25/64) (1/320) tau := by
                convert childUL hs011111 hx011111 hy011111 using 1 <;> norm_num
              rcases le_total tau.re (-3/320 : ℝ) with hx0111112 | hx0111112
              · rcases le_total tau.im (-25/64 : ℝ) with hy0111112 | hy0111112
                · have hs01111120 : InSquare (-7/640) (-251/640) (1/640) tau := by
                    convert childLL hs0111112 hx0111112 hy0111112 using 1 <;> norm_num
                  exact Batch0359.cell2876.sound htau (by
                    simp only [Batch0359.cell2876, Batch0359.tau2876, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01111120 (by positivity) using 1 <;> norm_num)
                · have hs01111122 : InSquare (-7/640) (-249/640) (1/640) tau := by
                    convert childUL hs0111112 hx0111112 hy0111112 using 1 <;> norm_num
                  exact Batch0359.cell2878.sound htau (by
                    simp only [Batch0359.cell2878, Batch0359.tau2878, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01111122 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-25/64 : ℝ) with hy0111112 | hy0111112
                · have hs01111121 : InSquare (-1/128) (-251/640) (1/640) tau := by
                    convert childLR hs0111112 hx0111112 hy0111112 using 1 <;> norm_num
                  exact Batch0359.cell2877.sound htau (by
                    simp only [Batch0359.cell2877, Batch0359.tau2877, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01111121 (by positivity) using 1 <;> norm_num)
                · have hs01111123 : InSquare (-1/128) (-249/640) (1/640) tau := by
                    convert childUR hs0111112 hx0111112 hy0111112 using 1 <;> norm_num
                  exact Batch0359.cell2879.sound htau (by
                    simp only [Batch0359.cell2879, Batch0359.tau2879, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01111123 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-63/160 : ℝ) with hy011111 | hy011111
            · have hs0111111 : InSquare (-1/320) (-127/320) (1/320) tau := by
                convert childLR hs011111 hx011111 hy011111 using 1 <;> norm_num
              rcases le_total tau.re (-1/320 : ℝ) with hx0111111 | hx0111111
              · rcases le_total tau.im (-127/320 : ℝ) with hy0111111 | hy0111111
                · have hs01111110 : InSquare (-3/640) (-51/128) (1/640) tau := by
                    convert childLL hs0111111 hx0111111 hy0111111 using 1 <;> norm_num
                  exact Batch0359.cell2872.sound htau (by
                    simp only [Batch0359.cell2872, Batch0359.tau2872, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01111110 (by positivity) using 1 <;> norm_num)
                · have hs01111112 : InSquare (-3/640) (-253/640) (1/640) tau := by
                    convert childUL hs0111111 hx0111111 hy0111111 using 1 <;> norm_num
                  exact Batch0359.cell2874.sound htau (by
                    simp only [Batch0359.cell2874, Batch0359.tau2874, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01111112 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-127/320 : ℝ) with hy0111111 | hy0111111
                · have hs01111111 : InSquare (-1/640) (-51/128) (1/640) tau := by
                    convert childLR hs0111111 hx0111111 hy0111111 using 1 <;> norm_num
                  exact Batch0359.cell2873.sound htau (by
                    simp only [Batch0359.cell2873, Batch0359.tau2873, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01111111 (by positivity) using 1 <;> norm_num)
                · have hs01111113 : InSquare (-1/640) (-253/640) (1/640) tau := by
                    convert childUR hs0111111 hx0111111 hy0111111 using 1 <;> norm_num
                  exact Batch0359.cell2875.sound htau (by
                    simp only [Batch0359.cell2875, Batch0359.tau2875, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01111113 (by positivity) using 1 <;> norm_num)
            · have hs0111113 : InSquare (-1/320) (-25/64) (1/320) tau := by
                convert childUR hs011111 hx011111 hy011111 using 1 <;> norm_num
              rcases le_total tau.re (-1/320 : ℝ) with hx0111113 | hx0111113
              · rcases le_total tau.im (-25/64 : ℝ) with hy0111113 | hy0111113
                · have hs01111130 : InSquare (-3/640) (-251/640) (1/640) tau := by
                    convert childLL hs0111113 hx0111113 hy0111113 using 1 <;> norm_num
                  exact Batch0360.cell2880.sound htau (by
                    simp only [Batch0360.cell2880, Batch0360.tau2880, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01111130 (by positivity) using 1 <;> norm_num)
                · have hs01111132 : InSquare (-3/640) (-249/640) (1/640) tau := by
                    convert childUL hs0111113 hx0111113 hy0111113 using 1 <;> norm_num
                  exact Batch0360.cell2882.sound htau (by
                    simp only [Batch0360.cell2882, Batch0360.tau2882, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01111132 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-25/64 : ℝ) with hy0111113 | hy0111113
                · have hs01111131 : InSquare (-1/640) (-251/640) (1/640) tau := by
                    convert childLR hs0111113 hx0111113 hy0111113 using 1 <;> norm_num
                  exact Batch0360.cell2881.sound htau (by
                    simp only [Batch0360.cell2881, Batch0360.tau2881, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01111131 (by positivity) using 1 <;> norm_num)
                · have hs01111133 : InSquare (-1/640) (-249/640) (1/640) tau := by
                    convert childUR hs0111113 hx0111113 hy0111113 using 1 <;> norm_num
                  exact Batch0360.cell2883.sound htau (by
                    simp only [Batch0360.cell2883, Batch0360.tau2883, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01111133 (by positivity) using 1 <;> norm_num)
        · have hs011113 : InSquare (-1/160) (-61/160) (1/160) tau := by
            convert childUR hs01111 hx01111 hy01111 using 1 <;> norm_num
          rcases le_total tau.re (-1/160 : ℝ) with hx011113 | hx011113
          · rcases le_total tau.im (-61/160 : ℝ) with hy011113 | hy011113
            · have hs0111130 : InSquare (-3/320) (-123/320) (1/320) tau := by
                convert childLL hs011113 hx011113 hy011113 using 1 <;> norm_num
              exact Batch0187.cell1496.sound htau (by
                simp only [Batch0187.cell1496, Batch0187.tau1496, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0111130 (by positivity) using 1 <;> norm_num)
            · have hs0111132 : InSquare (-3/320) (-121/320) (1/320) tau := by
                convert childUL hs011113 hx011113 hy011113 using 1 <;> norm_num
              exact Batch0187.cell1498.sound htau (by
                simp only [Batch0187.cell1498, Batch0187.tau1498, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0111132 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-61/160 : ℝ) with hy011113 | hy011113
            · have hs0111131 : InSquare (-1/320) (-123/320) (1/320) tau := by
                convert childLR hs011113 hx011113 hy011113 using 1 <;> norm_num
              exact Batch0187.cell1497.sound htau (by
                simp only [Batch0187.cell1497, Batch0187.tau1497, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0111131 (by positivity) using 1 <;> norm_num)
            · have hs0111133 : InSquare (-1/320) (-121/320) (1/320) tau := by
                convert childUR hs011113 hx011113 hy011113 using 1 <;> norm_num
              exact Batch0187.cell1499.sound htau (by
                simp only [Batch0187.cell1499, Batch0187.tau1499, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0111133 (by positivity) using 1 <;> norm_num)
    · have hs01113 : InSquare (-1/80) (-29/80) (1/80) tau := by
        convert childUR hs hx0111 hy0111 using 1 <;> norm_num
      rcases le_total tau.re (-1/80 : ℝ) with hx01113 | hx01113
      · rcases le_total tau.im (-29/80 : ℝ) with hy01113 | hy01113
        · have hs011130 : InSquare (-3/160) (-59/160) (1/160) tau := by
            convert childLL hs01113 hx01113 hy01113 using 1 <;> norm_num
          rcases le_total tau.re (-3/160 : ℝ) with hx011130 | hx011130
          · rcases le_total tau.im (-59/160 : ℝ) with hy011130 | hy011130
            · have hs0111300 : InSquare (-7/320) (-119/320) (1/320) tau := by
                convert childLL hs011130 hx011130 hy011130 using 1 <;> norm_num
              exact Batch0189.cell1516.sound htau (by
                simp only [Batch0189.cell1516, Batch0189.tau1516, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0111300 (by positivity) using 1 <;> norm_num)
            · have hs0111302 : InSquare (-7/320) (-117/320) (1/320) tau := by
                convert childUL hs011130 hx011130 hy011130 using 1 <;> norm_num
              exact Batch0189.cell1518.sound htau (by
                simp only [Batch0189.cell1518, Batch0189.tau1518, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0111302 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-59/160 : ℝ) with hy011130 | hy011130
            · have hs0111301 : InSquare (-1/64) (-119/320) (1/320) tau := by
                convert childLR hs011130 hx011130 hy011130 using 1 <;> norm_num
              exact Batch0189.cell1517.sound htau (by
                simp only [Batch0189.cell1517, Batch0189.tau1517, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0111301 (by positivity) using 1 <;> norm_num)
            · have hs0111303 : InSquare (-1/64) (-117/320) (1/320) tau := by
                convert childUR hs011130 hx011130 hy011130 using 1 <;> norm_num
              exact Batch0189.cell1519.sound htau (by
                simp only [Batch0189.cell1519, Batch0189.tau1519, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0111303 (by positivity) using 1 <;> norm_num)
        · have hs011132 : InSquare (-3/160) (-57/160) (1/160) tau := by
            convert childUL hs01113 hx01113 hy01113 using 1 <;> norm_num
          rcases le_total tau.re (-3/160 : ℝ) with hx011132 | hx011132
          · rcases le_total tau.im (-57/160 : ℝ) with hy011132 | hy011132
            · have hs0111320 : InSquare (-7/320) (-23/64) (1/320) tau := by
                convert childLL hs011132 hx011132 hy011132 using 1 <;> norm_num
              exact Batch0190.cell1524.sound htau (by
                simp only [Batch0190.cell1524, Batch0190.tau1524, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0111320 (by positivity) using 1 <;> norm_num)
            · have hs0111322 : InSquare (-7/320) (-113/320) (1/320) tau := by
                convert childUL hs011132 hx011132 hy011132 using 1 <;> norm_num
              exact Batch0190.cell1526.sound htau (by
                simp only [Batch0190.cell1526, Batch0190.tau1526, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0111322 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-57/160 : ℝ) with hy011132 | hy011132
            · have hs0111321 : InSquare (-1/64) (-23/64) (1/320) tau := by
                convert childLR hs011132 hx011132 hy011132 using 1 <;> norm_num
              exact Batch0190.cell1525.sound htau (by
                simp only [Batch0190.cell1525, Batch0190.tau1525, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0111321 (by positivity) using 1 <;> norm_num)
            · have hs0111323 : InSquare (-1/64) (-113/320) (1/320) tau := by
                convert childUR hs011132 hx011132 hy011132 using 1 <;> norm_num
              exact Batch0190.cell1527.sound htau (by
                simp only [Batch0190.cell1527, Batch0190.tau1527, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0111323 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-29/80 : ℝ) with hy01113 | hy01113
        · have hs011131 : InSquare (-1/160) (-59/160) (1/160) tau := by
            convert childLR hs01113 hx01113 hy01113 using 1 <;> norm_num
          rcases le_total tau.re (-1/160 : ℝ) with hx011131 | hx011131
          · rcases le_total tau.im (-59/160 : ℝ) with hy011131 | hy011131
            · have hs0111310 : InSquare (-3/320) (-119/320) (1/320) tau := by
                convert childLL hs011131 hx011131 hy011131 using 1 <;> norm_num
              exact Batch0190.cell1520.sound htau (by
                simp only [Batch0190.cell1520, Batch0190.tau1520, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0111310 (by positivity) using 1 <;> norm_num)
            · have hs0111312 : InSquare (-3/320) (-117/320) (1/320) tau := by
                convert childUL hs011131 hx011131 hy011131 using 1 <;> norm_num
              exact Batch0190.cell1522.sound htau (by
                simp only [Batch0190.cell1522, Batch0190.tau1522, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0111312 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-59/160 : ℝ) with hy011131 | hy011131
            · have hs0111311 : InSquare (-1/320) (-119/320) (1/320) tau := by
                convert childLR hs011131 hx011131 hy011131 using 1 <;> norm_num
              exact Batch0190.cell1521.sound htau (by
                simp only [Batch0190.cell1521, Batch0190.tau1521, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0111311 (by positivity) using 1 <;> norm_num)
            · have hs0111313 : InSquare (-1/320) (-117/320) (1/320) tau := by
                convert childUR hs011131 hx011131 hy011131 using 1 <;> norm_num
              exact Batch0190.cell1523.sound htau (by
                simp only [Batch0190.cell1523, Batch0190.tau1523, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0111313 (by positivity) using 1 <;> norm_num)
        · have hs011133 : InSquare (-1/160) (-57/160) (1/160) tau := by
            convert childUR hs01113 hx01113 hy01113 using 1 <;> norm_num
          exact Batch0050.cell0403.sound htau (by
            simp only [Batch0050.cell0403, Batch0050.tau0403, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs011133 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0111
