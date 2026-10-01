import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0069
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0192
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0193
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0194
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0195
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0196
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0197
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0360
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0361
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0362
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0363
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0364
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0365
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0366
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0367
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0368
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0369

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1000

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (1/40) (-3/8) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (1/40 : ℝ) with hx1000 | hx1000
  · rcases le_total tau.im (-3/8 : ℝ) with hy1000 | hy1000
    · have hs10000 : InSquare (1/80) (-31/80) (1/80) tau := by
        convert childLL hs hx1000 hy1000 using 1 <;> norm_num
      rcases le_total tau.re (1/80 : ℝ) with hx10000 | hx10000
      · rcases le_total tau.im (-31/80 : ℝ) with hy10000 | hy10000
        · have hs100000 : InSquare (1/160) (-63/160) (1/160) tau := by
            convert childLL hs10000 hx10000 hy10000 using 1 <;> norm_num
          rcases le_total tau.re (1/160 : ℝ) with hx100000 | hx100000
          · rcases le_total tau.im (-63/160 : ℝ) with hy100000 | hy100000
            · have hs1000000 : InSquare (1/320) (-127/320) (1/320) tau := by
                convert childLL hs100000 hx100000 hy100000 using 1 <;> norm_num
              rcases le_total tau.re (1/320 : ℝ) with hx1000000 | hx1000000
              · rcases le_total tau.im (-127/320 : ℝ) with hy1000000 | hy1000000
                · have hs10000000 : InSquare (1/640) (-51/128) (1/640) tau := by
                    convert childLL hs1000000 hx1000000 hy1000000 using 1 <;> norm_num
                  exact Batch0360.cell2884.sound htau (by
                    simp only [Batch0360.cell2884, Batch0360.tau2884, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10000000 (by positivity) using 1 <;> norm_num)
                · have hs10000002 : InSquare (1/640) (-253/640) (1/640) tau := by
                    convert childUL hs1000000 hx1000000 hy1000000 using 1 <;> norm_num
                  exact Batch0360.cell2886.sound htau (by
                    simp only [Batch0360.cell2886, Batch0360.tau2886, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10000002 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-127/320 : ℝ) with hy1000000 | hy1000000
                · have hs10000001 : InSquare (3/640) (-51/128) (1/640) tau := by
                    convert childLR hs1000000 hx1000000 hy1000000 using 1 <;> norm_num
                  exact Batch0360.cell2885.sound htau (by
                    simp only [Batch0360.cell2885, Batch0360.tau2885, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10000001 (by positivity) using 1 <;> norm_num)
                · have hs10000003 : InSquare (3/640) (-253/640) (1/640) tau := by
                    convert childUR hs1000000 hx1000000 hy1000000 using 1 <;> norm_num
                  exact Batch0360.cell2887.sound htau (by
                    simp only [Batch0360.cell2887, Batch0360.tau2887, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10000003 (by positivity) using 1 <;> norm_num)
            · have hs1000002 : InSquare (1/320) (-25/64) (1/320) tau := by
                convert childUL hs100000 hx100000 hy100000 using 1 <;> norm_num
              rcases le_total tau.re (1/320 : ℝ) with hx1000002 | hx1000002
              · rcases le_total tau.im (-25/64 : ℝ) with hy1000002 | hy1000002
                · have hs10000020 : InSquare (1/640) (-251/640) (1/640) tau := by
                    convert childLL hs1000002 hx1000002 hy1000002 using 1 <;> norm_num
                  exact Batch0361.cell2892.sound htau (by
                    simp only [Batch0361.cell2892, Batch0361.tau2892, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10000020 (by positivity) using 1 <;> norm_num)
                · have hs10000022 : InSquare (1/640) (-249/640) (1/640) tau := by
                    convert childUL hs1000002 hx1000002 hy1000002 using 1 <;> norm_num
                  exact Batch0361.cell2894.sound htau (by
                    simp only [Batch0361.cell2894, Batch0361.tau2894, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10000022 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-25/64 : ℝ) with hy1000002 | hy1000002
                · have hs10000021 : InSquare (3/640) (-251/640) (1/640) tau := by
                    convert childLR hs1000002 hx1000002 hy1000002 using 1 <;> norm_num
                  exact Batch0361.cell2893.sound htau (by
                    simp only [Batch0361.cell2893, Batch0361.tau2893, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10000021 (by positivity) using 1 <;> norm_num)
                · have hs10000023 : InSquare (3/640) (-249/640) (1/640) tau := by
                    convert childUR hs1000002 hx1000002 hy1000002 using 1 <;> norm_num
                  exact Batch0361.cell2895.sound htau (by
                    simp only [Batch0361.cell2895, Batch0361.tau2895, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10000023 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-63/160 : ℝ) with hy100000 | hy100000
            · have hs1000001 : InSquare (3/320) (-127/320) (1/320) tau := by
                convert childLR hs100000 hx100000 hy100000 using 1 <;> norm_num
              rcases le_total tau.re (3/320 : ℝ) with hx1000001 | hx1000001
              · rcases le_total tau.im (-127/320 : ℝ) with hy1000001 | hy1000001
                · have hs10000010 : InSquare (1/128) (-51/128) (1/640) tau := by
                    convert childLL hs1000001 hx1000001 hy1000001 using 1 <;> norm_num
                  exact Batch0361.cell2888.sound htau (by
                    simp only [Batch0361.cell2888, Batch0361.tau2888, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10000010 (by positivity) using 1 <;> norm_num)
                · have hs10000012 : InSquare (1/128) (-253/640) (1/640) tau := by
                    convert childUL hs1000001 hx1000001 hy1000001 using 1 <;> norm_num
                  exact Batch0361.cell2890.sound htau (by
                    simp only [Batch0361.cell2890, Batch0361.tau2890, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10000012 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-127/320 : ℝ) with hy1000001 | hy1000001
                · have hs10000011 : InSquare (7/640) (-51/128) (1/640) tau := by
                    convert childLR hs1000001 hx1000001 hy1000001 using 1 <;> norm_num
                  exact Batch0361.cell2889.sound htau (by
                    simp only [Batch0361.cell2889, Batch0361.tau2889, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10000011 (by positivity) using 1 <;> norm_num)
                · have hs10000013 : InSquare (7/640) (-253/640) (1/640) tau := by
                    convert childUR hs1000001 hx1000001 hy1000001 using 1 <;> norm_num
                  exact Batch0361.cell2891.sound htau (by
                    simp only [Batch0361.cell2891, Batch0361.tau2891, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10000013 (by positivity) using 1 <;> norm_num)
            · have hs1000003 : InSquare (3/320) (-25/64) (1/320) tau := by
                convert childUR hs100000 hx100000 hy100000 using 1 <;> norm_num
              rcases le_total tau.re (3/320 : ℝ) with hx1000003 | hx1000003
              · rcases le_total tau.im (-25/64 : ℝ) with hy1000003 | hy1000003
                · have hs10000030 : InSquare (1/128) (-251/640) (1/640) tau := by
                    convert childLL hs1000003 hx1000003 hy1000003 using 1 <;> norm_num
                  exact Batch0362.cell2896.sound htau (by
                    simp only [Batch0362.cell2896, Batch0362.tau2896, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10000030 (by positivity) using 1 <;> norm_num)
                · have hs10000032 : InSquare (1/128) (-249/640) (1/640) tau := by
                    convert childUL hs1000003 hx1000003 hy1000003 using 1 <;> norm_num
                  exact Batch0362.cell2898.sound htau (by
                    simp only [Batch0362.cell2898, Batch0362.tau2898, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10000032 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-25/64 : ℝ) with hy1000003 | hy1000003
                · have hs10000031 : InSquare (7/640) (-251/640) (1/640) tau := by
                    convert childLR hs1000003 hx1000003 hy1000003 using 1 <;> norm_num
                  exact Batch0362.cell2897.sound htau (by
                    simp only [Batch0362.cell2897, Batch0362.tau2897, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10000031 (by positivity) using 1 <;> norm_num)
                · have hs10000033 : InSquare (7/640) (-249/640) (1/640) tau := by
                    convert childUR hs1000003 hx1000003 hy1000003 using 1 <;> norm_num
                  exact Batch0362.cell2899.sound htau (by
                    simp only [Batch0362.cell2899, Batch0362.tau2899, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10000033 (by positivity) using 1 <;> norm_num)
        · have hs100002 : InSquare (1/160) (-61/160) (1/160) tau := by
            convert childUL hs10000 hx10000 hy10000 using 1 <;> norm_num
          rcases le_total tau.re (1/160 : ℝ) with hx100002 | hx100002
          · rcases le_total tau.im (-61/160 : ℝ) with hy100002 | hy100002
            · have hs1000020 : InSquare (1/320) (-123/320) (1/320) tau := by
                convert childLL hs100002 hx100002 hy100002 using 1 <;> norm_num
              exact Batch0192.cell1541.sound htau (by
                simp only [Batch0192.cell1541, Batch0192.tau1541, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1000020 (by positivity) using 1 <;> norm_num)
            · have hs1000022 : InSquare (1/320) (-121/320) (1/320) tau := by
                convert childUL hs100002 hx100002 hy100002 using 1 <;> norm_num
              exact Batch0192.cell1543.sound htau (by
                simp only [Batch0192.cell1543, Batch0192.tau1543, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1000022 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-61/160 : ℝ) with hy100002 | hy100002
            · have hs1000021 : InSquare (3/320) (-123/320) (1/320) tau := by
                convert childLR hs100002 hx100002 hy100002 using 1 <;> norm_num
              exact Batch0192.cell1542.sound htau (by
                simp only [Batch0192.cell1542, Batch0192.tau1542, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1000021 (by positivity) using 1 <;> norm_num)
            · have hs1000023 : InSquare (3/320) (-121/320) (1/320) tau := by
                convert childUR hs100002 hx100002 hy100002 using 1 <;> norm_num
              exact Batch0193.cell1544.sound htau (by
                simp only [Batch0193.cell1544, Batch0193.tau1544, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1000023 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-31/80 : ℝ) with hy10000 | hy10000
        · have hs100001 : InSquare (3/160) (-63/160) (1/160) tau := by
            convert childLR hs10000 hx10000 hy10000 using 1 <;> norm_num
          rcases le_total tau.re (3/160 : ℝ) with hx100001 | hx100001
          · rcases le_total tau.im (-63/160 : ℝ) with hy100001 | hy100001
            · have hs1000010 : InSquare (1/64) (-127/320) (1/320) tau := by
                convert childLL hs100001 hx100001 hy100001 using 1 <;> norm_num
              rcases le_total tau.re (1/64 : ℝ) with hx1000010 | hx1000010
              · rcases le_total tau.im (-127/320 : ℝ) with hy1000010 | hy1000010
                · have hs10000100 : InSquare (9/640) (-51/128) (1/640) tau := by
                    convert childLL hs1000010 hx1000010 hy1000010 using 1 <;> norm_num
                  exact Batch0362.cell2900.sound htau (by
                    simp only [Batch0362.cell2900, Batch0362.tau2900, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10000100 (by positivity) using 1 <;> norm_num)
                · have hs10000102 : InSquare (9/640) (-253/640) (1/640) tau := by
                    convert childUL hs1000010 hx1000010 hy1000010 using 1 <;> norm_num
                  exact Batch0362.cell2902.sound htau (by
                    simp only [Batch0362.cell2902, Batch0362.tau2902, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10000102 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-127/320 : ℝ) with hy1000010 | hy1000010
                · have hs10000101 : InSquare (11/640) (-51/128) (1/640) tau := by
                    convert childLR hs1000010 hx1000010 hy1000010 using 1 <;> norm_num
                  exact Batch0362.cell2901.sound htau (by
                    simp only [Batch0362.cell2901, Batch0362.tau2901, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10000101 (by positivity) using 1 <;> norm_num)
                · have hs10000103 : InSquare (11/640) (-253/640) (1/640) tau := by
                    convert childUR hs1000010 hx1000010 hy1000010 using 1 <;> norm_num
                  exact Batch0362.cell2903.sound htau (by
                    simp only [Batch0362.cell2903, Batch0362.tau2903, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10000103 (by positivity) using 1 <;> norm_num)
            · have hs1000012 : InSquare (1/64) (-25/64) (1/320) tau := by
                convert childUL hs100001 hx100001 hy100001 using 1 <;> norm_num
              rcases le_total tau.re (1/64 : ℝ) with hx1000012 | hx1000012
              · rcases le_total tau.im (-25/64 : ℝ) with hy1000012 | hy1000012
                · have hs10000120 : InSquare (9/640) (-251/640) (1/640) tau := by
                    convert childLL hs1000012 hx1000012 hy1000012 using 1 <;> norm_num
                  exact Batch0363.cell2908.sound htau (by
                    simp only [Batch0363.cell2908, Batch0363.tau2908, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10000120 (by positivity) using 1 <;> norm_num)
                · have hs10000122 : InSquare (9/640) (-249/640) (1/640) tau := by
                    convert childUL hs1000012 hx1000012 hy1000012 using 1 <;> norm_num
                  exact Batch0363.cell2910.sound htau (by
                    simp only [Batch0363.cell2910, Batch0363.tau2910, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10000122 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-25/64 : ℝ) with hy1000012 | hy1000012
                · have hs10000121 : InSquare (11/640) (-251/640) (1/640) tau := by
                    convert childLR hs1000012 hx1000012 hy1000012 using 1 <;> norm_num
                  exact Batch0363.cell2909.sound htau (by
                    simp only [Batch0363.cell2909, Batch0363.tau2909, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10000121 (by positivity) using 1 <;> norm_num)
                · have hs10000123 : InSquare (11/640) (-249/640) (1/640) tau := by
                    convert childUR hs1000012 hx1000012 hy1000012 using 1 <;> norm_num
                  exact Batch0363.cell2911.sound htau (by
                    simp only [Batch0363.cell2911, Batch0363.tau2911, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10000123 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-63/160 : ℝ) with hy100001 | hy100001
            · have hs1000011 : InSquare (7/320) (-127/320) (1/320) tau := by
                convert childLR hs100001 hx100001 hy100001 using 1 <;> norm_num
              rcases le_total tau.re (7/320 : ℝ) with hx1000011 | hx1000011
              · rcases le_total tau.im (-127/320 : ℝ) with hy1000011 | hy1000011
                · have hs10000110 : InSquare (13/640) (-51/128) (1/640) tau := by
                    convert childLL hs1000011 hx1000011 hy1000011 using 1 <;> norm_num
                  exact Batch0363.cell2904.sound htau (by
                    simp only [Batch0363.cell2904, Batch0363.tau2904, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10000110 (by positivity) using 1 <;> norm_num)
                · have hs10000112 : InSquare (13/640) (-253/640) (1/640) tau := by
                    convert childUL hs1000011 hx1000011 hy1000011 using 1 <;> norm_num
                  exact Batch0363.cell2906.sound htau (by
                    simp only [Batch0363.cell2906, Batch0363.tau2906, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10000112 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-127/320 : ℝ) with hy1000011 | hy1000011
                · have hs10000111 : InSquare (3/128) (-51/128) (1/640) tau := by
                    convert childLR hs1000011 hx1000011 hy1000011 using 1 <;> norm_num
                  exact Batch0363.cell2905.sound htau (by
                    simp only [Batch0363.cell2905, Batch0363.tau2905, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10000111 (by positivity) using 1 <;> norm_num)
                · have hs10000113 : InSquare (3/128) (-253/640) (1/640) tau := by
                    convert childUR hs1000011 hx1000011 hy1000011 using 1 <;> norm_num
                  exact Batch0363.cell2907.sound htau (by
                    simp only [Batch0363.cell2907, Batch0363.tau2907, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10000113 (by positivity) using 1 <;> norm_num)
            · have hs1000013 : InSquare (7/320) (-25/64) (1/320) tau := by
                convert childUR hs100001 hx100001 hy100001 using 1 <;> norm_num
              rcases le_total tau.re (7/320 : ℝ) with hx1000013 | hx1000013
              · rcases le_total tau.im (-25/64 : ℝ) with hy1000013 | hy1000013
                · have hs10000130 : InSquare (13/640) (-251/640) (1/640) tau := by
                    convert childLL hs1000013 hx1000013 hy1000013 using 1 <;> norm_num
                  exact Batch0364.cell2912.sound htau (by
                    simp only [Batch0364.cell2912, Batch0364.tau2912, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10000130 (by positivity) using 1 <;> norm_num)
                · have hs10000132 : InSquare (13/640) (-249/640) (1/640) tau := by
                    convert childUL hs1000013 hx1000013 hy1000013 using 1 <;> norm_num
                  exact Batch0364.cell2914.sound htau (by
                    simp only [Batch0364.cell2914, Batch0364.tau2914, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10000132 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-25/64 : ℝ) with hy1000013 | hy1000013
                · have hs10000131 : InSquare (3/128) (-251/640) (1/640) tau := by
                    convert childLR hs1000013 hx1000013 hy1000013 using 1 <;> norm_num
                  exact Batch0364.cell2913.sound htau (by
                    simp only [Batch0364.cell2913, Batch0364.tau2913, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10000131 (by positivity) using 1 <;> norm_num)
                · have hs10000133 : InSquare (3/128) (-249/640) (1/640) tau := by
                    convert childUR hs1000013 hx1000013 hy1000013 using 1 <;> norm_num
                  exact Batch0364.cell2915.sound htau (by
                    simp only [Batch0364.cell2915, Batch0364.tau2915, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10000133 (by positivity) using 1 <;> norm_num)
        · have hs100003 : InSquare (3/160) (-61/160) (1/160) tau := by
            convert childUR hs10000 hx10000 hy10000 using 1 <;> norm_num
          rcases le_total tau.re (3/160 : ℝ) with hx100003 | hx100003
          · rcases le_total tau.im (-61/160 : ℝ) with hy100003 | hy100003
            · have hs1000030 : InSquare (1/64) (-123/320) (1/320) tau := by
                convert childLL hs100003 hx100003 hy100003 using 1 <;> norm_num
              exact Batch0193.cell1545.sound htau (by
                simp only [Batch0193.cell1545, Batch0193.tau1545, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1000030 (by positivity) using 1 <;> norm_num)
            · have hs1000032 : InSquare (1/64) (-121/320) (1/320) tau := by
                convert childUL hs100003 hx100003 hy100003 using 1 <;> norm_num
              exact Batch0193.cell1547.sound htau (by
                simp only [Batch0193.cell1547, Batch0193.tau1547, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1000032 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-61/160 : ℝ) with hy100003 | hy100003
            · have hs1000031 : InSquare (7/320) (-123/320) (1/320) tau := by
                convert childLR hs100003 hx100003 hy100003 using 1 <;> norm_num
              exact Batch0193.cell1546.sound htau (by
                simp only [Batch0193.cell1546, Batch0193.tau1546, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1000031 (by positivity) using 1 <;> norm_num)
            · have hs1000033 : InSquare (7/320) (-121/320) (1/320) tau := by
                convert childUR hs100003 hx100003 hy100003 using 1 <;> norm_num
              exact Batch0193.cell1548.sound htau (by
                simp only [Batch0193.cell1548, Batch0193.tau1548, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1000033 (by positivity) using 1 <;> norm_num)
    · have hs10002 : InSquare (1/80) (-29/80) (1/80) tau := by
        convert childUL hs hx1000 hy1000 using 1 <;> norm_num
      rcases le_total tau.re (1/80 : ℝ) with hx10002 | hx10002
      · rcases le_total tau.im (-29/80 : ℝ) with hy10002 | hy10002
        · have hs100020 : InSquare (1/160) (-59/160) (1/160) tau := by
            convert childLL hs10002 hx10002 hy10002 using 1 <;> norm_num
          rcases le_total tau.re (1/160 : ℝ) with hx100020 | hx100020
          · rcases le_total tau.im (-59/160 : ℝ) with hy100020 | hy100020
            · have hs1000200 : InSquare (1/320) (-119/320) (1/320) tau := by
                convert childLL hs100020 hx100020 hy100020 using 1 <;> norm_num
              exact Batch0194.cell1554.sound htau (by
                simp only [Batch0194.cell1554, Batch0194.tau1554, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1000200 (by positivity) using 1 <;> norm_num)
            · have hs1000202 : InSquare (1/320) (-117/320) (1/320) tau := by
                convert childUL hs100020 hx100020 hy100020 using 1 <;> norm_num
              exact Batch0194.cell1556.sound htau (by
                simp only [Batch0194.cell1556, Batch0194.tau1556, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1000202 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-59/160 : ℝ) with hy100020 | hy100020
            · have hs1000201 : InSquare (3/320) (-119/320) (1/320) tau := by
                convert childLR hs100020 hx100020 hy100020 using 1 <;> norm_num
              exact Batch0194.cell1555.sound htau (by
                simp only [Batch0194.cell1555, Batch0194.tau1555, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1000201 (by positivity) using 1 <;> norm_num)
            · have hs1000203 : InSquare (3/320) (-117/320) (1/320) tau := by
                convert childUR hs100020 hx100020 hy100020 using 1 <;> norm_num
              exact Batch0194.cell1557.sound htau (by
                simp only [Batch0194.cell1557, Batch0194.tau1557, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1000203 (by positivity) using 1 <;> norm_num)
        · have hs100022 : InSquare (1/160) (-57/160) (1/160) tau := by
            convert childUL hs10002 hx10002 hy10002 using 1 <;> norm_num
          exact Batch0069.cell0558.sound htau (by
            simp only [Batch0069.cell0558, Batch0069.tau0558, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs100022 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-29/80 : ℝ) with hy10002 | hy10002
        · have hs100021 : InSquare (3/160) (-59/160) (1/160) tau := by
            convert childLR hs10002 hx10002 hy10002 using 1 <;> norm_num
          rcases le_total tau.re (3/160 : ℝ) with hx100021 | hx100021
          · rcases le_total tau.im (-59/160 : ℝ) with hy100021 | hy100021
            · have hs1000210 : InSquare (1/64) (-119/320) (1/320) tau := by
                convert childLL hs100021 hx100021 hy100021 using 1 <;> norm_num
              exact Batch0194.cell1558.sound htau (by
                simp only [Batch0194.cell1558, Batch0194.tau1558, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1000210 (by positivity) using 1 <;> norm_num)
            · have hs1000212 : InSquare (1/64) (-117/320) (1/320) tau := by
                convert childUL hs100021 hx100021 hy100021 using 1 <;> norm_num
              exact Batch0195.cell1560.sound htau (by
                simp only [Batch0195.cell1560, Batch0195.tau1560, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1000212 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-59/160 : ℝ) with hy100021 | hy100021
            · have hs1000211 : InSquare (7/320) (-119/320) (1/320) tau := by
                convert childLR hs100021 hx100021 hy100021 using 1 <;> norm_num
              exact Batch0194.cell1559.sound htau (by
                simp only [Batch0194.cell1559, Batch0194.tau1559, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1000211 (by positivity) using 1 <;> norm_num)
            · have hs1000213 : InSquare (7/320) (-117/320) (1/320) tau := by
                convert childUR hs100021 hx100021 hy100021 using 1 <;> norm_num
              exact Batch0195.cell1561.sound htau (by
                simp only [Batch0195.cell1561, Batch0195.tau1561, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1000213 (by positivity) using 1 <;> norm_num)
        · have hs100023 : InSquare (3/160) (-57/160) (1/160) tau := by
            convert childUR hs10002 hx10002 hy10002 using 1 <;> norm_num
          rcases le_total tau.re (3/160 : ℝ) with hx100023 | hx100023
          · rcases le_total tau.im (-57/160 : ℝ) with hy100023 | hy100023
            · have hs1000230 : InSquare (1/64) (-23/64) (1/320) tau := by
                convert childLL hs100023 hx100023 hy100023 using 1 <;> norm_num
              exact Batch0195.cell1562.sound htau (by
                simp only [Batch0195.cell1562, Batch0195.tau1562, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1000230 (by positivity) using 1 <;> norm_num)
            · have hs1000232 : InSquare (1/64) (-113/320) (1/320) tau := by
                convert childUL hs100023 hx100023 hy100023 using 1 <;> norm_num
              exact Batch0195.cell1564.sound htau (by
                simp only [Batch0195.cell1564, Batch0195.tau1564, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1000232 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-57/160 : ℝ) with hy100023 | hy100023
            · have hs1000231 : InSquare (7/320) (-23/64) (1/320) tau := by
                convert childLR hs100023 hx100023 hy100023 using 1 <;> norm_num
              exact Batch0195.cell1563.sound htau (by
                simp only [Batch0195.cell1563, Batch0195.tau1563, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1000231 (by positivity) using 1 <;> norm_num)
            · have hs1000233 : InSquare (7/320) (-113/320) (1/320) tau := by
                convert childUR hs100023 hx100023 hy100023 using 1 <;> norm_num
              exact Batch0195.cell1565.sound htau (by
                simp only [Batch0195.cell1565, Batch0195.tau1565, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1000233 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (-3/8 : ℝ) with hy1000 | hy1000
    · have hs10001 : InSquare (3/80) (-31/80) (1/80) tau := by
        convert childLR hs hx1000 hy1000 using 1 <;> norm_num
      rcases le_total tau.re (3/80 : ℝ) with hx10001 | hx10001
      · rcases le_total tau.im (-31/80 : ℝ) with hy10001 | hy10001
        · have hs100010 : InSquare (1/32) (-63/160) (1/160) tau := by
            convert childLL hs10001 hx10001 hy10001 using 1 <;> norm_num
          rcases le_total tau.re (1/32 : ℝ) with hx100010 | hx100010
          · rcases le_total tau.im (-63/160 : ℝ) with hy100010 | hy100010
            · have hs1000100 : InSquare (9/320) (-127/320) (1/320) tau := by
                convert childLL hs100010 hx100010 hy100010 using 1 <;> norm_num
              rcases le_total tau.re (9/320 : ℝ) with hx1000100 | hx1000100
              · rcases le_total tau.im (-127/320 : ℝ) with hy1000100 | hy1000100
                · have hs10001000 : InSquare (17/640) (-51/128) (1/640) tau := by
                    convert childLL hs1000100 hx1000100 hy1000100 using 1 <;> norm_num
                  exact Batch0364.cell2916.sound htau (by
                    simp only [Batch0364.cell2916, Batch0364.tau2916, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10001000 (by positivity) using 1 <;> norm_num)
                · have hs10001002 : InSquare (17/640) (-253/640) (1/640) tau := by
                    convert childUL hs1000100 hx1000100 hy1000100 using 1 <;> norm_num
                  exact Batch0364.cell2918.sound htau (by
                    simp only [Batch0364.cell2918, Batch0364.tau2918, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10001002 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-127/320 : ℝ) with hy1000100 | hy1000100
                · have hs10001001 : InSquare (19/640) (-51/128) (1/640) tau := by
                    convert childLR hs1000100 hx1000100 hy1000100 using 1 <;> norm_num
                  exact Batch0364.cell2917.sound htau (by
                    simp only [Batch0364.cell2917, Batch0364.tau2917, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10001001 (by positivity) using 1 <;> norm_num)
                · have hs10001003 : InSquare (19/640) (-253/640) (1/640) tau := by
                    convert childUR hs1000100 hx1000100 hy1000100 using 1 <;> norm_num
                  exact Batch0364.cell2919.sound htau (by
                    simp only [Batch0364.cell2919, Batch0364.tau2919, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10001003 (by positivity) using 1 <;> norm_num)
            · have hs1000102 : InSquare (9/320) (-25/64) (1/320) tau := by
                convert childUL hs100010 hx100010 hy100010 using 1 <;> norm_num
              rcases le_total tau.re (9/320 : ℝ) with hx1000102 | hx1000102
              · rcases le_total tau.im (-25/64 : ℝ) with hy1000102 | hy1000102
                · have hs10001020 : InSquare (17/640) (-251/640) (1/640) tau := by
                    convert childLL hs1000102 hx1000102 hy1000102 using 1 <;> norm_num
                  exact Batch0365.cell2924.sound htau (by
                    simp only [Batch0365.cell2924, Batch0365.tau2924, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10001020 (by positivity) using 1 <;> norm_num)
                · have hs10001022 : InSquare (17/640) (-249/640) (1/640) tau := by
                    convert childUL hs1000102 hx1000102 hy1000102 using 1 <;> norm_num
                  exact Batch0365.cell2926.sound htau (by
                    simp only [Batch0365.cell2926, Batch0365.tau2926, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10001022 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-25/64 : ℝ) with hy1000102 | hy1000102
                · have hs10001021 : InSquare (19/640) (-251/640) (1/640) tau := by
                    convert childLR hs1000102 hx1000102 hy1000102 using 1 <;> norm_num
                  exact Batch0365.cell2925.sound htau (by
                    simp only [Batch0365.cell2925, Batch0365.tau2925, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10001021 (by positivity) using 1 <;> norm_num)
                · have hs10001023 : InSquare (19/640) (-249/640) (1/640) tau := by
                    convert childUR hs1000102 hx1000102 hy1000102 using 1 <;> norm_num
                  exact Batch0365.cell2927.sound htau (by
                    simp only [Batch0365.cell2927, Batch0365.tau2927, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10001023 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-63/160 : ℝ) with hy100010 | hy100010
            · have hs1000101 : InSquare (11/320) (-127/320) (1/320) tau := by
                convert childLR hs100010 hx100010 hy100010 using 1 <;> norm_num
              rcases le_total tau.re (11/320 : ℝ) with hx1000101 | hx1000101
              · rcases le_total tau.im (-127/320 : ℝ) with hy1000101 | hy1000101
                · have hs10001010 : InSquare (21/640) (-51/128) (1/640) tau := by
                    convert childLL hs1000101 hx1000101 hy1000101 using 1 <;> norm_num
                  exact Batch0365.cell2920.sound htau (by
                    simp only [Batch0365.cell2920, Batch0365.tau2920, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10001010 (by positivity) using 1 <;> norm_num)
                · have hs10001012 : InSquare (21/640) (-253/640) (1/640) tau := by
                    convert childUL hs1000101 hx1000101 hy1000101 using 1 <;> norm_num
                  exact Batch0365.cell2922.sound htau (by
                    simp only [Batch0365.cell2922, Batch0365.tau2922, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10001012 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-127/320 : ℝ) with hy1000101 | hy1000101
                · have hs10001011 : InSquare (23/640) (-51/128) (1/640) tau := by
                    convert childLR hs1000101 hx1000101 hy1000101 using 1 <;> norm_num
                  exact Batch0365.cell2921.sound htau (by
                    simp only [Batch0365.cell2921, Batch0365.tau2921, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10001011 (by positivity) using 1 <;> norm_num)
                · have hs10001013 : InSquare (23/640) (-253/640) (1/640) tau := by
                    convert childUR hs1000101 hx1000101 hy1000101 using 1 <;> norm_num
                  exact Batch0365.cell2923.sound htau (by
                    simp only [Batch0365.cell2923, Batch0365.tau2923, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10001013 (by positivity) using 1 <;> norm_num)
            · have hs1000103 : InSquare (11/320) (-25/64) (1/320) tau := by
                convert childUR hs100010 hx100010 hy100010 using 1 <;> norm_num
              rcases le_total tau.re (11/320 : ℝ) with hx1000103 | hx1000103
              · rcases le_total tau.im (-25/64 : ℝ) with hy1000103 | hy1000103
                · have hs10001030 : InSquare (21/640) (-251/640) (1/640) tau := by
                    convert childLL hs1000103 hx1000103 hy1000103 using 1 <;> norm_num
                  exact Batch0366.cell2928.sound htau (by
                    simp only [Batch0366.cell2928, Batch0366.tau2928, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10001030 (by positivity) using 1 <;> norm_num)
                · have hs10001032 : InSquare (21/640) (-249/640) (1/640) tau := by
                    convert childUL hs1000103 hx1000103 hy1000103 using 1 <;> norm_num
                  exact Batch0366.cell2930.sound htau (by
                    simp only [Batch0366.cell2930, Batch0366.tau2930, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10001032 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-25/64 : ℝ) with hy1000103 | hy1000103
                · have hs10001031 : InSquare (23/640) (-251/640) (1/640) tau := by
                    convert childLR hs1000103 hx1000103 hy1000103 using 1 <;> norm_num
                  exact Batch0366.cell2929.sound htau (by
                    simp only [Batch0366.cell2929, Batch0366.tau2929, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10001031 (by positivity) using 1 <;> norm_num)
                · have hs10001033 : InSquare (23/640) (-249/640) (1/640) tau := by
                    convert childUR hs1000103 hx1000103 hy1000103 using 1 <;> norm_num
                  exact Batch0366.cell2931.sound htau (by
                    simp only [Batch0366.cell2931, Batch0366.tau2931, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10001033 (by positivity) using 1 <;> norm_num)
        · have hs100012 : InSquare (1/32) (-61/160) (1/160) tau := by
            convert childUL hs10001 hx10001 hy10001 using 1 <;> norm_num
          rcases le_total tau.re (1/32 : ℝ) with hx100012 | hx100012
          · rcases le_total tau.im (-61/160 : ℝ) with hy100012 | hy100012
            · have hs1000120 : InSquare (9/320) (-123/320) (1/320) tau := by
                convert childLL hs100012 hx100012 hy100012 using 1 <;> norm_num
              exact Batch0193.cell1549.sound htau (by
                simp only [Batch0193.cell1549, Batch0193.tau1549, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1000120 (by positivity) using 1 <;> norm_num)
            · have hs1000122 : InSquare (9/320) (-121/320) (1/320) tau := by
                convert childUL hs100012 hx100012 hy100012 using 1 <;> norm_num
              exact Batch0193.cell1550.sound htau (by
                simp only [Batch0193.cell1550, Batch0193.tau1550, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1000122 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-61/160 : ℝ) with hy100012 | hy100012
            · have hs1000121 : InSquare (11/320) (-123/320) (1/320) tau := by
                convert childLR hs100012 hx100012 hy100012 using 1 <;> norm_num
              rcases le_total tau.re (11/320 : ℝ) with hx1000121 | hx1000121
              · rcases le_total tau.im (-123/320 : ℝ) with hy1000121 | hy1000121
                · have hs10001210 : InSquare (21/640) (-247/640) (1/640) tau := by
                    convert childLL hs1000121 hx1000121 hy1000121 using 1 <;> norm_num
                  exact Batch0368.cell2948.sound htau (by
                    simp only [Batch0368.cell2948, Batch0368.tau2948, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10001210 (by positivity) using 1 <;> norm_num)
                · have hs10001212 : InSquare (21/640) (-49/128) (1/640) tau := by
                    convert childUL hs1000121 hx1000121 hy1000121 using 1 <;> norm_num
                  exact Batch0368.cell2950.sound htau (by
                    simp only [Batch0368.cell2950, Batch0368.tau2950, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10001212 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-123/320 : ℝ) with hy1000121 | hy1000121
                · have hs10001211 : InSquare (23/640) (-247/640) (1/640) tau := by
                    convert childLR hs1000121 hx1000121 hy1000121 using 1 <;> norm_num
                  exact Batch0368.cell2949.sound htau (by
                    simp only [Batch0368.cell2949, Batch0368.tau2949, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10001211 (by positivity) using 1 <;> norm_num)
                · have hs10001213 : InSquare (23/640) (-49/128) (1/640) tau := by
                    convert childUR hs1000121 hx1000121 hy1000121 using 1 <;> norm_num
                  exact Batch0368.cell2951.sound htau (by
                    simp only [Batch0368.cell2951, Batch0368.tau2951, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10001213 (by positivity) using 1 <;> norm_num)
            · have hs1000123 : InSquare (11/320) (-121/320) (1/320) tau := by
                convert childUR hs100012 hx100012 hy100012 using 1 <;> norm_num
              exact Batch0193.cell1551.sound htau (by
                simp only [Batch0193.cell1551, Batch0193.tau1551, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1000123 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-31/80 : ℝ) with hy10001 | hy10001
        · have hs100011 : InSquare (7/160) (-63/160) (1/160) tau := by
            convert childLR hs10001 hx10001 hy10001 using 1 <;> norm_num
          rcases le_total tau.re (7/160 : ℝ) with hx100011 | hx100011
          · rcases le_total tau.im (-63/160 : ℝ) with hy100011 | hy100011
            · have hs1000110 : InSquare (13/320) (-127/320) (1/320) tau := by
                convert childLL hs100011 hx100011 hy100011 using 1 <;> norm_num
              rcases le_total tau.re (13/320 : ℝ) with hx1000110 | hx1000110
              · rcases le_total tau.im (-127/320 : ℝ) with hy1000110 | hy1000110
                · have hs10001100 : InSquare (5/128) (-51/128) (1/640) tau := by
                    convert childLL hs1000110 hx1000110 hy1000110 using 1 <;> norm_num
                  exact Batch0366.cell2932.sound htau (by
                    simp only [Batch0366.cell2932, Batch0366.tau2932, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10001100 (by positivity) using 1 <;> norm_num)
                · have hs10001102 : InSquare (5/128) (-253/640) (1/640) tau := by
                    convert childUL hs1000110 hx1000110 hy1000110 using 1 <;> norm_num
                  exact Batch0366.cell2934.sound htau (by
                    simp only [Batch0366.cell2934, Batch0366.tau2934, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10001102 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-127/320 : ℝ) with hy1000110 | hy1000110
                · have hs10001101 : InSquare (27/640) (-51/128) (1/640) tau := by
                    convert childLR hs1000110 hx1000110 hy1000110 using 1 <;> norm_num
                  exact Batch0366.cell2933.sound htau (by
                    simp only [Batch0366.cell2933, Batch0366.tau2933, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10001101 (by positivity) using 1 <;> norm_num)
                · have hs10001103 : InSquare (27/640) (-253/640) (1/640) tau := by
                    convert childUR hs1000110 hx1000110 hy1000110 using 1 <;> norm_num
                  exact Batch0366.cell2935.sound htau (by
                    simp only [Batch0366.cell2935, Batch0366.tau2935, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10001103 (by positivity) using 1 <;> norm_num)
            · have hs1000112 : InSquare (13/320) (-25/64) (1/320) tau := by
                convert childUL hs100011 hx100011 hy100011 using 1 <;> norm_num
              rcases le_total tau.re (13/320 : ℝ) with hx1000112 | hx1000112
              · rcases le_total tau.im (-25/64 : ℝ) with hy1000112 | hy1000112
                · have hs10001120 : InSquare (5/128) (-251/640) (1/640) tau := by
                    convert childLL hs1000112 hx1000112 hy1000112 using 1 <;> norm_num
                  exact Batch0367.cell2940.sound htau (by
                    simp only [Batch0367.cell2940, Batch0367.tau2940, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10001120 (by positivity) using 1 <;> norm_num)
                · have hs10001122 : InSquare (5/128) (-249/640) (1/640) tau := by
                    convert childUL hs1000112 hx1000112 hy1000112 using 1 <;> norm_num
                  exact Batch0367.cell2942.sound htau (by
                    simp only [Batch0367.cell2942, Batch0367.tau2942, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10001122 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-25/64 : ℝ) with hy1000112 | hy1000112
                · have hs10001121 : InSquare (27/640) (-251/640) (1/640) tau := by
                    convert childLR hs1000112 hx1000112 hy1000112 using 1 <;> norm_num
                  exact Batch0367.cell2941.sound htau (by
                    simp only [Batch0367.cell2941, Batch0367.tau2941, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10001121 (by positivity) using 1 <;> norm_num)
                · have hs10001123 : InSquare (27/640) (-249/640) (1/640) tau := by
                    convert childUR hs1000112 hx1000112 hy1000112 using 1 <;> norm_num
                  exact Batch0367.cell2943.sound htau (by
                    simp only [Batch0367.cell2943, Batch0367.tau2943, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10001123 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-63/160 : ℝ) with hy100011 | hy100011
            · have hs1000111 : InSquare (3/64) (-127/320) (1/320) tau := by
                convert childLR hs100011 hx100011 hy100011 using 1 <;> norm_num
              rcases le_total tau.re (3/64 : ℝ) with hx1000111 | hx1000111
              · rcases le_total tau.im (-127/320 : ℝ) with hy1000111 | hy1000111
                · have hs10001110 : InSquare (29/640) (-51/128) (1/640) tau := by
                    convert childLL hs1000111 hx1000111 hy1000111 using 1 <;> norm_num
                  exact Batch0367.cell2936.sound htau (by
                    simp only [Batch0367.cell2936, Batch0367.tau2936, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10001110 (by positivity) using 1 <;> norm_num)
                · have hs10001112 : InSquare (29/640) (-253/640) (1/640) tau := by
                    convert childUL hs1000111 hx1000111 hy1000111 using 1 <;> norm_num
                  exact Batch0367.cell2938.sound htau (by
                    simp only [Batch0367.cell2938, Batch0367.tau2938, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10001112 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-127/320 : ℝ) with hy1000111 | hy1000111
                · have hs10001111 : InSquare (31/640) (-51/128) (1/640) tau := by
                    convert childLR hs1000111 hx1000111 hy1000111 using 1 <;> norm_num
                  exact Batch0367.cell2937.sound htau (by
                    simp only [Batch0367.cell2937, Batch0367.tau2937, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10001111 (by positivity) using 1 <;> norm_num)
                · have hs10001113 : InSquare (31/640) (-253/640) (1/640) tau := by
                    convert childUR hs1000111 hx1000111 hy1000111 using 1 <;> norm_num
                  exact Batch0367.cell2939.sound htau (by
                    simp only [Batch0367.cell2939, Batch0367.tau2939, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10001113 (by positivity) using 1 <;> norm_num)
            · have hs1000113 : InSquare (3/64) (-25/64) (1/320) tau := by
                convert childUR hs100011 hx100011 hy100011 using 1 <;> norm_num
              rcases le_total tau.re (3/64 : ℝ) with hx1000113 | hx1000113
              · rcases le_total tau.im (-25/64 : ℝ) with hy1000113 | hy1000113
                · have hs10001130 : InSquare (29/640) (-251/640) (1/640) tau := by
                    convert childLL hs1000113 hx1000113 hy1000113 using 1 <;> norm_num
                  exact Batch0368.cell2944.sound htau (by
                    simp only [Batch0368.cell2944, Batch0368.tau2944, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10001130 (by positivity) using 1 <;> norm_num)
                · have hs10001132 : InSquare (29/640) (-249/640) (1/640) tau := by
                    convert childUL hs1000113 hx1000113 hy1000113 using 1 <;> norm_num
                  exact Batch0368.cell2946.sound htau (by
                    simp only [Batch0368.cell2946, Batch0368.tau2946, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10001132 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-25/64 : ℝ) with hy1000113 | hy1000113
                · have hs10001131 : InSquare (31/640) (-251/640) (1/640) tau := by
                    convert childLR hs1000113 hx1000113 hy1000113 using 1 <;> norm_num
                  exact Batch0368.cell2945.sound htau (by
                    simp only [Batch0368.cell2945, Batch0368.tau2945, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10001131 (by positivity) using 1 <;> norm_num)
                · have hs10001133 : InSquare (31/640) (-249/640) (1/640) tau := by
                    convert childUR hs1000113 hx1000113 hy1000113 using 1 <;> norm_num
                  exact Batch0368.cell2947.sound htau (by
                    simp only [Batch0368.cell2947, Batch0368.tau2947, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10001133 (by positivity) using 1 <;> norm_num)
        · have hs100013 : InSquare (7/160) (-61/160) (1/160) tau := by
            convert childUR hs10001 hx10001 hy10001 using 1 <;> norm_num
          rcases le_total tau.re (7/160 : ℝ) with hx100013 | hx100013
          · rcases le_total tau.im (-61/160 : ℝ) with hy100013 | hy100013
            · have hs1000130 : InSquare (13/320) (-123/320) (1/320) tau := by
                convert childLL hs100013 hx100013 hy100013 using 1 <;> norm_num
              rcases le_total tau.re (13/320 : ℝ) with hx1000130 | hx1000130
              · rcases le_total tau.im (-123/320 : ℝ) with hy1000130 | hy1000130
                · have hs10001300 : InSquare (5/128) (-247/640) (1/640) tau := by
                    convert childLL hs1000130 hx1000130 hy1000130 using 1 <;> norm_num
                  exact Batch0369.cell2952.sound htau (by
                    simp only [Batch0369.cell2952, Batch0369.tau2952, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10001300 (by positivity) using 1 <;> norm_num)
                · have hs10001302 : InSquare (5/128) (-49/128) (1/640) tau := by
                    convert childUL hs1000130 hx1000130 hy1000130 using 1 <;> norm_num
                  exact Batch0369.cell2954.sound htau (by
                    simp only [Batch0369.cell2954, Batch0369.tau2954, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10001302 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-123/320 : ℝ) with hy1000130 | hy1000130
                · have hs10001301 : InSquare (27/640) (-247/640) (1/640) tau := by
                    convert childLR hs1000130 hx1000130 hy1000130 using 1 <;> norm_num
                  exact Batch0369.cell2953.sound htau (by
                    simp only [Batch0369.cell2953, Batch0369.tau2953, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10001301 (by positivity) using 1 <;> norm_num)
                · have hs10001303 : InSquare (27/640) (-49/128) (1/640) tau := by
                    convert childUR hs1000130 hx1000130 hy1000130 using 1 <;> norm_num
                  exact Batch0369.cell2955.sound htau (by
                    simp only [Batch0369.cell2955, Batch0369.tau2955, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10001303 (by positivity) using 1 <;> norm_num)
            · have hs1000132 : InSquare (13/320) (-121/320) (1/320) tau := by
                convert childUL hs100013 hx100013 hy100013 using 1 <;> norm_num
              exact Batch0194.cell1552.sound htau (by
                simp only [Batch0194.cell1552, Batch0194.tau1552, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1000132 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-61/160 : ℝ) with hy100013 | hy100013
            · have hs1000131 : InSquare (3/64) (-123/320) (1/320) tau := by
                convert childLR hs100013 hx100013 hy100013 using 1 <;> norm_num
              rcases le_total tau.re (3/64 : ℝ) with hx1000131 | hx1000131
              · rcases le_total tau.im (-123/320 : ℝ) with hy1000131 | hy1000131
                · have hs10001310 : InSquare (29/640) (-247/640) (1/640) tau := by
                    convert childLL hs1000131 hx1000131 hy1000131 using 1 <;> norm_num
                  exact Batch0369.cell2956.sound htau (by
                    simp only [Batch0369.cell2956, Batch0369.tau2956, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10001310 (by positivity) using 1 <;> norm_num)
                · have hs10001312 : InSquare (29/640) (-49/128) (1/640) tau := by
                    convert childUL hs1000131 hx1000131 hy1000131 using 1 <;> norm_num
                  exact Batch0369.cell2958.sound htau (by
                    simp only [Batch0369.cell2958, Batch0369.tau2958, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10001312 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-123/320 : ℝ) with hy1000131 | hy1000131
                · have hs10001311 : InSquare (31/640) (-247/640) (1/640) tau := by
                    convert childLR hs1000131 hx1000131 hy1000131 using 1 <;> norm_num
                  exact Batch0369.cell2957.sound htau (by
                    simp only [Batch0369.cell2957, Batch0369.tau2957, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10001311 (by positivity) using 1 <;> norm_num)
                · have hs10001313 : InSquare (31/640) (-49/128) (1/640) tau := by
                    convert childUR hs1000131 hx1000131 hy1000131 using 1 <;> norm_num
                  exact Batch0369.cell2959.sound htau (by
                    simp only [Batch0369.cell2959, Batch0369.tau2959, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10001313 (by positivity) using 1 <;> norm_num)
            · have hs1000133 : InSquare (3/64) (-121/320) (1/320) tau := by
                convert childUR hs100013 hx100013 hy100013 using 1 <;> norm_num
              exact Batch0194.cell1553.sound htau (by
                simp only [Batch0194.cell1553, Batch0194.tau1553, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1000133 (by positivity) using 1 <;> norm_num)
    · have hs10003 : InSquare (3/80) (-29/80) (1/80) tau := by
        convert childUR hs hx1000 hy1000 using 1 <;> norm_num
      rcases le_total tau.re (3/80 : ℝ) with hx10003 | hx10003
      · rcases le_total tau.im (-29/80 : ℝ) with hy10003 | hy10003
        · have hs100030 : InSquare (1/32) (-59/160) (1/160) tau := by
            convert childLL hs10003 hx10003 hy10003 using 1 <;> norm_num
          rcases le_total tau.re (1/32 : ℝ) with hx100030 | hx100030
          · rcases le_total tau.im (-59/160 : ℝ) with hy100030 | hy100030
            · have hs1000300 : InSquare (9/320) (-119/320) (1/320) tau := by
                convert childLL hs100030 hx100030 hy100030 using 1 <;> norm_num
              exact Batch0195.cell1566.sound htau (by
                simp only [Batch0195.cell1566, Batch0195.tau1566, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1000300 (by positivity) using 1 <;> norm_num)
            · have hs1000302 : InSquare (9/320) (-117/320) (1/320) tau := by
                convert childUL hs100030 hx100030 hy100030 using 1 <;> norm_num
              exact Batch0196.cell1568.sound htau (by
                simp only [Batch0196.cell1568, Batch0196.tau1568, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1000302 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-59/160 : ℝ) with hy100030 | hy100030
            · have hs1000301 : InSquare (11/320) (-119/320) (1/320) tau := by
                convert childLR hs100030 hx100030 hy100030 using 1 <;> norm_num
              exact Batch0195.cell1567.sound htau (by
                simp only [Batch0195.cell1567, Batch0195.tau1567, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1000301 (by positivity) using 1 <;> norm_num)
            · have hs1000303 : InSquare (11/320) (-117/320) (1/320) tau := by
                convert childUR hs100030 hx100030 hy100030 using 1 <;> norm_num
              exact Batch0196.cell1569.sound htau (by
                simp only [Batch0196.cell1569, Batch0196.tau1569, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1000303 (by positivity) using 1 <;> norm_num)
        · have hs100032 : InSquare (1/32) (-57/160) (1/160) tau := by
            convert childUL hs10003 hx10003 hy10003 using 1 <;> norm_num
          rcases le_total tau.re (1/32 : ℝ) with hx100032 | hx100032
          · rcases le_total tau.im (-57/160 : ℝ) with hy100032 | hy100032
            · have hs1000320 : InSquare (9/320) (-23/64) (1/320) tau := by
                convert childLL hs100032 hx100032 hy100032 using 1 <;> norm_num
              exact Batch0196.cell1574.sound htau (by
                simp only [Batch0196.cell1574, Batch0196.tau1574, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1000320 (by positivity) using 1 <;> norm_num)
            · have hs1000322 : InSquare (9/320) (-113/320) (1/320) tau := by
                convert childUL hs100032 hx100032 hy100032 using 1 <;> norm_num
              exact Batch0197.cell1576.sound htau (by
                simp only [Batch0197.cell1576, Batch0197.tau1576, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1000322 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-57/160 : ℝ) with hy100032 | hy100032
            · have hs1000321 : InSquare (11/320) (-23/64) (1/320) tau := by
                convert childLR hs100032 hx100032 hy100032 using 1 <;> norm_num
              exact Batch0196.cell1575.sound htau (by
                simp only [Batch0196.cell1575, Batch0196.tau1575, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1000321 (by positivity) using 1 <;> norm_num)
            · have hs1000323 : InSquare (11/320) (-113/320) (1/320) tau := by
                convert childUR hs100032 hx100032 hy100032 using 1 <;> norm_num
              exact Batch0197.cell1577.sound htau (by
                simp only [Batch0197.cell1577, Batch0197.tau1577, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1000323 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-29/80 : ℝ) with hy10003 | hy10003
        · have hs100031 : InSquare (7/160) (-59/160) (1/160) tau := by
            convert childLR hs10003 hx10003 hy10003 using 1 <;> norm_num
          rcases le_total tau.re (7/160 : ℝ) with hx100031 | hx100031
          · rcases le_total tau.im (-59/160 : ℝ) with hy100031 | hy100031
            · have hs1000310 : InSquare (13/320) (-119/320) (1/320) tau := by
                convert childLL hs100031 hx100031 hy100031 using 1 <;> norm_num
              exact Batch0196.cell1570.sound htau (by
                simp only [Batch0196.cell1570, Batch0196.tau1570, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1000310 (by positivity) using 1 <;> norm_num)
            · have hs1000312 : InSquare (13/320) (-117/320) (1/320) tau := by
                convert childUL hs100031 hx100031 hy100031 using 1 <;> norm_num
              exact Batch0196.cell1572.sound htau (by
                simp only [Batch0196.cell1572, Batch0196.tau1572, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1000312 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-59/160 : ℝ) with hy100031 | hy100031
            · have hs1000311 : InSquare (3/64) (-119/320) (1/320) tau := by
                convert childLR hs100031 hx100031 hy100031 using 1 <;> norm_num
              exact Batch0196.cell1571.sound htau (by
                simp only [Batch0196.cell1571, Batch0196.tau1571, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1000311 (by positivity) using 1 <;> norm_num)
            · have hs1000313 : InSquare (3/64) (-117/320) (1/320) tau := by
                convert childUR hs100031 hx100031 hy100031 using 1 <;> norm_num
              exact Batch0196.cell1573.sound htau (by
                simp only [Batch0196.cell1573, Batch0196.tau1573, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1000313 (by positivity) using 1 <;> norm_num)
        · have hs100033 : InSquare (7/160) (-57/160) (1/160) tau := by
            convert childUR hs10003 hx10003 hy10003 using 1 <;> norm_num
          rcases le_total tau.re (7/160 : ℝ) with hx100033 | hx100033
          · rcases le_total tau.im (-57/160 : ℝ) with hy100033 | hy100033
            · have hs1000330 : InSquare (13/320) (-23/64) (1/320) tau := by
                convert childLL hs100033 hx100033 hy100033 using 1 <;> norm_num
              exact Batch0197.cell1578.sound htau (by
                simp only [Batch0197.cell1578, Batch0197.tau1578, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1000330 (by positivity) using 1 <;> norm_num)
            · have hs1000332 : InSquare (13/320) (-113/320) (1/320) tau := by
                convert childUL hs100033 hx100033 hy100033 using 1 <;> norm_num
              exact Batch0197.cell1580.sound htau (by
                simp only [Batch0197.cell1580, Batch0197.tau1580, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1000332 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-57/160 : ℝ) with hy100033 | hy100033
            · have hs1000331 : InSquare (3/64) (-23/64) (1/320) tau := by
                convert childLR hs100033 hx100033 hy100033 using 1 <;> norm_num
              exact Batch0197.cell1579.sound htau (by
                simp only [Batch0197.cell1579, Batch0197.tau1579, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1000331 (by positivity) using 1 <;> norm_num)
            · have hs1000333 : InSquare (3/64) (-113/320) (1/320) tau := by
                convert childUR hs100033 hx100033 hy100033 using 1 <;> norm_num
              exact Batch0197.cell1581.sound htau (by
                simp only [Batch0197.cell1581, Batch0197.tau1581, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1000333 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1000
