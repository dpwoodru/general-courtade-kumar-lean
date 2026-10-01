import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0143
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0293
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0294
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0295
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0296
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0297
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0298
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0299
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0460
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0461

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3231

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (7/40) (13/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (7/40 : ℝ) with hx3231 | hx3231
  · rcases le_total tau.im (13/40 : ℝ) with hy3231 | hy3231
    · have hs32310 : InSquare (13/80) (5/16) (1/80) tau := by
        convert childLL hs hx3231 hy3231 using 1 <;> norm_num
      rcases le_total tau.re (13/80 : ℝ) with hx32310 | hx32310
      · rcases le_total tau.im (5/16 : ℝ) with hy32310 | hy32310
        · have hs323100 : InSquare (5/32) (49/160) (1/160) tau := by
            convert childLL hs32310 hx32310 hy32310 using 1 <;> norm_num
          exact Batch0143.cell1149.sound htau (by
            simp only [Batch0143.cell1149, Batch0143.tau1149, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs323100 (by positivity) using 1 <;> norm_num)
        · have hs323102 : InSquare (5/32) (51/160) (1/160) tau := by
            convert childUL hs32310 hx32310 hy32310 using 1 <;> norm_num
          rcases le_total tau.re (5/32 : ℝ) with hx323102 | hx323102
          · rcases le_total tau.im (51/160 : ℝ) with hy323102 | hy323102
            · have hs3231020 : InSquare (49/320) (101/320) (1/320) tau := by
                convert childLL hs323102 hx323102 hy323102 using 1 <;> norm_num
              exact Batch0293.cell2344.sound htau (by
                simp only [Batch0293.cell2344, Batch0293.tau2344, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3231020 (by positivity) using 1 <;> norm_num)
            · have hs3231022 : InSquare (49/320) (103/320) (1/320) tau := by
                convert childUL hs323102 hx323102 hy323102 using 1 <;> norm_num
              exact Batch0293.cell2346.sound htau (by
                simp only [Batch0293.cell2346, Batch0293.tau2346, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3231022 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (51/160 : ℝ) with hy323102 | hy323102
            · have hs3231021 : InSquare (51/320) (101/320) (1/320) tau := by
                convert childLR hs323102 hx323102 hy323102 using 1 <;> norm_num
              exact Batch0293.cell2345.sound htau (by
                simp only [Batch0293.cell2345, Batch0293.tau2345, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3231021 (by positivity) using 1 <;> norm_num)
            · have hs3231023 : InSquare (51/320) (103/320) (1/320) tau := by
                convert childUR hs323102 hx323102 hy323102 using 1 <;> norm_num
              exact Batch0293.cell2347.sound htau (by
                simp only [Batch0293.cell2347, Batch0293.tau2347, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3231023 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (5/16 : ℝ) with hy32310 | hy32310
        · have hs323101 : InSquare (27/160) (49/160) (1/160) tau := by
            convert childLR hs32310 hx32310 hy32310 using 1 <;> norm_num
          exact Batch0143.cell1150.sound htau (by
            simp only [Batch0143.cell1150, Batch0143.tau1150, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs323101 (by positivity) using 1 <;> norm_num)
        · have hs323103 : InSquare (27/160) (51/160) (1/160) tau := by
            convert childUR hs32310 hx32310 hy32310 using 1 <;> norm_num
          rcases le_total tau.re (27/160 : ℝ) with hx323103 | hx323103
          · rcases le_total tau.im (51/160 : ℝ) with hy323103 | hy323103
            · have hs3231030 : InSquare (53/320) (101/320) (1/320) tau := by
                convert childLL hs323103 hx323103 hy323103 using 1 <;> norm_num
              exact Batch0293.cell2348.sound htau (by
                simp only [Batch0293.cell2348, Batch0293.tau2348, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3231030 (by positivity) using 1 <;> norm_num)
            · have hs3231032 : InSquare (53/320) (103/320) (1/320) tau := by
                convert childUL hs323103 hx323103 hy323103 using 1 <;> norm_num
              exact Batch0293.cell2350.sound htau (by
                simp only [Batch0293.cell2350, Batch0293.tau2350, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3231032 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (51/160 : ℝ) with hy323103 | hy323103
            · have hs3231031 : InSquare (11/64) (101/320) (1/320) tau := by
                convert childLR hs323103 hx323103 hy323103 using 1 <;> norm_num
              exact Batch0293.cell2349.sound htau (by
                simp only [Batch0293.cell2349, Batch0293.tau2349, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3231031 (by positivity) using 1 <;> norm_num)
            · have hs3231033 : InSquare (11/64) (103/320) (1/320) tau := by
                convert childUR hs323103 hx323103 hy323103 using 1 <;> norm_num
              exact Batch0293.cell2351.sound htau (by
                simp only [Batch0293.cell2351, Batch0293.tau2351, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3231033 (by positivity) using 1 <;> norm_num)
    · have hs32312 : InSquare (13/80) (27/80) (1/80) tau := by
        convert childUL hs hx3231 hy3231 using 1 <;> norm_num
      rcases le_total tau.re (13/80 : ℝ) with hx32312 | hx32312
      · rcases le_total tau.im (27/80 : ℝ) with hy32312 | hy32312
        · have hs323120 : InSquare (5/32) (53/160) (1/160) tau := by
            convert childLL hs32312 hx32312 hy32312 using 1 <;> norm_num
          rcases le_total tau.re (5/32 : ℝ) with hx323120 | hx323120
          · rcases le_total tau.im (53/160 : ℝ) with hy323120 | hy323120
            · have hs3231200 : InSquare (49/320) (21/64) (1/320) tau := by
                convert childLL hs323120 hx323120 hy323120 using 1 <;> norm_num
              exact Batch0296.cell2368.sound htau (by
                simp only [Batch0296.cell2368, Batch0296.tau2368, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3231200 (by positivity) using 1 <;> norm_num)
            · have hs3231202 : InSquare (49/320) (107/320) (1/320) tau := by
                convert childUL hs323120 hx323120 hy323120 using 1 <;> norm_num
              exact Batch0296.cell2370.sound htau (by
                simp only [Batch0296.cell2370, Batch0296.tau2370, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3231202 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (53/160 : ℝ) with hy323120 | hy323120
            · have hs3231201 : InSquare (51/320) (21/64) (1/320) tau := by
                convert childLR hs323120 hx323120 hy323120 using 1 <;> norm_num
              exact Batch0296.cell2369.sound htau (by
                simp only [Batch0296.cell2369, Batch0296.tau2369, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3231201 (by positivity) using 1 <;> norm_num)
            · have hs3231203 : InSquare (51/320) (107/320) (1/320) tau := by
                convert childUR hs323120 hx323120 hy323120 using 1 <;> norm_num
              exact Batch0296.cell2371.sound htau (by
                simp only [Batch0296.cell2371, Batch0296.tau2371, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3231203 (by positivity) using 1 <;> norm_num)
        · have hs323122 : InSquare (5/32) (11/32) (1/160) tau := by
            convert childUL hs32312 hx32312 hy32312 using 1 <;> norm_num
          rcases le_total tau.re (5/32 : ℝ) with hx323122 | hx323122
          · rcases le_total tau.im (11/32 : ℝ) with hy323122 | hy323122
            · have hs3231220 : InSquare (49/320) (109/320) (1/320) tau := by
                convert childLL hs323122 hx323122 hy323122 using 1 <;> norm_num
              exact Batch0297.cell2376.sound htau (by
                simp only [Batch0297.cell2376, Batch0297.tau2376, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3231220 (by positivity) using 1 <;> norm_num)
            · have hs3231222 : InSquare (49/320) (111/320) (1/320) tau := by
                convert childUL hs323122 hx323122 hy323122 using 1 <;> norm_num
              exact Batch0297.cell2378.sound htau (by
                simp only [Batch0297.cell2378, Batch0297.tau2378, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3231222 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (11/32 : ℝ) with hy323122 | hy323122
            · have hs3231221 : InSquare (51/320) (109/320) (1/320) tau := by
                convert childLR hs323122 hx323122 hy323122 using 1 <;> norm_num
              exact Batch0297.cell2377.sound htau (by
                simp only [Batch0297.cell2377, Batch0297.tau2377, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3231221 (by positivity) using 1 <;> norm_num)
            · have hs3231223 : InSquare (51/320) (111/320) (1/320) tau := by
                convert childUR hs323122 hx323122 hy323122 using 1 <;> norm_num
              exact Batch0297.cell2379.sound htau (by
                simp only [Batch0297.cell2379, Batch0297.tau2379, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3231223 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (27/80 : ℝ) with hy32312 | hy32312
        · have hs323121 : InSquare (27/160) (53/160) (1/160) tau := by
            convert childLR hs32312 hx32312 hy32312 using 1 <;> norm_num
          rcases le_total tau.re (27/160 : ℝ) with hx323121 | hx323121
          · rcases le_total tau.im (53/160 : ℝ) with hy323121 | hy323121
            · have hs3231210 : InSquare (53/320) (21/64) (1/320) tau := by
                convert childLL hs323121 hx323121 hy323121 using 1 <;> norm_num
              exact Batch0296.cell2372.sound htau (by
                simp only [Batch0296.cell2372, Batch0296.tau2372, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3231210 (by positivity) using 1 <;> norm_num)
            · have hs3231212 : InSquare (53/320) (107/320) (1/320) tau := by
                convert childUL hs323121 hx323121 hy323121 using 1 <;> norm_num
              exact Batch0296.cell2374.sound htau (by
                simp only [Batch0296.cell2374, Batch0296.tau2374, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3231212 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (53/160 : ℝ) with hy323121 | hy323121
            · have hs3231211 : InSquare (11/64) (21/64) (1/320) tau := by
                convert childLR hs323121 hx323121 hy323121 using 1 <;> norm_num
              exact Batch0296.cell2373.sound htau (by
                simp only [Batch0296.cell2373, Batch0296.tau2373, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3231211 (by positivity) using 1 <;> norm_num)
            · have hs3231213 : InSquare (11/64) (107/320) (1/320) tau := by
                convert childUR hs323121 hx323121 hy323121 using 1 <;> norm_num
              exact Batch0296.cell2375.sound htau (by
                simp only [Batch0296.cell2375, Batch0296.tau2375, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3231213 (by positivity) using 1 <;> norm_num)
        · have hs323123 : InSquare (27/160) (11/32) (1/160) tau := by
            convert childUR hs32312 hx32312 hy32312 using 1 <;> norm_num
          rcases le_total tau.re (27/160 : ℝ) with hx323123 | hx323123
          · rcases le_total tau.im (11/32 : ℝ) with hy323123 | hy323123
            · have hs3231230 : InSquare (53/320) (109/320) (1/320) tau := by
                convert childLL hs323123 hx323123 hy323123 using 1 <;> norm_num
              exact Batch0297.cell2380.sound htau (by
                simp only [Batch0297.cell2380, Batch0297.tau2380, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3231230 (by positivity) using 1 <;> norm_num)
            · have hs3231232 : InSquare (53/320) (111/320) (1/320) tau := by
                convert childUL hs323123 hx323123 hy323123 using 1 <;> norm_num
              exact Batch0297.cell2382.sound htau (by
                simp only [Batch0297.cell2382, Batch0297.tau2382, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3231232 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (11/32 : ℝ) with hy323123 | hy323123
            · have hs3231231 : InSquare (11/64) (109/320) (1/320) tau := by
                convert childLR hs323123 hx323123 hy323123 using 1 <;> norm_num
              exact Batch0297.cell2381.sound htau (by
                simp only [Batch0297.cell2381, Batch0297.tau2381, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3231231 (by positivity) using 1 <;> norm_num)
            · have hs3231233 : InSquare (11/64) (111/320) (1/320) tau := by
                convert childUR hs323123 hx323123 hy323123 using 1 <;> norm_num
              exact Batch0297.cell2383.sound htau (by
                simp only [Batch0297.cell2383, Batch0297.tau2383, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3231233 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (13/40 : ℝ) with hy3231 | hy3231
    · have hs32311 : InSquare (3/16) (5/16) (1/80) tau := by
        convert childLR hs hx3231 hy3231 using 1 <;> norm_num
      rcases le_total tau.re (3/16 : ℝ) with hx32311 | hx32311
      · rcases le_total tau.im (5/16 : ℝ) with hy32311 | hy32311
        · have hs323110 : InSquare (29/160) (49/160) (1/160) tau := by
            convert childLL hs32311 hx32311 hy32311 using 1 <;> norm_num
          rcases le_total tau.re (29/160 : ℝ) with hx323110 | hx323110
          · rcases le_total tau.im (49/160 : ℝ) with hy323110 | hy323110
            · have hs3231100 : InSquare (57/320) (97/320) (1/320) tau := by
                convert childLL hs323110 hx323110 hy323110 using 1 <;> norm_num
              exact Batch0294.cell2352.sound htau (by
                simp only [Batch0294.cell2352, Batch0294.tau2352, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3231100 (by positivity) using 1 <;> norm_num)
            · have hs3231102 : InSquare (57/320) (99/320) (1/320) tau := by
                convert childUL hs323110 hx323110 hy323110 using 1 <;> norm_num
              exact Batch0294.cell2354.sound htau (by
                simp only [Batch0294.cell2354, Batch0294.tau2354, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3231102 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (49/160 : ℝ) with hy323110 | hy323110
            · have hs3231101 : InSquare (59/320) (97/320) (1/320) tau := by
                convert childLR hs323110 hx323110 hy323110 using 1 <;> norm_num
              exact Batch0294.cell2353.sound htau (by
                simp only [Batch0294.cell2353, Batch0294.tau2353, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3231101 (by positivity) using 1 <;> norm_num)
            · have hs3231103 : InSquare (59/320) (99/320) (1/320) tau := by
                convert childUR hs323110 hx323110 hy323110 using 1 <;> norm_num
              exact Batch0294.cell2355.sound htau (by
                simp only [Batch0294.cell2355, Batch0294.tau2355, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3231103 (by positivity) using 1 <;> norm_num)
        · have hs323112 : InSquare (29/160) (51/160) (1/160) tau := by
            convert childUL hs32311 hx32311 hy32311 using 1 <;> norm_num
          rcases le_total tau.re (29/160 : ℝ) with hx323112 | hx323112
          · rcases le_total tau.im (51/160 : ℝ) with hy323112 | hy323112
            · have hs3231120 : InSquare (57/320) (101/320) (1/320) tau := by
                convert childLL hs323112 hx323112 hy323112 using 1 <;> norm_num
              exact Batch0295.cell2360.sound htau (by
                simp only [Batch0295.cell2360, Batch0295.tau2360, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3231120 (by positivity) using 1 <;> norm_num)
            · have hs3231122 : InSquare (57/320) (103/320) (1/320) tau := by
                convert childUL hs323112 hx323112 hy323112 using 1 <;> norm_num
              exact Batch0295.cell2362.sound htau (by
                simp only [Batch0295.cell2362, Batch0295.tau2362, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3231122 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (51/160 : ℝ) with hy323112 | hy323112
            · have hs3231121 : InSquare (59/320) (101/320) (1/320) tau := by
                convert childLR hs323112 hx323112 hy323112 using 1 <;> norm_num
              exact Batch0295.cell2361.sound htau (by
                simp only [Batch0295.cell2361, Batch0295.tau2361, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3231121 (by positivity) using 1 <;> norm_num)
            · have hs3231123 : InSquare (59/320) (103/320) (1/320) tau := by
                convert childUR hs323112 hx323112 hy323112 using 1 <;> norm_num
              exact Batch0295.cell2363.sound htau (by
                simp only [Batch0295.cell2363, Batch0295.tau2363, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3231123 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (5/16 : ℝ) with hy32311 | hy32311
        · have hs323111 : InSquare (31/160) (49/160) (1/160) tau := by
            convert childLR hs32311 hx32311 hy32311 using 1 <;> norm_num
          rcases le_total tau.re (31/160 : ℝ) with hx323111 | hx323111
          · rcases le_total tau.im (49/160 : ℝ) with hy323111 | hy323111
            · have hs3231110 : InSquare (61/320) (97/320) (1/320) tau := by
                convert childLL hs323111 hx323111 hy323111 using 1 <;> norm_num
              exact Batch0294.cell2356.sound htau (by
                simp only [Batch0294.cell2356, Batch0294.tau2356, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3231110 (by positivity) using 1 <;> norm_num)
            · have hs3231112 : InSquare (61/320) (99/320) (1/320) tau := by
                convert childUL hs323111 hx323111 hy323111 using 1 <;> norm_num
              exact Batch0294.cell2358.sound htau (by
                simp only [Batch0294.cell2358, Batch0294.tau2358, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3231112 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (49/160 : ℝ) with hy323111 | hy323111
            · have hs3231111 : InSquare (63/320) (97/320) (1/320) tau := by
                convert childLR hs323111 hx323111 hy323111 using 1 <;> norm_num
              exact Batch0294.cell2357.sound htau (by
                simp only [Batch0294.cell2357, Batch0294.tau2357, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3231111 (by positivity) using 1 <;> norm_num)
            · have hs3231113 : InSquare (63/320) (99/320) (1/320) tau := by
                convert childUR hs323111 hx323111 hy323111 using 1 <;> norm_num
              exact Batch0294.cell2359.sound htau (by
                simp only [Batch0294.cell2359, Batch0294.tau2359, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3231113 (by positivity) using 1 <;> norm_num)
        · have hs323113 : InSquare (31/160) (51/160) (1/160) tau := by
            convert childUR hs32311 hx32311 hy32311 using 1 <;> norm_num
          rcases le_total tau.re (31/160 : ℝ) with hx323113 | hx323113
          · rcases le_total tau.im (51/160 : ℝ) with hy323113 | hy323113
            · have hs3231130 : InSquare (61/320) (101/320) (1/320) tau := by
                convert childLL hs323113 hx323113 hy323113 using 1 <;> norm_num
              exact Batch0295.cell2364.sound htau (by
                simp only [Batch0295.cell2364, Batch0295.tau2364, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3231130 (by positivity) using 1 <;> norm_num)
            · have hs3231132 : InSquare (61/320) (103/320) (1/320) tau := by
                convert childUL hs323113 hx323113 hy323113 using 1 <;> norm_num
              exact Batch0295.cell2366.sound htau (by
                simp only [Batch0295.cell2366, Batch0295.tau2366, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3231132 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (51/160 : ℝ) with hy323113 | hy323113
            · have hs3231131 : InSquare (63/320) (101/320) (1/320) tau := by
                convert childLR hs323113 hx323113 hy323113 using 1 <;> norm_num
              exact Batch0295.cell2365.sound htau (by
                simp only [Batch0295.cell2365, Batch0295.tau2365, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3231131 (by positivity) using 1 <;> norm_num)
            · have hs3231133 : InSquare (63/320) (103/320) (1/320) tau := by
                convert childUR hs323113 hx323113 hy323113 using 1 <;> norm_num
              exact Batch0295.cell2367.sound htau (by
                simp only [Batch0295.cell2367, Batch0295.tau2367, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3231133 (by positivity) using 1 <;> norm_num)
    · have hs32313 : InSquare (3/16) (27/80) (1/80) tau := by
        convert childUR hs hx3231 hy3231 using 1 <;> norm_num
      rcases le_total tau.re (3/16 : ℝ) with hx32313 | hx32313
      · rcases le_total tau.im (27/80 : ℝ) with hy32313 | hy32313
        · have hs323130 : InSquare (29/160) (53/160) (1/160) tau := by
            convert childLL hs32313 hx32313 hy32313 using 1 <;> norm_num
          rcases le_total tau.re (29/160 : ℝ) with hx323130 | hx323130
          · rcases le_total tau.im (53/160 : ℝ) with hy323130 | hy323130
            · have hs3231300 : InSquare (57/320) (21/64) (1/320) tau := by
                convert childLL hs323130 hx323130 hy323130 using 1 <;> norm_num
              exact Batch0298.cell2384.sound htau (by
                simp only [Batch0298.cell2384, Batch0298.tau2384, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3231300 (by positivity) using 1 <;> norm_num)
            · have hs3231302 : InSquare (57/320) (107/320) (1/320) tau := by
                convert childUL hs323130 hx323130 hy323130 using 1 <;> norm_num
              exact Batch0298.cell2386.sound htau (by
                simp only [Batch0298.cell2386, Batch0298.tau2386, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3231302 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (53/160 : ℝ) with hy323130 | hy323130
            · have hs3231301 : InSquare (59/320) (21/64) (1/320) tau := by
                convert childLR hs323130 hx323130 hy323130 using 1 <;> norm_num
              exact Batch0298.cell2385.sound htau (by
                simp only [Batch0298.cell2385, Batch0298.tau2385, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3231301 (by positivity) using 1 <;> norm_num)
            · have hs3231303 : InSquare (59/320) (107/320) (1/320) tau := by
                convert childUR hs323130 hx323130 hy323130 using 1 <;> norm_num
              exact Batch0298.cell2387.sound htau (by
                simp only [Batch0298.cell2387, Batch0298.tau2387, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3231303 (by positivity) using 1 <;> norm_num)
        · have hs323132 : InSquare (29/160) (11/32) (1/160) tau := by
            convert childUL hs32313 hx32313 hy32313 using 1 <;> norm_num
          rcases le_total tau.re (29/160 : ℝ) with hx323132 | hx323132
          · rcases le_total tau.im (11/32 : ℝ) with hy323132 | hy323132
            · have hs3231320 : InSquare (57/320) (109/320) (1/320) tau := by
                convert childLL hs323132 hx323132 hy323132 using 1 <;> norm_num
              exact Batch0299.cell2392.sound htau (by
                simp only [Batch0299.cell2392, Batch0299.tau2392, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3231320 (by positivity) using 1 <;> norm_num)
            · have hs3231322 : InSquare (57/320) (111/320) (1/320) tau := by
                convert childUL hs323132 hx323132 hy323132 using 1 <;> norm_num
              exact Batch0299.cell2394.sound htau (by
                simp only [Batch0299.cell2394, Batch0299.tau2394, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3231322 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (11/32 : ℝ) with hy323132 | hy323132
            · have hs3231321 : InSquare (59/320) (109/320) (1/320) tau := by
                convert childLR hs323132 hx323132 hy323132 using 1 <;> norm_num
              exact Batch0299.cell2393.sound htau (by
                simp only [Batch0299.cell2393, Batch0299.tau2393, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3231321 (by positivity) using 1 <;> norm_num)
            · have hs3231323 : InSquare (59/320) (111/320) (1/320) tau := by
                convert childUR hs323132 hx323132 hy323132 using 1 <;> norm_num
              exact Batch0299.cell2395.sound htau (by
                simp only [Batch0299.cell2395, Batch0299.tau2395, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3231323 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (27/80 : ℝ) with hy32313 | hy32313
        · have hs323131 : InSquare (31/160) (53/160) (1/160) tau := by
            convert childLR hs32313 hx32313 hy32313 using 1 <;> norm_num
          rcases le_total tau.re (31/160 : ℝ) with hx323131 | hx323131
          · rcases le_total tau.im (53/160 : ℝ) with hy323131 | hy323131
            · have hs3231310 : InSquare (61/320) (21/64) (1/320) tau := by
                convert childLL hs323131 hx323131 hy323131 using 1 <;> norm_num
              exact Batch0298.cell2388.sound htau (by
                simp only [Batch0298.cell2388, Batch0298.tau2388, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3231310 (by positivity) using 1 <;> norm_num)
            · have hs3231312 : InSquare (61/320) (107/320) (1/320) tau := by
                convert childUL hs323131 hx323131 hy323131 using 1 <;> norm_num
              exact Batch0298.cell2390.sound htau (by
                simp only [Batch0298.cell2390, Batch0298.tau2390, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3231312 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (53/160 : ℝ) with hy323131 | hy323131
            · have hs3231311 : InSquare (63/320) (21/64) (1/320) tau := by
                convert childLR hs323131 hx323131 hy323131 using 1 <;> norm_num
              exact Batch0298.cell2389.sound htau (by
                simp only [Batch0298.cell2389, Batch0298.tau2389, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3231311 (by positivity) using 1 <;> norm_num)
            · have hs3231313 : InSquare (63/320) (107/320) (1/320) tau := by
                convert childUR hs323131 hx323131 hy323131 using 1 <;> norm_num
              exact Batch0298.cell2391.sound htau (by
                simp only [Batch0298.cell2391, Batch0298.tau2391, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3231313 (by positivity) using 1 <;> norm_num)
        · have hs323133 : InSquare (31/160) (11/32) (1/160) tau := by
            convert childUR hs32313 hx32313 hy32313 using 1 <;> norm_num
          rcases le_total tau.re (31/160 : ℝ) with hx323133 | hx323133
          · rcases le_total tau.im (11/32 : ℝ) with hy323133 | hy323133
            · have hs3231330 : InSquare (61/320) (109/320) (1/320) tau := by
                convert childLL hs323133 hx323133 hy323133 using 1 <;> norm_num
              exact Batch0299.cell2396.sound htau (by
                simp only [Batch0299.cell2396, Batch0299.tau2396, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3231330 (by positivity) using 1 <;> norm_num)
            · have hs3231332 : InSquare (61/320) (111/320) (1/320) tau := by
                convert childUL hs323133 hx323133 hy323133 using 1 <;> norm_num
              rcases le_total tau.re (61/320 : ℝ) with hx3231332 | hx3231332
              · rcases le_total tau.im (111/320 : ℝ) with hy3231332 | hy3231332
                · have hs32313320 : InSquare (121/640) (221/640) (1/640) tau := by
                    convert childLL hs3231332 hx3231332 hy3231332 using 1 <;> norm_num
                  exact Batch0460.cell3687.sound htau (by
                    simp only [Batch0460.cell3687, Batch0460.tau3687, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32313320 (by positivity) using 1 <;> norm_num)
                · have hs32313322 : InSquare (121/640) (223/640) (1/640) tau := by
                    convert childUL hs3231332 hx3231332 hy3231332 using 1 <;> norm_num
                  exact Batch0461.cell3689.sound htau (by
                    simp only [Batch0461.cell3689, Batch0461.tau3689, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32313322 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (111/320 : ℝ) with hy3231332 | hy3231332
                · have hs32313321 : InSquare (123/640) (221/640) (1/640) tau := by
                    convert childLR hs3231332 hx3231332 hy3231332 using 1 <;> norm_num
                  exact Batch0461.cell3688.sound htau (by
                    simp only [Batch0461.cell3688, Batch0461.tau3688, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32313321 (by positivity) using 1 <;> norm_num)
                · have hs32313323 : InSquare (123/640) (223/640) (1/640) tau := by
                    convert childUR hs3231332 hx3231332 hy3231332 using 1 <;> norm_num
                  exact Batch0461.cell3690.sound htau (by
                    simp only [Batch0461.cell3690, Batch0461.tau3690, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32313323 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (11/32 : ℝ) with hy323133 | hy323133
            · have hs3231331 : InSquare (63/320) (109/320) (1/320) tau := by
                convert childLR hs323133 hx323133 hy323133 using 1 <;> norm_num
              exact Batch0299.cell2397.sound htau (by
                simp only [Batch0299.cell2397, Batch0299.tau2397, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3231331 (by positivity) using 1 <;> norm_num)
            · have hs3231333 : InSquare (63/320) (111/320) (1/320) tau := by
                convert childUR hs323133 hx323133 hy323133 using 1 <;> norm_num
              rcases le_total tau.re (63/320 : ℝ) with hx3231333 | hx3231333
              · rcases le_total tau.im (111/320 : ℝ) with hy3231333 | hy3231333
                · have hs32313330 : InSquare (25/128) (221/640) (1/640) tau := by
                    convert childLL hs3231333 hx3231333 hy3231333 using 1 <;> norm_num
                  exact Batch0461.cell3691.sound htau (by
                    simp only [Batch0461.cell3691, Batch0461.tau3691, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32313330 (by positivity) using 1 <;> norm_num)
                · have hs32313332 : InSquare (25/128) (223/640) (1/640) tau := by
                    convert childUL hs3231333 hx3231333 hy3231333 using 1 <;> norm_num
                  exact Batch0461.cell3693.sound htau (by
                    simp only [Batch0461.cell3693, Batch0461.tau3693, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32313332 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (111/320 : ℝ) with hy3231333 | hy3231333
                · have hs32313331 : InSquare (127/640) (221/640) (1/640) tau := by
                    convert childLR hs3231333 hx3231333 hy3231333 using 1 <;> norm_num
                  exact Batch0461.cell3692.sound htau (by
                    simp only [Batch0461.cell3692, Batch0461.tau3692, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32313331 (by positivity) using 1 <;> norm_num)
                · have hs32313333 : InSquare (127/640) (223/640) (1/640) tau := by
                    convert childUR hs3231333 hx3231333 hy3231333 using 1 <;> norm_num
                  exact Batch0461.cell3694.sound htau (by
                    simp only [Batch0461.cell3694, Batch0461.tau3694, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32313333 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3231
