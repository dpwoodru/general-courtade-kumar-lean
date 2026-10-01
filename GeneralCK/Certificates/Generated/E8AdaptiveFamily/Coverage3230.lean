import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0142
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0143
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0289
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0290
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0291
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0292

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3230

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (1/8) (13/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (1/8 : ℝ) with hx3230 | hx3230
  · rcases le_total tau.im (13/40 : ℝ) with hy3230 | hy3230
    · have hs32300 : InSquare (9/80) (5/16) (1/80) tau := by
        convert childLL hs hx3230 hy3230 using 1 <;> norm_num
      rcases le_total tau.re (9/80 : ℝ) with hx32300 | hx32300
      · rcases le_total tau.im (5/16 : ℝ) with hy32300 | hy32300
        · have hs323000 : InSquare (17/160) (49/160) (1/160) tau := by
            convert childLL hs32300 hx32300 hy32300 using 1 <;> norm_num
          exact Batch0142.cell1141.sound htau (by
            simp only [Batch0142.cell1141, Batch0142.tau1141, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs323000 (by positivity) using 1 <;> norm_num)
        · have hs323002 : InSquare (17/160) (51/160) (1/160) tau := by
            convert childUL hs32300 hx32300 hy32300 using 1 <;> norm_num
          exact Batch0142.cell1143.sound htau (by
            simp only [Batch0142.cell1143, Batch0142.tau1143, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs323002 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (5/16 : ℝ) with hy32300 | hy32300
        · have hs323001 : InSquare (19/160) (49/160) (1/160) tau := by
            convert childLR hs32300 hx32300 hy32300 using 1 <;> norm_num
          exact Batch0142.cell1142.sound htau (by
            simp only [Batch0142.cell1142, Batch0142.tau1142, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs323001 (by positivity) using 1 <;> norm_num)
        · have hs323003 : InSquare (19/160) (51/160) (1/160) tau := by
            convert childUR hs32300 hx32300 hy32300 using 1 <;> norm_num
          exact Batch0143.cell1144.sound htau (by
            simp only [Batch0143.cell1144, Batch0143.tau1144, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs323003 (by positivity) using 1 <;> norm_num)
    · have hs32302 : InSquare (9/80) (27/80) (1/80) tau := by
        convert childUL hs hx3230 hy3230 using 1 <;> norm_num
      rcases le_total tau.re (9/80 : ℝ) with hx32302 | hx32302
      · rcases le_total tau.im (27/80 : ℝ) with hy32302 | hy32302
        · have hs323020 : InSquare (17/160) (53/160) (1/160) tau := by
            convert childLL hs32302 hx32302 hy32302 using 1 <;> norm_num
          exact Batch0143.cell1148.sound htau (by
            simp only [Batch0143.cell1148, Batch0143.tau1148, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs323020 (by positivity) using 1 <;> norm_num)
        · have hs323022 : InSquare (17/160) (11/32) (1/160) tau := by
            convert childUL hs32302 hx32302 hy32302 using 1 <;> norm_num
          rcases le_total tau.re (17/160 : ℝ) with hx323022 | hx323022
          · rcases le_total tau.im (11/32 : ℝ) with hy323022 | hy323022
            · have hs3230220 : InSquare (33/320) (109/320) (1/320) tau := by
                convert childLL hs323022 hx323022 hy323022 using 1 <;> norm_num
              exact Batch0290.cell2320.sound htau (by
                simp only [Batch0290.cell2320, Batch0290.tau2320, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3230220 (by positivity) using 1 <;> norm_num)
            · have hs3230222 : InSquare (33/320) (111/320) (1/320) tau := by
                convert childUL hs323022 hx323022 hy323022 using 1 <;> norm_num
              exact Batch0290.cell2322.sound htau (by
                simp only [Batch0290.cell2322, Batch0290.tau2322, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3230222 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (11/32 : ℝ) with hy323022 | hy323022
            · have hs3230221 : InSquare (7/64) (109/320) (1/320) tau := by
                convert childLR hs323022 hx323022 hy323022 using 1 <;> norm_num
              exact Batch0290.cell2321.sound htau (by
                simp only [Batch0290.cell2321, Batch0290.tau2321, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3230221 (by positivity) using 1 <;> norm_num)
            · have hs3230223 : InSquare (7/64) (111/320) (1/320) tau := by
                convert childUR hs323022 hx323022 hy323022 using 1 <;> norm_num
              exact Batch0290.cell2323.sound htau (by
                simp only [Batch0290.cell2323, Batch0290.tau2323, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3230223 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (27/80 : ℝ) with hy32302 | hy32302
        · have hs323021 : InSquare (19/160) (53/160) (1/160) tau := by
            convert childLR hs32302 hx32302 hy32302 using 1 <;> norm_num
          rcases le_total tau.re (19/160 : ℝ) with hx323021 | hx323021
          · rcases le_total tau.im (53/160 : ℝ) with hy323021 | hy323021
            · have hs3230210 : InSquare (37/320) (21/64) (1/320) tau := by
                convert childLL hs323021 hx323021 hy323021 using 1 <;> norm_num
              exact Batch0289.cell2316.sound htau (by
                simp only [Batch0289.cell2316, Batch0289.tau2316, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3230210 (by positivity) using 1 <;> norm_num)
            · have hs3230212 : InSquare (37/320) (107/320) (1/320) tau := by
                convert childUL hs323021 hx323021 hy323021 using 1 <;> norm_num
              exact Batch0289.cell2318.sound htau (by
                simp only [Batch0289.cell2318, Batch0289.tau2318, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3230212 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (53/160 : ℝ) with hy323021 | hy323021
            · have hs3230211 : InSquare (39/320) (21/64) (1/320) tau := by
                convert childLR hs323021 hx323021 hy323021 using 1 <;> norm_num
              exact Batch0289.cell2317.sound htau (by
                simp only [Batch0289.cell2317, Batch0289.tau2317, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3230211 (by positivity) using 1 <;> norm_num)
            · have hs3230213 : InSquare (39/320) (107/320) (1/320) tau := by
                convert childUR hs323021 hx323021 hy323021 using 1 <;> norm_num
              exact Batch0289.cell2319.sound htau (by
                simp only [Batch0289.cell2319, Batch0289.tau2319, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3230213 (by positivity) using 1 <;> norm_num)
        · have hs323023 : InSquare (19/160) (11/32) (1/160) tau := by
            convert childUR hs32302 hx32302 hy32302 using 1 <;> norm_num
          rcases le_total tau.re (19/160 : ℝ) with hx323023 | hx323023
          · rcases le_total tau.im (11/32 : ℝ) with hy323023 | hy323023
            · have hs3230230 : InSquare (37/320) (109/320) (1/320) tau := by
                convert childLL hs323023 hx323023 hy323023 using 1 <;> norm_num
              exact Batch0290.cell2324.sound htau (by
                simp only [Batch0290.cell2324, Batch0290.tau2324, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3230230 (by positivity) using 1 <;> norm_num)
            · have hs3230232 : InSquare (37/320) (111/320) (1/320) tau := by
                convert childUL hs323023 hx323023 hy323023 using 1 <;> norm_num
              exact Batch0290.cell2326.sound htau (by
                simp only [Batch0290.cell2326, Batch0290.tau2326, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3230232 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (11/32 : ℝ) with hy323023 | hy323023
            · have hs3230231 : InSquare (39/320) (109/320) (1/320) tau := by
                convert childLR hs323023 hx323023 hy323023 using 1 <;> norm_num
              exact Batch0290.cell2325.sound htau (by
                simp only [Batch0290.cell2325, Batch0290.tau2325, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3230231 (by positivity) using 1 <;> norm_num)
            · have hs3230233 : InSquare (39/320) (111/320) (1/320) tau := by
                convert childUR hs323023 hx323023 hy323023 using 1 <;> norm_num
              exact Batch0290.cell2327.sound htau (by
                simp only [Batch0290.cell2327, Batch0290.tau2327, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3230233 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (13/40 : ℝ) with hy3230 | hy3230
    · have hs32301 : InSquare (11/80) (5/16) (1/80) tau := by
        convert childLR hs hx3230 hy3230 using 1 <;> norm_num
      rcases le_total tau.re (11/80 : ℝ) with hx32301 | hx32301
      · rcases le_total tau.im (5/16 : ℝ) with hy32301 | hy32301
        · have hs323010 : InSquare (21/160) (49/160) (1/160) tau := by
            convert childLL hs32301 hx32301 hy32301 using 1 <;> norm_num
          exact Batch0143.cell1145.sound htau (by
            simp only [Batch0143.cell1145, Batch0143.tau1145, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs323010 (by positivity) using 1 <;> norm_num)
        · have hs323012 : InSquare (21/160) (51/160) (1/160) tau := by
            convert childUL hs32301 hx32301 hy32301 using 1 <;> norm_num
          exact Batch0143.cell1147.sound htau (by
            simp only [Batch0143.cell1147, Batch0143.tau1147, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs323012 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (5/16 : ℝ) with hy32301 | hy32301
        · have hs323011 : InSquare (23/160) (49/160) (1/160) tau := by
            convert childLR hs32301 hx32301 hy32301 using 1 <;> norm_num
          exact Batch0143.cell1146.sound htau (by
            simp only [Batch0143.cell1146, Batch0143.tau1146, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs323011 (by positivity) using 1 <;> norm_num)
        · have hs323013 : InSquare (23/160) (51/160) (1/160) tau := by
            convert childUR hs32301 hx32301 hy32301 using 1 <;> norm_num
          rcases le_total tau.re (23/160 : ℝ) with hx323013 | hx323013
          · rcases le_total tau.im (51/160 : ℝ) with hy323013 | hy323013
            · have hs3230130 : InSquare (9/64) (101/320) (1/320) tau := by
                convert childLL hs323013 hx323013 hy323013 using 1 <;> norm_num
              exact Batch0289.cell2312.sound htau (by
                simp only [Batch0289.cell2312, Batch0289.tau2312, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3230130 (by positivity) using 1 <;> norm_num)
            · have hs3230132 : InSquare (9/64) (103/320) (1/320) tau := by
                convert childUL hs323013 hx323013 hy323013 using 1 <;> norm_num
              exact Batch0289.cell2314.sound htau (by
                simp only [Batch0289.cell2314, Batch0289.tau2314, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3230132 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (51/160 : ℝ) with hy323013 | hy323013
            · have hs3230131 : InSquare (47/320) (101/320) (1/320) tau := by
                convert childLR hs323013 hx323013 hy323013 using 1 <;> norm_num
              exact Batch0289.cell2313.sound htau (by
                simp only [Batch0289.cell2313, Batch0289.tau2313, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3230131 (by positivity) using 1 <;> norm_num)
            · have hs3230133 : InSquare (47/320) (103/320) (1/320) tau := by
                convert childUR hs323013 hx323013 hy323013 using 1 <;> norm_num
              exact Batch0289.cell2315.sound htau (by
                simp only [Batch0289.cell2315, Batch0289.tau2315, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3230133 (by positivity) using 1 <;> norm_num)
    · have hs32303 : InSquare (11/80) (27/80) (1/80) tau := by
        convert childUR hs hx3230 hy3230 using 1 <;> norm_num
      rcases le_total tau.re (11/80 : ℝ) with hx32303 | hx32303
      · rcases le_total tau.im (27/80 : ℝ) with hy32303 | hy32303
        · have hs323030 : InSquare (21/160) (53/160) (1/160) tau := by
            convert childLL hs32303 hx32303 hy32303 using 1 <;> norm_num
          rcases le_total tau.re (21/160 : ℝ) with hx323030 | hx323030
          · rcases le_total tau.im (53/160 : ℝ) with hy323030 | hy323030
            · have hs3230300 : InSquare (41/320) (21/64) (1/320) tau := by
                convert childLL hs323030 hx323030 hy323030 using 1 <;> norm_num
              exact Batch0291.cell2328.sound htau (by
                simp only [Batch0291.cell2328, Batch0291.tau2328, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3230300 (by positivity) using 1 <;> norm_num)
            · have hs3230302 : InSquare (41/320) (107/320) (1/320) tau := by
                convert childUL hs323030 hx323030 hy323030 using 1 <;> norm_num
              exact Batch0291.cell2330.sound htau (by
                simp only [Batch0291.cell2330, Batch0291.tau2330, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3230302 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (53/160 : ℝ) with hy323030 | hy323030
            · have hs3230301 : InSquare (43/320) (21/64) (1/320) tau := by
                convert childLR hs323030 hx323030 hy323030 using 1 <;> norm_num
              exact Batch0291.cell2329.sound htau (by
                simp only [Batch0291.cell2329, Batch0291.tau2329, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3230301 (by positivity) using 1 <;> norm_num)
            · have hs3230303 : InSquare (43/320) (107/320) (1/320) tau := by
                convert childUR hs323030 hx323030 hy323030 using 1 <;> norm_num
              exact Batch0291.cell2331.sound htau (by
                simp only [Batch0291.cell2331, Batch0291.tau2331, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3230303 (by positivity) using 1 <;> norm_num)
        · have hs323032 : InSquare (21/160) (11/32) (1/160) tau := by
            convert childUL hs32303 hx32303 hy32303 using 1 <;> norm_num
          rcases le_total tau.re (21/160 : ℝ) with hx323032 | hx323032
          · rcases le_total tau.im (11/32 : ℝ) with hy323032 | hy323032
            · have hs3230320 : InSquare (41/320) (109/320) (1/320) tau := by
                convert childLL hs323032 hx323032 hy323032 using 1 <;> norm_num
              exact Batch0292.cell2336.sound htau (by
                simp only [Batch0292.cell2336, Batch0292.tau2336, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3230320 (by positivity) using 1 <;> norm_num)
            · have hs3230322 : InSquare (41/320) (111/320) (1/320) tau := by
                convert childUL hs323032 hx323032 hy323032 using 1 <;> norm_num
              exact Batch0292.cell2338.sound htau (by
                simp only [Batch0292.cell2338, Batch0292.tau2338, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3230322 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (11/32 : ℝ) with hy323032 | hy323032
            · have hs3230321 : InSquare (43/320) (109/320) (1/320) tau := by
                convert childLR hs323032 hx323032 hy323032 using 1 <;> norm_num
              exact Batch0292.cell2337.sound htau (by
                simp only [Batch0292.cell2337, Batch0292.tau2337, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3230321 (by positivity) using 1 <;> norm_num)
            · have hs3230323 : InSquare (43/320) (111/320) (1/320) tau := by
                convert childUR hs323032 hx323032 hy323032 using 1 <;> norm_num
              exact Batch0292.cell2339.sound htau (by
                simp only [Batch0292.cell2339, Batch0292.tau2339, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3230323 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (27/80 : ℝ) with hy32303 | hy32303
        · have hs323031 : InSquare (23/160) (53/160) (1/160) tau := by
            convert childLR hs32303 hx32303 hy32303 using 1 <;> norm_num
          rcases le_total tau.re (23/160 : ℝ) with hx323031 | hx323031
          · rcases le_total tau.im (53/160 : ℝ) with hy323031 | hy323031
            · have hs3230310 : InSquare (9/64) (21/64) (1/320) tau := by
                convert childLL hs323031 hx323031 hy323031 using 1 <;> norm_num
              exact Batch0291.cell2332.sound htau (by
                simp only [Batch0291.cell2332, Batch0291.tau2332, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3230310 (by positivity) using 1 <;> norm_num)
            · have hs3230312 : InSquare (9/64) (107/320) (1/320) tau := by
                convert childUL hs323031 hx323031 hy323031 using 1 <;> norm_num
              exact Batch0291.cell2334.sound htau (by
                simp only [Batch0291.cell2334, Batch0291.tau2334, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3230312 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (53/160 : ℝ) with hy323031 | hy323031
            · have hs3230311 : InSquare (47/320) (21/64) (1/320) tau := by
                convert childLR hs323031 hx323031 hy323031 using 1 <;> norm_num
              exact Batch0291.cell2333.sound htau (by
                simp only [Batch0291.cell2333, Batch0291.tau2333, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3230311 (by positivity) using 1 <;> norm_num)
            · have hs3230313 : InSquare (47/320) (107/320) (1/320) tau := by
                convert childUR hs323031 hx323031 hy323031 using 1 <;> norm_num
              exact Batch0291.cell2335.sound htau (by
                simp only [Batch0291.cell2335, Batch0291.tau2335, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3230313 (by positivity) using 1 <;> norm_num)
        · have hs323033 : InSquare (23/160) (11/32) (1/160) tau := by
            convert childUR hs32303 hx32303 hy32303 using 1 <;> norm_num
          rcases le_total tau.re (23/160 : ℝ) with hx323033 | hx323033
          · rcases le_total tau.im (11/32 : ℝ) with hy323033 | hy323033
            · have hs3230330 : InSquare (9/64) (109/320) (1/320) tau := by
                convert childLL hs323033 hx323033 hy323033 using 1 <;> norm_num
              exact Batch0292.cell2340.sound htau (by
                simp only [Batch0292.cell2340, Batch0292.tau2340, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3230330 (by positivity) using 1 <;> norm_num)
            · have hs3230332 : InSquare (9/64) (111/320) (1/320) tau := by
                convert childUL hs323033 hx323033 hy323033 using 1 <;> norm_num
              exact Batch0292.cell2342.sound htau (by
                simp only [Batch0292.cell2342, Batch0292.tau2342, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3230332 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (11/32 : ℝ) with hy323033 | hy323033
            · have hs3230331 : InSquare (47/320) (109/320) (1/320) tau := by
                convert childLR hs323033 hx323033 hy323033 using 1 <;> norm_num
              exact Batch0292.cell2341.sound htau (by
                simp only [Batch0292.cell2341, Batch0292.tau2341, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3230331 (by positivity) using 1 <;> norm_num)
            · have hs3230333 : InSquare (47/320) (111/320) (1/320) tau := by
                convert childUR hs323033 hx323033 hy323033 using 1 <;> norm_num
              exact Batch0292.cell2343.sound htau (by
                simp only [Batch0292.cell2343, Batch0292.tau2343, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3230333 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3230
