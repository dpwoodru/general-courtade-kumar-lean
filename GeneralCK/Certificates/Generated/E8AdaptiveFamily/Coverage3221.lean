import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0140
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0141
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0142
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0278
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0279

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3221

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (3/40) (13/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (3/40 : ℝ) with hx3221 | hx3221
  · rcases le_total tau.im (13/40 : ℝ) with hy3221 | hy3221
    · have hs32210 : InSquare (1/16) (5/16) (1/80) tau := by
        convert childLL hs hx3221 hy3221 using 1 <;> norm_num
      rcases le_total tau.re (1/16 : ℝ) with hx32210 | hx32210
      · rcases le_total tau.im (5/16 : ℝ) with hy32210 | hy32210
        · have hs322100 : InSquare (9/160) (49/160) (1/160) tau := by
            convert childLL hs32210 hx32210 hy32210 using 1 <;> norm_num
          exact Batch0140.cell1127.sound htau (by
            simp only [Batch0140.cell1127, Batch0140.tau1127, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs322100 (by positivity) using 1 <;> norm_num)
        · have hs322102 : InSquare (9/160) (51/160) (1/160) tau := by
            convert childUL hs32210 hx32210 hy32210 using 1 <;> norm_num
          exact Batch0141.cell1129.sound htau (by
            simp only [Batch0141.cell1129, Batch0141.tau1129, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs322102 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (5/16 : ℝ) with hy32210 | hy32210
        · have hs322101 : InSquare (11/160) (49/160) (1/160) tau := by
            convert childLR hs32210 hx32210 hy32210 using 1 <;> norm_num
          exact Batch0141.cell1128.sound htau (by
            simp only [Batch0141.cell1128, Batch0141.tau1128, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs322101 (by positivity) using 1 <;> norm_num)
        · have hs322103 : InSquare (11/160) (51/160) (1/160) tau := by
            convert childUR hs32210 hx32210 hy32210 using 1 <;> norm_num
          exact Batch0141.cell1130.sound htau (by
            simp only [Batch0141.cell1130, Batch0141.tau1130, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs322103 (by positivity) using 1 <;> norm_num)
    · have hs32212 : InSquare (1/16) (27/80) (1/80) tau := by
        convert childUL hs hx3221 hy3221 using 1 <;> norm_num
      rcases le_total tau.re (1/16 : ℝ) with hx32212 | hx32212
      · rcases le_total tau.im (27/80 : ℝ) with hy32212 | hy32212
        · have hs322120 : InSquare (9/160) (53/160) (1/160) tau := by
            convert childLL hs32212 hx32212 hy32212 using 1 <;> norm_num
          exact Batch0141.cell1135.sound htau (by
            simp only [Batch0141.cell1135, Batch0141.tau1135, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs322120 (by positivity) using 1 <;> norm_num)
        · have hs322122 : InSquare (9/160) (11/32) (1/160) tau := by
            convert childUL hs32212 hx32212 hy32212 using 1 <;> norm_num
          exact Batch0142.cell1137.sound htau (by
            simp only [Batch0142.cell1137, Batch0142.tau1137, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs322122 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (27/80 : ℝ) with hy32212 | hy32212
        · have hs322121 : InSquare (11/160) (53/160) (1/160) tau := by
            convert childLR hs32212 hx32212 hy32212 using 1 <;> norm_num
          exact Batch0142.cell1136.sound htau (by
            simp only [Batch0142.cell1136, Batch0142.tau1136, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs322121 (by positivity) using 1 <;> norm_num)
        · have hs322123 : InSquare (11/160) (11/32) (1/160) tau := by
            convert childUR hs32212 hx32212 hy32212 using 1 <;> norm_num
          rcases le_total tau.re (11/160 : ℝ) with hx322123 | hx322123
          · rcases le_total tau.im (11/32 : ℝ) with hy322123 | hy322123
            · have hs3221230 : InSquare (21/320) (109/320) (1/320) tau := by
                convert childLL hs322123 hx322123 hy322123 using 1 <;> norm_num
              exact Batch0278.cell2224.sound htau (by
                simp only [Batch0278.cell2224, Batch0278.tau2224, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3221230 (by positivity) using 1 <;> norm_num)
            · have hs3221232 : InSquare (21/320) (111/320) (1/320) tau := by
                convert childUL hs322123 hx322123 hy322123 using 1 <;> norm_num
              exact Batch0278.cell2226.sound htau (by
                simp only [Batch0278.cell2226, Batch0278.tau2226, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3221232 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (11/32 : ℝ) with hy322123 | hy322123
            · have hs3221231 : InSquare (23/320) (109/320) (1/320) tau := by
                convert childLR hs322123 hx322123 hy322123 using 1 <;> norm_num
              exact Batch0278.cell2225.sound htau (by
                simp only [Batch0278.cell2225, Batch0278.tau2225, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3221231 (by positivity) using 1 <;> norm_num)
            · have hs3221233 : InSquare (23/320) (111/320) (1/320) tau := by
                convert childUR hs322123 hx322123 hy322123 using 1 <;> norm_num
              exact Batch0278.cell2227.sound htau (by
                simp only [Batch0278.cell2227, Batch0278.tau2227, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3221233 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (13/40 : ℝ) with hy3221 | hy3221
    · have hs32211 : InSquare (7/80) (5/16) (1/80) tau := by
        convert childLR hs hx3221 hy3221 using 1 <;> norm_num
      rcases le_total tau.re (7/80 : ℝ) with hx32211 | hx32211
      · rcases le_total tau.im (5/16 : ℝ) with hy32211 | hy32211
        · have hs322110 : InSquare (13/160) (49/160) (1/160) tau := by
            convert childLL hs32211 hx32211 hy32211 using 1 <;> norm_num
          exact Batch0141.cell1131.sound htau (by
            simp only [Batch0141.cell1131, Batch0141.tau1131, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs322110 (by positivity) using 1 <;> norm_num)
        · have hs322112 : InSquare (13/160) (51/160) (1/160) tau := by
            convert childUL hs32211 hx32211 hy32211 using 1 <;> norm_num
          exact Batch0141.cell1133.sound htau (by
            simp only [Batch0141.cell1133, Batch0141.tau1133, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs322112 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (5/16 : ℝ) with hy32211 | hy32211
        · have hs322111 : InSquare (3/32) (49/160) (1/160) tau := by
            convert childLR hs32211 hx32211 hy32211 using 1 <;> norm_num
          exact Batch0141.cell1132.sound htau (by
            simp only [Batch0141.cell1132, Batch0141.tau1132, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs322111 (by positivity) using 1 <;> norm_num)
        · have hs322113 : InSquare (3/32) (51/160) (1/160) tau := by
            convert childUR hs32211 hx32211 hy32211 using 1 <;> norm_num
          exact Batch0141.cell1134.sound htau (by
            simp only [Batch0141.cell1134, Batch0141.tau1134, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs322113 (by positivity) using 1 <;> norm_num)
    · have hs32213 : InSquare (7/80) (27/80) (1/80) tau := by
        convert childUR hs hx3221 hy3221 using 1 <;> norm_num
      rcases le_total tau.re (7/80 : ℝ) with hx32213 | hx32213
      · rcases le_total tau.im (27/80 : ℝ) with hy32213 | hy32213
        · have hs322130 : InSquare (13/160) (53/160) (1/160) tau := by
            convert childLL hs32213 hx32213 hy32213 using 1 <;> norm_num
          exact Batch0142.cell1138.sound htau (by
            simp only [Batch0142.cell1138, Batch0142.tau1138, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs322130 (by positivity) using 1 <;> norm_num)
        · have hs322132 : InSquare (13/160) (11/32) (1/160) tau := by
            convert childUL hs32213 hx32213 hy32213 using 1 <;> norm_num
          rcases le_total tau.re (13/160 : ℝ) with hx322132 | hx322132
          · rcases le_total tau.im (11/32 : ℝ) with hy322132 | hy322132
            · have hs3221320 : InSquare (5/64) (109/320) (1/320) tau := by
                convert childLL hs322132 hx322132 hy322132 using 1 <;> norm_num
              exact Batch0278.cell2228.sound htau (by
                simp only [Batch0278.cell2228, Batch0278.tau2228, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3221320 (by positivity) using 1 <;> norm_num)
            · have hs3221322 : InSquare (5/64) (111/320) (1/320) tau := by
                convert childUL hs322132 hx322132 hy322132 using 1 <;> norm_num
              exact Batch0278.cell2230.sound htau (by
                simp only [Batch0278.cell2230, Batch0278.tau2230, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3221322 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (11/32 : ℝ) with hy322132 | hy322132
            · have hs3221321 : InSquare (27/320) (109/320) (1/320) tau := by
                convert childLR hs322132 hx322132 hy322132 using 1 <;> norm_num
              exact Batch0278.cell2229.sound htau (by
                simp only [Batch0278.cell2229, Batch0278.tau2229, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3221321 (by positivity) using 1 <;> norm_num)
            · have hs3221323 : InSquare (27/320) (111/320) (1/320) tau := by
                convert childUR hs322132 hx322132 hy322132 using 1 <;> norm_num
              exact Batch0278.cell2231.sound htau (by
                simp only [Batch0278.cell2231, Batch0278.tau2231, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3221323 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (27/80 : ℝ) with hy32213 | hy32213
        · have hs322131 : InSquare (3/32) (53/160) (1/160) tau := by
            convert childLR hs32213 hx32213 hy32213 using 1 <;> norm_num
          exact Batch0142.cell1139.sound htau (by
            simp only [Batch0142.cell1139, Batch0142.tau1139, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs322131 (by positivity) using 1 <;> norm_num)
        · have hs322133 : InSquare (3/32) (11/32) (1/160) tau := by
            convert childUR hs32213 hx32213 hy32213 using 1 <;> norm_num
          rcases le_total tau.re (3/32 : ℝ) with hx322133 | hx322133
          · rcases le_total tau.im (11/32 : ℝ) with hy322133 | hy322133
            · have hs3221330 : InSquare (29/320) (109/320) (1/320) tau := by
                convert childLL hs322133 hx322133 hy322133 using 1 <;> norm_num
              exact Batch0279.cell2232.sound htau (by
                simp only [Batch0279.cell2232, Batch0279.tau2232, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3221330 (by positivity) using 1 <;> norm_num)
            · have hs3221332 : InSquare (29/320) (111/320) (1/320) tau := by
                convert childUL hs322133 hx322133 hy322133 using 1 <;> norm_num
              exact Batch0279.cell2234.sound htau (by
                simp only [Batch0279.cell2234, Batch0279.tau2234, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3221332 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (11/32 : ℝ) with hy322133 | hy322133
            · have hs3221331 : InSquare (31/320) (109/320) (1/320) tau := by
                convert childLR hs322133 hx322133 hy322133 using 1 <;> norm_num
              exact Batch0279.cell2233.sound htau (by
                simp only [Batch0279.cell2233, Batch0279.tau2233, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3221331 (by positivity) using 1 <;> norm_num)
            · have hs3221333 : InSquare (31/320) (111/320) (1/320) tau := by
                convert childUR hs322133 hx322133 hy322133 using 1 <;> norm_num
              exact Batch0279.cell2235.sound htau (by
                simp only [Batch0279.cell2235, Batch0279.tau2235, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3221333 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3221
