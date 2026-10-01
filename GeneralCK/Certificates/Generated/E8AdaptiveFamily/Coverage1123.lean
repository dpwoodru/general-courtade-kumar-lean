import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0084
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0085
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0086
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0231

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1123

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (11/40) (-9/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (11/40 : ℝ) with hx1123 | hx1123
  · rcases le_total tau.im (-9/40 : ℝ) with hy1123 | hy1123
    · have hs11230 : InSquare (21/80) (-19/80) (1/80) tau := by
        convert childLL hs hx1123 hy1123 using 1 <;> norm_num
      rcases le_total tau.re (21/80 : ℝ) with hx11230 | hx11230
      · rcases le_total tau.im (-19/80 : ℝ) with hy11230 | hy11230
        · have hs112300 : InSquare (41/160) (-39/160) (1/160) tau := by
            convert childLL hs11230 hx11230 hy11230 using 1 <;> norm_num
          exact Batch0084.cell0674.sound htau (by
            simp only [Batch0084.cell0674, Batch0084.tau0674, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs112300 (by positivity) using 1 <;> norm_num)
        · have hs112302 : InSquare (41/160) (-37/160) (1/160) tau := by
            convert childUL hs11230 hx11230 hy11230 using 1 <;> norm_num
          exact Batch0084.cell0676.sound htau (by
            simp only [Batch0084.cell0676, Batch0084.tau0676, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs112302 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-19/80 : ℝ) with hy11230 | hy11230
        · have hs112301 : InSquare (43/160) (-39/160) (1/160) tau := by
            convert childLR hs11230 hx11230 hy11230 using 1 <;> norm_num
          exact Batch0084.cell0675.sound htau (by
            simp only [Batch0084.cell0675, Batch0084.tau0675, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs112301 (by positivity) using 1 <;> norm_num)
        · have hs112303 : InSquare (43/160) (-37/160) (1/160) tau := by
            convert childUR hs11230 hx11230 hy11230 using 1 <;> norm_num
          exact Batch0084.cell0677.sound htau (by
            simp only [Batch0084.cell0677, Batch0084.tau0677, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs112303 (by positivity) using 1 <;> norm_num)
    · have hs11232 : InSquare (21/80) (-17/80) (1/80) tau := by
        convert childUL hs hx1123 hy1123 using 1 <;> norm_num
      rcases le_total tau.re (21/80 : ℝ) with hx11232 | hx11232
      · rcases le_total tau.im (-17/80 : ℝ) with hy11232 | hy11232
        · have hs112320 : InSquare (41/160) (-7/32) (1/160) tau := by
            convert childLL hs11232 hx11232 hy11232 using 1 <;> norm_num
          exact Batch0085.cell0681.sound htau (by
            simp only [Batch0085.cell0681, Batch0085.tau0681, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs112320 (by positivity) using 1 <;> norm_num)
        · have hs112322 : InSquare (41/160) (-33/160) (1/160) tau := by
            convert childUL hs11232 hx11232 hy11232 using 1 <;> norm_num
          exact Batch0085.cell0683.sound htau (by
            simp only [Batch0085.cell0683, Batch0085.tau0683, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs112322 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-17/80 : ℝ) with hy11232 | hy11232
        · have hs112321 : InSquare (43/160) (-7/32) (1/160) tau := by
            convert childLR hs11232 hx11232 hy11232 using 1 <;> norm_num
          exact Batch0085.cell0682.sound htau (by
            simp only [Batch0085.cell0682, Batch0085.tau0682, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs112321 (by positivity) using 1 <;> norm_num)
        · have hs112323 : InSquare (43/160) (-33/160) (1/160) tau := by
            convert childUR hs11232 hx11232 hy11232 using 1 <;> norm_num
          exact Batch0085.cell0684.sound htau (by
            simp only [Batch0085.cell0684, Batch0085.tau0684, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs112323 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (-9/40 : ℝ) with hy1123 | hy1123
    · have hs11231 : InSquare (23/80) (-19/80) (1/80) tau := by
        convert childLR hs hx1123 hy1123 using 1 <;> norm_num
      rcases le_total tau.re (23/80 : ℝ) with hx11231 | hx11231
      · rcases le_total tau.im (-19/80 : ℝ) with hy11231 | hy11231
        · have hs112310 : InSquare (9/32) (-39/160) (1/160) tau := by
            convert childLL hs11231 hx11231 hy11231 using 1 <;> norm_num
          exact Batch0084.cell0678.sound htau (by
            simp only [Batch0084.cell0678, Batch0084.tau0678, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs112310 (by positivity) using 1 <;> norm_num)
        · have hs112312 : InSquare (9/32) (-37/160) (1/160) tau := by
            convert childUL hs11231 hx11231 hy11231 using 1 <;> norm_num
          exact Batch0084.cell0679.sound htau (by
            simp only [Batch0084.cell0679, Batch0084.tau0679, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs112312 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-19/80 : ℝ) with hy11231 | hy11231
        · have hs112311 : InSquare (47/160) (-39/160) (1/160) tau := by
            convert childLR hs11231 hx11231 hy11231 using 1 <;> norm_num
          rcases le_total tau.re (47/160 : ℝ) with hx112311 | hx112311
          · rcases le_total tau.im (-39/160 : ℝ) with hy112311 | hy112311
            · have hs1123110 : InSquare (93/320) (-79/320) (1/320) tau := by
                convert childLL hs112311 hx112311 hy112311 using 1 <;> norm_num
              exact Batch0231.cell1851.sound htau (by
                simp only [Batch0231.cell1851, Batch0231.tau1851, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1123110 (by positivity) using 1 <;> norm_num)
            · have hs1123112 : InSquare (93/320) (-77/320) (1/320) tau := by
                convert childUL hs112311 hx112311 hy112311 using 1 <;> norm_num
              exact Batch0231.cell1853.sound htau (by
                simp only [Batch0231.cell1853, Batch0231.tau1853, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1123112 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-39/160 : ℝ) with hy112311 | hy112311
            · have hs1123111 : InSquare (19/64) (-79/320) (1/320) tau := by
                convert childLR hs112311 hx112311 hy112311 using 1 <;> norm_num
              exact Batch0231.cell1852.sound htau (by
                simp only [Batch0231.cell1852, Batch0231.tau1852, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1123111 (by positivity) using 1 <;> norm_num)
            · have hs1123113 : InSquare (19/64) (-77/320) (1/320) tau := by
                convert childUR hs112311 hx112311 hy112311 using 1 <;> norm_num
              exact Batch0231.cell1854.sound htau (by
                simp only [Batch0231.cell1854, Batch0231.tau1854, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1123113 (by positivity) using 1 <;> norm_num)
        · have hs112313 : InSquare (47/160) (-37/160) (1/160) tau := by
            convert childUR hs11231 hx11231 hy11231 using 1 <;> norm_num
          exact Batch0085.cell0680.sound htau (by
            simp only [Batch0085.cell0680, Batch0085.tau0680, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs112313 (by positivity) using 1 <;> norm_num)
    · have hs11233 : InSquare (23/80) (-17/80) (1/80) tau := by
        convert childUR hs hx1123 hy1123 using 1 <;> norm_num
      rcases le_total tau.re (23/80 : ℝ) with hx11233 | hx11233
      · rcases le_total tau.im (-17/80 : ℝ) with hy11233 | hy11233
        · have hs112330 : InSquare (9/32) (-7/32) (1/160) tau := by
            convert childLL hs11233 hx11233 hy11233 using 1 <;> norm_num
          exact Batch0085.cell0685.sound htau (by
            simp only [Batch0085.cell0685, Batch0085.tau0685, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs112330 (by positivity) using 1 <;> norm_num)
        · have hs112332 : InSquare (9/32) (-33/160) (1/160) tau := by
            convert childUL hs11233 hx11233 hy11233 using 1 <;> norm_num
          exact Batch0085.cell0687.sound htau (by
            simp only [Batch0085.cell0687, Batch0085.tau0687, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs112332 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-17/80 : ℝ) with hy11233 | hy11233
        · have hs112331 : InSquare (47/160) (-7/32) (1/160) tau := by
            convert childLR hs11233 hx11233 hy11233 using 1 <;> norm_num
          exact Batch0085.cell0686.sound htau (by
            simp only [Batch0085.cell0686, Batch0085.tau0686, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs112331 (by positivity) using 1 <;> norm_num)
        · have hs112333 : InSquare (47/160) (-33/160) (1/160) tau := by
            convert childUR hs11233 hx11233 hy11233 using 1 <;> norm_num
          exact Batch0086.cell0688.sound htau (by
            simp only [Batch0086.cell0688, Batch0086.tau0688, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs112333 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1123
