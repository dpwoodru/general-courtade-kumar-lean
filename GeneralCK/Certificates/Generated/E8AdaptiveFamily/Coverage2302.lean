import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0113
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0114
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0115

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2302

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-7/40) (11/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (-7/40 : ℝ) with hx2302 | hx2302
  · rcases le_total tau.im (11/40 : ℝ) with hy2302 | hy2302
    · have hs23020 : InSquare (-3/16) (21/80) (1/80) tau := by
        convert childLL hs hx2302 hy2302 using 1 <;> norm_num
      rcases le_total tau.re (-3/16 : ℝ) with hx23020 | hx23020
      · rcases le_total tau.im (21/80 : ℝ) with hy23020 | hy23020
        · have hs230200 : InSquare (-31/160) (41/160) (1/160) tau := by
            convert childLL hs23020 hx23020 hy23020 using 1 <;> norm_num
          exact Batch0113.cell0906.sound htau (by
            simp only [Batch0113.cell0906, Batch0113.tau0906, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs230200 (by positivity) using 1 <;> norm_num)
        · have hs230202 : InSquare (-31/160) (43/160) (1/160) tau := by
            convert childUL hs23020 hx23020 hy23020 using 1 <;> norm_num
          exact Batch0113.cell0908.sound htau (by
            simp only [Batch0113.cell0908, Batch0113.tau0908, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs230202 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (21/80 : ℝ) with hy23020 | hy23020
        · have hs230201 : InSquare (-29/160) (41/160) (1/160) tau := by
            convert childLR hs23020 hx23020 hy23020 using 1 <;> norm_num
          exact Batch0113.cell0907.sound htau (by
            simp only [Batch0113.cell0907, Batch0113.tau0907, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs230201 (by positivity) using 1 <;> norm_num)
        · have hs230203 : InSquare (-29/160) (43/160) (1/160) tau := by
            convert childUR hs23020 hx23020 hy23020 using 1 <;> norm_num
          exact Batch0113.cell0909.sound htau (by
            simp only [Batch0113.cell0909, Batch0113.tau0909, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs230203 (by positivity) using 1 <;> norm_num)
    · have hs23022 : InSquare (-3/16) (23/80) (1/80) tau := by
        convert childUL hs hx2302 hy2302 using 1 <;> norm_num
      rcases le_total tau.re (-3/16 : ℝ) with hx23022 | hx23022
      · rcases le_total tau.im (23/80 : ℝ) with hy23022 | hy23022
        · have hs230220 : InSquare (-31/160) (9/32) (1/160) tau := by
            convert childLL hs23022 hx23022 hy23022 using 1 <;> norm_num
          exact Batch0114.cell0914.sound htau (by
            simp only [Batch0114.cell0914, Batch0114.tau0914, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs230220 (by positivity) using 1 <;> norm_num)
        · have hs230222 : InSquare (-31/160) (47/160) (1/160) tau := by
            convert childUL hs23022 hx23022 hy23022 using 1 <;> norm_num
          exact Batch0114.cell0916.sound htau (by
            simp only [Batch0114.cell0916, Batch0114.tau0916, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs230222 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (23/80 : ℝ) with hy23022 | hy23022
        · have hs230221 : InSquare (-29/160) (9/32) (1/160) tau := by
            convert childLR hs23022 hx23022 hy23022 using 1 <;> norm_num
          exact Batch0114.cell0915.sound htau (by
            simp only [Batch0114.cell0915, Batch0114.tau0915, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs230221 (by positivity) using 1 <;> norm_num)
        · have hs230223 : InSquare (-29/160) (47/160) (1/160) tau := by
            convert childUR hs23022 hx23022 hy23022 using 1 <;> norm_num
          exact Batch0114.cell0917.sound htau (by
            simp only [Batch0114.cell0917, Batch0114.tau0917, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs230223 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (11/40 : ℝ) with hy2302 | hy2302
    · have hs23021 : InSquare (-13/80) (21/80) (1/80) tau := by
        convert childLR hs hx2302 hy2302 using 1 <;> norm_num
      rcases le_total tau.re (-13/80 : ℝ) with hx23021 | hx23021
      · rcases le_total tau.im (21/80 : ℝ) with hy23021 | hy23021
        · have hs230210 : InSquare (-27/160) (41/160) (1/160) tau := by
            convert childLL hs23021 hx23021 hy23021 using 1 <;> norm_num
          exact Batch0113.cell0910.sound htau (by
            simp only [Batch0113.cell0910, Batch0113.tau0910, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs230210 (by positivity) using 1 <;> norm_num)
        · have hs230212 : InSquare (-27/160) (43/160) (1/160) tau := by
            convert childUL hs23021 hx23021 hy23021 using 1 <;> norm_num
          exact Batch0114.cell0912.sound htau (by
            simp only [Batch0114.cell0912, Batch0114.tau0912, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs230212 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (21/80 : ℝ) with hy23021 | hy23021
        · have hs230211 : InSquare (-5/32) (41/160) (1/160) tau := by
            convert childLR hs23021 hx23021 hy23021 using 1 <;> norm_num
          exact Batch0113.cell0911.sound htau (by
            simp only [Batch0113.cell0911, Batch0113.tau0911, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs230211 (by positivity) using 1 <;> norm_num)
        · have hs230213 : InSquare (-5/32) (43/160) (1/160) tau := by
            convert childUR hs23021 hx23021 hy23021 using 1 <;> norm_num
          exact Batch0114.cell0913.sound htau (by
            simp only [Batch0114.cell0913, Batch0114.tau0913, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs230213 (by positivity) using 1 <;> norm_num)
    · have hs23023 : InSquare (-13/80) (23/80) (1/80) tau := by
        convert childUR hs hx2302 hy2302 using 1 <;> norm_num
      rcases le_total tau.re (-13/80 : ℝ) with hx23023 | hx23023
      · rcases le_total tau.im (23/80 : ℝ) with hy23023 | hy23023
        · have hs230230 : InSquare (-27/160) (9/32) (1/160) tau := by
            convert childLL hs23023 hx23023 hy23023 using 1 <;> norm_num
          exact Batch0114.cell0918.sound htau (by
            simp only [Batch0114.cell0918, Batch0114.tau0918, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs230230 (by positivity) using 1 <;> norm_num)
        · have hs230232 : InSquare (-27/160) (47/160) (1/160) tau := by
            convert childUL hs23023 hx23023 hy23023 using 1 <;> norm_num
          exact Batch0115.cell0920.sound htau (by
            simp only [Batch0115.cell0920, Batch0115.tau0920, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs230232 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (23/80 : ℝ) with hy23023 | hy23023
        · have hs230231 : InSquare (-5/32) (9/32) (1/160) tau := by
            convert childLR hs23023 hx23023 hy23023 using 1 <;> norm_num
          exact Batch0114.cell0919.sound htau (by
            simp only [Batch0114.cell0919, Batch0114.tau0919, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs230231 (by positivity) using 1 <;> norm_num)
        · have hs230233 : InSquare (-5/32) (47/160) (1/160) tau := by
            convert childUR hs23023 hx23023 hy23023 using 1 <;> norm_num
          exact Batch0115.cell0921.sound htau (by
            simp only [Batch0115.cell0921, Batch0115.tau0921, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs230233 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2302
