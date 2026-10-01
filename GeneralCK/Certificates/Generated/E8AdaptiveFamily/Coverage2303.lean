import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0115
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0116
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0117

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2303

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-1/8) (11/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (-1/8 : ℝ) with hx2303 | hx2303
  · rcases le_total tau.im (11/40 : ℝ) with hy2303 | hy2303
    · have hs23030 : InSquare (-11/80) (21/80) (1/80) tau := by
        convert childLL hs hx2303 hy2303 using 1 <;> norm_num
      rcases le_total tau.re (-11/80 : ℝ) with hx23030 | hx23030
      · rcases le_total tau.im (21/80 : ℝ) with hy23030 | hy23030
        · have hs230300 : InSquare (-23/160) (41/160) (1/160) tau := by
            convert childLL hs23030 hx23030 hy23030 using 1 <;> norm_num
          exact Batch0115.cell0922.sound htau (by
            simp only [Batch0115.cell0922, Batch0115.tau0922, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs230300 (by positivity) using 1 <;> norm_num)
        · have hs230302 : InSquare (-23/160) (43/160) (1/160) tau := by
            convert childUL hs23030 hx23030 hy23030 using 1 <;> norm_num
          exact Batch0115.cell0924.sound htau (by
            simp only [Batch0115.cell0924, Batch0115.tau0924, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs230302 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (21/80 : ℝ) with hy23030 | hy23030
        · have hs230301 : InSquare (-21/160) (41/160) (1/160) tau := by
            convert childLR hs23030 hx23030 hy23030 using 1 <;> norm_num
          exact Batch0115.cell0923.sound htau (by
            simp only [Batch0115.cell0923, Batch0115.tau0923, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs230301 (by positivity) using 1 <;> norm_num)
        · have hs230303 : InSquare (-21/160) (43/160) (1/160) tau := by
            convert childUR hs23030 hx23030 hy23030 using 1 <;> norm_num
          exact Batch0115.cell0925.sound htau (by
            simp only [Batch0115.cell0925, Batch0115.tau0925, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs230303 (by positivity) using 1 <;> norm_num)
    · have hs23032 : InSquare (-11/80) (23/80) (1/80) tau := by
        convert childUL hs hx2303 hy2303 using 1 <;> norm_num
      rcases le_total tau.re (-11/80 : ℝ) with hx23032 | hx23032
      · rcases le_total tau.im (23/80 : ℝ) with hy23032 | hy23032
        · have hs230320 : InSquare (-23/160) (9/32) (1/160) tau := by
            convert childLL hs23032 hx23032 hy23032 using 1 <;> norm_num
          exact Batch0116.cell0930.sound htau (by
            simp only [Batch0116.cell0930, Batch0116.tau0930, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs230320 (by positivity) using 1 <;> norm_num)
        · have hs230322 : InSquare (-23/160) (47/160) (1/160) tau := by
            convert childUL hs23032 hx23032 hy23032 using 1 <;> norm_num
          exact Batch0116.cell0932.sound htau (by
            simp only [Batch0116.cell0932, Batch0116.tau0932, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs230322 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (23/80 : ℝ) with hy23032 | hy23032
        · have hs230321 : InSquare (-21/160) (9/32) (1/160) tau := by
            convert childLR hs23032 hx23032 hy23032 using 1 <;> norm_num
          exact Batch0116.cell0931.sound htau (by
            simp only [Batch0116.cell0931, Batch0116.tau0931, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs230321 (by positivity) using 1 <;> norm_num)
        · have hs230323 : InSquare (-21/160) (47/160) (1/160) tau := by
            convert childUR hs23032 hx23032 hy23032 using 1 <;> norm_num
          exact Batch0116.cell0933.sound htau (by
            simp only [Batch0116.cell0933, Batch0116.tau0933, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs230323 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (11/40 : ℝ) with hy2303 | hy2303
    · have hs23031 : InSquare (-9/80) (21/80) (1/80) tau := by
        convert childLR hs hx2303 hy2303 using 1 <;> norm_num
      rcases le_total tau.re (-9/80 : ℝ) with hx23031 | hx23031
      · rcases le_total tau.im (21/80 : ℝ) with hy23031 | hy23031
        · have hs230310 : InSquare (-19/160) (41/160) (1/160) tau := by
            convert childLL hs23031 hx23031 hy23031 using 1 <;> norm_num
          exact Batch0115.cell0926.sound htau (by
            simp only [Batch0115.cell0926, Batch0115.tau0926, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs230310 (by positivity) using 1 <;> norm_num)
        · have hs230312 : InSquare (-19/160) (43/160) (1/160) tau := by
            convert childUL hs23031 hx23031 hy23031 using 1 <;> norm_num
          exact Batch0116.cell0928.sound htau (by
            simp only [Batch0116.cell0928, Batch0116.tau0928, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs230312 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (21/80 : ℝ) with hy23031 | hy23031
        · have hs230311 : InSquare (-17/160) (41/160) (1/160) tau := by
            convert childLR hs23031 hx23031 hy23031 using 1 <;> norm_num
          exact Batch0115.cell0927.sound htau (by
            simp only [Batch0115.cell0927, Batch0115.tau0927, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs230311 (by positivity) using 1 <;> norm_num)
        · have hs230313 : InSquare (-17/160) (43/160) (1/160) tau := by
            convert childUR hs23031 hx23031 hy23031 using 1 <;> norm_num
          exact Batch0116.cell0929.sound htau (by
            simp only [Batch0116.cell0929, Batch0116.tau0929, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs230313 (by positivity) using 1 <;> norm_num)
    · have hs23033 : InSquare (-9/80) (23/80) (1/80) tau := by
        convert childUR hs hx2303 hy2303 using 1 <;> norm_num
      rcases le_total tau.re (-9/80 : ℝ) with hx23033 | hx23033
      · rcases le_total tau.im (23/80 : ℝ) with hy23033 | hy23033
        · have hs230330 : InSquare (-19/160) (9/32) (1/160) tau := by
            convert childLL hs23033 hx23033 hy23033 using 1 <;> norm_num
          exact Batch0116.cell0934.sound htau (by
            simp only [Batch0116.cell0934, Batch0116.tau0934, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs230330 (by positivity) using 1 <;> norm_num)
        · have hs230332 : InSquare (-19/160) (47/160) (1/160) tau := by
            convert childUL hs23033 hx23033 hy23033 using 1 <;> norm_num
          exact Batch0117.cell0936.sound htau (by
            simp only [Batch0117.cell0936, Batch0117.tau0936, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs230332 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (23/80 : ℝ) with hy23033 | hy23033
        · have hs230331 : InSquare (-17/160) (9/32) (1/160) tau := by
            convert childLR hs23033 hx23033 hy23033 using 1 <;> norm_num
          exact Batch0116.cell0935.sound htau (by
            simp only [Batch0116.cell0935, Batch0116.tau0935, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs230331 (by positivity) using 1 <;> norm_num)
        · have hs230333 : InSquare (-17/160) (47/160) (1/160) tau := by
            convert childUR hs23033 hx23033 hy23033 using 1 <;> norm_num
          exact Batch0117.cell0937.sound htau (by
            simp only [Batch0117.cell0937, Batch0117.tau0937, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs230333 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2303
