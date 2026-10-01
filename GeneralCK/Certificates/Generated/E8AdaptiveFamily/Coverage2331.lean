import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0121
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0122
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0123

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2331

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-1/40) (13/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (-1/40 : ℝ) with hx2331 | hx2331
  · rcases le_total tau.im (13/40 : ℝ) with hy2331 | hy2331
    · have hs23310 : InSquare (-3/80) (5/16) (1/80) tau := by
        convert childLL hs hx2331 hy2331 using 1 <;> norm_num
      rcases le_total tau.re (-3/80 : ℝ) with hx23310 | hx23310
      · rcases le_total tau.im (5/16 : ℝ) with hy23310 | hy23310
        · have hs233100 : InSquare (-7/160) (49/160) (1/160) tau := by
            convert childLL hs23310 hx23310 hy23310 using 1 <;> norm_num
          exact Batch0121.cell0969.sound htau (by
            simp only [Batch0121.cell0969, Batch0121.tau0969, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs233100 (by positivity) using 1 <;> norm_num)
        · have hs233102 : InSquare (-7/160) (51/160) (1/160) tau := by
            convert childUL hs23310 hx23310 hy23310 using 1 <;> norm_num
          exact Batch0121.cell0971.sound htau (by
            simp only [Batch0121.cell0971, Batch0121.tau0971, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs233102 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (5/16 : ℝ) with hy23310 | hy23310
        · have hs233101 : InSquare (-1/32) (49/160) (1/160) tau := by
            convert childLR hs23310 hx23310 hy23310 using 1 <;> norm_num
          exact Batch0121.cell0970.sound htau (by
            simp only [Batch0121.cell0970, Batch0121.tau0970, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs233101 (by positivity) using 1 <;> norm_num)
        · have hs233103 : InSquare (-1/32) (51/160) (1/160) tau := by
            convert childUR hs23310 hx23310 hy23310 using 1 <;> norm_num
          exact Batch0121.cell0972.sound htau (by
            simp only [Batch0121.cell0972, Batch0121.tau0972, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs233103 (by positivity) using 1 <;> norm_num)
    · have hs23312 : InSquare (-3/80) (27/80) (1/80) tau := by
        convert childUL hs hx2331 hy2331 using 1 <;> norm_num
      rcases le_total tau.re (-3/80 : ℝ) with hx23312 | hx23312
      · rcases le_total tau.im (27/80 : ℝ) with hy23312 | hy23312
        · have hs233120 : InSquare (-7/160) (53/160) (1/160) tau := by
            convert childLL hs23312 hx23312 hy23312 using 1 <;> norm_num
          exact Batch0122.cell0977.sound htau (by
            simp only [Batch0122.cell0977, Batch0122.tau0977, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs233120 (by positivity) using 1 <;> norm_num)
        · have hs233122 : InSquare (-7/160) (11/32) (1/160) tau := by
            convert childUL hs23312 hx23312 hy23312 using 1 <;> norm_num
          exact Batch0122.cell0979.sound htau (by
            simp only [Batch0122.cell0979, Batch0122.tau0979, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs233122 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (27/80 : ℝ) with hy23312 | hy23312
        · have hs233121 : InSquare (-1/32) (53/160) (1/160) tau := by
            convert childLR hs23312 hx23312 hy23312 using 1 <;> norm_num
          exact Batch0122.cell0978.sound htau (by
            simp only [Batch0122.cell0978, Batch0122.tau0978, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs233121 (by positivity) using 1 <;> norm_num)
        · have hs233123 : InSquare (-1/32) (11/32) (1/160) tau := by
            convert childUR hs23312 hx23312 hy23312 using 1 <;> norm_num
          exact Batch0122.cell0980.sound htau (by
            simp only [Batch0122.cell0980, Batch0122.tau0980, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs233123 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (13/40 : ℝ) with hy2331 | hy2331
    · have hs23311 : InSquare (-1/80) (5/16) (1/80) tau := by
        convert childLR hs hx2331 hy2331 using 1 <;> norm_num
      rcases le_total tau.re (-1/80 : ℝ) with hx23311 | hx23311
      · rcases le_total tau.im (5/16 : ℝ) with hy23311 | hy23311
        · have hs233110 : InSquare (-3/160) (49/160) (1/160) tau := by
            convert childLL hs23311 hx23311 hy23311 using 1 <;> norm_num
          exact Batch0121.cell0973.sound htau (by
            simp only [Batch0121.cell0973, Batch0121.tau0973, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs233110 (by positivity) using 1 <;> norm_num)
        · have hs233112 : InSquare (-3/160) (51/160) (1/160) tau := by
            convert childUL hs23311 hx23311 hy23311 using 1 <;> norm_num
          exact Batch0121.cell0975.sound htau (by
            simp only [Batch0121.cell0975, Batch0121.tau0975, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs233112 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (5/16 : ℝ) with hy23311 | hy23311
        · have hs233111 : InSquare (-1/160) (49/160) (1/160) tau := by
            convert childLR hs23311 hx23311 hy23311 using 1 <;> norm_num
          exact Batch0121.cell0974.sound htau (by
            simp only [Batch0121.cell0974, Batch0121.tau0974, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs233111 (by positivity) using 1 <;> norm_num)
        · have hs233113 : InSquare (-1/160) (51/160) (1/160) tau := by
            convert childUR hs23311 hx23311 hy23311 using 1 <;> norm_num
          exact Batch0122.cell0976.sound htau (by
            simp only [Batch0122.cell0976, Batch0122.tau0976, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs233113 (by positivity) using 1 <;> norm_num)
    · have hs23313 : InSquare (-1/80) (27/80) (1/80) tau := by
        convert childUR hs hx2331 hy2331 using 1 <;> norm_num
      rcases le_total tau.re (-1/80 : ℝ) with hx23313 | hx23313
      · rcases le_total tau.im (27/80 : ℝ) with hy23313 | hy23313
        · have hs233130 : InSquare (-3/160) (53/160) (1/160) tau := by
            convert childLL hs23313 hx23313 hy23313 using 1 <;> norm_num
          exact Batch0122.cell0981.sound htau (by
            simp only [Batch0122.cell0981, Batch0122.tau0981, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs233130 (by positivity) using 1 <;> norm_num)
        · have hs233132 : InSquare (-3/160) (11/32) (1/160) tau := by
            convert childUL hs23313 hx23313 hy23313 using 1 <;> norm_num
          exact Batch0122.cell0983.sound htau (by
            simp only [Batch0122.cell0983, Batch0122.tau0983, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs233132 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (27/80 : ℝ) with hy23313 | hy23313
        · have hs233131 : InSquare (-1/160) (53/160) (1/160) tau := by
            convert childLR hs23313 hx23313 hy23313 using 1 <;> norm_num
          exact Batch0122.cell0982.sound htau (by
            simp only [Batch0122.cell0982, Batch0122.tau0982, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs233131 (by positivity) using 1 <;> norm_num)
        · have hs233133 : InSquare (-1/160) (11/32) (1/160) tau := by
            convert childUR hs23313 hx23313 hy23313 using 1 <;> norm_num
          exact Batch0123.cell0984.sound htau (by
            simp only [Batch0123.cell0984, Batch0123.tau0984, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs233133 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2331
