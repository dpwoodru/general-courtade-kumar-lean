import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0031
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0112
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0113

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2300

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-7/40) (9/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (-7/40 : ℝ) with hx2300 | hx2300
  · rcases le_total tau.im (9/40 : ℝ) with hy2300 | hy2300
    · have hs23000 : InSquare (-3/16) (17/80) (1/80) tau := by
        convert childLL hs hx2300 hy2300 using 1 <;> norm_num
      exact Batch0031.cell0251.sound htau (by
        simp only [Batch0031.cell0251, Batch0031.tau0251, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs23000 (by positivity) using 1 <;> norm_num)
    · have hs23002 : InSquare (-3/16) (19/80) (1/80) tau := by
        convert childUL hs hx2300 hy2300 using 1 <;> norm_num
      rcases le_total tau.re (-3/16 : ℝ) with hx23002 | hx23002
      · rcases le_total tau.im (19/80 : ℝ) with hy23002 | hy23002
        · have hs230020 : InSquare (-31/160) (37/160) (1/160) tau := by
            convert childLL hs23002 hx23002 hy23002 using 1 <;> norm_num
          exact Batch0112.cell0898.sound htau (by
            simp only [Batch0112.cell0898, Batch0112.tau0898, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs230020 (by positivity) using 1 <;> norm_num)
        · have hs230022 : InSquare (-31/160) (39/160) (1/160) tau := by
            convert childUL hs23002 hx23002 hy23002 using 1 <;> norm_num
          exact Batch0112.cell0900.sound htau (by
            simp only [Batch0112.cell0900, Batch0112.tau0900, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs230022 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (19/80 : ℝ) with hy23002 | hy23002
        · have hs230021 : InSquare (-29/160) (37/160) (1/160) tau := by
            convert childLR hs23002 hx23002 hy23002 using 1 <;> norm_num
          exact Batch0112.cell0899.sound htau (by
            simp only [Batch0112.cell0899, Batch0112.tau0899, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs230021 (by positivity) using 1 <;> norm_num)
        · have hs230023 : InSquare (-29/160) (39/160) (1/160) tau := by
            convert childUR hs23002 hx23002 hy23002 using 1 <;> norm_num
          exact Batch0112.cell0901.sound htau (by
            simp only [Batch0112.cell0901, Batch0112.tau0901, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs230023 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (9/40 : ℝ) with hy2300 | hy2300
    · have hs23001 : InSquare (-13/80) (17/80) (1/80) tau := by
        convert childLR hs hx2300 hy2300 using 1 <;> norm_num
      exact Batch0031.cell0252.sound htau (by
        simp only [Batch0031.cell0252, Batch0031.tau0252, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs23001 (by positivity) using 1 <;> norm_num)
    · have hs23003 : InSquare (-13/80) (19/80) (1/80) tau := by
        convert childUR hs hx2300 hy2300 using 1 <;> norm_num
      rcases le_total tau.re (-13/80 : ℝ) with hx23003 | hx23003
      · rcases le_total tau.im (19/80 : ℝ) with hy23003 | hy23003
        · have hs230030 : InSquare (-27/160) (37/160) (1/160) tau := by
            convert childLL hs23003 hx23003 hy23003 using 1 <;> norm_num
          exact Batch0112.cell0902.sound htau (by
            simp only [Batch0112.cell0902, Batch0112.tau0902, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs230030 (by positivity) using 1 <;> norm_num)
        · have hs230032 : InSquare (-27/160) (39/160) (1/160) tau := by
            convert childUL hs23003 hx23003 hy23003 using 1 <;> norm_num
          exact Batch0113.cell0904.sound htau (by
            simp only [Batch0113.cell0904, Batch0113.tau0904, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs230032 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (19/80 : ℝ) with hy23003 | hy23003
        · have hs230031 : InSquare (-5/32) (37/160) (1/160) tau := by
            convert childLR hs23003 hx23003 hy23003 using 1 <;> norm_num
          exact Batch0112.cell0903.sound htau (by
            simp only [Batch0112.cell0903, Batch0112.tau0903, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs230031 (by positivity) using 1 <;> norm_num)
        · have hs230033 : InSquare (-5/32) (39/160) (1/160) tau := by
            convert childUR hs23003 hx23003 hy23003 using 1 <;> norm_num
          exact Batch0113.cell0905.sound htau (by
            simp only [Batch0113.cell0905, Batch0113.tau0905, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs230033 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2300
