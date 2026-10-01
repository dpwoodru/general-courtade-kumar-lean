import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0028

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2031

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-9/40) (1/8) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (-9/40 : ℝ) with hx2031 | hx2031
  · rcases le_total tau.im (1/8 : ℝ) with hy2031 | hy2031
    · have hs20310 : InSquare (-19/80) (9/80) (1/80) tau := by
        convert childLL hs hx2031 hy2031 using 1 <;> norm_num
      exact Batch0028.cell0227.sound htau (by
        simp only [Batch0028.cell0227, Batch0028.tau0227, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs20310 (by positivity) using 1 <;> norm_num)
    · have hs20312 : InSquare (-19/80) (11/80) (1/80) tau := by
        convert childUL hs hx2031 hy2031 using 1 <;> norm_num
      exact Batch0028.cell0229.sound htau (by
        simp only [Batch0028.cell0229, Batch0028.tau0229, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs20312 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (1/8 : ℝ) with hy2031 | hy2031
    · have hs20311 : InSquare (-17/80) (9/80) (1/80) tau := by
        convert childLR hs hx2031 hy2031 using 1 <;> norm_num
      exact Batch0028.cell0228.sound htau (by
        simp only [Batch0028.cell0228, Batch0028.tau0228, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs20311 (by positivity) using 1 <;> norm_num)
    · have hs20313 : InSquare (-17/80) (11/80) (1/80) tau := by
        convert childUR hs hx2031 hy2031 using 1 <;> norm_num
      exact Batch0028.cell0230.sound htau (by
        simp only [Batch0028.cell0230, Batch0028.tau0230, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs20313 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2031
