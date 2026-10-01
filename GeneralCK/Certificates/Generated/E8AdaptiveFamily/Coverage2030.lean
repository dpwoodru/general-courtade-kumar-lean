import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0027
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0028

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2030

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-11/40) (1/8) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (-11/40 : ℝ) with hx2030 | hx2030
  · rcases le_total tau.im (1/8 : ℝ) with hy2030 | hy2030
    · have hs20300 : InSquare (-23/80) (9/80) (1/80) tau := by
        convert childLL hs hx2030 hy2030 using 1 <;> norm_num
      exact Batch0027.cell0223.sound htau (by
        simp only [Batch0027.cell0223, Batch0027.tau0223, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs20300 (by positivity) using 1 <;> norm_num)
    · have hs20302 : InSquare (-23/80) (11/80) (1/80) tau := by
        convert childUL hs hx2030 hy2030 using 1 <;> norm_num
      exact Batch0028.cell0225.sound htau (by
        simp only [Batch0028.cell0225, Batch0028.tau0225, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs20302 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (1/8 : ℝ) with hy2030 | hy2030
    · have hs20301 : InSquare (-21/80) (9/80) (1/80) tau := by
        convert childLR hs hx2030 hy2030 using 1 <;> norm_num
      exact Batch0028.cell0224.sound htau (by
        simp only [Batch0028.cell0224, Batch0028.tau0224, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs20301 (by positivity) using 1 <;> norm_num)
    · have hs20303 : InSquare (-21/80) (11/80) (1/80) tau := by
        convert childUR hs hx2030 hy2030 using 1 <;> norm_num
      exact Batch0028.cell0226.sound htau (by
        simp only [Batch0028.cell0226, Batch0028.tau0226, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs20303 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2030
