import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0025

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2001

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-13/40) (1/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (-13/40 : ℝ) with hx2001 | hx2001
  · rcases le_total tau.im (1/40 : ℝ) with hy2001 | hy2001
    · have hs20010 : InSquare (-27/80) (1/80) (1/80) tau := by
        convert childLL hs hx2001 hy2001 using 1 <;> norm_num
      exact Batch0025.cell0201.sound htau (by
        simp only [Batch0025.cell0201, Batch0025.tau0201, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs20010 (by positivity) using 1 <;> norm_num)
    · have hs20012 : InSquare (-27/80) (3/80) (1/80) tau := by
        convert childUL hs hx2001 hy2001 using 1 <;> norm_num
      exact Batch0025.cell0203.sound htau (by
        simp only [Batch0025.cell0203, Batch0025.tau0203, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs20012 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (1/40 : ℝ) with hy2001 | hy2001
    · have hs20011 : InSquare (-5/16) (1/80) (1/80) tau := by
        convert childLR hs hx2001 hy2001 using 1 <;> norm_num
      exact Batch0025.cell0202.sound htau (by
        simp only [Batch0025.cell0202, Batch0025.tau0202, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs20011 (by positivity) using 1 <;> norm_num)
    · have hs20013 : InSquare (-5/16) (3/80) (1/80) tau := by
        convert childUR hs hx2001 hy2001 using 1 <;> norm_num
      exact Batch0025.cell0204.sound htau (by
        simp only [Batch0025.cell0204, Batch0025.tau0204, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs20013 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2001
