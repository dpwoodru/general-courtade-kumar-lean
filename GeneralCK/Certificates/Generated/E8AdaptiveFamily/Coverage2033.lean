import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0029
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0105
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0106

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2033

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-9/40) (7/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (-9/40 : ℝ) with hx2033 | hx2033
  · rcases le_total tau.im (7/40 : ℝ) with hy2033 | hy2033
    · have hs20330 : InSquare (-19/80) (13/80) (1/80) tau := by
        convert childLL hs hx2033 hy2033 using 1 <;> norm_num
      exact Batch0029.cell0232.sound htau (by
        simp only [Batch0029.cell0232, Batch0029.tau0232, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs20330 (by positivity) using 1 <;> norm_num)
    · have hs20332 : InSquare (-19/80) (3/16) (1/80) tau := by
        convert childUL hs hx2033 hy2033 using 1 <;> norm_num
      rcases le_total tau.re (-19/80 : ℝ) with hx20332 | hx20332
      · rcases le_total tau.im (3/16 : ℝ) with hy20332 | hy20332
        · have hs203320 : InSquare (-39/160) (29/160) (1/160) tau := by
            convert childLL hs20332 hx20332 hy20332 using 1 <;> norm_num
          exact Batch0105.cell0845.sound htau (by
            simp only [Batch0105.cell0845, Batch0105.tau0845, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs203320 (by positivity) using 1 <;> norm_num)
        · have hs203322 : InSquare (-39/160) (31/160) (1/160) tau := by
            convert childUL hs20332 hx20332 hy20332 using 1 <;> norm_num
          exact Batch0105.cell0847.sound htau (by
            simp only [Batch0105.cell0847, Batch0105.tau0847, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs203322 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (3/16 : ℝ) with hy20332 | hy20332
        · have hs203321 : InSquare (-37/160) (29/160) (1/160) tau := by
            convert childLR hs20332 hx20332 hy20332 using 1 <;> norm_num
          exact Batch0105.cell0846.sound htau (by
            simp only [Batch0105.cell0846, Batch0105.tau0846, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs203321 (by positivity) using 1 <;> norm_num)
        · have hs203323 : InSquare (-37/160) (31/160) (1/160) tau := by
            convert childUR hs20332 hx20332 hy20332 using 1 <;> norm_num
          exact Batch0106.cell0848.sound htau (by
            simp only [Batch0106.cell0848, Batch0106.tau0848, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs203323 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (7/40 : ℝ) with hy2033 | hy2033
    · have hs20331 : InSquare (-17/80) (13/80) (1/80) tau := by
        convert childLR hs hx2033 hy2033 using 1 <;> norm_num
      exact Batch0029.cell0233.sound htau (by
        simp only [Batch0029.cell0233, Batch0029.tau0233, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs20331 (by positivity) using 1 <;> norm_num)
    · have hs20333 : InSquare (-17/80) (3/16) (1/80) tau := by
        convert childUR hs hx2033 hy2033 using 1 <;> norm_num
      exact Batch0029.cell0234.sound htau (by
        simp only [Batch0029.cell0234, Batch0029.tau0234, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs20333 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2033
