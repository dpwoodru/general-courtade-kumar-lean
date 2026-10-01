import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0024
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0025
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0096

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2000

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-3/8) (1/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (-3/8 : ℝ) with hx2000 | hx2000
  · rcases le_total tau.im (1/40 : ℝ) with hy2000 | hy2000
    · have hs20000 : InSquare (-31/80) (1/80) (1/80) tau := by
        convert childLL hs hx2000 hy2000 using 1 <;> norm_num
      exact Batch0024.cell0198.sound htau (by
        simp only [Batch0024.cell0198, Batch0024.tau0198, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs20000 (by positivity) using 1 <;> norm_num)
    · have hs20002 : InSquare (-31/80) (3/80) (1/80) tau := by
        convert childUL hs hx2000 hy2000 using 1 <;> norm_num
      rcases le_total tau.re (-31/80 : ℝ) with hx20002 | hx20002
      · rcases le_total tau.im (3/80 : ℝ) with hy20002 | hy20002
        · have hs200020 : InSquare (-63/160) (1/32) (1/160) tau := by
            convert childLL hs20002 hx20002 hy20002 using 1 <;> norm_num
          exact Batch0096.cell0772.sound htau (by
            simp only [Batch0096.cell0772, Batch0096.tau0772, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs200020 (by positivity) using 1 <;> norm_num)
        · have hs200022 : InSquare (-63/160) (7/160) (1/160) tau := by
            convert childUL hs20002 hx20002 hy20002 using 1 <;> norm_num
          exact Batch0096.cell0774.sound htau (by
            simp only [Batch0096.cell0774, Batch0096.tau0774, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs200022 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (3/80 : ℝ) with hy20002 | hy20002
        · have hs200021 : InSquare (-61/160) (1/32) (1/160) tau := by
            convert childLR hs20002 hx20002 hy20002 using 1 <;> norm_num
          exact Batch0096.cell0773.sound htau (by
            simp only [Batch0096.cell0773, Batch0096.tau0773, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs200021 (by positivity) using 1 <;> norm_num)
        · have hs200023 : InSquare (-61/160) (7/160) (1/160) tau := by
            convert childUR hs20002 hx20002 hy20002 using 1 <;> norm_num
          exact Batch0096.cell0775.sound htau (by
            simp only [Batch0096.cell0775, Batch0096.tau0775, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs200023 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (1/40 : ℝ) with hy2000 | hy2000
    · have hs20001 : InSquare (-29/80) (1/80) (1/80) tau := by
        convert childLR hs hx2000 hy2000 using 1 <;> norm_num
      exact Batch0024.cell0199.sound htau (by
        simp only [Batch0024.cell0199, Batch0024.tau0199, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs20001 (by positivity) using 1 <;> norm_num)
    · have hs20003 : InSquare (-29/80) (3/80) (1/80) tau := by
        convert childUR hs hx2000 hy2000 using 1 <;> norm_num
      exact Batch0025.cell0200.sound htau (by
        simp only [Batch0025.cell0200, Batch0025.tau0200, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs20003 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2000
