import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0028
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0104
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0105

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2032

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-11/40) (7/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (-11/40 : ℝ) with hx2032 | hx2032
  · rcases le_total tau.im (7/40 : ℝ) with hy2032 | hy2032
    · have hs20320 : InSquare (-23/80) (13/80) (1/80) tau := by
        convert childLL hs hx2032 hy2032 using 1 <;> norm_num
      rcases le_total tau.re (-23/80 : ℝ) with hx20320 | hx20320
      · rcases le_total tau.im (13/80 : ℝ) with hy20320 | hy20320
        · have hs203200 : InSquare (-47/160) (5/32) (1/160) tau := by
            convert childLL hs20320 hx20320 hy20320 using 1 <;> norm_num
          exact Batch0104.cell0833.sound htau (by
            simp only [Batch0104.cell0833, Batch0104.tau0833, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs203200 (by positivity) using 1 <;> norm_num)
        · have hs203202 : InSquare (-47/160) (27/160) (1/160) tau := by
            convert childUL hs20320 hx20320 hy20320 using 1 <;> norm_num
          exact Batch0104.cell0835.sound htau (by
            simp only [Batch0104.cell0835, Batch0104.tau0835, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs203202 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (13/80 : ℝ) with hy20320 | hy20320
        · have hs203201 : InSquare (-9/32) (5/32) (1/160) tau := by
            convert childLR hs20320 hx20320 hy20320 using 1 <;> norm_num
          exact Batch0104.cell0834.sound htau (by
            simp only [Batch0104.cell0834, Batch0104.tau0834, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs203201 (by positivity) using 1 <;> norm_num)
        · have hs203203 : InSquare (-9/32) (27/160) (1/160) tau := by
            convert childUR hs20320 hx20320 hy20320 using 1 <;> norm_num
          exact Batch0104.cell0836.sound htau (by
            simp only [Batch0104.cell0836, Batch0104.tau0836, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs203203 (by positivity) using 1 <;> norm_num)
    · have hs20322 : InSquare (-23/80) (3/16) (1/80) tau := by
        convert childUL hs hx2032 hy2032 using 1 <;> norm_num
      rcases le_total tau.re (-23/80 : ℝ) with hx20322 | hx20322
      · rcases le_total tau.im (3/16 : ℝ) with hy20322 | hy20322
        · have hs203220 : InSquare (-47/160) (29/160) (1/160) tau := by
            convert childLL hs20322 hx20322 hy20322 using 1 <;> norm_num
          exact Batch0104.cell0837.sound htau (by
            simp only [Batch0104.cell0837, Batch0104.tau0837, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs203220 (by positivity) using 1 <;> norm_num)
        · have hs203222 : InSquare (-47/160) (31/160) (1/160) tau := by
            convert childUL hs20322 hx20322 hy20322 using 1 <;> norm_num
          exact Batch0104.cell0839.sound htau (by
            simp only [Batch0104.cell0839, Batch0104.tau0839, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs203222 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (3/16 : ℝ) with hy20322 | hy20322
        · have hs203221 : InSquare (-9/32) (29/160) (1/160) tau := by
            convert childLR hs20322 hx20322 hy20322 using 1 <;> norm_num
          exact Batch0104.cell0838.sound htau (by
            simp only [Batch0104.cell0838, Batch0104.tau0838, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs203221 (by positivity) using 1 <;> norm_num)
        · have hs203223 : InSquare (-9/32) (31/160) (1/160) tau := by
            convert childUR hs20322 hx20322 hy20322 using 1 <;> norm_num
          exact Batch0105.cell0840.sound htau (by
            simp only [Batch0105.cell0840, Batch0105.tau0840, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs203223 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (7/40 : ℝ) with hy2032 | hy2032
    · have hs20321 : InSquare (-21/80) (13/80) (1/80) tau := by
        convert childLR hs hx2032 hy2032 using 1 <;> norm_num
      exact Batch0028.cell0231.sound htau (by
        simp only [Batch0028.cell0231, Batch0028.tau0231, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs20321 (by positivity) using 1 <;> norm_num)
    · have hs20323 : InSquare (-21/80) (3/16) (1/80) tau := by
        convert childUR hs hx2032 hy2032 using 1 <;> norm_num
      rcases le_total tau.re (-21/80 : ℝ) with hx20323 | hx20323
      · rcases le_total tau.im (3/16 : ℝ) with hy20323 | hy20323
        · have hs203230 : InSquare (-43/160) (29/160) (1/160) tau := by
            convert childLL hs20323 hx20323 hy20323 using 1 <;> norm_num
          exact Batch0105.cell0841.sound htau (by
            simp only [Batch0105.cell0841, Batch0105.tau0841, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs203230 (by positivity) using 1 <;> norm_num)
        · have hs203232 : InSquare (-43/160) (31/160) (1/160) tau := by
            convert childUL hs20323 hx20323 hy20323 using 1 <;> norm_num
          exact Batch0105.cell0843.sound htau (by
            simp only [Batch0105.cell0843, Batch0105.tau0843, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs203232 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (3/16 : ℝ) with hy20323 | hy20323
        · have hs203231 : InSquare (-41/160) (29/160) (1/160) tau := by
            convert childLR hs20323 hx20323 hy20323 using 1 <;> norm_num
          exact Batch0105.cell0842.sound htau (by
            simp only [Batch0105.cell0842, Batch0105.tau0842, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs203231 (by positivity) using 1 <;> norm_num)
        · have hs203233 : InSquare (-41/160) (31/160) (1/160) tau := by
            convert childUR hs20323 hx20323 hy20323 using 1 <;> norm_num
          exact Batch0105.cell0844.sound htau (by
            simp only [Batch0105.cell0844, Batch0105.tau0844, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs203233 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2032
