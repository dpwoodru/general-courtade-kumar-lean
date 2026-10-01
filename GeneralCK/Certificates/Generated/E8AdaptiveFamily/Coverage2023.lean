import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0102
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0103
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0104

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2023

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-13/40) (7/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (-13/40 : ℝ) with hx2023 | hx2023
  · rcases le_total tau.im (7/40 : ℝ) with hy2023 | hy2023
    · have hs20230 : InSquare (-27/80) (13/80) (1/80) tau := by
        convert childLL hs hx2023 hy2023 using 1 <;> norm_num
      rcases le_total tau.re (-27/80 : ℝ) with hx20230 | hx20230
      · rcases le_total tau.im (13/80 : ℝ) with hy20230 | hy20230
        · have hs202300 : InSquare (-11/32) (5/32) (1/160) tau := by
            convert childLL hs20230 hx20230 hy20230 using 1 <;> norm_num
          exact Batch0102.cell0817.sound htau (by
            simp only [Batch0102.cell0817, Batch0102.tau0817, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs202300 (by positivity) using 1 <;> norm_num)
        · have hs202302 : InSquare (-11/32) (27/160) (1/160) tau := by
            convert childUL hs20230 hx20230 hy20230 using 1 <;> norm_num
          exact Batch0102.cell0819.sound htau (by
            simp only [Batch0102.cell0819, Batch0102.tau0819, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs202302 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (13/80 : ℝ) with hy20230 | hy20230
        · have hs202301 : InSquare (-53/160) (5/32) (1/160) tau := by
            convert childLR hs20230 hx20230 hy20230 using 1 <;> norm_num
          exact Batch0102.cell0818.sound htau (by
            simp only [Batch0102.cell0818, Batch0102.tau0818, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs202301 (by positivity) using 1 <;> norm_num)
        · have hs202303 : InSquare (-53/160) (27/160) (1/160) tau := by
            convert childUR hs20230 hx20230 hy20230 using 1 <;> norm_num
          exact Batch0102.cell0820.sound htau (by
            simp only [Batch0102.cell0820, Batch0102.tau0820, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs202303 (by positivity) using 1 <;> norm_num)
    · have hs20232 : InSquare (-27/80) (3/16) (1/80) tau := by
        convert childUL hs hx2023 hy2023 using 1 <;> norm_num
      rcases le_total tau.re (-27/80 : ℝ) with hx20232 | hx20232
      · rcases le_total tau.im (3/16 : ℝ) with hy20232 | hy20232
        · have hs202320 : InSquare (-11/32) (29/160) (1/160) tau := by
            convert childLL hs20232 hx20232 hy20232 using 1 <;> norm_num
          exact Batch0103.cell0825.sound htau (by
            simp only [Batch0103.cell0825, Batch0103.tau0825, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs202320 (by positivity) using 1 <;> norm_num)
        · have hs202322 : InSquare (-11/32) (31/160) (1/160) tau := by
            convert childUL hs20232 hx20232 hy20232 using 1 <;> norm_num
          exact Batch0103.cell0827.sound htau (by
            simp only [Batch0103.cell0827, Batch0103.tau0827, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs202322 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (3/16 : ℝ) with hy20232 | hy20232
        · have hs202321 : InSquare (-53/160) (29/160) (1/160) tau := by
            convert childLR hs20232 hx20232 hy20232 using 1 <;> norm_num
          exact Batch0103.cell0826.sound htau (by
            simp only [Batch0103.cell0826, Batch0103.tau0826, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs202321 (by positivity) using 1 <;> norm_num)
        · have hs202323 : InSquare (-53/160) (31/160) (1/160) tau := by
            convert childUR hs20232 hx20232 hy20232 using 1 <;> norm_num
          exact Batch0103.cell0828.sound htau (by
            simp only [Batch0103.cell0828, Batch0103.tau0828, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs202323 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (7/40 : ℝ) with hy2023 | hy2023
    · have hs20231 : InSquare (-5/16) (13/80) (1/80) tau := by
        convert childLR hs hx2023 hy2023 using 1 <;> norm_num
      rcases le_total tau.re (-5/16 : ℝ) with hx20231 | hx20231
      · rcases le_total tau.im (13/80 : ℝ) with hy20231 | hy20231
        · have hs202310 : InSquare (-51/160) (5/32) (1/160) tau := by
            convert childLL hs20231 hx20231 hy20231 using 1 <;> norm_num
          exact Batch0102.cell0821.sound htau (by
            simp only [Batch0102.cell0821, Batch0102.tau0821, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs202310 (by positivity) using 1 <;> norm_num)
        · have hs202312 : InSquare (-51/160) (27/160) (1/160) tau := by
            convert childUL hs20231 hx20231 hy20231 using 1 <;> norm_num
          exact Batch0102.cell0823.sound htau (by
            simp only [Batch0102.cell0823, Batch0102.tau0823, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs202312 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (13/80 : ℝ) with hy20231 | hy20231
        · have hs202311 : InSquare (-49/160) (5/32) (1/160) tau := by
            convert childLR hs20231 hx20231 hy20231 using 1 <;> norm_num
          exact Batch0102.cell0822.sound htau (by
            simp only [Batch0102.cell0822, Batch0102.tau0822, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs202311 (by positivity) using 1 <;> norm_num)
        · have hs202313 : InSquare (-49/160) (27/160) (1/160) tau := by
            convert childUR hs20231 hx20231 hy20231 using 1 <;> norm_num
          exact Batch0103.cell0824.sound htau (by
            simp only [Batch0103.cell0824, Batch0103.tau0824, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs202313 (by positivity) using 1 <;> norm_num)
    · have hs20233 : InSquare (-5/16) (3/16) (1/80) tau := by
        convert childUR hs hx2023 hy2023 using 1 <;> norm_num
      rcases le_total tau.re (-5/16 : ℝ) with hx20233 | hx20233
      · rcases le_total tau.im (3/16 : ℝ) with hy20233 | hy20233
        · have hs202330 : InSquare (-51/160) (29/160) (1/160) tau := by
            convert childLL hs20233 hx20233 hy20233 using 1 <;> norm_num
          exact Batch0103.cell0829.sound htau (by
            simp only [Batch0103.cell0829, Batch0103.tau0829, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs202330 (by positivity) using 1 <;> norm_num)
        · have hs202332 : InSquare (-51/160) (31/160) (1/160) tau := by
            convert childUL hs20233 hx20233 hy20233 using 1 <;> norm_num
          exact Batch0103.cell0831.sound htau (by
            simp only [Batch0103.cell0831, Batch0103.tau0831, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs202332 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (3/16 : ℝ) with hy20233 | hy20233
        · have hs202331 : InSquare (-49/160) (29/160) (1/160) tau := by
            convert childLR hs20233 hx20233 hy20233 using 1 <;> norm_num
          exact Batch0103.cell0830.sound htau (by
            simp only [Batch0103.cell0830, Batch0103.tau0830, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs202331 (by positivity) using 1 <;> norm_num)
        · have hs202333 : InSquare (-49/160) (31/160) (1/160) tau := by
            convert childUR hs20233 hx20233 hy20233 using 1 <;> norm_num
          exact Batch0104.cell0832.sound htau (by
            simp only [Batch0104.cell0832, Batch0104.tau0832, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs202333 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2023
