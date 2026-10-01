import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0027
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0100
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0101

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2021

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-13/40) (1/8) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (-13/40 : ℝ) with hx2021 | hx2021
  · rcases le_total tau.im (1/8 : ℝ) with hy2021 | hy2021
    · have hs20210 : InSquare (-27/80) (9/80) (1/80) tau := by
        convert childLL hs hx2021 hy2021 using 1 <;> norm_num
      rcases le_total tau.re (-27/80 : ℝ) with hx20210 | hx20210
      · rcases le_total tau.im (9/80 : ℝ) with hy20210 | hy20210
        · have hs202100 : InSquare (-11/32) (17/160) (1/160) tau := by
            convert childLL hs20210 hx20210 hy20210 using 1 <;> norm_num
          exact Batch0100.cell0800.sound htau (by
            simp only [Batch0100.cell0800, Batch0100.tau0800, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs202100 (by positivity) using 1 <;> norm_num)
        · have hs202102 : InSquare (-11/32) (19/160) (1/160) tau := by
            convert childUL hs20210 hx20210 hy20210 using 1 <;> norm_num
          exact Batch0100.cell0802.sound htau (by
            simp only [Batch0100.cell0802, Batch0100.tau0802, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs202102 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (9/80 : ℝ) with hy20210 | hy20210
        · have hs202101 : InSquare (-53/160) (17/160) (1/160) tau := by
            convert childLR hs20210 hx20210 hy20210 using 1 <;> norm_num
          exact Batch0100.cell0801.sound htau (by
            simp only [Batch0100.cell0801, Batch0100.tau0801, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs202101 (by positivity) using 1 <;> norm_num)
        · have hs202103 : InSquare (-53/160) (19/160) (1/160) tau := by
            convert childUR hs20210 hx20210 hy20210 using 1 <;> norm_num
          exact Batch0100.cell0803.sound htau (by
            simp only [Batch0100.cell0803, Batch0100.tau0803, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs202103 (by positivity) using 1 <;> norm_num)
    · have hs20212 : InSquare (-27/80) (11/80) (1/80) tau := by
        convert childUL hs hx2021 hy2021 using 1 <;> norm_num
      rcases le_total tau.re (-27/80 : ℝ) with hx20212 | hx20212
      · rcases le_total tau.im (11/80 : ℝ) with hy20212 | hy20212
        · have hs202120 : InSquare (-11/32) (21/160) (1/160) tau := by
            convert childLL hs20212 hx20212 hy20212 using 1 <;> norm_num
          exact Batch0100.cell0804.sound htau (by
            simp only [Batch0100.cell0804, Batch0100.tau0804, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs202120 (by positivity) using 1 <;> norm_num)
        · have hs202122 : InSquare (-11/32) (23/160) (1/160) tau := by
            convert childUL hs20212 hx20212 hy20212 using 1 <;> norm_num
          exact Batch0100.cell0806.sound htau (by
            simp only [Batch0100.cell0806, Batch0100.tau0806, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs202122 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (11/80 : ℝ) with hy20212 | hy20212
        · have hs202121 : InSquare (-53/160) (21/160) (1/160) tau := by
            convert childLR hs20212 hx20212 hy20212 using 1 <;> norm_num
          exact Batch0100.cell0805.sound htau (by
            simp only [Batch0100.cell0805, Batch0100.tau0805, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs202121 (by positivity) using 1 <;> norm_num)
        · have hs202123 : InSquare (-53/160) (23/160) (1/160) tau := by
            convert childUR hs20212 hx20212 hy20212 using 1 <;> norm_num
          exact Batch0100.cell0807.sound htau (by
            simp only [Batch0100.cell0807, Batch0100.tau0807, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs202123 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (1/8 : ℝ) with hy2021 | hy2021
    · have hs20211 : InSquare (-5/16) (9/80) (1/80) tau := by
        convert childLR hs hx2021 hy2021 using 1 <;> norm_num
      exact Batch0027.cell0222.sound htau (by
        simp only [Batch0027.cell0222, Batch0027.tau0222, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs20211 (by positivity) using 1 <;> norm_num)
    · have hs20213 : InSquare (-5/16) (11/80) (1/80) tau := by
        convert childUR hs hx2021 hy2021 using 1 <;> norm_num
      rcases le_total tau.re (-5/16 : ℝ) with hx20213 | hx20213
      · rcases le_total tau.im (11/80 : ℝ) with hy20213 | hy20213
        · have hs202130 : InSquare (-51/160) (21/160) (1/160) tau := by
            convert childLL hs20213 hx20213 hy20213 using 1 <;> norm_num
          exact Batch0101.cell0808.sound htau (by
            simp only [Batch0101.cell0808, Batch0101.tau0808, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs202130 (by positivity) using 1 <;> norm_num)
        · have hs202132 : InSquare (-51/160) (23/160) (1/160) tau := by
            convert childUL hs20213 hx20213 hy20213 using 1 <;> norm_num
          exact Batch0101.cell0810.sound htau (by
            simp only [Batch0101.cell0810, Batch0101.tau0810, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs202132 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (11/80 : ℝ) with hy20213 | hy20213
        · have hs202131 : InSquare (-49/160) (21/160) (1/160) tau := by
            convert childLR hs20213 hx20213 hy20213 using 1 <;> norm_num
          exact Batch0101.cell0809.sound htau (by
            simp only [Batch0101.cell0809, Batch0101.tau0809, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs202131 (by positivity) using 1 <;> norm_num)
        · have hs202133 : InSquare (-49/160) (23/160) (1/160) tau := by
            convert childUR hs20213 hx20213 hy20213 using 1 <;> norm_num
          exact Batch0101.cell0811.sound htau (by
            simp only [Batch0101.cell0811, Batch0101.tau0811, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs202133 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2021
