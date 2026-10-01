import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0108
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0109
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0110

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2211

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-9/40) (9/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (-9/40 : ℝ) with hx2211 | hx2211
  · rcases le_total tau.im (9/40 : ℝ) with hy2211 | hy2211
    · have hs22110 : InSquare (-19/80) (17/80) (1/80) tau := by
        convert childLL hs hx2211 hy2211 using 1 <;> norm_num
      rcases le_total tau.re (-19/80 : ℝ) with hx22110 | hx22110
      · rcases le_total tau.im (17/80 : ℝ) with hy22110 | hy22110
        · have hs221100 : InSquare (-39/160) (33/160) (1/160) tau := by
            convert childLL hs22110 hx22110 hy22110 using 1 <;> norm_num
          exact Batch0108.cell0870.sound htau (by
            simp only [Batch0108.cell0870, Batch0108.tau0870, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs221100 (by positivity) using 1 <;> norm_num)
        · have hs221102 : InSquare (-39/160) (7/32) (1/160) tau := by
            convert childUL hs22110 hx22110 hy22110 using 1 <;> norm_num
          exact Batch0109.cell0872.sound htau (by
            simp only [Batch0109.cell0872, Batch0109.tau0872, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs221102 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (17/80 : ℝ) with hy22110 | hy22110
        · have hs221101 : InSquare (-37/160) (33/160) (1/160) tau := by
            convert childLR hs22110 hx22110 hy22110 using 1 <;> norm_num
          exact Batch0108.cell0871.sound htau (by
            simp only [Batch0108.cell0871, Batch0108.tau0871, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs221101 (by positivity) using 1 <;> norm_num)
        · have hs221103 : InSquare (-37/160) (7/32) (1/160) tau := by
            convert childUR hs22110 hx22110 hy22110 using 1 <;> norm_num
          exact Batch0109.cell0873.sound htau (by
            simp only [Batch0109.cell0873, Batch0109.tau0873, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs221103 (by positivity) using 1 <;> norm_num)
    · have hs22112 : InSquare (-19/80) (19/80) (1/80) tau := by
        convert childUL hs hx2211 hy2211 using 1 <;> norm_num
      rcases le_total tau.re (-19/80 : ℝ) with hx22112 | hx22112
      · rcases le_total tau.im (19/80 : ℝ) with hy22112 | hy22112
        · have hs221120 : InSquare (-39/160) (37/160) (1/160) tau := by
            convert childLL hs22112 hx22112 hy22112 using 1 <;> norm_num
          exact Batch0109.cell0878.sound htau (by
            simp only [Batch0109.cell0878, Batch0109.tau0878, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs221120 (by positivity) using 1 <;> norm_num)
        · have hs221122 : InSquare (-39/160) (39/160) (1/160) tau := by
            convert childUL hs22112 hx22112 hy22112 using 1 <;> norm_num
          exact Batch0110.cell0880.sound htau (by
            simp only [Batch0110.cell0880, Batch0110.tau0880, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs221122 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (19/80 : ℝ) with hy22112 | hy22112
        · have hs221121 : InSquare (-37/160) (37/160) (1/160) tau := by
            convert childLR hs22112 hx22112 hy22112 using 1 <;> norm_num
          exact Batch0109.cell0879.sound htau (by
            simp only [Batch0109.cell0879, Batch0109.tau0879, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs221121 (by positivity) using 1 <;> norm_num)
        · have hs221123 : InSquare (-37/160) (39/160) (1/160) tau := by
            convert childUR hs22112 hx22112 hy22112 using 1 <;> norm_num
          exact Batch0110.cell0881.sound htau (by
            simp only [Batch0110.cell0881, Batch0110.tau0881, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs221123 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (9/40 : ℝ) with hy2211 | hy2211
    · have hs22111 : InSquare (-17/80) (17/80) (1/80) tau := by
        convert childLR hs hx2211 hy2211 using 1 <;> norm_num
      rcases le_total tau.re (-17/80 : ℝ) with hx22111 | hx22111
      · rcases le_total tau.im (17/80 : ℝ) with hy22111 | hy22111
        · have hs221110 : InSquare (-7/32) (33/160) (1/160) tau := by
            convert childLL hs22111 hx22111 hy22111 using 1 <;> norm_num
          exact Batch0109.cell0874.sound htau (by
            simp only [Batch0109.cell0874, Batch0109.tau0874, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs221110 (by positivity) using 1 <;> norm_num)
        · have hs221112 : InSquare (-7/32) (7/32) (1/160) tau := by
            convert childUL hs22111 hx22111 hy22111 using 1 <;> norm_num
          exact Batch0109.cell0876.sound htau (by
            simp only [Batch0109.cell0876, Batch0109.tau0876, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs221112 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (17/80 : ℝ) with hy22111 | hy22111
        · have hs221111 : InSquare (-33/160) (33/160) (1/160) tau := by
            convert childLR hs22111 hx22111 hy22111 using 1 <;> norm_num
          exact Batch0109.cell0875.sound htau (by
            simp only [Batch0109.cell0875, Batch0109.tau0875, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs221111 (by positivity) using 1 <;> norm_num)
        · have hs221113 : InSquare (-33/160) (7/32) (1/160) tau := by
            convert childUR hs22111 hx22111 hy22111 using 1 <;> norm_num
          exact Batch0109.cell0877.sound htau (by
            simp only [Batch0109.cell0877, Batch0109.tau0877, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs221113 (by positivity) using 1 <;> norm_num)
    · have hs22113 : InSquare (-17/80) (19/80) (1/80) tau := by
        convert childUR hs hx2211 hy2211 using 1 <;> norm_num
      rcases le_total tau.re (-17/80 : ℝ) with hx22113 | hx22113
      · rcases le_total tau.im (19/80 : ℝ) with hy22113 | hy22113
        · have hs221130 : InSquare (-7/32) (37/160) (1/160) tau := by
            convert childLL hs22113 hx22113 hy22113 using 1 <;> norm_num
          exact Batch0110.cell0882.sound htau (by
            simp only [Batch0110.cell0882, Batch0110.tau0882, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs221130 (by positivity) using 1 <;> norm_num)
        · have hs221132 : InSquare (-7/32) (39/160) (1/160) tau := by
            convert childUL hs22113 hx22113 hy22113 using 1 <;> norm_num
          exact Batch0110.cell0884.sound htau (by
            simp only [Batch0110.cell0884, Batch0110.tau0884, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs221132 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (19/80 : ℝ) with hy22113 | hy22113
        · have hs221131 : InSquare (-33/160) (37/160) (1/160) tau := by
            convert childLR hs22113 hx22113 hy22113 using 1 <;> norm_num
          exact Batch0110.cell0883.sound htau (by
            simp only [Batch0110.cell0883, Batch0110.tau0883, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs221131 (by positivity) using 1 <;> norm_num)
        · have hs221133 : InSquare (-33/160) (39/160) (1/160) tau := by
            convert childUR hs22113 hx22113 hy22113 using 1 <;> norm_num
          exact Batch0110.cell0885.sound htau (by
            simp only [Batch0110.cell0885, Batch0110.tau0885, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs221133 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2211
