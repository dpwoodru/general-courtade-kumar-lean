import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0025
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0097
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0098

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2002

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-3/8) (3/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (-3/8 : ℝ) with hx2002 | hx2002
  · rcases le_total tau.im (3/40 : ℝ) with hy2002 | hy2002
    · have hs20020 : InSquare (-31/80) (1/16) (1/80) tau := by
        convert childLL hs hx2002 hy2002 using 1 <;> norm_num
      rcases le_total tau.re (-31/80 : ℝ) with hx20020 | hx20020
      · rcases le_total tau.im (1/16 : ℝ) with hy20020 | hy20020
        · have hs200200 : InSquare (-63/160) (9/160) (1/160) tau := by
            convert childLL hs20020 hx20020 hy20020 using 1 <;> norm_num
          exact Batch0097.cell0776.sound htau (by
            simp only [Batch0097.cell0776, Batch0097.tau0776, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs200200 (by positivity) using 1 <;> norm_num)
        · have hs200202 : InSquare (-63/160) (11/160) (1/160) tau := by
            convert childUL hs20020 hx20020 hy20020 using 1 <;> norm_num
          exact Batch0097.cell0778.sound htau (by
            simp only [Batch0097.cell0778, Batch0097.tau0778, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs200202 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (1/16 : ℝ) with hy20020 | hy20020
        · have hs200201 : InSquare (-61/160) (9/160) (1/160) tau := by
            convert childLR hs20020 hx20020 hy20020 using 1 <;> norm_num
          exact Batch0097.cell0777.sound htau (by
            simp only [Batch0097.cell0777, Batch0097.tau0777, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs200201 (by positivity) using 1 <;> norm_num)
        · have hs200203 : InSquare (-61/160) (11/160) (1/160) tau := by
            convert childUR hs20020 hx20020 hy20020 using 1 <;> norm_num
          exact Batch0097.cell0779.sound htau (by
            simp only [Batch0097.cell0779, Batch0097.tau0779, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs200203 (by positivity) using 1 <;> norm_num)
    · have hs20022 : InSquare (-31/80) (7/80) (1/80) tau := by
        convert childUL hs hx2002 hy2002 using 1 <;> norm_num
      rcases le_total tau.re (-31/80 : ℝ) with hx20022 | hx20022
      · rcases le_total tau.im (7/80 : ℝ) with hy20022 | hy20022
        · have hs200220 : InSquare (-63/160) (13/160) (1/160) tau := by
            convert childLL hs20022 hx20022 hy20022 using 1 <;> norm_num
          exact Batch0097.cell0780.sound htau (by
            simp only [Batch0097.cell0780, Batch0097.tau0780, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs200220 (by positivity) using 1 <;> norm_num)
        · have hs200222 : InSquare (-63/160) (3/32) (1/160) tau := by
            convert childUL hs20022 hx20022 hy20022 using 1 <;> norm_num
          exact Batch0097.cell0782.sound htau (by
            simp only [Batch0097.cell0782, Batch0097.tau0782, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs200222 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (7/80 : ℝ) with hy20022 | hy20022
        · have hs200221 : InSquare (-61/160) (13/160) (1/160) tau := by
            convert childLR hs20022 hx20022 hy20022 using 1 <;> norm_num
          exact Batch0097.cell0781.sound htau (by
            simp only [Batch0097.cell0781, Batch0097.tau0781, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs200221 (by positivity) using 1 <;> norm_num)
        · have hs200223 : InSquare (-61/160) (3/32) (1/160) tau := by
            convert childUR hs20022 hx20022 hy20022 using 1 <;> norm_num
          exact Batch0097.cell0783.sound htau (by
            simp only [Batch0097.cell0783, Batch0097.tau0783, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs200223 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (3/40 : ℝ) with hy2002 | hy2002
    · have hs20021 : InSquare (-29/80) (1/16) (1/80) tau := by
        convert childLR hs hx2002 hy2002 using 1 <;> norm_num
      exact Batch0025.cell0205.sound htau (by
        simp only [Batch0025.cell0205, Batch0025.tau0205, RatBall.Holds, GaussianRat.val]
        convert inBall_of_inSquare hs20021 (by positivity) using 1 <;> norm_num)
    · have hs20023 : InSquare (-29/80) (7/80) (1/80) tau := by
        convert childUR hs hx2002 hy2002 using 1 <;> norm_num
      rcases le_total tau.re (-29/80 : ℝ) with hx20023 | hx20023
      · rcases le_total tau.im (7/80 : ℝ) with hy20023 | hy20023
        · have hs200230 : InSquare (-59/160) (13/160) (1/160) tau := by
            convert childLL hs20023 hx20023 hy20023 using 1 <;> norm_num
          exact Batch0098.cell0784.sound htau (by
            simp only [Batch0098.cell0784, Batch0098.tau0784, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs200230 (by positivity) using 1 <;> norm_num)
        · have hs200232 : InSquare (-59/160) (3/32) (1/160) tau := by
            convert childUL hs20023 hx20023 hy20023 using 1 <;> norm_num
          exact Batch0098.cell0786.sound htau (by
            simp only [Batch0098.cell0786, Batch0098.tau0786, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs200232 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (7/80 : ℝ) with hy20023 | hy20023
        · have hs200231 : InSquare (-57/160) (13/160) (1/160) tau := by
            convert childLR hs20023 hx20023 hy20023 using 1 <;> norm_num
          exact Batch0098.cell0785.sound htau (by
            simp only [Batch0098.cell0785, Batch0098.tau0785, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs200231 (by positivity) using 1 <;> norm_num)
        · have hs200233 : InSquare (-57/160) (3/32) (1/160) tau := by
            convert childUR hs20023 hx20023 hy20023 using 1 <;> norm_num
          exact Batch0098.cell0787.sound htau (by
            simp only [Batch0098.cell0787, Batch0098.tau0787, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs200233 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2002
