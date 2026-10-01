import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0136
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0137
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0138

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3213

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (7/40) (11/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (7/40 : ℝ) with hx3213 | hx3213
  · rcases le_total tau.im (11/40 : ℝ) with hy3213 | hy3213
    · have hs32130 : InSquare (13/80) (21/80) (1/80) tau := by
        convert childLL hs hx3213 hy3213 using 1 <;> norm_num
      rcases le_total tau.re (13/80 : ℝ) with hx32130 | hx32130
      · rcases le_total tau.im (21/80 : ℝ) with hy32130 | hy32130
        · have hs321300 : InSquare (5/32) (41/160) (1/160) tau := by
            convert childLL hs32130 hx32130 hy32130 using 1 <;> norm_num
          exact Batch0136.cell1095.sound htau (by
            simp only [Batch0136.cell1095, Batch0136.tau1095, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs321300 (by positivity) using 1 <;> norm_num)
        · have hs321302 : InSquare (5/32) (43/160) (1/160) tau := by
            convert childUL hs32130 hx32130 hy32130 using 1 <;> norm_num
          exact Batch0137.cell1097.sound htau (by
            simp only [Batch0137.cell1097, Batch0137.tau1097, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs321302 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (21/80 : ℝ) with hy32130 | hy32130
        · have hs321301 : InSquare (27/160) (41/160) (1/160) tau := by
            convert childLR hs32130 hx32130 hy32130 using 1 <;> norm_num
          exact Batch0137.cell1096.sound htau (by
            simp only [Batch0137.cell1096, Batch0137.tau1096, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs321301 (by positivity) using 1 <;> norm_num)
        · have hs321303 : InSquare (27/160) (43/160) (1/160) tau := by
            convert childUR hs32130 hx32130 hy32130 using 1 <;> norm_num
          exact Batch0137.cell1098.sound htau (by
            simp only [Batch0137.cell1098, Batch0137.tau1098, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs321303 (by positivity) using 1 <;> norm_num)
    · have hs32132 : InSquare (13/80) (23/80) (1/80) tau := by
        convert childUL hs hx3213 hy3213 using 1 <;> norm_num
      rcases le_total tau.re (13/80 : ℝ) with hx32132 | hx32132
      · rcases le_total tau.im (23/80 : ℝ) with hy32132 | hy32132
        · have hs321320 : InSquare (5/32) (9/32) (1/160) tau := by
            convert childLL hs32132 hx32132 hy32132 using 1 <;> norm_num
          exact Batch0137.cell1103.sound htau (by
            simp only [Batch0137.cell1103, Batch0137.tau1103, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs321320 (by positivity) using 1 <;> norm_num)
        · have hs321322 : InSquare (5/32) (47/160) (1/160) tau := by
            convert childUL hs32132 hx32132 hy32132 using 1 <;> norm_num
          exact Batch0138.cell1105.sound htau (by
            simp only [Batch0138.cell1105, Batch0138.tau1105, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs321322 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (23/80 : ℝ) with hy32132 | hy32132
        · have hs321321 : InSquare (27/160) (9/32) (1/160) tau := by
            convert childLR hs32132 hx32132 hy32132 using 1 <;> norm_num
          exact Batch0138.cell1104.sound htau (by
            simp only [Batch0138.cell1104, Batch0138.tau1104, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs321321 (by positivity) using 1 <;> norm_num)
        · have hs321323 : InSquare (27/160) (47/160) (1/160) tau := by
            convert childUR hs32132 hx32132 hy32132 using 1 <;> norm_num
          exact Batch0138.cell1106.sound htau (by
            simp only [Batch0138.cell1106, Batch0138.tau1106, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs321323 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (11/40 : ℝ) with hy3213 | hy3213
    · have hs32131 : InSquare (3/16) (21/80) (1/80) tau := by
        convert childLR hs hx3213 hy3213 using 1 <;> norm_num
      rcases le_total tau.re (3/16 : ℝ) with hx32131 | hx32131
      · rcases le_total tau.im (21/80 : ℝ) with hy32131 | hy32131
        · have hs321310 : InSquare (29/160) (41/160) (1/160) tau := by
            convert childLL hs32131 hx32131 hy32131 using 1 <;> norm_num
          exact Batch0137.cell1099.sound htau (by
            simp only [Batch0137.cell1099, Batch0137.tau1099, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs321310 (by positivity) using 1 <;> norm_num)
        · have hs321312 : InSquare (29/160) (43/160) (1/160) tau := by
            convert childUL hs32131 hx32131 hy32131 using 1 <;> norm_num
          exact Batch0137.cell1101.sound htau (by
            simp only [Batch0137.cell1101, Batch0137.tau1101, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs321312 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (21/80 : ℝ) with hy32131 | hy32131
        · have hs321311 : InSquare (31/160) (41/160) (1/160) tau := by
            convert childLR hs32131 hx32131 hy32131 using 1 <;> norm_num
          exact Batch0137.cell1100.sound htau (by
            simp only [Batch0137.cell1100, Batch0137.tau1100, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs321311 (by positivity) using 1 <;> norm_num)
        · have hs321313 : InSquare (31/160) (43/160) (1/160) tau := by
            convert childUR hs32131 hx32131 hy32131 using 1 <;> norm_num
          exact Batch0137.cell1102.sound htau (by
            simp only [Batch0137.cell1102, Batch0137.tau1102, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs321313 (by positivity) using 1 <;> norm_num)
    · have hs32133 : InSquare (3/16) (23/80) (1/80) tau := by
        convert childUR hs hx3213 hy3213 using 1 <;> norm_num
      rcases le_total tau.re (3/16 : ℝ) with hx32133 | hx32133
      · rcases le_total tau.im (23/80 : ℝ) with hy32133 | hy32133
        · have hs321330 : InSquare (29/160) (9/32) (1/160) tau := by
            convert childLL hs32133 hx32133 hy32133 using 1 <;> norm_num
          exact Batch0138.cell1107.sound htau (by
            simp only [Batch0138.cell1107, Batch0138.tau1107, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs321330 (by positivity) using 1 <;> norm_num)
        · have hs321332 : InSquare (29/160) (47/160) (1/160) tau := by
            convert childUL hs32133 hx32133 hy32133 using 1 <;> norm_num
          exact Batch0138.cell1109.sound htau (by
            simp only [Batch0138.cell1109, Batch0138.tau1109, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs321332 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (23/80 : ℝ) with hy32133 | hy32133
        · have hs321331 : InSquare (31/160) (9/32) (1/160) tau := by
            convert childLR hs32133 hx32133 hy32133 using 1 <;> norm_num
          exact Batch0138.cell1108.sound htau (by
            simp only [Batch0138.cell1108, Batch0138.tau1108, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs321331 (by positivity) using 1 <;> norm_num)
        · have hs321333 : InSquare (31/160) (47/160) (1/160) tau := by
            convert childUR hs32133 hx32133 hy32133 using 1 <;> norm_num
          exact Batch0138.cell1110.sound htau (by
            simp only [Batch0138.cell1110, Batch0138.tau1110, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs321333 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3213
