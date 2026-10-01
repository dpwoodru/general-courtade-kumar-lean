import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0093
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0094

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1313

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

private theorem outside_131311 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (63/160) (-23/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (31/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-31/80)]
  have himSq : (11/80 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+11/80)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_131313 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (63/160) (-21/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (31/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-31/80)]
  have himSq : (1/8 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+1/8)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_131331 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (63/160) (-19/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (31/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-31/80)]
  have himSq : (9/80 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+9/80)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_131333 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (63/160) (-17/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (31/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-31/80)]
  have himSq : (1/10 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+1/10)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (3/8) (-1/8) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (3/8 : ℝ) with hx1313 | hx1313
  · rcases le_total tau.im (-1/8 : ℝ) with hy1313 | hy1313
    · have hs13130 : InSquare (29/80) (-11/80) (1/80) tau := by
        convert childLL hs hx1313 hy1313 using 1 <;> norm_num
      rcases le_total tau.re (29/80 : ℝ) with hx13130 | hx13130
      · rcases le_total tau.im (-11/80 : ℝ) with hy13130 | hy13130
        · have hs131300 : InSquare (57/160) (-23/160) (1/160) tau := by
            convert childLL hs13130 hx13130 hy13130 using 1 <;> norm_num
          exact Batch0093.cell0744.sound htau (by
            simp only [Batch0093.cell0744, Batch0093.tau0744, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs131300 (by positivity) using 1 <;> norm_num)
        · have hs131302 : InSquare (57/160) (-21/160) (1/160) tau := by
            convert childUL hs13130 hx13130 hy13130 using 1 <;> norm_num
          exact Batch0093.cell0746.sound htau (by
            simp only [Batch0093.cell0746, Batch0093.tau0746, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs131302 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-11/80 : ℝ) with hy13130 | hy13130
        · have hs131301 : InSquare (59/160) (-23/160) (1/160) tau := by
            convert childLR hs13130 hx13130 hy13130 using 1 <;> norm_num
          exact Batch0093.cell0745.sound htau (by
            simp only [Batch0093.cell0745, Batch0093.tau0745, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs131301 (by positivity) using 1 <;> norm_num)
        · have hs131303 : InSquare (59/160) (-21/160) (1/160) tau := by
            convert childUR hs13130 hx13130 hy13130 using 1 <;> norm_num
          exact Batch0093.cell0747.sound htau (by
            simp only [Batch0093.cell0747, Batch0093.tau0747, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs131303 (by positivity) using 1 <;> norm_num)
    · have hs13132 : InSquare (29/80) (-9/80) (1/80) tau := by
        convert childUL hs hx1313 hy1313 using 1 <;> norm_num
      rcases le_total tau.re (29/80 : ℝ) with hx13132 | hx13132
      · rcases le_total tau.im (-9/80 : ℝ) with hy13132 | hy13132
        · have hs131320 : InSquare (57/160) (-19/160) (1/160) tau := by
            convert childLL hs13132 hx13132 hy13132 using 1 <;> norm_num
          exact Batch0093.cell0750.sound htau (by
            simp only [Batch0093.cell0750, Batch0093.tau0750, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs131320 (by positivity) using 1 <;> norm_num)
        · have hs131322 : InSquare (57/160) (-17/160) (1/160) tau := by
            convert childUL hs13132 hx13132 hy13132 using 1 <;> norm_num
          exact Batch0094.cell0752.sound htau (by
            simp only [Batch0094.cell0752, Batch0094.tau0752, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs131322 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-9/80 : ℝ) with hy13132 | hy13132
        · have hs131321 : InSquare (59/160) (-19/160) (1/160) tau := by
            convert childLR hs13132 hx13132 hy13132 using 1 <;> norm_num
          exact Batch0093.cell0751.sound htau (by
            simp only [Batch0093.cell0751, Batch0093.tau0751, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs131321 (by positivity) using 1 <;> norm_num)
        · have hs131323 : InSquare (59/160) (-17/160) (1/160) tau := by
            convert childUR hs13132 hx13132 hy13132 using 1 <;> norm_num
          exact Batch0094.cell0753.sound htau (by
            simp only [Batch0094.cell0753, Batch0094.tau0753, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs131323 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (-1/8 : ℝ) with hy1313 | hy1313
    · have hs13131 : InSquare (31/80) (-11/80) (1/80) tau := by
        convert childLR hs hx1313 hy1313 using 1 <;> norm_num
      rcases le_total tau.re (31/80 : ℝ) with hx13131 | hx13131
      · rcases le_total tau.im (-11/80 : ℝ) with hy13131 | hy13131
        · have hs131310 : InSquare (61/160) (-23/160) (1/160) tau := by
            convert childLL hs13131 hx13131 hy13131 using 1 <;> norm_num
          exact Batch0093.cell0748.sound htau (by
            simp only [Batch0093.cell0748, Batch0093.tau0748, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs131310 (by positivity) using 1 <;> norm_num)
        · have hs131312 : InSquare (61/160) (-21/160) (1/160) tau := by
            convert childUL hs13131 hx13131 hy13131 using 1 <;> norm_num
          exact Batch0093.cell0749.sound htau (by
            simp only [Batch0093.cell0749, Batch0093.tau0749, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs131312 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-11/80 : ℝ) with hy13131 | hy13131
        · have hs131311 : InSquare (63/160) (-23/160) (1/160) tau := by
            convert childLR hs13131 hx13131 hy13131 using 1 <;> norm_num
          exact (outside_131311 htau hs131311).elim
        · have hs131313 : InSquare (63/160) (-21/160) (1/160) tau := by
            convert childUR hs13131 hx13131 hy13131 using 1 <;> norm_num
          exact (outside_131313 htau hs131313).elim
    · have hs13133 : InSquare (31/80) (-9/80) (1/80) tau := by
        convert childUR hs hx1313 hy1313 using 1 <;> norm_num
      rcases le_total tau.re (31/80 : ℝ) with hx13133 | hx13133
      · rcases le_total tau.im (-9/80 : ℝ) with hy13133 | hy13133
        · have hs131330 : InSquare (61/160) (-19/160) (1/160) tau := by
            convert childLL hs13133 hx13133 hy13133 using 1 <;> norm_num
          exact Batch0094.cell0754.sound htau (by
            simp only [Batch0094.cell0754, Batch0094.tau0754, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs131330 (by positivity) using 1 <;> norm_num)
        · have hs131332 : InSquare (61/160) (-17/160) (1/160) tau := by
            convert childUL hs13133 hx13133 hy13133 using 1 <;> norm_num
          exact Batch0094.cell0755.sound htau (by
            simp only [Batch0094.cell0755, Batch0094.tau0755, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs131332 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-9/80 : ℝ) with hy13133 | hy13133
        · have hs131331 : InSquare (63/160) (-19/160) (1/160) tau := by
            convert childLR hs13133 hx13133 hy13133 using 1 <;> norm_num
          exact (outside_131331 htau hs131331).elim
        · have hs131333 : InSquare (63/160) (-17/160) (1/160) tau := by
            convert childUR hs13133 hx13133 hy13133 using 1 <;> norm_num
          exact (outside_131333 htau hs131333).elim

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1313
