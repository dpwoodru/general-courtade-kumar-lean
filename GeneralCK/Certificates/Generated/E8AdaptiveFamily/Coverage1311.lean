import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0090
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0091
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0235

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1311

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

private theorem outside_13111 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (31/80) (-3/16) (1/80) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (3/8 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-3/8)]
  have himSq : (7/40 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+7/40)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_13113 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (31/80) (-13/80) (1/80) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (3/8 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-3/8)]
  have himSq : (3/20 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+3/20)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_131101 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (59/160) (-31/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (29/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-29/80)]
  have himSq : (3/16 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+3/16)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_131103 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (59/160) (-29/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (29/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-29/80)]
  have himSq : (7/40 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+7/40)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_1311000 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (113/320) (-63/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (7/20 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-7/20)]
  have himSq : (31/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+31/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_1311001 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (23/64) (-63/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (57/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-57/160)]
  have himSq : (31/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+31/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_1311003 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (23/64) (-61/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (57/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-57/160)]
  have himSq : (3/16 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+3/16)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (3/8) (-7/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (3/8 : ℝ) with hx1311 | hx1311
  · rcases le_total tau.im (-7/40 : ℝ) with hy1311 | hy1311
    · have hs13110 : InSquare (29/80) (-3/16) (1/80) tau := by
        convert childLL hs hx1311 hy1311 using 1 <;> norm_num
      rcases le_total tau.re (29/80 : ℝ) with hx13110 | hx13110
      · rcases le_total tau.im (-3/16 : ℝ) with hy13110 | hy13110
        · have hs131100 : InSquare (57/160) (-31/160) (1/160) tau := by
            convert childLL hs13110 hx13110 hy13110 using 1 <;> norm_num
          rcases le_total tau.re (57/160 : ℝ) with hx131100 | hx131100
          · rcases le_total tau.im (-31/160 : ℝ) with hy131100 | hy131100
            · have hs1311000 : InSquare (113/320) (-63/320) (1/320) tau := by
                convert childLL hs131100 hx131100 hy131100 using 1 <;> norm_num
              exact (outside_1311000 htau hs1311000).elim
            · have hs1311002 : InSquare (113/320) (-61/320) (1/320) tau := by
                convert childUL hs131100 hx131100 hy131100 using 1 <;> norm_num
              exact Batch0235.cell1881.sound htau (by
                simp only [Batch0235.cell1881, Batch0235.tau1881, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1311002 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-31/160 : ℝ) with hy131100 | hy131100
            · have hs1311001 : InSquare (23/64) (-63/320) (1/320) tau := by
                convert childLR hs131100 hx131100 hy131100 using 1 <;> norm_num
              exact (outside_1311001 htau hs1311001).elim
            · have hs1311003 : InSquare (23/64) (-61/320) (1/320) tau := by
                convert childUR hs131100 hx131100 hy131100 using 1 <;> norm_num
              exact (outside_1311003 htau hs1311003).elim
        · have hs131102 : InSquare (57/160) (-29/160) (1/160) tau := by
            convert childUL hs13110 hx13110 hy13110 using 1 <;> norm_num
          exact Batch0090.cell0727.sound htau (by
            simp only [Batch0090.cell0727, Batch0090.tau0727, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs131102 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-3/16 : ℝ) with hy13110 | hy13110
        · have hs131101 : InSquare (59/160) (-31/160) (1/160) tau := by
            convert childLR hs13110 hx13110 hy13110 using 1 <;> norm_num
          exact (outside_131101 htau hs131101).elim
        · have hs131103 : InSquare (59/160) (-29/160) (1/160) tau := by
            convert childUR hs13110 hx13110 hy13110 using 1 <;> norm_num
          exact (outside_131103 htau hs131103).elim
    · have hs13112 : InSquare (29/80) (-13/80) (1/80) tau := by
        convert childUL hs hx1311 hy1311 using 1 <;> norm_num
      rcases le_total tau.re (29/80 : ℝ) with hx13112 | hx13112
      · rcases le_total tau.im (-13/80 : ℝ) with hy13112 | hy13112
        · have hs131120 : InSquare (57/160) (-27/160) (1/160) tau := by
            convert childLL hs13112 hx13112 hy13112 using 1 <;> norm_num
          exact Batch0091.cell0728.sound htau (by
            simp only [Batch0091.cell0728, Batch0091.tau0728, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs131120 (by positivity) using 1 <;> norm_num)
        · have hs131122 : InSquare (57/160) (-5/32) (1/160) tau := by
            convert childUL hs13112 hx13112 hy13112 using 1 <;> norm_num
          exact Batch0091.cell0730.sound htau (by
            simp only [Batch0091.cell0730, Batch0091.tau0730, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs131122 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-13/80 : ℝ) with hy13112 | hy13112
        · have hs131121 : InSquare (59/160) (-27/160) (1/160) tau := by
            convert childLR hs13112 hx13112 hy13112 using 1 <;> norm_num
          exact Batch0091.cell0729.sound htau (by
            simp only [Batch0091.cell0729, Batch0091.tau0729, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs131121 (by positivity) using 1 <;> norm_num)
        · have hs131123 : InSquare (59/160) (-5/32) (1/160) tau := by
            convert childUR hs13112 hx13112 hy13112 using 1 <;> norm_num
          exact Batch0091.cell0731.sound htau (by
            simp only [Batch0091.cell0731, Batch0091.tau0731, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs131123 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (-7/40 : ℝ) with hy1311 | hy1311
    · have hs13111 : InSquare (31/80) (-3/16) (1/80) tau := by
        convert childLR hs hx1311 hy1311 using 1 <;> norm_num
      exact (outside_13111 htau hs13111).elim
    · have hs13113 : InSquare (31/80) (-13/80) (1/80) tau := by
        convert childUR hs hx1311 hy1311 using 1 <;> norm_num
      exact (outside_13113 htau hs13113).elim

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1311
