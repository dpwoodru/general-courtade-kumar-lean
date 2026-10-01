import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0132
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0277

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3133

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

private theorem outside_31331 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (31/80) (13/80) (1/80) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (3/8 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-3/8)]
  have himSq : (3/20 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-3/20)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_31333 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (31/80) (3/16) (1/80) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (3/8 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-3/8)]
  have himSq : (7/40 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-7/40)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_313321 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (59/160) (29/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (29/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-29/80)]
  have himSq : (7/40 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-7/40)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_313323 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (59/160) (31/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (29/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-29/80)]
  have himSq : (3/16 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-3/16)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_3133221 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (23/64) (61/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (57/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-57/160)]
  have himSq : (3/16 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-3/16)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_3133222 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (113/320) (63/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (7/20 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-7/20)]
  have himSq : (31/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-31/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_3133223 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (23/64) (63/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (57/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-57/160)]
  have himSq : (31/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-31/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (3/8) (7/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (3/8 : ℝ) with hx3133 | hx3133
  · rcases le_total tau.im (7/40 : ℝ) with hy3133 | hy3133
    · have hs31330 : InSquare (29/80) (13/80) (1/80) tau := by
        convert childLL hs hx3133 hy3133 using 1 <;> norm_num
      rcases le_total tau.re (29/80 : ℝ) with hx31330 | hx31330
      · rcases le_total tau.im (13/80 : ℝ) with hy31330 | hy31330
        · have hs313300 : InSquare (57/160) (5/32) (1/160) tau := by
            convert childLL hs31330 hx31330 hy31330 using 1 <;> norm_num
          exact Batch0132.cell1058.sound htau (by
            simp only [Batch0132.cell1058, Batch0132.tau1058, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs313300 (by positivity) using 1 <;> norm_num)
        · have hs313302 : InSquare (57/160) (27/160) (1/160) tau := by
            convert childUL hs31330 hx31330 hy31330 using 1 <;> norm_num
          exact Batch0132.cell1060.sound htau (by
            simp only [Batch0132.cell1060, Batch0132.tau1060, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs313302 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (13/80 : ℝ) with hy31330 | hy31330
        · have hs313301 : InSquare (59/160) (5/32) (1/160) tau := by
            convert childLR hs31330 hx31330 hy31330 using 1 <;> norm_num
          exact Batch0132.cell1059.sound htau (by
            simp only [Batch0132.cell1059, Batch0132.tau1059, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs313301 (by positivity) using 1 <;> norm_num)
        · have hs313303 : InSquare (59/160) (27/160) (1/160) tau := by
            convert childUR hs31330 hx31330 hy31330 using 1 <;> norm_num
          exact Batch0132.cell1061.sound htau (by
            simp only [Batch0132.cell1061, Batch0132.tau1061, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs313303 (by positivity) using 1 <;> norm_num)
    · have hs31332 : InSquare (29/80) (3/16) (1/80) tau := by
        convert childUL hs hx3133 hy3133 using 1 <;> norm_num
      rcases le_total tau.re (29/80 : ℝ) with hx31332 | hx31332
      · rcases le_total tau.im (3/16 : ℝ) with hy31332 | hy31332
        · have hs313320 : InSquare (57/160) (29/160) (1/160) tau := by
            convert childLL hs31332 hx31332 hy31332 using 1 <;> norm_num
          exact Batch0132.cell1062.sound htau (by
            simp only [Batch0132.cell1062, Batch0132.tau1062, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs313320 (by positivity) using 1 <;> norm_num)
        · have hs313322 : InSquare (57/160) (31/160) (1/160) tau := by
            convert childUL hs31332 hx31332 hy31332 using 1 <;> norm_num
          rcases le_total tau.re (57/160 : ℝ) with hx313322 | hx313322
          · rcases le_total tau.im (31/160 : ℝ) with hy313322 | hy313322
            · have hs3133220 : InSquare (113/320) (61/320) (1/320) tau := by
                convert childLL hs313322 hx313322 hy313322 using 1 <;> norm_num
              exact Batch0277.cell2223.sound htau (by
                simp only [Batch0277.cell2223, Batch0277.tau2223, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3133220 (by positivity) using 1 <;> norm_num)
            · have hs3133222 : InSquare (113/320) (63/320) (1/320) tau := by
                convert childUL hs313322 hx313322 hy313322 using 1 <;> norm_num
              exact (outside_3133222 htau hs3133222).elim
          · rcases le_total tau.im (31/160 : ℝ) with hy313322 | hy313322
            · have hs3133221 : InSquare (23/64) (61/320) (1/320) tau := by
                convert childLR hs313322 hx313322 hy313322 using 1 <;> norm_num
              exact (outside_3133221 htau hs3133221).elim
            · have hs3133223 : InSquare (23/64) (63/320) (1/320) tau := by
                convert childUR hs313322 hx313322 hy313322 using 1 <;> norm_num
              exact (outside_3133223 htau hs3133223).elim
      · rcases le_total tau.im (3/16 : ℝ) with hy31332 | hy31332
        · have hs313321 : InSquare (59/160) (29/160) (1/160) tau := by
            convert childLR hs31332 hx31332 hy31332 using 1 <;> norm_num
          exact (outside_313321 htau hs313321).elim
        · have hs313323 : InSquare (59/160) (31/160) (1/160) tau := by
            convert childUR hs31332 hx31332 hy31332 using 1 <;> norm_num
          exact (outside_313323 htau hs313323).elim
  · rcases le_total tau.im (7/40 : ℝ) with hy3133 | hy3133
    · have hs31331 : InSquare (31/80) (13/80) (1/80) tau := by
        convert childLR hs hx3133 hy3133 using 1 <;> norm_num
      exact (outside_31331 htau hs31331).elim
    · have hs31333 : InSquare (31/80) (3/16) (1/80) tau := by
        convert childUR hs hx3133 hy3133 using 1 <;> norm_num
      exact (outside_31333 htau hs31333).elim

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3133
