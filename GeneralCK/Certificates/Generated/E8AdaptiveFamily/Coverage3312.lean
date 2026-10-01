import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0314

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3312

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

private theorem outside_33121 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (27/80) (21/80) (1/80) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (13/40 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-13/40)]
  have himSq : (1/4 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-1/4)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_33122 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (5/16) (23/80) (1/80) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (3/10 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-3/10)]
  have himSq : (11/40 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-11/40)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_33123 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (27/80) (23/80) (1/80) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (13/40 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-13/40)]
  have himSq : (11/40 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-11/40)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_331201 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (51/160) (41/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (5/16 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-5/16)]
  have himSq : (1/4 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-1/4)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_331203 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (51/160) (43/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (5/16 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-5/16)]
  have himSq : (21/80 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-21/80)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_3312021 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (99/320) (17/64) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (49/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-49/160)]
  have himSq : (21/80 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-21/80)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_3312022 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (97/320) (87/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (3/10 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-3/10)]
  have himSq : (43/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-43/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_3312023 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (99/320) (87/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (49/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-49/160)]
  have himSq : (43/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-43/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (13/40) (11/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (13/40 : ℝ) with hx3312 | hx3312
  · rcases le_total tau.im (11/40 : ℝ) with hy3312 | hy3312
    · have hs33120 : InSquare (5/16) (21/80) (1/80) tau := by
        convert childLL hs hx3312 hy3312 using 1 <;> norm_num
      rcases le_total tau.re (5/16 : ℝ) with hx33120 | hx33120
      · rcases le_total tau.im (21/80 : ℝ) with hy33120 | hy33120
        · have hs331200 : InSquare (49/160) (41/160) (1/160) tau := by
            convert childLL hs33120 hx33120 hy33120 using 1 <;> norm_num
          rcases le_total tau.re (49/160 : ℝ) with hx331200 | hx331200
          · rcases le_total tau.im (41/160 : ℝ) with hy331200 | hy331200
            · have hs3312000 : InSquare (97/320) (81/320) (1/320) tau := by
                convert childLL hs331200 hx331200 hy331200 using 1 <;> norm_num
              exact Batch0314.cell2515.sound htau (by
                simp only [Batch0314.cell2515, Batch0314.tau2515, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3312000 (by positivity) using 1 <;> norm_num)
            · have hs3312002 : InSquare (97/320) (83/320) (1/320) tau := by
                convert childUL hs331200 hx331200 hy331200 using 1 <;> norm_num
              exact Batch0314.cell2517.sound htau (by
                simp only [Batch0314.cell2517, Batch0314.tau2517, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3312002 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (41/160 : ℝ) with hy331200 | hy331200
            · have hs3312001 : InSquare (99/320) (81/320) (1/320) tau := by
                convert childLR hs331200 hx331200 hy331200 using 1 <;> norm_num
              exact Batch0314.cell2516.sound htau (by
                simp only [Batch0314.cell2516, Batch0314.tau2516, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3312001 (by positivity) using 1 <;> norm_num)
            · have hs3312003 : InSquare (99/320) (83/320) (1/320) tau := by
                convert childUR hs331200 hx331200 hy331200 using 1 <;> norm_num
              exact Batch0314.cell2518.sound htau (by
                simp only [Batch0314.cell2518, Batch0314.tau2518, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3312003 (by positivity) using 1 <;> norm_num)
        · have hs331202 : InSquare (49/160) (43/160) (1/160) tau := by
            convert childUL hs33120 hx33120 hy33120 using 1 <;> norm_num
          rcases le_total tau.re (49/160 : ℝ) with hx331202 | hx331202
          · rcases le_total tau.im (43/160 : ℝ) with hy331202 | hy331202
            · have hs3312020 : InSquare (97/320) (17/64) (1/320) tau := by
                convert childLL hs331202 hx331202 hy331202 using 1 <;> norm_num
              exact Batch0314.cell2519.sound htau (by
                simp only [Batch0314.cell2519, Batch0314.tau2519, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3312020 (by positivity) using 1 <;> norm_num)
            · have hs3312022 : InSquare (97/320) (87/320) (1/320) tau := by
                convert childUL hs331202 hx331202 hy331202 using 1 <;> norm_num
              exact (outside_3312022 htau hs3312022).elim
          · rcases le_total tau.im (43/160 : ℝ) with hy331202 | hy331202
            · have hs3312021 : InSquare (99/320) (17/64) (1/320) tau := by
                convert childLR hs331202 hx331202 hy331202 using 1 <;> norm_num
              exact (outside_3312021 htau hs3312021).elim
            · have hs3312023 : InSquare (99/320) (87/320) (1/320) tau := by
                convert childUR hs331202 hx331202 hy331202 using 1 <;> norm_num
              exact (outside_3312023 htau hs3312023).elim
      · rcases le_total tau.im (21/80 : ℝ) with hy33120 | hy33120
        · have hs331201 : InSquare (51/160) (41/160) (1/160) tau := by
            convert childLR hs33120 hx33120 hy33120 using 1 <;> norm_num
          exact (outside_331201 htau hs331201).elim
        · have hs331203 : InSquare (51/160) (43/160) (1/160) tau := by
            convert childUR hs33120 hx33120 hy33120 using 1 <;> norm_num
          exact (outside_331203 htau hs331203).elim
    · have hs33122 : InSquare (5/16) (23/80) (1/80) tau := by
        convert childUL hs hx3312 hy3312 using 1 <;> norm_num
      exact (outside_33122 htau hs33122).elim
  · rcases le_total tau.im (11/40 : ℝ) with hy3312 | hy3312
    · have hs33121 : InSquare (27/80) (21/80) (1/80) tau := by
        convert childLR hs hx3312 hy3312 using 1 <;> norm_num
      exact (outside_33121 htau hs33121).elim
    · have hs33123 : InSquare (27/80) (23/80) (1/80) tau := by
        convert childUR hs hx3312 hy3312 using 1 <;> norm_num
      exact (outside_33123 htau hs33123).elim

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3312
