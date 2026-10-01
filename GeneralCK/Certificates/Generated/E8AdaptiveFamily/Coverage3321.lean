import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0319
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0320

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3321

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

private theorem outside_33211 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (23/80) (5/16) (1/80) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (11/40 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-11/40)]
  have himSq : (3/10 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-3/10)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_33212 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (21/80) (27/80) (1/80) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (1/4 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-1/4)]
  have himSq : (13/40 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-13/40)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_33213 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (23/80) (27/80) (1/80) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (11/40 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-11/40)]
  have himSq : (13/40 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-13/40)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_332102 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (41/160) (51/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (1/4 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-1/4)]
  have himSq : (5/16 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-5/16)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_332103 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (43/160) (51/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (21/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-21/80)]
  have himSq : (5/16 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-5/16)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_3321011 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (87/320) (97/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (43/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-43/160)]
  have himSq : (3/10 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-3/10)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_3321012 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (17/64) (99/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (21/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-21/80)]
  have himSq : (49/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-49/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_3321013 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (87/320) (99/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (43/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-43/160)]
  have himSq : (49/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-49/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (11/40) (13/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (11/40 : ℝ) with hx3321 | hx3321
  · rcases le_total tau.im (13/40 : ℝ) with hy3321 | hy3321
    · have hs33210 : InSquare (21/80) (5/16) (1/80) tau := by
        convert childLL hs hx3321 hy3321 using 1 <;> norm_num
      rcases le_total tau.re (21/80 : ℝ) with hx33210 | hx33210
      · rcases le_total tau.im (5/16 : ℝ) with hy33210 | hy33210
        · have hs332100 : InSquare (41/160) (49/160) (1/160) tau := by
            convert childLL hs33210 hx33210 hy33210 using 1 <;> norm_num
          rcases le_total tau.re (41/160 : ℝ) with hx332100 | hx332100
          · rcases le_total tau.im (49/160 : ℝ) with hy332100 | hy332100
            · have hs3321000 : InSquare (81/320) (97/320) (1/320) tau := by
                convert childLL hs332100 hx332100 hy332100 using 1 <;> norm_num
              exact Batch0319.cell2559.sound htau (by
                simp only [Batch0319.cell2559, Batch0319.tau2559, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3321000 (by positivity) using 1 <;> norm_num)
            · have hs3321002 : InSquare (81/320) (99/320) (1/320) tau := by
                convert childUL hs332100 hx332100 hy332100 using 1 <;> norm_num
              exact Batch0320.cell2561.sound htau (by
                simp only [Batch0320.cell2561, Batch0320.tau2561, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3321002 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (49/160 : ℝ) with hy332100 | hy332100
            · have hs3321001 : InSquare (83/320) (97/320) (1/320) tau := by
                convert childLR hs332100 hx332100 hy332100 using 1 <;> norm_num
              exact Batch0320.cell2560.sound htau (by
                simp only [Batch0320.cell2560, Batch0320.tau2560, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3321001 (by positivity) using 1 <;> norm_num)
            · have hs3321003 : InSquare (83/320) (99/320) (1/320) tau := by
                convert childUR hs332100 hx332100 hy332100 using 1 <;> norm_num
              exact Batch0320.cell2562.sound htau (by
                simp only [Batch0320.cell2562, Batch0320.tau2562, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3321003 (by positivity) using 1 <;> norm_num)
        · have hs332102 : InSquare (41/160) (51/160) (1/160) tau := by
            convert childUL hs33210 hx33210 hy33210 using 1 <;> norm_num
          exact (outside_332102 htau hs332102).elim
      · rcases le_total tau.im (5/16 : ℝ) with hy33210 | hy33210
        · have hs332101 : InSquare (43/160) (49/160) (1/160) tau := by
            convert childLR hs33210 hx33210 hy33210 using 1 <;> norm_num
          rcases le_total tau.re (43/160 : ℝ) with hx332101 | hx332101
          · rcases le_total tau.im (49/160 : ℝ) with hy332101 | hy332101
            · have hs3321010 : InSquare (17/64) (97/320) (1/320) tau := by
                convert childLL hs332101 hx332101 hy332101 using 1 <;> norm_num
              exact Batch0320.cell2563.sound htau (by
                simp only [Batch0320.cell2563, Batch0320.tau2563, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3321010 (by positivity) using 1 <;> norm_num)
            · have hs3321012 : InSquare (17/64) (99/320) (1/320) tau := by
                convert childUL hs332101 hx332101 hy332101 using 1 <;> norm_num
              exact (outside_3321012 htau hs3321012).elim
          · rcases le_total tau.im (49/160 : ℝ) with hy332101 | hy332101
            · have hs3321011 : InSquare (87/320) (97/320) (1/320) tau := by
                convert childLR hs332101 hx332101 hy332101 using 1 <;> norm_num
              exact (outside_3321011 htau hs3321011).elim
            · have hs3321013 : InSquare (87/320) (99/320) (1/320) tau := by
                convert childUR hs332101 hx332101 hy332101 using 1 <;> norm_num
              exact (outside_3321013 htau hs3321013).elim
        · have hs332103 : InSquare (43/160) (51/160) (1/160) tau := by
            convert childUR hs33210 hx33210 hy33210 using 1 <;> norm_num
          exact (outside_332103 htau hs332103).elim
    · have hs33212 : InSquare (21/80) (27/80) (1/80) tau := by
        convert childUL hs hx3321 hy3321 using 1 <;> norm_num
      exact (outside_33212 htau hs33212).elim
  · rcases le_total tau.im (13/40 : ℝ) with hy3321 | hy3321
    · have hs33211 : InSquare (23/80) (5/16) (1/80) tau := by
        convert childLR hs hx3321 hy3321 using 1 <;> norm_num
      exact (outside_33211 htau hs33211).elim
    · have hs33213 : InSquare (23/80) (27/80) (1/80) tau := by
        convert childUR hs hx3321 hy3321 using 1 <;> norm_num
      exact (outside_33213 htau hs33213).elim

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3321
