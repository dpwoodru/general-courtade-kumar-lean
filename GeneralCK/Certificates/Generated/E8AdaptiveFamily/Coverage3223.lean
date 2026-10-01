import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0284
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0285
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0286
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0287
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0288
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0450
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0451
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0452
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0453
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0454
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0455
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0456
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0457
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0458
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0459
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0460

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3223

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

private theorem outside_3223322 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (5/64) (127/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (3/40 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-3/40)]
  have himSq : (63/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-63/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_3223323 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (27/320) (127/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (13/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-13/160)]
  have himSq : (63/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-63/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_3223332 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (29/320) (127/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (7/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-7/80)]
  have himSq : (63/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-63/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_3223333 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (31/320) (127/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (3/32 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-3/32)]
  have himSq : (63/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-63/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_32232222 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (33/640) (51/128) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (1/20 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-1/20)]
  have himSq : (127/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-127/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_32232223 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (7/128) (51/128) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (17/320 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-17/320)]
  have himSq : (127/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-127/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_32232232 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (37/640) (51/128) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (9/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-9/160)]
  have himSq : (127/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-127/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_32232233 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (39/640) (51/128) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (19/320 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-19/320)]
  have himSq : (127/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-127/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_32232322 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (41/640) (51/128) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (1/16 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-1/16)]
  have himSq : (127/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-127/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_32232323 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (43/640) (51/128) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (21/320 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-21/320)]
  have himSq : (127/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-127/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_32232331 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (47/640) (253/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (23/320 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-23/320)]
  have himSq : (63/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-63/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_32232332 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (9/128) (51/128) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (11/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-11/160)]
  have himSq : (127/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-127/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_32232333 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (47/640) (51/128) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (23/320 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-23/320)]
  have himSq : (127/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-127/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_32233302 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (57/640) (251/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (7/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-7/80)]
  have himSq : (25/64 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-25/64)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_32233303 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (59/640) (251/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (29/320 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-29/320)]
  have himSq : (25/64 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-25/64)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_32233312 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (61/640) (251/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (3/32 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-3/32)]
  have himSq : (25/64 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-25/64)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_32233313 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (63/640) (251/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (31/320 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-31/320)]
  have himSq : (25/64 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-25/64)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (3/40) (3/8) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (3/40 : ℝ) with hx3223 | hx3223
  · rcases le_total tau.im (3/8 : ℝ) with hy3223 | hy3223
    · have hs32230 : InSquare (1/16) (29/80) (1/80) tau := by
        convert childLL hs hx3223 hy3223 using 1 <;> norm_num
      rcases le_total tau.re (1/16 : ℝ) with hx32230 | hx32230
      · rcases le_total tau.im (29/80 : ℝ) with hy32230 | hy32230
        · have hs322300 : InSquare (9/160) (57/160) (1/160) tau := by
            convert childLL hs32230 hx32230 hy32230 using 1 <;> norm_num
          rcases le_total tau.re (9/160 : ℝ) with hx322300 | hx322300
          · rcases le_total tau.im (57/160 : ℝ) with hy322300 | hy322300
            · have hs3223000 : InSquare (17/320) (113/320) (1/320) tau := by
                convert childLL hs322300 hx322300 hy322300 using 1 <;> norm_num
              exact Batch0284.cell2277.sound htau (by
                simp only [Batch0284.cell2277, Batch0284.tau2277, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3223000 (by positivity) using 1 <;> norm_num)
            · have hs3223002 : InSquare (17/320) (23/64) (1/320) tau := by
                convert childUL hs322300 hx322300 hy322300 using 1 <;> norm_num
              exact Batch0284.cell2279.sound htau (by
                simp only [Batch0284.cell2279, Batch0284.tau2279, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3223002 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (57/160 : ℝ) with hy322300 | hy322300
            · have hs3223001 : InSquare (19/320) (113/320) (1/320) tau := by
                convert childLR hs322300 hx322300 hy322300 using 1 <;> norm_num
              exact Batch0284.cell2278.sound htau (by
                simp only [Batch0284.cell2278, Batch0284.tau2278, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3223001 (by positivity) using 1 <;> norm_num)
            · have hs3223003 : InSquare (19/320) (23/64) (1/320) tau := by
                convert childUR hs322300 hx322300 hy322300 using 1 <;> norm_num
              exact Batch0285.cell2280.sound htau (by
                simp only [Batch0285.cell2280, Batch0285.tau2280, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3223003 (by positivity) using 1 <;> norm_num)
        · have hs322302 : InSquare (9/160) (59/160) (1/160) tau := by
            convert childUL hs32230 hx32230 hy32230 using 1 <;> norm_num
          rcases le_total tau.re (9/160 : ℝ) with hx322302 | hx322302
          · rcases le_total tau.im (59/160 : ℝ) with hy322302 | hy322302
            · have hs3223020 : InSquare (17/320) (117/320) (1/320) tau := by
                convert childLL hs322302 hx322302 hy322302 using 1 <;> norm_num
              exact Batch0285.cell2285.sound htau (by
                simp only [Batch0285.cell2285, Batch0285.tau2285, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3223020 (by positivity) using 1 <;> norm_num)
            · have hs3223022 : InSquare (17/320) (119/320) (1/320) tau := by
                convert childUL hs322302 hx322302 hy322302 using 1 <;> norm_num
              exact Batch0285.cell2287.sound htau (by
                simp only [Batch0285.cell2287, Batch0285.tau2287, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3223022 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (59/160 : ℝ) with hy322302 | hy322302
            · have hs3223021 : InSquare (19/320) (117/320) (1/320) tau := by
                convert childLR hs322302 hx322302 hy322302 using 1 <;> norm_num
              exact Batch0285.cell2286.sound htau (by
                simp only [Batch0285.cell2286, Batch0285.tau2286, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3223021 (by positivity) using 1 <;> norm_num)
            · have hs3223023 : InSquare (19/320) (119/320) (1/320) tau := by
                convert childUR hs322302 hx322302 hy322302 using 1 <;> norm_num
              exact Batch0286.cell2288.sound htau (by
                simp only [Batch0286.cell2288, Batch0286.tau2288, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3223023 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (29/80 : ℝ) with hy32230 | hy32230
        · have hs322301 : InSquare (11/160) (57/160) (1/160) tau := by
            convert childLR hs32230 hx32230 hy32230 using 1 <;> norm_num
          rcases le_total tau.re (11/160 : ℝ) with hx322301 | hx322301
          · rcases le_total tau.im (57/160 : ℝ) with hy322301 | hy322301
            · have hs3223010 : InSquare (21/320) (113/320) (1/320) tau := by
                convert childLL hs322301 hx322301 hy322301 using 1 <;> norm_num
              exact Batch0285.cell2281.sound htau (by
                simp only [Batch0285.cell2281, Batch0285.tau2281, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3223010 (by positivity) using 1 <;> norm_num)
            · have hs3223012 : InSquare (21/320) (23/64) (1/320) tau := by
                convert childUL hs322301 hx322301 hy322301 using 1 <;> norm_num
              exact Batch0285.cell2283.sound htau (by
                simp only [Batch0285.cell2283, Batch0285.tau2283, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3223012 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (57/160 : ℝ) with hy322301 | hy322301
            · have hs3223011 : InSquare (23/320) (113/320) (1/320) tau := by
                convert childLR hs322301 hx322301 hy322301 using 1 <;> norm_num
              exact Batch0285.cell2282.sound htau (by
                simp only [Batch0285.cell2282, Batch0285.tau2282, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3223011 (by positivity) using 1 <;> norm_num)
            · have hs3223013 : InSquare (23/320) (23/64) (1/320) tau := by
                convert childUR hs322301 hx322301 hy322301 using 1 <;> norm_num
              exact Batch0285.cell2284.sound htau (by
                simp only [Batch0285.cell2284, Batch0285.tau2284, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3223013 (by positivity) using 1 <;> norm_num)
        · have hs322303 : InSquare (11/160) (59/160) (1/160) tau := by
            convert childUR hs32230 hx32230 hy32230 using 1 <;> norm_num
          rcases le_total tau.re (11/160 : ℝ) with hx322303 | hx322303
          · rcases le_total tau.im (59/160 : ℝ) with hy322303 | hy322303
            · have hs3223030 : InSquare (21/320) (117/320) (1/320) tau := by
                convert childLL hs322303 hx322303 hy322303 using 1 <;> norm_num
              exact Batch0286.cell2289.sound htau (by
                simp only [Batch0286.cell2289, Batch0286.tau2289, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3223030 (by positivity) using 1 <;> norm_num)
            · have hs3223032 : InSquare (21/320) (119/320) (1/320) tau := by
                convert childUL hs322303 hx322303 hy322303 using 1 <;> norm_num
              exact Batch0286.cell2291.sound htau (by
                simp only [Batch0286.cell2291, Batch0286.tau2291, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3223032 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (59/160 : ℝ) with hy322303 | hy322303
            · have hs3223031 : InSquare (23/320) (117/320) (1/320) tau := by
                convert childLR hs322303 hx322303 hy322303 using 1 <;> norm_num
              exact Batch0286.cell2290.sound htau (by
                simp only [Batch0286.cell2290, Batch0286.tau2290, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3223031 (by positivity) using 1 <;> norm_num)
            · have hs3223033 : InSquare (23/320) (119/320) (1/320) tau := by
                convert childUR hs322303 hx322303 hy322303 using 1 <;> norm_num
              exact Batch0286.cell2292.sound htau (by
                simp only [Batch0286.cell2292, Batch0286.tau2292, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3223033 (by positivity) using 1 <;> norm_num)
    · have hs32232 : InSquare (1/16) (31/80) (1/80) tau := by
        convert childUL hs hx3223 hy3223 using 1 <;> norm_num
      rcases le_total tau.re (1/16 : ℝ) with hx32232 | hx32232
      · rcases le_total tau.im (31/80 : ℝ) with hy32232 | hy32232
        · have hs322320 : InSquare (9/160) (61/160) (1/160) tau := by
            convert childLL hs32232 hx32232 hy32232 using 1 <;> norm_num
          rcases le_total tau.re (9/160 : ℝ) with hx322320 | hx322320
          · rcases le_total tau.im (61/160 : ℝ) with hy322320 | hy322320
            · have hs3223200 : InSquare (17/320) (121/320) (1/320) tau := by
                convert childLL hs322320 hx322320 hy322320 using 1 <;> norm_num
              exact Batch0288.cell2309.sound htau (by
                simp only [Batch0288.cell2309, Batch0288.tau2309, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3223200 (by positivity) using 1 <;> norm_num)
            · have hs3223202 : InSquare (17/320) (123/320) (1/320) tau := by
                convert childUL hs322320 hx322320 hy322320 using 1 <;> norm_num
              rcases le_total tau.re (17/320 : ℝ) with hx3223202 | hx3223202
              · rcases le_total tau.im (123/320 : ℝ) with hy3223202 | hy3223202
                · have hs32232020 : InSquare (33/640) (49/128) (1/640) tau := by
                    convert childLL hs3223202 hx3223202 hy3223202 using 1 <;> norm_num
                  exact Batch0450.cell3600.sound htau (by
                    simp only [Batch0450.cell3600, Batch0450.tau3600, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32232020 (by positivity) using 1 <;> norm_num)
                · have hs32232022 : InSquare (33/640) (247/640) (1/640) tau := by
                    convert childUL hs3223202 hx3223202 hy3223202 using 1 <;> norm_num
                  exact Batch0450.cell3602.sound htau (by
                    simp only [Batch0450.cell3602, Batch0450.tau3602, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32232022 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (123/320 : ℝ) with hy3223202 | hy3223202
                · have hs32232021 : InSquare (7/128) (49/128) (1/640) tau := by
                    convert childLR hs3223202 hx3223202 hy3223202 using 1 <;> norm_num
                  exact Batch0450.cell3601.sound htau (by
                    simp only [Batch0450.cell3601, Batch0450.tau3601, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32232021 (by positivity) using 1 <;> norm_num)
                · have hs32232023 : InSquare (7/128) (247/640) (1/640) tau := by
                    convert childUR hs3223202 hx3223202 hy3223202 using 1 <;> norm_num
                  exact Batch0450.cell3603.sound htau (by
                    simp only [Batch0450.cell3603, Batch0450.tau3603, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32232023 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (61/160 : ℝ) with hy322320 | hy322320
            · have hs3223201 : InSquare (19/320) (121/320) (1/320) tau := by
                convert childLR hs322320 hx322320 hy322320 using 1 <;> norm_num
              exact Batch0288.cell2310.sound htau (by
                simp only [Batch0288.cell2310, Batch0288.tau2310, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3223201 (by positivity) using 1 <;> norm_num)
            · have hs3223203 : InSquare (19/320) (123/320) (1/320) tau := by
                convert childUR hs322320 hx322320 hy322320 using 1 <;> norm_num
              rcases le_total tau.re (19/320 : ℝ) with hx3223203 | hx3223203
              · rcases le_total tau.im (123/320 : ℝ) with hy3223203 | hy3223203
                · have hs32232030 : InSquare (37/640) (49/128) (1/640) tau := by
                    convert childLL hs3223203 hx3223203 hy3223203 using 1 <;> norm_num
                  exact Batch0450.cell3604.sound htau (by
                    simp only [Batch0450.cell3604, Batch0450.tau3604, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32232030 (by positivity) using 1 <;> norm_num)
                · have hs32232032 : InSquare (37/640) (247/640) (1/640) tau := by
                    convert childUL hs3223203 hx3223203 hy3223203 using 1 <;> norm_num
                  exact Batch0450.cell3606.sound htau (by
                    simp only [Batch0450.cell3606, Batch0450.tau3606, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32232032 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (123/320 : ℝ) with hy3223203 | hy3223203
                · have hs32232031 : InSquare (39/640) (49/128) (1/640) tau := by
                    convert childLR hs3223203 hx3223203 hy3223203 using 1 <;> norm_num
                  exact Batch0450.cell3605.sound htau (by
                    simp only [Batch0450.cell3605, Batch0450.tau3605, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32232031 (by positivity) using 1 <;> norm_num)
                · have hs32232033 : InSquare (39/640) (247/640) (1/640) tau := by
                    convert childUR hs3223203 hx3223203 hy3223203 using 1 <;> norm_num
                  exact Batch0450.cell3607.sound htau (by
                    simp only [Batch0450.cell3607, Batch0450.tau3607, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32232033 (by positivity) using 1 <;> norm_num)
        · have hs322322 : InSquare (9/160) (63/160) (1/160) tau := by
            convert childUL hs32232 hx32232 hy32232 using 1 <;> norm_num
          rcases le_total tau.re (9/160 : ℝ) with hx322322 | hx322322
          · rcases le_total tau.im (63/160 : ℝ) with hy322322 | hy322322
            · have hs3223220 : InSquare (17/320) (25/64) (1/320) tau := by
                convert childLL hs322322 hx322322 hy322322 using 1 <;> norm_num
              rcases le_total tau.re (17/320 : ℝ) with hx3223220 | hx3223220
              · rcases le_total tau.im (25/64 : ℝ) with hy3223220 | hy3223220
                · have hs32232200 : InSquare (33/640) (249/640) (1/640) tau := by
                    convert childLL hs3223220 hx3223220 hy3223220 using 1 <;> norm_num
                  exact Batch0452.cell3620.sound htau (by
                    simp only [Batch0452.cell3620, Batch0452.tau3620, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32232200 (by positivity) using 1 <;> norm_num)
                · have hs32232202 : InSquare (33/640) (251/640) (1/640) tau := by
                    convert childUL hs3223220 hx3223220 hy3223220 using 1 <;> norm_num
                  exact Batch0452.cell3622.sound htau (by
                    simp only [Batch0452.cell3622, Batch0452.tau3622, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32232202 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (25/64 : ℝ) with hy3223220 | hy3223220
                · have hs32232201 : InSquare (7/128) (249/640) (1/640) tau := by
                    convert childLR hs3223220 hx3223220 hy3223220 using 1 <;> norm_num
                  exact Batch0452.cell3621.sound htau (by
                    simp only [Batch0452.cell3621, Batch0452.tau3621, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32232201 (by positivity) using 1 <;> norm_num)
                · have hs32232203 : InSquare (7/128) (251/640) (1/640) tau := by
                    convert childUR hs3223220 hx3223220 hy3223220 using 1 <;> norm_num
                  exact Batch0452.cell3623.sound htau (by
                    simp only [Batch0452.cell3623, Batch0452.tau3623, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32232203 (by positivity) using 1 <;> norm_num)
            · have hs3223222 : InSquare (17/320) (127/320) (1/320) tau := by
                convert childUL hs322322 hx322322 hy322322 using 1 <;> norm_num
              rcases le_total tau.re (17/320 : ℝ) with hx3223222 | hx3223222
              · rcases le_total tau.im (127/320 : ℝ) with hy3223222 | hy3223222
                · have hs32232220 : InSquare (33/640) (253/640) (1/640) tau := by
                    convert childLL hs3223222 hx3223222 hy3223222 using 1 <;> norm_num
                  exact Batch0453.cell3628.sound htau (by
                    simp only [Batch0453.cell3628, Batch0453.tau3628, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32232220 (by positivity) using 1 <;> norm_num)
                · have hs32232222 : InSquare (33/640) (51/128) (1/640) tau := by
                    convert childUL hs3223222 hx3223222 hy3223222 using 1 <;> norm_num
                  exact (outside_32232222 htau hs32232222).elim
              · rcases le_total tau.im (127/320 : ℝ) with hy3223222 | hy3223222
                · have hs32232221 : InSquare (7/128) (253/640) (1/640) tau := by
                    convert childLR hs3223222 hx3223222 hy3223222 using 1 <;> norm_num
                  exact Batch0453.cell3629.sound htau (by
                    simp only [Batch0453.cell3629, Batch0453.tau3629, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32232221 (by positivity) using 1 <;> norm_num)
                · have hs32232223 : InSquare (7/128) (51/128) (1/640) tau := by
                    convert childUR hs3223222 hx3223222 hy3223222 using 1 <;> norm_num
                  exact (outside_32232223 htau hs32232223).elim
          · rcases le_total tau.im (63/160 : ℝ) with hy322322 | hy322322
            · have hs3223221 : InSquare (19/320) (25/64) (1/320) tau := by
                convert childLR hs322322 hx322322 hy322322 using 1 <;> norm_num
              rcases le_total tau.re (19/320 : ℝ) with hx3223221 | hx3223221
              · rcases le_total tau.im (25/64 : ℝ) with hy3223221 | hy3223221
                · have hs32232210 : InSquare (37/640) (249/640) (1/640) tau := by
                    convert childLL hs3223221 hx3223221 hy3223221 using 1 <;> norm_num
                  exact Batch0453.cell3624.sound htau (by
                    simp only [Batch0453.cell3624, Batch0453.tau3624, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32232210 (by positivity) using 1 <;> norm_num)
                · have hs32232212 : InSquare (37/640) (251/640) (1/640) tau := by
                    convert childUL hs3223221 hx3223221 hy3223221 using 1 <;> norm_num
                  exact Batch0453.cell3626.sound htau (by
                    simp only [Batch0453.cell3626, Batch0453.tau3626, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32232212 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (25/64 : ℝ) with hy3223221 | hy3223221
                · have hs32232211 : InSquare (39/640) (249/640) (1/640) tau := by
                    convert childLR hs3223221 hx3223221 hy3223221 using 1 <;> norm_num
                  exact Batch0453.cell3625.sound htau (by
                    simp only [Batch0453.cell3625, Batch0453.tau3625, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32232211 (by positivity) using 1 <;> norm_num)
                · have hs32232213 : InSquare (39/640) (251/640) (1/640) tau := by
                    convert childUR hs3223221 hx3223221 hy3223221 using 1 <;> norm_num
                  exact Batch0453.cell3627.sound htau (by
                    simp only [Batch0453.cell3627, Batch0453.tau3627, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32232213 (by positivity) using 1 <;> norm_num)
            · have hs3223223 : InSquare (19/320) (127/320) (1/320) tau := by
                convert childUR hs322322 hx322322 hy322322 using 1 <;> norm_num
              rcases le_total tau.re (19/320 : ℝ) with hx3223223 | hx3223223
              · rcases le_total tau.im (127/320 : ℝ) with hy3223223 | hy3223223
                · have hs32232230 : InSquare (37/640) (253/640) (1/640) tau := by
                    convert childLL hs3223223 hx3223223 hy3223223 using 1 <;> norm_num
                  exact Batch0453.cell3630.sound htau (by
                    simp only [Batch0453.cell3630, Batch0453.tau3630, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32232230 (by positivity) using 1 <;> norm_num)
                · have hs32232232 : InSquare (37/640) (51/128) (1/640) tau := by
                    convert childUL hs3223223 hx3223223 hy3223223 using 1 <;> norm_num
                  exact (outside_32232232 htau hs32232232).elim
              · rcases le_total tau.im (127/320 : ℝ) with hy3223223 | hy3223223
                · have hs32232231 : InSquare (39/640) (253/640) (1/640) tau := by
                    convert childLR hs3223223 hx3223223 hy3223223 using 1 <;> norm_num
                  exact Batch0453.cell3631.sound htau (by
                    simp only [Batch0453.cell3631, Batch0453.tau3631, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32232231 (by positivity) using 1 <;> norm_num)
                · have hs32232233 : InSquare (39/640) (51/128) (1/640) tau := by
                    convert childUR hs3223223 hx3223223 hy3223223 using 1 <;> norm_num
                  exact (outside_32232233 htau hs32232233).elim
      · rcases le_total tau.im (31/80 : ℝ) with hy32232 | hy32232
        · have hs322321 : InSquare (11/160) (61/160) (1/160) tau := by
            convert childLR hs32232 hx32232 hy32232 using 1 <;> norm_num
          rcases le_total tau.re (11/160 : ℝ) with hx322321 | hx322321
          · rcases le_total tau.im (61/160 : ℝ) with hy322321 | hy322321
            · have hs3223210 : InSquare (21/320) (121/320) (1/320) tau := by
                convert childLL hs322321 hx322321 hy322321 using 1 <;> norm_num
              exact Batch0288.cell2311.sound htau (by
                simp only [Batch0288.cell2311, Batch0288.tau2311, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3223210 (by positivity) using 1 <;> norm_num)
            · have hs3223212 : InSquare (21/320) (123/320) (1/320) tau := by
                convert childUL hs322321 hx322321 hy322321 using 1 <;> norm_num
              rcases le_total tau.re (21/320 : ℝ) with hx3223212 | hx3223212
              · rcases le_total tau.im (123/320 : ℝ) with hy3223212 | hy3223212
                · have hs32232120 : InSquare (41/640) (49/128) (1/640) tau := by
                    convert childLL hs3223212 hx3223212 hy3223212 using 1 <;> norm_num
                  exact Batch0451.cell3612.sound htau (by
                    simp only [Batch0451.cell3612, Batch0451.tau3612, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32232120 (by positivity) using 1 <;> norm_num)
                · have hs32232122 : InSquare (41/640) (247/640) (1/640) tau := by
                    convert childUL hs3223212 hx3223212 hy3223212 using 1 <;> norm_num
                  exact Batch0451.cell3614.sound htau (by
                    simp only [Batch0451.cell3614, Batch0451.tau3614, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32232122 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (123/320 : ℝ) with hy3223212 | hy3223212
                · have hs32232121 : InSquare (43/640) (49/128) (1/640) tau := by
                    convert childLR hs3223212 hx3223212 hy3223212 using 1 <;> norm_num
                  exact Batch0451.cell3613.sound htau (by
                    simp only [Batch0451.cell3613, Batch0451.tau3613, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32232121 (by positivity) using 1 <;> norm_num)
                · have hs32232123 : InSquare (43/640) (247/640) (1/640) tau := by
                    convert childUR hs3223212 hx3223212 hy3223212 using 1 <;> norm_num
                  exact Batch0451.cell3615.sound htau (by
                    simp only [Batch0451.cell3615, Batch0451.tau3615, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32232123 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (61/160 : ℝ) with hy322321 | hy322321
            · have hs3223211 : InSquare (23/320) (121/320) (1/320) tau := by
                convert childLR hs322321 hx322321 hy322321 using 1 <;> norm_num
              rcases le_total tau.re (23/320 : ℝ) with hx3223211 | hx3223211
              · rcases le_total tau.im (121/320 : ℝ) with hy3223211 | hy3223211
                · have hs32232110 : InSquare (9/128) (241/640) (1/640) tau := by
                    convert childLL hs3223211 hx3223211 hy3223211 using 1 <;> norm_num
                  exact Batch0451.cell3608.sound htau (by
                    simp only [Batch0451.cell3608, Batch0451.tau3608, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32232110 (by positivity) using 1 <;> norm_num)
                · have hs32232112 : InSquare (9/128) (243/640) (1/640) tau := by
                    convert childUL hs3223211 hx3223211 hy3223211 using 1 <;> norm_num
                  exact Batch0451.cell3610.sound htau (by
                    simp only [Batch0451.cell3610, Batch0451.tau3610, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32232112 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (121/320 : ℝ) with hy3223211 | hy3223211
                · have hs32232111 : InSquare (47/640) (241/640) (1/640) tau := by
                    convert childLR hs3223211 hx3223211 hy3223211 using 1 <;> norm_num
                  exact Batch0451.cell3609.sound htau (by
                    simp only [Batch0451.cell3609, Batch0451.tau3609, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32232111 (by positivity) using 1 <;> norm_num)
                · have hs32232113 : InSquare (47/640) (243/640) (1/640) tau := by
                    convert childUR hs3223211 hx3223211 hy3223211 using 1 <;> norm_num
                  exact Batch0451.cell3611.sound htau (by
                    simp only [Batch0451.cell3611, Batch0451.tau3611, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32232113 (by positivity) using 1 <;> norm_num)
            · have hs3223213 : InSquare (23/320) (123/320) (1/320) tau := by
                convert childUR hs322321 hx322321 hy322321 using 1 <;> norm_num
              rcases le_total tau.re (23/320 : ℝ) with hx3223213 | hx3223213
              · rcases le_total tau.im (123/320 : ℝ) with hy3223213 | hy3223213
                · have hs32232130 : InSquare (9/128) (49/128) (1/640) tau := by
                    convert childLL hs3223213 hx3223213 hy3223213 using 1 <;> norm_num
                  exact Batch0452.cell3616.sound htau (by
                    simp only [Batch0452.cell3616, Batch0452.tau3616, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32232130 (by positivity) using 1 <;> norm_num)
                · have hs32232132 : InSquare (9/128) (247/640) (1/640) tau := by
                    convert childUL hs3223213 hx3223213 hy3223213 using 1 <;> norm_num
                  exact Batch0452.cell3618.sound htau (by
                    simp only [Batch0452.cell3618, Batch0452.tau3618, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32232132 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (123/320 : ℝ) with hy3223213 | hy3223213
                · have hs32232131 : InSquare (47/640) (49/128) (1/640) tau := by
                    convert childLR hs3223213 hx3223213 hy3223213 using 1 <;> norm_num
                  exact Batch0452.cell3617.sound htau (by
                    simp only [Batch0452.cell3617, Batch0452.tau3617, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32232131 (by positivity) using 1 <;> norm_num)
                · have hs32232133 : InSquare (47/640) (247/640) (1/640) tau := by
                    convert childUR hs3223213 hx3223213 hy3223213 using 1 <;> norm_num
                  exact Batch0452.cell3619.sound htau (by
                    simp only [Batch0452.cell3619, Batch0452.tau3619, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32232133 (by positivity) using 1 <;> norm_num)
        · have hs322323 : InSquare (11/160) (63/160) (1/160) tau := by
            convert childUR hs32232 hx32232 hy32232 using 1 <;> norm_num
          rcases le_total tau.re (11/160 : ℝ) with hx322323 | hx322323
          · rcases le_total tau.im (63/160 : ℝ) with hy322323 | hy322323
            · have hs3223230 : InSquare (21/320) (25/64) (1/320) tau := by
                convert childLL hs322323 hx322323 hy322323 using 1 <;> norm_num
              rcases le_total tau.re (21/320 : ℝ) with hx3223230 | hx3223230
              · rcases le_total tau.im (25/64 : ℝ) with hy3223230 | hy3223230
                · have hs32232300 : InSquare (41/640) (249/640) (1/640) tau := by
                    convert childLL hs3223230 hx3223230 hy3223230 using 1 <;> norm_num
                  exact Batch0454.cell3632.sound htau (by
                    simp only [Batch0454.cell3632, Batch0454.tau3632, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32232300 (by positivity) using 1 <;> norm_num)
                · have hs32232302 : InSquare (41/640) (251/640) (1/640) tau := by
                    convert childUL hs3223230 hx3223230 hy3223230 using 1 <;> norm_num
                  exact Batch0454.cell3634.sound htau (by
                    simp only [Batch0454.cell3634, Batch0454.tau3634, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32232302 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (25/64 : ℝ) with hy3223230 | hy3223230
                · have hs32232301 : InSquare (43/640) (249/640) (1/640) tau := by
                    convert childLR hs3223230 hx3223230 hy3223230 using 1 <;> norm_num
                  exact Batch0454.cell3633.sound htau (by
                    simp only [Batch0454.cell3633, Batch0454.tau3633, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32232301 (by positivity) using 1 <;> norm_num)
                · have hs32232303 : InSquare (43/640) (251/640) (1/640) tau := by
                    convert childUR hs3223230 hx3223230 hy3223230 using 1 <;> norm_num
                  exact Batch0454.cell3635.sound htau (by
                    simp only [Batch0454.cell3635, Batch0454.tau3635, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32232303 (by positivity) using 1 <;> norm_num)
            · have hs3223232 : InSquare (21/320) (127/320) (1/320) tau := by
                convert childUL hs322323 hx322323 hy322323 using 1 <;> norm_num
              rcases le_total tau.re (21/320 : ℝ) with hx3223232 | hx3223232
              · rcases le_total tau.im (127/320 : ℝ) with hy3223232 | hy3223232
                · have hs32232320 : InSquare (41/640) (253/640) (1/640) tau := by
                    convert childLL hs3223232 hx3223232 hy3223232 using 1 <;> norm_num
                  exact Batch0455.cell3640.sound htau (by
                    simp only [Batch0455.cell3640, Batch0455.tau3640, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32232320 (by positivity) using 1 <;> norm_num)
                · have hs32232322 : InSquare (41/640) (51/128) (1/640) tau := by
                    convert childUL hs3223232 hx3223232 hy3223232 using 1 <;> norm_num
                  exact (outside_32232322 htau hs32232322).elim
              · rcases le_total tau.im (127/320 : ℝ) with hy3223232 | hy3223232
                · have hs32232321 : InSquare (43/640) (253/640) (1/640) tau := by
                    convert childLR hs3223232 hx3223232 hy3223232 using 1 <;> norm_num
                  exact Batch0455.cell3641.sound htau (by
                    simp only [Batch0455.cell3641, Batch0455.tau3641, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32232321 (by positivity) using 1 <;> norm_num)
                · have hs32232323 : InSquare (43/640) (51/128) (1/640) tau := by
                    convert childUR hs3223232 hx3223232 hy3223232 using 1 <;> norm_num
                  exact (outside_32232323 htau hs32232323).elim
          · rcases le_total tau.im (63/160 : ℝ) with hy322323 | hy322323
            · have hs3223231 : InSquare (23/320) (25/64) (1/320) tau := by
                convert childLR hs322323 hx322323 hy322323 using 1 <;> norm_num
              rcases le_total tau.re (23/320 : ℝ) with hx3223231 | hx3223231
              · rcases le_total tau.im (25/64 : ℝ) with hy3223231 | hy3223231
                · have hs32232310 : InSquare (9/128) (249/640) (1/640) tau := by
                    convert childLL hs3223231 hx3223231 hy3223231 using 1 <;> norm_num
                  exact Batch0454.cell3636.sound htau (by
                    simp only [Batch0454.cell3636, Batch0454.tau3636, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32232310 (by positivity) using 1 <;> norm_num)
                · have hs32232312 : InSquare (9/128) (251/640) (1/640) tau := by
                    convert childUL hs3223231 hx3223231 hy3223231 using 1 <;> norm_num
                  exact Batch0454.cell3638.sound htau (by
                    simp only [Batch0454.cell3638, Batch0454.tau3638, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32232312 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (25/64 : ℝ) with hy3223231 | hy3223231
                · have hs32232311 : InSquare (47/640) (249/640) (1/640) tau := by
                    convert childLR hs3223231 hx3223231 hy3223231 using 1 <;> norm_num
                  exact Batch0454.cell3637.sound htau (by
                    simp only [Batch0454.cell3637, Batch0454.tau3637, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32232311 (by positivity) using 1 <;> norm_num)
                · have hs32232313 : InSquare (47/640) (251/640) (1/640) tau := by
                    convert childUR hs3223231 hx3223231 hy3223231 using 1 <;> norm_num
                  exact Batch0454.cell3639.sound htau (by
                    simp only [Batch0454.cell3639, Batch0454.tau3639, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32232313 (by positivity) using 1 <;> norm_num)
            · have hs3223233 : InSquare (23/320) (127/320) (1/320) tau := by
                convert childUR hs322323 hx322323 hy322323 using 1 <;> norm_num
              rcases le_total tau.re (23/320 : ℝ) with hx3223233 | hx3223233
              · rcases le_total tau.im (127/320 : ℝ) with hy3223233 | hy3223233
                · have hs32232330 : InSquare (9/128) (253/640) (1/640) tau := by
                    convert childLL hs3223233 hx3223233 hy3223233 using 1 <;> norm_num
                  exact Batch0455.cell3642.sound htau (by
                    simp only [Batch0455.cell3642, Batch0455.tau3642, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32232330 (by positivity) using 1 <;> norm_num)
                · have hs32232332 : InSquare (9/128) (51/128) (1/640) tau := by
                    convert childUL hs3223233 hx3223233 hy3223233 using 1 <;> norm_num
                  exact (outside_32232332 htau hs32232332).elim
              · rcases le_total tau.im (127/320 : ℝ) with hy3223233 | hy3223233
                · have hs32232331 : InSquare (47/640) (253/640) (1/640) tau := by
                    convert childLR hs3223233 hx3223233 hy3223233 using 1 <;> norm_num
                  exact (outside_32232331 htau hs32232331).elim
                · have hs32232333 : InSquare (47/640) (51/128) (1/640) tau := by
                    convert childUR hs3223233 hx3223233 hy3223233 using 1 <;> norm_num
                  exact (outside_32232333 htau hs32232333).elim
  · rcases le_total tau.im (3/8 : ℝ) with hy3223 | hy3223
    · have hs32231 : InSquare (7/80) (29/80) (1/80) tau := by
        convert childLR hs hx3223 hy3223 using 1 <;> norm_num
      rcases le_total tau.re (7/80 : ℝ) with hx32231 | hx32231
      · rcases le_total tau.im (29/80 : ℝ) with hy32231 | hy32231
        · have hs322310 : InSquare (13/160) (57/160) (1/160) tau := by
            convert childLL hs32231 hx32231 hy32231 using 1 <;> norm_num
          rcases le_total tau.re (13/160 : ℝ) with hx322310 | hx322310
          · rcases le_total tau.im (57/160 : ℝ) with hy322310 | hy322310
            · have hs3223100 : InSquare (5/64) (113/320) (1/320) tau := by
                convert childLL hs322310 hx322310 hy322310 using 1 <;> norm_num
              exact Batch0286.cell2293.sound htau (by
                simp only [Batch0286.cell2293, Batch0286.tau2293, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3223100 (by positivity) using 1 <;> norm_num)
            · have hs3223102 : InSquare (5/64) (23/64) (1/320) tau := by
                convert childUL hs322310 hx322310 hy322310 using 1 <;> norm_num
              exact Batch0286.cell2295.sound htau (by
                simp only [Batch0286.cell2295, Batch0286.tau2295, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3223102 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (57/160 : ℝ) with hy322310 | hy322310
            · have hs3223101 : InSquare (27/320) (113/320) (1/320) tau := by
                convert childLR hs322310 hx322310 hy322310 using 1 <;> norm_num
              exact Batch0286.cell2294.sound htau (by
                simp only [Batch0286.cell2294, Batch0286.tau2294, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3223101 (by positivity) using 1 <;> norm_num)
            · have hs3223103 : InSquare (27/320) (23/64) (1/320) tau := by
                convert childUR hs322310 hx322310 hy322310 using 1 <;> norm_num
              exact Batch0287.cell2296.sound htau (by
                simp only [Batch0287.cell2296, Batch0287.tau2296, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3223103 (by positivity) using 1 <;> norm_num)
        · have hs322312 : InSquare (13/160) (59/160) (1/160) tau := by
            convert childUL hs32231 hx32231 hy32231 using 1 <;> norm_num
          rcases le_total tau.re (13/160 : ℝ) with hx322312 | hx322312
          · rcases le_total tau.im (59/160 : ℝ) with hy322312 | hy322312
            · have hs3223120 : InSquare (5/64) (117/320) (1/320) tau := by
                convert childLL hs322312 hx322312 hy322312 using 1 <;> norm_num
              exact Batch0287.cell2301.sound htau (by
                simp only [Batch0287.cell2301, Batch0287.tau2301, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3223120 (by positivity) using 1 <;> norm_num)
            · have hs3223122 : InSquare (5/64) (119/320) (1/320) tau := by
                convert childUL hs322312 hx322312 hy322312 using 1 <;> norm_num
              exact Batch0287.cell2303.sound htau (by
                simp only [Batch0287.cell2303, Batch0287.tau2303, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3223122 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (59/160 : ℝ) with hy322312 | hy322312
            · have hs3223121 : InSquare (27/320) (117/320) (1/320) tau := by
                convert childLR hs322312 hx322312 hy322312 using 1 <;> norm_num
              exact Batch0287.cell2302.sound htau (by
                simp only [Batch0287.cell2302, Batch0287.tau2302, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3223121 (by positivity) using 1 <;> norm_num)
            · have hs3223123 : InSquare (27/320) (119/320) (1/320) tau := by
                convert childUR hs322312 hx322312 hy322312 using 1 <;> norm_num
              exact Batch0288.cell2304.sound htau (by
                simp only [Batch0288.cell2304, Batch0288.tau2304, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3223123 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (29/80 : ℝ) with hy32231 | hy32231
        · have hs322311 : InSquare (3/32) (57/160) (1/160) tau := by
            convert childLR hs32231 hx32231 hy32231 using 1 <;> norm_num
          rcases le_total tau.re (3/32 : ℝ) with hx322311 | hx322311
          · rcases le_total tau.im (57/160 : ℝ) with hy322311 | hy322311
            · have hs3223110 : InSquare (29/320) (113/320) (1/320) tau := by
                convert childLL hs322311 hx322311 hy322311 using 1 <;> norm_num
              exact Batch0287.cell2297.sound htau (by
                simp only [Batch0287.cell2297, Batch0287.tau2297, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3223110 (by positivity) using 1 <;> norm_num)
            · have hs3223112 : InSquare (29/320) (23/64) (1/320) tau := by
                convert childUL hs322311 hx322311 hy322311 using 1 <;> norm_num
              exact Batch0287.cell2299.sound htau (by
                simp only [Batch0287.cell2299, Batch0287.tau2299, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3223112 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (57/160 : ℝ) with hy322311 | hy322311
            · have hs3223111 : InSquare (31/320) (113/320) (1/320) tau := by
                convert childLR hs322311 hx322311 hy322311 using 1 <;> norm_num
              exact Batch0287.cell2298.sound htau (by
                simp only [Batch0287.cell2298, Batch0287.tau2298, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3223111 (by positivity) using 1 <;> norm_num)
            · have hs3223113 : InSquare (31/320) (23/64) (1/320) tau := by
                convert childUR hs322311 hx322311 hy322311 using 1 <;> norm_num
              exact Batch0287.cell2300.sound htau (by
                simp only [Batch0287.cell2300, Batch0287.tau2300, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3223113 (by positivity) using 1 <;> norm_num)
        · have hs322313 : InSquare (3/32) (59/160) (1/160) tau := by
            convert childUR hs32231 hx32231 hy32231 using 1 <;> norm_num
          rcases le_total tau.re (3/32 : ℝ) with hx322313 | hx322313
          · rcases le_total tau.im (59/160 : ℝ) with hy322313 | hy322313
            · have hs3223130 : InSquare (29/320) (117/320) (1/320) tau := by
                convert childLL hs322313 hx322313 hy322313 using 1 <;> norm_num
              exact Batch0288.cell2305.sound htau (by
                simp only [Batch0288.cell2305, Batch0288.tau2305, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3223130 (by positivity) using 1 <;> norm_num)
            · have hs3223132 : InSquare (29/320) (119/320) (1/320) tau := by
                convert childUL hs322313 hx322313 hy322313 using 1 <;> norm_num
              exact Batch0288.cell2307.sound htau (by
                simp only [Batch0288.cell2307, Batch0288.tau2307, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3223132 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (59/160 : ℝ) with hy322313 | hy322313
            · have hs3223131 : InSquare (31/320) (117/320) (1/320) tau := by
                convert childLR hs322313 hx322313 hy322313 using 1 <;> norm_num
              exact Batch0288.cell2306.sound htau (by
                simp only [Batch0288.cell2306, Batch0288.tau2306, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3223131 (by positivity) using 1 <;> norm_num)
            · have hs3223133 : InSquare (31/320) (119/320) (1/320) tau := by
                convert childUR hs322313 hx322313 hy322313 using 1 <;> norm_num
              exact Batch0288.cell2308.sound htau (by
                simp only [Batch0288.cell2308, Batch0288.tau2308, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3223133 (by positivity) using 1 <;> norm_num)
    · have hs32233 : InSquare (7/80) (31/80) (1/80) tau := by
        convert childUR hs hx3223 hy3223 using 1 <;> norm_num
      rcases le_total tau.re (7/80 : ℝ) with hx32233 | hx32233
      · rcases le_total tau.im (31/80 : ℝ) with hy32233 | hy32233
        · have hs322330 : InSquare (13/160) (61/160) (1/160) tau := by
            convert childLL hs32233 hx32233 hy32233 using 1 <;> norm_num
          rcases le_total tau.re (13/160 : ℝ) with hx322330 | hx322330
          · rcases le_total tau.im (61/160 : ℝ) with hy322330 | hy322330
            · have hs3223300 : InSquare (5/64) (121/320) (1/320) tau := by
                convert childLL hs322330 hx322330 hy322330 using 1 <;> norm_num
              rcases le_total tau.re (5/64 : ℝ) with hx3223300 | hx3223300
              · rcases le_total tau.im (121/320 : ℝ) with hy3223300 | hy3223300
                · have hs32233000 : InSquare (49/640) (241/640) (1/640) tau := by
                    convert childLL hs3223300 hx3223300 hy3223300 using 1 <;> norm_num
                  exact Batch0455.cell3643.sound htau (by
                    simp only [Batch0455.cell3643, Batch0455.tau3643, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32233000 (by positivity) using 1 <;> norm_num)
                · have hs32233002 : InSquare (49/640) (243/640) (1/640) tau := by
                    convert childUL hs3223300 hx3223300 hy3223300 using 1 <;> norm_num
                  exact Batch0455.cell3645.sound htau (by
                    simp only [Batch0455.cell3645, Batch0455.tau3645, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32233002 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (121/320 : ℝ) with hy3223300 | hy3223300
                · have hs32233001 : InSquare (51/640) (241/640) (1/640) tau := by
                    convert childLR hs3223300 hx3223300 hy3223300 using 1 <;> norm_num
                  exact Batch0455.cell3644.sound htau (by
                    simp only [Batch0455.cell3644, Batch0455.tau3644, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32233001 (by positivity) using 1 <;> norm_num)
                · have hs32233003 : InSquare (51/640) (243/640) (1/640) tau := by
                    convert childUR hs3223300 hx3223300 hy3223300 using 1 <;> norm_num
                  exact Batch0455.cell3646.sound htau (by
                    simp only [Batch0455.cell3646, Batch0455.tau3646, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32233003 (by positivity) using 1 <;> norm_num)
            · have hs3223302 : InSquare (5/64) (123/320) (1/320) tau := by
                convert childUL hs322330 hx322330 hy322330 using 1 <;> norm_num
              rcases le_total tau.re (5/64 : ℝ) with hx3223302 | hx3223302
              · rcases le_total tau.im (123/320 : ℝ) with hy3223302 | hy3223302
                · have hs32233020 : InSquare (49/640) (49/128) (1/640) tau := by
                    convert childLL hs3223302 hx3223302 hy3223302 using 1 <;> norm_num
                  exact Batch0456.cell3651.sound htau (by
                    simp only [Batch0456.cell3651, Batch0456.tau3651, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32233020 (by positivity) using 1 <;> norm_num)
                · have hs32233022 : InSquare (49/640) (247/640) (1/640) tau := by
                    convert childUL hs3223302 hx3223302 hy3223302 using 1 <;> norm_num
                  exact Batch0456.cell3653.sound htau (by
                    simp only [Batch0456.cell3653, Batch0456.tau3653, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32233022 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (123/320 : ℝ) with hy3223302 | hy3223302
                · have hs32233021 : InSquare (51/640) (49/128) (1/640) tau := by
                    convert childLR hs3223302 hx3223302 hy3223302 using 1 <;> norm_num
                  exact Batch0456.cell3652.sound htau (by
                    simp only [Batch0456.cell3652, Batch0456.tau3652, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32233021 (by positivity) using 1 <;> norm_num)
                · have hs32233023 : InSquare (51/640) (247/640) (1/640) tau := by
                    convert childUR hs3223302 hx3223302 hy3223302 using 1 <;> norm_num
                  exact Batch0456.cell3654.sound htau (by
                    simp only [Batch0456.cell3654, Batch0456.tau3654, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32233023 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (61/160 : ℝ) with hy322330 | hy322330
            · have hs3223301 : InSquare (27/320) (121/320) (1/320) tau := by
                convert childLR hs322330 hx322330 hy322330 using 1 <;> norm_num
              rcases le_total tau.re (27/320 : ℝ) with hx3223301 | hx3223301
              · rcases le_total tau.im (121/320 : ℝ) with hy3223301 | hy3223301
                · have hs32233010 : InSquare (53/640) (241/640) (1/640) tau := by
                    convert childLL hs3223301 hx3223301 hy3223301 using 1 <;> norm_num
                  exact Batch0455.cell3647.sound htau (by
                    simp only [Batch0455.cell3647, Batch0455.tau3647, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32233010 (by positivity) using 1 <;> norm_num)
                · have hs32233012 : InSquare (53/640) (243/640) (1/640) tau := by
                    convert childUL hs3223301 hx3223301 hy3223301 using 1 <;> norm_num
                  exact Batch0456.cell3649.sound htau (by
                    simp only [Batch0456.cell3649, Batch0456.tau3649, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32233012 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (121/320 : ℝ) with hy3223301 | hy3223301
                · have hs32233011 : InSquare (11/128) (241/640) (1/640) tau := by
                    convert childLR hs3223301 hx3223301 hy3223301 using 1 <;> norm_num
                  exact Batch0456.cell3648.sound htau (by
                    simp only [Batch0456.cell3648, Batch0456.tau3648, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32233011 (by positivity) using 1 <;> norm_num)
                · have hs32233013 : InSquare (11/128) (243/640) (1/640) tau := by
                    convert childUR hs3223301 hx3223301 hy3223301 using 1 <;> norm_num
                  exact Batch0456.cell3650.sound htau (by
                    simp only [Batch0456.cell3650, Batch0456.tau3650, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32233013 (by positivity) using 1 <;> norm_num)
            · have hs3223303 : InSquare (27/320) (123/320) (1/320) tau := by
                convert childUR hs322330 hx322330 hy322330 using 1 <;> norm_num
              rcases le_total tau.re (27/320 : ℝ) with hx3223303 | hx3223303
              · rcases le_total tau.im (123/320 : ℝ) with hy3223303 | hy3223303
                · have hs32233030 : InSquare (53/640) (49/128) (1/640) tau := by
                    convert childLL hs3223303 hx3223303 hy3223303 using 1 <;> norm_num
                  exact Batch0456.cell3655.sound htau (by
                    simp only [Batch0456.cell3655, Batch0456.tau3655, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32233030 (by positivity) using 1 <;> norm_num)
                · have hs32233032 : InSquare (53/640) (247/640) (1/640) tau := by
                    convert childUL hs3223303 hx3223303 hy3223303 using 1 <;> norm_num
                  exact Batch0457.cell3657.sound htau (by
                    simp only [Batch0457.cell3657, Batch0457.tau3657, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32233032 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (123/320 : ℝ) with hy3223303 | hy3223303
                · have hs32233031 : InSquare (11/128) (49/128) (1/640) tau := by
                    convert childLR hs3223303 hx3223303 hy3223303 using 1 <;> norm_num
                  exact Batch0457.cell3656.sound htau (by
                    simp only [Batch0457.cell3656, Batch0457.tau3656, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32233031 (by positivity) using 1 <;> norm_num)
                · have hs32233033 : InSquare (11/128) (247/640) (1/640) tau := by
                    convert childUR hs3223303 hx3223303 hy3223303 using 1 <;> norm_num
                  exact Batch0457.cell3658.sound htau (by
                    simp only [Batch0457.cell3658, Batch0457.tau3658, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32233033 (by positivity) using 1 <;> norm_num)
        · have hs322332 : InSquare (13/160) (63/160) (1/160) tau := by
            convert childUL hs32233 hx32233 hy32233 using 1 <;> norm_num
          rcases le_total tau.re (13/160 : ℝ) with hx322332 | hx322332
          · rcases le_total tau.im (63/160 : ℝ) with hy322332 | hy322332
            · have hs3223320 : InSquare (5/64) (25/64) (1/320) tau := by
                convert childLL hs322332 hx322332 hy322332 using 1 <;> norm_num
              rcases le_total tau.re (5/64 : ℝ) with hx3223320 | hx3223320
              · rcases le_total tau.im (25/64 : ℝ) with hy3223320 | hy3223320
                · have hs32233200 : InSquare (49/640) (249/640) (1/640) tau := by
                    convert childLL hs3223320 hx3223320 hy3223320 using 1 <;> norm_num
                  exact Batch0459.cell3675.sound htau (by
                    simp only [Batch0459.cell3675, Batch0459.tau3675, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32233200 (by positivity) using 1 <;> norm_num)
                · have hs32233202 : InSquare (49/640) (251/640) (1/640) tau := by
                    convert childUL hs3223320 hx3223320 hy3223320 using 1 <;> norm_num
                  exact Batch0459.cell3677.sound htau (by
                    simp only [Batch0459.cell3677, Batch0459.tau3677, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32233202 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (25/64 : ℝ) with hy3223320 | hy3223320
                · have hs32233201 : InSquare (51/640) (249/640) (1/640) tau := by
                    convert childLR hs3223320 hx3223320 hy3223320 using 1 <;> norm_num
                  exact Batch0459.cell3676.sound htau (by
                    simp only [Batch0459.cell3676, Batch0459.tau3676, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32233201 (by positivity) using 1 <;> norm_num)
                · have hs32233203 : InSquare (51/640) (251/640) (1/640) tau := by
                    convert childUR hs3223320 hx3223320 hy3223320 using 1 <;> norm_num
                  exact Batch0459.cell3678.sound htau (by
                    simp only [Batch0459.cell3678, Batch0459.tau3678, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32233203 (by positivity) using 1 <;> norm_num)
            · have hs3223322 : InSquare (5/64) (127/320) (1/320) tau := by
                convert childUL hs322332 hx322332 hy322332 using 1 <;> norm_num
              exact (outside_3223322 htau hs3223322).elim
          · rcases le_total tau.im (63/160 : ℝ) with hy322332 | hy322332
            · have hs3223321 : InSquare (27/320) (25/64) (1/320) tau := by
                convert childLR hs322332 hx322332 hy322332 using 1 <;> norm_num
              rcases le_total tau.re (27/320 : ℝ) with hx3223321 | hx3223321
              · rcases le_total tau.im (25/64 : ℝ) with hy3223321 | hy3223321
                · have hs32233210 : InSquare (53/640) (249/640) (1/640) tau := by
                    convert childLL hs3223321 hx3223321 hy3223321 using 1 <;> norm_num
                  exact Batch0459.cell3679.sound htau (by
                    simp only [Batch0459.cell3679, Batch0459.tau3679, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32233210 (by positivity) using 1 <;> norm_num)
                · have hs32233212 : InSquare (53/640) (251/640) (1/640) tau := by
                    convert childUL hs3223321 hx3223321 hy3223321 using 1 <;> norm_num
                  exact Batch0460.cell3681.sound htau (by
                    simp only [Batch0460.cell3681, Batch0460.tau3681, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32233212 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (25/64 : ℝ) with hy3223321 | hy3223321
                · have hs32233211 : InSquare (11/128) (249/640) (1/640) tau := by
                    convert childLR hs3223321 hx3223321 hy3223321 using 1 <;> norm_num
                  exact Batch0460.cell3680.sound htau (by
                    simp only [Batch0460.cell3680, Batch0460.tau3680, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32233211 (by positivity) using 1 <;> norm_num)
                · have hs32233213 : InSquare (11/128) (251/640) (1/640) tau := by
                    convert childUR hs3223321 hx3223321 hy3223321 using 1 <;> norm_num
                  exact Batch0460.cell3682.sound htau (by
                    simp only [Batch0460.cell3682, Batch0460.tau3682, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32233213 (by positivity) using 1 <;> norm_num)
            · have hs3223323 : InSquare (27/320) (127/320) (1/320) tau := by
                convert childUR hs322332 hx322332 hy322332 using 1 <;> norm_num
              exact (outside_3223323 htau hs3223323).elim
      · rcases le_total tau.im (31/80 : ℝ) with hy32233 | hy32233
        · have hs322331 : InSquare (3/32) (61/160) (1/160) tau := by
            convert childLR hs32233 hx32233 hy32233 using 1 <;> norm_num
          rcases le_total tau.re (3/32 : ℝ) with hx322331 | hx322331
          · rcases le_total tau.im (61/160 : ℝ) with hy322331 | hy322331
            · have hs3223310 : InSquare (29/320) (121/320) (1/320) tau := by
                convert childLL hs322331 hx322331 hy322331 using 1 <;> norm_num
              rcases le_total tau.re (29/320 : ℝ) with hx3223310 | hx3223310
              · rcases le_total tau.im (121/320 : ℝ) with hy3223310 | hy3223310
                · have hs32233100 : InSquare (57/640) (241/640) (1/640) tau := by
                    convert childLL hs3223310 hx3223310 hy3223310 using 1 <;> norm_num
                  exact Batch0457.cell3659.sound htau (by
                    simp only [Batch0457.cell3659, Batch0457.tau3659, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32233100 (by positivity) using 1 <;> norm_num)
                · have hs32233102 : InSquare (57/640) (243/640) (1/640) tau := by
                    convert childUL hs3223310 hx3223310 hy3223310 using 1 <;> norm_num
                  exact Batch0457.cell3661.sound htau (by
                    simp only [Batch0457.cell3661, Batch0457.tau3661, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32233102 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (121/320 : ℝ) with hy3223310 | hy3223310
                · have hs32233101 : InSquare (59/640) (241/640) (1/640) tau := by
                    convert childLR hs3223310 hx3223310 hy3223310 using 1 <;> norm_num
                  exact Batch0457.cell3660.sound htau (by
                    simp only [Batch0457.cell3660, Batch0457.tau3660, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32233101 (by positivity) using 1 <;> norm_num)
                · have hs32233103 : InSquare (59/640) (243/640) (1/640) tau := by
                    convert childUR hs3223310 hx3223310 hy3223310 using 1 <;> norm_num
                  exact Batch0457.cell3662.sound htau (by
                    simp only [Batch0457.cell3662, Batch0457.tau3662, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32233103 (by positivity) using 1 <;> norm_num)
            · have hs3223312 : InSquare (29/320) (123/320) (1/320) tau := by
                convert childUL hs322331 hx322331 hy322331 using 1 <;> norm_num
              rcases le_total tau.re (29/320 : ℝ) with hx3223312 | hx3223312
              · rcases le_total tau.im (123/320 : ℝ) with hy3223312 | hy3223312
                · have hs32233120 : InSquare (57/640) (49/128) (1/640) tau := by
                    convert childLL hs3223312 hx3223312 hy3223312 using 1 <;> norm_num
                  exact Batch0458.cell3667.sound htau (by
                    simp only [Batch0458.cell3667, Batch0458.tau3667, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32233120 (by positivity) using 1 <;> norm_num)
                · have hs32233122 : InSquare (57/640) (247/640) (1/640) tau := by
                    convert childUL hs3223312 hx3223312 hy3223312 using 1 <;> norm_num
                  exact Batch0458.cell3669.sound htau (by
                    simp only [Batch0458.cell3669, Batch0458.tau3669, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32233122 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (123/320 : ℝ) with hy3223312 | hy3223312
                · have hs32233121 : InSquare (59/640) (49/128) (1/640) tau := by
                    convert childLR hs3223312 hx3223312 hy3223312 using 1 <;> norm_num
                  exact Batch0458.cell3668.sound htau (by
                    simp only [Batch0458.cell3668, Batch0458.tau3668, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32233121 (by positivity) using 1 <;> norm_num)
                · have hs32233123 : InSquare (59/640) (247/640) (1/640) tau := by
                    convert childUR hs3223312 hx3223312 hy3223312 using 1 <;> norm_num
                  exact Batch0458.cell3670.sound htau (by
                    simp only [Batch0458.cell3670, Batch0458.tau3670, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32233123 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (61/160 : ℝ) with hy322331 | hy322331
            · have hs3223311 : InSquare (31/320) (121/320) (1/320) tau := by
                convert childLR hs322331 hx322331 hy322331 using 1 <;> norm_num
              rcases le_total tau.re (31/320 : ℝ) with hx3223311 | hx3223311
              · rcases le_total tau.im (121/320 : ℝ) with hy3223311 | hy3223311
                · have hs32233110 : InSquare (61/640) (241/640) (1/640) tau := by
                    convert childLL hs3223311 hx3223311 hy3223311 using 1 <;> norm_num
                  exact Batch0457.cell3663.sound htau (by
                    simp only [Batch0457.cell3663, Batch0457.tau3663, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32233110 (by positivity) using 1 <;> norm_num)
                · have hs32233112 : InSquare (61/640) (243/640) (1/640) tau := by
                    convert childUL hs3223311 hx3223311 hy3223311 using 1 <;> norm_num
                  exact Batch0458.cell3665.sound htau (by
                    simp only [Batch0458.cell3665, Batch0458.tau3665, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32233112 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (121/320 : ℝ) with hy3223311 | hy3223311
                · have hs32233111 : InSquare (63/640) (241/640) (1/640) tau := by
                    convert childLR hs3223311 hx3223311 hy3223311 using 1 <;> norm_num
                  exact Batch0458.cell3664.sound htau (by
                    simp only [Batch0458.cell3664, Batch0458.tau3664, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32233111 (by positivity) using 1 <;> norm_num)
                · have hs32233113 : InSquare (63/640) (243/640) (1/640) tau := by
                    convert childUR hs3223311 hx3223311 hy3223311 using 1 <;> norm_num
                  exact Batch0458.cell3666.sound htau (by
                    simp only [Batch0458.cell3666, Batch0458.tau3666, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32233113 (by positivity) using 1 <;> norm_num)
            · have hs3223313 : InSquare (31/320) (123/320) (1/320) tau := by
                convert childUR hs322331 hx322331 hy322331 using 1 <;> norm_num
              rcases le_total tau.re (31/320 : ℝ) with hx3223313 | hx3223313
              · rcases le_total tau.im (123/320 : ℝ) with hy3223313 | hy3223313
                · have hs32233130 : InSquare (61/640) (49/128) (1/640) tau := by
                    convert childLL hs3223313 hx3223313 hy3223313 using 1 <;> norm_num
                  exact Batch0458.cell3671.sound htau (by
                    simp only [Batch0458.cell3671, Batch0458.tau3671, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32233130 (by positivity) using 1 <;> norm_num)
                · have hs32233132 : InSquare (61/640) (247/640) (1/640) tau := by
                    convert childUL hs3223313 hx3223313 hy3223313 using 1 <;> norm_num
                  exact Batch0459.cell3673.sound htau (by
                    simp only [Batch0459.cell3673, Batch0459.tau3673, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32233132 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (123/320 : ℝ) with hy3223313 | hy3223313
                · have hs32233131 : InSquare (63/640) (49/128) (1/640) tau := by
                    convert childLR hs3223313 hx3223313 hy3223313 using 1 <;> norm_num
                  exact Batch0459.cell3672.sound htau (by
                    simp only [Batch0459.cell3672, Batch0459.tau3672, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32233131 (by positivity) using 1 <;> norm_num)
                · have hs32233133 : InSquare (63/640) (247/640) (1/640) tau := by
                    convert childUR hs3223313 hx3223313 hy3223313 using 1 <;> norm_num
                  exact Batch0459.cell3674.sound htau (by
                    simp only [Batch0459.cell3674, Batch0459.tau3674, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32233133 (by positivity) using 1 <;> norm_num)
        · have hs322333 : InSquare (3/32) (63/160) (1/160) tau := by
            convert childUR hs32233 hx32233 hy32233 using 1 <;> norm_num
          rcases le_total tau.re (3/32 : ℝ) with hx322333 | hx322333
          · rcases le_total tau.im (63/160 : ℝ) with hy322333 | hy322333
            · have hs3223330 : InSquare (29/320) (25/64) (1/320) tau := by
                convert childLL hs322333 hx322333 hy322333 using 1 <;> norm_num
              rcases le_total tau.re (29/320 : ℝ) with hx3223330 | hx3223330
              · rcases le_total tau.im (25/64 : ℝ) with hy3223330 | hy3223330
                · have hs32233300 : InSquare (57/640) (249/640) (1/640) tau := by
                    convert childLL hs3223330 hx3223330 hy3223330 using 1 <;> norm_num
                  exact Batch0460.cell3683.sound htau (by
                    simp only [Batch0460.cell3683, Batch0460.tau3683, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32233300 (by positivity) using 1 <;> norm_num)
                · have hs32233302 : InSquare (57/640) (251/640) (1/640) tau := by
                    convert childUL hs3223330 hx3223330 hy3223330 using 1 <;> norm_num
                  exact (outside_32233302 htau hs32233302).elim
              · rcases le_total tau.im (25/64 : ℝ) with hy3223330 | hy3223330
                · have hs32233301 : InSquare (59/640) (249/640) (1/640) tau := by
                    convert childLR hs3223330 hx3223330 hy3223330 using 1 <;> norm_num
                  exact Batch0460.cell3684.sound htau (by
                    simp only [Batch0460.cell3684, Batch0460.tau3684, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32233301 (by positivity) using 1 <;> norm_num)
                · have hs32233303 : InSquare (59/640) (251/640) (1/640) tau := by
                    convert childUR hs3223330 hx3223330 hy3223330 using 1 <;> norm_num
                  exact (outside_32233303 htau hs32233303).elim
            · have hs3223332 : InSquare (29/320) (127/320) (1/320) tau := by
                convert childUL hs322333 hx322333 hy322333 using 1 <;> norm_num
              exact (outside_3223332 htau hs3223332).elim
          · rcases le_total tau.im (63/160 : ℝ) with hy322333 | hy322333
            · have hs3223331 : InSquare (31/320) (25/64) (1/320) tau := by
                convert childLR hs322333 hx322333 hy322333 using 1 <;> norm_num
              rcases le_total tau.re (31/320 : ℝ) with hx3223331 | hx3223331
              · rcases le_total tau.im (25/64 : ℝ) with hy3223331 | hy3223331
                · have hs32233310 : InSquare (61/640) (249/640) (1/640) tau := by
                    convert childLL hs3223331 hx3223331 hy3223331 using 1 <;> norm_num
                  exact Batch0460.cell3685.sound htau (by
                    simp only [Batch0460.cell3685, Batch0460.tau3685, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32233310 (by positivity) using 1 <;> norm_num)
                · have hs32233312 : InSquare (61/640) (251/640) (1/640) tau := by
                    convert childUL hs3223331 hx3223331 hy3223331 using 1 <;> norm_num
                  exact (outside_32233312 htau hs32233312).elim
              · rcases le_total tau.im (25/64 : ℝ) with hy3223331 | hy3223331
                · have hs32233311 : InSquare (63/640) (249/640) (1/640) tau := by
                    convert childLR hs3223331 hx3223331 hy3223331 using 1 <;> norm_num
                  exact Batch0460.cell3686.sound htau (by
                    simp only [Batch0460.cell3686, Batch0460.tau3686, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32233311 (by positivity) using 1 <;> norm_num)
                · have hs32233313 : InSquare (63/640) (251/640) (1/640) tau := by
                    convert childUR hs3223331 hx3223331 hy3223331 using 1 <;> norm_num
                  exact (outside_32233313 htau hs32233313).elim
            · have hs3223333 : InSquare (31/320) (127/320) (1/320) tau := by
                convert childUR hs322333 hx322333 hy322333 using 1 <;> norm_num
              exact (outside_3223333 htau hs3223333).elim

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3223
