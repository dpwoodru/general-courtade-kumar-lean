import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0149
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0306
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0307
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0308
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0309
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0310
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0311

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3303

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

private theorem outside_330333 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (47/160) (47/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (23/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-23/80)]
  have himSq : (23/80 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-23/80)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_3303311 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (19/64) (89/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (47/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-47/160)]
  have himSq : (11/40 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-11/40)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_3303312 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (93/320) (91/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (23/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-23/80)]
  have himSq : (9/32 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-9/32)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_3303313 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (19/64) (91/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (47/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-47/160)]
  have himSq : (9/32 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-9/32)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_3303321 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (91/320) (93/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (9/32 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-9/32)]
  have himSq : (23/80 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-23/80)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_3303322 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (89/320) (19/64) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (11/40 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-11/40)]
  have himSq : (47/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-47/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_3303323 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (91/320) (19/64) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (9/32 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-9/32)]
  have himSq : (47/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-47/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (11/40) (11/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (11/40 : ℝ) with hx3303 | hx3303
  · rcases le_total tau.im (11/40 : ℝ) with hy3303 | hy3303
    · have hs33030 : InSquare (21/80) (21/80) (1/80) tau := by
        convert childLL hs hx3303 hy3303 using 1 <;> norm_num
      rcases le_total tau.re (21/80 : ℝ) with hx33030 | hx33030
      · rcases le_total tau.im (21/80 : ℝ) with hy33030 | hy33030
        · have hs330300 : InSquare (41/160) (41/160) (1/160) tau := by
            convert childLL hs33030 hx33030 hy33030 using 1 <;> norm_num
          exact Batch0149.cell1192.sound htau (by
            simp only [Batch0149.cell1192, Batch0149.tau1192, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs330300 (by positivity) using 1 <;> norm_num)
        · have hs330302 : InSquare (41/160) (43/160) (1/160) tau := by
            convert childUL hs33030 hx33030 hy33030 using 1 <;> norm_num
          rcases le_total tau.re (41/160 : ℝ) with hx330302 | hx330302
          · rcases le_total tau.im (43/160 : ℝ) with hy330302 | hy330302
            · have hs3303020 : InSquare (81/320) (17/64) (1/320) tau := by
                convert childLL hs330302 hx330302 hy330302 using 1 <;> norm_num
              exact Batch0306.cell2448.sound htau (by
                simp only [Batch0306.cell2448, Batch0306.tau2448, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3303020 (by positivity) using 1 <;> norm_num)
            · have hs3303022 : InSquare (81/320) (87/320) (1/320) tau := by
                convert childUL hs330302 hx330302 hy330302 using 1 <;> norm_num
              exact Batch0306.cell2450.sound htau (by
                simp only [Batch0306.cell2450, Batch0306.tau2450, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3303022 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (43/160 : ℝ) with hy330302 | hy330302
            · have hs3303021 : InSquare (83/320) (17/64) (1/320) tau := by
                convert childLR hs330302 hx330302 hy330302 using 1 <;> norm_num
              exact Batch0306.cell2449.sound htau (by
                simp only [Batch0306.cell2449, Batch0306.tau2449, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3303021 (by positivity) using 1 <;> norm_num)
            · have hs3303023 : InSquare (83/320) (87/320) (1/320) tau := by
                convert childUR hs330302 hx330302 hy330302 using 1 <;> norm_num
              exact Batch0306.cell2451.sound htau (by
                simp only [Batch0306.cell2451, Batch0306.tau2451, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3303023 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (21/80 : ℝ) with hy33030 | hy33030
        · have hs330301 : InSquare (43/160) (41/160) (1/160) tau := by
            convert childLR hs33030 hx33030 hy33030 using 1 <;> norm_num
          exact Batch0149.cell1193.sound htau (by
            simp only [Batch0149.cell1193, Batch0149.tau1193, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs330301 (by positivity) using 1 <;> norm_num)
        · have hs330303 : InSquare (43/160) (43/160) (1/160) tau := by
            convert childUR hs33030 hx33030 hy33030 using 1 <;> norm_num
          rcases le_total tau.re (43/160 : ℝ) with hx330303 | hx330303
          · rcases le_total tau.im (43/160 : ℝ) with hy330303 | hy330303
            · have hs3303030 : InSquare (17/64) (17/64) (1/320) tau := by
                convert childLL hs330303 hx330303 hy330303 using 1 <;> norm_num
              exact Batch0306.cell2452.sound htau (by
                simp only [Batch0306.cell2452, Batch0306.tau2452, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3303030 (by positivity) using 1 <;> norm_num)
            · have hs3303032 : InSquare (17/64) (87/320) (1/320) tau := by
                convert childUL hs330303 hx330303 hy330303 using 1 <;> norm_num
              exact Batch0306.cell2454.sound htau (by
                simp only [Batch0306.cell2454, Batch0306.tau2454, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3303032 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (43/160 : ℝ) with hy330303 | hy330303
            · have hs3303031 : InSquare (87/320) (17/64) (1/320) tau := by
                convert childLR hs330303 hx330303 hy330303 using 1 <;> norm_num
              exact Batch0306.cell2453.sound htau (by
                simp only [Batch0306.cell2453, Batch0306.tau2453, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3303031 (by positivity) using 1 <;> norm_num)
            · have hs3303033 : InSquare (87/320) (87/320) (1/320) tau := by
                convert childUR hs330303 hx330303 hy330303 using 1 <;> norm_num
              exact Batch0306.cell2455.sound htau (by
                simp only [Batch0306.cell2455, Batch0306.tau2455, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3303033 (by positivity) using 1 <;> norm_num)
    · have hs33032 : InSquare (21/80) (23/80) (1/80) tau := by
        convert childUL hs hx3303 hy3303 using 1 <;> norm_num
      rcases le_total tau.re (21/80 : ℝ) with hx33032 | hx33032
      · rcases le_total tau.im (23/80 : ℝ) with hy33032 | hy33032
        · have hs330320 : InSquare (41/160) (9/32) (1/160) tau := by
            convert childLL hs33032 hx33032 hy33032 using 1 <;> norm_num
          rcases le_total tau.re (41/160 : ℝ) with hx330320 | hx330320
          · rcases le_total tau.im (9/32 : ℝ) with hy330320 | hy330320
            · have hs3303200 : InSquare (81/320) (89/320) (1/320) tau := by
                convert childLL hs330320 hx330320 hy330320 using 1 <;> norm_num
              exact Batch0309.cell2472.sound htau (by
                simp only [Batch0309.cell2472, Batch0309.tau2472, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3303200 (by positivity) using 1 <;> norm_num)
            · have hs3303202 : InSquare (81/320) (91/320) (1/320) tau := by
                convert childUL hs330320 hx330320 hy330320 using 1 <;> norm_num
              exact Batch0309.cell2474.sound htau (by
                simp only [Batch0309.cell2474, Batch0309.tau2474, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3303202 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (9/32 : ℝ) with hy330320 | hy330320
            · have hs3303201 : InSquare (83/320) (89/320) (1/320) tau := by
                convert childLR hs330320 hx330320 hy330320 using 1 <;> norm_num
              exact Batch0309.cell2473.sound htau (by
                simp only [Batch0309.cell2473, Batch0309.tau2473, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3303201 (by positivity) using 1 <;> norm_num)
            · have hs3303203 : InSquare (83/320) (91/320) (1/320) tau := by
                convert childUR hs330320 hx330320 hy330320 using 1 <;> norm_num
              exact Batch0309.cell2475.sound htau (by
                simp only [Batch0309.cell2475, Batch0309.tau2475, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3303203 (by positivity) using 1 <;> norm_num)
        · have hs330322 : InSquare (41/160) (47/160) (1/160) tau := by
            convert childUL hs33032 hx33032 hy33032 using 1 <;> norm_num
          rcases le_total tau.re (41/160 : ℝ) with hx330322 | hx330322
          · rcases le_total tau.im (47/160 : ℝ) with hy330322 | hy330322
            · have hs3303220 : InSquare (81/320) (93/320) (1/320) tau := by
                convert childLL hs330322 hx330322 hy330322 using 1 <;> norm_num
              exact Batch0310.cell2480.sound htau (by
                simp only [Batch0310.cell2480, Batch0310.tau2480, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3303220 (by positivity) using 1 <;> norm_num)
            · have hs3303222 : InSquare (81/320) (19/64) (1/320) tau := by
                convert childUL hs330322 hx330322 hy330322 using 1 <;> norm_num
              exact Batch0310.cell2482.sound htau (by
                simp only [Batch0310.cell2482, Batch0310.tau2482, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3303222 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (47/160 : ℝ) with hy330322 | hy330322
            · have hs3303221 : InSquare (83/320) (93/320) (1/320) tau := by
                convert childLR hs330322 hx330322 hy330322 using 1 <;> norm_num
              exact Batch0310.cell2481.sound htau (by
                simp only [Batch0310.cell2481, Batch0310.tau2481, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3303221 (by positivity) using 1 <;> norm_num)
            · have hs3303223 : InSquare (83/320) (19/64) (1/320) tau := by
                convert childUR hs330322 hx330322 hy330322 using 1 <;> norm_num
              exact Batch0310.cell2483.sound htau (by
                simp only [Batch0310.cell2483, Batch0310.tau2483, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3303223 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (23/80 : ℝ) with hy33032 | hy33032
        · have hs330321 : InSquare (43/160) (9/32) (1/160) tau := by
            convert childLR hs33032 hx33032 hy33032 using 1 <;> norm_num
          rcases le_total tau.re (43/160 : ℝ) with hx330321 | hx330321
          · rcases le_total tau.im (9/32 : ℝ) with hy330321 | hy330321
            · have hs3303210 : InSquare (17/64) (89/320) (1/320) tau := by
                convert childLL hs330321 hx330321 hy330321 using 1 <;> norm_num
              exact Batch0309.cell2476.sound htau (by
                simp only [Batch0309.cell2476, Batch0309.tau2476, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3303210 (by positivity) using 1 <;> norm_num)
            · have hs3303212 : InSquare (17/64) (91/320) (1/320) tau := by
                convert childUL hs330321 hx330321 hy330321 using 1 <;> norm_num
              exact Batch0309.cell2478.sound htau (by
                simp only [Batch0309.cell2478, Batch0309.tau2478, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3303212 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (9/32 : ℝ) with hy330321 | hy330321
            · have hs3303211 : InSquare (87/320) (89/320) (1/320) tau := by
                convert childLR hs330321 hx330321 hy330321 using 1 <;> norm_num
              exact Batch0309.cell2477.sound htau (by
                simp only [Batch0309.cell2477, Batch0309.tau2477, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3303211 (by positivity) using 1 <;> norm_num)
            · have hs3303213 : InSquare (87/320) (91/320) (1/320) tau := by
                convert childUR hs330321 hx330321 hy330321 using 1 <;> norm_num
              exact Batch0309.cell2479.sound htau (by
                simp only [Batch0309.cell2479, Batch0309.tau2479, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3303213 (by positivity) using 1 <;> norm_num)
        · have hs330323 : InSquare (43/160) (47/160) (1/160) tau := by
            convert childUR hs33032 hx33032 hy33032 using 1 <;> norm_num
          rcases le_total tau.re (43/160 : ℝ) with hx330323 | hx330323
          · rcases le_total tau.im (47/160 : ℝ) with hy330323 | hy330323
            · have hs3303230 : InSquare (17/64) (93/320) (1/320) tau := by
                convert childLL hs330323 hx330323 hy330323 using 1 <;> norm_num
              exact Batch0310.cell2484.sound htau (by
                simp only [Batch0310.cell2484, Batch0310.tau2484, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3303230 (by positivity) using 1 <;> norm_num)
            · have hs3303232 : InSquare (17/64) (19/64) (1/320) tau := by
                convert childUL hs330323 hx330323 hy330323 using 1 <;> norm_num
              exact Batch0310.cell2486.sound htau (by
                simp only [Batch0310.cell2486, Batch0310.tau2486, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3303232 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (47/160 : ℝ) with hy330323 | hy330323
            · have hs3303231 : InSquare (87/320) (93/320) (1/320) tau := by
                convert childLR hs330323 hx330323 hy330323 using 1 <;> norm_num
              exact Batch0310.cell2485.sound htau (by
                simp only [Batch0310.cell2485, Batch0310.tau2485, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3303231 (by positivity) using 1 <;> norm_num)
            · have hs3303233 : InSquare (87/320) (19/64) (1/320) tau := by
                convert childUR hs330323 hx330323 hy330323 using 1 <;> norm_num
              exact Batch0310.cell2487.sound htau (by
                simp only [Batch0310.cell2487, Batch0310.tau2487, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3303233 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (11/40 : ℝ) with hy3303 | hy3303
    · have hs33031 : InSquare (23/80) (21/80) (1/80) tau := by
        convert childLR hs hx3303 hy3303 using 1 <;> norm_num
      rcases le_total tau.re (23/80 : ℝ) with hx33031 | hx33031
      · rcases le_total tau.im (21/80 : ℝ) with hy33031 | hy33031
        · have hs330310 : InSquare (9/32) (41/160) (1/160) tau := by
            convert childLL hs33031 hx33031 hy33031 using 1 <;> norm_num
          rcases le_total tau.re (9/32 : ℝ) with hx330310 | hx330310
          · rcases le_total tau.im (41/160 : ℝ) with hy330310 | hy330310
            · have hs3303100 : InSquare (89/320) (81/320) (1/320) tau := by
                convert childLL hs330310 hx330310 hy330310 using 1 <;> norm_num
              exact Batch0307.cell2456.sound htau (by
                simp only [Batch0307.cell2456, Batch0307.tau2456, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3303100 (by positivity) using 1 <;> norm_num)
            · have hs3303102 : InSquare (89/320) (83/320) (1/320) tau := by
                convert childUL hs330310 hx330310 hy330310 using 1 <;> norm_num
              exact Batch0307.cell2458.sound htau (by
                simp only [Batch0307.cell2458, Batch0307.tau2458, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3303102 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (41/160 : ℝ) with hy330310 | hy330310
            · have hs3303101 : InSquare (91/320) (81/320) (1/320) tau := by
                convert childLR hs330310 hx330310 hy330310 using 1 <;> norm_num
              exact Batch0307.cell2457.sound htau (by
                simp only [Batch0307.cell2457, Batch0307.tau2457, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3303101 (by positivity) using 1 <;> norm_num)
            · have hs3303103 : InSquare (91/320) (83/320) (1/320) tau := by
                convert childUR hs330310 hx330310 hy330310 using 1 <;> norm_num
              exact Batch0307.cell2459.sound htau (by
                simp only [Batch0307.cell2459, Batch0307.tau2459, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3303103 (by positivity) using 1 <;> norm_num)
        · have hs330312 : InSquare (9/32) (43/160) (1/160) tau := by
            convert childUL hs33031 hx33031 hy33031 using 1 <;> norm_num
          rcases le_total tau.re (9/32 : ℝ) with hx330312 | hx330312
          · rcases le_total tau.im (43/160 : ℝ) with hy330312 | hy330312
            · have hs3303120 : InSquare (89/320) (17/64) (1/320) tau := by
                convert childLL hs330312 hx330312 hy330312 using 1 <;> norm_num
              exact Batch0308.cell2464.sound htau (by
                simp only [Batch0308.cell2464, Batch0308.tau2464, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3303120 (by positivity) using 1 <;> norm_num)
            · have hs3303122 : InSquare (89/320) (87/320) (1/320) tau := by
                convert childUL hs330312 hx330312 hy330312 using 1 <;> norm_num
              exact Batch0308.cell2466.sound htau (by
                simp only [Batch0308.cell2466, Batch0308.tau2466, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3303122 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (43/160 : ℝ) with hy330312 | hy330312
            · have hs3303121 : InSquare (91/320) (17/64) (1/320) tau := by
                convert childLR hs330312 hx330312 hy330312 using 1 <;> norm_num
              exact Batch0308.cell2465.sound htau (by
                simp only [Batch0308.cell2465, Batch0308.tau2465, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3303121 (by positivity) using 1 <;> norm_num)
            · have hs3303123 : InSquare (91/320) (87/320) (1/320) tau := by
                convert childUR hs330312 hx330312 hy330312 using 1 <;> norm_num
              exact Batch0308.cell2467.sound htau (by
                simp only [Batch0308.cell2467, Batch0308.tau2467, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3303123 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (21/80 : ℝ) with hy33031 | hy33031
        · have hs330311 : InSquare (47/160) (41/160) (1/160) tau := by
            convert childLR hs33031 hx33031 hy33031 using 1 <;> norm_num
          rcases le_total tau.re (47/160 : ℝ) with hx330311 | hx330311
          · rcases le_total tau.im (41/160 : ℝ) with hy330311 | hy330311
            · have hs3303110 : InSquare (93/320) (81/320) (1/320) tau := by
                convert childLL hs330311 hx330311 hy330311 using 1 <;> norm_num
              exact Batch0307.cell2460.sound htau (by
                simp only [Batch0307.cell2460, Batch0307.tau2460, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3303110 (by positivity) using 1 <;> norm_num)
            · have hs3303112 : InSquare (93/320) (83/320) (1/320) tau := by
                convert childUL hs330311 hx330311 hy330311 using 1 <;> norm_num
              exact Batch0307.cell2462.sound htau (by
                simp only [Batch0307.cell2462, Batch0307.tau2462, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3303112 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (41/160 : ℝ) with hy330311 | hy330311
            · have hs3303111 : InSquare (19/64) (81/320) (1/320) tau := by
                convert childLR hs330311 hx330311 hy330311 using 1 <;> norm_num
              exact Batch0307.cell2461.sound htau (by
                simp only [Batch0307.cell2461, Batch0307.tau2461, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3303111 (by positivity) using 1 <;> norm_num)
            · have hs3303113 : InSquare (19/64) (83/320) (1/320) tau := by
                convert childUR hs330311 hx330311 hy330311 using 1 <;> norm_num
              exact Batch0307.cell2463.sound htau (by
                simp only [Batch0307.cell2463, Batch0307.tau2463, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3303113 (by positivity) using 1 <;> norm_num)
        · have hs330313 : InSquare (47/160) (43/160) (1/160) tau := by
            convert childUR hs33031 hx33031 hy33031 using 1 <;> norm_num
          rcases le_total tau.re (47/160 : ℝ) with hx330313 | hx330313
          · rcases le_total tau.im (43/160 : ℝ) with hy330313 | hy330313
            · have hs3303130 : InSquare (93/320) (17/64) (1/320) tau := by
                convert childLL hs330313 hx330313 hy330313 using 1 <;> norm_num
              exact Batch0308.cell2468.sound htau (by
                simp only [Batch0308.cell2468, Batch0308.tau2468, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3303130 (by positivity) using 1 <;> norm_num)
            · have hs3303132 : InSquare (93/320) (87/320) (1/320) tau := by
                convert childUL hs330313 hx330313 hy330313 using 1 <;> norm_num
              exact Batch0308.cell2470.sound htau (by
                simp only [Batch0308.cell2470, Batch0308.tau2470, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3303132 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (43/160 : ℝ) with hy330313 | hy330313
            · have hs3303131 : InSquare (19/64) (17/64) (1/320) tau := by
                convert childLR hs330313 hx330313 hy330313 using 1 <;> norm_num
              exact Batch0308.cell2469.sound htau (by
                simp only [Batch0308.cell2469, Batch0308.tau2469, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3303131 (by positivity) using 1 <;> norm_num)
            · have hs3303133 : InSquare (19/64) (87/320) (1/320) tau := by
                convert childUR hs330313 hx330313 hy330313 using 1 <;> norm_num
              exact Batch0308.cell2471.sound htau (by
                simp only [Batch0308.cell2471, Batch0308.tau2471, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3303133 (by positivity) using 1 <;> norm_num)
    · have hs33033 : InSquare (23/80) (23/80) (1/80) tau := by
        convert childUR hs hx3303 hy3303 using 1 <;> norm_num
      rcases le_total tau.re (23/80 : ℝ) with hx33033 | hx33033
      · rcases le_total tau.im (23/80 : ℝ) with hy33033 | hy33033
        · have hs330330 : InSquare (9/32) (9/32) (1/160) tau := by
            convert childLL hs33033 hx33033 hy33033 using 1 <;> norm_num
          rcases le_total tau.re (9/32 : ℝ) with hx330330 | hx330330
          · rcases le_total tau.im (9/32 : ℝ) with hy330330 | hy330330
            · have hs3303300 : InSquare (89/320) (89/320) (1/320) tau := by
                convert childLL hs330330 hx330330 hy330330 using 1 <;> norm_num
              exact Batch0311.cell2488.sound htau (by
                simp only [Batch0311.cell2488, Batch0311.tau2488, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3303300 (by positivity) using 1 <;> norm_num)
            · have hs3303302 : InSquare (89/320) (91/320) (1/320) tau := by
                convert childUL hs330330 hx330330 hy330330 using 1 <;> norm_num
              exact Batch0311.cell2490.sound htau (by
                simp only [Batch0311.cell2490, Batch0311.tau2490, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3303302 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (9/32 : ℝ) with hy330330 | hy330330
            · have hs3303301 : InSquare (91/320) (89/320) (1/320) tau := by
                convert childLR hs330330 hx330330 hy330330 using 1 <;> norm_num
              exact Batch0311.cell2489.sound htau (by
                simp only [Batch0311.cell2489, Batch0311.tau2489, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3303301 (by positivity) using 1 <;> norm_num)
            · have hs3303303 : InSquare (91/320) (91/320) (1/320) tau := by
                convert childUR hs330330 hx330330 hy330330 using 1 <;> norm_num
              exact Batch0311.cell2491.sound htau (by
                simp only [Batch0311.cell2491, Batch0311.tau2491, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3303303 (by positivity) using 1 <;> norm_num)
        · have hs330332 : InSquare (9/32) (47/160) (1/160) tau := by
            convert childUL hs33033 hx33033 hy33033 using 1 <;> norm_num
          rcases le_total tau.re (9/32 : ℝ) with hx330332 | hx330332
          · rcases le_total tau.im (47/160 : ℝ) with hy330332 | hy330332
            · have hs3303320 : InSquare (89/320) (93/320) (1/320) tau := by
                convert childLL hs330332 hx330332 hy330332 using 1 <;> norm_num
              exact Batch0311.cell2493.sound htau (by
                simp only [Batch0311.cell2493, Batch0311.tau2493, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3303320 (by positivity) using 1 <;> norm_num)
            · have hs3303322 : InSquare (89/320) (19/64) (1/320) tau := by
                convert childUL hs330332 hx330332 hy330332 using 1 <;> norm_num
              exact (outside_3303322 htau hs3303322).elim
          · rcases le_total tau.im (47/160 : ℝ) with hy330332 | hy330332
            · have hs3303321 : InSquare (91/320) (93/320) (1/320) tau := by
                convert childLR hs330332 hx330332 hy330332 using 1 <;> norm_num
              exact (outside_3303321 htau hs3303321).elim
            · have hs3303323 : InSquare (91/320) (19/64) (1/320) tau := by
                convert childUR hs330332 hx330332 hy330332 using 1 <;> norm_num
              exact (outside_3303323 htau hs3303323).elim
      · rcases le_total tau.im (23/80 : ℝ) with hy33033 | hy33033
        · have hs330331 : InSquare (47/160) (9/32) (1/160) tau := by
            convert childLR hs33033 hx33033 hy33033 using 1 <;> norm_num
          rcases le_total tau.re (47/160 : ℝ) with hx330331 | hx330331
          · rcases le_total tau.im (9/32 : ℝ) with hy330331 | hy330331
            · have hs3303310 : InSquare (93/320) (89/320) (1/320) tau := by
                convert childLL hs330331 hx330331 hy330331 using 1 <;> norm_num
              exact Batch0311.cell2492.sound htau (by
                simp only [Batch0311.cell2492, Batch0311.tau2492, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3303310 (by positivity) using 1 <;> norm_num)
            · have hs3303312 : InSquare (93/320) (91/320) (1/320) tau := by
                convert childUL hs330331 hx330331 hy330331 using 1 <;> norm_num
              exact (outside_3303312 htau hs3303312).elim
          · rcases le_total tau.im (9/32 : ℝ) with hy330331 | hy330331
            · have hs3303311 : InSquare (19/64) (89/320) (1/320) tau := by
                convert childLR hs330331 hx330331 hy330331 using 1 <;> norm_num
              exact (outside_3303311 htau hs3303311).elim
            · have hs3303313 : InSquare (19/64) (91/320) (1/320) tau := by
                convert childUR hs330331 hx330331 hy330331 using 1 <;> norm_num
              exact (outside_3303313 htau hs3303313).elim
        · have hs330333 : InSquare (47/160) (47/160) (1/160) tau := by
            convert childUR hs33033 hx33033 hy33033 using 1 <;> norm_num
          exact (outside_330333 htau hs330333).elim

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3303
