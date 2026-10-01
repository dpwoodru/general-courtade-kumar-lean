import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0268
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0269
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0270
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0271
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0272
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0420
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0421
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0422
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0423
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0424
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0425
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0426
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0427
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0428
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0429
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0430

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2332

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

private theorem outside_2332222 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-31/320) (127/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (3/32 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+3/32)]
  have himSq : (63/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-63/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_2332223 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-29/320) (127/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (7/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+7/80)]
  have himSq : (63/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-63/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_2332232 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-27/320) (127/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (13/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+13/160)]
  have himSq : (63/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-63/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_2332233 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-5/64) (127/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (3/40 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+3/40)]
  have himSq : (63/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-63/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_23322202 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-63/640) (251/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (31/320 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+31/320)]
  have himSq : (25/64 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-25/64)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_23322203 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-61/640) (251/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (3/32 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+3/32)]
  have himSq : (25/64 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-25/64)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_23322212 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-59/640) (251/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (29/320 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+29/320)]
  have himSq : (25/64 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-25/64)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_23322213 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-57/640) (251/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (7/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+7/80)]
  have himSq : (25/64 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-25/64)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_23323220 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-47/640) (253/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (23/320 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+23/320)]
  have himSq : (63/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-63/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_23323222 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-47/640) (51/128) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (23/320 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+23/320)]
  have himSq : (127/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-127/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_23323223 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-9/128) (51/128) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (11/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+11/160)]
  have himSq : (127/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-127/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_23323232 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-43/640) (51/128) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (21/320 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+21/320)]
  have himSq : (127/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-127/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_23323233 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-41/640) (51/128) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (1/16 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+1/16)]
  have himSq : (127/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-127/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_23323322 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-39/640) (51/128) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (19/320 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+19/320)]
  have himSq : (127/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-127/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_23323323 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-37/640) (51/128) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (9/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+9/160)]
  have himSq : (127/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-127/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_23323332 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-7/128) (51/128) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (17/320 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+17/320)]
  have himSq : (127/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-127/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_23323333 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-33/640) (51/128) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (1/20 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+1/20)]
  have himSq : (127/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-127/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-3/40) (3/8) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (-3/40 : ℝ) with hx2332 | hx2332
  · rcases le_total tau.im (3/8 : ℝ) with hy2332 | hy2332
    · have hs23320 : InSquare (-7/80) (29/80) (1/80) tau := by
        convert childLL hs hx2332 hy2332 using 1 <;> norm_num
      rcases le_total tau.re (-7/80 : ℝ) with hx23320 | hx23320
      · rcases le_total tau.im (29/80 : ℝ) with hy23320 | hy23320
        · have hs233200 : InSquare (-3/32) (57/160) (1/160) tau := by
            convert childLL hs23320 hx23320 hy23320 using 1 <;> norm_num
          rcases le_total tau.re (-3/32 : ℝ) with hx233200 | hx233200
          · rcases le_total tau.im (57/160 : ℝ) with hy233200 | hy233200
            · have hs2332000 : InSquare (-31/320) (113/320) (1/320) tau := by
                convert childLL hs233200 hx233200 hy233200 using 1 <;> norm_num
              exact Batch0268.cell2147.sound htau (by
                simp only [Batch0268.cell2147, Batch0268.tau2147, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2332000 (by positivity) using 1 <;> norm_num)
            · have hs2332002 : InSquare (-31/320) (23/64) (1/320) tau := by
                convert childUL hs233200 hx233200 hy233200 using 1 <;> norm_num
              exact Batch0268.cell2149.sound htau (by
                simp only [Batch0268.cell2149, Batch0268.tau2149, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2332002 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (57/160 : ℝ) with hy233200 | hy233200
            · have hs2332001 : InSquare (-29/320) (113/320) (1/320) tau := by
                convert childLR hs233200 hx233200 hy233200 using 1 <;> norm_num
              exact Batch0268.cell2148.sound htau (by
                simp only [Batch0268.cell2148, Batch0268.tau2148, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2332001 (by positivity) using 1 <;> norm_num)
            · have hs2332003 : InSquare (-29/320) (23/64) (1/320) tau := by
                convert childUR hs233200 hx233200 hy233200 using 1 <;> norm_num
              exact Batch0268.cell2150.sound htau (by
                simp only [Batch0268.cell2150, Batch0268.tau2150, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2332003 (by positivity) using 1 <;> norm_num)
        · have hs233202 : InSquare (-3/32) (59/160) (1/160) tau := by
            convert childUL hs23320 hx23320 hy23320 using 1 <;> norm_num
          rcases le_total tau.re (-3/32 : ℝ) with hx233202 | hx233202
          · rcases le_total tau.im (59/160 : ℝ) with hy233202 | hy233202
            · have hs2332020 : InSquare (-31/320) (117/320) (1/320) tau := by
                convert childLL hs233202 hx233202 hy233202 using 1 <;> norm_num
              exact Batch0269.cell2155.sound htau (by
                simp only [Batch0269.cell2155, Batch0269.tau2155, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2332020 (by positivity) using 1 <;> norm_num)
            · have hs2332022 : InSquare (-31/320) (119/320) (1/320) tau := by
                convert childUL hs233202 hx233202 hy233202 using 1 <;> norm_num
              exact Batch0269.cell2157.sound htau (by
                simp only [Batch0269.cell2157, Batch0269.tau2157, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2332022 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (59/160 : ℝ) with hy233202 | hy233202
            · have hs2332021 : InSquare (-29/320) (117/320) (1/320) tau := by
                convert childLR hs233202 hx233202 hy233202 using 1 <;> norm_num
              exact Batch0269.cell2156.sound htau (by
                simp only [Batch0269.cell2156, Batch0269.tau2156, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2332021 (by positivity) using 1 <;> norm_num)
            · have hs2332023 : InSquare (-29/320) (119/320) (1/320) tau := by
                convert childUR hs233202 hx233202 hy233202 using 1 <;> norm_num
              exact Batch0269.cell2158.sound htau (by
                simp only [Batch0269.cell2158, Batch0269.tau2158, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2332023 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (29/80 : ℝ) with hy23320 | hy23320
        · have hs233201 : InSquare (-13/160) (57/160) (1/160) tau := by
            convert childLR hs23320 hx23320 hy23320 using 1 <;> norm_num
          rcases le_total tau.re (-13/160 : ℝ) with hx233201 | hx233201
          · rcases le_total tau.im (57/160 : ℝ) with hy233201 | hy233201
            · have hs2332010 : InSquare (-27/320) (113/320) (1/320) tau := by
                convert childLL hs233201 hx233201 hy233201 using 1 <;> norm_num
              exact Batch0268.cell2151.sound htau (by
                simp only [Batch0268.cell2151, Batch0268.tau2151, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2332010 (by positivity) using 1 <;> norm_num)
            · have hs2332012 : InSquare (-27/320) (23/64) (1/320) tau := by
                convert childUL hs233201 hx233201 hy233201 using 1 <;> norm_num
              exact Batch0269.cell2153.sound htau (by
                simp only [Batch0269.cell2153, Batch0269.tau2153, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2332012 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (57/160 : ℝ) with hy233201 | hy233201
            · have hs2332011 : InSquare (-5/64) (113/320) (1/320) tau := by
                convert childLR hs233201 hx233201 hy233201 using 1 <;> norm_num
              exact Batch0269.cell2152.sound htau (by
                simp only [Batch0269.cell2152, Batch0269.tau2152, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2332011 (by positivity) using 1 <;> norm_num)
            · have hs2332013 : InSquare (-5/64) (23/64) (1/320) tau := by
                convert childUR hs233201 hx233201 hy233201 using 1 <;> norm_num
              exact Batch0269.cell2154.sound htau (by
                simp only [Batch0269.cell2154, Batch0269.tau2154, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2332013 (by positivity) using 1 <;> norm_num)
        · have hs233203 : InSquare (-13/160) (59/160) (1/160) tau := by
            convert childUR hs23320 hx23320 hy23320 using 1 <;> norm_num
          rcases le_total tau.re (-13/160 : ℝ) with hx233203 | hx233203
          · rcases le_total tau.im (59/160 : ℝ) with hy233203 | hy233203
            · have hs2332030 : InSquare (-27/320) (117/320) (1/320) tau := by
                convert childLL hs233203 hx233203 hy233203 using 1 <;> norm_num
              exact Batch0269.cell2159.sound htau (by
                simp only [Batch0269.cell2159, Batch0269.tau2159, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2332030 (by positivity) using 1 <;> norm_num)
            · have hs2332032 : InSquare (-27/320) (119/320) (1/320) tau := by
                convert childUL hs233203 hx233203 hy233203 using 1 <;> norm_num
              exact Batch0270.cell2161.sound htau (by
                simp only [Batch0270.cell2161, Batch0270.tau2161, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2332032 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (59/160 : ℝ) with hy233203 | hy233203
            · have hs2332031 : InSquare (-5/64) (117/320) (1/320) tau := by
                convert childLR hs233203 hx233203 hy233203 using 1 <;> norm_num
              exact Batch0270.cell2160.sound htau (by
                simp only [Batch0270.cell2160, Batch0270.tau2160, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2332031 (by positivity) using 1 <;> norm_num)
            · have hs2332033 : InSquare (-5/64) (119/320) (1/320) tau := by
                convert childUR hs233203 hx233203 hy233203 using 1 <;> norm_num
              exact Batch0270.cell2162.sound htau (by
                simp only [Batch0270.cell2162, Batch0270.tau2162, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2332033 (by positivity) using 1 <;> norm_num)
    · have hs23322 : InSquare (-7/80) (31/80) (1/80) tau := by
        convert childUL hs hx2332 hy2332 using 1 <;> norm_num
      rcases le_total tau.re (-7/80 : ℝ) with hx23322 | hx23322
      · rcases le_total tau.im (31/80 : ℝ) with hy23322 | hy23322
        · have hs233220 : InSquare (-3/32) (61/160) (1/160) tau := by
            convert childLL hs23322 hx23322 hy23322 using 1 <;> norm_num
          rcases le_total tau.re (-3/32 : ℝ) with hx233220 | hx233220
          · rcases le_total tau.im (61/160 : ℝ) with hy233220 | hy233220
            · have hs2332200 : InSquare (-31/320) (121/320) (1/320) tau := by
                convert childLL hs233220 hx233220 hy233220 using 1 <;> norm_num
              rcases le_total tau.re (-31/320 : ℝ) with hx2332200 | hx2332200
              · rcases le_total tau.im (121/320 : ℝ) with hy2332200 | hy2332200
                · have hs23322000 : InSquare (-63/640) (241/640) (1/640) tau := by
                    convert childLL hs2332200 hx2332200 hy2332200 using 1 <;> norm_num
                  exact Batch0420.cell3361.sound htau (by
                    simp only [Batch0420.cell3361, Batch0420.tau3361, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23322000 (by positivity) using 1 <;> norm_num)
                · have hs23322002 : InSquare (-63/640) (243/640) (1/640) tau := by
                    convert childUL hs2332200 hx2332200 hy2332200 using 1 <;> norm_num
                  exact Batch0420.cell3363.sound htau (by
                    simp only [Batch0420.cell3363, Batch0420.tau3363, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23322002 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (121/320 : ℝ) with hy2332200 | hy2332200
                · have hs23322001 : InSquare (-61/640) (241/640) (1/640) tau := by
                    convert childLR hs2332200 hx2332200 hy2332200 using 1 <;> norm_num
                  exact Batch0420.cell3362.sound htau (by
                    simp only [Batch0420.cell3362, Batch0420.tau3362, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23322001 (by positivity) using 1 <;> norm_num)
                · have hs23322003 : InSquare (-61/640) (243/640) (1/640) tau := by
                    convert childUR hs2332200 hx2332200 hy2332200 using 1 <;> norm_num
                  exact Batch0420.cell3364.sound htau (by
                    simp only [Batch0420.cell3364, Batch0420.tau3364, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23322003 (by positivity) using 1 <;> norm_num)
            · have hs2332202 : InSquare (-31/320) (123/320) (1/320) tau := by
                convert childUL hs233220 hx233220 hy233220 using 1 <;> norm_num
              rcases le_total tau.re (-31/320 : ℝ) with hx2332202 | hx2332202
              · rcases le_total tau.im (123/320 : ℝ) with hy2332202 | hy2332202
                · have hs23322020 : InSquare (-63/640) (49/128) (1/640) tau := by
                    convert childLL hs2332202 hx2332202 hy2332202 using 1 <;> norm_num
                  exact Batch0421.cell3369.sound htau (by
                    simp only [Batch0421.cell3369, Batch0421.tau3369, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23322020 (by positivity) using 1 <;> norm_num)
                · have hs23322022 : InSquare (-63/640) (247/640) (1/640) tau := by
                    convert childUL hs2332202 hx2332202 hy2332202 using 1 <;> norm_num
                  exact Batch0421.cell3371.sound htau (by
                    simp only [Batch0421.cell3371, Batch0421.tau3371, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23322022 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (123/320 : ℝ) with hy2332202 | hy2332202
                · have hs23322021 : InSquare (-61/640) (49/128) (1/640) tau := by
                    convert childLR hs2332202 hx2332202 hy2332202 using 1 <;> norm_num
                  exact Batch0421.cell3370.sound htau (by
                    simp only [Batch0421.cell3370, Batch0421.tau3370, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23322021 (by positivity) using 1 <;> norm_num)
                · have hs23322023 : InSquare (-61/640) (247/640) (1/640) tau := by
                    convert childUR hs2332202 hx2332202 hy2332202 using 1 <;> norm_num
                  exact Batch0421.cell3372.sound htau (by
                    simp only [Batch0421.cell3372, Batch0421.tau3372, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23322023 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (61/160 : ℝ) with hy233220 | hy233220
            · have hs2332201 : InSquare (-29/320) (121/320) (1/320) tau := by
                convert childLR hs233220 hx233220 hy233220 using 1 <;> norm_num
              rcases le_total tau.re (-29/320 : ℝ) with hx2332201 | hx2332201
              · rcases le_total tau.im (121/320 : ℝ) with hy2332201 | hy2332201
                · have hs23322010 : InSquare (-59/640) (241/640) (1/640) tau := by
                    convert childLL hs2332201 hx2332201 hy2332201 using 1 <;> norm_num
                  exact Batch0420.cell3365.sound htau (by
                    simp only [Batch0420.cell3365, Batch0420.tau3365, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23322010 (by positivity) using 1 <;> norm_num)
                · have hs23322012 : InSquare (-59/640) (243/640) (1/640) tau := by
                    convert childUL hs2332201 hx2332201 hy2332201 using 1 <;> norm_num
                  exact Batch0420.cell3367.sound htau (by
                    simp only [Batch0420.cell3367, Batch0420.tau3367, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23322012 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (121/320 : ℝ) with hy2332201 | hy2332201
                · have hs23322011 : InSquare (-57/640) (241/640) (1/640) tau := by
                    convert childLR hs2332201 hx2332201 hy2332201 using 1 <;> norm_num
                  exact Batch0420.cell3366.sound htau (by
                    simp only [Batch0420.cell3366, Batch0420.tau3366, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23322011 (by positivity) using 1 <;> norm_num)
                · have hs23322013 : InSquare (-57/640) (243/640) (1/640) tau := by
                    convert childUR hs2332201 hx2332201 hy2332201 using 1 <;> norm_num
                  exact Batch0421.cell3368.sound htau (by
                    simp only [Batch0421.cell3368, Batch0421.tau3368, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23322013 (by positivity) using 1 <;> norm_num)
            · have hs2332203 : InSquare (-29/320) (123/320) (1/320) tau := by
                convert childUR hs233220 hx233220 hy233220 using 1 <;> norm_num
              rcases le_total tau.re (-29/320 : ℝ) with hx2332203 | hx2332203
              · rcases le_total tau.im (123/320 : ℝ) with hy2332203 | hy2332203
                · have hs23322030 : InSquare (-59/640) (49/128) (1/640) tau := by
                    convert childLL hs2332203 hx2332203 hy2332203 using 1 <;> norm_num
                  exact Batch0421.cell3373.sound htau (by
                    simp only [Batch0421.cell3373, Batch0421.tau3373, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23322030 (by positivity) using 1 <;> norm_num)
                · have hs23322032 : InSquare (-59/640) (247/640) (1/640) tau := by
                    convert childUL hs2332203 hx2332203 hy2332203 using 1 <;> norm_num
                  exact Batch0421.cell3375.sound htau (by
                    simp only [Batch0421.cell3375, Batch0421.tau3375, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23322032 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (123/320 : ℝ) with hy2332203 | hy2332203
                · have hs23322031 : InSquare (-57/640) (49/128) (1/640) tau := by
                    convert childLR hs2332203 hx2332203 hy2332203 using 1 <;> norm_num
                  exact Batch0421.cell3374.sound htau (by
                    simp only [Batch0421.cell3374, Batch0421.tau3374, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23322031 (by positivity) using 1 <;> norm_num)
                · have hs23322033 : InSquare (-57/640) (247/640) (1/640) tau := by
                    convert childUR hs2332203 hx2332203 hy2332203 using 1 <;> norm_num
                  exact Batch0422.cell3376.sound htau (by
                    simp only [Batch0422.cell3376, Batch0422.tau3376, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23322033 (by positivity) using 1 <;> norm_num)
        · have hs233222 : InSquare (-3/32) (63/160) (1/160) tau := by
            convert childUL hs23322 hx23322 hy23322 using 1 <;> norm_num
          rcases le_total tau.re (-3/32 : ℝ) with hx233222 | hx233222
          · rcases le_total tau.im (63/160 : ℝ) with hy233222 | hy233222
            · have hs2332220 : InSquare (-31/320) (25/64) (1/320) tau := by
                convert childLL hs233222 hx233222 hy233222 using 1 <;> norm_num
              rcases le_total tau.re (-31/320 : ℝ) with hx2332220 | hx2332220
              · rcases le_total tau.im (25/64 : ℝ) with hy2332220 | hy2332220
                · have hs23322200 : InSquare (-63/640) (249/640) (1/640) tau := by
                    convert childLL hs2332220 hx2332220 hy2332220 using 1 <;> norm_num
                  exact Batch0424.cell3393.sound htau (by
                    simp only [Batch0424.cell3393, Batch0424.tau3393, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23322200 (by positivity) using 1 <;> norm_num)
                · have hs23322202 : InSquare (-63/640) (251/640) (1/640) tau := by
                    convert childUL hs2332220 hx2332220 hy2332220 using 1 <;> norm_num
                  exact (outside_23322202 htau hs23322202).elim
              · rcases le_total tau.im (25/64 : ℝ) with hy2332220 | hy2332220
                · have hs23322201 : InSquare (-61/640) (249/640) (1/640) tau := by
                    convert childLR hs2332220 hx2332220 hy2332220 using 1 <;> norm_num
                  exact Batch0424.cell3394.sound htau (by
                    simp only [Batch0424.cell3394, Batch0424.tau3394, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23322201 (by positivity) using 1 <;> norm_num)
                · have hs23322203 : InSquare (-61/640) (251/640) (1/640) tau := by
                    convert childUR hs2332220 hx2332220 hy2332220 using 1 <;> norm_num
                  exact (outside_23322203 htau hs23322203).elim
            · have hs2332222 : InSquare (-31/320) (127/320) (1/320) tau := by
                convert childUL hs233222 hx233222 hy233222 using 1 <;> norm_num
              exact (outside_2332222 htau hs2332222).elim
          · rcases le_total tau.im (63/160 : ℝ) with hy233222 | hy233222
            · have hs2332221 : InSquare (-29/320) (25/64) (1/320) tau := by
                convert childLR hs233222 hx233222 hy233222 using 1 <;> norm_num
              rcases le_total tau.re (-29/320 : ℝ) with hx2332221 | hx2332221
              · rcases le_total tau.im (25/64 : ℝ) with hy2332221 | hy2332221
                · have hs23322210 : InSquare (-59/640) (249/640) (1/640) tau := by
                    convert childLL hs2332221 hx2332221 hy2332221 using 1 <;> norm_num
                  exact Batch0424.cell3395.sound htau (by
                    simp only [Batch0424.cell3395, Batch0424.tau3395, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23322210 (by positivity) using 1 <;> norm_num)
                · have hs23322212 : InSquare (-59/640) (251/640) (1/640) tau := by
                    convert childUL hs2332221 hx2332221 hy2332221 using 1 <;> norm_num
                  exact (outside_23322212 htau hs23322212).elim
              · rcases le_total tau.im (25/64 : ℝ) with hy2332221 | hy2332221
                · have hs23322211 : InSquare (-57/640) (249/640) (1/640) tau := by
                    convert childLR hs2332221 hx2332221 hy2332221 using 1 <;> norm_num
                  exact Batch0424.cell3396.sound htau (by
                    simp only [Batch0424.cell3396, Batch0424.tau3396, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23322211 (by positivity) using 1 <;> norm_num)
                · have hs23322213 : InSquare (-57/640) (251/640) (1/640) tau := by
                    convert childUR hs2332221 hx2332221 hy2332221 using 1 <;> norm_num
                  exact (outside_23322213 htau hs23322213).elim
            · have hs2332223 : InSquare (-29/320) (127/320) (1/320) tau := by
                convert childUR hs233222 hx233222 hy233222 using 1 <;> norm_num
              exact (outside_2332223 htau hs2332223).elim
      · rcases le_total tau.im (31/80 : ℝ) with hy23322 | hy23322
        · have hs233221 : InSquare (-13/160) (61/160) (1/160) tau := by
            convert childLR hs23322 hx23322 hy23322 using 1 <;> norm_num
          rcases le_total tau.re (-13/160 : ℝ) with hx233221 | hx233221
          · rcases le_total tau.im (61/160 : ℝ) with hy233221 | hy233221
            · have hs2332210 : InSquare (-27/320) (121/320) (1/320) tau := by
                convert childLL hs233221 hx233221 hy233221 using 1 <;> norm_num
              rcases le_total tau.re (-27/320 : ℝ) with hx2332210 | hx2332210
              · rcases le_total tau.im (121/320 : ℝ) with hy2332210 | hy2332210
                · have hs23322100 : InSquare (-11/128) (241/640) (1/640) tau := by
                    convert childLL hs2332210 hx2332210 hy2332210 using 1 <;> norm_num
                  exact Batch0422.cell3377.sound htau (by
                    simp only [Batch0422.cell3377, Batch0422.tau3377, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23322100 (by positivity) using 1 <;> norm_num)
                · have hs23322102 : InSquare (-11/128) (243/640) (1/640) tau := by
                    convert childUL hs2332210 hx2332210 hy2332210 using 1 <;> norm_num
                  exact Batch0422.cell3379.sound htau (by
                    simp only [Batch0422.cell3379, Batch0422.tau3379, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23322102 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (121/320 : ℝ) with hy2332210 | hy2332210
                · have hs23322101 : InSquare (-53/640) (241/640) (1/640) tau := by
                    convert childLR hs2332210 hx2332210 hy2332210 using 1 <;> norm_num
                  exact Batch0422.cell3378.sound htau (by
                    simp only [Batch0422.cell3378, Batch0422.tau3378, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23322101 (by positivity) using 1 <;> norm_num)
                · have hs23322103 : InSquare (-53/640) (243/640) (1/640) tau := by
                    convert childUR hs2332210 hx2332210 hy2332210 using 1 <;> norm_num
                  exact Batch0422.cell3380.sound htau (by
                    simp only [Batch0422.cell3380, Batch0422.tau3380, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23322103 (by positivity) using 1 <;> norm_num)
            · have hs2332212 : InSquare (-27/320) (123/320) (1/320) tau := by
                convert childUL hs233221 hx233221 hy233221 using 1 <;> norm_num
              rcases le_total tau.re (-27/320 : ℝ) with hx2332212 | hx2332212
              · rcases le_total tau.im (123/320 : ℝ) with hy2332212 | hy2332212
                · have hs23322120 : InSquare (-11/128) (49/128) (1/640) tau := by
                    convert childLL hs2332212 hx2332212 hy2332212 using 1 <;> norm_num
                  exact Batch0423.cell3385.sound htau (by
                    simp only [Batch0423.cell3385, Batch0423.tau3385, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23322120 (by positivity) using 1 <;> norm_num)
                · have hs23322122 : InSquare (-11/128) (247/640) (1/640) tau := by
                    convert childUL hs2332212 hx2332212 hy2332212 using 1 <;> norm_num
                  exact Batch0423.cell3387.sound htau (by
                    simp only [Batch0423.cell3387, Batch0423.tau3387, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23322122 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (123/320 : ℝ) with hy2332212 | hy2332212
                · have hs23322121 : InSquare (-53/640) (49/128) (1/640) tau := by
                    convert childLR hs2332212 hx2332212 hy2332212 using 1 <;> norm_num
                  exact Batch0423.cell3386.sound htau (by
                    simp only [Batch0423.cell3386, Batch0423.tau3386, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23322121 (by positivity) using 1 <;> norm_num)
                · have hs23322123 : InSquare (-53/640) (247/640) (1/640) tau := by
                    convert childUR hs2332212 hx2332212 hy2332212 using 1 <;> norm_num
                  exact Batch0423.cell3388.sound htau (by
                    simp only [Batch0423.cell3388, Batch0423.tau3388, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23322123 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (61/160 : ℝ) with hy233221 | hy233221
            · have hs2332211 : InSquare (-5/64) (121/320) (1/320) tau := by
                convert childLR hs233221 hx233221 hy233221 using 1 <;> norm_num
              rcases le_total tau.re (-5/64 : ℝ) with hx2332211 | hx2332211
              · rcases le_total tau.im (121/320 : ℝ) with hy2332211 | hy2332211
                · have hs23322110 : InSquare (-51/640) (241/640) (1/640) tau := by
                    convert childLL hs2332211 hx2332211 hy2332211 using 1 <;> norm_num
                  exact Batch0422.cell3381.sound htau (by
                    simp only [Batch0422.cell3381, Batch0422.tau3381, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23322110 (by positivity) using 1 <;> norm_num)
                · have hs23322112 : InSquare (-51/640) (243/640) (1/640) tau := by
                    convert childUL hs2332211 hx2332211 hy2332211 using 1 <;> norm_num
                  exact Batch0422.cell3383.sound htau (by
                    simp only [Batch0422.cell3383, Batch0422.tau3383, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23322112 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (121/320 : ℝ) with hy2332211 | hy2332211
                · have hs23322111 : InSquare (-49/640) (241/640) (1/640) tau := by
                    convert childLR hs2332211 hx2332211 hy2332211 using 1 <;> norm_num
                  exact Batch0422.cell3382.sound htau (by
                    simp only [Batch0422.cell3382, Batch0422.tau3382, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23322111 (by positivity) using 1 <;> norm_num)
                · have hs23322113 : InSquare (-49/640) (243/640) (1/640) tau := by
                    convert childUR hs2332211 hx2332211 hy2332211 using 1 <;> norm_num
                  exact Batch0423.cell3384.sound htau (by
                    simp only [Batch0423.cell3384, Batch0423.tau3384, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23322113 (by positivity) using 1 <;> norm_num)
            · have hs2332213 : InSquare (-5/64) (123/320) (1/320) tau := by
                convert childUR hs233221 hx233221 hy233221 using 1 <;> norm_num
              rcases le_total tau.re (-5/64 : ℝ) with hx2332213 | hx2332213
              · rcases le_total tau.im (123/320 : ℝ) with hy2332213 | hy2332213
                · have hs23322130 : InSquare (-51/640) (49/128) (1/640) tau := by
                    convert childLL hs2332213 hx2332213 hy2332213 using 1 <;> norm_num
                  exact Batch0423.cell3389.sound htau (by
                    simp only [Batch0423.cell3389, Batch0423.tau3389, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23322130 (by positivity) using 1 <;> norm_num)
                · have hs23322132 : InSquare (-51/640) (247/640) (1/640) tau := by
                    convert childUL hs2332213 hx2332213 hy2332213 using 1 <;> norm_num
                  exact Batch0423.cell3391.sound htau (by
                    simp only [Batch0423.cell3391, Batch0423.tau3391, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23322132 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (123/320 : ℝ) with hy2332213 | hy2332213
                · have hs23322131 : InSquare (-49/640) (49/128) (1/640) tau := by
                    convert childLR hs2332213 hx2332213 hy2332213 using 1 <;> norm_num
                  exact Batch0423.cell3390.sound htau (by
                    simp only [Batch0423.cell3390, Batch0423.tau3390, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23322131 (by positivity) using 1 <;> norm_num)
                · have hs23322133 : InSquare (-49/640) (247/640) (1/640) tau := by
                    convert childUR hs2332213 hx2332213 hy2332213 using 1 <;> norm_num
                  exact Batch0424.cell3392.sound htau (by
                    simp only [Batch0424.cell3392, Batch0424.tau3392, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23322133 (by positivity) using 1 <;> norm_num)
        · have hs233223 : InSquare (-13/160) (63/160) (1/160) tau := by
            convert childUR hs23322 hx23322 hy23322 using 1 <;> norm_num
          rcases le_total tau.re (-13/160 : ℝ) with hx233223 | hx233223
          · rcases le_total tau.im (63/160 : ℝ) with hy233223 | hy233223
            · have hs2332230 : InSquare (-27/320) (25/64) (1/320) tau := by
                convert childLL hs233223 hx233223 hy233223 using 1 <;> norm_num
              rcases le_total tau.re (-27/320 : ℝ) with hx2332230 | hx2332230
              · rcases le_total tau.im (25/64 : ℝ) with hy2332230 | hy2332230
                · have hs23322300 : InSquare (-11/128) (249/640) (1/640) tau := by
                    convert childLL hs2332230 hx2332230 hy2332230 using 1 <;> norm_num
                  exact Batch0424.cell3397.sound htau (by
                    simp only [Batch0424.cell3397, Batch0424.tau3397, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23322300 (by positivity) using 1 <;> norm_num)
                · have hs23322302 : InSquare (-11/128) (251/640) (1/640) tau := by
                    convert childUL hs2332230 hx2332230 hy2332230 using 1 <;> norm_num
                  exact Batch0424.cell3399.sound htau (by
                    simp only [Batch0424.cell3399, Batch0424.tau3399, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23322302 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (25/64 : ℝ) with hy2332230 | hy2332230
                · have hs23322301 : InSquare (-53/640) (249/640) (1/640) tau := by
                    convert childLR hs2332230 hx2332230 hy2332230 using 1 <;> norm_num
                  exact Batch0424.cell3398.sound htau (by
                    simp only [Batch0424.cell3398, Batch0424.tau3398, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23322301 (by positivity) using 1 <;> norm_num)
                · have hs23322303 : InSquare (-53/640) (251/640) (1/640) tau := by
                    convert childUR hs2332230 hx2332230 hy2332230 using 1 <;> norm_num
                  exact Batch0425.cell3400.sound htau (by
                    simp only [Batch0425.cell3400, Batch0425.tau3400, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23322303 (by positivity) using 1 <;> norm_num)
            · have hs2332232 : InSquare (-27/320) (127/320) (1/320) tau := by
                convert childUL hs233223 hx233223 hy233223 using 1 <;> norm_num
              exact (outside_2332232 htau hs2332232).elim
          · rcases le_total tau.im (63/160 : ℝ) with hy233223 | hy233223
            · have hs2332231 : InSquare (-5/64) (25/64) (1/320) tau := by
                convert childLR hs233223 hx233223 hy233223 using 1 <;> norm_num
              rcases le_total tau.re (-5/64 : ℝ) with hx2332231 | hx2332231
              · rcases le_total tau.im (25/64 : ℝ) with hy2332231 | hy2332231
                · have hs23322310 : InSquare (-51/640) (249/640) (1/640) tau := by
                    convert childLL hs2332231 hx2332231 hy2332231 using 1 <;> norm_num
                  exact Batch0425.cell3401.sound htau (by
                    simp only [Batch0425.cell3401, Batch0425.tau3401, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23322310 (by positivity) using 1 <;> norm_num)
                · have hs23322312 : InSquare (-51/640) (251/640) (1/640) tau := by
                    convert childUL hs2332231 hx2332231 hy2332231 using 1 <;> norm_num
                  exact Batch0425.cell3403.sound htau (by
                    simp only [Batch0425.cell3403, Batch0425.tau3403, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23322312 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (25/64 : ℝ) with hy2332231 | hy2332231
                · have hs23322311 : InSquare (-49/640) (249/640) (1/640) tau := by
                    convert childLR hs2332231 hx2332231 hy2332231 using 1 <;> norm_num
                  exact Batch0425.cell3402.sound htau (by
                    simp only [Batch0425.cell3402, Batch0425.tau3402, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23322311 (by positivity) using 1 <;> norm_num)
                · have hs23322313 : InSquare (-49/640) (251/640) (1/640) tau := by
                    convert childUR hs2332231 hx2332231 hy2332231 using 1 <;> norm_num
                  exact Batch0425.cell3404.sound htau (by
                    simp only [Batch0425.cell3404, Batch0425.tau3404, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23322313 (by positivity) using 1 <;> norm_num)
            · have hs2332233 : InSquare (-5/64) (127/320) (1/320) tau := by
                convert childUR hs233223 hx233223 hy233223 using 1 <;> norm_num
              exact (outside_2332233 htau hs2332233).elim
  · rcases le_total tau.im (3/8 : ℝ) with hy2332 | hy2332
    · have hs23321 : InSquare (-1/16) (29/80) (1/80) tau := by
        convert childLR hs hx2332 hy2332 using 1 <;> norm_num
      rcases le_total tau.re (-1/16 : ℝ) with hx23321 | hx23321
      · rcases le_total tau.im (29/80 : ℝ) with hy23321 | hy23321
        · have hs233210 : InSquare (-11/160) (57/160) (1/160) tau := by
            convert childLL hs23321 hx23321 hy23321 using 1 <;> norm_num
          rcases le_total tau.re (-11/160 : ℝ) with hx233210 | hx233210
          · rcases le_total tau.im (57/160 : ℝ) with hy233210 | hy233210
            · have hs2332100 : InSquare (-23/320) (113/320) (1/320) tau := by
                convert childLL hs233210 hx233210 hy233210 using 1 <;> norm_num
              exact Batch0270.cell2163.sound htau (by
                simp only [Batch0270.cell2163, Batch0270.tau2163, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2332100 (by positivity) using 1 <;> norm_num)
            · have hs2332102 : InSquare (-23/320) (23/64) (1/320) tau := by
                convert childUL hs233210 hx233210 hy233210 using 1 <;> norm_num
              exact Batch0270.cell2165.sound htau (by
                simp only [Batch0270.cell2165, Batch0270.tau2165, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2332102 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (57/160 : ℝ) with hy233210 | hy233210
            · have hs2332101 : InSquare (-21/320) (113/320) (1/320) tau := by
                convert childLR hs233210 hx233210 hy233210 using 1 <;> norm_num
              exact Batch0270.cell2164.sound htau (by
                simp only [Batch0270.cell2164, Batch0270.tau2164, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2332101 (by positivity) using 1 <;> norm_num)
            · have hs2332103 : InSquare (-21/320) (23/64) (1/320) tau := by
                convert childUR hs233210 hx233210 hy233210 using 1 <;> norm_num
              exact Batch0270.cell2166.sound htau (by
                simp only [Batch0270.cell2166, Batch0270.tau2166, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2332103 (by positivity) using 1 <;> norm_num)
        · have hs233212 : InSquare (-11/160) (59/160) (1/160) tau := by
            convert childUL hs23321 hx23321 hy23321 using 1 <;> norm_num
          rcases le_total tau.re (-11/160 : ℝ) with hx233212 | hx233212
          · rcases le_total tau.im (59/160 : ℝ) with hy233212 | hy233212
            · have hs2332120 : InSquare (-23/320) (117/320) (1/320) tau := by
                convert childLL hs233212 hx233212 hy233212 using 1 <;> norm_num
              exact Batch0271.cell2171.sound htau (by
                simp only [Batch0271.cell2171, Batch0271.tau2171, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2332120 (by positivity) using 1 <;> norm_num)
            · have hs2332122 : InSquare (-23/320) (119/320) (1/320) tau := by
                convert childUL hs233212 hx233212 hy233212 using 1 <;> norm_num
              exact Batch0271.cell2173.sound htau (by
                simp only [Batch0271.cell2173, Batch0271.tau2173, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2332122 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (59/160 : ℝ) with hy233212 | hy233212
            · have hs2332121 : InSquare (-21/320) (117/320) (1/320) tau := by
                convert childLR hs233212 hx233212 hy233212 using 1 <;> norm_num
              exact Batch0271.cell2172.sound htau (by
                simp only [Batch0271.cell2172, Batch0271.tau2172, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2332121 (by positivity) using 1 <;> norm_num)
            · have hs2332123 : InSquare (-21/320) (119/320) (1/320) tau := by
                convert childUR hs233212 hx233212 hy233212 using 1 <;> norm_num
              exact Batch0271.cell2174.sound htau (by
                simp only [Batch0271.cell2174, Batch0271.tau2174, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2332123 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (29/80 : ℝ) with hy23321 | hy23321
        · have hs233211 : InSquare (-9/160) (57/160) (1/160) tau := by
            convert childLR hs23321 hx23321 hy23321 using 1 <;> norm_num
          rcases le_total tau.re (-9/160 : ℝ) with hx233211 | hx233211
          · rcases le_total tau.im (57/160 : ℝ) with hy233211 | hy233211
            · have hs2332110 : InSquare (-19/320) (113/320) (1/320) tau := by
                convert childLL hs233211 hx233211 hy233211 using 1 <;> norm_num
              exact Batch0270.cell2167.sound htau (by
                simp only [Batch0270.cell2167, Batch0270.tau2167, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2332110 (by positivity) using 1 <;> norm_num)
            · have hs2332112 : InSquare (-19/320) (23/64) (1/320) tau := by
                convert childUL hs233211 hx233211 hy233211 using 1 <;> norm_num
              exact Batch0271.cell2169.sound htau (by
                simp only [Batch0271.cell2169, Batch0271.tau2169, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2332112 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (57/160 : ℝ) with hy233211 | hy233211
            · have hs2332111 : InSquare (-17/320) (113/320) (1/320) tau := by
                convert childLR hs233211 hx233211 hy233211 using 1 <;> norm_num
              exact Batch0271.cell2168.sound htau (by
                simp only [Batch0271.cell2168, Batch0271.tau2168, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2332111 (by positivity) using 1 <;> norm_num)
            · have hs2332113 : InSquare (-17/320) (23/64) (1/320) tau := by
                convert childUR hs233211 hx233211 hy233211 using 1 <;> norm_num
              exact Batch0271.cell2170.sound htau (by
                simp only [Batch0271.cell2170, Batch0271.tau2170, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2332113 (by positivity) using 1 <;> norm_num)
        · have hs233213 : InSquare (-9/160) (59/160) (1/160) tau := by
            convert childUR hs23321 hx23321 hy23321 using 1 <;> norm_num
          rcases le_total tau.re (-9/160 : ℝ) with hx233213 | hx233213
          · rcases le_total tau.im (59/160 : ℝ) with hy233213 | hy233213
            · have hs2332130 : InSquare (-19/320) (117/320) (1/320) tau := by
                convert childLL hs233213 hx233213 hy233213 using 1 <;> norm_num
              exact Batch0271.cell2175.sound htau (by
                simp only [Batch0271.cell2175, Batch0271.tau2175, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2332130 (by positivity) using 1 <;> norm_num)
            · have hs2332132 : InSquare (-19/320) (119/320) (1/320) tau := by
                convert childUL hs233213 hx233213 hy233213 using 1 <;> norm_num
              exact Batch0272.cell2177.sound htau (by
                simp only [Batch0272.cell2177, Batch0272.tau2177, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2332132 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (59/160 : ℝ) with hy233213 | hy233213
            · have hs2332131 : InSquare (-17/320) (117/320) (1/320) tau := by
                convert childLR hs233213 hx233213 hy233213 using 1 <;> norm_num
              exact Batch0272.cell2176.sound htau (by
                simp only [Batch0272.cell2176, Batch0272.tau2176, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2332131 (by positivity) using 1 <;> norm_num)
            · have hs2332133 : InSquare (-17/320) (119/320) (1/320) tau := by
                convert childUR hs233213 hx233213 hy233213 using 1 <;> norm_num
              exact Batch0272.cell2178.sound htau (by
                simp only [Batch0272.cell2178, Batch0272.tau2178, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2332133 (by positivity) using 1 <;> norm_num)
    · have hs23323 : InSquare (-1/16) (31/80) (1/80) tau := by
        convert childUR hs hx2332 hy2332 using 1 <;> norm_num
      rcases le_total tau.re (-1/16 : ℝ) with hx23323 | hx23323
      · rcases le_total tau.im (31/80 : ℝ) with hy23323 | hy23323
        · have hs233230 : InSquare (-11/160) (61/160) (1/160) tau := by
            convert childLL hs23323 hx23323 hy23323 using 1 <;> norm_num
          rcases le_total tau.re (-11/160 : ℝ) with hx233230 | hx233230
          · rcases le_total tau.im (61/160 : ℝ) with hy233230 | hy233230
            · have hs2332300 : InSquare (-23/320) (121/320) (1/320) tau := by
                convert childLL hs233230 hx233230 hy233230 using 1 <;> norm_num
              rcases le_total tau.re (-23/320 : ℝ) with hx2332300 | hx2332300
              · rcases le_total tau.im (121/320 : ℝ) with hy2332300 | hy2332300
                · have hs23323000 : InSquare (-47/640) (241/640) (1/640) tau := by
                    convert childLL hs2332300 hx2332300 hy2332300 using 1 <;> norm_num
                  exact Batch0425.cell3405.sound htau (by
                    simp only [Batch0425.cell3405, Batch0425.tau3405, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23323000 (by positivity) using 1 <;> norm_num)
                · have hs23323002 : InSquare (-47/640) (243/640) (1/640) tau := by
                    convert childUL hs2332300 hx2332300 hy2332300 using 1 <;> norm_num
                  exact Batch0425.cell3407.sound htau (by
                    simp only [Batch0425.cell3407, Batch0425.tau3407, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23323002 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (121/320 : ℝ) with hy2332300 | hy2332300
                · have hs23323001 : InSquare (-9/128) (241/640) (1/640) tau := by
                    convert childLR hs2332300 hx2332300 hy2332300 using 1 <;> norm_num
                  exact Batch0425.cell3406.sound htau (by
                    simp only [Batch0425.cell3406, Batch0425.tau3406, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23323001 (by positivity) using 1 <;> norm_num)
                · have hs23323003 : InSquare (-9/128) (243/640) (1/640) tau := by
                    convert childUR hs2332300 hx2332300 hy2332300 using 1 <;> norm_num
                  exact Batch0426.cell3408.sound htau (by
                    simp only [Batch0426.cell3408, Batch0426.tau3408, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23323003 (by positivity) using 1 <;> norm_num)
            · have hs2332302 : InSquare (-23/320) (123/320) (1/320) tau := by
                convert childUL hs233230 hx233230 hy233230 using 1 <;> norm_num
              rcases le_total tau.re (-23/320 : ℝ) with hx2332302 | hx2332302
              · rcases le_total tau.im (123/320 : ℝ) with hy2332302 | hy2332302
                · have hs23323020 : InSquare (-47/640) (49/128) (1/640) tau := by
                    convert childLL hs2332302 hx2332302 hy2332302 using 1 <;> norm_num
                  exact Batch0426.cell3409.sound htau (by
                    simp only [Batch0426.cell3409, Batch0426.tau3409, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23323020 (by positivity) using 1 <;> norm_num)
                · have hs23323022 : InSquare (-47/640) (247/640) (1/640) tau := by
                    convert childUL hs2332302 hx2332302 hy2332302 using 1 <;> norm_num
                  exact Batch0426.cell3411.sound htau (by
                    simp only [Batch0426.cell3411, Batch0426.tau3411, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23323022 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (123/320 : ℝ) with hy2332302 | hy2332302
                · have hs23323021 : InSquare (-9/128) (49/128) (1/640) tau := by
                    convert childLR hs2332302 hx2332302 hy2332302 using 1 <;> norm_num
                  exact Batch0426.cell3410.sound htau (by
                    simp only [Batch0426.cell3410, Batch0426.tau3410, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23323021 (by positivity) using 1 <;> norm_num)
                · have hs23323023 : InSquare (-9/128) (247/640) (1/640) tau := by
                    convert childUR hs2332302 hx2332302 hy2332302 using 1 <;> norm_num
                  exact Batch0426.cell3412.sound htau (by
                    simp only [Batch0426.cell3412, Batch0426.tau3412, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23323023 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (61/160 : ℝ) with hy233230 | hy233230
            · have hs2332301 : InSquare (-21/320) (121/320) (1/320) tau := by
                convert childLR hs233230 hx233230 hy233230 using 1 <;> norm_num
              exact Batch0272.cell2179.sound htau (by
                simp only [Batch0272.cell2179, Batch0272.tau2179, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2332301 (by positivity) using 1 <;> norm_num)
            · have hs2332303 : InSquare (-21/320) (123/320) (1/320) tau := by
                convert childUR hs233230 hx233230 hy233230 using 1 <;> norm_num
              rcases le_total tau.re (-21/320 : ℝ) with hx2332303 | hx2332303
              · rcases le_total tau.im (123/320 : ℝ) with hy2332303 | hy2332303
                · have hs23323030 : InSquare (-43/640) (49/128) (1/640) tau := by
                    convert childLL hs2332303 hx2332303 hy2332303 using 1 <;> norm_num
                  exact Batch0426.cell3413.sound htau (by
                    simp only [Batch0426.cell3413, Batch0426.tau3413, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23323030 (by positivity) using 1 <;> norm_num)
                · have hs23323032 : InSquare (-43/640) (247/640) (1/640) tau := by
                    convert childUL hs2332303 hx2332303 hy2332303 using 1 <;> norm_num
                  exact Batch0426.cell3415.sound htau (by
                    simp only [Batch0426.cell3415, Batch0426.tau3415, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23323032 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (123/320 : ℝ) with hy2332303 | hy2332303
                · have hs23323031 : InSquare (-41/640) (49/128) (1/640) tau := by
                    convert childLR hs2332303 hx2332303 hy2332303 using 1 <;> norm_num
                  exact Batch0426.cell3414.sound htau (by
                    simp only [Batch0426.cell3414, Batch0426.tau3414, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23323031 (by positivity) using 1 <;> norm_num)
                · have hs23323033 : InSquare (-41/640) (247/640) (1/640) tau := by
                    convert childUR hs2332303 hx2332303 hy2332303 using 1 <;> norm_num
                  exact Batch0427.cell3416.sound htau (by
                    simp only [Batch0427.cell3416, Batch0427.tau3416, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23323033 (by positivity) using 1 <;> norm_num)
        · have hs233232 : InSquare (-11/160) (63/160) (1/160) tau := by
            convert childUL hs23323 hx23323 hy23323 using 1 <;> norm_num
          rcases le_total tau.re (-11/160 : ℝ) with hx233232 | hx233232
          · rcases le_total tau.im (63/160 : ℝ) with hy233232 | hy233232
            · have hs2332320 : InSquare (-23/320) (25/64) (1/320) tau := by
                convert childLL hs233232 hx233232 hy233232 using 1 <;> norm_num
              rcases le_total tau.re (-23/320 : ℝ) with hx2332320 | hx2332320
              · rcases le_total tau.im (25/64 : ℝ) with hy2332320 | hy2332320
                · have hs23323200 : InSquare (-47/640) (249/640) (1/640) tau := by
                    convert childLL hs2332320 hx2332320 hy2332320 using 1 <;> norm_num
                  exact Batch0428.cell3425.sound htau (by
                    simp only [Batch0428.cell3425, Batch0428.tau3425, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23323200 (by positivity) using 1 <;> norm_num)
                · have hs23323202 : InSquare (-47/640) (251/640) (1/640) tau := by
                    convert childUL hs2332320 hx2332320 hy2332320 using 1 <;> norm_num
                  exact Batch0428.cell3427.sound htau (by
                    simp only [Batch0428.cell3427, Batch0428.tau3427, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23323202 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (25/64 : ℝ) with hy2332320 | hy2332320
                · have hs23323201 : InSquare (-9/128) (249/640) (1/640) tau := by
                    convert childLR hs2332320 hx2332320 hy2332320 using 1 <;> norm_num
                  exact Batch0428.cell3426.sound htau (by
                    simp only [Batch0428.cell3426, Batch0428.tau3426, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23323201 (by positivity) using 1 <;> norm_num)
                · have hs23323203 : InSquare (-9/128) (251/640) (1/640) tau := by
                    convert childUR hs2332320 hx2332320 hy2332320 using 1 <;> norm_num
                  exact Batch0428.cell3428.sound htau (by
                    simp only [Batch0428.cell3428, Batch0428.tau3428, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23323203 (by positivity) using 1 <;> norm_num)
            · have hs2332322 : InSquare (-23/320) (127/320) (1/320) tau := by
                convert childUL hs233232 hx233232 hy233232 using 1 <;> norm_num
              rcases le_total tau.re (-23/320 : ℝ) with hx2332322 | hx2332322
              · rcases le_total tau.im (127/320 : ℝ) with hy2332322 | hy2332322
                · have hs23323220 : InSquare (-47/640) (253/640) (1/640) tau := by
                    convert childLL hs2332322 hx2332322 hy2332322 using 1 <;> norm_num
                  exact (outside_23323220 htau hs23323220).elim
                · have hs23323222 : InSquare (-47/640) (51/128) (1/640) tau := by
                    convert childUL hs2332322 hx2332322 hy2332322 using 1 <;> norm_num
                  exact (outside_23323222 htau hs23323222).elim
              · rcases le_total tau.im (127/320 : ℝ) with hy2332322 | hy2332322
                · have hs23323221 : InSquare (-9/128) (253/640) (1/640) tau := by
                    convert childLR hs2332322 hx2332322 hy2332322 using 1 <;> norm_num
                  exact Batch0429.cell3433.sound htau (by
                    simp only [Batch0429.cell3433, Batch0429.tau3433, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23323221 (by positivity) using 1 <;> norm_num)
                · have hs23323223 : InSquare (-9/128) (51/128) (1/640) tau := by
                    convert childUR hs2332322 hx2332322 hy2332322 using 1 <;> norm_num
                  exact (outside_23323223 htau hs23323223).elim
          · rcases le_total tau.im (63/160 : ℝ) with hy233232 | hy233232
            · have hs2332321 : InSquare (-21/320) (25/64) (1/320) tau := by
                convert childLR hs233232 hx233232 hy233232 using 1 <;> norm_num
              rcases le_total tau.re (-21/320 : ℝ) with hx2332321 | hx2332321
              · rcases le_total tau.im (25/64 : ℝ) with hy2332321 | hy2332321
                · have hs23323210 : InSquare (-43/640) (249/640) (1/640) tau := by
                    convert childLL hs2332321 hx2332321 hy2332321 using 1 <;> norm_num
                  exact Batch0428.cell3429.sound htau (by
                    simp only [Batch0428.cell3429, Batch0428.tau3429, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23323210 (by positivity) using 1 <;> norm_num)
                · have hs23323212 : InSquare (-43/640) (251/640) (1/640) tau := by
                    convert childUL hs2332321 hx2332321 hy2332321 using 1 <;> norm_num
                  exact Batch0428.cell3431.sound htau (by
                    simp only [Batch0428.cell3431, Batch0428.tau3431, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23323212 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (25/64 : ℝ) with hy2332321 | hy2332321
                · have hs23323211 : InSquare (-41/640) (249/640) (1/640) tau := by
                    convert childLR hs2332321 hx2332321 hy2332321 using 1 <;> norm_num
                  exact Batch0428.cell3430.sound htau (by
                    simp only [Batch0428.cell3430, Batch0428.tau3430, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23323211 (by positivity) using 1 <;> norm_num)
                · have hs23323213 : InSquare (-41/640) (251/640) (1/640) tau := by
                    convert childUR hs2332321 hx2332321 hy2332321 using 1 <;> norm_num
                  exact Batch0429.cell3432.sound htau (by
                    simp only [Batch0429.cell3432, Batch0429.tau3432, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23323213 (by positivity) using 1 <;> norm_num)
            · have hs2332323 : InSquare (-21/320) (127/320) (1/320) tau := by
                convert childUR hs233232 hx233232 hy233232 using 1 <;> norm_num
              rcases le_total tau.re (-21/320 : ℝ) with hx2332323 | hx2332323
              · rcases le_total tau.im (127/320 : ℝ) with hy2332323 | hy2332323
                · have hs23323230 : InSquare (-43/640) (253/640) (1/640) tau := by
                    convert childLL hs2332323 hx2332323 hy2332323 using 1 <;> norm_num
                  exact Batch0429.cell3434.sound htau (by
                    simp only [Batch0429.cell3434, Batch0429.tau3434, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23323230 (by positivity) using 1 <;> norm_num)
                · have hs23323232 : InSquare (-43/640) (51/128) (1/640) tau := by
                    convert childUL hs2332323 hx2332323 hy2332323 using 1 <;> norm_num
                  exact (outside_23323232 htau hs23323232).elim
              · rcases le_total tau.im (127/320 : ℝ) with hy2332323 | hy2332323
                · have hs23323231 : InSquare (-41/640) (253/640) (1/640) tau := by
                    convert childLR hs2332323 hx2332323 hy2332323 using 1 <;> norm_num
                  exact Batch0429.cell3435.sound htau (by
                    simp only [Batch0429.cell3435, Batch0429.tau3435, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23323231 (by positivity) using 1 <;> norm_num)
                · have hs23323233 : InSquare (-41/640) (51/128) (1/640) tau := by
                    convert childUR hs2332323 hx2332323 hy2332323 using 1 <;> norm_num
                  exact (outside_23323233 htau hs23323233).elim
      · rcases le_total tau.im (31/80 : ℝ) with hy23323 | hy23323
        · have hs233231 : InSquare (-9/160) (61/160) (1/160) tau := by
            convert childLR hs23323 hx23323 hy23323 using 1 <;> norm_num
          rcases le_total tau.re (-9/160 : ℝ) with hx233231 | hx233231
          · rcases le_total tau.im (61/160 : ℝ) with hy233231 | hy233231
            · have hs2332310 : InSquare (-19/320) (121/320) (1/320) tau := by
                convert childLL hs233231 hx233231 hy233231 using 1 <;> norm_num
              exact Batch0272.cell2180.sound htau (by
                simp only [Batch0272.cell2180, Batch0272.tau2180, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2332310 (by positivity) using 1 <;> norm_num)
            · have hs2332312 : InSquare (-19/320) (123/320) (1/320) tau := by
                convert childUL hs233231 hx233231 hy233231 using 1 <;> norm_num
              rcases le_total tau.re (-19/320 : ℝ) with hx2332312 | hx2332312
              · rcases le_total tau.im (123/320 : ℝ) with hy2332312 | hy2332312
                · have hs23323120 : InSquare (-39/640) (49/128) (1/640) tau := by
                    convert childLL hs2332312 hx2332312 hy2332312 using 1 <;> norm_num
                  exact Batch0427.cell3417.sound htau (by
                    simp only [Batch0427.cell3417, Batch0427.tau3417, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23323120 (by positivity) using 1 <;> norm_num)
                · have hs23323122 : InSquare (-39/640) (247/640) (1/640) tau := by
                    convert childUL hs2332312 hx2332312 hy2332312 using 1 <;> norm_num
                  exact Batch0427.cell3419.sound htau (by
                    simp only [Batch0427.cell3419, Batch0427.tau3419, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23323122 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (123/320 : ℝ) with hy2332312 | hy2332312
                · have hs23323121 : InSquare (-37/640) (49/128) (1/640) tau := by
                    convert childLR hs2332312 hx2332312 hy2332312 using 1 <;> norm_num
                  exact Batch0427.cell3418.sound htau (by
                    simp only [Batch0427.cell3418, Batch0427.tau3418, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23323121 (by positivity) using 1 <;> norm_num)
                · have hs23323123 : InSquare (-37/640) (247/640) (1/640) tau := by
                    convert childUR hs2332312 hx2332312 hy2332312 using 1 <;> norm_num
                  exact Batch0427.cell3420.sound htau (by
                    simp only [Batch0427.cell3420, Batch0427.tau3420, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23323123 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (61/160 : ℝ) with hy233231 | hy233231
            · have hs2332311 : InSquare (-17/320) (121/320) (1/320) tau := by
                convert childLR hs233231 hx233231 hy233231 using 1 <;> norm_num
              exact Batch0272.cell2181.sound htau (by
                simp only [Batch0272.cell2181, Batch0272.tau2181, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2332311 (by positivity) using 1 <;> norm_num)
            · have hs2332313 : InSquare (-17/320) (123/320) (1/320) tau := by
                convert childUR hs233231 hx233231 hy233231 using 1 <;> norm_num
              rcases le_total tau.re (-17/320 : ℝ) with hx2332313 | hx2332313
              · rcases le_total tau.im (123/320 : ℝ) with hy2332313 | hy2332313
                · have hs23323130 : InSquare (-7/128) (49/128) (1/640) tau := by
                    convert childLL hs2332313 hx2332313 hy2332313 using 1 <;> norm_num
                  exact Batch0427.cell3421.sound htau (by
                    simp only [Batch0427.cell3421, Batch0427.tau3421, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23323130 (by positivity) using 1 <;> norm_num)
                · have hs23323132 : InSquare (-7/128) (247/640) (1/640) tau := by
                    convert childUL hs2332313 hx2332313 hy2332313 using 1 <;> norm_num
                  exact Batch0427.cell3423.sound htau (by
                    simp only [Batch0427.cell3423, Batch0427.tau3423, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23323132 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (123/320 : ℝ) with hy2332313 | hy2332313
                · have hs23323131 : InSquare (-33/640) (49/128) (1/640) tau := by
                    convert childLR hs2332313 hx2332313 hy2332313 using 1 <;> norm_num
                  exact Batch0427.cell3422.sound htau (by
                    simp only [Batch0427.cell3422, Batch0427.tau3422, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23323131 (by positivity) using 1 <;> norm_num)
                · have hs23323133 : InSquare (-33/640) (247/640) (1/640) tau := by
                    convert childUR hs2332313 hx2332313 hy2332313 using 1 <;> norm_num
                  exact Batch0428.cell3424.sound htau (by
                    simp only [Batch0428.cell3424, Batch0428.tau3424, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23323133 (by positivity) using 1 <;> norm_num)
        · have hs233233 : InSquare (-9/160) (63/160) (1/160) tau := by
            convert childUR hs23323 hx23323 hy23323 using 1 <;> norm_num
          rcases le_total tau.re (-9/160 : ℝ) with hx233233 | hx233233
          · rcases le_total tau.im (63/160 : ℝ) with hy233233 | hy233233
            · have hs2332330 : InSquare (-19/320) (25/64) (1/320) tau := by
                convert childLL hs233233 hx233233 hy233233 using 1 <;> norm_num
              rcases le_total tau.re (-19/320 : ℝ) with hx2332330 | hx2332330
              · rcases le_total tau.im (25/64 : ℝ) with hy2332330 | hy2332330
                · have hs23323300 : InSquare (-39/640) (249/640) (1/640) tau := by
                    convert childLL hs2332330 hx2332330 hy2332330 using 1 <;> norm_num
                  exact Batch0429.cell3436.sound htau (by
                    simp only [Batch0429.cell3436, Batch0429.tau3436, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23323300 (by positivity) using 1 <;> norm_num)
                · have hs23323302 : InSquare (-39/640) (251/640) (1/640) tau := by
                    convert childUL hs2332330 hx2332330 hy2332330 using 1 <;> norm_num
                  exact Batch0429.cell3438.sound htau (by
                    simp only [Batch0429.cell3438, Batch0429.tau3438, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23323302 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (25/64 : ℝ) with hy2332330 | hy2332330
                · have hs23323301 : InSquare (-37/640) (249/640) (1/640) tau := by
                    convert childLR hs2332330 hx2332330 hy2332330 using 1 <;> norm_num
                  exact Batch0429.cell3437.sound htau (by
                    simp only [Batch0429.cell3437, Batch0429.tau3437, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23323301 (by positivity) using 1 <;> norm_num)
                · have hs23323303 : InSquare (-37/640) (251/640) (1/640) tau := by
                    convert childUR hs2332330 hx2332330 hy2332330 using 1 <;> norm_num
                  exact Batch0429.cell3439.sound htau (by
                    simp only [Batch0429.cell3439, Batch0429.tau3439, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23323303 (by positivity) using 1 <;> norm_num)
            · have hs2332332 : InSquare (-19/320) (127/320) (1/320) tau := by
                convert childUL hs233233 hx233233 hy233233 using 1 <;> norm_num
              rcases le_total tau.re (-19/320 : ℝ) with hx2332332 | hx2332332
              · rcases le_total tau.im (127/320 : ℝ) with hy2332332 | hy2332332
                · have hs23323320 : InSquare (-39/640) (253/640) (1/640) tau := by
                    convert childLL hs2332332 hx2332332 hy2332332 using 1 <;> norm_num
                  exact Batch0430.cell3444.sound htau (by
                    simp only [Batch0430.cell3444, Batch0430.tau3444, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23323320 (by positivity) using 1 <;> norm_num)
                · have hs23323322 : InSquare (-39/640) (51/128) (1/640) tau := by
                    convert childUL hs2332332 hx2332332 hy2332332 using 1 <;> norm_num
                  exact (outside_23323322 htau hs23323322).elim
              · rcases le_total tau.im (127/320 : ℝ) with hy2332332 | hy2332332
                · have hs23323321 : InSquare (-37/640) (253/640) (1/640) tau := by
                    convert childLR hs2332332 hx2332332 hy2332332 using 1 <;> norm_num
                  exact Batch0430.cell3445.sound htau (by
                    simp only [Batch0430.cell3445, Batch0430.tau3445, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23323321 (by positivity) using 1 <;> norm_num)
                · have hs23323323 : InSquare (-37/640) (51/128) (1/640) tau := by
                    convert childUR hs2332332 hx2332332 hy2332332 using 1 <;> norm_num
                  exact (outside_23323323 htau hs23323323).elim
          · rcases le_total tau.im (63/160 : ℝ) with hy233233 | hy233233
            · have hs2332331 : InSquare (-17/320) (25/64) (1/320) tau := by
                convert childLR hs233233 hx233233 hy233233 using 1 <;> norm_num
              rcases le_total tau.re (-17/320 : ℝ) with hx2332331 | hx2332331
              · rcases le_total tau.im (25/64 : ℝ) with hy2332331 | hy2332331
                · have hs23323310 : InSquare (-7/128) (249/640) (1/640) tau := by
                    convert childLL hs2332331 hx2332331 hy2332331 using 1 <;> norm_num
                  exact Batch0430.cell3440.sound htau (by
                    simp only [Batch0430.cell3440, Batch0430.tau3440, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23323310 (by positivity) using 1 <;> norm_num)
                · have hs23323312 : InSquare (-7/128) (251/640) (1/640) tau := by
                    convert childUL hs2332331 hx2332331 hy2332331 using 1 <;> norm_num
                  exact Batch0430.cell3442.sound htau (by
                    simp only [Batch0430.cell3442, Batch0430.tau3442, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23323312 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (25/64 : ℝ) with hy2332331 | hy2332331
                · have hs23323311 : InSquare (-33/640) (249/640) (1/640) tau := by
                    convert childLR hs2332331 hx2332331 hy2332331 using 1 <;> norm_num
                  exact Batch0430.cell3441.sound htau (by
                    simp only [Batch0430.cell3441, Batch0430.tau3441, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23323311 (by positivity) using 1 <;> norm_num)
                · have hs23323313 : InSquare (-33/640) (251/640) (1/640) tau := by
                    convert childUR hs2332331 hx2332331 hy2332331 using 1 <;> norm_num
                  exact Batch0430.cell3443.sound htau (by
                    simp only [Batch0430.cell3443, Batch0430.tau3443, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23323313 (by positivity) using 1 <;> norm_num)
            · have hs2332333 : InSquare (-17/320) (127/320) (1/320) tau := by
                convert childUR hs233233 hx233233 hy233233 using 1 <;> norm_num
              rcases le_total tau.re (-17/320 : ℝ) with hx2332333 | hx2332333
              · rcases le_total tau.im (127/320 : ℝ) with hy2332333 | hy2332333
                · have hs23323330 : InSquare (-7/128) (253/640) (1/640) tau := by
                    convert childLL hs2332333 hx2332333 hy2332333 using 1 <;> norm_num
                  exact Batch0430.cell3446.sound htau (by
                    simp only [Batch0430.cell3446, Batch0430.tau3446, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23323330 (by positivity) using 1 <;> norm_num)
                · have hs23323332 : InSquare (-7/128) (51/128) (1/640) tau := by
                    convert childUL hs2332333 hx2332333 hy2332333 using 1 <;> norm_num
                  exact (outside_23323332 htau hs23323332).elim
              · rcases le_total tau.im (127/320 : ℝ) with hy2332333 | hy2332333
                · have hs23323331 : InSquare (-33/640) (253/640) (1/640) tau := by
                    convert childLR hs2332333 hx2332333 hy2332333 using 1 <;> norm_num
                  exact Batch0430.cell3447.sound htau (by
                    simp only [Batch0430.cell3447, Batch0430.tau3447, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23323331 (by positivity) using 1 <;> norm_num)
                · have hs23323333 : InSquare (-33/640) (51/128) (1/640) tau := by
                    convert childUR hs2332333 hx2332333 hy2332333 using 1 <;> norm_num
                  exact (outside_23323333 htau hs23323333).elim

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2332
