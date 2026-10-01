import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0264
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0265
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0266
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0409
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0410
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0411
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0412
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0413
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0414
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0415
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0416
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0417
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0418
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0419
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0420

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2323

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

private theorem outside_232322 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-23/160) (63/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (11/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+11/80)]
  have himSq : (31/80 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-31/80)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_232323 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-21/160) (63/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (1/8 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+1/8)]
  have himSq : (31/80 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-31/80)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_232332 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-19/160) (63/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (9/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+9/80)]
  have himSq : (31/80 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-31/80)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_232333 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-17/160) (63/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (1/10 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+1/10)]
  have himSq : (31/80 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-31/80)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_2323200 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-47/320) (121/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (23/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+23/160)]
  have himSq : (3/8 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-3/8)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_2323202 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-47/320) (123/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (23/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+23/160)]
  have himSq : (61/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-61/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_2323203 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-9/64) (123/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (11/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+11/80)]
  have himSq : (61/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-61/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_2323212 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-43/320) (123/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (21/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+21/160)]
  have himSq : (61/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-61/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_2323213 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-41/320) (123/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (1/8 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+1/8)]
  have himSq : (61/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-61/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_23232010 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-91/640) (241/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (9/64 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+9/64)]
  have himSq : (3/8 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-3/8)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_23232012 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-91/640) (243/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (9/64 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+9/64)]
  have himSq : (121/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-121/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_23232013 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-89/640) (243/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (11/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+11/80)]
  have himSq : (121/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-121/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_23232102 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-87/640) (243/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (43/320 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+43/320)]
  have himSq : (121/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-121/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_23232103 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-17/128) (243/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (21/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+21/160)]
  have himSq : (121/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-121/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_23233020 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-79/640) (49/128) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (39/320 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+39/320)]
  have himSq : (61/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-61/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_23233022 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-79/640) (247/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (39/320 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+39/320)]
  have himSq : (123/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-123/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_23233023 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-77/640) (247/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (19/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+19/160)]
  have himSq : (123/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-123/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_23233032 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-15/128) (247/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (37/320 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+37/320)]
  have himSq : (123/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-123/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_23233033 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-73/640) (247/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (9/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+9/80)]
  have himSq : (123/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-123/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-1/8) (3/8) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (-1/8 : ℝ) with hx2323 | hx2323
  · rcases le_total tau.im (3/8 : ℝ) with hy2323 | hy2323
    · have hs23230 : InSquare (-11/80) (29/80) (1/80) tau := by
        convert childLL hs hx2323 hy2323 using 1 <;> norm_num
      rcases le_total tau.re (-11/80 : ℝ) with hx23230 | hx23230
      · rcases le_total tau.im (29/80 : ℝ) with hy23230 | hy23230
        · have hs232300 : InSquare (-23/160) (57/160) (1/160) tau := by
            convert childLL hs23230 hx23230 hy23230 using 1 <;> norm_num
          rcases le_total tau.re (-23/160 : ℝ) with hx232300 | hx232300
          · rcases le_total tau.im (57/160 : ℝ) with hy232300 | hy232300
            · have hs2323000 : InSquare (-47/320) (113/320) (1/320) tau := by
                convert childLL hs232300 hx232300 hy232300 using 1 <;> norm_num
              exact Batch0264.cell2116.sound htau (by
                simp only [Batch0264.cell2116, Batch0264.tau2116, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2323000 (by positivity) using 1 <;> norm_num)
            · have hs2323002 : InSquare (-47/320) (23/64) (1/320) tau := by
                convert childUL hs232300 hx232300 hy232300 using 1 <;> norm_num
              rcases le_total tau.re (-47/320 : ℝ) with hx2323002 | hx2323002
              · rcases le_total tau.im (23/64 : ℝ) with hy2323002 | hy2323002
                · have hs23230020 : InSquare (-19/128) (229/640) (1/640) tau := by
                    convert childLL hs2323002 hx2323002 hy2323002 using 1 <;> norm_num
                  exact Batch0409.cell3275.sound htau (by
                    simp only [Batch0409.cell3275, Batch0409.tau3275, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23230020 (by positivity) using 1 <;> norm_num)
                · have hs23230022 : InSquare (-19/128) (231/640) (1/640) tau := by
                    convert childUL hs2323002 hx2323002 hy2323002 using 1 <;> norm_num
                  exact Batch0409.cell3277.sound htau (by
                    simp only [Batch0409.cell3277, Batch0409.tau3277, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23230022 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (23/64 : ℝ) with hy2323002 | hy2323002
                · have hs23230021 : InSquare (-93/640) (229/640) (1/640) tau := by
                    convert childLR hs2323002 hx2323002 hy2323002 using 1 <;> norm_num
                  exact Batch0409.cell3276.sound htau (by
                    simp only [Batch0409.cell3276, Batch0409.tau3276, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23230021 (by positivity) using 1 <;> norm_num)
                · have hs23230023 : InSquare (-93/640) (231/640) (1/640) tau := by
                    convert childUR hs2323002 hx2323002 hy2323002 using 1 <;> norm_num
                  exact Batch0409.cell3278.sound htau (by
                    simp only [Batch0409.cell3278, Batch0409.tau3278, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23230023 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (57/160 : ℝ) with hy232300 | hy232300
            · have hs2323001 : InSquare (-9/64) (113/320) (1/320) tau := by
                convert childLR hs232300 hx232300 hy232300 using 1 <;> norm_num
              exact Batch0264.cell2117.sound htau (by
                simp only [Batch0264.cell2117, Batch0264.tau2117, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2323001 (by positivity) using 1 <;> norm_num)
            · have hs2323003 : InSquare (-9/64) (23/64) (1/320) tau := by
                convert childUR hs232300 hx232300 hy232300 using 1 <;> norm_num
              exact Batch0264.cell2118.sound htau (by
                simp only [Batch0264.cell2118, Batch0264.tau2118, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2323003 (by positivity) using 1 <;> norm_num)
        · have hs232302 : InSquare (-23/160) (59/160) (1/160) tau := by
            convert childUL hs23230 hx23230 hy23230 using 1 <;> norm_num
          rcases le_total tau.re (-23/160 : ℝ) with hx232302 | hx232302
          · rcases le_total tau.im (59/160 : ℝ) with hy232302 | hy232302
            · have hs2323020 : InSquare (-47/320) (117/320) (1/320) tau := by
                convert childLL hs232302 hx232302 hy232302 using 1 <;> norm_num
              rcases le_total tau.re (-47/320 : ℝ) with hx2323020 | hx2323020
              · rcases le_total tau.im (117/320 : ℝ) with hy2323020 | hy2323020
                · have hs23230200 : InSquare (-19/128) (233/640) (1/640) tau := by
                    convert childLL hs2323020 hx2323020 hy2323020 using 1 <;> norm_num
                  exact Batch0409.cell3279.sound htau (by
                    simp only [Batch0409.cell3279, Batch0409.tau3279, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23230200 (by positivity) using 1 <;> norm_num)
                · have hs23230202 : InSquare (-19/128) (47/128) (1/640) tau := by
                    convert childUL hs2323020 hx2323020 hy2323020 using 1 <;> norm_num
                  exact Batch0410.cell3281.sound htau (by
                    simp only [Batch0410.cell3281, Batch0410.tau3281, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23230202 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (117/320 : ℝ) with hy2323020 | hy2323020
                · have hs23230201 : InSquare (-93/640) (233/640) (1/640) tau := by
                    convert childLR hs2323020 hx2323020 hy2323020 using 1 <;> norm_num
                  exact Batch0410.cell3280.sound htau (by
                    simp only [Batch0410.cell3280, Batch0410.tau3280, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23230201 (by positivity) using 1 <;> norm_num)
                · have hs23230203 : InSquare (-93/640) (47/128) (1/640) tau := by
                    convert childUR hs2323020 hx2323020 hy2323020 using 1 <;> norm_num
                  exact Batch0410.cell3282.sound htau (by
                    simp only [Batch0410.cell3282, Batch0410.tau3282, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23230203 (by positivity) using 1 <;> norm_num)
            · have hs2323022 : InSquare (-47/320) (119/320) (1/320) tau := by
                convert childUL hs232302 hx232302 hy232302 using 1 <;> norm_num
              rcases le_total tau.re (-47/320 : ℝ) with hx2323022 | hx2323022
              · rcases le_total tau.im (119/320 : ℝ) with hy2323022 | hy2323022
                · have hs23230220 : InSquare (-19/128) (237/640) (1/640) tau := by
                    convert childLL hs2323022 hx2323022 hy2323022 using 1 <;> norm_num
                  exact Batch0410.cell3287.sound htau (by
                    simp only [Batch0410.cell3287, Batch0410.tau3287, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23230220 (by positivity) using 1 <;> norm_num)
                · have hs23230222 : InSquare (-19/128) (239/640) (1/640) tau := by
                    convert childUL hs2323022 hx2323022 hy2323022 using 1 <;> norm_num
                  exact Batch0411.cell3289.sound htau (by
                    simp only [Batch0411.cell3289, Batch0411.tau3289, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23230222 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (119/320 : ℝ) with hy2323022 | hy2323022
                · have hs23230221 : InSquare (-93/640) (237/640) (1/640) tau := by
                    convert childLR hs2323022 hx2323022 hy2323022 using 1 <;> norm_num
                  exact Batch0411.cell3288.sound htau (by
                    simp only [Batch0411.cell3288, Batch0411.tau3288, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23230221 (by positivity) using 1 <;> norm_num)
                · have hs23230223 : InSquare (-93/640) (239/640) (1/640) tau := by
                    convert childUR hs2323022 hx2323022 hy2323022 using 1 <;> norm_num
                  exact Batch0411.cell3290.sound htau (by
                    simp only [Batch0411.cell3290, Batch0411.tau3290, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23230223 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (59/160 : ℝ) with hy232302 | hy232302
            · have hs2323021 : InSquare (-9/64) (117/320) (1/320) tau := by
                convert childLR hs232302 hx232302 hy232302 using 1 <;> norm_num
              rcases le_total tau.re (-9/64 : ℝ) with hx2323021 | hx2323021
              · rcases le_total tau.im (117/320 : ℝ) with hy2323021 | hy2323021
                · have hs23230210 : InSquare (-91/640) (233/640) (1/640) tau := by
                    convert childLL hs2323021 hx2323021 hy2323021 using 1 <;> norm_num
                  exact Batch0410.cell3283.sound htau (by
                    simp only [Batch0410.cell3283, Batch0410.tau3283, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23230210 (by positivity) using 1 <;> norm_num)
                · have hs23230212 : InSquare (-91/640) (47/128) (1/640) tau := by
                    convert childUL hs2323021 hx2323021 hy2323021 using 1 <;> norm_num
                  exact Batch0410.cell3285.sound htau (by
                    simp only [Batch0410.cell3285, Batch0410.tau3285, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23230212 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (117/320 : ℝ) with hy2323021 | hy2323021
                · have hs23230211 : InSquare (-89/640) (233/640) (1/640) tau := by
                    convert childLR hs2323021 hx2323021 hy2323021 using 1 <;> norm_num
                  exact Batch0410.cell3284.sound htau (by
                    simp only [Batch0410.cell3284, Batch0410.tau3284, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23230211 (by positivity) using 1 <;> norm_num)
                · have hs23230213 : InSquare (-89/640) (47/128) (1/640) tau := by
                    convert childUR hs2323021 hx2323021 hy2323021 using 1 <;> norm_num
                  exact Batch0410.cell3286.sound htau (by
                    simp only [Batch0410.cell3286, Batch0410.tau3286, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23230213 (by positivity) using 1 <;> norm_num)
            · have hs2323023 : InSquare (-9/64) (119/320) (1/320) tau := by
                convert childUR hs232302 hx232302 hy232302 using 1 <;> norm_num
              rcases le_total tau.re (-9/64 : ℝ) with hx2323023 | hx2323023
              · rcases le_total tau.im (119/320 : ℝ) with hy2323023 | hy2323023
                · have hs23230230 : InSquare (-91/640) (237/640) (1/640) tau := by
                    convert childLL hs2323023 hx2323023 hy2323023 using 1 <;> norm_num
                  exact Batch0411.cell3291.sound htau (by
                    simp only [Batch0411.cell3291, Batch0411.tau3291, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23230230 (by positivity) using 1 <;> norm_num)
                · have hs23230232 : InSquare (-91/640) (239/640) (1/640) tau := by
                    convert childUL hs2323023 hx2323023 hy2323023 using 1 <;> norm_num
                  exact Batch0411.cell3293.sound htau (by
                    simp only [Batch0411.cell3293, Batch0411.tau3293, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23230232 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (119/320 : ℝ) with hy2323023 | hy2323023
                · have hs23230231 : InSquare (-89/640) (237/640) (1/640) tau := by
                    convert childLR hs2323023 hx2323023 hy2323023 using 1 <;> norm_num
                  exact Batch0411.cell3292.sound htau (by
                    simp only [Batch0411.cell3292, Batch0411.tau3292, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23230231 (by positivity) using 1 <;> norm_num)
                · have hs23230233 : InSquare (-89/640) (239/640) (1/640) tau := by
                    convert childUR hs2323023 hx2323023 hy2323023 using 1 <;> norm_num
                  exact Batch0411.cell3294.sound htau (by
                    simp only [Batch0411.cell3294, Batch0411.tau3294, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23230233 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (29/80 : ℝ) with hy23230 | hy23230
        · have hs232301 : InSquare (-21/160) (57/160) (1/160) tau := by
            convert childLR hs23230 hx23230 hy23230 using 1 <;> norm_num
          rcases le_total tau.re (-21/160 : ℝ) with hx232301 | hx232301
          · rcases le_total tau.im (57/160 : ℝ) with hy232301 | hy232301
            · have hs2323010 : InSquare (-43/320) (113/320) (1/320) tau := by
                convert childLL hs232301 hx232301 hy232301 using 1 <;> norm_num
              exact Batch0264.cell2119.sound htau (by
                simp only [Batch0264.cell2119, Batch0264.tau2119, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2323010 (by positivity) using 1 <;> norm_num)
            · have hs2323012 : InSquare (-43/320) (23/64) (1/320) tau := by
                convert childUL hs232301 hx232301 hy232301 using 1 <;> norm_num
              exact Batch0265.cell2121.sound htau (by
                simp only [Batch0265.cell2121, Batch0265.tau2121, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2323012 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (57/160 : ℝ) with hy232301 | hy232301
            · have hs2323011 : InSquare (-41/320) (113/320) (1/320) tau := by
                convert childLR hs232301 hx232301 hy232301 using 1 <;> norm_num
              exact Batch0265.cell2120.sound htau (by
                simp only [Batch0265.cell2120, Batch0265.tau2120, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2323011 (by positivity) using 1 <;> norm_num)
            · have hs2323013 : InSquare (-41/320) (23/64) (1/320) tau := by
                convert childUR hs232301 hx232301 hy232301 using 1 <;> norm_num
              exact Batch0265.cell2122.sound htau (by
                simp only [Batch0265.cell2122, Batch0265.tau2122, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2323013 (by positivity) using 1 <;> norm_num)
        · have hs232303 : InSquare (-21/160) (59/160) (1/160) tau := by
            convert childUR hs23230 hx23230 hy23230 using 1 <;> norm_num
          rcases le_total tau.re (-21/160 : ℝ) with hx232303 | hx232303
          · rcases le_total tau.im (59/160 : ℝ) with hy232303 | hy232303
            · have hs2323030 : InSquare (-43/320) (117/320) (1/320) tau := by
                convert childLL hs232303 hx232303 hy232303 using 1 <;> norm_num
              rcases le_total tau.re (-43/320 : ℝ) with hx2323030 | hx2323030
              · rcases le_total tau.im (117/320 : ℝ) with hy2323030 | hy2323030
                · have hs23230300 : InSquare (-87/640) (233/640) (1/640) tau := by
                    convert childLL hs2323030 hx2323030 hy2323030 using 1 <;> norm_num
                  exact Batch0411.cell3295.sound htau (by
                    simp only [Batch0411.cell3295, Batch0411.tau3295, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23230300 (by positivity) using 1 <;> norm_num)
                · have hs23230302 : InSquare (-87/640) (47/128) (1/640) tau := by
                    convert childUL hs2323030 hx2323030 hy2323030 using 1 <;> norm_num
                  exact Batch0412.cell3297.sound htau (by
                    simp only [Batch0412.cell3297, Batch0412.tau3297, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23230302 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (117/320 : ℝ) with hy2323030 | hy2323030
                · have hs23230301 : InSquare (-17/128) (233/640) (1/640) tau := by
                    convert childLR hs2323030 hx2323030 hy2323030 using 1 <;> norm_num
                  exact Batch0412.cell3296.sound htau (by
                    simp only [Batch0412.cell3296, Batch0412.tau3296, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23230301 (by positivity) using 1 <;> norm_num)
                · have hs23230303 : InSquare (-17/128) (47/128) (1/640) tau := by
                    convert childUR hs2323030 hx2323030 hy2323030 using 1 <;> norm_num
                  exact Batch0412.cell3298.sound htau (by
                    simp only [Batch0412.cell3298, Batch0412.tau3298, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23230303 (by positivity) using 1 <;> norm_num)
            · have hs2323032 : InSquare (-43/320) (119/320) (1/320) tau := by
                convert childUL hs232303 hx232303 hy232303 using 1 <;> norm_num
              rcases le_total tau.re (-43/320 : ℝ) with hx2323032 | hx2323032
              · rcases le_total tau.im (119/320 : ℝ) with hy2323032 | hy2323032
                · have hs23230320 : InSquare (-87/640) (237/640) (1/640) tau := by
                    convert childLL hs2323032 hx2323032 hy2323032 using 1 <;> norm_num
                  exact Batch0412.cell3303.sound htau (by
                    simp only [Batch0412.cell3303, Batch0412.tau3303, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23230320 (by positivity) using 1 <;> norm_num)
                · have hs23230322 : InSquare (-87/640) (239/640) (1/640) tau := by
                    convert childUL hs2323032 hx2323032 hy2323032 using 1 <;> norm_num
                  exact Batch0413.cell3305.sound htau (by
                    simp only [Batch0413.cell3305, Batch0413.tau3305, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23230322 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (119/320 : ℝ) with hy2323032 | hy2323032
                · have hs23230321 : InSquare (-17/128) (237/640) (1/640) tau := by
                    convert childLR hs2323032 hx2323032 hy2323032 using 1 <;> norm_num
                  exact Batch0413.cell3304.sound htau (by
                    simp only [Batch0413.cell3304, Batch0413.tau3304, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23230321 (by positivity) using 1 <;> norm_num)
                · have hs23230323 : InSquare (-17/128) (239/640) (1/640) tau := by
                    convert childUR hs2323032 hx2323032 hy2323032 using 1 <;> norm_num
                  exact Batch0413.cell3306.sound htau (by
                    simp only [Batch0413.cell3306, Batch0413.tau3306, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23230323 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (59/160 : ℝ) with hy232303 | hy232303
            · have hs2323031 : InSquare (-41/320) (117/320) (1/320) tau := by
                convert childLR hs232303 hx232303 hy232303 using 1 <;> norm_num
              rcases le_total tau.re (-41/320 : ℝ) with hx2323031 | hx2323031
              · rcases le_total tau.im (117/320 : ℝ) with hy2323031 | hy2323031
                · have hs23230310 : InSquare (-83/640) (233/640) (1/640) tau := by
                    convert childLL hs2323031 hx2323031 hy2323031 using 1 <;> norm_num
                  exact Batch0412.cell3299.sound htau (by
                    simp only [Batch0412.cell3299, Batch0412.tau3299, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23230310 (by positivity) using 1 <;> norm_num)
                · have hs23230312 : InSquare (-83/640) (47/128) (1/640) tau := by
                    convert childUL hs2323031 hx2323031 hy2323031 using 1 <;> norm_num
                  exact Batch0412.cell3301.sound htau (by
                    simp only [Batch0412.cell3301, Batch0412.tau3301, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23230312 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (117/320 : ℝ) with hy2323031 | hy2323031
                · have hs23230311 : InSquare (-81/640) (233/640) (1/640) tau := by
                    convert childLR hs2323031 hx2323031 hy2323031 using 1 <;> norm_num
                  exact Batch0412.cell3300.sound htau (by
                    simp only [Batch0412.cell3300, Batch0412.tau3300, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23230311 (by positivity) using 1 <;> norm_num)
                · have hs23230313 : InSquare (-81/640) (47/128) (1/640) tau := by
                    convert childUR hs2323031 hx2323031 hy2323031 using 1 <;> norm_num
                  exact Batch0412.cell3302.sound htau (by
                    simp only [Batch0412.cell3302, Batch0412.tau3302, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23230313 (by positivity) using 1 <;> norm_num)
            · have hs2323033 : InSquare (-41/320) (119/320) (1/320) tau := by
                convert childUR hs232303 hx232303 hy232303 using 1 <;> norm_num
              rcases le_total tau.re (-41/320 : ℝ) with hx2323033 | hx2323033
              · rcases le_total tau.im (119/320 : ℝ) with hy2323033 | hy2323033
                · have hs23230330 : InSquare (-83/640) (237/640) (1/640) tau := by
                    convert childLL hs2323033 hx2323033 hy2323033 using 1 <;> norm_num
                  exact Batch0413.cell3307.sound htau (by
                    simp only [Batch0413.cell3307, Batch0413.tau3307, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23230330 (by positivity) using 1 <;> norm_num)
                · have hs23230332 : InSquare (-83/640) (239/640) (1/640) tau := by
                    convert childUL hs2323033 hx2323033 hy2323033 using 1 <;> norm_num
                  exact Batch0413.cell3309.sound htau (by
                    simp only [Batch0413.cell3309, Batch0413.tau3309, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23230332 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (119/320 : ℝ) with hy2323033 | hy2323033
                · have hs23230331 : InSquare (-81/640) (237/640) (1/640) tau := by
                    convert childLR hs2323033 hx2323033 hy2323033 using 1 <;> norm_num
                  exact Batch0413.cell3308.sound htau (by
                    simp only [Batch0413.cell3308, Batch0413.tau3308, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23230331 (by positivity) using 1 <;> norm_num)
                · have hs23230333 : InSquare (-81/640) (239/640) (1/640) tau := by
                    convert childUR hs2323033 hx2323033 hy2323033 using 1 <;> norm_num
                  exact Batch0413.cell3310.sound htau (by
                    simp only [Batch0413.cell3310, Batch0413.tau3310, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23230333 (by positivity) using 1 <;> norm_num)
    · have hs23232 : InSquare (-11/80) (31/80) (1/80) tau := by
        convert childUL hs hx2323 hy2323 using 1 <;> norm_num
      rcases le_total tau.re (-11/80 : ℝ) with hx23232 | hx23232
      · rcases le_total tau.im (31/80 : ℝ) with hy23232 | hy23232
        · have hs232320 : InSquare (-23/160) (61/160) (1/160) tau := by
            convert childLL hs23232 hx23232 hy23232 using 1 <;> norm_num
          rcases le_total tau.re (-23/160 : ℝ) with hx232320 | hx232320
          · rcases le_total tau.im (61/160 : ℝ) with hy232320 | hy232320
            · have hs2323200 : InSquare (-47/320) (121/320) (1/320) tau := by
                convert childLL hs232320 hx232320 hy232320 using 1 <;> norm_num
              exact (outside_2323200 htau hs2323200).elim
            · have hs2323202 : InSquare (-47/320) (123/320) (1/320) tau := by
                convert childUL hs232320 hx232320 hy232320 using 1 <;> norm_num
              exact (outside_2323202 htau hs2323202).elim
          · rcases le_total tau.im (61/160 : ℝ) with hy232320 | hy232320
            · have hs2323201 : InSquare (-9/64) (121/320) (1/320) tau := by
                convert childLR hs232320 hx232320 hy232320 using 1 <;> norm_num
              rcases le_total tau.re (-9/64 : ℝ) with hx2323201 | hx2323201
              · rcases le_total tau.im (121/320 : ℝ) with hy2323201 | hy2323201
                · have hs23232010 : InSquare (-91/640) (241/640) (1/640) tau := by
                    convert childLL hs2323201 hx2323201 hy2323201 using 1 <;> norm_num
                  exact (outside_23232010 htau hs23232010).elim
                · have hs23232012 : InSquare (-91/640) (243/640) (1/640) tau := by
                    convert childUL hs2323201 hx2323201 hy2323201 using 1 <;> norm_num
                  exact (outside_23232012 htau hs23232012).elim
              · rcases le_total tau.im (121/320 : ℝ) with hy2323201 | hy2323201
                · have hs23232011 : InSquare (-89/640) (241/640) (1/640) tau := by
                    convert childLR hs2323201 hx2323201 hy2323201 using 1 <;> norm_num
                  exact Batch0415.cell3327.sound htau (by
                    simp only [Batch0415.cell3327, Batch0415.tau3327, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23232011 (by positivity) using 1 <;> norm_num)
                · have hs23232013 : InSquare (-89/640) (243/640) (1/640) tau := by
                    convert childUR hs2323201 hx2323201 hy2323201 using 1 <;> norm_num
                  exact (outside_23232013 htau hs23232013).elim
            · have hs2323203 : InSquare (-9/64) (123/320) (1/320) tau := by
                convert childUR hs232320 hx232320 hy232320 using 1 <;> norm_num
              exact (outside_2323203 htau hs2323203).elim
        · have hs232322 : InSquare (-23/160) (63/160) (1/160) tau := by
            convert childUL hs23232 hx23232 hy23232 using 1 <;> norm_num
          exact (outside_232322 htau hs232322).elim
      · rcases le_total tau.im (31/80 : ℝ) with hy23232 | hy23232
        · have hs232321 : InSquare (-21/160) (61/160) (1/160) tau := by
            convert childLR hs23232 hx23232 hy23232 using 1 <;> norm_num
          rcases le_total tau.re (-21/160 : ℝ) with hx232321 | hx232321
          · rcases le_total tau.im (61/160 : ℝ) with hy232321 | hy232321
            · have hs2323210 : InSquare (-43/320) (121/320) (1/320) tau := by
                convert childLL hs232321 hx232321 hy232321 using 1 <;> norm_num
              rcases le_total tau.re (-43/320 : ℝ) with hx2323210 | hx2323210
              · rcases le_total tau.im (121/320 : ℝ) with hy2323210 | hy2323210
                · have hs23232100 : InSquare (-87/640) (241/640) (1/640) tau := by
                    convert childLL hs2323210 hx2323210 hy2323210 using 1 <;> norm_num
                  exact Batch0416.cell3328.sound htau (by
                    simp only [Batch0416.cell3328, Batch0416.tau3328, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23232100 (by positivity) using 1 <;> norm_num)
                · have hs23232102 : InSquare (-87/640) (243/640) (1/640) tau := by
                    convert childUL hs2323210 hx2323210 hy2323210 using 1 <;> norm_num
                  exact (outside_23232102 htau hs23232102).elim
              · rcases le_total tau.im (121/320 : ℝ) with hy2323210 | hy2323210
                · have hs23232101 : InSquare (-17/128) (241/640) (1/640) tau := by
                    convert childLR hs2323210 hx2323210 hy2323210 using 1 <;> norm_num
                  exact Batch0416.cell3329.sound htau (by
                    simp only [Batch0416.cell3329, Batch0416.tau3329, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23232101 (by positivity) using 1 <;> norm_num)
                · have hs23232103 : InSquare (-17/128) (243/640) (1/640) tau := by
                    convert childUR hs2323210 hx2323210 hy2323210 using 1 <;> norm_num
                  exact (outside_23232103 htau hs23232103).elim
            · have hs2323212 : InSquare (-43/320) (123/320) (1/320) tau := by
                convert childUL hs232321 hx232321 hy232321 using 1 <;> norm_num
              exact (outside_2323212 htau hs2323212).elim
          · rcases le_total tau.im (61/160 : ℝ) with hy232321 | hy232321
            · have hs2323211 : InSquare (-41/320) (121/320) (1/320) tau := by
                convert childLR hs232321 hx232321 hy232321 using 1 <;> norm_num
              rcases le_total tau.re (-41/320 : ℝ) with hx2323211 | hx2323211
              · rcases le_total tau.im (121/320 : ℝ) with hy2323211 | hy2323211
                · have hs23232110 : InSquare (-83/640) (241/640) (1/640) tau := by
                    convert childLL hs2323211 hx2323211 hy2323211 using 1 <;> norm_num
                  exact Batch0416.cell3330.sound htau (by
                    simp only [Batch0416.cell3330, Batch0416.tau3330, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23232110 (by positivity) using 1 <;> norm_num)
                · have hs23232112 : InSquare (-83/640) (243/640) (1/640) tau := by
                    convert childUL hs2323211 hx2323211 hy2323211 using 1 <;> norm_num
                  exact Batch0416.cell3332.sound htau (by
                    simp only [Batch0416.cell3332, Batch0416.tau3332, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23232112 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (121/320 : ℝ) with hy2323211 | hy2323211
                · have hs23232111 : InSquare (-81/640) (241/640) (1/640) tau := by
                    convert childLR hs2323211 hx2323211 hy2323211 using 1 <;> norm_num
                  exact Batch0416.cell3331.sound htau (by
                    simp only [Batch0416.cell3331, Batch0416.tau3331, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23232111 (by positivity) using 1 <;> norm_num)
                · have hs23232113 : InSquare (-81/640) (243/640) (1/640) tau := by
                    convert childUR hs2323211 hx2323211 hy2323211 using 1 <;> norm_num
                  exact Batch0416.cell3333.sound htau (by
                    simp only [Batch0416.cell3333, Batch0416.tau3333, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23232113 (by positivity) using 1 <;> norm_num)
            · have hs2323213 : InSquare (-41/320) (123/320) (1/320) tau := by
                convert childUR hs232321 hx232321 hy232321 using 1 <;> norm_num
              exact (outside_2323213 htau hs2323213).elim
        · have hs232323 : InSquare (-21/160) (63/160) (1/160) tau := by
            convert childUR hs23232 hx23232 hy23232 using 1 <;> norm_num
          exact (outside_232323 htau hs232323).elim
  · rcases le_total tau.im (3/8 : ℝ) with hy2323 | hy2323
    · have hs23231 : InSquare (-9/80) (29/80) (1/80) tau := by
        convert childLR hs hx2323 hy2323 using 1 <;> norm_num
      rcases le_total tau.re (-9/80 : ℝ) with hx23231 | hx23231
      · rcases le_total tau.im (29/80 : ℝ) with hy23231 | hy23231
        · have hs232310 : InSquare (-19/160) (57/160) (1/160) tau := by
            convert childLL hs23231 hx23231 hy23231 using 1 <;> norm_num
          rcases le_total tau.re (-19/160 : ℝ) with hx232310 | hx232310
          · rcases le_total tau.im (57/160 : ℝ) with hy232310 | hy232310
            · have hs2323100 : InSquare (-39/320) (113/320) (1/320) tau := by
                convert childLL hs232310 hx232310 hy232310 using 1 <;> norm_num
              exact Batch0265.cell2123.sound htau (by
                simp only [Batch0265.cell2123, Batch0265.tau2123, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2323100 (by positivity) using 1 <;> norm_num)
            · have hs2323102 : InSquare (-39/320) (23/64) (1/320) tau := by
                convert childUL hs232310 hx232310 hy232310 using 1 <;> norm_num
              exact Batch0265.cell2125.sound htau (by
                simp only [Batch0265.cell2125, Batch0265.tau2125, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2323102 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (57/160 : ℝ) with hy232310 | hy232310
            · have hs2323101 : InSquare (-37/320) (113/320) (1/320) tau := by
                convert childLR hs232310 hx232310 hy232310 using 1 <;> norm_num
              exact Batch0265.cell2124.sound htau (by
                simp only [Batch0265.cell2124, Batch0265.tau2124, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2323101 (by positivity) using 1 <;> norm_num)
            · have hs2323103 : InSquare (-37/320) (23/64) (1/320) tau := by
                convert childUR hs232310 hx232310 hy232310 using 1 <;> norm_num
              exact Batch0265.cell2126.sound htau (by
                simp only [Batch0265.cell2126, Batch0265.tau2126, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2323103 (by positivity) using 1 <;> norm_num)
        · have hs232312 : InSquare (-19/160) (59/160) (1/160) tau := by
            convert childUL hs23231 hx23231 hy23231 using 1 <;> norm_num
          rcases le_total tau.re (-19/160 : ℝ) with hx232312 | hx232312
          · rcases le_total tau.im (59/160 : ℝ) with hy232312 | hy232312
            · have hs2323120 : InSquare (-39/320) (117/320) (1/320) tau := by
                convert childLL hs232312 hx232312 hy232312 using 1 <;> norm_num
              exact Batch0266.cell2131.sound htau (by
                simp only [Batch0266.cell2131, Batch0266.tau2131, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2323120 (by positivity) using 1 <;> norm_num)
            · have hs2323122 : InSquare (-39/320) (119/320) (1/320) tau := by
                convert childUL hs232312 hx232312 hy232312 using 1 <;> norm_num
              rcases le_total tau.re (-39/320 : ℝ) with hx2323122 | hx2323122
              · rcases le_total tau.im (119/320 : ℝ) with hy2323122 | hy2323122
                · have hs23231220 : InSquare (-79/640) (237/640) (1/640) tau := by
                    convert childLL hs2323122 hx2323122 hy2323122 using 1 <;> norm_num
                  exact Batch0413.cell3311.sound htau (by
                    simp only [Batch0413.cell3311, Batch0413.tau3311, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23231220 (by positivity) using 1 <;> norm_num)
                · have hs23231222 : InSquare (-79/640) (239/640) (1/640) tau := by
                    convert childUL hs2323122 hx2323122 hy2323122 using 1 <;> norm_num
                  exact Batch0414.cell3313.sound htau (by
                    simp only [Batch0414.cell3313, Batch0414.tau3313, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23231222 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (119/320 : ℝ) with hy2323122 | hy2323122
                · have hs23231221 : InSquare (-77/640) (237/640) (1/640) tau := by
                    convert childLR hs2323122 hx2323122 hy2323122 using 1 <;> norm_num
                  exact Batch0414.cell3312.sound htau (by
                    simp only [Batch0414.cell3312, Batch0414.tau3312, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23231221 (by positivity) using 1 <;> norm_num)
                · have hs23231223 : InSquare (-77/640) (239/640) (1/640) tau := by
                    convert childUR hs2323122 hx2323122 hy2323122 using 1 <;> norm_num
                  exact Batch0414.cell3314.sound htau (by
                    simp only [Batch0414.cell3314, Batch0414.tau3314, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23231223 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (59/160 : ℝ) with hy232312 | hy232312
            · have hs2323121 : InSquare (-37/320) (117/320) (1/320) tau := by
                convert childLR hs232312 hx232312 hy232312 using 1 <;> norm_num
              exact Batch0266.cell2132.sound htau (by
                simp only [Batch0266.cell2132, Batch0266.tau2132, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2323121 (by positivity) using 1 <;> norm_num)
            · have hs2323123 : InSquare (-37/320) (119/320) (1/320) tau := by
                convert childUR hs232312 hx232312 hy232312 using 1 <;> norm_num
              rcases le_total tau.re (-37/320 : ℝ) with hx2323123 | hx2323123
              · rcases le_total tau.im (119/320 : ℝ) with hy2323123 | hy2323123
                · have hs23231230 : InSquare (-15/128) (237/640) (1/640) tau := by
                    convert childLL hs2323123 hx2323123 hy2323123 using 1 <;> norm_num
                  exact Batch0414.cell3315.sound htau (by
                    simp only [Batch0414.cell3315, Batch0414.tau3315, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23231230 (by positivity) using 1 <;> norm_num)
                · have hs23231232 : InSquare (-15/128) (239/640) (1/640) tau := by
                    convert childUL hs2323123 hx2323123 hy2323123 using 1 <;> norm_num
                  exact Batch0414.cell3317.sound htau (by
                    simp only [Batch0414.cell3317, Batch0414.tau3317, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23231232 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (119/320 : ℝ) with hy2323123 | hy2323123
                · have hs23231231 : InSquare (-73/640) (237/640) (1/640) tau := by
                    convert childLR hs2323123 hx2323123 hy2323123 using 1 <;> norm_num
                  exact Batch0414.cell3316.sound htau (by
                    simp only [Batch0414.cell3316, Batch0414.tau3316, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23231231 (by positivity) using 1 <;> norm_num)
                · have hs23231233 : InSquare (-73/640) (239/640) (1/640) tau := by
                    convert childUR hs2323123 hx2323123 hy2323123 using 1 <;> norm_num
                  exact Batch0414.cell3318.sound htau (by
                    simp only [Batch0414.cell3318, Batch0414.tau3318, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23231233 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (29/80 : ℝ) with hy23231 | hy23231
        · have hs232311 : InSquare (-17/160) (57/160) (1/160) tau := by
            convert childLR hs23231 hx23231 hy23231 using 1 <;> norm_num
          rcases le_total tau.re (-17/160 : ℝ) with hx232311 | hx232311
          · rcases le_total tau.im (57/160 : ℝ) with hy232311 | hy232311
            · have hs2323110 : InSquare (-7/64) (113/320) (1/320) tau := by
                convert childLL hs232311 hx232311 hy232311 using 1 <;> norm_num
              exact Batch0265.cell2127.sound htau (by
                simp only [Batch0265.cell2127, Batch0265.tau2127, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2323110 (by positivity) using 1 <;> norm_num)
            · have hs2323112 : InSquare (-7/64) (23/64) (1/320) tau := by
                convert childUL hs232311 hx232311 hy232311 using 1 <;> norm_num
              exact Batch0266.cell2129.sound htau (by
                simp only [Batch0266.cell2129, Batch0266.tau2129, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2323112 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (57/160 : ℝ) with hy232311 | hy232311
            · have hs2323111 : InSquare (-33/320) (113/320) (1/320) tau := by
                convert childLR hs232311 hx232311 hy232311 using 1 <;> norm_num
              exact Batch0266.cell2128.sound htau (by
                simp only [Batch0266.cell2128, Batch0266.tau2128, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2323111 (by positivity) using 1 <;> norm_num)
            · have hs2323113 : InSquare (-33/320) (23/64) (1/320) tau := by
                convert childUR hs232311 hx232311 hy232311 using 1 <;> norm_num
              exact Batch0266.cell2130.sound htau (by
                simp only [Batch0266.cell2130, Batch0266.tau2130, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2323113 (by positivity) using 1 <;> norm_num)
        · have hs232313 : InSquare (-17/160) (59/160) (1/160) tau := by
            convert childUR hs23231 hx23231 hy23231 using 1 <;> norm_num
          rcases le_total tau.re (-17/160 : ℝ) with hx232313 | hx232313
          · rcases le_total tau.im (59/160 : ℝ) with hy232313 | hy232313
            · have hs2323130 : InSquare (-7/64) (117/320) (1/320) tau := by
                convert childLL hs232313 hx232313 hy232313 using 1 <;> norm_num
              exact Batch0266.cell2133.sound htau (by
                simp only [Batch0266.cell2133, Batch0266.tau2133, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2323130 (by positivity) using 1 <;> norm_num)
            · have hs2323132 : InSquare (-7/64) (119/320) (1/320) tau := by
                convert childUL hs232313 hx232313 hy232313 using 1 <;> norm_num
              rcases le_total tau.re (-7/64 : ℝ) with hx2323132 | hx2323132
              · rcases le_total tau.im (119/320 : ℝ) with hy2323132 | hy2323132
                · have hs23231320 : InSquare (-71/640) (237/640) (1/640) tau := by
                    convert childLL hs2323132 hx2323132 hy2323132 using 1 <;> norm_num
                  exact Batch0414.cell3319.sound htau (by
                    simp only [Batch0414.cell3319, Batch0414.tau3319, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23231320 (by positivity) using 1 <;> norm_num)
                · have hs23231322 : InSquare (-71/640) (239/640) (1/640) tau := by
                    convert childUL hs2323132 hx2323132 hy2323132 using 1 <;> norm_num
                  exact Batch0415.cell3321.sound htau (by
                    simp only [Batch0415.cell3321, Batch0415.tau3321, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23231322 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (119/320 : ℝ) with hy2323132 | hy2323132
                · have hs23231321 : InSquare (-69/640) (237/640) (1/640) tau := by
                    convert childLR hs2323132 hx2323132 hy2323132 using 1 <;> norm_num
                  exact Batch0415.cell3320.sound htau (by
                    simp only [Batch0415.cell3320, Batch0415.tau3320, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23231321 (by positivity) using 1 <;> norm_num)
                · have hs23231323 : InSquare (-69/640) (239/640) (1/640) tau := by
                    convert childUR hs2323132 hx2323132 hy2323132 using 1 <;> norm_num
                  exact Batch0415.cell3322.sound htau (by
                    simp only [Batch0415.cell3322, Batch0415.tau3322, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23231323 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (59/160 : ℝ) with hy232313 | hy232313
            · have hs2323131 : InSquare (-33/320) (117/320) (1/320) tau := by
                convert childLR hs232313 hx232313 hy232313 using 1 <;> norm_num
              exact Batch0266.cell2134.sound htau (by
                simp only [Batch0266.cell2134, Batch0266.tau2134, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2323131 (by positivity) using 1 <;> norm_num)
            · have hs2323133 : InSquare (-33/320) (119/320) (1/320) tau := by
                convert childUR hs232313 hx232313 hy232313 using 1 <;> norm_num
              rcases le_total tau.re (-33/320 : ℝ) with hx2323133 | hx2323133
              · rcases le_total tau.im (119/320 : ℝ) with hy2323133 | hy2323133
                · have hs23231330 : InSquare (-67/640) (237/640) (1/640) tau := by
                    convert childLL hs2323133 hx2323133 hy2323133 using 1 <;> norm_num
                  exact Batch0415.cell3323.sound htau (by
                    simp only [Batch0415.cell3323, Batch0415.tau3323, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23231330 (by positivity) using 1 <;> norm_num)
                · have hs23231332 : InSquare (-67/640) (239/640) (1/640) tau := by
                    convert childUL hs2323133 hx2323133 hy2323133 using 1 <;> norm_num
                  exact Batch0415.cell3325.sound htau (by
                    simp only [Batch0415.cell3325, Batch0415.tau3325, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23231332 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (119/320 : ℝ) with hy2323133 | hy2323133
                · have hs23231331 : InSquare (-13/128) (237/640) (1/640) tau := by
                    convert childLR hs2323133 hx2323133 hy2323133 using 1 <;> norm_num
                  exact Batch0415.cell3324.sound htau (by
                    simp only [Batch0415.cell3324, Batch0415.tau3324, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23231331 (by positivity) using 1 <;> norm_num)
                · have hs23231333 : InSquare (-13/128) (239/640) (1/640) tau := by
                    convert childUR hs2323133 hx2323133 hy2323133 using 1 <;> norm_num
                  exact Batch0415.cell3326.sound htau (by
                    simp only [Batch0415.cell3326, Batch0415.tau3326, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23231333 (by positivity) using 1 <;> norm_num)
    · have hs23233 : InSquare (-9/80) (31/80) (1/80) tau := by
        convert childUR hs hx2323 hy2323 using 1 <;> norm_num
      rcases le_total tau.re (-9/80 : ℝ) with hx23233 | hx23233
      · rcases le_total tau.im (31/80 : ℝ) with hy23233 | hy23233
        · have hs232330 : InSquare (-19/160) (61/160) (1/160) tau := by
            convert childLL hs23233 hx23233 hy23233 using 1 <;> norm_num
          rcases le_total tau.re (-19/160 : ℝ) with hx232330 | hx232330
          · rcases le_total tau.im (61/160 : ℝ) with hy232330 | hy232330
            · have hs2323300 : InSquare (-39/320) (121/320) (1/320) tau := by
                convert childLL hs232330 hx232330 hy232330 using 1 <;> norm_num
              rcases le_total tau.re (-39/320 : ℝ) with hx2323300 | hx2323300
              · rcases le_total tau.im (121/320 : ℝ) with hy2323300 | hy2323300
                · have hs23233000 : InSquare (-79/640) (241/640) (1/640) tau := by
                    convert childLL hs2323300 hx2323300 hy2323300 using 1 <;> norm_num
                  exact Batch0416.cell3334.sound htau (by
                    simp only [Batch0416.cell3334, Batch0416.tau3334, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23233000 (by positivity) using 1 <;> norm_num)
                · have hs23233002 : InSquare (-79/640) (243/640) (1/640) tau := by
                    convert childUL hs2323300 hx2323300 hy2323300 using 1 <;> norm_num
                  exact Batch0417.cell3336.sound htau (by
                    simp only [Batch0417.cell3336, Batch0417.tau3336, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23233002 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (121/320 : ℝ) with hy2323300 | hy2323300
                · have hs23233001 : InSquare (-77/640) (241/640) (1/640) tau := by
                    convert childLR hs2323300 hx2323300 hy2323300 using 1 <;> norm_num
                  exact Batch0416.cell3335.sound htau (by
                    simp only [Batch0416.cell3335, Batch0416.tau3335, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23233001 (by positivity) using 1 <;> norm_num)
                · have hs23233003 : InSquare (-77/640) (243/640) (1/640) tau := by
                    convert childUR hs2323300 hx2323300 hy2323300 using 1 <;> norm_num
                  exact Batch0417.cell3337.sound htau (by
                    simp only [Batch0417.cell3337, Batch0417.tau3337, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23233003 (by positivity) using 1 <;> norm_num)
            · have hs2323302 : InSquare (-39/320) (123/320) (1/320) tau := by
                convert childUL hs232330 hx232330 hy232330 using 1 <;> norm_num
              rcases le_total tau.re (-39/320 : ℝ) with hx2323302 | hx2323302
              · rcases le_total tau.im (123/320 : ℝ) with hy2323302 | hy2323302
                · have hs23233020 : InSquare (-79/640) (49/128) (1/640) tau := by
                    convert childLL hs2323302 hx2323302 hy2323302 using 1 <;> norm_num
                  exact (outside_23233020 htau hs23233020).elim
                · have hs23233022 : InSquare (-79/640) (247/640) (1/640) tau := by
                    convert childUL hs2323302 hx2323302 hy2323302 using 1 <;> norm_num
                  exact (outside_23233022 htau hs23233022).elim
              · rcases le_total tau.im (123/320 : ℝ) with hy2323302 | hy2323302
                · have hs23233021 : InSquare (-77/640) (49/128) (1/640) tau := by
                    convert childLR hs2323302 hx2323302 hy2323302 using 1 <;> norm_num
                  exact Batch0417.cell3342.sound htau (by
                    simp only [Batch0417.cell3342, Batch0417.tau3342, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23233021 (by positivity) using 1 <;> norm_num)
                · have hs23233023 : InSquare (-77/640) (247/640) (1/640) tau := by
                    convert childUR hs2323302 hx2323302 hy2323302 using 1 <;> norm_num
                  exact (outside_23233023 htau hs23233023).elim
          · rcases le_total tau.im (61/160 : ℝ) with hy232330 | hy232330
            · have hs2323301 : InSquare (-37/320) (121/320) (1/320) tau := by
                convert childLR hs232330 hx232330 hy232330 using 1 <;> norm_num
              rcases le_total tau.re (-37/320 : ℝ) with hx2323301 | hx2323301
              · rcases le_total tau.im (121/320 : ℝ) with hy2323301 | hy2323301
                · have hs23233010 : InSquare (-15/128) (241/640) (1/640) tau := by
                    convert childLL hs2323301 hx2323301 hy2323301 using 1 <;> norm_num
                  exact Batch0417.cell3338.sound htau (by
                    simp only [Batch0417.cell3338, Batch0417.tau3338, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23233010 (by positivity) using 1 <;> norm_num)
                · have hs23233012 : InSquare (-15/128) (243/640) (1/640) tau := by
                    convert childUL hs2323301 hx2323301 hy2323301 using 1 <;> norm_num
                  exact Batch0417.cell3340.sound htau (by
                    simp only [Batch0417.cell3340, Batch0417.tau3340, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23233012 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (121/320 : ℝ) with hy2323301 | hy2323301
                · have hs23233011 : InSquare (-73/640) (241/640) (1/640) tau := by
                    convert childLR hs2323301 hx2323301 hy2323301 using 1 <;> norm_num
                  exact Batch0417.cell3339.sound htau (by
                    simp only [Batch0417.cell3339, Batch0417.tau3339, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23233011 (by positivity) using 1 <;> norm_num)
                · have hs23233013 : InSquare (-73/640) (243/640) (1/640) tau := by
                    convert childUR hs2323301 hx2323301 hy2323301 using 1 <;> norm_num
                  exact Batch0417.cell3341.sound htau (by
                    simp only [Batch0417.cell3341, Batch0417.tau3341, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23233013 (by positivity) using 1 <;> norm_num)
            · have hs2323303 : InSquare (-37/320) (123/320) (1/320) tau := by
                convert childUR hs232330 hx232330 hy232330 using 1 <;> norm_num
              rcases le_total tau.re (-37/320 : ℝ) with hx2323303 | hx2323303
              · rcases le_total tau.im (123/320 : ℝ) with hy2323303 | hy2323303
                · have hs23233030 : InSquare (-15/128) (49/128) (1/640) tau := by
                    convert childLL hs2323303 hx2323303 hy2323303 using 1 <;> norm_num
                  exact Batch0417.cell3343.sound htau (by
                    simp only [Batch0417.cell3343, Batch0417.tau3343, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23233030 (by positivity) using 1 <;> norm_num)
                · have hs23233032 : InSquare (-15/128) (247/640) (1/640) tau := by
                    convert childUL hs2323303 hx2323303 hy2323303 using 1 <;> norm_num
                  exact (outside_23233032 htau hs23233032).elim
              · rcases le_total tau.im (123/320 : ℝ) with hy2323303 | hy2323303
                · have hs23233031 : InSquare (-73/640) (49/128) (1/640) tau := by
                    convert childLR hs2323303 hx2323303 hy2323303 using 1 <;> norm_num
                  exact Batch0418.cell3344.sound htau (by
                    simp only [Batch0418.cell3344, Batch0418.tau3344, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23233031 (by positivity) using 1 <;> norm_num)
                · have hs23233033 : InSquare (-73/640) (247/640) (1/640) tau := by
                    convert childUR hs2323303 hx2323303 hy2323303 using 1 <;> norm_num
                  exact (outside_23233033 htau hs23233033).elim
        · have hs232332 : InSquare (-19/160) (63/160) (1/160) tau := by
            convert childUL hs23233 hx23233 hy23233 using 1 <;> norm_num
          exact (outside_232332 htau hs232332).elim
      · rcases le_total tau.im (31/80 : ℝ) with hy23233 | hy23233
        · have hs232331 : InSquare (-17/160) (61/160) (1/160) tau := by
            convert childLR hs23233 hx23233 hy23233 using 1 <;> norm_num
          rcases le_total tau.re (-17/160 : ℝ) with hx232331 | hx232331
          · rcases le_total tau.im (61/160 : ℝ) with hy232331 | hy232331
            · have hs2323310 : InSquare (-7/64) (121/320) (1/320) tau := by
                convert childLL hs232331 hx232331 hy232331 using 1 <;> norm_num
              rcases le_total tau.re (-7/64 : ℝ) with hx2323310 | hx2323310
              · rcases le_total tau.im (121/320 : ℝ) with hy2323310 | hy2323310
                · have hs23233100 : InSquare (-71/640) (241/640) (1/640) tau := by
                    convert childLL hs2323310 hx2323310 hy2323310 using 1 <;> norm_num
                  exact Batch0418.cell3345.sound htau (by
                    simp only [Batch0418.cell3345, Batch0418.tau3345, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23233100 (by positivity) using 1 <;> norm_num)
                · have hs23233102 : InSquare (-71/640) (243/640) (1/640) tau := by
                    convert childUL hs2323310 hx2323310 hy2323310 using 1 <;> norm_num
                  exact Batch0418.cell3347.sound htau (by
                    simp only [Batch0418.cell3347, Batch0418.tau3347, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23233102 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (121/320 : ℝ) with hy2323310 | hy2323310
                · have hs23233101 : InSquare (-69/640) (241/640) (1/640) tau := by
                    convert childLR hs2323310 hx2323310 hy2323310 using 1 <;> norm_num
                  exact Batch0418.cell3346.sound htau (by
                    simp only [Batch0418.cell3346, Batch0418.tau3346, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23233101 (by positivity) using 1 <;> norm_num)
                · have hs23233103 : InSquare (-69/640) (243/640) (1/640) tau := by
                    convert childUR hs2323310 hx2323310 hy2323310 using 1 <;> norm_num
                  exact Batch0418.cell3348.sound htau (by
                    simp only [Batch0418.cell3348, Batch0418.tau3348, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23233103 (by positivity) using 1 <;> norm_num)
            · have hs2323312 : InSquare (-7/64) (123/320) (1/320) tau := by
                convert childUL hs232331 hx232331 hy232331 using 1 <;> norm_num
              rcases le_total tau.re (-7/64 : ℝ) with hx2323312 | hx2323312
              · rcases le_total tau.im (123/320 : ℝ) with hy2323312 | hy2323312
                · have hs23233120 : InSquare (-71/640) (49/128) (1/640) tau := by
                    convert childLL hs2323312 hx2323312 hy2323312 using 1 <;> norm_num
                  exact Batch0419.cell3353.sound htau (by
                    simp only [Batch0419.cell3353, Batch0419.tau3353, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23233120 (by positivity) using 1 <;> norm_num)
                · have hs23233122 : InSquare (-71/640) (247/640) (1/640) tau := by
                    convert childUL hs2323312 hx2323312 hy2323312 using 1 <;> norm_num
                  exact Batch0419.cell3355.sound htau (by
                    simp only [Batch0419.cell3355, Batch0419.tau3355, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23233122 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (123/320 : ℝ) with hy2323312 | hy2323312
                · have hs23233121 : InSquare (-69/640) (49/128) (1/640) tau := by
                    convert childLR hs2323312 hx2323312 hy2323312 using 1 <;> norm_num
                  exact Batch0419.cell3354.sound htau (by
                    simp only [Batch0419.cell3354, Batch0419.tau3354, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23233121 (by positivity) using 1 <;> norm_num)
                · have hs23233123 : InSquare (-69/640) (247/640) (1/640) tau := by
                    convert childUR hs2323312 hx2323312 hy2323312 using 1 <;> norm_num
                  exact Batch0419.cell3356.sound htau (by
                    simp only [Batch0419.cell3356, Batch0419.tau3356, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23233123 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (61/160 : ℝ) with hy232331 | hy232331
            · have hs2323311 : InSquare (-33/320) (121/320) (1/320) tau := by
                convert childLR hs232331 hx232331 hy232331 using 1 <;> norm_num
              rcases le_total tau.re (-33/320 : ℝ) with hx2323311 | hx2323311
              · rcases le_total tau.im (121/320 : ℝ) with hy2323311 | hy2323311
                · have hs23233110 : InSquare (-67/640) (241/640) (1/640) tau := by
                    convert childLL hs2323311 hx2323311 hy2323311 using 1 <;> norm_num
                  exact Batch0418.cell3349.sound htau (by
                    simp only [Batch0418.cell3349, Batch0418.tau3349, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23233110 (by positivity) using 1 <;> norm_num)
                · have hs23233112 : InSquare (-67/640) (243/640) (1/640) tau := by
                    convert childUL hs2323311 hx2323311 hy2323311 using 1 <;> norm_num
                  exact Batch0418.cell3351.sound htau (by
                    simp only [Batch0418.cell3351, Batch0418.tau3351, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23233112 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (121/320 : ℝ) with hy2323311 | hy2323311
                · have hs23233111 : InSquare (-13/128) (241/640) (1/640) tau := by
                    convert childLR hs2323311 hx2323311 hy2323311 using 1 <;> norm_num
                  exact Batch0418.cell3350.sound htau (by
                    simp only [Batch0418.cell3350, Batch0418.tau3350, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23233111 (by positivity) using 1 <;> norm_num)
                · have hs23233113 : InSquare (-13/128) (243/640) (1/640) tau := by
                    convert childUR hs2323311 hx2323311 hy2323311 using 1 <;> norm_num
                  exact Batch0419.cell3352.sound htau (by
                    simp only [Batch0419.cell3352, Batch0419.tau3352, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23233113 (by positivity) using 1 <;> norm_num)
            · have hs2323313 : InSquare (-33/320) (123/320) (1/320) tau := by
                convert childUR hs232331 hx232331 hy232331 using 1 <;> norm_num
              rcases le_total tau.re (-33/320 : ℝ) with hx2323313 | hx2323313
              · rcases le_total tau.im (123/320 : ℝ) with hy2323313 | hy2323313
                · have hs23233130 : InSquare (-67/640) (49/128) (1/640) tau := by
                    convert childLL hs2323313 hx2323313 hy2323313 using 1 <;> norm_num
                  exact Batch0419.cell3357.sound htau (by
                    simp only [Batch0419.cell3357, Batch0419.tau3357, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23233130 (by positivity) using 1 <;> norm_num)
                · have hs23233132 : InSquare (-67/640) (247/640) (1/640) tau := by
                    convert childUL hs2323313 hx2323313 hy2323313 using 1 <;> norm_num
                  exact Batch0419.cell3359.sound htau (by
                    simp only [Batch0419.cell3359, Batch0419.tau3359, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23233132 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (123/320 : ℝ) with hy2323313 | hy2323313
                · have hs23233131 : InSquare (-13/128) (49/128) (1/640) tau := by
                    convert childLR hs2323313 hx2323313 hy2323313 using 1 <;> norm_num
                  exact Batch0419.cell3358.sound htau (by
                    simp only [Batch0419.cell3358, Batch0419.tau3358, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23233131 (by positivity) using 1 <;> norm_num)
                · have hs23233133 : InSquare (-13/128) (247/640) (1/640) tau := by
                    convert childUR hs2323313 hx2323313 hy2323313 using 1 <;> norm_num
                  exact Batch0420.cell3360.sound htau (by
                    simp only [Batch0420.cell3360, Batch0420.tau3360, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23233133 (by positivity) using 1 <;> norm_num)
        · have hs232333 : InSquare (-17/160) (63/160) (1/160) tau := by
            convert childUR hs23233 hx23233 hy23233 using 1 <;> norm_num
          exact (outside_232333 htau hs232333).elim

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2323
