import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0302
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0472
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0473
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0474
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0475
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0476
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0477
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0478

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3233

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

private theorem outside_32332 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (13/80) (31/80) (1/80) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (3/20 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-3/20)]
  have himSq : (3/8 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-3/8)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_32333 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (3/16) (31/80) (1/80) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (7/40 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-7/40)]
  have himSq : (3/8 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-3/8)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_323312 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (29/160) (59/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (7/40 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-7/40)]
  have himSq : (29/80 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-29/80)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_323313 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (31/160) (59/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (3/16 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-3/16)]
  have himSq : (29/80 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-29/80)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_3233023 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (51/320) (119/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (5/32 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-5/32)]
  have himSq : (59/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-59/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_3233032 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (53/320) (119/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (13/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-13/80)]
  have himSq : (59/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-59/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_3233033 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (11/64) (119/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (27/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-27/160)]
  have himSq : (59/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-59/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_3233111 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (63/320) (113/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (31/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-31/160)]
  have himSq : (7/20 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-7/20)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_3233112 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (61/320) (23/64) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (3/16 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-3/16)]
  have himSq : (57/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-57/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_3233113 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (63/320) (23/64) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (31/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-31/160)]
  have himSq : (57/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-57/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_32330222 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (97/640) (239/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (3/20 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-3/20)]
  have himSq : (119/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-119/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_32330223 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (99/640) (239/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (49/320 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-49/320)]
  have himSq : (119/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-119/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_32330302 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (21/128) (47/128) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (13/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-13/80)]
  have himSq : (117/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-117/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_32330303 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (107/640) (47/128) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (53/320 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-53/320)]
  have himSq : (117/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-117/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_32330311 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (111/640) (233/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (11/64 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-11/64)]
  have himSq : (29/80 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-29/80)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_32330312 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (109/640) (47/128) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (27/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-27/160)]
  have himSq : (117/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-117/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_32330313 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (111/640) (47/128) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (11/64 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-11/64)]
  have himSq : (117/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-117/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_32331023 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (23/128) (231/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (57/320 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-57/320)]
  have himSq : (23/64 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-23/64)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_32331031 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (119/640) (229/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (59/320 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-59/320)]
  have himSq : (57/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-57/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_32331032 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (117/640) (231/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (29/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-29/160)]
  have himSq : (23/64 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-23/64)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_32331033 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (119/640) (231/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (59/320 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-59/320)]
  have himSq : (23/64 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-23/64)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_32331103 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (123/640) (227/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (61/320 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-61/320)]
  have himSq : (113/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-113/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (7/40) (3/8) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (7/40 : ℝ) with hx3233 | hx3233
  · rcases le_total tau.im (3/8 : ℝ) with hy3233 | hy3233
    · have hs32330 : InSquare (13/80) (29/80) (1/80) tau := by
        convert childLL hs hx3233 hy3233 using 1 <;> norm_num
      rcases le_total tau.re (13/80 : ℝ) with hx32330 | hx32330
      · rcases le_total tau.im (29/80 : ℝ) with hy32330 | hy32330
        · have hs323300 : InSquare (5/32) (57/160) (1/160) tau := by
            convert childLL hs32330 hx32330 hy32330 using 1 <;> norm_num
          rcases le_total tau.re (5/32 : ℝ) with hx323300 | hx323300
          · rcases le_total tau.im (57/160 : ℝ) with hy323300 | hy323300
            · have hs3233000 : InSquare (49/320) (113/320) (1/320) tau := by
                convert childLL hs323300 hx323300 hy323300 using 1 <;> norm_num
              exact Batch0302.cell2417.sound htau (by
                simp only [Batch0302.cell2417, Batch0302.tau2417, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3233000 (by positivity) using 1 <;> norm_num)
            · have hs3233002 : InSquare (49/320) (23/64) (1/320) tau := by
                convert childUL hs323300 hx323300 hy323300 using 1 <;> norm_num
              rcases le_total tau.re (49/320 : ℝ) with hx3233002 | hx3233002
              · rcases le_total tau.im (23/64 : ℝ) with hy3233002 | hy3233002
                · have hs32330020 : InSquare (97/640) (229/640) (1/640) tau := by
                    convert childLL hs3233002 hx3233002 hy3233002 using 1 <;> norm_num
                  exact Batch0472.cell3781.sound htau (by
                    simp only [Batch0472.cell3781, Batch0472.tau3781, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32330020 (by positivity) using 1 <;> norm_num)
                · have hs32330022 : InSquare (97/640) (231/640) (1/640) tau := by
                    convert childUL hs3233002 hx3233002 hy3233002 using 1 <;> norm_num
                  exact Batch0472.cell3783.sound htau (by
                    simp only [Batch0472.cell3783, Batch0472.tau3783, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32330022 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (23/64 : ℝ) with hy3233002 | hy3233002
                · have hs32330021 : InSquare (99/640) (229/640) (1/640) tau := by
                    convert childLR hs3233002 hx3233002 hy3233002 using 1 <;> norm_num
                  exact Batch0472.cell3782.sound htau (by
                    simp only [Batch0472.cell3782, Batch0472.tau3782, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32330021 (by positivity) using 1 <;> norm_num)
                · have hs32330023 : InSquare (99/640) (231/640) (1/640) tau := by
                    convert childUR hs3233002 hx3233002 hy3233002 using 1 <;> norm_num
                  exact Batch0473.cell3784.sound htau (by
                    simp only [Batch0473.cell3784, Batch0473.tau3784, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32330023 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (57/160 : ℝ) with hy323300 | hy323300
            · have hs3233001 : InSquare (51/320) (113/320) (1/320) tau := by
                convert childLR hs323300 hx323300 hy323300 using 1 <;> norm_num
              exact Batch0302.cell2418.sound htau (by
                simp only [Batch0302.cell2418, Batch0302.tau2418, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3233001 (by positivity) using 1 <;> norm_num)
            · have hs3233003 : InSquare (51/320) (23/64) (1/320) tau := by
                convert childUR hs323300 hx323300 hy323300 using 1 <;> norm_num
              rcases le_total tau.re (51/320 : ℝ) with hx3233003 | hx3233003
              · rcases le_total tau.im (23/64 : ℝ) with hy3233003 | hy3233003
                · have hs32330030 : InSquare (101/640) (229/640) (1/640) tau := by
                    convert childLL hs3233003 hx3233003 hy3233003 using 1 <;> norm_num
                  exact Batch0473.cell3785.sound htau (by
                    simp only [Batch0473.cell3785, Batch0473.tau3785, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32330030 (by positivity) using 1 <;> norm_num)
                · have hs32330032 : InSquare (101/640) (231/640) (1/640) tau := by
                    convert childUL hs3233003 hx3233003 hy3233003 using 1 <;> norm_num
                  exact Batch0473.cell3787.sound htau (by
                    simp only [Batch0473.cell3787, Batch0473.tau3787, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32330032 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (23/64 : ℝ) with hy3233003 | hy3233003
                · have hs32330031 : InSquare (103/640) (229/640) (1/640) tau := by
                    convert childLR hs3233003 hx3233003 hy3233003 using 1 <;> norm_num
                  exact Batch0473.cell3786.sound htau (by
                    simp only [Batch0473.cell3786, Batch0473.tau3786, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32330031 (by positivity) using 1 <;> norm_num)
                · have hs32330033 : InSquare (103/640) (231/640) (1/640) tau := by
                    convert childUR hs3233003 hx3233003 hy3233003 using 1 <;> norm_num
                  exact Batch0473.cell3788.sound htau (by
                    simp only [Batch0473.cell3788, Batch0473.tau3788, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32330033 (by positivity) using 1 <;> norm_num)
        · have hs323302 : InSquare (5/32) (59/160) (1/160) tau := by
            convert childUL hs32330 hx32330 hy32330 using 1 <;> norm_num
          rcases le_total tau.re (5/32 : ℝ) with hx323302 | hx323302
          · rcases le_total tau.im (59/160 : ℝ) with hy323302 | hy323302
            · have hs3233020 : InSquare (49/320) (117/320) (1/320) tau := by
                convert childLL hs323302 hx323302 hy323302 using 1 <;> norm_num
              rcases le_total tau.re (49/320 : ℝ) with hx3233020 | hx3233020
              · rcases le_total tau.im (117/320 : ℝ) with hy3233020 | hy3233020
                · have hs32330200 : InSquare (97/640) (233/640) (1/640) tau := by
                    convert childLL hs3233020 hx3233020 hy3233020 using 1 <;> norm_num
                  exact Batch0475.cell3801.sound htau (by
                    simp only [Batch0475.cell3801, Batch0475.tau3801, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32330200 (by positivity) using 1 <;> norm_num)
                · have hs32330202 : InSquare (97/640) (47/128) (1/640) tau := by
                    convert childUL hs3233020 hx3233020 hy3233020 using 1 <;> norm_num
                  exact Batch0475.cell3803.sound htau (by
                    simp only [Batch0475.cell3803, Batch0475.tau3803, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32330202 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (117/320 : ℝ) with hy3233020 | hy3233020
                · have hs32330201 : InSquare (99/640) (233/640) (1/640) tau := by
                    convert childLR hs3233020 hx3233020 hy3233020 using 1 <;> norm_num
                  exact Batch0475.cell3802.sound htau (by
                    simp only [Batch0475.cell3802, Batch0475.tau3802, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32330201 (by positivity) using 1 <;> norm_num)
                · have hs32330203 : InSquare (99/640) (47/128) (1/640) tau := by
                    convert childUR hs3233020 hx3233020 hy3233020 using 1 <;> norm_num
                  exact Batch0475.cell3804.sound htau (by
                    simp only [Batch0475.cell3804, Batch0475.tau3804, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32330203 (by positivity) using 1 <;> norm_num)
            · have hs3233022 : InSquare (49/320) (119/320) (1/320) tau := by
                convert childUL hs323302 hx323302 hy323302 using 1 <;> norm_num
              rcases le_total tau.re (49/320 : ℝ) with hx3233022 | hx3233022
              · rcases le_total tau.im (119/320 : ℝ) with hy3233022 | hy3233022
                · have hs32330220 : InSquare (97/640) (237/640) (1/640) tau := by
                    convert childLL hs3233022 hx3233022 hy3233022 using 1 <;> norm_num
                  exact Batch0476.cell3809.sound htau (by
                    simp only [Batch0476.cell3809, Batch0476.tau3809, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32330220 (by positivity) using 1 <;> norm_num)
                · have hs32330222 : InSquare (97/640) (239/640) (1/640) tau := by
                    convert childUL hs3233022 hx3233022 hy3233022 using 1 <;> norm_num
                  exact (outside_32330222 htau hs32330222).elim
              · rcases le_total tau.im (119/320 : ℝ) with hy3233022 | hy3233022
                · have hs32330221 : InSquare (99/640) (237/640) (1/640) tau := by
                    convert childLR hs3233022 hx3233022 hy3233022 using 1 <;> norm_num
                  exact Batch0476.cell3810.sound htau (by
                    simp only [Batch0476.cell3810, Batch0476.tau3810, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32330221 (by positivity) using 1 <;> norm_num)
                · have hs32330223 : InSquare (99/640) (239/640) (1/640) tau := by
                    convert childUR hs3233022 hx3233022 hy3233022 using 1 <;> norm_num
                  exact (outside_32330223 htau hs32330223).elim
          · rcases le_total tau.im (59/160 : ℝ) with hy323302 | hy323302
            · have hs3233021 : InSquare (51/320) (117/320) (1/320) tau := by
                convert childLR hs323302 hx323302 hy323302 using 1 <;> norm_num
              rcases le_total tau.re (51/320 : ℝ) with hx3233021 | hx3233021
              · rcases le_total tau.im (117/320 : ℝ) with hy3233021 | hy3233021
                · have hs32330210 : InSquare (101/640) (233/640) (1/640) tau := by
                    convert childLL hs3233021 hx3233021 hy3233021 using 1 <;> norm_num
                  exact Batch0475.cell3805.sound htau (by
                    simp only [Batch0475.cell3805, Batch0475.tau3805, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32330210 (by positivity) using 1 <;> norm_num)
                · have hs32330212 : InSquare (101/640) (47/128) (1/640) tau := by
                    convert childUL hs3233021 hx3233021 hy3233021 using 1 <;> norm_num
                  exact Batch0475.cell3807.sound htau (by
                    simp only [Batch0475.cell3807, Batch0475.tau3807, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32330212 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (117/320 : ℝ) with hy3233021 | hy3233021
                · have hs32330211 : InSquare (103/640) (233/640) (1/640) tau := by
                    convert childLR hs3233021 hx3233021 hy3233021 using 1 <;> norm_num
                  exact Batch0475.cell3806.sound htau (by
                    simp only [Batch0475.cell3806, Batch0475.tau3806, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32330211 (by positivity) using 1 <;> norm_num)
                · have hs32330213 : InSquare (103/640) (47/128) (1/640) tau := by
                    convert childUR hs3233021 hx3233021 hy3233021 using 1 <;> norm_num
                  exact Batch0476.cell3808.sound htau (by
                    simp only [Batch0476.cell3808, Batch0476.tau3808, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32330213 (by positivity) using 1 <;> norm_num)
            · have hs3233023 : InSquare (51/320) (119/320) (1/320) tau := by
                convert childUR hs323302 hx323302 hy323302 using 1 <;> norm_num
              exact (outside_3233023 htau hs3233023).elim
      · rcases le_total tau.im (29/80 : ℝ) with hy32330 | hy32330
        · have hs323301 : InSquare (27/160) (57/160) (1/160) tau := by
            convert childLR hs32330 hx32330 hy32330 using 1 <;> norm_num
          rcases le_total tau.re (27/160 : ℝ) with hx323301 | hx323301
          · rcases le_total tau.im (57/160 : ℝ) with hy323301 | hy323301
            · have hs3233010 : InSquare (53/320) (113/320) (1/320) tau := by
                convert childLL hs323301 hx323301 hy323301 using 1 <;> norm_num
              exact Batch0302.cell2419.sound htau (by
                simp only [Batch0302.cell2419, Batch0302.tau2419, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3233010 (by positivity) using 1 <;> norm_num)
            · have hs3233012 : InSquare (53/320) (23/64) (1/320) tau := by
                convert childUL hs323301 hx323301 hy323301 using 1 <;> norm_num
              rcases le_total tau.re (53/320 : ℝ) with hx3233012 | hx3233012
              · rcases le_total tau.im (23/64 : ℝ) with hy3233012 | hy3233012
                · have hs32330120 : InSquare (21/128) (229/640) (1/640) tau := by
                    convert childLL hs3233012 hx3233012 hy3233012 using 1 <;> norm_num
                  exact Batch0474.cell3793.sound htau (by
                    simp only [Batch0474.cell3793, Batch0474.tau3793, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32330120 (by positivity) using 1 <;> norm_num)
                · have hs32330122 : InSquare (21/128) (231/640) (1/640) tau := by
                    convert childUL hs3233012 hx3233012 hy3233012 using 1 <;> norm_num
                  exact Batch0474.cell3795.sound htau (by
                    simp only [Batch0474.cell3795, Batch0474.tau3795, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32330122 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (23/64 : ℝ) with hy3233012 | hy3233012
                · have hs32330121 : InSquare (107/640) (229/640) (1/640) tau := by
                    convert childLR hs3233012 hx3233012 hy3233012 using 1 <;> norm_num
                  exact Batch0474.cell3794.sound htau (by
                    simp only [Batch0474.cell3794, Batch0474.tau3794, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32330121 (by positivity) using 1 <;> norm_num)
                · have hs32330123 : InSquare (107/640) (231/640) (1/640) tau := by
                    convert childUR hs3233012 hx3233012 hy3233012 using 1 <;> norm_num
                  exact Batch0474.cell3796.sound htau (by
                    simp only [Batch0474.cell3796, Batch0474.tau3796, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32330123 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (57/160 : ℝ) with hy323301 | hy323301
            · have hs3233011 : InSquare (11/64) (113/320) (1/320) tau := by
                convert childLR hs323301 hx323301 hy323301 using 1 <;> norm_num
              rcases le_total tau.re (11/64 : ℝ) with hx3233011 | hx3233011
              · rcases le_total tau.im (113/320 : ℝ) with hy3233011 | hy3233011
                · have hs32330110 : InSquare (109/640) (45/128) (1/640) tau := by
                    convert childLL hs3233011 hx3233011 hy3233011 using 1 <;> norm_num
                  exact Batch0473.cell3789.sound htau (by
                    simp only [Batch0473.cell3789, Batch0473.tau3789, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32330110 (by positivity) using 1 <;> norm_num)
                · have hs32330112 : InSquare (109/640) (227/640) (1/640) tau := by
                    convert childUL hs3233011 hx3233011 hy3233011 using 1 <;> norm_num
                  exact Batch0473.cell3791.sound htau (by
                    simp only [Batch0473.cell3791, Batch0473.tau3791, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32330112 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (113/320 : ℝ) with hy3233011 | hy3233011
                · have hs32330111 : InSquare (111/640) (45/128) (1/640) tau := by
                    convert childLR hs3233011 hx3233011 hy3233011 using 1 <;> norm_num
                  exact Batch0473.cell3790.sound htau (by
                    simp only [Batch0473.cell3790, Batch0473.tau3790, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32330111 (by positivity) using 1 <;> norm_num)
                · have hs32330113 : InSquare (111/640) (227/640) (1/640) tau := by
                    convert childUR hs3233011 hx3233011 hy3233011 using 1 <;> norm_num
                  exact Batch0474.cell3792.sound htau (by
                    simp only [Batch0474.cell3792, Batch0474.tau3792, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32330113 (by positivity) using 1 <;> norm_num)
            · have hs3233013 : InSquare (11/64) (23/64) (1/320) tau := by
                convert childUR hs323301 hx323301 hy323301 using 1 <;> norm_num
              rcases le_total tau.re (11/64 : ℝ) with hx3233013 | hx3233013
              · rcases le_total tau.im (23/64 : ℝ) with hy3233013 | hy3233013
                · have hs32330130 : InSquare (109/640) (229/640) (1/640) tau := by
                    convert childLL hs3233013 hx3233013 hy3233013 using 1 <;> norm_num
                  exact Batch0474.cell3797.sound htau (by
                    simp only [Batch0474.cell3797, Batch0474.tau3797, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32330130 (by positivity) using 1 <;> norm_num)
                · have hs32330132 : InSquare (109/640) (231/640) (1/640) tau := by
                    convert childUL hs3233013 hx3233013 hy3233013 using 1 <;> norm_num
                  exact Batch0474.cell3799.sound htau (by
                    simp only [Batch0474.cell3799, Batch0474.tau3799, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32330132 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (23/64 : ℝ) with hy3233013 | hy3233013
                · have hs32330131 : InSquare (111/640) (229/640) (1/640) tau := by
                    convert childLR hs3233013 hx3233013 hy3233013 using 1 <;> norm_num
                  exact Batch0474.cell3798.sound htau (by
                    simp only [Batch0474.cell3798, Batch0474.tau3798, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32330131 (by positivity) using 1 <;> norm_num)
                · have hs32330133 : InSquare (111/640) (231/640) (1/640) tau := by
                    convert childUR hs3233013 hx3233013 hy3233013 using 1 <;> norm_num
                  exact Batch0475.cell3800.sound htau (by
                    simp only [Batch0475.cell3800, Batch0475.tau3800, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32330133 (by positivity) using 1 <;> norm_num)
        · have hs323303 : InSquare (27/160) (59/160) (1/160) tau := by
            convert childUR hs32330 hx32330 hy32330 using 1 <;> norm_num
          rcases le_total tau.re (27/160 : ℝ) with hx323303 | hx323303
          · rcases le_total tau.im (59/160 : ℝ) with hy323303 | hy323303
            · have hs3233030 : InSquare (53/320) (117/320) (1/320) tau := by
                convert childLL hs323303 hx323303 hy323303 using 1 <;> norm_num
              rcases le_total tau.re (53/320 : ℝ) with hx3233030 | hx3233030
              · rcases le_total tau.im (117/320 : ℝ) with hy3233030 | hy3233030
                · have hs32330300 : InSquare (21/128) (233/640) (1/640) tau := by
                    convert childLL hs3233030 hx3233030 hy3233030 using 1 <;> norm_num
                  exact Batch0476.cell3811.sound htau (by
                    simp only [Batch0476.cell3811, Batch0476.tau3811, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32330300 (by positivity) using 1 <;> norm_num)
                · have hs32330302 : InSquare (21/128) (47/128) (1/640) tau := by
                    convert childUL hs3233030 hx3233030 hy3233030 using 1 <;> norm_num
                  exact (outside_32330302 htau hs32330302).elim
              · rcases le_total tau.im (117/320 : ℝ) with hy3233030 | hy3233030
                · have hs32330301 : InSquare (107/640) (233/640) (1/640) tau := by
                    convert childLR hs3233030 hx3233030 hy3233030 using 1 <;> norm_num
                  exact Batch0476.cell3812.sound htau (by
                    simp only [Batch0476.cell3812, Batch0476.tau3812, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32330301 (by positivity) using 1 <;> norm_num)
                · have hs32330303 : InSquare (107/640) (47/128) (1/640) tau := by
                    convert childUR hs3233030 hx3233030 hy3233030 using 1 <;> norm_num
                  exact (outside_32330303 htau hs32330303).elim
            · have hs3233032 : InSquare (53/320) (119/320) (1/320) tau := by
                convert childUL hs323303 hx323303 hy323303 using 1 <;> norm_num
              exact (outside_3233032 htau hs3233032).elim
          · rcases le_total tau.im (59/160 : ℝ) with hy323303 | hy323303
            · have hs3233031 : InSquare (11/64) (117/320) (1/320) tau := by
                convert childLR hs323303 hx323303 hy323303 using 1 <;> norm_num
              rcases le_total tau.re (11/64 : ℝ) with hx3233031 | hx3233031
              · rcases le_total tau.im (117/320 : ℝ) with hy3233031 | hy3233031
                · have hs32330310 : InSquare (109/640) (233/640) (1/640) tau := by
                    convert childLL hs3233031 hx3233031 hy3233031 using 1 <;> norm_num
                  exact Batch0476.cell3813.sound htau (by
                    simp only [Batch0476.cell3813, Batch0476.tau3813, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32330310 (by positivity) using 1 <;> norm_num)
                · have hs32330312 : InSquare (109/640) (47/128) (1/640) tau := by
                    convert childUL hs3233031 hx3233031 hy3233031 using 1 <;> norm_num
                  exact (outside_32330312 htau hs32330312).elim
              · rcases le_total tau.im (117/320 : ℝ) with hy3233031 | hy3233031
                · have hs32330311 : InSquare (111/640) (233/640) (1/640) tau := by
                    convert childLR hs3233031 hx3233031 hy3233031 using 1 <;> norm_num
                  exact (outside_32330311 htau hs32330311).elim
                · have hs32330313 : InSquare (111/640) (47/128) (1/640) tau := by
                    convert childUR hs3233031 hx3233031 hy3233031 using 1 <;> norm_num
                  exact (outside_32330313 htau hs32330313).elim
            · have hs3233033 : InSquare (11/64) (119/320) (1/320) tau := by
                convert childUR hs323303 hx323303 hy323303 using 1 <;> norm_num
              exact (outside_3233033 htau hs3233033).elim
    · have hs32332 : InSquare (13/80) (31/80) (1/80) tau := by
        convert childUL hs hx3233 hy3233 using 1 <;> norm_num
      exact (outside_32332 htau hs32332).elim
  · rcases le_total tau.im (3/8 : ℝ) with hy3233 | hy3233
    · have hs32331 : InSquare (3/16) (29/80) (1/80) tau := by
        convert childLR hs hx3233 hy3233 using 1 <;> norm_num
      rcases le_total tau.re (3/16 : ℝ) with hx32331 | hx32331
      · rcases le_total tau.im (29/80 : ℝ) with hy32331 | hy32331
        · have hs323310 : InSquare (29/160) (57/160) (1/160) tau := by
            convert childLL hs32331 hx32331 hy32331 using 1 <;> norm_num
          rcases le_total tau.re (29/160 : ℝ) with hx323310 | hx323310
          · rcases le_total tau.im (57/160 : ℝ) with hy323310 | hy323310
            · have hs3233100 : InSquare (57/320) (113/320) (1/320) tau := by
                convert childLL hs323310 hx323310 hy323310 using 1 <;> norm_num
              rcases le_total tau.re (57/320 : ℝ) with hx3233100 | hx3233100
              · rcases le_total tau.im (113/320 : ℝ) with hy3233100 | hy3233100
                · have hs32331000 : InSquare (113/640) (45/128) (1/640) tau := by
                    convert childLL hs3233100 hx3233100 hy3233100 using 1 <;> norm_num
                  exact Batch0476.cell3814.sound htau (by
                    simp only [Batch0476.cell3814, Batch0476.tau3814, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32331000 (by positivity) using 1 <;> norm_num)
                · have hs32331002 : InSquare (113/640) (227/640) (1/640) tau := by
                    convert childUL hs3233100 hx3233100 hy3233100 using 1 <;> norm_num
                  exact Batch0477.cell3816.sound htau (by
                    simp only [Batch0477.cell3816, Batch0477.tau3816, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32331002 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (113/320 : ℝ) with hy3233100 | hy3233100
                · have hs32331001 : InSquare (23/128) (45/128) (1/640) tau := by
                    convert childLR hs3233100 hx3233100 hy3233100 using 1 <;> norm_num
                  exact Batch0476.cell3815.sound htau (by
                    simp only [Batch0476.cell3815, Batch0476.tau3815, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32331001 (by positivity) using 1 <;> norm_num)
                · have hs32331003 : InSquare (23/128) (227/640) (1/640) tau := by
                    convert childUR hs3233100 hx3233100 hy3233100 using 1 <;> norm_num
                  exact Batch0477.cell3817.sound htau (by
                    simp only [Batch0477.cell3817, Batch0477.tau3817, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32331003 (by positivity) using 1 <;> norm_num)
            · have hs3233102 : InSquare (57/320) (23/64) (1/320) tau := by
                convert childUL hs323310 hx323310 hy323310 using 1 <;> norm_num
              rcases le_total tau.re (57/320 : ℝ) with hx3233102 | hx3233102
              · rcases le_total tau.im (23/64 : ℝ) with hy3233102 | hy3233102
                · have hs32331020 : InSquare (113/640) (229/640) (1/640) tau := by
                    convert childLL hs3233102 hx3233102 hy3233102 using 1 <;> norm_num
                  exact Batch0477.cell3822.sound htau (by
                    simp only [Batch0477.cell3822, Batch0477.tau3822, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32331020 (by positivity) using 1 <;> norm_num)
                · have hs32331022 : InSquare (113/640) (231/640) (1/640) tau := by
                    convert childUL hs3233102 hx3233102 hy3233102 using 1 <;> norm_num
                  exact Batch0478.cell3824.sound htau (by
                    simp only [Batch0478.cell3824, Batch0478.tau3824, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32331022 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (23/64 : ℝ) with hy3233102 | hy3233102
                · have hs32331021 : InSquare (23/128) (229/640) (1/640) tau := by
                    convert childLR hs3233102 hx3233102 hy3233102 using 1 <;> norm_num
                  exact Batch0477.cell3823.sound htau (by
                    simp only [Batch0477.cell3823, Batch0477.tau3823, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32331021 (by positivity) using 1 <;> norm_num)
                · have hs32331023 : InSquare (23/128) (231/640) (1/640) tau := by
                    convert childUR hs3233102 hx3233102 hy3233102 using 1 <;> norm_num
                  exact (outside_32331023 htau hs32331023).elim
          · rcases le_total tau.im (57/160 : ℝ) with hy323310 | hy323310
            · have hs3233101 : InSquare (59/320) (113/320) (1/320) tau := by
                convert childLR hs323310 hx323310 hy323310 using 1 <;> norm_num
              rcases le_total tau.re (59/320 : ℝ) with hx3233101 | hx3233101
              · rcases le_total tau.im (113/320 : ℝ) with hy3233101 | hy3233101
                · have hs32331010 : InSquare (117/640) (45/128) (1/640) tau := by
                    convert childLL hs3233101 hx3233101 hy3233101 using 1 <;> norm_num
                  exact Batch0477.cell3818.sound htau (by
                    simp only [Batch0477.cell3818, Batch0477.tau3818, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32331010 (by positivity) using 1 <;> norm_num)
                · have hs32331012 : InSquare (117/640) (227/640) (1/640) tau := by
                    convert childUL hs3233101 hx3233101 hy3233101 using 1 <;> norm_num
                  exact Batch0477.cell3820.sound htau (by
                    simp only [Batch0477.cell3820, Batch0477.tau3820, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32331012 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (113/320 : ℝ) with hy3233101 | hy3233101
                · have hs32331011 : InSquare (119/640) (45/128) (1/640) tau := by
                    convert childLR hs3233101 hx3233101 hy3233101 using 1 <;> norm_num
                  exact Batch0477.cell3819.sound htau (by
                    simp only [Batch0477.cell3819, Batch0477.tau3819, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32331011 (by positivity) using 1 <;> norm_num)
                · have hs32331013 : InSquare (119/640) (227/640) (1/640) tau := by
                    convert childUR hs3233101 hx3233101 hy3233101 using 1 <;> norm_num
                  exact Batch0477.cell3821.sound htau (by
                    simp only [Batch0477.cell3821, Batch0477.tau3821, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32331013 (by positivity) using 1 <;> norm_num)
            · have hs3233103 : InSquare (59/320) (23/64) (1/320) tau := by
                convert childUR hs323310 hx323310 hy323310 using 1 <;> norm_num
              rcases le_total tau.re (59/320 : ℝ) with hx3233103 | hx3233103
              · rcases le_total tau.im (23/64 : ℝ) with hy3233103 | hy3233103
                · have hs32331030 : InSquare (117/640) (229/640) (1/640) tau := by
                    convert childLL hs3233103 hx3233103 hy3233103 using 1 <;> norm_num
                  exact Batch0478.cell3825.sound htau (by
                    simp only [Batch0478.cell3825, Batch0478.tau3825, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32331030 (by positivity) using 1 <;> norm_num)
                · have hs32331032 : InSquare (117/640) (231/640) (1/640) tau := by
                    convert childUL hs3233103 hx3233103 hy3233103 using 1 <;> norm_num
                  exact (outside_32331032 htau hs32331032).elim
              · rcases le_total tau.im (23/64 : ℝ) with hy3233103 | hy3233103
                · have hs32331031 : InSquare (119/640) (229/640) (1/640) tau := by
                    convert childLR hs3233103 hx3233103 hy3233103 using 1 <;> norm_num
                  exact (outside_32331031 htau hs32331031).elim
                · have hs32331033 : InSquare (119/640) (231/640) (1/640) tau := by
                    convert childUR hs3233103 hx3233103 hy3233103 using 1 <;> norm_num
                  exact (outside_32331033 htau hs32331033).elim
        · have hs323312 : InSquare (29/160) (59/160) (1/160) tau := by
            convert childUL hs32331 hx32331 hy32331 using 1 <;> norm_num
          exact (outside_323312 htau hs323312).elim
      · rcases le_total tau.im (29/80 : ℝ) with hy32331 | hy32331
        · have hs323311 : InSquare (31/160) (57/160) (1/160) tau := by
            convert childLR hs32331 hx32331 hy32331 using 1 <;> norm_num
          rcases le_total tau.re (31/160 : ℝ) with hx323311 | hx323311
          · rcases le_total tau.im (57/160 : ℝ) with hy323311 | hy323311
            · have hs3233110 : InSquare (61/320) (113/320) (1/320) tau := by
                convert childLL hs323311 hx323311 hy323311 using 1 <;> norm_num
              rcases le_total tau.re (61/320 : ℝ) with hx3233110 | hx3233110
              · rcases le_total tau.im (113/320 : ℝ) with hy3233110 | hy3233110
                · have hs32331100 : InSquare (121/640) (45/128) (1/640) tau := by
                    convert childLL hs3233110 hx3233110 hy3233110 using 1 <;> norm_num
                  exact Batch0478.cell3826.sound htau (by
                    simp only [Batch0478.cell3826, Batch0478.tau3826, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32331100 (by positivity) using 1 <;> norm_num)
                · have hs32331102 : InSquare (121/640) (227/640) (1/640) tau := by
                    convert childUL hs3233110 hx3233110 hy3233110 using 1 <;> norm_num
                  exact Batch0478.cell3828.sound htau (by
                    simp only [Batch0478.cell3828, Batch0478.tau3828, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32331102 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (113/320 : ℝ) with hy3233110 | hy3233110
                · have hs32331101 : InSquare (123/640) (45/128) (1/640) tau := by
                    convert childLR hs3233110 hx3233110 hy3233110 using 1 <;> norm_num
                  exact Batch0478.cell3827.sound htau (by
                    simp only [Batch0478.cell3827, Batch0478.tau3827, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32331101 (by positivity) using 1 <;> norm_num)
                · have hs32331103 : InSquare (123/640) (227/640) (1/640) tau := by
                    convert childUR hs3233110 hx3233110 hy3233110 using 1 <;> norm_num
                  exact (outside_32331103 htau hs32331103).elim
            · have hs3233112 : InSquare (61/320) (23/64) (1/320) tau := by
                convert childUL hs323311 hx323311 hy323311 using 1 <;> norm_num
              exact (outside_3233112 htau hs3233112).elim
          · rcases le_total tau.im (57/160 : ℝ) with hy323311 | hy323311
            · have hs3233111 : InSquare (63/320) (113/320) (1/320) tau := by
                convert childLR hs323311 hx323311 hy323311 using 1 <;> norm_num
              exact (outside_3233111 htau hs3233111).elim
            · have hs3233113 : InSquare (63/320) (23/64) (1/320) tau := by
                convert childUR hs323311 hx323311 hy323311 using 1 <;> norm_num
              exact (outside_3233113 htau hs3233113).elim
        · have hs323313 : InSquare (31/160) (59/160) (1/160) tau := by
            convert childUR hs32331 hx32331 hy32331 using 1 <;> norm_num
          exact (outside_323313 htau hs323313).elim
    · have hs32333 : InSquare (3/16) (31/80) (1/80) tau := by
        convert childUR hs hx3233 hy3233 using 1 <;> norm_num
      exact (outside_32333 htau hs32333).elim

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3233
