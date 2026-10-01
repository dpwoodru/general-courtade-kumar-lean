import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0299
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0300
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0301
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0302
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0461
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0462
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0463
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0464
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0465
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0466
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0467
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0468
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0469
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0470
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0471
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0472

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3232

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

private theorem outside_323222 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (17/160) (63/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (1/10 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-1/10)]
  have himSq : (31/80 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-31/80)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_323223 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (19/160) (63/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (9/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-9/80)]
  have himSq : (31/80 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-31/80)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_323232 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (21/160) (63/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (1/8 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-1/8)]
  have himSq : (31/80 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-31/80)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_323233 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (23/160) (63/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (11/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-11/80)]
  have himSq : (31/80 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-31/80)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_3232302 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (41/320) (123/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (1/8 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-1/8)]
  have himSq : (61/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-61/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_3232303 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (43/320) (123/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (21/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-21/160)]
  have himSq : (61/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-61/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_3232311 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (47/320) (121/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (23/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-23/160)]
  have himSq : (3/8 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-3/8)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_3232312 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (9/64) (123/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (11/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-11/80)]
  have himSq : (61/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-61/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_3232313 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (47/320) (123/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (23/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-23/160)]
  have himSq : (61/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-61/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_32322122 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (73/640) (247/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (9/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-9/80)]
  have himSq : (123/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-123/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_32322123 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (15/128) (247/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (37/320 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-37/320)]
  have himSq : (123/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-123/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_32322131 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (79/640) (49/128) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (39/320 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-39/320)]
  have himSq : (61/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-61/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_32322132 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (77/640) (247/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (19/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-19/160)]
  have himSq : (123/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-123/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_32322133 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (79/640) (247/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (39/320 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-39/320)]
  have himSq : (123/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-123/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_32323012 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (17/128) (243/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (21/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-21/160)]
  have himSq : (121/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-121/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_32323013 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (87/640) (243/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (43/320 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-43/320)]
  have himSq : (121/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-121/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_32323101 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (91/640) (241/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (9/64 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-9/64)]
  have himSq : (3/8 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-3/8)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_32323102 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (89/640) (243/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (11/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-11/80)]
  have himSq : (121/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-121/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_32323103 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (91/640) (243/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (9/64 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-9/64)]
  have himSq : (121/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-121/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (1/8) (3/8) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (1/8 : ℝ) with hx3232 | hx3232
  · rcases le_total tau.im (3/8 : ℝ) with hy3232 | hy3232
    · have hs32320 : InSquare (9/80) (29/80) (1/80) tau := by
        convert childLL hs hx3232 hy3232 using 1 <;> norm_num
      rcases le_total tau.re (9/80 : ℝ) with hx32320 | hx32320
      · rcases le_total tau.im (29/80 : ℝ) with hy32320 | hy32320
        · have hs323200 : InSquare (17/160) (57/160) (1/160) tau := by
            convert childLL hs32320 hx32320 hy32320 using 1 <;> norm_num
          rcases le_total tau.re (17/160 : ℝ) with hx323200 | hx323200
          · rcases le_total tau.im (57/160 : ℝ) with hy323200 | hy323200
            · have hs3232000 : InSquare (33/320) (113/320) (1/320) tau := by
                convert childLL hs323200 hx323200 hy323200 using 1 <;> norm_num
              exact Batch0299.cell2398.sound htau (by
                simp only [Batch0299.cell2398, Batch0299.tau2398, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3232000 (by positivity) using 1 <;> norm_num)
            · have hs3232002 : InSquare (33/320) (23/64) (1/320) tau := by
                convert childUL hs323200 hx323200 hy323200 using 1 <;> norm_num
              exact Batch0300.cell2400.sound htau (by
                simp only [Batch0300.cell2400, Batch0300.tau2400, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3232002 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (57/160 : ℝ) with hy323200 | hy323200
            · have hs3232001 : InSquare (7/64) (113/320) (1/320) tau := by
                convert childLR hs323200 hx323200 hy323200 using 1 <;> norm_num
              exact Batch0299.cell2399.sound htau (by
                simp only [Batch0299.cell2399, Batch0299.tau2399, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3232001 (by positivity) using 1 <;> norm_num)
            · have hs3232003 : InSquare (7/64) (23/64) (1/320) tau := by
                convert childUR hs323200 hx323200 hy323200 using 1 <;> norm_num
              exact Batch0300.cell2401.sound htau (by
                simp only [Batch0300.cell2401, Batch0300.tau2401, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3232003 (by positivity) using 1 <;> norm_num)
        · have hs323202 : InSquare (17/160) (59/160) (1/160) tau := by
            convert childUL hs32320 hx32320 hy32320 using 1 <;> norm_num
          rcases le_total tau.re (17/160 : ℝ) with hx323202 | hx323202
          · rcases le_total tau.im (59/160 : ℝ) with hy323202 | hy323202
            · have hs3232020 : InSquare (33/320) (117/320) (1/320) tau := by
                convert childLL hs323202 hx323202 hy323202 using 1 <;> norm_num
              exact Batch0300.cell2406.sound htau (by
                simp only [Batch0300.cell2406, Batch0300.tau2406, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3232020 (by positivity) using 1 <;> norm_num)
            · have hs3232022 : InSquare (33/320) (119/320) (1/320) tau := by
                convert childUL hs323202 hx323202 hy323202 using 1 <;> norm_num
              rcases le_total tau.re (33/320 : ℝ) with hx3232022 | hx3232022
              · rcases le_total tau.im (119/320 : ℝ) with hy3232022 | hy3232022
                · have hs32320220 : InSquare (13/128) (237/640) (1/640) tau := by
                    convert childLL hs3232022 hx3232022 hy3232022 using 1 <;> norm_num
                  exact Batch0461.cell3695.sound htau (by
                    simp only [Batch0461.cell3695, Batch0461.tau3695, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32320220 (by positivity) using 1 <;> norm_num)
                · have hs32320222 : InSquare (13/128) (239/640) (1/640) tau := by
                    convert childUL hs3232022 hx3232022 hy3232022 using 1 <;> norm_num
                  exact Batch0462.cell3697.sound htau (by
                    simp only [Batch0462.cell3697, Batch0462.tau3697, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32320222 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (119/320 : ℝ) with hy3232022 | hy3232022
                · have hs32320221 : InSquare (67/640) (237/640) (1/640) tau := by
                    convert childLR hs3232022 hx3232022 hy3232022 using 1 <;> norm_num
                  exact Batch0462.cell3696.sound htau (by
                    simp only [Batch0462.cell3696, Batch0462.tau3696, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32320221 (by positivity) using 1 <;> norm_num)
                · have hs32320223 : InSquare (67/640) (239/640) (1/640) tau := by
                    convert childUR hs3232022 hx3232022 hy3232022 using 1 <;> norm_num
                  exact Batch0462.cell3698.sound htau (by
                    simp only [Batch0462.cell3698, Batch0462.tau3698, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32320223 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (59/160 : ℝ) with hy323202 | hy323202
            · have hs3232021 : InSquare (7/64) (117/320) (1/320) tau := by
                convert childLR hs323202 hx323202 hy323202 using 1 <;> norm_num
              exact Batch0300.cell2407.sound htau (by
                simp only [Batch0300.cell2407, Batch0300.tau2407, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3232021 (by positivity) using 1 <;> norm_num)
            · have hs3232023 : InSquare (7/64) (119/320) (1/320) tau := by
                convert childUR hs323202 hx323202 hy323202 using 1 <;> norm_num
              rcases le_total tau.re (7/64 : ℝ) with hx3232023 | hx3232023
              · rcases le_total tau.im (119/320 : ℝ) with hy3232023 | hy3232023
                · have hs32320230 : InSquare (69/640) (237/640) (1/640) tau := by
                    convert childLL hs3232023 hx3232023 hy3232023 using 1 <;> norm_num
                  exact Batch0462.cell3699.sound htau (by
                    simp only [Batch0462.cell3699, Batch0462.tau3699, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32320230 (by positivity) using 1 <;> norm_num)
                · have hs32320232 : InSquare (69/640) (239/640) (1/640) tau := by
                    convert childUL hs3232023 hx3232023 hy3232023 using 1 <;> norm_num
                  exact Batch0462.cell3701.sound htau (by
                    simp only [Batch0462.cell3701, Batch0462.tau3701, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32320232 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (119/320 : ℝ) with hy3232023 | hy3232023
                · have hs32320231 : InSquare (71/640) (237/640) (1/640) tau := by
                    convert childLR hs3232023 hx3232023 hy3232023 using 1 <;> norm_num
                  exact Batch0462.cell3700.sound htau (by
                    simp only [Batch0462.cell3700, Batch0462.tau3700, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32320231 (by positivity) using 1 <;> norm_num)
                · have hs32320233 : InSquare (71/640) (239/640) (1/640) tau := by
                    convert childUR hs3232023 hx3232023 hy3232023 using 1 <;> norm_num
                  exact Batch0462.cell3702.sound htau (by
                    simp only [Batch0462.cell3702, Batch0462.tau3702, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32320233 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (29/80 : ℝ) with hy32320 | hy32320
        · have hs323201 : InSquare (19/160) (57/160) (1/160) tau := by
            convert childLR hs32320 hx32320 hy32320 using 1 <;> norm_num
          rcases le_total tau.re (19/160 : ℝ) with hx323201 | hx323201
          · rcases le_total tau.im (57/160 : ℝ) with hy323201 | hy323201
            · have hs3232010 : InSquare (37/320) (113/320) (1/320) tau := by
                convert childLL hs323201 hx323201 hy323201 using 1 <;> norm_num
              exact Batch0300.cell2402.sound htau (by
                simp only [Batch0300.cell2402, Batch0300.tau2402, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3232010 (by positivity) using 1 <;> norm_num)
            · have hs3232012 : InSquare (37/320) (23/64) (1/320) tau := by
                convert childUL hs323201 hx323201 hy323201 using 1 <;> norm_num
              exact Batch0300.cell2404.sound htau (by
                simp only [Batch0300.cell2404, Batch0300.tau2404, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3232012 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (57/160 : ℝ) with hy323201 | hy323201
            · have hs3232011 : InSquare (39/320) (113/320) (1/320) tau := by
                convert childLR hs323201 hx323201 hy323201 using 1 <;> norm_num
              exact Batch0300.cell2403.sound htau (by
                simp only [Batch0300.cell2403, Batch0300.tau2403, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3232011 (by positivity) using 1 <;> norm_num)
            · have hs3232013 : InSquare (39/320) (23/64) (1/320) tau := by
                convert childUR hs323201 hx323201 hy323201 using 1 <;> norm_num
              exact Batch0300.cell2405.sound htau (by
                simp only [Batch0300.cell2405, Batch0300.tau2405, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3232013 (by positivity) using 1 <;> norm_num)
        · have hs323203 : InSquare (19/160) (59/160) (1/160) tau := by
            convert childUR hs32320 hx32320 hy32320 using 1 <;> norm_num
          rcases le_total tau.re (19/160 : ℝ) with hx323203 | hx323203
          · rcases le_total tau.im (59/160 : ℝ) with hy323203 | hy323203
            · have hs3232030 : InSquare (37/320) (117/320) (1/320) tau := by
                convert childLL hs323203 hx323203 hy323203 using 1 <;> norm_num
              exact Batch0301.cell2408.sound htau (by
                simp only [Batch0301.cell2408, Batch0301.tau2408, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3232030 (by positivity) using 1 <;> norm_num)
            · have hs3232032 : InSquare (37/320) (119/320) (1/320) tau := by
                convert childUL hs323203 hx323203 hy323203 using 1 <;> norm_num
              rcases le_total tau.re (37/320 : ℝ) with hx3232032 | hx3232032
              · rcases le_total tau.im (119/320 : ℝ) with hy3232032 | hy3232032
                · have hs32320320 : InSquare (73/640) (237/640) (1/640) tau := by
                    convert childLL hs3232032 hx3232032 hy3232032 using 1 <;> norm_num
                  exact Batch0462.cell3703.sound htau (by
                    simp only [Batch0462.cell3703, Batch0462.tau3703, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32320320 (by positivity) using 1 <;> norm_num)
                · have hs32320322 : InSquare (73/640) (239/640) (1/640) tau := by
                    convert childUL hs3232032 hx3232032 hy3232032 using 1 <;> norm_num
                  exact Batch0463.cell3705.sound htau (by
                    simp only [Batch0463.cell3705, Batch0463.tau3705, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32320322 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (119/320 : ℝ) with hy3232032 | hy3232032
                · have hs32320321 : InSquare (15/128) (237/640) (1/640) tau := by
                    convert childLR hs3232032 hx3232032 hy3232032 using 1 <;> norm_num
                  exact Batch0463.cell3704.sound htau (by
                    simp only [Batch0463.cell3704, Batch0463.tau3704, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32320321 (by positivity) using 1 <;> norm_num)
                · have hs32320323 : InSquare (15/128) (239/640) (1/640) tau := by
                    convert childUR hs3232032 hx3232032 hy3232032 using 1 <;> norm_num
                  exact Batch0463.cell3706.sound htau (by
                    simp only [Batch0463.cell3706, Batch0463.tau3706, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32320323 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (59/160 : ℝ) with hy323203 | hy323203
            · have hs3232031 : InSquare (39/320) (117/320) (1/320) tau := by
                convert childLR hs323203 hx323203 hy323203 using 1 <;> norm_num
              exact Batch0301.cell2409.sound htau (by
                simp only [Batch0301.cell2409, Batch0301.tau2409, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3232031 (by positivity) using 1 <;> norm_num)
            · have hs3232033 : InSquare (39/320) (119/320) (1/320) tau := by
                convert childUR hs323203 hx323203 hy323203 using 1 <;> norm_num
              rcases le_total tau.re (39/320 : ℝ) with hx3232033 | hx3232033
              · rcases le_total tau.im (119/320 : ℝ) with hy3232033 | hy3232033
                · have hs32320330 : InSquare (77/640) (237/640) (1/640) tau := by
                    convert childLL hs3232033 hx3232033 hy3232033 using 1 <;> norm_num
                  exact Batch0463.cell3707.sound htau (by
                    simp only [Batch0463.cell3707, Batch0463.tau3707, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32320330 (by positivity) using 1 <;> norm_num)
                · have hs32320332 : InSquare (77/640) (239/640) (1/640) tau := by
                    convert childUL hs3232033 hx3232033 hy3232033 using 1 <;> norm_num
                  exact Batch0463.cell3709.sound htau (by
                    simp only [Batch0463.cell3709, Batch0463.tau3709, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32320332 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (119/320 : ℝ) with hy3232033 | hy3232033
                · have hs32320331 : InSquare (79/640) (237/640) (1/640) tau := by
                    convert childLR hs3232033 hx3232033 hy3232033 using 1 <;> norm_num
                  exact Batch0463.cell3708.sound htau (by
                    simp only [Batch0463.cell3708, Batch0463.tau3708, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32320331 (by positivity) using 1 <;> norm_num)
                · have hs32320333 : InSquare (79/640) (239/640) (1/640) tau := by
                    convert childUR hs3232033 hx3232033 hy3232033 using 1 <;> norm_num
                  exact Batch0463.cell3710.sound htau (by
                    simp only [Batch0463.cell3710, Batch0463.tau3710, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32320333 (by positivity) using 1 <;> norm_num)
    · have hs32322 : InSquare (9/80) (31/80) (1/80) tau := by
        convert childUL hs hx3232 hy3232 using 1 <;> norm_num
      rcases le_total tau.re (9/80 : ℝ) with hx32322 | hx32322
      · rcases le_total tau.im (31/80 : ℝ) with hy32322 | hy32322
        · have hs323220 : InSquare (17/160) (61/160) (1/160) tau := by
            convert childLL hs32322 hx32322 hy32322 using 1 <;> norm_num
          rcases le_total tau.re (17/160 : ℝ) with hx323220 | hx323220
          · rcases le_total tau.im (61/160 : ℝ) with hy323220 | hy323220
            · have hs3232200 : InSquare (33/320) (121/320) (1/320) tau := by
                convert childLL hs323220 hx323220 hy323220 using 1 <;> norm_num
              rcases le_total tau.re (33/320 : ℝ) with hx3232200 | hx3232200
              · rcases le_total tau.im (121/320 : ℝ) with hy3232200 | hy3232200
                · have hs32322000 : InSquare (13/128) (241/640) (1/640) tau := by
                    convert childLL hs3232200 hx3232200 hy3232200 using 1 <;> norm_num
                  exact Batch0468.cell3747.sound htau (by
                    simp only [Batch0468.cell3747, Batch0468.tau3747, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32322000 (by positivity) using 1 <;> norm_num)
                · have hs32322002 : InSquare (13/128) (243/640) (1/640) tau := by
                    convert childUL hs3232200 hx3232200 hy3232200 using 1 <;> norm_num
                  exact Batch0468.cell3749.sound htau (by
                    simp only [Batch0468.cell3749, Batch0468.tau3749, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32322002 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (121/320 : ℝ) with hy3232200 | hy3232200
                · have hs32322001 : InSquare (67/640) (241/640) (1/640) tau := by
                    convert childLR hs3232200 hx3232200 hy3232200 using 1 <;> norm_num
                  exact Batch0468.cell3748.sound htau (by
                    simp only [Batch0468.cell3748, Batch0468.tau3748, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32322001 (by positivity) using 1 <;> norm_num)
                · have hs32322003 : InSquare (67/640) (243/640) (1/640) tau := by
                    convert childUR hs3232200 hx3232200 hy3232200 using 1 <;> norm_num
                  exact Batch0468.cell3750.sound htau (by
                    simp only [Batch0468.cell3750, Batch0468.tau3750, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32322003 (by positivity) using 1 <;> norm_num)
            · have hs3232202 : InSquare (33/320) (123/320) (1/320) tau := by
                convert childUL hs323220 hx323220 hy323220 using 1 <;> norm_num
              rcases le_total tau.re (33/320 : ℝ) with hx3232202 | hx3232202
              · rcases le_total tau.im (123/320 : ℝ) with hy3232202 | hy3232202
                · have hs32322020 : InSquare (13/128) (49/128) (1/640) tau := by
                    convert childLL hs3232202 hx3232202 hy3232202 using 1 <;> norm_num
                  exact Batch0469.cell3755.sound htau (by
                    simp only [Batch0469.cell3755, Batch0469.tau3755, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32322020 (by positivity) using 1 <;> norm_num)
                · have hs32322022 : InSquare (13/128) (247/640) (1/640) tau := by
                    convert childUL hs3232202 hx3232202 hy3232202 using 1 <;> norm_num
                  exact Batch0469.cell3757.sound htau (by
                    simp only [Batch0469.cell3757, Batch0469.tau3757, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32322022 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (123/320 : ℝ) with hy3232202 | hy3232202
                · have hs32322021 : InSquare (67/640) (49/128) (1/640) tau := by
                    convert childLR hs3232202 hx3232202 hy3232202 using 1 <;> norm_num
                  exact Batch0469.cell3756.sound htau (by
                    simp only [Batch0469.cell3756, Batch0469.tau3756, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32322021 (by positivity) using 1 <;> norm_num)
                · have hs32322023 : InSquare (67/640) (247/640) (1/640) tau := by
                    convert childUR hs3232202 hx3232202 hy3232202 using 1 <;> norm_num
                  exact Batch0469.cell3758.sound htau (by
                    simp only [Batch0469.cell3758, Batch0469.tau3758, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32322023 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (61/160 : ℝ) with hy323220 | hy323220
            · have hs3232201 : InSquare (7/64) (121/320) (1/320) tau := by
                convert childLR hs323220 hx323220 hy323220 using 1 <;> norm_num
              rcases le_total tau.re (7/64 : ℝ) with hx3232201 | hx3232201
              · rcases le_total tau.im (121/320 : ℝ) with hy3232201 | hy3232201
                · have hs32322010 : InSquare (69/640) (241/640) (1/640) tau := by
                    convert childLL hs3232201 hx3232201 hy3232201 using 1 <;> norm_num
                  exact Batch0468.cell3751.sound htau (by
                    simp only [Batch0468.cell3751, Batch0468.tau3751, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32322010 (by positivity) using 1 <;> norm_num)
                · have hs32322012 : InSquare (69/640) (243/640) (1/640) tau := by
                    convert childUL hs3232201 hx3232201 hy3232201 using 1 <;> norm_num
                  exact Batch0469.cell3753.sound htau (by
                    simp only [Batch0469.cell3753, Batch0469.tau3753, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32322012 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (121/320 : ℝ) with hy3232201 | hy3232201
                · have hs32322011 : InSquare (71/640) (241/640) (1/640) tau := by
                    convert childLR hs3232201 hx3232201 hy3232201 using 1 <;> norm_num
                  exact Batch0469.cell3752.sound htau (by
                    simp only [Batch0469.cell3752, Batch0469.tau3752, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32322011 (by positivity) using 1 <;> norm_num)
                · have hs32322013 : InSquare (71/640) (243/640) (1/640) tau := by
                    convert childUR hs3232201 hx3232201 hy3232201 using 1 <;> norm_num
                  exact Batch0469.cell3754.sound htau (by
                    simp only [Batch0469.cell3754, Batch0469.tau3754, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32322013 (by positivity) using 1 <;> norm_num)
            · have hs3232203 : InSquare (7/64) (123/320) (1/320) tau := by
                convert childUR hs323220 hx323220 hy323220 using 1 <;> norm_num
              rcases le_total tau.re (7/64 : ℝ) with hx3232203 | hx3232203
              · rcases le_total tau.im (123/320 : ℝ) with hy3232203 | hy3232203
                · have hs32322030 : InSquare (69/640) (49/128) (1/640) tau := by
                    convert childLL hs3232203 hx3232203 hy3232203 using 1 <;> norm_num
                  exact Batch0469.cell3759.sound htau (by
                    simp only [Batch0469.cell3759, Batch0469.tau3759, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32322030 (by positivity) using 1 <;> norm_num)
                · have hs32322032 : InSquare (69/640) (247/640) (1/640) tau := by
                    convert childUL hs3232203 hx3232203 hy3232203 using 1 <;> norm_num
                  exact Batch0470.cell3761.sound htau (by
                    simp only [Batch0470.cell3761, Batch0470.tau3761, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32322032 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (123/320 : ℝ) with hy3232203 | hy3232203
                · have hs32322031 : InSquare (71/640) (49/128) (1/640) tau := by
                    convert childLR hs3232203 hx3232203 hy3232203 using 1 <;> norm_num
                  exact Batch0470.cell3760.sound htau (by
                    simp only [Batch0470.cell3760, Batch0470.tau3760, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32322031 (by positivity) using 1 <;> norm_num)
                · have hs32322033 : InSquare (71/640) (247/640) (1/640) tau := by
                    convert childUR hs3232203 hx3232203 hy3232203 using 1 <;> norm_num
                  exact Batch0470.cell3762.sound htau (by
                    simp only [Batch0470.cell3762, Batch0470.tau3762, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32322033 (by positivity) using 1 <;> norm_num)
        · have hs323222 : InSquare (17/160) (63/160) (1/160) tau := by
            convert childUL hs32322 hx32322 hy32322 using 1 <;> norm_num
          exact (outside_323222 htau hs323222).elim
      · rcases le_total tau.im (31/80 : ℝ) with hy32322 | hy32322
        · have hs323221 : InSquare (19/160) (61/160) (1/160) tau := by
            convert childLR hs32322 hx32322 hy32322 using 1 <;> norm_num
          rcases le_total tau.re (19/160 : ℝ) with hx323221 | hx323221
          · rcases le_total tau.im (61/160 : ℝ) with hy323221 | hy323221
            · have hs3232210 : InSquare (37/320) (121/320) (1/320) tau := by
                convert childLL hs323221 hx323221 hy323221 using 1 <;> norm_num
              rcases le_total tau.re (37/320 : ℝ) with hx3232210 | hx3232210
              · rcases le_total tau.im (121/320 : ℝ) with hy3232210 | hy3232210
                · have hs32322100 : InSquare (73/640) (241/640) (1/640) tau := by
                    convert childLL hs3232210 hx3232210 hy3232210 using 1 <;> norm_num
                  exact Batch0470.cell3763.sound htau (by
                    simp only [Batch0470.cell3763, Batch0470.tau3763, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32322100 (by positivity) using 1 <;> norm_num)
                · have hs32322102 : InSquare (73/640) (243/640) (1/640) tau := by
                    convert childUL hs3232210 hx3232210 hy3232210 using 1 <;> norm_num
                  exact Batch0470.cell3765.sound htau (by
                    simp only [Batch0470.cell3765, Batch0470.tau3765, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32322102 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (121/320 : ℝ) with hy3232210 | hy3232210
                · have hs32322101 : InSquare (15/128) (241/640) (1/640) tau := by
                    convert childLR hs3232210 hx3232210 hy3232210 using 1 <;> norm_num
                  exact Batch0470.cell3764.sound htau (by
                    simp only [Batch0470.cell3764, Batch0470.tau3764, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32322101 (by positivity) using 1 <;> norm_num)
                · have hs32322103 : InSquare (15/128) (243/640) (1/640) tau := by
                    convert childUR hs3232210 hx3232210 hy3232210 using 1 <;> norm_num
                  exact Batch0470.cell3766.sound htau (by
                    simp only [Batch0470.cell3766, Batch0470.tau3766, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32322103 (by positivity) using 1 <;> norm_num)
            · have hs3232212 : InSquare (37/320) (123/320) (1/320) tau := by
                convert childUL hs323221 hx323221 hy323221 using 1 <;> norm_num
              rcases le_total tau.re (37/320 : ℝ) with hx3232212 | hx3232212
              · rcases le_total tau.im (123/320 : ℝ) with hy3232212 | hy3232212
                · have hs32322120 : InSquare (73/640) (49/128) (1/640) tau := by
                    convert childLL hs3232212 hx3232212 hy3232212 using 1 <;> norm_num
                  exact Batch0471.cell3771.sound htau (by
                    simp only [Batch0471.cell3771, Batch0471.tau3771, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32322120 (by positivity) using 1 <;> norm_num)
                · have hs32322122 : InSquare (73/640) (247/640) (1/640) tau := by
                    convert childUL hs3232212 hx3232212 hy3232212 using 1 <;> norm_num
                  exact (outside_32322122 htau hs32322122).elim
              · rcases le_total tau.im (123/320 : ℝ) with hy3232212 | hy3232212
                · have hs32322121 : InSquare (15/128) (49/128) (1/640) tau := by
                    convert childLR hs3232212 hx3232212 hy3232212 using 1 <;> norm_num
                  exact Batch0471.cell3772.sound htau (by
                    simp only [Batch0471.cell3772, Batch0471.tau3772, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32322121 (by positivity) using 1 <;> norm_num)
                · have hs32322123 : InSquare (15/128) (247/640) (1/640) tau := by
                    convert childUR hs3232212 hx3232212 hy3232212 using 1 <;> norm_num
                  exact (outside_32322123 htau hs32322123).elim
          · rcases le_total tau.im (61/160 : ℝ) with hy323221 | hy323221
            · have hs3232211 : InSquare (39/320) (121/320) (1/320) tau := by
                convert childLR hs323221 hx323221 hy323221 using 1 <;> norm_num
              rcases le_total tau.re (39/320 : ℝ) with hx3232211 | hx3232211
              · rcases le_total tau.im (121/320 : ℝ) with hy3232211 | hy3232211
                · have hs32322110 : InSquare (77/640) (241/640) (1/640) tau := by
                    convert childLL hs3232211 hx3232211 hy3232211 using 1 <;> norm_num
                  exact Batch0470.cell3767.sound htau (by
                    simp only [Batch0470.cell3767, Batch0470.tau3767, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32322110 (by positivity) using 1 <;> norm_num)
                · have hs32322112 : InSquare (77/640) (243/640) (1/640) tau := by
                    convert childUL hs3232211 hx3232211 hy3232211 using 1 <;> norm_num
                  exact Batch0471.cell3769.sound htau (by
                    simp only [Batch0471.cell3769, Batch0471.tau3769, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32322112 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (121/320 : ℝ) with hy3232211 | hy3232211
                · have hs32322111 : InSquare (79/640) (241/640) (1/640) tau := by
                    convert childLR hs3232211 hx3232211 hy3232211 using 1 <;> norm_num
                  exact Batch0471.cell3768.sound htau (by
                    simp only [Batch0471.cell3768, Batch0471.tau3768, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32322111 (by positivity) using 1 <;> norm_num)
                · have hs32322113 : InSquare (79/640) (243/640) (1/640) tau := by
                    convert childUR hs3232211 hx3232211 hy3232211 using 1 <;> norm_num
                  exact Batch0471.cell3770.sound htau (by
                    simp only [Batch0471.cell3770, Batch0471.tau3770, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32322113 (by positivity) using 1 <;> norm_num)
            · have hs3232213 : InSquare (39/320) (123/320) (1/320) tau := by
                convert childUR hs323221 hx323221 hy323221 using 1 <;> norm_num
              rcases le_total tau.re (39/320 : ℝ) with hx3232213 | hx3232213
              · rcases le_total tau.im (123/320 : ℝ) with hy3232213 | hy3232213
                · have hs32322130 : InSquare (77/640) (49/128) (1/640) tau := by
                    convert childLL hs3232213 hx3232213 hy3232213 using 1 <;> norm_num
                  exact Batch0471.cell3773.sound htau (by
                    simp only [Batch0471.cell3773, Batch0471.tau3773, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32322130 (by positivity) using 1 <;> norm_num)
                · have hs32322132 : InSquare (77/640) (247/640) (1/640) tau := by
                    convert childUL hs3232213 hx3232213 hy3232213 using 1 <;> norm_num
                  exact (outside_32322132 htau hs32322132).elim
              · rcases le_total tau.im (123/320 : ℝ) with hy3232213 | hy3232213
                · have hs32322131 : InSquare (79/640) (49/128) (1/640) tau := by
                    convert childLR hs3232213 hx3232213 hy3232213 using 1 <;> norm_num
                  exact (outside_32322131 htau hs32322131).elim
                · have hs32322133 : InSquare (79/640) (247/640) (1/640) tau := by
                    convert childUR hs3232213 hx3232213 hy3232213 using 1 <;> norm_num
                  exact (outside_32322133 htau hs32322133).elim
        · have hs323223 : InSquare (19/160) (63/160) (1/160) tau := by
            convert childUR hs32322 hx32322 hy32322 using 1 <;> norm_num
          exact (outside_323223 htau hs323223).elim
  · rcases le_total tau.im (3/8 : ℝ) with hy3232 | hy3232
    · have hs32321 : InSquare (11/80) (29/80) (1/80) tau := by
        convert childLR hs hx3232 hy3232 using 1 <;> norm_num
      rcases le_total tau.re (11/80 : ℝ) with hx32321 | hx32321
      · rcases le_total tau.im (29/80 : ℝ) with hy32321 | hy32321
        · have hs323210 : InSquare (21/160) (57/160) (1/160) tau := by
            convert childLL hs32321 hx32321 hy32321 using 1 <;> norm_num
          rcases le_total tau.re (21/160 : ℝ) with hx323210 | hx323210
          · rcases le_total tau.im (57/160 : ℝ) with hy323210 | hy323210
            · have hs3232100 : InSquare (41/320) (113/320) (1/320) tau := by
                convert childLL hs323210 hx323210 hy323210 using 1 <;> norm_num
              exact Batch0301.cell2410.sound htau (by
                simp only [Batch0301.cell2410, Batch0301.tau2410, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3232100 (by positivity) using 1 <;> norm_num)
            · have hs3232102 : InSquare (41/320) (23/64) (1/320) tau := by
                convert childUL hs323210 hx323210 hy323210 using 1 <;> norm_num
              exact Batch0301.cell2412.sound htau (by
                simp only [Batch0301.cell2412, Batch0301.tau2412, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3232102 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (57/160 : ℝ) with hy323210 | hy323210
            · have hs3232101 : InSquare (43/320) (113/320) (1/320) tau := by
                convert childLR hs323210 hx323210 hy323210 using 1 <;> norm_num
              exact Batch0301.cell2411.sound htau (by
                simp only [Batch0301.cell2411, Batch0301.tau2411, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3232101 (by positivity) using 1 <;> norm_num)
            · have hs3232103 : InSquare (43/320) (23/64) (1/320) tau := by
                convert childUR hs323210 hx323210 hy323210 using 1 <;> norm_num
              exact Batch0301.cell2413.sound htau (by
                simp only [Batch0301.cell2413, Batch0301.tau2413, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3232103 (by positivity) using 1 <;> norm_num)
        · have hs323212 : InSquare (21/160) (59/160) (1/160) tau := by
            convert childUL hs32321 hx32321 hy32321 using 1 <;> norm_num
          rcases le_total tau.re (21/160 : ℝ) with hx323212 | hx323212
          · rcases le_total tau.im (59/160 : ℝ) with hy323212 | hy323212
            · have hs3232120 : InSquare (41/320) (117/320) (1/320) tau := by
                convert childLL hs323212 hx323212 hy323212 using 1 <;> norm_num
              rcases le_total tau.re (41/320 : ℝ) with hx3232120 | hx3232120
              · rcases le_total tau.im (117/320 : ℝ) with hy3232120 | hy3232120
                · have hs32321200 : InSquare (81/640) (233/640) (1/640) tau := by
                    convert childLL hs3232120 hx3232120 hy3232120 using 1 <;> norm_num
                  exact Batch0464.cell3715.sound htau (by
                    simp only [Batch0464.cell3715, Batch0464.tau3715, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32321200 (by positivity) using 1 <;> norm_num)
                · have hs32321202 : InSquare (81/640) (47/128) (1/640) tau := by
                    convert childUL hs3232120 hx3232120 hy3232120 using 1 <;> norm_num
                  exact Batch0464.cell3717.sound htau (by
                    simp only [Batch0464.cell3717, Batch0464.tau3717, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32321202 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (117/320 : ℝ) with hy3232120 | hy3232120
                · have hs32321201 : InSquare (83/640) (233/640) (1/640) tau := by
                    convert childLR hs3232120 hx3232120 hy3232120 using 1 <;> norm_num
                  exact Batch0464.cell3716.sound htau (by
                    simp only [Batch0464.cell3716, Batch0464.tau3716, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32321201 (by positivity) using 1 <;> norm_num)
                · have hs32321203 : InSquare (83/640) (47/128) (1/640) tau := by
                    convert childUR hs3232120 hx3232120 hy3232120 using 1 <;> norm_num
                  exact Batch0464.cell3718.sound htau (by
                    simp only [Batch0464.cell3718, Batch0464.tau3718, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32321203 (by positivity) using 1 <;> norm_num)
            · have hs3232122 : InSquare (41/320) (119/320) (1/320) tau := by
                convert childUL hs323212 hx323212 hy323212 using 1 <;> norm_num
              rcases le_total tau.re (41/320 : ℝ) with hx3232122 | hx3232122
              · rcases le_total tau.im (119/320 : ℝ) with hy3232122 | hy3232122
                · have hs32321220 : InSquare (81/640) (237/640) (1/640) tau := by
                    convert childLL hs3232122 hx3232122 hy3232122 using 1 <;> norm_num
                  exact Batch0465.cell3723.sound htau (by
                    simp only [Batch0465.cell3723, Batch0465.tau3723, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32321220 (by positivity) using 1 <;> norm_num)
                · have hs32321222 : InSquare (81/640) (239/640) (1/640) tau := by
                    convert childUL hs3232122 hx3232122 hy3232122 using 1 <;> norm_num
                  exact Batch0465.cell3725.sound htau (by
                    simp only [Batch0465.cell3725, Batch0465.tau3725, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32321222 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (119/320 : ℝ) with hy3232122 | hy3232122
                · have hs32321221 : InSquare (83/640) (237/640) (1/640) tau := by
                    convert childLR hs3232122 hx3232122 hy3232122 using 1 <;> norm_num
                  exact Batch0465.cell3724.sound htau (by
                    simp only [Batch0465.cell3724, Batch0465.tau3724, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32321221 (by positivity) using 1 <;> norm_num)
                · have hs32321223 : InSquare (83/640) (239/640) (1/640) tau := by
                    convert childUR hs3232122 hx3232122 hy3232122 using 1 <;> norm_num
                  exact Batch0465.cell3726.sound htau (by
                    simp only [Batch0465.cell3726, Batch0465.tau3726, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32321223 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (59/160 : ℝ) with hy323212 | hy323212
            · have hs3232121 : InSquare (43/320) (117/320) (1/320) tau := by
                convert childLR hs323212 hx323212 hy323212 using 1 <;> norm_num
              rcases le_total tau.re (43/320 : ℝ) with hx3232121 | hx3232121
              · rcases le_total tau.im (117/320 : ℝ) with hy3232121 | hy3232121
                · have hs32321210 : InSquare (17/128) (233/640) (1/640) tau := by
                    convert childLL hs3232121 hx3232121 hy3232121 using 1 <;> norm_num
                  exact Batch0464.cell3719.sound htau (by
                    simp only [Batch0464.cell3719, Batch0464.tau3719, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32321210 (by positivity) using 1 <;> norm_num)
                · have hs32321212 : InSquare (17/128) (47/128) (1/640) tau := by
                    convert childUL hs3232121 hx3232121 hy3232121 using 1 <;> norm_num
                  exact Batch0465.cell3721.sound htau (by
                    simp only [Batch0465.cell3721, Batch0465.tau3721, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32321212 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (117/320 : ℝ) with hy3232121 | hy3232121
                · have hs32321211 : InSquare (87/640) (233/640) (1/640) tau := by
                    convert childLR hs3232121 hx3232121 hy3232121 using 1 <;> norm_num
                  exact Batch0465.cell3720.sound htau (by
                    simp only [Batch0465.cell3720, Batch0465.tau3720, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32321211 (by positivity) using 1 <;> norm_num)
                · have hs32321213 : InSquare (87/640) (47/128) (1/640) tau := by
                    convert childUR hs3232121 hx3232121 hy3232121 using 1 <;> norm_num
                  exact Batch0465.cell3722.sound htau (by
                    simp only [Batch0465.cell3722, Batch0465.tau3722, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32321213 (by positivity) using 1 <;> norm_num)
            · have hs3232123 : InSquare (43/320) (119/320) (1/320) tau := by
                convert childUR hs323212 hx323212 hy323212 using 1 <;> norm_num
              rcases le_total tau.re (43/320 : ℝ) with hx3232123 | hx3232123
              · rcases le_total tau.im (119/320 : ℝ) with hy3232123 | hy3232123
                · have hs32321230 : InSquare (17/128) (237/640) (1/640) tau := by
                    convert childLL hs3232123 hx3232123 hy3232123 using 1 <;> norm_num
                  exact Batch0465.cell3727.sound htau (by
                    simp only [Batch0465.cell3727, Batch0465.tau3727, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32321230 (by positivity) using 1 <;> norm_num)
                · have hs32321232 : InSquare (17/128) (239/640) (1/640) tau := by
                    convert childUL hs3232123 hx3232123 hy3232123 using 1 <;> norm_num
                  exact Batch0466.cell3729.sound htau (by
                    simp only [Batch0466.cell3729, Batch0466.tau3729, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32321232 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (119/320 : ℝ) with hy3232123 | hy3232123
                · have hs32321231 : InSquare (87/640) (237/640) (1/640) tau := by
                    convert childLR hs3232123 hx3232123 hy3232123 using 1 <;> norm_num
                  exact Batch0466.cell3728.sound htau (by
                    simp only [Batch0466.cell3728, Batch0466.tau3728, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32321231 (by positivity) using 1 <;> norm_num)
                · have hs32321233 : InSquare (87/640) (239/640) (1/640) tau := by
                    convert childUR hs3232123 hx3232123 hy3232123 using 1 <;> norm_num
                  exact Batch0466.cell3730.sound htau (by
                    simp only [Batch0466.cell3730, Batch0466.tau3730, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32321233 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (29/80 : ℝ) with hy32321 | hy32321
        · have hs323211 : InSquare (23/160) (57/160) (1/160) tau := by
            convert childLR hs32321 hx32321 hy32321 using 1 <;> norm_num
          rcases le_total tau.re (23/160 : ℝ) with hx323211 | hx323211
          · rcases le_total tau.im (57/160 : ℝ) with hy323211 | hy323211
            · have hs3232110 : InSquare (9/64) (113/320) (1/320) tau := by
                convert childLL hs323211 hx323211 hy323211 using 1 <;> norm_num
              exact Batch0301.cell2414.sound htau (by
                simp only [Batch0301.cell2414, Batch0301.tau2414, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3232110 (by positivity) using 1 <;> norm_num)
            · have hs3232112 : InSquare (9/64) (23/64) (1/320) tau := by
                convert childUL hs323211 hx323211 hy323211 using 1 <;> norm_num
              exact Batch0302.cell2416.sound htau (by
                simp only [Batch0302.cell2416, Batch0302.tau2416, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3232112 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (57/160 : ℝ) with hy323211 | hy323211
            · have hs3232111 : InSquare (47/320) (113/320) (1/320) tau := by
                convert childLR hs323211 hx323211 hy323211 using 1 <;> norm_num
              exact Batch0301.cell2415.sound htau (by
                simp only [Batch0301.cell2415, Batch0301.tau2415, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3232111 (by positivity) using 1 <;> norm_num)
            · have hs3232113 : InSquare (47/320) (23/64) (1/320) tau := by
                convert childUR hs323211 hx323211 hy323211 using 1 <;> norm_num
              rcases le_total tau.re (47/320 : ℝ) with hx3232113 | hx3232113
              · rcases le_total tau.im (23/64 : ℝ) with hy3232113 | hy3232113
                · have hs32321130 : InSquare (93/640) (229/640) (1/640) tau := by
                    convert childLL hs3232113 hx3232113 hy3232113 using 1 <;> norm_num
                  exact Batch0463.cell3711.sound htau (by
                    simp only [Batch0463.cell3711, Batch0463.tau3711, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32321130 (by positivity) using 1 <;> norm_num)
                · have hs32321132 : InSquare (93/640) (231/640) (1/640) tau := by
                    convert childUL hs3232113 hx3232113 hy3232113 using 1 <;> norm_num
                  exact Batch0464.cell3713.sound htau (by
                    simp only [Batch0464.cell3713, Batch0464.tau3713, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32321132 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (23/64 : ℝ) with hy3232113 | hy3232113
                · have hs32321131 : InSquare (19/128) (229/640) (1/640) tau := by
                    convert childLR hs3232113 hx3232113 hy3232113 using 1 <;> norm_num
                  exact Batch0464.cell3712.sound htau (by
                    simp only [Batch0464.cell3712, Batch0464.tau3712, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32321131 (by positivity) using 1 <;> norm_num)
                · have hs32321133 : InSquare (19/128) (231/640) (1/640) tau := by
                    convert childUR hs3232113 hx3232113 hy3232113 using 1 <;> norm_num
                  exact Batch0464.cell3714.sound htau (by
                    simp only [Batch0464.cell3714, Batch0464.tau3714, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32321133 (by positivity) using 1 <;> norm_num)
        · have hs323213 : InSquare (23/160) (59/160) (1/160) tau := by
            convert childUR hs32321 hx32321 hy32321 using 1 <;> norm_num
          rcases le_total tau.re (23/160 : ℝ) with hx323213 | hx323213
          · rcases le_total tau.im (59/160 : ℝ) with hy323213 | hy323213
            · have hs3232130 : InSquare (9/64) (117/320) (1/320) tau := by
                convert childLL hs323213 hx323213 hy323213 using 1 <;> norm_num
              rcases le_total tau.re (9/64 : ℝ) with hx3232130 | hx3232130
              · rcases le_total tau.im (117/320 : ℝ) with hy3232130 | hy3232130
                · have hs32321300 : InSquare (89/640) (233/640) (1/640) tau := by
                    convert childLL hs3232130 hx3232130 hy3232130 using 1 <;> norm_num
                  exact Batch0466.cell3731.sound htau (by
                    simp only [Batch0466.cell3731, Batch0466.tau3731, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32321300 (by positivity) using 1 <;> norm_num)
                · have hs32321302 : InSquare (89/640) (47/128) (1/640) tau := by
                    convert childUL hs3232130 hx3232130 hy3232130 using 1 <;> norm_num
                  exact Batch0466.cell3733.sound htau (by
                    simp only [Batch0466.cell3733, Batch0466.tau3733, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32321302 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (117/320 : ℝ) with hy3232130 | hy3232130
                · have hs32321301 : InSquare (91/640) (233/640) (1/640) tau := by
                    convert childLR hs3232130 hx3232130 hy3232130 using 1 <;> norm_num
                  exact Batch0466.cell3732.sound htau (by
                    simp only [Batch0466.cell3732, Batch0466.tau3732, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32321301 (by positivity) using 1 <;> norm_num)
                · have hs32321303 : InSquare (91/640) (47/128) (1/640) tau := by
                    convert childUR hs3232130 hx3232130 hy3232130 using 1 <;> norm_num
                  exact Batch0466.cell3734.sound htau (by
                    simp only [Batch0466.cell3734, Batch0466.tau3734, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32321303 (by positivity) using 1 <;> norm_num)
            · have hs3232132 : InSquare (9/64) (119/320) (1/320) tau := by
                convert childUL hs323213 hx323213 hy323213 using 1 <;> norm_num
              rcases le_total tau.re (9/64 : ℝ) with hx3232132 | hx3232132
              · rcases le_total tau.im (119/320 : ℝ) with hy3232132 | hy3232132
                · have hs32321320 : InSquare (89/640) (237/640) (1/640) tau := by
                    convert childLL hs3232132 hx3232132 hy3232132 using 1 <;> norm_num
                  exact Batch0467.cell3739.sound htau (by
                    simp only [Batch0467.cell3739, Batch0467.tau3739, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32321320 (by positivity) using 1 <;> norm_num)
                · have hs32321322 : InSquare (89/640) (239/640) (1/640) tau := by
                    convert childUL hs3232132 hx3232132 hy3232132 using 1 <;> norm_num
                  exact Batch0467.cell3741.sound htau (by
                    simp only [Batch0467.cell3741, Batch0467.tau3741, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32321322 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (119/320 : ℝ) with hy3232132 | hy3232132
                · have hs32321321 : InSquare (91/640) (237/640) (1/640) tau := by
                    convert childLR hs3232132 hx3232132 hy3232132 using 1 <;> norm_num
                  exact Batch0467.cell3740.sound htau (by
                    simp only [Batch0467.cell3740, Batch0467.tau3740, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32321321 (by positivity) using 1 <;> norm_num)
                · have hs32321323 : InSquare (91/640) (239/640) (1/640) tau := by
                    convert childUR hs3232132 hx3232132 hy3232132 using 1 <;> norm_num
                  exact Batch0467.cell3742.sound htau (by
                    simp only [Batch0467.cell3742, Batch0467.tau3742, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32321323 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (59/160 : ℝ) with hy323213 | hy323213
            · have hs3232131 : InSquare (47/320) (117/320) (1/320) tau := by
                convert childLR hs323213 hx323213 hy323213 using 1 <;> norm_num
              rcases le_total tau.re (47/320 : ℝ) with hx3232131 | hx3232131
              · rcases le_total tau.im (117/320 : ℝ) with hy3232131 | hy3232131
                · have hs32321310 : InSquare (93/640) (233/640) (1/640) tau := by
                    convert childLL hs3232131 hx3232131 hy3232131 using 1 <;> norm_num
                  exact Batch0466.cell3735.sound htau (by
                    simp only [Batch0466.cell3735, Batch0466.tau3735, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32321310 (by positivity) using 1 <;> norm_num)
                · have hs32321312 : InSquare (93/640) (47/128) (1/640) tau := by
                    convert childUL hs3232131 hx3232131 hy3232131 using 1 <;> norm_num
                  exact Batch0467.cell3737.sound htau (by
                    simp only [Batch0467.cell3737, Batch0467.tau3737, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32321312 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (117/320 : ℝ) with hy3232131 | hy3232131
                · have hs32321311 : InSquare (19/128) (233/640) (1/640) tau := by
                    convert childLR hs3232131 hx3232131 hy3232131 using 1 <;> norm_num
                  exact Batch0467.cell3736.sound htau (by
                    simp only [Batch0467.cell3736, Batch0467.tau3736, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32321311 (by positivity) using 1 <;> norm_num)
                · have hs32321313 : InSquare (19/128) (47/128) (1/640) tau := by
                    convert childUR hs3232131 hx3232131 hy3232131 using 1 <;> norm_num
                  exact Batch0467.cell3738.sound htau (by
                    simp only [Batch0467.cell3738, Batch0467.tau3738, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32321313 (by positivity) using 1 <;> norm_num)
            · have hs3232133 : InSquare (47/320) (119/320) (1/320) tau := by
                convert childUR hs323213 hx323213 hy323213 using 1 <;> norm_num
              rcases le_total tau.re (47/320 : ℝ) with hx3232133 | hx3232133
              · rcases le_total tau.im (119/320 : ℝ) with hy3232133 | hy3232133
                · have hs32321330 : InSquare (93/640) (237/640) (1/640) tau := by
                    convert childLL hs3232133 hx3232133 hy3232133 using 1 <;> norm_num
                  exact Batch0467.cell3743.sound htau (by
                    simp only [Batch0467.cell3743, Batch0467.tau3743, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32321330 (by positivity) using 1 <;> norm_num)
                · have hs32321332 : InSquare (93/640) (239/640) (1/640) tau := by
                    convert childUL hs3232133 hx3232133 hy3232133 using 1 <;> norm_num
                  exact Batch0468.cell3745.sound htau (by
                    simp only [Batch0468.cell3745, Batch0468.tau3745, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32321332 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (119/320 : ℝ) with hy3232133 | hy3232133
                · have hs32321331 : InSquare (19/128) (237/640) (1/640) tau := by
                    convert childLR hs3232133 hx3232133 hy3232133 using 1 <;> norm_num
                  exact Batch0468.cell3744.sound htau (by
                    simp only [Batch0468.cell3744, Batch0468.tau3744, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32321331 (by positivity) using 1 <;> norm_num)
                · have hs32321333 : InSquare (19/128) (239/640) (1/640) tau := by
                    convert childUR hs3232133 hx3232133 hy3232133 using 1 <;> norm_num
                  exact Batch0468.cell3746.sound htau (by
                    simp only [Batch0468.cell3746, Batch0468.tau3746, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32321333 (by positivity) using 1 <;> norm_num)
    · have hs32323 : InSquare (11/80) (31/80) (1/80) tau := by
        convert childUR hs hx3232 hy3232 using 1 <;> norm_num
      rcases le_total tau.re (11/80 : ℝ) with hx32323 | hx32323
      · rcases le_total tau.im (31/80 : ℝ) with hy32323 | hy32323
        · have hs323230 : InSquare (21/160) (61/160) (1/160) tau := by
            convert childLL hs32323 hx32323 hy32323 using 1 <;> norm_num
          rcases le_total tau.re (21/160 : ℝ) with hx323230 | hx323230
          · rcases le_total tau.im (61/160 : ℝ) with hy323230 | hy323230
            · have hs3232300 : InSquare (41/320) (121/320) (1/320) tau := by
                convert childLL hs323230 hx323230 hy323230 using 1 <;> norm_num
              rcases le_total tau.re (41/320 : ℝ) with hx3232300 | hx3232300
              · rcases le_total tau.im (121/320 : ℝ) with hy3232300 | hy3232300
                · have hs32323000 : InSquare (81/640) (241/640) (1/640) tau := by
                    convert childLL hs3232300 hx3232300 hy3232300 using 1 <;> norm_num
                  exact Batch0471.cell3774.sound htau (by
                    simp only [Batch0471.cell3774, Batch0471.tau3774, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32323000 (by positivity) using 1 <;> norm_num)
                · have hs32323002 : InSquare (81/640) (243/640) (1/640) tau := by
                    convert childUL hs3232300 hx3232300 hy3232300 using 1 <;> norm_num
                  exact Batch0472.cell3776.sound htau (by
                    simp only [Batch0472.cell3776, Batch0472.tau3776, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32323002 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (121/320 : ℝ) with hy3232300 | hy3232300
                · have hs32323001 : InSquare (83/640) (241/640) (1/640) tau := by
                    convert childLR hs3232300 hx3232300 hy3232300 using 1 <;> norm_num
                  exact Batch0471.cell3775.sound htau (by
                    simp only [Batch0471.cell3775, Batch0471.tau3775, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32323001 (by positivity) using 1 <;> norm_num)
                · have hs32323003 : InSquare (83/640) (243/640) (1/640) tau := by
                    convert childUR hs3232300 hx3232300 hy3232300 using 1 <;> norm_num
                  exact Batch0472.cell3777.sound htau (by
                    simp only [Batch0472.cell3777, Batch0472.tau3777, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32323003 (by positivity) using 1 <;> norm_num)
            · have hs3232302 : InSquare (41/320) (123/320) (1/320) tau := by
                convert childUL hs323230 hx323230 hy323230 using 1 <;> norm_num
              exact (outside_3232302 htau hs3232302).elim
          · rcases le_total tau.im (61/160 : ℝ) with hy323230 | hy323230
            · have hs3232301 : InSquare (43/320) (121/320) (1/320) tau := by
                convert childLR hs323230 hx323230 hy323230 using 1 <;> norm_num
              rcases le_total tau.re (43/320 : ℝ) with hx3232301 | hx3232301
              · rcases le_total tau.im (121/320 : ℝ) with hy3232301 | hy3232301
                · have hs32323010 : InSquare (17/128) (241/640) (1/640) tau := by
                    convert childLL hs3232301 hx3232301 hy3232301 using 1 <;> norm_num
                  exact Batch0472.cell3778.sound htau (by
                    simp only [Batch0472.cell3778, Batch0472.tau3778, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32323010 (by positivity) using 1 <;> norm_num)
                · have hs32323012 : InSquare (17/128) (243/640) (1/640) tau := by
                    convert childUL hs3232301 hx3232301 hy3232301 using 1 <;> norm_num
                  exact (outside_32323012 htau hs32323012).elim
              · rcases le_total tau.im (121/320 : ℝ) with hy3232301 | hy3232301
                · have hs32323011 : InSquare (87/640) (241/640) (1/640) tau := by
                    convert childLR hs3232301 hx3232301 hy3232301 using 1 <;> norm_num
                  exact Batch0472.cell3779.sound htau (by
                    simp only [Batch0472.cell3779, Batch0472.tau3779, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32323011 (by positivity) using 1 <;> norm_num)
                · have hs32323013 : InSquare (87/640) (243/640) (1/640) tau := by
                    convert childUR hs3232301 hx3232301 hy3232301 using 1 <;> norm_num
                  exact (outside_32323013 htau hs32323013).elim
            · have hs3232303 : InSquare (43/320) (123/320) (1/320) tau := by
                convert childUR hs323230 hx323230 hy323230 using 1 <;> norm_num
              exact (outside_3232303 htau hs3232303).elim
        · have hs323232 : InSquare (21/160) (63/160) (1/160) tau := by
            convert childUL hs32323 hx32323 hy32323 using 1 <;> norm_num
          exact (outside_323232 htau hs323232).elim
      · rcases le_total tau.im (31/80 : ℝ) with hy32323 | hy32323
        · have hs323231 : InSquare (23/160) (61/160) (1/160) tau := by
            convert childLR hs32323 hx32323 hy32323 using 1 <;> norm_num
          rcases le_total tau.re (23/160 : ℝ) with hx323231 | hx323231
          · rcases le_total tau.im (61/160 : ℝ) with hy323231 | hy323231
            · have hs3232310 : InSquare (9/64) (121/320) (1/320) tau := by
                convert childLL hs323231 hx323231 hy323231 using 1 <;> norm_num
              rcases le_total tau.re (9/64 : ℝ) with hx3232310 | hx3232310
              · rcases le_total tau.im (121/320 : ℝ) with hy3232310 | hy3232310
                · have hs32323100 : InSquare (89/640) (241/640) (1/640) tau := by
                    convert childLL hs3232310 hx3232310 hy3232310 using 1 <;> norm_num
                  exact Batch0472.cell3780.sound htau (by
                    simp only [Batch0472.cell3780, Batch0472.tau3780, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs32323100 (by positivity) using 1 <;> norm_num)
                · have hs32323102 : InSquare (89/640) (243/640) (1/640) tau := by
                    convert childUL hs3232310 hx3232310 hy3232310 using 1 <;> norm_num
                  exact (outside_32323102 htau hs32323102).elim
              · rcases le_total tau.im (121/320 : ℝ) with hy3232310 | hy3232310
                · have hs32323101 : InSquare (91/640) (241/640) (1/640) tau := by
                    convert childLR hs3232310 hx3232310 hy3232310 using 1 <;> norm_num
                  exact (outside_32323101 htau hs32323101).elim
                · have hs32323103 : InSquare (91/640) (243/640) (1/640) tau := by
                    convert childUR hs3232310 hx3232310 hy3232310 using 1 <;> norm_num
                  exact (outside_32323103 htau hs32323103).elim
            · have hs3232312 : InSquare (9/64) (123/320) (1/320) tau := by
                convert childUL hs323231 hx323231 hy323231 using 1 <;> norm_num
              exact (outside_3232312 htau hs3232312).elim
          · rcases le_total tau.im (61/160 : ℝ) with hy323231 | hy323231
            · have hs3232311 : InSquare (47/320) (121/320) (1/320) tau := by
                convert childLR hs323231 hx323231 hy323231 using 1 <;> norm_num
              exact (outside_3232311 htau hs3232311).elim
            · have hs3232313 : InSquare (47/320) (123/320) (1/320) tau := by
                convert childUR hs323231 hx323231 hy323231 using 1 <;> norm_num
              exact (outside_3232313 htau hs3232313).elim
        · have hs323233 : InSquare (23/160) (63/160) (1/160) tau := by
            convert childUR hs32323 hx32323 hy32323 using 1 <;> norm_num
          exact (outside_323233 htau hs323233).elim

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3232
