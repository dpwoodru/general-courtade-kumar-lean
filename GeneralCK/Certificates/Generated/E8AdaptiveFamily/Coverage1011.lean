import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0206
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0391
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0392
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0393
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0394
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0395
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0396
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0397

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1011

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

private theorem outside_10110 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (13/80) (-31/80) (1/80) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (3/20 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-3/20)]
  have himSq : (3/8 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+3/8)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_10111 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (3/16) (-31/80) (1/80) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (7/40 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-7/40)]
  have himSq : (3/8 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+3/8)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_101130 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (29/160) (-59/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (7/40 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-7/40)]
  have himSq : (29/80 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+29/80)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_101131 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (31/160) (-59/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (3/16 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-3/16)]
  have himSq : (29/80 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+29/80)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_1011201 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (51/320) (-119/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (5/32 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-5/32)]
  have himSq : (59/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+59/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_1011210 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (53/320) (-119/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (13/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-13/80)]
  have himSq : (59/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+59/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_1011211 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (11/64) (-119/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (27/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-27/160)]
  have himSq : (59/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+59/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_1011330 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (61/320) (-23/64) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (3/16 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-3/16)]
  have himSq : (57/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+57/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_1011331 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (63/320) (-23/64) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (31/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-31/160)]
  have himSq : (57/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+57/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_1011333 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (63/320) (-113/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (31/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-31/160)]
  have himSq : (7/20 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+7/20)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_10112000 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (97/640) (-239/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (3/20 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-3/20)]
  have himSq : (119/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+119/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_10112001 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (99/640) (-239/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (49/320 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-49/320)]
  have himSq : (119/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+119/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_10112120 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (21/128) (-47/128) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (13/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-13/80)]
  have himSq : (117/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+117/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_10112121 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (107/640) (-47/128) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (53/320 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-53/320)]
  have himSq : (117/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+117/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_10112130 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (109/640) (-47/128) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (27/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-27/160)]
  have himSq : (117/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+117/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_10112131 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (111/640) (-47/128) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (11/64 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-11/64)]
  have himSq : (117/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+117/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_10112133 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (111/640) (-233/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (11/64 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-11/64)]
  have himSq : (29/80 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+29/80)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_10113201 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (23/128) (-231/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (57/320 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-57/320)]
  have himSq : (23/64 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+23/64)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_10113210 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (117/640) (-231/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (29/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-29/160)]
  have himSq : (23/64 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+23/64)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_10113211 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (119/640) (-231/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (59/320 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-59/320)]
  have himSq : (23/64 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+23/64)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_10113213 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (119/640) (-229/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (59/320 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-59/320)]
  have himSq : (57/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+57/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_10113321 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (123/640) (-227/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (61/320 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-61/320)]
  have himSq : (113/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+113/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (7/40) (-3/8) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (7/40 : ℝ) with hx1011 | hx1011
  · rcases le_total tau.im (-3/8 : ℝ) with hy1011 | hy1011
    · have hs10110 : InSquare (13/80) (-31/80) (1/80) tau := by
        convert childLL hs hx1011 hy1011 using 1 <;> norm_num
      exact (outside_10110 htau hs10110).elim
    · have hs10112 : InSquare (13/80) (-29/80) (1/80) tau := by
        convert childUL hs hx1011 hy1011 using 1 <;> norm_num
      rcases le_total tau.re (13/80 : ℝ) with hx10112 | hx10112
      · rcases le_total tau.im (-29/80 : ℝ) with hy10112 | hy10112
        · have hs101120 : InSquare (5/32) (-59/160) (1/160) tau := by
            convert childLL hs10112 hx10112 hy10112 using 1 <;> norm_num
          rcases le_total tau.re (5/32 : ℝ) with hx101120 | hx101120
          · rcases le_total tau.im (-59/160 : ℝ) with hy101120 | hy101120
            · have hs1011200 : InSquare (49/320) (-119/320) (1/320) tau := by
                convert childLL hs101120 hx101120 hy101120 using 1 <;> norm_num
              rcases le_total tau.re (49/320 : ℝ) with hx1011200 | hx1011200
              · rcases le_total tau.im (-119/320 : ℝ) with hy1011200 | hy1011200
                · have hs10112000 : InSquare (97/640) (-239/640) (1/640) tau := by
                    convert childLL hs1011200 hx1011200 hy1011200 using 1 <;> norm_num
                  exact (outside_10112000 htau hs10112000).elim
                · have hs10112002 : InSquare (97/640) (-237/640) (1/640) tau := by
                    convert childUL hs1011200 hx1011200 hy1011200 using 1 <;> norm_num
                  exact Batch0391.cell3133.sound htau (by
                    simp only [Batch0391.cell3133, Batch0391.tau3133, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10112002 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-119/320 : ℝ) with hy1011200 | hy1011200
                · have hs10112001 : InSquare (99/640) (-239/640) (1/640) tau := by
                    convert childLR hs1011200 hx1011200 hy1011200 using 1 <;> norm_num
                  exact (outside_10112001 htau hs10112001).elim
                · have hs10112003 : InSquare (99/640) (-237/640) (1/640) tau := by
                    convert childUR hs1011200 hx1011200 hy1011200 using 1 <;> norm_num
                  exact Batch0391.cell3134.sound htau (by
                    simp only [Batch0391.cell3134, Batch0391.tau3134, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10112003 (by positivity) using 1 <;> norm_num)
            · have hs1011202 : InSquare (49/320) (-117/320) (1/320) tau := by
                convert childUL hs101120 hx101120 hy101120 using 1 <;> norm_num
              rcases le_total tau.re (49/320 : ℝ) with hx1011202 | hx1011202
              · rcases le_total tau.im (-117/320 : ℝ) with hy1011202 | hy1011202
                · have hs10112020 : InSquare (97/640) (-47/128) (1/640) tau := by
                    convert childLL hs1011202 hx1011202 hy1011202 using 1 <;> norm_num
                  exact Batch0391.cell3135.sound htau (by
                    simp only [Batch0391.cell3135, Batch0391.tau3135, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10112020 (by positivity) using 1 <;> norm_num)
                · have hs10112022 : InSquare (97/640) (-233/640) (1/640) tau := by
                    convert childUL hs1011202 hx1011202 hy1011202 using 1 <;> norm_num
                  exact Batch0392.cell3137.sound htau (by
                    simp only [Batch0392.cell3137, Batch0392.tau3137, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10112022 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-117/320 : ℝ) with hy1011202 | hy1011202
                · have hs10112021 : InSquare (99/640) (-47/128) (1/640) tau := by
                    convert childLR hs1011202 hx1011202 hy1011202 using 1 <;> norm_num
                  exact Batch0392.cell3136.sound htau (by
                    simp only [Batch0392.cell3136, Batch0392.tau3136, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10112021 (by positivity) using 1 <;> norm_num)
                · have hs10112023 : InSquare (99/640) (-233/640) (1/640) tau := by
                    convert childUR hs1011202 hx1011202 hy1011202 using 1 <;> norm_num
                  exact Batch0392.cell3138.sound htau (by
                    simp only [Batch0392.cell3138, Batch0392.tau3138, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10112023 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-59/160 : ℝ) with hy101120 | hy101120
            · have hs1011201 : InSquare (51/320) (-119/320) (1/320) tau := by
                convert childLR hs101120 hx101120 hy101120 using 1 <;> norm_num
              exact (outside_1011201 htau hs1011201).elim
            · have hs1011203 : InSquare (51/320) (-117/320) (1/320) tau := by
                convert childUR hs101120 hx101120 hy101120 using 1 <;> norm_num
              rcases le_total tau.re (51/320 : ℝ) with hx1011203 | hx1011203
              · rcases le_total tau.im (-117/320 : ℝ) with hy1011203 | hy1011203
                · have hs10112030 : InSquare (101/640) (-47/128) (1/640) tau := by
                    convert childLL hs1011203 hx1011203 hy1011203 using 1 <;> norm_num
                  exact Batch0392.cell3139.sound htau (by
                    simp only [Batch0392.cell3139, Batch0392.tau3139, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10112030 (by positivity) using 1 <;> norm_num)
                · have hs10112032 : InSquare (101/640) (-233/640) (1/640) tau := by
                    convert childUL hs1011203 hx1011203 hy1011203 using 1 <;> norm_num
                  exact Batch0392.cell3141.sound htau (by
                    simp only [Batch0392.cell3141, Batch0392.tau3141, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10112032 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-117/320 : ℝ) with hy1011203 | hy1011203
                · have hs10112031 : InSquare (103/640) (-47/128) (1/640) tau := by
                    convert childLR hs1011203 hx1011203 hy1011203 using 1 <;> norm_num
                  exact Batch0392.cell3140.sound htau (by
                    simp only [Batch0392.cell3140, Batch0392.tau3140, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10112031 (by positivity) using 1 <;> norm_num)
                · have hs10112033 : InSquare (103/640) (-233/640) (1/640) tau := by
                    convert childUR hs1011203 hx1011203 hy1011203 using 1 <;> norm_num
                  exact Batch0392.cell3142.sound htau (by
                    simp only [Batch0392.cell3142, Batch0392.tau3142, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10112033 (by positivity) using 1 <;> norm_num)
        · have hs101122 : InSquare (5/32) (-57/160) (1/160) tau := by
            convert childUL hs10112 hx10112 hy10112 using 1 <;> norm_num
          rcases le_total tau.re (5/32 : ℝ) with hx101122 | hx101122
          · rcases le_total tau.im (-57/160 : ℝ) with hy101122 | hy101122
            · have hs1011220 : InSquare (49/320) (-23/64) (1/320) tau := by
                convert childLL hs101122 hx101122 hy101122 using 1 <;> norm_num
              rcases le_total tau.re (49/320 : ℝ) with hx1011220 | hx1011220
              · rcases le_total tau.im (-23/64 : ℝ) with hy1011220 | hy1011220
                · have hs10112200 : InSquare (97/640) (-231/640) (1/640) tau := by
                    convert childLL hs1011220 hx1011220 hy1011220 using 1 <;> norm_num
                  exact Batch0393.cell3146.sound htau (by
                    simp only [Batch0393.cell3146, Batch0393.tau3146, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10112200 (by positivity) using 1 <;> norm_num)
                · have hs10112202 : InSquare (97/640) (-229/640) (1/640) tau := by
                    convert childUL hs1011220 hx1011220 hy1011220 using 1 <;> norm_num
                  exact Batch0393.cell3148.sound htau (by
                    simp only [Batch0393.cell3148, Batch0393.tau3148, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10112202 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-23/64 : ℝ) with hy1011220 | hy1011220
                · have hs10112201 : InSquare (99/640) (-231/640) (1/640) tau := by
                    convert childLR hs1011220 hx1011220 hy1011220 using 1 <;> norm_num
                  exact Batch0393.cell3147.sound htau (by
                    simp only [Batch0393.cell3147, Batch0393.tau3147, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10112201 (by positivity) using 1 <;> norm_num)
                · have hs10112203 : InSquare (99/640) (-229/640) (1/640) tau := by
                    convert childUR hs1011220 hx1011220 hy1011220 using 1 <;> norm_num
                  exact Batch0393.cell3149.sound htau (by
                    simp only [Batch0393.cell3149, Batch0393.tau3149, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10112203 (by positivity) using 1 <;> norm_num)
            · have hs1011222 : InSquare (49/320) (-113/320) (1/320) tau := by
                convert childUL hs101122 hx101122 hy101122 using 1 <;> norm_num
              exact Batch0206.cell1648.sound htau (by
                simp only [Batch0206.cell1648, Batch0206.tau1648, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1011222 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-57/160 : ℝ) with hy101122 | hy101122
            · have hs1011221 : InSquare (51/320) (-23/64) (1/320) tau := by
                convert childLR hs101122 hx101122 hy101122 using 1 <;> norm_num
              rcases le_total tau.re (51/320 : ℝ) with hx1011221 | hx1011221
              · rcases le_total tau.im (-23/64 : ℝ) with hy1011221 | hy1011221
                · have hs10112210 : InSquare (101/640) (-231/640) (1/640) tau := by
                    convert childLL hs1011221 hx1011221 hy1011221 using 1 <;> norm_num
                  exact Batch0393.cell3150.sound htau (by
                    simp only [Batch0393.cell3150, Batch0393.tau3150, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10112210 (by positivity) using 1 <;> norm_num)
                · have hs10112212 : InSquare (101/640) (-229/640) (1/640) tau := by
                    convert childUL hs1011221 hx1011221 hy1011221 using 1 <;> norm_num
                  exact Batch0394.cell3152.sound htau (by
                    simp only [Batch0394.cell3152, Batch0394.tau3152, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10112212 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-23/64 : ℝ) with hy1011221 | hy1011221
                · have hs10112211 : InSquare (103/640) (-231/640) (1/640) tau := by
                    convert childLR hs1011221 hx1011221 hy1011221 using 1 <;> norm_num
                  exact Batch0393.cell3151.sound htau (by
                    simp only [Batch0393.cell3151, Batch0393.tau3151, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10112211 (by positivity) using 1 <;> norm_num)
                · have hs10112213 : InSquare (103/640) (-229/640) (1/640) tau := by
                    convert childUR hs1011221 hx1011221 hy1011221 using 1 <;> norm_num
                  exact Batch0394.cell3153.sound htau (by
                    simp only [Batch0394.cell3153, Batch0394.tau3153, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10112213 (by positivity) using 1 <;> norm_num)
            · have hs1011223 : InSquare (51/320) (-113/320) (1/320) tau := by
                convert childUR hs101122 hx101122 hy101122 using 1 <;> norm_num
              exact Batch0206.cell1649.sound htau (by
                simp only [Batch0206.cell1649, Batch0206.tau1649, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1011223 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-29/80 : ℝ) with hy10112 | hy10112
        · have hs101121 : InSquare (27/160) (-59/160) (1/160) tau := by
            convert childLR hs10112 hx10112 hy10112 using 1 <;> norm_num
          rcases le_total tau.re (27/160 : ℝ) with hx101121 | hx101121
          · rcases le_total tau.im (-59/160 : ℝ) with hy101121 | hy101121
            · have hs1011210 : InSquare (53/320) (-119/320) (1/320) tau := by
                convert childLL hs101121 hx101121 hy101121 using 1 <;> norm_num
              exact (outside_1011210 htau hs1011210).elim
            · have hs1011212 : InSquare (53/320) (-117/320) (1/320) tau := by
                convert childUL hs101121 hx101121 hy101121 using 1 <;> norm_num
              rcases le_total tau.re (53/320 : ℝ) with hx1011212 | hx1011212
              · rcases le_total tau.im (-117/320 : ℝ) with hy1011212 | hy1011212
                · have hs10112120 : InSquare (21/128) (-47/128) (1/640) tau := by
                    convert childLL hs1011212 hx1011212 hy1011212 using 1 <;> norm_num
                  exact (outside_10112120 htau hs10112120).elim
                · have hs10112122 : InSquare (21/128) (-233/640) (1/640) tau := by
                    convert childUL hs1011212 hx1011212 hy1011212 using 1 <;> norm_num
                  exact Batch0392.cell3143.sound htau (by
                    simp only [Batch0392.cell3143, Batch0392.tau3143, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10112122 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-117/320 : ℝ) with hy1011212 | hy1011212
                · have hs10112121 : InSquare (107/640) (-47/128) (1/640) tau := by
                    convert childLR hs1011212 hx1011212 hy1011212 using 1 <;> norm_num
                  exact (outside_10112121 htau hs10112121).elim
                · have hs10112123 : InSquare (107/640) (-233/640) (1/640) tau := by
                    convert childUR hs1011212 hx1011212 hy1011212 using 1 <;> norm_num
                  exact Batch0393.cell3144.sound htau (by
                    simp only [Batch0393.cell3144, Batch0393.tau3144, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10112123 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-59/160 : ℝ) with hy101121 | hy101121
            · have hs1011211 : InSquare (11/64) (-119/320) (1/320) tau := by
                convert childLR hs101121 hx101121 hy101121 using 1 <;> norm_num
              exact (outside_1011211 htau hs1011211).elim
            · have hs1011213 : InSquare (11/64) (-117/320) (1/320) tau := by
                convert childUR hs101121 hx101121 hy101121 using 1 <;> norm_num
              rcases le_total tau.re (11/64 : ℝ) with hx1011213 | hx1011213
              · rcases le_total tau.im (-117/320 : ℝ) with hy1011213 | hy1011213
                · have hs10112130 : InSquare (109/640) (-47/128) (1/640) tau := by
                    convert childLL hs1011213 hx1011213 hy1011213 using 1 <;> norm_num
                  exact (outside_10112130 htau hs10112130).elim
                · have hs10112132 : InSquare (109/640) (-233/640) (1/640) tau := by
                    convert childUL hs1011213 hx1011213 hy1011213 using 1 <;> norm_num
                  exact Batch0393.cell3145.sound htau (by
                    simp only [Batch0393.cell3145, Batch0393.tau3145, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10112132 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-117/320 : ℝ) with hy1011213 | hy1011213
                · have hs10112131 : InSquare (111/640) (-47/128) (1/640) tau := by
                    convert childLR hs1011213 hx1011213 hy1011213 using 1 <;> norm_num
                  exact (outside_10112131 htau hs10112131).elim
                · have hs10112133 : InSquare (111/640) (-233/640) (1/640) tau := by
                    convert childUR hs1011213 hx1011213 hy1011213 using 1 <;> norm_num
                  exact (outside_10112133 htau hs10112133).elim
        · have hs101123 : InSquare (27/160) (-57/160) (1/160) tau := by
            convert childUR hs10112 hx10112 hy10112 using 1 <;> norm_num
          rcases le_total tau.re (27/160 : ℝ) with hx101123 | hx101123
          · rcases le_total tau.im (-57/160 : ℝ) with hy101123 | hy101123
            · have hs1011230 : InSquare (53/320) (-23/64) (1/320) tau := by
                convert childLL hs101123 hx101123 hy101123 using 1 <;> norm_num
              rcases le_total tau.re (53/320 : ℝ) with hx1011230 | hx1011230
              · rcases le_total tau.im (-23/64 : ℝ) with hy1011230 | hy1011230
                · have hs10112300 : InSquare (21/128) (-231/640) (1/640) tau := by
                    convert childLL hs1011230 hx1011230 hy1011230 using 1 <;> norm_num
                  exact Batch0394.cell3154.sound htau (by
                    simp only [Batch0394.cell3154, Batch0394.tau3154, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10112300 (by positivity) using 1 <;> norm_num)
                · have hs10112302 : InSquare (21/128) (-229/640) (1/640) tau := by
                    convert childUL hs1011230 hx1011230 hy1011230 using 1 <;> norm_num
                  exact Batch0394.cell3156.sound htau (by
                    simp only [Batch0394.cell3156, Batch0394.tau3156, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10112302 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-23/64 : ℝ) with hy1011230 | hy1011230
                · have hs10112301 : InSquare (107/640) (-231/640) (1/640) tau := by
                    convert childLR hs1011230 hx1011230 hy1011230 using 1 <;> norm_num
                  exact Batch0394.cell3155.sound htau (by
                    simp only [Batch0394.cell3155, Batch0394.tau3155, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10112301 (by positivity) using 1 <;> norm_num)
                · have hs10112303 : InSquare (107/640) (-229/640) (1/640) tau := by
                    convert childUR hs1011230 hx1011230 hy1011230 using 1 <;> norm_num
                  exact Batch0394.cell3157.sound htau (by
                    simp only [Batch0394.cell3157, Batch0394.tau3157, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10112303 (by positivity) using 1 <;> norm_num)
            · have hs1011232 : InSquare (53/320) (-113/320) (1/320) tau := by
                convert childUL hs101123 hx101123 hy101123 using 1 <;> norm_num
              exact Batch0206.cell1650.sound htau (by
                simp only [Batch0206.cell1650, Batch0206.tau1650, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1011232 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-57/160 : ℝ) with hy101123 | hy101123
            · have hs1011231 : InSquare (11/64) (-23/64) (1/320) tau := by
                convert childLR hs101123 hx101123 hy101123 using 1 <;> norm_num
              rcases le_total tau.re (11/64 : ℝ) with hx1011231 | hx1011231
              · rcases le_total tau.im (-23/64 : ℝ) with hy1011231 | hy1011231
                · have hs10112310 : InSquare (109/640) (-231/640) (1/640) tau := by
                    convert childLL hs1011231 hx1011231 hy1011231 using 1 <;> norm_num
                  exact Batch0394.cell3158.sound htau (by
                    simp only [Batch0394.cell3158, Batch0394.tau3158, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10112310 (by positivity) using 1 <;> norm_num)
                · have hs10112312 : InSquare (109/640) (-229/640) (1/640) tau := by
                    convert childUL hs1011231 hx1011231 hy1011231 using 1 <;> norm_num
                  exact Batch0395.cell3160.sound htau (by
                    simp only [Batch0395.cell3160, Batch0395.tau3160, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10112312 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-23/64 : ℝ) with hy1011231 | hy1011231
                · have hs10112311 : InSquare (111/640) (-231/640) (1/640) tau := by
                    convert childLR hs1011231 hx1011231 hy1011231 using 1 <;> norm_num
                  exact Batch0394.cell3159.sound htau (by
                    simp only [Batch0394.cell3159, Batch0394.tau3159, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10112311 (by positivity) using 1 <;> norm_num)
                · have hs10112313 : InSquare (111/640) (-229/640) (1/640) tau := by
                    convert childUR hs1011231 hx1011231 hy1011231 using 1 <;> norm_num
                  exact Batch0395.cell3161.sound htau (by
                    simp only [Batch0395.cell3161, Batch0395.tau3161, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10112313 (by positivity) using 1 <;> norm_num)
            · have hs1011233 : InSquare (11/64) (-113/320) (1/320) tau := by
                convert childUR hs101123 hx101123 hy101123 using 1 <;> norm_num
              rcases le_total tau.re (11/64 : ℝ) with hx1011233 | hx1011233
              · rcases le_total tau.im (-113/320 : ℝ) with hy1011233 | hy1011233
                · have hs10112330 : InSquare (109/640) (-227/640) (1/640) tau := by
                    convert childLL hs1011233 hx1011233 hy1011233 using 1 <;> norm_num
                  exact Batch0395.cell3162.sound htau (by
                    simp only [Batch0395.cell3162, Batch0395.tau3162, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10112330 (by positivity) using 1 <;> norm_num)
                · have hs10112332 : InSquare (109/640) (-45/128) (1/640) tau := by
                    convert childUL hs1011233 hx1011233 hy1011233 using 1 <;> norm_num
                  exact Batch0395.cell3164.sound htau (by
                    simp only [Batch0395.cell3164, Batch0395.tau3164, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10112332 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-113/320 : ℝ) with hy1011233 | hy1011233
                · have hs10112331 : InSquare (111/640) (-227/640) (1/640) tau := by
                    convert childLR hs1011233 hx1011233 hy1011233 using 1 <;> norm_num
                  exact Batch0395.cell3163.sound htau (by
                    simp only [Batch0395.cell3163, Batch0395.tau3163, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10112331 (by positivity) using 1 <;> norm_num)
                · have hs10112333 : InSquare (111/640) (-45/128) (1/640) tau := by
                    convert childUR hs1011233 hx1011233 hy1011233 using 1 <;> norm_num
                  exact Batch0395.cell3165.sound htau (by
                    simp only [Batch0395.cell3165, Batch0395.tau3165, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10112333 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (-3/8 : ℝ) with hy1011 | hy1011
    · have hs10111 : InSquare (3/16) (-31/80) (1/80) tau := by
        convert childLR hs hx1011 hy1011 using 1 <;> norm_num
      exact (outside_10111 htau hs10111).elim
    · have hs10113 : InSquare (3/16) (-29/80) (1/80) tau := by
        convert childUR hs hx1011 hy1011 using 1 <;> norm_num
      rcases le_total tau.re (3/16 : ℝ) with hx10113 | hx10113
      · rcases le_total tau.im (-29/80 : ℝ) with hy10113 | hy10113
        · have hs101130 : InSquare (29/160) (-59/160) (1/160) tau := by
            convert childLL hs10113 hx10113 hy10113 using 1 <;> norm_num
          exact (outside_101130 htau hs101130).elim
        · have hs101132 : InSquare (29/160) (-57/160) (1/160) tau := by
            convert childUL hs10113 hx10113 hy10113 using 1 <;> norm_num
          rcases le_total tau.re (29/160 : ℝ) with hx101132 | hx101132
          · rcases le_total tau.im (-57/160 : ℝ) with hy101132 | hy101132
            · have hs1011320 : InSquare (57/320) (-23/64) (1/320) tau := by
                convert childLL hs101132 hx101132 hy101132 using 1 <;> norm_num
              rcases le_total tau.re (57/320 : ℝ) with hx1011320 | hx1011320
              · rcases le_total tau.im (-23/64 : ℝ) with hy1011320 | hy1011320
                · have hs10113200 : InSquare (113/640) (-231/640) (1/640) tau := by
                    convert childLL hs1011320 hx1011320 hy1011320 using 1 <;> norm_num
                  exact Batch0395.cell3166.sound htau (by
                    simp only [Batch0395.cell3166, Batch0395.tau3166, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10113200 (by positivity) using 1 <;> norm_num)
                · have hs10113202 : InSquare (113/640) (-229/640) (1/640) tau := by
                    convert childUL hs1011320 hx1011320 hy1011320 using 1 <;> norm_num
                  exact Batch0395.cell3167.sound htau (by
                    simp only [Batch0395.cell3167, Batch0395.tau3167, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10113202 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-23/64 : ℝ) with hy1011320 | hy1011320
                · have hs10113201 : InSquare (23/128) (-231/640) (1/640) tau := by
                    convert childLR hs1011320 hx1011320 hy1011320 using 1 <;> norm_num
                  exact (outside_10113201 htau hs10113201).elim
                · have hs10113203 : InSquare (23/128) (-229/640) (1/640) tau := by
                    convert childUR hs1011320 hx1011320 hy1011320 using 1 <;> norm_num
                  exact Batch0396.cell3168.sound htau (by
                    simp only [Batch0396.cell3168, Batch0396.tau3168, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10113203 (by positivity) using 1 <;> norm_num)
            · have hs1011322 : InSquare (57/320) (-113/320) (1/320) tau := by
                convert childUL hs101132 hx101132 hy101132 using 1 <;> norm_num
              rcases le_total tau.re (57/320 : ℝ) with hx1011322 | hx1011322
              · rcases le_total tau.im (-113/320 : ℝ) with hy1011322 | hy1011322
                · have hs10113220 : InSquare (113/640) (-227/640) (1/640) tau := by
                    convert childLL hs1011322 hx1011322 hy1011322 using 1 <;> norm_num
                  exact Batch0396.cell3170.sound htau (by
                    simp only [Batch0396.cell3170, Batch0396.tau3170, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10113220 (by positivity) using 1 <;> norm_num)
                · have hs10113222 : InSquare (113/640) (-45/128) (1/640) tau := by
                    convert childUL hs1011322 hx1011322 hy1011322 using 1 <;> norm_num
                  exact Batch0396.cell3172.sound htau (by
                    simp only [Batch0396.cell3172, Batch0396.tau3172, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10113222 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-113/320 : ℝ) with hy1011322 | hy1011322
                · have hs10113221 : InSquare (23/128) (-227/640) (1/640) tau := by
                    convert childLR hs1011322 hx1011322 hy1011322 using 1 <;> norm_num
                  exact Batch0396.cell3171.sound htau (by
                    simp only [Batch0396.cell3171, Batch0396.tau3171, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10113221 (by positivity) using 1 <;> norm_num)
                · have hs10113223 : InSquare (23/128) (-45/128) (1/640) tau := by
                    convert childUR hs1011322 hx1011322 hy1011322 using 1 <;> norm_num
                  exact Batch0396.cell3173.sound htau (by
                    simp only [Batch0396.cell3173, Batch0396.tau3173, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10113223 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-57/160 : ℝ) with hy101132 | hy101132
            · have hs1011321 : InSquare (59/320) (-23/64) (1/320) tau := by
                convert childLR hs101132 hx101132 hy101132 using 1 <;> norm_num
              rcases le_total tau.re (59/320 : ℝ) with hx1011321 | hx1011321
              · rcases le_total tau.im (-23/64 : ℝ) with hy1011321 | hy1011321
                · have hs10113210 : InSquare (117/640) (-231/640) (1/640) tau := by
                    convert childLL hs1011321 hx1011321 hy1011321 using 1 <;> norm_num
                  exact (outside_10113210 htau hs10113210).elim
                · have hs10113212 : InSquare (117/640) (-229/640) (1/640) tau := by
                    convert childUL hs1011321 hx1011321 hy1011321 using 1 <;> norm_num
                  exact Batch0396.cell3169.sound htau (by
                    simp only [Batch0396.cell3169, Batch0396.tau3169, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10113212 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-23/64 : ℝ) with hy1011321 | hy1011321
                · have hs10113211 : InSquare (119/640) (-231/640) (1/640) tau := by
                    convert childLR hs1011321 hx1011321 hy1011321 using 1 <;> norm_num
                  exact (outside_10113211 htau hs10113211).elim
                · have hs10113213 : InSquare (119/640) (-229/640) (1/640) tau := by
                    convert childUR hs1011321 hx1011321 hy1011321 using 1 <;> norm_num
                  exact (outside_10113213 htau hs10113213).elim
            · have hs1011323 : InSquare (59/320) (-113/320) (1/320) tau := by
                convert childUR hs101132 hx101132 hy101132 using 1 <;> norm_num
              rcases le_total tau.re (59/320 : ℝ) with hx1011323 | hx1011323
              · rcases le_total tau.im (-113/320 : ℝ) with hy1011323 | hy1011323
                · have hs10113230 : InSquare (117/640) (-227/640) (1/640) tau := by
                    convert childLL hs1011323 hx1011323 hy1011323 using 1 <;> norm_num
                  exact Batch0396.cell3174.sound htau (by
                    simp only [Batch0396.cell3174, Batch0396.tau3174, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10113230 (by positivity) using 1 <;> norm_num)
                · have hs10113232 : InSquare (117/640) (-45/128) (1/640) tau := by
                    convert childUL hs1011323 hx1011323 hy1011323 using 1 <;> norm_num
                  exact Batch0397.cell3176.sound htau (by
                    simp only [Batch0397.cell3176, Batch0397.tau3176, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10113232 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-113/320 : ℝ) with hy1011323 | hy1011323
                · have hs10113231 : InSquare (119/640) (-227/640) (1/640) tau := by
                    convert childLR hs1011323 hx1011323 hy1011323 using 1 <;> norm_num
                  exact Batch0396.cell3175.sound htau (by
                    simp only [Batch0396.cell3175, Batch0396.tau3175, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10113231 (by positivity) using 1 <;> norm_num)
                · have hs10113233 : InSquare (119/640) (-45/128) (1/640) tau := by
                    convert childUR hs1011323 hx1011323 hy1011323 using 1 <;> norm_num
                  exact Batch0397.cell3177.sound htau (by
                    simp only [Batch0397.cell3177, Batch0397.tau3177, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10113233 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-29/80 : ℝ) with hy10113 | hy10113
        · have hs101131 : InSquare (31/160) (-59/160) (1/160) tau := by
            convert childLR hs10113 hx10113 hy10113 using 1 <;> norm_num
          exact (outside_101131 htau hs101131).elim
        · have hs101133 : InSquare (31/160) (-57/160) (1/160) tau := by
            convert childUR hs10113 hx10113 hy10113 using 1 <;> norm_num
          rcases le_total tau.re (31/160 : ℝ) with hx101133 | hx101133
          · rcases le_total tau.im (-57/160 : ℝ) with hy101133 | hy101133
            · have hs1011330 : InSquare (61/320) (-23/64) (1/320) tau := by
                convert childLL hs101133 hx101133 hy101133 using 1 <;> norm_num
              exact (outside_1011330 htau hs1011330).elim
            · have hs1011332 : InSquare (61/320) (-113/320) (1/320) tau := by
                convert childUL hs101133 hx101133 hy101133 using 1 <;> norm_num
              rcases le_total tau.re (61/320 : ℝ) with hx1011332 | hx1011332
              · rcases le_total tau.im (-113/320 : ℝ) with hy1011332 | hy1011332
                · have hs10113320 : InSquare (121/640) (-227/640) (1/640) tau := by
                    convert childLL hs1011332 hx1011332 hy1011332 using 1 <;> norm_num
                  exact Batch0397.cell3178.sound htau (by
                    simp only [Batch0397.cell3178, Batch0397.tau3178, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10113320 (by positivity) using 1 <;> norm_num)
                · have hs10113322 : InSquare (121/640) (-45/128) (1/640) tau := by
                    convert childUL hs1011332 hx1011332 hy1011332 using 1 <;> norm_num
                  exact Batch0397.cell3179.sound htau (by
                    simp only [Batch0397.cell3179, Batch0397.tau3179, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10113322 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-113/320 : ℝ) with hy1011332 | hy1011332
                · have hs10113321 : InSquare (123/640) (-227/640) (1/640) tau := by
                    convert childLR hs1011332 hx1011332 hy1011332 using 1 <;> norm_num
                  exact (outside_10113321 htau hs10113321).elim
                · have hs10113323 : InSquare (123/640) (-45/128) (1/640) tau := by
                    convert childUR hs1011332 hx1011332 hy1011332 using 1 <;> norm_num
                  exact Batch0397.cell3180.sound htau (by
                    simp only [Batch0397.cell3180, Batch0397.tau3180, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10113323 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-57/160 : ℝ) with hy101133 | hy101133
            · have hs1011331 : InSquare (63/320) (-23/64) (1/320) tau := by
                convert childLR hs101133 hx101133 hy101133 using 1 <;> norm_num
              exact (outside_1011331 htau hs1011331).elim
            · have hs1011333 : InSquare (63/320) (-113/320) (1/320) tau := by
                convert childUR hs101133 hx101133 hy101133 using 1 <;> norm_num
              exact (outside_1011333 htau hs1011333).elim

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1011
