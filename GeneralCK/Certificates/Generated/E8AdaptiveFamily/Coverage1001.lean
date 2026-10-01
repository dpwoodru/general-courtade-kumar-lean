import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0197
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0198
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0199
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0200
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0201
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0202
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0370
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0371
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0372
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0373
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0374
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0375
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0376
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0377
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0378
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0379
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0380

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1001

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

private theorem outside_1001100 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (5/64) (-127/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (3/40 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-3/40)]
  have himSq : (63/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+63/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_1001101 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (27/320) (-127/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (13/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-13/160)]
  have himSq : (63/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+63/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_1001110 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (29/320) (-127/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (7/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-7/80)]
  have himSq : (63/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+63/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_1001111 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (31/320) (-127/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (3/32 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-3/32)]
  have himSq : (63/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+63/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_10010000 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (33/640) (-51/128) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (1/20 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-1/20)]
  have himSq : (127/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+127/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_10010001 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (7/128) (-51/128) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (17/320 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-17/320)]
  have himSq : (127/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+127/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_10010010 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (37/640) (-51/128) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (9/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-9/160)]
  have himSq : (127/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+127/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_10010011 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (39/640) (-51/128) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (19/320 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-19/320)]
  have himSq : (127/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+127/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_10010100 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (41/640) (-51/128) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (1/16 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-1/16)]
  have himSq : (127/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+127/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_10010101 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (43/640) (-51/128) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (21/320 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-21/320)]
  have himSq : (127/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+127/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_10010110 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (9/128) (-51/128) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (11/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-11/160)]
  have himSq : (127/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+127/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_10010111 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (47/640) (-51/128) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (23/320 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-23/320)]
  have himSq : (127/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+127/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_10010113 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (47/640) (-253/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (23/320 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-23/320)]
  have himSq : (63/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+63/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_10011120 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (57/640) (-251/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (7/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-7/80)]
  have himSq : (25/64 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+25/64)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_10011121 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (59/640) (-251/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (29/320 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-29/320)]
  have himSq : (25/64 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+25/64)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_10011130 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (61/640) (-251/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (3/32 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-3/32)]
  have himSq : (25/64 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+25/64)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_10011131 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (63/640) (-251/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (31/320 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-31/320)]
  have himSq : (25/64 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+25/64)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (3/40) (-3/8) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (3/40 : ℝ) with hx1001 | hx1001
  · rcases le_total tau.im (-3/8 : ℝ) with hy1001 | hy1001
    · have hs10010 : InSquare (1/16) (-31/80) (1/80) tau := by
        convert childLL hs hx1001 hy1001 using 1 <;> norm_num
      rcases le_total tau.re (1/16 : ℝ) with hx10010 | hx10010
      · rcases le_total tau.im (-31/80 : ℝ) with hy10010 | hy10010
        · have hs100100 : InSquare (9/160) (-63/160) (1/160) tau := by
            convert childLL hs10010 hx10010 hy10010 using 1 <;> norm_num
          rcases le_total tau.re (9/160 : ℝ) with hx100100 | hx100100
          · rcases le_total tau.im (-63/160 : ℝ) with hy100100 | hy100100
            · have hs1001000 : InSquare (17/320) (-127/320) (1/320) tau := by
                convert childLL hs100100 hx100100 hy100100 using 1 <;> norm_num
              rcases le_total tau.re (17/320 : ℝ) with hx1001000 | hx1001000
              · rcases le_total tau.im (-127/320 : ℝ) with hy1001000 | hy1001000
                · have hs10010000 : InSquare (33/640) (-51/128) (1/640) tau := by
                    convert childLL hs1001000 hx1001000 hy1001000 using 1 <;> norm_num
                  exact (outside_10010000 htau hs10010000).elim
                · have hs10010002 : InSquare (33/640) (-253/640) (1/640) tau := by
                    convert childUL hs1001000 hx1001000 hy1001000 using 1 <;> norm_num
                  exact Batch0370.cell2960.sound htau (by
                    simp only [Batch0370.cell2960, Batch0370.tau2960, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10010002 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-127/320 : ℝ) with hy1001000 | hy1001000
                · have hs10010001 : InSquare (7/128) (-51/128) (1/640) tau := by
                    convert childLR hs1001000 hx1001000 hy1001000 using 1 <;> norm_num
                  exact (outside_10010001 htau hs10010001).elim
                · have hs10010003 : InSquare (7/128) (-253/640) (1/640) tau := by
                    convert childUR hs1001000 hx1001000 hy1001000 using 1 <;> norm_num
                  exact Batch0370.cell2961.sound htau (by
                    simp only [Batch0370.cell2961, Batch0370.tau2961, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10010003 (by positivity) using 1 <;> norm_num)
            · have hs1001002 : InSquare (17/320) (-25/64) (1/320) tau := by
                convert childUL hs100100 hx100100 hy100100 using 1 <;> norm_num
              rcases le_total tau.re (17/320 : ℝ) with hx1001002 | hx1001002
              · rcases le_total tau.im (-25/64 : ℝ) with hy1001002 | hy1001002
                · have hs10010020 : InSquare (33/640) (-251/640) (1/640) tau := by
                    convert childLL hs1001002 hx1001002 hy1001002 using 1 <;> norm_num
                  exact Batch0370.cell2964.sound htau (by
                    simp only [Batch0370.cell2964, Batch0370.tau2964, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10010020 (by positivity) using 1 <;> norm_num)
                · have hs10010022 : InSquare (33/640) (-249/640) (1/640) tau := by
                    convert childUL hs1001002 hx1001002 hy1001002 using 1 <;> norm_num
                  exact Batch0370.cell2966.sound htau (by
                    simp only [Batch0370.cell2966, Batch0370.tau2966, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10010022 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-25/64 : ℝ) with hy1001002 | hy1001002
                · have hs10010021 : InSquare (7/128) (-251/640) (1/640) tau := by
                    convert childLR hs1001002 hx1001002 hy1001002 using 1 <;> norm_num
                  exact Batch0370.cell2965.sound htau (by
                    simp only [Batch0370.cell2965, Batch0370.tau2965, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10010021 (by positivity) using 1 <;> norm_num)
                · have hs10010023 : InSquare (7/128) (-249/640) (1/640) tau := by
                    convert childUR hs1001002 hx1001002 hy1001002 using 1 <;> norm_num
                  exact Batch0370.cell2967.sound htau (by
                    simp only [Batch0370.cell2967, Batch0370.tau2967, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10010023 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-63/160 : ℝ) with hy100100 | hy100100
            · have hs1001001 : InSquare (19/320) (-127/320) (1/320) tau := by
                convert childLR hs100100 hx100100 hy100100 using 1 <;> norm_num
              rcases le_total tau.re (19/320 : ℝ) with hx1001001 | hx1001001
              · rcases le_total tau.im (-127/320 : ℝ) with hy1001001 | hy1001001
                · have hs10010010 : InSquare (37/640) (-51/128) (1/640) tau := by
                    convert childLL hs1001001 hx1001001 hy1001001 using 1 <;> norm_num
                  exact (outside_10010010 htau hs10010010).elim
                · have hs10010012 : InSquare (37/640) (-253/640) (1/640) tau := by
                    convert childUL hs1001001 hx1001001 hy1001001 using 1 <;> norm_num
                  exact Batch0370.cell2962.sound htau (by
                    simp only [Batch0370.cell2962, Batch0370.tau2962, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10010012 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-127/320 : ℝ) with hy1001001 | hy1001001
                · have hs10010011 : InSquare (39/640) (-51/128) (1/640) tau := by
                    convert childLR hs1001001 hx1001001 hy1001001 using 1 <;> norm_num
                  exact (outside_10010011 htau hs10010011).elim
                · have hs10010013 : InSquare (39/640) (-253/640) (1/640) tau := by
                    convert childUR hs1001001 hx1001001 hy1001001 using 1 <;> norm_num
                  exact Batch0370.cell2963.sound htau (by
                    simp only [Batch0370.cell2963, Batch0370.tau2963, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10010013 (by positivity) using 1 <;> norm_num)
            · have hs1001003 : InSquare (19/320) (-25/64) (1/320) tau := by
                convert childUR hs100100 hx100100 hy100100 using 1 <;> norm_num
              rcases le_total tau.re (19/320 : ℝ) with hx1001003 | hx1001003
              · rcases le_total tau.im (-25/64 : ℝ) with hy1001003 | hy1001003
                · have hs10010030 : InSquare (37/640) (-251/640) (1/640) tau := by
                    convert childLL hs1001003 hx1001003 hy1001003 using 1 <;> norm_num
                  exact Batch0371.cell2968.sound htau (by
                    simp only [Batch0371.cell2968, Batch0371.tau2968, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10010030 (by positivity) using 1 <;> norm_num)
                · have hs10010032 : InSquare (37/640) (-249/640) (1/640) tau := by
                    convert childUL hs1001003 hx1001003 hy1001003 using 1 <;> norm_num
                  exact Batch0371.cell2970.sound htau (by
                    simp only [Batch0371.cell2970, Batch0371.tau2970, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10010032 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-25/64 : ℝ) with hy1001003 | hy1001003
                · have hs10010031 : InSquare (39/640) (-251/640) (1/640) tau := by
                    convert childLR hs1001003 hx1001003 hy1001003 using 1 <;> norm_num
                  exact Batch0371.cell2969.sound htau (by
                    simp only [Batch0371.cell2969, Batch0371.tau2969, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10010031 (by positivity) using 1 <;> norm_num)
                · have hs10010033 : InSquare (39/640) (-249/640) (1/640) tau := by
                    convert childUR hs1001003 hx1001003 hy1001003 using 1 <;> norm_num
                  exact Batch0371.cell2971.sound htau (by
                    simp only [Batch0371.cell2971, Batch0371.tau2971, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10010033 (by positivity) using 1 <;> norm_num)
        · have hs100102 : InSquare (9/160) (-61/160) (1/160) tau := by
            convert childUL hs10010 hx10010 hy10010 using 1 <;> norm_num
          rcases le_total tau.re (9/160 : ℝ) with hx100102 | hx100102
          · rcases le_total tau.im (-61/160 : ℝ) with hy100102 | hy100102
            · have hs1001020 : InSquare (17/320) (-123/320) (1/320) tau := by
                convert childLL hs100102 hx100102 hy100102 using 1 <;> norm_num
              rcases le_total tau.re (17/320 : ℝ) with hx1001020 | hx1001020
              · rcases le_total tau.im (-123/320 : ℝ) with hy1001020 | hy1001020
                · have hs10010200 : InSquare (33/640) (-247/640) (1/640) tau := by
                    convert childLL hs1001020 hx1001020 hy1001020 using 1 <;> norm_num
                  exact Batch0372.cell2983.sound htau (by
                    simp only [Batch0372.cell2983, Batch0372.tau2983, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10010200 (by positivity) using 1 <;> norm_num)
                · have hs10010202 : InSquare (33/640) (-49/128) (1/640) tau := by
                    convert childUL hs1001020 hx1001020 hy1001020 using 1 <;> norm_num
                  exact Batch0373.cell2985.sound htau (by
                    simp only [Batch0373.cell2985, Batch0373.tau2985, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10010202 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-123/320 : ℝ) with hy1001020 | hy1001020
                · have hs10010201 : InSquare (7/128) (-247/640) (1/640) tau := by
                    convert childLR hs1001020 hx1001020 hy1001020 using 1 <;> norm_num
                  exact Batch0373.cell2984.sound htau (by
                    simp only [Batch0373.cell2984, Batch0373.tau2984, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10010201 (by positivity) using 1 <;> norm_num)
                · have hs10010203 : InSquare (7/128) (-49/128) (1/640) tau := by
                    convert childUR hs1001020 hx1001020 hy1001020 using 1 <;> norm_num
                  exact Batch0373.cell2986.sound htau (by
                    simp only [Batch0373.cell2986, Batch0373.tau2986, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10010203 (by positivity) using 1 <;> norm_num)
            · have hs1001022 : InSquare (17/320) (-121/320) (1/320) tau := by
                convert childUL hs100102 hx100102 hy100102 using 1 <;> norm_num
              exact Batch0197.cell1582.sound htau (by
                simp only [Batch0197.cell1582, Batch0197.tau1582, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1001022 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-61/160 : ℝ) with hy100102 | hy100102
            · have hs1001021 : InSquare (19/320) (-123/320) (1/320) tau := by
                convert childLR hs100102 hx100102 hy100102 using 1 <;> norm_num
              rcases le_total tau.re (19/320 : ℝ) with hx1001021 | hx1001021
              · rcases le_total tau.im (-123/320 : ℝ) with hy1001021 | hy1001021
                · have hs10010210 : InSquare (37/640) (-247/640) (1/640) tau := by
                    convert childLL hs1001021 hx1001021 hy1001021 using 1 <;> norm_num
                  exact Batch0373.cell2987.sound htau (by
                    simp only [Batch0373.cell2987, Batch0373.tau2987, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10010210 (by positivity) using 1 <;> norm_num)
                · have hs10010212 : InSquare (37/640) (-49/128) (1/640) tau := by
                    convert childUL hs1001021 hx1001021 hy1001021 using 1 <;> norm_num
                  exact Batch0373.cell2989.sound htau (by
                    simp only [Batch0373.cell2989, Batch0373.tau2989, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10010212 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-123/320 : ℝ) with hy1001021 | hy1001021
                · have hs10010211 : InSquare (39/640) (-247/640) (1/640) tau := by
                    convert childLR hs1001021 hx1001021 hy1001021 using 1 <;> norm_num
                  exact Batch0373.cell2988.sound htau (by
                    simp only [Batch0373.cell2988, Batch0373.tau2988, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10010211 (by positivity) using 1 <;> norm_num)
                · have hs10010213 : InSquare (39/640) (-49/128) (1/640) tau := by
                    convert childUR hs1001021 hx1001021 hy1001021 using 1 <;> norm_num
                  exact Batch0373.cell2990.sound htau (by
                    simp only [Batch0373.cell2990, Batch0373.tau2990, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10010213 (by positivity) using 1 <;> norm_num)
            · have hs1001023 : InSquare (19/320) (-121/320) (1/320) tau := by
                convert childUR hs100102 hx100102 hy100102 using 1 <;> norm_num
              exact Batch0197.cell1583.sound htau (by
                simp only [Batch0197.cell1583, Batch0197.tau1583, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1001023 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-31/80 : ℝ) with hy10010 | hy10010
        · have hs100101 : InSquare (11/160) (-63/160) (1/160) tau := by
            convert childLR hs10010 hx10010 hy10010 using 1 <;> norm_num
          rcases le_total tau.re (11/160 : ℝ) with hx100101 | hx100101
          · rcases le_total tau.im (-63/160 : ℝ) with hy100101 | hy100101
            · have hs1001010 : InSquare (21/320) (-127/320) (1/320) tau := by
                convert childLL hs100101 hx100101 hy100101 using 1 <;> norm_num
              rcases le_total tau.re (21/320 : ℝ) with hx1001010 | hx1001010
              · rcases le_total tau.im (-127/320 : ℝ) with hy1001010 | hy1001010
                · have hs10010100 : InSquare (41/640) (-51/128) (1/640) tau := by
                    convert childLL hs1001010 hx1001010 hy1001010 using 1 <;> norm_num
                  exact (outside_10010100 htau hs10010100).elim
                · have hs10010102 : InSquare (41/640) (-253/640) (1/640) tau := by
                    convert childUL hs1001010 hx1001010 hy1001010 using 1 <;> norm_num
                  exact Batch0371.cell2972.sound htau (by
                    simp only [Batch0371.cell2972, Batch0371.tau2972, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10010102 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-127/320 : ℝ) with hy1001010 | hy1001010
                · have hs10010101 : InSquare (43/640) (-51/128) (1/640) tau := by
                    convert childLR hs1001010 hx1001010 hy1001010 using 1 <;> norm_num
                  exact (outside_10010101 htau hs10010101).elim
                · have hs10010103 : InSquare (43/640) (-253/640) (1/640) tau := by
                    convert childUR hs1001010 hx1001010 hy1001010 using 1 <;> norm_num
                  exact Batch0371.cell2973.sound htau (by
                    simp only [Batch0371.cell2973, Batch0371.tau2973, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10010103 (by positivity) using 1 <;> norm_num)
            · have hs1001012 : InSquare (21/320) (-25/64) (1/320) tau := by
                convert childUL hs100101 hx100101 hy100101 using 1 <;> norm_num
              rcases le_total tau.re (21/320 : ℝ) with hx1001012 | hx1001012
              · rcases le_total tau.im (-25/64 : ℝ) with hy1001012 | hy1001012
                · have hs10010120 : InSquare (41/640) (-251/640) (1/640) tau := by
                    convert childLL hs1001012 hx1001012 hy1001012 using 1 <;> norm_num
                  exact Batch0371.cell2975.sound htau (by
                    simp only [Batch0371.cell2975, Batch0371.tau2975, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10010120 (by positivity) using 1 <;> norm_num)
                · have hs10010122 : InSquare (41/640) (-249/640) (1/640) tau := by
                    convert childUL hs1001012 hx1001012 hy1001012 using 1 <;> norm_num
                  exact Batch0372.cell2977.sound htau (by
                    simp only [Batch0372.cell2977, Batch0372.tau2977, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10010122 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-25/64 : ℝ) with hy1001012 | hy1001012
                · have hs10010121 : InSquare (43/640) (-251/640) (1/640) tau := by
                    convert childLR hs1001012 hx1001012 hy1001012 using 1 <;> norm_num
                  exact Batch0372.cell2976.sound htau (by
                    simp only [Batch0372.cell2976, Batch0372.tau2976, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10010121 (by positivity) using 1 <;> norm_num)
                · have hs10010123 : InSquare (43/640) (-249/640) (1/640) tau := by
                    convert childUR hs1001012 hx1001012 hy1001012 using 1 <;> norm_num
                  exact Batch0372.cell2978.sound htau (by
                    simp only [Batch0372.cell2978, Batch0372.tau2978, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10010123 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-63/160 : ℝ) with hy100101 | hy100101
            · have hs1001011 : InSquare (23/320) (-127/320) (1/320) tau := by
                convert childLR hs100101 hx100101 hy100101 using 1 <;> norm_num
              rcases le_total tau.re (23/320 : ℝ) with hx1001011 | hx1001011
              · rcases le_total tau.im (-127/320 : ℝ) with hy1001011 | hy1001011
                · have hs10010110 : InSquare (9/128) (-51/128) (1/640) tau := by
                    convert childLL hs1001011 hx1001011 hy1001011 using 1 <;> norm_num
                  exact (outside_10010110 htau hs10010110).elim
                · have hs10010112 : InSquare (9/128) (-253/640) (1/640) tau := by
                    convert childUL hs1001011 hx1001011 hy1001011 using 1 <;> norm_num
                  exact Batch0371.cell2974.sound htau (by
                    simp only [Batch0371.cell2974, Batch0371.tau2974, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10010112 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-127/320 : ℝ) with hy1001011 | hy1001011
                · have hs10010111 : InSquare (47/640) (-51/128) (1/640) tau := by
                    convert childLR hs1001011 hx1001011 hy1001011 using 1 <;> norm_num
                  exact (outside_10010111 htau hs10010111).elim
                · have hs10010113 : InSquare (47/640) (-253/640) (1/640) tau := by
                    convert childUR hs1001011 hx1001011 hy1001011 using 1 <;> norm_num
                  exact (outside_10010113 htau hs10010113).elim
            · have hs1001013 : InSquare (23/320) (-25/64) (1/320) tau := by
                convert childUR hs100101 hx100101 hy100101 using 1 <;> norm_num
              rcases le_total tau.re (23/320 : ℝ) with hx1001013 | hx1001013
              · rcases le_total tau.im (-25/64 : ℝ) with hy1001013 | hy1001013
                · have hs10010130 : InSquare (9/128) (-251/640) (1/640) tau := by
                    convert childLL hs1001013 hx1001013 hy1001013 using 1 <;> norm_num
                  exact Batch0372.cell2979.sound htau (by
                    simp only [Batch0372.cell2979, Batch0372.tau2979, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10010130 (by positivity) using 1 <;> norm_num)
                · have hs10010132 : InSquare (9/128) (-249/640) (1/640) tau := by
                    convert childUL hs1001013 hx1001013 hy1001013 using 1 <;> norm_num
                  exact Batch0372.cell2981.sound htau (by
                    simp only [Batch0372.cell2981, Batch0372.tau2981, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10010132 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-25/64 : ℝ) with hy1001013 | hy1001013
                · have hs10010131 : InSquare (47/640) (-251/640) (1/640) tau := by
                    convert childLR hs1001013 hx1001013 hy1001013 using 1 <;> norm_num
                  exact Batch0372.cell2980.sound htau (by
                    simp only [Batch0372.cell2980, Batch0372.tau2980, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10010131 (by positivity) using 1 <;> norm_num)
                · have hs10010133 : InSquare (47/640) (-249/640) (1/640) tau := by
                    convert childUR hs1001013 hx1001013 hy1001013 using 1 <;> norm_num
                  exact Batch0372.cell2982.sound htau (by
                    simp only [Batch0372.cell2982, Batch0372.tau2982, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10010133 (by positivity) using 1 <;> norm_num)
        · have hs100103 : InSquare (11/160) (-61/160) (1/160) tau := by
            convert childUR hs10010 hx10010 hy10010 using 1 <;> norm_num
          rcases le_total tau.re (11/160 : ℝ) with hx100103 | hx100103
          · rcases le_total tau.im (-61/160 : ℝ) with hy100103 | hy100103
            · have hs1001030 : InSquare (21/320) (-123/320) (1/320) tau := by
                convert childLL hs100103 hx100103 hy100103 using 1 <;> norm_num
              rcases le_total tau.re (21/320 : ℝ) with hx1001030 | hx1001030
              · rcases le_total tau.im (-123/320 : ℝ) with hy1001030 | hy1001030
                · have hs10010300 : InSquare (41/640) (-247/640) (1/640) tau := by
                    convert childLL hs1001030 hx1001030 hy1001030 using 1 <;> norm_num
                  exact Batch0373.cell2991.sound htau (by
                    simp only [Batch0373.cell2991, Batch0373.tau2991, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10010300 (by positivity) using 1 <;> norm_num)
                · have hs10010302 : InSquare (41/640) (-49/128) (1/640) tau := by
                    convert childUL hs1001030 hx1001030 hy1001030 using 1 <;> norm_num
                  exact Batch0374.cell2993.sound htau (by
                    simp only [Batch0374.cell2993, Batch0374.tau2993, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10010302 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-123/320 : ℝ) with hy1001030 | hy1001030
                · have hs10010301 : InSquare (43/640) (-247/640) (1/640) tau := by
                    convert childLR hs1001030 hx1001030 hy1001030 using 1 <;> norm_num
                  exact Batch0374.cell2992.sound htau (by
                    simp only [Batch0374.cell2992, Batch0374.tau2992, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10010301 (by positivity) using 1 <;> norm_num)
                · have hs10010303 : InSquare (43/640) (-49/128) (1/640) tau := by
                    convert childUR hs1001030 hx1001030 hy1001030 using 1 <;> norm_num
                  exact Batch0374.cell2994.sound htau (by
                    simp only [Batch0374.cell2994, Batch0374.tau2994, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10010303 (by positivity) using 1 <;> norm_num)
            · have hs1001032 : InSquare (21/320) (-121/320) (1/320) tau := by
                convert childUL hs100103 hx100103 hy100103 using 1 <;> norm_num
              exact Batch0198.cell1584.sound htau (by
                simp only [Batch0198.cell1584, Batch0198.tau1584, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1001032 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-61/160 : ℝ) with hy100103 | hy100103
            · have hs1001031 : InSquare (23/320) (-123/320) (1/320) tau := by
                convert childLR hs100103 hx100103 hy100103 using 1 <;> norm_num
              rcases le_total tau.re (23/320 : ℝ) with hx1001031 | hx1001031
              · rcases le_total tau.im (-123/320 : ℝ) with hy1001031 | hy1001031
                · have hs10010310 : InSquare (9/128) (-247/640) (1/640) tau := by
                    convert childLL hs1001031 hx1001031 hy1001031 using 1 <;> norm_num
                  exact Batch0374.cell2995.sound htau (by
                    simp only [Batch0374.cell2995, Batch0374.tau2995, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10010310 (by positivity) using 1 <;> norm_num)
                · have hs10010312 : InSquare (9/128) (-49/128) (1/640) tau := by
                    convert childUL hs1001031 hx1001031 hy1001031 using 1 <;> norm_num
                  exact Batch0374.cell2997.sound htau (by
                    simp only [Batch0374.cell2997, Batch0374.tau2997, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10010312 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-123/320 : ℝ) with hy1001031 | hy1001031
                · have hs10010311 : InSquare (47/640) (-247/640) (1/640) tau := by
                    convert childLR hs1001031 hx1001031 hy1001031 using 1 <;> norm_num
                  exact Batch0374.cell2996.sound htau (by
                    simp only [Batch0374.cell2996, Batch0374.tau2996, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10010311 (by positivity) using 1 <;> norm_num)
                · have hs10010313 : InSquare (47/640) (-49/128) (1/640) tau := by
                    convert childUR hs1001031 hx1001031 hy1001031 using 1 <;> norm_num
                  exact Batch0374.cell2998.sound htau (by
                    simp only [Batch0374.cell2998, Batch0374.tau2998, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10010313 (by positivity) using 1 <;> norm_num)
            · have hs1001033 : InSquare (23/320) (-121/320) (1/320) tau := by
                convert childUR hs100103 hx100103 hy100103 using 1 <;> norm_num
              rcases le_total tau.re (23/320 : ℝ) with hx1001033 | hx1001033
              · rcases le_total tau.im (-121/320 : ℝ) with hy1001033 | hy1001033
                · have hs10010330 : InSquare (9/128) (-243/640) (1/640) tau := by
                    convert childLL hs1001033 hx1001033 hy1001033 using 1 <;> norm_num
                  exact Batch0374.cell2999.sound htau (by
                    simp only [Batch0374.cell2999, Batch0374.tau2999, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10010330 (by positivity) using 1 <;> norm_num)
                · have hs10010332 : InSquare (9/128) (-241/640) (1/640) tau := by
                    convert childUL hs1001033 hx1001033 hy1001033 using 1 <;> norm_num
                  exact Batch0375.cell3001.sound htau (by
                    simp only [Batch0375.cell3001, Batch0375.tau3001, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10010332 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-121/320 : ℝ) with hy1001033 | hy1001033
                · have hs10010331 : InSquare (47/640) (-243/640) (1/640) tau := by
                    convert childLR hs1001033 hx1001033 hy1001033 using 1 <;> norm_num
                  exact Batch0375.cell3000.sound htau (by
                    simp only [Batch0375.cell3000, Batch0375.tau3000, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10010331 (by positivity) using 1 <;> norm_num)
                · have hs10010333 : InSquare (47/640) (-241/640) (1/640) tau := by
                    convert childUR hs1001033 hx1001033 hy1001033 using 1 <;> norm_num
                  exact Batch0375.cell3002.sound htau (by
                    simp only [Batch0375.cell3002, Batch0375.tau3002, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10010333 (by positivity) using 1 <;> norm_num)
    · have hs10012 : InSquare (1/16) (-29/80) (1/80) tau := by
        convert childUL hs hx1001 hy1001 using 1 <;> norm_num
      rcases le_total tau.re (1/16 : ℝ) with hx10012 | hx10012
      · rcases le_total tau.im (-29/80 : ℝ) with hy10012 | hy10012
        · have hs100120 : InSquare (9/160) (-59/160) (1/160) tau := by
            convert childLL hs10012 hx10012 hy10012 using 1 <;> norm_num
          rcases le_total tau.re (9/160 : ℝ) with hx100120 | hx100120
          · rcases le_total tau.im (-59/160 : ℝ) with hy100120 | hy100120
            · have hs1001200 : InSquare (17/320) (-119/320) (1/320) tau := by
                convert childLL hs100120 hx100120 hy100120 using 1 <;> norm_num
              exact Batch0198.cell1585.sound htau (by
                simp only [Batch0198.cell1585, Batch0198.tau1585, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1001200 (by positivity) using 1 <;> norm_num)
            · have hs1001202 : InSquare (17/320) (-117/320) (1/320) tau := by
                convert childUL hs100120 hx100120 hy100120 using 1 <;> norm_num
              exact Batch0198.cell1587.sound htau (by
                simp only [Batch0198.cell1587, Batch0198.tau1587, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1001202 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-59/160 : ℝ) with hy100120 | hy100120
            · have hs1001201 : InSquare (19/320) (-119/320) (1/320) tau := by
                convert childLR hs100120 hx100120 hy100120 using 1 <;> norm_num
              exact Batch0198.cell1586.sound htau (by
                simp only [Batch0198.cell1586, Batch0198.tau1586, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1001201 (by positivity) using 1 <;> norm_num)
            · have hs1001203 : InSquare (19/320) (-117/320) (1/320) tau := by
                convert childUR hs100120 hx100120 hy100120 using 1 <;> norm_num
              exact Batch0198.cell1588.sound htau (by
                simp only [Batch0198.cell1588, Batch0198.tau1588, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1001203 (by positivity) using 1 <;> norm_num)
        · have hs100122 : InSquare (9/160) (-57/160) (1/160) tau := by
            convert childUL hs10012 hx10012 hy10012 using 1 <;> norm_num
          rcases le_total tau.re (9/160 : ℝ) with hx100122 | hx100122
          · rcases le_total tau.im (-57/160 : ℝ) with hy100122 | hy100122
            · have hs1001220 : InSquare (17/320) (-23/64) (1/320) tau := by
                convert childLL hs100122 hx100122 hy100122 using 1 <;> norm_num
              exact Batch0199.cell1593.sound htau (by
                simp only [Batch0199.cell1593, Batch0199.tau1593, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1001220 (by positivity) using 1 <;> norm_num)
            · have hs1001222 : InSquare (17/320) (-113/320) (1/320) tau := by
                convert childUL hs100122 hx100122 hy100122 using 1 <;> norm_num
              exact Batch0199.cell1595.sound htau (by
                simp only [Batch0199.cell1595, Batch0199.tau1595, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1001222 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-57/160 : ℝ) with hy100122 | hy100122
            · have hs1001221 : InSquare (19/320) (-23/64) (1/320) tau := by
                convert childLR hs100122 hx100122 hy100122 using 1 <;> norm_num
              exact Batch0199.cell1594.sound htau (by
                simp only [Batch0199.cell1594, Batch0199.tau1594, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1001221 (by positivity) using 1 <;> norm_num)
            · have hs1001223 : InSquare (19/320) (-113/320) (1/320) tau := by
                convert childUR hs100122 hx100122 hy100122 using 1 <;> norm_num
              exact Batch0199.cell1596.sound htau (by
                simp only [Batch0199.cell1596, Batch0199.tau1596, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1001223 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-29/80 : ℝ) with hy10012 | hy10012
        · have hs100121 : InSquare (11/160) (-59/160) (1/160) tau := by
            convert childLR hs10012 hx10012 hy10012 using 1 <;> norm_num
          rcases le_total tau.re (11/160 : ℝ) with hx100121 | hx100121
          · rcases le_total tau.im (-59/160 : ℝ) with hy100121 | hy100121
            · have hs1001210 : InSquare (21/320) (-119/320) (1/320) tau := by
                convert childLL hs100121 hx100121 hy100121 using 1 <;> norm_num
              exact Batch0198.cell1589.sound htau (by
                simp only [Batch0198.cell1589, Batch0198.tau1589, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1001210 (by positivity) using 1 <;> norm_num)
            · have hs1001212 : InSquare (21/320) (-117/320) (1/320) tau := by
                convert childUL hs100121 hx100121 hy100121 using 1 <;> norm_num
              exact Batch0198.cell1591.sound htau (by
                simp only [Batch0198.cell1591, Batch0198.tau1591, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1001212 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-59/160 : ℝ) with hy100121 | hy100121
            · have hs1001211 : InSquare (23/320) (-119/320) (1/320) tau := by
                convert childLR hs100121 hx100121 hy100121 using 1 <;> norm_num
              exact Batch0198.cell1590.sound htau (by
                simp only [Batch0198.cell1590, Batch0198.tau1590, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1001211 (by positivity) using 1 <;> norm_num)
            · have hs1001213 : InSquare (23/320) (-117/320) (1/320) tau := by
                convert childUR hs100121 hx100121 hy100121 using 1 <;> norm_num
              exact Batch0199.cell1592.sound htau (by
                simp only [Batch0199.cell1592, Batch0199.tau1592, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1001213 (by positivity) using 1 <;> norm_num)
        · have hs100123 : InSquare (11/160) (-57/160) (1/160) tau := by
            convert childUR hs10012 hx10012 hy10012 using 1 <;> norm_num
          rcases le_total tau.re (11/160 : ℝ) with hx100123 | hx100123
          · rcases le_total tau.im (-57/160 : ℝ) with hy100123 | hy100123
            · have hs1001230 : InSquare (21/320) (-23/64) (1/320) tau := by
                convert childLL hs100123 hx100123 hy100123 using 1 <;> norm_num
              exact Batch0199.cell1597.sound htau (by
                simp only [Batch0199.cell1597, Batch0199.tau1597, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1001230 (by positivity) using 1 <;> norm_num)
            · have hs1001232 : InSquare (21/320) (-113/320) (1/320) tau := by
                convert childUL hs100123 hx100123 hy100123 using 1 <;> norm_num
              exact Batch0199.cell1599.sound htau (by
                simp only [Batch0199.cell1599, Batch0199.tau1599, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1001232 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-57/160 : ℝ) with hy100123 | hy100123
            · have hs1001231 : InSquare (23/320) (-23/64) (1/320) tau := by
                convert childLR hs100123 hx100123 hy100123 using 1 <;> norm_num
              exact Batch0199.cell1598.sound htau (by
                simp only [Batch0199.cell1598, Batch0199.tau1598, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1001231 (by positivity) using 1 <;> norm_num)
            · have hs1001233 : InSquare (23/320) (-113/320) (1/320) tau := by
                convert childUR hs100123 hx100123 hy100123 using 1 <;> norm_num
              exact Batch0200.cell1600.sound htau (by
                simp only [Batch0200.cell1600, Batch0200.tau1600, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1001233 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (-3/8 : ℝ) with hy1001 | hy1001
    · have hs10011 : InSquare (7/80) (-31/80) (1/80) tau := by
        convert childLR hs hx1001 hy1001 using 1 <;> norm_num
      rcases le_total tau.re (7/80 : ℝ) with hx10011 | hx10011
      · rcases le_total tau.im (-31/80 : ℝ) with hy10011 | hy10011
        · have hs100110 : InSquare (13/160) (-63/160) (1/160) tau := by
            convert childLL hs10011 hx10011 hy10011 using 1 <;> norm_num
          rcases le_total tau.re (13/160 : ℝ) with hx100110 | hx100110
          · rcases le_total tau.im (-63/160 : ℝ) with hy100110 | hy100110
            · have hs1001100 : InSquare (5/64) (-127/320) (1/320) tau := by
                convert childLL hs100110 hx100110 hy100110 using 1 <;> norm_num
              exact (outside_1001100 htau hs1001100).elim
            · have hs1001102 : InSquare (5/64) (-25/64) (1/320) tau := by
                convert childUL hs100110 hx100110 hy100110 using 1 <;> norm_num
              rcases le_total tau.re (5/64 : ℝ) with hx1001102 | hx1001102
              · rcases le_total tau.im (-25/64 : ℝ) with hy1001102 | hy1001102
                · have hs10011020 : InSquare (49/640) (-251/640) (1/640) tau := by
                    convert childLL hs1001102 hx1001102 hy1001102 using 1 <;> norm_num
                  exact Batch0375.cell3003.sound htau (by
                    simp only [Batch0375.cell3003, Batch0375.tau3003, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10011020 (by positivity) using 1 <;> norm_num)
                · have hs10011022 : InSquare (49/640) (-249/640) (1/640) tau := by
                    convert childUL hs1001102 hx1001102 hy1001102 using 1 <;> norm_num
                  exact Batch0375.cell3005.sound htau (by
                    simp only [Batch0375.cell3005, Batch0375.tau3005, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10011022 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-25/64 : ℝ) with hy1001102 | hy1001102
                · have hs10011021 : InSquare (51/640) (-251/640) (1/640) tau := by
                    convert childLR hs1001102 hx1001102 hy1001102 using 1 <;> norm_num
                  exact Batch0375.cell3004.sound htau (by
                    simp only [Batch0375.cell3004, Batch0375.tau3004, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10011021 (by positivity) using 1 <;> norm_num)
                · have hs10011023 : InSquare (51/640) (-249/640) (1/640) tau := by
                    convert childUR hs1001102 hx1001102 hy1001102 using 1 <;> norm_num
                  exact Batch0375.cell3006.sound htau (by
                    simp only [Batch0375.cell3006, Batch0375.tau3006, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10011023 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-63/160 : ℝ) with hy100110 | hy100110
            · have hs1001101 : InSquare (27/320) (-127/320) (1/320) tau := by
                convert childLR hs100110 hx100110 hy100110 using 1 <;> norm_num
              exact (outside_1001101 htau hs1001101).elim
            · have hs1001103 : InSquare (27/320) (-25/64) (1/320) tau := by
                convert childUR hs100110 hx100110 hy100110 using 1 <;> norm_num
              rcases le_total tau.re (27/320 : ℝ) with hx1001103 | hx1001103
              · rcases le_total tau.im (-25/64 : ℝ) with hy1001103 | hy1001103
                · have hs10011030 : InSquare (53/640) (-251/640) (1/640) tau := by
                    convert childLL hs1001103 hx1001103 hy1001103 using 1 <;> norm_num
                  exact Batch0375.cell3007.sound htau (by
                    simp only [Batch0375.cell3007, Batch0375.tau3007, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10011030 (by positivity) using 1 <;> norm_num)
                · have hs10011032 : InSquare (53/640) (-249/640) (1/640) tau := by
                    convert childUL hs1001103 hx1001103 hy1001103 using 1 <;> norm_num
                  exact Batch0376.cell3009.sound htau (by
                    simp only [Batch0376.cell3009, Batch0376.tau3009, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10011032 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-25/64 : ℝ) with hy1001103 | hy1001103
                · have hs10011031 : InSquare (11/128) (-251/640) (1/640) tau := by
                    convert childLR hs1001103 hx1001103 hy1001103 using 1 <;> norm_num
                  exact Batch0376.cell3008.sound htau (by
                    simp only [Batch0376.cell3008, Batch0376.tau3008, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10011031 (by positivity) using 1 <;> norm_num)
                · have hs10011033 : InSquare (11/128) (-249/640) (1/640) tau := by
                    convert childUR hs1001103 hx1001103 hy1001103 using 1 <;> norm_num
                  exact Batch0376.cell3010.sound htau (by
                    simp only [Batch0376.cell3010, Batch0376.tau3010, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10011033 (by positivity) using 1 <;> norm_num)
        · have hs100112 : InSquare (13/160) (-61/160) (1/160) tau := by
            convert childUL hs10011 hx10011 hy10011 using 1 <;> norm_num
          rcases le_total tau.re (13/160 : ℝ) with hx100112 | hx100112
          · rcases le_total tau.im (-61/160 : ℝ) with hy100112 | hy100112
            · have hs1001120 : InSquare (5/64) (-123/320) (1/320) tau := by
                convert childLL hs100112 hx100112 hy100112 using 1 <;> norm_num
              rcases le_total tau.re (5/64 : ℝ) with hx1001120 | hx1001120
              · rcases le_total tau.im (-123/320 : ℝ) with hy1001120 | hy1001120
                · have hs10011200 : InSquare (49/640) (-247/640) (1/640) tau := by
                    convert childLL hs1001120 hx1001120 hy1001120 using 1 <;> norm_num
                  exact Batch0376.cell3015.sound htau (by
                    simp only [Batch0376.cell3015, Batch0376.tau3015, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10011200 (by positivity) using 1 <;> norm_num)
                · have hs10011202 : InSquare (49/640) (-49/128) (1/640) tau := by
                    convert childUL hs1001120 hx1001120 hy1001120 using 1 <;> norm_num
                  exact Batch0377.cell3017.sound htau (by
                    simp only [Batch0377.cell3017, Batch0377.tau3017, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10011202 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-123/320 : ℝ) with hy1001120 | hy1001120
                · have hs10011201 : InSquare (51/640) (-247/640) (1/640) tau := by
                    convert childLR hs1001120 hx1001120 hy1001120 using 1 <;> norm_num
                  exact Batch0377.cell3016.sound htau (by
                    simp only [Batch0377.cell3016, Batch0377.tau3016, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10011201 (by positivity) using 1 <;> norm_num)
                · have hs10011203 : InSquare (51/640) (-49/128) (1/640) tau := by
                    convert childUR hs1001120 hx1001120 hy1001120 using 1 <;> norm_num
                  exact Batch0377.cell3018.sound htau (by
                    simp only [Batch0377.cell3018, Batch0377.tau3018, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10011203 (by positivity) using 1 <;> norm_num)
            · have hs1001122 : InSquare (5/64) (-121/320) (1/320) tau := by
                convert childUL hs100112 hx100112 hy100112 using 1 <;> norm_num
              rcases le_total tau.re (5/64 : ℝ) with hx1001122 | hx1001122
              · rcases le_total tau.im (-121/320 : ℝ) with hy1001122 | hy1001122
                · have hs10011220 : InSquare (49/640) (-243/640) (1/640) tau := by
                    convert childLL hs1001122 hx1001122 hy1001122 using 1 <;> norm_num
                  exact Batch0377.cell3023.sound htau (by
                    simp only [Batch0377.cell3023, Batch0377.tau3023, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10011220 (by positivity) using 1 <;> norm_num)
                · have hs10011222 : InSquare (49/640) (-241/640) (1/640) tau := by
                    convert childUL hs1001122 hx1001122 hy1001122 using 1 <;> norm_num
                  exact Batch0378.cell3025.sound htau (by
                    simp only [Batch0378.cell3025, Batch0378.tau3025, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10011222 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-121/320 : ℝ) with hy1001122 | hy1001122
                · have hs10011221 : InSquare (51/640) (-243/640) (1/640) tau := by
                    convert childLR hs1001122 hx1001122 hy1001122 using 1 <;> norm_num
                  exact Batch0378.cell3024.sound htau (by
                    simp only [Batch0378.cell3024, Batch0378.tau3024, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10011221 (by positivity) using 1 <;> norm_num)
                · have hs10011223 : InSquare (51/640) (-241/640) (1/640) tau := by
                    convert childUR hs1001122 hx1001122 hy1001122 using 1 <;> norm_num
                  exact Batch0378.cell3026.sound htau (by
                    simp only [Batch0378.cell3026, Batch0378.tau3026, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10011223 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-61/160 : ℝ) with hy100112 | hy100112
            · have hs1001121 : InSquare (27/320) (-123/320) (1/320) tau := by
                convert childLR hs100112 hx100112 hy100112 using 1 <;> norm_num
              rcases le_total tau.re (27/320 : ℝ) with hx1001121 | hx1001121
              · rcases le_total tau.im (-123/320 : ℝ) with hy1001121 | hy1001121
                · have hs10011210 : InSquare (53/640) (-247/640) (1/640) tau := by
                    convert childLL hs1001121 hx1001121 hy1001121 using 1 <;> norm_num
                  exact Batch0377.cell3019.sound htau (by
                    simp only [Batch0377.cell3019, Batch0377.tau3019, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10011210 (by positivity) using 1 <;> norm_num)
                · have hs10011212 : InSquare (53/640) (-49/128) (1/640) tau := by
                    convert childUL hs1001121 hx1001121 hy1001121 using 1 <;> norm_num
                  exact Batch0377.cell3021.sound htau (by
                    simp only [Batch0377.cell3021, Batch0377.tau3021, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10011212 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-123/320 : ℝ) with hy1001121 | hy1001121
                · have hs10011211 : InSquare (11/128) (-247/640) (1/640) tau := by
                    convert childLR hs1001121 hx1001121 hy1001121 using 1 <;> norm_num
                  exact Batch0377.cell3020.sound htau (by
                    simp only [Batch0377.cell3020, Batch0377.tau3020, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10011211 (by positivity) using 1 <;> norm_num)
                · have hs10011213 : InSquare (11/128) (-49/128) (1/640) tau := by
                    convert childUR hs1001121 hx1001121 hy1001121 using 1 <;> norm_num
                  exact Batch0377.cell3022.sound htau (by
                    simp only [Batch0377.cell3022, Batch0377.tau3022, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10011213 (by positivity) using 1 <;> norm_num)
            · have hs1001123 : InSquare (27/320) (-121/320) (1/320) tau := by
                convert childUR hs100112 hx100112 hy100112 using 1 <;> norm_num
              rcases le_total tau.re (27/320 : ℝ) with hx1001123 | hx1001123
              · rcases le_total tau.im (-121/320 : ℝ) with hy1001123 | hy1001123
                · have hs10011230 : InSquare (53/640) (-243/640) (1/640) tau := by
                    convert childLL hs1001123 hx1001123 hy1001123 using 1 <;> norm_num
                  exact Batch0378.cell3027.sound htau (by
                    simp only [Batch0378.cell3027, Batch0378.tau3027, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10011230 (by positivity) using 1 <;> norm_num)
                · have hs10011232 : InSquare (53/640) (-241/640) (1/640) tau := by
                    convert childUL hs1001123 hx1001123 hy1001123 using 1 <;> norm_num
                  exact Batch0378.cell3029.sound htau (by
                    simp only [Batch0378.cell3029, Batch0378.tau3029, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10011232 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-121/320 : ℝ) with hy1001123 | hy1001123
                · have hs10011231 : InSquare (11/128) (-243/640) (1/640) tau := by
                    convert childLR hs1001123 hx1001123 hy1001123 using 1 <;> norm_num
                  exact Batch0378.cell3028.sound htau (by
                    simp only [Batch0378.cell3028, Batch0378.tau3028, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10011231 (by positivity) using 1 <;> norm_num)
                · have hs10011233 : InSquare (11/128) (-241/640) (1/640) tau := by
                    convert childUR hs1001123 hx1001123 hy1001123 using 1 <;> norm_num
                  exact Batch0378.cell3030.sound htau (by
                    simp only [Batch0378.cell3030, Batch0378.tau3030, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10011233 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-31/80 : ℝ) with hy10011 | hy10011
        · have hs100111 : InSquare (3/32) (-63/160) (1/160) tau := by
            convert childLR hs10011 hx10011 hy10011 using 1 <;> norm_num
          rcases le_total tau.re (3/32 : ℝ) with hx100111 | hx100111
          · rcases le_total tau.im (-63/160 : ℝ) with hy100111 | hy100111
            · have hs1001110 : InSquare (29/320) (-127/320) (1/320) tau := by
                convert childLL hs100111 hx100111 hy100111 using 1 <;> norm_num
              exact (outside_1001110 htau hs1001110).elim
            · have hs1001112 : InSquare (29/320) (-25/64) (1/320) tau := by
                convert childUL hs100111 hx100111 hy100111 using 1 <;> norm_num
              rcases le_total tau.re (29/320 : ℝ) with hx1001112 | hx1001112
              · rcases le_total tau.im (-25/64 : ℝ) with hy1001112 | hy1001112
                · have hs10011120 : InSquare (57/640) (-251/640) (1/640) tau := by
                    convert childLL hs1001112 hx1001112 hy1001112 using 1 <;> norm_num
                  exact (outside_10011120 htau hs10011120).elim
                · have hs10011122 : InSquare (57/640) (-249/640) (1/640) tau := by
                    convert childUL hs1001112 hx1001112 hy1001112 using 1 <;> norm_num
                  exact Batch0376.cell3011.sound htau (by
                    simp only [Batch0376.cell3011, Batch0376.tau3011, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10011122 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-25/64 : ℝ) with hy1001112 | hy1001112
                · have hs10011121 : InSquare (59/640) (-251/640) (1/640) tau := by
                    convert childLR hs1001112 hx1001112 hy1001112 using 1 <;> norm_num
                  exact (outside_10011121 htau hs10011121).elim
                · have hs10011123 : InSquare (59/640) (-249/640) (1/640) tau := by
                    convert childUR hs1001112 hx1001112 hy1001112 using 1 <;> norm_num
                  exact Batch0376.cell3012.sound htau (by
                    simp only [Batch0376.cell3012, Batch0376.tau3012, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10011123 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-63/160 : ℝ) with hy100111 | hy100111
            · have hs1001111 : InSquare (31/320) (-127/320) (1/320) tau := by
                convert childLR hs100111 hx100111 hy100111 using 1 <;> norm_num
              exact (outside_1001111 htau hs1001111).elim
            · have hs1001113 : InSquare (31/320) (-25/64) (1/320) tau := by
                convert childUR hs100111 hx100111 hy100111 using 1 <;> norm_num
              rcases le_total tau.re (31/320 : ℝ) with hx1001113 | hx1001113
              · rcases le_total tau.im (-25/64 : ℝ) with hy1001113 | hy1001113
                · have hs10011130 : InSquare (61/640) (-251/640) (1/640) tau := by
                    convert childLL hs1001113 hx1001113 hy1001113 using 1 <;> norm_num
                  exact (outside_10011130 htau hs10011130).elim
                · have hs10011132 : InSquare (61/640) (-249/640) (1/640) tau := by
                    convert childUL hs1001113 hx1001113 hy1001113 using 1 <;> norm_num
                  exact Batch0376.cell3013.sound htau (by
                    simp only [Batch0376.cell3013, Batch0376.tau3013, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10011132 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-25/64 : ℝ) with hy1001113 | hy1001113
                · have hs10011131 : InSquare (63/640) (-251/640) (1/640) tau := by
                    convert childLR hs1001113 hx1001113 hy1001113 using 1 <;> norm_num
                  exact (outside_10011131 htau hs10011131).elim
                · have hs10011133 : InSquare (63/640) (-249/640) (1/640) tau := by
                    convert childUR hs1001113 hx1001113 hy1001113 using 1 <;> norm_num
                  exact Batch0376.cell3014.sound htau (by
                    simp only [Batch0376.cell3014, Batch0376.tau3014, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10011133 (by positivity) using 1 <;> norm_num)
        · have hs100113 : InSquare (3/32) (-61/160) (1/160) tau := by
            convert childUR hs10011 hx10011 hy10011 using 1 <;> norm_num
          rcases le_total tau.re (3/32 : ℝ) with hx100113 | hx100113
          · rcases le_total tau.im (-61/160 : ℝ) with hy100113 | hy100113
            · have hs1001130 : InSquare (29/320) (-123/320) (1/320) tau := by
                convert childLL hs100113 hx100113 hy100113 using 1 <;> norm_num
              rcases le_total tau.re (29/320 : ℝ) with hx1001130 | hx1001130
              · rcases le_total tau.im (-123/320 : ℝ) with hy1001130 | hy1001130
                · have hs10011300 : InSquare (57/640) (-247/640) (1/640) tau := by
                    convert childLL hs1001130 hx1001130 hy1001130 using 1 <;> norm_num
                  exact Batch0378.cell3031.sound htau (by
                    simp only [Batch0378.cell3031, Batch0378.tau3031, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10011300 (by positivity) using 1 <;> norm_num)
                · have hs10011302 : InSquare (57/640) (-49/128) (1/640) tau := by
                    convert childUL hs1001130 hx1001130 hy1001130 using 1 <;> norm_num
                  exact Batch0379.cell3033.sound htau (by
                    simp only [Batch0379.cell3033, Batch0379.tau3033, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10011302 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-123/320 : ℝ) with hy1001130 | hy1001130
                · have hs10011301 : InSquare (59/640) (-247/640) (1/640) tau := by
                    convert childLR hs1001130 hx1001130 hy1001130 using 1 <;> norm_num
                  exact Batch0379.cell3032.sound htau (by
                    simp only [Batch0379.cell3032, Batch0379.tau3032, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10011301 (by positivity) using 1 <;> norm_num)
                · have hs10011303 : InSquare (59/640) (-49/128) (1/640) tau := by
                    convert childUR hs1001130 hx1001130 hy1001130 using 1 <;> norm_num
                  exact Batch0379.cell3034.sound htau (by
                    simp only [Batch0379.cell3034, Batch0379.tau3034, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10011303 (by positivity) using 1 <;> norm_num)
            · have hs1001132 : InSquare (29/320) (-121/320) (1/320) tau := by
                convert childUL hs100113 hx100113 hy100113 using 1 <;> norm_num
              rcases le_total tau.re (29/320 : ℝ) with hx1001132 | hx1001132
              · rcases le_total tau.im (-121/320 : ℝ) with hy1001132 | hy1001132
                · have hs10011320 : InSquare (57/640) (-243/640) (1/640) tau := by
                    convert childLL hs1001132 hx1001132 hy1001132 using 1 <;> norm_num
                  exact Batch0379.cell3039.sound htau (by
                    simp only [Batch0379.cell3039, Batch0379.tau3039, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10011320 (by positivity) using 1 <;> norm_num)
                · have hs10011322 : InSquare (57/640) (-241/640) (1/640) tau := by
                    convert childUL hs1001132 hx1001132 hy1001132 using 1 <;> norm_num
                  exact Batch0380.cell3041.sound htau (by
                    simp only [Batch0380.cell3041, Batch0380.tau3041, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10011322 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-121/320 : ℝ) with hy1001132 | hy1001132
                · have hs10011321 : InSquare (59/640) (-243/640) (1/640) tau := by
                    convert childLR hs1001132 hx1001132 hy1001132 using 1 <;> norm_num
                  exact Batch0380.cell3040.sound htau (by
                    simp only [Batch0380.cell3040, Batch0380.tau3040, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10011321 (by positivity) using 1 <;> norm_num)
                · have hs10011323 : InSquare (59/640) (-241/640) (1/640) tau := by
                    convert childUR hs1001132 hx1001132 hy1001132 using 1 <;> norm_num
                  exact Batch0380.cell3042.sound htau (by
                    simp only [Batch0380.cell3042, Batch0380.tau3042, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10011323 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-61/160 : ℝ) with hy100113 | hy100113
            · have hs1001131 : InSquare (31/320) (-123/320) (1/320) tau := by
                convert childLR hs100113 hx100113 hy100113 using 1 <;> norm_num
              rcases le_total tau.re (31/320 : ℝ) with hx1001131 | hx1001131
              · rcases le_total tau.im (-123/320 : ℝ) with hy1001131 | hy1001131
                · have hs10011310 : InSquare (61/640) (-247/640) (1/640) tau := by
                    convert childLL hs1001131 hx1001131 hy1001131 using 1 <;> norm_num
                  exact Batch0379.cell3035.sound htau (by
                    simp only [Batch0379.cell3035, Batch0379.tau3035, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10011310 (by positivity) using 1 <;> norm_num)
                · have hs10011312 : InSquare (61/640) (-49/128) (1/640) tau := by
                    convert childUL hs1001131 hx1001131 hy1001131 using 1 <;> norm_num
                  exact Batch0379.cell3037.sound htau (by
                    simp only [Batch0379.cell3037, Batch0379.tau3037, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10011312 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-123/320 : ℝ) with hy1001131 | hy1001131
                · have hs10011311 : InSquare (63/640) (-247/640) (1/640) tau := by
                    convert childLR hs1001131 hx1001131 hy1001131 using 1 <;> norm_num
                  exact Batch0379.cell3036.sound htau (by
                    simp only [Batch0379.cell3036, Batch0379.tau3036, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10011311 (by positivity) using 1 <;> norm_num)
                · have hs10011313 : InSquare (63/640) (-49/128) (1/640) tau := by
                    convert childUR hs1001131 hx1001131 hy1001131 using 1 <;> norm_num
                  exact Batch0379.cell3038.sound htau (by
                    simp only [Batch0379.cell3038, Batch0379.tau3038, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10011313 (by positivity) using 1 <;> norm_num)
            · have hs1001133 : InSquare (31/320) (-121/320) (1/320) tau := by
                convert childUR hs100113 hx100113 hy100113 using 1 <;> norm_num
              rcases le_total tau.re (31/320 : ℝ) with hx1001133 | hx1001133
              · rcases le_total tau.im (-121/320 : ℝ) with hy1001133 | hy1001133
                · have hs10011330 : InSquare (61/640) (-243/640) (1/640) tau := by
                    convert childLL hs1001133 hx1001133 hy1001133 using 1 <;> norm_num
                  exact Batch0380.cell3043.sound htau (by
                    simp only [Batch0380.cell3043, Batch0380.tau3043, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10011330 (by positivity) using 1 <;> norm_num)
                · have hs10011332 : InSquare (61/640) (-241/640) (1/640) tau := by
                    convert childUL hs1001133 hx1001133 hy1001133 using 1 <;> norm_num
                  exact Batch0380.cell3045.sound htau (by
                    simp only [Batch0380.cell3045, Batch0380.tau3045, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10011332 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-121/320 : ℝ) with hy1001133 | hy1001133
                · have hs10011331 : InSquare (63/640) (-243/640) (1/640) tau := by
                    convert childLR hs1001133 hx1001133 hy1001133 using 1 <;> norm_num
                  exact Batch0380.cell3044.sound htau (by
                    simp only [Batch0380.cell3044, Batch0380.tau3044, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10011331 (by positivity) using 1 <;> norm_num)
                · have hs10011333 : InSquare (63/640) (-241/640) (1/640) tau := by
                    convert childUR hs1001133 hx1001133 hy1001133 using 1 <;> norm_num
                  exact Batch0380.cell3046.sound htau (by
                    simp only [Batch0380.cell3046, Batch0380.tau3046, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10011333 (by positivity) using 1 <;> norm_num)
    · have hs10013 : InSquare (7/80) (-29/80) (1/80) tau := by
        convert childUR hs hx1001 hy1001 using 1 <;> norm_num
      rcases le_total tau.re (7/80 : ℝ) with hx10013 | hx10013
      · rcases le_total tau.im (-29/80 : ℝ) with hy10013 | hy10013
        · have hs100130 : InSquare (13/160) (-59/160) (1/160) tau := by
            convert childLL hs10013 hx10013 hy10013 using 1 <;> norm_num
          rcases le_total tau.re (13/160 : ℝ) with hx100130 | hx100130
          · rcases le_total tau.im (-59/160 : ℝ) with hy100130 | hy100130
            · have hs1001300 : InSquare (5/64) (-119/320) (1/320) tau := by
                convert childLL hs100130 hx100130 hy100130 using 1 <;> norm_num
              exact Batch0200.cell1601.sound htau (by
                simp only [Batch0200.cell1601, Batch0200.tau1601, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1001300 (by positivity) using 1 <;> norm_num)
            · have hs1001302 : InSquare (5/64) (-117/320) (1/320) tau := by
                convert childUL hs100130 hx100130 hy100130 using 1 <;> norm_num
              exact Batch0200.cell1603.sound htau (by
                simp only [Batch0200.cell1603, Batch0200.tau1603, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1001302 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-59/160 : ℝ) with hy100130 | hy100130
            · have hs1001301 : InSquare (27/320) (-119/320) (1/320) tau := by
                convert childLR hs100130 hx100130 hy100130 using 1 <;> norm_num
              exact Batch0200.cell1602.sound htau (by
                simp only [Batch0200.cell1602, Batch0200.tau1602, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1001301 (by positivity) using 1 <;> norm_num)
            · have hs1001303 : InSquare (27/320) (-117/320) (1/320) tau := by
                convert childUR hs100130 hx100130 hy100130 using 1 <;> norm_num
              exact Batch0200.cell1604.sound htau (by
                simp only [Batch0200.cell1604, Batch0200.tau1604, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1001303 (by positivity) using 1 <;> norm_num)
        · have hs100132 : InSquare (13/160) (-57/160) (1/160) tau := by
            convert childUL hs10013 hx10013 hy10013 using 1 <;> norm_num
          rcases le_total tau.re (13/160 : ℝ) with hx100132 | hx100132
          · rcases le_total tau.im (-57/160 : ℝ) with hy100132 | hy100132
            · have hs1001320 : InSquare (5/64) (-23/64) (1/320) tau := by
                convert childLL hs100132 hx100132 hy100132 using 1 <;> norm_num
              exact Batch0201.cell1609.sound htau (by
                simp only [Batch0201.cell1609, Batch0201.tau1609, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1001320 (by positivity) using 1 <;> norm_num)
            · have hs1001322 : InSquare (5/64) (-113/320) (1/320) tau := by
                convert childUL hs100132 hx100132 hy100132 using 1 <;> norm_num
              exact Batch0201.cell1611.sound htau (by
                simp only [Batch0201.cell1611, Batch0201.tau1611, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1001322 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-57/160 : ℝ) with hy100132 | hy100132
            · have hs1001321 : InSquare (27/320) (-23/64) (1/320) tau := by
                convert childLR hs100132 hx100132 hy100132 using 1 <;> norm_num
              exact Batch0201.cell1610.sound htau (by
                simp only [Batch0201.cell1610, Batch0201.tau1610, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1001321 (by positivity) using 1 <;> norm_num)
            · have hs1001323 : InSquare (27/320) (-113/320) (1/320) tau := by
                convert childUR hs100132 hx100132 hy100132 using 1 <;> norm_num
              exact Batch0201.cell1612.sound htau (by
                simp only [Batch0201.cell1612, Batch0201.tau1612, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1001323 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-29/80 : ℝ) with hy10013 | hy10013
        · have hs100131 : InSquare (3/32) (-59/160) (1/160) tau := by
            convert childLR hs10013 hx10013 hy10013 using 1 <;> norm_num
          rcases le_total tau.re (3/32 : ℝ) with hx100131 | hx100131
          · rcases le_total tau.im (-59/160 : ℝ) with hy100131 | hy100131
            · have hs1001310 : InSquare (29/320) (-119/320) (1/320) tau := by
                convert childLL hs100131 hx100131 hy100131 using 1 <;> norm_num
              exact Batch0200.cell1605.sound htau (by
                simp only [Batch0200.cell1605, Batch0200.tau1605, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1001310 (by positivity) using 1 <;> norm_num)
            · have hs1001312 : InSquare (29/320) (-117/320) (1/320) tau := by
                convert childUL hs100131 hx100131 hy100131 using 1 <;> norm_num
              exact Batch0200.cell1607.sound htau (by
                simp only [Batch0200.cell1607, Batch0200.tau1607, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1001312 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-59/160 : ℝ) with hy100131 | hy100131
            · have hs1001311 : InSquare (31/320) (-119/320) (1/320) tau := by
                convert childLR hs100131 hx100131 hy100131 using 1 <;> norm_num
              exact Batch0200.cell1606.sound htau (by
                simp only [Batch0200.cell1606, Batch0200.tau1606, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1001311 (by positivity) using 1 <;> norm_num)
            · have hs1001313 : InSquare (31/320) (-117/320) (1/320) tau := by
                convert childUR hs100131 hx100131 hy100131 using 1 <;> norm_num
              exact Batch0201.cell1608.sound htau (by
                simp only [Batch0201.cell1608, Batch0201.tau1608, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1001313 (by positivity) using 1 <;> norm_num)
        · have hs100133 : InSquare (3/32) (-57/160) (1/160) tau := by
            convert childUR hs10013 hx10013 hy10013 using 1 <;> norm_num
          rcases le_total tau.re (3/32 : ℝ) with hx100133 | hx100133
          · rcases le_total tau.im (-57/160 : ℝ) with hy100133 | hy100133
            · have hs1001330 : InSquare (29/320) (-23/64) (1/320) tau := by
                convert childLL hs100133 hx100133 hy100133 using 1 <;> norm_num
              exact Batch0201.cell1613.sound htau (by
                simp only [Batch0201.cell1613, Batch0201.tau1613, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1001330 (by positivity) using 1 <;> norm_num)
            · have hs1001332 : InSquare (29/320) (-113/320) (1/320) tau := by
                convert childUL hs100133 hx100133 hy100133 using 1 <;> norm_num
              exact Batch0201.cell1615.sound htau (by
                simp only [Batch0201.cell1615, Batch0201.tau1615, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1001332 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-57/160 : ℝ) with hy100133 | hy100133
            · have hs1001331 : InSquare (31/320) (-23/64) (1/320) tau := by
                convert childLR hs100133 hx100133 hy100133 using 1 <;> norm_num
              exact Batch0201.cell1614.sound htau (by
                simp only [Batch0201.cell1614, Batch0201.tau1614, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1001331 (by positivity) using 1 <;> norm_num)
            · have hs1001333 : InSquare (31/320) (-113/320) (1/320) tau := by
                convert childUR hs100133 hx100133 hy100133 using 1 <;> norm_num
              exact Batch0202.cell1616.sound htau (by
                simp only [Batch0202.cell1616, Batch0202.tau1616, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1001333 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1001
