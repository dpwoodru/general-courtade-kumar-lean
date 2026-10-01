import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0264
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0403
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0404
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0405
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0406
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0407
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0408
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0409

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2322

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

private theorem outside_23222 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-3/16) (31/80) (1/80) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (7/40 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+7/40)]
  have himSq : (3/8 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-3/8)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_23223 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-13/80) (31/80) (1/80) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (3/20 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+3/20)]
  have himSq : (3/8 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-3/8)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_232202 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-31/160) (59/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (3/16 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+3/16)]
  have himSq : (29/80 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-29/80)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_232203 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-29/160) (59/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (7/40 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+7/40)]
  have himSq : (29/80 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-29/80)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_2322000 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-63/320) (113/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (31/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+31/160)]
  have himSq : (7/20 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-7/20)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_2322002 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-63/320) (23/64) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (31/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+31/160)]
  have himSq : (57/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-57/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_2322003 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-61/320) (23/64) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (3/16 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+3/16)]
  have himSq : (57/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-57/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_2322122 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-11/64) (119/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (27/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+27/160)]
  have himSq : (59/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-59/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_2322123 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-53/320) (119/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (13/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+13/80)]
  have himSq : (59/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-59/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_2322132 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-51/320) (119/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (5/32 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+5/32)]
  have himSq : (59/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-59/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_23220012 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-123/640) (227/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (61/320 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+61/320)]
  have himSq : (113/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-113/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_23220120 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-119/640) (229/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (59/320 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+59/320)]
  have himSq : (57/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-57/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_23220122 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-119/640) (231/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (59/320 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+59/320)]
  have himSq : (23/64 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-23/64)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_23220123 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-117/640) (231/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (29/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+29/160)]
  have himSq : (23/64 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-23/64)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_23220132 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-23/128) (231/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (57/320 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+57/320)]
  have himSq : (23/64 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-23/64)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_23221200 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-111/640) (233/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (11/64 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+11/64)]
  have himSq : (29/80 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-29/80)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_23221202 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-111/640) (47/128) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (11/64 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+11/64)]
  have himSq : (117/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-117/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_23221203 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-109/640) (47/128) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (27/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+27/160)]
  have himSq : (117/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-117/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_23221212 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-107/640) (47/128) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (53/320 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+53/320)]
  have himSq : (117/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-117/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_23221213 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-21/128) (47/128) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (13/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+13/80)]
  have himSq : (117/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-117/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_23221332 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-99/640) (239/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (49/320 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+49/320)]
  have himSq : (119/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-119/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_23221333 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-97/640) (239/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (3/20 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+3/20)]
  have himSq : (119/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-119/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-7/40) (3/8) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (-7/40 : ℝ) with hx2322 | hx2322
  · rcases le_total tau.im (3/8 : ℝ) with hy2322 | hy2322
    · have hs23220 : InSquare (-3/16) (29/80) (1/80) tau := by
        convert childLL hs hx2322 hy2322 using 1 <;> norm_num
      rcases le_total tau.re (-3/16 : ℝ) with hx23220 | hx23220
      · rcases le_total tau.im (29/80 : ℝ) with hy23220 | hy23220
        · have hs232200 : InSquare (-31/160) (57/160) (1/160) tau := by
            convert childLL hs23220 hx23220 hy23220 using 1 <;> norm_num
          rcases le_total tau.re (-31/160 : ℝ) with hx232200 | hx232200
          · rcases le_total tau.im (57/160 : ℝ) with hy232200 | hy232200
            · have hs2322000 : InSquare (-63/320) (113/320) (1/320) tau := by
                convert childLL hs232200 hx232200 hy232200 using 1 <;> norm_num
              exact (outside_2322000 htau hs2322000).elim
            · have hs2322002 : InSquare (-63/320) (23/64) (1/320) tau := by
                convert childUL hs232200 hx232200 hy232200 using 1 <;> norm_num
              exact (outside_2322002 htau hs2322002).elim
          · rcases le_total tau.im (57/160 : ℝ) with hy232200 | hy232200
            · have hs2322001 : InSquare (-61/320) (113/320) (1/320) tau := by
                convert childLR hs232200 hx232200 hy232200 using 1 <;> norm_num
              rcases le_total tau.re (-61/320 : ℝ) with hx2322001 | hx2322001
              · rcases le_total tau.im (113/320 : ℝ) with hy2322001 | hy2322001
                · have hs23220010 : InSquare (-123/640) (45/128) (1/640) tau := by
                    convert childLL hs2322001 hx2322001 hy2322001 using 1 <;> norm_num
                  exact Batch0403.cell3227.sound htau (by
                    simp only [Batch0403.cell3227, Batch0403.tau3227, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23220010 (by positivity) using 1 <;> norm_num)
                · have hs23220012 : InSquare (-123/640) (227/640) (1/640) tau := by
                    convert childUL hs2322001 hx2322001 hy2322001 using 1 <;> norm_num
                  exact (outside_23220012 htau hs23220012).elim
              · rcases le_total tau.im (113/320 : ℝ) with hy2322001 | hy2322001
                · have hs23220011 : InSquare (-121/640) (45/128) (1/640) tau := by
                    convert childLR hs2322001 hx2322001 hy2322001 using 1 <;> norm_num
                  exact Batch0403.cell3228.sound htau (by
                    simp only [Batch0403.cell3228, Batch0403.tau3228, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23220011 (by positivity) using 1 <;> norm_num)
                · have hs23220013 : InSquare (-121/640) (227/640) (1/640) tau := by
                    convert childUR hs2322001 hx2322001 hy2322001 using 1 <;> norm_num
                  exact Batch0403.cell3229.sound htau (by
                    simp only [Batch0403.cell3229, Batch0403.tau3229, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23220013 (by positivity) using 1 <;> norm_num)
            · have hs2322003 : InSquare (-61/320) (23/64) (1/320) tau := by
                convert childUR hs232200 hx232200 hy232200 using 1 <;> norm_num
              exact (outside_2322003 htau hs2322003).elim
        · have hs232202 : InSquare (-31/160) (59/160) (1/160) tau := by
            convert childUL hs23220 hx23220 hy23220 using 1 <;> norm_num
          exact (outside_232202 htau hs232202).elim
      · rcases le_total tau.im (29/80 : ℝ) with hy23220 | hy23220
        · have hs232201 : InSquare (-29/160) (57/160) (1/160) tau := by
            convert childLR hs23220 hx23220 hy23220 using 1 <;> norm_num
          rcases le_total tau.re (-29/160 : ℝ) with hx232201 | hx232201
          · rcases le_total tau.im (57/160 : ℝ) with hy232201 | hy232201
            · have hs2322010 : InSquare (-59/320) (113/320) (1/320) tau := by
                convert childLL hs232201 hx232201 hy232201 using 1 <;> norm_num
              rcases le_total tau.re (-59/320 : ℝ) with hx2322010 | hx2322010
              · rcases le_total tau.im (113/320 : ℝ) with hy2322010 | hy2322010
                · have hs23220100 : InSquare (-119/640) (45/128) (1/640) tau := by
                    convert childLL hs2322010 hx2322010 hy2322010 using 1 <;> norm_num
                  exact Batch0403.cell3230.sound htau (by
                    simp only [Batch0403.cell3230, Batch0403.tau3230, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23220100 (by positivity) using 1 <;> norm_num)
                · have hs23220102 : InSquare (-119/640) (227/640) (1/640) tau := by
                    convert childUL hs2322010 hx2322010 hy2322010 using 1 <;> norm_num
                  exact Batch0404.cell3232.sound htau (by
                    simp only [Batch0404.cell3232, Batch0404.tau3232, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23220102 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (113/320 : ℝ) with hy2322010 | hy2322010
                · have hs23220101 : InSquare (-117/640) (45/128) (1/640) tau := by
                    convert childLR hs2322010 hx2322010 hy2322010 using 1 <;> norm_num
                  exact Batch0403.cell3231.sound htau (by
                    simp only [Batch0403.cell3231, Batch0403.tau3231, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23220101 (by positivity) using 1 <;> norm_num)
                · have hs23220103 : InSquare (-117/640) (227/640) (1/640) tau := by
                    convert childUR hs2322010 hx2322010 hy2322010 using 1 <;> norm_num
                  exact Batch0404.cell3233.sound htau (by
                    simp only [Batch0404.cell3233, Batch0404.tau3233, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23220103 (by positivity) using 1 <;> norm_num)
            · have hs2322012 : InSquare (-59/320) (23/64) (1/320) tau := by
                convert childUL hs232201 hx232201 hy232201 using 1 <;> norm_num
              rcases le_total tau.re (-59/320 : ℝ) with hx2322012 | hx2322012
              · rcases le_total tau.im (23/64 : ℝ) with hy2322012 | hy2322012
                · have hs23220120 : InSquare (-119/640) (229/640) (1/640) tau := by
                    convert childLL hs2322012 hx2322012 hy2322012 using 1 <;> norm_num
                  exact (outside_23220120 htau hs23220120).elim
                · have hs23220122 : InSquare (-119/640) (231/640) (1/640) tau := by
                    convert childUL hs2322012 hx2322012 hy2322012 using 1 <;> norm_num
                  exact (outside_23220122 htau hs23220122).elim
              · rcases le_total tau.im (23/64 : ℝ) with hy2322012 | hy2322012
                · have hs23220121 : InSquare (-117/640) (229/640) (1/640) tau := by
                    convert childLR hs2322012 hx2322012 hy2322012 using 1 <;> norm_num
                  exact Batch0404.cell3238.sound htau (by
                    simp only [Batch0404.cell3238, Batch0404.tau3238, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23220121 (by positivity) using 1 <;> norm_num)
                · have hs23220123 : InSquare (-117/640) (231/640) (1/640) tau := by
                    convert childUR hs2322012 hx2322012 hy2322012 using 1 <;> norm_num
                  exact (outside_23220123 htau hs23220123).elim
          · rcases le_total tau.im (57/160 : ℝ) with hy232201 | hy232201
            · have hs2322011 : InSquare (-57/320) (113/320) (1/320) tau := by
                convert childLR hs232201 hx232201 hy232201 using 1 <;> norm_num
              rcases le_total tau.re (-57/320 : ℝ) with hx2322011 | hx2322011
              · rcases le_total tau.im (113/320 : ℝ) with hy2322011 | hy2322011
                · have hs23220110 : InSquare (-23/128) (45/128) (1/640) tau := by
                    convert childLL hs2322011 hx2322011 hy2322011 using 1 <;> norm_num
                  exact Batch0404.cell3234.sound htau (by
                    simp only [Batch0404.cell3234, Batch0404.tau3234, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23220110 (by positivity) using 1 <;> norm_num)
                · have hs23220112 : InSquare (-23/128) (227/640) (1/640) tau := by
                    convert childUL hs2322011 hx2322011 hy2322011 using 1 <;> norm_num
                  exact Batch0404.cell3236.sound htau (by
                    simp only [Batch0404.cell3236, Batch0404.tau3236, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23220112 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (113/320 : ℝ) with hy2322011 | hy2322011
                · have hs23220111 : InSquare (-113/640) (45/128) (1/640) tau := by
                    convert childLR hs2322011 hx2322011 hy2322011 using 1 <;> norm_num
                  exact Batch0404.cell3235.sound htau (by
                    simp only [Batch0404.cell3235, Batch0404.tau3235, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23220111 (by positivity) using 1 <;> norm_num)
                · have hs23220113 : InSquare (-113/640) (227/640) (1/640) tau := by
                    convert childUR hs2322011 hx2322011 hy2322011 using 1 <;> norm_num
                  exact Batch0404.cell3237.sound htau (by
                    simp only [Batch0404.cell3237, Batch0404.tau3237, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23220113 (by positivity) using 1 <;> norm_num)
            · have hs2322013 : InSquare (-57/320) (23/64) (1/320) tau := by
                convert childUR hs232201 hx232201 hy232201 using 1 <;> norm_num
              rcases le_total tau.re (-57/320 : ℝ) with hx2322013 | hx2322013
              · rcases le_total tau.im (23/64 : ℝ) with hy2322013 | hy2322013
                · have hs23220130 : InSquare (-23/128) (229/640) (1/640) tau := by
                    convert childLL hs2322013 hx2322013 hy2322013 using 1 <;> norm_num
                  exact Batch0404.cell3239.sound htau (by
                    simp only [Batch0404.cell3239, Batch0404.tau3239, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23220130 (by positivity) using 1 <;> norm_num)
                · have hs23220132 : InSquare (-23/128) (231/640) (1/640) tau := by
                    convert childUL hs2322013 hx2322013 hy2322013 using 1 <;> norm_num
                  exact (outside_23220132 htau hs23220132).elim
              · rcases le_total tau.im (23/64 : ℝ) with hy2322013 | hy2322013
                · have hs23220131 : InSquare (-113/640) (229/640) (1/640) tau := by
                    convert childLR hs2322013 hx2322013 hy2322013 using 1 <;> norm_num
                  exact Batch0405.cell3240.sound htau (by
                    simp only [Batch0405.cell3240, Batch0405.tau3240, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23220131 (by positivity) using 1 <;> norm_num)
                · have hs23220133 : InSquare (-113/640) (231/640) (1/640) tau := by
                    convert childUR hs2322013 hx2322013 hy2322013 using 1 <;> norm_num
                  exact Batch0405.cell3241.sound htau (by
                    simp only [Batch0405.cell3241, Batch0405.tau3241, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23220133 (by positivity) using 1 <;> norm_num)
        · have hs232203 : InSquare (-29/160) (59/160) (1/160) tau := by
            convert childUR hs23220 hx23220 hy23220 using 1 <;> norm_num
          exact (outside_232203 htau hs232203).elim
    · have hs23222 : InSquare (-3/16) (31/80) (1/80) tau := by
        convert childUL hs hx2322 hy2322 using 1 <;> norm_num
      exact (outside_23222 htau hs23222).elim
  · rcases le_total tau.im (3/8 : ℝ) with hy2322 | hy2322
    · have hs23221 : InSquare (-13/80) (29/80) (1/80) tau := by
        convert childLR hs hx2322 hy2322 using 1 <;> norm_num
      rcases le_total tau.re (-13/80 : ℝ) with hx23221 | hx23221
      · rcases le_total tau.im (29/80 : ℝ) with hy23221 | hy23221
        · have hs232210 : InSquare (-27/160) (57/160) (1/160) tau := by
            convert childLL hs23221 hx23221 hy23221 using 1 <;> norm_num
          rcases le_total tau.re (-27/160 : ℝ) with hx232210 | hx232210
          · rcases le_total tau.im (57/160 : ℝ) with hy232210 | hy232210
            · have hs2322100 : InSquare (-11/64) (113/320) (1/320) tau := by
                convert childLL hs232210 hx232210 hy232210 using 1 <;> norm_num
              rcases le_total tau.re (-11/64 : ℝ) with hx2322100 | hx2322100
              · rcases le_total tau.im (113/320 : ℝ) with hy2322100 | hy2322100
                · have hs23221000 : InSquare (-111/640) (45/128) (1/640) tau := by
                    convert childLL hs2322100 hx2322100 hy2322100 using 1 <;> norm_num
                  exact Batch0405.cell3242.sound htau (by
                    simp only [Batch0405.cell3242, Batch0405.tau3242, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23221000 (by positivity) using 1 <;> norm_num)
                · have hs23221002 : InSquare (-111/640) (227/640) (1/640) tau := by
                    convert childUL hs2322100 hx2322100 hy2322100 using 1 <;> norm_num
                  exact Batch0405.cell3244.sound htau (by
                    simp only [Batch0405.cell3244, Batch0405.tau3244, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23221002 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (113/320 : ℝ) with hy2322100 | hy2322100
                · have hs23221001 : InSquare (-109/640) (45/128) (1/640) tau := by
                    convert childLR hs2322100 hx2322100 hy2322100 using 1 <;> norm_num
                  exact Batch0405.cell3243.sound htau (by
                    simp only [Batch0405.cell3243, Batch0405.tau3243, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23221001 (by positivity) using 1 <;> norm_num)
                · have hs23221003 : InSquare (-109/640) (227/640) (1/640) tau := by
                    convert childUR hs2322100 hx2322100 hy2322100 using 1 <;> norm_num
                  exact Batch0405.cell3245.sound htau (by
                    simp only [Batch0405.cell3245, Batch0405.tau3245, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23221003 (by positivity) using 1 <;> norm_num)
            · have hs2322102 : InSquare (-11/64) (23/64) (1/320) tau := by
                convert childUL hs232210 hx232210 hy232210 using 1 <;> norm_num
              rcases le_total tau.re (-11/64 : ℝ) with hx2322102 | hx2322102
              · rcases le_total tau.im (23/64 : ℝ) with hy2322102 | hy2322102
                · have hs23221020 : InSquare (-111/640) (229/640) (1/640) tau := by
                    convert childLL hs2322102 hx2322102 hy2322102 using 1 <;> norm_num
                  exact Batch0405.cell3246.sound htau (by
                    simp only [Batch0405.cell3246, Batch0405.tau3246, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23221020 (by positivity) using 1 <;> norm_num)
                · have hs23221022 : InSquare (-111/640) (231/640) (1/640) tau := by
                    convert childUL hs2322102 hx2322102 hy2322102 using 1 <;> norm_num
                  exact Batch0406.cell3248.sound htau (by
                    simp only [Batch0406.cell3248, Batch0406.tau3248, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23221022 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (23/64 : ℝ) with hy2322102 | hy2322102
                · have hs23221021 : InSquare (-109/640) (229/640) (1/640) tau := by
                    convert childLR hs2322102 hx2322102 hy2322102 using 1 <;> norm_num
                  exact Batch0405.cell3247.sound htau (by
                    simp only [Batch0405.cell3247, Batch0405.tau3247, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23221021 (by positivity) using 1 <;> norm_num)
                · have hs23221023 : InSquare (-109/640) (231/640) (1/640) tau := by
                    convert childUR hs2322102 hx2322102 hy2322102 using 1 <;> norm_num
                  exact Batch0406.cell3249.sound htau (by
                    simp only [Batch0406.cell3249, Batch0406.tau3249, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23221023 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (57/160 : ℝ) with hy232210 | hy232210
            · have hs2322101 : InSquare (-53/320) (113/320) (1/320) tau := by
                convert childLR hs232210 hx232210 hy232210 using 1 <;> norm_num
              exact Batch0264.cell2113.sound htau (by
                simp only [Batch0264.cell2113, Batch0264.tau2113, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2322101 (by positivity) using 1 <;> norm_num)
            · have hs2322103 : InSquare (-53/320) (23/64) (1/320) tau := by
                convert childUR hs232210 hx232210 hy232210 using 1 <;> norm_num
              rcases le_total tau.re (-53/320 : ℝ) with hx2322103 | hx2322103
              · rcases le_total tau.im (23/64 : ℝ) with hy2322103 | hy2322103
                · have hs23221030 : InSquare (-107/640) (229/640) (1/640) tau := by
                    convert childLL hs2322103 hx2322103 hy2322103 using 1 <;> norm_num
                  exact Batch0406.cell3250.sound htau (by
                    simp only [Batch0406.cell3250, Batch0406.tau3250, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23221030 (by positivity) using 1 <;> norm_num)
                · have hs23221032 : InSquare (-107/640) (231/640) (1/640) tau := by
                    convert childUL hs2322103 hx2322103 hy2322103 using 1 <;> norm_num
                  exact Batch0406.cell3252.sound htau (by
                    simp only [Batch0406.cell3252, Batch0406.tau3252, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23221032 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (23/64 : ℝ) with hy2322103 | hy2322103
                · have hs23221031 : InSquare (-21/128) (229/640) (1/640) tau := by
                    convert childLR hs2322103 hx2322103 hy2322103 using 1 <;> norm_num
                  exact Batch0406.cell3251.sound htau (by
                    simp only [Batch0406.cell3251, Batch0406.tau3251, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23221031 (by positivity) using 1 <;> norm_num)
                · have hs23221033 : InSquare (-21/128) (231/640) (1/640) tau := by
                    convert childUR hs2322103 hx2322103 hy2322103 using 1 <;> norm_num
                  exact Batch0406.cell3253.sound htau (by
                    simp only [Batch0406.cell3253, Batch0406.tau3253, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23221033 (by positivity) using 1 <;> norm_num)
        · have hs232212 : InSquare (-27/160) (59/160) (1/160) tau := by
            convert childUL hs23221 hx23221 hy23221 using 1 <;> norm_num
          rcases le_total tau.re (-27/160 : ℝ) with hx232212 | hx232212
          · rcases le_total tau.im (59/160 : ℝ) with hy232212 | hy232212
            · have hs2322120 : InSquare (-11/64) (117/320) (1/320) tau := by
                convert childLL hs232212 hx232212 hy232212 using 1 <;> norm_num
              rcases le_total tau.re (-11/64 : ℝ) with hx2322120 | hx2322120
              · rcases le_total tau.im (117/320 : ℝ) with hy2322120 | hy2322120
                · have hs23221200 : InSquare (-111/640) (233/640) (1/640) tau := by
                    convert childLL hs2322120 hx2322120 hy2322120 using 1 <;> norm_num
                  exact (outside_23221200 htau hs23221200).elim
                · have hs23221202 : InSquare (-111/640) (47/128) (1/640) tau := by
                    convert childUL hs2322120 hx2322120 hy2322120 using 1 <;> norm_num
                  exact (outside_23221202 htau hs23221202).elim
              · rcases le_total tau.im (117/320 : ℝ) with hy2322120 | hy2322120
                · have hs23221201 : InSquare (-109/640) (233/640) (1/640) tau := by
                    convert childLR hs2322120 hx2322120 hy2322120 using 1 <;> norm_num
                  exact Batch0407.cell3262.sound htau (by
                    simp only [Batch0407.cell3262, Batch0407.tau3262, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23221201 (by positivity) using 1 <;> norm_num)
                · have hs23221203 : InSquare (-109/640) (47/128) (1/640) tau := by
                    convert childUR hs2322120 hx2322120 hy2322120 using 1 <;> norm_num
                  exact (outside_23221203 htau hs23221203).elim
            · have hs2322122 : InSquare (-11/64) (119/320) (1/320) tau := by
                convert childUL hs232212 hx232212 hy232212 using 1 <;> norm_num
              exact (outside_2322122 htau hs2322122).elim
          · rcases le_total tau.im (59/160 : ℝ) with hy232212 | hy232212
            · have hs2322121 : InSquare (-53/320) (117/320) (1/320) tau := by
                convert childLR hs232212 hx232212 hy232212 using 1 <;> norm_num
              rcases le_total tau.re (-53/320 : ℝ) with hx2322121 | hx2322121
              · rcases le_total tau.im (117/320 : ℝ) with hy2322121 | hy2322121
                · have hs23221210 : InSquare (-107/640) (233/640) (1/640) tau := by
                    convert childLL hs2322121 hx2322121 hy2322121 using 1 <;> norm_num
                  exact Batch0407.cell3263.sound htau (by
                    simp only [Batch0407.cell3263, Batch0407.tau3263, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23221210 (by positivity) using 1 <;> norm_num)
                · have hs23221212 : InSquare (-107/640) (47/128) (1/640) tau := by
                    convert childUL hs2322121 hx2322121 hy2322121 using 1 <;> norm_num
                  exact (outside_23221212 htau hs23221212).elim
              · rcases le_total tau.im (117/320 : ℝ) with hy2322121 | hy2322121
                · have hs23221211 : InSquare (-21/128) (233/640) (1/640) tau := by
                    convert childLR hs2322121 hx2322121 hy2322121 using 1 <;> norm_num
                  exact Batch0408.cell3264.sound htau (by
                    simp only [Batch0408.cell3264, Batch0408.tau3264, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23221211 (by positivity) using 1 <;> norm_num)
                · have hs23221213 : InSquare (-21/128) (47/128) (1/640) tau := by
                    convert childUR hs2322121 hx2322121 hy2322121 using 1 <;> norm_num
                  exact (outside_23221213 htau hs23221213).elim
            · have hs2322123 : InSquare (-53/320) (119/320) (1/320) tau := by
                convert childUR hs232212 hx232212 hy232212 using 1 <;> norm_num
              exact (outside_2322123 htau hs2322123).elim
      · rcases le_total tau.im (29/80 : ℝ) with hy23221 | hy23221
        · have hs232211 : InSquare (-5/32) (57/160) (1/160) tau := by
            convert childLR hs23221 hx23221 hy23221 using 1 <;> norm_num
          rcases le_total tau.re (-5/32 : ℝ) with hx232211 | hx232211
          · rcases le_total tau.im (57/160 : ℝ) with hy232211 | hy232211
            · have hs2322110 : InSquare (-51/320) (113/320) (1/320) tau := by
                convert childLL hs232211 hx232211 hy232211 using 1 <;> norm_num
              exact Batch0264.cell2114.sound htau (by
                simp only [Batch0264.cell2114, Batch0264.tau2114, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2322110 (by positivity) using 1 <;> norm_num)
            · have hs2322112 : InSquare (-51/320) (23/64) (1/320) tau := by
                convert childUL hs232211 hx232211 hy232211 using 1 <;> norm_num
              rcases le_total tau.re (-51/320 : ℝ) with hx2322112 | hx2322112
              · rcases le_total tau.im (23/64 : ℝ) with hy2322112 | hy2322112
                · have hs23221120 : InSquare (-103/640) (229/640) (1/640) tau := by
                    convert childLL hs2322112 hx2322112 hy2322112 using 1 <;> norm_num
                  exact Batch0406.cell3254.sound htau (by
                    simp only [Batch0406.cell3254, Batch0406.tau3254, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23221120 (by positivity) using 1 <;> norm_num)
                · have hs23221122 : InSquare (-103/640) (231/640) (1/640) tau := by
                    convert childUL hs2322112 hx2322112 hy2322112 using 1 <;> norm_num
                  exact Batch0407.cell3256.sound htau (by
                    simp only [Batch0407.cell3256, Batch0407.tau3256, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23221122 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (23/64 : ℝ) with hy2322112 | hy2322112
                · have hs23221121 : InSquare (-101/640) (229/640) (1/640) tau := by
                    convert childLR hs2322112 hx2322112 hy2322112 using 1 <;> norm_num
                  exact Batch0406.cell3255.sound htau (by
                    simp only [Batch0406.cell3255, Batch0406.tau3255, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23221121 (by positivity) using 1 <;> norm_num)
                · have hs23221123 : InSquare (-101/640) (231/640) (1/640) tau := by
                    convert childUR hs2322112 hx2322112 hy2322112 using 1 <;> norm_num
                  exact Batch0407.cell3257.sound htau (by
                    simp only [Batch0407.cell3257, Batch0407.tau3257, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23221123 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (57/160 : ℝ) with hy232211 | hy232211
            · have hs2322111 : InSquare (-49/320) (113/320) (1/320) tau := by
                convert childLR hs232211 hx232211 hy232211 using 1 <;> norm_num
              exact Batch0264.cell2115.sound htau (by
                simp only [Batch0264.cell2115, Batch0264.tau2115, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2322111 (by positivity) using 1 <;> norm_num)
            · have hs2322113 : InSquare (-49/320) (23/64) (1/320) tau := by
                convert childUR hs232211 hx232211 hy232211 using 1 <;> norm_num
              rcases le_total tau.re (-49/320 : ℝ) with hx2322113 | hx2322113
              · rcases le_total tau.im (23/64 : ℝ) with hy2322113 | hy2322113
                · have hs23221130 : InSquare (-99/640) (229/640) (1/640) tau := by
                    convert childLL hs2322113 hx2322113 hy2322113 using 1 <;> norm_num
                  exact Batch0407.cell3258.sound htau (by
                    simp only [Batch0407.cell3258, Batch0407.tau3258, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23221130 (by positivity) using 1 <;> norm_num)
                · have hs23221132 : InSquare (-99/640) (231/640) (1/640) tau := by
                    convert childUL hs2322113 hx2322113 hy2322113 using 1 <;> norm_num
                  exact Batch0407.cell3260.sound htau (by
                    simp only [Batch0407.cell3260, Batch0407.tau3260, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23221132 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (23/64 : ℝ) with hy2322113 | hy2322113
                · have hs23221131 : InSquare (-97/640) (229/640) (1/640) tau := by
                    convert childLR hs2322113 hx2322113 hy2322113 using 1 <;> norm_num
                  exact Batch0407.cell3259.sound htau (by
                    simp only [Batch0407.cell3259, Batch0407.tau3259, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23221131 (by positivity) using 1 <;> norm_num)
                · have hs23221133 : InSquare (-97/640) (231/640) (1/640) tau := by
                    convert childUR hs2322113 hx2322113 hy2322113 using 1 <;> norm_num
                  exact Batch0407.cell3261.sound htau (by
                    simp only [Batch0407.cell3261, Batch0407.tau3261, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23221133 (by positivity) using 1 <;> norm_num)
        · have hs232213 : InSquare (-5/32) (59/160) (1/160) tau := by
            convert childUR hs23221 hx23221 hy23221 using 1 <;> norm_num
          rcases le_total tau.re (-5/32 : ℝ) with hx232213 | hx232213
          · rcases le_total tau.im (59/160 : ℝ) with hy232213 | hy232213
            · have hs2322130 : InSquare (-51/320) (117/320) (1/320) tau := by
                convert childLL hs232213 hx232213 hy232213 using 1 <;> norm_num
              rcases le_total tau.re (-51/320 : ℝ) with hx2322130 | hx2322130
              · rcases le_total tau.im (117/320 : ℝ) with hy2322130 | hy2322130
                · have hs23221300 : InSquare (-103/640) (233/640) (1/640) tau := by
                    convert childLL hs2322130 hx2322130 hy2322130 using 1 <;> norm_num
                  exact Batch0408.cell3265.sound htau (by
                    simp only [Batch0408.cell3265, Batch0408.tau3265, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23221300 (by positivity) using 1 <;> norm_num)
                · have hs23221302 : InSquare (-103/640) (47/128) (1/640) tau := by
                    convert childUL hs2322130 hx2322130 hy2322130 using 1 <;> norm_num
                  exact Batch0408.cell3267.sound htau (by
                    simp only [Batch0408.cell3267, Batch0408.tau3267, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23221302 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (117/320 : ℝ) with hy2322130 | hy2322130
                · have hs23221301 : InSquare (-101/640) (233/640) (1/640) tau := by
                    convert childLR hs2322130 hx2322130 hy2322130 using 1 <;> norm_num
                  exact Batch0408.cell3266.sound htau (by
                    simp only [Batch0408.cell3266, Batch0408.tau3266, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23221301 (by positivity) using 1 <;> norm_num)
                · have hs23221303 : InSquare (-101/640) (47/128) (1/640) tau := by
                    convert childUR hs2322130 hx2322130 hy2322130 using 1 <;> norm_num
                  exact Batch0408.cell3268.sound htau (by
                    simp only [Batch0408.cell3268, Batch0408.tau3268, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23221303 (by positivity) using 1 <;> norm_num)
            · have hs2322132 : InSquare (-51/320) (119/320) (1/320) tau := by
                convert childUL hs232213 hx232213 hy232213 using 1 <;> norm_num
              exact (outside_2322132 htau hs2322132).elim
          · rcases le_total tau.im (59/160 : ℝ) with hy232213 | hy232213
            · have hs2322131 : InSquare (-49/320) (117/320) (1/320) tau := by
                convert childLR hs232213 hx232213 hy232213 using 1 <;> norm_num
              rcases le_total tau.re (-49/320 : ℝ) with hx2322131 | hx2322131
              · rcases le_total tau.im (117/320 : ℝ) with hy2322131 | hy2322131
                · have hs23221310 : InSquare (-99/640) (233/640) (1/640) tau := by
                    convert childLL hs2322131 hx2322131 hy2322131 using 1 <;> norm_num
                  exact Batch0408.cell3269.sound htau (by
                    simp only [Batch0408.cell3269, Batch0408.tau3269, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23221310 (by positivity) using 1 <;> norm_num)
                · have hs23221312 : InSquare (-99/640) (47/128) (1/640) tau := by
                    convert childUL hs2322131 hx2322131 hy2322131 using 1 <;> norm_num
                  exact Batch0408.cell3271.sound htau (by
                    simp only [Batch0408.cell3271, Batch0408.tau3271, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23221312 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (117/320 : ℝ) with hy2322131 | hy2322131
                · have hs23221311 : InSquare (-97/640) (233/640) (1/640) tau := by
                    convert childLR hs2322131 hx2322131 hy2322131 using 1 <;> norm_num
                  exact Batch0408.cell3270.sound htau (by
                    simp only [Batch0408.cell3270, Batch0408.tau3270, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23221311 (by positivity) using 1 <;> norm_num)
                · have hs23221313 : InSquare (-97/640) (47/128) (1/640) tau := by
                    convert childUR hs2322131 hx2322131 hy2322131 using 1 <;> norm_num
                  exact Batch0409.cell3272.sound htau (by
                    simp only [Batch0409.cell3272, Batch0409.tau3272, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23221313 (by positivity) using 1 <;> norm_num)
            · have hs2322133 : InSquare (-49/320) (119/320) (1/320) tau := by
                convert childUR hs232213 hx232213 hy232213 using 1 <;> norm_num
              rcases le_total tau.re (-49/320 : ℝ) with hx2322133 | hx2322133
              · rcases le_total tau.im (119/320 : ℝ) with hy2322133 | hy2322133
                · have hs23221330 : InSquare (-99/640) (237/640) (1/640) tau := by
                    convert childLL hs2322133 hx2322133 hy2322133 using 1 <;> norm_num
                  exact Batch0409.cell3273.sound htau (by
                    simp only [Batch0409.cell3273, Batch0409.tau3273, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23221330 (by positivity) using 1 <;> norm_num)
                · have hs23221332 : InSquare (-99/640) (239/640) (1/640) tau := by
                    convert childUL hs2322133 hx2322133 hy2322133 using 1 <;> norm_num
                  exact (outside_23221332 htau hs23221332).elim
              · rcases le_total tau.im (119/320 : ℝ) with hy2322133 | hy2322133
                · have hs23221331 : InSquare (-97/640) (237/640) (1/640) tau := by
                    convert childLR hs2322133 hx2322133 hy2322133 using 1 <;> norm_num
                  exact Batch0409.cell3274.sound htau (by
                    simp only [Batch0409.cell3274, Batch0409.tau3274, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs23221331 (by positivity) using 1 <;> norm_num)
                · have hs23221333 : InSquare (-97/640) (239/640) (1/640) tau := by
                    convert childUR hs2322133 hx2322133 hy2322133 using 1 <;> norm_num
                  exact (outside_23221333 htau hs23221333).elim
    · have hs23223 : InSquare (-13/80) (31/80) (1/80) tau := by
        convert childUR hs hx2322 hy2322 using 1 <;> norm_num
      exact (outside_23223 htau hs23223).elim

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2322
