import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0150
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0151
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0152
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0153
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0154
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0155
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0320
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0321
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0322

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0013

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

private theorem outside_001300 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-39/160) (-11/32) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (19/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+19/80)]
  have himSq : (27/80 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+27/80)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_001301 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-37/160) (-11/32) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (9/40 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+9/40)]
  have himSq : (27/80 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+27/80)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_001302 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-39/160) (-53/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (19/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+19/80)]
  have himSq : (13/40 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+13/40)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_0013030 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-15/64) (-107/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (37/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+37/160)]
  have himSq : (53/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+53/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_0013031 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-73/320) (-107/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (9/40 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+9/40)]
  have himSq : (53/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+53/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_0013100 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-71/320) (-111/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (7/32 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+7/32)]
  have himSq : (11/32 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+11/32)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_0013101 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-69/320) (-111/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (17/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+17/80)]
  have himSq : (11/32 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+11/32)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_0013102 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-71/320) (-109/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (7/32 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+7/32)]
  have himSq : (27/80 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+27/80)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_0013110 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-67/320) (-111/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (33/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+33/160)]
  have himSq : (11/32 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+11/32)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_0013200 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-79/320) (-103/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (39/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+39/160)]
  have himSq : (51/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+51/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_00130320 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-151/640) (-211/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (15/64 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+15/64)]
  have himSq : (21/64 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+21/64)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_00130321 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-149/640) (-211/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (37/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+37/160)]
  have himSq : (21/64 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+21/64)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_00130322 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-151/640) (-209/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (15/64 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+15/64)]
  have himSq : (13/40 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+13/40)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_00131030 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-139/640) (-219/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (69/320 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+69/320)]
  have himSq : (109/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+109/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_00131031 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-137/640) (-219/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (17/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+17/80)]
  have himSq : (109/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+109/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_00131032 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-139/640) (-217/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (69/320 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+69/320)]
  have himSq : (27/80 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+27/80)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_00131110 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-131/640) (-223/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (13/64 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+13/64)]
  have himSq : (111/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+111/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_00131111 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-129/640) (-223/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (1/5 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+1/5)]
  have himSq : (111/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+111/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_00131200 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-143/640) (-43/128) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (71/320 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+71/320)]
  have himSq : (107/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+107/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-9/40) (-13/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (-9/40 : ℝ) with hx0013 | hx0013
  · rcases le_total tau.im (-13/40 : ℝ) with hy0013 | hy0013
    · have hs00130 : InSquare (-19/80) (-27/80) (1/80) tau := by
        convert childLL hs hx0013 hy0013 using 1 <;> norm_num
      rcases le_total tau.re (-19/80 : ℝ) with hx00130 | hx00130
      · rcases le_total tau.im (-27/80 : ℝ) with hy00130 | hy00130
        · have hs001300 : InSquare (-39/160) (-11/32) (1/160) tau := by
            convert childLL hs00130 hx00130 hy00130 using 1 <;> norm_num
          exact (outside_001300 htau hs001300).elim
        · have hs001302 : InSquare (-39/160) (-53/160) (1/160) tau := by
            convert childUL hs00130 hx00130 hy00130 using 1 <;> norm_num
          exact (outside_001302 htau hs001302).elim
      · rcases le_total tau.im (-27/80 : ℝ) with hy00130 | hy00130
        · have hs001301 : InSquare (-37/160) (-11/32) (1/160) tau := by
            convert childLR hs00130 hx00130 hy00130 using 1 <;> norm_num
          exact (outside_001301 htau hs001301).elim
        · have hs001303 : InSquare (-37/160) (-53/160) (1/160) tau := by
            convert childUR hs00130 hx00130 hy00130 using 1 <;> norm_num
          rcases le_total tau.re (-37/160 : ℝ) with hx001303 | hx001303
          · rcases le_total tau.im (-53/160 : ℝ) with hy001303 | hy001303
            · have hs0013030 : InSquare (-15/64) (-107/320) (1/320) tau := by
                convert childLL hs001303 hx001303 hy001303 using 1 <;> norm_num
              exact (outside_0013030 htau hs0013030).elim
            · have hs0013032 : InSquare (-15/64) (-21/64) (1/320) tau := by
                convert childUL hs001303 hx001303 hy001303 using 1 <;> norm_num
              rcases le_total tau.re (-15/64 : ℝ) with hx0013032 | hx0013032
              · rcases le_total tau.im (-21/64 : ℝ) with hy0013032 | hy0013032
                · have hs00130320 : InSquare (-151/640) (-211/640) (1/640) tau := by
                    convert childLL hs0013032 hx0013032 hy0013032 using 1 <;> norm_num
                  exact (outside_00130320 htau hs00130320).elim
                · have hs00130322 : InSquare (-151/640) (-209/640) (1/640) tau := by
                    convert childUL hs0013032 hx0013032 hy0013032 using 1 <;> norm_num
                  exact (outside_00130322 htau hs00130322).elim
              · rcases le_total tau.im (-21/64 : ℝ) with hy0013032 | hy0013032
                · have hs00130321 : InSquare (-149/640) (-211/640) (1/640) tau := by
                    convert childLR hs0013032 hx0013032 hy0013032 using 1 <;> norm_num
                  exact (outside_00130321 htau hs00130321).elim
                · have hs00130323 : InSquare (-149/640) (-209/640) (1/640) tau := by
                    convert childUR hs0013032 hx0013032 hy0013032 using 1 <;> norm_num
                  exact Batch0320.cell2564.sound htau (by
                    simp only [Batch0320.cell2564, Batch0320.tau2564, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs00130323 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-53/160 : ℝ) with hy001303 | hy001303
            · have hs0013031 : InSquare (-73/320) (-107/320) (1/320) tau := by
                convert childLR hs001303 hx001303 hy001303 using 1 <;> norm_num
              exact (outside_0013031 htau hs0013031).elim
            · have hs0013033 : InSquare (-73/320) (-21/64) (1/320) tau := by
                convert childUR hs001303 hx001303 hy001303 using 1 <;> norm_num
              exact Batch0150.cell1205.sound htau (by
                simp only [Batch0150.cell1205, Batch0150.tau1205, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0013033 (by positivity) using 1 <;> norm_num)
    · have hs00132 : InSquare (-19/80) (-5/16) (1/80) tau := by
        convert childUL hs hx0013 hy0013 using 1 <;> norm_num
      rcases le_total tau.re (-19/80 : ℝ) with hx00132 | hx00132
      · rcases le_total tau.im (-5/16 : ℝ) with hy00132 | hy00132
        · have hs001320 : InSquare (-39/160) (-51/160) (1/160) tau := by
            convert childLL hs00132 hx00132 hy00132 using 1 <;> norm_num
          rcases le_total tau.re (-39/160 : ℝ) with hx001320 | hx001320
          · rcases le_total tau.im (-51/160 : ℝ) with hy001320 | hy001320
            · have hs0013200 : InSquare (-79/320) (-103/320) (1/320) tau := by
                convert childLL hs001320 hx001320 hy001320 using 1 <;> norm_num
              exact (outside_0013200 htau hs0013200).elim
            · have hs0013202 : InSquare (-79/320) (-101/320) (1/320) tau := by
                convert childUL hs001320 hx001320 hy001320 using 1 <;> norm_num
              exact Batch0151.cell1214.sound htau (by
                simp only [Batch0151.cell1214, Batch0151.tau1214, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0013202 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-51/160 : ℝ) with hy001320 | hy001320
            · have hs0013201 : InSquare (-77/320) (-103/320) (1/320) tau := by
                convert childLR hs001320 hx001320 hy001320 using 1 <;> norm_num
              exact Batch0151.cell1213.sound htau (by
                simp only [Batch0151.cell1213, Batch0151.tau1213, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0013201 (by positivity) using 1 <;> norm_num)
            · have hs0013203 : InSquare (-77/320) (-101/320) (1/320) tau := by
                convert childUR hs001320 hx001320 hy001320 using 1 <;> norm_num
              exact Batch0151.cell1215.sound htau (by
                simp only [Batch0151.cell1215, Batch0151.tau1215, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0013203 (by positivity) using 1 <;> norm_num)
        · have hs001322 : InSquare (-39/160) (-49/160) (1/160) tau := by
            convert childUL hs00132 hx00132 hy00132 using 1 <;> norm_num
          rcases le_total tau.re (-39/160 : ℝ) with hx001322 | hx001322
          · rcases le_total tau.im (-49/160 : ℝ) with hy001322 | hy001322
            · have hs0013220 : InSquare (-79/320) (-99/320) (1/320) tau := by
                convert childLL hs001322 hx001322 hy001322 using 1 <;> norm_num
              exact Batch0152.cell1220.sound htau (by
                simp only [Batch0152.cell1220, Batch0152.tau1220, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0013220 (by positivity) using 1 <;> norm_num)
            · have hs0013222 : InSquare (-79/320) (-97/320) (1/320) tau := by
                convert childUL hs001322 hx001322 hy001322 using 1 <;> norm_num
              exact Batch0152.cell1222.sound htau (by
                simp only [Batch0152.cell1222, Batch0152.tau1222, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0013222 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-49/160 : ℝ) with hy001322 | hy001322
            · have hs0013221 : InSquare (-77/320) (-99/320) (1/320) tau := by
                convert childLR hs001322 hx001322 hy001322 using 1 <;> norm_num
              exact Batch0152.cell1221.sound htau (by
                simp only [Batch0152.cell1221, Batch0152.tau1221, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0013221 (by positivity) using 1 <;> norm_num)
            · have hs0013223 : InSquare (-77/320) (-97/320) (1/320) tau := by
                convert childUR hs001322 hx001322 hy001322 using 1 <;> norm_num
              exact Batch0152.cell1223.sound htau (by
                simp only [Batch0152.cell1223, Batch0152.tau1223, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0013223 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-5/16 : ℝ) with hy00132 | hy00132
        · have hs001321 : InSquare (-37/160) (-51/160) (1/160) tau := by
            convert childLR hs00132 hx00132 hy00132 using 1 <;> norm_num
          rcases le_total tau.re (-37/160 : ℝ) with hx001321 | hx001321
          · rcases le_total tau.im (-51/160 : ℝ) with hy001321 | hy001321
            · have hs0013210 : InSquare (-15/64) (-103/320) (1/320) tau := by
                convert childLL hs001321 hx001321 hy001321 using 1 <;> norm_num
              exact Batch0152.cell1216.sound htau (by
                simp only [Batch0152.cell1216, Batch0152.tau1216, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0013210 (by positivity) using 1 <;> norm_num)
            · have hs0013212 : InSquare (-15/64) (-101/320) (1/320) tau := by
                convert childUL hs001321 hx001321 hy001321 using 1 <;> norm_num
              exact Batch0152.cell1218.sound htau (by
                simp only [Batch0152.cell1218, Batch0152.tau1218, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0013212 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-51/160 : ℝ) with hy001321 | hy001321
            · have hs0013211 : InSquare (-73/320) (-103/320) (1/320) tau := by
                convert childLR hs001321 hx001321 hy001321 using 1 <;> norm_num
              exact Batch0152.cell1217.sound htau (by
                simp only [Batch0152.cell1217, Batch0152.tau1217, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0013211 (by positivity) using 1 <;> norm_num)
            · have hs0013213 : InSquare (-73/320) (-101/320) (1/320) tau := by
                convert childUR hs001321 hx001321 hy001321 using 1 <;> norm_num
              exact Batch0152.cell1219.sound htau (by
                simp only [Batch0152.cell1219, Batch0152.tau1219, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0013213 (by positivity) using 1 <;> norm_num)
        · have hs001323 : InSquare (-37/160) (-49/160) (1/160) tau := by
            convert childUR hs00132 hx00132 hy00132 using 1 <;> norm_num
          rcases le_total tau.re (-37/160 : ℝ) with hx001323 | hx001323
          · rcases le_total tau.im (-49/160 : ℝ) with hy001323 | hy001323
            · have hs0013230 : InSquare (-15/64) (-99/320) (1/320) tau := by
                convert childLL hs001323 hx001323 hy001323 using 1 <;> norm_num
              exact Batch0153.cell1224.sound htau (by
                simp only [Batch0153.cell1224, Batch0153.tau1224, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0013230 (by positivity) using 1 <;> norm_num)
            · have hs0013232 : InSquare (-15/64) (-97/320) (1/320) tau := by
                convert childUL hs001323 hx001323 hy001323 using 1 <;> norm_num
              exact Batch0153.cell1226.sound htau (by
                simp only [Batch0153.cell1226, Batch0153.tau1226, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0013232 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-49/160 : ℝ) with hy001323 | hy001323
            · have hs0013231 : InSquare (-73/320) (-99/320) (1/320) tau := by
                convert childLR hs001323 hx001323 hy001323 using 1 <;> norm_num
              exact Batch0153.cell1225.sound htau (by
                simp only [Batch0153.cell1225, Batch0153.tau1225, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0013231 (by positivity) using 1 <;> norm_num)
            · have hs0013233 : InSquare (-73/320) (-97/320) (1/320) tau := by
                convert childUR hs001323 hx001323 hy001323 using 1 <;> norm_num
              exact Batch0153.cell1227.sound htau (by
                simp only [Batch0153.cell1227, Batch0153.tau1227, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0013233 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (-13/40 : ℝ) with hy0013 | hy0013
    · have hs00131 : InSquare (-17/80) (-27/80) (1/80) tau := by
        convert childLR hs hx0013 hy0013 using 1 <;> norm_num
      rcases le_total tau.re (-17/80 : ℝ) with hx00131 | hx00131
      · rcases le_total tau.im (-27/80 : ℝ) with hy00131 | hy00131
        · have hs001310 : InSquare (-7/32) (-11/32) (1/160) tau := by
            convert childLL hs00131 hx00131 hy00131 using 1 <;> norm_num
          rcases le_total tau.re (-7/32 : ℝ) with hx001310 | hx001310
          · rcases le_total tau.im (-11/32 : ℝ) with hy001310 | hy001310
            · have hs0013100 : InSquare (-71/320) (-111/320) (1/320) tau := by
                convert childLL hs001310 hx001310 hy001310 using 1 <;> norm_num
              exact (outside_0013100 htau hs0013100).elim
            · have hs0013102 : InSquare (-71/320) (-109/320) (1/320) tau := by
                convert childUL hs001310 hx001310 hy001310 using 1 <;> norm_num
              exact (outside_0013102 htau hs0013102).elim
          · rcases le_total tau.im (-11/32 : ℝ) with hy001310 | hy001310
            · have hs0013101 : InSquare (-69/320) (-111/320) (1/320) tau := by
                convert childLR hs001310 hx001310 hy001310 using 1 <;> norm_num
              exact (outside_0013101 htau hs0013101).elim
            · have hs0013103 : InSquare (-69/320) (-109/320) (1/320) tau := by
                convert childUR hs001310 hx001310 hy001310 using 1 <;> norm_num
              rcases le_total tau.re (-69/320 : ℝ) with hx0013103 | hx0013103
              · rcases le_total tau.im (-109/320 : ℝ) with hy0013103 | hy0013103
                · have hs00131030 : InSquare (-139/640) (-219/640) (1/640) tau := by
                    convert childLL hs0013103 hx0013103 hy0013103 using 1 <;> norm_num
                  exact (outside_00131030 htau hs00131030).elim
                · have hs00131032 : InSquare (-139/640) (-217/640) (1/640) tau := by
                    convert childUL hs0013103 hx0013103 hy0013103 using 1 <;> norm_num
                  exact (outside_00131032 htau hs00131032).elim
              · rcases le_total tau.im (-109/320 : ℝ) with hy0013103 | hy0013103
                · have hs00131031 : InSquare (-137/640) (-219/640) (1/640) tau := by
                    convert childLR hs0013103 hx0013103 hy0013103 using 1 <;> norm_num
                  exact (outside_00131031 htau hs00131031).elim
                · have hs00131033 : InSquare (-137/640) (-217/640) (1/640) tau := by
                    convert childUR hs0013103 hx0013103 hy0013103 using 1 <;> norm_num
                  exact Batch0320.cell2565.sound htau (by
                    simp only [Batch0320.cell2565, Batch0320.tau2565, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs00131033 (by positivity) using 1 <;> norm_num)
        · have hs001312 : InSquare (-7/32) (-53/160) (1/160) tau := by
            convert childUL hs00131 hx00131 hy00131 using 1 <;> norm_num
          rcases le_total tau.re (-7/32 : ℝ) with hx001312 | hx001312
          · rcases le_total tau.im (-53/160 : ℝ) with hy001312 | hy001312
            · have hs0013120 : InSquare (-71/320) (-107/320) (1/320) tau := by
                convert childLL hs001312 hx001312 hy001312 using 1 <;> norm_num
              rcases le_total tau.re (-71/320 : ℝ) with hx0013120 | hx0013120
              · rcases le_total tau.im (-107/320 : ℝ) with hy0013120 | hy0013120
                · have hs00131200 : InSquare (-143/640) (-43/128) (1/640) tau := by
                    convert childLL hs0013120 hx0013120 hy0013120 using 1 <;> norm_num
                  exact (outside_00131200 htau hs00131200).elim
                · have hs00131202 : InSquare (-143/640) (-213/640) (1/640) tau := by
                    convert childUL hs0013120 hx0013120 hy0013120 using 1 <;> norm_num
                  exact Batch0322.cell2577.sound htau (by
                    simp only [Batch0322.cell2577, Batch0322.tau2577, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs00131202 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-107/320 : ℝ) with hy0013120 | hy0013120
                · have hs00131201 : InSquare (-141/640) (-43/128) (1/640) tau := by
                    convert childLR hs0013120 hx0013120 hy0013120 using 1 <;> norm_num
                  exact Batch0322.cell2576.sound htau (by
                    simp only [Batch0322.cell2576, Batch0322.tau2576, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs00131201 (by positivity) using 1 <;> norm_num)
                · have hs00131203 : InSquare (-141/640) (-213/640) (1/640) tau := by
                    convert childUR hs0013120 hx0013120 hy0013120 using 1 <;> norm_num
                  exact Batch0322.cell2578.sound htau (by
                    simp only [Batch0322.cell2578, Batch0322.tau2578, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs00131203 (by positivity) using 1 <;> norm_num)
            · have hs0013122 : InSquare (-71/320) (-21/64) (1/320) tau := by
                convert childUL hs001312 hx001312 hy001312 using 1 <;> norm_num
              exact Batch0150.cell1207.sound htau (by
                simp only [Batch0150.cell1207, Batch0150.tau1207, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0013122 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-53/160 : ℝ) with hy001312 | hy001312
            · have hs0013121 : InSquare (-69/320) (-107/320) (1/320) tau := by
                convert childLR hs001312 hx001312 hy001312 using 1 <;> norm_num
              exact Batch0150.cell1206.sound htau (by
                simp only [Batch0150.cell1206, Batch0150.tau1206, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0013121 (by positivity) using 1 <;> norm_num)
            · have hs0013123 : InSquare (-69/320) (-21/64) (1/320) tau := by
                convert childUR hs001312 hx001312 hy001312 using 1 <;> norm_num
              exact Batch0151.cell1208.sound htau (by
                simp only [Batch0151.cell1208, Batch0151.tau1208, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0013123 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-27/80 : ℝ) with hy00131 | hy00131
        · have hs001311 : InSquare (-33/160) (-11/32) (1/160) tau := by
            convert childLR hs00131 hx00131 hy00131 using 1 <;> norm_num
          rcases le_total tau.re (-33/160 : ℝ) with hx001311 | hx001311
          · rcases le_total tau.im (-11/32 : ℝ) with hy001311 | hy001311
            · have hs0013110 : InSquare (-67/320) (-111/320) (1/320) tau := by
                convert childLL hs001311 hx001311 hy001311 using 1 <;> norm_num
              exact (outside_0013110 htau hs0013110).elim
            · have hs0013112 : InSquare (-67/320) (-109/320) (1/320) tau := by
                convert childUL hs001311 hx001311 hy001311 using 1 <;> norm_num
              rcases le_total tau.re (-67/320 : ℝ) with hx0013112 | hx0013112
              · rcases le_total tau.im (-109/320 : ℝ) with hy0013112 | hy0013112
                · have hs00131120 : InSquare (-27/128) (-219/640) (1/640) tau := by
                    convert childLL hs0013112 hx0013112 hy0013112 using 1 <;> norm_num
                  exact Batch0321.cell2568.sound htau (by
                    simp only [Batch0321.cell2568, Batch0321.tau2568, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs00131120 (by positivity) using 1 <;> norm_num)
                · have hs00131122 : InSquare (-27/128) (-217/640) (1/640) tau := by
                    convert childUL hs0013112 hx0013112 hy0013112 using 1 <;> norm_num
                  exact Batch0321.cell2570.sound htau (by
                    simp only [Batch0321.cell2570, Batch0321.tau2570, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs00131122 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-109/320 : ℝ) with hy0013112 | hy0013112
                · have hs00131121 : InSquare (-133/640) (-219/640) (1/640) tau := by
                    convert childLR hs0013112 hx0013112 hy0013112 using 1 <;> norm_num
                  exact Batch0321.cell2569.sound htau (by
                    simp only [Batch0321.cell2569, Batch0321.tau2569, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs00131121 (by positivity) using 1 <;> norm_num)
                · have hs00131123 : InSquare (-133/640) (-217/640) (1/640) tau := by
                    convert childUR hs0013112 hx0013112 hy0013112 using 1 <;> norm_num
                  exact Batch0321.cell2571.sound htau (by
                    simp only [Batch0321.cell2571, Batch0321.tau2571, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs00131123 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-11/32 : ℝ) with hy001311 | hy001311
            · have hs0013111 : InSquare (-13/64) (-111/320) (1/320) tau := by
                convert childLR hs001311 hx001311 hy001311 using 1 <;> norm_num
              rcases le_total tau.re (-13/64 : ℝ) with hx0013111 | hx0013111
              · rcases le_total tau.im (-111/320 : ℝ) with hy0013111 | hy0013111
                · have hs00131110 : InSquare (-131/640) (-223/640) (1/640) tau := by
                    convert childLL hs0013111 hx0013111 hy0013111 using 1 <;> norm_num
                  exact (outside_00131110 htau hs00131110).elim
                · have hs00131112 : InSquare (-131/640) (-221/640) (1/640) tau := by
                    convert childUL hs0013111 hx0013111 hy0013111 using 1 <;> norm_num
                  exact Batch0320.cell2566.sound htau (by
                    simp only [Batch0320.cell2566, Batch0320.tau2566, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs00131112 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-111/320 : ℝ) with hy0013111 | hy0013111
                · have hs00131111 : InSquare (-129/640) (-223/640) (1/640) tau := by
                    convert childLR hs0013111 hx0013111 hy0013111 using 1 <;> norm_num
                  exact (outside_00131111 htau hs00131111).elim
                · have hs00131113 : InSquare (-129/640) (-221/640) (1/640) tau := by
                    convert childUR hs0013111 hx0013111 hy0013111 using 1 <;> norm_num
                  exact Batch0320.cell2567.sound htau (by
                    simp only [Batch0320.cell2567, Batch0320.tau2567, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs00131113 (by positivity) using 1 <;> norm_num)
            · have hs0013113 : InSquare (-13/64) (-109/320) (1/320) tau := by
                convert childUR hs001311 hx001311 hy001311 using 1 <;> norm_num
              rcases le_total tau.re (-13/64 : ℝ) with hx0013113 | hx0013113
              · rcases le_total tau.im (-109/320 : ℝ) with hy0013113 | hy0013113
                · have hs00131130 : InSquare (-131/640) (-219/640) (1/640) tau := by
                    convert childLL hs0013113 hx0013113 hy0013113 using 1 <;> norm_num
                  exact Batch0321.cell2572.sound htau (by
                    simp only [Batch0321.cell2572, Batch0321.tau2572, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs00131130 (by positivity) using 1 <;> norm_num)
                · have hs00131132 : InSquare (-131/640) (-217/640) (1/640) tau := by
                    convert childUL hs0013113 hx0013113 hy0013113 using 1 <;> norm_num
                  exact Batch0321.cell2574.sound htau (by
                    simp only [Batch0321.cell2574, Batch0321.tau2574, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs00131132 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-109/320 : ℝ) with hy0013113 | hy0013113
                · have hs00131131 : InSquare (-129/640) (-219/640) (1/640) tau := by
                    convert childLR hs0013113 hx0013113 hy0013113 using 1 <;> norm_num
                  exact Batch0321.cell2573.sound htau (by
                    simp only [Batch0321.cell2573, Batch0321.tau2573, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs00131131 (by positivity) using 1 <;> norm_num)
                · have hs00131133 : InSquare (-129/640) (-217/640) (1/640) tau := by
                    convert childUR hs0013113 hx0013113 hy0013113 using 1 <;> norm_num
                  exact Batch0321.cell2575.sound htau (by
                    simp only [Batch0321.cell2575, Batch0321.tau2575, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs00131133 (by positivity) using 1 <;> norm_num)
        · have hs001313 : InSquare (-33/160) (-53/160) (1/160) tau := by
            convert childUR hs00131 hx00131 hy00131 using 1 <;> norm_num
          rcases le_total tau.re (-33/160 : ℝ) with hx001313 | hx001313
          · rcases le_total tau.im (-53/160 : ℝ) with hy001313 | hy001313
            · have hs0013130 : InSquare (-67/320) (-107/320) (1/320) tau := by
                convert childLL hs001313 hx001313 hy001313 using 1 <;> norm_num
              exact Batch0151.cell1209.sound htau (by
                simp only [Batch0151.cell1209, Batch0151.tau1209, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0013130 (by positivity) using 1 <;> norm_num)
            · have hs0013132 : InSquare (-67/320) (-21/64) (1/320) tau := by
                convert childUL hs001313 hx001313 hy001313 using 1 <;> norm_num
              exact Batch0151.cell1211.sound htau (by
                simp only [Batch0151.cell1211, Batch0151.tau1211, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0013132 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-53/160 : ℝ) with hy001313 | hy001313
            · have hs0013131 : InSquare (-13/64) (-107/320) (1/320) tau := by
                convert childLR hs001313 hx001313 hy001313 using 1 <;> norm_num
              exact Batch0151.cell1210.sound htau (by
                simp only [Batch0151.cell1210, Batch0151.tau1210, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0013131 (by positivity) using 1 <;> norm_num)
            · have hs0013133 : InSquare (-13/64) (-21/64) (1/320) tau := by
                convert childUR hs001313 hx001313 hy001313 using 1 <;> norm_num
              exact Batch0151.cell1212.sound htau (by
                simp only [Batch0151.cell1212, Batch0151.tau1212, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0013133 (by positivity) using 1 <;> norm_num)
    · have hs00133 : InSquare (-17/80) (-5/16) (1/80) tau := by
        convert childUR hs hx0013 hy0013 using 1 <;> norm_num
      rcases le_total tau.re (-17/80 : ℝ) with hx00133 | hx00133
      · rcases le_total tau.im (-5/16 : ℝ) with hy00133 | hy00133
        · have hs001330 : InSquare (-7/32) (-51/160) (1/160) tau := by
            convert childLL hs00133 hx00133 hy00133 using 1 <;> norm_num
          rcases le_total tau.re (-7/32 : ℝ) with hx001330 | hx001330
          · rcases le_total tau.im (-51/160 : ℝ) with hy001330 | hy001330
            · have hs0013300 : InSquare (-71/320) (-103/320) (1/320) tau := by
                convert childLL hs001330 hx001330 hy001330 using 1 <;> norm_num
              exact Batch0153.cell1228.sound htau (by
                simp only [Batch0153.cell1228, Batch0153.tau1228, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0013300 (by positivity) using 1 <;> norm_num)
            · have hs0013302 : InSquare (-71/320) (-101/320) (1/320) tau := by
                convert childUL hs001330 hx001330 hy001330 using 1 <;> norm_num
              exact Batch0153.cell1230.sound htau (by
                simp only [Batch0153.cell1230, Batch0153.tau1230, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0013302 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-51/160 : ℝ) with hy001330 | hy001330
            · have hs0013301 : InSquare (-69/320) (-103/320) (1/320) tau := by
                convert childLR hs001330 hx001330 hy001330 using 1 <;> norm_num
              exact Batch0153.cell1229.sound htau (by
                simp only [Batch0153.cell1229, Batch0153.tau1229, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0013301 (by positivity) using 1 <;> norm_num)
            · have hs0013303 : InSquare (-69/320) (-101/320) (1/320) tau := by
                convert childUR hs001330 hx001330 hy001330 using 1 <;> norm_num
              exact Batch0153.cell1231.sound htau (by
                simp only [Batch0153.cell1231, Batch0153.tau1231, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0013303 (by positivity) using 1 <;> norm_num)
        · have hs001332 : InSquare (-7/32) (-49/160) (1/160) tau := by
            convert childUL hs00133 hx00133 hy00133 using 1 <;> norm_num
          rcases le_total tau.re (-7/32 : ℝ) with hx001332 | hx001332
          · rcases le_total tau.im (-49/160 : ℝ) with hy001332 | hy001332
            · have hs0013320 : InSquare (-71/320) (-99/320) (1/320) tau := by
                convert childLL hs001332 hx001332 hy001332 using 1 <;> norm_num
              exact Batch0154.cell1236.sound htau (by
                simp only [Batch0154.cell1236, Batch0154.tau1236, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0013320 (by positivity) using 1 <;> norm_num)
            · have hs0013322 : InSquare (-71/320) (-97/320) (1/320) tau := by
                convert childUL hs001332 hx001332 hy001332 using 1 <;> norm_num
              exact Batch0154.cell1238.sound htau (by
                simp only [Batch0154.cell1238, Batch0154.tau1238, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0013322 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-49/160 : ℝ) with hy001332 | hy001332
            · have hs0013321 : InSquare (-69/320) (-99/320) (1/320) tau := by
                convert childLR hs001332 hx001332 hy001332 using 1 <;> norm_num
              exact Batch0154.cell1237.sound htau (by
                simp only [Batch0154.cell1237, Batch0154.tau1237, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0013321 (by positivity) using 1 <;> norm_num)
            · have hs0013323 : InSquare (-69/320) (-97/320) (1/320) tau := by
                convert childUR hs001332 hx001332 hy001332 using 1 <;> norm_num
              exact Batch0154.cell1239.sound htau (by
                simp only [Batch0154.cell1239, Batch0154.tau1239, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0013323 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-5/16 : ℝ) with hy00133 | hy00133
        · have hs001331 : InSquare (-33/160) (-51/160) (1/160) tau := by
            convert childLR hs00133 hx00133 hy00133 using 1 <;> norm_num
          rcases le_total tau.re (-33/160 : ℝ) with hx001331 | hx001331
          · rcases le_total tau.im (-51/160 : ℝ) with hy001331 | hy001331
            · have hs0013310 : InSquare (-67/320) (-103/320) (1/320) tau := by
                convert childLL hs001331 hx001331 hy001331 using 1 <;> norm_num
              exact Batch0154.cell1232.sound htau (by
                simp only [Batch0154.cell1232, Batch0154.tau1232, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0013310 (by positivity) using 1 <;> norm_num)
            · have hs0013312 : InSquare (-67/320) (-101/320) (1/320) tau := by
                convert childUL hs001331 hx001331 hy001331 using 1 <;> norm_num
              exact Batch0154.cell1234.sound htau (by
                simp only [Batch0154.cell1234, Batch0154.tau1234, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0013312 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-51/160 : ℝ) with hy001331 | hy001331
            · have hs0013311 : InSquare (-13/64) (-103/320) (1/320) tau := by
                convert childLR hs001331 hx001331 hy001331 using 1 <;> norm_num
              exact Batch0154.cell1233.sound htau (by
                simp only [Batch0154.cell1233, Batch0154.tau1233, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0013311 (by positivity) using 1 <;> norm_num)
            · have hs0013313 : InSquare (-13/64) (-101/320) (1/320) tau := by
                convert childUR hs001331 hx001331 hy001331 using 1 <;> norm_num
              exact Batch0154.cell1235.sound htau (by
                simp only [Batch0154.cell1235, Batch0154.tau1235, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0013313 (by positivity) using 1 <;> norm_num)
        · have hs001333 : InSquare (-33/160) (-49/160) (1/160) tau := by
            convert childUR hs00133 hx00133 hy00133 using 1 <;> norm_num
          rcases le_total tau.re (-33/160 : ℝ) with hx001333 | hx001333
          · rcases le_total tau.im (-49/160 : ℝ) with hy001333 | hy001333
            · have hs0013330 : InSquare (-67/320) (-99/320) (1/320) tau := by
                convert childLL hs001333 hx001333 hy001333 using 1 <;> norm_num
              exact Batch0155.cell1240.sound htau (by
                simp only [Batch0155.cell1240, Batch0155.tau1240, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0013330 (by positivity) using 1 <;> norm_num)
            · have hs0013332 : InSquare (-67/320) (-97/320) (1/320) tau := by
                convert childUL hs001333 hx001333 hy001333 using 1 <;> norm_num
              exact Batch0155.cell1242.sound htau (by
                simp only [Batch0155.cell1242, Batch0155.tau1242, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0013332 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-49/160 : ℝ) with hy001333 | hy001333
            · have hs0013331 : InSquare (-13/64) (-99/320) (1/320) tau := by
                convert childLR hs001333 hx001333 hy001333 using 1 <;> norm_num
              exact Batch0155.cell1241.sound htau (by
                simp only [Batch0155.cell1241, Batch0155.tau1241, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0013331 (by positivity) using 1 <;> norm_num)
            · have hs0013333 : InSquare (-13/64) (-97/320) (1/320) tau := by
                convert childUR hs001333 hx001333 hy001333 using 1 <;> norm_num
              exact Batch0155.cell1243.sound htau (by
                simp only [Batch0155.cell1243, Batch0155.tau1243, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0013333 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0013
