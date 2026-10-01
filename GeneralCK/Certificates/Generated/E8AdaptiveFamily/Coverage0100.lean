import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0168
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0322
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0323
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0324
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0325
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0326
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0327
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0328

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0100

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

private theorem outside_01000 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-3/16) (-31/80) (1/80) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (7/40 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+7/40)]
  have himSq : (3/8 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+3/8)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_01001 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-13/80) (-31/80) (1/80) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (3/20 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+3/20)]
  have himSq : (3/8 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+3/8)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_010020 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-31/160) (-59/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (3/16 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+3/16)]
  have himSq : (29/80 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+29/80)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_010021 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-29/160) (-59/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (7/40 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+7/40)]
  have himSq : (29/80 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+29/80)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_0100220 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-63/320) (-23/64) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (31/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+31/160)]
  have himSq : (57/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+57/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_0100221 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-61/320) (-23/64) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (3/16 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+3/16)]
  have himSq : (57/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+57/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_0100222 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-63/320) (-113/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (31/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+31/160)]
  have himSq : (7/20 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+7/20)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_0100300 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-11/64) (-119/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (27/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+27/160)]
  have himSq : (59/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+59/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_0100301 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-53/320) (-119/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (13/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+13/80)]
  have himSq : (59/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+59/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_0100310 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-51/320) (-119/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (5/32 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+5/32)]
  have himSq : (59/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+59/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_01002230 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-123/640) (-227/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (61/320 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+61/320)]
  have himSq : (113/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+113/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_01002300 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-119/640) (-231/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (59/320 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+59/320)]
  have himSq : (23/64 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+23/64)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_01002301 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-117/640) (-231/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (29/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+29/160)]
  have himSq : (23/64 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+23/64)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_01002302 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-119/640) (-229/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (59/320 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+59/320)]
  have himSq : (57/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+57/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_01002310 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-23/128) (-231/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (57/320 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+57/320)]
  have himSq : (23/64 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+23/64)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_01003020 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-111/640) (-47/128) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (11/64 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+11/64)]
  have himSq : (117/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+117/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_01003021 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-109/640) (-47/128) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (27/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+27/160)]
  have himSq : (117/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+117/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_01003022 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-111/640) (-233/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (11/64 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+11/64)]
  have himSq : (29/80 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+29/80)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_01003030 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-107/640) (-47/128) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (53/320 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+53/320)]
  have himSq : (117/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+117/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_01003031 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-21/128) (-47/128) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (13/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+13/80)]
  have himSq : (117/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+117/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_01003110 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-99/640) (-239/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (49/320 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+49/320)]
  have himSq : (119/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+119/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_01003111 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-97/640) (-239/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (3/20 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+3/20)]
  have himSq : (119/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+119/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-7/40) (-3/8) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (-7/40 : ℝ) with hx0100 | hx0100
  · rcases le_total tau.im (-3/8 : ℝ) with hy0100 | hy0100
    · have hs01000 : InSquare (-3/16) (-31/80) (1/80) tau := by
        convert childLL hs hx0100 hy0100 using 1 <;> norm_num
      exact (outside_01000 htau hs01000).elim
    · have hs01002 : InSquare (-3/16) (-29/80) (1/80) tau := by
        convert childUL hs hx0100 hy0100 using 1 <;> norm_num
      rcases le_total tau.re (-3/16 : ℝ) with hx01002 | hx01002
      · rcases le_total tau.im (-29/80 : ℝ) with hy01002 | hy01002
        · have hs010020 : InSquare (-31/160) (-59/160) (1/160) tau := by
            convert childLL hs01002 hx01002 hy01002 using 1 <;> norm_num
          exact (outside_010020 htau hs010020).elim
        · have hs010022 : InSquare (-31/160) (-57/160) (1/160) tau := by
            convert childUL hs01002 hx01002 hy01002 using 1 <;> norm_num
          rcases le_total tau.re (-31/160 : ℝ) with hx010022 | hx010022
          · rcases le_total tau.im (-57/160 : ℝ) with hy010022 | hy010022
            · have hs0100220 : InSquare (-63/320) (-23/64) (1/320) tau := by
                convert childLL hs010022 hx010022 hy010022 using 1 <;> norm_num
              exact (outside_0100220 htau hs0100220).elim
            · have hs0100222 : InSquare (-63/320) (-113/320) (1/320) tau := by
                convert childUL hs010022 hx010022 hy010022 using 1 <;> norm_num
              exact (outside_0100222 htau hs0100222).elim
          · rcases le_total tau.im (-57/160 : ℝ) with hy010022 | hy010022
            · have hs0100221 : InSquare (-61/320) (-23/64) (1/320) tau := by
                convert childLR hs010022 hx010022 hy010022 using 1 <;> norm_num
              exact (outside_0100221 htau hs0100221).elim
            · have hs0100223 : InSquare (-61/320) (-113/320) (1/320) tau := by
                convert childUR hs010022 hx010022 hy010022 using 1 <;> norm_num
              rcases le_total tau.re (-61/320 : ℝ) with hx0100223 | hx0100223
              · rcases le_total tau.im (-113/320 : ℝ) with hy0100223 | hy0100223
                · have hs01002230 : InSquare (-123/640) (-227/640) (1/640) tau := by
                    convert childLL hs0100223 hx0100223 hy0100223 using 1 <;> norm_num
                  exact (outside_01002230 htau hs01002230).elim
                · have hs01002232 : InSquare (-123/640) (-45/128) (1/640) tau := by
                    convert childUL hs0100223 hx0100223 hy0100223 using 1 <;> norm_num
                  exact Batch0322.cell2580.sound htau (by
                    simp only [Batch0322.cell2580, Batch0322.tau2580, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01002232 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-113/320 : ℝ) with hy0100223 | hy0100223
                · have hs01002231 : InSquare (-121/640) (-227/640) (1/640) tau := by
                    convert childLR hs0100223 hx0100223 hy0100223 using 1 <;> norm_num
                  exact Batch0322.cell2579.sound htau (by
                    simp only [Batch0322.cell2579, Batch0322.tau2579, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01002231 (by positivity) using 1 <;> norm_num)
                · have hs01002233 : InSquare (-121/640) (-45/128) (1/640) tau := by
                    convert childUR hs0100223 hx0100223 hy0100223 using 1 <;> norm_num
                  exact Batch0322.cell2581.sound htau (by
                    simp only [Batch0322.cell2581, Batch0322.tau2581, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01002233 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-29/80 : ℝ) with hy01002 | hy01002
        · have hs010021 : InSquare (-29/160) (-59/160) (1/160) tau := by
            convert childLR hs01002 hx01002 hy01002 using 1 <;> norm_num
          exact (outside_010021 htau hs010021).elim
        · have hs010023 : InSquare (-29/160) (-57/160) (1/160) tau := by
            convert childUR hs01002 hx01002 hy01002 using 1 <;> norm_num
          rcases le_total tau.re (-29/160 : ℝ) with hx010023 | hx010023
          · rcases le_total tau.im (-57/160 : ℝ) with hy010023 | hy010023
            · have hs0100230 : InSquare (-59/320) (-23/64) (1/320) tau := by
                convert childLL hs010023 hx010023 hy010023 using 1 <;> norm_num
              rcases le_total tau.re (-59/320 : ℝ) with hx0100230 | hx0100230
              · rcases le_total tau.im (-23/64 : ℝ) with hy0100230 | hy0100230
                · have hs01002300 : InSquare (-119/640) (-231/640) (1/640) tau := by
                    convert childLL hs0100230 hx0100230 hy0100230 using 1 <;> norm_num
                  exact (outside_01002300 htau hs01002300).elim
                · have hs01002302 : InSquare (-119/640) (-229/640) (1/640) tau := by
                    convert childUL hs0100230 hx0100230 hy0100230 using 1 <;> norm_num
                  exact (outside_01002302 htau hs01002302).elim
              · rcases le_total tau.im (-23/64 : ℝ) with hy0100230 | hy0100230
                · have hs01002301 : InSquare (-117/640) (-231/640) (1/640) tau := by
                    convert childLR hs0100230 hx0100230 hy0100230 using 1 <;> norm_num
                  exact (outside_01002301 htau hs01002301).elim
                · have hs01002303 : InSquare (-117/640) (-229/640) (1/640) tau := by
                    convert childUR hs0100230 hx0100230 hy0100230 using 1 <;> norm_num
                  exact Batch0322.cell2582.sound htau (by
                    simp only [Batch0322.cell2582, Batch0322.tau2582, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01002303 (by positivity) using 1 <;> norm_num)
            · have hs0100232 : InSquare (-59/320) (-113/320) (1/320) tau := by
                convert childUL hs010023 hx010023 hy010023 using 1 <;> norm_num
              rcases le_total tau.re (-59/320 : ℝ) with hx0100232 | hx0100232
              · rcases le_total tau.im (-113/320 : ℝ) with hy0100232 | hy0100232
                · have hs01002320 : InSquare (-119/640) (-227/640) (1/640) tau := by
                    convert childLL hs0100232 hx0100232 hy0100232 using 1 <;> norm_num
                  exact Batch0323.cell2586.sound htau (by
                    simp only [Batch0323.cell2586, Batch0323.tau2586, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01002320 (by positivity) using 1 <;> norm_num)
                · have hs01002322 : InSquare (-119/640) (-45/128) (1/640) tau := by
                    convert childUL hs0100232 hx0100232 hy0100232 using 1 <;> norm_num
                  exact Batch0323.cell2588.sound htau (by
                    simp only [Batch0323.cell2588, Batch0323.tau2588, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01002322 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-113/320 : ℝ) with hy0100232 | hy0100232
                · have hs01002321 : InSquare (-117/640) (-227/640) (1/640) tau := by
                    convert childLR hs0100232 hx0100232 hy0100232 using 1 <;> norm_num
                  exact Batch0323.cell2587.sound htau (by
                    simp only [Batch0323.cell2587, Batch0323.tau2587, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01002321 (by positivity) using 1 <;> norm_num)
                · have hs01002323 : InSquare (-117/640) (-45/128) (1/640) tau := by
                    convert childUR hs0100232 hx0100232 hy0100232 using 1 <;> norm_num
                  exact Batch0323.cell2589.sound htau (by
                    simp only [Batch0323.cell2589, Batch0323.tau2589, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01002323 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-57/160 : ℝ) with hy010023 | hy010023
            · have hs0100231 : InSquare (-57/320) (-23/64) (1/320) tau := by
                convert childLR hs010023 hx010023 hy010023 using 1 <;> norm_num
              rcases le_total tau.re (-57/320 : ℝ) with hx0100231 | hx0100231
              · rcases le_total tau.im (-23/64 : ℝ) with hy0100231 | hy0100231
                · have hs01002310 : InSquare (-23/128) (-231/640) (1/640) tau := by
                    convert childLL hs0100231 hx0100231 hy0100231 using 1 <;> norm_num
                  exact (outside_01002310 htau hs01002310).elim
                · have hs01002312 : InSquare (-23/128) (-229/640) (1/640) tau := by
                    convert childUL hs0100231 hx0100231 hy0100231 using 1 <;> norm_num
                  exact Batch0323.cell2584.sound htau (by
                    simp only [Batch0323.cell2584, Batch0323.tau2584, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01002312 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-23/64 : ℝ) with hy0100231 | hy0100231
                · have hs01002311 : InSquare (-113/640) (-231/640) (1/640) tau := by
                    convert childLR hs0100231 hx0100231 hy0100231 using 1 <;> norm_num
                  exact Batch0322.cell2583.sound htau (by
                    simp only [Batch0322.cell2583, Batch0322.tau2583, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01002311 (by positivity) using 1 <;> norm_num)
                · have hs01002313 : InSquare (-113/640) (-229/640) (1/640) tau := by
                    convert childUR hs0100231 hx0100231 hy0100231 using 1 <;> norm_num
                  exact Batch0323.cell2585.sound htau (by
                    simp only [Batch0323.cell2585, Batch0323.tau2585, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01002313 (by positivity) using 1 <;> norm_num)
            · have hs0100233 : InSquare (-57/320) (-113/320) (1/320) tau := by
                convert childUR hs010023 hx010023 hy010023 using 1 <;> norm_num
              rcases le_total tau.re (-57/320 : ℝ) with hx0100233 | hx0100233
              · rcases le_total tau.im (-113/320 : ℝ) with hy0100233 | hy0100233
                · have hs01002330 : InSquare (-23/128) (-227/640) (1/640) tau := by
                    convert childLL hs0100233 hx0100233 hy0100233 using 1 <;> norm_num
                  exact Batch0323.cell2590.sound htau (by
                    simp only [Batch0323.cell2590, Batch0323.tau2590, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01002330 (by positivity) using 1 <;> norm_num)
                · have hs01002332 : InSquare (-23/128) (-45/128) (1/640) tau := by
                    convert childUL hs0100233 hx0100233 hy0100233 using 1 <;> norm_num
                  exact Batch0324.cell2592.sound htau (by
                    simp only [Batch0324.cell2592, Batch0324.tau2592, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01002332 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-113/320 : ℝ) with hy0100233 | hy0100233
                · have hs01002331 : InSquare (-113/640) (-227/640) (1/640) tau := by
                    convert childLR hs0100233 hx0100233 hy0100233 using 1 <;> norm_num
                  exact Batch0323.cell2591.sound htau (by
                    simp only [Batch0323.cell2591, Batch0323.tau2591, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01002331 (by positivity) using 1 <;> norm_num)
                · have hs01002333 : InSquare (-113/640) (-45/128) (1/640) tau := by
                    convert childUR hs0100233 hx0100233 hy0100233 using 1 <;> norm_num
                  exact Batch0324.cell2593.sound htau (by
                    simp only [Batch0324.cell2593, Batch0324.tau2593, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01002333 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (-3/8 : ℝ) with hy0100 | hy0100
    · have hs01001 : InSquare (-13/80) (-31/80) (1/80) tau := by
        convert childLR hs hx0100 hy0100 using 1 <;> norm_num
      exact (outside_01001 htau hs01001).elim
    · have hs01003 : InSquare (-13/80) (-29/80) (1/80) tau := by
        convert childUR hs hx0100 hy0100 using 1 <;> norm_num
      rcases le_total tau.re (-13/80 : ℝ) with hx01003 | hx01003
      · rcases le_total tau.im (-29/80 : ℝ) with hy01003 | hy01003
        · have hs010030 : InSquare (-27/160) (-59/160) (1/160) tau := by
            convert childLL hs01003 hx01003 hy01003 using 1 <;> norm_num
          rcases le_total tau.re (-27/160 : ℝ) with hx010030 | hx010030
          · rcases le_total tau.im (-59/160 : ℝ) with hy010030 | hy010030
            · have hs0100300 : InSquare (-11/64) (-119/320) (1/320) tau := by
                convert childLL hs010030 hx010030 hy010030 using 1 <;> norm_num
              exact (outside_0100300 htau hs0100300).elim
            · have hs0100302 : InSquare (-11/64) (-117/320) (1/320) tau := by
                convert childUL hs010030 hx010030 hy010030 using 1 <;> norm_num
              rcases le_total tau.re (-11/64 : ℝ) with hx0100302 | hx0100302
              · rcases le_total tau.im (-117/320 : ℝ) with hy0100302 | hy0100302
                · have hs01003020 : InSquare (-111/640) (-47/128) (1/640) tau := by
                    convert childLL hs0100302 hx0100302 hy0100302 using 1 <;> norm_num
                  exact (outside_01003020 htau hs01003020).elim
                · have hs01003022 : InSquare (-111/640) (-233/640) (1/640) tau := by
                    convert childUL hs0100302 hx0100302 hy0100302 using 1 <;> norm_num
                  exact (outside_01003022 htau hs01003022).elim
              · rcases le_total tau.im (-117/320 : ℝ) with hy0100302 | hy0100302
                · have hs01003021 : InSquare (-109/640) (-47/128) (1/640) tau := by
                    convert childLR hs0100302 hx0100302 hy0100302 using 1 <;> norm_num
                  exact (outside_01003021 htau hs01003021).elim
                · have hs01003023 : InSquare (-109/640) (-233/640) (1/640) tau := by
                    convert childUR hs0100302 hx0100302 hy0100302 using 1 <;> norm_num
                  exact Batch0324.cell2594.sound htau (by
                    simp only [Batch0324.cell2594, Batch0324.tau2594, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01003023 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-59/160 : ℝ) with hy010030 | hy010030
            · have hs0100301 : InSquare (-53/320) (-119/320) (1/320) tau := by
                convert childLR hs010030 hx010030 hy010030 using 1 <;> norm_num
              exact (outside_0100301 htau hs0100301).elim
            · have hs0100303 : InSquare (-53/320) (-117/320) (1/320) tau := by
                convert childUR hs010030 hx010030 hy010030 using 1 <;> norm_num
              rcases le_total tau.re (-53/320 : ℝ) with hx0100303 | hx0100303
              · rcases le_total tau.im (-117/320 : ℝ) with hy0100303 | hy0100303
                · have hs01003030 : InSquare (-107/640) (-47/128) (1/640) tau := by
                    convert childLL hs0100303 hx0100303 hy0100303 using 1 <;> norm_num
                  exact (outside_01003030 htau hs01003030).elim
                · have hs01003032 : InSquare (-107/640) (-233/640) (1/640) tau := by
                    convert childUL hs0100303 hx0100303 hy0100303 using 1 <;> norm_num
                  exact Batch0324.cell2595.sound htau (by
                    simp only [Batch0324.cell2595, Batch0324.tau2595, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01003032 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-117/320 : ℝ) with hy0100303 | hy0100303
                · have hs01003031 : InSquare (-21/128) (-47/128) (1/640) tau := by
                    convert childLR hs0100303 hx0100303 hy0100303 using 1 <;> norm_num
                  exact (outside_01003031 htau hs01003031).elim
                · have hs01003033 : InSquare (-21/128) (-233/640) (1/640) tau := by
                    convert childUR hs0100303 hx0100303 hy0100303 using 1 <;> norm_num
                  exact Batch0324.cell2596.sound htau (by
                    simp only [Batch0324.cell2596, Batch0324.tau2596, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01003033 (by positivity) using 1 <;> norm_num)
        · have hs010032 : InSquare (-27/160) (-57/160) (1/160) tau := by
            convert childUL hs01003 hx01003 hy01003 using 1 <;> norm_num
          rcases le_total tau.re (-27/160 : ℝ) with hx010032 | hx010032
          · rcases le_total tau.im (-57/160 : ℝ) with hy010032 | hy010032
            · have hs0100320 : InSquare (-11/64) (-23/64) (1/320) tau := by
                convert childLL hs010032 hx010032 hy010032 using 1 <;> norm_num
              rcases le_total tau.re (-11/64 : ℝ) with hx0100320 | hx0100320
              · rcases le_total tau.im (-23/64 : ℝ) with hy0100320 | hy0100320
                · have hs01003200 : InSquare (-111/640) (-231/640) (1/640) tau := by
                    convert childLL hs0100320 hx0100320 hy0100320 using 1 <;> norm_num
                  exact Batch0325.cell2607.sound htau (by
                    simp only [Batch0325.cell2607, Batch0325.tau2607, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01003200 (by positivity) using 1 <;> norm_num)
                · have hs01003202 : InSquare (-111/640) (-229/640) (1/640) tau := by
                    convert childUL hs0100320 hx0100320 hy0100320 using 1 <;> norm_num
                  exact Batch0326.cell2609.sound htau (by
                    simp only [Batch0326.cell2609, Batch0326.tau2609, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01003202 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-23/64 : ℝ) with hy0100320 | hy0100320
                · have hs01003201 : InSquare (-109/640) (-231/640) (1/640) tau := by
                    convert childLR hs0100320 hx0100320 hy0100320 using 1 <;> norm_num
                  exact Batch0326.cell2608.sound htau (by
                    simp only [Batch0326.cell2608, Batch0326.tau2608, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01003201 (by positivity) using 1 <;> norm_num)
                · have hs01003203 : InSquare (-109/640) (-229/640) (1/640) tau := by
                    convert childUR hs0100320 hx0100320 hy0100320 using 1 <;> norm_num
                  exact Batch0326.cell2610.sound htau (by
                    simp only [Batch0326.cell2610, Batch0326.tau2610, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01003203 (by positivity) using 1 <;> norm_num)
            · have hs0100322 : InSquare (-11/64) (-113/320) (1/320) tau := by
                convert childUL hs010032 hx010032 hy010032 using 1 <;> norm_num
              rcases le_total tau.re (-11/64 : ℝ) with hx0100322 | hx0100322
              · rcases le_total tau.im (-113/320 : ℝ) with hy0100322 | hy0100322
                · have hs01003220 : InSquare (-111/640) (-227/640) (1/640) tau := by
                    convert childLL hs0100322 hx0100322 hy0100322 using 1 <;> norm_num
                  exact Batch0326.cell2615.sound htau (by
                    simp only [Batch0326.cell2615, Batch0326.tau2615, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01003220 (by positivity) using 1 <;> norm_num)
                · have hs01003222 : InSquare (-111/640) (-45/128) (1/640) tau := by
                    convert childUL hs0100322 hx0100322 hy0100322 using 1 <;> norm_num
                  exact Batch0327.cell2617.sound htau (by
                    simp only [Batch0327.cell2617, Batch0327.tau2617, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01003222 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-113/320 : ℝ) with hy0100322 | hy0100322
                · have hs01003221 : InSquare (-109/640) (-227/640) (1/640) tau := by
                    convert childLR hs0100322 hx0100322 hy0100322 using 1 <;> norm_num
                  exact Batch0327.cell2616.sound htau (by
                    simp only [Batch0327.cell2616, Batch0327.tau2616, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01003221 (by positivity) using 1 <;> norm_num)
                · have hs01003223 : InSquare (-109/640) (-45/128) (1/640) tau := by
                    convert childUR hs0100322 hx0100322 hy0100322 using 1 <;> norm_num
                  exact Batch0327.cell2618.sound htau (by
                    simp only [Batch0327.cell2618, Batch0327.tau2618, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01003223 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-57/160 : ℝ) with hy010032 | hy010032
            · have hs0100321 : InSquare (-53/320) (-23/64) (1/320) tau := by
                convert childLR hs010032 hx010032 hy010032 using 1 <;> norm_num
              rcases le_total tau.re (-53/320 : ℝ) with hx0100321 | hx0100321
              · rcases le_total tau.im (-23/64 : ℝ) with hy0100321 | hy0100321
                · have hs01003210 : InSquare (-107/640) (-231/640) (1/640) tau := by
                    convert childLL hs0100321 hx0100321 hy0100321 using 1 <;> norm_num
                  exact Batch0326.cell2611.sound htau (by
                    simp only [Batch0326.cell2611, Batch0326.tau2611, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01003210 (by positivity) using 1 <;> norm_num)
                · have hs01003212 : InSquare (-107/640) (-229/640) (1/640) tau := by
                    convert childUL hs0100321 hx0100321 hy0100321 using 1 <;> norm_num
                  exact Batch0326.cell2613.sound htau (by
                    simp only [Batch0326.cell2613, Batch0326.tau2613, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01003212 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-23/64 : ℝ) with hy0100321 | hy0100321
                · have hs01003211 : InSquare (-21/128) (-231/640) (1/640) tau := by
                    convert childLR hs0100321 hx0100321 hy0100321 using 1 <;> norm_num
                  exact Batch0326.cell2612.sound htau (by
                    simp only [Batch0326.cell2612, Batch0326.tau2612, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01003211 (by positivity) using 1 <;> norm_num)
                · have hs01003213 : InSquare (-21/128) (-229/640) (1/640) tau := by
                    convert childUR hs0100321 hx0100321 hy0100321 using 1 <;> norm_num
                  exact Batch0326.cell2614.sound htau (by
                    simp only [Batch0326.cell2614, Batch0326.tau2614, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01003213 (by positivity) using 1 <;> norm_num)
            · have hs0100323 : InSquare (-53/320) (-113/320) (1/320) tau := by
                convert childUR hs010032 hx010032 hy010032 using 1 <;> norm_num
              exact Batch0168.cell1344.sound htau (by
                simp only [Batch0168.cell1344, Batch0168.tau1344, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0100323 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-29/80 : ℝ) with hy01003 | hy01003
        · have hs010031 : InSquare (-5/32) (-59/160) (1/160) tau := by
            convert childLR hs01003 hx01003 hy01003 using 1 <;> norm_num
          rcases le_total tau.re (-5/32 : ℝ) with hx010031 | hx010031
          · rcases le_total tau.im (-59/160 : ℝ) with hy010031 | hy010031
            · have hs0100310 : InSquare (-51/320) (-119/320) (1/320) tau := by
                convert childLL hs010031 hx010031 hy010031 using 1 <;> norm_num
              exact (outside_0100310 htau hs0100310).elim
            · have hs0100312 : InSquare (-51/320) (-117/320) (1/320) tau := by
                convert childUL hs010031 hx010031 hy010031 using 1 <;> norm_num
              rcases le_total tau.re (-51/320 : ℝ) with hx0100312 | hx0100312
              · rcases le_total tau.im (-117/320 : ℝ) with hy0100312 | hy0100312
                · have hs01003120 : InSquare (-103/640) (-47/128) (1/640) tau := by
                    convert childLL hs0100312 hx0100312 hy0100312 using 1 <;> norm_num
                  exact Batch0324.cell2599.sound htau (by
                    simp only [Batch0324.cell2599, Batch0324.tau2599, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01003120 (by positivity) using 1 <;> norm_num)
                · have hs01003122 : InSquare (-103/640) (-233/640) (1/640) tau := by
                    convert childUL hs0100312 hx0100312 hy0100312 using 1 <;> norm_num
                  exact Batch0325.cell2601.sound htau (by
                    simp only [Batch0325.cell2601, Batch0325.tau2601, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01003122 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-117/320 : ℝ) with hy0100312 | hy0100312
                · have hs01003121 : InSquare (-101/640) (-47/128) (1/640) tau := by
                    convert childLR hs0100312 hx0100312 hy0100312 using 1 <;> norm_num
                  exact Batch0325.cell2600.sound htau (by
                    simp only [Batch0325.cell2600, Batch0325.tau2600, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01003121 (by positivity) using 1 <;> norm_num)
                · have hs01003123 : InSquare (-101/640) (-233/640) (1/640) tau := by
                    convert childUR hs0100312 hx0100312 hy0100312 using 1 <;> norm_num
                  exact Batch0325.cell2602.sound htau (by
                    simp only [Batch0325.cell2602, Batch0325.tau2602, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01003123 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-59/160 : ℝ) with hy010031 | hy010031
            · have hs0100311 : InSquare (-49/320) (-119/320) (1/320) tau := by
                convert childLR hs010031 hx010031 hy010031 using 1 <;> norm_num
              rcases le_total tau.re (-49/320 : ℝ) with hx0100311 | hx0100311
              · rcases le_total tau.im (-119/320 : ℝ) with hy0100311 | hy0100311
                · have hs01003110 : InSquare (-99/640) (-239/640) (1/640) tau := by
                    convert childLL hs0100311 hx0100311 hy0100311 using 1 <;> norm_num
                  exact (outside_01003110 htau hs01003110).elim
                · have hs01003112 : InSquare (-99/640) (-237/640) (1/640) tau := by
                    convert childUL hs0100311 hx0100311 hy0100311 using 1 <;> norm_num
                  exact Batch0324.cell2597.sound htau (by
                    simp only [Batch0324.cell2597, Batch0324.tau2597, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01003112 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-119/320 : ℝ) with hy0100311 | hy0100311
                · have hs01003111 : InSquare (-97/640) (-239/640) (1/640) tau := by
                    convert childLR hs0100311 hx0100311 hy0100311 using 1 <;> norm_num
                  exact (outside_01003111 htau hs01003111).elim
                · have hs01003113 : InSquare (-97/640) (-237/640) (1/640) tau := by
                    convert childUR hs0100311 hx0100311 hy0100311 using 1 <;> norm_num
                  exact Batch0324.cell2598.sound htau (by
                    simp only [Batch0324.cell2598, Batch0324.tau2598, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01003113 (by positivity) using 1 <;> norm_num)
            · have hs0100313 : InSquare (-49/320) (-117/320) (1/320) tau := by
                convert childUR hs010031 hx010031 hy010031 using 1 <;> norm_num
              rcases le_total tau.re (-49/320 : ℝ) with hx0100313 | hx0100313
              · rcases le_total tau.im (-117/320 : ℝ) with hy0100313 | hy0100313
                · have hs01003130 : InSquare (-99/640) (-47/128) (1/640) tau := by
                    convert childLL hs0100313 hx0100313 hy0100313 using 1 <;> norm_num
                  exact Batch0325.cell2603.sound htau (by
                    simp only [Batch0325.cell2603, Batch0325.tau2603, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01003130 (by positivity) using 1 <;> norm_num)
                · have hs01003132 : InSquare (-99/640) (-233/640) (1/640) tau := by
                    convert childUL hs0100313 hx0100313 hy0100313 using 1 <;> norm_num
                  exact Batch0325.cell2605.sound htau (by
                    simp only [Batch0325.cell2605, Batch0325.tau2605, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01003132 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-117/320 : ℝ) with hy0100313 | hy0100313
                · have hs01003131 : InSquare (-97/640) (-47/128) (1/640) tau := by
                    convert childLR hs0100313 hx0100313 hy0100313 using 1 <;> norm_num
                  exact Batch0325.cell2604.sound htau (by
                    simp only [Batch0325.cell2604, Batch0325.tau2604, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01003131 (by positivity) using 1 <;> norm_num)
                · have hs01003133 : InSquare (-97/640) (-233/640) (1/640) tau := by
                    convert childUR hs0100313 hx0100313 hy0100313 using 1 <;> norm_num
                  exact Batch0325.cell2606.sound htau (by
                    simp only [Batch0325.cell2606, Batch0325.tau2606, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01003133 (by positivity) using 1 <;> norm_num)
        · have hs010033 : InSquare (-5/32) (-57/160) (1/160) tau := by
            convert childUR hs01003 hx01003 hy01003 using 1 <;> norm_num
          rcases le_total tau.re (-5/32 : ℝ) with hx010033 | hx010033
          · rcases le_total tau.im (-57/160 : ℝ) with hy010033 | hy010033
            · have hs0100330 : InSquare (-51/320) (-23/64) (1/320) tau := by
                convert childLL hs010033 hx010033 hy010033 using 1 <;> norm_num
              rcases le_total tau.re (-51/320 : ℝ) with hx0100330 | hx0100330
              · rcases le_total tau.im (-23/64 : ℝ) with hy0100330 | hy0100330
                · have hs01003300 : InSquare (-103/640) (-231/640) (1/640) tau := by
                    convert childLL hs0100330 hx0100330 hy0100330 using 1 <;> norm_num
                  exact Batch0327.cell2619.sound htau (by
                    simp only [Batch0327.cell2619, Batch0327.tau2619, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01003300 (by positivity) using 1 <;> norm_num)
                · have hs01003302 : InSquare (-103/640) (-229/640) (1/640) tau := by
                    convert childUL hs0100330 hx0100330 hy0100330 using 1 <;> norm_num
                  exact Batch0327.cell2621.sound htau (by
                    simp only [Batch0327.cell2621, Batch0327.tau2621, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01003302 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-23/64 : ℝ) with hy0100330 | hy0100330
                · have hs01003301 : InSquare (-101/640) (-231/640) (1/640) tau := by
                    convert childLR hs0100330 hx0100330 hy0100330 using 1 <;> norm_num
                  exact Batch0327.cell2620.sound htau (by
                    simp only [Batch0327.cell2620, Batch0327.tau2620, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01003301 (by positivity) using 1 <;> norm_num)
                · have hs01003303 : InSquare (-101/640) (-229/640) (1/640) tau := by
                    convert childUR hs0100330 hx0100330 hy0100330 using 1 <;> norm_num
                  exact Batch0327.cell2622.sound htau (by
                    simp only [Batch0327.cell2622, Batch0327.tau2622, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01003303 (by positivity) using 1 <;> norm_num)
            · have hs0100332 : InSquare (-51/320) (-113/320) (1/320) tau := by
                convert childUL hs010033 hx010033 hy010033 using 1 <;> norm_num
              exact Batch0168.cell1345.sound htau (by
                simp only [Batch0168.cell1345, Batch0168.tau1345, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0100332 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-57/160 : ℝ) with hy010033 | hy010033
            · have hs0100331 : InSquare (-49/320) (-23/64) (1/320) tau := by
                convert childLR hs010033 hx010033 hy010033 using 1 <;> norm_num
              rcases le_total tau.re (-49/320 : ℝ) with hx0100331 | hx0100331
              · rcases le_total tau.im (-23/64 : ℝ) with hy0100331 | hy0100331
                · have hs01003310 : InSquare (-99/640) (-231/640) (1/640) tau := by
                    convert childLL hs0100331 hx0100331 hy0100331 using 1 <;> norm_num
                  exact Batch0327.cell2623.sound htau (by
                    simp only [Batch0327.cell2623, Batch0327.tau2623, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01003310 (by positivity) using 1 <;> norm_num)
                · have hs01003312 : InSquare (-99/640) (-229/640) (1/640) tau := by
                    convert childUL hs0100331 hx0100331 hy0100331 using 1 <;> norm_num
                  exact Batch0328.cell2625.sound htau (by
                    simp only [Batch0328.cell2625, Batch0328.tau2625, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01003312 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-23/64 : ℝ) with hy0100331 | hy0100331
                · have hs01003311 : InSquare (-97/640) (-231/640) (1/640) tau := by
                    convert childLR hs0100331 hx0100331 hy0100331 using 1 <;> norm_num
                  exact Batch0328.cell2624.sound htau (by
                    simp only [Batch0328.cell2624, Batch0328.tau2624, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01003311 (by positivity) using 1 <;> norm_num)
                · have hs01003313 : InSquare (-97/640) (-229/640) (1/640) tau := by
                    convert childUR hs0100331 hx0100331 hy0100331 using 1 <;> norm_num
                  exact Batch0328.cell2626.sound htau (by
                    simp only [Batch0328.cell2626, Batch0328.tau2626, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01003313 (by positivity) using 1 <;> norm_num)
            · have hs0100333 : InSquare (-49/320) (-113/320) (1/320) tau := by
                convert childUR hs010033 hx010033 hy010033 using 1 <;> norm_num
              exact Batch0168.cell1346.sound htau (by
                simp only [Batch0168.cell1346, Batch0168.tau1346, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0100333 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0100
