import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0181
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0182
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0183
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0184
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0185
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0340
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0341
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0342
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0343
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0344
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0345
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0346
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0347
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0348
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0349
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0350

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0110

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

private theorem outside_0110000 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-31/320) (-127/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (3/32 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+3/32)]
  have himSq : (63/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+63/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_0110001 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-29/320) (-127/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (7/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+7/80)]
  have himSq : (63/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+63/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_0110010 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-27/320) (-127/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (13/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+13/160)]
  have himSq : (63/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+63/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_0110011 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-5/64) (-127/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (3/40 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+3/40)]
  have himSq : (63/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+63/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_01100020 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-63/640) (-251/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (31/320 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+31/320)]
  have himSq : (25/64 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+25/64)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_01100021 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-61/640) (-251/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (3/32 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+3/32)]
  have himSq : (25/64 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+25/64)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_01100030 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-59/640) (-251/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (29/320 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+29/320)]
  have himSq : (25/64 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+25/64)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_01100031 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-57/640) (-251/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (7/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+7/80)]
  have himSq : (25/64 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+25/64)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_01101000 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-47/640) (-51/128) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (23/320 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+23/320)]
  have himSq : (127/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+127/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_01101001 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-9/128) (-51/128) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (11/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+11/160)]
  have himSq : (127/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+127/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_01101002 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-47/640) (-253/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (23/320 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+23/320)]
  have himSq : (63/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+63/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_01101010 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-43/640) (-51/128) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (21/320 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+21/320)]
  have himSq : (127/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+127/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_01101011 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-41/640) (-51/128) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (1/16 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+1/16)]
  have himSq : (127/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+127/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_01101100 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-39/640) (-51/128) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (19/320 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+19/320)]
  have himSq : (127/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+127/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_01101101 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-37/640) (-51/128) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (9/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+9/160)]
  have himSq : (127/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+127/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_01101110 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-7/128) (-51/128) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (17/320 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+17/320)]
  have himSq : (127/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+127/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_01101111 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-33/640) (-51/128) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (1/20 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+1/20)]
  have himSq : (127/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+127/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-3/40) (-3/8) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (-3/40 : ℝ) with hx0110 | hx0110
  · rcases le_total tau.im (-3/8 : ℝ) with hy0110 | hy0110
    · have hs01100 : InSquare (-7/80) (-31/80) (1/80) tau := by
        convert childLL hs hx0110 hy0110 using 1 <;> norm_num
      rcases le_total tau.re (-7/80 : ℝ) with hx01100 | hx01100
      · rcases le_total tau.im (-31/80 : ℝ) with hy01100 | hy01100
        · have hs011000 : InSquare (-3/32) (-63/160) (1/160) tau := by
            convert childLL hs01100 hx01100 hy01100 using 1 <;> norm_num
          rcases le_total tau.re (-3/32 : ℝ) with hx011000 | hx011000
          · rcases le_total tau.im (-63/160 : ℝ) with hy011000 | hy011000
            · have hs0110000 : InSquare (-31/320) (-127/320) (1/320) tau := by
                convert childLL hs011000 hx011000 hy011000 using 1 <;> norm_num
              exact (outside_0110000 htau hs0110000).elim
            · have hs0110002 : InSquare (-31/320) (-25/64) (1/320) tau := by
                convert childUL hs011000 hx011000 hy011000 using 1 <;> norm_num
              rcases le_total tau.re (-31/320 : ℝ) with hx0110002 | hx0110002
              · rcases le_total tau.im (-25/64 : ℝ) with hy0110002 | hy0110002
                · have hs01100020 : InSquare (-63/640) (-251/640) (1/640) tau := by
                    convert childLL hs0110002 hx0110002 hy0110002 using 1 <;> norm_num
                  exact (outside_01100020 htau hs01100020).elim
                · have hs01100022 : InSquare (-63/640) (-249/640) (1/640) tau := by
                    convert childUL hs0110002 hx0110002 hy0110002 using 1 <;> norm_num
                  exact Batch0340.cell2721.sound htau (by
                    simp only [Batch0340.cell2721, Batch0340.tau2721, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01100022 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-25/64 : ℝ) with hy0110002 | hy0110002
                · have hs01100021 : InSquare (-61/640) (-251/640) (1/640) tau := by
                    convert childLR hs0110002 hx0110002 hy0110002 using 1 <;> norm_num
                  exact (outside_01100021 htau hs01100021).elim
                · have hs01100023 : InSquare (-61/640) (-249/640) (1/640) tau := by
                    convert childUR hs0110002 hx0110002 hy0110002 using 1 <;> norm_num
                  exact Batch0340.cell2722.sound htau (by
                    simp only [Batch0340.cell2722, Batch0340.tau2722, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01100023 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-63/160 : ℝ) with hy011000 | hy011000
            · have hs0110001 : InSquare (-29/320) (-127/320) (1/320) tau := by
                convert childLR hs011000 hx011000 hy011000 using 1 <;> norm_num
              exact (outside_0110001 htau hs0110001).elim
            · have hs0110003 : InSquare (-29/320) (-25/64) (1/320) tau := by
                convert childUR hs011000 hx011000 hy011000 using 1 <;> norm_num
              rcases le_total tau.re (-29/320 : ℝ) with hx0110003 | hx0110003
              · rcases le_total tau.im (-25/64 : ℝ) with hy0110003 | hy0110003
                · have hs01100030 : InSquare (-59/640) (-251/640) (1/640) tau := by
                    convert childLL hs0110003 hx0110003 hy0110003 using 1 <;> norm_num
                  exact (outside_01100030 htau hs01100030).elim
                · have hs01100032 : InSquare (-59/640) (-249/640) (1/640) tau := by
                    convert childUL hs0110003 hx0110003 hy0110003 using 1 <;> norm_num
                  exact Batch0340.cell2723.sound htau (by
                    simp only [Batch0340.cell2723, Batch0340.tau2723, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01100032 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-25/64 : ℝ) with hy0110003 | hy0110003
                · have hs01100031 : InSquare (-57/640) (-251/640) (1/640) tau := by
                    convert childLR hs0110003 hx0110003 hy0110003 using 1 <;> norm_num
                  exact (outside_01100031 htau hs01100031).elim
                · have hs01100033 : InSquare (-57/640) (-249/640) (1/640) tau := by
                    convert childUR hs0110003 hx0110003 hy0110003 using 1 <;> norm_num
                  exact Batch0340.cell2724.sound htau (by
                    simp only [Batch0340.cell2724, Batch0340.tau2724, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01100033 (by positivity) using 1 <;> norm_num)
        · have hs011002 : InSquare (-3/32) (-61/160) (1/160) tau := by
            convert childUL hs01100 hx01100 hy01100 using 1 <;> norm_num
          rcases le_total tau.re (-3/32 : ℝ) with hx011002 | hx011002
          · rcases le_total tau.im (-61/160 : ℝ) with hy011002 | hy011002
            · have hs0110020 : InSquare (-31/320) (-123/320) (1/320) tau := by
                convert childLL hs011002 hx011002 hy011002 using 1 <;> norm_num
              rcases le_total tau.re (-31/320 : ℝ) with hx0110020 | hx0110020
              · rcases le_total tau.im (-123/320 : ℝ) with hy0110020 | hy0110020
                · have hs01100200 : InSquare (-63/640) (-247/640) (1/640) tau := by
                    convert childLL hs0110020 hx0110020 hy0110020 using 1 <;> norm_num
                  exact Batch0341.cell2733.sound htau (by
                    simp only [Batch0341.cell2733, Batch0341.tau2733, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01100200 (by positivity) using 1 <;> norm_num)
                · have hs01100202 : InSquare (-63/640) (-49/128) (1/640) tau := by
                    convert childUL hs0110020 hx0110020 hy0110020 using 1 <;> norm_num
                  exact Batch0341.cell2735.sound htau (by
                    simp only [Batch0341.cell2735, Batch0341.tau2735, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01100202 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-123/320 : ℝ) with hy0110020 | hy0110020
                · have hs01100201 : InSquare (-61/640) (-247/640) (1/640) tau := by
                    convert childLR hs0110020 hx0110020 hy0110020 using 1 <;> norm_num
                  exact Batch0341.cell2734.sound htau (by
                    simp only [Batch0341.cell2734, Batch0341.tau2734, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01100201 (by positivity) using 1 <;> norm_num)
                · have hs01100203 : InSquare (-61/640) (-49/128) (1/640) tau := by
                    convert childUR hs0110020 hx0110020 hy0110020 using 1 <;> norm_num
                  exact Batch0342.cell2736.sound htau (by
                    simp only [Batch0342.cell2736, Batch0342.tau2736, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01100203 (by positivity) using 1 <;> norm_num)
            · have hs0110022 : InSquare (-31/320) (-121/320) (1/320) tau := by
                convert childUL hs011002 hx011002 hy011002 using 1 <;> norm_num
              rcases le_total tau.re (-31/320 : ℝ) with hx0110022 | hx0110022
              · rcases le_total tau.im (-121/320 : ℝ) with hy0110022 | hy0110022
                · have hs01100220 : InSquare (-63/640) (-243/640) (1/640) tau := by
                    convert childLL hs0110022 hx0110022 hy0110022 using 1 <;> norm_num
                  exact Batch0342.cell2741.sound htau (by
                    simp only [Batch0342.cell2741, Batch0342.tau2741, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01100220 (by positivity) using 1 <;> norm_num)
                · have hs01100222 : InSquare (-63/640) (-241/640) (1/640) tau := by
                    convert childUL hs0110022 hx0110022 hy0110022 using 1 <;> norm_num
                  exact Batch0342.cell2743.sound htau (by
                    simp only [Batch0342.cell2743, Batch0342.tau2743, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01100222 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-121/320 : ℝ) with hy0110022 | hy0110022
                · have hs01100221 : InSquare (-61/640) (-243/640) (1/640) tau := by
                    convert childLR hs0110022 hx0110022 hy0110022 using 1 <;> norm_num
                  exact Batch0342.cell2742.sound htau (by
                    simp only [Batch0342.cell2742, Batch0342.tau2742, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01100221 (by positivity) using 1 <;> norm_num)
                · have hs01100223 : InSquare (-61/640) (-241/640) (1/640) tau := by
                    convert childUR hs0110022 hx0110022 hy0110022 using 1 <;> norm_num
                  exact Batch0343.cell2744.sound htau (by
                    simp only [Batch0343.cell2744, Batch0343.tau2744, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01100223 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-61/160 : ℝ) with hy011002 | hy011002
            · have hs0110021 : InSquare (-29/320) (-123/320) (1/320) tau := by
                convert childLR hs011002 hx011002 hy011002 using 1 <;> norm_num
              rcases le_total tau.re (-29/320 : ℝ) with hx0110021 | hx0110021
              · rcases le_total tau.im (-123/320 : ℝ) with hy0110021 | hy0110021
                · have hs01100210 : InSquare (-59/640) (-247/640) (1/640) tau := by
                    convert childLL hs0110021 hx0110021 hy0110021 using 1 <;> norm_num
                  exact Batch0342.cell2737.sound htau (by
                    simp only [Batch0342.cell2737, Batch0342.tau2737, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01100210 (by positivity) using 1 <;> norm_num)
                · have hs01100212 : InSquare (-59/640) (-49/128) (1/640) tau := by
                    convert childUL hs0110021 hx0110021 hy0110021 using 1 <;> norm_num
                  exact Batch0342.cell2739.sound htau (by
                    simp only [Batch0342.cell2739, Batch0342.tau2739, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01100212 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-123/320 : ℝ) with hy0110021 | hy0110021
                · have hs01100211 : InSquare (-57/640) (-247/640) (1/640) tau := by
                    convert childLR hs0110021 hx0110021 hy0110021 using 1 <;> norm_num
                  exact Batch0342.cell2738.sound htau (by
                    simp only [Batch0342.cell2738, Batch0342.tau2738, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01100211 (by positivity) using 1 <;> norm_num)
                · have hs01100213 : InSquare (-57/640) (-49/128) (1/640) tau := by
                    convert childUR hs0110021 hx0110021 hy0110021 using 1 <;> norm_num
                  exact Batch0342.cell2740.sound htau (by
                    simp only [Batch0342.cell2740, Batch0342.tau2740, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01100213 (by positivity) using 1 <;> norm_num)
            · have hs0110023 : InSquare (-29/320) (-121/320) (1/320) tau := by
                convert childUR hs011002 hx011002 hy011002 using 1 <;> norm_num
              rcases le_total tau.re (-29/320 : ℝ) with hx0110023 | hx0110023
              · rcases le_total tau.im (-121/320 : ℝ) with hy0110023 | hy0110023
                · have hs01100230 : InSquare (-59/640) (-243/640) (1/640) tau := by
                    convert childLL hs0110023 hx0110023 hy0110023 using 1 <;> norm_num
                  exact Batch0343.cell2745.sound htau (by
                    simp only [Batch0343.cell2745, Batch0343.tau2745, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01100230 (by positivity) using 1 <;> norm_num)
                · have hs01100232 : InSquare (-59/640) (-241/640) (1/640) tau := by
                    convert childUL hs0110023 hx0110023 hy0110023 using 1 <;> norm_num
                  exact Batch0343.cell2747.sound htau (by
                    simp only [Batch0343.cell2747, Batch0343.tau2747, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01100232 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-121/320 : ℝ) with hy0110023 | hy0110023
                · have hs01100231 : InSquare (-57/640) (-243/640) (1/640) tau := by
                    convert childLR hs0110023 hx0110023 hy0110023 using 1 <;> norm_num
                  exact Batch0343.cell2746.sound htau (by
                    simp only [Batch0343.cell2746, Batch0343.tau2746, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01100231 (by positivity) using 1 <;> norm_num)
                · have hs01100233 : InSquare (-57/640) (-241/640) (1/640) tau := by
                    convert childUR hs0110023 hx0110023 hy0110023 using 1 <;> norm_num
                  exact Batch0343.cell2748.sound htau (by
                    simp only [Batch0343.cell2748, Batch0343.tau2748, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01100233 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-31/80 : ℝ) with hy01100 | hy01100
        · have hs011001 : InSquare (-13/160) (-63/160) (1/160) tau := by
            convert childLR hs01100 hx01100 hy01100 using 1 <;> norm_num
          rcases le_total tau.re (-13/160 : ℝ) with hx011001 | hx011001
          · rcases le_total tau.im (-63/160 : ℝ) with hy011001 | hy011001
            · have hs0110010 : InSquare (-27/320) (-127/320) (1/320) tau := by
                convert childLL hs011001 hx011001 hy011001 using 1 <;> norm_num
              exact (outside_0110010 htau hs0110010).elim
            · have hs0110012 : InSquare (-27/320) (-25/64) (1/320) tau := by
                convert childUL hs011001 hx011001 hy011001 using 1 <;> norm_num
              rcases le_total tau.re (-27/320 : ℝ) with hx0110012 | hx0110012
              · rcases le_total tau.im (-25/64 : ℝ) with hy0110012 | hy0110012
                · have hs01100120 : InSquare (-11/128) (-251/640) (1/640) tau := by
                    convert childLL hs0110012 hx0110012 hy0110012 using 1 <;> norm_num
                  exact Batch0340.cell2725.sound htau (by
                    simp only [Batch0340.cell2725, Batch0340.tau2725, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01100120 (by positivity) using 1 <;> norm_num)
                · have hs01100122 : InSquare (-11/128) (-249/640) (1/640) tau := by
                    convert childUL hs0110012 hx0110012 hy0110012 using 1 <;> norm_num
                  exact Batch0340.cell2727.sound htau (by
                    simp only [Batch0340.cell2727, Batch0340.tau2727, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01100122 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-25/64 : ℝ) with hy0110012 | hy0110012
                · have hs01100121 : InSquare (-53/640) (-251/640) (1/640) tau := by
                    convert childLR hs0110012 hx0110012 hy0110012 using 1 <;> norm_num
                  exact Batch0340.cell2726.sound htau (by
                    simp only [Batch0340.cell2726, Batch0340.tau2726, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01100121 (by positivity) using 1 <;> norm_num)
                · have hs01100123 : InSquare (-53/640) (-249/640) (1/640) tau := by
                    convert childUR hs0110012 hx0110012 hy0110012 using 1 <;> norm_num
                  exact Batch0341.cell2728.sound htau (by
                    simp only [Batch0341.cell2728, Batch0341.tau2728, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01100123 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-63/160 : ℝ) with hy011001 | hy011001
            · have hs0110011 : InSquare (-5/64) (-127/320) (1/320) tau := by
                convert childLR hs011001 hx011001 hy011001 using 1 <;> norm_num
              exact (outside_0110011 htau hs0110011).elim
            · have hs0110013 : InSquare (-5/64) (-25/64) (1/320) tau := by
                convert childUR hs011001 hx011001 hy011001 using 1 <;> norm_num
              rcases le_total tau.re (-5/64 : ℝ) with hx0110013 | hx0110013
              · rcases le_total tau.im (-25/64 : ℝ) with hy0110013 | hy0110013
                · have hs01100130 : InSquare (-51/640) (-251/640) (1/640) tau := by
                    convert childLL hs0110013 hx0110013 hy0110013 using 1 <;> norm_num
                  exact Batch0341.cell2729.sound htau (by
                    simp only [Batch0341.cell2729, Batch0341.tau2729, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01100130 (by positivity) using 1 <;> norm_num)
                · have hs01100132 : InSquare (-51/640) (-249/640) (1/640) tau := by
                    convert childUL hs0110013 hx0110013 hy0110013 using 1 <;> norm_num
                  exact Batch0341.cell2731.sound htau (by
                    simp only [Batch0341.cell2731, Batch0341.tau2731, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01100132 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-25/64 : ℝ) with hy0110013 | hy0110013
                · have hs01100131 : InSquare (-49/640) (-251/640) (1/640) tau := by
                    convert childLR hs0110013 hx0110013 hy0110013 using 1 <;> norm_num
                  exact Batch0341.cell2730.sound htau (by
                    simp only [Batch0341.cell2730, Batch0341.tau2730, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01100131 (by positivity) using 1 <;> norm_num)
                · have hs01100133 : InSquare (-49/640) (-249/640) (1/640) tau := by
                    convert childUR hs0110013 hx0110013 hy0110013 using 1 <;> norm_num
                  exact Batch0341.cell2732.sound htau (by
                    simp only [Batch0341.cell2732, Batch0341.tau2732, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01100133 (by positivity) using 1 <;> norm_num)
        · have hs011003 : InSquare (-13/160) (-61/160) (1/160) tau := by
            convert childUR hs01100 hx01100 hy01100 using 1 <;> norm_num
          rcases le_total tau.re (-13/160 : ℝ) with hx011003 | hx011003
          · rcases le_total tau.im (-61/160 : ℝ) with hy011003 | hy011003
            · have hs0110030 : InSquare (-27/320) (-123/320) (1/320) tau := by
                convert childLL hs011003 hx011003 hy011003 using 1 <;> norm_num
              rcases le_total tau.re (-27/320 : ℝ) with hx0110030 | hx0110030
              · rcases le_total tau.im (-123/320 : ℝ) with hy0110030 | hy0110030
                · have hs01100300 : InSquare (-11/128) (-247/640) (1/640) tau := by
                    convert childLL hs0110030 hx0110030 hy0110030 using 1 <;> norm_num
                  exact Batch0343.cell2749.sound htau (by
                    simp only [Batch0343.cell2749, Batch0343.tau2749, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01100300 (by positivity) using 1 <;> norm_num)
                · have hs01100302 : InSquare (-11/128) (-49/128) (1/640) tau := by
                    convert childUL hs0110030 hx0110030 hy0110030 using 1 <;> norm_num
                  exact Batch0343.cell2751.sound htau (by
                    simp only [Batch0343.cell2751, Batch0343.tau2751, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01100302 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-123/320 : ℝ) with hy0110030 | hy0110030
                · have hs01100301 : InSquare (-53/640) (-247/640) (1/640) tau := by
                    convert childLR hs0110030 hx0110030 hy0110030 using 1 <;> norm_num
                  exact Batch0343.cell2750.sound htau (by
                    simp only [Batch0343.cell2750, Batch0343.tau2750, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01100301 (by positivity) using 1 <;> norm_num)
                · have hs01100303 : InSquare (-53/640) (-49/128) (1/640) tau := by
                    convert childUR hs0110030 hx0110030 hy0110030 using 1 <;> norm_num
                  exact Batch0344.cell2752.sound htau (by
                    simp only [Batch0344.cell2752, Batch0344.tau2752, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01100303 (by positivity) using 1 <;> norm_num)
            · have hs0110032 : InSquare (-27/320) (-121/320) (1/320) tau := by
                convert childUL hs011003 hx011003 hy011003 using 1 <;> norm_num
              rcases le_total tau.re (-27/320 : ℝ) with hx0110032 | hx0110032
              · rcases le_total tau.im (-121/320 : ℝ) with hy0110032 | hy0110032
                · have hs01100320 : InSquare (-11/128) (-243/640) (1/640) tau := by
                    convert childLL hs0110032 hx0110032 hy0110032 using 1 <;> norm_num
                  exact Batch0344.cell2757.sound htau (by
                    simp only [Batch0344.cell2757, Batch0344.tau2757, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01100320 (by positivity) using 1 <;> norm_num)
                · have hs01100322 : InSquare (-11/128) (-241/640) (1/640) tau := by
                    convert childUL hs0110032 hx0110032 hy0110032 using 1 <;> norm_num
                  exact Batch0344.cell2759.sound htau (by
                    simp only [Batch0344.cell2759, Batch0344.tau2759, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01100322 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-121/320 : ℝ) with hy0110032 | hy0110032
                · have hs01100321 : InSquare (-53/640) (-243/640) (1/640) tau := by
                    convert childLR hs0110032 hx0110032 hy0110032 using 1 <;> norm_num
                  exact Batch0344.cell2758.sound htau (by
                    simp only [Batch0344.cell2758, Batch0344.tau2758, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01100321 (by positivity) using 1 <;> norm_num)
                · have hs01100323 : InSquare (-53/640) (-241/640) (1/640) tau := by
                    convert childUR hs0110032 hx0110032 hy0110032 using 1 <;> norm_num
                  exact Batch0345.cell2760.sound htau (by
                    simp only [Batch0345.cell2760, Batch0345.tau2760, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01100323 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-61/160 : ℝ) with hy011003 | hy011003
            · have hs0110031 : InSquare (-5/64) (-123/320) (1/320) tau := by
                convert childLR hs011003 hx011003 hy011003 using 1 <;> norm_num
              rcases le_total tau.re (-5/64 : ℝ) with hx0110031 | hx0110031
              · rcases le_total tau.im (-123/320 : ℝ) with hy0110031 | hy0110031
                · have hs01100310 : InSquare (-51/640) (-247/640) (1/640) tau := by
                    convert childLL hs0110031 hx0110031 hy0110031 using 1 <;> norm_num
                  exact Batch0344.cell2753.sound htau (by
                    simp only [Batch0344.cell2753, Batch0344.tau2753, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01100310 (by positivity) using 1 <;> norm_num)
                · have hs01100312 : InSquare (-51/640) (-49/128) (1/640) tau := by
                    convert childUL hs0110031 hx0110031 hy0110031 using 1 <;> norm_num
                  exact Batch0344.cell2755.sound htau (by
                    simp only [Batch0344.cell2755, Batch0344.tau2755, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01100312 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-123/320 : ℝ) with hy0110031 | hy0110031
                · have hs01100311 : InSquare (-49/640) (-247/640) (1/640) tau := by
                    convert childLR hs0110031 hx0110031 hy0110031 using 1 <;> norm_num
                  exact Batch0344.cell2754.sound htau (by
                    simp only [Batch0344.cell2754, Batch0344.tau2754, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01100311 (by positivity) using 1 <;> norm_num)
                · have hs01100313 : InSquare (-49/640) (-49/128) (1/640) tau := by
                    convert childUR hs0110031 hx0110031 hy0110031 using 1 <;> norm_num
                  exact Batch0344.cell2756.sound htau (by
                    simp only [Batch0344.cell2756, Batch0344.tau2756, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01100313 (by positivity) using 1 <;> norm_num)
            · have hs0110033 : InSquare (-5/64) (-121/320) (1/320) tau := by
                convert childUR hs011003 hx011003 hy011003 using 1 <;> norm_num
              rcases le_total tau.re (-5/64 : ℝ) with hx0110033 | hx0110033
              · rcases le_total tau.im (-121/320 : ℝ) with hy0110033 | hy0110033
                · have hs01100330 : InSquare (-51/640) (-243/640) (1/640) tau := by
                    convert childLL hs0110033 hx0110033 hy0110033 using 1 <;> norm_num
                  exact Batch0345.cell2761.sound htau (by
                    simp only [Batch0345.cell2761, Batch0345.tau2761, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01100330 (by positivity) using 1 <;> norm_num)
                · have hs01100332 : InSquare (-51/640) (-241/640) (1/640) tau := by
                    convert childUL hs0110033 hx0110033 hy0110033 using 1 <;> norm_num
                  exact Batch0345.cell2763.sound htau (by
                    simp only [Batch0345.cell2763, Batch0345.tau2763, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01100332 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-121/320 : ℝ) with hy0110033 | hy0110033
                · have hs01100331 : InSquare (-49/640) (-243/640) (1/640) tau := by
                    convert childLR hs0110033 hx0110033 hy0110033 using 1 <;> norm_num
                  exact Batch0345.cell2762.sound htau (by
                    simp only [Batch0345.cell2762, Batch0345.tau2762, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01100331 (by positivity) using 1 <;> norm_num)
                · have hs01100333 : InSquare (-49/640) (-241/640) (1/640) tau := by
                    convert childUR hs0110033 hx0110033 hy0110033 using 1 <;> norm_num
                  exact Batch0345.cell2764.sound htau (by
                    simp only [Batch0345.cell2764, Batch0345.tau2764, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01100333 (by positivity) using 1 <;> norm_num)
    · have hs01102 : InSquare (-7/80) (-29/80) (1/80) tau := by
        convert childUL hs hx0110 hy0110 using 1 <;> norm_num
      rcases le_total tau.re (-7/80 : ℝ) with hx01102 | hx01102
      · rcases le_total tau.im (-29/80 : ℝ) with hy01102 | hy01102
        · have hs011020 : InSquare (-3/32) (-59/160) (1/160) tau := by
            convert childLL hs01102 hx01102 hy01102 using 1 <;> norm_num
          rcases le_total tau.re (-3/32 : ℝ) with hx011020 | hx011020
          · rcases le_total tau.im (-59/160 : ℝ) with hy011020 | hy011020
            · have hs0110200 : InSquare (-31/320) (-119/320) (1/320) tau := by
                convert childLL hs011020 hx011020 hy011020 using 1 <;> norm_num
              exact Batch0181.cell1455.sound htau (by
                simp only [Batch0181.cell1455, Batch0181.tau1455, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0110200 (by positivity) using 1 <;> norm_num)
            · have hs0110202 : InSquare (-31/320) (-117/320) (1/320) tau := by
                convert childUL hs011020 hx011020 hy011020 using 1 <;> norm_num
              exact Batch0182.cell1457.sound htau (by
                simp only [Batch0182.cell1457, Batch0182.tau1457, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0110202 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-59/160 : ℝ) with hy011020 | hy011020
            · have hs0110201 : InSquare (-29/320) (-119/320) (1/320) tau := by
                convert childLR hs011020 hx011020 hy011020 using 1 <;> norm_num
              exact Batch0182.cell1456.sound htau (by
                simp only [Batch0182.cell1456, Batch0182.tau1456, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0110201 (by positivity) using 1 <;> norm_num)
            · have hs0110203 : InSquare (-29/320) (-117/320) (1/320) tau := by
                convert childUR hs011020 hx011020 hy011020 using 1 <;> norm_num
              exact Batch0182.cell1458.sound htau (by
                simp only [Batch0182.cell1458, Batch0182.tau1458, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0110203 (by positivity) using 1 <;> norm_num)
        · have hs011022 : InSquare (-3/32) (-57/160) (1/160) tau := by
            convert childUL hs01102 hx01102 hy01102 using 1 <;> norm_num
          rcases le_total tau.re (-3/32 : ℝ) with hx011022 | hx011022
          · rcases le_total tau.im (-57/160 : ℝ) with hy011022 | hy011022
            · have hs0110220 : InSquare (-31/320) (-23/64) (1/320) tau := by
                convert childLL hs011022 hx011022 hy011022 using 1 <;> norm_num
              exact Batch0182.cell1463.sound htau (by
                simp only [Batch0182.cell1463, Batch0182.tau1463, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0110220 (by positivity) using 1 <;> norm_num)
            · have hs0110222 : InSquare (-31/320) (-113/320) (1/320) tau := by
                convert childUL hs011022 hx011022 hy011022 using 1 <;> norm_num
              exact Batch0183.cell1465.sound htau (by
                simp only [Batch0183.cell1465, Batch0183.tau1465, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0110222 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-57/160 : ℝ) with hy011022 | hy011022
            · have hs0110221 : InSquare (-29/320) (-23/64) (1/320) tau := by
                convert childLR hs011022 hx011022 hy011022 using 1 <;> norm_num
              exact Batch0183.cell1464.sound htau (by
                simp only [Batch0183.cell1464, Batch0183.tau1464, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0110221 (by positivity) using 1 <;> norm_num)
            · have hs0110223 : InSquare (-29/320) (-113/320) (1/320) tau := by
                convert childUR hs011022 hx011022 hy011022 using 1 <;> norm_num
              exact Batch0183.cell1466.sound htau (by
                simp only [Batch0183.cell1466, Batch0183.tau1466, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0110223 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-29/80 : ℝ) with hy01102 | hy01102
        · have hs011021 : InSquare (-13/160) (-59/160) (1/160) tau := by
            convert childLR hs01102 hx01102 hy01102 using 1 <;> norm_num
          rcases le_total tau.re (-13/160 : ℝ) with hx011021 | hx011021
          · rcases le_total tau.im (-59/160 : ℝ) with hy011021 | hy011021
            · have hs0110210 : InSquare (-27/320) (-119/320) (1/320) tau := by
                convert childLL hs011021 hx011021 hy011021 using 1 <;> norm_num
              exact Batch0182.cell1459.sound htau (by
                simp only [Batch0182.cell1459, Batch0182.tau1459, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0110210 (by positivity) using 1 <;> norm_num)
            · have hs0110212 : InSquare (-27/320) (-117/320) (1/320) tau := by
                convert childUL hs011021 hx011021 hy011021 using 1 <;> norm_num
              exact Batch0182.cell1461.sound htau (by
                simp only [Batch0182.cell1461, Batch0182.tau1461, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0110212 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-59/160 : ℝ) with hy011021 | hy011021
            · have hs0110211 : InSquare (-5/64) (-119/320) (1/320) tau := by
                convert childLR hs011021 hx011021 hy011021 using 1 <;> norm_num
              exact Batch0182.cell1460.sound htau (by
                simp only [Batch0182.cell1460, Batch0182.tau1460, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0110211 (by positivity) using 1 <;> norm_num)
            · have hs0110213 : InSquare (-5/64) (-117/320) (1/320) tau := by
                convert childUR hs011021 hx011021 hy011021 using 1 <;> norm_num
              exact Batch0182.cell1462.sound htau (by
                simp only [Batch0182.cell1462, Batch0182.tau1462, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0110213 (by positivity) using 1 <;> norm_num)
        · have hs011023 : InSquare (-13/160) (-57/160) (1/160) tau := by
            convert childUR hs01102 hx01102 hy01102 using 1 <;> norm_num
          rcases le_total tau.re (-13/160 : ℝ) with hx011023 | hx011023
          · rcases le_total tau.im (-57/160 : ℝ) with hy011023 | hy011023
            · have hs0110230 : InSquare (-27/320) (-23/64) (1/320) tau := by
                convert childLL hs011023 hx011023 hy011023 using 1 <;> norm_num
              exact Batch0183.cell1467.sound htau (by
                simp only [Batch0183.cell1467, Batch0183.tau1467, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0110230 (by positivity) using 1 <;> norm_num)
            · have hs0110232 : InSquare (-27/320) (-113/320) (1/320) tau := by
                convert childUL hs011023 hx011023 hy011023 using 1 <;> norm_num
              exact Batch0183.cell1469.sound htau (by
                simp only [Batch0183.cell1469, Batch0183.tau1469, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0110232 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-57/160 : ℝ) with hy011023 | hy011023
            · have hs0110231 : InSquare (-5/64) (-23/64) (1/320) tau := by
                convert childLR hs011023 hx011023 hy011023 using 1 <;> norm_num
              exact Batch0183.cell1468.sound htau (by
                simp only [Batch0183.cell1468, Batch0183.tau1468, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0110231 (by positivity) using 1 <;> norm_num)
            · have hs0110233 : InSquare (-5/64) (-113/320) (1/320) tau := by
                convert childUR hs011023 hx011023 hy011023 using 1 <;> norm_num
              exact Batch0183.cell1470.sound htau (by
                simp only [Batch0183.cell1470, Batch0183.tau1470, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0110233 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (-3/8 : ℝ) with hy0110 | hy0110
    · have hs01101 : InSquare (-1/16) (-31/80) (1/80) tau := by
        convert childLR hs hx0110 hy0110 using 1 <;> norm_num
      rcases le_total tau.re (-1/16 : ℝ) with hx01101 | hx01101
      · rcases le_total tau.im (-31/80 : ℝ) with hy01101 | hy01101
        · have hs011010 : InSquare (-11/160) (-63/160) (1/160) tau := by
            convert childLL hs01101 hx01101 hy01101 using 1 <;> norm_num
          rcases le_total tau.re (-11/160 : ℝ) with hx011010 | hx011010
          · rcases le_total tau.im (-63/160 : ℝ) with hy011010 | hy011010
            · have hs0110100 : InSquare (-23/320) (-127/320) (1/320) tau := by
                convert childLL hs011010 hx011010 hy011010 using 1 <;> norm_num
              rcases le_total tau.re (-23/320 : ℝ) with hx0110100 | hx0110100
              · rcases le_total tau.im (-127/320 : ℝ) with hy0110100 | hy0110100
                · have hs01101000 : InSquare (-47/640) (-51/128) (1/640) tau := by
                    convert childLL hs0110100 hx0110100 hy0110100 using 1 <;> norm_num
                  exact (outside_01101000 htau hs01101000).elim
                · have hs01101002 : InSquare (-47/640) (-253/640) (1/640) tau := by
                    convert childUL hs0110100 hx0110100 hy0110100 using 1 <;> norm_num
                  exact (outside_01101002 htau hs01101002).elim
              · rcases le_total tau.im (-127/320 : ℝ) with hy0110100 | hy0110100
                · have hs01101001 : InSquare (-9/128) (-51/128) (1/640) tau := by
                    convert childLR hs0110100 hx0110100 hy0110100 using 1 <;> norm_num
                  exact (outside_01101001 htau hs01101001).elim
                · have hs01101003 : InSquare (-9/128) (-253/640) (1/640) tau := by
                    convert childUR hs0110100 hx0110100 hy0110100 using 1 <;> norm_num
                  exact Batch0345.cell2765.sound htau (by
                    simp only [Batch0345.cell2765, Batch0345.tau2765, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01101003 (by positivity) using 1 <;> norm_num)
            · have hs0110102 : InSquare (-23/320) (-25/64) (1/320) tau := by
                convert childUL hs011010 hx011010 hy011010 using 1 <;> norm_num
              rcases le_total tau.re (-23/320 : ℝ) with hx0110102 | hx0110102
              · rcases le_total tau.im (-25/64 : ℝ) with hy0110102 | hy0110102
                · have hs01101020 : InSquare (-47/640) (-251/640) (1/640) tau := by
                    convert childLL hs0110102 hx0110102 hy0110102 using 1 <;> norm_num
                  exact Batch0346.cell2768.sound htau (by
                    simp only [Batch0346.cell2768, Batch0346.tau2768, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01101020 (by positivity) using 1 <;> norm_num)
                · have hs01101022 : InSquare (-47/640) (-249/640) (1/640) tau := by
                    convert childUL hs0110102 hx0110102 hy0110102 using 1 <;> norm_num
                  exact Batch0346.cell2770.sound htau (by
                    simp only [Batch0346.cell2770, Batch0346.tau2770, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01101022 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-25/64 : ℝ) with hy0110102 | hy0110102
                · have hs01101021 : InSquare (-9/128) (-251/640) (1/640) tau := by
                    convert childLR hs0110102 hx0110102 hy0110102 using 1 <;> norm_num
                  exact Batch0346.cell2769.sound htau (by
                    simp only [Batch0346.cell2769, Batch0346.tau2769, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01101021 (by positivity) using 1 <;> norm_num)
                · have hs01101023 : InSquare (-9/128) (-249/640) (1/640) tau := by
                    convert childUR hs0110102 hx0110102 hy0110102 using 1 <;> norm_num
                  exact Batch0346.cell2771.sound htau (by
                    simp only [Batch0346.cell2771, Batch0346.tau2771, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01101023 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-63/160 : ℝ) with hy011010 | hy011010
            · have hs0110101 : InSquare (-21/320) (-127/320) (1/320) tau := by
                convert childLR hs011010 hx011010 hy011010 using 1 <;> norm_num
              rcases le_total tau.re (-21/320 : ℝ) with hx0110101 | hx0110101
              · rcases le_total tau.im (-127/320 : ℝ) with hy0110101 | hy0110101
                · have hs01101010 : InSquare (-43/640) (-51/128) (1/640) tau := by
                    convert childLL hs0110101 hx0110101 hy0110101 using 1 <;> norm_num
                  exact (outside_01101010 htau hs01101010).elim
                · have hs01101012 : InSquare (-43/640) (-253/640) (1/640) tau := by
                    convert childUL hs0110101 hx0110101 hy0110101 using 1 <;> norm_num
                  exact Batch0345.cell2766.sound htau (by
                    simp only [Batch0345.cell2766, Batch0345.tau2766, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01101012 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-127/320 : ℝ) with hy0110101 | hy0110101
                · have hs01101011 : InSquare (-41/640) (-51/128) (1/640) tau := by
                    convert childLR hs0110101 hx0110101 hy0110101 using 1 <;> norm_num
                  exact (outside_01101011 htau hs01101011).elim
                · have hs01101013 : InSquare (-41/640) (-253/640) (1/640) tau := by
                    convert childUR hs0110101 hx0110101 hy0110101 using 1 <;> norm_num
                  exact Batch0345.cell2767.sound htau (by
                    simp only [Batch0345.cell2767, Batch0345.tau2767, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01101013 (by positivity) using 1 <;> norm_num)
            · have hs0110103 : InSquare (-21/320) (-25/64) (1/320) tau := by
                convert childUR hs011010 hx011010 hy011010 using 1 <;> norm_num
              rcases le_total tau.re (-21/320 : ℝ) with hx0110103 | hx0110103
              · rcases le_total tau.im (-25/64 : ℝ) with hy0110103 | hy0110103
                · have hs01101030 : InSquare (-43/640) (-251/640) (1/640) tau := by
                    convert childLL hs0110103 hx0110103 hy0110103 using 1 <;> norm_num
                  exact Batch0346.cell2772.sound htau (by
                    simp only [Batch0346.cell2772, Batch0346.tau2772, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01101030 (by positivity) using 1 <;> norm_num)
                · have hs01101032 : InSquare (-43/640) (-249/640) (1/640) tau := by
                    convert childUL hs0110103 hx0110103 hy0110103 using 1 <;> norm_num
                  exact Batch0346.cell2774.sound htau (by
                    simp only [Batch0346.cell2774, Batch0346.tau2774, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01101032 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-25/64 : ℝ) with hy0110103 | hy0110103
                · have hs01101031 : InSquare (-41/640) (-251/640) (1/640) tau := by
                    convert childLR hs0110103 hx0110103 hy0110103 using 1 <;> norm_num
                  exact Batch0346.cell2773.sound htau (by
                    simp only [Batch0346.cell2773, Batch0346.tau2773, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01101031 (by positivity) using 1 <;> norm_num)
                · have hs01101033 : InSquare (-41/640) (-249/640) (1/640) tau := by
                    convert childUR hs0110103 hx0110103 hy0110103 using 1 <;> norm_num
                  exact Batch0346.cell2775.sound htau (by
                    simp only [Batch0346.cell2775, Batch0346.tau2775, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01101033 (by positivity) using 1 <;> norm_num)
        · have hs011012 : InSquare (-11/160) (-61/160) (1/160) tau := by
            convert childUL hs01101 hx01101 hy01101 using 1 <;> norm_num
          rcases le_total tau.re (-11/160 : ℝ) with hx011012 | hx011012
          · rcases le_total tau.im (-61/160 : ℝ) with hy011012 | hy011012
            · have hs0110120 : InSquare (-23/320) (-123/320) (1/320) tau := by
                convert childLL hs011012 hx011012 hy011012 using 1 <;> norm_num
              rcases le_total tau.re (-23/320 : ℝ) with hx0110120 | hx0110120
              · rcases le_total tau.im (-123/320 : ℝ) with hy0110120 | hy0110120
                · have hs01101200 : InSquare (-47/640) (-247/640) (1/640) tau := by
                    convert childLL hs0110120 hx0110120 hy0110120 using 1 <;> norm_num
                  exact Batch0348.cell2788.sound htau (by
                    simp only [Batch0348.cell2788, Batch0348.tau2788, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01101200 (by positivity) using 1 <;> norm_num)
                · have hs01101202 : InSquare (-47/640) (-49/128) (1/640) tau := by
                    convert childUL hs0110120 hx0110120 hy0110120 using 1 <;> norm_num
                  exact Batch0348.cell2790.sound htau (by
                    simp only [Batch0348.cell2790, Batch0348.tau2790, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01101202 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-123/320 : ℝ) with hy0110120 | hy0110120
                · have hs01101201 : InSquare (-9/128) (-247/640) (1/640) tau := by
                    convert childLR hs0110120 hx0110120 hy0110120 using 1 <;> norm_num
                  exact Batch0348.cell2789.sound htau (by
                    simp only [Batch0348.cell2789, Batch0348.tau2789, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01101201 (by positivity) using 1 <;> norm_num)
                · have hs01101203 : InSquare (-9/128) (-49/128) (1/640) tau := by
                    convert childUR hs0110120 hx0110120 hy0110120 using 1 <;> norm_num
                  exact Batch0348.cell2791.sound htau (by
                    simp only [Batch0348.cell2791, Batch0348.tau2791, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01101203 (by positivity) using 1 <;> norm_num)
            · have hs0110122 : InSquare (-23/320) (-121/320) (1/320) tau := by
                convert childUL hs011012 hx011012 hy011012 using 1 <;> norm_num
              rcases le_total tau.re (-23/320 : ℝ) with hx0110122 | hx0110122
              · rcases le_total tau.im (-121/320 : ℝ) with hy0110122 | hy0110122
                · have hs01101220 : InSquare (-47/640) (-243/640) (1/640) tau := by
                    convert childLL hs0110122 hx0110122 hy0110122 using 1 <;> norm_num
                  exact Batch0349.cell2796.sound htau (by
                    simp only [Batch0349.cell2796, Batch0349.tau2796, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01101220 (by positivity) using 1 <;> norm_num)
                · have hs01101222 : InSquare (-47/640) (-241/640) (1/640) tau := by
                    convert childUL hs0110122 hx0110122 hy0110122 using 1 <;> norm_num
                  exact Batch0349.cell2798.sound htau (by
                    simp only [Batch0349.cell2798, Batch0349.tau2798, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01101222 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-121/320 : ℝ) with hy0110122 | hy0110122
                · have hs01101221 : InSquare (-9/128) (-243/640) (1/640) tau := by
                    convert childLR hs0110122 hx0110122 hy0110122 using 1 <;> norm_num
                  exact Batch0349.cell2797.sound htau (by
                    simp only [Batch0349.cell2797, Batch0349.tau2797, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01101221 (by positivity) using 1 <;> norm_num)
                · have hs01101223 : InSquare (-9/128) (-241/640) (1/640) tau := by
                    convert childUR hs0110122 hx0110122 hy0110122 using 1 <;> norm_num
                  exact Batch0349.cell2799.sound htau (by
                    simp only [Batch0349.cell2799, Batch0349.tau2799, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01101223 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-61/160 : ℝ) with hy011012 | hy011012
            · have hs0110121 : InSquare (-21/320) (-123/320) (1/320) tau := by
                convert childLR hs011012 hx011012 hy011012 using 1 <;> norm_num
              rcases le_total tau.re (-21/320 : ℝ) with hx0110121 | hx0110121
              · rcases le_total tau.im (-123/320 : ℝ) with hy0110121 | hy0110121
                · have hs01101210 : InSquare (-43/640) (-247/640) (1/640) tau := by
                    convert childLL hs0110121 hx0110121 hy0110121 using 1 <;> norm_num
                  exact Batch0349.cell2792.sound htau (by
                    simp only [Batch0349.cell2792, Batch0349.tau2792, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01101210 (by positivity) using 1 <;> norm_num)
                · have hs01101212 : InSquare (-43/640) (-49/128) (1/640) tau := by
                    convert childUL hs0110121 hx0110121 hy0110121 using 1 <;> norm_num
                  exact Batch0349.cell2794.sound htau (by
                    simp only [Batch0349.cell2794, Batch0349.tau2794, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01101212 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-123/320 : ℝ) with hy0110121 | hy0110121
                · have hs01101211 : InSquare (-41/640) (-247/640) (1/640) tau := by
                    convert childLR hs0110121 hx0110121 hy0110121 using 1 <;> norm_num
                  exact Batch0349.cell2793.sound htau (by
                    simp only [Batch0349.cell2793, Batch0349.tau2793, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01101211 (by positivity) using 1 <;> norm_num)
                · have hs01101213 : InSquare (-41/640) (-49/128) (1/640) tau := by
                    convert childUR hs0110121 hx0110121 hy0110121 using 1 <;> norm_num
                  exact Batch0349.cell2795.sound htau (by
                    simp only [Batch0349.cell2795, Batch0349.tau2795, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01101213 (by positivity) using 1 <;> norm_num)
            · have hs0110123 : InSquare (-21/320) (-121/320) (1/320) tau := by
                convert childUR hs011012 hx011012 hy011012 using 1 <;> norm_num
              exact Batch0181.cell1452.sound htau (by
                simp only [Batch0181.cell1452, Batch0181.tau1452, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0110123 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-31/80 : ℝ) with hy01101 | hy01101
        · have hs011011 : InSquare (-9/160) (-63/160) (1/160) tau := by
            convert childLR hs01101 hx01101 hy01101 using 1 <;> norm_num
          rcases le_total tau.re (-9/160 : ℝ) with hx011011 | hx011011
          · rcases le_total tau.im (-63/160 : ℝ) with hy011011 | hy011011
            · have hs0110110 : InSquare (-19/320) (-127/320) (1/320) tau := by
                convert childLL hs011011 hx011011 hy011011 using 1 <;> norm_num
              rcases le_total tau.re (-19/320 : ℝ) with hx0110110 | hx0110110
              · rcases le_total tau.im (-127/320 : ℝ) with hy0110110 | hy0110110
                · have hs01101100 : InSquare (-39/640) (-51/128) (1/640) tau := by
                    convert childLL hs0110110 hx0110110 hy0110110 using 1 <;> norm_num
                  exact (outside_01101100 htau hs01101100).elim
                · have hs01101102 : InSquare (-39/640) (-253/640) (1/640) tau := by
                    convert childUL hs0110110 hx0110110 hy0110110 using 1 <;> norm_num
                  exact Batch0347.cell2776.sound htau (by
                    simp only [Batch0347.cell2776, Batch0347.tau2776, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01101102 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-127/320 : ℝ) with hy0110110 | hy0110110
                · have hs01101101 : InSquare (-37/640) (-51/128) (1/640) tau := by
                    convert childLR hs0110110 hx0110110 hy0110110 using 1 <;> norm_num
                  exact (outside_01101101 htau hs01101101).elim
                · have hs01101103 : InSquare (-37/640) (-253/640) (1/640) tau := by
                    convert childUR hs0110110 hx0110110 hy0110110 using 1 <;> norm_num
                  exact Batch0347.cell2777.sound htau (by
                    simp only [Batch0347.cell2777, Batch0347.tau2777, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01101103 (by positivity) using 1 <;> norm_num)
            · have hs0110112 : InSquare (-19/320) (-25/64) (1/320) tau := by
                convert childUL hs011011 hx011011 hy011011 using 1 <;> norm_num
              rcases le_total tau.re (-19/320 : ℝ) with hx0110112 | hx0110112
              · rcases le_total tau.im (-25/64 : ℝ) with hy0110112 | hy0110112
                · have hs01101120 : InSquare (-39/640) (-251/640) (1/640) tau := by
                    convert childLL hs0110112 hx0110112 hy0110112 using 1 <;> norm_num
                  exact Batch0347.cell2780.sound htau (by
                    simp only [Batch0347.cell2780, Batch0347.tau2780, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01101120 (by positivity) using 1 <;> norm_num)
                · have hs01101122 : InSquare (-39/640) (-249/640) (1/640) tau := by
                    convert childUL hs0110112 hx0110112 hy0110112 using 1 <;> norm_num
                  exact Batch0347.cell2782.sound htau (by
                    simp only [Batch0347.cell2782, Batch0347.tau2782, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01101122 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-25/64 : ℝ) with hy0110112 | hy0110112
                · have hs01101121 : InSquare (-37/640) (-251/640) (1/640) tau := by
                    convert childLR hs0110112 hx0110112 hy0110112 using 1 <;> norm_num
                  exact Batch0347.cell2781.sound htau (by
                    simp only [Batch0347.cell2781, Batch0347.tau2781, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01101121 (by positivity) using 1 <;> norm_num)
                · have hs01101123 : InSquare (-37/640) (-249/640) (1/640) tau := by
                    convert childUR hs0110112 hx0110112 hy0110112 using 1 <;> norm_num
                  exact Batch0347.cell2783.sound htau (by
                    simp only [Batch0347.cell2783, Batch0347.tau2783, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01101123 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-63/160 : ℝ) with hy011011 | hy011011
            · have hs0110111 : InSquare (-17/320) (-127/320) (1/320) tau := by
                convert childLR hs011011 hx011011 hy011011 using 1 <;> norm_num
              rcases le_total tau.re (-17/320 : ℝ) with hx0110111 | hx0110111
              · rcases le_total tau.im (-127/320 : ℝ) with hy0110111 | hy0110111
                · have hs01101110 : InSquare (-7/128) (-51/128) (1/640) tau := by
                    convert childLL hs0110111 hx0110111 hy0110111 using 1 <;> norm_num
                  exact (outside_01101110 htau hs01101110).elim
                · have hs01101112 : InSquare (-7/128) (-253/640) (1/640) tau := by
                    convert childUL hs0110111 hx0110111 hy0110111 using 1 <;> norm_num
                  exact Batch0347.cell2778.sound htau (by
                    simp only [Batch0347.cell2778, Batch0347.tau2778, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01101112 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-127/320 : ℝ) with hy0110111 | hy0110111
                · have hs01101111 : InSquare (-33/640) (-51/128) (1/640) tau := by
                    convert childLR hs0110111 hx0110111 hy0110111 using 1 <;> norm_num
                  exact (outside_01101111 htau hs01101111).elim
                · have hs01101113 : InSquare (-33/640) (-253/640) (1/640) tau := by
                    convert childUR hs0110111 hx0110111 hy0110111 using 1 <;> norm_num
                  exact Batch0347.cell2779.sound htau (by
                    simp only [Batch0347.cell2779, Batch0347.tau2779, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01101113 (by positivity) using 1 <;> norm_num)
            · have hs0110113 : InSquare (-17/320) (-25/64) (1/320) tau := by
                convert childUR hs011011 hx011011 hy011011 using 1 <;> norm_num
              rcases le_total tau.re (-17/320 : ℝ) with hx0110113 | hx0110113
              · rcases le_total tau.im (-25/64 : ℝ) with hy0110113 | hy0110113
                · have hs01101130 : InSquare (-7/128) (-251/640) (1/640) tau := by
                    convert childLL hs0110113 hx0110113 hy0110113 using 1 <;> norm_num
                  exact Batch0348.cell2784.sound htau (by
                    simp only [Batch0348.cell2784, Batch0348.tau2784, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01101130 (by positivity) using 1 <;> norm_num)
                · have hs01101132 : InSquare (-7/128) (-249/640) (1/640) tau := by
                    convert childUL hs0110113 hx0110113 hy0110113 using 1 <;> norm_num
                  exact Batch0348.cell2786.sound htau (by
                    simp only [Batch0348.cell2786, Batch0348.tau2786, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01101132 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-25/64 : ℝ) with hy0110113 | hy0110113
                · have hs01101131 : InSquare (-33/640) (-251/640) (1/640) tau := by
                    convert childLR hs0110113 hx0110113 hy0110113 using 1 <;> norm_num
                  exact Batch0348.cell2785.sound htau (by
                    simp only [Batch0348.cell2785, Batch0348.tau2785, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01101131 (by positivity) using 1 <;> norm_num)
                · have hs01101133 : InSquare (-33/640) (-249/640) (1/640) tau := by
                    convert childUR hs0110113 hx0110113 hy0110113 using 1 <;> norm_num
                  exact Batch0348.cell2787.sound htau (by
                    simp only [Batch0348.cell2787, Batch0348.tau2787, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01101133 (by positivity) using 1 <;> norm_num)
        · have hs011013 : InSquare (-9/160) (-61/160) (1/160) tau := by
            convert childUR hs01101 hx01101 hy01101 using 1 <;> norm_num
          rcases le_total tau.re (-9/160 : ℝ) with hx011013 | hx011013
          · rcases le_total tau.im (-61/160 : ℝ) with hy011013 | hy011013
            · have hs0110130 : InSquare (-19/320) (-123/320) (1/320) tau := by
                convert childLL hs011013 hx011013 hy011013 using 1 <;> norm_num
              rcases le_total tau.re (-19/320 : ℝ) with hx0110130 | hx0110130
              · rcases le_total tau.im (-123/320 : ℝ) with hy0110130 | hy0110130
                · have hs01101300 : InSquare (-39/640) (-247/640) (1/640) tau := by
                    convert childLL hs0110130 hx0110130 hy0110130 using 1 <;> norm_num
                  exact Batch0350.cell2800.sound htau (by
                    simp only [Batch0350.cell2800, Batch0350.tau2800, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01101300 (by positivity) using 1 <;> norm_num)
                · have hs01101302 : InSquare (-39/640) (-49/128) (1/640) tau := by
                    convert childUL hs0110130 hx0110130 hy0110130 using 1 <;> norm_num
                  exact Batch0350.cell2802.sound htau (by
                    simp only [Batch0350.cell2802, Batch0350.tau2802, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01101302 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-123/320 : ℝ) with hy0110130 | hy0110130
                · have hs01101301 : InSquare (-37/640) (-247/640) (1/640) tau := by
                    convert childLR hs0110130 hx0110130 hy0110130 using 1 <;> norm_num
                  exact Batch0350.cell2801.sound htau (by
                    simp only [Batch0350.cell2801, Batch0350.tau2801, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01101301 (by positivity) using 1 <;> norm_num)
                · have hs01101303 : InSquare (-37/640) (-49/128) (1/640) tau := by
                    convert childUR hs0110130 hx0110130 hy0110130 using 1 <;> norm_num
                  exact Batch0350.cell2803.sound htau (by
                    simp only [Batch0350.cell2803, Batch0350.tau2803, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01101303 (by positivity) using 1 <;> norm_num)
            · have hs0110132 : InSquare (-19/320) (-121/320) (1/320) tau := by
                convert childUL hs011013 hx011013 hy011013 using 1 <;> norm_num
              exact Batch0181.cell1453.sound htau (by
                simp only [Batch0181.cell1453, Batch0181.tau1453, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0110132 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-61/160 : ℝ) with hy011013 | hy011013
            · have hs0110131 : InSquare (-17/320) (-123/320) (1/320) tau := by
                convert childLR hs011013 hx011013 hy011013 using 1 <;> norm_num
              rcases le_total tau.re (-17/320 : ℝ) with hx0110131 | hx0110131
              · rcases le_total tau.im (-123/320 : ℝ) with hy0110131 | hy0110131
                · have hs01101310 : InSquare (-7/128) (-247/640) (1/640) tau := by
                    convert childLL hs0110131 hx0110131 hy0110131 using 1 <;> norm_num
                  exact Batch0350.cell2804.sound htau (by
                    simp only [Batch0350.cell2804, Batch0350.tau2804, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01101310 (by positivity) using 1 <;> norm_num)
                · have hs01101312 : InSquare (-7/128) (-49/128) (1/640) tau := by
                    convert childUL hs0110131 hx0110131 hy0110131 using 1 <;> norm_num
                  exact Batch0350.cell2806.sound htau (by
                    simp only [Batch0350.cell2806, Batch0350.tau2806, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01101312 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-123/320 : ℝ) with hy0110131 | hy0110131
                · have hs01101311 : InSquare (-33/640) (-247/640) (1/640) tau := by
                    convert childLR hs0110131 hx0110131 hy0110131 using 1 <;> norm_num
                  exact Batch0350.cell2805.sound htau (by
                    simp only [Batch0350.cell2805, Batch0350.tau2805, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01101311 (by positivity) using 1 <;> norm_num)
                · have hs01101313 : InSquare (-33/640) (-49/128) (1/640) tau := by
                    convert childUR hs0110131 hx0110131 hy0110131 using 1 <;> norm_num
                  exact Batch0350.cell2807.sound htau (by
                    simp only [Batch0350.cell2807, Batch0350.tau2807, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01101313 (by positivity) using 1 <;> norm_num)
            · have hs0110133 : InSquare (-17/320) (-121/320) (1/320) tau := by
                convert childUR hs011013 hx011013 hy011013 using 1 <;> norm_num
              exact Batch0181.cell1454.sound htau (by
                simp only [Batch0181.cell1454, Batch0181.tau1454, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0110133 (by positivity) using 1 <;> norm_num)
    · have hs01103 : InSquare (-1/16) (-29/80) (1/80) tau := by
        convert childUR hs hx0110 hy0110 using 1 <;> norm_num
      rcases le_total tau.re (-1/16 : ℝ) with hx01103 | hx01103
      · rcases le_total tau.im (-29/80 : ℝ) with hy01103 | hy01103
        · have hs011030 : InSquare (-11/160) (-59/160) (1/160) tau := by
            convert childLL hs01103 hx01103 hy01103 using 1 <;> norm_num
          rcases le_total tau.re (-11/160 : ℝ) with hx011030 | hx011030
          · rcases le_total tau.im (-59/160 : ℝ) with hy011030 | hy011030
            · have hs0110300 : InSquare (-23/320) (-119/320) (1/320) tau := by
                convert childLL hs011030 hx011030 hy011030 using 1 <;> norm_num
              exact Batch0183.cell1471.sound htau (by
                simp only [Batch0183.cell1471, Batch0183.tau1471, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0110300 (by positivity) using 1 <;> norm_num)
            · have hs0110302 : InSquare (-23/320) (-117/320) (1/320) tau := by
                convert childUL hs011030 hx011030 hy011030 using 1 <;> norm_num
              exact Batch0184.cell1473.sound htau (by
                simp only [Batch0184.cell1473, Batch0184.tau1473, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0110302 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-59/160 : ℝ) with hy011030 | hy011030
            · have hs0110301 : InSquare (-21/320) (-119/320) (1/320) tau := by
                convert childLR hs011030 hx011030 hy011030 using 1 <;> norm_num
              exact Batch0184.cell1472.sound htau (by
                simp only [Batch0184.cell1472, Batch0184.tau1472, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0110301 (by positivity) using 1 <;> norm_num)
            · have hs0110303 : InSquare (-21/320) (-117/320) (1/320) tau := by
                convert childUR hs011030 hx011030 hy011030 using 1 <;> norm_num
              exact Batch0184.cell1474.sound htau (by
                simp only [Batch0184.cell1474, Batch0184.tau1474, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0110303 (by positivity) using 1 <;> norm_num)
        · have hs011032 : InSquare (-11/160) (-57/160) (1/160) tau := by
            convert childUL hs01103 hx01103 hy01103 using 1 <;> norm_num
          rcases le_total tau.re (-11/160 : ℝ) with hx011032 | hx011032
          · rcases le_total tau.im (-57/160 : ℝ) with hy011032 | hy011032
            · have hs0110320 : InSquare (-23/320) (-23/64) (1/320) tau := by
                convert childLL hs011032 hx011032 hy011032 using 1 <;> norm_num
              exact Batch0184.cell1479.sound htau (by
                simp only [Batch0184.cell1479, Batch0184.tau1479, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0110320 (by positivity) using 1 <;> norm_num)
            · have hs0110322 : InSquare (-23/320) (-113/320) (1/320) tau := by
                convert childUL hs011032 hx011032 hy011032 using 1 <;> norm_num
              exact Batch0185.cell1481.sound htau (by
                simp only [Batch0185.cell1481, Batch0185.tau1481, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0110322 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-57/160 : ℝ) with hy011032 | hy011032
            · have hs0110321 : InSquare (-21/320) (-23/64) (1/320) tau := by
                convert childLR hs011032 hx011032 hy011032 using 1 <;> norm_num
              exact Batch0185.cell1480.sound htau (by
                simp only [Batch0185.cell1480, Batch0185.tau1480, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0110321 (by positivity) using 1 <;> norm_num)
            · have hs0110323 : InSquare (-21/320) (-113/320) (1/320) tau := by
                convert childUR hs011032 hx011032 hy011032 using 1 <;> norm_num
              exact Batch0185.cell1482.sound htau (by
                simp only [Batch0185.cell1482, Batch0185.tau1482, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0110323 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-29/80 : ℝ) with hy01103 | hy01103
        · have hs011031 : InSquare (-9/160) (-59/160) (1/160) tau := by
            convert childLR hs01103 hx01103 hy01103 using 1 <;> norm_num
          rcases le_total tau.re (-9/160 : ℝ) with hx011031 | hx011031
          · rcases le_total tau.im (-59/160 : ℝ) with hy011031 | hy011031
            · have hs0110310 : InSquare (-19/320) (-119/320) (1/320) tau := by
                convert childLL hs011031 hx011031 hy011031 using 1 <;> norm_num
              exact Batch0184.cell1475.sound htau (by
                simp only [Batch0184.cell1475, Batch0184.tau1475, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0110310 (by positivity) using 1 <;> norm_num)
            · have hs0110312 : InSquare (-19/320) (-117/320) (1/320) tau := by
                convert childUL hs011031 hx011031 hy011031 using 1 <;> norm_num
              exact Batch0184.cell1477.sound htau (by
                simp only [Batch0184.cell1477, Batch0184.tau1477, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0110312 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-59/160 : ℝ) with hy011031 | hy011031
            · have hs0110311 : InSquare (-17/320) (-119/320) (1/320) tau := by
                convert childLR hs011031 hx011031 hy011031 using 1 <;> norm_num
              exact Batch0184.cell1476.sound htau (by
                simp only [Batch0184.cell1476, Batch0184.tau1476, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0110311 (by positivity) using 1 <;> norm_num)
            · have hs0110313 : InSquare (-17/320) (-117/320) (1/320) tau := by
                convert childUR hs011031 hx011031 hy011031 using 1 <;> norm_num
              exact Batch0184.cell1478.sound htau (by
                simp only [Batch0184.cell1478, Batch0184.tau1478, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0110313 (by positivity) using 1 <;> norm_num)
        · have hs011033 : InSquare (-9/160) (-57/160) (1/160) tau := by
            convert childUR hs01103 hx01103 hy01103 using 1 <;> norm_num
          rcases le_total tau.re (-9/160 : ℝ) with hx011033 | hx011033
          · rcases le_total tau.im (-57/160 : ℝ) with hy011033 | hy011033
            · have hs0110330 : InSquare (-19/320) (-23/64) (1/320) tau := by
                convert childLL hs011033 hx011033 hy011033 using 1 <;> norm_num
              exact Batch0185.cell1483.sound htau (by
                simp only [Batch0185.cell1483, Batch0185.tau1483, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0110330 (by positivity) using 1 <;> norm_num)
            · have hs0110332 : InSquare (-19/320) (-113/320) (1/320) tau := by
                convert childUL hs011033 hx011033 hy011033 using 1 <;> norm_num
              exact Batch0185.cell1485.sound htau (by
                simp only [Batch0185.cell1485, Batch0185.tau1485, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0110332 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-57/160 : ℝ) with hy011033 | hy011033
            · have hs0110331 : InSquare (-17/320) (-23/64) (1/320) tau := by
                convert childLR hs011033 hx011033 hy011033 using 1 <;> norm_num
              exact Batch0185.cell1484.sound htau (by
                simp only [Batch0185.cell1484, Batch0185.tau1484, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0110331 (by positivity) using 1 <;> norm_num)
            · have hs0110333 : InSquare (-17/320) (-113/320) (1/320) tau := by
                convert childUR hs011033 hx011033 hy011033 using 1 <;> norm_num
              exact Batch0185.cell1486.sound htau (by
                simp only [Batch0185.cell1486, Batch0185.tau1486, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0110333 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0110
