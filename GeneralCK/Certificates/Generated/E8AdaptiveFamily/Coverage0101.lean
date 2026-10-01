import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0168
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0169
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0170
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0328
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0329
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0330
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0331
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0332
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0333
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0334
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0335
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0336
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0337
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0338
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0339

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0101

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

private theorem outside_010100 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-23/160) (-63/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (11/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+11/80)]
  have himSq : (31/80 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+31/80)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_010101 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-21/160) (-63/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (1/8 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+1/8)]
  have himSq : (31/80 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+31/80)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_010110 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-19/160) (-63/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (9/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+9/80)]
  have himSq : (31/80 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+31/80)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_010111 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-17/160) (-63/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (1/10 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+1/10)]
  have himSq : (31/80 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+31/80)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_0101020 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-47/320) (-123/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (23/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+23/160)]
  have himSq : (61/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+61/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_0101021 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-9/64) (-123/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (11/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+11/80)]
  have himSq : (61/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+61/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_0101022 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-47/320) (-121/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (23/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+23/160)]
  have himSq : (3/8 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+3/8)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_0101030 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-43/320) (-123/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (21/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+21/160)]
  have himSq : (61/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+61/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_0101031 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-41/320) (-123/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (1/8 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+1/8)]
  have himSq : (61/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+61/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_01010230 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-91/640) (-243/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (9/64 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+9/64)]
  have himSq : (121/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+121/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_01010231 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-89/640) (-243/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (11/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+11/80)]
  have himSq : (121/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+121/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_01010232 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-91/640) (-241/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (9/64 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+9/64)]
  have himSq : (3/8 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+3/8)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_01010320 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-87/640) (-243/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (43/320 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+43/320)]
  have himSq : (121/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+121/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_01010321 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-17/128) (-243/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (21/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+21/160)]
  have himSq : (121/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+121/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_01011200 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-79/640) (-247/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (39/320 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+39/320)]
  have himSq : (123/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+123/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_01011201 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-77/640) (-247/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (19/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+19/160)]
  have himSq : (123/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+123/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_01011202 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-79/640) (-49/128) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (39/320 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+39/320)]
  have himSq : (61/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+61/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_01011210 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-15/128) (-247/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (37/320 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+37/320)]
  have himSq : (123/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+123/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_01011211 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-73/640) (-247/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (9/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+9/80)]
  have himSq : (123/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+123/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-1/8) (-3/8) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (-1/8 : ℝ) with hx0101 | hx0101
  · rcases le_total tau.im (-3/8 : ℝ) with hy0101 | hy0101
    · have hs01010 : InSquare (-11/80) (-31/80) (1/80) tau := by
        convert childLL hs hx0101 hy0101 using 1 <;> norm_num
      rcases le_total tau.re (-11/80 : ℝ) with hx01010 | hx01010
      · rcases le_total tau.im (-31/80 : ℝ) with hy01010 | hy01010
        · have hs010100 : InSquare (-23/160) (-63/160) (1/160) tau := by
            convert childLL hs01010 hx01010 hy01010 using 1 <;> norm_num
          exact (outside_010100 htau hs010100).elim
        · have hs010102 : InSquare (-23/160) (-61/160) (1/160) tau := by
            convert childUL hs01010 hx01010 hy01010 using 1 <;> norm_num
          rcases le_total tau.re (-23/160 : ℝ) with hx010102 | hx010102
          · rcases le_total tau.im (-61/160 : ℝ) with hy010102 | hy010102
            · have hs0101020 : InSquare (-47/320) (-123/320) (1/320) tau := by
                convert childLL hs010102 hx010102 hy010102 using 1 <;> norm_num
              exact (outside_0101020 htau hs0101020).elim
            · have hs0101022 : InSquare (-47/320) (-121/320) (1/320) tau := by
                convert childUL hs010102 hx010102 hy010102 using 1 <;> norm_num
              exact (outside_0101022 htau hs0101022).elim
          · rcases le_total tau.im (-61/160 : ℝ) with hy010102 | hy010102
            · have hs0101021 : InSquare (-9/64) (-123/320) (1/320) tau := by
                convert childLR hs010102 hx010102 hy010102 using 1 <;> norm_num
              exact (outside_0101021 htau hs0101021).elim
            · have hs0101023 : InSquare (-9/64) (-121/320) (1/320) tau := by
                convert childUR hs010102 hx010102 hy010102 using 1 <;> norm_num
              rcases le_total tau.re (-9/64 : ℝ) with hx0101023 | hx0101023
              · rcases le_total tau.im (-121/320 : ℝ) with hy0101023 | hy0101023
                · have hs01010230 : InSquare (-91/640) (-243/640) (1/640) tau := by
                    convert childLL hs0101023 hx0101023 hy0101023 using 1 <;> norm_num
                  exact (outside_01010230 htau hs01010230).elim
                · have hs01010232 : InSquare (-91/640) (-241/640) (1/640) tau := by
                    convert childUL hs0101023 hx0101023 hy0101023 using 1 <;> norm_num
                  exact (outside_01010232 htau hs01010232).elim
              · rcases le_total tau.im (-121/320 : ℝ) with hy0101023 | hy0101023
                · have hs01010231 : InSquare (-89/640) (-243/640) (1/640) tau := by
                    convert childLR hs0101023 hx0101023 hy0101023 using 1 <;> norm_num
                  exact (outside_01010231 htau hs01010231).elim
                · have hs01010233 : InSquare (-89/640) (-241/640) (1/640) tau := by
                    convert childUR hs0101023 hx0101023 hy0101023 using 1 <;> norm_num
                  exact Batch0328.cell2627.sound htau (by
                    simp only [Batch0328.cell2627, Batch0328.tau2627, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01010233 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-31/80 : ℝ) with hy01010 | hy01010
        · have hs010101 : InSquare (-21/160) (-63/160) (1/160) tau := by
            convert childLR hs01010 hx01010 hy01010 using 1 <;> norm_num
          exact (outside_010101 htau hs010101).elim
        · have hs010103 : InSquare (-21/160) (-61/160) (1/160) tau := by
            convert childUR hs01010 hx01010 hy01010 using 1 <;> norm_num
          rcases le_total tau.re (-21/160 : ℝ) with hx010103 | hx010103
          · rcases le_total tau.im (-61/160 : ℝ) with hy010103 | hy010103
            · have hs0101030 : InSquare (-43/320) (-123/320) (1/320) tau := by
                convert childLL hs010103 hx010103 hy010103 using 1 <;> norm_num
              exact (outside_0101030 htau hs0101030).elim
            · have hs0101032 : InSquare (-43/320) (-121/320) (1/320) tau := by
                convert childUL hs010103 hx010103 hy010103 using 1 <;> norm_num
              rcases le_total tau.re (-43/320 : ℝ) with hx0101032 | hx0101032
              · rcases le_total tau.im (-121/320 : ℝ) with hy0101032 | hy0101032
                · have hs01010320 : InSquare (-87/640) (-243/640) (1/640) tau := by
                    convert childLL hs0101032 hx0101032 hy0101032 using 1 <;> norm_num
                  exact (outside_01010320 htau hs01010320).elim
                · have hs01010322 : InSquare (-87/640) (-241/640) (1/640) tau := by
                    convert childUL hs0101032 hx0101032 hy0101032 using 1 <;> norm_num
                  exact Batch0328.cell2628.sound htau (by
                    simp only [Batch0328.cell2628, Batch0328.tau2628, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01010322 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-121/320 : ℝ) with hy0101032 | hy0101032
                · have hs01010321 : InSquare (-17/128) (-243/640) (1/640) tau := by
                    convert childLR hs0101032 hx0101032 hy0101032 using 1 <;> norm_num
                  exact (outside_01010321 htau hs01010321).elim
                · have hs01010323 : InSquare (-17/128) (-241/640) (1/640) tau := by
                    convert childUR hs0101032 hx0101032 hy0101032 using 1 <;> norm_num
                  exact Batch0328.cell2629.sound htau (by
                    simp only [Batch0328.cell2629, Batch0328.tau2629, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01010323 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-61/160 : ℝ) with hy010103 | hy010103
            · have hs0101031 : InSquare (-41/320) (-123/320) (1/320) tau := by
                convert childLR hs010103 hx010103 hy010103 using 1 <;> norm_num
              exact (outside_0101031 htau hs0101031).elim
            · have hs0101033 : InSquare (-41/320) (-121/320) (1/320) tau := by
                convert childUR hs010103 hx010103 hy010103 using 1 <;> norm_num
              rcases le_total tau.re (-41/320 : ℝ) with hx0101033 | hx0101033
              · rcases le_total tau.im (-121/320 : ℝ) with hy0101033 | hy0101033
                · have hs01010330 : InSquare (-83/640) (-243/640) (1/640) tau := by
                    convert childLL hs0101033 hx0101033 hy0101033 using 1 <;> norm_num
                  exact Batch0328.cell2630.sound htau (by
                    simp only [Batch0328.cell2630, Batch0328.tau2630, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01010330 (by positivity) using 1 <;> norm_num)
                · have hs01010332 : InSquare (-83/640) (-241/640) (1/640) tau := by
                    convert childUL hs0101033 hx0101033 hy0101033 using 1 <;> norm_num
                  exact Batch0329.cell2632.sound htau (by
                    simp only [Batch0329.cell2632, Batch0329.tau2632, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01010332 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-121/320 : ℝ) with hy0101033 | hy0101033
                · have hs01010331 : InSquare (-81/640) (-243/640) (1/640) tau := by
                    convert childLR hs0101033 hx0101033 hy0101033 using 1 <;> norm_num
                  exact Batch0328.cell2631.sound htau (by
                    simp only [Batch0328.cell2631, Batch0328.tau2631, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01010331 (by positivity) using 1 <;> norm_num)
                · have hs01010333 : InSquare (-81/640) (-241/640) (1/640) tau := by
                    convert childUR hs0101033 hx0101033 hy0101033 using 1 <;> norm_num
                  exact Batch0329.cell2633.sound htau (by
                    simp only [Batch0329.cell2633, Batch0329.tau2633, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01010333 (by positivity) using 1 <;> norm_num)
    · have hs01012 : InSquare (-11/80) (-29/80) (1/80) tau := by
        convert childUL hs hx0101 hy0101 using 1 <;> norm_num
      rcases le_total tau.re (-11/80 : ℝ) with hx01012 | hx01012
      · rcases le_total tau.im (-29/80 : ℝ) with hy01012 | hy01012
        · have hs010120 : InSquare (-23/160) (-59/160) (1/160) tau := by
            convert childLL hs01012 hx01012 hy01012 using 1 <;> norm_num
          rcases le_total tau.re (-23/160 : ℝ) with hx010120 | hx010120
          · rcases le_total tau.im (-59/160 : ℝ) with hy010120 | hy010120
            · have hs0101200 : InSquare (-47/320) (-119/320) (1/320) tau := by
                convert childLL hs010120 hx010120 hy010120 using 1 <;> norm_num
              rcases le_total tau.re (-47/320 : ℝ) with hx0101200 | hx0101200
              · rcases le_total tau.im (-119/320 : ℝ) with hy0101200 | hy0101200
                · have hs01012000 : InSquare (-19/128) (-239/640) (1/640) tau := by
                    convert childLL hs0101200 hx0101200 hy0101200 using 1 <;> norm_num
                  exact Batch0332.cell2661.sound htau (by
                    simp only [Batch0332.cell2661, Batch0332.tau2661, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01012000 (by positivity) using 1 <;> norm_num)
                · have hs01012002 : InSquare (-19/128) (-237/640) (1/640) tau := by
                    convert childUL hs0101200 hx0101200 hy0101200 using 1 <;> norm_num
                  exact Batch0332.cell2663.sound htau (by
                    simp only [Batch0332.cell2663, Batch0332.tau2663, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01012002 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-119/320 : ℝ) with hy0101200 | hy0101200
                · have hs01012001 : InSquare (-93/640) (-239/640) (1/640) tau := by
                    convert childLR hs0101200 hx0101200 hy0101200 using 1 <;> norm_num
                  exact Batch0332.cell2662.sound htau (by
                    simp only [Batch0332.cell2662, Batch0332.tau2662, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01012001 (by positivity) using 1 <;> norm_num)
                · have hs01012003 : InSquare (-93/640) (-237/640) (1/640) tau := by
                    convert childUR hs0101200 hx0101200 hy0101200 using 1 <;> norm_num
                  exact Batch0333.cell2664.sound htau (by
                    simp only [Batch0333.cell2664, Batch0333.tau2664, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01012003 (by positivity) using 1 <;> norm_num)
            · have hs0101202 : InSquare (-47/320) (-117/320) (1/320) tau := by
                convert childUL hs010120 hx010120 hy010120 using 1 <;> norm_num
              rcases le_total tau.re (-47/320 : ℝ) with hx0101202 | hx0101202
              · rcases le_total tau.im (-117/320 : ℝ) with hy0101202 | hy0101202
                · have hs01012020 : InSquare (-19/128) (-47/128) (1/640) tau := by
                    convert childLL hs0101202 hx0101202 hy0101202 using 1 <;> norm_num
                  exact Batch0333.cell2669.sound htau (by
                    simp only [Batch0333.cell2669, Batch0333.tau2669, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01012020 (by positivity) using 1 <;> norm_num)
                · have hs01012022 : InSquare (-19/128) (-233/640) (1/640) tau := by
                    convert childUL hs0101202 hx0101202 hy0101202 using 1 <;> norm_num
                  exact Batch0333.cell2671.sound htau (by
                    simp only [Batch0333.cell2671, Batch0333.tau2671, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01012022 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-117/320 : ℝ) with hy0101202 | hy0101202
                · have hs01012021 : InSquare (-93/640) (-47/128) (1/640) tau := by
                    convert childLR hs0101202 hx0101202 hy0101202 using 1 <;> norm_num
                  exact Batch0333.cell2670.sound htau (by
                    simp only [Batch0333.cell2670, Batch0333.tau2670, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01012021 (by positivity) using 1 <;> norm_num)
                · have hs01012023 : InSquare (-93/640) (-233/640) (1/640) tau := by
                    convert childUR hs0101202 hx0101202 hy0101202 using 1 <;> norm_num
                  exact Batch0334.cell2672.sound htau (by
                    simp only [Batch0334.cell2672, Batch0334.tau2672, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01012023 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-59/160 : ℝ) with hy010120 | hy010120
            · have hs0101201 : InSquare (-9/64) (-119/320) (1/320) tau := by
                convert childLR hs010120 hx010120 hy010120 using 1 <;> norm_num
              rcases le_total tau.re (-9/64 : ℝ) with hx0101201 | hx0101201
              · rcases le_total tau.im (-119/320 : ℝ) with hy0101201 | hy0101201
                · have hs01012010 : InSquare (-91/640) (-239/640) (1/640) tau := by
                    convert childLL hs0101201 hx0101201 hy0101201 using 1 <;> norm_num
                  exact Batch0333.cell2665.sound htau (by
                    simp only [Batch0333.cell2665, Batch0333.tau2665, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01012010 (by positivity) using 1 <;> norm_num)
                · have hs01012012 : InSquare (-91/640) (-237/640) (1/640) tau := by
                    convert childUL hs0101201 hx0101201 hy0101201 using 1 <;> norm_num
                  exact Batch0333.cell2667.sound htau (by
                    simp only [Batch0333.cell2667, Batch0333.tau2667, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01012012 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-119/320 : ℝ) with hy0101201 | hy0101201
                · have hs01012011 : InSquare (-89/640) (-239/640) (1/640) tau := by
                    convert childLR hs0101201 hx0101201 hy0101201 using 1 <;> norm_num
                  exact Batch0333.cell2666.sound htau (by
                    simp only [Batch0333.cell2666, Batch0333.tau2666, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01012011 (by positivity) using 1 <;> norm_num)
                · have hs01012013 : InSquare (-89/640) (-237/640) (1/640) tau := by
                    convert childUR hs0101201 hx0101201 hy0101201 using 1 <;> norm_num
                  exact Batch0333.cell2668.sound htau (by
                    simp only [Batch0333.cell2668, Batch0333.tau2668, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01012013 (by positivity) using 1 <;> norm_num)
            · have hs0101203 : InSquare (-9/64) (-117/320) (1/320) tau := by
                convert childUR hs010120 hx010120 hy010120 using 1 <;> norm_num
              rcases le_total tau.re (-9/64 : ℝ) with hx0101203 | hx0101203
              · rcases le_total tau.im (-117/320 : ℝ) with hy0101203 | hy0101203
                · have hs01012030 : InSquare (-91/640) (-47/128) (1/640) tau := by
                    convert childLL hs0101203 hx0101203 hy0101203 using 1 <;> norm_num
                  exact Batch0334.cell2673.sound htau (by
                    simp only [Batch0334.cell2673, Batch0334.tau2673, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01012030 (by positivity) using 1 <;> norm_num)
                · have hs01012032 : InSquare (-91/640) (-233/640) (1/640) tau := by
                    convert childUL hs0101203 hx0101203 hy0101203 using 1 <;> norm_num
                  exact Batch0334.cell2675.sound htau (by
                    simp only [Batch0334.cell2675, Batch0334.tau2675, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01012032 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-117/320 : ℝ) with hy0101203 | hy0101203
                · have hs01012031 : InSquare (-89/640) (-47/128) (1/640) tau := by
                    convert childLR hs0101203 hx0101203 hy0101203 using 1 <;> norm_num
                  exact Batch0334.cell2674.sound htau (by
                    simp only [Batch0334.cell2674, Batch0334.tau2674, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01012031 (by positivity) using 1 <;> norm_num)
                · have hs01012033 : InSquare (-89/640) (-233/640) (1/640) tau := by
                    convert childUR hs0101203 hx0101203 hy0101203 using 1 <;> norm_num
                  exact Batch0334.cell2676.sound htau (by
                    simp only [Batch0334.cell2676, Batch0334.tau2676, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01012033 (by positivity) using 1 <;> norm_num)
        · have hs010122 : InSquare (-23/160) (-57/160) (1/160) tau := by
            convert childUL hs01012 hx01012 hy01012 using 1 <;> norm_num
          rcases le_total tau.re (-23/160 : ℝ) with hx010122 | hx010122
          · rcases le_total tau.im (-57/160 : ℝ) with hy010122 | hy010122
            · have hs0101220 : InSquare (-47/320) (-23/64) (1/320) tau := by
                convert childLL hs010122 hx010122 hy010122 using 1 <;> norm_num
              rcases le_total tau.re (-47/320 : ℝ) with hx0101220 | hx0101220
              · rcases le_total tau.im (-23/64 : ℝ) with hy0101220 | hy0101220
                · have hs01012200 : InSquare (-19/128) (-231/640) (1/640) tau := by
                    convert childLL hs0101220 hx0101220 hy0101220 using 1 <;> norm_num
                  exact Batch0336.cell2693.sound htau (by
                    simp only [Batch0336.cell2693, Batch0336.tau2693, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01012200 (by positivity) using 1 <;> norm_num)
                · have hs01012202 : InSquare (-19/128) (-229/640) (1/640) tau := by
                    convert childUL hs0101220 hx0101220 hy0101220 using 1 <;> norm_num
                  exact Batch0336.cell2695.sound htau (by
                    simp only [Batch0336.cell2695, Batch0336.tau2695, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01012202 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-23/64 : ℝ) with hy0101220 | hy0101220
                · have hs01012201 : InSquare (-93/640) (-231/640) (1/640) tau := by
                    convert childLR hs0101220 hx0101220 hy0101220 using 1 <;> norm_num
                  exact Batch0336.cell2694.sound htau (by
                    simp only [Batch0336.cell2694, Batch0336.tau2694, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01012201 (by positivity) using 1 <;> norm_num)
                · have hs01012203 : InSquare (-93/640) (-229/640) (1/640) tau := by
                    convert childUR hs0101220 hx0101220 hy0101220 using 1 <;> norm_num
                  exact Batch0337.cell2696.sound htau (by
                    simp only [Batch0337.cell2696, Batch0337.tau2696, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01012203 (by positivity) using 1 <;> norm_num)
            · have hs0101222 : InSquare (-47/320) (-113/320) (1/320) tau := by
                convert childUL hs010122 hx010122 hy010122 using 1 <;> norm_num
              exact Batch0168.cell1348.sound htau (by
                simp only [Batch0168.cell1348, Batch0168.tau1348, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0101222 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-57/160 : ℝ) with hy010122 | hy010122
            · have hs0101221 : InSquare (-9/64) (-23/64) (1/320) tau := by
                convert childLR hs010122 hx010122 hy010122 using 1 <;> norm_num
              exact Batch0168.cell1347.sound htau (by
                simp only [Batch0168.cell1347, Batch0168.tau1347, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0101221 (by positivity) using 1 <;> norm_num)
            · have hs0101223 : InSquare (-9/64) (-113/320) (1/320) tau := by
                convert childUR hs010122 hx010122 hy010122 using 1 <;> norm_num
              exact Batch0168.cell1349.sound htau (by
                simp only [Batch0168.cell1349, Batch0168.tau1349, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0101223 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-29/80 : ℝ) with hy01012 | hy01012
        · have hs010121 : InSquare (-21/160) (-59/160) (1/160) tau := by
            convert childLR hs01012 hx01012 hy01012 using 1 <;> norm_num
          rcases le_total tau.re (-21/160 : ℝ) with hx010121 | hx010121
          · rcases le_total tau.im (-59/160 : ℝ) with hy010121 | hy010121
            · have hs0101210 : InSquare (-43/320) (-119/320) (1/320) tau := by
                convert childLL hs010121 hx010121 hy010121 using 1 <;> norm_num
              rcases le_total tau.re (-43/320 : ℝ) with hx0101210 | hx0101210
              · rcases le_total tau.im (-119/320 : ℝ) with hy0101210 | hy0101210
                · have hs01012100 : InSquare (-87/640) (-239/640) (1/640) tau := by
                    convert childLL hs0101210 hx0101210 hy0101210 using 1 <;> norm_num
                  exact Batch0334.cell2677.sound htau (by
                    simp only [Batch0334.cell2677, Batch0334.tau2677, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01012100 (by positivity) using 1 <;> norm_num)
                · have hs01012102 : InSquare (-87/640) (-237/640) (1/640) tau := by
                    convert childUL hs0101210 hx0101210 hy0101210 using 1 <;> norm_num
                  exact Batch0334.cell2679.sound htau (by
                    simp only [Batch0334.cell2679, Batch0334.tau2679, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01012102 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-119/320 : ℝ) with hy0101210 | hy0101210
                · have hs01012101 : InSquare (-17/128) (-239/640) (1/640) tau := by
                    convert childLR hs0101210 hx0101210 hy0101210 using 1 <;> norm_num
                  exact Batch0334.cell2678.sound htau (by
                    simp only [Batch0334.cell2678, Batch0334.tau2678, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01012101 (by positivity) using 1 <;> norm_num)
                · have hs01012103 : InSquare (-17/128) (-237/640) (1/640) tau := by
                    convert childUR hs0101210 hx0101210 hy0101210 using 1 <;> norm_num
                  exact Batch0335.cell2680.sound htau (by
                    simp only [Batch0335.cell2680, Batch0335.tau2680, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01012103 (by positivity) using 1 <;> norm_num)
            · have hs0101212 : InSquare (-43/320) (-117/320) (1/320) tau := by
                convert childUL hs010121 hx010121 hy010121 using 1 <;> norm_num
              rcases le_total tau.re (-43/320 : ℝ) with hx0101212 | hx0101212
              · rcases le_total tau.im (-117/320 : ℝ) with hy0101212 | hy0101212
                · have hs01012120 : InSquare (-87/640) (-47/128) (1/640) tau := by
                    convert childLL hs0101212 hx0101212 hy0101212 using 1 <;> norm_num
                  exact Batch0335.cell2685.sound htau (by
                    simp only [Batch0335.cell2685, Batch0335.tau2685, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01012120 (by positivity) using 1 <;> norm_num)
                · have hs01012122 : InSquare (-87/640) (-233/640) (1/640) tau := by
                    convert childUL hs0101212 hx0101212 hy0101212 using 1 <;> norm_num
                  exact Batch0335.cell2687.sound htau (by
                    simp only [Batch0335.cell2687, Batch0335.tau2687, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01012122 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-117/320 : ℝ) with hy0101212 | hy0101212
                · have hs01012121 : InSquare (-17/128) (-47/128) (1/640) tau := by
                    convert childLR hs0101212 hx0101212 hy0101212 using 1 <;> norm_num
                  exact Batch0335.cell2686.sound htau (by
                    simp only [Batch0335.cell2686, Batch0335.tau2686, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01012121 (by positivity) using 1 <;> norm_num)
                · have hs01012123 : InSquare (-17/128) (-233/640) (1/640) tau := by
                    convert childUR hs0101212 hx0101212 hy0101212 using 1 <;> norm_num
                  exact Batch0336.cell2688.sound htau (by
                    simp only [Batch0336.cell2688, Batch0336.tau2688, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01012123 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-59/160 : ℝ) with hy010121 | hy010121
            · have hs0101211 : InSquare (-41/320) (-119/320) (1/320) tau := by
                convert childLR hs010121 hx010121 hy010121 using 1 <;> norm_num
              rcases le_total tau.re (-41/320 : ℝ) with hx0101211 | hx0101211
              · rcases le_total tau.im (-119/320 : ℝ) with hy0101211 | hy0101211
                · have hs01012110 : InSquare (-83/640) (-239/640) (1/640) tau := by
                    convert childLL hs0101211 hx0101211 hy0101211 using 1 <;> norm_num
                  exact Batch0335.cell2681.sound htau (by
                    simp only [Batch0335.cell2681, Batch0335.tau2681, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01012110 (by positivity) using 1 <;> norm_num)
                · have hs01012112 : InSquare (-83/640) (-237/640) (1/640) tau := by
                    convert childUL hs0101211 hx0101211 hy0101211 using 1 <;> norm_num
                  exact Batch0335.cell2683.sound htau (by
                    simp only [Batch0335.cell2683, Batch0335.tau2683, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01012112 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-119/320 : ℝ) with hy0101211 | hy0101211
                · have hs01012111 : InSquare (-81/640) (-239/640) (1/640) tau := by
                    convert childLR hs0101211 hx0101211 hy0101211 using 1 <;> norm_num
                  exact Batch0335.cell2682.sound htau (by
                    simp only [Batch0335.cell2682, Batch0335.tau2682, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01012111 (by positivity) using 1 <;> norm_num)
                · have hs01012113 : InSquare (-81/640) (-237/640) (1/640) tau := by
                    convert childUR hs0101211 hx0101211 hy0101211 using 1 <;> norm_num
                  exact Batch0335.cell2684.sound htau (by
                    simp only [Batch0335.cell2684, Batch0335.tau2684, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01012113 (by positivity) using 1 <;> norm_num)
            · have hs0101213 : InSquare (-41/320) (-117/320) (1/320) tau := by
                convert childUR hs010121 hx010121 hy010121 using 1 <;> norm_num
              rcases le_total tau.re (-41/320 : ℝ) with hx0101213 | hx0101213
              · rcases le_total tau.im (-117/320 : ℝ) with hy0101213 | hy0101213
                · have hs01012130 : InSquare (-83/640) (-47/128) (1/640) tau := by
                    convert childLL hs0101213 hx0101213 hy0101213 using 1 <;> norm_num
                  exact Batch0336.cell2689.sound htau (by
                    simp only [Batch0336.cell2689, Batch0336.tau2689, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01012130 (by positivity) using 1 <;> norm_num)
                · have hs01012132 : InSquare (-83/640) (-233/640) (1/640) tau := by
                    convert childUL hs0101213 hx0101213 hy0101213 using 1 <;> norm_num
                  exact Batch0336.cell2691.sound htau (by
                    simp only [Batch0336.cell2691, Batch0336.tau2691, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01012132 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-117/320 : ℝ) with hy0101213 | hy0101213
                · have hs01012131 : InSquare (-81/640) (-47/128) (1/640) tau := by
                    convert childLR hs0101213 hx0101213 hy0101213 using 1 <;> norm_num
                  exact Batch0336.cell2690.sound htau (by
                    simp only [Batch0336.cell2690, Batch0336.tau2690, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01012131 (by positivity) using 1 <;> norm_num)
                · have hs01012133 : InSquare (-81/640) (-233/640) (1/640) tau := by
                    convert childUR hs0101213 hx0101213 hy0101213 using 1 <;> norm_num
                  exact Batch0336.cell2692.sound htau (by
                    simp only [Batch0336.cell2692, Batch0336.tau2692, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01012133 (by positivity) using 1 <;> norm_num)
        · have hs010123 : InSquare (-21/160) (-57/160) (1/160) tau := by
            convert childUR hs01012 hx01012 hy01012 using 1 <;> norm_num
          rcases le_total tau.re (-21/160 : ℝ) with hx010123 | hx010123
          · rcases le_total tau.im (-57/160 : ℝ) with hy010123 | hy010123
            · have hs0101230 : InSquare (-43/320) (-23/64) (1/320) tau := by
                convert childLL hs010123 hx010123 hy010123 using 1 <;> norm_num
              exact Batch0168.cell1350.sound htau (by
                simp only [Batch0168.cell1350, Batch0168.tau1350, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0101230 (by positivity) using 1 <;> norm_num)
            · have hs0101232 : InSquare (-43/320) (-113/320) (1/320) tau := by
                convert childUL hs010123 hx010123 hy010123 using 1 <;> norm_num
              exact Batch0169.cell1352.sound htau (by
                simp only [Batch0169.cell1352, Batch0169.tau1352, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0101232 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-57/160 : ℝ) with hy010123 | hy010123
            · have hs0101231 : InSquare (-41/320) (-23/64) (1/320) tau := by
                convert childLR hs010123 hx010123 hy010123 using 1 <;> norm_num
              exact Batch0168.cell1351.sound htau (by
                simp only [Batch0168.cell1351, Batch0168.tau1351, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0101231 (by positivity) using 1 <;> norm_num)
            · have hs0101233 : InSquare (-41/320) (-113/320) (1/320) tau := by
                convert childUR hs010123 hx010123 hy010123 using 1 <;> norm_num
              exact Batch0169.cell1353.sound htau (by
                simp only [Batch0169.cell1353, Batch0169.tau1353, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0101233 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (-3/8 : ℝ) with hy0101 | hy0101
    · have hs01011 : InSquare (-9/80) (-31/80) (1/80) tau := by
        convert childLR hs hx0101 hy0101 using 1 <;> norm_num
      rcases le_total tau.re (-9/80 : ℝ) with hx01011 | hx01011
      · rcases le_total tau.im (-31/80 : ℝ) with hy01011 | hy01011
        · have hs010110 : InSquare (-19/160) (-63/160) (1/160) tau := by
            convert childLL hs01011 hx01011 hy01011 using 1 <;> norm_num
          exact (outside_010110 htau hs010110).elim
        · have hs010112 : InSquare (-19/160) (-61/160) (1/160) tau := by
            convert childUL hs01011 hx01011 hy01011 using 1 <;> norm_num
          rcases le_total tau.re (-19/160 : ℝ) with hx010112 | hx010112
          · rcases le_total tau.im (-61/160 : ℝ) with hy010112 | hy010112
            · have hs0101120 : InSquare (-39/320) (-123/320) (1/320) tau := by
                convert childLL hs010112 hx010112 hy010112 using 1 <;> norm_num
              rcases le_total tau.re (-39/320 : ℝ) with hx0101120 | hx0101120
              · rcases le_total tau.im (-123/320 : ℝ) with hy0101120 | hy0101120
                · have hs01011200 : InSquare (-79/640) (-247/640) (1/640) tau := by
                    convert childLL hs0101120 hx0101120 hy0101120 using 1 <;> norm_num
                  exact (outside_01011200 htau hs01011200).elim
                · have hs01011202 : InSquare (-79/640) (-49/128) (1/640) tau := by
                    convert childUL hs0101120 hx0101120 hy0101120 using 1 <;> norm_num
                  exact (outside_01011202 htau hs01011202).elim
              · rcases le_total tau.im (-123/320 : ℝ) with hy0101120 | hy0101120
                · have hs01011201 : InSquare (-77/640) (-247/640) (1/640) tau := by
                    convert childLR hs0101120 hx0101120 hy0101120 using 1 <;> norm_num
                  exact (outside_01011201 htau hs01011201).elim
                · have hs01011203 : InSquare (-77/640) (-49/128) (1/640) tau := by
                    convert childUR hs0101120 hx0101120 hy0101120 using 1 <;> norm_num
                  exact Batch0329.cell2634.sound htau (by
                    simp only [Batch0329.cell2634, Batch0329.tau2634, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01011203 (by positivity) using 1 <;> norm_num)
            · have hs0101122 : InSquare (-39/320) (-121/320) (1/320) tau := by
                convert childUL hs010112 hx010112 hy010112 using 1 <;> norm_num
              rcases le_total tau.re (-39/320 : ℝ) with hx0101122 | hx0101122
              · rcases le_total tau.im (-121/320 : ℝ) with hy0101122 | hy0101122
                · have hs01011220 : InSquare (-79/640) (-243/640) (1/640) tau := by
                    convert childLL hs0101122 hx0101122 hy0101122 using 1 <;> norm_num
                  exact Batch0329.cell2637.sound htau (by
                    simp only [Batch0329.cell2637, Batch0329.tau2637, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01011220 (by positivity) using 1 <;> norm_num)
                · have hs01011222 : InSquare (-79/640) (-241/640) (1/640) tau := by
                    convert childUL hs0101122 hx0101122 hy0101122 using 1 <;> norm_num
                  exact Batch0329.cell2639.sound htau (by
                    simp only [Batch0329.cell2639, Batch0329.tau2639, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01011222 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-121/320 : ℝ) with hy0101122 | hy0101122
                · have hs01011221 : InSquare (-77/640) (-243/640) (1/640) tau := by
                    convert childLR hs0101122 hx0101122 hy0101122 using 1 <;> norm_num
                  exact Batch0329.cell2638.sound htau (by
                    simp only [Batch0329.cell2638, Batch0329.tau2638, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01011221 (by positivity) using 1 <;> norm_num)
                · have hs01011223 : InSquare (-77/640) (-241/640) (1/640) tau := by
                    convert childUR hs0101122 hx0101122 hy0101122 using 1 <;> norm_num
                  exact Batch0330.cell2640.sound htau (by
                    simp only [Batch0330.cell2640, Batch0330.tau2640, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01011223 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-61/160 : ℝ) with hy010112 | hy010112
            · have hs0101121 : InSquare (-37/320) (-123/320) (1/320) tau := by
                convert childLR hs010112 hx010112 hy010112 using 1 <;> norm_num
              rcases le_total tau.re (-37/320 : ℝ) with hx0101121 | hx0101121
              · rcases le_total tau.im (-123/320 : ℝ) with hy0101121 | hy0101121
                · have hs01011210 : InSquare (-15/128) (-247/640) (1/640) tau := by
                    convert childLL hs0101121 hx0101121 hy0101121 using 1 <;> norm_num
                  exact (outside_01011210 htau hs01011210).elim
                · have hs01011212 : InSquare (-15/128) (-49/128) (1/640) tau := by
                    convert childUL hs0101121 hx0101121 hy0101121 using 1 <;> norm_num
                  exact Batch0329.cell2635.sound htau (by
                    simp only [Batch0329.cell2635, Batch0329.tau2635, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01011212 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-123/320 : ℝ) with hy0101121 | hy0101121
                · have hs01011211 : InSquare (-73/640) (-247/640) (1/640) tau := by
                    convert childLR hs0101121 hx0101121 hy0101121 using 1 <;> norm_num
                  exact (outside_01011211 htau hs01011211).elim
                · have hs01011213 : InSquare (-73/640) (-49/128) (1/640) tau := by
                    convert childUR hs0101121 hx0101121 hy0101121 using 1 <;> norm_num
                  exact Batch0329.cell2636.sound htau (by
                    simp only [Batch0329.cell2636, Batch0329.tau2636, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01011213 (by positivity) using 1 <;> norm_num)
            · have hs0101123 : InSquare (-37/320) (-121/320) (1/320) tau := by
                convert childUR hs010112 hx010112 hy010112 using 1 <;> norm_num
              rcases le_total tau.re (-37/320 : ℝ) with hx0101123 | hx0101123
              · rcases le_total tau.im (-121/320 : ℝ) with hy0101123 | hy0101123
                · have hs01011230 : InSquare (-15/128) (-243/640) (1/640) tau := by
                    convert childLL hs0101123 hx0101123 hy0101123 using 1 <;> norm_num
                  exact Batch0330.cell2641.sound htau (by
                    simp only [Batch0330.cell2641, Batch0330.tau2641, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01011230 (by positivity) using 1 <;> norm_num)
                · have hs01011232 : InSquare (-15/128) (-241/640) (1/640) tau := by
                    convert childUL hs0101123 hx0101123 hy0101123 using 1 <;> norm_num
                  exact Batch0330.cell2643.sound htau (by
                    simp only [Batch0330.cell2643, Batch0330.tau2643, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01011232 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-121/320 : ℝ) with hy0101123 | hy0101123
                · have hs01011231 : InSquare (-73/640) (-243/640) (1/640) tau := by
                    convert childLR hs0101123 hx0101123 hy0101123 using 1 <;> norm_num
                  exact Batch0330.cell2642.sound htau (by
                    simp only [Batch0330.cell2642, Batch0330.tau2642, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01011231 (by positivity) using 1 <;> norm_num)
                · have hs01011233 : InSquare (-73/640) (-241/640) (1/640) tau := by
                    convert childUR hs0101123 hx0101123 hy0101123 using 1 <;> norm_num
                  exact Batch0330.cell2644.sound htau (by
                    simp only [Batch0330.cell2644, Batch0330.tau2644, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01011233 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-31/80 : ℝ) with hy01011 | hy01011
        · have hs010111 : InSquare (-17/160) (-63/160) (1/160) tau := by
            convert childLR hs01011 hx01011 hy01011 using 1 <;> norm_num
          exact (outside_010111 htau hs010111).elim
        · have hs010113 : InSquare (-17/160) (-61/160) (1/160) tau := by
            convert childUR hs01011 hx01011 hy01011 using 1 <;> norm_num
          rcases le_total tau.re (-17/160 : ℝ) with hx010113 | hx010113
          · rcases le_total tau.im (-61/160 : ℝ) with hy010113 | hy010113
            · have hs0101130 : InSquare (-7/64) (-123/320) (1/320) tau := by
                convert childLL hs010113 hx010113 hy010113 using 1 <;> norm_num
              rcases le_total tau.re (-7/64 : ℝ) with hx0101130 | hx0101130
              · rcases le_total tau.im (-123/320 : ℝ) with hy0101130 | hy0101130
                · have hs01011300 : InSquare (-71/640) (-247/640) (1/640) tau := by
                    convert childLL hs0101130 hx0101130 hy0101130 using 1 <;> norm_num
                  exact Batch0330.cell2645.sound htau (by
                    simp only [Batch0330.cell2645, Batch0330.tau2645, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01011300 (by positivity) using 1 <;> norm_num)
                · have hs01011302 : InSquare (-71/640) (-49/128) (1/640) tau := by
                    convert childUL hs0101130 hx0101130 hy0101130 using 1 <;> norm_num
                  exact Batch0330.cell2647.sound htau (by
                    simp only [Batch0330.cell2647, Batch0330.tau2647, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01011302 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-123/320 : ℝ) with hy0101130 | hy0101130
                · have hs01011301 : InSquare (-69/640) (-247/640) (1/640) tau := by
                    convert childLR hs0101130 hx0101130 hy0101130 using 1 <;> norm_num
                  exact Batch0330.cell2646.sound htau (by
                    simp only [Batch0330.cell2646, Batch0330.tau2646, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01011301 (by positivity) using 1 <;> norm_num)
                · have hs01011303 : InSquare (-69/640) (-49/128) (1/640) tau := by
                    convert childUR hs0101130 hx0101130 hy0101130 using 1 <;> norm_num
                  exact Batch0331.cell2648.sound htau (by
                    simp only [Batch0331.cell2648, Batch0331.tau2648, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01011303 (by positivity) using 1 <;> norm_num)
            · have hs0101132 : InSquare (-7/64) (-121/320) (1/320) tau := by
                convert childUL hs010113 hx010113 hy010113 using 1 <;> norm_num
              rcases le_total tau.re (-7/64 : ℝ) with hx0101132 | hx0101132
              · rcases le_total tau.im (-121/320 : ℝ) with hy0101132 | hy0101132
                · have hs01011320 : InSquare (-71/640) (-243/640) (1/640) tau := by
                    convert childLL hs0101132 hx0101132 hy0101132 using 1 <;> norm_num
                  exact Batch0331.cell2653.sound htau (by
                    simp only [Batch0331.cell2653, Batch0331.tau2653, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01011320 (by positivity) using 1 <;> norm_num)
                · have hs01011322 : InSquare (-71/640) (-241/640) (1/640) tau := by
                    convert childUL hs0101132 hx0101132 hy0101132 using 1 <;> norm_num
                  exact Batch0331.cell2655.sound htau (by
                    simp only [Batch0331.cell2655, Batch0331.tau2655, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01011322 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-121/320 : ℝ) with hy0101132 | hy0101132
                · have hs01011321 : InSquare (-69/640) (-243/640) (1/640) tau := by
                    convert childLR hs0101132 hx0101132 hy0101132 using 1 <;> norm_num
                  exact Batch0331.cell2654.sound htau (by
                    simp only [Batch0331.cell2654, Batch0331.tau2654, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01011321 (by positivity) using 1 <;> norm_num)
                · have hs01011323 : InSquare (-69/640) (-241/640) (1/640) tau := by
                    convert childUR hs0101132 hx0101132 hy0101132 using 1 <;> norm_num
                  exact Batch0332.cell2656.sound htau (by
                    simp only [Batch0332.cell2656, Batch0332.tau2656, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01011323 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-61/160 : ℝ) with hy010113 | hy010113
            · have hs0101131 : InSquare (-33/320) (-123/320) (1/320) tau := by
                convert childLR hs010113 hx010113 hy010113 using 1 <;> norm_num
              rcases le_total tau.re (-33/320 : ℝ) with hx0101131 | hx0101131
              · rcases le_total tau.im (-123/320 : ℝ) with hy0101131 | hy0101131
                · have hs01011310 : InSquare (-67/640) (-247/640) (1/640) tau := by
                    convert childLL hs0101131 hx0101131 hy0101131 using 1 <;> norm_num
                  exact Batch0331.cell2649.sound htau (by
                    simp only [Batch0331.cell2649, Batch0331.tau2649, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01011310 (by positivity) using 1 <;> norm_num)
                · have hs01011312 : InSquare (-67/640) (-49/128) (1/640) tau := by
                    convert childUL hs0101131 hx0101131 hy0101131 using 1 <;> norm_num
                  exact Batch0331.cell2651.sound htau (by
                    simp only [Batch0331.cell2651, Batch0331.tau2651, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01011312 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-123/320 : ℝ) with hy0101131 | hy0101131
                · have hs01011311 : InSquare (-13/128) (-247/640) (1/640) tau := by
                    convert childLR hs0101131 hx0101131 hy0101131 using 1 <;> norm_num
                  exact Batch0331.cell2650.sound htau (by
                    simp only [Batch0331.cell2650, Batch0331.tau2650, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01011311 (by positivity) using 1 <;> norm_num)
                · have hs01011313 : InSquare (-13/128) (-49/128) (1/640) tau := by
                    convert childUR hs0101131 hx0101131 hy0101131 using 1 <;> norm_num
                  exact Batch0331.cell2652.sound htau (by
                    simp only [Batch0331.cell2652, Batch0331.tau2652, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01011313 (by positivity) using 1 <;> norm_num)
            · have hs0101133 : InSquare (-33/320) (-121/320) (1/320) tau := by
                convert childUR hs010113 hx010113 hy010113 using 1 <;> norm_num
              rcases le_total tau.re (-33/320 : ℝ) with hx0101133 | hx0101133
              · rcases le_total tau.im (-121/320 : ℝ) with hy0101133 | hy0101133
                · have hs01011330 : InSquare (-67/640) (-243/640) (1/640) tau := by
                    convert childLL hs0101133 hx0101133 hy0101133 using 1 <;> norm_num
                  exact Batch0332.cell2657.sound htau (by
                    simp only [Batch0332.cell2657, Batch0332.tau2657, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01011330 (by positivity) using 1 <;> norm_num)
                · have hs01011332 : InSquare (-67/640) (-241/640) (1/640) tau := by
                    convert childUL hs0101133 hx0101133 hy0101133 using 1 <;> norm_num
                  exact Batch0332.cell2659.sound htau (by
                    simp only [Batch0332.cell2659, Batch0332.tau2659, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01011332 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-121/320 : ℝ) with hy0101133 | hy0101133
                · have hs01011331 : InSquare (-13/128) (-243/640) (1/640) tau := by
                    convert childLR hs0101133 hx0101133 hy0101133 using 1 <;> norm_num
                  exact Batch0332.cell2658.sound htau (by
                    simp only [Batch0332.cell2658, Batch0332.tau2658, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01011331 (by positivity) using 1 <;> norm_num)
                · have hs01011333 : InSquare (-13/128) (-241/640) (1/640) tau := by
                    convert childUR hs0101133 hx0101133 hy0101133 using 1 <;> norm_num
                  exact Batch0332.cell2660.sound htau (by
                    simp only [Batch0332.cell2660, Batch0332.tau2660, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01011333 (by positivity) using 1 <;> norm_num)
    · have hs01013 : InSquare (-9/80) (-29/80) (1/80) tau := by
        convert childUR hs hx0101 hy0101 using 1 <;> norm_num
      rcases le_total tau.re (-9/80 : ℝ) with hx01013 | hx01013
      · rcases le_total tau.im (-29/80 : ℝ) with hy01013 | hy01013
        · have hs010130 : InSquare (-19/160) (-59/160) (1/160) tau := by
            convert childLL hs01013 hx01013 hy01013 using 1 <;> norm_num
          rcases le_total tau.re (-19/160 : ℝ) with hx010130 | hx010130
          · rcases le_total tau.im (-59/160 : ℝ) with hy010130 | hy010130
            · have hs0101300 : InSquare (-39/320) (-119/320) (1/320) tau := by
                convert childLL hs010130 hx010130 hy010130 using 1 <;> norm_num
              rcases le_total tau.re (-39/320 : ℝ) with hx0101300 | hx0101300
              · rcases le_total tau.im (-119/320 : ℝ) with hy0101300 | hy0101300
                · have hs01013000 : InSquare (-79/640) (-239/640) (1/640) tau := by
                    convert childLL hs0101300 hx0101300 hy0101300 using 1 <;> norm_num
                  exact Batch0337.cell2697.sound htau (by
                    simp only [Batch0337.cell2697, Batch0337.tau2697, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01013000 (by positivity) using 1 <;> norm_num)
                · have hs01013002 : InSquare (-79/640) (-237/640) (1/640) tau := by
                    convert childUL hs0101300 hx0101300 hy0101300 using 1 <;> norm_num
                  exact Batch0337.cell2699.sound htau (by
                    simp only [Batch0337.cell2699, Batch0337.tau2699, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01013002 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-119/320 : ℝ) with hy0101300 | hy0101300
                · have hs01013001 : InSquare (-77/640) (-239/640) (1/640) tau := by
                    convert childLR hs0101300 hx0101300 hy0101300 using 1 <;> norm_num
                  exact Batch0337.cell2698.sound htau (by
                    simp only [Batch0337.cell2698, Batch0337.tau2698, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01013001 (by positivity) using 1 <;> norm_num)
                · have hs01013003 : InSquare (-77/640) (-237/640) (1/640) tau := by
                    convert childUR hs0101300 hx0101300 hy0101300 using 1 <;> norm_num
                  exact Batch0337.cell2700.sound htau (by
                    simp only [Batch0337.cell2700, Batch0337.tau2700, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01013003 (by positivity) using 1 <;> norm_num)
            · have hs0101302 : InSquare (-39/320) (-117/320) (1/320) tau := by
                convert childUL hs010130 hx010130 hy010130 using 1 <;> norm_num
              exact Batch0169.cell1354.sound htau (by
                simp only [Batch0169.cell1354, Batch0169.tau1354, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0101302 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-59/160 : ℝ) with hy010130 | hy010130
            · have hs0101301 : InSquare (-37/320) (-119/320) (1/320) tau := by
                convert childLR hs010130 hx010130 hy010130 using 1 <;> norm_num
              rcases le_total tau.re (-37/320 : ℝ) with hx0101301 | hx0101301
              · rcases le_total tau.im (-119/320 : ℝ) with hy0101301 | hy0101301
                · have hs01013010 : InSquare (-15/128) (-239/640) (1/640) tau := by
                    convert childLL hs0101301 hx0101301 hy0101301 using 1 <;> norm_num
                  exact Batch0337.cell2701.sound htau (by
                    simp only [Batch0337.cell2701, Batch0337.tau2701, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01013010 (by positivity) using 1 <;> norm_num)
                · have hs01013012 : InSquare (-15/128) (-237/640) (1/640) tau := by
                    convert childUL hs0101301 hx0101301 hy0101301 using 1 <;> norm_num
                  exact Batch0337.cell2703.sound htau (by
                    simp only [Batch0337.cell2703, Batch0337.tau2703, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01013012 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-119/320 : ℝ) with hy0101301 | hy0101301
                · have hs01013011 : InSquare (-73/640) (-239/640) (1/640) tau := by
                    convert childLR hs0101301 hx0101301 hy0101301 using 1 <;> norm_num
                  exact Batch0337.cell2702.sound htau (by
                    simp only [Batch0337.cell2702, Batch0337.tau2702, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01013011 (by positivity) using 1 <;> norm_num)
                · have hs01013013 : InSquare (-73/640) (-237/640) (1/640) tau := by
                    convert childUR hs0101301 hx0101301 hy0101301 using 1 <;> norm_num
                  exact Batch0338.cell2704.sound htau (by
                    simp only [Batch0338.cell2704, Batch0338.tau2704, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01013013 (by positivity) using 1 <;> norm_num)
            · have hs0101303 : InSquare (-37/320) (-117/320) (1/320) tau := by
                convert childUR hs010130 hx010130 hy010130 using 1 <;> norm_num
              exact Batch0169.cell1355.sound htau (by
                simp only [Batch0169.cell1355, Batch0169.tau1355, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0101303 (by positivity) using 1 <;> norm_num)
        · have hs010132 : InSquare (-19/160) (-57/160) (1/160) tau := by
            convert childUL hs01013 hx01013 hy01013 using 1 <;> norm_num
          rcases le_total tau.re (-19/160 : ℝ) with hx010132 | hx010132
          · rcases le_total tau.im (-57/160 : ℝ) with hy010132 | hy010132
            · have hs0101320 : InSquare (-39/320) (-23/64) (1/320) tau := by
                convert childLL hs010132 hx010132 hy010132 using 1 <;> norm_num
              exact Batch0169.cell1358.sound htau (by
                simp only [Batch0169.cell1358, Batch0169.tau1358, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0101320 (by positivity) using 1 <;> norm_num)
            · have hs0101322 : InSquare (-39/320) (-113/320) (1/320) tau := by
                convert childUL hs010132 hx010132 hy010132 using 1 <;> norm_num
              exact Batch0170.cell1360.sound htau (by
                simp only [Batch0170.cell1360, Batch0170.tau1360, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0101322 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-57/160 : ℝ) with hy010132 | hy010132
            · have hs0101321 : InSquare (-37/320) (-23/64) (1/320) tau := by
                convert childLR hs010132 hx010132 hy010132 using 1 <;> norm_num
              exact Batch0169.cell1359.sound htau (by
                simp only [Batch0169.cell1359, Batch0169.tau1359, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0101321 (by positivity) using 1 <;> norm_num)
            · have hs0101323 : InSquare (-37/320) (-113/320) (1/320) tau := by
                convert childUR hs010132 hx010132 hy010132 using 1 <;> norm_num
              exact Batch0170.cell1361.sound htau (by
                simp only [Batch0170.cell1361, Batch0170.tau1361, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0101323 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-29/80 : ℝ) with hy01013 | hy01013
        · have hs010131 : InSquare (-17/160) (-59/160) (1/160) tau := by
            convert childLR hs01013 hx01013 hy01013 using 1 <;> norm_num
          rcases le_total tau.re (-17/160 : ℝ) with hx010131 | hx010131
          · rcases le_total tau.im (-59/160 : ℝ) with hy010131 | hy010131
            · have hs0101310 : InSquare (-7/64) (-119/320) (1/320) tau := by
                convert childLL hs010131 hx010131 hy010131 using 1 <;> norm_num
              rcases le_total tau.re (-7/64 : ℝ) with hx0101310 | hx0101310
              · rcases le_total tau.im (-119/320 : ℝ) with hy0101310 | hy0101310
                · have hs01013100 : InSquare (-71/640) (-239/640) (1/640) tau := by
                    convert childLL hs0101310 hx0101310 hy0101310 using 1 <;> norm_num
                  exact Batch0338.cell2705.sound htau (by
                    simp only [Batch0338.cell2705, Batch0338.tau2705, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01013100 (by positivity) using 1 <;> norm_num)
                · have hs01013102 : InSquare (-71/640) (-237/640) (1/640) tau := by
                    convert childUL hs0101310 hx0101310 hy0101310 using 1 <;> norm_num
                  exact Batch0338.cell2707.sound htau (by
                    simp only [Batch0338.cell2707, Batch0338.tau2707, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01013102 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-119/320 : ℝ) with hy0101310 | hy0101310
                · have hs01013101 : InSquare (-69/640) (-239/640) (1/640) tau := by
                    convert childLR hs0101310 hx0101310 hy0101310 using 1 <;> norm_num
                  exact Batch0338.cell2706.sound htau (by
                    simp only [Batch0338.cell2706, Batch0338.tau2706, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01013101 (by positivity) using 1 <;> norm_num)
                · have hs01013103 : InSquare (-69/640) (-237/640) (1/640) tau := by
                    convert childUR hs0101310 hx0101310 hy0101310 using 1 <;> norm_num
                  exact Batch0338.cell2708.sound htau (by
                    simp only [Batch0338.cell2708, Batch0338.tau2708, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01013103 (by positivity) using 1 <;> norm_num)
            · have hs0101312 : InSquare (-7/64) (-117/320) (1/320) tau := by
                convert childUL hs010131 hx010131 hy010131 using 1 <;> norm_num
              exact Batch0169.cell1356.sound htau (by
                simp only [Batch0169.cell1356, Batch0169.tau1356, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0101312 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-59/160 : ℝ) with hy010131 | hy010131
            · have hs0101311 : InSquare (-33/320) (-119/320) (1/320) tau := by
                convert childLR hs010131 hx010131 hy010131 using 1 <;> norm_num
              rcases le_total tau.re (-33/320 : ℝ) with hx0101311 | hx0101311
              · rcases le_total tau.im (-119/320 : ℝ) with hy0101311 | hy0101311
                · have hs01013110 : InSquare (-67/640) (-239/640) (1/640) tau := by
                    convert childLL hs0101311 hx0101311 hy0101311 using 1 <;> norm_num
                  exact Batch0338.cell2709.sound htau (by
                    simp only [Batch0338.cell2709, Batch0338.tau2709, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01013110 (by positivity) using 1 <;> norm_num)
                · have hs01013112 : InSquare (-67/640) (-237/640) (1/640) tau := by
                    convert childUL hs0101311 hx0101311 hy0101311 using 1 <;> norm_num
                  exact Batch0338.cell2711.sound htau (by
                    simp only [Batch0338.cell2711, Batch0338.tau2711, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01013112 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-119/320 : ℝ) with hy0101311 | hy0101311
                · have hs01013111 : InSquare (-13/128) (-239/640) (1/640) tau := by
                    convert childLR hs0101311 hx0101311 hy0101311 using 1 <;> norm_num
                  exact Batch0338.cell2710.sound htau (by
                    simp only [Batch0338.cell2710, Batch0338.tau2710, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01013111 (by positivity) using 1 <;> norm_num)
                · have hs01013113 : InSquare (-13/128) (-237/640) (1/640) tau := by
                    convert childUR hs0101311 hx0101311 hy0101311 using 1 <;> norm_num
                  exact Batch0339.cell2712.sound htau (by
                    simp only [Batch0339.cell2712, Batch0339.tau2712, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs01013113 (by positivity) using 1 <;> norm_num)
            · have hs0101313 : InSquare (-33/320) (-117/320) (1/320) tau := by
                convert childUR hs010131 hx010131 hy010131 using 1 <;> norm_num
              exact Batch0169.cell1357.sound htau (by
                simp only [Batch0169.cell1357, Batch0169.tau1357, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0101313 (by positivity) using 1 <;> norm_num)
        · have hs010133 : InSquare (-17/160) (-57/160) (1/160) tau := by
            convert childUR hs01013 hx01013 hy01013 using 1 <;> norm_num
          rcases le_total tau.re (-17/160 : ℝ) with hx010133 | hx010133
          · rcases le_total tau.im (-57/160 : ℝ) with hy010133 | hy010133
            · have hs0101330 : InSquare (-7/64) (-23/64) (1/320) tau := by
                convert childLL hs010133 hx010133 hy010133 using 1 <;> norm_num
              exact Batch0170.cell1362.sound htau (by
                simp only [Batch0170.cell1362, Batch0170.tau1362, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0101330 (by positivity) using 1 <;> norm_num)
            · have hs0101332 : InSquare (-7/64) (-113/320) (1/320) tau := by
                convert childUL hs010133 hx010133 hy010133 using 1 <;> norm_num
              exact Batch0170.cell1364.sound htau (by
                simp only [Batch0170.cell1364, Batch0170.tau1364, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0101332 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-57/160 : ℝ) with hy010133 | hy010133
            · have hs0101331 : InSquare (-33/320) (-23/64) (1/320) tau := by
                convert childLR hs010133 hx010133 hy010133 using 1 <;> norm_num
              exact Batch0170.cell1363.sound htau (by
                simp only [Batch0170.cell1363, Batch0170.tau1363, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0101331 (by positivity) using 1 <;> norm_num)
            · have hs0101333 : InSquare (-33/320) (-113/320) (1/320) tau := by
                convert childUR hs010133 hx010133 hy010133 using 1 <;> norm_num
              exact Batch0170.cell1365.sound htau (by
                simp only [Batch0170.cell1365, Batch0170.tau1365, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0101333 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0101
