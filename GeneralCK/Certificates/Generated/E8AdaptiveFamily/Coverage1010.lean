import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0203
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0204
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0205
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0380
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0381
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0382
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0383
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0384
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0385
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0386
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0387
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0388
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0389
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0390
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0391

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1010

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

private theorem outside_101000 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (17/160) (-63/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (1/10 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-1/10)]
  have himSq : (31/80 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+31/80)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_101001 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (19/160) (-63/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (9/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-9/80)]
  have himSq : (31/80 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+31/80)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_101010 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (21/160) (-63/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (1/8 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-1/8)]
  have himSq : (31/80 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+31/80)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_101011 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (23/160) (-63/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (11/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-11/80)]
  have himSq : (31/80 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+31/80)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_1010120 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (41/320) (-123/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (1/8 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-1/8)]
  have himSq : (61/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+61/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_1010121 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (43/320) (-123/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (21/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-21/160)]
  have himSq : (61/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+61/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_1010130 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (9/64) (-123/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (11/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-11/80)]
  have himSq : (61/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+61/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_1010131 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (47/320) (-123/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (23/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-23/160)]
  have himSq : (61/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+61/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_1010133 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (47/320) (-121/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (23/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-23/160)]
  have himSq : (3/8 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+3/8)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_10100300 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (73/640) (-247/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (9/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-9/80)]
  have himSq : (123/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+123/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_10100301 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (15/128) (-247/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (37/320 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-37/320)]
  have himSq : (123/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+123/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_10100310 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (77/640) (-247/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (19/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-19/160)]
  have himSq : (123/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+123/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_10100311 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (79/640) (-247/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (39/320 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-39/320)]
  have himSq : (123/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+123/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_10100313 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (79/640) (-49/128) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (39/320 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-39/320)]
  have himSq : (61/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+61/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_10101230 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (17/128) (-243/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (21/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-21/160)]
  have himSq : (121/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+121/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_10101231 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (87/640) (-243/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (43/320 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-43/320)]
  have himSq : (121/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+121/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_10101320 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (89/640) (-243/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (11/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-11/80)]
  have himSq : (121/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+121/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_10101321 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (91/640) (-243/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (9/64 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-9/64)]
  have himSq : (121/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+121/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_10101323 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (91/640) (-241/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (9/64 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-9/64)]
  have himSq : (3/8 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+3/8)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (1/8) (-3/8) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (1/8 : ℝ) with hx1010 | hx1010
  · rcases le_total tau.im (-3/8 : ℝ) with hy1010 | hy1010
    · have hs10100 : InSquare (9/80) (-31/80) (1/80) tau := by
        convert childLL hs hx1010 hy1010 using 1 <;> norm_num
      rcases le_total tau.re (9/80 : ℝ) with hx10100 | hx10100
      · rcases le_total tau.im (-31/80 : ℝ) with hy10100 | hy10100
        · have hs101000 : InSquare (17/160) (-63/160) (1/160) tau := by
            convert childLL hs10100 hx10100 hy10100 using 1 <;> norm_num
          exact (outside_101000 htau hs101000).elim
        · have hs101002 : InSquare (17/160) (-61/160) (1/160) tau := by
            convert childUL hs10100 hx10100 hy10100 using 1 <;> norm_num
          rcases le_total tau.re (17/160 : ℝ) with hx101002 | hx101002
          · rcases le_total tau.im (-61/160 : ℝ) with hy101002 | hy101002
            · have hs1010020 : InSquare (33/320) (-123/320) (1/320) tau := by
                convert childLL hs101002 hx101002 hy101002 using 1 <;> norm_num
              rcases le_total tau.re (33/320 : ℝ) with hx1010020 | hx1010020
              · rcases le_total tau.im (-123/320 : ℝ) with hy1010020 | hy1010020
                · have hs10100200 : InSquare (13/128) (-247/640) (1/640) tau := by
                    convert childLL hs1010020 hx1010020 hy1010020 using 1 <;> norm_num
                  exact Batch0380.cell3047.sound htau (by
                    simp only [Batch0380.cell3047, Batch0380.tau3047, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10100200 (by positivity) using 1 <;> norm_num)
                · have hs10100202 : InSquare (13/128) (-49/128) (1/640) tau := by
                    convert childUL hs1010020 hx1010020 hy1010020 using 1 <;> norm_num
                  exact Batch0381.cell3049.sound htau (by
                    simp only [Batch0381.cell3049, Batch0381.tau3049, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10100202 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-123/320 : ℝ) with hy1010020 | hy1010020
                · have hs10100201 : InSquare (67/640) (-247/640) (1/640) tau := by
                    convert childLR hs1010020 hx1010020 hy1010020 using 1 <;> norm_num
                  exact Batch0381.cell3048.sound htau (by
                    simp only [Batch0381.cell3048, Batch0381.tau3048, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10100201 (by positivity) using 1 <;> norm_num)
                · have hs10100203 : InSquare (67/640) (-49/128) (1/640) tau := by
                    convert childUR hs1010020 hx1010020 hy1010020 using 1 <;> norm_num
                  exact Batch0381.cell3050.sound htau (by
                    simp only [Batch0381.cell3050, Batch0381.tau3050, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10100203 (by positivity) using 1 <;> norm_num)
            · have hs1010022 : InSquare (33/320) (-121/320) (1/320) tau := by
                convert childUL hs101002 hx101002 hy101002 using 1 <;> norm_num
              rcases le_total tau.re (33/320 : ℝ) with hx1010022 | hx1010022
              · rcases le_total tau.im (-121/320 : ℝ) with hy1010022 | hy1010022
                · have hs10100220 : InSquare (13/128) (-243/640) (1/640) tau := by
                    convert childLL hs1010022 hx1010022 hy1010022 using 1 <;> norm_num
                  exact Batch0381.cell3055.sound htau (by
                    simp only [Batch0381.cell3055, Batch0381.tau3055, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10100220 (by positivity) using 1 <;> norm_num)
                · have hs10100222 : InSquare (13/128) (-241/640) (1/640) tau := by
                    convert childUL hs1010022 hx1010022 hy1010022 using 1 <;> norm_num
                  exact Batch0382.cell3057.sound htau (by
                    simp only [Batch0382.cell3057, Batch0382.tau3057, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10100222 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-121/320 : ℝ) with hy1010022 | hy1010022
                · have hs10100221 : InSquare (67/640) (-243/640) (1/640) tau := by
                    convert childLR hs1010022 hx1010022 hy1010022 using 1 <;> norm_num
                  exact Batch0382.cell3056.sound htau (by
                    simp only [Batch0382.cell3056, Batch0382.tau3056, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10100221 (by positivity) using 1 <;> norm_num)
                · have hs10100223 : InSquare (67/640) (-241/640) (1/640) tau := by
                    convert childUR hs1010022 hx1010022 hy1010022 using 1 <;> norm_num
                  exact Batch0382.cell3058.sound htau (by
                    simp only [Batch0382.cell3058, Batch0382.tau3058, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10100223 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-61/160 : ℝ) with hy101002 | hy101002
            · have hs1010021 : InSquare (7/64) (-123/320) (1/320) tau := by
                convert childLR hs101002 hx101002 hy101002 using 1 <;> norm_num
              rcases le_total tau.re (7/64 : ℝ) with hx1010021 | hx1010021
              · rcases le_total tau.im (-123/320 : ℝ) with hy1010021 | hy1010021
                · have hs10100210 : InSquare (69/640) (-247/640) (1/640) tau := by
                    convert childLL hs1010021 hx1010021 hy1010021 using 1 <;> norm_num
                  exact Batch0381.cell3051.sound htau (by
                    simp only [Batch0381.cell3051, Batch0381.tau3051, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10100210 (by positivity) using 1 <;> norm_num)
                · have hs10100212 : InSquare (69/640) (-49/128) (1/640) tau := by
                    convert childUL hs1010021 hx1010021 hy1010021 using 1 <;> norm_num
                  exact Batch0381.cell3053.sound htau (by
                    simp only [Batch0381.cell3053, Batch0381.tau3053, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10100212 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-123/320 : ℝ) with hy1010021 | hy1010021
                · have hs10100211 : InSquare (71/640) (-247/640) (1/640) tau := by
                    convert childLR hs1010021 hx1010021 hy1010021 using 1 <;> norm_num
                  exact Batch0381.cell3052.sound htau (by
                    simp only [Batch0381.cell3052, Batch0381.tau3052, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10100211 (by positivity) using 1 <;> norm_num)
                · have hs10100213 : InSquare (71/640) (-49/128) (1/640) tau := by
                    convert childUR hs1010021 hx1010021 hy1010021 using 1 <;> norm_num
                  exact Batch0381.cell3054.sound htau (by
                    simp only [Batch0381.cell3054, Batch0381.tau3054, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10100213 (by positivity) using 1 <;> norm_num)
            · have hs1010023 : InSquare (7/64) (-121/320) (1/320) tau := by
                convert childUR hs101002 hx101002 hy101002 using 1 <;> norm_num
              rcases le_total tau.re (7/64 : ℝ) with hx1010023 | hx1010023
              · rcases le_total tau.im (-121/320 : ℝ) with hy1010023 | hy1010023
                · have hs10100230 : InSquare (69/640) (-243/640) (1/640) tau := by
                    convert childLL hs1010023 hx1010023 hy1010023 using 1 <;> norm_num
                  exact Batch0382.cell3059.sound htau (by
                    simp only [Batch0382.cell3059, Batch0382.tau3059, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10100230 (by positivity) using 1 <;> norm_num)
                · have hs10100232 : InSquare (69/640) (-241/640) (1/640) tau := by
                    convert childUL hs1010023 hx1010023 hy1010023 using 1 <;> norm_num
                  exact Batch0382.cell3061.sound htau (by
                    simp only [Batch0382.cell3061, Batch0382.tau3061, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10100232 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-121/320 : ℝ) with hy1010023 | hy1010023
                · have hs10100231 : InSquare (71/640) (-243/640) (1/640) tau := by
                    convert childLR hs1010023 hx1010023 hy1010023 using 1 <;> norm_num
                  exact Batch0382.cell3060.sound htau (by
                    simp only [Batch0382.cell3060, Batch0382.tau3060, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10100231 (by positivity) using 1 <;> norm_num)
                · have hs10100233 : InSquare (71/640) (-241/640) (1/640) tau := by
                    convert childUR hs1010023 hx1010023 hy1010023 using 1 <;> norm_num
                  exact Batch0382.cell3062.sound htau (by
                    simp only [Batch0382.cell3062, Batch0382.tau3062, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10100233 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-31/80 : ℝ) with hy10100 | hy10100
        · have hs101001 : InSquare (19/160) (-63/160) (1/160) tau := by
            convert childLR hs10100 hx10100 hy10100 using 1 <;> norm_num
          exact (outside_101001 htau hs101001).elim
        · have hs101003 : InSquare (19/160) (-61/160) (1/160) tau := by
            convert childUR hs10100 hx10100 hy10100 using 1 <;> norm_num
          rcases le_total tau.re (19/160 : ℝ) with hx101003 | hx101003
          · rcases le_total tau.im (-61/160 : ℝ) with hy101003 | hy101003
            · have hs1010030 : InSquare (37/320) (-123/320) (1/320) tau := by
                convert childLL hs101003 hx101003 hy101003 using 1 <;> norm_num
              rcases le_total tau.re (37/320 : ℝ) with hx1010030 | hx1010030
              · rcases le_total tau.im (-123/320 : ℝ) with hy1010030 | hy1010030
                · have hs10100300 : InSquare (73/640) (-247/640) (1/640) tau := by
                    convert childLL hs1010030 hx1010030 hy1010030 using 1 <;> norm_num
                  exact (outside_10100300 htau hs10100300).elim
                · have hs10100302 : InSquare (73/640) (-49/128) (1/640) tau := by
                    convert childUL hs1010030 hx1010030 hy1010030 using 1 <;> norm_num
                  exact Batch0382.cell3063.sound htau (by
                    simp only [Batch0382.cell3063, Batch0382.tau3063, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10100302 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-123/320 : ℝ) with hy1010030 | hy1010030
                · have hs10100301 : InSquare (15/128) (-247/640) (1/640) tau := by
                    convert childLR hs1010030 hx1010030 hy1010030 using 1 <;> norm_num
                  exact (outside_10100301 htau hs10100301).elim
                · have hs10100303 : InSquare (15/128) (-49/128) (1/640) tau := by
                    convert childUR hs1010030 hx1010030 hy1010030 using 1 <;> norm_num
                  exact Batch0383.cell3064.sound htau (by
                    simp only [Batch0383.cell3064, Batch0383.tau3064, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10100303 (by positivity) using 1 <;> norm_num)
            · have hs1010032 : InSquare (37/320) (-121/320) (1/320) tau := by
                convert childUL hs101003 hx101003 hy101003 using 1 <;> norm_num
              rcases le_total tau.re (37/320 : ℝ) with hx1010032 | hx1010032
              · rcases le_total tau.im (-121/320 : ℝ) with hy1010032 | hy1010032
                · have hs10100320 : InSquare (73/640) (-243/640) (1/640) tau := by
                    convert childLL hs1010032 hx1010032 hy1010032 using 1 <;> norm_num
                  exact Batch0383.cell3066.sound htau (by
                    simp only [Batch0383.cell3066, Batch0383.tau3066, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10100320 (by positivity) using 1 <;> norm_num)
                · have hs10100322 : InSquare (73/640) (-241/640) (1/640) tau := by
                    convert childUL hs1010032 hx1010032 hy1010032 using 1 <;> norm_num
                  exact Batch0383.cell3068.sound htau (by
                    simp only [Batch0383.cell3068, Batch0383.tau3068, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10100322 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-121/320 : ℝ) with hy1010032 | hy1010032
                · have hs10100321 : InSquare (15/128) (-243/640) (1/640) tau := by
                    convert childLR hs1010032 hx1010032 hy1010032 using 1 <;> norm_num
                  exact Batch0383.cell3067.sound htau (by
                    simp only [Batch0383.cell3067, Batch0383.tau3067, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10100321 (by positivity) using 1 <;> norm_num)
                · have hs10100323 : InSquare (15/128) (-241/640) (1/640) tau := by
                    convert childUR hs1010032 hx1010032 hy1010032 using 1 <;> norm_num
                  exact Batch0383.cell3069.sound htau (by
                    simp only [Batch0383.cell3069, Batch0383.tau3069, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10100323 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-61/160 : ℝ) with hy101003 | hy101003
            · have hs1010031 : InSquare (39/320) (-123/320) (1/320) tau := by
                convert childLR hs101003 hx101003 hy101003 using 1 <;> norm_num
              rcases le_total tau.re (39/320 : ℝ) with hx1010031 | hx1010031
              · rcases le_total tau.im (-123/320 : ℝ) with hy1010031 | hy1010031
                · have hs10100310 : InSquare (77/640) (-247/640) (1/640) tau := by
                    convert childLL hs1010031 hx1010031 hy1010031 using 1 <;> norm_num
                  exact (outside_10100310 htau hs10100310).elim
                · have hs10100312 : InSquare (77/640) (-49/128) (1/640) tau := by
                    convert childUL hs1010031 hx1010031 hy1010031 using 1 <;> norm_num
                  exact Batch0383.cell3065.sound htau (by
                    simp only [Batch0383.cell3065, Batch0383.tau3065, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10100312 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-123/320 : ℝ) with hy1010031 | hy1010031
                · have hs10100311 : InSquare (79/640) (-247/640) (1/640) tau := by
                    convert childLR hs1010031 hx1010031 hy1010031 using 1 <;> norm_num
                  exact (outside_10100311 htau hs10100311).elim
                · have hs10100313 : InSquare (79/640) (-49/128) (1/640) tau := by
                    convert childUR hs1010031 hx1010031 hy1010031 using 1 <;> norm_num
                  exact (outside_10100313 htau hs10100313).elim
            · have hs1010033 : InSquare (39/320) (-121/320) (1/320) tau := by
                convert childUR hs101003 hx101003 hy101003 using 1 <;> norm_num
              rcases le_total tau.re (39/320 : ℝ) with hx1010033 | hx1010033
              · rcases le_total tau.im (-121/320 : ℝ) with hy1010033 | hy1010033
                · have hs10100330 : InSquare (77/640) (-243/640) (1/640) tau := by
                    convert childLL hs1010033 hx1010033 hy1010033 using 1 <;> norm_num
                  exact Batch0383.cell3070.sound htau (by
                    simp only [Batch0383.cell3070, Batch0383.tau3070, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10100330 (by positivity) using 1 <;> norm_num)
                · have hs10100332 : InSquare (77/640) (-241/640) (1/640) tau := by
                    convert childUL hs1010033 hx1010033 hy1010033 using 1 <;> norm_num
                  exact Batch0384.cell3072.sound htau (by
                    simp only [Batch0384.cell3072, Batch0384.tau3072, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10100332 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-121/320 : ℝ) with hy1010033 | hy1010033
                · have hs10100331 : InSquare (79/640) (-243/640) (1/640) tau := by
                    convert childLR hs1010033 hx1010033 hy1010033 using 1 <;> norm_num
                  exact Batch0383.cell3071.sound htau (by
                    simp only [Batch0383.cell3071, Batch0383.tau3071, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10100331 (by positivity) using 1 <;> norm_num)
                · have hs10100333 : InSquare (79/640) (-241/640) (1/640) tau := by
                    convert childUR hs1010033 hx1010033 hy1010033 using 1 <;> norm_num
                  exact Batch0384.cell3073.sound htau (by
                    simp only [Batch0384.cell3073, Batch0384.tau3073, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10100333 (by positivity) using 1 <;> norm_num)
    · have hs10102 : InSquare (9/80) (-29/80) (1/80) tau := by
        convert childUL hs hx1010 hy1010 using 1 <;> norm_num
      rcases le_total tau.re (9/80 : ℝ) with hx10102 | hx10102
      · rcases le_total tau.im (-29/80 : ℝ) with hy10102 | hy10102
        · have hs101020 : InSquare (17/160) (-59/160) (1/160) tau := by
            convert childLL hs10102 hx10102 hy10102 using 1 <;> norm_num
          rcases le_total tau.re (17/160 : ℝ) with hx101020 | hx101020
          · rcases le_total tau.im (-59/160 : ℝ) with hy101020 | hy101020
            · have hs1010200 : InSquare (33/320) (-119/320) (1/320) tau := by
                convert childLL hs101020 hx101020 hy101020 using 1 <;> norm_num
              rcases le_total tau.re (33/320 : ℝ) with hx1010200 | hx1010200
              · rcases le_total tau.im (-119/320 : ℝ) with hy1010200 | hy1010200
                · have hs10102000 : InSquare (13/128) (-239/640) (1/640) tau := by
                    convert childLL hs1010200 hx1010200 hy1010200 using 1 <;> norm_num
                  exact Batch0385.cell3081.sound htau (by
                    simp only [Batch0385.cell3081, Batch0385.tau3081, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10102000 (by positivity) using 1 <;> norm_num)
                · have hs10102002 : InSquare (13/128) (-237/640) (1/640) tau := by
                    convert childUL hs1010200 hx1010200 hy1010200 using 1 <;> norm_num
                  exact Batch0385.cell3083.sound htau (by
                    simp only [Batch0385.cell3083, Batch0385.tau3083, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10102002 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-119/320 : ℝ) with hy1010200 | hy1010200
                · have hs10102001 : InSquare (67/640) (-239/640) (1/640) tau := by
                    convert childLR hs1010200 hx1010200 hy1010200 using 1 <;> norm_num
                  exact Batch0385.cell3082.sound htau (by
                    simp only [Batch0385.cell3082, Batch0385.tau3082, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10102001 (by positivity) using 1 <;> norm_num)
                · have hs10102003 : InSquare (67/640) (-237/640) (1/640) tau := by
                    convert childUR hs1010200 hx1010200 hy1010200 using 1 <;> norm_num
                  exact Batch0385.cell3084.sound htau (by
                    simp only [Batch0385.cell3084, Batch0385.tau3084, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10102003 (by positivity) using 1 <;> norm_num)
            · have hs1010202 : InSquare (33/320) (-117/320) (1/320) tau := by
                convert childUL hs101020 hx101020 hy101020 using 1 <;> norm_num
              exact Batch0203.cell1629.sound htau (by
                simp only [Batch0203.cell1629, Batch0203.tau1629, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1010202 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-59/160 : ℝ) with hy101020 | hy101020
            · have hs1010201 : InSquare (7/64) (-119/320) (1/320) tau := by
                convert childLR hs101020 hx101020 hy101020 using 1 <;> norm_num
              rcases le_total tau.re (7/64 : ℝ) with hx1010201 | hx1010201
              · rcases le_total tau.im (-119/320 : ℝ) with hy1010201 | hy1010201
                · have hs10102010 : InSquare (69/640) (-239/640) (1/640) tau := by
                    convert childLL hs1010201 hx1010201 hy1010201 using 1 <;> norm_num
                  exact Batch0385.cell3085.sound htau (by
                    simp only [Batch0385.cell3085, Batch0385.tau3085, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10102010 (by positivity) using 1 <;> norm_num)
                · have hs10102012 : InSquare (69/640) (-237/640) (1/640) tau := by
                    convert childUL hs1010201 hx1010201 hy1010201 using 1 <;> norm_num
                  exact Batch0385.cell3087.sound htau (by
                    simp only [Batch0385.cell3087, Batch0385.tau3087, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10102012 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-119/320 : ℝ) with hy1010201 | hy1010201
                · have hs10102011 : InSquare (71/640) (-239/640) (1/640) tau := by
                    convert childLR hs1010201 hx1010201 hy1010201 using 1 <;> norm_num
                  exact Batch0385.cell3086.sound htau (by
                    simp only [Batch0385.cell3086, Batch0385.tau3086, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10102011 (by positivity) using 1 <;> norm_num)
                · have hs10102013 : InSquare (71/640) (-237/640) (1/640) tau := by
                    convert childUR hs1010201 hx1010201 hy1010201 using 1 <;> norm_num
                  exact Batch0386.cell3088.sound htau (by
                    simp only [Batch0386.cell3088, Batch0386.tau3088, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10102013 (by positivity) using 1 <;> norm_num)
            · have hs1010203 : InSquare (7/64) (-117/320) (1/320) tau := by
                convert childUR hs101020 hx101020 hy101020 using 1 <;> norm_num
              exact Batch0203.cell1630.sound htau (by
                simp only [Batch0203.cell1630, Batch0203.tau1630, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1010203 (by positivity) using 1 <;> norm_num)
        · have hs101022 : InSquare (17/160) (-57/160) (1/160) tau := by
            convert childUL hs10102 hx10102 hy10102 using 1 <;> norm_num
          rcases le_total tau.re (17/160 : ℝ) with hx101022 | hx101022
          · rcases le_total tau.im (-57/160 : ℝ) with hy101022 | hy101022
            · have hs1010220 : InSquare (33/320) (-23/64) (1/320) tau := by
                convert childLL hs101022 hx101022 hy101022 using 1 <;> norm_num
              exact Batch0204.cell1633.sound htau (by
                simp only [Batch0204.cell1633, Batch0204.tau1633, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1010220 (by positivity) using 1 <;> norm_num)
            · have hs1010222 : InSquare (33/320) (-113/320) (1/320) tau := by
                convert childUL hs101022 hx101022 hy101022 using 1 <;> norm_num
              exact Batch0204.cell1635.sound htau (by
                simp only [Batch0204.cell1635, Batch0204.tau1635, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1010222 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-57/160 : ℝ) with hy101022 | hy101022
            · have hs1010221 : InSquare (7/64) (-23/64) (1/320) tau := by
                convert childLR hs101022 hx101022 hy101022 using 1 <;> norm_num
              exact Batch0204.cell1634.sound htau (by
                simp only [Batch0204.cell1634, Batch0204.tau1634, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1010221 (by positivity) using 1 <;> norm_num)
            · have hs1010223 : InSquare (7/64) (-113/320) (1/320) tau := by
                convert childUR hs101022 hx101022 hy101022 using 1 <;> norm_num
              exact Batch0204.cell1636.sound htau (by
                simp only [Batch0204.cell1636, Batch0204.tau1636, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1010223 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-29/80 : ℝ) with hy10102 | hy10102
        · have hs101021 : InSquare (19/160) (-59/160) (1/160) tau := by
            convert childLR hs10102 hx10102 hy10102 using 1 <;> norm_num
          rcases le_total tau.re (19/160 : ℝ) with hx101021 | hx101021
          · rcases le_total tau.im (-59/160 : ℝ) with hy101021 | hy101021
            · have hs1010210 : InSquare (37/320) (-119/320) (1/320) tau := by
                convert childLL hs101021 hx101021 hy101021 using 1 <;> norm_num
              rcases le_total tau.re (37/320 : ℝ) with hx1010210 | hx1010210
              · rcases le_total tau.im (-119/320 : ℝ) with hy1010210 | hy1010210
                · have hs10102100 : InSquare (73/640) (-239/640) (1/640) tau := by
                    convert childLL hs1010210 hx1010210 hy1010210 using 1 <;> norm_num
                  exact Batch0386.cell3089.sound htau (by
                    simp only [Batch0386.cell3089, Batch0386.tau3089, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10102100 (by positivity) using 1 <;> norm_num)
                · have hs10102102 : InSquare (73/640) (-237/640) (1/640) tau := by
                    convert childUL hs1010210 hx1010210 hy1010210 using 1 <;> norm_num
                  exact Batch0386.cell3091.sound htau (by
                    simp only [Batch0386.cell3091, Batch0386.tau3091, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10102102 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-119/320 : ℝ) with hy1010210 | hy1010210
                · have hs10102101 : InSquare (15/128) (-239/640) (1/640) tau := by
                    convert childLR hs1010210 hx1010210 hy1010210 using 1 <;> norm_num
                  exact Batch0386.cell3090.sound htau (by
                    simp only [Batch0386.cell3090, Batch0386.tau3090, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10102101 (by positivity) using 1 <;> norm_num)
                · have hs10102103 : InSquare (15/128) (-237/640) (1/640) tau := by
                    convert childUR hs1010210 hx1010210 hy1010210 using 1 <;> norm_num
                  exact Batch0386.cell3092.sound htau (by
                    simp only [Batch0386.cell3092, Batch0386.tau3092, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10102103 (by positivity) using 1 <;> norm_num)
            · have hs1010212 : InSquare (37/320) (-117/320) (1/320) tau := by
                convert childUL hs101021 hx101021 hy101021 using 1 <;> norm_num
              exact Batch0203.cell1631.sound htau (by
                simp only [Batch0203.cell1631, Batch0203.tau1631, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1010212 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-59/160 : ℝ) with hy101021 | hy101021
            · have hs1010211 : InSquare (39/320) (-119/320) (1/320) tau := by
                convert childLR hs101021 hx101021 hy101021 using 1 <;> norm_num
              rcases le_total tau.re (39/320 : ℝ) with hx1010211 | hx1010211
              · rcases le_total tau.im (-119/320 : ℝ) with hy1010211 | hy1010211
                · have hs10102110 : InSquare (77/640) (-239/640) (1/640) tau := by
                    convert childLL hs1010211 hx1010211 hy1010211 using 1 <;> norm_num
                  exact Batch0386.cell3093.sound htau (by
                    simp only [Batch0386.cell3093, Batch0386.tau3093, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10102110 (by positivity) using 1 <;> norm_num)
                · have hs10102112 : InSquare (77/640) (-237/640) (1/640) tau := by
                    convert childUL hs1010211 hx1010211 hy1010211 using 1 <;> norm_num
                  exact Batch0386.cell3095.sound htau (by
                    simp only [Batch0386.cell3095, Batch0386.tau3095, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10102112 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-119/320 : ℝ) with hy1010211 | hy1010211
                · have hs10102111 : InSquare (79/640) (-239/640) (1/640) tau := by
                    convert childLR hs1010211 hx1010211 hy1010211 using 1 <;> norm_num
                  exact Batch0386.cell3094.sound htau (by
                    simp only [Batch0386.cell3094, Batch0386.tau3094, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10102111 (by positivity) using 1 <;> norm_num)
                · have hs10102113 : InSquare (79/640) (-237/640) (1/640) tau := by
                    convert childUR hs1010211 hx1010211 hy1010211 using 1 <;> norm_num
                  exact Batch0387.cell3096.sound htau (by
                    simp only [Batch0387.cell3096, Batch0387.tau3096, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10102113 (by positivity) using 1 <;> norm_num)
            · have hs1010213 : InSquare (39/320) (-117/320) (1/320) tau := by
                convert childUR hs101021 hx101021 hy101021 using 1 <;> norm_num
              exact Batch0204.cell1632.sound htau (by
                simp only [Batch0204.cell1632, Batch0204.tau1632, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1010213 (by positivity) using 1 <;> norm_num)
        · have hs101023 : InSquare (19/160) (-57/160) (1/160) tau := by
            convert childUR hs10102 hx10102 hy10102 using 1 <;> norm_num
          rcases le_total tau.re (19/160 : ℝ) with hx101023 | hx101023
          · rcases le_total tau.im (-57/160 : ℝ) with hy101023 | hy101023
            · have hs1010230 : InSquare (37/320) (-23/64) (1/320) tau := by
                convert childLL hs101023 hx101023 hy101023 using 1 <;> norm_num
              exact Batch0204.cell1637.sound htau (by
                simp only [Batch0204.cell1637, Batch0204.tau1637, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1010230 (by positivity) using 1 <;> norm_num)
            · have hs1010232 : InSquare (37/320) (-113/320) (1/320) tau := by
                convert childUL hs101023 hx101023 hy101023 using 1 <;> norm_num
              exact Batch0204.cell1639.sound htau (by
                simp only [Batch0204.cell1639, Batch0204.tau1639, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1010232 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-57/160 : ℝ) with hy101023 | hy101023
            · have hs1010231 : InSquare (39/320) (-23/64) (1/320) tau := by
                convert childLR hs101023 hx101023 hy101023 using 1 <;> norm_num
              exact Batch0204.cell1638.sound htau (by
                simp only [Batch0204.cell1638, Batch0204.tau1638, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1010231 (by positivity) using 1 <;> norm_num)
            · have hs1010233 : InSquare (39/320) (-113/320) (1/320) tau := by
                convert childUR hs101023 hx101023 hy101023 using 1 <;> norm_num
              exact Batch0205.cell1640.sound htau (by
                simp only [Batch0205.cell1640, Batch0205.tau1640, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1010233 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (-3/8 : ℝ) with hy1010 | hy1010
    · have hs10101 : InSquare (11/80) (-31/80) (1/80) tau := by
        convert childLR hs hx1010 hy1010 using 1 <;> norm_num
      rcases le_total tau.re (11/80 : ℝ) with hx10101 | hx10101
      · rcases le_total tau.im (-31/80 : ℝ) with hy10101 | hy10101
        · have hs101010 : InSquare (21/160) (-63/160) (1/160) tau := by
            convert childLL hs10101 hx10101 hy10101 using 1 <;> norm_num
          exact (outside_101010 htau hs101010).elim
        · have hs101012 : InSquare (21/160) (-61/160) (1/160) tau := by
            convert childUL hs10101 hx10101 hy10101 using 1 <;> norm_num
          rcases le_total tau.re (21/160 : ℝ) with hx101012 | hx101012
          · rcases le_total tau.im (-61/160 : ℝ) with hy101012 | hy101012
            · have hs1010120 : InSquare (41/320) (-123/320) (1/320) tau := by
                convert childLL hs101012 hx101012 hy101012 using 1 <;> norm_num
              exact (outside_1010120 htau hs1010120).elim
            · have hs1010122 : InSquare (41/320) (-121/320) (1/320) tau := by
                convert childUL hs101012 hx101012 hy101012 using 1 <;> norm_num
              rcases le_total tau.re (41/320 : ℝ) with hx1010122 | hx1010122
              · rcases le_total tau.im (-121/320 : ℝ) with hy1010122 | hy1010122
                · have hs10101220 : InSquare (81/640) (-243/640) (1/640) tau := by
                    convert childLL hs1010122 hx1010122 hy1010122 using 1 <;> norm_num
                  exact Batch0384.cell3074.sound htau (by
                    simp only [Batch0384.cell3074, Batch0384.tau3074, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10101220 (by positivity) using 1 <;> norm_num)
                · have hs10101222 : InSquare (81/640) (-241/640) (1/640) tau := by
                    convert childUL hs1010122 hx1010122 hy1010122 using 1 <;> norm_num
                  exact Batch0384.cell3076.sound htau (by
                    simp only [Batch0384.cell3076, Batch0384.tau3076, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10101222 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-121/320 : ℝ) with hy1010122 | hy1010122
                · have hs10101221 : InSquare (83/640) (-243/640) (1/640) tau := by
                    convert childLR hs1010122 hx1010122 hy1010122 using 1 <;> norm_num
                  exact Batch0384.cell3075.sound htau (by
                    simp only [Batch0384.cell3075, Batch0384.tau3075, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10101221 (by positivity) using 1 <;> norm_num)
                · have hs10101223 : InSquare (83/640) (-241/640) (1/640) tau := by
                    convert childUR hs1010122 hx1010122 hy1010122 using 1 <;> norm_num
                  exact Batch0384.cell3077.sound htau (by
                    simp only [Batch0384.cell3077, Batch0384.tau3077, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10101223 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-61/160 : ℝ) with hy101012 | hy101012
            · have hs1010121 : InSquare (43/320) (-123/320) (1/320) tau := by
                convert childLR hs101012 hx101012 hy101012 using 1 <;> norm_num
              exact (outside_1010121 htau hs1010121).elim
            · have hs1010123 : InSquare (43/320) (-121/320) (1/320) tau := by
                convert childUR hs101012 hx101012 hy101012 using 1 <;> norm_num
              rcases le_total tau.re (43/320 : ℝ) with hx1010123 | hx1010123
              · rcases le_total tau.im (-121/320 : ℝ) with hy1010123 | hy1010123
                · have hs10101230 : InSquare (17/128) (-243/640) (1/640) tau := by
                    convert childLL hs1010123 hx1010123 hy1010123 using 1 <;> norm_num
                  exact (outside_10101230 htau hs10101230).elim
                · have hs10101232 : InSquare (17/128) (-241/640) (1/640) tau := by
                    convert childUL hs1010123 hx1010123 hy1010123 using 1 <;> norm_num
                  exact Batch0384.cell3078.sound htau (by
                    simp only [Batch0384.cell3078, Batch0384.tau3078, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10101232 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-121/320 : ℝ) with hy1010123 | hy1010123
                · have hs10101231 : InSquare (87/640) (-243/640) (1/640) tau := by
                    convert childLR hs1010123 hx1010123 hy1010123 using 1 <;> norm_num
                  exact (outside_10101231 htau hs10101231).elim
                · have hs10101233 : InSquare (87/640) (-241/640) (1/640) tau := by
                    convert childUR hs1010123 hx1010123 hy1010123 using 1 <;> norm_num
                  exact Batch0384.cell3079.sound htau (by
                    simp only [Batch0384.cell3079, Batch0384.tau3079, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10101233 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-31/80 : ℝ) with hy10101 | hy10101
        · have hs101011 : InSquare (23/160) (-63/160) (1/160) tau := by
            convert childLR hs10101 hx10101 hy10101 using 1 <;> norm_num
          exact (outside_101011 htau hs101011).elim
        · have hs101013 : InSquare (23/160) (-61/160) (1/160) tau := by
            convert childUR hs10101 hx10101 hy10101 using 1 <;> norm_num
          rcases le_total tau.re (23/160 : ℝ) with hx101013 | hx101013
          · rcases le_total tau.im (-61/160 : ℝ) with hy101013 | hy101013
            · have hs1010130 : InSquare (9/64) (-123/320) (1/320) tau := by
                convert childLL hs101013 hx101013 hy101013 using 1 <;> norm_num
              exact (outside_1010130 htau hs1010130).elim
            · have hs1010132 : InSquare (9/64) (-121/320) (1/320) tau := by
                convert childUL hs101013 hx101013 hy101013 using 1 <;> norm_num
              rcases le_total tau.re (9/64 : ℝ) with hx1010132 | hx1010132
              · rcases le_total tau.im (-121/320 : ℝ) with hy1010132 | hy1010132
                · have hs10101320 : InSquare (89/640) (-243/640) (1/640) tau := by
                    convert childLL hs1010132 hx1010132 hy1010132 using 1 <;> norm_num
                  exact (outside_10101320 htau hs10101320).elim
                · have hs10101322 : InSquare (89/640) (-241/640) (1/640) tau := by
                    convert childUL hs1010132 hx1010132 hy1010132 using 1 <;> norm_num
                  exact Batch0385.cell3080.sound htau (by
                    simp only [Batch0385.cell3080, Batch0385.tau3080, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10101322 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-121/320 : ℝ) with hy1010132 | hy1010132
                · have hs10101321 : InSquare (91/640) (-243/640) (1/640) tau := by
                    convert childLR hs1010132 hx1010132 hy1010132 using 1 <;> norm_num
                  exact (outside_10101321 htau hs10101321).elim
                · have hs10101323 : InSquare (91/640) (-241/640) (1/640) tau := by
                    convert childUR hs1010132 hx1010132 hy1010132 using 1 <;> norm_num
                  exact (outside_10101323 htau hs10101323).elim
          · rcases le_total tau.im (-61/160 : ℝ) with hy101013 | hy101013
            · have hs1010131 : InSquare (47/320) (-123/320) (1/320) tau := by
                convert childLR hs101013 hx101013 hy101013 using 1 <;> norm_num
              exact (outside_1010131 htau hs1010131).elim
            · have hs1010133 : InSquare (47/320) (-121/320) (1/320) tau := by
                convert childUR hs101013 hx101013 hy101013 using 1 <;> norm_num
              exact (outside_1010133 htau hs1010133).elim
    · have hs10103 : InSquare (11/80) (-29/80) (1/80) tau := by
        convert childUR hs hx1010 hy1010 using 1 <;> norm_num
      rcases le_total tau.re (11/80 : ℝ) with hx10103 | hx10103
      · rcases le_total tau.im (-29/80 : ℝ) with hy10103 | hy10103
        · have hs101030 : InSquare (21/160) (-59/160) (1/160) tau := by
            convert childLL hs10103 hx10103 hy10103 using 1 <;> norm_num
          rcases le_total tau.re (21/160 : ℝ) with hx101030 | hx101030
          · rcases le_total tau.im (-59/160 : ℝ) with hy101030 | hy101030
            · have hs1010300 : InSquare (41/320) (-119/320) (1/320) tau := by
                convert childLL hs101030 hx101030 hy101030 using 1 <;> norm_num
              rcases le_total tau.re (41/320 : ℝ) with hx1010300 | hx1010300
              · rcases le_total tau.im (-119/320 : ℝ) with hy1010300 | hy1010300
                · have hs10103000 : InSquare (81/640) (-239/640) (1/640) tau := by
                    convert childLL hs1010300 hx1010300 hy1010300 using 1 <;> norm_num
                  exact Batch0387.cell3097.sound htau (by
                    simp only [Batch0387.cell3097, Batch0387.tau3097, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10103000 (by positivity) using 1 <;> norm_num)
                · have hs10103002 : InSquare (81/640) (-237/640) (1/640) tau := by
                    convert childUL hs1010300 hx1010300 hy1010300 using 1 <;> norm_num
                  exact Batch0387.cell3099.sound htau (by
                    simp only [Batch0387.cell3099, Batch0387.tau3099, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10103002 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-119/320 : ℝ) with hy1010300 | hy1010300
                · have hs10103001 : InSquare (83/640) (-239/640) (1/640) tau := by
                    convert childLR hs1010300 hx1010300 hy1010300 using 1 <;> norm_num
                  exact Batch0387.cell3098.sound htau (by
                    simp only [Batch0387.cell3098, Batch0387.tau3098, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10103001 (by positivity) using 1 <;> norm_num)
                · have hs10103003 : InSquare (83/640) (-237/640) (1/640) tau := by
                    convert childUR hs1010300 hx1010300 hy1010300 using 1 <;> norm_num
                  exact Batch0387.cell3100.sound htau (by
                    simp only [Batch0387.cell3100, Batch0387.tau3100, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10103003 (by positivity) using 1 <;> norm_num)
            · have hs1010302 : InSquare (41/320) (-117/320) (1/320) tau := by
                convert childUL hs101030 hx101030 hy101030 using 1 <;> norm_num
              rcases le_total tau.re (41/320 : ℝ) with hx1010302 | hx1010302
              · rcases le_total tau.im (-117/320 : ℝ) with hy1010302 | hy1010302
                · have hs10103020 : InSquare (81/640) (-47/128) (1/640) tau := by
                    convert childLL hs1010302 hx1010302 hy1010302 using 1 <;> norm_num
                  exact Batch0388.cell3105.sound htau (by
                    simp only [Batch0388.cell3105, Batch0388.tau3105, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10103020 (by positivity) using 1 <;> norm_num)
                · have hs10103022 : InSquare (81/640) (-233/640) (1/640) tau := by
                    convert childUL hs1010302 hx1010302 hy1010302 using 1 <;> norm_num
                  exact Batch0388.cell3107.sound htau (by
                    simp only [Batch0388.cell3107, Batch0388.tau3107, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10103022 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-117/320 : ℝ) with hy1010302 | hy1010302
                · have hs10103021 : InSquare (83/640) (-47/128) (1/640) tau := by
                    convert childLR hs1010302 hx1010302 hy1010302 using 1 <;> norm_num
                  exact Batch0388.cell3106.sound htau (by
                    simp only [Batch0388.cell3106, Batch0388.tau3106, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10103021 (by positivity) using 1 <;> norm_num)
                · have hs10103023 : InSquare (83/640) (-233/640) (1/640) tau := by
                    convert childUR hs1010302 hx1010302 hy1010302 using 1 <;> norm_num
                  exact Batch0388.cell3108.sound htau (by
                    simp only [Batch0388.cell3108, Batch0388.tau3108, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10103023 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-59/160 : ℝ) with hy101030 | hy101030
            · have hs1010301 : InSquare (43/320) (-119/320) (1/320) tau := by
                convert childLR hs101030 hx101030 hy101030 using 1 <;> norm_num
              rcases le_total tau.re (43/320 : ℝ) with hx1010301 | hx1010301
              · rcases le_total tau.im (-119/320 : ℝ) with hy1010301 | hy1010301
                · have hs10103010 : InSquare (17/128) (-239/640) (1/640) tau := by
                    convert childLL hs1010301 hx1010301 hy1010301 using 1 <;> norm_num
                  exact Batch0387.cell3101.sound htau (by
                    simp only [Batch0387.cell3101, Batch0387.tau3101, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10103010 (by positivity) using 1 <;> norm_num)
                · have hs10103012 : InSquare (17/128) (-237/640) (1/640) tau := by
                    convert childUL hs1010301 hx1010301 hy1010301 using 1 <;> norm_num
                  exact Batch0387.cell3103.sound htau (by
                    simp only [Batch0387.cell3103, Batch0387.tau3103, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10103012 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-119/320 : ℝ) with hy1010301 | hy1010301
                · have hs10103011 : InSquare (87/640) (-239/640) (1/640) tau := by
                    convert childLR hs1010301 hx1010301 hy1010301 using 1 <;> norm_num
                  exact Batch0387.cell3102.sound htau (by
                    simp only [Batch0387.cell3102, Batch0387.tau3102, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10103011 (by positivity) using 1 <;> norm_num)
                · have hs10103013 : InSquare (87/640) (-237/640) (1/640) tau := by
                    convert childUR hs1010301 hx1010301 hy1010301 using 1 <;> norm_num
                  exact Batch0388.cell3104.sound htau (by
                    simp only [Batch0388.cell3104, Batch0388.tau3104, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10103013 (by positivity) using 1 <;> norm_num)
            · have hs1010303 : InSquare (43/320) (-117/320) (1/320) tau := by
                convert childUR hs101030 hx101030 hy101030 using 1 <;> norm_num
              rcases le_total tau.re (43/320 : ℝ) with hx1010303 | hx1010303
              · rcases le_total tau.im (-117/320 : ℝ) with hy1010303 | hy1010303
                · have hs10103030 : InSquare (17/128) (-47/128) (1/640) tau := by
                    convert childLL hs1010303 hx1010303 hy1010303 using 1 <;> norm_num
                  exact Batch0388.cell3109.sound htau (by
                    simp only [Batch0388.cell3109, Batch0388.tau3109, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10103030 (by positivity) using 1 <;> norm_num)
                · have hs10103032 : InSquare (17/128) (-233/640) (1/640) tau := by
                    convert childUL hs1010303 hx1010303 hy1010303 using 1 <;> norm_num
                  exact Batch0388.cell3111.sound htau (by
                    simp only [Batch0388.cell3111, Batch0388.tau3111, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10103032 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-117/320 : ℝ) with hy1010303 | hy1010303
                · have hs10103031 : InSquare (87/640) (-47/128) (1/640) tau := by
                    convert childLR hs1010303 hx1010303 hy1010303 using 1 <;> norm_num
                  exact Batch0388.cell3110.sound htau (by
                    simp only [Batch0388.cell3110, Batch0388.tau3110, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10103031 (by positivity) using 1 <;> norm_num)
                · have hs10103033 : InSquare (87/640) (-233/640) (1/640) tau := by
                    convert childUR hs1010303 hx1010303 hy1010303 using 1 <;> norm_num
                  exact Batch0389.cell3112.sound htau (by
                    simp only [Batch0389.cell3112, Batch0389.tau3112, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10103033 (by positivity) using 1 <;> norm_num)
        · have hs101032 : InSquare (21/160) (-57/160) (1/160) tau := by
            convert childUL hs10103 hx10103 hy10103 using 1 <;> norm_num
          rcases le_total tau.re (21/160 : ℝ) with hx101032 | hx101032
          · rcases le_total tau.im (-57/160 : ℝ) with hy101032 | hy101032
            · have hs1010320 : InSquare (41/320) (-23/64) (1/320) tau := by
                convert childLL hs101032 hx101032 hy101032 using 1 <;> norm_num
              exact Batch0205.cell1641.sound htau (by
                simp only [Batch0205.cell1641, Batch0205.tau1641, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1010320 (by positivity) using 1 <;> norm_num)
            · have hs1010322 : InSquare (41/320) (-113/320) (1/320) tau := by
                convert childUL hs101032 hx101032 hy101032 using 1 <;> norm_num
              exact Batch0205.cell1643.sound htau (by
                simp only [Batch0205.cell1643, Batch0205.tau1643, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1010322 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-57/160 : ℝ) with hy101032 | hy101032
            · have hs1010321 : InSquare (43/320) (-23/64) (1/320) tau := by
                convert childLR hs101032 hx101032 hy101032 using 1 <;> norm_num
              exact Batch0205.cell1642.sound htau (by
                simp only [Batch0205.cell1642, Batch0205.tau1642, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1010321 (by positivity) using 1 <;> norm_num)
            · have hs1010323 : InSquare (43/320) (-113/320) (1/320) tau := by
                convert childUR hs101032 hx101032 hy101032 using 1 <;> norm_num
              exact Batch0205.cell1644.sound htau (by
                simp only [Batch0205.cell1644, Batch0205.tau1644, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1010323 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-29/80 : ℝ) with hy10103 | hy10103
        · have hs101031 : InSquare (23/160) (-59/160) (1/160) tau := by
            convert childLR hs10103 hx10103 hy10103 using 1 <;> norm_num
          rcases le_total tau.re (23/160 : ℝ) with hx101031 | hx101031
          · rcases le_total tau.im (-59/160 : ℝ) with hy101031 | hy101031
            · have hs1010310 : InSquare (9/64) (-119/320) (1/320) tau := by
                convert childLL hs101031 hx101031 hy101031 using 1 <;> norm_num
              rcases le_total tau.re (9/64 : ℝ) with hx1010310 | hx1010310
              · rcases le_total tau.im (-119/320 : ℝ) with hy1010310 | hy1010310
                · have hs10103100 : InSquare (89/640) (-239/640) (1/640) tau := by
                    convert childLL hs1010310 hx1010310 hy1010310 using 1 <;> norm_num
                  exact Batch0389.cell3113.sound htau (by
                    simp only [Batch0389.cell3113, Batch0389.tau3113, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10103100 (by positivity) using 1 <;> norm_num)
                · have hs10103102 : InSquare (89/640) (-237/640) (1/640) tau := by
                    convert childUL hs1010310 hx1010310 hy1010310 using 1 <;> norm_num
                  exact Batch0389.cell3115.sound htau (by
                    simp only [Batch0389.cell3115, Batch0389.tau3115, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10103102 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-119/320 : ℝ) with hy1010310 | hy1010310
                · have hs10103101 : InSquare (91/640) (-239/640) (1/640) tau := by
                    convert childLR hs1010310 hx1010310 hy1010310 using 1 <;> norm_num
                  exact Batch0389.cell3114.sound htau (by
                    simp only [Batch0389.cell3114, Batch0389.tau3114, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10103101 (by positivity) using 1 <;> norm_num)
                · have hs10103103 : InSquare (91/640) (-237/640) (1/640) tau := by
                    convert childUR hs1010310 hx1010310 hy1010310 using 1 <;> norm_num
                  exact Batch0389.cell3116.sound htau (by
                    simp only [Batch0389.cell3116, Batch0389.tau3116, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10103103 (by positivity) using 1 <;> norm_num)
            · have hs1010312 : InSquare (9/64) (-117/320) (1/320) tau := by
                convert childUL hs101031 hx101031 hy101031 using 1 <;> norm_num
              rcases le_total tau.re (9/64 : ℝ) with hx1010312 | hx1010312
              · rcases le_total tau.im (-117/320 : ℝ) with hy1010312 | hy1010312
                · have hs10103120 : InSquare (89/640) (-47/128) (1/640) tau := by
                    convert childLL hs1010312 hx1010312 hy1010312 using 1 <;> norm_num
                  exact Batch0390.cell3121.sound htau (by
                    simp only [Batch0390.cell3121, Batch0390.tau3121, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10103120 (by positivity) using 1 <;> norm_num)
                · have hs10103122 : InSquare (89/640) (-233/640) (1/640) tau := by
                    convert childUL hs1010312 hx1010312 hy1010312 using 1 <;> norm_num
                  exact Batch0390.cell3123.sound htau (by
                    simp only [Batch0390.cell3123, Batch0390.tau3123, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10103122 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-117/320 : ℝ) with hy1010312 | hy1010312
                · have hs10103121 : InSquare (91/640) (-47/128) (1/640) tau := by
                    convert childLR hs1010312 hx1010312 hy1010312 using 1 <;> norm_num
                  exact Batch0390.cell3122.sound htau (by
                    simp only [Batch0390.cell3122, Batch0390.tau3122, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10103121 (by positivity) using 1 <;> norm_num)
                · have hs10103123 : InSquare (91/640) (-233/640) (1/640) tau := by
                    convert childUR hs1010312 hx1010312 hy1010312 using 1 <;> norm_num
                  exact Batch0390.cell3124.sound htau (by
                    simp only [Batch0390.cell3124, Batch0390.tau3124, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10103123 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-59/160 : ℝ) with hy101031 | hy101031
            · have hs1010311 : InSquare (47/320) (-119/320) (1/320) tau := by
                convert childLR hs101031 hx101031 hy101031 using 1 <;> norm_num
              rcases le_total tau.re (47/320 : ℝ) with hx1010311 | hx1010311
              · rcases le_total tau.im (-119/320 : ℝ) with hy1010311 | hy1010311
                · have hs10103110 : InSquare (93/640) (-239/640) (1/640) tau := by
                    convert childLL hs1010311 hx1010311 hy1010311 using 1 <;> norm_num
                  exact Batch0389.cell3117.sound htau (by
                    simp only [Batch0389.cell3117, Batch0389.tau3117, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10103110 (by positivity) using 1 <;> norm_num)
                · have hs10103112 : InSquare (93/640) (-237/640) (1/640) tau := by
                    convert childUL hs1010311 hx1010311 hy1010311 using 1 <;> norm_num
                  exact Batch0389.cell3119.sound htau (by
                    simp only [Batch0389.cell3119, Batch0389.tau3119, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10103112 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-119/320 : ℝ) with hy1010311 | hy1010311
                · have hs10103111 : InSquare (19/128) (-239/640) (1/640) tau := by
                    convert childLR hs1010311 hx1010311 hy1010311 using 1 <;> norm_num
                  exact Batch0389.cell3118.sound htau (by
                    simp only [Batch0389.cell3118, Batch0389.tau3118, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10103111 (by positivity) using 1 <;> norm_num)
                · have hs10103113 : InSquare (19/128) (-237/640) (1/640) tau := by
                    convert childUR hs1010311 hx1010311 hy1010311 using 1 <;> norm_num
                  exact Batch0390.cell3120.sound htau (by
                    simp only [Batch0390.cell3120, Batch0390.tau3120, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10103113 (by positivity) using 1 <;> norm_num)
            · have hs1010313 : InSquare (47/320) (-117/320) (1/320) tau := by
                convert childUR hs101031 hx101031 hy101031 using 1 <;> norm_num
              rcases le_total tau.re (47/320 : ℝ) with hx1010313 | hx1010313
              · rcases le_total tau.im (-117/320 : ℝ) with hy1010313 | hy1010313
                · have hs10103130 : InSquare (93/640) (-47/128) (1/640) tau := by
                    convert childLL hs1010313 hx1010313 hy1010313 using 1 <;> norm_num
                  exact Batch0390.cell3125.sound htau (by
                    simp only [Batch0390.cell3125, Batch0390.tau3125, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10103130 (by positivity) using 1 <;> norm_num)
                · have hs10103132 : InSquare (93/640) (-233/640) (1/640) tau := by
                    convert childUL hs1010313 hx1010313 hy1010313 using 1 <;> norm_num
                  exact Batch0390.cell3127.sound htau (by
                    simp only [Batch0390.cell3127, Batch0390.tau3127, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10103132 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-117/320 : ℝ) with hy1010313 | hy1010313
                · have hs10103131 : InSquare (19/128) (-47/128) (1/640) tau := by
                    convert childLR hs1010313 hx1010313 hy1010313 using 1 <;> norm_num
                  exact Batch0390.cell3126.sound htau (by
                    simp only [Batch0390.cell3126, Batch0390.tau3126, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10103131 (by positivity) using 1 <;> norm_num)
                · have hs10103133 : InSquare (19/128) (-233/640) (1/640) tau := by
                    convert childUR hs1010313 hx1010313 hy1010313 using 1 <;> norm_num
                  exact Batch0391.cell3128.sound htau (by
                    simp only [Batch0391.cell3128, Batch0391.tau3128, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10103133 (by positivity) using 1 <;> norm_num)
        · have hs101033 : InSquare (23/160) (-57/160) (1/160) tau := by
            convert childUR hs10103 hx10103 hy10103 using 1 <;> norm_num
          rcases le_total tau.re (23/160 : ℝ) with hx101033 | hx101033
          · rcases le_total tau.im (-57/160 : ℝ) with hy101033 | hy101033
            · have hs1010330 : InSquare (9/64) (-23/64) (1/320) tau := by
                convert childLL hs101033 hx101033 hy101033 using 1 <;> norm_num
              exact Batch0205.cell1645.sound htau (by
                simp only [Batch0205.cell1645, Batch0205.tau1645, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1010330 (by positivity) using 1 <;> norm_num)
            · have hs1010332 : InSquare (9/64) (-113/320) (1/320) tau := by
                convert childUL hs101033 hx101033 hy101033 using 1 <;> norm_num
              exact Batch0205.cell1646.sound htau (by
                simp only [Batch0205.cell1646, Batch0205.tau1646, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1010332 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-57/160 : ℝ) with hy101033 | hy101033
            · have hs1010331 : InSquare (47/320) (-23/64) (1/320) tau := by
                convert childLR hs101033 hx101033 hy101033 using 1 <;> norm_num
              rcases le_total tau.re (47/320 : ℝ) with hx1010331 | hx1010331
              · rcases le_total tau.im (-23/64 : ℝ) with hy1010331 | hy1010331
                · have hs10103310 : InSquare (93/640) (-231/640) (1/640) tau := by
                    convert childLL hs1010331 hx1010331 hy1010331 using 1 <;> norm_num
                  exact Batch0391.cell3129.sound htau (by
                    simp only [Batch0391.cell3129, Batch0391.tau3129, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10103310 (by positivity) using 1 <;> norm_num)
                · have hs10103312 : InSquare (93/640) (-229/640) (1/640) tau := by
                    convert childUL hs1010331 hx1010331 hy1010331 using 1 <;> norm_num
                  exact Batch0391.cell3131.sound htau (by
                    simp only [Batch0391.cell3131, Batch0391.tau3131, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10103312 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-23/64 : ℝ) with hy1010331 | hy1010331
                · have hs10103311 : InSquare (19/128) (-231/640) (1/640) tau := by
                    convert childLR hs1010331 hx1010331 hy1010331 using 1 <;> norm_num
                  exact Batch0391.cell3130.sound htau (by
                    simp only [Batch0391.cell3130, Batch0391.tau3130, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10103311 (by positivity) using 1 <;> norm_num)
                · have hs10103313 : InSquare (19/128) (-229/640) (1/640) tau := by
                    convert childUR hs1010331 hx1010331 hy1010331 using 1 <;> norm_num
                  exact Batch0391.cell3132.sound htau (by
                    simp only [Batch0391.cell3132, Batch0391.tau3132, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs10103313 (by positivity) using 1 <;> norm_num)
            · have hs1010333 : InSquare (47/320) (-113/320) (1/320) tau := by
                convert childUR hs101033 hx101033 hy101033 using 1 <;> norm_num
              exact Batch0205.cell1647.sound htau (by
                simp only [Batch0205.cell1647, Batch0205.tau1647, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1010333 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1010
