import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0217
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0218
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0219
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0220
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0221
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0398
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0399
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0400

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1102

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

private theorem outside_110210 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (37/160) (-11/32) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (9/40 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-9/40)]
  have himSq : (27/80 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+27/80)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_110211 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (39/160) (-11/32) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (19/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-19/80)]
  have himSq : (27/80 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+27/80)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_110213 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (39/160) (-53/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (19/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-19/80)]
  have himSq : (13/40 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+13/40)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_1102001 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (67/320) (-111/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (33/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-33/160)]
  have himSq : (11/32 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+11/32)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_1102010 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (69/320) (-111/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (17/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-17/80)]
  have himSq : (11/32 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+11/32)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_1102011 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (71/320) (-111/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (7/32 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-7/32)]
  have himSq : (11/32 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+11/32)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_1102013 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (71/320) (-109/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (7/32 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-7/32)]
  have himSq : (27/80 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+27/80)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_1102120 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (73/320) (-107/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (9/40 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-9/40)]
  have himSq : (53/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+53/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_1102121 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (15/64) (-107/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (37/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-37/160)]
  have himSq : (53/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+53/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_1102311 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (79/320) (-103/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (39/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-39/160)]
  have himSq : (51/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+51/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_11020000 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (129/640) (-223/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (1/5 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-1/5)]
  have himSq : (111/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+111/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_11020001 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (131/640) (-223/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (13/64 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-13/64)]
  have himSq : (111/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+111/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_11020120 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (137/640) (-219/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (17/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-17/80)]
  have himSq : (109/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+109/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_11020121 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (139/640) (-219/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (69/320 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-69/320)]
  have himSq : (109/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+109/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_11020123 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (139/640) (-217/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (69/320 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-69/320)]
  have himSq : (27/80 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+27/80)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_11020311 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (143/640) (-43/128) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (71/320 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-71/320)]
  have himSq : (107/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+107/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_11021230 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (149/640) (-211/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (37/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-37/160)]
  have himSq : (21/64 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+21/64)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_11021231 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (151/640) (-211/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (15/64 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-15/64)]
  have himSq : (21/64 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+21/64)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_11021233 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (151/640) (-209/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (15/64 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-15/64)]
  have himSq : (13/40 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+13/40)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (9/40) (-13/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (9/40 : ℝ) with hx1102 | hx1102
  · rcases le_total tau.im (-13/40 : ℝ) with hy1102 | hy1102
    · have hs11020 : InSquare (17/80) (-27/80) (1/80) tau := by
        convert childLL hs hx1102 hy1102 using 1 <;> norm_num
      rcases le_total tau.re (17/80 : ℝ) with hx11020 | hx11020
      · rcases le_total tau.im (-27/80 : ℝ) with hy11020 | hy11020
        · have hs110200 : InSquare (33/160) (-11/32) (1/160) tau := by
            convert childLL hs11020 hx11020 hy11020 using 1 <;> norm_num
          rcases le_total tau.re (33/160 : ℝ) with hx110200 | hx110200
          · rcases le_total tau.im (-11/32 : ℝ) with hy110200 | hy110200
            · have hs1102000 : InSquare (13/64) (-111/320) (1/320) tau := by
                convert childLL hs110200 hx110200 hy110200 using 1 <;> norm_num
              rcases le_total tau.re (13/64 : ℝ) with hx1102000 | hx1102000
              · rcases le_total tau.im (-111/320 : ℝ) with hy1102000 | hy1102000
                · have hs11020000 : InSquare (129/640) (-223/640) (1/640) tau := by
                    convert childLL hs1102000 hx1102000 hy1102000 using 1 <;> norm_num
                  exact (outside_11020000 htau hs11020000).elim
                · have hs11020002 : InSquare (129/640) (-221/640) (1/640) tau := by
                    convert childUL hs1102000 hx1102000 hy1102000 using 1 <;> norm_num
                  exact Batch0398.cell3189.sound htau (by
                    simp only [Batch0398.cell3189, Batch0398.tau3189, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs11020002 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-111/320 : ℝ) with hy1102000 | hy1102000
                · have hs11020001 : InSquare (131/640) (-223/640) (1/640) tau := by
                    convert childLR hs1102000 hx1102000 hy1102000 using 1 <;> norm_num
                  exact (outside_11020001 htau hs11020001).elim
                · have hs11020003 : InSquare (131/640) (-221/640) (1/640) tau := by
                    convert childUR hs1102000 hx1102000 hy1102000 using 1 <;> norm_num
                  exact Batch0398.cell3190.sound htau (by
                    simp only [Batch0398.cell3190, Batch0398.tau3190, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs11020003 (by positivity) using 1 <;> norm_num)
            · have hs1102002 : InSquare (13/64) (-109/320) (1/320) tau := by
                convert childUL hs110200 hx110200 hy110200 using 1 <;> norm_num
              rcases le_total tau.re (13/64 : ℝ) with hx1102002 | hx1102002
              · rcases le_total tau.im (-109/320 : ℝ) with hy1102002 | hy1102002
                · have hs11020020 : InSquare (129/640) (-219/640) (1/640) tau := by
                    convert childLL hs1102002 hx1102002 hy1102002 using 1 <;> norm_num
                  exact Batch0398.cell3191.sound htau (by
                    simp only [Batch0398.cell3191, Batch0398.tau3191, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs11020020 (by positivity) using 1 <;> norm_num)
                · have hs11020022 : InSquare (129/640) (-217/640) (1/640) tau := by
                    convert childUL hs1102002 hx1102002 hy1102002 using 1 <;> norm_num
                  exact Batch0399.cell3193.sound htau (by
                    simp only [Batch0399.cell3193, Batch0399.tau3193, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs11020022 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-109/320 : ℝ) with hy1102002 | hy1102002
                · have hs11020021 : InSquare (131/640) (-219/640) (1/640) tau := by
                    convert childLR hs1102002 hx1102002 hy1102002 using 1 <;> norm_num
                  exact Batch0399.cell3192.sound htau (by
                    simp only [Batch0399.cell3192, Batch0399.tau3192, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs11020021 (by positivity) using 1 <;> norm_num)
                · have hs11020023 : InSquare (131/640) (-217/640) (1/640) tau := by
                    convert childUR hs1102002 hx1102002 hy1102002 using 1 <;> norm_num
                  exact Batch0399.cell3194.sound htau (by
                    simp only [Batch0399.cell3194, Batch0399.tau3194, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs11020023 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-11/32 : ℝ) with hy110200 | hy110200
            · have hs1102001 : InSquare (67/320) (-111/320) (1/320) tau := by
                convert childLR hs110200 hx110200 hy110200 using 1 <;> norm_num
              exact (outside_1102001 htau hs1102001).elim
            · have hs1102003 : InSquare (67/320) (-109/320) (1/320) tau := by
                convert childUR hs110200 hx110200 hy110200 using 1 <;> norm_num
              rcases le_total tau.re (67/320 : ℝ) with hx1102003 | hx1102003
              · rcases le_total tau.im (-109/320 : ℝ) with hy1102003 | hy1102003
                · have hs11020030 : InSquare (133/640) (-219/640) (1/640) tau := by
                    convert childLL hs1102003 hx1102003 hy1102003 using 1 <;> norm_num
                  exact Batch0399.cell3195.sound htau (by
                    simp only [Batch0399.cell3195, Batch0399.tau3195, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs11020030 (by positivity) using 1 <;> norm_num)
                · have hs11020032 : InSquare (133/640) (-217/640) (1/640) tau := by
                    convert childUL hs1102003 hx1102003 hy1102003 using 1 <;> norm_num
                  exact Batch0399.cell3197.sound htau (by
                    simp only [Batch0399.cell3197, Batch0399.tau3197, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs11020032 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-109/320 : ℝ) with hy1102003 | hy1102003
                · have hs11020031 : InSquare (27/128) (-219/640) (1/640) tau := by
                    convert childLR hs1102003 hx1102003 hy1102003 using 1 <;> norm_num
                  exact Batch0399.cell3196.sound htau (by
                    simp only [Batch0399.cell3196, Batch0399.tau3196, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs11020031 (by positivity) using 1 <;> norm_num)
                · have hs11020033 : InSquare (27/128) (-217/640) (1/640) tau := by
                    convert childUR hs1102003 hx1102003 hy1102003 using 1 <;> norm_num
                  exact Batch0399.cell3198.sound htau (by
                    simp only [Batch0399.cell3198, Batch0399.tau3198, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs11020033 (by positivity) using 1 <;> norm_num)
        · have hs110202 : InSquare (33/160) (-53/160) (1/160) tau := by
            convert childUL hs11020 hx11020 hy11020 using 1 <;> norm_num
          rcases le_total tau.re (33/160 : ℝ) with hx110202 | hx110202
          · rcases le_total tau.im (-53/160 : ℝ) with hy110202 | hy110202
            · have hs1102020 : InSquare (13/64) (-107/320) (1/320) tau := by
                convert childLL hs110202 hx110202 hy110202 using 1 <;> norm_num
              exact Batch0217.cell1737.sound htau (by
                simp only [Batch0217.cell1737, Batch0217.tau1737, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1102020 (by positivity) using 1 <;> norm_num)
            · have hs1102022 : InSquare (13/64) (-21/64) (1/320) tau := by
                convert childUL hs110202 hx110202 hy110202 using 1 <;> norm_num
              exact Batch0217.cell1739.sound htau (by
                simp only [Batch0217.cell1739, Batch0217.tau1739, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1102022 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-53/160 : ℝ) with hy110202 | hy110202
            · have hs1102021 : InSquare (67/320) (-107/320) (1/320) tau := by
                convert childLR hs110202 hx110202 hy110202 using 1 <;> norm_num
              exact Batch0217.cell1738.sound htau (by
                simp only [Batch0217.cell1738, Batch0217.tau1738, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1102021 (by positivity) using 1 <;> norm_num)
            · have hs1102023 : InSquare (67/320) (-21/64) (1/320) tau := by
                convert childUR hs110202 hx110202 hy110202 using 1 <;> norm_num
              exact Batch0217.cell1740.sound htau (by
                simp only [Batch0217.cell1740, Batch0217.tau1740, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1102023 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-27/80 : ℝ) with hy11020 | hy11020
        · have hs110201 : InSquare (7/32) (-11/32) (1/160) tau := by
            convert childLR hs11020 hx11020 hy11020 using 1 <;> norm_num
          rcases le_total tau.re (7/32 : ℝ) with hx110201 | hx110201
          · rcases le_total tau.im (-11/32 : ℝ) with hy110201 | hy110201
            · have hs1102010 : InSquare (69/320) (-111/320) (1/320) tau := by
                convert childLL hs110201 hx110201 hy110201 using 1 <;> norm_num
              exact (outside_1102010 htau hs1102010).elim
            · have hs1102012 : InSquare (69/320) (-109/320) (1/320) tau := by
                convert childUL hs110201 hx110201 hy110201 using 1 <;> norm_num
              rcases le_total tau.re (69/320 : ℝ) with hx1102012 | hx1102012
              · rcases le_total tau.im (-109/320 : ℝ) with hy1102012 | hy1102012
                · have hs11020120 : InSquare (137/640) (-219/640) (1/640) tau := by
                    convert childLL hs1102012 hx1102012 hy1102012 using 1 <;> norm_num
                  exact (outside_11020120 htau hs11020120).elim
                · have hs11020122 : InSquare (137/640) (-217/640) (1/640) tau := by
                    convert childUL hs1102012 hx1102012 hy1102012 using 1 <;> norm_num
                  exact Batch0399.cell3199.sound htau (by
                    simp only [Batch0399.cell3199, Batch0399.tau3199, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs11020122 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-109/320 : ℝ) with hy1102012 | hy1102012
                · have hs11020121 : InSquare (139/640) (-219/640) (1/640) tau := by
                    convert childLR hs1102012 hx1102012 hy1102012 using 1 <;> norm_num
                  exact (outside_11020121 htau hs11020121).elim
                · have hs11020123 : InSquare (139/640) (-217/640) (1/640) tau := by
                    convert childUR hs1102012 hx1102012 hy1102012 using 1 <;> norm_num
                  exact (outside_11020123 htau hs11020123).elim
          · rcases le_total tau.im (-11/32 : ℝ) with hy110201 | hy110201
            · have hs1102011 : InSquare (71/320) (-111/320) (1/320) tau := by
                convert childLR hs110201 hx110201 hy110201 using 1 <;> norm_num
              exact (outside_1102011 htau hs1102011).elim
            · have hs1102013 : InSquare (71/320) (-109/320) (1/320) tau := by
                convert childUR hs110201 hx110201 hy110201 using 1 <;> norm_num
              exact (outside_1102013 htau hs1102013).elim
        · have hs110203 : InSquare (7/32) (-53/160) (1/160) tau := by
            convert childUR hs11020 hx11020 hy11020 using 1 <;> norm_num
          rcases le_total tau.re (7/32 : ℝ) with hx110203 | hx110203
          · rcases le_total tau.im (-53/160 : ℝ) with hy110203 | hy110203
            · have hs1102030 : InSquare (69/320) (-107/320) (1/320) tau := by
                convert childLL hs110203 hx110203 hy110203 using 1 <;> norm_num
              exact Batch0217.cell1741.sound htau (by
                simp only [Batch0217.cell1741, Batch0217.tau1741, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1102030 (by positivity) using 1 <;> norm_num)
            · have hs1102032 : InSquare (69/320) (-21/64) (1/320) tau := by
                convert childUL hs110203 hx110203 hy110203 using 1 <;> norm_num
              exact Batch0217.cell1742.sound htau (by
                simp only [Batch0217.cell1742, Batch0217.tau1742, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1102032 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-53/160 : ℝ) with hy110203 | hy110203
            · have hs1102031 : InSquare (71/320) (-107/320) (1/320) tau := by
                convert childLR hs110203 hx110203 hy110203 using 1 <;> norm_num
              rcases le_total tau.re (71/320 : ℝ) with hx1102031 | hx1102031
              · rcases le_total tau.im (-107/320 : ℝ) with hy1102031 | hy1102031
                · have hs11020310 : InSquare (141/640) (-43/128) (1/640) tau := by
                    convert childLL hs1102031 hx1102031 hy1102031 using 1 <;> norm_num
                  exact Batch0400.cell3200.sound htau (by
                    simp only [Batch0400.cell3200, Batch0400.tau3200, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs11020310 (by positivity) using 1 <;> norm_num)
                · have hs11020312 : InSquare (141/640) (-213/640) (1/640) tau := by
                    convert childUL hs1102031 hx1102031 hy1102031 using 1 <;> norm_num
                  exact Batch0400.cell3201.sound htau (by
                    simp only [Batch0400.cell3201, Batch0400.tau3201, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs11020312 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-107/320 : ℝ) with hy1102031 | hy1102031
                · have hs11020311 : InSquare (143/640) (-43/128) (1/640) tau := by
                    convert childLR hs1102031 hx1102031 hy1102031 using 1 <;> norm_num
                  exact (outside_11020311 htau hs11020311).elim
                · have hs11020313 : InSquare (143/640) (-213/640) (1/640) tau := by
                    convert childUR hs1102031 hx1102031 hy1102031 using 1 <;> norm_num
                  exact Batch0400.cell3202.sound htau (by
                    simp only [Batch0400.cell3202, Batch0400.tau3202, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs11020313 (by positivity) using 1 <;> norm_num)
            · have hs1102033 : InSquare (71/320) (-21/64) (1/320) tau := by
                convert childUR hs110203 hx110203 hy110203 using 1 <;> norm_num
              exact Batch0217.cell1743.sound htau (by
                simp only [Batch0217.cell1743, Batch0217.tau1743, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1102033 (by positivity) using 1 <;> norm_num)
    · have hs11022 : InSquare (17/80) (-5/16) (1/80) tau := by
        convert childUL hs hx1102 hy1102 using 1 <;> norm_num
      rcases le_total tau.re (17/80 : ℝ) with hx11022 | hx11022
      · rcases le_total tau.im (-5/16 : ℝ) with hy11022 | hy11022
        · have hs110220 : InSquare (33/160) (-51/160) (1/160) tau := by
            convert childLL hs11022 hx11022 hy11022 using 1 <;> norm_num
          rcases le_total tau.re (33/160 : ℝ) with hx110220 | hx110220
          · rcases le_total tau.im (-51/160 : ℝ) with hy110220 | hy110220
            · have hs1102200 : InSquare (13/64) (-103/320) (1/320) tau := by
                convert childLL hs110220 hx110220 hy110220 using 1 <;> norm_num
              exact Batch0218.cell1745.sound htau (by
                simp only [Batch0218.cell1745, Batch0218.tau1745, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1102200 (by positivity) using 1 <;> norm_num)
            · have hs1102202 : InSquare (13/64) (-101/320) (1/320) tau := by
                convert childUL hs110220 hx110220 hy110220 using 1 <;> norm_num
              exact Batch0218.cell1747.sound htau (by
                simp only [Batch0218.cell1747, Batch0218.tau1747, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1102202 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-51/160 : ℝ) with hy110220 | hy110220
            · have hs1102201 : InSquare (67/320) (-103/320) (1/320) tau := by
                convert childLR hs110220 hx110220 hy110220 using 1 <;> norm_num
              exact Batch0218.cell1746.sound htau (by
                simp only [Batch0218.cell1746, Batch0218.tau1746, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1102201 (by positivity) using 1 <;> norm_num)
            · have hs1102203 : InSquare (67/320) (-101/320) (1/320) tau := by
                convert childUR hs110220 hx110220 hy110220 using 1 <;> norm_num
              exact Batch0218.cell1748.sound htau (by
                simp only [Batch0218.cell1748, Batch0218.tau1748, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1102203 (by positivity) using 1 <;> norm_num)
        · have hs110222 : InSquare (33/160) (-49/160) (1/160) tau := by
            convert childUL hs11022 hx11022 hy11022 using 1 <;> norm_num
          rcases le_total tau.re (33/160 : ℝ) with hx110222 | hx110222
          · rcases le_total tau.im (-49/160 : ℝ) with hy110222 | hy110222
            · have hs1102220 : InSquare (13/64) (-99/320) (1/320) tau := by
                convert childLL hs110222 hx110222 hy110222 using 1 <;> norm_num
              exact Batch0219.cell1753.sound htau (by
                simp only [Batch0219.cell1753, Batch0219.tau1753, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1102220 (by positivity) using 1 <;> norm_num)
            · have hs1102222 : InSquare (13/64) (-97/320) (1/320) tau := by
                convert childUL hs110222 hx110222 hy110222 using 1 <;> norm_num
              exact Batch0219.cell1755.sound htau (by
                simp only [Batch0219.cell1755, Batch0219.tau1755, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1102222 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-49/160 : ℝ) with hy110222 | hy110222
            · have hs1102221 : InSquare (67/320) (-99/320) (1/320) tau := by
                convert childLR hs110222 hx110222 hy110222 using 1 <;> norm_num
              exact Batch0219.cell1754.sound htau (by
                simp only [Batch0219.cell1754, Batch0219.tau1754, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1102221 (by positivity) using 1 <;> norm_num)
            · have hs1102223 : InSquare (67/320) (-97/320) (1/320) tau := by
                convert childUR hs110222 hx110222 hy110222 using 1 <;> norm_num
              exact Batch0219.cell1756.sound htau (by
                simp only [Batch0219.cell1756, Batch0219.tau1756, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1102223 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-5/16 : ℝ) with hy11022 | hy11022
        · have hs110221 : InSquare (7/32) (-51/160) (1/160) tau := by
            convert childLR hs11022 hx11022 hy11022 using 1 <;> norm_num
          rcases le_total tau.re (7/32 : ℝ) with hx110221 | hx110221
          · rcases le_total tau.im (-51/160 : ℝ) with hy110221 | hy110221
            · have hs1102210 : InSquare (69/320) (-103/320) (1/320) tau := by
                convert childLL hs110221 hx110221 hy110221 using 1 <;> norm_num
              exact Batch0218.cell1749.sound htau (by
                simp only [Batch0218.cell1749, Batch0218.tau1749, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1102210 (by positivity) using 1 <;> norm_num)
            · have hs1102212 : InSquare (69/320) (-101/320) (1/320) tau := by
                convert childUL hs110221 hx110221 hy110221 using 1 <;> norm_num
              exact Batch0218.cell1751.sound htau (by
                simp only [Batch0218.cell1751, Batch0218.tau1751, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1102212 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-51/160 : ℝ) with hy110221 | hy110221
            · have hs1102211 : InSquare (71/320) (-103/320) (1/320) tau := by
                convert childLR hs110221 hx110221 hy110221 using 1 <;> norm_num
              exact Batch0218.cell1750.sound htau (by
                simp only [Batch0218.cell1750, Batch0218.tau1750, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1102211 (by positivity) using 1 <;> norm_num)
            · have hs1102213 : InSquare (71/320) (-101/320) (1/320) tau := by
                convert childUR hs110221 hx110221 hy110221 using 1 <;> norm_num
              exact Batch0219.cell1752.sound htau (by
                simp only [Batch0219.cell1752, Batch0219.tau1752, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1102213 (by positivity) using 1 <;> norm_num)
        · have hs110223 : InSquare (7/32) (-49/160) (1/160) tau := by
            convert childUR hs11022 hx11022 hy11022 using 1 <;> norm_num
          rcases le_total tau.re (7/32 : ℝ) with hx110223 | hx110223
          · rcases le_total tau.im (-49/160 : ℝ) with hy110223 | hy110223
            · have hs1102230 : InSquare (69/320) (-99/320) (1/320) tau := by
                convert childLL hs110223 hx110223 hy110223 using 1 <;> norm_num
              exact Batch0219.cell1757.sound htau (by
                simp only [Batch0219.cell1757, Batch0219.tau1757, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1102230 (by positivity) using 1 <;> norm_num)
            · have hs1102232 : InSquare (69/320) (-97/320) (1/320) tau := by
                convert childUL hs110223 hx110223 hy110223 using 1 <;> norm_num
              exact Batch0219.cell1759.sound htau (by
                simp only [Batch0219.cell1759, Batch0219.tau1759, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1102232 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-49/160 : ℝ) with hy110223 | hy110223
            · have hs1102231 : InSquare (71/320) (-99/320) (1/320) tau := by
                convert childLR hs110223 hx110223 hy110223 using 1 <;> norm_num
              exact Batch0219.cell1758.sound htau (by
                simp only [Batch0219.cell1758, Batch0219.tau1758, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1102231 (by positivity) using 1 <;> norm_num)
            · have hs1102233 : InSquare (71/320) (-97/320) (1/320) tau := by
                convert childUR hs110223 hx110223 hy110223 using 1 <;> norm_num
              exact Batch0220.cell1760.sound htau (by
                simp only [Batch0220.cell1760, Batch0220.tau1760, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1102233 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (-13/40 : ℝ) with hy1102 | hy1102
    · have hs11021 : InSquare (19/80) (-27/80) (1/80) tau := by
        convert childLR hs hx1102 hy1102 using 1 <;> norm_num
      rcases le_total tau.re (19/80 : ℝ) with hx11021 | hx11021
      · rcases le_total tau.im (-27/80 : ℝ) with hy11021 | hy11021
        · have hs110210 : InSquare (37/160) (-11/32) (1/160) tau := by
            convert childLL hs11021 hx11021 hy11021 using 1 <;> norm_num
          exact (outside_110210 htau hs110210).elim
        · have hs110212 : InSquare (37/160) (-53/160) (1/160) tau := by
            convert childUL hs11021 hx11021 hy11021 using 1 <;> norm_num
          rcases le_total tau.re (37/160 : ℝ) with hx110212 | hx110212
          · rcases le_total tau.im (-53/160 : ℝ) with hy110212 | hy110212
            · have hs1102120 : InSquare (73/320) (-107/320) (1/320) tau := by
                convert childLL hs110212 hx110212 hy110212 using 1 <;> norm_num
              exact (outside_1102120 htau hs1102120).elim
            · have hs1102122 : InSquare (73/320) (-21/64) (1/320) tau := by
                convert childUL hs110212 hx110212 hy110212 using 1 <;> norm_num
              exact Batch0218.cell1744.sound htau (by
                simp only [Batch0218.cell1744, Batch0218.tau1744, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1102122 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-53/160 : ℝ) with hy110212 | hy110212
            · have hs1102121 : InSquare (15/64) (-107/320) (1/320) tau := by
                convert childLR hs110212 hx110212 hy110212 using 1 <;> norm_num
              exact (outside_1102121 htau hs1102121).elim
            · have hs1102123 : InSquare (15/64) (-21/64) (1/320) tau := by
                convert childUR hs110212 hx110212 hy110212 using 1 <;> norm_num
              rcases le_total tau.re (15/64 : ℝ) with hx1102123 | hx1102123
              · rcases le_total tau.im (-21/64 : ℝ) with hy1102123 | hy1102123
                · have hs11021230 : InSquare (149/640) (-211/640) (1/640) tau := by
                    convert childLL hs1102123 hx1102123 hy1102123 using 1 <;> norm_num
                  exact (outside_11021230 htau hs11021230).elim
                · have hs11021232 : InSquare (149/640) (-209/640) (1/640) tau := by
                    convert childUL hs1102123 hx1102123 hy1102123 using 1 <;> norm_num
                  exact Batch0400.cell3203.sound htau (by
                    simp only [Batch0400.cell3203, Batch0400.tau3203, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs11021232 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (-21/64 : ℝ) with hy1102123 | hy1102123
                · have hs11021231 : InSquare (151/640) (-211/640) (1/640) tau := by
                    convert childLR hs1102123 hx1102123 hy1102123 using 1 <;> norm_num
                  exact (outside_11021231 htau hs11021231).elim
                · have hs11021233 : InSquare (151/640) (-209/640) (1/640) tau := by
                    convert childUR hs1102123 hx1102123 hy1102123 using 1 <;> norm_num
                  exact (outside_11021233 htau hs11021233).elim
      · rcases le_total tau.im (-27/80 : ℝ) with hy11021 | hy11021
        · have hs110211 : InSquare (39/160) (-11/32) (1/160) tau := by
            convert childLR hs11021 hx11021 hy11021 using 1 <;> norm_num
          exact (outside_110211 htau hs110211).elim
        · have hs110213 : InSquare (39/160) (-53/160) (1/160) tau := by
            convert childUR hs11021 hx11021 hy11021 using 1 <;> norm_num
          exact (outside_110213 htau hs110213).elim
    · have hs11023 : InSquare (19/80) (-5/16) (1/80) tau := by
        convert childUR hs hx1102 hy1102 using 1 <;> norm_num
      rcases le_total tau.re (19/80 : ℝ) with hx11023 | hx11023
      · rcases le_total tau.im (-5/16 : ℝ) with hy11023 | hy11023
        · have hs110230 : InSquare (37/160) (-51/160) (1/160) tau := by
            convert childLL hs11023 hx11023 hy11023 using 1 <;> norm_num
          rcases le_total tau.re (37/160 : ℝ) with hx110230 | hx110230
          · rcases le_total tau.im (-51/160 : ℝ) with hy110230 | hy110230
            · have hs1102300 : InSquare (73/320) (-103/320) (1/320) tau := by
                convert childLL hs110230 hx110230 hy110230 using 1 <;> norm_num
              exact Batch0220.cell1761.sound htau (by
                simp only [Batch0220.cell1761, Batch0220.tau1761, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1102300 (by positivity) using 1 <;> norm_num)
            · have hs1102302 : InSquare (73/320) (-101/320) (1/320) tau := by
                convert childUL hs110230 hx110230 hy110230 using 1 <;> norm_num
              exact Batch0220.cell1763.sound htau (by
                simp only [Batch0220.cell1763, Batch0220.tau1763, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1102302 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-51/160 : ℝ) with hy110230 | hy110230
            · have hs1102301 : InSquare (15/64) (-103/320) (1/320) tau := by
                convert childLR hs110230 hx110230 hy110230 using 1 <;> norm_num
              exact Batch0220.cell1762.sound htau (by
                simp only [Batch0220.cell1762, Batch0220.tau1762, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1102301 (by positivity) using 1 <;> norm_num)
            · have hs1102303 : InSquare (15/64) (-101/320) (1/320) tau := by
                convert childUR hs110230 hx110230 hy110230 using 1 <;> norm_num
              exact Batch0220.cell1764.sound htau (by
                simp only [Batch0220.cell1764, Batch0220.tau1764, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1102303 (by positivity) using 1 <;> norm_num)
        · have hs110232 : InSquare (37/160) (-49/160) (1/160) tau := by
            convert childUL hs11023 hx11023 hy11023 using 1 <;> norm_num
          rcases le_total tau.re (37/160 : ℝ) with hx110232 | hx110232
          · rcases le_total tau.im (-49/160 : ℝ) with hy110232 | hy110232
            · have hs1102320 : InSquare (73/320) (-99/320) (1/320) tau := by
                convert childLL hs110232 hx110232 hy110232 using 1 <;> norm_num
              exact Batch0221.cell1768.sound htau (by
                simp only [Batch0221.cell1768, Batch0221.tau1768, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1102320 (by positivity) using 1 <;> norm_num)
            · have hs1102322 : InSquare (73/320) (-97/320) (1/320) tau := by
                convert childUL hs110232 hx110232 hy110232 using 1 <;> norm_num
              exact Batch0221.cell1770.sound htau (by
                simp only [Batch0221.cell1770, Batch0221.tau1770, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1102322 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-49/160 : ℝ) with hy110232 | hy110232
            · have hs1102321 : InSquare (15/64) (-99/320) (1/320) tau := by
                convert childLR hs110232 hx110232 hy110232 using 1 <;> norm_num
              exact Batch0221.cell1769.sound htau (by
                simp only [Batch0221.cell1769, Batch0221.tau1769, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1102321 (by positivity) using 1 <;> norm_num)
            · have hs1102323 : InSquare (15/64) (-97/320) (1/320) tau := by
                convert childUR hs110232 hx110232 hy110232 using 1 <;> norm_num
              exact Batch0221.cell1771.sound htau (by
                simp only [Batch0221.cell1771, Batch0221.tau1771, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1102323 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-5/16 : ℝ) with hy11023 | hy11023
        · have hs110231 : InSquare (39/160) (-51/160) (1/160) tau := by
            convert childLR hs11023 hx11023 hy11023 using 1 <;> norm_num
          rcases le_total tau.re (39/160 : ℝ) with hx110231 | hx110231
          · rcases le_total tau.im (-51/160 : ℝ) with hy110231 | hy110231
            · have hs1102310 : InSquare (77/320) (-103/320) (1/320) tau := by
                convert childLL hs110231 hx110231 hy110231 using 1 <;> norm_num
              exact Batch0220.cell1765.sound htau (by
                simp only [Batch0220.cell1765, Batch0220.tau1765, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1102310 (by positivity) using 1 <;> norm_num)
            · have hs1102312 : InSquare (77/320) (-101/320) (1/320) tau := by
                convert childUL hs110231 hx110231 hy110231 using 1 <;> norm_num
              exact Batch0220.cell1766.sound htau (by
                simp only [Batch0220.cell1766, Batch0220.tau1766, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1102312 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-51/160 : ℝ) with hy110231 | hy110231
            · have hs1102311 : InSquare (79/320) (-103/320) (1/320) tau := by
                convert childLR hs110231 hx110231 hy110231 using 1 <;> norm_num
              exact (outside_1102311 htau hs1102311).elim
            · have hs1102313 : InSquare (79/320) (-101/320) (1/320) tau := by
                convert childUR hs110231 hx110231 hy110231 using 1 <;> norm_num
              exact Batch0220.cell1767.sound htau (by
                simp only [Batch0220.cell1767, Batch0220.tau1767, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1102313 (by positivity) using 1 <;> norm_num)
        · have hs110233 : InSquare (39/160) (-49/160) (1/160) tau := by
            convert childUR hs11023 hx11023 hy11023 using 1 <;> norm_num
          rcases le_total tau.re (39/160 : ℝ) with hx110233 | hx110233
          · rcases le_total tau.im (-49/160 : ℝ) with hy110233 | hy110233
            · have hs1102330 : InSquare (77/320) (-99/320) (1/320) tau := by
                convert childLL hs110233 hx110233 hy110233 using 1 <;> norm_num
              exact Batch0221.cell1772.sound htau (by
                simp only [Batch0221.cell1772, Batch0221.tau1772, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1102330 (by positivity) using 1 <;> norm_num)
            · have hs1102332 : InSquare (77/320) (-97/320) (1/320) tau := by
                convert childUL hs110233 hx110233 hy110233 using 1 <;> norm_num
              exact Batch0221.cell1774.sound htau (by
                simp only [Batch0221.cell1774, Batch0221.tau1774, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1102332 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-49/160 : ℝ) with hy110233 | hy110233
            · have hs1102331 : InSquare (79/320) (-99/320) (1/320) tau := by
                convert childLR hs110233 hx110233 hy110233 using 1 <;> norm_num
              exact Batch0221.cell1773.sound htau (by
                simp only [Batch0221.cell1773, Batch0221.tau1773, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1102331 (by positivity) using 1 <;> norm_num)
            · have hs1102333 : InSquare (79/320) (-97/320) (1/320) tau := by
                convert childUR hs110233 hx110233 hy110233 using 1 <;> norm_num
              exact Batch0221.cell1775.sound htau (by
                simp only [Batch0221.cell1775, Batch0221.tau1775, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1102333 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1102
