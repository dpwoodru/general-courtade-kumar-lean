import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0149
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0311
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0312
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0313
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0314

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3310

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

private theorem outside_331031 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (11/32) (37/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (27/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-27/80)]
  have himSq : (9/40 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-9/40)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_331032 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (53/160) (39/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (13/40 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-13/40)]
  have himSq : (19/80 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-19/80)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_331033 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (11/32) (39/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (27/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-27/80)]
  have himSq : (19/80 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-19/80)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_3310113 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (111/320) (67/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (11/32 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-11/32)]
  have himSq : (33/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-33/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_3310131 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (111/320) (69/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (11/32 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-11/32)]
  have himSq : (17/80 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-17/80)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_3310132 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (109/320) (71/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (27/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-27/80)]
  have himSq : (7/32 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-7/32)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_3310133 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (111/320) (71/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (11/32 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-11/32)]
  have himSq : (7/32 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-7/32)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_3310233 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (103/320) (79/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (51/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-51/160)]
  have himSq : (39/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-39/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_3310301 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (107/320) (73/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (53/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-53/160)]
  have himSq : (9/40 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-9/40)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_3310303 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (107/320) (15/64) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (53/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-53/160)]
  have himSq : (37/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-37/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (13/40) (9/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (13/40 : ℝ) with hx3310 | hx3310
  · rcases le_total tau.im (9/40 : ℝ) with hy3310 | hy3310
    · have hs33100 : InSquare (5/16) (17/80) (1/80) tau := by
        convert childLL hs hx3310 hy3310 using 1 <;> norm_num
      rcases le_total tau.re (5/16 : ℝ) with hx33100 | hx33100
      · rcases le_total tau.im (17/80 : ℝ) with hy33100 | hy33100
        · have hs331000 : InSquare (49/160) (33/160) (1/160) tau := by
            convert childLL hs33100 hx33100 hy33100 using 1 <;> norm_num
          exact Batch0149.cell1194.sound htau (by
            simp only [Batch0149.cell1194, Batch0149.tau1194, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs331000 (by positivity) using 1 <;> norm_num)
        · have hs331002 : InSquare (49/160) (7/32) (1/160) tau := by
            convert childUL hs33100 hx33100 hy33100 using 1 <;> norm_num
          exact Batch0149.cell1196.sound htau (by
            simp only [Batch0149.cell1196, Batch0149.tau1196, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs331002 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (17/80 : ℝ) with hy33100 | hy33100
        · have hs331001 : InSquare (51/160) (33/160) (1/160) tau := by
            convert childLR hs33100 hx33100 hy33100 using 1 <;> norm_num
          exact Batch0149.cell1195.sound htau (by
            simp only [Batch0149.cell1195, Batch0149.tau1195, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs331001 (by positivity) using 1 <;> norm_num)
        · have hs331003 : InSquare (51/160) (7/32) (1/160) tau := by
            convert childUR hs33100 hx33100 hy33100 using 1 <;> norm_num
          exact Batch0149.cell1197.sound htau (by
            simp only [Batch0149.cell1197, Batch0149.tau1197, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs331003 (by positivity) using 1 <;> norm_num)
    · have hs33102 : InSquare (5/16) (19/80) (1/80) tau := by
        convert childUL hs hx3310 hy3310 using 1 <;> norm_num
      rcases le_total tau.re (5/16 : ℝ) with hx33102 | hx33102
      · rcases le_total tau.im (19/80 : ℝ) with hy33102 | hy33102
        · have hs331020 : InSquare (49/160) (37/160) (1/160) tau := by
            convert childLL hs33102 hx33102 hy33102 using 1 <;> norm_num
          exact Batch0149.cell1199.sound htau (by
            simp only [Batch0149.cell1199, Batch0149.tau1199, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs331020 (by positivity) using 1 <;> norm_num)
        · have hs331022 : InSquare (49/160) (39/160) (1/160) tau := by
            convert childUL hs33102 hx33102 hy33102 using 1 <;> norm_num
          rcases le_total tau.re (49/160 : ℝ) with hx331022 | hx331022
          · rcases le_total tau.im (39/160 : ℝ) with hy331022 | hy331022
            · have hs3310220 : InSquare (97/320) (77/320) (1/320) tau := by
                convert childLL hs331022 hx331022 hy331022 using 1 <;> norm_num
              exact Batch0313.cell2506.sound htau (by
                simp only [Batch0313.cell2506, Batch0313.tau2506, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3310220 (by positivity) using 1 <;> norm_num)
            · have hs3310222 : InSquare (97/320) (79/320) (1/320) tau := by
                convert childUL hs331022 hx331022 hy331022 using 1 <;> norm_num
              exact Batch0313.cell2508.sound htau (by
                simp only [Batch0313.cell2508, Batch0313.tau2508, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3310222 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (39/160 : ℝ) with hy331022 | hy331022
            · have hs3310221 : InSquare (99/320) (77/320) (1/320) tau := by
                convert childLR hs331022 hx331022 hy331022 using 1 <;> norm_num
              exact Batch0313.cell2507.sound htau (by
                simp only [Batch0313.cell2507, Batch0313.tau2507, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3310221 (by positivity) using 1 <;> norm_num)
            · have hs3310223 : InSquare (99/320) (79/320) (1/320) tau := by
                convert childUR hs331022 hx331022 hy331022 using 1 <;> norm_num
              exact Batch0313.cell2509.sound htau (by
                simp only [Batch0313.cell2509, Batch0313.tau2509, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3310223 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (19/80 : ℝ) with hy33102 | hy33102
        · have hs331021 : InSquare (51/160) (37/160) (1/160) tau := by
            convert childLR hs33102 hx33102 hy33102 using 1 <;> norm_num
          rcases le_total tau.re (51/160 : ℝ) with hx331021 | hx331021
          · rcases le_total tau.im (37/160 : ℝ) with hy331021 | hy331021
            · have hs3310210 : InSquare (101/320) (73/320) (1/320) tau := by
                convert childLL hs331021 hx331021 hy331021 using 1 <;> norm_num
              exact Batch0312.cell2502.sound htau (by
                simp only [Batch0312.cell2502, Batch0312.tau2502, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3310210 (by positivity) using 1 <;> norm_num)
            · have hs3310212 : InSquare (101/320) (15/64) (1/320) tau := by
                convert childUL hs331021 hx331021 hy331021 using 1 <;> norm_num
              exact Batch0313.cell2504.sound htau (by
                simp only [Batch0313.cell2504, Batch0313.tau2504, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3310212 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (37/160 : ℝ) with hy331021 | hy331021
            · have hs3310211 : InSquare (103/320) (73/320) (1/320) tau := by
                convert childLR hs331021 hx331021 hy331021 using 1 <;> norm_num
              exact Batch0312.cell2503.sound htau (by
                simp only [Batch0312.cell2503, Batch0312.tau2503, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3310211 (by positivity) using 1 <;> norm_num)
            · have hs3310213 : InSquare (103/320) (15/64) (1/320) tau := by
                convert childUR hs331021 hx331021 hy331021 using 1 <;> norm_num
              exact Batch0313.cell2505.sound htau (by
                simp only [Batch0313.cell2505, Batch0313.tau2505, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3310213 (by positivity) using 1 <;> norm_num)
        · have hs331023 : InSquare (51/160) (39/160) (1/160) tau := by
            convert childUR hs33102 hx33102 hy33102 using 1 <;> norm_num
          rcases le_total tau.re (51/160 : ℝ) with hx331023 | hx331023
          · rcases le_total tau.im (39/160 : ℝ) with hy331023 | hy331023
            · have hs3310230 : InSquare (101/320) (77/320) (1/320) tau := by
                convert childLL hs331023 hx331023 hy331023 using 1 <;> norm_num
              exact Batch0313.cell2510.sound htau (by
                simp only [Batch0313.cell2510, Batch0313.tau2510, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3310230 (by positivity) using 1 <;> norm_num)
            · have hs3310232 : InSquare (101/320) (79/320) (1/320) tau := by
                convert childUL hs331023 hx331023 hy331023 using 1 <;> norm_num
              exact Batch0314.cell2512.sound htau (by
                simp only [Batch0314.cell2512, Batch0314.tau2512, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3310232 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (39/160 : ℝ) with hy331023 | hy331023
            · have hs3310231 : InSquare (103/320) (77/320) (1/320) tau := by
                convert childLR hs331023 hx331023 hy331023 using 1 <;> norm_num
              exact Batch0313.cell2511.sound htau (by
                simp only [Batch0313.cell2511, Batch0313.tau2511, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3310231 (by positivity) using 1 <;> norm_num)
            · have hs3310233 : InSquare (103/320) (79/320) (1/320) tau := by
                convert childUR hs331023 hx331023 hy331023 using 1 <;> norm_num
              exact (outside_3310233 htau hs3310233).elim
  · rcases le_total tau.im (9/40 : ℝ) with hy3310 | hy3310
    · have hs33101 : InSquare (27/80) (17/80) (1/80) tau := by
        convert childLR hs hx3310 hy3310 using 1 <;> norm_num
      rcases le_total tau.re (27/80 : ℝ) with hx33101 | hx33101
      · rcases le_total tau.im (17/80 : ℝ) with hy33101 | hy33101
        · have hs331010 : InSquare (53/160) (33/160) (1/160) tau := by
            convert childLL hs33101 hx33101 hy33101 using 1 <;> norm_num
          exact Batch0149.cell1198.sound htau (by
            simp only [Batch0149.cell1198, Batch0149.tau1198, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs331010 (by positivity) using 1 <;> norm_num)
        · have hs331012 : InSquare (53/160) (7/32) (1/160) tau := by
            convert childUL hs33101 hx33101 hy33101 using 1 <;> norm_num
          rcases le_total tau.re (53/160 : ℝ) with hx331012 | hx331012
          · rcases le_total tau.im (7/32 : ℝ) with hy331012 | hy331012
            · have hs3310120 : InSquare (21/64) (69/320) (1/320) tau := by
                convert childLL hs331012 hx331012 hy331012 using 1 <;> norm_num
              exact Batch0312.cell2497.sound htau (by
                simp only [Batch0312.cell2497, Batch0312.tau2497, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3310120 (by positivity) using 1 <;> norm_num)
            · have hs3310122 : InSquare (21/64) (71/320) (1/320) tau := by
                convert childUL hs331012 hx331012 hy331012 using 1 <;> norm_num
              exact Batch0312.cell2499.sound htau (by
                simp only [Batch0312.cell2499, Batch0312.tau2499, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3310122 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (7/32 : ℝ) with hy331012 | hy331012
            · have hs3310121 : InSquare (107/320) (69/320) (1/320) tau := by
                convert childLR hs331012 hx331012 hy331012 using 1 <;> norm_num
              exact Batch0312.cell2498.sound htau (by
                simp only [Batch0312.cell2498, Batch0312.tau2498, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3310121 (by positivity) using 1 <;> norm_num)
            · have hs3310123 : InSquare (107/320) (71/320) (1/320) tau := by
                convert childUR hs331012 hx331012 hy331012 using 1 <;> norm_num
              exact Batch0312.cell2500.sound htau (by
                simp only [Batch0312.cell2500, Batch0312.tau2500, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3310123 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (17/80 : ℝ) with hy33101 | hy33101
        · have hs331011 : InSquare (11/32) (33/160) (1/160) tau := by
            convert childLR hs33101 hx33101 hy33101 using 1 <;> norm_num
          rcases le_total tau.re (11/32 : ℝ) with hx331011 | hx331011
          · rcases le_total tau.im (33/160 : ℝ) with hy331011 | hy331011
            · have hs3310110 : InSquare (109/320) (13/64) (1/320) tau := by
                convert childLL hs331011 hx331011 hy331011 using 1 <;> norm_num
              exact Batch0311.cell2494.sound htau (by
                simp only [Batch0311.cell2494, Batch0311.tau2494, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3310110 (by positivity) using 1 <;> norm_num)
            · have hs3310112 : InSquare (109/320) (67/320) (1/320) tau := by
                convert childUL hs331011 hx331011 hy331011 using 1 <;> norm_num
              exact Batch0312.cell2496.sound htau (by
                simp only [Batch0312.cell2496, Batch0312.tau2496, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3310112 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (33/160 : ℝ) with hy331011 | hy331011
            · have hs3310111 : InSquare (111/320) (13/64) (1/320) tau := by
                convert childLR hs331011 hx331011 hy331011 using 1 <;> norm_num
              exact Batch0311.cell2495.sound htau (by
                simp only [Batch0311.cell2495, Batch0311.tau2495, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3310111 (by positivity) using 1 <;> norm_num)
            · have hs3310113 : InSquare (111/320) (67/320) (1/320) tau := by
                convert childUR hs331011 hx331011 hy331011 using 1 <;> norm_num
              exact (outside_3310113 htau hs3310113).elim
        · have hs331013 : InSquare (11/32) (7/32) (1/160) tau := by
            convert childUR hs33101 hx33101 hy33101 using 1 <;> norm_num
          rcases le_total tau.re (11/32 : ℝ) with hx331013 | hx331013
          · rcases le_total tau.im (7/32 : ℝ) with hy331013 | hy331013
            · have hs3310130 : InSquare (109/320) (69/320) (1/320) tau := by
                convert childLL hs331013 hx331013 hy331013 using 1 <;> norm_num
              exact Batch0312.cell2501.sound htau (by
                simp only [Batch0312.cell2501, Batch0312.tau2501, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3310130 (by positivity) using 1 <;> norm_num)
            · have hs3310132 : InSquare (109/320) (71/320) (1/320) tau := by
                convert childUL hs331013 hx331013 hy331013 using 1 <;> norm_num
              exact (outside_3310132 htau hs3310132).elim
          · rcases le_total tau.im (7/32 : ℝ) with hy331013 | hy331013
            · have hs3310131 : InSquare (111/320) (69/320) (1/320) tau := by
                convert childLR hs331013 hx331013 hy331013 using 1 <;> norm_num
              exact (outside_3310131 htau hs3310131).elim
            · have hs3310133 : InSquare (111/320) (71/320) (1/320) tau := by
                convert childUR hs331013 hx331013 hy331013 using 1 <;> norm_num
              exact (outside_3310133 htau hs3310133).elim
    · have hs33103 : InSquare (27/80) (19/80) (1/80) tau := by
        convert childUR hs hx3310 hy3310 using 1 <;> norm_num
      rcases le_total tau.re (27/80 : ℝ) with hx33103 | hx33103
      · rcases le_total tau.im (19/80 : ℝ) with hy33103 | hy33103
        · have hs331030 : InSquare (53/160) (37/160) (1/160) tau := by
            convert childLL hs33103 hx33103 hy33103 using 1 <;> norm_num
          rcases le_total tau.re (53/160 : ℝ) with hx331030 | hx331030
          · rcases le_total tau.im (37/160 : ℝ) with hy331030 | hy331030
            · have hs3310300 : InSquare (21/64) (73/320) (1/320) tau := by
                convert childLL hs331030 hx331030 hy331030 using 1 <;> norm_num
              exact Batch0314.cell2513.sound htau (by
                simp only [Batch0314.cell2513, Batch0314.tau2513, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3310300 (by positivity) using 1 <;> norm_num)
            · have hs3310302 : InSquare (21/64) (15/64) (1/320) tau := by
                convert childUL hs331030 hx331030 hy331030 using 1 <;> norm_num
              exact Batch0314.cell2514.sound htau (by
                simp only [Batch0314.cell2514, Batch0314.tau2514, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3310302 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (37/160 : ℝ) with hy331030 | hy331030
            · have hs3310301 : InSquare (107/320) (73/320) (1/320) tau := by
                convert childLR hs331030 hx331030 hy331030 using 1 <;> norm_num
              exact (outside_3310301 htau hs3310301).elim
            · have hs3310303 : InSquare (107/320) (15/64) (1/320) tau := by
                convert childUR hs331030 hx331030 hy331030 using 1 <;> norm_num
              exact (outside_3310303 htau hs3310303).elim
        · have hs331032 : InSquare (53/160) (39/160) (1/160) tau := by
            convert childUL hs33103 hx33103 hy33103 using 1 <;> norm_num
          exact (outside_331032 htau hs331032).elim
      · rcases le_total tau.im (19/80 : ℝ) with hy33103 | hy33103
        · have hs331031 : InSquare (11/32) (37/160) (1/160) tau := by
            convert childLR hs33103 hx33103 hy33103 using 1 <;> norm_num
          exact (outside_331031 htau hs331031).elim
        · have hs331033 : InSquare (11/32) (39/160) (1/160) tau := by
            convert childUR hs33103 hx33103 hy33103 using 1 <;> norm_num
          exact (outside_331033 htau hs331033).elim

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3310
