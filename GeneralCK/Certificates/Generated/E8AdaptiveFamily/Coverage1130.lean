import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0231
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0232

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1130

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

private theorem outside_11300 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (5/16) (-23/80) (1/80) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (3/10 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-3/10)]
  have himSq : (11/40 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+11/40)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_11301 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (27/80) (-23/80) (1/80) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (13/40 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-13/40)]
  have himSq : (11/40 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+11/40)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_11303 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (27/80) (-21/80) (1/80) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (13/40 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-13/40)]
  have himSq : (1/4 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+1/4)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_113021 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (51/160) (-43/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (5/16 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-5/16)]
  have himSq : (21/80 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+21/80)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_113023 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (51/160) (-41/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (5/16 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-5/16)]
  have himSq : (1/4 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+1/4)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_1130200 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (97/320) (-87/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (3/10 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-3/10)]
  have himSq : (43/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+43/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_1130201 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (99/320) (-87/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (49/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-49/160)]
  have himSq : (43/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+43/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_1130203 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (99/320) (-17/64) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (49/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-49/160)]
  have himSq : (21/80 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+21/80)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (13/40) (-11/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (13/40 : ℝ) with hx1130 | hx1130
  · rcases le_total tau.im (-11/40 : ℝ) with hy1130 | hy1130
    · have hs11300 : InSquare (5/16) (-23/80) (1/80) tau := by
        convert childLL hs hx1130 hy1130 using 1 <;> norm_num
      exact (outside_11300 htau hs11300).elim
    · have hs11302 : InSquare (5/16) (-21/80) (1/80) tau := by
        convert childUL hs hx1130 hy1130 using 1 <;> norm_num
      rcases le_total tau.re (5/16 : ℝ) with hx11302 | hx11302
      · rcases le_total tau.im (-21/80 : ℝ) with hy11302 | hy11302
        · have hs113020 : InSquare (49/160) (-43/160) (1/160) tau := by
            convert childLL hs11302 hx11302 hy11302 using 1 <;> norm_num
          rcases le_total tau.re (49/160 : ℝ) with hx113020 | hx113020
          · rcases le_total tau.im (-43/160 : ℝ) with hy113020 | hy113020
            · have hs1130200 : InSquare (97/320) (-87/320) (1/320) tau := by
                convert childLL hs113020 hx113020 hy113020 using 1 <;> norm_num
              exact (outside_1130200 htau hs1130200).elim
            · have hs1130202 : InSquare (97/320) (-17/64) (1/320) tau := by
                convert childUL hs113020 hx113020 hy113020 using 1 <;> norm_num
              exact Batch0231.cell1855.sound htau (by
                simp only [Batch0231.cell1855, Batch0231.tau1855, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1130202 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-43/160 : ℝ) with hy113020 | hy113020
            · have hs1130201 : InSquare (99/320) (-87/320) (1/320) tau := by
                convert childLR hs113020 hx113020 hy113020 using 1 <;> norm_num
              exact (outside_1130201 htau hs1130201).elim
            · have hs1130203 : InSquare (99/320) (-17/64) (1/320) tau := by
                convert childUR hs113020 hx113020 hy113020 using 1 <;> norm_num
              exact (outside_1130203 htau hs1130203).elim
        · have hs113022 : InSquare (49/160) (-41/160) (1/160) tau := by
            convert childUL hs11302 hx11302 hy11302 using 1 <;> norm_num
          rcases le_total tau.re (49/160 : ℝ) with hx113022 | hx113022
          · rcases le_total tau.im (-41/160 : ℝ) with hy113022 | hy113022
            · have hs1130220 : InSquare (97/320) (-83/320) (1/320) tau := by
                convert childLL hs113022 hx113022 hy113022 using 1 <;> norm_num
              exact Batch0232.cell1856.sound htau (by
                simp only [Batch0232.cell1856, Batch0232.tau1856, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1130220 (by positivity) using 1 <;> norm_num)
            · have hs1130222 : InSquare (97/320) (-81/320) (1/320) tau := by
                convert childUL hs113022 hx113022 hy113022 using 1 <;> norm_num
              exact Batch0232.cell1858.sound htau (by
                simp only [Batch0232.cell1858, Batch0232.tau1858, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1130222 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-41/160 : ℝ) with hy113022 | hy113022
            · have hs1130221 : InSquare (99/320) (-83/320) (1/320) tau := by
                convert childLR hs113022 hx113022 hy113022 using 1 <;> norm_num
              exact Batch0232.cell1857.sound htau (by
                simp only [Batch0232.cell1857, Batch0232.tau1857, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1130221 (by positivity) using 1 <;> norm_num)
            · have hs1130223 : InSquare (99/320) (-81/320) (1/320) tau := by
                convert childUR hs113022 hx113022 hy113022 using 1 <;> norm_num
              exact Batch0232.cell1859.sound htau (by
                simp only [Batch0232.cell1859, Batch0232.tau1859, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1130223 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-21/80 : ℝ) with hy11302 | hy11302
        · have hs113021 : InSquare (51/160) (-43/160) (1/160) tau := by
            convert childLR hs11302 hx11302 hy11302 using 1 <;> norm_num
          exact (outside_113021 htau hs113021).elim
        · have hs113023 : InSquare (51/160) (-41/160) (1/160) tau := by
            convert childUR hs11302 hx11302 hy11302 using 1 <;> norm_num
          exact (outside_113023 htau hs113023).elim
  · rcases le_total tau.im (-11/40 : ℝ) with hy1130 | hy1130
    · have hs11301 : InSquare (27/80) (-23/80) (1/80) tau := by
        convert childLR hs hx1130 hy1130 using 1 <;> norm_num
      exact (outside_11301 htau hs11301).elim
    · have hs11303 : InSquare (27/80) (-21/80) (1/80) tau := by
        convert childUR hs hx1130 hy1130 using 1 <;> norm_num
      exact (outside_11303 htau hs11303).elim

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1130
