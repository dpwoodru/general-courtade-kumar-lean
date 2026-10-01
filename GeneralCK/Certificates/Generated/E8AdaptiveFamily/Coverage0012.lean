import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0150

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0012

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

private theorem outside_00120 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-23/80) (-27/80) (1/80) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (11/40 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+11/40)]
  have himSq : (13/40 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+13/40)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_00121 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-21/80) (-27/80) (1/80) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (1/4 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+1/4)]
  have himSq : (13/40 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+13/40)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_00122 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-23/80) (-5/16) (1/80) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (11/40 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+11/40)]
  have himSq : (3/10 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+3/10)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_001230 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-43/160) (-51/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (21/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+21/80)]
  have himSq : (5/16 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+5/16)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_001231 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-41/160) (-51/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (1/4 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+1/4)]
  have himSq : (5/16 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+5/16)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_0012320 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-87/320) (-99/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (43/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+43/160)]
  have himSq : (49/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+49/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_0012321 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-17/64) (-99/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (21/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+21/80)]
  have himSq : (49/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+49/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_0012322 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-87/320) (-97/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (43/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+43/160)]
  have himSq : (3/10 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+3/10)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-11/40) (-13/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (-11/40 : ℝ) with hx0012 | hx0012
  · rcases le_total tau.im (-13/40 : ℝ) with hy0012 | hy0012
    · have hs00120 : InSquare (-23/80) (-27/80) (1/80) tau := by
        convert childLL hs hx0012 hy0012 using 1 <;> norm_num
      exact (outside_00120 htau hs00120).elim
    · have hs00122 : InSquare (-23/80) (-5/16) (1/80) tau := by
        convert childUL hs hx0012 hy0012 using 1 <;> norm_num
      exact (outside_00122 htau hs00122).elim
  · rcases le_total tau.im (-13/40 : ℝ) with hy0012 | hy0012
    · have hs00121 : InSquare (-21/80) (-27/80) (1/80) tau := by
        convert childLR hs hx0012 hy0012 using 1 <;> norm_num
      exact (outside_00121 htau hs00121).elim
    · have hs00123 : InSquare (-21/80) (-5/16) (1/80) tau := by
        convert childUR hs hx0012 hy0012 using 1 <;> norm_num
      rcases le_total tau.re (-21/80 : ℝ) with hx00123 | hx00123
      · rcases le_total tau.im (-5/16 : ℝ) with hy00123 | hy00123
        · have hs001230 : InSquare (-43/160) (-51/160) (1/160) tau := by
            convert childLL hs00123 hx00123 hy00123 using 1 <;> norm_num
          exact (outside_001230 htau hs001230).elim
        · have hs001232 : InSquare (-43/160) (-49/160) (1/160) tau := by
            convert childUL hs00123 hx00123 hy00123 using 1 <;> norm_num
          rcases le_total tau.re (-43/160 : ℝ) with hx001232 | hx001232
          · rcases le_total tau.im (-49/160 : ℝ) with hy001232 | hy001232
            · have hs0012320 : InSquare (-87/320) (-99/320) (1/320) tau := by
                convert childLL hs001232 hx001232 hy001232 using 1 <;> norm_num
              exact (outside_0012320 htau hs0012320).elim
            · have hs0012322 : InSquare (-87/320) (-97/320) (1/320) tau := by
                convert childUL hs001232 hx001232 hy001232 using 1 <;> norm_num
              exact (outside_0012322 htau hs0012322).elim
          · rcases le_total tau.im (-49/160 : ℝ) with hy001232 | hy001232
            · have hs0012321 : InSquare (-17/64) (-99/320) (1/320) tau := by
                convert childLR hs001232 hx001232 hy001232 using 1 <;> norm_num
              exact (outside_0012321 htau hs0012321).elim
            · have hs0012323 : InSquare (-17/64) (-97/320) (1/320) tau := by
                convert childUR hs001232 hx001232 hy001232 using 1 <;> norm_num
              exact Batch0150.cell1200.sound htau (by
                simp only [Batch0150.cell1200, Batch0150.tau1200, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0012323 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-5/16 : ℝ) with hy00123 | hy00123
        · have hs001231 : InSquare (-41/160) (-51/160) (1/160) tau := by
            convert childLR hs00123 hx00123 hy00123 using 1 <;> norm_num
          exact (outside_001231 htau hs001231).elim
        · have hs001233 : InSquare (-41/160) (-49/160) (1/160) tau := by
            convert childUR hs00123 hx00123 hy00123 using 1 <;> norm_num
          rcases le_total tau.re (-41/160 : ℝ) with hx001233 | hx001233
          · rcases le_total tau.im (-49/160 : ℝ) with hy001233 | hy001233
            · have hs0012330 : InSquare (-83/320) (-99/320) (1/320) tau := by
                convert childLL hs001233 hx001233 hy001233 using 1 <;> norm_num
              exact Batch0150.cell1201.sound htau (by
                simp only [Batch0150.cell1201, Batch0150.tau1201, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0012330 (by positivity) using 1 <;> norm_num)
            · have hs0012332 : InSquare (-83/320) (-97/320) (1/320) tau := by
                convert childUL hs001233 hx001233 hy001233 using 1 <;> norm_num
              exact Batch0150.cell1203.sound htau (by
                simp only [Batch0150.cell1203, Batch0150.tau1203, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0012332 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-49/160 : ℝ) with hy001233 | hy001233
            · have hs0012331 : InSquare (-81/320) (-99/320) (1/320) tau := by
                convert childLR hs001233 hx001233 hy001233 using 1 <;> norm_num
              exact Batch0150.cell1202.sound htau (by
                simp only [Batch0150.cell1202, Batch0150.tau1202, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0012331 (by positivity) using 1 <;> norm_num)
            · have hs0012333 : InSquare (-81/320) (-97/320) (1/320) tau := by
                convert childUR hs001233 hx001233 hy001233 using 1 <;> norm_num
              exact Batch0150.cell1204.sound htau (by
                simp only [Batch0150.cell1204, Batch0150.tau1204, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0012333 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0012
