import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0060
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0192

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0200

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

private theorem outside_02000 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-31/80) (-3/16) (1/80) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (3/8 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+3/8)]
  have himSq : (7/40 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+7/40)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_02002 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-31/80) (-13/80) (1/80) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (3/8 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+3/8)]
  have himSq : (3/20 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+3/20)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_020010 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-59/160) (-31/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (29/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+29/80)]
  have himSq : (3/16 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+3/16)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_020012 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-59/160) (-29/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (29/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+29/80)]
  have himSq : (7/40 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+7/40)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_0200110 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-23/64) (-63/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (57/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+57/160)]
  have himSq : (31/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+31/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_0200111 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-113/320) (-63/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (7/20 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+7/20)]
  have himSq : (31/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+31/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_0200112 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-23/64) (-61/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (57/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+57/160)]
  have himSq : (3/16 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+3/16)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-3/8) (-7/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (-3/8 : ℝ) with hx0200 | hx0200
  · rcases le_total tau.im (-7/40 : ℝ) with hy0200 | hy0200
    · have hs02000 : InSquare (-31/80) (-3/16) (1/80) tau := by
        convert childLL hs hx0200 hy0200 using 1 <;> norm_num
      exact (outside_02000 htau hs02000).elim
    · have hs02002 : InSquare (-31/80) (-13/80) (1/80) tau := by
        convert childUL hs hx0200 hy0200 using 1 <;> norm_num
      exact (outside_02002 htau hs02002).elim
  · rcases le_total tau.im (-7/40 : ℝ) with hy0200 | hy0200
    · have hs02001 : InSquare (-29/80) (-3/16) (1/80) tau := by
        convert childLR hs hx0200 hy0200 using 1 <;> norm_num
      rcases le_total tau.re (-29/80 : ℝ) with hx02001 | hx02001
      · rcases le_total tau.im (-3/16 : ℝ) with hy02001 | hy02001
        · have hs020010 : InSquare (-59/160) (-31/160) (1/160) tau := by
            convert childLL hs02001 hx02001 hy02001 using 1 <;> norm_num
          exact (outside_020010 htau hs020010).elim
        · have hs020012 : InSquare (-59/160) (-29/160) (1/160) tau := by
            convert childUL hs02001 hx02001 hy02001 using 1 <;> norm_num
          exact (outside_020012 htau hs020012).elim
      · rcases le_total tau.im (-3/16 : ℝ) with hy02001 | hy02001
        · have hs020011 : InSquare (-57/160) (-31/160) (1/160) tau := by
            convert childLR hs02001 hx02001 hy02001 using 1 <;> norm_num
          rcases le_total tau.re (-57/160 : ℝ) with hx020011 | hx020011
          · rcases le_total tau.im (-31/160 : ℝ) with hy020011 | hy020011
            · have hs0200110 : InSquare (-23/64) (-63/320) (1/320) tau := by
                convert childLL hs020011 hx020011 hy020011 using 1 <;> norm_num
              exact (outside_0200110 htau hs0200110).elim
            · have hs0200112 : InSquare (-23/64) (-61/320) (1/320) tau := by
                convert childUL hs020011 hx020011 hy020011 using 1 <;> norm_num
              exact (outside_0200112 htau hs0200112).elim
          · rcases le_total tau.im (-31/160 : ℝ) with hy020011 | hy020011
            · have hs0200111 : InSquare (-113/320) (-63/320) (1/320) tau := by
                convert childLR hs020011 hx020011 hy020011 using 1 <;> norm_num
              exact (outside_0200111 htau hs0200111).elim
            · have hs0200113 : InSquare (-113/320) (-61/320) (1/320) tau := by
                convert childUR hs020011 hx020011 hy020011 using 1 <;> norm_num
              exact Batch0192.cell1540.sound htau (by
                simp only [Batch0192.cell1540, Batch0192.tau1540, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0200113 (by positivity) using 1 <;> norm_num)
        · have hs020013 : InSquare (-57/160) (-29/160) (1/160) tau := by
            convert childUR hs02001 hx02001 hy02001 using 1 <;> norm_num
          exact Batch0060.cell0481.sound htau (by
            simp only [Batch0060.cell0481, Batch0060.tau0481, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs020013 (by positivity) using 1 <;> norm_num)
    · have hs02003 : InSquare (-29/80) (-13/80) (1/80) tau := by
        convert childUR hs hx0200 hy0200 using 1 <;> norm_num
      rcases le_total tau.re (-29/80 : ℝ) with hx02003 | hx02003
      · rcases le_total tau.im (-13/80 : ℝ) with hy02003 | hy02003
        · have hs020030 : InSquare (-59/160) (-27/160) (1/160) tau := by
            convert childLL hs02003 hx02003 hy02003 using 1 <;> norm_num
          exact Batch0060.cell0482.sound htau (by
            simp only [Batch0060.cell0482, Batch0060.tau0482, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs020030 (by positivity) using 1 <;> norm_num)
        · have hs020032 : InSquare (-59/160) (-5/32) (1/160) tau := by
            convert childUL hs02003 hx02003 hy02003 using 1 <;> norm_num
          exact Batch0060.cell0484.sound htau (by
            simp only [Batch0060.cell0484, Batch0060.tau0484, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs020032 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-13/80 : ℝ) with hy02003 | hy02003
        · have hs020031 : InSquare (-57/160) (-27/160) (1/160) tau := by
            convert childLR hs02003 hx02003 hy02003 using 1 <;> norm_num
          exact Batch0060.cell0483.sound htau (by
            simp only [Batch0060.cell0483, Batch0060.tau0483, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs020031 (by positivity) using 1 <;> norm_num)
        · have hs020033 : InSquare (-57/160) (-5/32) (1/160) tau := by
            convert childUR hs02003 hx02003 hy02003 using 1 <;> norm_num
          exact Batch0060.cell0485.sound htau (by
            simp only [Batch0060.cell0485, Batch0060.tau0485, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs020033 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0200
