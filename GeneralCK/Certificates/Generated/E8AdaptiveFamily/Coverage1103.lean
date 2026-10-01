import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0222

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1103

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

private theorem outside_11030 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (21/80) (-27/80) (1/80) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (1/4 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-1/4)]
  have himSq : (13/40 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+13/40)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_11031 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (23/80) (-27/80) (1/80) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (11/40 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-11/40)]
  have himSq : (13/40 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+13/40)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_11033 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (23/80) (-5/16) (1/80) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (11/40 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-11/40)]
  have himSq : (3/10 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+3/10)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_110320 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (41/160) (-51/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (1/4 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-1/4)]
  have himSq : (5/16 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+5/16)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_110321 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (43/160) (-51/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (21/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-21/80)]
  have himSq : (5/16 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+5/16)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_1103230 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (17/64) (-99/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (21/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-21/80)]
  have himSq : (49/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+49/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_1103231 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (87/320) (-99/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (43/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-43/160)]
  have himSq : (49/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+49/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_1103233 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (87/320) (-97/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (43/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-43/160)]
  have himSq : (3/10 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+3/10)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (11/40) (-13/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (11/40 : ℝ) with hx1103 | hx1103
  · rcases le_total tau.im (-13/40 : ℝ) with hy1103 | hy1103
    · have hs11030 : InSquare (21/80) (-27/80) (1/80) tau := by
        convert childLL hs hx1103 hy1103 using 1 <;> norm_num
      exact (outside_11030 htau hs11030).elim
    · have hs11032 : InSquare (21/80) (-5/16) (1/80) tau := by
        convert childUL hs hx1103 hy1103 using 1 <;> norm_num
      rcases le_total tau.re (21/80 : ℝ) with hx11032 | hx11032
      · rcases le_total tau.im (-5/16 : ℝ) with hy11032 | hy11032
        · have hs110320 : InSquare (41/160) (-51/160) (1/160) tau := by
            convert childLL hs11032 hx11032 hy11032 using 1 <;> norm_num
          exact (outside_110320 htau hs110320).elim
        · have hs110322 : InSquare (41/160) (-49/160) (1/160) tau := by
            convert childUL hs11032 hx11032 hy11032 using 1 <;> norm_num
          rcases le_total tau.re (41/160 : ℝ) with hx110322 | hx110322
          · rcases le_total tau.im (-49/160 : ℝ) with hy110322 | hy110322
            · have hs1103220 : InSquare (81/320) (-99/320) (1/320) tau := by
                convert childLL hs110322 hx110322 hy110322 using 1 <;> norm_num
              exact Batch0222.cell1776.sound htau (by
                simp only [Batch0222.cell1776, Batch0222.tau1776, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1103220 (by positivity) using 1 <;> norm_num)
            · have hs1103222 : InSquare (81/320) (-97/320) (1/320) tau := by
                convert childUL hs110322 hx110322 hy110322 using 1 <;> norm_num
              exact Batch0222.cell1778.sound htau (by
                simp only [Batch0222.cell1778, Batch0222.tau1778, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1103222 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-49/160 : ℝ) with hy110322 | hy110322
            · have hs1103221 : InSquare (83/320) (-99/320) (1/320) tau := by
                convert childLR hs110322 hx110322 hy110322 using 1 <;> norm_num
              exact Batch0222.cell1777.sound htau (by
                simp only [Batch0222.cell1777, Batch0222.tau1777, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1103221 (by positivity) using 1 <;> norm_num)
            · have hs1103223 : InSquare (83/320) (-97/320) (1/320) tau := by
                convert childUR hs110322 hx110322 hy110322 using 1 <;> norm_num
              exact Batch0222.cell1779.sound htau (by
                simp only [Batch0222.cell1779, Batch0222.tau1779, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1103223 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-5/16 : ℝ) with hy11032 | hy11032
        · have hs110321 : InSquare (43/160) (-51/160) (1/160) tau := by
            convert childLR hs11032 hx11032 hy11032 using 1 <;> norm_num
          exact (outside_110321 htau hs110321).elim
        · have hs110323 : InSquare (43/160) (-49/160) (1/160) tau := by
            convert childUR hs11032 hx11032 hy11032 using 1 <;> norm_num
          rcases le_total tau.re (43/160 : ℝ) with hx110323 | hx110323
          · rcases le_total tau.im (-49/160 : ℝ) with hy110323 | hy110323
            · have hs1103230 : InSquare (17/64) (-99/320) (1/320) tau := by
                convert childLL hs110323 hx110323 hy110323 using 1 <;> norm_num
              exact (outside_1103230 htau hs1103230).elim
            · have hs1103232 : InSquare (17/64) (-97/320) (1/320) tau := by
                convert childUL hs110323 hx110323 hy110323 using 1 <;> norm_num
              exact Batch0222.cell1780.sound htau (by
                simp only [Batch0222.cell1780, Batch0222.tau1780, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1103232 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-49/160 : ℝ) with hy110323 | hy110323
            · have hs1103231 : InSquare (87/320) (-99/320) (1/320) tau := by
                convert childLR hs110323 hx110323 hy110323 using 1 <;> norm_num
              exact (outside_1103231 htau hs1103231).elim
            · have hs1103233 : InSquare (87/320) (-97/320) (1/320) tau := by
                convert childUR hs110323 hx110323 hy110323 using 1 <;> norm_num
              exact (outside_1103233 htau hs1103233).elim
  · rcases le_total tau.im (-13/40 : ℝ) with hy1103 | hy1103
    · have hs11031 : InSquare (23/80) (-27/80) (1/80) tau := by
        convert childLR hs hx1103 hy1103 using 1 <;> norm_num
      exact (outside_11031 htau hs11031).elim
    · have hs11033 : InSquare (23/80) (-5/16) (1/80) tau := by
        convert childUR hs hx1103 hy1103 using 1 <;> norm_num
      exact (outside_11033 htau hs11033).elim

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1103
