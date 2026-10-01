import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0238

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2203

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

private theorem outside_22030 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-27/80) (21/80) (1/80) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (13/40 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+13/40)]
  have himSq : (1/4 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-1/4)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_22032 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-27/80) (23/80) (1/80) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (13/40 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+13/40)]
  have himSq : (11/40 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-11/40)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_22033 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-5/16) (23/80) (1/80) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (3/10 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+3/10)]
  have himSq : (11/40 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-11/40)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_220310 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-51/160) (41/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (5/16 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+5/16)]
  have himSq : (1/4 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-1/4)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_220312 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-51/160) (43/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (5/16 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+5/16)]
  have himSq : (21/80 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-21/80)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_2203130 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-99/320) (17/64) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (49/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+49/160)]
  have himSq : (21/80 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-21/80)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_2203132 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-99/320) (87/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (49/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+49/160)]
  have himSq : (43/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-43/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_2203133 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-97/320) (87/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (3/10 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+3/10)]
  have himSq : (43/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-43/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-13/40) (11/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (-13/40 : ℝ) with hx2203 | hx2203
  · rcases le_total tau.im (11/40 : ℝ) with hy2203 | hy2203
    · have hs22030 : InSquare (-27/80) (21/80) (1/80) tau := by
        convert childLL hs hx2203 hy2203 using 1 <;> norm_num
      exact (outside_22030 htau hs22030).elim
    · have hs22032 : InSquare (-27/80) (23/80) (1/80) tau := by
        convert childUL hs hx2203 hy2203 using 1 <;> norm_num
      exact (outside_22032 htau hs22032).elim
  · rcases le_total tau.im (11/40 : ℝ) with hy2203 | hy2203
    · have hs22031 : InSquare (-5/16) (21/80) (1/80) tau := by
        convert childLR hs hx2203 hy2203 using 1 <;> norm_num
      rcases le_total tau.re (-5/16 : ℝ) with hx22031 | hx22031
      · rcases le_total tau.im (21/80 : ℝ) with hy22031 | hy22031
        · have hs220310 : InSquare (-51/160) (41/160) (1/160) tau := by
            convert childLL hs22031 hx22031 hy22031 using 1 <;> norm_num
          exact (outside_220310 htau hs220310).elim
        · have hs220312 : InSquare (-51/160) (43/160) (1/160) tau := by
            convert childUL hs22031 hx22031 hy22031 using 1 <;> norm_num
          exact (outside_220312 htau hs220312).elim
      · rcases le_total tau.im (21/80 : ℝ) with hy22031 | hy22031
        · have hs220311 : InSquare (-49/160) (41/160) (1/160) tau := by
            convert childLR hs22031 hx22031 hy22031 using 1 <;> norm_num
          rcases le_total tau.re (-49/160 : ℝ) with hx220311 | hx220311
          · rcases le_total tau.im (41/160 : ℝ) with hy220311 | hy220311
            · have hs2203110 : InSquare (-99/320) (81/320) (1/320) tau := by
                convert childLL hs220311 hx220311 hy220311 using 1 <;> norm_num
              exact Batch0238.cell1904.sound htau (by
                simp only [Batch0238.cell1904, Batch0238.tau1904, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2203110 (by positivity) using 1 <;> norm_num)
            · have hs2203112 : InSquare (-99/320) (83/320) (1/320) tau := by
                convert childUL hs220311 hx220311 hy220311 using 1 <;> norm_num
              exact Batch0238.cell1906.sound htau (by
                simp only [Batch0238.cell1906, Batch0238.tau1906, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2203112 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (41/160 : ℝ) with hy220311 | hy220311
            · have hs2203111 : InSquare (-97/320) (81/320) (1/320) tau := by
                convert childLR hs220311 hx220311 hy220311 using 1 <;> norm_num
              exact Batch0238.cell1905.sound htau (by
                simp only [Batch0238.cell1905, Batch0238.tau1905, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2203111 (by positivity) using 1 <;> norm_num)
            · have hs2203113 : InSquare (-97/320) (83/320) (1/320) tau := by
                convert childUR hs220311 hx220311 hy220311 using 1 <;> norm_num
              exact Batch0238.cell1907.sound htau (by
                simp only [Batch0238.cell1907, Batch0238.tau1907, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2203113 (by positivity) using 1 <;> norm_num)
        · have hs220313 : InSquare (-49/160) (43/160) (1/160) tau := by
            convert childUR hs22031 hx22031 hy22031 using 1 <;> norm_num
          rcases le_total tau.re (-49/160 : ℝ) with hx220313 | hx220313
          · rcases le_total tau.im (43/160 : ℝ) with hy220313 | hy220313
            · have hs2203130 : InSquare (-99/320) (17/64) (1/320) tau := by
                convert childLL hs220313 hx220313 hy220313 using 1 <;> norm_num
              exact (outside_2203130 htau hs2203130).elim
            · have hs2203132 : InSquare (-99/320) (87/320) (1/320) tau := by
                convert childUL hs220313 hx220313 hy220313 using 1 <;> norm_num
              exact (outside_2203132 htau hs2203132).elim
          · rcases le_total tau.im (43/160 : ℝ) with hy220313 | hy220313
            · have hs2203131 : InSquare (-97/320) (17/64) (1/320) tau := by
                convert childLR hs220313 hx220313 hy220313 using 1 <;> norm_num
              exact Batch0238.cell1908.sound htau (by
                simp only [Batch0238.cell1908, Batch0238.tau1908, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2203131 (by positivity) using 1 <;> norm_num)
            · have hs2203133 : InSquare (-97/320) (87/320) (1/320) tau := by
                convert childUR hs220313 hx220313 hy220313 using 1 <;> norm_num
              exact (outside_2203133 htau hs2203133).elim
    · have hs22033 : InSquare (-5/16) (23/80) (1/80) tau := by
        convert childUR hs hx2203 hy2203 using 1 <;> norm_num
      exact (outside_22033 htau hs22033).elim

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2203
