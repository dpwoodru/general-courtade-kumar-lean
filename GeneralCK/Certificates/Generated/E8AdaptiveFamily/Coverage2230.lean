import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0247
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0248

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2230

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

private theorem outside_22300 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-23/80) (5/16) (1/80) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (11/40 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+11/40)]
  have himSq : (3/10 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-3/10)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_22302 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-23/80) (27/80) (1/80) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (11/40 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+11/40)]
  have himSq : (13/40 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-13/40)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_22303 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-21/80) (27/80) (1/80) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (1/4 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+1/4)]
  have himSq : (13/40 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-13/40)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_223012 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-43/160) (51/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (21/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+21/80)]
  have himSq : (5/16 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-5/16)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_223013 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-41/160) (51/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (1/4 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+1/4)]
  have himSq : (5/16 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-5/16)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_2230100 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-87/320) (97/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (43/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+43/160)]
  have himSq : (3/10 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-3/10)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_2230102 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-87/320) (99/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (43/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+43/160)]
  have himSq : (49/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-49/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_2230103 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-17/64) (99/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (21/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+21/80)]
  have himSq : (49/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-49/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-11/40) (13/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (-11/40 : ℝ) with hx2230 | hx2230
  · rcases le_total tau.im (13/40 : ℝ) with hy2230 | hy2230
    · have hs22300 : InSquare (-23/80) (5/16) (1/80) tau := by
        convert childLL hs hx2230 hy2230 using 1 <;> norm_num
      exact (outside_22300 htau hs22300).elim
    · have hs22302 : InSquare (-23/80) (27/80) (1/80) tau := by
        convert childUL hs hx2230 hy2230 using 1 <;> norm_num
      exact (outside_22302 htau hs22302).elim
  · rcases le_total tau.im (13/40 : ℝ) with hy2230 | hy2230
    · have hs22301 : InSquare (-21/80) (5/16) (1/80) tau := by
        convert childLR hs hx2230 hy2230 using 1 <;> norm_num
      rcases le_total tau.re (-21/80 : ℝ) with hx22301 | hx22301
      · rcases le_total tau.im (5/16 : ℝ) with hy22301 | hy22301
        · have hs223010 : InSquare (-43/160) (49/160) (1/160) tau := by
            convert childLL hs22301 hx22301 hy22301 using 1 <;> norm_num
          rcases le_total tau.re (-43/160 : ℝ) with hx223010 | hx223010
          · rcases le_total tau.im (49/160 : ℝ) with hy223010 | hy223010
            · have hs2230100 : InSquare (-87/320) (97/320) (1/320) tau := by
                convert childLL hs223010 hx223010 hy223010 using 1 <;> norm_num
              exact (outside_2230100 htau hs2230100).elim
            · have hs2230102 : InSquare (-87/320) (99/320) (1/320) tau := by
                convert childUL hs223010 hx223010 hy223010 using 1 <;> norm_num
              exact (outside_2230102 htau hs2230102).elim
          · rcases le_total tau.im (49/160 : ℝ) with hy223010 | hy223010
            · have hs2230101 : InSquare (-17/64) (97/320) (1/320) tau := by
                convert childLR hs223010 hx223010 hy223010 using 1 <;> norm_num
              exact Batch0247.cell1983.sound htau (by
                simp only [Batch0247.cell1983, Batch0247.tau1983, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2230101 (by positivity) using 1 <;> norm_num)
            · have hs2230103 : InSquare (-17/64) (99/320) (1/320) tau := by
                convert childUR hs223010 hx223010 hy223010 using 1 <;> norm_num
              exact (outside_2230103 htau hs2230103).elim
        · have hs223012 : InSquare (-43/160) (51/160) (1/160) tau := by
            convert childUL hs22301 hx22301 hy22301 using 1 <;> norm_num
          exact (outside_223012 htau hs223012).elim
      · rcases le_total tau.im (5/16 : ℝ) with hy22301 | hy22301
        · have hs223011 : InSquare (-41/160) (49/160) (1/160) tau := by
            convert childLR hs22301 hx22301 hy22301 using 1 <;> norm_num
          rcases le_total tau.re (-41/160 : ℝ) with hx223011 | hx223011
          · rcases le_total tau.im (49/160 : ℝ) with hy223011 | hy223011
            · have hs2230110 : InSquare (-83/320) (97/320) (1/320) tau := by
                convert childLL hs223011 hx223011 hy223011 using 1 <;> norm_num
              exact Batch0248.cell1984.sound htau (by
                simp only [Batch0248.cell1984, Batch0248.tau1984, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2230110 (by positivity) using 1 <;> norm_num)
            · have hs2230112 : InSquare (-83/320) (99/320) (1/320) tau := by
                convert childUL hs223011 hx223011 hy223011 using 1 <;> norm_num
              exact Batch0248.cell1986.sound htau (by
                simp only [Batch0248.cell1986, Batch0248.tau1986, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2230112 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (49/160 : ℝ) with hy223011 | hy223011
            · have hs2230111 : InSquare (-81/320) (97/320) (1/320) tau := by
                convert childLR hs223011 hx223011 hy223011 using 1 <;> norm_num
              exact Batch0248.cell1985.sound htau (by
                simp only [Batch0248.cell1985, Batch0248.tau1985, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2230111 (by positivity) using 1 <;> norm_num)
            · have hs2230113 : InSquare (-81/320) (99/320) (1/320) tau := by
                convert childUR hs223011 hx223011 hy223011 using 1 <;> norm_num
              exact Batch0248.cell1987.sound htau (by
                simp only [Batch0248.cell1987, Batch0248.tau1987, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2230113 (by positivity) using 1 <;> norm_num)
        · have hs223013 : InSquare (-41/160) (51/160) (1/160) tau := by
            convert childUR hs22301 hx22301 hy22301 using 1 <;> norm_num
          exact (outside_223013 htau hs223013).elim
    · have hs22303 : InSquare (-21/80) (27/80) (1/80) tau := by
        convert childUR hs hx2230 hy2230 using 1 <;> norm_num
      exact (outside_22303 htau hs22303).elim

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2230
