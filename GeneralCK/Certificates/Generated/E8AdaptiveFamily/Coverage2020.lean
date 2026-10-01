import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0098
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0099

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2020

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

private theorem outside_202000 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-63/160) (17/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (31/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+31/80)]
  have himSq : (1/10 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-1/10)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_202002 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-63/160) (19/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (31/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+31/80)]
  have himSq : (9/80 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-9/80)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_202020 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-63/160) (21/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (31/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+31/80)]
  have himSq : (1/8 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-1/8)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_202022 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-63/160) (23/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (31/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+31/80)]
  have himSq : (11/80 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-11/80)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-3/8) (1/8) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (-3/8 : ℝ) with hx2020 | hx2020
  · rcases le_total tau.im (1/8 : ℝ) with hy2020 | hy2020
    · have hs20200 : InSquare (-31/80) (9/80) (1/80) tau := by
        convert childLL hs hx2020 hy2020 using 1 <;> norm_num
      rcases le_total tau.re (-31/80 : ℝ) with hx20200 | hx20200
      · rcases le_total tau.im (9/80 : ℝ) with hy20200 | hy20200
        · have hs202000 : InSquare (-63/160) (17/160) (1/160) tau := by
            convert childLL hs20200 hx20200 hy20200 using 1 <;> norm_num
          exact (outside_202000 htau hs202000).elim
        · have hs202002 : InSquare (-63/160) (19/160) (1/160) tau := by
            convert childUL hs20200 hx20200 hy20200 using 1 <;> norm_num
          exact (outside_202002 htau hs202002).elim
      · rcases le_total tau.im (9/80 : ℝ) with hy20200 | hy20200
        · have hs202001 : InSquare (-61/160) (17/160) (1/160) tau := by
            convert childLR hs20200 hx20200 hy20200 using 1 <;> norm_num
          exact Batch0098.cell0788.sound htau (by
            simp only [Batch0098.cell0788, Batch0098.tau0788, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs202001 (by positivity) using 1 <;> norm_num)
        · have hs202003 : InSquare (-61/160) (19/160) (1/160) tau := by
            convert childUR hs20200 hx20200 hy20200 using 1 <;> norm_num
          exact Batch0098.cell0789.sound htau (by
            simp only [Batch0098.cell0789, Batch0098.tau0789, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs202003 (by positivity) using 1 <;> norm_num)
    · have hs20202 : InSquare (-31/80) (11/80) (1/80) tau := by
        convert childUL hs hx2020 hy2020 using 1 <;> norm_num
      rcases le_total tau.re (-31/80 : ℝ) with hx20202 | hx20202
      · rcases le_total tau.im (11/80 : ℝ) with hy20202 | hy20202
        · have hs202020 : InSquare (-63/160) (21/160) (1/160) tau := by
            convert childLL hs20202 hx20202 hy20202 using 1 <;> norm_num
          exact (outside_202020 htau hs202020).elim
        · have hs202022 : InSquare (-63/160) (23/160) (1/160) tau := by
            convert childUL hs20202 hx20202 hy20202 using 1 <;> norm_num
          exact (outside_202022 htau hs202022).elim
      · rcases le_total tau.im (11/80 : ℝ) with hy20202 | hy20202
        · have hs202021 : InSquare (-61/160) (21/160) (1/160) tau := by
            convert childLR hs20202 hx20202 hy20202 using 1 <;> norm_num
          exact Batch0099.cell0794.sound htau (by
            simp only [Batch0099.cell0794, Batch0099.tau0794, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs202021 (by positivity) using 1 <;> norm_num)
        · have hs202023 : InSquare (-61/160) (23/160) (1/160) tau := by
            convert childUR hs20202 hx20202 hy20202 using 1 <;> norm_num
          exact Batch0099.cell0795.sound htau (by
            simp only [Batch0099.cell0795, Batch0099.tau0795, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs202023 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (1/8 : ℝ) with hy2020 | hy2020
    · have hs20201 : InSquare (-29/80) (9/80) (1/80) tau := by
        convert childLR hs hx2020 hy2020 using 1 <;> norm_num
      rcases le_total tau.re (-29/80 : ℝ) with hx20201 | hx20201
      · rcases le_total tau.im (9/80 : ℝ) with hy20201 | hy20201
        · have hs202010 : InSquare (-59/160) (17/160) (1/160) tau := by
            convert childLL hs20201 hx20201 hy20201 using 1 <;> norm_num
          exact Batch0098.cell0790.sound htau (by
            simp only [Batch0098.cell0790, Batch0098.tau0790, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs202010 (by positivity) using 1 <;> norm_num)
        · have hs202012 : InSquare (-59/160) (19/160) (1/160) tau := by
            convert childUL hs20201 hx20201 hy20201 using 1 <;> norm_num
          exact Batch0099.cell0792.sound htau (by
            simp only [Batch0099.cell0792, Batch0099.tau0792, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs202012 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (9/80 : ℝ) with hy20201 | hy20201
        · have hs202011 : InSquare (-57/160) (17/160) (1/160) tau := by
            convert childLR hs20201 hx20201 hy20201 using 1 <;> norm_num
          exact Batch0098.cell0791.sound htau (by
            simp only [Batch0098.cell0791, Batch0098.tau0791, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs202011 (by positivity) using 1 <;> norm_num)
        · have hs202013 : InSquare (-57/160) (19/160) (1/160) tau := by
            convert childUR hs20201 hx20201 hy20201 using 1 <;> norm_num
          exact Batch0099.cell0793.sound htau (by
            simp only [Batch0099.cell0793, Batch0099.tau0793, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs202013 (by positivity) using 1 <;> norm_num)
    · have hs20203 : InSquare (-29/80) (11/80) (1/80) tau := by
        convert childUR hs hx2020 hy2020 using 1 <;> norm_num
      rcases le_total tau.re (-29/80 : ℝ) with hx20203 | hx20203
      · rcases le_total tau.im (11/80 : ℝ) with hy20203 | hy20203
        · have hs202030 : InSquare (-59/160) (21/160) (1/160) tau := by
            convert childLL hs20203 hx20203 hy20203 using 1 <;> norm_num
          exact Batch0099.cell0796.sound htau (by
            simp only [Batch0099.cell0796, Batch0099.tau0796, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs202030 (by positivity) using 1 <;> norm_num)
        · have hs202032 : InSquare (-59/160) (23/160) (1/160) tau := by
            convert childUL hs20203 hx20203 hy20203 using 1 <;> norm_num
          exact Batch0099.cell0798.sound htau (by
            simp only [Batch0099.cell0798, Batch0099.tau0798, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs202032 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (11/80 : ℝ) with hy20203 | hy20203
        · have hs202031 : InSquare (-57/160) (21/160) (1/160) tau := by
            convert childLR hs20203 hx20203 hy20203 using 1 <;> norm_num
          exact Batch0099.cell0797.sound htau (by
            simp only [Batch0099.cell0797, Batch0099.tau0797, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs202031 (by positivity) using 1 <;> norm_num)
        · have hs202033 : InSquare (-57/160) (23/160) (1/160) tau := by
            convert childUR hs20203 hx20203 hy20203 using 1 <;> norm_num
          exact Batch0099.cell0799.sound htau (by
            simp only [Batch0099.cell0799, Batch0099.tau0799, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs202033 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2020
