import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0062
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0063
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0064

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0202

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

private theorem outside_020200 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-63/160) (-23/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (31/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+31/80)]
  have himSq : (11/80 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+11/80)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_020202 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-63/160) (-21/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (31/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+31/80)]
  have himSq : (1/8 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+1/8)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_020220 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-63/160) (-19/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (31/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+31/80)]
  have himSq : (9/80 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+9/80)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_020222 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-63/160) (-17/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (31/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+31/80)]
  have himSq : (1/10 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+1/10)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-3/8) (-1/8) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (-3/8 : ℝ) with hx0202 | hx0202
  · rcases le_total tau.im (-1/8 : ℝ) with hy0202 | hy0202
    · have hs02020 : InSquare (-31/80) (-11/80) (1/80) tau := by
        convert childLL hs hx0202 hy0202 using 1 <;> norm_num
      rcases le_total tau.re (-31/80 : ℝ) with hx02020 | hx02020
      · rcases le_total tau.im (-11/80 : ℝ) with hy02020 | hy02020
        · have hs020200 : InSquare (-63/160) (-23/160) (1/160) tau := by
            convert childLL hs02020 hx02020 hy02020 using 1 <;> norm_num
          exact (outside_020200 htau hs020200).elim
        · have hs020202 : InSquare (-63/160) (-21/160) (1/160) tau := by
            convert childUL hs02020 hx02020 hy02020 using 1 <;> norm_num
          exact (outside_020202 htau hs020202).elim
      · rcases le_total tau.im (-11/80 : ℝ) with hy02020 | hy02020
        · have hs020201 : InSquare (-61/160) (-23/160) (1/160) tau := by
            convert childLR hs02020 hx02020 hy02020 using 1 <;> norm_num
          exact Batch0062.cell0502.sound htau (by
            simp only [Batch0062.cell0502, Batch0062.tau0502, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs020201 (by positivity) using 1 <;> norm_num)
        · have hs020203 : InSquare (-61/160) (-21/160) (1/160) tau := by
            convert childUR hs02020 hx02020 hy02020 using 1 <;> norm_num
          exact Batch0062.cell0503.sound htau (by
            simp only [Batch0062.cell0503, Batch0062.tau0503, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs020203 (by positivity) using 1 <;> norm_num)
    · have hs02022 : InSquare (-31/80) (-9/80) (1/80) tau := by
        convert childUL hs hx0202 hy0202 using 1 <;> norm_num
      rcases le_total tau.re (-31/80 : ℝ) with hx02022 | hx02022
      · rcases le_total tau.im (-9/80 : ℝ) with hy02022 | hy02022
        · have hs020220 : InSquare (-63/160) (-19/160) (1/160) tau := by
            convert childLL hs02022 hx02022 hy02022 using 1 <;> norm_num
          exact (outside_020220 htau hs020220).elim
        · have hs020222 : InSquare (-63/160) (-17/160) (1/160) tau := by
            convert childUL hs02022 hx02022 hy02022 using 1 <;> norm_num
          exact (outside_020222 htau hs020222).elim
      · rcases le_total tau.im (-9/80 : ℝ) with hy02022 | hy02022
        · have hs020221 : InSquare (-61/160) (-19/160) (1/160) tau := by
            convert childLR hs02022 hx02022 hy02022 using 1 <;> norm_num
          exact Batch0063.cell0508.sound htau (by
            simp only [Batch0063.cell0508, Batch0063.tau0508, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs020221 (by positivity) using 1 <;> norm_num)
        · have hs020223 : InSquare (-61/160) (-17/160) (1/160) tau := by
            convert childUR hs02022 hx02022 hy02022 using 1 <;> norm_num
          exact Batch0063.cell0509.sound htau (by
            simp only [Batch0063.cell0509, Batch0063.tau0509, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs020223 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (-1/8 : ℝ) with hy0202 | hy0202
    · have hs02021 : InSquare (-29/80) (-11/80) (1/80) tau := by
        convert childLR hs hx0202 hy0202 using 1 <;> norm_num
      rcases le_total tau.re (-29/80 : ℝ) with hx02021 | hx02021
      · rcases le_total tau.im (-11/80 : ℝ) with hy02021 | hy02021
        · have hs020210 : InSquare (-59/160) (-23/160) (1/160) tau := by
            convert childLL hs02021 hx02021 hy02021 using 1 <;> norm_num
          exact Batch0063.cell0504.sound htau (by
            simp only [Batch0063.cell0504, Batch0063.tau0504, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs020210 (by positivity) using 1 <;> norm_num)
        · have hs020212 : InSquare (-59/160) (-21/160) (1/160) tau := by
            convert childUL hs02021 hx02021 hy02021 using 1 <;> norm_num
          exact Batch0063.cell0506.sound htau (by
            simp only [Batch0063.cell0506, Batch0063.tau0506, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs020212 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-11/80 : ℝ) with hy02021 | hy02021
        · have hs020211 : InSquare (-57/160) (-23/160) (1/160) tau := by
            convert childLR hs02021 hx02021 hy02021 using 1 <;> norm_num
          exact Batch0063.cell0505.sound htau (by
            simp only [Batch0063.cell0505, Batch0063.tau0505, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs020211 (by positivity) using 1 <;> norm_num)
        · have hs020213 : InSquare (-57/160) (-21/160) (1/160) tau := by
            convert childUR hs02021 hx02021 hy02021 using 1 <;> norm_num
          exact Batch0063.cell0507.sound htau (by
            simp only [Batch0063.cell0507, Batch0063.tau0507, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs020213 (by positivity) using 1 <;> norm_num)
    · have hs02023 : InSquare (-29/80) (-9/80) (1/80) tau := by
        convert childUR hs hx0202 hy0202 using 1 <;> norm_num
      rcases le_total tau.re (-29/80 : ℝ) with hx02023 | hx02023
      · rcases le_total tau.im (-9/80 : ℝ) with hy02023 | hy02023
        · have hs020230 : InSquare (-59/160) (-19/160) (1/160) tau := by
            convert childLL hs02023 hx02023 hy02023 using 1 <;> norm_num
          exact Batch0063.cell0510.sound htau (by
            simp only [Batch0063.cell0510, Batch0063.tau0510, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs020230 (by positivity) using 1 <;> norm_num)
        · have hs020232 : InSquare (-59/160) (-17/160) (1/160) tau := by
            convert childUL hs02023 hx02023 hy02023 using 1 <;> norm_num
          exact Batch0064.cell0512.sound htau (by
            simp only [Batch0064.cell0512, Batch0064.tau0512, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs020232 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-9/80 : ℝ) with hy02023 | hy02023
        · have hs020231 : InSquare (-57/160) (-19/160) (1/160) tau := by
            convert childLR hs02023 hx02023 hy02023 using 1 <;> norm_num
          exact Batch0063.cell0511.sound htau (by
            simp only [Batch0063.cell0511, Batch0063.tau0511, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs020231 (by positivity) using 1 <;> norm_num)
        · have hs020233 : InSquare (-57/160) (-17/160) (1/160) tau := by
            convert childUR hs02023 hx02023 hy02023 using 1 <;> norm_num
          exact Batch0064.cell0513.sound htau (by
            simp only [Batch0064.cell0513, Batch0064.tau0513, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs020233 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0202
