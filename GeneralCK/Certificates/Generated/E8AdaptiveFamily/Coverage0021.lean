import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0155
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0156

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0021

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

private theorem outside_00210 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-27/80) (-23/80) (1/80) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (13/40 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+13/40)]
  have himSq : (11/40 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+11/40)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_00211 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-5/16) (-23/80) (1/80) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (3/10 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+3/10)]
  have himSq : (11/40 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+11/40)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_00212 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-27/80) (-21/80) (1/80) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (13/40 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+13/40)]
  have himSq : (1/4 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+1/4)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_002130 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-51/160) (-43/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (5/16 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+5/16)]
  have himSq : (21/80 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+21/80)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_002132 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-51/160) (-41/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (5/16 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+5/16)]
  have himSq : (1/4 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+1/4)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_0021310 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-99/320) (-87/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (49/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+49/160)]
  have himSq : (43/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+43/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_0021311 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-97/320) (-87/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (3/10 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+3/10)]
  have himSq : (43/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+43/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_0021312 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-99/320) (-17/64) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (49/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+49/160)]
  have himSq : (21/80 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+21/80)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-13/40) (-11/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (-13/40 : ℝ) with hx0021 | hx0021
  · rcases le_total tau.im (-11/40 : ℝ) with hy0021 | hy0021
    · have hs00210 : InSquare (-27/80) (-23/80) (1/80) tau := by
        convert childLL hs hx0021 hy0021 using 1 <;> norm_num
      exact (outside_00210 htau hs00210).elim
    · have hs00212 : InSquare (-27/80) (-21/80) (1/80) tau := by
        convert childUL hs hx0021 hy0021 using 1 <;> norm_num
      exact (outside_00212 htau hs00212).elim
  · rcases le_total tau.im (-11/40 : ℝ) with hy0021 | hy0021
    · have hs00211 : InSquare (-5/16) (-23/80) (1/80) tau := by
        convert childLR hs hx0021 hy0021 using 1 <;> norm_num
      exact (outside_00211 htau hs00211).elim
    · have hs00213 : InSquare (-5/16) (-21/80) (1/80) tau := by
        convert childUR hs hx0021 hy0021 using 1 <;> norm_num
      rcases le_total tau.re (-5/16 : ℝ) with hx00213 | hx00213
      · rcases le_total tau.im (-21/80 : ℝ) with hy00213 | hy00213
        · have hs002130 : InSquare (-51/160) (-43/160) (1/160) tau := by
            convert childLL hs00213 hx00213 hy00213 using 1 <;> norm_num
          exact (outside_002130 htau hs002130).elim
        · have hs002132 : InSquare (-51/160) (-41/160) (1/160) tau := by
            convert childUL hs00213 hx00213 hy00213 using 1 <;> norm_num
          exact (outside_002132 htau hs002132).elim
      · rcases le_total tau.im (-21/80 : ℝ) with hy00213 | hy00213
        · have hs002131 : InSquare (-49/160) (-43/160) (1/160) tau := by
            convert childLR hs00213 hx00213 hy00213 using 1 <;> norm_num
          rcases le_total tau.re (-49/160 : ℝ) with hx002131 | hx002131
          · rcases le_total tau.im (-43/160 : ℝ) with hy002131 | hy002131
            · have hs0021310 : InSquare (-99/320) (-87/320) (1/320) tau := by
                convert childLL hs002131 hx002131 hy002131 using 1 <;> norm_num
              exact (outside_0021310 htau hs0021310).elim
            · have hs0021312 : InSquare (-99/320) (-17/64) (1/320) tau := by
                convert childUL hs002131 hx002131 hy002131 using 1 <;> norm_num
              exact (outside_0021312 htau hs0021312).elim
          · rcases le_total tau.im (-43/160 : ℝ) with hy002131 | hy002131
            · have hs0021311 : InSquare (-97/320) (-87/320) (1/320) tau := by
                convert childLR hs002131 hx002131 hy002131 using 1 <;> norm_num
              exact (outside_0021311 htau hs0021311).elim
            · have hs0021313 : InSquare (-97/320) (-17/64) (1/320) tau := by
                convert childUR hs002131 hx002131 hy002131 using 1 <;> norm_num
              exact Batch0155.cell1244.sound htau (by
                simp only [Batch0155.cell1244, Batch0155.tau1244, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0021313 (by positivity) using 1 <;> norm_num)
        · have hs002133 : InSquare (-49/160) (-41/160) (1/160) tau := by
            convert childUR hs00213 hx00213 hy00213 using 1 <;> norm_num
          rcases le_total tau.re (-49/160 : ℝ) with hx002133 | hx002133
          · rcases le_total tau.im (-41/160 : ℝ) with hy002133 | hy002133
            · have hs0021330 : InSquare (-99/320) (-83/320) (1/320) tau := by
                convert childLL hs002133 hx002133 hy002133 using 1 <;> norm_num
              exact Batch0155.cell1245.sound htau (by
                simp only [Batch0155.cell1245, Batch0155.tau1245, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0021330 (by positivity) using 1 <;> norm_num)
            · have hs0021332 : InSquare (-99/320) (-81/320) (1/320) tau := by
                convert childUL hs002133 hx002133 hy002133 using 1 <;> norm_num
              exact Batch0155.cell1247.sound htau (by
                simp only [Batch0155.cell1247, Batch0155.tau1247, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0021332 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-41/160 : ℝ) with hy002133 | hy002133
            · have hs0021331 : InSquare (-97/320) (-83/320) (1/320) tau := by
                convert childLR hs002133 hx002133 hy002133 using 1 <;> norm_num
              exact Batch0155.cell1246.sound htau (by
                simp only [Batch0155.cell1246, Batch0155.tau1246, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0021331 (by positivity) using 1 <;> norm_num)
            · have hs0021333 : InSquare (-97/320) (-81/320) (1/320) tau := by
                convert childUR hs002133 hx002133 hy002133 using 1 <;> norm_num
              exact Batch0156.cell1248.sound htau (by
                simp only [Batch0156.cell1248, Batch0156.tau1248, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0021333 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0021
