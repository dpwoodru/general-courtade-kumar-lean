import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0043
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0156
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0157
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0158

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0023

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

private theorem outside_002300 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-11/32) (-39/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (27/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+27/80)]
  have himSq : (19/80 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+19/80)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_002301 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-53/160) (-39/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (13/40 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+13/40)]
  have himSq : (19/80 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+19/80)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_002302 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-11/32) (-37/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (27/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+27/80)]
  have himSq : (9/40 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+9/40)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_0023030 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-107/320) (-15/64) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (53/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+53/160)]
  have himSq : (37/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+37/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_0023032 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-107/320) (-73/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (53/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+53/160)]
  have himSq : (9/40 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+9/40)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_0023100 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-103/320) (-79/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (51/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+51/160)]
  have himSq : (39/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+39/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_0023200 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-111/320) (-71/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (11/32 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+11/32)]
  have himSq : (7/32 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+7/32)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_0023201 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-109/320) (-71/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (27/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+27/80)]
  have himSq : (7/32 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+7/32)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_0023202 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-111/320) (-69/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (11/32 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+11/32)]
  have himSq : (17/80 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+17/80)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_0023220 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-111/320) (-67/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (11/32 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+11/32)]
  have himSq : (33/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+33/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-13/40) (-9/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (-13/40 : ℝ) with hx0023 | hx0023
  · rcases le_total tau.im (-9/40 : ℝ) with hy0023 | hy0023
    · have hs00230 : InSquare (-27/80) (-19/80) (1/80) tau := by
        convert childLL hs hx0023 hy0023 using 1 <;> norm_num
      rcases le_total tau.re (-27/80 : ℝ) with hx00230 | hx00230
      · rcases le_total tau.im (-19/80 : ℝ) with hy00230 | hy00230
        · have hs002300 : InSquare (-11/32) (-39/160) (1/160) tau := by
            convert childLL hs00230 hx00230 hy00230 using 1 <;> norm_num
          exact (outside_002300 htau hs002300).elim
        · have hs002302 : InSquare (-11/32) (-37/160) (1/160) tau := by
            convert childUL hs00230 hx00230 hy00230 using 1 <;> norm_num
          exact (outside_002302 htau hs002302).elim
      · rcases le_total tau.im (-19/80 : ℝ) with hy00230 | hy00230
        · have hs002301 : InSquare (-53/160) (-39/160) (1/160) tau := by
            convert childLR hs00230 hx00230 hy00230 using 1 <;> norm_num
          exact (outside_002301 htau hs002301).elim
        · have hs002303 : InSquare (-53/160) (-37/160) (1/160) tau := by
            convert childUR hs00230 hx00230 hy00230 using 1 <;> norm_num
          rcases le_total tau.re (-53/160 : ℝ) with hx002303 | hx002303
          · rcases le_total tau.im (-37/160 : ℝ) with hy002303 | hy002303
            · have hs0023030 : InSquare (-107/320) (-15/64) (1/320) tau := by
                convert childLL hs002303 hx002303 hy002303 using 1 <;> norm_num
              exact (outside_0023030 htau hs0023030).elim
            · have hs0023032 : InSquare (-107/320) (-73/320) (1/320) tau := by
                convert childUL hs002303 hx002303 hy002303 using 1 <;> norm_num
              exact (outside_0023032 htau hs0023032).elim
          · rcases le_total tau.im (-37/160 : ℝ) with hy002303 | hy002303
            · have hs0023031 : InSquare (-21/64) (-15/64) (1/320) tau := by
                convert childLR hs002303 hx002303 hy002303 using 1 <;> norm_num
              exact Batch0156.cell1249.sound htau (by
                simp only [Batch0156.cell1249, Batch0156.tau1249, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0023031 (by positivity) using 1 <;> norm_num)
            · have hs0023033 : InSquare (-21/64) (-73/320) (1/320) tau := by
                convert childUR hs002303 hx002303 hy002303 using 1 <;> norm_num
              exact Batch0156.cell1250.sound htau (by
                simp only [Batch0156.cell1250, Batch0156.tau1250, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0023033 (by positivity) using 1 <;> norm_num)
    · have hs00232 : InSquare (-27/80) (-17/80) (1/80) tau := by
        convert childUL hs hx0023 hy0023 using 1 <;> norm_num
      rcases le_total tau.re (-27/80 : ℝ) with hx00232 | hx00232
      · rcases le_total tau.im (-17/80 : ℝ) with hy00232 | hy00232
        · have hs002320 : InSquare (-11/32) (-7/32) (1/160) tau := by
            convert childLL hs00232 hx00232 hy00232 using 1 <;> norm_num
          rcases le_total tau.re (-11/32 : ℝ) with hx002320 | hx002320
          · rcases le_total tau.im (-7/32 : ℝ) with hy002320 | hy002320
            · have hs0023200 : InSquare (-111/320) (-71/320) (1/320) tau := by
                convert childLL hs002320 hx002320 hy002320 using 1 <;> norm_num
              exact (outside_0023200 htau hs0023200).elim
            · have hs0023202 : InSquare (-111/320) (-69/320) (1/320) tau := by
                convert childUL hs002320 hx002320 hy002320 using 1 <;> norm_num
              exact (outside_0023202 htau hs0023202).elim
          · rcases le_total tau.im (-7/32 : ℝ) with hy002320 | hy002320
            · have hs0023201 : InSquare (-109/320) (-71/320) (1/320) tau := by
                convert childLR hs002320 hx002320 hy002320 using 1 <;> norm_num
              exact (outside_0023201 htau hs0023201).elim
            · have hs0023203 : InSquare (-109/320) (-69/320) (1/320) tau := by
                convert childUR hs002320 hx002320 hy002320 using 1 <;> norm_num
              exact Batch0157.cell1262.sound htau (by
                simp only [Batch0157.cell1262, Batch0157.tau1262, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0023203 (by positivity) using 1 <;> norm_num)
        · have hs002322 : InSquare (-11/32) (-33/160) (1/160) tau := by
            convert childUL hs00232 hx00232 hy00232 using 1 <;> norm_num
          rcases le_total tau.re (-11/32 : ℝ) with hx002322 | hx002322
          · rcases le_total tau.im (-33/160 : ℝ) with hy002322 | hy002322
            · have hs0023220 : InSquare (-111/320) (-67/320) (1/320) tau := by
                convert childLL hs002322 hx002322 hy002322 using 1 <;> norm_num
              exact (outside_0023220 htau hs0023220).elim
            · have hs0023222 : InSquare (-111/320) (-13/64) (1/320) tau := by
                convert childUL hs002322 hx002322 hy002322 using 1 <;> norm_num
              exact Batch0158.cell1268.sound htau (by
                simp only [Batch0158.cell1268, Batch0158.tau1268, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0023222 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-33/160 : ℝ) with hy002322 | hy002322
            · have hs0023221 : InSquare (-109/320) (-67/320) (1/320) tau := by
                convert childLR hs002322 hx002322 hy002322 using 1 <;> norm_num
              exact Batch0158.cell1267.sound htau (by
                simp only [Batch0158.cell1267, Batch0158.tau1267, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0023221 (by positivity) using 1 <;> norm_num)
            · have hs0023223 : InSquare (-109/320) (-13/64) (1/320) tau := by
                convert childUR hs002322 hx002322 hy002322 using 1 <;> norm_num
              exact Batch0158.cell1269.sound htau (by
                simp only [Batch0158.cell1269, Batch0158.tau1269, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0023223 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-17/80 : ℝ) with hy00232 | hy00232
        · have hs002321 : InSquare (-53/160) (-7/32) (1/160) tau := by
            convert childLR hs00232 hx00232 hy00232 using 1 <;> norm_num
          rcases le_total tau.re (-53/160 : ℝ) with hx002321 | hx002321
          · rcases le_total tau.im (-7/32 : ℝ) with hy002321 | hy002321
            · have hs0023210 : InSquare (-107/320) (-71/320) (1/320) tau := by
                convert childLL hs002321 hx002321 hy002321 using 1 <;> norm_num
              exact Batch0157.cell1263.sound htau (by
                simp only [Batch0157.cell1263, Batch0157.tau1263, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0023210 (by positivity) using 1 <;> norm_num)
            · have hs0023212 : InSquare (-107/320) (-69/320) (1/320) tau := by
                convert childUL hs002321 hx002321 hy002321 using 1 <;> norm_num
              exact Batch0158.cell1265.sound htau (by
                simp only [Batch0158.cell1265, Batch0158.tau1265, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0023212 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-7/32 : ℝ) with hy002321 | hy002321
            · have hs0023211 : InSquare (-21/64) (-71/320) (1/320) tau := by
                convert childLR hs002321 hx002321 hy002321 using 1 <;> norm_num
              exact Batch0158.cell1264.sound htau (by
                simp only [Batch0158.cell1264, Batch0158.tau1264, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0023211 (by positivity) using 1 <;> norm_num)
            · have hs0023213 : InSquare (-21/64) (-69/320) (1/320) tau := by
                convert childUR hs002321 hx002321 hy002321 using 1 <;> norm_num
              exact Batch0158.cell1266.sound htau (by
                simp only [Batch0158.cell1266, Batch0158.tau1266, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0023213 (by positivity) using 1 <;> norm_num)
        · have hs002323 : InSquare (-53/160) (-33/160) (1/160) tau := by
            convert childUR hs00232 hx00232 hy00232 using 1 <;> norm_num
          exact Batch0043.cell0345.sound htau (by
            simp only [Batch0043.cell0345, Batch0043.tau0345, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs002323 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (-9/40 : ℝ) with hy0023 | hy0023
    · have hs00231 : InSquare (-5/16) (-19/80) (1/80) tau := by
        convert childLR hs hx0023 hy0023 using 1 <;> norm_num
      rcases le_total tau.re (-5/16 : ℝ) with hx00231 | hx00231
      · rcases le_total tau.im (-19/80 : ℝ) with hy00231 | hy00231
        · have hs002310 : InSquare (-51/160) (-39/160) (1/160) tau := by
            convert childLL hs00231 hx00231 hy00231 using 1 <;> norm_num
          rcases le_total tau.re (-51/160 : ℝ) with hx002310 | hx002310
          · rcases le_total tau.im (-39/160 : ℝ) with hy002310 | hy002310
            · have hs0023100 : InSquare (-103/320) (-79/320) (1/320) tau := by
                convert childLL hs002310 hx002310 hy002310 using 1 <;> norm_num
              exact (outside_0023100 htau hs0023100).elim
            · have hs0023102 : InSquare (-103/320) (-77/320) (1/320) tau := by
                convert childUL hs002310 hx002310 hy002310 using 1 <;> norm_num
              exact Batch0156.cell1252.sound htau (by
                simp only [Batch0156.cell1252, Batch0156.tau1252, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0023102 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-39/160 : ℝ) with hy002310 | hy002310
            · have hs0023101 : InSquare (-101/320) (-79/320) (1/320) tau := by
                convert childLR hs002310 hx002310 hy002310 using 1 <;> norm_num
              exact Batch0156.cell1251.sound htau (by
                simp only [Batch0156.cell1251, Batch0156.tau1251, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0023101 (by positivity) using 1 <;> norm_num)
            · have hs0023103 : InSquare (-101/320) (-77/320) (1/320) tau := by
                convert childUR hs002310 hx002310 hy002310 using 1 <;> norm_num
              exact Batch0156.cell1253.sound htau (by
                simp only [Batch0156.cell1253, Batch0156.tau1253, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0023103 (by positivity) using 1 <;> norm_num)
        · have hs002312 : InSquare (-51/160) (-37/160) (1/160) tau := by
            convert childUL hs00231 hx00231 hy00231 using 1 <;> norm_num
          rcases le_total tau.re (-51/160 : ℝ) with hx002312 | hx002312
          · rcases le_total tau.im (-37/160 : ℝ) with hy002312 | hy002312
            · have hs0023120 : InSquare (-103/320) (-15/64) (1/320) tau := by
                convert childLL hs002312 hx002312 hy002312 using 1 <;> norm_num
              exact Batch0157.cell1258.sound htau (by
                simp only [Batch0157.cell1258, Batch0157.tau1258, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0023120 (by positivity) using 1 <;> norm_num)
            · have hs0023122 : InSquare (-103/320) (-73/320) (1/320) tau := by
                convert childUL hs002312 hx002312 hy002312 using 1 <;> norm_num
              exact Batch0157.cell1260.sound htau (by
                simp only [Batch0157.cell1260, Batch0157.tau1260, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0023122 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-37/160 : ℝ) with hy002312 | hy002312
            · have hs0023121 : InSquare (-101/320) (-15/64) (1/320) tau := by
                convert childLR hs002312 hx002312 hy002312 using 1 <;> norm_num
              exact Batch0157.cell1259.sound htau (by
                simp only [Batch0157.cell1259, Batch0157.tau1259, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0023121 (by positivity) using 1 <;> norm_num)
            · have hs0023123 : InSquare (-101/320) (-73/320) (1/320) tau := by
                convert childUR hs002312 hx002312 hy002312 using 1 <;> norm_num
              exact Batch0157.cell1261.sound htau (by
                simp only [Batch0157.cell1261, Batch0157.tau1261, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0023123 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-19/80 : ℝ) with hy00231 | hy00231
        · have hs002311 : InSquare (-49/160) (-39/160) (1/160) tau := by
            convert childLR hs00231 hx00231 hy00231 using 1 <;> norm_num
          rcases le_total tau.re (-49/160 : ℝ) with hx002311 | hx002311
          · rcases le_total tau.im (-39/160 : ℝ) with hy002311 | hy002311
            · have hs0023110 : InSquare (-99/320) (-79/320) (1/320) tau := by
                convert childLL hs002311 hx002311 hy002311 using 1 <;> norm_num
              exact Batch0156.cell1254.sound htau (by
                simp only [Batch0156.cell1254, Batch0156.tau1254, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0023110 (by positivity) using 1 <;> norm_num)
            · have hs0023112 : InSquare (-99/320) (-77/320) (1/320) tau := by
                convert childUL hs002311 hx002311 hy002311 using 1 <;> norm_num
              exact Batch0157.cell1256.sound htau (by
                simp only [Batch0157.cell1256, Batch0157.tau1256, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0023112 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-39/160 : ℝ) with hy002311 | hy002311
            · have hs0023111 : InSquare (-97/320) (-79/320) (1/320) tau := by
                convert childLR hs002311 hx002311 hy002311 using 1 <;> norm_num
              exact Batch0156.cell1255.sound htau (by
                simp only [Batch0156.cell1255, Batch0156.tau1255, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0023111 (by positivity) using 1 <;> norm_num)
            · have hs0023113 : InSquare (-97/320) (-77/320) (1/320) tau := by
                convert childUR hs002311 hx002311 hy002311 using 1 <;> norm_num
              exact Batch0157.cell1257.sound htau (by
                simp only [Batch0157.cell1257, Batch0157.tau1257, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0023113 (by positivity) using 1 <;> norm_num)
        · have hs002313 : InSquare (-49/160) (-37/160) (1/160) tau := by
            convert childUR hs00231 hx00231 hy00231 using 1 <;> norm_num
          exact Batch0043.cell0344.sound htau (by
            simp only [Batch0043.cell0344, Batch0043.tau0344, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs002313 (by positivity) using 1 <;> norm_num)
    · have hs00233 : InSquare (-5/16) (-17/80) (1/80) tau := by
        convert childUR hs hx0023 hy0023 using 1 <;> norm_num
      rcases le_total tau.re (-5/16 : ℝ) with hx00233 | hx00233
      · rcases le_total tau.im (-17/80 : ℝ) with hy00233 | hy00233
        · have hs002330 : InSquare (-51/160) (-7/32) (1/160) tau := by
            convert childLL hs00233 hx00233 hy00233 using 1 <;> norm_num
          exact Batch0043.cell0346.sound htau (by
            simp only [Batch0043.cell0346, Batch0043.tau0346, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs002330 (by positivity) using 1 <;> norm_num)
        · have hs002332 : InSquare (-51/160) (-33/160) (1/160) tau := by
            convert childUL hs00233 hx00233 hy00233 using 1 <;> norm_num
          exact Batch0043.cell0348.sound htau (by
            simp only [Batch0043.cell0348, Batch0043.tau0348, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs002332 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-17/80 : ℝ) with hy00233 | hy00233
        · have hs002331 : InSquare (-49/160) (-7/32) (1/160) tau := by
            convert childLR hs00233 hx00233 hy00233 using 1 <;> norm_num
          exact Batch0043.cell0347.sound htau (by
            simp only [Batch0043.cell0347, Batch0043.tau0347, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs002331 (by positivity) using 1 <;> norm_num)
        · have hs002333 : InSquare (-49/160) (-33/160) (1/160) tau := by
            convert childUR hs00233 hx00233 hy00233 using 1 <;> norm_num
          exact Batch0043.cell0349.sound htau (by
            simp only [Batch0043.cell0349, Batch0043.tau0349, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs002333 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0023
