import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0043
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0158
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0159
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0160
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0161
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0162
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0163
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0164

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0030

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

private theorem outside_003000 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-47/160) (-47/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (23/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+23/80)]
  have himSq : (23/80 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+23/80)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_0030010 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-91/320) (-19/64) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (9/32 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+9/32)]
  have himSq : (47/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+47/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_0030011 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-89/320) (-19/64) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (11/40 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+11/40)]
  have himSq : (47/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+47/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_0030012 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-91/320) (-93/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (9/32 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+9/32)]
  have himSq : (23/80 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+23/80)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_0030020 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-19/64) (-91/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (47/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+47/160)]
  have himSq : (9/32 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+9/32)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_0030021 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-93/320) (-91/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (23/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+23/80)]
  have himSq : (9/32 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+9/32)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_0030022 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-19/64) (-89/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (47/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+47/160)]
  have himSq : (11/40 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+11/40)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-11/40) (-11/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (-11/40 : ℝ) with hx0030 | hx0030
  · rcases le_total tau.im (-11/40 : ℝ) with hy0030 | hy0030
    · have hs00300 : InSquare (-23/80) (-23/80) (1/80) tau := by
        convert childLL hs hx0030 hy0030 using 1 <;> norm_num
      rcases le_total tau.re (-23/80 : ℝ) with hx00300 | hx00300
      · rcases le_total tau.im (-23/80 : ℝ) with hy00300 | hy00300
        · have hs003000 : InSquare (-47/160) (-47/160) (1/160) tau := by
            convert childLL hs00300 hx00300 hy00300 using 1 <;> norm_num
          exact (outside_003000 htau hs003000).elim
        · have hs003002 : InSquare (-47/160) (-9/32) (1/160) tau := by
            convert childUL hs00300 hx00300 hy00300 using 1 <;> norm_num
          rcases le_total tau.re (-47/160 : ℝ) with hx003002 | hx003002
          · rcases le_total tau.im (-9/32 : ℝ) with hy003002 | hy003002
            · have hs0030020 : InSquare (-19/64) (-91/320) (1/320) tau := by
                convert childLL hs003002 hx003002 hy003002 using 1 <;> norm_num
              exact (outside_0030020 htau hs0030020).elim
            · have hs0030022 : InSquare (-19/64) (-89/320) (1/320) tau := by
                convert childUL hs003002 hx003002 hy003002 using 1 <;> norm_num
              exact (outside_0030022 htau hs0030022).elim
          · rcases le_total tau.im (-9/32 : ℝ) with hy003002 | hy003002
            · have hs0030021 : InSquare (-93/320) (-91/320) (1/320) tau := by
                convert childLR hs003002 hx003002 hy003002 using 1 <;> norm_num
              exact (outside_0030021 htau hs0030021).elim
            · have hs0030023 : InSquare (-93/320) (-89/320) (1/320) tau := by
                convert childUR hs003002 hx003002 hy003002 using 1 <;> norm_num
              exact Batch0158.cell1271.sound htau (by
                simp only [Batch0158.cell1271, Batch0158.tau1271, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0030023 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-23/80 : ℝ) with hy00300 | hy00300
        · have hs003001 : InSquare (-9/32) (-47/160) (1/160) tau := by
            convert childLR hs00300 hx00300 hy00300 using 1 <;> norm_num
          rcases le_total tau.re (-9/32 : ℝ) with hx003001 | hx003001
          · rcases le_total tau.im (-47/160 : ℝ) with hy003001 | hy003001
            · have hs0030010 : InSquare (-91/320) (-19/64) (1/320) tau := by
                convert childLL hs003001 hx003001 hy003001 using 1 <;> norm_num
              exact (outside_0030010 htau hs0030010).elim
            · have hs0030012 : InSquare (-91/320) (-93/320) (1/320) tau := by
                convert childUL hs003001 hx003001 hy003001 using 1 <;> norm_num
              exact (outside_0030012 htau hs0030012).elim
          · rcases le_total tau.im (-47/160 : ℝ) with hy003001 | hy003001
            · have hs0030011 : InSquare (-89/320) (-19/64) (1/320) tau := by
                convert childLR hs003001 hx003001 hy003001 using 1 <;> norm_num
              exact (outside_0030011 htau hs0030011).elim
            · have hs0030013 : InSquare (-89/320) (-93/320) (1/320) tau := by
                convert childUR hs003001 hx003001 hy003001 using 1 <;> norm_num
              exact Batch0158.cell1270.sound htau (by
                simp only [Batch0158.cell1270, Batch0158.tau1270, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0030013 (by positivity) using 1 <;> norm_num)
        · have hs003003 : InSquare (-9/32) (-9/32) (1/160) tau := by
            convert childUR hs00300 hx00300 hy00300 using 1 <;> norm_num
          rcases le_total tau.re (-9/32 : ℝ) with hx003003 | hx003003
          · rcases le_total tau.im (-9/32 : ℝ) with hy003003 | hy003003
            · have hs0030030 : InSquare (-91/320) (-91/320) (1/320) tau := by
                convert childLL hs003003 hx003003 hy003003 using 1 <;> norm_num
              exact Batch0159.cell1272.sound htau (by
                simp only [Batch0159.cell1272, Batch0159.tau1272, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0030030 (by positivity) using 1 <;> norm_num)
            · have hs0030032 : InSquare (-91/320) (-89/320) (1/320) tau := by
                convert childUL hs003003 hx003003 hy003003 using 1 <;> norm_num
              exact Batch0159.cell1274.sound htau (by
                simp only [Batch0159.cell1274, Batch0159.tau1274, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0030032 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-9/32 : ℝ) with hy003003 | hy003003
            · have hs0030031 : InSquare (-89/320) (-91/320) (1/320) tau := by
                convert childLR hs003003 hx003003 hy003003 using 1 <;> norm_num
              exact Batch0159.cell1273.sound htau (by
                simp only [Batch0159.cell1273, Batch0159.tau1273, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0030031 (by positivity) using 1 <;> norm_num)
            · have hs0030033 : InSquare (-89/320) (-89/320) (1/320) tau := by
                convert childUR hs003003 hx003003 hy003003 using 1 <;> norm_num
              exact Batch0159.cell1275.sound htau (by
                simp only [Batch0159.cell1275, Batch0159.tau1275, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0030033 (by positivity) using 1 <;> norm_num)
    · have hs00302 : InSquare (-23/80) (-21/80) (1/80) tau := by
        convert childUL hs hx0030 hy0030 using 1 <;> norm_num
      rcases le_total tau.re (-23/80 : ℝ) with hx00302 | hx00302
      · rcases le_total tau.im (-21/80 : ℝ) with hy00302 | hy00302
        · have hs003020 : InSquare (-47/160) (-43/160) (1/160) tau := by
            convert childLL hs00302 hx00302 hy00302 using 1 <;> norm_num
          rcases le_total tau.re (-47/160 : ℝ) with hx003020 | hx003020
          · rcases le_total tau.im (-43/160 : ℝ) with hy003020 | hy003020
            · have hs0030200 : InSquare (-19/64) (-87/320) (1/320) tau := by
                convert childLL hs003020 hx003020 hy003020 using 1 <;> norm_num
              exact Batch0161.cell1292.sound htau (by
                simp only [Batch0161.cell1292, Batch0161.tau1292, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0030200 (by positivity) using 1 <;> norm_num)
            · have hs0030202 : InSquare (-19/64) (-17/64) (1/320) tau := by
                convert childUL hs003020 hx003020 hy003020 using 1 <;> norm_num
              exact Batch0161.cell1294.sound htau (by
                simp only [Batch0161.cell1294, Batch0161.tau1294, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0030202 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-43/160 : ℝ) with hy003020 | hy003020
            · have hs0030201 : InSquare (-93/320) (-87/320) (1/320) tau := by
                convert childLR hs003020 hx003020 hy003020 using 1 <;> norm_num
              exact Batch0161.cell1293.sound htau (by
                simp only [Batch0161.cell1293, Batch0161.tau1293, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0030201 (by positivity) using 1 <;> norm_num)
            · have hs0030203 : InSquare (-93/320) (-17/64) (1/320) tau := by
                convert childUR hs003020 hx003020 hy003020 using 1 <;> norm_num
              exact Batch0161.cell1295.sound htau (by
                simp only [Batch0161.cell1295, Batch0161.tau1295, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0030203 (by positivity) using 1 <;> norm_num)
        · have hs003022 : InSquare (-47/160) (-41/160) (1/160) tau := by
            convert childUL hs00302 hx00302 hy00302 using 1 <;> norm_num
          rcases le_total tau.re (-47/160 : ℝ) with hx003022 | hx003022
          · rcases le_total tau.im (-41/160 : ℝ) with hy003022 | hy003022
            · have hs0030220 : InSquare (-19/64) (-83/320) (1/320) tau := by
                convert childLL hs003022 hx003022 hy003022 using 1 <;> norm_num
              exact Batch0162.cell1300.sound htau (by
                simp only [Batch0162.cell1300, Batch0162.tau1300, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0030220 (by positivity) using 1 <;> norm_num)
            · have hs0030222 : InSquare (-19/64) (-81/320) (1/320) tau := by
                convert childUL hs003022 hx003022 hy003022 using 1 <;> norm_num
              exact Batch0162.cell1302.sound htau (by
                simp only [Batch0162.cell1302, Batch0162.tau1302, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0030222 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-41/160 : ℝ) with hy003022 | hy003022
            · have hs0030221 : InSquare (-93/320) (-83/320) (1/320) tau := by
                convert childLR hs003022 hx003022 hy003022 using 1 <;> norm_num
              exact Batch0162.cell1301.sound htau (by
                simp only [Batch0162.cell1301, Batch0162.tau1301, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0030221 (by positivity) using 1 <;> norm_num)
            · have hs0030223 : InSquare (-93/320) (-81/320) (1/320) tau := by
                convert childUR hs003022 hx003022 hy003022 using 1 <;> norm_num
              exact Batch0162.cell1303.sound htau (by
                simp only [Batch0162.cell1303, Batch0162.tau1303, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0030223 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-21/80 : ℝ) with hy00302 | hy00302
        · have hs003021 : InSquare (-9/32) (-43/160) (1/160) tau := by
            convert childLR hs00302 hx00302 hy00302 using 1 <;> norm_num
          rcases le_total tau.re (-9/32 : ℝ) with hx003021 | hx003021
          · rcases le_total tau.im (-43/160 : ℝ) with hy003021 | hy003021
            · have hs0030210 : InSquare (-91/320) (-87/320) (1/320) tau := by
                convert childLL hs003021 hx003021 hy003021 using 1 <;> norm_num
              exact Batch0162.cell1296.sound htau (by
                simp only [Batch0162.cell1296, Batch0162.tau1296, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0030210 (by positivity) using 1 <;> norm_num)
            · have hs0030212 : InSquare (-91/320) (-17/64) (1/320) tau := by
                convert childUL hs003021 hx003021 hy003021 using 1 <;> norm_num
              exact Batch0162.cell1298.sound htau (by
                simp only [Batch0162.cell1298, Batch0162.tau1298, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0030212 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-43/160 : ℝ) with hy003021 | hy003021
            · have hs0030211 : InSquare (-89/320) (-87/320) (1/320) tau := by
                convert childLR hs003021 hx003021 hy003021 using 1 <;> norm_num
              exact Batch0162.cell1297.sound htau (by
                simp only [Batch0162.cell1297, Batch0162.tau1297, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0030211 (by positivity) using 1 <;> norm_num)
            · have hs0030213 : InSquare (-89/320) (-17/64) (1/320) tau := by
                convert childUR hs003021 hx003021 hy003021 using 1 <;> norm_num
              exact Batch0162.cell1299.sound htau (by
                simp only [Batch0162.cell1299, Batch0162.tau1299, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0030213 (by positivity) using 1 <;> norm_num)
        · have hs003023 : InSquare (-9/32) (-41/160) (1/160) tau := by
            convert childUR hs00302 hx00302 hy00302 using 1 <;> norm_num
          rcases le_total tau.re (-9/32 : ℝ) with hx003023 | hx003023
          · rcases le_total tau.im (-41/160 : ℝ) with hy003023 | hy003023
            · have hs0030230 : InSquare (-91/320) (-83/320) (1/320) tau := by
                convert childLL hs003023 hx003023 hy003023 using 1 <;> norm_num
              exact Batch0163.cell1304.sound htau (by
                simp only [Batch0163.cell1304, Batch0163.tau1304, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0030230 (by positivity) using 1 <;> norm_num)
            · have hs0030232 : InSquare (-91/320) (-81/320) (1/320) tau := by
                convert childUL hs003023 hx003023 hy003023 using 1 <;> norm_num
              exact Batch0163.cell1306.sound htau (by
                simp only [Batch0163.cell1306, Batch0163.tau1306, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0030232 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-41/160 : ℝ) with hy003023 | hy003023
            · have hs0030231 : InSquare (-89/320) (-83/320) (1/320) tau := by
                convert childLR hs003023 hx003023 hy003023 using 1 <;> norm_num
              exact Batch0163.cell1305.sound htau (by
                simp only [Batch0163.cell1305, Batch0163.tau1305, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0030231 (by positivity) using 1 <;> norm_num)
            · have hs0030233 : InSquare (-89/320) (-81/320) (1/320) tau := by
                convert childUR hs003023 hx003023 hy003023 using 1 <;> norm_num
              exact Batch0163.cell1307.sound htau (by
                simp only [Batch0163.cell1307, Batch0163.tau1307, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0030233 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (-11/40 : ℝ) with hy0030 | hy0030
    · have hs00301 : InSquare (-21/80) (-23/80) (1/80) tau := by
        convert childLR hs hx0030 hy0030 using 1 <;> norm_num
      rcases le_total tau.re (-21/80 : ℝ) with hx00301 | hx00301
      · rcases le_total tau.im (-23/80 : ℝ) with hy00301 | hy00301
        · have hs003010 : InSquare (-43/160) (-47/160) (1/160) tau := by
            convert childLL hs00301 hx00301 hy00301 using 1 <;> norm_num
          rcases le_total tau.re (-43/160 : ℝ) with hx003010 | hx003010
          · rcases le_total tau.im (-47/160 : ℝ) with hy003010 | hy003010
            · have hs0030100 : InSquare (-87/320) (-19/64) (1/320) tau := by
                convert childLL hs003010 hx003010 hy003010 using 1 <;> norm_num
              exact Batch0159.cell1276.sound htau (by
                simp only [Batch0159.cell1276, Batch0159.tau1276, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0030100 (by positivity) using 1 <;> norm_num)
            · have hs0030102 : InSquare (-87/320) (-93/320) (1/320) tau := by
                convert childUL hs003010 hx003010 hy003010 using 1 <;> norm_num
              exact Batch0159.cell1278.sound htau (by
                simp only [Batch0159.cell1278, Batch0159.tau1278, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0030102 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-47/160 : ℝ) with hy003010 | hy003010
            · have hs0030101 : InSquare (-17/64) (-19/64) (1/320) tau := by
                convert childLR hs003010 hx003010 hy003010 using 1 <;> norm_num
              exact Batch0159.cell1277.sound htau (by
                simp only [Batch0159.cell1277, Batch0159.tau1277, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0030101 (by positivity) using 1 <;> norm_num)
            · have hs0030103 : InSquare (-17/64) (-93/320) (1/320) tau := by
                convert childUR hs003010 hx003010 hy003010 using 1 <;> norm_num
              exact Batch0159.cell1279.sound htau (by
                simp only [Batch0159.cell1279, Batch0159.tau1279, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0030103 (by positivity) using 1 <;> norm_num)
        · have hs003012 : InSquare (-43/160) (-9/32) (1/160) tau := by
            convert childUL hs00301 hx00301 hy00301 using 1 <;> norm_num
          rcases le_total tau.re (-43/160 : ℝ) with hx003012 | hx003012
          · rcases le_total tau.im (-9/32 : ℝ) with hy003012 | hy003012
            · have hs0030120 : InSquare (-87/320) (-91/320) (1/320) tau := by
                convert childLL hs003012 hx003012 hy003012 using 1 <;> norm_num
              exact Batch0160.cell1284.sound htau (by
                simp only [Batch0160.cell1284, Batch0160.tau1284, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0030120 (by positivity) using 1 <;> norm_num)
            · have hs0030122 : InSquare (-87/320) (-89/320) (1/320) tau := by
                convert childUL hs003012 hx003012 hy003012 using 1 <;> norm_num
              exact Batch0160.cell1286.sound htau (by
                simp only [Batch0160.cell1286, Batch0160.tau1286, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0030122 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-9/32 : ℝ) with hy003012 | hy003012
            · have hs0030121 : InSquare (-17/64) (-91/320) (1/320) tau := by
                convert childLR hs003012 hx003012 hy003012 using 1 <;> norm_num
              exact Batch0160.cell1285.sound htau (by
                simp only [Batch0160.cell1285, Batch0160.tau1285, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0030121 (by positivity) using 1 <;> norm_num)
            · have hs0030123 : InSquare (-17/64) (-89/320) (1/320) tau := by
                convert childUR hs003012 hx003012 hy003012 using 1 <;> norm_num
              exact Batch0160.cell1287.sound htau (by
                simp only [Batch0160.cell1287, Batch0160.tau1287, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0030123 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-23/80 : ℝ) with hy00301 | hy00301
        · have hs003011 : InSquare (-41/160) (-47/160) (1/160) tau := by
            convert childLR hs00301 hx00301 hy00301 using 1 <;> norm_num
          rcases le_total tau.re (-41/160 : ℝ) with hx003011 | hx003011
          · rcases le_total tau.im (-47/160 : ℝ) with hy003011 | hy003011
            · have hs0030110 : InSquare (-83/320) (-19/64) (1/320) tau := by
                convert childLL hs003011 hx003011 hy003011 using 1 <;> norm_num
              exact Batch0160.cell1280.sound htau (by
                simp only [Batch0160.cell1280, Batch0160.tau1280, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0030110 (by positivity) using 1 <;> norm_num)
            · have hs0030112 : InSquare (-83/320) (-93/320) (1/320) tau := by
                convert childUL hs003011 hx003011 hy003011 using 1 <;> norm_num
              exact Batch0160.cell1282.sound htau (by
                simp only [Batch0160.cell1282, Batch0160.tau1282, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0030112 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-47/160 : ℝ) with hy003011 | hy003011
            · have hs0030111 : InSquare (-81/320) (-19/64) (1/320) tau := by
                convert childLR hs003011 hx003011 hy003011 using 1 <;> norm_num
              exact Batch0160.cell1281.sound htau (by
                simp only [Batch0160.cell1281, Batch0160.tau1281, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0030111 (by positivity) using 1 <;> norm_num)
            · have hs0030113 : InSquare (-81/320) (-93/320) (1/320) tau := by
                convert childUR hs003011 hx003011 hy003011 using 1 <;> norm_num
              exact Batch0160.cell1283.sound htau (by
                simp only [Batch0160.cell1283, Batch0160.tau1283, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0030113 (by positivity) using 1 <;> norm_num)
        · have hs003013 : InSquare (-41/160) (-9/32) (1/160) tau := by
            convert childUR hs00301 hx00301 hy00301 using 1 <;> norm_num
          rcases le_total tau.re (-41/160 : ℝ) with hx003013 | hx003013
          · rcases le_total tau.im (-9/32 : ℝ) with hy003013 | hy003013
            · have hs0030130 : InSquare (-83/320) (-91/320) (1/320) tau := by
                convert childLL hs003013 hx003013 hy003013 using 1 <;> norm_num
              exact Batch0161.cell1288.sound htau (by
                simp only [Batch0161.cell1288, Batch0161.tau1288, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0030130 (by positivity) using 1 <;> norm_num)
            · have hs0030132 : InSquare (-83/320) (-89/320) (1/320) tau := by
                convert childUL hs003013 hx003013 hy003013 using 1 <;> norm_num
              exact Batch0161.cell1290.sound htau (by
                simp only [Batch0161.cell1290, Batch0161.tau1290, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0030132 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-9/32 : ℝ) with hy003013 | hy003013
            · have hs0030131 : InSquare (-81/320) (-91/320) (1/320) tau := by
                convert childLR hs003013 hx003013 hy003013 using 1 <;> norm_num
              exact Batch0161.cell1289.sound htau (by
                simp only [Batch0161.cell1289, Batch0161.tau1289, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0030131 (by positivity) using 1 <;> norm_num)
            · have hs0030133 : InSquare (-81/320) (-89/320) (1/320) tau := by
                convert childUR hs003013 hx003013 hy003013 using 1 <;> norm_num
              exact Batch0161.cell1291.sound htau (by
                simp only [Batch0161.cell1291, Batch0161.tau1291, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0030133 (by positivity) using 1 <;> norm_num)
    · have hs00303 : InSquare (-21/80) (-21/80) (1/80) tau := by
        convert childUR hs hx0030 hy0030 using 1 <;> norm_num
      rcases le_total tau.re (-21/80 : ℝ) with hx00303 | hx00303
      · rcases le_total tau.im (-21/80 : ℝ) with hy00303 | hy00303
        · have hs003030 : InSquare (-43/160) (-43/160) (1/160) tau := by
            convert childLL hs00303 hx00303 hy00303 using 1 <;> norm_num
          rcases le_total tau.re (-43/160 : ℝ) with hx003030 | hx003030
          · rcases le_total tau.im (-43/160 : ℝ) with hy003030 | hy003030
            · have hs0030300 : InSquare (-87/320) (-87/320) (1/320) tau := by
                convert childLL hs003030 hx003030 hy003030 using 1 <;> norm_num
              exact Batch0163.cell1308.sound htau (by
                simp only [Batch0163.cell1308, Batch0163.tau1308, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0030300 (by positivity) using 1 <;> norm_num)
            · have hs0030302 : InSquare (-87/320) (-17/64) (1/320) tau := by
                convert childUL hs003030 hx003030 hy003030 using 1 <;> norm_num
              exact Batch0163.cell1310.sound htau (by
                simp only [Batch0163.cell1310, Batch0163.tau1310, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0030302 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-43/160 : ℝ) with hy003030 | hy003030
            · have hs0030301 : InSquare (-17/64) (-87/320) (1/320) tau := by
                convert childLR hs003030 hx003030 hy003030 using 1 <;> norm_num
              exact Batch0163.cell1309.sound htau (by
                simp only [Batch0163.cell1309, Batch0163.tau1309, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0030301 (by positivity) using 1 <;> norm_num)
            · have hs0030303 : InSquare (-17/64) (-17/64) (1/320) tau := by
                convert childUR hs003030 hx003030 hy003030 using 1 <;> norm_num
              exact Batch0163.cell1311.sound htau (by
                simp only [Batch0163.cell1311, Batch0163.tau1311, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0030303 (by positivity) using 1 <;> norm_num)
        · have hs003032 : InSquare (-43/160) (-41/160) (1/160) tau := by
            convert childUL hs00303 hx00303 hy00303 using 1 <;> norm_num
          exact Batch0043.cell0350.sound htau (by
            simp only [Batch0043.cell0350, Batch0043.tau0350, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs003032 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-21/80 : ℝ) with hy00303 | hy00303
        · have hs003031 : InSquare (-41/160) (-43/160) (1/160) tau := by
            convert childLR hs00303 hx00303 hy00303 using 1 <;> norm_num
          rcases le_total tau.re (-41/160 : ℝ) with hx003031 | hx003031
          · rcases le_total tau.im (-43/160 : ℝ) with hy003031 | hy003031
            · have hs0030310 : InSquare (-83/320) (-87/320) (1/320) tau := by
                convert childLL hs003031 hx003031 hy003031 using 1 <;> norm_num
              exact Batch0164.cell1312.sound htau (by
                simp only [Batch0164.cell1312, Batch0164.tau1312, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0030310 (by positivity) using 1 <;> norm_num)
            · have hs0030312 : InSquare (-83/320) (-17/64) (1/320) tau := by
                convert childUL hs003031 hx003031 hy003031 using 1 <;> norm_num
              exact Batch0164.cell1314.sound htau (by
                simp only [Batch0164.cell1314, Batch0164.tau1314, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0030312 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-43/160 : ℝ) with hy003031 | hy003031
            · have hs0030311 : InSquare (-81/320) (-87/320) (1/320) tau := by
                convert childLR hs003031 hx003031 hy003031 using 1 <;> norm_num
              exact Batch0164.cell1313.sound htau (by
                simp only [Batch0164.cell1313, Batch0164.tau1313, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0030311 (by positivity) using 1 <;> norm_num)
            · have hs0030313 : InSquare (-81/320) (-17/64) (1/320) tau := by
                convert childUR hs003031 hx003031 hy003031 using 1 <;> norm_num
              exact Batch0164.cell1315.sound htau (by
                simp only [Batch0164.cell1315, Batch0164.tau1315, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0030313 (by positivity) using 1 <;> norm_num)
        · have hs003033 : InSquare (-41/160) (-41/160) (1/160) tau := by
            convert childUR hs00303 hx00303 hy00303 using 1 <;> norm_num
          exact Batch0043.cell0351.sound htau (by
            simp only [Batch0043.cell0351, Batch0043.tau0351, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs003033 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0030
