import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0110
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0239
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0240
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0241
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0242
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0243
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0244

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2212

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

private theorem outside_221222 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-47/160) (47/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (23/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+23/80)]
  have himSq : (23/80 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-23/80)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_2212200 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-19/64) (89/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (47/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+47/160)]
  have himSq : (11/40 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-11/40)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_2212202 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-19/64) (91/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (47/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+47/160)]
  have himSq : (9/32 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-9/32)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_2212203 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-93/320) (91/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (23/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+23/80)]
  have himSq : (9/32 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-9/32)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_2212230 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-91/320) (93/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (9/32 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+9/32)]
  have himSq : (23/80 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-23/80)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_2212232 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-91/320) (19/64) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (9/32 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+9/32)]
  have himSq : (47/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-47/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_2212233 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-89/320) (19/64) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (11/40 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+11/40)]
  have himSq : (47/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-47/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-11/40) (11/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (-11/40 : ℝ) with hx2212 | hx2212
  · rcases le_total tau.im (11/40 : ℝ) with hy2212 | hy2212
    · have hs22120 : InSquare (-23/80) (21/80) (1/80) tau := by
        convert childLL hs hx2212 hy2212 using 1 <;> norm_num
      rcases le_total tau.re (-23/80 : ℝ) with hx22120 | hx22120
      · rcases le_total tau.im (21/80 : ℝ) with hy22120 | hy22120
        · have hs221200 : InSquare (-47/160) (41/160) (1/160) tau := by
            convert childLL hs22120 hx22120 hy22120 using 1 <;> norm_num
          rcases le_total tau.re (-47/160 : ℝ) with hx221200 | hx221200
          · rcases le_total tau.im (41/160 : ℝ) with hy221200 | hy221200
            · have hs2212000 : InSquare (-19/64) (81/320) (1/320) tau := by
                convert childLL hs221200 hx221200 hy221200 using 1 <;> norm_num
              exact Batch0239.cell1913.sound htau (by
                simp only [Batch0239.cell1913, Batch0239.tau1913, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2212000 (by positivity) using 1 <;> norm_num)
            · have hs2212002 : InSquare (-19/64) (83/320) (1/320) tau := by
                convert childUL hs221200 hx221200 hy221200 using 1 <;> norm_num
              exact Batch0239.cell1915.sound htau (by
                simp only [Batch0239.cell1915, Batch0239.tau1915, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2212002 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (41/160 : ℝ) with hy221200 | hy221200
            · have hs2212001 : InSquare (-93/320) (81/320) (1/320) tau := by
                convert childLR hs221200 hx221200 hy221200 using 1 <;> norm_num
              exact Batch0239.cell1914.sound htau (by
                simp only [Batch0239.cell1914, Batch0239.tau1914, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2212001 (by positivity) using 1 <;> norm_num)
            · have hs2212003 : InSquare (-93/320) (83/320) (1/320) tau := by
                convert childUR hs221200 hx221200 hy221200 using 1 <;> norm_num
              exact Batch0239.cell1916.sound htau (by
                simp only [Batch0239.cell1916, Batch0239.tau1916, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2212003 (by positivity) using 1 <;> norm_num)
        · have hs221202 : InSquare (-47/160) (43/160) (1/160) tau := by
            convert childUL hs22120 hx22120 hy22120 using 1 <;> norm_num
          rcases le_total tau.re (-47/160 : ℝ) with hx221202 | hx221202
          · rcases le_total tau.im (43/160 : ℝ) with hy221202 | hy221202
            · have hs2212020 : InSquare (-19/64) (17/64) (1/320) tau := by
                convert childLL hs221202 hx221202 hy221202 using 1 <;> norm_num
              exact Batch0240.cell1921.sound htau (by
                simp only [Batch0240.cell1921, Batch0240.tau1921, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2212020 (by positivity) using 1 <;> norm_num)
            · have hs2212022 : InSquare (-19/64) (87/320) (1/320) tau := by
                convert childUL hs221202 hx221202 hy221202 using 1 <;> norm_num
              exact Batch0240.cell1923.sound htau (by
                simp only [Batch0240.cell1923, Batch0240.tau1923, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2212022 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (43/160 : ℝ) with hy221202 | hy221202
            · have hs2212021 : InSquare (-93/320) (17/64) (1/320) tau := by
                convert childLR hs221202 hx221202 hy221202 using 1 <;> norm_num
              exact Batch0240.cell1922.sound htau (by
                simp only [Batch0240.cell1922, Batch0240.tau1922, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2212021 (by positivity) using 1 <;> norm_num)
            · have hs2212023 : InSquare (-93/320) (87/320) (1/320) tau := by
                convert childUR hs221202 hx221202 hy221202 using 1 <;> norm_num
              exact Batch0240.cell1924.sound htau (by
                simp only [Batch0240.cell1924, Batch0240.tau1924, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2212023 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (21/80 : ℝ) with hy22120 | hy22120
        · have hs221201 : InSquare (-9/32) (41/160) (1/160) tau := by
            convert childLR hs22120 hx22120 hy22120 using 1 <;> norm_num
          rcases le_total tau.re (-9/32 : ℝ) with hx221201 | hx221201
          · rcases le_total tau.im (41/160 : ℝ) with hy221201 | hy221201
            · have hs2212010 : InSquare (-91/320) (81/320) (1/320) tau := by
                convert childLL hs221201 hx221201 hy221201 using 1 <;> norm_num
              exact Batch0239.cell1917.sound htau (by
                simp only [Batch0239.cell1917, Batch0239.tau1917, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2212010 (by positivity) using 1 <;> norm_num)
            · have hs2212012 : InSquare (-91/320) (83/320) (1/320) tau := by
                convert childUL hs221201 hx221201 hy221201 using 1 <;> norm_num
              exact Batch0239.cell1919.sound htau (by
                simp only [Batch0239.cell1919, Batch0239.tau1919, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2212012 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (41/160 : ℝ) with hy221201 | hy221201
            · have hs2212011 : InSquare (-89/320) (81/320) (1/320) tau := by
                convert childLR hs221201 hx221201 hy221201 using 1 <;> norm_num
              exact Batch0239.cell1918.sound htau (by
                simp only [Batch0239.cell1918, Batch0239.tau1918, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2212011 (by positivity) using 1 <;> norm_num)
            · have hs2212013 : InSquare (-89/320) (83/320) (1/320) tau := by
                convert childUR hs221201 hx221201 hy221201 using 1 <;> norm_num
              exact Batch0240.cell1920.sound htau (by
                simp only [Batch0240.cell1920, Batch0240.tau1920, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2212013 (by positivity) using 1 <;> norm_num)
        · have hs221203 : InSquare (-9/32) (43/160) (1/160) tau := by
            convert childUR hs22120 hx22120 hy22120 using 1 <;> norm_num
          rcases le_total tau.re (-9/32 : ℝ) with hx221203 | hx221203
          · rcases le_total tau.im (43/160 : ℝ) with hy221203 | hy221203
            · have hs2212030 : InSquare (-91/320) (17/64) (1/320) tau := by
                convert childLL hs221203 hx221203 hy221203 using 1 <;> norm_num
              exact Batch0240.cell1925.sound htau (by
                simp only [Batch0240.cell1925, Batch0240.tau1925, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2212030 (by positivity) using 1 <;> norm_num)
            · have hs2212032 : InSquare (-91/320) (87/320) (1/320) tau := by
                convert childUL hs221203 hx221203 hy221203 using 1 <;> norm_num
              exact Batch0240.cell1927.sound htau (by
                simp only [Batch0240.cell1927, Batch0240.tau1927, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2212032 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (43/160 : ℝ) with hy221203 | hy221203
            · have hs2212031 : InSquare (-89/320) (17/64) (1/320) tau := by
                convert childLR hs221203 hx221203 hy221203 using 1 <;> norm_num
              exact Batch0240.cell1926.sound htau (by
                simp only [Batch0240.cell1926, Batch0240.tau1926, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2212031 (by positivity) using 1 <;> norm_num)
            · have hs2212033 : InSquare (-89/320) (87/320) (1/320) tau := by
                convert childUR hs221203 hx221203 hy221203 using 1 <;> norm_num
              exact Batch0241.cell1928.sound htau (by
                simp only [Batch0241.cell1928, Batch0241.tau1928, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2212033 (by positivity) using 1 <;> norm_num)
    · have hs22122 : InSquare (-23/80) (23/80) (1/80) tau := by
        convert childUL hs hx2212 hy2212 using 1 <;> norm_num
      rcases le_total tau.re (-23/80 : ℝ) with hx22122 | hx22122
      · rcases le_total tau.im (23/80 : ℝ) with hy22122 | hy22122
        · have hs221220 : InSquare (-47/160) (9/32) (1/160) tau := by
            convert childLL hs22122 hx22122 hy22122 using 1 <;> norm_num
          rcases le_total tau.re (-47/160 : ℝ) with hx221220 | hx221220
          · rcases le_total tau.im (9/32 : ℝ) with hy221220 | hy221220
            · have hs2212200 : InSquare (-19/64) (89/320) (1/320) tau := by
                convert childLL hs221220 hx221220 hy221220 using 1 <;> norm_num
              exact (outside_2212200 htau hs2212200).elim
            · have hs2212202 : InSquare (-19/64) (91/320) (1/320) tau := by
                convert childUL hs221220 hx221220 hy221220 using 1 <;> norm_num
              exact (outside_2212202 htau hs2212202).elim
          · rcases le_total tau.im (9/32 : ℝ) with hy221220 | hy221220
            · have hs2212201 : InSquare (-93/320) (89/320) (1/320) tau := by
                convert childLR hs221220 hx221220 hy221220 using 1 <;> norm_num
              exact Batch0242.cell1937.sound htau (by
                simp only [Batch0242.cell1937, Batch0242.tau1937, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2212201 (by positivity) using 1 <;> norm_num)
            · have hs2212203 : InSquare (-93/320) (91/320) (1/320) tau := by
                convert childUR hs221220 hx221220 hy221220 using 1 <;> norm_num
              exact (outside_2212203 htau hs2212203).elim
        · have hs221222 : InSquare (-47/160) (47/160) (1/160) tau := by
            convert childUL hs22122 hx22122 hy22122 using 1 <;> norm_num
          exact (outside_221222 htau hs221222).elim
      · rcases le_total tau.im (23/80 : ℝ) with hy22122 | hy22122
        · have hs221221 : InSquare (-9/32) (9/32) (1/160) tau := by
            convert childLR hs22122 hx22122 hy22122 using 1 <;> norm_num
          rcases le_total tau.re (-9/32 : ℝ) with hx221221 | hx221221
          · rcases le_total tau.im (9/32 : ℝ) with hy221221 | hy221221
            · have hs2212210 : InSquare (-91/320) (89/320) (1/320) tau := by
                convert childLL hs221221 hx221221 hy221221 using 1 <;> norm_num
              exact Batch0242.cell1938.sound htau (by
                simp only [Batch0242.cell1938, Batch0242.tau1938, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2212210 (by positivity) using 1 <;> norm_num)
            · have hs2212212 : InSquare (-91/320) (91/320) (1/320) tau := by
                convert childUL hs221221 hx221221 hy221221 using 1 <;> norm_num
              exact Batch0242.cell1940.sound htau (by
                simp only [Batch0242.cell1940, Batch0242.tau1940, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2212212 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (9/32 : ℝ) with hy221221 | hy221221
            · have hs2212211 : InSquare (-89/320) (89/320) (1/320) tau := by
                convert childLR hs221221 hx221221 hy221221 using 1 <;> norm_num
              exact Batch0242.cell1939.sound htau (by
                simp only [Batch0242.cell1939, Batch0242.tau1939, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2212211 (by positivity) using 1 <;> norm_num)
            · have hs2212213 : InSquare (-89/320) (91/320) (1/320) tau := by
                convert childUR hs221221 hx221221 hy221221 using 1 <;> norm_num
              exact Batch0242.cell1941.sound htau (by
                simp only [Batch0242.cell1941, Batch0242.tau1941, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2212213 (by positivity) using 1 <;> norm_num)
        · have hs221223 : InSquare (-9/32) (47/160) (1/160) tau := by
            convert childUR hs22122 hx22122 hy22122 using 1 <;> norm_num
          rcases le_total tau.re (-9/32 : ℝ) with hx221223 | hx221223
          · rcases le_total tau.im (47/160 : ℝ) with hy221223 | hy221223
            · have hs2212230 : InSquare (-91/320) (93/320) (1/320) tau := by
                convert childLL hs221223 hx221223 hy221223 using 1 <;> norm_num
              exact (outside_2212230 htau hs2212230).elim
            · have hs2212232 : InSquare (-91/320) (19/64) (1/320) tau := by
                convert childUL hs221223 hx221223 hy221223 using 1 <;> norm_num
              exact (outside_2212232 htau hs2212232).elim
          · rcases le_total tau.im (47/160 : ℝ) with hy221223 | hy221223
            · have hs2212231 : InSquare (-89/320) (93/320) (1/320) tau := by
                convert childLR hs221223 hx221223 hy221223 using 1 <;> norm_num
              exact Batch0242.cell1942.sound htau (by
                simp only [Batch0242.cell1942, Batch0242.tau1942, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2212231 (by positivity) using 1 <;> norm_num)
            · have hs2212233 : InSquare (-89/320) (19/64) (1/320) tau := by
                convert childUR hs221223 hx221223 hy221223 using 1 <;> norm_num
              exact (outside_2212233 htau hs2212233).elim
  · rcases le_total tau.im (11/40 : ℝ) with hy2212 | hy2212
    · have hs22121 : InSquare (-21/80) (21/80) (1/80) tau := by
        convert childLR hs hx2212 hy2212 using 1 <;> norm_num
      rcases le_total tau.re (-21/80 : ℝ) with hx22121 | hx22121
      · rcases le_total tau.im (21/80 : ℝ) with hy22121 | hy22121
        · have hs221210 : InSquare (-43/160) (41/160) (1/160) tau := by
            convert childLL hs22121 hx22121 hy22121 using 1 <;> norm_num
          exact Batch0110.cell0886.sound htau (by
            simp only [Batch0110.cell0886, Batch0110.tau0886, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs221210 (by positivity) using 1 <;> norm_num)
        · have hs221212 : InSquare (-43/160) (43/160) (1/160) tau := by
            convert childUL hs22121 hx22121 hy22121 using 1 <;> norm_num
          rcases le_total tau.re (-43/160 : ℝ) with hx221212 | hx221212
          · rcases le_total tau.im (43/160 : ℝ) with hy221212 | hy221212
            · have hs2212120 : InSquare (-87/320) (17/64) (1/320) tau := by
                convert childLL hs221212 hx221212 hy221212 using 1 <;> norm_num
              exact Batch0241.cell1929.sound htau (by
                simp only [Batch0241.cell1929, Batch0241.tau1929, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2212120 (by positivity) using 1 <;> norm_num)
            · have hs2212122 : InSquare (-87/320) (87/320) (1/320) tau := by
                convert childUL hs221212 hx221212 hy221212 using 1 <;> norm_num
              exact Batch0241.cell1931.sound htau (by
                simp only [Batch0241.cell1931, Batch0241.tau1931, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2212122 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (43/160 : ℝ) with hy221212 | hy221212
            · have hs2212121 : InSquare (-17/64) (17/64) (1/320) tau := by
                convert childLR hs221212 hx221212 hy221212 using 1 <;> norm_num
              exact Batch0241.cell1930.sound htau (by
                simp only [Batch0241.cell1930, Batch0241.tau1930, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2212121 (by positivity) using 1 <;> norm_num)
            · have hs2212123 : InSquare (-17/64) (87/320) (1/320) tau := by
                convert childUR hs221212 hx221212 hy221212 using 1 <;> norm_num
              exact Batch0241.cell1932.sound htau (by
                simp only [Batch0241.cell1932, Batch0241.tau1932, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2212123 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (21/80 : ℝ) with hy22121 | hy22121
        · have hs221211 : InSquare (-41/160) (41/160) (1/160) tau := by
            convert childLR hs22121 hx22121 hy22121 using 1 <;> norm_num
          exact Batch0110.cell0887.sound htau (by
            simp only [Batch0110.cell0887, Batch0110.tau0887, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs221211 (by positivity) using 1 <;> norm_num)
        · have hs221213 : InSquare (-41/160) (43/160) (1/160) tau := by
            convert childUR hs22121 hx22121 hy22121 using 1 <;> norm_num
          rcases le_total tau.re (-41/160 : ℝ) with hx221213 | hx221213
          · rcases le_total tau.im (43/160 : ℝ) with hy221213 | hy221213
            · have hs2212130 : InSquare (-83/320) (17/64) (1/320) tau := by
                convert childLL hs221213 hx221213 hy221213 using 1 <;> norm_num
              exact Batch0241.cell1933.sound htau (by
                simp only [Batch0241.cell1933, Batch0241.tau1933, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2212130 (by positivity) using 1 <;> norm_num)
            · have hs2212132 : InSquare (-83/320) (87/320) (1/320) tau := by
                convert childUL hs221213 hx221213 hy221213 using 1 <;> norm_num
              exact Batch0241.cell1935.sound htau (by
                simp only [Batch0241.cell1935, Batch0241.tau1935, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2212132 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (43/160 : ℝ) with hy221213 | hy221213
            · have hs2212131 : InSquare (-81/320) (17/64) (1/320) tau := by
                convert childLR hs221213 hx221213 hy221213 using 1 <;> norm_num
              exact Batch0241.cell1934.sound htau (by
                simp only [Batch0241.cell1934, Batch0241.tau1934, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2212131 (by positivity) using 1 <;> norm_num)
            · have hs2212133 : InSquare (-81/320) (87/320) (1/320) tau := by
                convert childUR hs221213 hx221213 hy221213 using 1 <;> norm_num
              exact Batch0242.cell1936.sound htau (by
                simp only [Batch0242.cell1936, Batch0242.tau1936, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2212133 (by positivity) using 1 <;> norm_num)
    · have hs22123 : InSquare (-21/80) (23/80) (1/80) tau := by
        convert childUR hs hx2212 hy2212 using 1 <;> norm_num
      rcases le_total tau.re (-21/80 : ℝ) with hx22123 | hx22123
      · rcases le_total tau.im (23/80 : ℝ) with hy22123 | hy22123
        · have hs221230 : InSquare (-43/160) (9/32) (1/160) tau := by
            convert childLL hs22123 hx22123 hy22123 using 1 <;> norm_num
          rcases le_total tau.re (-43/160 : ℝ) with hx221230 | hx221230
          · rcases le_total tau.im (9/32 : ℝ) with hy221230 | hy221230
            · have hs2212300 : InSquare (-87/320) (89/320) (1/320) tau := by
                convert childLL hs221230 hx221230 hy221230 using 1 <;> norm_num
              exact Batch0242.cell1943.sound htau (by
                simp only [Batch0242.cell1943, Batch0242.tau1943, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2212300 (by positivity) using 1 <;> norm_num)
            · have hs2212302 : InSquare (-87/320) (91/320) (1/320) tau := by
                convert childUL hs221230 hx221230 hy221230 using 1 <;> norm_num
              exact Batch0243.cell1945.sound htau (by
                simp only [Batch0243.cell1945, Batch0243.tau1945, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2212302 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (9/32 : ℝ) with hy221230 | hy221230
            · have hs2212301 : InSquare (-17/64) (89/320) (1/320) tau := by
                convert childLR hs221230 hx221230 hy221230 using 1 <;> norm_num
              exact Batch0243.cell1944.sound htau (by
                simp only [Batch0243.cell1944, Batch0243.tau1944, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2212301 (by positivity) using 1 <;> norm_num)
            · have hs2212303 : InSquare (-17/64) (91/320) (1/320) tau := by
                convert childUR hs221230 hx221230 hy221230 using 1 <;> norm_num
              exact Batch0243.cell1946.sound htau (by
                simp only [Batch0243.cell1946, Batch0243.tau1946, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2212303 (by positivity) using 1 <;> norm_num)
        · have hs221232 : InSquare (-43/160) (47/160) (1/160) tau := by
            convert childUL hs22123 hx22123 hy22123 using 1 <;> norm_num
          rcases le_total tau.re (-43/160 : ℝ) with hx221232 | hx221232
          · rcases le_total tau.im (47/160 : ℝ) with hy221232 | hy221232
            · have hs2212320 : InSquare (-87/320) (93/320) (1/320) tau := by
                convert childLL hs221232 hx221232 hy221232 using 1 <;> norm_num
              exact Batch0243.cell1951.sound htau (by
                simp only [Batch0243.cell1951, Batch0243.tau1951, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2212320 (by positivity) using 1 <;> norm_num)
            · have hs2212322 : InSquare (-87/320) (19/64) (1/320) tau := by
                convert childUL hs221232 hx221232 hy221232 using 1 <;> norm_num
              exact Batch0244.cell1953.sound htau (by
                simp only [Batch0244.cell1953, Batch0244.tau1953, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2212322 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (47/160 : ℝ) with hy221232 | hy221232
            · have hs2212321 : InSquare (-17/64) (93/320) (1/320) tau := by
                convert childLR hs221232 hx221232 hy221232 using 1 <;> norm_num
              exact Batch0244.cell1952.sound htau (by
                simp only [Batch0244.cell1952, Batch0244.tau1952, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2212321 (by positivity) using 1 <;> norm_num)
            · have hs2212323 : InSquare (-17/64) (19/64) (1/320) tau := by
                convert childUR hs221232 hx221232 hy221232 using 1 <;> norm_num
              exact Batch0244.cell1954.sound htau (by
                simp only [Batch0244.cell1954, Batch0244.tau1954, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2212323 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (23/80 : ℝ) with hy22123 | hy22123
        · have hs221231 : InSquare (-41/160) (9/32) (1/160) tau := by
            convert childLR hs22123 hx22123 hy22123 using 1 <;> norm_num
          rcases le_total tau.re (-41/160 : ℝ) with hx221231 | hx221231
          · rcases le_total tau.im (9/32 : ℝ) with hy221231 | hy221231
            · have hs2212310 : InSquare (-83/320) (89/320) (1/320) tau := by
                convert childLL hs221231 hx221231 hy221231 using 1 <;> norm_num
              exact Batch0243.cell1947.sound htau (by
                simp only [Batch0243.cell1947, Batch0243.tau1947, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2212310 (by positivity) using 1 <;> norm_num)
            · have hs2212312 : InSquare (-83/320) (91/320) (1/320) tau := by
                convert childUL hs221231 hx221231 hy221231 using 1 <;> norm_num
              exact Batch0243.cell1949.sound htau (by
                simp only [Batch0243.cell1949, Batch0243.tau1949, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2212312 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (9/32 : ℝ) with hy221231 | hy221231
            · have hs2212311 : InSquare (-81/320) (89/320) (1/320) tau := by
                convert childLR hs221231 hx221231 hy221231 using 1 <;> norm_num
              exact Batch0243.cell1948.sound htau (by
                simp only [Batch0243.cell1948, Batch0243.tau1948, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2212311 (by positivity) using 1 <;> norm_num)
            · have hs2212313 : InSquare (-81/320) (91/320) (1/320) tau := by
                convert childUR hs221231 hx221231 hy221231 using 1 <;> norm_num
              exact Batch0243.cell1950.sound htau (by
                simp only [Batch0243.cell1950, Batch0243.tau1950, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2212313 (by positivity) using 1 <;> norm_num)
        · have hs221233 : InSquare (-41/160) (47/160) (1/160) tau := by
            convert childUR hs22123 hx22123 hy22123 using 1 <;> norm_num
          rcases le_total tau.re (-41/160 : ℝ) with hx221233 | hx221233
          · rcases le_total tau.im (47/160 : ℝ) with hy221233 | hy221233
            · have hs2212330 : InSquare (-83/320) (93/320) (1/320) tau := by
                convert childLL hs221233 hx221233 hy221233 using 1 <;> norm_num
              exact Batch0244.cell1955.sound htau (by
                simp only [Batch0244.cell1955, Batch0244.tau1955, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2212330 (by positivity) using 1 <;> norm_num)
            · have hs2212332 : InSquare (-83/320) (19/64) (1/320) tau := by
                convert childUL hs221233 hx221233 hy221233 using 1 <;> norm_num
              exact Batch0244.cell1957.sound htau (by
                simp only [Batch0244.cell1957, Batch0244.tau1957, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2212332 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (47/160 : ℝ) with hy221233 | hy221233
            · have hs2212331 : InSquare (-81/320) (93/320) (1/320) tau := by
                convert childLR hs221233 hx221233 hy221233 using 1 <;> norm_num
              exact Batch0244.cell1956.sound htau (by
                simp only [Batch0244.cell1956, Batch0244.tau1956, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2212331 (by positivity) using 1 <;> norm_num)
            · have hs2212333 : InSquare (-81/320) (19/64) (1/320) tau := by
                convert childUR hs221233 hx221233 hy221233 using 1 <;> norm_num
              exact Batch0244.cell1958.sound htau (by
                simp only [Batch0244.cell1958, Batch0244.tau1958, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2212333 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2212
