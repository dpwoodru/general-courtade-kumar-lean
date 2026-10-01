import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0082
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0225
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0226
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0227
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0228
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0229
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0230
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0231

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1121

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

private theorem outside_112111 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (47/160) (-47/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (23/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-23/80)]
  have himSq : (23/80 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+23/80)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_1121100 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (89/320) (-19/64) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (11/40 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-11/40)]
  have himSq : (47/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+47/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_1121101 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (91/320) (-19/64) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (9/32 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-9/32)]
  have himSq : (47/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+47/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_1121103 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (91/320) (-93/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (9/32 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-9/32)]
  have himSq : (23/80 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+23/80)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_1121130 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (93/320) (-91/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (23/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-23/80)]
  have himSq : (9/32 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+9/32)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_1121131 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (19/64) (-91/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (47/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-47/160)]
  have himSq : (9/32 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+9/32)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_1121133 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (19/64) (-89/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (47/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-47/160)]
  have himSq : (11/40 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+11/40)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (11/40) (-11/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (11/40 : ℝ) with hx1121 | hx1121
  · rcases le_total tau.im (-11/40 : ℝ) with hy1121 | hy1121
    · have hs11210 : InSquare (21/80) (-23/80) (1/80) tau := by
        convert childLL hs hx1121 hy1121 using 1 <;> norm_num
      rcases le_total tau.re (21/80 : ℝ) with hx11210 | hx11210
      · rcases le_total tau.im (-23/80 : ℝ) with hy11210 | hy11210
        · have hs112100 : InSquare (41/160) (-47/160) (1/160) tau := by
            convert childLL hs11210 hx11210 hy11210 using 1 <;> norm_num
          rcases le_total tau.re (41/160 : ℝ) with hx112100 | hx112100
          · rcases le_total tau.im (-47/160 : ℝ) with hy112100 | hy112100
            · have hs1121000 : InSquare (81/320) (-19/64) (1/320) tau := by
                convert childLL hs112100 hx112100 hy112100 using 1 <;> norm_num
              exact Batch0225.cell1805.sound htau (by
                simp only [Batch0225.cell1805, Batch0225.tau1805, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1121000 (by positivity) using 1 <;> norm_num)
            · have hs1121002 : InSquare (81/320) (-93/320) (1/320) tau := by
                convert childUL hs112100 hx112100 hy112100 using 1 <;> norm_num
              exact Batch0225.cell1807.sound htau (by
                simp only [Batch0225.cell1807, Batch0225.tau1807, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1121002 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-47/160 : ℝ) with hy112100 | hy112100
            · have hs1121001 : InSquare (83/320) (-19/64) (1/320) tau := by
                convert childLR hs112100 hx112100 hy112100 using 1 <;> norm_num
              exact Batch0225.cell1806.sound htau (by
                simp only [Batch0225.cell1806, Batch0225.tau1806, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1121001 (by positivity) using 1 <;> norm_num)
            · have hs1121003 : InSquare (83/320) (-93/320) (1/320) tau := by
                convert childUR hs112100 hx112100 hy112100 using 1 <;> norm_num
              exact Batch0226.cell1808.sound htau (by
                simp only [Batch0226.cell1808, Batch0226.tau1808, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1121003 (by positivity) using 1 <;> norm_num)
        · have hs112102 : InSquare (41/160) (-9/32) (1/160) tau := by
            convert childUL hs11210 hx11210 hy11210 using 1 <;> norm_num
          rcases le_total tau.re (41/160 : ℝ) with hx112102 | hx112102
          · rcases le_total tau.im (-9/32 : ℝ) with hy112102 | hy112102
            · have hs1121020 : InSquare (81/320) (-91/320) (1/320) tau := by
                convert childLL hs112102 hx112102 hy112102 using 1 <;> norm_num
              exact Batch0226.cell1813.sound htau (by
                simp only [Batch0226.cell1813, Batch0226.tau1813, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1121020 (by positivity) using 1 <;> norm_num)
            · have hs1121022 : InSquare (81/320) (-89/320) (1/320) tau := by
                convert childUL hs112102 hx112102 hy112102 using 1 <;> norm_num
              exact Batch0226.cell1815.sound htau (by
                simp only [Batch0226.cell1815, Batch0226.tau1815, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1121022 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-9/32 : ℝ) with hy112102 | hy112102
            · have hs1121021 : InSquare (83/320) (-91/320) (1/320) tau := by
                convert childLR hs112102 hx112102 hy112102 using 1 <;> norm_num
              exact Batch0226.cell1814.sound htau (by
                simp only [Batch0226.cell1814, Batch0226.tau1814, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1121021 (by positivity) using 1 <;> norm_num)
            · have hs1121023 : InSquare (83/320) (-89/320) (1/320) tau := by
                convert childUR hs112102 hx112102 hy112102 using 1 <;> norm_num
              exact Batch0227.cell1816.sound htau (by
                simp only [Batch0227.cell1816, Batch0227.tau1816, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1121023 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-23/80 : ℝ) with hy11210 | hy11210
        · have hs112101 : InSquare (43/160) (-47/160) (1/160) tau := by
            convert childLR hs11210 hx11210 hy11210 using 1 <;> norm_num
          rcases le_total tau.re (43/160 : ℝ) with hx112101 | hx112101
          · rcases le_total tau.im (-47/160 : ℝ) with hy112101 | hy112101
            · have hs1121010 : InSquare (17/64) (-19/64) (1/320) tau := by
                convert childLL hs112101 hx112101 hy112101 using 1 <;> norm_num
              exact Batch0226.cell1809.sound htau (by
                simp only [Batch0226.cell1809, Batch0226.tau1809, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1121010 (by positivity) using 1 <;> norm_num)
            · have hs1121012 : InSquare (17/64) (-93/320) (1/320) tau := by
                convert childUL hs112101 hx112101 hy112101 using 1 <;> norm_num
              exact Batch0226.cell1811.sound htau (by
                simp only [Batch0226.cell1811, Batch0226.tau1811, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1121012 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-47/160 : ℝ) with hy112101 | hy112101
            · have hs1121011 : InSquare (87/320) (-19/64) (1/320) tau := by
                convert childLR hs112101 hx112101 hy112101 using 1 <;> norm_num
              exact Batch0226.cell1810.sound htau (by
                simp only [Batch0226.cell1810, Batch0226.tau1810, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1121011 (by positivity) using 1 <;> norm_num)
            · have hs1121013 : InSquare (87/320) (-93/320) (1/320) tau := by
                convert childUR hs112101 hx112101 hy112101 using 1 <;> norm_num
              exact Batch0226.cell1812.sound htau (by
                simp only [Batch0226.cell1812, Batch0226.tau1812, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1121013 (by positivity) using 1 <;> norm_num)
        · have hs112103 : InSquare (43/160) (-9/32) (1/160) tau := by
            convert childUR hs11210 hx11210 hy11210 using 1 <;> norm_num
          rcases le_total tau.re (43/160 : ℝ) with hx112103 | hx112103
          · rcases le_total tau.im (-9/32 : ℝ) with hy112103 | hy112103
            · have hs1121030 : InSquare (17/64) (-91/320) (1/320) tau := by
                convert childLL hs112103 hx112103 hy112103 using 1 <;> norm_num
              exact Batch0227.cell1817.sound htau (by
                simp only [Batch0227.cell1817, Batch0227.tau1817, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1121030 (by positivity) using 1 <;> norm_num)
            · have hs1121032 : InSquare (17/64) (-89/320) (1/320) tau := by
                convert childUL hs112103 hx112103 hy112103 using 1 <;> norm_num
              exact Batch0227.cell1819.sound htau (by
                simp only [Batch0227.cell1819, Batch0227.tau1819, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1121032 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-9/32 : ℝ) with hy112103 | hy112103
            · have hs1121031 : InSquare (87/320) (-91/320) (1/320) tau := by
                convert childLR hs112103 hx112103 hy112103 using 1 <;> norm_num
              exact Batch0227.cell1818.sound htau (by
                simp only [Batch0227.cell1818, Batch0227.tau1818, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1121031 (by positivity) using 1 <;> norm_num)
            · have hs1121033 : InSquare (87/320) (-89/320) (1/320) tau := by
                convert childUR hs112103 hx112103 hy112103 using 1 <;> norm_num
              exact Batch0227.cell1820.sound htau (by
                simp only [Batch0227.cell1820, Batch0227.tau1820, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1121033 (by positivity) using 1 <;> norm_num)
    · have hs11212 : InSquare (21/80) (-21/80) (1/80) tau := by
        convert childUL hs hx1121 hy1121 using 1 <;> norm_num
      rcases le_total tau.re (21/80 : ℝ) with hx11212 | hx11212
      · rcases le_total tau.im (-21/80 : ℝ) with hy11212 | hy11212
        · have hs112120 : InSquare (41/160) (-43/160) (1/160) tau := by
            convert childLL hs11212 hx11212 hy11212 using 1 <;> norm_num
          rcases le_total tau.re (41/160 : ℝ) with hx112120 | hx112120
          · rcases le_total tau.im (-43/160 : ℝ) with hy112120 | hy112120
            · have hs1121200 : InSquare (81/320) (-87/320) (1/320) tau := by
                convert childLL hs112120 hx112120 hy112120 using 1 <;> norm_num
              exact Batch0228.cell1827.sound htau (by
                simp only [Batch0228.cell1827, Batch0228.tau1827, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1121200 (by positivity) using 1 <;> norm_num)
            · have hs1121202 : InSquare (81/320) (-17/64) (1/320) tau := by
                convert childUL hs112120 hx112120 hy112120 using 1 <;> norm_num
              exact Batch0228.cell1829.sound htau (by
                simp only [Batch0228.cell1829, Batch0228.tau1829, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1121202 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-43/160 : ℝ) with hy112120 | hy112120
            · have hs1121201 : InSquare (83/320) (-87/320) (1/320) tau := by
                convert childLR hs112120 hx112120 hy112120 using 1 <;> norm_num
              exact Batch0228.cell1828.sound htau (by
                simp only [Batch0228.cell1828, Batch0228.tau1828, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1121201 (by positivity) using 1 <;> norm_num)
            · have hs1121203 : InSquare (83/320) (-17/64) (1/320) tau := by
                convert childUR hs112120 hx112120 hy112120 using 1 <;> norm_num
              exact Batch0228.cell1830.sound htau (by
                simp only [Batch0228.cell1830, Batch0228.tau1830, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1121203 (by positivity) using 1 <;> norm_num)
        · have hs112122 : InSquare (41/160) (-41/160) (1/160) tau := by
            convert childUL hs11212 hx11212 hy11212 using 1 <;> norm_num
          exact Batch0082.cell0656.sound htau (by
            simp only [Batch0082.cell0656, Batch0082.tau0656, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs112122 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-21/80 : ℝ) with hy11212 | hy11212
        · have hs112121 : InSquare (43/160) (-43/160) (1/160) tau := by
            convert childLR hs11212 hx11212 hy11212 using 1 <;> norm_num
          rcases le_total tau.re (43/160 : ℝ) with hx112121 | hx112121
          · rcases le_total tau.im (-43/160 : ℝ) with hy112121 | hy112121
            · have hs1121210 : InSquare (17/64) (-87/320) (1/320) tau := by
                convert childLL hs112121 hx112121 hy112121 using 1 <;> norm_num
              exact Batch0228.cell1831.sound htau (by
                simp only [Batch0228.cell1831, Batch0228.tau1831, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1121210 (by positivity) using 1 <;> norm_num)
            · have hs1121212 : InSquare (17/64) (-17/64) (1/320) tau := by
                convert childUL hs112121 hx112121 hy112121 using 1 <;> norm_num
              exact Batch0229.cell1833.sound htau (by
                simp only [Batch0229.cell1833, Batch0229.tau1833, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1121212 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-43/160 : ℝ) with hy112121 | hy112121
            · have hs1121211 : InSquare (87/320) (-87/320) (1/320) tau := by
                convert childLR hs112121 hx112121 hy112121 using 1 <;> norm_num
              exact Batch0229.cell1832.sound htau (by
                simp only [Batch0229.cell1832, Batch0229.tau1832, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1121211 (by positivity) using 1 <;> norm_num)
            · have hs1121213 : InSquare (87/320) (-17/64) (1/320) tau := by
                convert childUR hs112121 hx112121 hy112121 using 1 <;> norm_num
              exact Batch0229.cell1834.sound htau (by
                simp only [Batch0229.cell1834, Batch0229.tau1834, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1121213 (by positivity) using 1 <;> norm_num)
        · have hs112123 : InSquare (43/160) (-41/160) (1/160) tau := by
            convert childUR hs11212 hx11212 hy11212 using 1 <;> norm_num
          exact Batch0082.cell0657.sound htau (by
            simp only [Batch0082.cell0657, Batch0082.tau0657, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs112123 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (-11/40 : ℝ) with hy1121 | hy1121
    · have hs11211 : InSquare (23/80) (-23/80) (1/80) tau := by
        convert childLR hs hx1121 hy1121 using 1 <;> norm_num
      rcases le_total tau.re (23/80 : ℝ) with hx11211 | hx11211
      · rcases le_total tau.im (-23/80 : ℝ) with hy11211 | hy11211
        · have hs112110 : InSquare (9/32) (-47/160) (1/160) tau := by
            convert childLL hs11211 hx11211 hy11211 using 1 <;> norm_num
          rcases le_total tau.re (9/32 : ℝ) with hx112110 | hx112110
          · rcases le_total tau.im (-47/160 : ℝ) with hy112110 | hy112110
            · have hs1121100 : InSquare (89/320) (-19/64) (1/320) tau := by
                convert childLL hs112110 hx112110 hy112110 using 1 <;> norm_num
              exact (outside_1121100 htau hs1121100).elim
            · have hs1121102 : InSquare (89/320) (-93/320) (1/320) tau := by
                convert childUL hs112110 hx112110 hy112110 using 1 <;> norm_num
              exact Batch0227.cell1821.sound htau (by
                simp only [Batch0227.cell1821, Batch0227.tau1821, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1121102 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-47/160 : ℝ) with hy112110 | hy112110
            · have hs1121101 : InSquare (91/320) (-19/64) (1/320) tau := by
                convert childLR hs112110 hx112110 hy112110 using 1 <;> norm_num
              exact (outside_1121101 htau hs1121101).elim
            · have hs1121103 : InSquare (91/320) (-93/320) (1/320) tau := by
                convert childUR hs112110 hx112110 hy112110 using 1 <;> norm_num
              exact (outside_1121103 htau hs1121103).elim
        · have hs112112 : InSquare (9/32) (-9/32) (1/160) tau := by
            convert childUL hs11211 hx11211 hy11211 using 1 <;> norm_num
          rcases le_total tau.re (9/32 : ℝ) with hx112112 | hx112112
          · rcases le_total tau.im (-9/32 : ℝ) with hy112112 | hy112112
            · have hs1121120 : InSquare (89/320) (-91/320) (1/320) tau := by
                convert childLL hs112112 hx112112 hy112112 using 1 <;> norm_num
              exact Batch0227.cell1822.sound htau (by
                simp only [Batch0227.cell1822, Batch0227.tau1822, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1121120 (by positivity) using 1 <;> norm_num)
            · have hs1121122 : InSquare (89/320) (-89/320) (1/320) tau := by
                convert childUL hs112112 hx112112 hy112112 using 1 <;> norm_num
              exact Batch0228.cell1824.sound htau (by
                simp only [Batch0228.cell1824, Batch0228.tau1824, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1121122 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-9/32 : ℝ) with hy112112 | hy112112
            · have hs1121121 : InSquare (91/320) (-91/320) (1/320) tau := by
                convert childLR hs112112 hx112112 hy112112 using 1 <;> norm_num
              exact Batch0227.cell1823.sound htau (by
                simp only [Batch0227.cell1823, Batch0227.tau1823, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1121121 (by positivity) using 1 <;> norm_num)
            · have hs1121123 : InSquare (91/320) (-89/320) (1/320) tau := by
                convert childUR hs112112 hx112112 hy112112 using 1 <;> norm_num
              exact Batch0228.cell1825.sound htau (by
                simp only [Batch0228.cell1825, Batch0228.tau1825, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1121123 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-23/80 : ℝ) with hy11211 | hy11211
        · have hs112111 : InSquare (47/160) (-47/160) (1/160) tau := by
            convert childLR hs11211 hx11211 hy11211 using 1 <;> norm_num
          exact (outside_112111 htau hs112111).elim
        · have hs112113 : InSquare (47/160) (-9/32) (1/160) tau := by
            convert childUR hs11211 hx11211 hy11211 using 1 <;> norm_num
          rcases le_total tau.re (47/160 : ℝ) with hx112113 | hx112113
          · rcases le_total tau.im (-9/32 : ℝ) with hy112113 | hy112113
            · have hs1121130 : InSquare (93/320) (-91/320) (1/320) tau := by
                convert childLL hs112113 hx112113 hy112113 using 1 <;> norm_num
              exact (outside_1121130 htau hs1121130).elim
            · have hs1121132 : InSquare (93/320) (-89/320) (1/320) tau := by
                convert childUL hs112113 hx112113 hy112113 using 1 <;> norm_num
              exact Batch0228.cell1826.sound htau (by
                simp only [Batch0228.cell1826, Batch0228.tau1826, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1121132 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-9/32 : ℝ) with hy112113 | hy112113
            · have hs1121131 : InSquare (19/64) (-91/320) (1/320) tau := by
                convert childLR hs112113 hx112113 hy112113 using 1 <;> norm_num
              exact (outside_1121131 htau hs1121131).elim
            · have hs1121133 : InSquare (19/64) (-89/320) (1/320) tau := by
                convert childUR hs112113 hx112113 hy112113 using 1 <;> norm_num
              exact (outside_1121133 htau hs1121133).elim
    · have hs11213 : InSquare (23/80) (-21/80) (1/80) tau := by
        convert childUR hs hx1121 hy1121 using 1 <;> norm_num
      rcases le_total tau.re (23/80 : ℝ) with hx11213 | hx11213
      · rcases le_total tau.im (-21/80 : ℝ) with hy11213 | hy11213
        · have hs112130 : InSquare (9/32) (-43/160) (1/160) tau := by
            convert childLL hs11213 hx11213 hy11213 using 1 <;> norm_num
          rcases le_total tau.re (9/32 : ℝ) with hx112130 | hx112130
          · rcases le_total tau.im (-43/160 : ℝ) with hy112130 | hy112130
            · have hs1121300 : InSquare (89/320) (-87/320) (1/320) tau := by
                convert childLL hs112130 hx112130 hy112130 using 1 <;> norm_num
              exact Batch0229.cell1835.sound htau (by
                simp only [Batch0229.cell1835, Batch0229.tau1835, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1121300 (by positivity) using 1 <;> norm_num)
            · have hs1121302 : InSquare (89/320) (-17/64) (1/320) tau := by
                convert childUL hs112130 hx112130 hy112130 using 1 <;> norm_num
              exact Batch0229.cell1837.sound htau (by
                simp only [Batch0229.cell1837, Batch0229.tau1837, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1121302 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-43/160 : ℝ) with hy112130 | hy112130
            · have hs1121301 : InSquare (91/320) (-87/320) (1/320) tau := by
                convert childLR hs112130 hx112130 hy112130 using 1 <;> norm_num
              exact Batch0229.cell1836.sound htau (by
                simp only [Batch0229.cell1836, Batch0229.tau1836, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1121301 (by positivity) using 1 <;> norm_num)
            · have hs1121303 : InSquare (91/320) (-17/64) (1/320) tau := by
                convert childUR hs112130 hx112130 hy112130 using 1 <;> norm_num
              exact Batch0229.cell1838.sound htau (by
                simp only [Batch0229.cell1838, Batch0229.tau1838, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1121303 (by positivity) using 1 <;> norm_num)
        · have hs112132 : InSquare (9/32) (-41/160) (1/160) tau := by
            convert childUL hs11213 hx11213 hy11213 using 1 <;> norm_num
          rcases le_total tau.re (9/32 : ℝ) with hx112132 | hx112132
          · rcases le_total tau.im (-41/160 : ℝ) with hy112132 | hy112132
            · have hs1121320 : InSquare (89/320) (-83/320) (1/320) tau := by
                convert childLL hs112132 hx112132 hy112132 using 1 <;> norm_num
              exact Batch0230.cell1843.sound htau (by
                simp only [Batch0230.cell1843, Batch0230.tau1843, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1121320 (by positivity) using 1 <;> norm_num)
            · have hs1121322 : InSquare (89/320) (-81/320) (1/320) tau := by
                convert childUL hs112132 hx112132 hy112132 using 1 <;> norm_num
              exact Batch0230.cell1845.sound htau (by
                simp only [Batch0230.cell1845, Batch0230.tau1845, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1121322 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-41/160 : ℝ) with hy112132 | hy112132
            · have hs1121321 : InSquare (91/320) (-83/320) (1/320) tau := by
                convert childLR hs112132 hx112132 hy112132 using 1 <;> norm_num
              exact Batch0230.cell1844.sound htau (by
                simp only [Batch0230.cell1844, Batch0230.tau1844, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1121321 (by positivity) using 1 <;> norm_num)
            · have hs1121323 : InSquare (91/320) (-81/320) (1/320) tau := by
                convert childUR hs112132 hx112132 hy112132 using 1 <;> norm_num
              exact Batch0230.cell1846.sound htau (by
                simp only [Batch0230.cell1846, Batch0230.tau1846, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1121323 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-21/80 : ℝ) with hy11213 | hy11213
        · have hs112131 : InSquare (47/160) (-43/160) (1/160) tau := by
            convert childLR hs11213 hx11213 hy11213 using 1 <;> norm_num
          rcases le_total tau.re (47/160 : ℝ) with hx112131 | hx112131
          · rcases le_total tau.im (-43/160 : ℝ) with hy112131 | hy112131
            · have hs1121310 : InSquare (93/320) (-87/320) (1/320) tau := by
                convert childLL hs112131 hx112131 hy112131 using 1 <;> norm_num
              exact Batch0229.cell1839.sound htau (by
                simp only [Batch0229.cell1839, Batch0229.tau1839, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1121310 (by positivity) using 1 <;> norm_num)
            · have hs1121312 : InSquare (93/320) (-17/64) (1/320) tau := by
                convert childUL hs112131 hx112131 hy112131 using 1 <;> norm_num
              exact Batch0230.cell1841.sound htau (by
                simp only [Batch0230.cell1841, Batch0230.tau1841, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1121312 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-43/160 : ℝ) with hy112131 | hy112131
            · have hs1121311 : InSquare (19/64) (-87/320) (1/320) tau := by
                convert childLR hs112131 hx112131 hy112131 using 1 <;> norm_num
              exact Batch0230.cell1840.sound htau (by
                simp only [Batch0230.cell1840, Batch0230.tau1840, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1121311 (by positivity) using 1 <;> norm_num)
            · have hs1121313 : InSquare (19/64) (-17/64) (1/320) tau := by
                convert childUR hs112131 hx112131 hy112131 using 1 <;> norm_num
              exact Batch0230.cell1842.sound htau (by
                simp only [Batch0230.cell1842, Batch0230.tau1842, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1121313 (by positivity) using 1 <;> norm_num)
        · have hs112133 : InSquare (47/160) (-41/160) (1/160) tau := by
            convert childUR hs11213 hx11213 hy11213 using 1 <;> norm_num
          rcases le_total tau.re (47/160 : ℝ) with hx112133 | hx112133
          · rcases le_total tau.im (-41/160 : ℝ) with hy112133 | hy112133
            · have hs1121330 : InSquare (93/320) (-83/320) (1/320) tau := by
                convert childLL hs112133 hx112133 hy112133 using 1 <;> norm_num
              exact Batch0230.cell1847.sound htau (by
                simp only [Batch0230.cell1847, Batch0230.tau1847, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1121330 (by positivity) using 1 <;> norm_num)
            · have hs1121332 : InSquare (93/320) (-81/320) (1/320) tau := by
                convert childUL hs112133 hx112133 hy112133 using 1 <;> norm_num
              exact Batch0231.cell1849.sound htau (by
                simp only [Batch0231.cell1849, Batch0231.tau1849, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1121332 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-41/160 : ℝ) with hy112133 | hy112133
            · have hs1121331 : InSquare (19/64) (-83/320) (1/320) tau := by
                convert childLR hs112133 hx112133 hy112133 using 1 <;> norm_num
              exact Batch0231.cell1848.sound htau (by
                simp only [Batch0231.cell1848, Batch0231.tau1848, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1121331 (by positivity) using 1 <;> norm_num)
            · have hs1121333 : InSquare (19/64) (-81/320) (1/320) tau := by
                convert childUR hs112133 hx112133 hy112133 using 1 <;> norm_num
              exact Batch0231.cell1850.sound htau (by
                simp only [Batch0231.cell1850, Batch0231.tau1850, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1121333 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1121
