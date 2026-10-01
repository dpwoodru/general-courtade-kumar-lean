import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0086
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0232
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0233
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0234
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0235

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1132

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

private theorem outside_113210 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (53/160) (-39/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (13/40 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-13/40)]
  have himSq : (19/80 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+19/80)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_113211 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (11/32) (-39/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (27/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-27/80)]
  have himSq : (19/80 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+19/80)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_113213 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (11/32) (-37/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (27/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-27/80)]
  have himSq : (9/40 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+9/40)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_1132011 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (103/320) (-79/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (51/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-51/160)]
  have himSq : (39/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+39/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_1132121 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (107/320) (-15/64) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (53/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-53/160)]
  have himSq : (37/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+37/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_1132123 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (107/320) (-73/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (53/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-53/160)]
  have himSq : (9/40 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+9/40)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_1132310 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (109/320) (-71/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (27/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-27/80)]
  have himSq : (7/32 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+7/32)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_1132311 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (111/320) (-71/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (11/32 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-11/32)]
  have himSq : (7/32 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+7/32)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_1132313 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (111/320) (-69/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (11/32 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-11/32)]
  have himSq : (17/80 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+17/80)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_1132331 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (111/320) (-67/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (11/32 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re-11/32)]
  have himSq : (33/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im+33/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (13/40) (-9/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (13/40 : ℝ) with hx1132 | hx1132
  · rcases le_total tau.im (-9/40 : ℝ) with hy1132 | hy1132
    · have hs11320 : InSquare (5/16) (-19/80) (1/80) tau := by
        convert childLL hs hx1132 hy1132 using 1 <;> norm_num
      rcases le_total tau.re (5/16 : ℝ) with hx11320 | hx11320
      · rcases le_total tau.im (-19/80 : ℝ) with hy11320 | hy11320
        · have hs113200 : InSquare (49/160) (-39/160) (1/160) tau := by
            convert childLL hs11320 hx11320 hy11320 using 1 <;> norm_num
          rcases le_total tau.re (49/160 : ℝ) with hx113200 | hx113200
          · rcases le_total tau.im (-39/160 : ℝ) with hy113200 | hy113200
            · have hs1132000 : InSquare (97/320) (-79/320) (1/320) tau := by
                convert childLL hs113200 hx113200 hy113200 using 1 <;> norm_num
              exact Batch0232.cell1860.sound htau (by
                simp only [Batch0232.cell1860, Batch0232.tau1860, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1132000 (by positivity) using 1 <;> norm_num)
            · have hs1132002 : InSquare (97/320) (-77/320) (1/320) tau := by
                convert childUL hs113200 hx113200 hy113200 using 1 <;> norm_num
              exact Batch0232.cell1862.sound htau (by
                simp only [Batch0232.cell1862, Batch0232.tau1862, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1132002 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-39/160 : ℝ) with hy113200 | hy113200
            · have hs1132001 : InSquare (99/320) (-79/320) (1/320) tau := by
                convert childLR hs113200 hx113200 hy113200 using 1 <;> norm_num
              exact Batch0232.cell1861.sound htau (by
                simp only [Batch0232.cell1861, Batch0232.tau1861, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1132001 (by positivity) using 1 <;> norm_num)
            · have hs1132003 : InSquare (99/320) (-77/320) (1/320) tau := by
                convert childUR hs113200 hx113200 hy113200 using 1 <;> norm_num
              exact Batch0232.cell1863.sound htau (by
                simp only [Batch0232.cell1863, Batch0232.tau1863, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1132003 (by positivity) using 1 <;> norm_num)
        · have hs113202 : InSquare (49/160) (-37/160) (1/160) tau := by
            convert childUL hs11320 hx11320 hy11320 using 1 <;> norm_num
          exact Batch0086.cell0689.sound htau (by
            simp only [Batch0086.cell0689, Batch0086.tau0689, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs113202 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-19/80 : ℝ) with hy11320 | hy11320
        · have hs113201 : InSquare (51/160) (-39/160) (1/160) tau := by
            convert childLR hs11320 hx11320 hy11320 using 1 <;> norm_num
          rcases le_total tau.re (51/160 : ℝ) with hx113201 | hx113201
          · rcases le_total tau.im (-39/160 : ℝ) with hy113201 | hy113201
            · have hs1132010 : InSquare (101/320) (-79/320) (1/320) tau := by
                convert childLL hs113201 hx113201 hy113201 using 1 <;> norm_num
              exact Batch0233.cell1864.sound htau (by
                simp only [Batch0233.cell1864, Batch0233.tau1864, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1132010 (by positivity) using 1 <;> norm_num)
            · have hs1132012 : InSquare (101/320) (-77/320) (1/320) tau := by
                convert childUL hs113201 hx113201 hy113201 using 1 <;> norm_num
              exact Batch0233.cell1865.sound htau (by
                simp only [Batch0233.cell1865, Batch0233.tau1865, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1132012 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-39/160 : ℝ) with hy113201 | hy113201
            · have hs1132011 : InSquare (103/320) (-79/320) (1/320) tau := by
                convert childLR hs113201 hx113201 hy113201 using 1 <;> norm_num
              exact (outside_1132011 htau hs1132011).elim
            · have hs1132013 : InSquare (103/320) (-77/320) (1/320) tau := by
                convert childUR hs113201 hx113201 hy113201 using 1 <;> norm_num
              exact Batch0233.cell1866.sound htau (by
                simp only [Batch0233.cell1866, Batch0233.tau1866, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1132013 (by positivity) using 1 <;> norm_num)
        · have hs113203 : InSquare (51/160) (-37/160) (1/160) tau := by
            convert childUR hs11320 hx11320 hy11320 using 1 <;> norm_num
          rcases le_total tau.re (51/160 : ℝ) with hx113203 | hx113203
          · rcases le_total tau.im (-37/160 : ℝ) with hy113203 | hy113203
            · have hs1132030 : InSquare (101/320) (-15/64) (1/320) tau := by
                convert childLL hs113203 hx113203 hy113203 using 1 <;> norm_num
              exact Batch0233.cell1867.sound htau (by
                simp only [Batch0233.cell1867, Batch0233.tau1867, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1132030 (by positivity) using 1 <;> norm_num)
            · have hs1132032 : InSquare (101/320) (-73/320) (1/320) tau := by
                convert childUL hs113203 hx113203 hy113203 using 1 <;> norm_num
              exact Batch0233.cell1869.sound htau (by
                simp only [Batch0233.cell1869, Batch0233.tau1869, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1132032 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-37/160 : ℝ) with hy113203 | hy113203
            · have hs1132031 : InSquare (103/320) (-15/64) (1/320) tau := by
                convert childLR hs113203 hx113203 hy113203 using 1 <;> norm_num
              exact Batch0233.cell1868.sound htau (by
                simp only [Batch0233.cell1868, Batch0233.tau1868, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1132031 (by positivity) using 1 <;> norm_num)
            · have hs1132033 : InSquare (103/320) (-73/320) (1/320) tau := by
                convert childUR hs113203 hx113203 hy113203 using 1 <;> norm_num
              exact Batch0233.cell1870.sound htau (by
                simp only [Batch0233.cell1870, Batch0233.tau1870, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1132033 (by positivity) using 1 <;> norm_num)
    · have hs11322 : InSquare (5/16) (-17/80) (1/80) tau := by
        convert childUL hs hx1132 hy1132 using 1 <;> norm_num
      rcases le_total tau.re (5/16 : ℝ) with hx11322 | hx11322
      · rcases le_total tau.im (-17/80 : ℝ) with hy11322 | hy11322
        · have hs113220 : InSquare (49/160) (-7/32) (1/160) tau := by
            convert childLL hs11322 hx11322 hy11322 using 1 <;> norm_num
          exact Batch0086.cell0690.sound htau (by
            simp only [Batch0086.cell0690, Batch0086.tau0690, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs113220 (by positivity) using 1 <;> norm_num)
        · have hs113222 : InSquare (49/160) (-33/160) (1/160) tau := by
            convert childUL hs11322 hx11322 hy11322 using 1 <;> norm_num
          exact Batch0086.cell0692.sound htau (by
            simp only [Batch0086.cell0692, Batch0086.tau0692, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs113222 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-17/80 : ℝ) with hy11322 | hy11322
        · have hs113221 : InSquare (51/160) (-7/32) (1/160) tau := by
            convert childLR hs11322 hx11322 hy11322 using 1 <;> norm_num
          exact Batch0086.cell0691.sound htau (by
            simp only [Batch0086.cell0691, Batch0086.tau0691, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs113221 (by positivity) using 1 <;> norm_num)
        · have hs113223 : InSquare (51/160) (-33/160) (1/160) tau := by
            convert childUR hs11322 hx11322 hy11322 using 1 <;> norm_num
          exact Batch0086.cell0693.sound htau (by
            simp only [Batch0086.cell0693, Batch0086.tau0693, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs113223 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (-9/40 : ℝ) with hy1132 | hy1132
    · have hs11321 : InSquare (27/80) (-19/80) (1/80) tau := by
        convert childLR hs hx1132 hy1132 using 1 <;> norm_num
      rcases le_total tau.re (27/80 : ℝ) with hx11321 | hx11321
      · rcases le_total tau.im (-19/80 : ℝ) with hy11321 | hy11321
        · have hs113210 : InSquare (53/160) (-39/160) (1/160) tau := by
            convert childLL hs11321 hx11321 hy11321 using 1 <;> norm_num
          exact (outside_113210 htau hs113210).elim
        · have hs113212 : InSquare (53/160) (-37/160) (1/160) tau := by
            convert childUL hs11321 hx11321 hy11321 using 1 <;> norm_num
          rcases le_total tau.re (53/160 : ℝ) with hx113212 | hx113212
          · rcases le_total tau.im (-37/160 : ℝ) with hy113212 | hy113212
            · have hs1132120 : InSquare (21/64) (-15/64) (1/320) tau := by
                convert childLL hs113212 hx113212 hy113212 using 1 <;> norm_num
              exact Batch0233.cell1871.sound htau (by
                simp only [Batch0233.cell1871, Batch0233.tau1871, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1132120 (by positivity) using 1 <;> norm_num)
            · have hs1132122 : InSquare (21/64) (-73/320) (1/320) tau := by
                convert childUL hs113212 hx113212 hy113212 using 1 <;> norm_num
              exact Batch0234.cell1872.sound htau (by
                simp only [Batch0234.cell1872, Batch0234.tau1872, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1132122 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-37/160 : ℝ) with hy113212 | hy113212
            · have hs1132121 : InSquare (107/320) (-15/64) (1/320) tau := by
                convert childLR hs113212 hx113212 hy113212 using 1 <;> norm_num
              exact (outside_1132121 htau hs1132121).elim
            · have hs1132123 : InSquare (107/320) (-73/320) (1/320) tau := by
                convert childUR hs113212 hx113212 hy113212 using 1 <;> norm_num
              exact (outside_1132123 htau hs1132123).elim
      · rcases le_total tau.im (-19/80 : ℝ) with hy11321 | hy11321
        · have hs113211 : InSquare (11/32) (-39/160) (1/160) tau := by
            convert childLR hs11321 hx11321 hy11321 using 1 <;> norm_num
          exact (outside_113211 htau hs113211).elim
        · have hs113213 : InSquare (11/32) (-37/160) (1/160) tau := by
            convert childUR hs11321 hx11321 hy11321 using 1 <;> norm_num
          exact (outside_113213 htau hs113213).elim
    · have hs11323 : InSquare (27/80) (-17/80) (1/80) tau := by
        convert childUR hs hx1132 hy1132 using 1 <;> norm_num
      rcases le_total tau.re (27/80 : ℝ) with hx11323 | hx11323
      · rcases le_total tau.im (-17/80 : ℝ) with hy11323 | hy11323
        · have hs113230 : InSquare (53/160) (-7/32) (1/160) tau := by
            convert childLL hs11323 hx11323 hy11323 using 1 <;> norm_num
          rcases le_total tau.re (53/160 : ℝ) with hx113230 | hx113230
          · rcases le_total tau.im (-7/32 : ℝ) with hy113230 | hy113230
            · have hs1132300 : InSquare (21/64) (-71/320) (1/320) tau := by
                convert childLL hs113230 hx113230 hy113230 using 1 <;> norm_num
              exact Batch0234.cell1873.sound htau (by
                simp only [Batch0234.cell1873, Batch0234.tau1873, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1132300 (by positivity) using 1 <;> norm_num)
            · have hs1132302 : InSquare (21/64) (-69/320) (1/320) tau := by
                convert childUL hs113230 hx113230 hy113230 using 1 <;> norm_num
              exact Batch0234.cell1875.sound htau (by
                simp only [Batch0234.cell1875, Batch0234.tau1875, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1132302 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-7/32 : ℝ) with hy113230 | hy113230
            · have hs1132301 : InSquare (107/320) (-71/320) (1/320) tau := by
                convert childLR hs113230 hx113230 hy113230 using 1 <;> norm_num
              exact Batch0234.cell1874.sound htau (by
                simp only [Batch0234.cell1874, Batch0234.tau1874, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1132301 (by positivity) using 1 <;> norm_num)
            · have hs1132303 : InSquare (107/320) (-69/320) (1/320) tau := by
                convert childUR hs113230 hx113230 hy113230 using 1 <;> norm_num
              exact Batch0234.cell1876.sound htau (by
                simp only [Batch0234.cell1876, Batch0234.tau1876, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1132303 (by positivity) using 1 <;> norm_num)
        · have hs113232 : InSquare (53/160) (-33/160) (1/160) tau := by
            convert childUL hs11323 hx11323 hy11323 using 1 <;> norm_num
          exact Batch0086.cell0694.sound htau (by
            simp only [Batch0086.cell0694, Batch0086.tau0694, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs113232 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-17/80 : ℝ) with hy11323 | hy11323
        · have hs113231 : InSquare (11/32) (-7/32) (1/160) tau := by
            convert childLR hs11323 hx11323 hy11323 using 1 <;> norm_num
          rcases le_total tau.re (11/32 : ℝ) with hx113231 | hx113231
          · rcases le_total tau.im (-7/32 : ℝ) with hy113231 | hy113231
            · have hs1132310 : InSquare (109/320) (-71/320) (1/320) tau := by
                convert childLL hs113231 hx113231 hy113231 using 1 <;> norm_num
              exact (outside_1132310 htau hs1132310).elim
            · have hs1132312 : InSquare (109/320) (-69/320) (1/320) tau := by
                convert childUL hs113231 hx113231 hy113231 using 1 <;> norm_num
              exact Batch0234.cell1877.sound htau (by
                simp only [Batch0234.cell1877, Batch0234.tau1877, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1132312 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-7/32 : ℝ) with hy113231 | hy113231
            · have hs1132311 : InSquare (111/320) (-71/320) (1/320) tau := by
                convert childLR hs113231 hx113231 hy113231 using 1 <;> norm_num
              exact (outside_1132311 htau hs1132311).elim
            · have hs1132313 : InSquare (111/320) (-69/320) (1/320) tau := by
                convert childUR hs113231 hx113231 hy113231 using 1 <;> norm_num
              exact (outside_1132313 htau hs1132313).elim
        · have hs113233 : InSquare (11/32) (-33/160) (1/160) tau := by
            convert childUR hs11323 hx11323 hy11323 using 1 <;> norm_num
          rcases le_total tau.re (11/32 : ℝ) with hx113233 | hx113233
          · rcases le_total tau.im (-33/160 : ℝ) with hy113233 | hy113233
            · have hs1132330 : InSquare (109/320) (-67/320) (1/320) tau := by
                convert childLL hs113233 hx113233 hy113233 using 1 <;> norm_num
              exact Batch0234.cell1878.sound htau (by
                simp only [Batch0234.cell1878, Batch0234.tau1878, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1132330 (by positivity) using 1 <;> norm_num)
            · have hs1132332 : InSquare (109/320) (-13/64) (1/320) tau := by
                convert childUL hs113233 hx113233 hy113233 using 1 <;> norm_num
              exact Batch0234.cell1879.sound htau (by
                simp only [Batch0234.cell1879, Batch0234.tau1879, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1132332 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-33/160 : ℝ) with hy113233 | hy113233
            · have hs1132331 : InSquare (111/320) (-67/320) (1/320) tau := by
                convert childLR hs113233 hx113233 hy113233 using 1 <;> norm_num
              exact (outside_1132331 htau hs1132331).elim
            · have hs1132333 : InSquare (111/320) (-13/64) (1/320) tau := by
                convert childUR hs113233 hx113233 hy113233 using 1 <;> norm_num
              exact Batch0235.cell1880.sound htau (by
                simp only [Batch0235.cell1880, Batch0235.tau1880, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs1132333 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage1132
