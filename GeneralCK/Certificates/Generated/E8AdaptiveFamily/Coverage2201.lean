import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0106
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0235
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0236
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0237

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2201

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

private theorem outside_220120 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-11/32) (37/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (27/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+27/80)]
  have himSq : (9/40 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-9/40)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_220122 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-11/32) (39/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (27/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+27/80)]
  have himSq : (19/80 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-19/80)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_220123 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-53/160) (39/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (13/40 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+13/40)]
  have himSq : (19/80 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-19/80)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_2201002 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-111/320) (67/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (11/32 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+11/32)]
  have himSq : (33/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-33/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_2201020 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-111/320) (69/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (11/32 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+11/32)]
  have himSq : (17/80 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-17/80)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_2201022 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-111/320) (71/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (11/32 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+11/32)]
  have himSq : (7/32 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-7/32)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_2201023 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-109/320) (71/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (27/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+27/80)]
  have himSq : (7/32 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-7/32)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_2201210 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-107/320) (73/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (53/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+53/160)]
  have himSq : (9/40 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-9/40)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_2201212 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-107/320) (15/64) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (53/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+53/160)]
  have himSq : (37/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-37/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_2201322 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-103/320) (79/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (51/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+51/160)]
  have himSq : (39/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-39/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-13/40) (9/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (-13/40 : ℝ) with hx2201 | hx2201
  · rcases le_total tau.im (9/40 : ℝ) with hy2201 | hy2201
    · have hs22010 : InSquare (-27/80) (17/80) (1/80) tau := by
        convert childLL hs hx2201 hy2201 using 1 <;> norm_num
      rcases le_total tau.re (-27/80 : ℝ) with hx22010 | hx22010
      · rcases le_total tau.im (17/80 : ℝ) with hy22010 | hy22010
        · have hs220100 : InSquare (-11/32) (33/160) (1/160) tau := by
            convert childLL hs22010 hx22010 hy22010 using 1 <;> norm_num
          rcases le_total tau.re (-11/32 : ℝ) with hx220100 | hx220100
          · rcases le_total tau.im (33/160 : ℝ) with hy220100 | hy220100
            · have hs2201000 : InSquare (-111/320) (13/64) (1/320) tau := by
                convert childLL hs220100 hx220100 hy220100 using 1 <;> norm_num
              exact Batch0235.cell1883.sound htau (by
                simp only [Batch0235.cell1883, Batch0235.tau1883, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2201000 (by positivity) using 1 <;> norm_num)
            · have hs2201002 : InSquare (-111/320) (67/320) (1/320) tau := by
                convert childUL hs220100 hx220100 hy220100 using 1 <;> norm_num
              exact (outside_2201002 htau hs2201002).elim
          · rcases le_total tau.im (33/160 : ℝ) with hy220100 | hy220100
            · have hs2201001 : InSquare (-109/320) (13/64) (1/320) tau := by
                convert childLR hs220100 hx220100 hy220100 using 1 <;> norm_num
              exact Batch0235.cell1884.sound htau (by
                simp only [Batch0235.cell1884, Batch0235.tau1884, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2201001 (by positivity) using 1 <;> norm_num)
            · have hs2201003 : InSquare (-109/320) (67/320) (1/320) tau := by
                convert childUR hs220100 hx220100 hy220100 using 1 <;> norm_num
              exact Batch0235.cell1885.sound htau (by
                simp only [Batch0235.cell1885, Batch0235.tau1885, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2201003 (by positivity) using 1 <;> norm_num)
        · have hs220102 : InSquare (-11/32) (7/32) (1/160) tau := by
            convert childUL hs22010 hx22010 hy22010 using 1 <;> norm_num
          rcases le_total tau.re (-11/32 : ℝ) with hx220102 | hx220102
          · rcases le_total tau.im (7/32 : ℝ) with hy220102 | hy220102
            · have hs2201020 : InSquare (-111/320) (69/320) (1/320) tau := by
                convert childLL hs220102 hx220102 hy220102 using 1 <;> norm_num
              exact (outside_2201020 htau hs2201020).elim
            · have hs2201022 : InSquare (-111/320) (71/320) (1/320) tau := by
                convert childUL hs220102 hx220102 hy220102 using 1 <;> norm_num
              exact (outside_2201022 htau hs2201022).elim
          · rcases le_total tau.im (7/32 : ℝ) with hy220102 | hy220102
            · have hs2201021 : InSquare (-109/320) (69/320) (1/320) tau := by
                convert childLR hs220102 hx220102 hy220102 using 1 <;> norm_num
              exact Batch0235.cell1886.sound htau (by
                simp only [Batch0235.cell1886, Batch0235.tau1886, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2201021 (by positivity) using 1 <;> norm_num)
            · have hs2201023 : InSquare (-109/320) (71/320) (1/320) tau := by
                convert childUR hs220102 hx220102 hy220102 using 1 <;> norm_num
              exact (outside_2201023 htau hs2201023).elim
      · rcases le_total tau.im (17/80 : ℝ) with hy22010 | hy22010
        · have hs220101 : InSquare (-53/160) (33/160) (1/160) tau := by
            convert childLR hs22010 hx22010 hy22010 using 1 <;> norm_num
          exact Batch0106.cell0849.sound htau (by
            simp only [Batch0106.cell0849, Batch0106.tau0849, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs220101 (by positivity) using 1 <;> norm_num)
        · have hs220103 : InSquare (-53/160) (7/32) (1/160) tau := by
            convert childUR hs22010 hx22010 hy22010 using 1 <;> norm_num
          rcases le_total tau.re (-53/160 : ℝ) with hx220103 | hx220103
          · rcases le_total tau.im (7/32 : ℝ) with hy220103 | hy220103
            · have hs2201030 : InSquare (-107/320) (69/320) (1/320) tau := by
                convert childLL hs220103 hx220103 hy220103 using 1 <;> norm_num
              exact Batch0235.cell1887.sound htau (by
                simp only [Batch0235.cell1887, Batch0235.tau1887, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2201030 (by positivity) using 1 <;> norm_num)
            · have hs2201032 : InSquare (-107/320) (71/320) (1/320) tau := by
                convert childUL hs220103 hx220103 hy220103 using 1 <;> norm_num
              exact Batch0236.cell1889.sound htau (by
                simp only [Batch0236.cell1889, Batch0236.tau1889, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2201032 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (7/32 : ℝ) with hy220103 | hy220103
            · have hs2201031 : InSquare (-21/64) (69/320) (1/320) tau := by
                convert childLR hs220103 hx220103 hy220103 using 1 <;> norm_num
              exact Batch0236.cell1888.sound htau (by
                simp only [Batch0236.cell1888, Batch0236.tau1888, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2201031 (by positivity) using 1 <;> norm_num)
            · have hs2201033 : InSquare (-21/64) (71/320) (1/320) tau := by
                convert childUR hs220103 hx220103 hy220103 using 1 <;> norm_num
              exact Batch0236.cell1890.sound htau (by
                simp only [Batch0236.cell1890, Batch0236.tau1890, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2201033 (by positivity) using 1 <;> norm_num)
    · have hs22012 : InSquare (-27/80) (19/80) (1/80) tau := by
        convert childUL hs hx2201 hy2201 using 1 <;> norm_num
      rcases le_total tau.re (-27/80 : ℝ) with hx22012 | hx22012
      · rcases le_total tau.im (19/80 : ℝ) with hy22012 | hy22012
        · have hs220120 : InSquare (-11/32) (37/160) (1/160) tau := by
            convert childLL hs22012 hx22012 hy22012 using 1 <;> norm_num
          exact (outside_220120 htau hs220120).elim
        · have hs220122 : InSquare (-11/32) (39/160) (1/160) tau := by
            convert childUL hs22012 hx22012 hy22012 using 1 <;> norm_num
          exact (outside_220122 htau hs220122).elim
      · rcases le_total tau.im (19/80 : ℝ) with hy22012 | hy22012
        · have hs220121 : InSquare (-53/160) (37/160) (1/160) tau := by
            convert childLR hs22012 hx22012 hy22012 using 1 <;> norm_num
          rcases le_total tau.re (-53/160 : ℝ) with hx220121 | hx220121
          · rcases le_total tau.im (37/160 : ℝ) with hy220121 | hy220121
            · have hs2201210 : InSquare (-107/320) (73/320) (1/320) tau := by
                convert childLL hs220121 hx220121 hy220121 using 1 <;> norm_num
              exact (outside_2201210 htau hs2201210).elim
            · have hs2201212 : InSquare (-107/320) (15/64) (1/320) tau := by
                convert childUL hs220121 hx220121 hy220121 using 1 <;> norm_num
              exact (outside_2201212 htau hs2201212).elim
          · rcases le_total tau.im (37/160 : ℝ) with hy220121 | hy220121
            · have hs2201211 : InSquare (-21/64) (73/320) (1/320) tau := by
                convert childLR hs220121 hx220121 hy220121 using 1 <;> norm_num
              exact Batch0236.cell1891.sound htau (by
                simp only [Batch0236.cell1891, Batch0236.tau1891, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2201211 (by positivity) using 1 <;> norm_num)
            · have hs2201213 : InSquare (-21/64) (15/64) (1/320) tau := by
                convert childUR hs220121 hx220121 hy220121 using 1 <;> norm_num
              exact Batch0236.cell1892.sound htau (by
                simp only [Batch0236.cell1892, Batch0236.tau1892, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2201213 (by positivity) using 1 <;> norm_num)
        · have hs220123 : InSquare (-53/160) (39/160) (1/160) tau := by
            convert childUR hs22012 hx22012 hy22012 using 1 <;> norm_num
          exact (outside_220123 htau hs220123).elim
  · rcases le_total tau.im (9/40 : ℝ) with hy2201 | hy2201
    · have hs22011 : InSquare (-5/16) (17/80) (1/80) tau := by
        convert childLR hs hx2201 hy2201 using 1 <;> norm_num
      rcases le_total tau.re (-5/16 : ℝ) with hx22011 | hx22011
      · rcases le_total tau.im (17/80 : ℝ) with hy22011 | hy22011
        · have hs220110 : InSquare (-51/160) (33/160) (1/160) tau := by
            convert childLL hs22011 hx22011 hy22011 using 1 <;> norm_num
          exact Batch0106.cell0850.sound htau (by
            simp only [Batch0106.cell0850, Batch0106.tau0850, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs220110 (by positivity) using 1 <;> norm_num)
        · have hs220112 : InSquare (-51/160) (7/32) (1/160) tau := by
            convert childUL hs22011 hx22011 hy22011 using 1 <;> norm_num
          exact Batch0106.cell0852.sound htau (by
            simp only [Batch0106.cell0852, Batch0106.tau0852, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs220112 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (17/80 : ℝ) with hy22011 | hy22011
        · have hs220111 : InSquare (-49/160) (33/160) (1/160) tau := by
            convert childLR hs22011 hx22011 hy22011 using 1 <;> norm_num
          exact Batch0106.cell0851.sound htau (by
            simp only [Batch0106.cell0851, Batch0106.tau0851, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs220111 (by positivity) using 1 <;> norm_num)
        · have hs220113 : InSquare (-49/160) (7/32) (1/160) tau := by
            convert childUR hs22011 hx22011 hy22011 using 1 <;> norm_num
          exact Batch0106.cell0853.sound htau (by
            simp only [Batch0106.cell0853, Batch0106.tau0853, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs220113 (by positivity) using 1 <;> norm_num)
    · have hs22013 : InSquare (-5/16) (19/80) (1/80) tau := by
        convert childUR hs hx2201 hy2201 using 1 <;> norm_num
      rcases le_total tau.re (-5/16 : ℝ) with hx22013 | hx22013
      · rcases le_total tau.im (19/80 : ℝ) with hy22013 | hy22013
        · have hs220130 : InSquare (-51/160) (37/160) (1/160) tau := by
            convert childLL hs22013 hx22013 hy22013 using 1 <;> norm_num
          rcases le_total tau.re (-51/160 : ℝ) with hx220130 | hx220130
          · rcases le_total tau.im (37/160 : ℝ) with hy220130 | hy220130
            · have hs2201300 : InSquare (-103/320) (73/320) (1/320) tau := by
                convert childLL hs220130 hx220130 hy220130 using 1 <;> norm_num
              exact Batch0236.cell1893.sound htau (by
                simp only [Batch0236.cell1893, Batch0236.tau1893, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2201300 (by positivity) using 1 <;> norm_num)
            · have hs2201302 : InSquare (-103/320) (15/64) (1/320) tau := by
                convert childUL hs220130 hx220130 hy220130 using 1 <;> norm_num
              exact Batch0236.cell1895.sound htau (by
                simp only [Batch0236.cell1895, Batch0236.tau1895, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2201302 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (37/160 : ℝ) with hy220130 | hy220130
            · have hs2201301 : InSquare (-101/320) (73/320) (1/320) tau := by
                convert childLR hs220130 hx220130 hy220130 using 1 <;> norm_num
              exact Batch0236.cell1894.sound htau (by
                simp only [Batch0236.cell1894, Batch0236.tau1894, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2201301 (by positivity) using 1 <;> norm_num)
            · have hs2201303 : InSquare (-101/320) (15/64) (1/320) tau := by
                convert childUR hs220130 hx220130 hy220130 using 1 <;> norm_num
              exact Batch0237.cell1896.sound htau (by
                simp only [Batch0237.cell1896, Batch0237.tau1896, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2201303 (by positivity) using 1 <;> norm_num)
        · have hs220132 : InSquare (-51/160) (39/160) (1/160) tau := by
            convert childUL hs22013 hx22013 hy22013 using 1 <;> norm_num
          rcases le_total tau.re (-51/160 : ℝ) with hx220132 | hx220132
          · rcases le_total tau.im (39/160 : ℝ) with hy220132 | hy220132
            · have hs2201320 : InSquare (-103/320) (77/320) (1/320) tau := by
                convert childLL hs220132 hx220132 hy220132 using 1 <;> norm_num
              exact Batch0237.cell1897.sound htau (by
                simp only [Batch0237.cell1897, Batch0237.tau1897, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2201320 (by positivity) using 1 <;> norm_num)
            · have hs2201322 : InSquare (-103/320) (79/320) (1/320) tau := by
                convert childUL hs220132 hx220132 hy220132 using 1 <;> norm_num
              exact (outside_2201322 htau hs2201322).elim
          · rcases le_total tau.im (39/160 : ℝ) with hy220132 | hy220132
            · have hs2201321 : InSquare (-101/320) (77/320) (1/320) tau := by
                convert childLR hs220132 hx220132 hy220132 using 1 <;> norm_num
              exact Batch0237.cell1898.sound htau (by
                simp only [Batch0237.cell1898, Batch0237.tau1898, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2201321 (by positivity) using 1 <;> norm_num)
            · have hs2201323 : InSquare (-101/320) (79/320) (1/320) tau := by
                convert childUR hs220132 hx220132 hy220132 using 1 <;> norm_num
              exact Batch0237.cell1899.sound htau (by
                simp only [Batch0237.cell1899, Batch0237.tau1899, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2201323 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (19/80 : ℝ) with hy22013 | hy22013
        · have hs220131 : InSquare (-49/160) (37/160) (1/160) tau := by
            convert childLR hs22013 hx22013 hy22013 using 1 <;> norm_num
          exact Batch0106.cell0854.sound htau (by
            simp only [Batch0106.cell0854, Batch0106.tau0854, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs220131 (by positivity) using 1 <;> norm_num)
        · have hs220133 : InSquare (-49/160) (39/160) (1/160) tau := by
            convert childUR hs22013 hx22013 hy22013 using 1 <;> norm_num
          rcases le_total tau.re (-49/160 : ℝ) with hx220133 | hx220133
          · rcases le_total tau.im (39/160 : ℝ) with hy220133 | hy220133
            · have hs2201330 : InSquare (-99/320) (77/320) (1/320) tau := by
                convert childLL hs220133 hx220133 hy220133 using 1 <;> norm_num
              exact Batch0237.cell1900.sound htau (by
                simp only [Batch0237.cell1900, Batch0237.tau1900, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2201330 (by positivity) using 1 <;> norm_num)
            · have hs2201332 : InSquare (-99/320) (79/320) (1/320) tau := by
                convert childUL hs220133 hx220133 hy220133 using 1 <;> norm_num
              exact Batch0237.cell1902.sound htau (by
                simp only [Batch0237.cell1902, Batch0237.tau1902, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2201332 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (39/160 : ℝ) with hy220133 | hy220133
            · have hs2201331 : InSquare (-97/320) (77/320) (1/320) tau := by
                convert childLR hs220133 hx220133 hy220133 using 1 <;> norm_num
              exact Batch0237.cell1901.sound htau (by
                simp only [Batch0237.cell1901, Batch0237.tau1901, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2201331 (by positivity) using 1 <;> norm_num)
            · have hs2201333 : InSquare (-97/320) (79/320) (1/320) tau := by
                convert childUR hs220133 hx220133 hy220133 using 1 <;> norm_num
              exact Batch0237.cell1903.sound htau (by
                simp only [Batch0237.cell1903, Batch0237.tau1903, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2201333 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2201
