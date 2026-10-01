import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0248
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0249
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0250
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0251
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0252
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0253
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0400
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0401
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0402

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2231

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

private theorem outside_223120 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-39/160) (53/160) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (19/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+19/80)]
  have himSq : (13/40 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-13/40)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_223122 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-39/160) (11/32) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (19/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+19/80)]
  have himSq : (27/80 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-27/80)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_223123 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-37/160) (11/32) (1/160) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (9/40 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+9/40)]
  have himSq : (27/80 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-27/80)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_2231022 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-79/320) (103/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (39/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+39/160)]
  have himSq : (51/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-51/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_2231212 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-15/64) (107/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (37/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+37/160)]
  have himSq : (53/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-53/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_2231213 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-73/320) (107/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (9/40 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+9/40)]
  have himSq : (53/160 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-53/160)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_2231320 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-71/320) (109/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (7/32 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+7/32)]
  have himSq : (27/80 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-27/80)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_2231322 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-71/320) (111/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (7/32 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+7/32)]
  have himSq : (11/32 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-11/32)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_2231323 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-69/320) (111/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (17/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+17/80)]
  have himSq : (11/32 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-11/32)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_2231332 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-67/320) (111/320) (1/320) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (33/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+33/160)]
  have himSq : (11/32 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-11/32)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_22312100 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-151/640) (209/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (15/64 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+15/64)]
  have himSq : (13/40 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-13/40)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_22312102 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-151/640) (211/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (15/64 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+15/64)]
  have himSq : (21/64 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-21/64)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_22312103 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-149/640) (211/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (37/160 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+37/160)]
  have himSq : (21/64 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-21/64)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_22313022 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-143/640) (43/128) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (71/320 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+71/320)]
  have himSq : (107/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-107/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_22313210 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-139/640) (217/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (69/320 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+69/320)]
  have himSq : (27/80 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-27/80)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_22313212 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-139/640) (219/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (69/320 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+69/320)]
  have himSq : (109/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-109/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_22313213 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-137/640) (219/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (17/80 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+17/80)]
  have himSq : (109/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-109/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_22313332 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-131/640) (223/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (13/64 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+13/64)]
  have himSq : (111/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-111/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

private theorem outside_22313333 {tau : ℂ}
    (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-129/640) (223/640) (1/640) tau) : False := by
  rcases hs with ⟨hxl, hxu, hyl, hyu⟩
  have hreSq : (1/5 : ℝ)^2 ≤ tau.re^2 := by nlinarith [sq_nonneg (tau.re+1/5)]
  have himSq : (111/320 : ℝ)^2 ≤ tau.im^2 := by nlinarith [sq_nonneg (tau.im-111/320)]
  have hn : ‖tau‖^2 ≤ (2/5 : ℝ)^2 := by nlinarith [norm_nonneg tau]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  norm_num at hn hreSq himSq
  nlinarith

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-9/40) (13/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (-9/40 : ℝ) with hx2231 | hx2231
  · rcases le_total tau.im (13/40 : ℝ) with hy2231 | hy2231
    · have hs22310 : InSquare (-19/80) (5/16) (1/80) tau := by
        convert childLL hs hx2231 hy2231 using 1 <;> norm_num
      rcases le_total tau.re (-19/80 : ℝ) with hx22310 | hx22310
      · rcases le_total tau.im (5/16 : ℝ) with hy22310 | hy22310
        · have hs223100 : InSquare (-39/160) (49/160) (1/160) tau := by
            convert childLL hs22310 hx22310 hy22310 using 1 <;> norm_num
          rcases le_total tau.re (-39/160 : ℝ) with hx223100 | hx223100
          · rcases le_total tau.im (49/160 : ℝ) with hy223100 | hy223100
            · have hs2231000 : InSquare (-79/320) (97/320) (1/320) tau := by
                convert childLL hs223100 hx223100 hy223100 using 1 <;> norm_num
              exact Batch0248.cell1988.sound htau (by
                simp only [Batch0248.cell1988, Batch0248.tau1988, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2231000 (by positivity) using 1 <;> norm_num)
            · have hs2231002 : InSquare (-79/320) (99/320) (1/320) tau := by
                convert childUL hs223100 hx223100 hy223100 using 1 <;> norm_num
              exact Batch0248.cell1990.sound htau (by
                simp only [Batch0248.cell1990, Batch0248.tau1990, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2231002 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (49/160 : ℝ) with hy223100 | hy223100
            · have hs2231001 : InSquare (-77/320) (97/320) (1/320) tau := by
                convert childLR hs223100 hx223100 hy223100 using 1 <;> norm_num
              exact Batch0248.cell1989.sound htau (by
                simp only [Batch0248.cell1989, Batch0248.tau1989, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2231001 (by positivity) using 1 <;> norm_num)
            · have hs2231003 : InSquare (-77/320) (99/320) (1/320) tau := by
                convert childUR hs223100 hx223100 hy223100 using 1 <;> norm_num
              exact Batch0248.cell1991.sound htau (by
                simp only [Batch0248.cell1991, Batch0248.tau1991, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2231003 (by positivity) using 1 <;> norm_num)
        · have hs223102 : InSquare (-39/160) (51/160) (1/160) tau := by
            convert childUL hs22310 hx22310 hy22310 using 1 <;> norm_num
          rcases le_total tau.re (-39/160 : ℝ) with hx223102 | hx223102
          · rcases le_total tau.im (51/160 : ℝ) with hy223102 | hy223102
            · have hs2231020 : InSquare (-79/320) (101/320) (1/320) tau := by
                convert childLL hs223102 hx223102 hy223102 using 1 <;> norm_num
              exact Batch0249.cell1996.sound htau (by
                simp only [Batch0249.cell1996, Batch0249.tau1996, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2231020 (by positivity) using 1 <;> norm_num)
            · have hs2231022 : InSquare (-79/320) (103/320) (1/320) tau := by
                convert childUL hs223102 hx223102 hy223102 using 1 <;> norm_num
              exact (outside_2231022 htau hs2231022).elim
          · rcases le_total tau.im (51/160 : ℝ) with hy223102 | hy223102
            · have hs2231021 : InSquare (-77/320) (101/320) (1/320) tau := by
                convert childLR hs223102 hx223102 hy223102 using 1 <;> norm_num
              exact Batch0249.cell1997.sound htau (by
                simp only [Batch0249.cell1997, Batch0249.tau1997, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2231021 (by positivity) using 1 <;> norm_num)
            · have hs2231023 : InSquare (-77/320) (103/320) (1/320) tau := by
                convert childUR hs223102 hx223102 hy223102 using 1 <;> norm_num
              exact Batch0249.cell1998.sound htau (by
                simp only [Batch0249.cell1998, Batch0249.tau1998, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2231023 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (5/16 : ℝ) with hy22310 | hy22310
        · have hs223101 : InSquare (-37/160) (49/160) (1/160) tau := by
            convert childLR hs22310 hx22310 hy22310 using 1 <;> norm_num
          rcases le_total tau.re (-37/160 : ℝ) with hx223101 | hx223101
          · rcases le_total tau.im (49/160 : ℝ) with hy223101 | hy223101
            · have hs2231010 : InSquare (-15/64) (97/320) (1/320) tau := by
                convert childLL hs223101 hx223101 hy223101 using 1 <;> norm_num
              exact Batch0249.cell1992.sound htau (by
                simp only [Batch0249.cell1992, Batch0249.tau1992, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2231010 (by positivity) using 1 <;> norm_num)
            · have hs2231012 : InSquare (-15/64) (99/320) (1/320) tau := by
                convert childUL hs223101 hx223101 hy223101 using 1 <;> norm_num
              exact Batch0249.cell1994.sound htau (by
                simp only [Batch0249.cell1994, Batch0249.tau1994, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2231012 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (49/160 : ℝ) with hy223101 | hy223101
            · have hs2231011 : InSquare (-73/320) (97/320) (1/320) tau := by
                convert childLR hs223101 hx223101 hy223101 using 1 <;> norm_num
              exact Batch0249.cell1993.sound htau (by
                simp only [Batch0249.cell1993, Batch0249.tau1993, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2231011 (by positivity) using 1 <;> norm_num)
            · have hs2231013 : InSquare (-73/320) (99/320) (1/320) tau := by
                convert childUR hs223101 hx223101 hy223101 using 1 <;> norm_num
              exact Batch0249.cell1995.sound htau (by
                simp only [Batch0249.cell1995, Batch0249.tau1995, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2231013 (by positivity) using 1 <;> norm_num)
        · have hs223103 : InSquare (-37/160) (51/160) (1/160) tau := by
            convert childUR hs22310 hx22310 hy22310 using 1 <;> norm_num
          rcases le_total tau.re (-37/160 : ℝ) with hx223103 | hx223103
          · rcases le_total tau.im (51/160 : ℝ) with hy223103 | hy223103
            · have hs2231030 : InSquare (-15/64) (101/320) (1/320) tau := by
                convert childLL hs223103 hx223103 hy223103 using 1 <;> norm_num
              exact Batch0249.cell1999.sound htau (by
                simp only [Batch0249.cell1999, Batch0249.tau1999, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2231030 (by positivity) using 1 <;> norm_num)
            · have hs2231032 : InSquare (-15/64) (103/320) (1/320) tau := by
                convert childUL hs223103 hx223103 hy223103 using 1 <;> norm_num
              exact Batch0250.cell2001.sound htau (by
                simp only [Batch0250.cell2001, Batch0250.tau2001, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2231032 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (51/160 : ℝ) with hy223103 | hy223103
            · have hs2231031 : InSquare (-73/320) (101/320) (1/320) tau := by
                convert childLR hs223103 hx223103 hy223103 using 1 <;> norm_num
              exact Batch0250.cell2000.sound htau (by
                simp only [Batch0250.cell2000, Batch0250.tau2000, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2231031 (by positivity) using 1 <;> norm_num)
            · have hs2231033 : InSquare (-73/320) (103/320) (1/320) tau := by
                convert childUR hs223103 hx223103 hy223103 using 1 <;> norm_num
              exact Batch0250.cell2002.sound htau (by
                simp only [Batch0250.cell2002, Batch0250.tau2002, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2231033 (by positivity) using 1 <;> norm_num)
    · have hs22312 : InSquare (-19/80) (27/80) (1/80) tau := by
        convert childUL hs hx2231 hy2231 using 1 <;> norm_num
      rcases le_total tau.re (-19/80 : ℝ) with hx22312 | hx22312
      · rcases le_total tau.im (27/80 : ℝ) with hy22312 | hy22312
        · have hs223120 : InSquare (-39/160) (53/160) (1/160) tau := by
            convert childLL hs22312 hx22312 hy22312 using 1 <;> norm_num
          exact (outside_223120 htau hs223120).elim
        · have hs223122 : InSquare (-39/160) (11/32) (1/160) tau := by
            convert childUL hs22312 hx22312 hy22312 using 1 <;> norm_num
          exact (outside_223122 htau hs223122).elim
      · rcases le_total tau.im (27/80 : ℝ) with hy22312 | hy22312
        · have hs223121 : InSquare (-37/160) (53/160) (1/160) tau := by
            convert childLR hs22312 hx22312 hy22312 using 1 <;> norm_num
          rcases le_total tau.re (-37/160 : ℝ) with hx223121 | hx223121
          · rcases le_total tau.im (53/160 : ℝ) with hy223121 | hy223121
            · have hs2231210 : InSquare (-15/64) (21/64) (1/320) tau := by
                convert childLL hs223121 hx223121 hy223121 using 1 <;> norm_num
              rcases le_total tau.re (-15/64 : ℝ) with hx2231210 | hx2231210
              · rcases le_total tau.im (21/64 : ℝ) with hy2231210 | hy2231210
                · have hs22312100 : InSquare (-151/640) (209/640) (1/640) tau := by
                    convert childLL hs2231210 hx2231210 hy2231210 using 1 <;> norm_num
                  exact (outside_22312100 htau hs22312100).elim
                · have hs22312102 : InSquare (-151/640) (211/640) (1/640) tau := by
                    convert childUL hs2231210 hx2231210 hy2231210 using 1 <;> norm_num
                  exact (outside_22312102 htau hs22312102).elim
              · rcases le_total tau.im (21/64 : ℝ) with hy2231210 | hy2231210
                · have hs22312101 : InSquare (-149/640) (209/640) (1/640) tau := by
                    convert childLR hs2231210 hx2231210 hy2231210 using 1 <;> norm_num
                  exact Batch0400.cell3204.sound htau (by
                    simp only [Batch0400.cell3204, Batch0400.tau3204, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs22312101 (by positivity) using 1 <;> norm_num)
                · have hs22312103 : InSquare (-149/640) (211/640) (1/640) tau := by
                    convert childUR hs2231210 hx2231210 hy2231210 using 1 <;> norm_num
                  exact (outside_22312103 htau hs22312103).elim
            · have hs2231212 : InSquare (-15/64) (107/320) (1/320) tau := by
                convert childUL hs223121 hx223121 hy223121 using 1 <;> norm_num
              exact (outside_2231212 htau hs2231212).elim
          · rcases le_total tau.im (53/160 : ℝ) with hy223121 | hy223121
            · have hs2231211 : InSquare (-73/320) (21/64) (1/320) tau := by
                convert childLR hs223121 hx223121 hy223121 using 1 <;> norm_num
              exact Batch0252.cell2019.sound htau (by
                simp only [Batch0252.cell2019, Batch0252.tau2019, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2231211 (by positivity) using 1 <;> norm_num)
            · have hs2231213 : InSquare (-73/320) (107/320) (1/320) tau := by
                convert childUR hs223121 hx223121 hy223121 using 1 <;> norm_num
              exact (outside_2231213 htau hs2231213).elim
        · have hs223123 : InSquare (-37/160) (11/32) (1/160) tau := by
            convert childUR hs22312 hx22312 hy22312 using 1 <;> norm_num
          exact (outside_223123 htau hs223123).elim
  · rcases le_total tau.im (13/40 : ℝ) with hy2231 | hy2231
    · have hs22311 : InSquare (-17/80) (5/16) (1/80) tau := by
        convert childLR hs hx2231 hy2231 using 1 <;> norm_num
      rcases le_total tau.re (-17/80 : ℝ) with hx22311 | hx22311
      · rcases le_total tau.im (5/16 : ℝ) with hy22311 | hy22311
        · have hs223110 : InSquare (-7/32) (49/160) (1/160) tau := by
            convert childLL hs22311 hx22311 hy22311 using 1 <;> norm_num
          rcases le_total tau.re (-7/32 : ℝ) with hx223110 | hx223110
          · rcases le_total tau.im (49/160 : ℝ) with hy223110 | hy223110
            · have hs2231100 : InSquare (-71/320) (97/320) (1/320) tau := by
                convert childLL hs223110 hx223110 hy223110 using 1 <;> norm_num
              exact Batch0250.cell2003.sound htau (by
                simp only [Batch0250.cell2003, Batch0250.tau2003, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2231100 (by positivity) using 1 <;> norm_num)
            · have hs2231102 : InSquare (-71/320) (99/320) (1/320) tau := by
                convert childUL hs223110 hx223110 hy223110 using 1 <;> norm_num
              exact Batch0250.cell2005.sound htau (by
                simp only [Batch0250.cell2005, Batch0250.tau2005, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2231102 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (49/160 : ℝ) with hy223110 | hy223110
            · have hs2231101 : InSquare (-69/320) (97/320) (1/320) tau := by
                convert childLR hs223110 hx223110 hy223110 using 1 <;> norm_num
              exact Batch0250.cell2004.sound htau (by
                simp only [Batch0250.cell2004, Batch0250.tau2004, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2231101 (by positivity) using 1 <;> norm_num)
            · have hs2231103 : InSquare (-69/320) (99/320) (1/320) tau := by
                convert childUR hs223110 hx223110 hy223110 using 1 <;> norm_num
              exact Batch0250.cell2006.sound htau (by
                simp only [Batch0250.cell2006, Batch0250.tau2006, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2231103 (by positivity) using 1 <;> norm_num)
        · have hs223112 : InSquare (-7/32) (51/160) (1/160) tau := by
            convert childUL hs22311 hx22311 hy22311 using 1 <;> norm_num
          rcases le_total tau.re (-7/32 : ℝ) with hx223112 | hx223112
          · rcases le_total tau.im (51/160 : ℝ) with hy223112 | hy223112
            · have hs2231120 : InSquare (-71/320) (101/320) (1/320) tau := by
                convert childLL hs223112 hx223112 hy223112 using 1 <;> norm_num
              exact Batch0251.cell2011.sound htau (by
                simp only [Batch0251.cell2011, Batch0251.tau2011, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2231120 (by positivity) using 1 <;> norm_num)
            · have hs2231122 : InSquare (-71/320) (103/320) (1/320) tau := by
                convert childUL hs223112 hx223112 hy223112 using 1 <;> norm_num
              exact Batch0251.cell2013.sound htau (by
                simp only [Batch0251.cell2013, Batch0251.tau2013, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2231122 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (51/160 : ℝ) with hy223112 | hy223112
            · have hs2231121 : InSquare (-69/320) (101/320) (1/320) tau := by
                convert childLR hs223112 hx223112 hy223112 using 1 <;> norm_num
              exact Batch0251.cell2012.sound htau (by
                simp only [Batch0251.cell2012, Batch0251.tau2012, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2231121 (by positivity) using 1 <;> norm_num)
            · have hs2231123 : InSquare (-69/320) (103/320) (1/320) tau := by
                convert childUR hs223112 hx223112 hy223112 using 1 <;> norm_num
              exact Batch0251.cell2014.sound htau (by
                simp only [Batch0251.cell2014, Batch0251.tau2014, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2231123 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (5/16 : ℝ) with hy22311 | hy22311
        · have hs223111 : InSquare (-33/160) (49/160) (1/160) tau := by
            convert childLR hs22311 hx22311 hy22311 using 1 <;> norm_num
          rcases le_total tau.re (-33/160 : ℝ) with hx223111 | hx223111
          · rcases le_total tau.im (49/160 : ℝ) with hy223111 | hy223111
            · have hs2231110 : InSquare (-67/320) (97/320) (1/320) tau := by
                convert childLL hs223111 hx223111 hy223111 using 1 <;> norm_num
              exact Batch0250.cell2007.sound htau (by
                simp only [Batch0250.cell2007, Batch0250.tau2007, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2231110 (by positivity) using 1 <;> norm_num)
            · have hs2231112 : InSquare (-67/320) (99/320) (1/320) tau := by
                convert childUL hs223111 hx223111 hy223111 using 1 <;> norm_num
              exact Batch0251.cell2009.sound htau (by
                simp only [Batch0251.cell2009, Batch0251.tau2009, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2231112 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (49/160 : ℝ) with hy223111 | hy223111
            · have hs2231111 : InSquare (-13/64) (97/320) (1/320) tau := by
                convert childLR hs223111 hx223111 hy223111 using 1 <;> norm_num
              exact Batch0251.cell2008.sound htau (by
                simp only [Batch0251.cell2008, Batch0251.tau2008, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2231111 (by positivity) using 1 <;> norm_num)
            · have hs2231113 : InSquare (-13/64) (99/320) (1/320) tau := by
                convert childUR hs223111 hx223111 hy223111 using 1 <;> norm_num
              exact Batch0251.cell2010.sound htau (by
                simp only [Batch0251.cell2010, Batch0251.tau2010, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2231113 (by positivity) using 1 <;> norm_num)
        · have hs223113 : InSquare (-33/160) (51/160) (1/160) tau := by
            convert childUR hs22311 hx22311 hy22311 using 1 <;> norm_num
          rcases le_total tau.re (-33/160 : ℝ) with hx223113 | hx223113
          · rcases le_total tau.im (51/160 : ℝ) with hy223113 | hy223113
            · have hs2231130 : InSquare (-67/320) (101/320) (1/320) tau := by
                convert childLL hs223113 hx223113 hy223113 using 1 <;> norm_num
              exact Batch0251.cell2015.sound htau (by
                simp only [Batch0251.cell2015, Batch0251.tau2015, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2231130 (by positivity) using 1 <;> norm_num)
            · have hs2231132 : InSquare (-67/320) (103/320) (1/320) tau := by
                convert childUL hs223113 hx223113 hy223113 using 1 <;> norm_num
              exact Batch0252.cell2017.sound htau (by
                simp only [Batch0252.cell2017, Batch0252.tau2017, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2231132 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (51/160 : ℝ) with hy223113 | hy223113
            · have hs2231131 : InSquare (-13/64) (101/320) (1/320) tau := by
                convert childLR hs223113 hx223113 hy223113 using 1 <;> norm_num
              exact Batch0252.cell2016.sound htau (by
                simp only [Batch0252.cell2016, Batch0252.tau2016, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2231131 (by positivity) using 1 <;> norm_num)
            · have hs2231133 : InSquare (-13/64) (103/320) (1/320) tau := by
                convert childUR hs223113 hx223113 hy223113 using 1 <;> norm_num
              exact Batch0252.cell2018.sound htau (by
                simp only [Batch0252.cell2018, Batch0252.tau2018, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2231133 (by positivity) using 1 <;> norm_num)
    · have hs22313 : InSquare (-17/80) (27/80) (1/80) tau := by
        convert childUR hs hx2231 hy2231 using 1 <;> norm_num
      rcases le_total tau.re (-17/80 : ℝ) with hx22313 | hx22313
      · rcases le_total tau.im (27/80 : ℝ) with hy22313 | hy22313
        · have hs223130 : InSquare (-7/32) (53/160) (1/160) tau := by
            convert childLL hs22313 hx22313 hy22313 using 1 <;> norm_num
          rcases le_total tau.re (-7/32 : ℝ) with hx223130 | hx223130
          · rcases le_total tau.im (53/160 : ℝ) with hy223130 | hy223130
            · have hs2231300 : InSquare (-71/320) (21/64) (1/320) tau := by
                convert childLL hs223130 hx223130 hy223130 using 1 <;> norm_num
              exact Batch0252.cell2020.sound htau (by
                simp only [Batch0252.cell2020, Batch0252.tau2020, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2231300 (by positivity) using 1 <;> norm_num)
            · have hs2231302 : InSquare (-71/320) (107/320) (1/320) tau := by
                convert childUL hs223130 hx223130 hy223130 using 1 <;> norm_num
              rcases le_total tau.re (-71/320 : ℝ) with hx2231302 | hx2231302
              · rcases le_total tau.im (107/320 : ℝ) with hy2231302 | hy2231302
                · have hs22313020 : InSquare (-143/640) (213/640) (1/640) tau := by
                    convert childLL hs2231302 hx2231302 hy2231302 using 1 <;> norm_num
                  exact Batch0400.cell3205.sound htau (by
                    simp only [Batch0400.cell3205, Batch0400.tau3205, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs22313020 (by positivity) using 1 <;> norm_num)
                · have hs22313022 : InSquare (-143/640) (43/128) (1/640) tau := by
                    convert childUL hs2231302 hx2231302 hy2231302 using 1 <;> norm_num
                  exact (outside_22313022 htau hs22313022).elim
              · rcases le_total tau.im (107/320 : ℝ) with hy2231302 | hy2231302
                · have hs22313021 : InSquare (-141/640) (213/640) (1/640) tau := by
                    convert childLR hs2231302 hx2231302 hy2231302 using 1 <;> norm_num
                  exact Batch0400.cell3206.sound htau (by
                    simp only [Batch0400.cell3206, Batch0400.tau3206, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs22313021 (by positivity) using 1 <;> norm_num)
                · have hs22313023 : InSquare (-141/640) (43/128) (1/640) tau := by
                    convert childUR hs2231302 hx2231302 hy2231302 using 1 <;> norm_num
                  exact Batch0400.cell3207.sound htau (by
                    simp only [Batch0400.cell3207, Batch0400.tau3207, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs22313023 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (53/160 : ℝ) with hy223130 | hy223130
            · have hs2231301 : InSquare (-69/320) (21/64) (1/320) tau := by
                convert childLR hs223130 hx223130 hy223130 using 1 <;> norm_num
              exact Batch0252.cell2021.sound htau (by
                simp only [Batch0252.cell2021, Batch0252.tau2021, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2231301 (by positivity) using 1 <;> norm_num)
            · have hs2231303 : InSquare (-69/320) (107/320) (1/320) tau := by
                convert childUR hs223130 hx223130 hy223130 using 1 <;> norm_num
              exact Batch0252.cell2022.sound htau (by
                simp only [Batch0252.cell2022, Batch0252.tau2022, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2231303 (by positivity) using 1 <;> norm_num)
        · have hs223132 : InSquare (-7/32) (11/32) (1/160) tau := by
            convert childUL hs22313 hx22313 hy22313 using 1 <;> norm_num
          rcases le_total tau.re (-7/32 : ℝ) with hx223132 | hx223132
          · rcases le_total tau.im (11/32 : ℝ) with hy223132 | hy223132
            · have hs2231320 : InSquare (-71/320) (109/320) (1/320) tau := by
                convert childLL hs223132 hx223132 hy223132 using 1 <;> norm_num
              exact (outside_2231320 htau hs2231320).elim
            · have hs2231322 : InSquare (-71/320) (111/320) (1/320) tau := by
                convert childUL hs223132 hx223132 hy223132 using 1 <;> norm_num
              exact (outside_2231322 htau hs2231322).elim
          · rcases le_total tau.im (11/32 : ℝ) with hy223132 | hy223132
            · have hs2231321 : InSquare (-69/320) (109/320) (1/320) tau := by
                convert childLR hs223132 hx223132 hy223132 using 1 <;> norm_num
              rcases le_total tau.re (-69/320 : ℝ) with hx2231321 | hx2231321
              · rcases le_total tau.im (109/320 : ℝ) with hy2231321 | hy2231321
                · have hs22313210 : InSquare (-139/640) (217/640) (1/640) tau := by
                    convert childLL hs2231321 hx2231321 hy2231321 using 1 <;> norm_num
                  exact (outside_22313210 htau hs22313210).elim
                · have hs22313212 : InSquare (-139/640) (219/640) (1/640) tau := by
                    convert childUL hs2231321 hx2231321 hy2231321 using 1 <;> norm_num
                  exact (outside_22313212 htau hs22313212).elim
              · rcases le_total tau.im (109/320 : ℝ) with hy2231321 | hy2231321
                · have hs22313211 : InSquare (-137/640) (217/640) (1/640) tau := by
                    convert childLR hs2231321 hx2231321 hy2231321 using 1 <;> norm_num
                  exact Batch0401.cell3208.sound htau (by
                    simp only [Batch0401.cell3208, Batch0401.tau3208, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs22313211 (by positivity) using 1 <;> norm_num)
                · have hs22313213 : InSquare (-137/640) (219/640) (1/640) tau := by
                    convert childUR hs2231321 hx2231321 hy2231321 using 1 <;> norm_num
                  exact (outside_22313213 htau hs22313213).elim
            · have hs2231323 : InSquare (-69/320) (111/320) (1/320) tau := by
                convert childUR hs223132 hx223132 hy223132 using 1 <;> norm_num
              exact (outside_2231323 htau hs2231323).elim
      · rcases le_total tau.im (27/80 : ℝ) with hy22313 | hy22313
        · have hs223131 : InSquare (-33/160) (53/160) (1/160) tau := by
            convert childLR hs22313 hx22313 hy22313 using 1 <;> norm_num
          rcases le_total tau.re (-33/160 : ℝ) with hx223131 | hx223131
          · rcases le_total tau.im (53/160 : ℝ) with hy223131 | hy223131
            · have hs2231310 : InSquare (-67/320) (21/64) (1/320) tau := by
                convert childLL hs223131 hx223131 hy223131 using 1 <;> norm_num
              exact Batch0252.cell2023.sound htau (by
                simp only [Batch0252.cell2023, Batch0252.tau2023, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2231310 (by positivity) using 1 <;> norm_num)
            · have hs2231312 : InSquare (-67/320) (107/320) (1/320) tau := by
                convert childUL hs223131 hx223131 hy223131 using 1 <;> norm_num
              exact Batch0253.cell2025.sound htau (by
                simp only [Batch0253.cell2025, Batch0253.tau2025, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2231312 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (53/160 : ℝ) with hy223131 | hy223131
            · have hs2231311 : InSquare (-13/64) (21/64) (1/320) tau := by
                convert childLR hs223131 hx223131 hy223131 using 1 <;> norm_num
              exact Batch0253.cell2024.sound htau (by
                simp only [Batch0253.cell2024, Batch0253.tau2024, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2231311 (by positivity) using 1 <;> norm_num)
            · have hs2231313 : InSquare (-13/64) (107/320) (1/320) tau := by
                convert childUR hs223131 hx223131 hy223131 using 1 <;> norm_num
              exact Batch0253.cell2026.sound htau (by
                simp only [Batch0253.cell2026, Batch0253.tau2026, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2231313 (by positivity) using 1 <;> norm_num)
        · have hs223133 : InSquare (-33/160) (11/32) (1/160) tau := by
            convert childUR hs22313 hx22313 hy22313 using 1 <;> norm_num
          rcases le_total tau.re (-33/160 : ℝ) with hx223133 | hx223133
          · rcases le_total tau.im (11/32 : ℝ) with hy223133 | hy223133
            · have hs2231330 : InSquare (-67/320) (109/320) (1/320) tau := by
                convert childLL hs223133 hx223133 hy223133 using 1 <;> norm_num
              rcases le_total tau.re (-67/320 : ℝ) with hx2231330 | hx2231330
              · rcases le_total tau.im (109/320 : ℝ) with hy2231330 | hy2231330
                · have hs22313300 : InSquare (-27/128) (217/640) (1/640) tau := by
                    convert childLL hs2231330 hx2231330 hy2231330 using 1 <;> norm_num
                  exact Batch0401.cell3209.sound htau (by
                    simp only [Batch0401.cell3209, Batch0401.tau3209, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs22313300 (by positivity) using 1 <;> norm_num)
                · have hs22313302 : InSquare (-27/128) (219/640) (1/640) tau := by
                    convert childUL hs2231330 hx2231330 hy2231330 using 1 <;> norm_num
                  exact Batch0401.cell3211.sound htau (by
                    simp only [Batch0401.cell3211, Batch0401.tau3211, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs22313302 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (109/320 : ℝ) with hy2231330 | hy2231330
                · have hs22313301 : InSquare (-133/640) (217/640) (1/640) tau := by
                    convert childLR hs2231330 hx2231330 hy2231330 using 1 <;> norm_num
                  exact Batch0401.cell3210.sound htau (by
                    simp only [Batch0401.cell3210, Batch0401.tau3210, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs22313301 (by positivity) using 1 <;> norm_num)
                · have hs22313303 : InSquare (-133/640) (219/640) (1/640) tau := by
                    convert childUR hs2231330 hx2231330 hy2231330 using 1 <;> norm_num
                  exact Batch0401.cell3212.sound htau (by
                    simp only [Batch0401.cell3212, Batch0401.tau3212, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs22313303 (by positivity) using 1 <;> norm_num)
            · have hs2231332 : InSquare (-67/320) (111/320) (1/320) tau := by
                convert childUL hs223133 hx223133 hy223133 using 1 <;> norm_num
              exact (outside_2231332 htau hs2231332).elim
          · rcases le_total tau.im (11/32 : ℝ) with hy223133 | hy223133
            · have hs2231331 : InSquare (-13/64) (109/320) (1/320) tau := by
                convert childLR hs223133 hx223133 hy223133 using 1 <;> norm_num
              rcases le_total tau.re (-13/64 : ℝ) with hx2231331 | hx2231331
              · rcases le_total tau.im (109/320 : ℝ) with hy2231331 | hy2231331
                · have hs22313310 : InSquare (-131/640) (217/640) (1/640) tau := by
                    convert childLL hs2231331 hx2231331 hy2231331 using 1 <;> norm_num
                  exact Batch0401.cell3213.sound htau (by
                    simp only [Batch0401.cell3213, Batch0401.tau3213, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs22313310 (by positivity) using 1 <;> norm_num)
                · have hs22313312 : InSquare (-131/640) (219/640) (1/640) tau := by
                    convert childUL hs2231331 hx2231331 hy2231331 using 1 <;> norm_num
                  exact Batch0401.cell3215.sound htau (by
                    simp only [Batch0401.cell3215, Batch0401.tau3215, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs22313312 (by positivity) using 1 <;> norm_num)
              · rcases le_total tau.im (109/320 : ℝ) with hy2231331 | hy2231331
                · have hs22313311 : InSquare (-129/640) (217/640) (1/640) tau := by
                    convert childLR hs2231331 hx2231331 hy2231331 using 1 <;> norm_num
                  exact Batch0401.cell3214.sound htau (by
                    simp only [Batch0401.cell3214, Batch0401.tau3214, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs22313311 (by positivity) using 1 <;> norm_num)
                · have hs22313313 : InSquare (-129/640) (219/640) (1/640) tau := by
                    convert childUR hs2231331 hx2231331 hy2231331 using 1 <;> norm_num
                  exact Batch0402.cell3216.sound htau (by
                    simp only [Batch0402.cell3216, Batch0402.tau3216, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs22313313 (by positivity) using 1 <;> norm_num)
            · have hs2231333 : InSquare (-13/64) (111/320) (1/320) tau := by
                convert childUR hs223133 hx223133 hy223133 using 1 <;> norm_num
              rcases le_total tau.re (-13/64 : ℝ) with hx2231333 | hx2231333
              · rcases le_total tau.im (111/320 : ℝ) with hy2231333 | hy2231333
                · have hs22313330 : InSquare (-131/640) (221/640) (1/640) tau := by
                    convert childLL hs2231333 hx2231333 hy2231333 using 1 <;> norm_num
                  exact Batch0402.cell3217.sound htau (by
                    simp only [Batch0402.cell3217, Batch0402.tau3217, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs22313330 (by positivity) using 1 <;> norm_num)
                · have hs22313332 : InSquare (-131/640) (223/640) (1/640) tau := by
                    convert childUL hs2231333 hx2231333 hy2231333 using 1 <;> norm_num
                  exact (outside_22313332 htau hs22313332).elim
              · rcases le_total tau.im (111/320 : ℝ) with hy2231333 | hy2231333
                · have hs22313331 : InSquare (-129/640) (221/640) (1/640) tau := by
                    convert childLR hs2231333 hx2231333 hy2231333 using 1 <;> norm_num
                  exact Batch0402.cell3218.sound htau (by
                    simp only [Batch0402.cell3218, Batch0402.tau3218, RatBall.Holds, GaussianRat.val]
                    convert inBall_of_inSquare hs22313331 (by positivity) using 1 <;> norm_num)
                · have hs22313333 : InSquare (-129/640) (223/640) (1/640) tau := by
                    convert childUR hs2231333 hx2231333 hy2231333 using 1 <;> norm_num
                  exact (outside_22313333 htau hs22313333).elim

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2231
