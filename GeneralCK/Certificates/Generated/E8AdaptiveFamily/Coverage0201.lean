import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0060
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0061
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0062

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0201

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-13/40) (-7/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (-13/40 : ℝ) with hx0201 | hx0201
  · rcases le_total tau.im (-7/40 : ℝ) with hy0201 | hy0201
    · have hs02010 : InSquare (-27/80) (-3/16) (1/80) tau := by
        convert childLL hs hx0201 hy0201 using 1 <;> norm_num
      rcases le_total tau.re (-27/80 : ℝ) with hx02010 | hx02010
      · rcases le_total tau.im (-3/16 : ℝ) with hy02010 | hy02010
        · have hs020100 : InSquare (-11/32) (-31/160) (1/160) tau := by
            convert childLL hs02010 hx02010 hy02010 using 1 <;> norm_num
          exact Batch0060.cell0486.sound htau (by
            simp only [Batch0060.cell0486, Batch0060.tau0486, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs020100 (by positivity) using 1 <;> norm_num)
        · have hs020102 : InSquare (-11/32) (-29/160) (1/160) tau := by
            convert childUL hs02010 hx02010 hy02010 using 1 <;> norm_num
          exact Batch0061.cell0488.sound htau (by
            simp only [Batch0061.cell0488, Batch0061.tau0488, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs020102 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-3/16 : ℝ) with hy02010 | hy02010
        · have hs020101 : InSquare (-53/160) (-31/160) (1/160) tau := by
            convert childLR hs02010 hx02010 hy02010 using 1 <;> norm_num
          exact Batch0060.cell0487.sound htau (by
            simp only [Batch0060.cell0487, Batch0060.tau0487, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs020101 (by positivity) using 1 <;> norm_num)
        · have hs020103 : InSquare (-53/160) (-29/160) (1/160) tau := by
            convert childUR hs02010 hx02010 hy02010 using 1 <;> norm_num
          exact Batch0061.cell0489.sound htau (by
            simp only [Batch0061.cell0489, Batch0061.tau0489, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs020103 (by positivity) using 1 <;> norm_num)
    · have hs02012 : InSquare (-27/80) (-13/80) (1/80) tau := by
        convert childUL hs hx0201 hy0201 using 1 <;> norm_num
      rcases le_total tau.re (-27/80 : ℝ) with hx02012 | hx02012
      · rcases le_total tau.im (-13/80 : ℝ) with hy02012 | hy02012
        · have hs020120 : InSquare (-11/32) (-27/160) (1/160) tau := by
            convert childLL hs02012 hx02012 hy02012 using 1 <;> norm_num
          exact Batch0061.cell0494.sound htau (by
            simp only [Batch0061.cell0494, Batch0061.tau0494, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs020120 (by positivity) using 1 <;> norm_num)
        · have hs020122 : InSquare (-11/32) (-5/32) (1/160) tau := by
            convert childUL hs02012 hx02012 hy02012 using 1 <;> norm_num
          exact Batch0062.cell0496.sound htau (by
            simp only [Batch0062.cell0496, Batch0062.tau0496, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs020122 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-13/80 : ℝ) with hy02012 | hy02012
        · have hs020121 : InSquare (-53/160) (-27/160) (1/160) tau := by
            convert childLR hs02012 hx02012 hy02012 using 1 <;> norm_num
          exact Batch0061.cell0495.sound htau (by
            simp only [Batch0061.cell0495, Batch0061.tau0495, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs020121 (by positivity) using 1 <;> norm_num)
        · have hs020123 : InSquare (-53/160) (-5/32) (1/160) tau := by
            convert childUR hs02012 hx02012 hy02012 using 1 <;> norm_num
          exact Batch0062.cell0497.sound htau (by
            simp only [Batch0062.cell0497, Batch0062.tau0497, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs020123 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (-7/40 : ℝ) with hy0201 | hy0201
    · have hs02011 : InSquare (-5/16) (-3/16) (1/80) tau := by
        convert childLR hs hx0201 hy0201 using 1 <;> norm_num
      rcases le_total tau.re (-5/16 : ℝ) with hx02011 | hx02011
      · rcases le_total tau.im (-3/16 : ℝ) with hy02011 | hy02011
        · have hs020110 : InSquare (-51/160) (-31/160) (1/160) tau := by
            convert childLL hs02011 hx02011 hy02011 using 1 <;> norm_num
          exact Batch0061.cell0490.sound htau (by
            simp only [Batch0061.cell0490, Batch0061.tau0490, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs020110 (by positivity) using 1 <;> norm_num)
        · have hs020112 : InSquare (-51/160) (-29/160) (1/160) tau := by
            convert childUL hs02011 hx02011 hy02011 using 1 <;> norm_num
          exact Batch0061.cell0492.sound htau (by
            simp only [Batch0061.cell0492, Batch0061.tau0492, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs020112 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-3/16 : ℝ) with hy02011 | hy02011
        · have hs020111 : InSquare (-49/160) (-31/160) (1/160) tau := by
            convert childLR hs02011 hx02011 hy02011 using 1 <;> norm_num
          exact Batch0061.cell0491.sound htau (by
            simp only [Batch0061.cell0491, Batch0061.tau0491, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs020111 (by positivity) using 1 <;> norm_num)
        · have hs020113 : InSquare (-49/160) (-29/160) (1/160) tau := by
            convert childUR hs02011 hx02011 hy02011 using 1 <;> norm_num
          exact Batch0061.cell0493.sound htau (by
            simp only [Batch0061.cell0493, Batch0061.tau0493, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs020113 (by positivity) using 1 <;> norm_num)
    · have hs02013 : InSquare (-5/16) (-13/80) (1/80) tau := by
        convert childUR hs hx0201 hy0201 using 1 <;> norm_num
      rcases le_total tau.re (-5/16 : ℝ) with hx02013 | hx02013
      · rcases le_total tau.im (-13/80 : ℝ) with hy02013 | hy02013
        · have hs020130 : InSquare (-51/160) (-27/160) (1/160) tau := by
            convert childLL hs02013 hx02013 hy02013 using 1 <;> norm_num
          exact Batch0062.cell0498.sound htau (by
            simp only [Batch0062.cell0498, Batch0062.tau0498, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs020130 (by positivity) using 1 <;> norm_num)
        · have hs020132 : InSquare (-51/160) (-5/32) (1/160) tau := by
            convert childUL hs02013 hx02013 hy02013 using 1 <;> norm_num
          exact Batch0062.cell0500.sound htau (by
            simp only [Batch0062.cell0500, Batch0062.tau0500, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs020132 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-13/80 : ℝ) with hy02013 | hy02013
        · have hs020131 : InSquare (-49/160) (-27/160) (1/160) tau := by
            convert childLR hs02013 hx02013 hy02013 using 1 <;> norm_num
          exact Batch0062.cell0499.sound htau (by
            simp only [Batch0062.cell0499, Batch0062.tau0499, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs020131 (by positivity) using 1 <;> norm_num)
        · have hs020133 : InSquare (-49/160) (-5/32) (1/160) tau := by
            convert childUR hs02013 hx02013 hy02013 using 1 <;> norm_num
          exact Batch0062.cell0501.sound htau (by
            simp only [Batch0062.cell0501, Batch0062.tau0501, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs020133 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0201
