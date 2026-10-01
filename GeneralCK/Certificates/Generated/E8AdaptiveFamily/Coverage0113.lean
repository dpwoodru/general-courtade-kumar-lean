import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0052
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0053
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0054

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0113

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-1/40) (-13/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (-1/40 : ℝ) with hx0113 | hx0113
  · rcases le_total tau.im (-13/40 : ℝ) with hy0113 | hy0113
    · have hs01130 : InSquare (-3/80) (-27/80) (1/80) tau := by
        convert childLL hs hx0113 hy0113 using 1 <;> norm_num
      rcases le_total tau.re (-3/80 : ℝ) with hx01130 | hx01130
      · rcases le_total tau.im (-27/80 : ℝ) with hy01130 | hy01130
        · have hs011300 : InSquare (-7/160) (-11/32) (1/160) tau := by
            convert childLL hs01130 hx01130 hy01130 using 1 <;> norm_num
          exact Batch0052.cell0417.sound htau (by
            simp only [Batch0052.cell0417, Batch0052.tau0417, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs011300 (by positivity) using 1 <;> norm_num)
        · have hs011302 : InSquare (-7/160) (-53/160) (1/160) tau := by
            convert childUL hs01130 hx01130 hy01130 using 1 <;> norm_num
          exact Batch0052.cell0419.sound htau (by
            simp only [Batch0052.cell0419, Batch0052.tau0419, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs011302 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-27/80 : ℝ) with hy01130 | hy01130
        · have hs011301 : InSquare (-1/32) (-11/32) (1/160) tau := by
            convert childLR hs01130 hx01130 hy01130 using 1 <;> norm_num
          exact Batch0052.cell0418.sound htau (by
            simp only [Batch0052.cell0418, Batch0052.tau0418, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs011301 (by positivity) using 1 <;> norm_num)
        · have hs011303 : InSquare (-1/32) (-53/160) (1/160) tau := by
            convert childUR hs01130 hx01130 hy01130 using 1 <;> norm_num
          exact Batch0052.cell0420.sound htau (by
            simp only [Batch0052.cell0420, Batch0052.tau0420, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs011303 (by positivity) using 1 <;> norm_num)
    · have hs01132 : InSquare (-3/80) (-5/16) (1/80) tau := by
        convert childUL hs hx0113 hy0113 using 1 <;> norm_num
      rcases le_total tau.re (-3/80 : ℝ) with hx01132 | hx01132
      · rcases le_total tau.im (-5/16 : ℝ) with hy01132 | hy01132
        · have hs011320 : InSquare (-7/160) (-51/160) (1/160) tau := by
            convert childLL hs01132 hx01132 hy01132 using 1 <;> norm_num
          exact Batch0053.cell0425.sound htau (by
            simp only [Batch0053.cell0425, Batch0053.tau0425, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs011320 (by positivity) using 1 <;> norm_num)
        · have hs011322 : InSquare (-7/160) (-49/160) (1/160) tau := by
            convert childUL hs01132 hx01132 hy01132 using 1 <;> norm_num
          exact Batch0053.cell0427.sound htau (by
            simp only [Batch0053.cell0427, Batch0053.tau0427, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs011322 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-5/16 : ℝ) with hy01132 | hy01132
        · have hs011321 : InSquare (-1/32) (-51/160) (1/160) tau := by
            convert childLR hs01132 hx01132 hy01132 using 1 <;> norm_num
          exact Batch0053.cell0426.sound htau (by
            simp only [Batch0053.cell0426, Batch0053.tau0426, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs011321 (by positivity) using 1 <;> norm_num)
        · have hs011323 : InSquare (-1/32) (-49/160) (1/160) tau := by
            convert childUR hs01132 hx01132 hy01132 using 1 <;> norm_num
          exact Batch0053.cell0428.sound htau (by
            simp only [Batch0053.cell0428, Batch0053.tau0428, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs011323 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (-13/40 : ℝ) with hy0113 | hy0113
    · have hs01131 : InSquare (-1/80) (-27/80) (1/80) tau := by
        convert childLR hs hx0113 hy0113 using 1 <;> norm_num
      rcases le_total tau.re (-1/80 : ℝ) with hx01131 | hx01131
      · rcases le_total tau.im (-27/80 : ℝ) with hy01131 | hy01131
        · have hs011310 : InSquare (-3/160) (-11/32) (1/160) tau := by
            convert childLL hs01131 hx01131 hy01131 using 1 <;> norm_num
          exact Batch0052.cell0421.sound htau (by
            simp only [Batch0052.cell0421, Batch0052.tau0421, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs011310 (by positivity) using 1 <;> norm_num)
        · have hs011312 : InSquare (-3/160) (-53/160) (1/160) tau := by
            convert childUL hs01131 hx01131 hy01131 using 1 <;> norm_num
          exact Batch0052.cell0423.sound htau (by
            simp only [Batch0052.cell0423, Batch0052.tau0423, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs011312 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-27/80 : ℝ) with hy01131 | hy01131
        · have hs011311 : InSquare (-1/160) (-11/32) (1/160) tau := by
            convert childLR hs01131 hx01131 hy01131 using 1 <;> norm_num
          exact Batch0052.cell0422.sound htau (by
            simp only [Batch0052.cell0422, Batch0052.tau0422, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs011311 (by positivity) using 1 <;> norm_num)
        · have hs011313 : InSquare (-1/160) (-53/160) (1/160) tau := by
            convert childUR hs01131 hx01131 hy01131 using 1 <;> norm_num
          exact Batch0053.cell0424.sound htau (by
            simp only [Batch0053.cell0424, Batch0053.tau0424, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs011313 (by positivity) using 1 <;> norm_num)
    · have hs01133 : InSquare (-1/80) (-5/16) (1/80) tau := by
        convert childUR hs hx0113 hy0113 using 1 <;> norm_num
      rcases le_total tau.re (-1/80 : ℝ) with hx01133 | hx01133
      · rcases le_total tau.im (-5/16 : ℝ) with hy01133 | hy01133
        · have hs011330 : InSquare (-3/160) (-51/160) (1/160) tau := by
            convert childLL hs01133 hx01133 hy01133 using 1 <;> norm_num
          exact Batch0053.cell0429.sound htau (by
            simp only [Batch0053.cell0429, Batch0053.tau0429, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs011330 (by positivity) using 1 <;> norm_num)
        · have hs011332 : InSquare (-3/160) (-49/160) (1/160) tau := by
            convert childUL hs01133 hx01133 hy01133 using 1 <;> norm_num
          exact Batch0053.cell0431.sound htau (by
            simp only [Batch0053.cell0431, Batch0053.tau0431, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs011332 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-5/16 : ℝ) with hy01133 | hy01133
        · have hs011331 : InSquare (-1/160) (-51/160) (1/160) tau := by
            convert childLR hs01133 hx01133 hy01133 using 1 <;> norm_num
          exact Batch0053.cell0430.sound htau (by
            simp only [Batch0053.cell0430, Batch0053.tau0430, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs011331 (by positivity) using 1 <;> norm_num)
        · have hs011333 : InSquare (-1/160) (-49/160) (1/160) tau := by
            convert childUR hs01133 hx01133 hy01133 using 1 <;> norm_num
          exact Batch0054.cell0432.sound htau (by
            simp only [Batch0054.cell0432, Batch0054.tau0432, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs011333 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0113
