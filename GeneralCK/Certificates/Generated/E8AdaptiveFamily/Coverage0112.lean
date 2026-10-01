import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0050
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0051
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0052
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0191
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0192

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0112

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-3/40) (-13/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (-3/40 : ℝ) with hx0112 | hx0112
  · rcases le_total tau.im (-13/40 : ℝ) with hy0112 | hy0112
    · have hs01120 : InSquare (-7/80) (-27/80) (1/80) tau := by
        convert childLL hs hx0112 hy0112 using 1 <;> norm_num
      rcases le_total tau.re (-7/80 : ℝ) with hx01120 | hx01120
      · rcases le_total tau.im (-27/80 : ℝ) with hy01120 | hy01120
        · have hs011200 : InSquare (-3/32) (-11/32) (1/160) tau := by
            convert childLL hs01120 hx01120 hy01120 using 1 <;> norm_num
          rcases le_total tau.re (-3/32 : ℝ) with hx011200 | hx011200
          · rcases le_total tau.im (-11/32 : ℝ) with hy011200 | hy011200
            · have hs0112000 : InSquare (-31/320) (-111/320) (1/320) tau := by
                convert childLL hs011200 hx011200 hy011200 using 1 <;> norm_num
              exact Batch0191.cell1528.sound htau (by
                simp only [Batch0191.cell1528, Batch0191.tau1528, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0112000 (by positivity) using 1 <;> norm_num)
            · have hs0112002 : InSquare (-31/320) (-109/320) (1/320) tau := by
                convert childUL hs011200 hx011200 hy011200 using 1 <;> norm_num
              exact Batch0191.cell1530.sound htau (by
                simp only [Batch0191.cell1530, Batch0191.tau1530, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0112002 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-11/32 : ℝ) with hy011200 | hy011200
            · have hs0112001 : InSquare (-29/320) (-111/320) (1/320) tau := by
                convert childLR hs011200 hx011200 hy011200 using 1 <;> norm_num
              exact Batch0191.cell1529.sound htau (by
                simp only [Batch0191.cell1529, Batch0191.tau1529, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0112001 (by positivity) using 1 <;> norm_num)
            · have hs0112003 : InSquare (-29/320) (-109/320) (1/320) tau := by
                convert childUR hs011200 hx011200 hy011200 using 1 <;> norm_num
              exact Batch0191.cell1531.sound htau (by
                simp only [Batch0191.cell1531, Batch0191.tau1531, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0112003 (by positivity) using 1 <;> norm_num)
        · have hs011202 : InSquare (-3/32) (-53/160) (1/160) tau := by
            convert childUL hs01120 hx01120 hy01120 using 1 <;> norm_num
          exact Batch0050.cell0404.sound htau (by
            simp only [Batch0050.cell0404, Batch0050.tau0404, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs011202 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-27/80 : ℝ) with hy01120 | hy01120
        · have hs011201 : InSquare (-13/160) (-11/32) (1/160) tau := by
            convert childLR hs01120 hx01120 hy01120 using 1 <;> norm_num
          rcases le_total tau.re (-13/160 : ℝ) with hx011201 | hx011201
          · rcases le_total tau.im (-11/32 : ℝ) with hy011201 | hy011201
            · have hs0112010 : InSquare (-27/320) (-111/320) (1/320) tau := by
                convert childLL hs011201 hx011201 hy011201 using 1 <;> norm_num
              exact Batch0191.cell1532.sound htau (by
                simp only [Batch0191.cell1532, Batch0191.tau1532, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0112010 (by positivity) using 1 <;> norm_num)
            · have hs0112012 : InSquare (-27/320) (-109/320) (1/320) tau := by
                convert childUL hs011201 hx011201 hy011201 using 1 <;> norm_num
              exact Batch0191.cell1534.sound htau (by
                simp only [Batch0191.cell1534, Batch0191.tau1534, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0112012 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-11/32 : ℝ) with hy011201 | hy011201
            · have hs0112011 : InSquare (-5/64) (-111/320) (1/320) tau := by
                convert childLR hs011201 hx011201 hy011201 using 1 <;> norm_num
              exact Batch0191.cell1533.sound htau (by
                simp only [Batch0191.cell1533, Batch0191.tau1533, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0112011 (by positivity) using 1 <;> norm_num)
            · have hs0112013 : InSquare (-5/64) (-109/320) (1/320) tau := by
                convert childUR hs011201 hx011201 hy011201 using 1 <;> norm_num
              exact Batch0191.cell1535.sound htau (by
                simp only [Batch0191.cell1535, Batch0191.tau1535, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0112013 (by positivity) using 1 <;> norm_num)
        · have hs011203 : InSquare (-13/160) (-53/160) (1/160) tau := by
            convert childUR hs01120 hx01120 hy01120 using 1 <;> norm_num
          exact Batch0050.cell0405.sound htau (by
            simp only [Batch0050.cell0405, Batch0050.tau0405, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs011203 (by positivity) using 1 <;> norm_num)
    · have hs01122 : InSquare (-7/80) (-5/16) (1/80) tau := by
        convert childUL hs hx0112 hy0112 using 1 <;> norm_num
      rcases le_total tau.re (-7/80 : ℝ) with hx01122 | hx01122
      · rcases le_total tau.im (-5/16 : ℝ) with hy01122 | hy01122
        · have hs011220 : InSquare (-3/32) (-51/160) (1/160) tau := by
            convert childLL hs01122 hx01122 hy01122 using 1 <;> norm_num
          exact Batch0051.cell0409.sound htau (by
            simp only [Batch0051.cell0409, Batch0051.tau0409, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs011220 (by positivity) using 1 <;> norm_num)
        · have hs011222 : InSquare (-3/32) (-49/160) (1/160) tau := by
            convert childUL hs01122 hx01122 hy01122 using 1 <;> norm_num
          exact Batch0051.cell0411.sound htau (by
            simp only [Batch0051.cell0411, Batch0051.tau0411, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs011222 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-5/16 : ℝ) with hy01122 | hy01122
        · have hs011221 : InSquare (-13/160) (-51/160) (1/160) tau := by
            convert childLR hs01122 hx01122 hy01122 using 1 <;> norm_num
          exact Batch0051.cell0410.sound htau (by
            simp only [Batch0051.cell0410, Batch0051.tau0410, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs011221 (by positivity) using 1 <;> norm_num)
        · have hs011223 : InSquare (-13/160) (-49/160) (1/160) tau := by
            convert childUR hs01122 hx01122 hy01122 using 1 <;> norm_num
          exact Batch0051.cell0412.sound htau (by
            simp only [Batch0051.cell0412, Batch0051.tau0412, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs011223 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (-13/40 : ℝ) with hy0112 | hy0112
    · have hs01121 : InSquare (-1/16) (-27/80) (1/80) tau := by
        convert childLR hs hx0112 hy0112 using 1 <;> norm_num
      rcases le_total tau.re (-1/16 : ℝ) with hx01121 | hx01121
      · rcases le_total tau.im (-27/80 : ℝ) with hy01121 | hy01121
        · have hs011210 : InSquare (-11/160) (-11/32) (1/160) tau := by
            convert childLL hs01121 hx01121 hy01121 using 1 <;> norm_num
          rcases le_total tau.re (-11/160 : ℝ) with hx011210 | hx011210
          · rcases le_total tau.im (-11/32 : ℝ) with hy011210 | hy011210
            · have hs0112100 : InSquare (-23/320) (-111/320) (1/320) tau := by
                convert childLL hs011210 hx011210 hy011210 using 1 <;> norm_num
              exact Batch0192.cell1536.sound htau (by
                simp only [Batch0192.cell1536, Batch0192.tau1536, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0112100 (by positivity) using 1 <;> norm_num)
            · have hs0112102 : InSquare (-23/320) (-109/320) (1/320) tau := by
                convert childUL hs011210 hx011210 hy011210 using 1 <;> norm_num
              exact Batch0192.cell1538.sound htau (by
                simp only [Batch0192.cell1538, Batch0192.tau1538, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0112102 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-11/32 : ℝ) with hy011210 | hy011210
            · have hs0112101 : InSquare (-21/320) (-111/320) (1/320) tau := by
                convert childLR hs011210 hx011210 hy011210 using 1 <;> norm_num
              exact Batch0192.cell1537.sound htau (by
                simp only [Batch0192.cell1537, Batch0192.tau1537, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0112101 (by positivity) using 1 <;> norm_num)
            · have hs0112103 : InSquare (-21/320) (-109/320) (1/320) tau := by
                convert childUR hs011210 hx011210 hy011210 using 1 <;> norm_num
              exact Batch0192.cell1539.sound htau (by
                simp only [Batch0192.cell1539, Batch0192.tau1539, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0112103 (by positivity) using 1 <;> norm_num)
        · have hs011212 : InSquare (-11/160) (-53/160) (1/160) tau := by
            convert childUL hs01121 hx01121 hy01121 using 1 <;> norm_num
          exact Batch0050.cell0407.sound htau (by
            simp only [Batch0050.cell0407, Batch0050.tau0407, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs011212 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-27/80 : ℝ) with hy01121 | hy01121
        · have hs011211 : InSquare (-9/160) (-11/32) (1/160) tau := by
            convert childLR hs01121 hx01121 hy01121 using 1 <;> norm_num
          exact Batch0050.cell0406.sound htau (by
            simp only [Batch0050.cell0406, Batch0050.tau0406, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs011211 (by positivity) using 1 <;> norm_num)
        · have hs011213 : InSquare (-9/160) (-53/160) (1/160) tau := by
            convert childUR hs01121 hx01121 hy01121 using 1 <;> norm_num
          exact Batch0051.cell0408.sound htau (by
            simp only [Batch0051.cell0408, Batch0051.tau0408, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs011213 (by positivity) using 1 <;> norm_num)
    · have hs01123 : InSquare (-1/16) (-5/16) (1/80) tau := by
        convert childUR hs hx0112 hy0112 using 1 <;> norm_num
      rcases le_total tau.re (-1/16 : ℝ) with hx01123 | hx01123
      · rcases le_total tau.im (-5/16 : ℝ) with hy01123 | hy01123
        · have hs011230 : InSquare (-11/160) (-51/160) (1/160) tau := by
            convert childLL hs01123 hx01123 hy01123 using 1 <;> norm_num
          exact Batch0051.cell0413.sound htau (by
            simp only [Batch0051.cell0413, Batch0051.tau0413, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs011230 (by positivity) using 1 <;> norm_num)
        · have hs011232 : InSquare (-11/160) (-49/160) (1/160) tau := by
            convert childUL hs01123 hx01123 hy01123 using 1 <;> norm_num
          exact Batch0051.cell0415.sound htau (by
            simp only [Batch0051.cell0415, Batch0051.tau0415, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs011232 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-5/16 : ℝ) with hy01123 | hy01123
        · have hs011231 : InSquare (-9/160) (-51/160) (1/160) tau := by
            convert childLR hs01123 hx01123 hy01123 using 1 <;> norm_num
          exact Batch0051.cell0414.sound htau (by
            simp only [Batch0051.cell0414, Batch0051.tau0414, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs011231 (by positivity) using 1 <;> norm_num)
        · have hs011233 : InSquare (-9/160) (-49/160) (1/160) tau := by
            convert childUR hs01123 hx01123 hy01123 using 1 <;> norm_num
          exact Batch0052.cell0416.sound htau (by
            simp only [Batch0052.cell0416, Batch0052.tau0416, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs011233 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0112
