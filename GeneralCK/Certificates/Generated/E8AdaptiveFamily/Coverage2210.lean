import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0106
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0107
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0108
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0238
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0239

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2210

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-11/40) (9/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (-11/40 : ℝ) with hx2210 | hx2210
  · rcases le_total tau.im (9/40 : ℝ) with hy2210 | hy2210
    · have hs22100 : InSquare (-23/80) (17/80) (1/80) tau := by
        convert childLL hs hx2210 hy2210 using 1 <;> norm_num
      rcases le_total tau.re (-23/80 : ℝ) with hx22100 | hx22100
      · rcases le_total tau.im (17/80 : ℝ) with hy22100 | hy22100
        · have hs221000 : InSquare (-47/160) (33/160) (1/160) tau := by
            convert childLL hs22100 hx22100 hy22100 using 1 <;> norm_num
          exact Batch0106.cell0855.sound htau (by
            simp only [Batch0106.cell0855, Batch0106.tau0855, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs221000 (by positivity) using 1 <;> norm_num)
        · have hs221002 : InSquare (-47/160) (7/32) (1/160) tau := by
            convert childUL hs22100 hx22100 hy22100 using 1 <;> norm_num
          exact Batch0107.cell0857.sound htau (by
            simp only [Batch0107.cell0857, Batch0107.tau0857, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs221002 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (17/80 : ℝ) with hy22100 | hy22100
        · have hs221001 : InSquare (-9/32) (33/160) (1/160) tau := by
            convert childLR hs22100 hx22100 hy22100 using 1 <;> norm_num
          exact Batch0107.cell0856.sound htau (by
            simp only [Batch0107.cell0856, Batch0107.tau0856, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs221001 (by positivity) using 1 <;> norm_num)
        · have hs221003 : InSquare (-9/32) (7/32) (1/160) tau := by
            convert childUR hs22100 hx22100 hy22100 using 1 <;> norm_num
          exact Batch0107.cell0858.sound htau (by
            simp only [Batch0107.cell0858, Batch0107.tau0858, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs221003 (by positivity) using 1 <;> norm_num)
    · have hs22102 : InSquare (-23/80) (19/80) (1/80) tau := by
        convert childUL hs hx2210 hy2210 using 1 <;> norm_num
      rcases le_total tau.re (-23/80 : ℝ) with hx22102 | hx22102
      · rcases le_total tau.im (19/80 : ℝ) with hy22102 | hy22102
        · have hs221020 : InSquare (-47/160) (37/160) (1/160) tau := by
            convert childLL hs22102 hx22102 hy22102 using 1 <;> norm_num
          exact Batch0107.cell0863.sound htau (by
            simp only [Batch0107.cell0863, Batch0107.tau0863, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs221020 (by positivity) using 1 <;> norm_num)
        · have hs221022 : InSquare (-47/160) (39/160) (1/160) tau := by
            convert childUL hs22102 hx22102 hy22102 using 1 <;> norm_num
          rcases le_total tau.re (-47/160 : ℝ) with hx221022 | hx221022
          · rcases le_total tau.im (39/160 : ℝ) with hy221022 | hy221022
            · have hs2210220 : InSquare (-19/64) (77/320) (1/320) tau := by
                convert childLL hs221022 hx221022 hy221022 using 1 <;> norm_num
              exact Batch0238.cell1909.sound htau (by
                simp only [Batch0238.cell1909, Batch0238.tau1909, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2210220 (by positivity) using 1 <;> norm_num)
            · have hs2210222 : InSquare (-19/64) (79/320) (1/320) tau := by
                convert childUL hs221022 hx221022 hy221022 using 1 <;> norm_num
              exact Batch0238.cell1911.sound htau (by
                simp only [Batch0238.cell1911, Batch0238.tau1911, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2210222 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (39/160 : ℝ) with hy221022 | hy221022
            · have hs2210221 : InSquare (-93/320) (77/320) (1/320) tau := by
                convert childLR hs221022 hx221022 hy221022 using 1 <;> norm_num
              exact Batch0238.cell1910.sound htau (by
                simp only [Batch0238.cell1910, Batch0238.tau1910, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2210221 (by positivity) using 1 <;> norm_num)
            · have hs2210223 : InSquare (-93/320) (79/320) (1/320) tau := by
                convert childUR hs221022 hx221022 hy221022 using 1 <;> norm_num
              exact Batch0239.cell1912.sound htau (by
                simp only [Batch0239.cell1912, Batch0239.tau1912, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2210223 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (19/80 : ℝ) with hy22102 | hy22102
        · have hs221021 : InSquare (-9/32) (37/160) (1/160) tau := by
            convert childLR hs22102 hx22102 hy22102 using 1 <;> norm_num
          exact Batch0108.cell0864.sound htau (by
            simp only [Batch0108.cell0864, Batch0108.tau0864, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs221021 (by positivity) using 1 <;> norm_num)
        · have hs221023 : InSquare (-9/32) (39/160) (1/160) tau := by
            convert childUR hs22102 hx22102 hy22102 using 1 <;> norm_num
          exact Batch0108.cell0865.sound htau (by
            simp only [Batch0108.cell0865, Batch0108.tau0865, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs221023 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (9/40 : ℝ) with hy2210 | hy2210
    · have hs22101 : InSquare (-21/80) (17/80) (1/80) tau := by
        convert childLR hs hx2210 hy2210 using 1 <;> norm_num
      rcases le_total tau.re (-21/80 : ℝ) with hx22101 | hx22101
      · rcases le_total tau.im (17/80 : ℝ) with hy22101 | hy22101
        · have hs221010 : InSquare (-43/160) (33/160) (1/160) tau := by
            convert childLL hs22101 hx22101 hy22101 using 1 <;> norm_num
          exact Batch0107.cell0859.sound htau (by
            simp only [Batch0107.cell0859, Batch0107.tau0859, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs221010 (by positivity) using 1 <;> norm_num)
        · have hs221012 : InSquare (-43/160) (7/32) (1/160) tau := by
            convert childUL hs22101 hx22101 hy22101 using 1 <;> norm_num
          exact Batch0107.cell0861.sound htau (by
            simp only [Batch0107.cell0861, Batch0107.tau0861, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs221012 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (17/80 : ℝ) with hy22101 | hy22101
        · have hs221011 : InSquare (-41/160) (33/160) (1/160) tau := by
            convert childLR hs22101 hx22101 hy22101 using 1 <;> norm_num
          exact Batch0107.cell0860.sound htau (by
            simp only [Batch0107.cell0860, Batch0107.tau0860, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs221011 (by positivity) using 1 <;> norm_num)
        · have hs221013 : InSquare (-41/160) (7/32) (1/160) tau := by
            convert childUR hs22101 hx22101 hy22101 using 1 <;> norm_num
          exact Batch0107.cell0862.sound htau (by
            simp only [Batch0107.cell0862, Batch0107.tau0862, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs221013 (by positivity) using 1 <;> norm_num)
    · have hs22103 : InSquare (-21/80) (19/80) (1/80) tau := by
        convert childUR hs hx2210 hy2210 using 1 <;> norm_num
      rcases le_total tau.re (-21/80 : ℝ) with hx22103 | hx22103
      · rcases le_total tau.im (19/80 : ℝ) with hy22103 | hy22103
        · have hs221030 : InSquare (-43/160) (37/160) (1/160) tau := by
            convert childLL hs22103 hx22103 hy22103 using 1 <;> norm_num
          exact Batch0108.cell0866.sound htau (by
            simp only [Batch0108.cell0866, Batch0108.tau0866, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs221030 (by positivity) using 1 <;> norm_num)
        · have hs221032 : InSquare (-43/160) (39/160) (1/160) tau := by
            convert childUL hs22103 hx22103 hy22103 using 1 <;> norm_num
          exact Batch0108.cell0868.sound htau (by
            simp only [Batch0108.cell0868, Batch0108.tau0868, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs221032 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (19/80 : ℝ) with hy22103 | hy22103
        · have hs221031 : InSquare (-41/160) (37/160) (1/160) tau := by
            convert childLR hs22103 hx22103 hy22103 using 1 <;> norm_num
          exact Batch0108.cell0867.sound htau (by
            simp only [Batch0108.cell0867, Batch0108.tau0867, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs221031 (by positivity) using 1 <;> norm_num)
        · have hs221033 : InSquare (-41/160) (39/160) (1/160) tau := by
            convert childUR hs22103 hx22103 hy22103 using 1 <;> norm_num
          exact Batch0108.cell0869.sound htau (by
            simp only [Batch0108.cell0869, Batch0108.tau0869, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs221033 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2210
