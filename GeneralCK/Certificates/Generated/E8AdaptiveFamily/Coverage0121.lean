import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0056
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0057
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0058

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0121

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-1/8) (-11/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (-1/8 : ℝ) with hx0121 | hx0121
  · rcases le_total tau.im (-11/40 : ℝ) with hy0121 | hy0121
    · have hs01210 : InSquare (-11/80) (-23/80) (1/80) tau := by
        convert childLL hs hx0121 hy0121 using 1 <;> norm_num
      rcases le_total tau.re (-11/80 : ℝ) with hx01210 | hx01210
      · rcases le_total tau.im (-23/80 : ℝ) with hy01210 | hy01210
        · have hs012100 : InSquare (-23/160) (-47/160) (1/160) tau := by
            convert childLL hs01210 hx01210 hy01210 using 1 <;> norm_num
          exact Batch0056.cell0449.sound htau (by
            simp only [Batch0056.cell0449, Batch0056.tau0449, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs012100 (by positivity) using 1 <;> norm_num)
        · have hs012102 : InSquare (-23/160) (-9/32) (1/160) tau := by
            convert childUL hs01210 hx01210 hy01210 using 1 <;> norm_num
          exact Batch0056.cell0451.sound htau (by
            simp only [Batch0056.cell0451, Batch0056.tau0451, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs012102 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-23/80 : ℝ) with hy01210 | hy01210
        · have hs012101 : InSquare (-21/160) (-47/160) (1/160) tau := by
            convert childLR hs01210 hx01210 hy01210 using 1 <;> norm_num
          exact Batch0056.cell0450.sound htau (by
            simp only [Batch0056.cell0450, Batch0056.tau0450, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs012101 (by positivity) using 1 <;> norm_num)
        · have hs012103 : InSquare (-21/160) (-9/32) (1/160) tau := by
            convert childUR hs01210 hx01210 hy01210 using 1 <;> norm_num
          exact Batch0056.cell0452.sound htau (by
            simp only [Batch0056.cell0452, Batch0056.tau0452, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs012103 (by positivity) using 1 <;> norm_num)
    · have hs01212 : InSquare (-11/80) (-21/80) (1/80) tau := by
        convert childUL hs hx0121 hy0121 using 1 <;> norm_num
      rcases le_total tau.re (-11/80 : ℝ) with hx01212 | hx01212
      · rcases le_total tau.im (-21/80 : ℝ) with hy01212 | hy01212
        · have hs012120 : InSquare (-23/160) (-43/160) (1/160) tau := by
            convert childLL hs01212 hx01212 hy01212 using 1 <;> norm_num
          exact Batch0057.cell0457.sound htau (by
            simp only [Batch0057.cell0457, Batch0057.tau0457, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs012120 (by positivity) using 1 <;> norm_num)
        · have hs012122 : InSquare (-23/160) (-41/160) (1/160) tau := by
            convert childUL hs01212 hx01212 hy01212 using 1 <;> norm_num
          exact Batch0057.cell0459.sound htau (by
            simp only [Batch0057.cell0459, Batch0057.tau0459, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs012122 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-21/80 : ℝ) with hy01212 | hy01212
        · have hs012121 : InSquare (-21/160) (-43/160) (1/160) tau := by
            convert childLR hs01212 hx01212 hy01212 using 1 <;> norm_num
          exact Batch0057.cell0458.sound htau (by
            simp only [Batch0057.cell0458, Batch0057.tau0458, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs012121 (by positivity) using 1 <;> norm_num)
        · have hs012123 : InSquare (-21/160) (-41/160) (1/160) tau := by
            convert childUR hs01212 hx01212 hy01212 using 1 <;> norm_num
          exact Batch0057.cell0460.sound htau (by
            simp only [Batch0057.cell0460, Batch0057.tau0460, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs012123 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (-11/40 : ℝ) with hy0121 | hy0121
    · have hs01211 : InSquare (-9/80) (-23/80) (1/80) tau := by
        convert childLR hs hx0121 hy0121 using 1 <;> norm_num
      rcases le_total tau.re (-9/80 : ℝ) with hx01211 | hx01211
      · rcases le_total tau.im (-23/80 : ℝ) with hy01211 | hy01211
        · have hs012110 : InSquare (-19/160) (-47/160) (1/160) tau := by
            convert childLL hs01211 hx01211 hy01211 using 1 <;> norm_num
          exact Batch0056.cell0453.sound htau (by
            simp only [Batch0056.cell0453, Batch0056.tau0453, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs012110 (by positivity) using 1 <;> norm_num)
        · have hs012112 : InSquare (-19/160) (-9/32) (1/160) tau := by
            convert childUL hs01211 hx01211 hy01211 using 1 <;> norm_num
          exact Batch0056.cell0455.sound htau (by
            simp only [Batch0056.cell0455, Batch0056.tau0455, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs012112 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-23/80 : ℝ) with hy01211 | hy01211
        · have hs012111 : InSquare (-17/160) (-47/160) (1/160) tau := by
            convert childLR hs01211 hx01211 hy01211 using 1 <;> norm_num
          exact Batch0056.cell0454.sound htau (by
            simp only [Batch0056.cell0454, Batch0056.tau0454, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs012111 (by positivity) using 1 <;> norm_num)
        · have hs012113 : InSquare (-17/160) (-9/32) (1/160) tau := by
            convert childUR hs01211 hx01211 hy01211 using 1 <;> norm_num
          exact Batch0057.cell0456.sound htau (by
            simp only [Batch0057.cell0456, Batch0057.tau0456, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs012113 (by positivity) using 1 <;> norm_num)
    · have hs01213 : InSquare (-9/80) (-21/80) (1/80) tau := by
        convert childUR hs hx0121 hy0121 using 1 <;> norm_num
      rcases le_total tau.re (-9/80 : ℝ) with hx01213 | hx01213
      · rcases le_total tau.im (-21/80 : ℝ) with hy01213 | hy01213
        · have hs012130 : InSquare (-19/160) (-43/160) (1/160) tau := by
            convert childLL hs01213 hx01213 hy01213 using 1 <;> norm_num
          exact Batch0057.cell0461.sound htau (by
            simp only [Batch0057.cell0461, Batch0057.tau0461, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs012130 (by positivity) using 1 <;> norm_num)
        · have hs012132 : InSquare (-19/160) (-41/160) (1/160) tau := by
            convert childUL hs01213 hx01213 hy01213 using 1 <;> norm_num
          exact Batch0057.cell0463.sound htau (by
            simp only [Batch0057.cell0463, Batch0057.tau0463, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs012132 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-21/80 : ℝ) with hy01213 | hy01213
        · have hs012131 : InSquare (-17/160) (-43/160) (1/160) tau := by
            convert childLR hs01213 hx01213 hy01213 using 1 <;> norm_num
          exact Batch0057.cell0462.sound htau (by
            simp only [Batch0057.cell0462, Batch0057.tau0462, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs012131 (by positivity) using 1 <;> norm_num)
        · have hs012133 : InSquare (-17/160) (-41/160) (1/160) tau := by
            convert childUR hs01213 hx01213 hy01213 using 1 <;> norm_num
          exact Batch0058.cell0464.sound htau (by
            simp only [Batch0058.cell0464, Batch0058.tau0464, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs012133 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0121
