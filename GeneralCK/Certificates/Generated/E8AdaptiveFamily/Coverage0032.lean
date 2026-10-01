import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0045
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0046
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0047
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0167

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0032

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-11/40) (-9/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (-11/40 : ℝ) with hx0032 | hx0032
  · rcases le_total tau.im (-9/40 : ℝ) with hy0032 | hy0032
    · have hs00320 : InSquare (-23/80) (-19/80) (1/80) tau := by
        convert childLL hs hx0032 hy0032 using 1 <;> norm_num
      rcases le_total tau.re (-23/80 : ℝ) with hx00320 | hx00320
      · rcases le_total tau.im (-19/80 : ℝ) with hy00320 | hy00320
        · have hs003200 : InSquare (-47/160) (-39/160) (1/160) tau := by
            convert childLL hs00320 hx00320 hy00320 using 1 <;> norm_num
          rcases le_total tau.re (-47/160 : ℝ) with hx003200 | hx003200
          · rcases le_total tau.im (-39/160 : ℝ) with hy003200 | hy003200
            · have hs0032000 : InSquare (-19/64) (-79/320) (1/320) tau := by
                convert childLL hs003200 hx003200 hy003200 using 1 <;> norm_num
              exact Batch0167.cell1340.sound htau (by
                simp only [Batch0167.cell1340, Batch0167.tau1340, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0032000 (by positivity) using 1 <;> norm_num)
            · have hs0032002 : InSquare (-19/64) (-77/320) (1/320) tau := by
                convert childUL hs003200 hx003200 hy003200 using 1 <;> norm_num
              exact Batch0167.cell1342.sound htau (by
                simp only [Batch0167.cell1342, Batch0167.tau1342, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0032002 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-39/160 : ℝ) with hy003200 | hy003200
            · have hs0032001 : InSquare (-93/320) (-79/320) (1/320) tau := by
                convert childLR hs003200 hx003200 hy003200 using 1 <;> norm_num
              exact Batch0167.cell1341.sound htau (by
                simp only [Batch0167.cell1341, Batch0167.tau1341, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0032001 (by positivity) using 1 <;> norm_num)
            · have hs0032003 : InSquare (-93/320) (-77/320) (1/320) tau := by
                convert childUR hs003200 hx003200 hy003200 using 1 <;> norm_num
              exact Batch0167.cell1343.sound htau (by
                simp only [Batch0167.cell1343, Batch0167.tau1343, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0032003 (by positivity) using 1 <;> norm_num)
        · have hs003202 : InSquare (-47/160) (-37/160) (1/160) tau := by
            convert childUL hs00320 hx00320 hy00320 using 1 <;> norm_num
          exact Batch0045.cell0363.sound htau (by
            simp only [Batch0045.cell0363, Batch0045.tau0363, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs003202 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-19/80 : ℝ) with hy00320 | hy00320
        · have hs003201 : InSquare (-9/32) (-39/160) (1/160) tau := by
            convert childLR hs00320 hx00320 hy00320 using 1 <;> norm_num
          exact Batch0045.cell0362.sound htau (by
            simp only [Batch0045.cell0362, Batch0045.tau0362, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs003201 (by positivity) using 1 <;> norm_num)
        · have hs003203 : InSquare (-9/32) (-37/160) (1/160) tau := by
            convert childUR hs00320 hx00320 hy00320 using 1 <;> norm_num
          exact Batch0045.cell0364.sound htau (by
            simp only [Batch0045.cell0364, Batch0045.tau0364, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs003203 (by positivity) using 1 <;> norm_num)
    · have hs00322 : InSquare (-23/80) (-17/80) (1/80) tau := by
        convert childUL hs hx0032 hy0032 using 1 <;> norm_num
      rcases le_total tau.re (-23/80 : ℝ) with hx00322 | hx00322
      · rcases le_total tau.im (-17/80 : ℝ) with hy00322 | hy00322
        · have hs003220 : InSquare (-47/160) (-7/32) (1/160) tau := by
            convert childLL hs00322 hx00322 hy00322 using 1 <;> norm_num
          exact Batch0046.cell0369.sound htau (by
            simp only [Batch0046.cell0369, Batch0046.tau0369, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs003220 (by positivity) using 1 <;> norm_num)
        · have hs003222 : InSquare (-47/160) (-33/160) (1/160) tau := by
            convert childUL hs00322 hx00322 hy00322 using 1 <;> norm_num
          exact Batch0046.cell0371.sound htau (by
            simp only [Batch0046.cell0371, Batch0046.tau0371, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs003222 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-17/80 : ℝ) with hy00322 | hy00322
        · have hs003221 : InSquare (-9/32) (-7/32) (1/160) tau := by
            convert childLR hs00322 hx00322 hy00322 using 1 <;> norm_num
          exact Batch0046.cell0370.sound htau (by
            simp only [Batch0046.cell0370, Batch0046.tau0370, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs003221 (by positivity) using 1 <;> norm_num)
        · have hs003223 : InSquare (-9/32) (-33/160) (1/160) tau := by
            convert childUR hs00322 hx00322 hy00322 using 1 <;> norm_num
          exact Batch0046.cell0372.sound htau (by
            simp only [Batch0046.cell0372, Batch0046.tau0372, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs003223 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (-9/40 : ℝ) with hy0032 | hy0032
    · have hs00321 : InSquare (-21/80) (-19/80) (1/80) tau := by
        convert childLR hs hx0032 hy0032 using 1 <;> norm_num
      rcases le_total tau.re (-21/80 : ℝ) with hx00321 | hx00321
      · rcases le_total tau.im (-19/80 : ℝ) with hy00321 | hy00321
        · have hs003210 : InSquare (-43/160) (-39/160) (1/160) tau := by
            convert childLL hs00321 hx00321 hy00321 using 1 <;> norm_num
          exact Batch0045.cell0365.sound htau (by
            simp only [Batch0045.cell0365, Batch0045.tau0365, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs003210 (by positivity) using 1 <;> norm_num)
        · have hs003212 : InSquare (-43/160) (-37/160) (1/160) tau := by
            convert childUL hs00321 hx00321 hy00321 using 1 <;> norm_num
          exact Batch0045.cell0367.sound htau (by
            simp only [Batch0045.cell0367, Batch0045.tau0367, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs003212 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-19/80 : ℝ) with hy00321 | hy00321
        · have hs003211 : InSquare (-41/160) (-39/160) (1/160) tau := by
            convert childLR hs00321 hx00321 hy00321 using 1 <;> norm_num
          exact Batch0045.cell0366.sound htau (by
            simp only [Batch0045.cell0366, Batch0045.tau0366, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs003211 (by positivity) using 1 <;> norm_num)
        · have hs003213 : InSquare (-41/160) (-37/160) (1/160) tau := by
            convert childUR hs00321 hx00321 hy00321 using 1 <;> norm_num
          exact Batch0046.cell0368.sound htau (by
            simp only [Batch0046.cell0368, Batch0046.tau0368, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs003213 (by positivity) using 1 <;> norm_num)
    · have hs00323 : InSquare (-21/80) (-17/80) (1/80) tau := by
        convert childUR hs hx0032 hy0032 using 1 <;> norm_num
      rcases le_total tau.re (-21/80 : ℝ) with hx00323 | hx00323
      · rcases le_total tau.im (-17/80 : ℝ) with hy00323 | hy00323
        · have hs003230 : InSquare (-43/160) (-7/32) (1/160) tau := by
            convert childLL hs00323 hx00323 hy00323 using 1 <;> norm_num
          exact Batch0046.cell0373.sound htau (by
            simp only [Batch0046.cell0373, Batch0046.tau0373, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs003230 (by positivity) using 1 <;> norm_num)
        · have hs003232 : InSquare (-43/160) (-33/160) (1/160) tau := by
            convert childUL hs00323 hx00323 hy00323 using 1 <;> norm_num
          exact Batch0046.cell0375.sound htau (by
            simp only [Batch0046.cell0375, Batch0046.tau0375, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs003232 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-17/80 : ℝ) with hy00323 | hy00323
        · have hs003231 : InSquare (-41/160) (-7/32) (1/160) tau := by
            convert childLR hs00323 hx00323 hy00323 using 1 <;> norm_num
          exact Batch0046.cell0374.sound htau (by
            simp only [Batch0046.cell0374, Batch0046.tau0374, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs003231 (by positivity) using 1 <;> norm_num)
        · have hs003233 : InSquare (-41/160) (-33/160) (1/160) tau := by
            convert childUR hs00323 hx00323 hy00323 using 1 <;> norm_num
          exact Batch0047.cell0376.sound htau (by
            simp only [Batch0047.cell0376, Batch0047.tau0376, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs003233 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0032
