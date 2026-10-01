import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0143
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0144
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0145

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3300

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (9/40) (9/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (9/40 : ℝ) with hx3300 | hx3300
  · rcases le_total tau.im (9/40 : ℝ) with hy3300 | hy3300
    · have hs33000 : InSquare (17/80) (17/80) (1/80) tau := by
        convert childLL hs hx3300 hy3300 using 1 <;> norm_num
      rcases le_total tau.re (17/80 : ℝ) with hx33000 | hx33000
      · rcases le_total tau.im (17/80 : ℝ) with hy33000 | hy33000
        · have hs330000 : InSquare (33/160) (33/160) (1/160) tau := by
            convert childLL hs33000 hx33000 hy33000 using 1 <;> norm_num
          exact Batch0143.cell1151.sound htau (by
            simp only [Batch0143.cell1151, Batch0143.tau1151, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs330000 (by positivity) using 1 <;> norm_num)
        · have hs330002 : InSquare (33/160) (7/32) (1/160) tau := by
            convert childUL hs33000 hx33000 hy33000 using 1 <;> norm_num
          exact Batch0144.cell1153.sound htau (by
            simp only [Batch0144.cell1153, Batch0144.tau1153, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs330002 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (17/80 : ℝ) with hy33000 | hy33000
        · have hs330001 : InSquare (7/32) (33/160) (1/160) tau := by
            convert childLR hs33000 hx33000 hy33000 using 1 <;> norm_num
          exact Batch0144.cell1152.sound htau (by
            simp only [Batch0144.cell1152, Batch0144.tau1152, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs330001 (by positivity) using 1 <;> norm_num)
        · have hs330003 : InSquare (7/32) (7/32) (1/160) tau := by
            convert childUR hs33000 hx33000 hy33000 using 1 <;> norm_num
          exact Batch0144.cell1154.sound htau (by
            simp only [Batch0144.cell1154, Batch0144.tau1154, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs330003 (by positivity) using 1 <;> norm_num)
    · have hs33002 : InSquare (17/80) (19/80) (1/80) tau := by
        convert childUL hs hx3300 hy3300 using 1 <;> norm_num
      rcases le_total tau.re (17/80 : ℝ) with hx33002 | hx33002
      · rcases le_total tau.im (19/80 : ℝ) with hy33002 | hy33002
        · have hs330020 : InSquare (33/160) (37/160) (1/160) tau := by
            convert childLL hs33002 hx33002 hy33002 using 1 <;> norm_num
          exact Batch0144.cell1159.sound htau (by
            simp only [Batch0144.cell1159, Batch0144.tau1159, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs330020 (by positivity) using 1 <;> norm_num)
        · have hs330022 : InSquare (33/160) (39/160) (1/160) tau := by
            convert childUL hs33002 hx33002 hy33002 using 1 <;> norm_num
          exact Batch0145.cell1161.sound htau (by
            simp only [Batch0145.cell1161, Batch0145.tau1161, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs330022 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (19/80 : ℝ) with hy33002 | hy33002
        · have hs330021 : InSquare (7/32) (37/160) (1/160) tau := by
            convert childLR hs33002 hx33002 hy33002 using 1 <;> norm_num
          exact Batch0145.cell1160.sound htau (by
            simp only [Batch0145.cell1160, Batch0145.tau1160, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs330021 (by positivity) using 1 <;> norm_num)
        · have hs330023 : InSquare (7/32) (39/160) (1/160) tau := by
            convert childUR hs33002 hx33002 hy33002 using 1 <;> norm_num
          exact Batch0145.cell1162.sound htau (by
            simp only [Batch0145.cell1162, Batch0145.tau1162, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs330023 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (9/40 : ℝ) with hy3300 | hy3300
    · have hs33001 : InSquare (19/80) (17/80) (1/80) tau := by
        convert childLR hs hx3300 hy3300 using 1 <;> norm_num
      rcases le_total tau.re (19/80 : ℝ) with hx33001 | hx33001
      · rcases le_total tau.im (17/80 : ℝ) with hy33001 | hy33001
        · have hs330010 : InSquare (37/160) (33/160) (1/160) tau := by
            convert childLL hs33001 hx33001 hy33001 using 1 <;> norm_num
          exact Batch0144.cell1155.sound htau (by
            simp only [Batch0144.cell1155, Batch0144.tau1155, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs330010 (by positivity) using 1 <;> norm_num)
        · have hs330012 : InSquare (37/160) (7/32) (1/160) tau := by
            convert childUL hs33001 hx33001 hy33001 using 1 <;> norm_num
          exact Batch0144.cell1157.sound htau (by
            simp only [Batch0144.cell1157, Batch0144.tau1157, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs330012 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (17/80 : ℝ) with hy33001 | hy33001
        · have hs330011 : InSquare (39/160) (33/160) (1/160) tau := by
            convert childLR hs33001 hx33001 hy33001 using 1 <;> norm_num
          exact Batch0144.cell1156.sound htau (by
            simp only [Batch0144.cell1156, Batch0144.tau1156, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs330011 (by positivity) using 1 <;> norm_num)
        · have hs330013 : InSquare (39/160) (7/32) (1/160) tau := by
            convert childUR hs33001 hx33001 hy33001 using 1 <;> norm_num
          exact Batch0144.cell1158.sound htau (by
            simp only [Batch0144.cell1158, Batch0144.tau1158, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs330013 (by positivity) using 1 <;> norm_num)
    · have hs33003 : InSquare (19/80) (19/80) (1/80) tau := by
        convert childUR hs hx3300 hy3300 using 1 <;> norm_num
      rcases le_total tau.re (19/80 : ℝ) with hx33003 | hx33003
      · rcases le_total tau.im (19/80 : ℝ) with hy33003 | hy33003
        · have hs330030 : InSquare (37/160) (37/160) (1/160) tau := by
            convert childLL hs33003 hx33003 hy33003 using 1 <;> norm_num
          exact Batch0145.cell1163.sound htau (by
            simp only [Batch0145.cell1163, Batch0145.tau1163, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs330030 (by positivity) using 1 <;> norm_num)
        · have hs330032 : InSquare (37/160) (39/160) (1/160) tau := by
            convert childUL hs33003 hx33003 hy33003 using 1 <;> norm_num
          exact Batch0145.cell1165.sound htau (by
            simp only [Batch0145.cell1165, Batch0145.tau1165, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs330032 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (19/80 : ℝ) with hy33003 | hy33003
        · have hs330031 : InSquare (39/160) (37/160) (1/160) tau := by
            convert childLR hs33003 hx33003 hy33003 using 1 <;> norm_num
          exact Batch0145.cell1164.sound htau (by
            simp only [Batch0145.cell1164, Batch0145.tau1164, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs330031 (by positivity) using 1 <;> norm_num)
        · have hs330033 : InSquare (39/160) (39/160) (1/160) tau := by
            convert childUR hs33003 hx33003 hy33003 using 1 <;> norm_num
          exact Batch0145.cell1166.sound htau (by
            simp only [Batch0145.cell1166, Batch0145.tau1166, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs330033 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3300
