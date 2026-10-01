import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0145
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0146
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0147
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0302

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3301

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (11/40) (9/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (11/40 : ℝ) with hx3301 | hx3301
  · rcases le_total tau.im (9/40 : ℝ) with hy3301 | hy3301
    · have hs33010 : InSquare (21/80) (17/80) (1/80) tau := by
        convert childLL hs hx3301 hy3301 using 1 <;> norm_num
      rcases le_total tau.re (21/80 : ℝ) with hx33010 | hx33010
      · rcases le_total tau.im (17/80 : ℝ) with hy33010 | hy33010
        · have hs330100 : InSquare (41/160) (33/160) (1/160) tau := by
            convert childLL hs33010 hx33010 hy33010 using 1 <;> norm_num
          exact Batch0145.cell1167.sound htau (by
            simp only [Batch0145.cell1167, Batch0145.tau1167, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs330100 (by positivity) using 1 <;> norm_num)
        · have hs330102 : InSquare (41/160) (7/32) (1/160) tau := by
            convert childUL hs33010 hx33010 hy33010 using 1 <;> norm_num
          exact Batch0146.cell1169.sound htau (by
            simp only [Batch0146.cell1169, Batch0146.tau1169, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs330102 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (17/80 : ℝ) with hy33010 | hy33010
        · have hs330101 : InSquare (43/160) (33/160) (1/160) tau := by
            convert childLR hs33010 hx33010 hy33010 using 1 <;> norm_num
          exact Batch0146.cell1168.sound htau (by
            simp only [Batch0146.cell1168, Batch0146.tau1168, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs330101 (by positivity) using 1 <;> norm_num)
        · have hs330103 : InSquare (43/160) (7/32) (1/160) tau := by
            convert childUR hs33010 hx33010 hy33010 using 1 <;> norm_num
          exact Batch0146.cell1170.sound htau (by
            simp only [Batch0146.cell1170, Batch0146.tau1170, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs330103 (by positivity) using 1 <;> norm_num)
    · have hs33012 : InSquare (21/80) (19/80) (1/80) tau := by
        convert childUL hs hx3301 hy3301 using 1 <;> norm_num
      rcases le_total tau.re (21/80 : ℝ) with hx33012 | hx33012
      · rcases le_total tau.im (19/80 : ℝ) with hy33012 | hy33012
        · have hs330120 : InSquare (41/160) (37/160) (1/160) tau := by
            convert childLL hs33012 hx33012 hy33012 using 1 <;> norm_num
          exact Batch0146.cell1175.sound htau (by
            simp only [Batch0146.cell1175, Batch0146.tau1175, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs330120 (by positivity) using 1 <;> norm_num)
        · have hs330122 : InSquare (41/160) (39/160) (1/160) tau := by
            convert childUL hs33012 hx33012 hy33012 using 1 <;> norm_num
          exact Batch0147.cell1177.sound htau (by
            simp only [Batch0147.cell1177, Batch0147.tau1177, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs330122 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (19/80 : ℝ) with hy33012 | hy33012
        · have hs330121 : InSquare (43/160) (37/160) (1/160) tau := by
            convert childLR hs33012 hx33012 hy33012 using 1 <;> norm_num
          exact Batch0147.cell1176.sound htau (by
            simp only [Batch0147.cell1176, Batch0147.tau1176, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs330121 (by positivity) using 1 <;> norm_num)
        · have hs330123 : InSquare (43/160) (39/160) (1/160) tau := by
            convert childUR hs33012 hx33012 hy33012 using 1 <;> norm_num
          exact Batch0147.cell1178.sound htau (by
            simp only [Batch0147.cell1178, Batch0147.tau1178, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs330123 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (9/40 : ℝ) with hy3301 | hy3301
    · have hs33011 : InSquare (23/80) (17/80) (1/80) tau := by
        convert childLR hs hx3301 hy3301 using 1 <;> norm_num
      rcases le_total tau.re (23/80 : ℝ) with hx33011 | hx33011
      · rcases le_total tau.im (17/80 : ℝ) with hy33011 | hy33011
        · have hs330110 : InSquare (9/32) (33/160) (1/160) tau := by
            convert childLL hs33011 hx33011 hy33011 using 1 <;> norm_num
          exact Batch0146.cell1171.sound htau (by
            simp only [Batch0146.cell1171, Batch0146.tau1171, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs330110 (by positivity) using 1 <;> norm_num)
        · have hs330112 : InSquare (9/32) (7/32) (1/160) tau := by
            convert childUL hs33011 hx33011 hy33011 using 1 <;> norm_num
          exact Batch0146.cell1173.sound htau (by
            simp only [Batch0146.cell1173, Batch0146.tau1173, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs330112 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (17/80 : ℝ) with hy33011 | hy33011
        · have hs330111 : InSquare (47/160) (33/160) (1/160) tau := by
            convert childLR hs33011 hx33011 hy33011 using 1 <;> norm_num
          exact Batch0146.cell1172.sound htau (by
            simp only [Batch0146.cell1172, Batch0146.tau1172, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs330111 (by positivity) using 1 <;> norm_num)
        · have hs330113 : InSquare (47/160) (7/32) (1/160) tau := by
            convert childUR hs33011 hx33011 hy33011 using 1 <;> norm_num
          exact Batch0146.cell1174.sound htau (by
            simp only [Batch0146.cell1174, Batch0146.tau1174, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs330113 (by positivity) using 1 <;> norm_num)
    · have hs33013 : InSquare (23/80) (19/80) (1/80) tau := by
        convert childUR hs hx3301 hy3301 using 1 <;> norm_num
      rcases le_total tau.re (23/80 : ℝ) with hx33013 | hx33013
      · rcases le_total tau.im (19/80 : ℝ) with hy33013 | hy33013
        · have hs330130 : InSquare (9/32) (37/160) (1/160) tau := by
            convert childLL hs33013 hx33013 hy33013 using 1 <;> norm_num
          exact Batch0147.cell1179.sound htau (by
            simp only [Batch0147.cell1179, Batch0147.tau1179, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs330130 (by positivity) using 1 <;> norm_num)
        · have hs330132 : InSquare (9/32) (39/160) (1/160) tau := by
            convert childUL hs33013 hx33013 hy33013 using 1 <;> norm_num
          exact Batch0147.cell1181.sound htau (by
            simp only [Batch0147.cell1181, Batch0147.tau1181, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs330132 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (19/80 : ℝ) with hy33013 | hy33013
        · have hs330131 : InSquare (47/160) (37/160) (1/160) tau := by
            convert childLR hs33013 hx33013 hy33013 using 1 <;> norm_num
          exact Batch0147.cell1180.sound htau (by
            simp only [Batch0147.cell1180, Batch0147.tau1180, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs330131 (by positivity) using 1 <;> norm_num)
        · have hs330133 : InSquare (47/160) (39/160) (1/160) tau := by
            convert childUR hs33013 hx33013 hy33013 using 1 <;> norm_num
          rcases le_total tau.re (47/160 : ℝ) with hx330133 | hx330133
          · rcases le_total tau.im (39/160 : ℝ) with hy330133 | hy330133
            · have hs3301330 : InSquare (93/320) (77/320) (1/320) tau := by
                convert childLL hs330133 hx330133 hy330133 using 1 <;> norm_num
              exact Batch0302.cell2420.sound htau (by
                simp only [Batch0302.cell2420, Batch0302.tau2420, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3301330 (by positivity) using 1 <;> norm_num)
            · have hs3301332 : InSquare (93/320) (79/320) (1/320) tau := by
                convert childUL hs330133 hx330133 hy330133 using 1 <;> norm_num
              exact Batch0302.cell2422.sound htau (by
                simp only [Batch0302.cell2422, Batch0302.tau2422, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3301332 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (39/160 : ℝ) with hy330133 | hy330133
            · have hs3301331 : InSquare (19/64) (77/320) (1/320) tau := by
                convert childLR hs330133 hx330133 hy330133 using 1 <;> norm_num
              exact Batch0302.cell2421.sound htau (by
                simp only [Batch0302.cell2421, Batch0302.tau2421, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3301331 (by positivity) using 1 <;> norm_num)
            · have hs3301333 : InSquare (19/64) (79/320) (1/320) tau := by
                convert childUR hs330133 hx330133 hy330133 using 1 <;> norm_num
              exact Batch0302.cell2423.sound htau (by
                simp only [Batch0302.cell2423, Batch0302.tau2423, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs3301333 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage3301
