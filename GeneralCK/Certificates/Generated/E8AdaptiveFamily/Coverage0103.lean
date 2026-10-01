import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0049
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0050
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0177
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0178
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0179
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0180
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0181

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0103

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-1/8) (-13/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (-1/8 : ℝ) with hx0103 | hx0103
  · rcases le_total tau.im (-13/40 : ℝ) with hy0103 | hy0103
    · have hs01030 : InSquare (-11/80) (-27/80) (1/80) tau := by
        convert childLL hs hx0103 hy0103 using 1 <;> norm_num
      rcases le_total tau.re (-11/80 : ℝ) with hx01030 | hx01030
      · rcases le_total tau.im (-27/80 : ℝ) with hy01030 | hy01030
        · have hs010300 : InSquare (-23/160) (-11/32) (1/160) tau := by
            convert childLL hs01030 hx01030 hy01030 using 1 <;> norm_num
          rcases le_total tau.re (-23/160 : ℝ) with hx010300 | hx010300
          · rcases le_total tau.im (-11/32 : ℝ) with hy010300 | hy010300
            · have hs0103000 : InSquare (-47/320) (-111/320) (1/320) tau := by
                convert childLL hs010300 hx010300 hy010300 using 1 <;> norm_num
              exact Batch0177.cell1420.sound htau (by
                simp only [Batch0177.cell1420, Batch0177.tau1420, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0103000 (by positivity) using 1 <;> norm_num)
            · have hs0103002 : InSquare (-47/320) (-109/320) (1/320) tau := by
                convert childUL hs010300 hx010300 hy010300 using 1 <;> norm_num
              exact Batch0177.cell1422.sound htau (by
                simp only [Batch0177.cell1422, Batch0177.tau1422, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0103002 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-11/32 : ℝ) with hy010300 | hy010300
            · have hs0103001 : InSquare (-9/64) (-111/320) (1/320) tau := by
                convert childLR hs010300 hx010300 hy010300 using 1 <;> norm_num
              exact Batch0177.cell1421.sound htau (by
                simp only [Batch0177.cell1421, Batch0177.tau1421, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0103001 (by positivity) using 1 <;> norm_num)
            · have hs0103003 : InSquare (-9/64) (-109/320) (1/320) tau := by
                convert childUR hs010300 hx010300 hy010300 using 1 <;> norm_num
              exact Batch0177.cell1423.sound htau (by
                simp only [Batch0177.cell1423, Batch0177.tau1423, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0103003 (by positivity) using 1 <;> norm_num)
        · have hs010302 : InSquare (-23/160) (-53/160) (1/160) tau := by
            convert childUL hs01030 hx01030 hy01030 using 1 <;> norm_num
          rcases le_total tau.re (-23/160 : ℝ) with hx010302 | hx010302
          · rcases le_total tau.im (-53/160 : ℝ) with hy010302 | hy010302
            · have hs0103020 : InSquare (-47/320) (-107/320) (1/320) tau := by
                convert childLL hs010302 hx010302 hy010302 using 1 <;> norm_num
              exact Batch0178.cell1428.sound htau (by
                simp only [Batch0178.cell1428, Batch0178.tau1428, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0103020 (by positivity) using 1 <;> norm_num)
            · have hs0103022 : InSquare (-47/320) (-21/64) (1/320) tau := by
                convert childUL hs010302 hx010302 hy010302 using 1 <;> norm_num
              exact Batch0178.cell1430.sound htau (by
                simp only [Batch0178.cell1430, Batch0178.tau1430, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0103022 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-53/160 : ℝ) with hy010302 | hy010302
            · have hs0103021 : InSquare (-9/64) (-107/320) (1/320) tau := by
                convert childLR hs010302 hx010302 hy010302 using 1 <;> norm_num
              exact Batch0178.cell1429.sound htau (by
                simp only [Batch0178.cell1429, Batch0178.tau1429, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0103021 (by positivity) using 1 <;> norm_num)
            · have hs0103023 : InSquare (-9/64) (-21/64) (1/320) tau := by
                convert childUR hs010302 hx010302 hy010302 using 1 <;> norm_num
              exact Batch0178.cell1431.sound htau (by
                simp only [Batch0178.cell1431, Batch0178.tau1431, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0103023 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-27/80 : ℝ) with hy01030 | hy01030
        · have hs010301 : InSquare (-21/160) (-11/32) (1/160) tau := by
            convert childLR hs01030 hx01030 hy01030 using 1 <;> norm_num
          rcases le_total tau.re (-21/160 : ℝ) with hx010301 | hx010301
          · rcases le_total tau.im (-11/32 : ℝ) with hy010301 | hy010301
            · have hs0103010 : InSquare (-43/320) (-111/320) (1/320) tau := by
                convert childLL hs010301 hx010301 hy010301 using 1 <;> norm_num
              exact Batch0178.cell1424.sound htau (by
                simp only [Batch0178.cell1424, Batch0178.tau1424, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0103010 (by positivity) using 1 <;> norm_num)
            · have hs0103012 : InSquare (-43/320) (-109/320) (1/320) tau := by
                convert childUL hs010301 hx010301 hy010301 using 1 <;> norm_num
              exact Batch0178.cell1426.sound htau (by
                simp only [Batch0178.cell1426, Batch0178.tau1426, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0103012 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-11/32 : ℝ) with hy010301 | hy010301
            · have hs0103011 : InSquare (-41/320) (-111/320) (1/320) tau := by
                convert childLR hs010301 hx010301 hy010301 using 1 <;> norm_num
              exact Batch0178.cell1425.sound htau (by
                simp only [Batch0178.cell1425, Batch0178.tau1425, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0103011 (by positivity) using 1 <;> norm_num)
            · have hs0103013 : InSquare (-41/320) (-109/320) (1/320) tau := by
                convert childUR hs010301 hx010301 hy010301 using 1 <;> norm_num
              exact Batch0178.cell1427.sound htau (by
                simp only [Batch0178.cell1427, Batch0178.tau1427, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0103013 (by positivity) using 1 <;> norm_num)
        · have hs010303 : InSquare (-21/160) (-53/160) (1/160) tau := by
            convert childUR hs01030 hx01030 hy01030 using 1 <;> norm_num
          rcases le_total tau.re (-21/160 : ℝ) with hx010303 | hx010303
          · rcases le_total tau.im (-53/160 : ℝ) with hy010303 | hy010303
            · have hs0103030 : InSquare (-43/320) (-107/320) (1/320) tau := by
                convert childLL hs010303 hx010303 hy010303 using 1 <;> norm_num
              exact Batch0179.cell1432.sound htau (by
                simp only [Batch0179.cell1432, Batch0179.tau1432, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0103030 (by positivity) using 1 <;> norm_num)
            · have hs0103032 : InSquare (-43/320) (-21/64) (1/320) tau := by
                convert childUL hs010303 hx010303 hy010303 using 1 <;> norm_num
              exact Batch0179.cell1434.sound htau (by
                simp only [Batch0179.cell1434, Batch0179.tau1434, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0103032 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-53/160 : ℝ) with hy010303 | hy010303
            · have hs0103031 : InSquare (-41/320) (-107/320) (1/320) tau := by
                convert childLR hs010303 hx010303 hy010303 using 1 <;> norm_num
              exact Batch0179.cell1433.sound htau (by
                simp only [Batch0179.cell1433, Batch0179.tau1433, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0103031 (by positivity) using 1 <;> norm_num)
            · have hs0103033 : InSquare (-41/320) (-21/64) (1/320) tau := by
                convert childUR hs010303 hx010303 hy010303 using 1 <;> norm_num
              exact Batch0179.cell1435.sound htau (by
                simp only [Batch0179.cell1435, Batch0179.tau1435, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0103033 (by positivity) using 1 <;> norm_num)
    · have hs01032 : InSquare (-11/80) (-5/16) (1/80) tau := by
        convert childUL hs hx0103 hy0103 using 1 <;> norm_num
      rcases le_total tau.re (-11/80 : ℝ) with hx01032 | hx01032
      · rcases le_total tau.im (-5/16 : ℝ) with hy01032 | hy01032
        · have hs010320 : InSquare (-23/160) (-51/160) (1/160) tau := by
            convert childLL hs01032 hx01032 hy01032 using 1 <;> norm_num
          rcases le_total tau.re (-23/160 : ℝ) with hx010320 | hx010320
          · rcases le_total tau.im (-51/160 : ℝ) with hy010320 | hy010320
            · have hs0103200 : InSquare (-47/320) (-103/320) (1/320) tau := by
                convert childLL hs010320 hx010320 hy010320 using 1 <;> norm_num
              exact Batch0181.cell1448.sound htau (by
                simp only [Batch0181.cell1448, Batch0181.tau1448, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0103200 (by positivity) using 1 <;> norm_num)
            · have hs0103202 : InSquare (-47/320) (-101/320) (1/320) tau := by
                convert childUL hs010320 hx010320 hy010320 using 1 <;> norm_num
              exact Batch0181.cell1450.sound htau (by
                simp only [Batch0181.cell1450, Batch0181.tau1450, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0103202 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-51/160 : ℝ) with hy010320 | hy010320
            · have hs0103201 : InSquare (-9/64) (-103/320) (1/320) tau := by
                convert childLR hs010320 hx010320 hy010320 using 1 <;> norm_num
              exact Batch0181.cell1449.sound htau (by
                simp only [Batch0181.cell1449, Batch0181.tau1449, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0103201 (by positivity) using 1 <;> norm_num)
            · have hs0103203 : InSquare (-9/64) (-101/320) (1/320) tau := by
                convert childUR hs010320 hx010320 hy010320 using 1 <;> norm_num
              exact Batch0181.cell1451.sound htau (by
                simp only [Batch0181.cell1451, Batch0181.tau1451, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0103203 (by positivity) using 1 <;> norm_num)
        · have hs010322 : InSquare (-23/160) (-49/160) (1/160) tau := by
            convert childUL hs01032 hx01032 hy01032 using 1 <;> norm_num
          exact Batch0049.cell0397.sound htau (by
            simp only [Batch0049.cell0397, Batch0049.tau0397, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs010322 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-5/16 : ℝ) with hy01032 | hy01032
        · have hs010321 : InSquare (-21/160) (-51/160) (1/160) tau := by
            convert childLR hs01032 hx01032 hy01032 using 1 <;> norm_num
          exact Batch0049.cell0396.sound htau (by
            simp only [Batch0049.cell0396, Batch0049.tau0396, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs010321 (by positivity) using 1 <;> norm_num)
        · have hs010323 : InSquare (-21/160) (-49/160) (1/160) tau := by
            convert childUR hs01032 hx01032 hy01032 using 1 <;> norm_num
          exact Batch0049.cell0398.sound htau (by
            simp only [Batch0049.cell0398, Batch0049.tau0398, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs010323 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (-13/40 : ℝ) with hy0103 | hy0103
    · have hs01031 : InSquare (-9/80) (-27/80) (1/80) tau := by
        convert childLR hs hx0103 hy0103 using 1 <;> norm_num
      rcases le_total tau.re (-9/80 : ℝ) with hx01031 | hx01031
      · rcases le_total tau.im (-27/80 : ℝ) with hy01031 | hy01031
        · have hs010310 : InSquare (-19/160) (-11/32) (1/160) tau := by
            convert childLL hs01031 hx01031 hy01031 using 1 <;> norm_num
          rcases le_total tau.re (-19/160 : ℝ) with hx010310 | hx010310
          · rcases le_total tau.im (-11/32 : ℝ) with hy010310 | hy010310
            · have hs0103100 : InSquare (-39/320) (-111/320) (1/320) tau := by
                convert childLL hs010310 hx010310 hy010310 using 1 <;> norm_num
              exact Batch0179.cell1436.sound htau (by
                simp only [Batch0179.cell1436, Batch0179.tau1436, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0103100 (by positivity) using 1 <;> norm_num)
            · have hs0103102 : InSquare (-39/320) (-109/320) (1/320) tau := by
                convert childUL hs010310 hx010310 hy010310 using 1 <;> norm_num
              exact Batch0179.cell1438.sound htau (by
                simp only [Batch0179.cell1438, Batch0179.tau1438, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0103102 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-11/32 : ℝ) with hy010310 | hy010310
            · have hs0103101 : InSquare (-37/320) (-111/320) (1/320) tau := by
                convert childLR hs010310 hx010310 hy010310 using 1 <;> norm_num
              exact Batch0179.cell1437.sound htau (by
                simp only [Batch0179.cell1437, Batch0179.tau1437, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0103101 (by positivity) using 1 <;> norm_num)
            · have hs0103103 : InSquare (-37/320) (-109/320) (1/320) tau := by
                convert childUR hs010310 hx010310 hy010310 using 1 <;> norm_num
              exact Batch0179.cell1439.sound htau (by
                simp only [Batch0179.cell1439, Batch0179.tau1439, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0103103 (by positivity) using 1 <;> norm_num)
        · have hs010312 : InSquare (-19/160) (-53/160) (1/160) tau := by
            convert childUL hs01031 hx01031 hy01031 using 1 <;> norm_num
          rcases le_total tau.re (-19/160 : ℝ) with hx010312 | hx010312
          · rcases le_total tau.im (-53/160 : ℝ) with hy010312 | hy010312
            · have hs0103120 : InSquare (-39/320) (-107/320) (1/320) tau := by
                convert childLL hs010312 hx010312 hy010312 using 1 <;> norm_num
              exact Batch0180.cell1444.sound htau (by
                simp only [Batch0180.cell1444, Batch0180.tau1444, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0103120 (by positivity) using 1 <;> norm_num)
            · have hs0103122 : InSquare (-39/320) (-21/64) (1/320) tau := by
                convert childUL hs010312 hx010312 hy010312 using 1 <;> norm_num
              exact Batch0180.cell1446.sound htau (by
                simp only [Batch0180.cell1446, Batch0180.tau1446, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0103122 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-53/160 : ℝ) with hy010312 | hy010312
            · have hs0103121 : InSquare (-37/320) (-107/320) (1/320) tau := by
                convert childLR hs010312 hx010312 hy010312 using 1 <;> norm_num
              exact Batch0180.cell1445.sound htau (by
                simp only [Batch0180.cell1445, Batch0180.tau1445, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0103121 (by positivity) using 1 <;> norm_num)
            · have hs0103123 : InSquare (-37/320) (-21/64) (1/320) tau := by
                convert childUR hs010312 hx010312 hy010312 using 1 <;> norm_num
              exact Batch0180.cell1447.sound htau (by
                simp only [Batch0180.cell1447, Batch0180.tau1447, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0103123 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-27/80 : ℝ) with hy01031 | hy01031
        · have hs010311 : InSquare (-17/160) (-11/32) (1/160) tau := by
            convert childLR hs01031 hx01031 hy01031 using 1 <;> norm_num
          rcases le_total tau.re (-17/160 : ℝ) with hx010311 | hx010311
          · rcases le_total tau.im (-11/32 : ℝ) with hy010311 | hy010311
            · have hs0103110 : InSquare (-7/64) (-111/320) (1/320) tau := by
                convert childLL hs010311 hx010311 hy010311 using 1 <;> norm_num
              exact Batch0180.cell1440.sound htau (by
                simp only [Batch0180.cell1440, Batch0180.tau1440, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0103110 (by positivity) using 1 <;> norm_num)
            · have hs0103112 : InSquare (-7/64) (-109/320) (1/320) tau := by
                convert childUL hs010311 hx010311 hy010311 using 1 <;> norm_num
              exact Batch0180.cell1442.sound htau (by
                simp only [Batch0180.cell1442, Batch0180.tau1442, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0103112 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-11/32 : ℝ) with hy010311 | hy010311
            · have hs0103111 : InSquare (-33/320) (-111/320) (1/320) tau := by
                convert childLR hs010311 hx010311 hy010311 using 1 <;> norm_num
              exact Batch0180.cell1441.sound htau (by
                simp only [Batch0180.cell1441, Batch0180.tau1441, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0103111 (by positivity) using 1 <;> norm_num)
            · have hs0103113 : InSquare (-33/320) (-109/320) (1/320) tau := by
                convert childUR hs010311 hx010311 hy010311 using 1 <;> norm_num
              exact Batch0180.cell1443.sound htau (by
                simp only [Batch0180.cell1443, Batch0180.tau1443, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0103113 (by positivity) using 1 <;> norm_num)
        · have hs010313 : InSquare (-17/160) (-53/160) (1/160) tau := by
            convert childUR hs01031 hx01031 hy01031 using 1 <;> norm_num
          exact Batch0049.cell0395.sound htau (by
            simp only [Batch0049.cell0395, Batch0049.tau0395, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs010313 (by positivity) using 1 <;> norm_num)
    · have hs01033 : InSquare (-9/80) (-5/16) (1/80) tau := by
        convert childUR hs hx0103 hy0103 using 1 <;> norm_num
      rcases le_total tau.re (-9/80 : ℝ) with hx01033 | hx01033
      · rcases le_total tau.im (-5/16 : ℝ) with hy01033 | hy01033
        · have hs010330 : InSquare (-19/160) (-51/160) (1/160) tau := by
            convert childLL hs01033 hx01033 hy01033 using 1 <;> norm_num
          exact Batch0049.cell0399.sound htau (by
            simp only [Batch0049.cell0399, Batch0049.tau0399, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs010330 (by positivity) using 1 <;> norm_num)
        · have hs010332 : InSquare (-19/160) (-49/160) (1/160) tau := by
            convert childUL hs01033 hx01033 hy01033 using 1 <;> norm_num
          exact Batch0050.cell0401.sound htau (by
            simp only [Batch0050.cell0401, Batch0050.tau0401, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs010332 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-5/16 : ℝ) with hy01033 | hy01033
        · have hs010331 : InSquare (-17/160) (-51/160) (1/160) tau := by
            convert childLR hs01033 hx01033 hy01033 using 1 <;> norm_num
          exact Batch0050.cell0400.sound htau (by
            simp only [Batch0050.cell0400, Batch0050.tau0400, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs010331 (by positivity) using 1 <;> norm_num)
        · have hs010333 : InSquare (-17/160) (-49/160) (1/160) tau := by
            convert childUR hs01033 hx01033 hy01033 using 1 <;> norm_num
          exact Batch0050.cell0402.sound htau (by
            simp only [Batch0050.cell0402, Batch0050.tau0402, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs010333 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0103
