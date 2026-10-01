import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0044
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0045
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0164
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0165
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0166
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0167

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0031

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-9/40) (-11/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (-9/40 : ℝ) with hx0031 | hx0031
  · rcases le_total tau.im (-11/40 : ℝ) with hy0031 | hy0031
    · have hs00310 : InSquare (-19/80) (-23/80) (1/80) tau := by
        convert childLL hs hx0031 hy0031 using 1 <;> norm_num
      rcases le_total tau.re (-19/80 : ℝ) with hx00310 | hx00310
      · rcases le_total tau.im (-23/80 : ℝ) with hy00310 | hy00310
        · have hs003100 : InSquare (-39/160) (-47/160) (1/160) tau := by
            convert childLL hs00310 hx00310 hy00310 using 1 <;> norm_num
          rcases le_total tau.re (-39/160 : ℝ) with hx003100 | hx003100
          · rcases le_total tau.im (-47/160 : ℝ) with hy003100 | hy003100
            · have hs0031000 : InSquare (-79/320) (-19/64) (1/320) tau := by
                convert childLL hs003100 hx003100 hy003100 using 1 <;> norm_num
              exact Batch0164.cell1316.sound htau (by
                simp only [Batch0164.cell1316, Batch0164.tau1316, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0031000 (by positivity) using 1 <;> norm_num)
            · have hs0031002 : InSquare (-79/320) (-93/320) (1/320) tau := by
                convert childUL hs003100 hx003100 hy003100 using 1 <;> norm_num
              exact Batch0164.cell1318.sound htau (by
                simp only [Batch0164.cell1318, Batch0164.tau1318, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0031002 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-47/160 : ℝ) with hy003100 | hy003100
            · have hs0031001 : InSquare (-77/320) (-19/64) (1/320) tau := by
                convert childLR hs003100 hx003100 hy003100 using 1 <;> norm_num
              exact Batch0164.cell1317.sound htau (by
                simp only [Batch0164.cell1317, Batch0164.tau1317, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0031001 (by positivity) using 1 <;> norm_num)
            · have hs0031003 : InSquare (-77/320) (-93/320) (1/320) tau := by
                convert childUR hs003100 hx003100 hy003100 using 1 <;> norm_num
              exact Batch0164.cell1319.sound htau (by
                simp only [Batch0164.cell1319, Batch0164.tau1319, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0031003 (by positivity) using 1 <;> norm_num)
        · have hs003102 : InSquare (-39/160) (-9/32) (1/160) tau := by
            convert childUL hs00310 hx00310 hy00310 using 1 <;> norm_num
          rcases le_total tau.re (-39/160 : ℝ) with hx003102 | hx003102
          · rcases le_total tau.im (-9/32 : ℝ) with hy003102 | hy003102
            · have hs0031020 : InSquare (-79/320) (-91/320) (1/320) tau := by
                convert childLL hs003102 hx003102 hy003102 using 1 <;> norm_num
              exact Batch0165.cell1324.sound htau (by
                simp only [Batch0165.cell1324, Batch0165.tau1324, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0031020 (by positivity) using 1 <;> norm_num)
            · have hs0031022 : InSquare (-79/320) (-89/320) (1/320) tau := by
                convert childUL hs003102 hx003102 hy003102 using 1 <;> norm_num
              exact Batch0165.cell1326.sound htau (by
                simp only [Batch0165.cell1326, Batch0165.tau1326, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0031022 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-9/32 : ℝ) with hy003102 | hy003102
            · have hs0031021 : InSquare (-77/320) (-91/320) (1/320) tau := by
                convert childLR hs003102 hx003102 hy003102 using 1 <;> norm_num
              exact Batch0165.cell1325.sound htau (by
                simp only [Batch0165.cell1325, Batch0165.tau1325, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0031021 (by positivity) using 1 <;> norm_num)
            · have hs0031023 : InSquare (-77/320) (-89/320) (1/320) tau := by
                convert childUR hs003102 hx003102 hy003102 using 1 <;> norm_num
              exact Batch0165.cell1327.sound htau (by
                simp only [Batch0165.cell1327, Batch0165.tau1327, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0031023 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-23/80 : ℝ) with hy00310 | hy00310
        · have hs003101 : InSquare (-37/160) (-47/160) (1/160) tau := by
            convert childLR hs00310 hx00310 hy00310 using 1 <;> norm_num
          rcases le_total tau.re (-37/160 : ℝ) with hx003101 | hx003101
          · rcases le_total tau.im (-47/160 : ℝ) with hy003101 | hy003101
            · have hs0031010 : InSquare (-15/64) (-19/64) (1/320) tau := by
                convert childLL hs003101 hx003101 hy003101 using 1 <;> norm_num
              exact Batch0165.cell1320.sound htau (by
                simp only [Batch0165.cell1320, Batch0165.tau1320, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0031010 (by positivity) using 1 <;> norm_num)
            · have hs0031012 : InSquare (-15/64) (-93/320) (1/320) tau := by
                convert childUL hs003101 hx003101 hy003101 using 1 <;> norm_num
              exact Batch0165.cell1322.sound htau (by
                simp only [Batch0165.cell1322, Batch0165.tau1322, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0031012 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-47/160 : ℝ) with hy003101 | hy003101
            · have hs0031011 : InSquare (-73/320) (-19/64) (1/320) tau := by
                convert childLR hs003101 hx003101 hy003101 using 1 <;> norm_num
              exact Batch0165.cell1321.sound htau (by
                simp only [Batch0165.cell1321, Batch0165.tau1321, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0031011 (by positivity) using 1 <;> norm_num)
            · have hs0031013 : InSquare (-73/320) (-93/320) (1/320) tau := by
                convert childUR hs003101 hx003101 hy003101 using 1 <;> norm_num
              exact Batch0165.cell1323.sound htau (by
                simp only [Batch0165.cell1323, Batch0165.tau1323, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0031013 (by positivity) using 1 <;> norm_num)
        · have hs003103 : InSquare (-37/160) (-9/32) (1/160) tau := by
            convert childUR hs00310 hx00310 hy00310 using 1 <;> norm_num
          rcases le_total tau.re (-37/160 : ℝ) with hx003103 | hx003103
          · rcases le_total tau.im (-9/32 : ℝ) with hy003103 | hy003103
            · have hs0031030 : InSquare (-15/64) (-91/320) (1/320) tau := by
                convert childLL hs003103 hx003103 hy003103 using 1 <;> norm_num
              exact Batch0166.cell1328.sound htau (by
                simp only [Batch0166.cell1328, Batch0166.tau1328, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0031030 (by positivity) using 1 <;> norm_num)
            · have hs0031032 : InSquare (-15/64) (-89/320) (1/320) tau := by
                convert childUL hs003103 hx003103 hy003103 using 1 <;> norm_num
              exact Batch0166.cell1330.sound htau (by
                simp only [Batch0166.cell1330, Batch0166.tau1330, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0031032 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-9/32 : ℝ) with hy003103 | hy003103
            · have hs0031031 : InSquare (-73/320) (-91/320) (1/320) tau := by
                convert childLR hs003103 hx003103 hy003103 using 1 <;> norm_num
              exact Batch0166.cell1329.sound htau (by
                simp only [Batch0166.cell1329, Batch0166.tau1329, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0031031 (by positivity) using 1 <;> norm_num)
            · have hs0031033 : InSquare (-73/320) (-89/320) (1/320) tau := by
                convert childUR hs003103 hx003103 hy003103 using 1 <;> norm_num
              exact Batch0166.cell1331.sound htau (by
                simp only [Batch0166.cell1331, Batch0166.tau1331, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0031033 (by positivity) using 1 <;> norm_num)
    · have hs00312 : InSquare (-19/80) (-21/80) (1/80) tau := by
        convert childUL hs hx0031 hy0031 using 1 <;> norm_num
      rcases le_total tau.re (-19/80 : ℝ) with hx00312 | hx00312
      · rcases le_total tau.im (-21/80 : ℝ) with hy00312 | hy00312
        · have hs003120 : InSquare (-39/160) (-43/160) (1/160) tau := by
            convert childLL hs00312 hx00312 hy00312 using 1 <;> norm_num
          exact Batch0044.cell0354.sound htau (by
            simp only [Batch0044.cell0354, Batch0044.tau0354, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs003120 (by positivity) using 1 <;> norm_num)
        · have hs003122 : InSquare (-39/160) (-41/160) (1/160) tau := by
            convert childUL hs00312 hx00312 hy00312 using 1 <;> norm_num
          exact Batch0044.cell0356.sound htau (by
            simp only [Batch0044.cell0356, Batch0044.tau0356, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs003122 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-21/80 : ℝ) with hy00312 | hy00312
        · have hs003121 : InSquare (-37/160) (-43/160) (1/160) tau := by
            convert childLR hs00312 hx00312 hy00312 using 1 <;> norm_num
          exact Batch0044.cell0355.sound htau (by
            simp only [Batch0044.cell0355, Batch0044.tau0355, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs003121 (by positivity) using 1 <;> norm_num)
        · have hs003123 : InSquare (-37/160) (-41/160) (1/160) tau := by
            convert childUR hs00312 hx00312 hy00312 using 1 <;> norm_num
          exact Batch0044.cell0357.sound htau (by
            simp only [Batch0044.cell0357, Batch0044.tau0357, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs003123 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (-11/40 : ℝ) with hy0031 | hy0031
    · have hs00311 : InSquare (-17/80) (-23/80) (1/80) tau := by
        convert childLR hs hx0031 hy0031 using 1 <;> norm_num
      rcases le_total tau.re (-17/80 : ℝ) with hx00311 | hx00311
      · rcases le_total tau.im (-23/80 : ℝ) with hy00311 | hy00311
        · have hs003110 : InSquare (-7/32) (-47/160) (1/160) tau := by
            convert childLL hs00311 hx00311 hy00311 using 1 <;> norm_num
          rcases le_total tau.re (-7/32 : ℝ) with hx003110 | hx003110
          · rcases le_total tau.im (-47/160 : ℝ) with hy003110 | hy003110
            · have hs0031100 : InSquare (-71/320) (-19/64) (1/320) tau := by
                convert childLL hs003110 hx003110 hy003110 using 1 <;> norm_num
              exact Batch0166.cell1332.sound htau (by
                simp only [Batch0166.cell1332, Batch0166.tau1332, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0031100 (by positivity) using 1 <;> norm_num)
            · have hs0031102 : InSquare (-71/320) (-93/320) (1/320) tau := by
                convert childUL hs003110 hx003110 hy003110 using 1 <;> norm_num
              exact Batch0166.cell1334.sound htau (by
                simp only [Batch0166.cell1334, Batch0166.tau1334, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0031102 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-47/160 : ℝ) with hy003110 | hy003110
            · have hs0031101 : InSquare (-69/320) (-19/64) (1/320) tau := by
                convert childLR hs003110 hx003110 hy003110 using 1 <;> norm_num
              exact Batch0166.cell1333.sound htau (by
                simp only [Batch0166.cell1333, Batch0166.tau1333, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0031101 (by positivity) using 1 <;> norm_num)
            · have hs0031103 : InSquare (-69/320) (-93/320) (1/320) tau := by
                convert childUR hs003110 hx003110 hy003110 using 1 <;> norm_num
              exact Batch0166.cell1335.sound htau (by
                simp only [Batch0166.cell1335, Batch0166.tau1335, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0031103 (by positivity) using 1 <;> norm_num)
        · have hs003112 : InSquare (-7/32) (-9/32) (1/160) tau := by
            convert childUL hs00311 hx00311 hy00311 using 1 <;> norm_num
          exact Batch0044.cell0352.sound htau (by
            simp only [Batch0044.cell0352, Batch0044.tau0352, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs003112 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-23/80 : ℝ) with hy00311 | hy00311
        · have hs003111 : InSquare (-33/160) (-47/160) (1/160) tau := by
            convert childLR hs00311 hx00311 hy00311 using 1 <;> norm_num
          rcases le_total tau.re (-33/160 : ℝ) with hx003111 | hx003111
          · rcases le_total tau.im (-47/160 : ℝ) with hy003111 | hy003111
            · have hs0031110 : InSquare (-67/320) (-19/64) (1/320) tau := by
                convert childLL hs003111 hx003111 hy003111 using 1 <;> norm_num
              exact Batch0167.cell1336.sound htau (by
                simp only [Batch0167.cell1336, Batch0167.tau1336, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0031110 (by positivity) using 1 <;> norm_num)
            · have hs0031112 : InSquare (-67/320) (-93/320) (1/320) tau := by
                convert childUL hs003111 hx003111 hy003111 using 1 <;> norm_num
              exact Batch0167.cell1338.sound htau (by
                simp only [Batch0167.cell1338, Batch0167.tau1338, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0031112 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (-47/160 : ℝ) with hy003111 | hy003111
            · have hs0031111 : InSquare (-13/64) (-19/64) (1/320) tau := by
                convert childLR hs003111 hx003111 hy003111 using 1 <;> norm_num
              exact Batch0167.cell1337.sound htau (by
                simp only [Batch0167.cell1337, Batch0167.tau1337, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0031111 (by positivity) using 1 <;> norm_num)
            · have hs0031113 : InSquare (-13/64) (-93/320) (1/320) tau := by
                convert childUR hs003111 hx003111 hy003111 using 1 <;> norm_num
              exact Batch0167.cell1339.sound htau (by
                simp only [Batch0167.cell1339, Batch0167.tau1339, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs0031113 (by positivity) using 1 <;> norm_num)
        · have hs003113 : InSquare (-33/160) (-9/32) (1/160) tau := by
            convert childUR hs00311 hx00311 hy00311 using 1 <;> norm_num
          exact Batch0044.cell0353.sound htau (by
            simp only [Batch0044.cell0353, Batch0044.tau0353, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs003113 (by positivity) using 1 <;> norm_num)
    · have hs00313 : InSquare (-17/80) (-21/80) (1/80) tau := by
        convert childUR hs hx0031 hy0031 using 1 <;> norm_num
      rcases le_total tau.re (-17/80 : ℝ) with hx00313 | hx00313
      · rcases le_total tau.im (-21/80 : ℝ) with hy00313 | hy00313
        · have hs003130 : InSquare (-7/32) (-43/160) (1/160) tau := by
            convert childLL hs00313 hx00313 hy00313 using 1 <;> norm_num
          exact Batch0044.cell0358.sound htau (by
            simp only [Batch0044.cell0358, Batch0044.tau0358, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs003130 (by positivity) using 1 <;> norm_num)
        · have hs003132 : InSquare (-7/32) (-41/160) (1/160) tau := by
            convert childUL hs00313 hx00313 hy00313 using 1 <;> norm_num
          exact Batch0045.cell0360.sound htau (by
            simp only [Batch0045.cell0360, Batch0045.tau0360, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs003132 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (-21/80 : ℝ) with hy00313 | hy00313
        · have hs003131 : InSquare (-33/160) (-43/160) (1/160) tau := by
            convert childLR hs00313 hx00313 hy00313 using 1 <;> norm_num
          exact Batch0044.cell0359.sound htau (by
            simp only [Batch0044.cell0359, Batch0044.tau0359, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs003131 (by positivity) using 1 <;> norm_num)
        · have hs003133 : InSquare (-33/160) (-41/160) (1/160) tau := by
            convert childUR hs00313 hx00313 hy00313 using 1 <;> norm_num
          exact Batch0045.cell0361.sound htau (by
            simp only [Batch0045.cell0361, Batch0045.tau0361, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs003133 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage0031
