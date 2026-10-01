import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0118
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0119
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0260
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0261
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0262
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0263
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0264

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2321

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-1/8) (13/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (-1/8 : ℝ) with hx2321 | hx2321
  · rcases le_total tau.im (13/40 : ℝ) with hy2321 | hy2321
    · have hs23210 : InSquare (-11/80) (5/16) (1/80) tau := by
        convert childLL hs hx2321 hy2321 using 1 <;> norm_num
      rcases le_total tau.re (-11/80 : ℝ) with hx23210 | hx23210
      · rcases le_total tau.im (5/16 : ℝ) with hy23210 | hy23210
        · have hs232100 : InSquare (-23/160) (49/160) (1/160) tau := by
            convert childLL hs23210 hx23210 hy23210 using 1 <;> norm_num
          exact Batch0118.cell0948.sound htau (by
            simp only [Batch0118.cell0948, Batch0118.tau0948, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs232100 (by positivity) using 1 <;> norm_num)
        · have hs232102 : InSquare (-23/160) (51/160) (1/160) tau := by
            convert childUL hs23210 hx23210 hy23210 using 1 <;> norm_num
          rcases le_total tau.re (-23/160 : ℝ) with hx232102 | hx232102
          · rcases le_total tau.im (51/160 : ℝ) with hy232102 | hy232102
            · have hs2321020 : InSquare (-47/320) (101/320) (1/320) tau := by
                convert childLL hs232102 hx232102 hy232102 using 1 <;> norm_num
              exact Batch0260.cell2081.sound htau (by
                simp only [Batch0260.cell2081, Batch0260.tau2081, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2321020 (by positivity) using 1 <;> norm_num)
            · have hs2321022 : InSquare (-47/320) (103/320) (1/320) tau := by
                convert childUL hs232102 hx232102 hy232102 using 1 <;> norm_num
              exact Batch0260.cell2083.sound htau (by
                simp only [Batch0260.cell2083, Batch0260.tau2083, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2321022 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (51/160 : ℝ) with hy232102 | hy232102
            · have hs2321021 : InSquare (-9/64) (101/320) (1/320) tau := by
                convert childLR hs232102 hx232102 hy232102 using 1 <;> norm_num
              exact Batch0260.cell2082.sound htau (by
                simp only [Batch0260.cell2082, Batch0260.tau2082, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2321021 (by positivity) using 1 <;> norm_num)
            · have hs2321023 : InSquare (-9/64) (103/320) (1/320) tau := by
                convert childUR hs232102 hx232102 hy232102 using 1 <;> norm_num
              exact Batch0260.cell2084.sound htau (by
                simp only [Batch0260.cell2084, Batch0260.tau2084, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2321023 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (5/16 : ℝ) with hy23210 | hy23210
        · have hs232101 : InSquare (-21/160) (49/160) (1/160) tau := by
            convert childLR hs23210 hx23210 hy23210 using 1 <;> norm_num
          exact Batch0118.cell0949.sound htau (by
            simp only [Batch0118.cell0949, Batch0118.tau0949, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs232101 (by positivity) using 1 <;> norm_num)
        · have hs232103 : InSquare (-21/160) (51/160) (1/160) tau := by
            convert childUR hs23210 hx23210 hy23210 using 1 <;> norm_num
          exact Batch0118.cell0950.sound htau (by
            simp only [Batch0118.cell0950, Batch0118.tau0950, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs232103 (by positivity) using 1 <;> norm_num)
    · have hs23212 : InSquare (-11/80) (27/80) (1/80) tau := by
        convert childUL hs hx2321 hy2321 using 1 <;> norm_num
      rcases le_total tau.re (-11/80 : ℝ) with hx23212 | hx23212
      · rcases le_total tau.im (27/80 : ℝ) with hy23212 | hy23212
        · have hs232120 : InSquare (-23/160) (53/160) (1/160) tau := by
            convert childLL hs23212 hx23212 hy23212 using 1 <;> norm_num
          rcases le_total tau.re (-23/160 : ℝ) with hx232120 | hx232120
          · rcases le_total tau.im (53/160 : ℝ) with hy232120 | hy232120
            · have hs2321200 : InSquare (-47/320) (21/64) (1/320) tau := by
                convert childLL hs232120 hx232120 hy232120 using 1 <;> norm_num
              exact Batch0260.cell2085.sound htau (by
                simp only [Batch0260.cell2085, Batch0260.tau2085, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2321200 (by positivity) using 1 <;> norm_num)
            · have hs2321202 : InSquare (-47/320) (107/320) (1/320) tau := by
                convert childUL hs232120 hx232120 hy232120 using 1 <;> norm_num
              exact Batch0260.cell2087.sound htau (by
                simp only [Batch0260.cell2087, Batch0260.tau2087, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2321202 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (53/160 : ℝ) with hy232120 | hy232120
            · have hs2321201 : InSquare (-9/64) (21/64) (1/320) tau := by
                convert childLR hs232120 hx232120 hy232120 using 1 <;> norm_num
              exact Batch0260.cell2086.sound htau (by
                simp only [Batch0260.cell2086, Batch0260.tau2086, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2321201 (by positivity) using 1 <;> norm_num)
            · have hs2321203 : InSquare (-9/64) (107/320) (1/320) tau := by
                convert childUR hs232120 hx232120 hy232120 using 1 <;> norm_num
              exact Batch0261.cell2088.sound htau (by
                simp only [Batch0261.cell2088, Batch0261.tau2088, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2321203 (by positivity) using 1 <;> norm_num)
        · have hs232122 : InSquare (-23/160) (11/32) (1/160) tau := by
            convert childUL hs23212 hx23212 hy23212 using 1 <;> norm_num
          rcases le_total tau.re (-23/160 : ℝ) with hx232122 | hx232122
          · rcases le_total tau.im (11/32 : ℝ) with hy232122 | hy232122
            · have hs2321220 : InSquare (-47/320) (109/320) (1/320) tau := by
                convert childLL hs232122 hx232122 hy232122 using 1 <;> norm_num
              exact Batch0261.cell2093.sound htau (by
                simp only [Batch0261.cell2093, Batch0261.tau2093, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2321220 (by positivity) using 1 <;> norm_num)
            · have hs2321222 : InSquare (-47/320) (111/320) (1/320) tau := by
                convert childUL hs232122 hx232122 hy232122 using 1 <;> norm_num
              exact Batch0261.cell2095.sound htau (by
                simp only [Batch0261.cell2095, Batch0261.tau2095, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2321222 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (11/32 : ℝ) with hy232122 | hy232122
            · have hs2321221 : InSquare (-9/64) (109/320) (1/320) tau := by
                convert childLR hs232122 hx232122 hy232122 using 1 <;> norm_num
              exact Batch0261.cell2094.sound htau (by
                simp only [Batch0261.cell2094, Batch0261.tau2094, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2321221 (by positivity) using 1 <;> norm_num)
            · have hs2321223 : InSquare (-9/64) (111/320) (1/320) tau := by
                convert childUR hs232122 hx232122 hy232122 using 1 <;> norm_num
              exact Batch0262.cell2096.sound htau (by
                simp only [Batch0262.cell2096, Batch0262.tau2096, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2321223 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (27/80 : ℝ) with hy23212 | hy23212
        · have hs232121 : InSquare (-21/160) (53/160) (1/160) tau := by
            convert childLR hs23212 hx23212 hy23212 using 1 <;> norm_num
          rcases le_total tau.re (-21/160 : ℝ) with hx232121 | hx232121
          · rcases le_total tau.im (53/160 : ℝ) with hy232121 | hy232121
            · have hs2321210 : InSquare (-43/320) (21/64) (1/320) tau := by
                convert childLL hs232121 hx232121 hy232121 using 1 <;> norm_num
              exact Batch0261.cell2089.sound htau (by
                simp only [Batch0261.cell2089, Batch0261.tau2089, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2321210 (by positivity) using 1 <;> norm_num)
            · have hs2321212 : InSquare (-43/320) (107/320) (1/320) tau := by
                convert childUL hs232121 hx232121 hy232121 using 1 <;> norm_num
              exact Batch0261.cell2091.sound htau (by
                simp only [Batch0261.cell2091, Batch0261.tau2091, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2321212 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (53/160 : ℝ) with hy232121 | hy232121
            · have hs2321211 : InSquare (-41/320) (21/64) (1/320) tau := by
                convert childLR hs232121 hx232121 hy232121 using 1 <;> norm_num
              exact Batch0261.cell2090.sound htau (by
                simp only [Batch0261.cell2090, Batch0261.tau2090, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2321211 (by positivity) using 1 <;> norm_num)
            · have hs2321213 : InSquare (-41/320) (107/320) (1/320) tau := by
                convert childUR hs232121 hx232121 hy232121 using 1 <;> norm_num
              exact Batch0261.cell2092.sound htau (by
                simp only [Batch0261.cell2092, Batch0261.tau2092, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2321213 (by positivity) using 1 <;> norm_num)
        · have hs232123 : InSquare (-21/160) (11/32) (1/160) tau := by
            convert childUR hs23212 hx23212 hy23212 using 1 <;> norm_num
          rcases le_total tau.re (-21/160 : ℝ) with hx232123 | hx232123
          · rcases le_total tau.im (11/32 : ℝ) with hy232123 | hy232123
            · have hs2321230 : InSquare (-43/320) (109/320) (1/320) tau := by
                convert childLL hs232123 hx232123 hy232123 using 1 <;> norm_num
              exact Batch0262.cell2097.sound htau (by
                simp only [Batch0262.cell2097, Batch0262.tau2097, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2321230 (by positivity) using 1 <;> norm_num)
            · have hs2321232 : InSquare (-43/320) (111/320) (1/320) tau := by
                convert childUL hs232123 hx232123 hy232123 using 1 <;> norm_num
              exact Batch0262.cell2099.sound htau (by
                simp only [Batch0262.cell2099, Batch0262.tau2099, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2321232 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (11/32 : ℝ) with hy232123 | hy232123
            · have hs2321231 : InSquare (-41/320) (109/320) (1/320) tau := by
                convert childLR hs232123 hx232123 hy232123 using 1 <;> norm_num
              exact Batch0262.cell2098.sound htau (by
                simp only [Batch0262.cell2098, Batch0262.tau2098, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2321231 (by positivity) using 1 <;> norm_num)
            · have hs2321233 : InSquare (-41/320) (111/320) (1/320) tau := by
                convert childUR hs232123 hx232123 hy232123 using 1 <;> norm_num
              exact Batch0262.cell2100.sound htau (by
                simp only [Batch0262.cell2100, Batch0262.tau2100, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2321233 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (13/40 : ℝ) with hy2321 | hy2321
    · have hs23211 : InSquare (-9/80) (5/16) (1/80) tau := by
        convert childLR hs hx2321 hy2321 using 1 <;> norm_num
      rcases le_total tau.re (-9/80 : ℝ) with hx23211 | hx23211
      · rcases le_total tau.im (5/16 : ℝ) with hy23211 | hy23211
        · have hs232110 : InSquare (-19/160) (49/160) (1/160) tau := by
            convert childLL hs23211 hx23211 hy23211 using 1 <;> norm_num
          exact Batch0118.cell0951.sound htau (by
            simp only [Batch0118.cell0951, Batch0118.tau0951, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs232110 (by positivity) using 1 <;> norm_num)
        · have hs232112 : InSquare (-19/160) (51/160) (1/160) tau := by
            convert childUL hs23211 hx23211 hy23211 using 1 <;> norm_num
          exact Batch0119.cell0953.sound htau (by
            simp only [Batch0119.cell0953, Batch0119.tau0953, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs232112 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (5/16 : ℝ) with hy23211 | hy23211
        · have hs232111 : InSquare (-17/160) (49/160) (1/160) tau := by
            convert childLR hs23211 hx23211 hy23211 using 1 <;> norm_num
          exact Batch0119.cell0952.sound htau (by
            simp only [Batch0119.cell0952, Batch0119.tau0952, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs232111 (by positivity) using 1 <;> norm_num)
        · have hs232113 : InSquare (-17/160) (51/160) (1/160) tau := by
            convert childUR hs23211 hx23211 hy23211 using 1 <;> norm_num
          exact Batch0119.cell0954.sound htau (by
            simp only [Batch0119.cell0954, Batch0119.tau0954, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs232113 (by positivity) using 1 <;> norm_num)
    · have hs23213 : InSquare (-9/80) (27/80) (1/80) tau := by
        convert childUR hs hx2321 hy2321 using 1 <;> norm_num
      rcases le_total tau.re (-9/80 : ℝ) with hx23213 | hx23213
      · rcases le_total tau.im (27/80 : ℝ) with hy23213 | hy23213
        · have hs232130 : InSquare (-19/160) (53/160) (1/160) tau := by
            convert childLL hs23213 hx23213 hy23213 using 1 <;> norm_num
          rcases le_total tau.re (-19/160 : ℝ) with hx232130 | hx232130
          · rcases le_total tau.im (53/160 : ℝ) with hy232130 | hy232130
            · have hs2321300 : InSquare (-39/320) (21/64) (1/320) tau := by
                convert childLL hs232130 hx232130 hy232130 using 1 <;> norm_num
              exact Batch0262.cell2101.sound htau (by
                simp only [Batch0262.cell2101, Batch0262.tau2101, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2321300 (by positivity) using 1 <;> norm_num)
            · have hs2321302 : InSquare (-39/320) (107/320) (1/320) tau := by
                convert childUL hs232130 hx232130 hy232130 using 1 <;> norm_num
              exact Batch0262.cell2103.sound htau (by
                simp only [Batch0262.cell2103, Batch0262.tau2103, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2321302 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (53/160 : ℝ) with hy232130 | hy232130
            · have hs2321301 : InSquare (-37/320) (21/64) (1/320) tau := by
                convert childLR hs232130 hx232130 hy232130 using 1 <;> norm_num
              exact Batch0262.cell2102.sound htau (by
                simp only [Batch0262.cell2102, Batch0262.tau2102, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2321301 (by positivity) using 1 <;> norm_num)
            · have hs2321303 : InSquare (-37/320) (107/320) (1/320) tau := by
                convert childUR hs232130 hx232130 hy232130 using 1 <;> norm_num
              exact Batch0263.cell2104.sound htau (by
                simp only [Batch0263.cell2104, Batch0263.tau2104, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2321303 (by positivity) using 1 <;> norm_num)
        · have hs232132 : InSquare (-19/160) (11/32) (1/160) tau := by
            convert childUL hs23213 hx23213 hy23213 using 1 <;> norm_num
          rcases le_total tau.re (-19/160 : ℝ) with hx232132 | hx232132
          · rcases le_total tau.im (11/32 : ℝ) with hy232132 | hy232132
            · have hs2321320 : InSquare (-39/320) (109/320) (1/320) tau := by
                convert childLL hs232132 hx232132 hy232132 using 1 <;> norm_num
              exact Batch0263.cell2105.sound htau (by
                simp only [Batch0263.cell2105, Batch0263.tau2105, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2321320 (by positivity) using 1 <;> norm_num)
            · have hs2321322 : InSquare (-39/320) (111/320) (1/320) tau := by
                convert childUL hs232132 hx232132 hy232132 using 1 <;> norm_num
              exact Batch0263.cell2107.sound htau (by
                simp only [Batch0263.cell2107, Batch0263.tau2107, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2321322 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (11/32 : ℝ) with hy232132 | hy232132
            · have hs2321321 : InSquare (-37/320) (109/320) (1/320) tau := by
                convert childLR hs232132 hx232132 hy232132 using 1 <;> norm_num
              exact Batch0263.cell2106.sound htau (by
                simp only [Batch0263.cell2106, Batch0263.tau2106, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2321321 (by positivity) using 1 <;> norm_num)
            · have hs2321323 : InSquare (-37/320) (111/320) (1/320) tau := by
                convert childUR hs232132 hx232132 hy232132 using 1 <;> norm_num
              exact Batch0263.cell2108.sound htau (by
                simp only [Batch0263.cell2108, Batch0263.tau2108, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2321323 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (27/80 : ℝ) with hy23213 | hy23213
        · have hs232131 : InSquare (-17/160) (53/160) (1/160) tau := by
            convert childLR hs23213 hx23213 hy23213 using 1 <;> norm_num
          exact Batch0119.cell0955.sound htau (by
            simp only [Batch0119.cell0955, Batch0119.tau0955, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs232131 (by positivity) using 1 <;> norm_num)
        · have hs232133 : InSquare (-17/160) (11/32) (1/160) tau := by
            convert childUR hs23213 hx23213 hy23213 using 1 <;> norm_num
          rcases le_total tau.re (-17/160 : ℝ) with hx232133 | hx232133
          · rcases le_total tau.im (11/32 : ℝ) with hy232133 | hy232133
            · have hs2321330 : InSquare (-7/64) (109/320) (1/320) tau := by
                convert childLL hs232133 hx232133 hy232133 using 1 <;> norm_num
              exact Batch0263.cell2109.sound htau (by
                simp only [Batch0263.cell2109, Batch0263.tau2109, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2321330 (by positivity) using 1 <;> norm_num)
            · have hs2321332 : InSquare (-7/64) (111/320) (1/320) tau := by
                convert childUL hs232133 hx232133 hy232133 using 1 <;> norm_num
              exact Batch0263.cell2111.sound htau (by
                simp only [Batch0263.cell2111, Batch0263.tau2111, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2321332 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (11/32 : ℝ) with hy232133 | hy232133
            · have hs2321331 : InSquare (-33/320) (109/320) (1/320) tau := by
                convert childLR hs232133 hx232133 hy232133 using 1 <;> norm_num
              exact Batch0263.cell2110.sound htau (by
                simp only [Batch0263.cell2110, Batch0263.tau2110, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2321331 (by positivity) using 1 <;> norm_num)
            · have hs2321333 : InSquare (-33/320) (111/320) (1/320) tau := by
                convert childUR hs232133 hx232133 hy232133 using 1 <;> norm_num
              exact Batch0264.cell2112.sound htau (by
                simp only [Batch0264.cell2112, Batch0264.tau2112, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2321333 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2321
