import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0119
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0120
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0121
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0266
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0267
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0268

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2330

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-3/40) (13/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (-3/40 : ℝ) with hx2330 | hx2330
  · rcases le_total tau.im (13/40 : ℝ) with hy2330 | hy2330
    · have hs23300 : InSquare (-7/80) (5/16) (1/80) tau := by
        convert childLL hs hx2330 hy2330 using 1 <;> norm_num
      rcases le_total tau.re (-7/80 : ℝ) with hx23300 | hx23300
      · rcases le_total tau.im (5/16 : ℝ) with hy23300 | hy23300
        · have hs233000 : InSquare (-3/32) (49/160) (1/160) tau := by
            convert childLL hs23300 hx23300 hy23300 using 1 <;> norm_num
          exact Batch0119.cell0956.sound htau (by
            simp only [Batch0119.cell0956, Batch0119.tau0956, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs233000 (by positivity) using 1 <;> norm_num)
        · have hs233002 : InSquare (-3/32) (51/160) (1/160) tau := by
            convert childUL hs23300 hx23300 hy23300 using 1 <;> norm_num
          exact Batch0119.cell0958.sound htau (by
            simp only [Batch0119.cell0958, Batch0119.tau0958, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs233002 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (5/16 : ℝ) with hy23300 | hy23300
        · have hs233001 : InSquare (-13/160) (49/160) (1/160) tau := by
            convert childLR hs23300 hx23300 hy23300 using 1 <;> norm_num
          exact Batch0119.cell0957.sound htau (by
            simp only [Batch0119.cell0957, Batch0119.tau0957, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs233001 (by positivity) using 1 <;> norm_num)
        · have hs233003 : InSquare (-13/160) (51/160) (1/160) tau := by
            convert childUR hs23300 hx23300 hy23300 using 1 <;> norm_num
          exact Batch0119.cell0959.sound htau (by
            simp only [Batch0119.cell0959, Batch0119.tau0959, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs233003 (by positivity) using 1 <;> norm_num)
    · have hs23302 : InSquare (-7/80) (27/80) (1/80) tau := by
        convert childUL hs hx2330 hy2330 using 1 <;> norm_num
      rcases le_total tau.re (-7/80 : ℝ) with hx23302 | hx23302
      · rcases le_total tau.im (27/80 : ℝ) with hy23302 | hy23302
        · have hs233020 : InSquare (-3/32) (53/160) (1/160) tau := by
            convert childLL hs23302 hx23302 hy23302 using 1 <;> norm_num
          exact Batch0120.cell0964.sound htau (by
            simp only [Batch0120.cell0964, Batch0120.tau0964, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs233020 (by positivity) using 1 <;> norm_num)
        · have hs233022 : InSquare (-3/32) (11/32) (1/160) tau := by
            convert childUL hs23302 hx23302 hy23302 using 1 <;> norm_num
          rcases le_total tau.re (-3/32 : ℝ) with hx233022 | hx233022
          · rcases le_total tau.im (11/32 : ℝ) with hy233022 | hy233022
            · have hs2330220 : InSquare (-31/320) (109/320) (1/320) tau := by
                convert childLL hs233022 hx233022 hy233022 using 1 <;> norm_num
              exact Batch0266.cell2135.sound htau (by
                simp only [Batch0266.cell2135, Batch0266.tau2135, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2330220 (by positivity) using 1 <;> norm_num)
            · have hs2330222 : InSquare (-31/320) (111/320) (1/320) tau := by
                convert childUL hs233022 hx233022 hy233022 using 1 <;> norm_num
              exact Batch0267.cell2137.sound htau (by
                simp only [Batch0267.cell2137, Batch0267.tau2137, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2330222 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (11/32 : ℝ) with hy233022 | hy233022
            · have hs2330221 : InSquare (-29/320) (109/320) (1/320) tau := by
                convert childLR hs233022 hx233022 hy233022 using 1 <;> norm_num
              exact Batch0267.cell2136.sound htau (by
                simp only [Batch0267.cell2136, Batch0267.tau2136, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2330221 (by positivity) using 1 <;> norm_num)
            · have hs2330223 : InSquare (-29/320) (111/320) (1/320) tau := by
                convert childUR hs233022 hx233022 hy233022 using 1 <;> norm_num
              exact Batch0267.cell2138.sound htau (by
                simp only [Batch0267.cell2138, Batch0267.tau2138, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2330223 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (27/80 : ℝ) with hy23302 | hy23302
        · have hs233021 : InSquare (-13/160) (53/160) (1/160) tau := by
            convert childLR hs23302 hx23302 hy23302 using 1 <;> norm_num
          exact Batch0120.cell0965.sound htau (by
            simp only [Batch0120.cell0965, Batch0120.tau0965, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs233021 (by positivity) using 1 <;> norm_num)
        · have hs233023 : InSquare (-13/160) (11/32) (1/160) tau := by
            convert childUR hs23302 hx23302 hy23302 using 1 <;> norm_num
          rcases le_total tau.re (-13/160 : ℝ) with hx233023 | hx233023
          · rcases le_total tau.im (11/32 : ℝ) with hy233023 | hy233023
            · have hs2330230 : InSquare (-27/320) (109/320) (1/320) tau := by
                convert childLL hs233023 hx233023 hy233023 using 1 <;> norm_num
              exact Batch0267.cell2139.sound htau (by
                simp only [Batch0267.cell2139, Batch0267.tau2139, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2330230 (by positivity) using 1 <;> norm_num)
            · have hs2330232 : InSquare (-27/320) (111/320) (1/320) tau := by
                convert childUL hs233023 hx233023 hy233023 using 1 <;> norm_num
              exact Batch0267.cell2141.sound htau (by
                simp only [Batch0267.cell2141, Batch0267.tau2141, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2330232 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (11/32 : ℝ) with hy233023 | hy233023
            · have hs2330231 : InSquare (-5/64) (109/320) (1/320) tau := by
                convert childLR hs233023 hx233023 hy233023 using 1 <;> norm_num
              exact Batch0267.cell2140.sound htau (by
                simp only [Batch0267.cell2140, Batch0267.tau2140, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2330231 (by positivity) using 1 <;> norm_num)
            · have hs2330233 : InSquare (-5/64) (111/320) (1/320) tau := by
                convert childUR hs233023 hx233023 hy233023 using 1 <;> norm_num
              exact Batch0267.cell2142.sound htau (by
                simp only [Batch0267.cell2142, Batch0267.tau2142, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2330233 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (13/40 : ℝ) with hy2330 | hy2330
    · have hs23301 : InSquare (-1/16) (5/16) (1/80) tau := by
        convert childLR hs hx2330 hy2330 using 1 <;> norm_num
      rcases le_total tau.re (-1/16 : ℝ) with hx23301 | hx23301
      · rcases le_total tau.im (5/16 : ℝ) with hy23301 | hy23301
        · have hs233010 : InSquare (-11/160) (49/160) (1/160) tau := by
            convert childLL hs23301 hx23301 hy23301 using 1 <;> norm_num
          exact Batch0120.cell0960.sound htau (by
            simp only [Batch0120.cell0960, Batch0120.tau0960, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs233010 (by positivity) using 1 <;> norm_num)
        · have hs233012 : InSquare (-11/160) (51/160) (1/160) tau := by
            convert childUL hs23301 hx23301 hy23301 using 1 <;> norm_num
          exact Batch0120.cell0962.sound htau (by
            simp only [Batch0120.cell0962, Batch0120.tau0962, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs233012 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (5/16 : ℝ) with hy23301 | hy23301
        · have hs233011 : InSquare (-9/160) (49/160) (1/160) tau := by
            convert childLR hs23301 hx23301 hy23301 using 1 <;> norm_num
          exact Batch0120.cell0961.sound htau (by
            simp only [Batch0120.cell0961, Batch0120.tau0961, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs233011 (by positivity) using 1 <;> norm_num)
        · have hs233013 : InSquare (-9/160) (51/160) (1/160) tau := by
            convert childUR hs23301 hx23301 hy23301 using 1 <;> norm_num
          exact Batch0120.cell0963.sound htau (by
            simp only [Batch0120.cell0963, Batch0120.tau0963, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs233013 (by positivity) using 1 <;> norm_num)
    · have hs23303 : InSquare (-1/16) (27/80) (1/80) tau := by
        convert childUR hs hx2330 hy2330 using 1 <;> norm_num
      rcases le_total tau.re (-1/16 : ℝ) with hx23303 | hx23303
      · rcases le_total tau.im (27/80 : ℝ) with hy23303 | hy23303
        · have hs233030 : InSquare (-11/160) (53/160) (1/160) tau := by
            convert childLL hs23303 hx23303 hy23303 using 1 <;> norm_num
          exact Batch0120.cell0966.sound htau (by
            simp only [Batch0120.cell0966, Batch0120.tau0966, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs233030 (by positivity) using 1 <;> norm_num)
        · have hs233032 : InSquare (-11/160) (11/32) (1/160) tau := by
            convert childUL hs23303 hx23303 hy23303 using 1 <;> norm_num
          rcases le_total tau.re (-11/160 : ℝ) with hx233032 | hx233032
          · rcases le_total tau.im (11/32 : ℝ) with hy233032 | hy233032
            · have hs2330320 : InSquare (-23/320) (109/320) (1/320) tau := by
                convert childLL hs233032 hx233032 hy233032 using 1 <;> norm_num
              exact Batch0267.cell2143.sound htau (by
                simp only [Batch0267.cell2143, Batch0267.tau2143, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2330320 (by positivity) using 1 <;> norm_num)
            · have hs2330322 : InSquare (-23/320) (111/320) (1/320) tau := by
                convert childUL hs233032 hx233032 hy233032 using 1 <;> norm_num
              exact Batch0268.cell2145.sound htau (by
                simp only [Batch0268.cell2145, Batch0268.tau2145, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2330322 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (11/32 : ℝ) with hy233032 | hy233032
            · have hs2330321 : InSquare (-21/320) (109/320) (1/320) tau := by
                convert childLR hs233032 hx233032 hy233032 using 1 <;> norm_num
              exact Batch0268.cell2144.sound htau (by
                simp only [Batch0268.cell2144, Batch0268.tau2144, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2330321 (by positivity) using 1 <;> norm_num)
            · have hs2330323 : InSquare (-21/320) (111/320) (1/320) tau := by
                convert childUR hs233032 hx233032 hy233032 using 1 <;> norm_num
              exact Batch0268.cell2146.sound htau (by
                simp only [Batch0268.cell2146, Batch0268.tau2146, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2330323 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (27/80 : ℝ) with hy23303 | hy23303
        · have hs233031 : InSquare (-9/160) (53/160) (1/160) tau := by
            convert childLR hs23303 hx23303 hy23303 using 1 <;> norm_num
          exact Batch0120.cell0967.sound htau (by
            simp only [Batch0120.cell0967, Batch0120.tau0967, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs233031 (by positivity) using 1 <;> norm_num)
        · have hs233033 : InSquare (-9/160) (11/32) (1/160) tau := by
            convert childUR hs23303 hx23303 hy23303 using 1 <;> norm_num
          exact Batch0121.cell0968.sound htau (by
            simp only [Batch0121.cell0968, Batch0121.tau0968, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs233033 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2330
