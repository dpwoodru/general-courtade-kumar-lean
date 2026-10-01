import GeneralCK.Certificates.Generated.E8AdaptiveFamily.CoverageKernel
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0111
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0112
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0244
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0245
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0246
import GeneralCK.Certificates.Generated.E8AdaptiveFamily.Batch0247

namespace GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2213

open E8ComplexBallKernel E8GaussianRatBall E8QuadraticCellCertificateSchema
open CoverageKernel

theorem cover {tau : ℂ} (htau : ‖tau‖ ≤ (2/5 : ℝ))
    (hs : InSquare (-9/40) (11/40) (1/40) tau) :
    ‖E8ThetaTauDerivativeFormula.thetaTauDerivExpr tau - 4‖ ≤ (1 : ℝ) := by
  rcases le_total tau.re (-9/40 : ℝ) with hx2213 | hx2213
  · rcases le_total tau.im (11/40 : ℝ) with hy2213 | hy2213
    · have hs22130 : InSquare (-19/80) (21/80) (1/80) tau := by
        convert childLL hs hx2213 hy2213 using 1 <;> norm_num
      rcases le_total tau.re (-19/80 : ℝ) with hx22130 | hx22130
      · rcases le_total tau.im (21/80 : ℝ) with hy22130 | hy22130
        · have hs221300 : InSquare (-39/160) (41/160) (1/160) tau := by
            convert childLL hs22130 hx22130 hy22130 using 1 <;> norm_num
          exact Batch0111.cell0888.sound htau (by
            simp only [Batch0111.cell0888, Batch0111.tau0888, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs221300 (by positivity) using 1 <;> norm_num)
        · have hs221302 : InSquare (-39/160) (43/160) (1/160) tau := by
            convert childUL hs22130 hx22130 hy22130 using 1 <;> norm_num
          exact Batch0111.cell0890.sound htau (by
            simp only [Batch0111.cell0890, Batch0111.tau0890, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs221302 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (21/80 : ℝ) with hy22130 | hy22130
        · have hs221301 : InSquare (-37/160) (41/160) (1/160) tau := by
            convert childLR hs22130 hx22130 hy22130 using 1 <;> norm_num
          exact Batch0111.cell0889.sound htau (by
            simp only [Batch0111.cell0889, Batch0111.tau0889, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs221301 (by positivity) using 1 <;> norm_num)
        · have hs221303 : InSquare (-37/160) (43/160) (1/160) tau := by
            convert childUR hs22130 hx22130 hy22130 using 1 <;> norm_num
          exact Batch0111.cell0891.sound htau (by
            simp only [Batch0111.cell0891, Batch0111.tau0891, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs221303 (by positivity) using 1 <;> norm_num)
    · have hs22132 : InSquare (-19/80) (23/80) (1/80) tau := by
        convert childUL hs hx2213 hy2213 using 1 <;> norm_num
      rcases le_total tau.re (-19/80 : ℝ) with hx22132 | hx22132
      · rcases le_total tau.im (23/80 : ℝ) with hy22132 | hy22132
        · have hs221320 : InSquare (-39/160) (9/32) (1/160) tau := by
            convert childLL hs22132 hx22132 hy22132 using 1 <;> norm_num
          rcases le_total tau.re (-39/160 : ℝ) with hx221320 | hx221320
          · rcases le_total tau.im (9/32 : ℝ) with hy221320 | hy221320
            · have hs2213200 : InSquare (-79/320) (89/320) (1/320) tau := by
                convert childLL hs221320 hx221320 hy221320 using 1 <;> norm_num
              exact Batch0244.cell1959.sound htau (by
                simp only [Batch0244.cell1959, Batch0244.tau1959, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2213200 (by positivity) using 1 <;> norm_num)
            · have hs2213202 : InSquare (-79/320) (91/320) (1/320) tau := by
                convert childUL hs221320 hx221320 hy221320 using 1 <;> norm_num
              exact Batch0245.cell1961.sound htau (by
                simp only [Batch0245.cell1961, Batch0245.tau1961, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2213202 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (9/32 : ℝ) with hy221320 | hy221320
            · have hs2213201 : InSquare (-77/320) (89/320) (1/320) tau := by
                convert childLR hs221320 hx221320 hy221320 using 1 <;> norm_num
              exact Batch0245.cell1960.sound htau (by
                simp only [Batch0245.cell1960, Batch0245.tau1960, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2213201 (by positivity) using 1 <;> norm_num)
            · have hs2213203 : InSquare (-77/320) (91/320) (1/320) tau := by
                convert childUR hs221320 hx221320 hy221320 using 1 <;> norm_num
              exact Batch0245.cell1962.sound htau (by
                simp only [Batch0245.cell1962, Batch0245.tau1962, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2213203 (by positivity) using 1 <;> norm_num)
        · have hs221322 : InSquare (-39/160) (47/160) (1/160) tau := by
            convert childUL hs22132 hx22132 hy22132 using 1 <;> norm_num
          rcases le_total tau.re (-39/160 : ℝ) with hx221322 | hx221322
          · rcases le_total tau.im (47/160 : ℝ) with hy221322 | hy221322
            · have hs2213220 : InSquare (-79/320) (93/320) (1/320) tau := by
                convert childLL hs221322 hx221322 hy221322 using 1 <;> norm_num
              exact Batch0245.cell1967.sound htau (by
                simp only [Batch0245.cell1967, Batch0245.tau1967, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2213220 (by positivity) using 1 <;> norm_num)
            · have hs2213222 : InSquare (-79/320) (19/64) (1/320) tau := by
                convert childUL hs221322 hx221322 hy221322 using 1 <;> norm_num
              exact Batch0246.cell1969.sound htau (by
                simp only [Batch0246.cell1969, Batch0246.tau1969, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2213222 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (47/160 : ℝ) with hy221322 | hy221322
            · have hs2213221 : InSquare (-77/320) (93/320) (1/320) tau := by
                convert childLR hs221322 hx221322 hy221322 using 1 <;> norm_num
              exact Batch0246.cell1968.sound htau (by
                simp only [Batch0246.cell1968, Batch0246.tau1968, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2213221 (by positivity) using 1 <;> norm_num)
            · have hs2213223 : InSquare (-77/320) (19/64) (1/320) tau := by
                convert childUR hs221322 hx221322 hy221322 using 1 <;> norm_num
              exact Batch0246.cell1970.sound htau (by
                simp only [Batch0246.cell1970, Batch0246.tau1970, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2213223 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (23/80 : ℝ) with hy22132 | hy22132
        · have hs221321 : InSquare (-37/160) (9/32) (1/160) tau := by
            convert childLR hs22132 hx22132 hy22132 using 1 <;> norm_num
          rcases le_total tau.re (-37/160 : ℝ) with hx221321 | hx221321
          · rcases le_total tau.im (9/32 : ℝ) with hy221321 | hy221321
            · have hs2213210 : InSquare (-15/64) (89/320) (1/320) tau := by
                convert childLL hs221321 hx221321 hy221321 using 1 <;> norm_num
              exact Batch0245.cell1963.sound htau (by
                simp only [Batch0245.cell1963, Batch0245.tau1963, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2213210 (by positivity) using 1 <;> norm_num)
            · have hs2213212 : InSquare (-15/64) (91/320) (1/320) tau := by
                convert childUL hs221321 hx221321 hy221321 using 1 <;> norm_num
              exact Batch0245.cell1965.sound htau (by
                simp only [Batch0245.cell1965, Batch0245.tau1965, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2213212 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (9/32 : ℝ) with hy221321 | hy221321
            · have hs2213211 : InSquare (-73/320) (89/320) (1/320) tau := by
                convert childLR hs221321 hx221321 hy221321 using 1 <;> norm_num
              exact Batch0245.cell1964.sound htau (by
                simp only [Batch0245.cell1964, Batch0245.tau1964, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2213211 (by positivity) using 1 <;> norm_num)
            · have hs2213213 : InSquare (-73/320) (91/320) (1/320) tau := by
                convert childUR hs221321 hx221321 hy221321 using 1 <;> norm_num
              exact Batch0245.cell1966.sound htau (by
                simp only [Batch0245.cell1966, Batch0245.tau1966, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2213213 (by positivity) using 1 <;> norm_num)
        · have hs221323 : InSquare (-37/160) (47/160) (1/160) tau := by
            convert childUR hs22132 hx22132 hy22132 using 1 <;> norm_num
          rcases le_total tau.re (-37/160 : ℝ) with hx221323 | hx221323
          · rcases le_total tau.im (47/160 : ℝ) with hy221323 | hy221323
            · have hs2213230 : InSquare (-15/64) (93/320) (1/320) tau := by
                convert childLL hs221323 hx221323 hy221323 using 1 <;> norm_num
              exact Batch0246.cell1971.sound htau (by
                simp only [Batch0246.cell1971, Batch0246.tau1971, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2213230 (by positivity) using 1 <;> norm_num)
            · have hs2213232 : InSquare (-15/64) (19/64) (1/320) tau := by
                convert childUL hs221323 hx221323 hy221323 using 1 <;> norm_num
              exact Batch0246.cell1973.sound htau (by
                simp only [Batch0246.cell1973, Batch0246.tau1973, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2213232 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (47/160 : ℝ) with hy221323 | hy221323
            · have hs2213231 : InSquare (-73/320) (93/320) (1/320) tau := by
                convert childLR hs221323 hx221323 hy221323 using 1 <;> norm_num
              exact Batch0246.cell1972.sound htau (by
                simp only [Batch0246.cell1972, Batch0246.tau1972, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2213231 (by positivity) using 1 <;> norm_num)
            · have hs2213233 : InSquare (-73/320) (19/64) (1/320) tau := by
                convert childUR hs221323 hx221323 hy221323 using 1 <;> norm_num
              exact Batch0246.cell1974.sound htau (by
                simp only [Batch0246.cell1974, Batch0246.tau1974, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2213233 (by positivity) using 1 <;> norm_num)
  · rcases le_total tau.im (11/40 : ℝ) with hy2213 | hy2213
    · have hs22131 : InSquare (-17/80) (21/80) (1/80) tau := by
        convert childLR hs hx2213 hy2213 using 1 <;> norm_num
      rcases le_total tau.re (-17/80 : ℝ) with hx22131 | hx22131
      · rcases le_total tau.im (21/80 : ℝ) with hy22131 | hy22131
        · have hs221310 : InSquare (-7/32) (41/160) (1/160) tau := by
            convert childLL hs22131 hx22131 hy22131 using 1 <;> norm_num
          exact Batch0111.cell0892.sound htau (by
            simp only [Batch0111.cell0892, Batch0111.tau0892, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs221310 (by positivity) using 1 <;> norm_num)
        · have hs221312 : InSquare (-7/32) (43/160) (1/160) tau := by
            convert childUL hs22131 hx22131 hy22131 using 1 <;> norm_num
          exact Batch0111.cell0894.sound htau (by
            simp only [Batch0111.cell0894, Batch0111.tau0894, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs221312 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (21/80 : ℝ) with hy22131 | hy22131
        · have hs221311 : InSquare (-33/160) (41/160) (1/160) tau := by
            convert childLR hs22131 hx22131 hy22131 using 1 <;> norm_num
          exact Batch0111.cell0893.sound htau (by
            simp only [Batch0111.cell0893, Batch0111.tau0893, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs221311 (by positivity) using 1 <;> norm_num)
        · have hs221313 : InSquare (-33/160) (43/160) (1/160) tau := by
            convert childUR hs22131 hx22131 hy22131 using 1 <;> norm_num
          exact Batch0111.cell0895.sound htau (by
            simp only [Batch0111.cell0895, Batch0111.tau0895, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs221313 (by positivity) using 1 <;> norm_num)
    · have hs22133 : InSquare (-17/80) (23/80) (1/80) tau := by
        convert childUR hs hx2213 hy2213 using 1 <;> norm_num
      rcases le_total tau.re (-17/80 : ℝ) with hx22133 | hx22133
      · rcases le_total tau.im (23/80 : ℝ) with hy22133 | hy22133
        · have hs221330 : InSquare (-7/32) (9/32) (1/160) tau := by
            convert childLL hs22133 hx22133 hy22133 using 1 <;> norm_num
          exact Batch0112.cell0896.sound htau (by
            simp only [Batch0112.cell0896, Batch0112.tau0896, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs221330 (by positivity) using 1 <;> norm_num)
        · have hs221332 : InSquare (-7/32) (47/160) (1/160) tau := by
            convert childUL hs22133 hx22133 hy22133 using 1 <;> norm_num
          rcases le_total tau.re (-7/32 : ℝ) with hx221332 | hx221332
          · rcases le_total tau.im (47/160 : ℝ) with hy221332 | hy221332
            · have hs2213320 : InSquare (-71/320) (93/320) (1/320) tau := by
                convert childLL hs221332 hx221332 hy221332 using 1 <;> norm_num
              exact Batch0246.cell1975.sound htau (by
                simp only [Batch0246.cell1975, Batch0246.tau1975, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2213320 (by positivity) using 1 <;> norm_num)
            · have hs2213322 : InSquare (-71/320) (19/64) (1/320) tau := by
                convert childUL hs221332 hx221332 hy221332 using 1 <;> norm_num
              exact Batch0247.cell1977.sound htau (by
                simp only [Batch0247.cell1977, Batch0247.tau1977, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2213322 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (47/160 : ℝ) with hy221332 | hy221332
            · have hs2213321 : InSquare (-69/320) (93/320) (1/320) tau := by
                convert childLR hs221332 hx221332 hy221332 using 1 <;> norm_num
              exact Batch0247.cell1976.sound htau (by
                simp only [Batch0247.cell1976, Batch0247.tau1976, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2213321 (by positivity) using 1 <;> norm_num)
            · have hs2213323 : InSquare (-69/320) (19/64) (1/320) tau := by
                convert childUR hs221332 hx221332 hy221332 using 1 <;> norm_num
              exact Batch0247.cell1978.sound htau (by
                simp only [Batch0247.cell1978, Batch0247.tau1978, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2213323 (by positivity) using 1 <;> norm_num)
      · rcases le_total tau.im (23/80 : ℝ) with hy22133 | hy22133
        · have hs221331 : InSquare (-33/160) (9/32) (1/160) tau := by
            convert childLR hs22133 hx22133 hy22133 using 1 <;> norm_num
          exact Batch0112.cell0897.sound htau (by
            simp only [Batch0112.cell0897, Batch0112.tau0897, RatBall.Holds, GaussianRat.val]
            convert inBall_of_inSquare hs221331 (by positivity) using 1 <;> norm_num)
        · have hs221333 : InSquare (-33/160) (47/160) (1/160) tau := by
            convert childUR hs22133 hx22133 hy22133 using 1 <;> norm_num
          rcases le_total tau.re (-33/160 : ℝ) with hx221333 | hx221333
          · rcases le_total tau.im (47/160 : ℝ) with hy221333 | hy221333
            · have hs2213330 : InSquare (-67/320) (93/320) (1/320) tau := by
                convert childLL hs221333 hx221333 hy221333 using 1 <;> norm_num
              exact Batch0247.cell1979.sound htau (by
                simp only [Batch0247.cell1979, Batch0247.tau1979, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2213330 (by positivity) using 1 <;> norm_num)
            · have hs2213332 : InSquare (-67/320) (19/64) (1/320) tau := by
                convert childUL hs221333 hx221333 hy221333 using 1 <;> norm_num
              exact Batch0247.cell1981.sound htau (by
                simp only [Batch0247.cell1981, Batch0247.tau1981, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2213332 (by positivity) using 1 <;> norm_num)
          · rcases le_total tau.im (47/160 : ℝ) with hy221333 | hy221333
            · have hs2213331 : InSquare (-13/64) (93/320) (1/320) tau := by
                convert childLR hs221333 hx221333 hy221333 using 1 <;> norm_num
              exact Batch0247.cell1980.sound htau (by
                simp only [Batch0247.cell1980, Batch0247.tau1980, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2213331 (by positivity) using 1 <;> norm_num)
            · have hs2213333 : InSquare (-13/64) (19/64) (1/320) tau := by
                convert childUR hs221333 hx221333 hy221333 using 1 <;> norm_num
              exact Batch0247.cell1982.sound htau (by
                simp only [Batch0247.cell1982, Batch0247.tau1982, RatBall.Holds, GaussianRat.val]
                convert inBall_of_inSquare hs2213333 (by positivity) using 1 <;> norm_num)

end GeneralCK.Certificates.Generated.E8AdaptiveFamily.Coverage2213
