import GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0224
import GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0225
import GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0226
import GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0227
namespace GeneralCK.Certificates.DoubleCapLowMiddleAggregation.Part007
open GeneralCK
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

theorem cover : ∀ m : ℝ, 141 / 800 ≤ m → m ≤ 1 / 5 →
    0 ≤ doubleCapLowResidual m := by
  intro m hmLo hmHi
  by_cases h0224 : m ≤ (583 / 3200 : ℝ)
  · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0224.accepted_cell m (by linarith [hmLo]) h0224
  ·
    by_cases h0225 : m ≤ (301 / 1600 : ℝ)
    · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0225.accepted_cell m (by linarith [(lt_of_not_ge h0224).le]) h0225
    ·
      by_cases h0226 : m ≤ (621 / 3200 : ℝ)
      · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0226.accepted_cell m (by linarith [(lt_of_not_ge h0225).le]) h0226
      ·
        exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0227.accepted_cell m (by linarith [(lt_of_not_ge h0226).le]) hmHi

#print axioms cover
end GeneralCK.Certificates.DoubleCapLowMiddleAggregation.Part007
