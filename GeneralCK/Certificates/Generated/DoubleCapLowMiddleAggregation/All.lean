import GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part000
import GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part001
import GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part002
import GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part003
import GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part004
import GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part005
import GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part006
import GeneralCK.Certificates.Generated.DoubleCapLowMiddleAggregation.Part007
namespace GeneralCK.Certificates.DoubleCapLowMiddleAggregation
open GeneralCK
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

theorem doubleCapLowMiddleAggregation : ∀ m : ℝ, 1 / 100 ≤ m → m ≤ 1 / 5 →
    0 ≤ doubleCapLowResidual m := by
  intro m hmLo hmHi
  by_cases hp000 : m ≤ (2523 / 204800 : ℝ)
  · exact Part000.cover m (by linarith [hmLo]) hp000
  ·
    by_cases hp001 : m ≤ (3131 / 204800 : ℝ)
    · exact Part001.cover m (by linarith [(lt_of_not_ge hp000).le]) hp001
    ·
      by_cases hp002 : m ≤ (1063 / 51200 : ℝ)
      · exact Part002.cover m (by linarith [(lt_of_not_ge hp001).le]) hp002
      ·
        by_cases hp003 : m ≤ (1519 / 51200 : ℝ)
        · exact Part003.cover m (by linarith [(lt_of_not_ge hp002).le]) hp003
        ·
          by_cases hp004 : m ≤ (1187 / 25600 : ℝ)
          · exact Part004.cover m (by linarith [(lt_of_not_ge hp003).le]) hp004
          ·
            by_cases hp005 : m ≤ (1059 / 12800 : ℝ)
            · exact Part005.cover m (by linarith [(lt_of_not_ge hp004).le]) hp005
            ·
              by_cases hp006 : m ≤ (141 / 800 : ℝ)
              · exact Part006.cover m (by linarith [(lt_of_not_ge hp005).le]) hp006
              ·
                exact Part007.cover m (by linarith [(lt_of_not_ge hp006).le]) hmHi

#print axioms doubleCapLowMiddleAggregation
end GeneralCK.Certificates.DoubleCapLowMiddleAggregation
