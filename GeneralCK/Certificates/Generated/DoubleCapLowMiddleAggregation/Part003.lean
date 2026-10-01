import GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0096
import GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0097
import GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0098
import GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0099
import GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0100
import GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0101
import GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0102
import GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0103
import GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0104
import GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0105
import GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0106
import GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0107
import GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0108
import GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0109
import GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0110
import GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0111
import GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0112
import GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0113
import GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0114
import GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0115
import GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0116
import GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0117
import GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0118
import GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0119
import GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0120
import GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0121
import GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0122
import GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0123
import GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0124
import GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0125
import GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0126
import GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0127
namespace GeneralCK.Certificates.DoubleCapLowMiddleAggregation.Part003
open GeneralCK
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

theorem cover : ∀ m : ℝ, 1063 / 51200 ≤ m → m ≤ 1519 / 51200 →
    0 ≤ doubleCapLowResidual m := by
  intro m hmLo hmHi
  by_cases h0096 : m ≤ (429 / 20480 : ℝ)
  · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0096.accepted_cell m (by linarith [hmLo]) h0096
  ·
    by_cases h0097 : m ≤ (541 / 25600 : ℝ)
    · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0097.accepted_cell m (by linarith [(lt_of_not_ge h0096).le]) h0097
    ·
      by_cases h0098 : m ≤ (2183 / 102400 : ℝ)
      · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0098.accepted_cell m (by linarith [(lt_of_not_ge h0097).le]) h0098
      ·
        by_cases h0099 : m ≤ (1101 / 51200 : ℝ)
        · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0099.accepted_cell m (by linarith [(lt_of_not_ge h0098).le]) h0099
        ·
          by_cases h0100 : m ≤ (2221 / 102400 : ℝ)
          · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0100.accepted_cell m (by linarith [(lt_of_not_ge h0099).le]) h0100
          ·
            by_cases h0101 : m ≤ (7 / 320 : ℝ)
            · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0101.accepted_cell m (by linarith [(lt_of_not_ge h0100).le]) h0101
            ·
              by_cases h0102 : m ≤ (2259 / 102400 : ℝ)
              · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0102.accepted_cell m (by linarith [(lt_of_not_ge h0101).le]) h0102
              ·
                by_cases h0103 : m ≤ (1139 / 51200 : ℝ)
                · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0103.accepted_cell m (by linarith [(lt_of_not_ge h0102).le]) h0103
                ·
                  by_cases h0104 : m ≤ (2297 / 102400 : ℝ)
                  · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0104.accepted_cell m (by linarith [(lt_of_not_ge h0103).le]) h0104
                  ·
                    by_cases h0105 : m ≤ (579 / 25600 : ℝ)
                    · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0105.accepted_cell m (by linarith [(lt_of_not_ge h0104).le]) h0105
                    ·
                      by_cases h0106 : m ≤ (467 / 20480 : ℝ)
                      · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0106.accepted_cell m (by linarith [(lt_of_not_ge h0105).le]) h0106
                      ·
                        by_cases h0107 : m ≤ (1177 / 51200 : ℝ)
                        · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0107.accepted_cell m (by linarith [(lt_of_not_ge h0106).le]) h0107
                        ·
                          by_cases h0108 : m ≤ (2373 / 102400 : ℝ)
                          · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0108.accepted_cell m (by linarith [(lt_of_not_ge h0107).le]) h0108
                          ·
                            by_cases h0109 : m ≤ (299 / 12800 : ℝ)
                            · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0109.accepted_cell m (by linarith [(lt_of_not_ge h0108).le]) h0109
                            ·
                              by_cases h0110 : m ≤ (2411 / 102400 : ℝ)
                              · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0110.accepted_cell m (by linarith [(lt_of_not_ge h0109).le]) h0110
                              ·
                                by_cases h0111 : m ≤ (243 / 10240 : ℝ)
                                · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0111.accepted_cell m (by linarith [(lt_of_not_ge h0110).le]) h0111
                                ·
                                  by_cases h0112 : m ≤ (617 / 25600 : ℝ)
                                  · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0112.accepted_cell m (by linarith [(lt_of_not_ge h0111).le]) h0112
                                  ·
                                    by_cases h0113 : m ≤ (1253 / 51200 : ℝ)
                                    · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0113.accepted_cell m (by linarith [(lt_of_not_ge h0112).le]) h0113
                                    ·
                                      by_cases h0114 : m ≤ (159 / 6400 : ℝ)
                                      · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0114.accepted_cell m (by linarith [(lt_of_not_ge h0113).le]) h0114
                                      ·
                                        by_cases h0115 : m ≤ (1291 / 51200 : ℝ)
                                        · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0115.accepted_cell m (by linarith [(lt_of_not_ge h0114).le]) h0115
                                        ·
                                          by_cases h0116 : m ≤ (131 / 5120 : ℝ)
                                          · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0116.accepted_cell m (by linarith [(lt_of_not_ge h0115).le]) h0116
                                          ·
                                            by_cases h0117 : m ≤ (1329 / 51200 : ℝ)
                                            · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0117.accepted_cell m (by linarith [(lt_of_not_ge h0116).le]) h0117
                                            ·
                                              by_cases h0118 : m ≤ (337 / 12800 : ℝ)
                                              · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0118.accepted_cell m (by linarith [(lt_of_not_ge h0117).le]) h0118
                                              ·
                                                by_cases h0119 : m ≤ (1367 / 51200 : ℝ)
                                                · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0119.accepted_cell m (by linarith [(lt_of_not_ge h0118).le]) h0119
                                                ·
                                                  by_cases h0120 : m ≤ (693 / 25600 : ℝ)
                                                  · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0120.accepted_cell m (by linarith [(lt_of_not_ge h0119).le]) h0120
                                                  ·
                                                    by_cases h0121 : m ≤ (281 / 10240 : ℝ)
                                                    · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0121.accepted_cell m (by linarith [(lt_of_not_ge h0120).le]) h0121
                                                    ·
                                                      by_cases h0122 : m ≤ (89 / 3200 : ℝ)
                                                      · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0122.accepted_cell m (by linarith [(lt_of_not_ge h0121).le]) h0122
                                                      ·
                                                        by_cases h0123 : m ≤ (1443 / 51200 : ℝ)
                                                        · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0123.accepted_cell m (by linarith [(lt_of_not_ge h0122).le]) h0123
                                                        ·
                                                          by_cases h0124 : m ≤ (731 / 25600 : ℝ)
                                                          · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0124.accepted_cell m (by linarith [(lt_of_not_ge h0123).le]) h0124
                                                          ·
                                                            by_cases h0125 : m ≤ (1481 / 51200 : ℝ)
                                                            · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0125.accepted_cell m (by linarith [(lt_of_not_ge h0124).le]) h0125
                                                            ·
                                                              by_cases h0126 : m ≤ (15 / 512 : ℝ)
                                                              · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0126.accepted_cell m (by linarith [(lt_of_not_ge h0125).le]) h0126
                                                              ·
                                                                exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0127.accepted_cell m (by linarith [(lt_of_not_ge h0126).le]) hmHi

#print axioms cover
end GeneralCK.Certificates.DoubleCapLowMiddleAggregation.Part003
