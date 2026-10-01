import GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0064
import GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0065
import GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0066
import GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0067
import GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0068
import GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0069
import GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0070
import GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0071
import GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0072
import GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0073
import GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0074
import GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0075
import GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0076
import GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0077
import GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0078
import GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0079
import GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0080
import GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0081
import GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0082
import GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0083
import GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0084
import GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0085
import GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0086
import GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0087
import GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0088
import GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0089
import GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0090
import GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0091
import GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0092
import GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0093
import GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0094
import GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0095
namespace GeneralCK.Certificates.DoubleCapLowMiddleAggregation.Part002
open GeneralCK
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

theorem cover : ∀ m : ℝ, 3131 / 204800 ≤ m → m ≤ 1063 / 51200 →
    0 ≤ doubleCapLowResidual m := by
  intro m hmLo hmHi
  by_cases h0064 : m ≤ (63 / 4096 : ℝ)
  · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0064.accepted_cell m (by linarith [hmLo]) h0064
  ·
    by_cases h0065 : m ≤ (3169 / 204800 : ℝ)
    · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0065.accepted_cell m (by linarith [(lt_of_not_ge h0064).le]) h0065
    ·
      by_cases h0066 : m ≤ (797 / 51200 : ℝ)
      · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0066.accepted_cell m (by linarith [(lt_of_not_ge h0065).le]) h0066
      ·
        by_cases h0067 : m ≤ (3207 / 204800 : ℝ)
        · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0067.accepted_cell m (by linarith [(lt_of_not_ge h0066).le]) h0067
        ·
          by_cases h0068 : m ≤ (1613 / 102400 : ℝ)
          · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0068.accepted_cell m (by linarith [(lt_of_not_ge h0067).le]) h0068
          ·
            by_cases h0069 : m ≤ (51 / 3200 : ℝ)
            · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0069.accepted_cell m (by linarith [(lt_of_not_ge h0068).le]) h0069
            ·
              by_cases h0070 : m ≤ (1651 / 102400 : ℝ)
              · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0070.accepted_cell m (by linarith [(lt_of_not_ge h0069).le]) h0070
              ·
                by_cases h0071 : m ≤ (167 / 10240 : ℝ)
                · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0071.accepted_cell m (by linarith [(lt_of_not_ge h0070).le]) h0071
                ·
                  by_cases h0072 : m ≤ (1689 / 102400 : ℝ)
                  · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0072.accepted_cell m (by linarith [(lt_of_not_ge h0071).le]) h0072
                  ·
                    by_cases h0073 : m ≤ (427 / 25600 : ℝ)
                    · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0073.accepted_cell m (by linarith [(lt_of_not_ge h0072).le]) h0073
                    ·
                      by_cases h0074 : m ≤ (1727 / 102400 : ℝ)
                      · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0074.accepted_cell m (by linarith [(lt_of_not_ge h0073).le]) h0074
                      ·
                        by_cases h0075 : m ≤ (873 / 51200 : ℝ)
                        · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0075.accepted_cell m (by linarith [(lt_of_not_ge h0074).le]) h0075
                        ·
                          by_cases h0076 : m ≤ (353 / 20480 : ℝ)
                          · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0076.accepted_cell m (by linarith [(lt_of_not_ge h0075).le]) h0076
                          ·
                            by_cases h0077 : m ≤ (223 / 12800 : ℝ)
                            · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0077.accepted_cell m (by linarith [(lt_of_not_ge h0076).le]) h0077
                            ·
                              by_cases h0078 : m ≤ (1803 / 102400 : ℝ)
                              · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0078.accepted_cell m (by linarith [(lt_of_not_ge h0077).le]) h0078
                              ·
                                by_cases h0079 : m ≤ (911 / 51200 : ℝ)
                                · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0079.accepted_cell m (by linarith [(lt_of_not_ge h0078).le]) h0079
                                ·
                                  by_cases h0080 : m ≤ (1841 / 102400 : ℝ)
                                  · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0080.accepted_cell m (by linarith [(lt_of_not_ge h0079).le]) h0080
                                  ·
                                    by_cases h0081 : m ≤ (93 / 5120 : ℝ)
                                    · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0081.accepted_cell m (by linarith [(lt_of_not_ge h0080).le]) h0081
                                    ·
                                      by_cases h0082 : m ≤ (1879 / 102400 : ℝ)
                                      · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0082.accepted_cell m (by linarith [(lt_of_not_ge h0081).le]) h0082
                                      ·
                                        by_cases h0083 : m ≤ (949 / 51200 : ℝ)
                                        · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0083.accepted_cell m (by linarith [(lt_of_not_ge h0082).le]) h0083
                                        ·
                                          by_cases h0084 : m ≤ (1917 / 102400 : ℝ)
                                          · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0084.accepted_cell m (by linarith [(lt_of_not_ge h0083).le]) h0084
                                          ·
                                            by_cases h0085 : m ≤ (121 / 6400 : ℝ)
                                            · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0085.accepted_cell m (by linarith [(lt_of_not_ge h0084).le]) h0085
                                            ·
                                              by_cases h0086 : m ≤ (391 / 20480 : ℝ)
                                              · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0086.accepted_cell m (by linarith [(lt_of_not_ge h0085).le]) h0086
                                              ·
                                                by_cases h0087 : m ≤ (987 / 51200 : ℝ)
                                                · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0087.accepted_cell m (by linarith [(lt_of_not_ge h0086).le]) h0087
                                                ·
                                                  by_cases h0088 : m ≤ (1993 / 102400 : ℝ)
                                                  · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0088.accepted_cell m (by linarith [(lt_of_not_ge h0087).le]) h0088
                                                  ·
                                                    by_cases h0089 : m ≤ (503 / 25600 : ℝ)
                                                    · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0089.accepted_cell m (by linarith [(lt_of_not_ge h0088).le]) h0089
                                                    ·
                                                      by_cases h0090 : m ≤ (2031 / 102400 : ℝ)
                                                      · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0090.accepted_cell m (by linarith [(lt_of_not_ge h0089).le]) h0090
                                                      ·
                                                        by_cases h0091 : m ≤ (41 / 2048 : ℝ)
                                                        · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0091.accepted_cell m (by linarith [(lt_of_not_ge h0090).le]) h0091
                                                        ·
                                                          by_cases h0092 : m ≤ (2069 / 102400 : ℝ)
                                                          · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0092.accepted_cell m (by linarith [(lt_of_not_ge h0091).le]) h0092
                                                          ·
                                                            by_cases h0093 : m ≤ (261 / 12800 : ℝ)
                                                            · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0093.accepted_cell m (by linarith [(lt_of_not_ge h0092).le]) h0093
                                                            ·
                                                              by_cases h0094 : m ≤ (2107 / 102400 : ℝ)
                                                              · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0094.accepted_cell m (by linarith [(lt_of_not_ge h0093).le]) h0094
                                                              ·
                                                                exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0095.accepted_cell m (by linarith [(lt_of_not_ge h0094).le]) hmHi

#print axioms cover
end GeneralCK.Certificates.DoubleCapLowMiddleAggregation.Part002
