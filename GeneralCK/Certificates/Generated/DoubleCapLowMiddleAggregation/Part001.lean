import GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0032
import GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0033
import GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0034
import GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0035
import GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0036
import GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0037
import GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0038
import GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0039
import GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0040
import GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0041
import GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0042
import GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0043
import GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0044
import GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0045
import GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0046
import GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0047
import GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0048
import GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0049
import GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0050
import GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0051
import GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0052
import GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0053
import GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0054
import GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0055
import GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0056
import GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0057
import GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0058
import GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0059
import GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0060
import GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0061
import GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0062
import GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0063
namespace GeneralCK.Certificates.DoubleCapLowMiddleAggregation.Part001
open GeneralCK
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

theorem cover : ∀ m : ℝ, 2523 / 204800 ≤ m → m ≤ 3131 / 204800 →
    0 ≤ doubleCapLowResidual m := by
  intro m hmLo hmHi
  by_cases h0032 : m ≤ (1271 / 102400 : ℝ)
  · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0032.accepted_cell m (by linarith [hmLo]) h0032
  ·
    by_cases h0033 : m ≤ (2561 / 204800 : ℝ)
    · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0033.accepted_cell m (by linarith [(lt_of_not_ge h0032).le]) h0033
    ·
      by_cases h0034 : m ≤ (129 / 10240 : ℝ)
      · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0034.accepted_cell m (by linarith [(lt_of_not_ge h0033).le]) h0034
      ·
        by_cases h0035 : m ≤ (2599 / 204800 : ℝ)
        · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0035.accepted_cell m (by linarith [(lt_of_not_ge h0034).le]) h0035
        ·
          by_cases h0036 : m ≤ (1309 / 102400 : ℝ)
          · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0036.accepted_cell m (by linarith [(lt_of_not_ge h0035).le]) h0036
          ·
            by_cases h0037 : m ≤ (2637 / 204800 : ℝ)
            · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0037.accepted_cell m (by linarith [(lt_of_not_ge h0036).le]) h0037
            ·
              by_cases h0038 : m ≤ (83 / 6400 : ℝ)
              · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0038.accepted_cell m (by linarith [(lt_of_not_ge h0037).le]) h0038
              ·
                by_cases h0039 : m ≤ (107 / 8192 : ℝ)
                · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0039.accepted_cell m (by linarith [(lt_of_not_ge h0038).le]) h0039
                ·
                  by_cases h0040 : m ≤ (1347 / 102400 : ℝ)
                  · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0040.accepted_cell m (by linarith [(lt_of_not_ge h0039).le]) h0040
                  ·
                    by_cases h0041 : m ≤ (2713 / 204800 : ℝ)
                    · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0041.accepted_cell m (by linarith [(lt_of_not_ge h0040).le]) h0041
                    ·
                      by_cases h0042 : m ≤ (683 / 51200 : ℝ)
                      · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0042.accepted_cell m (by linarith [(lt_of_not_ge h0041).le]) h0042
                      ·
                        by_cases h0043 : m ≤ (2751 / 204800 : ℝ)
                        · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0043.accepted_cell m (by linarith [(lt_of_not_ge h0042).le]) h0043
                        ·
                          by_cases h0044 : m ≤ (277 / 20480 : ℝ)
                          · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0044.accepted_cell m (by linarith [(lt_of_not_ge h0043).le]) h0044
                          ·
                            by_cases h0045 : m ≤ (2789 / 204800 : ℝ)
                            · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0045.accepted_cell m (by linarith [(lt_of_not_ge h0044).le]) h0045
                            ·
                              by_cases h0046 : m ≤ (351 / 25600 : ℝ)
                              · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0046.accepted_cell m (by linarith [(lt_of_not_ge h0045).le]) h0046
                              ·
                                by_cases h0047 : m ≤ (2827 / 204800 : ℝ)
                                · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0047.accepted_cell m (by linarith [(lt_of_not_ge h0046).le]) h0047
                                ·
                                  by_cases h0048 : m ≤ (1423 / 102400 : ℝ)
                                  · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0048.accepted_cell m (by linarith [(lt_of_not_ge h0047).le]) h0048
                                  ·
                                    by_cases h0049 : m ≤ (573 / 40960 : ℝ)
                                    · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0049.accepted_cell m (by linarith [(lt_of_not_ge h0048).le]) h0049
                                    ·
                                      by_cases h0050 : m ≤ (721 / 51200 : ℝ)
                                      · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0050.accepted_cell m (by linarith [(lt_of_not_ge h0049).le]) h0050
                                      ·
                                        by_cases h0051 : m ≤ (2903 / 204800 : ℝ)
                                        · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0051.accepted_cell m (by linarith [(lt_of_not_ge h0050).le]) h0051
                                        ·
                                          by_cases h0052 : m ≤ (1461 / 102400 : ℝ)
                                          · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0052.accepted_cell m (by linarith [(lt_of_not_ge h0051).le]) h0052
                                          ·
                                            by_cases h0053 : m ≤ (2941 / 204800 : ℝ)
                                            · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0053.accepted_cell m (by linarith [(lt_of_not_ge h0052).le]) h0053
                                            ·
                                              by_cases h0054 : m ≤ (37 / 2560 : ℝ)
                                              · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0054.accepted_cell m (by linarith [(lt_of_not_ge h0053).le]) h0054
                                              ·
                                                by_cases h0055 : m ≤ (2979 / 204800 : ℝ)
                                                · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0055.accepted_cell m (by linarith [(lt_of_not_ge h0054).le]) h0055
                                                ·
                                                  by_cases h0056 : m ≤ (1499 / 102400 : ℝ)
                                                  · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0056.accepted_cell m (by linarith [(lt_of_not_ge h0055).le]) h0056
                                                  ·
                                                    by_cases h0057 : m ≤ (3017 / 204800 : ℝ)
                                                    · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0057.accepted_cell m (by linarith [(lt_of_not_ge h0056).le]) h0057
                                                    ·
                                                      by_cases h0058 : m ≤ (759 / 51200 : ℝ)
                                                      · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0058.accepted_cell m (by linarith [(lt_of_not_ge h0057).le]) h0058
                                                      ·
                                                        by_cases h0059 : m ≤ (611 / 40960 : ℝ)
                                                        · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0059.accepted_cell m (by linarith [(lt_of_not_ge h0058).le]) h0059
                                                        ·
                                                          by_cases h0060 : m ≤ (1537 / 102400 : ℝ)
                                                          · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0060.accepted_cell m (by linarith [(lt_of_not_ge h0059).le]) h0060
                                                          ·
                                                            by_cases h0061 : m ≤ (3093 / 204800 : ℝ)
                                                            · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0061.accepted_cell m (by linarith [(lt_of_not_ge h0060).le]) h0061
                                                            ·
                                                              by_cases h0062 : m ≤ (389 / 25600 : ℝ)
                                                              · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0062.accepted_cell m (by linarith [(lt_of_not_ge h0061).le]) h0062
                                                              ·
                                                                exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0063.accepted_cell m (by linarith [(lt_of_not_ge h0062).le]) hmHi

#print axioms cover
end GeneralCK.Certificates.DoubleCapLowMiddleAggregation.Part001
