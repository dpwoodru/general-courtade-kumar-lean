import GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0192
import GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0193
import GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0194
import GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0195
import GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0196
import GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0197
import GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0198
import GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0199
import GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0200
import GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0201
import GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0202
import GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0203
import GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0204
import GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0205
import GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0206
import GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0207
import GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0208
import GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0209
import GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0210
import GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0211
import GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0212
import GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0213
import GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0214
import GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0215
import GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0216
import GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0217
import GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0218
import GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0219
import GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0220
import GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0221
import GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0222
import GeneralCK.Certificates.Generated.DoubleCapLowMiddle.Cell0223
namespace GeneralCK.Certificates.DoubleCapLowMiddleAggregation.Part006
open GeneralCK
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

theorem cover : ∀ m : ℝ, 1059 / 12800 ≤ m → m ≤ 141 / 800 →
    0 ≤ doubleCapLowResidual m := by
  intro m hmLo hmHi
  by_cases h0192 : m ≤ (539 / 6400 : ℝ)
  · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0192.accepted_cell m (by linarith [hmLo]) h0192
  ·
    by_cases h0193 : m ≤ (1097 / 12800 : ℝ)
    · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0193.accepted_cell m (by linarith [(lt_of_not_ge h0192).le]) h0193
    ·
      by_cases h0194 : m ≤ (279 / 3200 : ℝ)
      · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0194.accepted_cell m (by linarith [(lt_of_not_ge h0193).le]) h0194
      ·
        by_cases h0195 : m ≤ (227 / 2560 : ℝ)
        · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0195.accepted_cell m (by linarith [(lt_of_not_ge h0194).le]) h0195
        ·
          by_cases h0196 : m ≤ (577 / 6400 : ℝ)
          · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0196.accepted_cell m (by linarith [(lt_of_not_ge h0195).le]) h0196
          ·
            by_cases h0197 : m ≤ (1173 / 12800 : ℝ)
            · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0197.accepted_cell m (by linarith [(lt_of_not_ge h0196).le]) h0197
            ·
              by_cases h0198 : m ≤ (149 / 1600 : ℝ)
              · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0198.accepted_cell m (by linarith [(lt_of_not_ge h0197).le]) h0198
              ·
                by_cases h0199 : m ≤ (123 / 1280 : ℝ)
                · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0199.accepted_cell m (by linarith [(lt_of_not_ge h0198).le]) h0199
                ·
                  by_cases h0200 : m ≤ (317 / 3200 : ℝ)
                  · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0200.accepted_cell m (by linarith [(lt_of_not_ge h0199).le]) h0200
                  ·
                    by_cases h0201 : m ≤ (653 / 6400 : ℝ)
                    · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0201.accepted_cell m (by linarith [(lt_of_not_ge h0200).le]) h0201
                    ·
                      by_cases h0202 : m ≤ (21 / 200 : ℝ)
                      · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0202.accepted_cell m (by linarith [(lt_of_not_ge h0201).le]) h0202
                      ·
                        by_cases h0203 : m ≤ (691 / 6400 : ℝ)
                        · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0203.accepted_cell m (by linarith [(lt_of_not_ge h0202).le]) h0203
                        ·
                          by_cases h0204 : m ≤ (71 / 640 : ℝ)
                          · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0204.accepted_cell m (by linarith [(lt_of_not_ge h0203).le]) h0204
                          ·
                            by_cases h0205 : m ≤ (729 / 6400 : ℝ)
                            · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0205.accepted_cell m (by linarith [(lt_of_not_ge h0204).le]) h0205
                            ·
                              by_cases h0206 : m ≤ (187 / 1600 : ℝ)
                              · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0206.accepted_cell m (by linarith [(lt_of_not_ge h0205).le]) h0206
                              ·
                                by_cases h0207 : m ≤ (767 / 6400 : ℝ)
                                · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0207.accepted_cell m (by linarith [(lt_of_not_ge h0206).le]) h0207
                                ·
                                  by_cases h0208 : m ≤ (393 / 3200 : ℝ)
                                  · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0208.accepted_cell m (by linarith [(lt_of_not_ge h0207).le]) h0208
                                  ·
                                    by_cases h0209 : m ≤ (161 / 1280 : ℝ)
                                    · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0209.accepted_cell m (by linarith [(lt_of_not_ge h0208).le]) h0209
                                    ·
                                      by_cases h0210 : m ≤ (103 / 800 : ℝ)
                                      · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0210.accepted_cell m (by linarith [(lt_of_not_ge h0209).le]) h0210
                                      ·
                                        by_cases h0211 : m ≤ (843 / 6400 : ℝ)
                                        · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0211.accepted_cell m (by linarith [(lt_of_not_ge h0210).le]) h0211
                                        ·
                                          by_cases h0212 : m ≤ (431 / 3200 : ℝ)
                                          · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0212.accepted_cell m (by linarith [(lt_of_not_ge h0211).le]) h0212
                                          ·
                                            by_cases h0213 : m ≤ (881 / 6400 : ℝ)
                                            · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0213.accepted_cell m (by linarith [(lt_of_not_ge h0212).le]) h0213
                                            ·
                                              by_cases h0214 : m ≤ (9 / 64 : ℝ)
                                              · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0214.accepted_cell m (by linarith [(lt_of_not_ge h0213).le]) h0214
                                              ·
                                                by_cases h0215 : m ≤ (919 / 6400 : ℝ)
                                                · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0215.accepted_cell m (by linarith [(lt_of_not_ge h0214).le]) h0215
                                                ·
                                                  by_cases h0216 : m ≤ (469 / 3200 : ℝ)
                                                  · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0216.accepted_cell m (by linarith [(lt_of_not_ge h0215).le]) h0216
                                                  ·
                                                    by_cases h0217 : m ≤ (957 / 6400 : ℝ)
                                                    · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0217.accepted_cell m (by linarith [(lt_of_not_ge h0216).le]) h0217
                                                    ·
                                                      by_cases h0218 : m ≤ (61 / 400 : ℝ)
                                                      · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0218.accepted_cell m (by linarith [(lt_of_not_ge h0217).le]) h0218
                                                      ·
                                                        by_cases h0219 : m ≤ (199 / 1280 : ℝ)
                                                        · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0219.accepted_cell m (by linarith [(lt_of_not_ge h0218).le]) h0219
                                                        ·
                                                          by_cases h0220 : m ≤ (507 / 3200 : ℝ)
                                                          · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0220.accepted_cell m (by linarith [(lt_of_not_ge h0219).le]) h0220
                                                          ·
                                                            by_cases h0221 : m ≤ (263 / 1600 : ℝ)
                                                            · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0221.accepted_cell m (by linarith [(lt_of_not_ge h0220).le]) h0221
                                                            ·
                                                              by_cases h0222 : m ≤ (109 / 640 : ℝ)
                                                              · exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0222.accepted_cell m (by linarith [(lt_of_not_ge h0221).le]) h0222
                                                              ·
                                                                exact GeneralCK.Certificates.DoubleCapLowMiddle.Cell0223.accepted_cell m (by linarith [(lt_of_not_ge h0222).le]) hmHi

#print axioms cover
end GeneralCK.Certificates.DoubleCapLowMiddleAggregation.Part006
