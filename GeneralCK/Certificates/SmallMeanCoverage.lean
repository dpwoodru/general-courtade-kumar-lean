import GeneralCK.Certificates.SmallMeanLeaves

namespace GeneralCK.Certificates.SmallMean

theorem scalar_certificate (gamma : ℝ → ℝ) (hmono : AntitoneOn gamma (Set.Ioc 0 1))
    (heq : gamma = gammaExpr) (r : ℝ) (hl : (1/6 : ℝ) ≤ r) (hu : r ≤ 1) :
    0 < W gamma r := by
  by_cases hm : r ≤ (139 / 384)
  · have hu := hm
    by_cases hm : r ≤ (19 / 64)
    · have hu := hm
      by_cases hm : r ≤ (47 / 192)
      · have hu := hm
        by_cases hm : r ≤ (7 / 32)
        · have hu := hm
          exact leaf_0 gamma hmono heq r hl (by simpa only [div_one] using hu)
        · have hl := (lt_of_not_ge hm).le
          exact leaf_1 gamma hmono heq r hl (by simpa only [div_one] using hu)
      · have hl := (lt_of_not_ge hm).le
        by_cases hm : r ≤ (13 / 48)
        · have hu := hm
          exact leaf_2 gamma hmono heq r hl (by simpa only [div_one] using hu)
        · have hl := (lt_of_not_ge hm).le
          by_cases hm : r ≤ (109 / 384)
          · have hu := hm
            exact leaf_3 gamma hmono heq r hl (by simpa only [div_one] using hu)
          · have hl := (lt_of_not_ge hm).le
            exact leaf_4 gamma hmono heq r hl (by simpa only [div_one] using hu)
    · have hl := (lt_of_not_ge hm).le
      by_cases hm : r ≤ (31 / 96)
      · have hu := hm
        by_cases hm : r ≤ (119 / 384)
        · have hu := hm
          exact leaf_5 gamma hmono heq r hl (by simpa only [div_one] using hu)
        · have hl := (lt_of_not_ge hm).le
          exact leaf_6 gamma hmono heq r hl (by simpa only [div_one] using hu)
      · have hl := (lt_of_not_ge hm).le
        by_cases hm : r ≤ (43 / 128)
        · have hu := hm
          exact leaf_7 gamma hmono heq r hl (by simpa only [div_one] using hu)
        · have hl := (lt_of_not_ge hm).le
          by_cases hm : r ≤ (67 / 192)
          · have hu := hm
            exact leaf_8 gamma hmono heq r hl (by simpa only [div_one] using hu)
          · have hl := (lt_of_not_ge hm).le
            exact leaf_9 gamma hmono heq r hl (by simpa only [div_one] using hu)
  · have hl := (lt_of_not_ge hm).le
    by_cases hm : r ≤ (23 / 48)
    · have hu := hm
      by_cases hm : r ≤ (77 / 192)
      · have hu := hm
        by_cases hm : r ≤ (3 / 8)
        · have hu := hm
          exact leaf_10 gamma hmono heq r hl (by simpa only [div_one] using hu)
        · have hl := (lt_of_not_ge hm).le
          exact leaf_11 gamma hmono heq r hl (by simpa only [div_one] using hu)
      · have hl := (lt_of_not_ge hm).le
        by_cases hm : r ≤ (41 / 96)
        · have hu := hm
          exact leaf_12 gamma hmono heq r hl (by simpa only [div_one] using hu)
        · have hl := (lt_of_not_ge hm).le
          by_cases hm : r ≤ (29 / 64)
          · have hu := hm
            exact leaf_13 gamma hmono heq r hl (by simpa only [div_one] using hu)
          · have hl := (lt_of_not_ge hm).le
            exact leaf_14 gamma hmono heq r hl (by simpa only [div_one] using hu)
    · have hl := (lt_of_not_ge hm).le
      by_cases hm : r ≤ (7 / 12)
      · have hu := hm
        by_cases hm : r ≤ (17 / 32)
        · have hu := hm
          exact leaf_15 gamma hmono heq r hl (by simpa only [div_one] using hu)
        · have hl := (lt_of_not_ge hm).le
          exact leaf_16 gamma hmono heq r hl (by simpa only [div_one] using hu)
      · have hl := (lt_of_not_ge hm).le
        by_cases hm : r ≤ (11 / 16)
        · have hu := hm
          exact leaf_17 gamma hmono heq r hl (by simpa only [div_one] using hu)
        · have hl := (lt_of_not_ge hm).le
          by_cases hm : r ≤ (19 / 24)
          · have hu := hm
            exact leaf_18 gamma hmono heq r hl (by simpa only [div_one] using hu)
          · have hl := (lt_of_not_ge hm).le
            exact leaf_19 gamma hmono heq r hl (by simpa only [div_one] using hu)

end GeneralCK.Certificates.SmallMean
