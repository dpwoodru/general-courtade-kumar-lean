import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_2176_neg : (87080833 / 1000000000) ≤ -Real.log (916603 / 1000000) ∧
    -Real.log (916603 / 1000000) ≤ (43540417 / 500000000) := by
  have h := checkLog_sound (w := (83397 / 1916603)) (n := 12)
    (lo := (87080833 / 1000000000)) (hi := (43540417 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 916603) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 916603) = 1/(916603 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2176 : Bounds (-43540417 / 500000000) (-87080833 / 1000000000) (Real.log (916603 / 1000000)) := by
  have h := reflection_log_2176_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2177_neg : (3489679 / 500000000) ≤ -Real.log (993044940391 / 1000000000000) ∧
    -Real.log (993044940391 / 1000000000000) ≤ (6979359 / 1000000000) := by
  have h := checkLog_sound (w := (6955059609 / 1993044940391)) (n := 12)
    (lo := (3489679 / 500000000)) (hi := (6979359 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993044940391) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993044940391) = 1/(993044940391 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2177 : Bounds (-6979359 / 1000000000) (-3489679 / 500000000) (Real.log (993044940391 / 1000000000000)) := by
  have h := reflection_log_2177_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2178_neg : (3471563 / 500000000) ≤ -Real.log (993080921239 / 1000000000000) ∧
    -Real.log (993080921239 / 1000000000000) ≤ (6943127 / 1000000000) := by
  have h := checkLog_sound (w := (6919078761 / 1993080921239)) (n := 12)
    (lo := (3471563 / 500000000)) (hi := (6943127 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993080921239) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993080921239) = 1/(993080921239 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2178 : Bounds (-6943127 / 1000000000) (-3471563 / 500000000) (Real.log (993080921239 / 1000000000000)) := by
  have h := reflection_log_2178_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2179_neg : (166747291 / 1000000000) ≤ -Real.log (250000000000 / 295363915887) ∧
    -Real.log (250000000000 / 295363915887) ≤ (41686823 / 250000000) := by
  have h := checkLog_sound (w := (45363915887 / 545363915887)) (n := 12)
    (lo := (166747291 / 1000000000)) (hi := (41686823 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((295363915887 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(295363915887 / 250000000000) = 1/(250000000000 / 295363915887) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2179 : Bounds (166747291 / 1000000000) (41686823 / 250000000) (Real.log (295363915887 / 250000000000)) := by
  have h := reflection_log_2179_neg
  have he : Real.log (295363915887 / 250000000000) = -Real.log (250000000000 / 295363915887) := by
    rw [show ((295363915887 / 250000000000) : ℝ) = ((250000000000 / 295363915887) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2180_neg : (167182309 / 1000000000) ≤ -Real.log (500000000000 / 590984864767) ∧
    -Real.log (500000000000 / 590984864767) ≤ (16718231 / 100000000) := by
  have h := checkLog_sound (w := (90984864767 / 1090984864767)) (n := 12)
    (lo := (167182309 / 1000000000)) (hi := (16718231 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((590984864767 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(590984864767 / 500000000000) = 1/(500000000000 / 590984864767) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2180 : Bounds (167182309 / 1000000000) (16718231 / 100000000) (Real.log (590984864767 / 500000000000)) := by
  have h := reflection_log_2180_neg
  have he : Real.log (590984864767 / 500000000000) = -Real.log (500000000000 / 590984864767) := by
    rw [show ((590984864767 / 500000000000) : ℝ) = ((500000000000 / 590984864767) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2181_neg : (167241997 / 500000000) ≤ -Real.log (500000000000 / 698609612849) ∧
    -Real.log (500000000000 / 698609612849) ≤ (66896799 / 200000000) := by
  have h := checkLog_sound (w := (198609612849 / 1198609612849)) (n := 12)
    (lo := (167241997 / 500000000)) (hi := (66896799 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((698609612849 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(698609612849 / 500000000000) = 1/(500000000000 / 698609612849) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2181 : Bounds (167241997 / 500000000) (66896799 / 200000000) (Real.log (698609612849 / 500000000000)) := by
  have h := reflection_log_2181_neg
  have he : Real.log (698609612849 / 500000000000) = -Real.log (500000000000 / 698609612849) := by
    rw [show ((698609612849 / 500000000000) : ℝ) = ((500000000000 / 698609612849) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2182_neg : (334689643 / 1000000000) ≤ -Real.log (125000000000 / 174688324143) ∧
    -Real.log (125000000000 / 174688324143) ≤ (83672411 / 250000000) := by
  have h := checkLog_sound (w := (49688324143 / 299688324143)) (n := 12)
    (lo := (334689643 / 1000000000)) (hi := (83672411 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((174688324143 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(174688324143 / 125000000000) = 1/(125000000000 / 174688324143) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2182 : Bounds (334689643 / 1000000000) (83672411 / 250000000) (Real.log (174688324143 / 125000000000)) := by
  have h := reflection_log_2182_neg
  have he : Real.log (174688324143 / 125000000000) = -Real.log (125000000000 / 174688324143) := by
    rw [show ((174688324143 / 125000000000) : ℝ) = ((125000000000 / 174688324143) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2183_neg : (3837333 / 25000000) ≤ -Real.log (10000 / 11659) ∧
    -Real.log (10000 / 11659) ≤ (153493321 / 1000000000) := by
  have h := checkLog_sound (w := (1659 / 21659)) (n := 12)
    (lo := (3837333 / 25000000)) (hi := (153493321 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11659 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11659 / 10000) = 1/(10000 / 11659) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2183 : Bounds (3837333 / 25000000) (153493321 / 1000000000) (Real.log (11659 / 10000)) := by
  have h := reflection_log_2183_neg
  have he : Real.log (11659 / 10000) = -Real.log (10000 / 11659) := by
    rw [show ((11659 / 10000) : ℝ) = ((10000 / 11659) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2184_neg : (181401979 / 1000000000) ≤ -Real.log (8341 / 10000) ∧
    -Real.log (8341 / 10000) ≤ (9070099 / 50000000) := by
  have h := checkLog_sound (w := (1659 / 18341)) (n := 12)
    (lo := (181401979 / 1000000000)) (hi := (9070099 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8341) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8341) = 1/(8341 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2184 : Bounds (-9070099 / 50000000) (-181401979 / 1000000000) (Real.log (8341 / 10000)) := by
  have h := reflection_log_2184_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2185_neg : (82943 / 500000000) ≤ -Real.log (10000000 / 10001659) ∧
    -Real.log (10000000 / 10001659) ≤ (165887 / 1000000000) := by
  have h := checkLog_sound (w := (1659 / 20001659)) (n := 12)
    (lo := (82943 / 500000000)) (hi := (165887 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001659 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001659 / 10000000) = 1/(10000000 / 10001659) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2185 : Bounds (82943 / 500000000) (165887 / 1000000000) (Real.log (10001659 / 10000000)) := by
  have h := reflection_log_2185_neg
  have he : Real.log (10001659 / 10000000) = -Real.log (10000000 / 10001659) := by
    rw [show ((10001659 / 10000000) : ℝ) = ((10000000 / 10001659) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2186_neg : (165913 / 1000000000) ≤ -Real.log (9998341 / 10000000) ∧
    -Real.log (9998341 / 10000000) ≤ (82957 / 500000000) := by
  have h := checkLog_sound (w := (1659 / 19998341)) (n := 12)
    (lo := (165913 / 1000000000)) (hi := (82957 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998341) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998341) = 1/(9998341 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2186 : Bounds (-82957 / 500000000) (-165913 / 1000000000) (Real.log (9998341 / 10000000)) := by
  have h := reflection_log_2186_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2187_neg : (79948241 / 1000000000) ≤ -Real.log (1000000 / 1083231) ∧
    -Real.log (1000000 / 1083231) ≤ (39974121 / 500000000) := by
  have h := checkLog_sound (w := (83231 / 2083231)) (n := 12)
    (lo := (79948241 / 1000000000)) (hi := (39974121 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1083231 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1083231 / 1000000) = 1/(1000000 / 1083231) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2187 : Bounds (79948241 / 1000000000) (39974121 / 500000000) (Real.log (1083231 / 1000000)) := by
  have h := reflection_log_2187_neg
  have he : Real.log (1083231 / 1000000) = -Real.log (1000000 / 1083231) := by
    rw [show ((1083231 / 1000000) : ℝ) = ((1000000 / 1083231) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2188_neg : (43449873 / 500000000) ≤ -Real.log (916769 / 1000000) ∧
    -Real.log (916769 / 1000000) ≤ (86899747 / 1000000000) := by
  have h := checkLog_sound (w := (83231 / 1916769)) (n := 12)
    (lo := (43449873 / 500000000)) (hi := (86899747 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 916769) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 916769) = 1/(916769 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2188 : Bounds (-86899747 / 1000000000) (-43449873 / 500000000) (Real.log (916769 / 1000000)) := by
  have h := reflection_log_2188_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2189_neg : (20037137 / 250000000) ≤ -Real.log (125000 / 135431) ∧
    -Real.log (125000 / 135431) ≤ (80148549 / 1000000000) := by
  have h := checkLog_sound (w := (10431 / 260431)) (n := 12)
    (lo := (20037137 / 250000000)) (hi := (80148549 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((135431 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(135431 / 125000) = 1/(125000 / 135431) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2189 : Bounds (20037137 / 250000000) (80148549 / 1000000000) (Real.log (135431 / 125000)) := by
  have h := reflection_log_2189_neg
  have he : Real.log (135431 / 125000) = -Real.log (125000 / 135431) := by
    rw [show ((135431 / 125000) : ℝ) = ((125000 / 135431) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2190_neg : (3485459 / 40000000) ≤ -Real.log (114569 / 125000) ∧
    -Real.log (114569 / 125000) ≤ (21784119 / 250000000) := by
  have h := checkLog_sound (w := (10431 / 239569)) (n := 12)
    (lo := (3485459 / 40000000)) (hi := (21784119 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 114569) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 114569) = 1/(114569 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2190 : Bounds (-21784119 / 250000000) (-3485459 / 40000000) (Real.log (114569 / 125000)) := by
  have h := reflection_log_2190_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2191_neg : (6987927 / 1000000000) ≤ -Real.log (15516194239 / 15625000000) ∧
    -Real.log (15516194239 / 15625000000) ≤ (873491 / 125000000) := by
  have h := checkLog_sound (w := (108805761 / 31141194239)) (n := 12)
    (lo := (6987927 / 1000000000)) (hi := (873491 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 15516194239) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 15516194239) = 1/(15516194239 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2191 : Bounds (-873491 / 125000000) (-6987927 / 1000000000) (Real.log (15516194239 / 15625000000)) := by
  have h := reflection_log_2191_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2192_neg : (1390301 / 200000000) ≤ -Real.log (993072600639 / 1000000000000) ∧
    -Real.log (993072600639 / 1000000000000) ≤ (3475753 / 500000000) := by
  have h := checkLog_sound (w := (6927399361 / 1993072600639)) (n := 12)
    (lo := (1390301 / 200000000)) (hi := (3475753 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993072600639) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993072600639) = 1/(993072600639 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2192 : Bounds (-3475753 / 500000000) (-1390301 / 200000000) (Real.log (993072600639 / 1000000000000)) := by
  have h := reflection_log_2192_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2193_neg : (41711997 / 250000000) ≤ -Real.log (500000000000 / 590787319379) ∧
    -Real.log (500000000000 / 590787319379) ≤ (166847989 / 1000000000) := by
  have h := checkLog_sound (w := (90787319379 / 1090787319379)) (n := 12)
    (lo := (41711997 / 250000000)) (hi := (166847989 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((590787319379 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(590787319379 / 500000000000) = 1/(500000000000 / 590787319379) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2193 : Bounds (41711997 / 250000000) (166847989 / 1000000000) (Real.log (590787319379 / 500000000000)) := by
  have h := reflection_log_2193_neg
  have he : Real.log (590787319379 / 500000000000) = -Real.log (500000000000 / 590787319379) := by
    rw [show ((590787319379 / 500000000000) : ℝ) = ((500000000000 / 590787319379) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2194_neg : (167285023 / 1000000000) ≤ -Real.log (62500000000 / 73880696349) ∧
    -Real.log (62500000000 / 73880696349) ≤ (5227657 / 31250000) := by
  have h := checkLog_sound (w := (11380696349 / 136380696349)) (n := 12)
    (lo := (167285023 / 1000000000)) (hi := (5227657 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((73880696349 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(73880696349 / 62500000000) = 1/(62500000000 / 73880696349) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2194 : Bounds (167285023 / 1000000000) (5227657 / 31250000) (Real.log (73880696349 / 62500000000)) := by
  have h := reflection_log_2194_neg
  have he : Real.log (73880696349 / 62500000000) = -Real.log (62500000000 / 73880696349) := by
    rw [show ((73880696349 / 62500000000) : ℝ) = ((62500000000 / 73880696349) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2195_neg : (334689643 / 1000000000) ≤ -Real.log (500000000000 / 698753296571) ∧
    -Real.log (500000000000 / 698753296571) ≤ (83672411 / 250000000) := by
  have h := checkLog_sound (w := (198753296571 / 1198753296571)) (n := 12)
    (lo := (334689643 / 1000000000)) (hi := (83672411 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((698753296571 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(698753296571 / 500000000000) = 1/(500000000000 / 698753296571) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2195 : Bounds (334689643 / 1000000000) (83672411 / 250000000) (Real.log (698753296571 / 500000000000)) := by
  have h := reflection_log_2195_neg
  have he : Real.log (698753296571 / 500000000000) = -Real.log (500000000000 / 698753296571) := by
    rw [show ((698753296571 / 500000000000) : ℝ) = ((500000000000 / 698753296571) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2196_neg : (3348953 / 10000000) ≤ -Real.log (500000000000 / 698897014747) ∧
    -Real.log (500000000000 / 698897014747) ≤ (334895301 / 1000000000) := by
  have h := checkLog_sound (w := (198897014747 / 1198897014747)) (n := 12)
    (lo := (3348953 / 10000000)) (hi := (334895301 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((698897014747 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(698897014747 / 500000000000) = 1/(500000000000 / 698897014747) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2196 : Bounds (3348953 / 10000000) (334895301 / 1000000000) (Real.log (698897014747 / 500000000000)) := by
  have h := reflection_log_2196_neg
  have he : Real.log (698897014747 / 500000000000) = -Real.log (500000000000 / 698897014747) := by
    rw [show ((698897014747 / 500000000000) : ℝ) = ((500000000000 / 698897014747) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2197_neg : (153579087 / 1000000000) ≤ -Real.log (500 / 583) ∧
    -Real.log (500 / 583) ≤ (9598693 / 62500000) := by
  have h := checkLog_sound (w := (83 / 1083)) (n := 12)
    (lo := (153579087 / 1000000000)) (hi := (9598693 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((583 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(583 / 500) = 1/(500 / 583) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2197 : Bounds (153579087 / 1000000000) (9598693 / 62500000) (Real.log (583 / 500)) := by
  have h := reflection_log_2197_neg
  have he : Real.log (583 / 500) = -Real.log (500 / 583) := by
    rw [show ((583 / 500) : ℝ) = ((500 / 583) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2198_neg : (45380469 / 250000000) ≤ -Real.log (417 / 500) ∧
    -Real.log (417 / 500) ≤ (181521877 / 1000000000) := by
  have h := checkLog_sound (w := (83 / 917)) (n := 12)
    (lo := (45380469 / 250000000)) (hi := (181521877 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 417) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500 / 417) = 1/(417 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2198 : Bounds (-181521877 / 1000000000) (-45380469 / 250000000) (Real.log (417 / 500)) := by
  have h := reflection_log_2198_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2199_neg : (82993 / 500000000) ≤ -Real.log (500000 / 500083) ∧
    -Real.log (500000 / 500083) ≤ (165987 / 1000000000) := by
  have h := checkLog_sound (w := (83 / 1000083)) (n := 12)
    (lo := (82993 / 500000000)) (hi := (165987 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500083 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500083 / 500000) = 1/(500000 / 500083) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2199 : Bounds (82993 / 500000000) (165987 / 1000000000) (Real.log (500083 / 500000)) := by
  have h := reflection_log_2199_neg
  have he : Real.log (500083 / 500000) = -Real.log (500000 / 500083) := by
    rw [show ((500083 / 500000) : ℝ) = ((500000 / 500083) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2200_neg : (166013 / 1000000000) ≤ -Real.log (499917 / 500000) ∧
    -Real.log (499917 / 500000) ≤ (83007 / 500000000) := by
  have h := checkLog_sound (w := (83 / 999917)) (n := 12)
    (lo := (166013 / 1000000000)) (hi := (83007 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499917) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499917) = 1/(499917 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2200 : Bounds (-83007 / 500000000) (-166013 / 1000000000) (Real.log (499917 / 500000)) := by
  have h := reflection_log_2200_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2201_neg : (79995321 / 1000000000) ≤ -Real.log (500000 / 541641) ∧
    -Real.log (500000 / 541641) ≤ (39997661 / 500000000) := by
  have h := checkLog_sound (w := (41641 / 1041641)) (n := 12)
    (lo := (79995321 / 1000000000)) (hi := (39997661 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((541641 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(541641 / 500000) = 1/(500000 / 541641) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2201 : Bounds (79995321 / 1000000000) (39997661 / 500000000) (Real.log (541641 / 500000)) := by
  have h := reflection_log_2201_neg
  have he : Real.log (541641 / 500000) = -Real.log (500000 / 541641) := by
    rw [show ((541641 / 500000) : ℝ) = ((500000 / 541641) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2202_neg : (43477689 / 500000000) ≤ -Real.log (458359 / 500000) ∧
    -Real.log (458359 / 500000) ≤ (86955379 / 1000000000) := by
  have h := checkLog_sound (w := (41641 / 958359)) (n := 12)
    (lo := (43477689 / 500000000)) (hi := (86955379 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 458359) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 458359) = 1/(458359 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2202 : Bounds (-86955379 / 1000000000) (-43477689 / 500000000) (Real.log (458359 / 500000)) := by
  have h := reflection_log_2202_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2203_neg : (80195619 / 1000000000) ≤ -Real.log (1000000 / 1083499) ∧
    -Real.log (1000000 / 1083499) ≤ (4009781 / 50000000) := by
  have h := checkLog_sound (w := (83499 / 2083499)) (n := 12)
    (lo := (80195619 / 1000000000)) (hi := (4009781 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1083499 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1083499 / 1000000) = 1/(1000000 / 1083499) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2203 : Bounds (80195619 / 1000000000) (4009781 / 50000000) (Real.log (1083499 / 1000000)) := by
  have h := reflection_log_2203_neg
  have he : Real.log (1083499 / 1000000) = -Real.log (1000000 / 1083499) := by
    rw [show ((1083499 / 1000000) : ℝ) = ((1000000 / 1083499) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2204_neg : (2179803 / 25000000) ≤ -Real.log (916501 / 1000000) ∧
    -Real.log (916501 / 1000000) ≤ (87192121 / 1000000000) := by
  have h := checkLog_sound (w := (83499 / 1916501)) (n := 12)
    (lo := (2179803 / 25000000)) (hi := (87192121 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 916501) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 916501) = 1/(916501 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2204 : Bounds (-87192121 / 1000000000) (-2179803 / 25000000) (Real.log (916501 / 1000000)) := by
  have h := reflection_log_2204_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2205_neg : (6996501 / 1000000000) ≤ -Real.log (993027916999 / 1000000000000) ∧
    -Real.log (993027916999 / 1000000000000) ≤ (3498251 / 500000000) := by
  have h := checkLog_sound (w := (6972083001 / 1993027916999)) (n := 12)
    (lo := (6996501 / 1000000000)) (hi := (3498251 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993027916999) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993027916999) = 1/(993027916999 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2205 : Bounds (-3498251 / 500000000) (-6996501 / 1000000000) (Real.log (993027916999 / 1000000000000)) := by
  have h := reflection_log_2205_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2206_neg : (870007 / 125000000) ≤ -Real.log (248266027119 / 250000000000) ∧
    -Real.log (248266027119 / 250000000000) ≤ (6960057 / 1000000000) := by
  have h := checkLog_sound (w := (1733972881 / 498266027119)) (n := 12)
    (lo := (870007 / 125000000)) (hi := (6960057 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248266027119) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248266027119) = 1/(248266027119 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2206 : Bounds (-6960057 / 1000000000) (-870007 / 125000000) (Real.log (248266027119 / 250000000000)) := by
  have h := reflection_log_2206_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2207_neg : (1669507 / 10000000) ≤ -Real.log (25000000000 / 29542400171) ∧
    -Real.log (25000000000 / 29542400171) ≤ (166950701 / 1000000000) := by
  have h := checkLog_sound (w := (4542400171 / 54542400171)) (n := 12)
    (lo := (1669507 / 10000000)) (hi := (166950701 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((29542400171 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(29542400171 / 25000000000) = 1/(25000000000 / 29542400171) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2207 : Bounds (1669507 / 10000000) (166950701 / 1000000000) (Real.log (29542400171 / 25000000000)) := by
  have h := reflection_log_2207_neg
  have he : Real.log (29542400171 / 25000000000) = -Real.log (25000000000 / 29542400171) := by
    rw [show ((29542400171 / 25000000000) : ℝ) = ((25000000000 / 29542400171) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2208_neg : (167387739 / 1000000000) ≤ -Real.log (125000000000 / 147776570893) ∧
    -Real.log (125000000000 / 147776570893) ≤ (8369387 / 50000000) := by
  have h := checkLog_sound (w := (22776570893 / 272776570893)) (n := 12)
    (lo := (167387739 / 1000000000)) (hi := (8369387 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((147776570893 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(147776570893 / 125000000000) = 1/(125000000000 / 147776570893) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2208 : Bounds (167387739 / 1000000000) (8369387 / 50000000) (Real.log (147776570893 / 125000000000)) := by
  have h := reflection_log_2208_neg
  have he : Real.log (147776570893 / 125000000000) = -Real.log (125000000000 / 147776570893) := by
    rw [show ((147776570893 / 125000000000) : ℝ) = ((125000000000 / 147776570893) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2209_neg : (3348953 / 10000000) ≤ -Real.log (250000000000 / 349448507373) ∧
    -Real.log (250000000000 / 349448507373) ≤ (334895301 / 1000000000) := by
  have h := checkLog_sound (w := (99448507373 / 599448507373)) (n := 12)
    (lo := (3348953 / 10000000)) (hi := (334895301 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((349448507373 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(349448507373 / 250000000000) = 1/(250000000000 / 349448507373) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2209 : Bounds (3348953 / 10000000) (334895301 / 1000000000) (Real.log (349448507373 / 250000000000)) := by
  have h := reflection_log_2209_neg
  have he : Real.log (349448507373 / 250000000000) = -Real.log (250000000000 / 349448507373) := by
    rw [show ((349448507373 / 250000000000) : ℝ) = ((250000000000 / 349448507373) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2210_neg : (83775241 / 250000000) ≤ -Real.log (500000000000 / 699040767387) ∧
    -Real.log (500000000000 / 699040767387) ≤ (67020193 / 200000000) := by
  have h := checkLog_sound (w := (199040767387 / 1199040767387)) (n := 12)
    (lo := (83775241 / 250000000)) (hi := (67020193 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((699040767387 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(699040767387 / 500000000000) = 1/(500000000000 / 699040767387) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2210 : Bounds (83775241 / 250000000) (67020193 / 200000000) (Real.log (699040767387 / 500000000000)) := by
  have h := reflection_log_2210_neg
  have he : Real.log (699040767387 / 500000000000) = -Real.log (500000000000 / 699040767387) := by
    rw [show ((699040767387 / 500000000000) : ℝ) = ((500000000000 / 699040767387) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2211_neg : (153664847 / 1000000000) ≤ -Real.log (10000 / 11661) ∧
    -Real.log (10000 / 11661) ≤ (9604053 / 62500000) := by
  have h := checkLog_sound (w := (1661 / 21661)) (n := 12)
    (lo := (153664847 / 1000000000)) (hi := (9604053 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11661 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11661 / 10000) = 1/(10000 / 11661) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2211 : Bounds (153664847 / 1000000000) (9604053 / 62500000) (Real.log (11661 / 10000)) := by
  have h := reflection_log_2211_neg
  have he : Real.log (11661 / 10000) = -Real.log (10000 / 11661) := by
    rw [show ((11661 / 10000) : ℝ) = ((10000 / 11661) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2212_neg : (181641787 / 1000000000) ≤ -Real.log (8339 / 10000) ∧
    -Real.log (8339 / 10000) ≤ (45410447 / 250000000) := by
  have h := checkLog_sound (w := (1661 / 18339)) (n := 12)
    (lo := (181641787 / 1000000000)) (hi := (45410447 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8339) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8339) = 1/(8339 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2212 : Bounds (-45410447 / 250000000) (-181641787 / 1000000000) (Real.log (8339 / 10000)) := by
  have h := reflection_log_2212_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2213_neg : (83043 / 500000000) ≤ -Real.log (10000000 / 10001661) ∧
    -Real.log (10000000 / 10001661) ≤ (166087 / 1000000000) := by
  have h := checkLog_sound (w := (1661 / 20001661)) (n := 12)
    (lo := (83043 / 500000000)) (hi := (166087 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001661 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001661 / 10000000) = 1/(10000000 / 10001661) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2213 : Bounds (83043 / 500000000) (166087 / 1000000000) (Real.log (10001661 / 10000000)) := by
  have h := reflection_log_2213_neg
  have he : Real.log (10001661 / 10000000) = -Real.log (10000000 / 10001661) := by
    rw [show ((10001661 / 10000000) : ℝ) = ((10000000 / 10001661) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2214_neg : (166113 / 1000000000) ≤ -Real.log (9998339 / 10000000) ∧
    -Real.log (9998339 / 10000000) ≤ (83057 / 500000000) := by
  have h := checkLog_sound (w := (1661 / 19998339)) (n := 12)
    (lo := (166113 / 1000000000)) (hi := (83057 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998339) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998339) = 1/(9998339 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2214 : Bounds (-83057 / 500000000) (-166113 / 1000000000) (Real.log (9998339 / 10000000)) := by
  have h := reflection_log_2214_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2215_neg : (80042399 / 1000000000) ≤ -Real.log (1000000 / 1083333) ∧
    -Real.log (1000000 / 1083333) ≤ (100053 / 1250000) := by
  have h := checkLog_sound (w := (83333 / 2083333)) (n := 12)
    (lo := (80042399 / 1000000000)) (hi := (100053 / 1250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1083333 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1083333 / 1000000) = 1/(1000000 / 1083333) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2215 : Bounds (80042399 / 1000000000) (100053 / 1250000) (Real.log (1083333 / 1000000)) := by
  have h := reflection_log_2215_neg
  have he : Real.log (1083333 / 1000000) = -Real.log (1000000 / 1083333) := by
    rw [show ((1083333 / 1000000) : ℝ) = ((1000000 / 1083333) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2216_neg : (87011013 / 1000000000) ≤ -Real.log (916667 / 1000000) ∧
    -Real.log (916667 / 1000000) ≤ (43505507 / 500000000) := by
  have h := checkLog_sound (w := (83333 / 1916667)) (n := 12)
    (lo := (87011013 / 1000000000)) (hi := (43505507 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 916667) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 916667) = 1/(916667 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2216 : Bounds (-43505507 / 500000000) (-87011013 / 1000000000) (Real.log (916667 / 1000000)) := by
  have h := reflection_log_2216_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2217_neg : (80242687 / 1000000000) ≤ -Real.log (20000 / 21671) ∧
    -Real.log (20000 / 21671) ≤ (156724 / 1953125) := by
  have h := checkLog_sound (w := (1671 / 41671)) (n := 12)
    (lo := (80242687 / 1000000000)) (hi := (156724 / 1953125))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((21671 / 20000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(21671 / 20000) = 1/(20000 / 21671) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2217 : Bounds (80242687 / 1000000000) (156724 / 1953125) (Real.log (21671 / 20000)) := by
  have h := reflection_log_2217_neg
  have he : Real.log (21671 / 20000) = -Real.log (20000 / 21671) := by
    rw [show ((21671 / 20000) : ℝ) = ((20000 / 21671) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2218_neg : (10905971 / 125000000) ≤ -Real.log (18329 / 20000) ∧
    -Real.log (18329 / 20000) ≤ (87247769 / 1000000000) := by
  have h := checkLog_sound (w := (1671 / 38329)) (n := 12)
    (lo := (10905971 / 125000000)) (hi := (87247769 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20000 / 18329) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20000 / 18329) = 1/(18329 / 20000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2218 : Bounds (-87247769 / 1000000000) (-10905971 / 125000000) (Real.log (18329 / 20000)) := by
  have h := reflection_log_2218_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2219_neg : (175127 / 25000000) ≤ -Real.log (397207759 / 400000000) ∧
    -Real.log (397207759 / 400000000) ≤ (7005081 / 1000000000) := by
  have h := checkLog_sound (w := (2792241 / 797207759)) (n := 12)
    (lo := (175127 / 25000000)) (hi := (7005081 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400000000 / 397207759) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400000000 / 397207759) = 1/(397207759 / 400000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2219 : Bounds (-7005081 / 1000000000) (-175127 / 25000000) (Real.log (397207759 / 400000000)) := by
  have h := reflection_log_2219_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2220_neg : (6968613 / 1000000000) ≤ -Real.log (993055611111 / 1000000000000) ∧
    -Real.log (993055611111 / 1000000000000) ≤ (3484307 / 500000000) := by
  have h := checkLog_sound (w := (6944388889 / 1993055611111)) (n := 12)
    (lo := (6968613 / 1000000000)) (hi := (3484307 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993055611111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993055611111) = 1/(993055611111 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2220 : Bounds (-3484307 / 500000000) (-6968613 / 1000000000) (Real.log (993055611111 / 1000000000000)) := by
  have h := reflection_log_2220_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2221_neg : (167053413 / 1000000000) ≤ -Real.log (100000000000 / 118181738843) ∧
    -Real.log (100000000000 / 118181738843) ≤ (83526707 / 500000000) := by
  have h := checkLog_sound (w := (18181738843 / 218181738843)) (n := 12)
    (lo := (167053413 / 1000000000)) (hi := (83526707 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((118181738843 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(118181738843 / 100000000000) = 1/(100000000000 / 118181738843) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2221 : Bounds (167053413 / 1000000000) (83526707 / 500000000) (Real.log (118181738843 / 100000000000)) := by
  have h := reflection_log_2221_neg
  have he : Real.log (118181738843 / 100000000000) = -Real.log (100000000000 / 118181738843) := by
    rw [show ((118181738843 / 100000000000) : ℝ) = ((100000000000 / 118181738843) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2222_neg : (20936307 / 125000000) ≤ -Real.log (50000000000 / 59116700311) ∧
    -Real.log (50000000000 / 59116700311) ≤ (167490457 / 1000000000) := by
  have h := checkLog_sound (w := (9116700311 / 109116700311)) (n := 12)
    (lo := (20936307 / 125000000)) (hi := (167490457 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((59116700311 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(59116700311 / 50000000000) = 1/(50000000000 / 59116700311) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2222 : Bounds (20936307 / 125000000) (167490457 / 1000000000) (Real.log (59116700311 / 50000000000)) := by
  have h := reflection_log_2222_neg
  have he : Real.log (59116700311 / 50000000000) = -Real.log (50000000000 / 59116700311) := by
    rw [show ((59116700311 / 50000000000) : ℝ) = ((50000000000 / 59116700311) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2223_neg : (83775241 / 250000000) ≤ -Real.log (250000000000 / 349520383693) ∧
    -Real.log (250000000000 / 349520383693) ≤ (67020193 / 200000000) := by
  have h := checkLog_sound (w := (99520383693 / 599520383693)) (n := 12)
    (lo := (83775241 / 250000000)) (hi := (67020193 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((349520383693 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(349520383693 / 250000000000) = 1/(250000000000 / 349520383693) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2223 : Bounds (83775241 / 250000000) (67020193 / 200000000) (Real.log (349520383693 / 250000000000)) := by
  have h := reflection_log_2223_neg
  have he : Real.log (349520383693 / 250000000000) = -Real.log (250000000000 / 349520383693) := by
    rw [show ((349520383693 / 250000000000) : ℝ) = ((250000000000 / 349520383693) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2224_neg : (67061327 / 200000000) ≤ -Real.log (500000000000 / 699184554503) ∧
    -Real.log (500000000000 / 699184554503) ≤ (83826659 / 250000000) := by
  have h := checkLog_sound (w := (199184554503 / 1199184554503)) (n := 12)
    (lo := (67061327 / 200000000)) (hi := (83826659 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((699184554503 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(699184554503 / 500000000000) = 1/(500000000000 / 699184554503) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2224 : Bounds (67061327 / 200000000) (83826659 / 250000000) (Real.log (699184554503 / 500000000000)) := by
  have h := reflection_log_2224_neg
  have he : Real.log (699184554503 / 500000000000) = -Real.log (500000000000 / 699184554503) := by
    rw [show ((699184554503 / 500000000000) : ℝ) = ((500000000000 / 699184554503) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2225_neg : (153750599 / 1000000000) ≤ -Real.log (5000 / 5831) ∧
    -Real.log (5000 / 5831) ≤ (768753 / 5000000) := by
  have h := checkLog_sound (w := (831 / 10831)) (n := 12)
    (lo := (153750599 / 1000000000)) (hi := (768753 / 5000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5831 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5831 / 5000) = 1/(5000 / 5831) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2225 : Bounds (153750599 / 1000000000) (768753 / 5000000) (Real.log (5831 / 5000)) := by
  have h := reflection_log_2225_neg
  have he : Real.log (5831 / 5000) = -Real.log (5000 / 5831) := by
    rw [show ((5831 / 5000) : ℝ) = ((5000 / 5831) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2226_neg : (181761713 / 1000000000) ≤ -Real.log (4169 / 5000) ∧
    -Real.log (4169 / 5000) ≤ (90880857 / 500000000) := by
  have h := checkLog_sound (w := (831 / 9169)) (n := 12)
    (lo := (181761713 / 1000000000)) (hi := (90880857 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4169) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4169) = 1/(4169 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2226 : Bounds (-90880857 / 500000000) (-181761713 / 1000000000) (Real.log (4169 / 5000)) := by
  have h := reflection_log_2226_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2227_neg : (83093 / 500000000) ≤ -Real.log (5000000 / 5000831) ∧
    -Real.log (5000000 / 5000831) ≤ (166187 / 1000000000) := by
  have h := checkLog_sound (w := (831 / 10000831)) (n := 12)
    (lo := (83093 / 500000000)) (hi := (166187 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000831 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000831 / 5000000) = 1/(5000000 / 5000831) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2227 : Bounds (83093 / 500000000) (166187 / 1000000000) (Real.log (5000831 / 5000000)) := by
  have h := reflection_log_2227_neg
  have he : Real.log (5000831 / 5000000) = -Real.log (5000000 / 5000831) := by
    rw [show ((5000831 / 5000000) : ℝ) = ((5000000 / 5000831) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2228_neg : (166213 / 1000000000) ≤ -Real.log (4999169 / 5000000) ∧
    -Real.log (4999169 / 5000000) ≤ (83107 / 500000000) := by
  have h := checkLog_sound (w := (831 / 9999169)) (n := 12)
    (lo := (166213 / 1000000000)) (hi := (83107 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999169) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999169) = 1/(4999169 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2228 : Bounds (-83107 / 500000000) (-166213 / 1000000000) (Real.log (4999169 / 5000000)) := by
  have h := reflection_log_2228_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2229_neg : (10011069 / 125000000) ≤ -Real.log (1000000 / 1083383) ∧
    -Real.log (1000000 / 1083383) ≤ (80088553 / 1000000000) := by
  have h := checkLog_sound (w := (83383 / 2083383)) (n := 12)
    (lo := (10011069 / 125000000)) (hi := (80088553 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1083383 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1083383 / 1000000) = 1/(1000000 / 1083383) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2229 : Bounds (10011069 / 125000000) (80088553 / 1000000000) (Real.log (1083383 / 1000000)) := by
  have h := reflection_log_2229_neg
  have he : Real.log (1083383 / 1000000) = -Real.log (1000000 / 1083383) := by
    rw [show ((1083383 / 1000000) : ℝ) = ((1000000 / 1083383) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2230_neg : (2176639 / 25000000) ≤ -Real.log (916617 / 1000000) ∧
    -Real.log (916617 / 1000000) ≤ (87065561 / 1000000000) := by
  have h := checkLog_sound (w := (83383 / 1916617)) (n := 12)
    (lo := (2176639 / 25000000)) (hi := (87065561 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 916617) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 916617) = 1/(916617 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2230 : Bounds (-87065561 / 1000000000) (-2176639 / 25000000) (Real.log (916617 / 1000000)) := by
  have h := reflection_log_2230_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2231_neg : (40144877 / 500000000) ≤ -Real.log (1000000 / 1083601) ∧
    -Real.log (1000000 / 1083601) ≤ (16057951 / 200000000) := by
  have h := checkLog_sound (w := (83601 / 2083601)) (n := 12)
    (lo := (40144877 / 500000000)) (hi := (16057951 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1083601 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1083601 / 1000000) = 1/(1000000 / 1083601) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2231 : Bounds (40144877 / 500000000) (16057951 / 200000000) (Real.log (1083601 / 1000000)) := by
  have h := reflection_log_2231_neg
  have he : Real.log (1083601 / 1000000) = -Real.log (1000000 / 1083601) := by
    rw [show ((1083601 / 1000000) : ℝ) = ((1000000 / 1083601) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2232_neg : (87303419 / 1000000000) ≤ -Real.log (916399 / 1000000) ∧
    -Real.log (916399 / 1000000) ≤ (4365171 / 50000000) := by
  have h := checkLog_sound (w := (83601 / 1916399)) (n := 12)
    (lo := (87303419 / 1000000000)) (hi := (4365171 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 916399) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 916399) = 1/(916399 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2232 : Bounds (-4365171 / 50000000) (-87303419 / 1000000000) (Real.log (916399 / 1000000)) := by
  have h := reflection_log_2232_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2233_neg : (1402733 / 200000000) ≤ -Real.log (993010872799 / 1000000000000) ∧
    -Real.log (993010872799 / 1000000000000) ≤ (3506833 / 500000000) := by
  have h := checkLog_sound (w := (6989127201 / 1993010872799)) (n := 12)
    (lo := (1402733 / 200000000)) (hi := (3506833 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993010872799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993010872799) = 1/(993010872799 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2233 : Bounds (-3506833 / 500000000) (-1402733 / 200000000) (Real.log (993010872799 / 1000000000000)) := by
  have h := reflection_log_2233_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2234_neg : (6977007 / 1000000000) ≤ -Real.log (993047275311 / 1000000000000) ∧
    -Real.log (993047275311 / 1000000000000) ≤ (436063 / 62500000) := by
  have h := checkLog_sound (w := (6952724689 / 1993047275311)) (n := 12)
    (lo := (6977007 / 1000000000)) (hi := (436063 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993047275311) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993047275311) = 1/(993047275311 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2234 : Bounds (-436063 / 62500000) (-6977007 / 1000000000) (Real.log (993047275311 / 1000000000000)) := by
  have h := reflection_log_2234_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2235_neg : (167154113 / 1000000000) ≤ -Real.log (500000000000 / 590968201549) ∧
    -Real.log (500000000000 / 590968201549) ≤ (83577057 / 500000000) := by
  have h := checkLog_sound (w := (90968201549 / 1090968201549)) (n := 12)
    (lo := (167154113 / 1000000000)) (hi := (83577057 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((590968201549 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(590968201549 / 500000000000) = 1/(500000000000 / 590968201549) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2235 : Bounds (167154113 / 1000000000) (83577057 / 500000000) (Real.log (590968201549 / 500000000000)) := by
  have h := reflection_log_2235_neg
  have he : Real.log (590968201549 / 500000000000) = -Real.log (500000000000 / 590968201549) := by
    rw [show ((590968201549 / 500000000000) : ℝ) = ((500000000000 / 590968201549) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2236_neg : (167593173 / 1000000000) ≤ -Real.log (500000000000 / 591227729407) ∧
    -Real.log (500000000000 / 591227729407) ≤ (83796587 / 500000000) := by
  have h := checkLog_sound (w := (91227729407 / 1091227729407)) (n := 12)
    (lo := (167593173 / 1000000000)) (hi := (83796587 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((591227729407 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(591227729407 / 500000000000) = 1/(500000000000 / 591227729407) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2236 : Bounds (167593173 / 1000000000) (83796587 / 500000000) (Real.log (591227729407 / 500000000000)) := by
  have h := reflection_log_2236_neg
  have he : Real.log (591227729407 / 500000000000) = -Real.log (500000000000 / 591227729407) := by
    rw [show ((591227729407 / 500000000000) : ℝ) = ((500000000000 / 591227729407) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2237_neg : (67061327 / 200000000) ≤ -Real.log (250000000000 / 349592277251) ∧
    -Real.log (250000000000 / 349592277251) ≤ (83826659 / 250000000) := by
  have h := checkLog_sound (w := (99592277251 / 599592277251)) (n := 12)
    (lo := (67061327 / 200000000)) (hi := (83826659 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((349592277251 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(349592277251 / 250000000000) = 1/(250000000000 / 349592277251) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2237 : Bounds (67061327 / 200000000) (83826659 / 250000000) (Real.log (349592277251 / 250000000000)) := by
  have h := reflection_log_2237_neg
  have he : Real.log (349592277251 / 250000000000) = -Real.log (250000000000 / 349592277251) := by
    rw [show ((349592277251 / 250000000000) : ℝ) = ((250000000000 / 349592277251) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2238_neg : (335512313 / 1000000000) ≤ -Real.log (50000000000 / 69932837611) ∧
    -Real.log (50000000000 / 69932837611) ≤ (167756157 / 500000000) := by
  have h := checkLog_sound (w := (19932837611 / 119932837611)) (n := 12)
    (lo := (335512313 / 1000000000)) (hi := (167756157 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((69932837611 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(69932837611 / 50000000000) = 1/(50000000000 / 69932837611) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2238 : Bounds (335512313 / 1000000000) (167756157 / 500000000) (Real.log (69932837611 / 50000000000)) := by
  have h := reflection_log_2238_neg
  have he : Real.log (69932837611 / 50000000000) = -Real.log (50000000000 / 69932837611) := by
    rw [show ((69932837611 / 50000000000) : ℝ) = ((50000000000 / 69932837611) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2239_neg : (19229543 / 125000000) ≤ -Real.log (10000 / 11663) ∧
    -Real.log (10000 / 11663) ≤ (30767269 / 200000000) := by
  have h := checkLog_sound (w := (1663 / 21663)) (n := 12)
    (lo := (19229543 / 125000000)) (hi := (30767269 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11663 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11663 / 10000) = 1/(10000 / 11663) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2239 : Bounds (19229543 / 125000000) (30767269 / 200000000) (Real.log (11663 / 10000)) := by
  have h := reflection_log_2239_neg
  have he : Real.log (11663 / 10000) = -Real.log (10000 / 11663) := by
    rw [show ((11663 / 10000) : ℝ) = ((10000 / 11663) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily
