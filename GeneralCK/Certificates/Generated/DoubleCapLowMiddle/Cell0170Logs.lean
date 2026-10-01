import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0170
open GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed

theorem reflection_log_0_neg : (34657359 / 50000000) ≤ -Real.log (1 / 2) ∧
    -Real.log (1 / 2) ≤ (693147181 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 3)) (n := 12)
    (lo := (34657359 / 50000000)) (hi := (693147181 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2 / 1) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2 / 1) = 1/(1 / 2) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_0 : Bounds (34657359 / 50000000) (693147181 / 1000000000) (Real.log (2 / 1)) := by
  have h := reflection_log_0_neg
  have he : Real.log (2 / 1) = -Real.log (1 / 2) := by
    rw [show ((2 / 1) : ℝ) = ((1 / 2) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1_neg : (39866089 / 62500000) ≤ -Real.log (12800 / 24223) ∧
    -Real.log (12800 / 24223) ≤ (25514297 / 40000000) := by
  have h := checkLog_sound (w := (11423 / 37023)) (n := 12)
    (lo := (39866089 / 62500000)) (hi := (25514297 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24223 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24223 / 12800) = 1/(12800 / 24223) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (39866089 / 62500000) (25514297 / 40000000) (Real.log (24223 / 12800)) := by
  have h := reflection_log_1_neg
  have he : Real.log (24223 / 12800) = -Real.log (12800 / 24223) := by
    rw [show ((24223 / 12800) : ℝ) = ((12800 / 24223) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (2229537949 / 1000000000) ≤ -Real.log (1377 / 12800) ∧
    -Real.log (1377 / 12800) ≤ (2229537953 / 1000000000) := by
  have h := checkLog_sound (w := (223 / 2977)) (n := 12)
    (lo := (150096409 / 1000000000)) (hi := (15009641 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1377) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1600 / 1377) = 1/(1377 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-2229537953 / 1000000000) (-2229537949 / 1000000000) (Real.log (1377 / 12800)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (637072737 / 1000000000) ≤ -Real.log (3200 / 6051) ∧
    -Real.log (3200 / 6051) ≤ (318536369 / 500000000) := by
  have h := checkLog_sound (w := (2851 / 9251)) (n := 12)
    (lo := (637072737 / 1000000000)) (hi := (318536369 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6051 / 3200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6051 / 3200) = 1/(3200 / 6051) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (637072737 / 1000000000) (318536369 / 500000000) (Real.log (6051 / 3200)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6051 / 3200) = -Real.log (3200 / 6051) := by
    rw [show ((6051 / 3200) : ℝ) = ((3200 / 6051) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (553958541 / 250000000) ≤ -Real.log (349 / 3200) ∧
    -Real.log (349 / 3200) ≤ (276979271 / 125000000) := by
  have h := checkLog_sound (w := (51 / 749)) (n := 12)
    (lo := (8524539 / 62500000)) (hi := (1091141 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 349) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(400 / 349) = 1/(349 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-276979271 / 125000000) (-553958541 / 250000000) (Real.log (349 / 3200)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (144832719 / 250000000) ≤ -Real.log (6400 / 11423) ∧
    -Real.log (6400 / 11423) ≤ (579330877 / 1000000000) := by
  have h := checkLog_sound (w := (5023 / 17823)) (n := 12)
    (lo := (144832719 / 250000000)) (hi := (579330877 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11423 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11423 / 6400) = 1/(6400 / 11423) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (144832719 / 250000000) (579330877 / 1000000000) (Real.log (11423 / 6400)) := by
  have h := reflection_log_5_neg
  have he : Real.log (11423 / 6400) = -Real.log (6400 / 11423) := by
    rw [show ((11423 / 6400) : ℝ) = ((6400 / 11423) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1536390769 / 1000000000) ≤ -Real.log (1377 / 6400) ∧
    -Real.log (1377 / 6400) ≤ (384097693 / 250000000) := by
  have h := checkLog_sound (w := (223 / 2977)) (n := 12)
    (lo := (150096409 / 1000000000)) (hi := (15009641 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1377) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1600 / 1377) = 1/(1377 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-384097693 / 250000000) (-1536390769 / 1000000000) (Real.log (1377 / 6400)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (28883309 / 50000000) ≤ -Real.log (1600 / 2851) ∧
    -Real.log (1600 / 2851) ≤ (577666181 / 1000000000) := by
  have h := checkLog_sound (w := (1251 / 4451)) (n := 12)
    (lo := (28883309 / 50000000)) (hi := (577666181 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2851 / 1600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2851 / 1600) = 1/(1600 / 2851) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (28883309 / 50000000) (577666181 / 1000000000) (Real.log (2851 / 1600)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2851 / 1600) = -Real.log (1600 / 2851) := by
    rw [show ((2851 / 1600) : ℝ) = ((1600 / 2851) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (190335873 / 125000000) ≤ -Real.log (349 / 1600) ∧
    -Real.log (349 / 1600) ≤ (1522686987 / 1000000000) := by
  have h := checkLog_sound (w := (51 / 749)) (n := 12)
    (lo := (8524539 / 62500000)) (hi := (1091141 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 349) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(400 / 349) = 1/(349 / 1600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1522686987 / 1000000000) (-190335873 / 125000000) (Real.log (349 / 1600)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (650896561 / 1000000000) ≤ -Real.log (1000000 / 1917259) ∧
    -Real.log (1000000 / 1917259) ≤ (325448281 / 500000000) := by
  have h := checkLog_sound (w := (917259 / 2917259)) (n := 12)
    (lo := (650896561 / 1000000000)) (hi := (325448281 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1917259 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1917259 / 1000000) = 1/(1000000 / 1917259) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (650896561 / 1000000000) (325448281 / 500000000) (Real.log (1917259 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1917259 / 1000000) = -Real.log (1000000 / 1917259) := by
    rw [show ((1917259 / 1000000) : ℝ) = ((1000000 / 1917259) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (249204003 / 100000000) ≤ -Real.log (82741 / 1000000) ∧
    -Real.log (82741 / 1000000) ≤ (1246020017 / 500000000) := by
  have h := checkLog_sound (w := (42259 / 207741)) (n := 12)
    (lo := (41259849 / 100000000)) (hi := (412598491 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 82741) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125000 / 82741) = 1/(82741 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-1246020017 / 500000000) (-249204003 / 100000000) (Real.log (82741 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (5211319 / 8000000) ≤ -Real.log (1000000 / 1918253) ∧
    -Real.log (1000000 / 1918253) ≤ (651414877 / 1000000000) := by
  have h := checkLog_sound (w := (918253 / 2918253)) (n := 12)
    (lo := (5211319 / 8000000)) (hi := (651414877 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1918253 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1918253 / 1000000) = 1/(1000000 / 1918253) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (5211319 / 8000000) (651414877 / 1000000000) (Real.log (1918253 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1918253 / 1000000) = -Real.log (1000000 / 1918253) := by
    rw [show ((1918253 / 1000000) : ℝ) = ((1000000 / 1918253) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (500825233 / 200000000) ≤ -Real.log (81747 / 1000000) ∧
    -Real.log (81747 / 1000000) ≤ (2504126169 / 1000000000) := by
  have h := checkLog_sound (w := (43253 / 206747)) (n := 12)
    (lo := (3397477 / 8000000)) (hi := (212342313 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 81747) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125000 / 81747) = 1/(81747 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-2504126169 / 1000000000) (-500825233 / 200000000) (Real.log (81747 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (649383363 / 1000000000) ≤ -Real.log (25000 / 47859) ∧
    -Real.log (25000 / 47859) ≤ (162345841 / 250000000) := by
  have h := checkLog_sound (w := (22859 / 72859)) (n := 12)
    (lo := (649383363 / 1000000000)) (hi := (162345841 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((47859 / 25000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(47859 / 25000) = 1/(25000 / 47859) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (649383363 / 1000000000) (162345841 / 250000000) (Real.log (47859 / 25000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (47859 / 25000) = -Real.log (25000 / 47859) := by
    rw [show ((47859 / 25000) : ℝ) = ((25000 / 47859) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (2457602813 / 1000000000) ≤ -Real.log (2141 / 25000) ∧
    -Real.log (2141 / 25000) ≤ (2457602817 / 1000000000) := by
  have h := checkLog_sound (w := (492 / 2633)) (n := 12)
    (lo := (378161273 / 1000000000)) (hi := (189080637 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3125 / 2141) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(3125 / 2141) = 1/(2141 / 25000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-2457602817 / 1000000000) (-2457602813 / 1000000000) (Real.log (2141 / 25000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (649950493 / 1000000000) ≤ -Real.log (500000 / 957723) ∧
    -Real.log (500000 / 957723) ≤ (324975247 / 500000000) := by
  have h := checkLog_sound (w := (457723 / 1457723)) (n := 12)
    (lo := (649950493 / 1000000000)) (hi := (324975247 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((957723 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(957723 / 500000) = 1/(500000 / 957723) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (649950493 / 1000000000) (324975247 / 500000000) (Real.log (957723 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (957723 / 500000) = -Real.log (500000 / 957723) := by
    rw [show ((957723 / 500000) : ℝ) = ((500000 / 957723) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (2470364893 / 1000000000) ≤ -Real.log (42277 / 500000) ∧
    -Real.log (42277 / 500000) ≤ (2470364897 / 1000000000) := by
  have h := checkLog_sound (w := (20223 / 104777)) (n := 12)
    (lo := (390923353 / 1000000000)) (hi := (195461677 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 42277) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(62500 / 42277) = 1/(42277 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-2470364897 / 1000000000) (-2470364893 / 1000000000) (Real.log (42277 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (3142936591 / 1000000000) ≤ -Real.log (100000000000 / 2317181324857) ∧
    -Real.log (100000000000 / 2317181324857) ≤ (785734149 / 250000000) := by
  have h := checkLog_sound (w := (717181324857 / 3917181324857)) (n := 12)
    (lo := (370347871 / 1000000000)) (hi := (11573371 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2317181324857 / 1600000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(2317181324857 / 1600000000000) = 1/(100000000000 / 2317181324857) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (3142936591 / 1000000000) (785734149 / 250000000) (Real.log (2317181324857 / 100000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (2317181324857 / 100000000000) = -Real.log (100000000000 / 2317181324857) := by
    rw [show ((2317181324857 / 100000000000) : ℝ) = ((100000000000 / 2317181324857) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (39444263 / 12500000) ≤ -Real.log (500000000000 / 11732864814611) ∧
    -Real.log (500000000000 / 11732864814611) ≤ (631108209 / 200000000) := by
  have h := checkLog_sound (w := (3732864814611 / 19732864814611)) (n := 12)
    (lo := (598363 / 1562500)) (hi := (382952321 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11732864814611 / 8000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(11732864814611 / 8000000000000) = 1/(500000000000 / 11732864814611) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (39444263 / 12500000) (631108209 / 200000000) (Real.log (11732864814611 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (11732864814611 / 500000000000) = -Real.log (500000000000 / 11732864814611) := by
    rw [show ((11732864814611 / 500000000000) : ℝ) = ((500000000000 / 11732864814611) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (48546659 / 15625000) ≤ -Real.log (500000000000 / 11176786548341) ∧
    -Real.log (500000000000 / 11176786548341) ≤ (3106986181 / 1000000000) := by
  have h := checkLog_sound (w := (3176786548341 / 19176786548341)) (n := 12)
    (lo := (20899841 / 62500000)) (hi := (334397457 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11176786548341 / 8000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(11176786548341 / 8000000000000) = 1/(500000000000 / 11176786548341) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (48546659 / 15625000) (3106986181 / 1000000000) (Real.log (11176786548341 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (11176786548341 / 500000000000) = -Real.log (500000000000 / 11176786548341) := by
    rw [show ((11176786548341 / 500000000000) : ℝ) = ((500000000000 / 11176786548341) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (1560157693 / 500000000) ≤ -Real.log (25000000000 / 566338079807) ∧
    -Real.log (25000000000 / 566338079807) ≤ (3120315391 / 1000000000) := by
  have h := checkLog_sound (w := (166338079807 / 966338079807)) (n := 12)
    (lo := (173863333 / 500000000)) (hi := (347726667 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((566338079807 / 400000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(566338079807 / 400000000000) = 1/(25000000000 / 566338079807) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (1560157693 / 500000000) (3120315391 / 1000000000) (Real.log (566338079807 / 25000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (566338079807 / 25000000000) = -Real.log (25000000000 / 566338079807) := by
    rw [show ((566338079807 / 25000000000) : ℝ) = ((25000000000 / 566338079807) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0170
