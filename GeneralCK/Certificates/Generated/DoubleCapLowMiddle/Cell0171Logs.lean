import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0171
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

theorem reflection_log_1_neg : (637072737 / 1000000000) ≤ -Real.log (3200 / 6051) ∧
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


theorem reflection_log_1 : Bounds (637072737 / 1000000000) (318536369 / 500000000) (Real.log (6051 / 3200)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6051 / 3200) = -Real.log (3200 / 6051) := by
    rw [show ((6051 / 3200) : ℝ) = ((3200 / 6051) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (553958541 / 250000000) ≤ -Real.log (349 / 3200) ∧
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


theorem reflection_log_2 : Bounds (-276979271 / 125000000) (-553958541 / 250000000) (Real.log (349 / 3200)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (127257487 / 200000000) ≤ -Real.log (2560 / 4837) ∧
    -Real.log (2560 / 4837) ≤ (159071859 / 250000000) := by
  have h := checkLog_sound (w := (2277 / 7397)) (n := 12)
    (lo := (127257487 / 200000000)) (hi := (159071859 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4837 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4837 / 2560) = 1/(2560 / 4837) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (127257487 / 200000000) (159071859 / 250000000) (Real.log (4837 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (4837 / 2560) = -Real.log (2560 / 4837) := by
    rw [show ((4837 / 2560) : ℝ) = ((2560 / 4837) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (1101157819 / 500000000) ≤ -Real.log (283 / 2560) ∧
    -Real.log (283 / 2560) ≤ (1101157821 / 500000000) := by
  have h := checkLog_sound (w := (37 / 603)) (n := 12)
    (lo := (61437049 / 500000000)) (hi := (122874099 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 283) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(320 / 283) = 1/(283 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-1101157821 / 500000000) (-1101157819 / 500000000) (Real.log (283 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (28883309 / 50000000) ≤ -Real.log (1600 / 2851) ∧
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


theorem reflection_log_5 : Bounds (28883309 / 50000000) (577666181 / 1000000000) (Real.log (2851 / 1600)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2851 / 1600) = -Real.log (1600 / 2851) := by
    rw [show ((2851 / 1600) : ℝ) = ((1600 / 2851) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (190335873 / 125000000) ≤ -Real.log (349 / 1600) ∧
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


theorem reflection_log_6 : Bounds (-1522686987 / 1000000000) (-190335873 / 125000000) (Real.log (349 / 1600)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (575998709 / 1000000000) ≤ -Real.log (1280 / 2277) ∧
    -Real.log (1280 / 2277) ≤ (57599871 / 100000000) := by
  have h := checkLog_sound (w := (997 / 3557)) (n := 12)
    (lo := (575998709 / 1000000000)) (hi := (57599871 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2277 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2277 / 1280) = 1/(1280 / 2277) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (575998709 / 1000000000) (57599871 / 100000000) (Real.log (2277 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2277 / 1280) = -Real.log (1280 / 2277) := by
    rw [show ((2277 / 1280) : ℝ) = ((1280 / 2277) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (754584229 / 500000000) ≤ -Real.log (283 / 1280) ∧
    -Real.log (283 / 1280) ≤ (1509168461 / 1000000000) := by
  have h := checkLog_sound (w := (37 / 603)) (n := 12)
    (lo := (61437049 / 500000000)) (hi := (122874099 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 283) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(320 / 283) = 1/(283 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1509168461 / 1000000000) (-754584229 / 500000000) (Real.log (283 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (81297443 / 125000000) ≤ -Real.log (250000 / 479067) ∧
    -Real.log (250000 / 479067) ≤ (130075909 / 200000000) := by
  have h := checkLog_sound (w := (229067 / 729067)) (n := 12)
    (lo := (81297443 / 125000000)) (hi := (130075909 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((479067 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(479067 / 250000) = 1/(250000 / 479067) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (81297443 / 125000000) (130075909 / 200000000) (Real.log (479067 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (479067 / 250000) = -Real.log (250000 / 479067) := by
    rw [show ((479067 / 250000) : ℝ) = ((250000 / 479067) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (496026811 / 200000000) ≤ -Real.log (20933 / 250000) ∧
    -Real.log (20933 / 250000) ≤ (2480134059 / 1000000000) := by
  have h := checkLog_sound (w := (10317 / 52183)) (n := 12)
    (lo := (80138503 / 200000000)) (hi := (100173129 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 20933) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(31250 / 20933) = 1/(20933 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-2480134059 / 1000000000) (-496026811 / 200000000) (Real.log (20933 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (650897083 / 1000000000) ≤ -Real.log (50000 / 95863) ∧
    -Real.log (50000 / 95863) ≤ (162724271 / 250000000) := by
  have h := checkLog_sound (w := (45863 / 145863)) (n := 12)
    (lo := (650897083 / 1000000000)) (hi := (162724271 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((95863 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(95863 / 50000) = 1/(50000 / 95863) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (650897083 / 1000000000) (162724271 / 250000000) (Real.log (95863 / 50000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (95863 / 50000) = -Real.log (50000 / 95863) := by
    rw [show ((95863 / 50000) : ℝ) = ((50000 / 95863) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (623013029 / 250000000) ≤ -Real.log (4137 / 50000) ∧
    -Real.log (4137 / 50000) ≤ (62301303 / 25000000) := by
  have h := checkLog_sound (w := (2113 / 10387)) (n := 12)
    (lo := (25788161 / 62500000)) (hi := (412610577 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6250 / 4137) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(6250 / 4137) = 1/(4137 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-62301303 / 25000000) (-623013029 / 250000000) (Real.log (4137 / 50000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (162204239 / 250000000) ≤ -Real.log (250000 / 478319) ∧
    -Real.log (250000 / 478319) ≤ (648816957 / 1000000000) := by
  have h := checkLog_sound (w := (228319 / 728319)) (n := 12)
    (lo := (162204239 / 250000000)) (hi := (648816957 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((478319 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(478319 / 250000) = 1/(250000 / 478319) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (162204239 / 250000000) (648816957 / 1000000000) (Real.log (478319 / 250000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (478319 / 250000) = -Real.log (250000 / 478319) := by
    rw [show ((478319 / 250000) : ℝ) = ((250000 / 478319) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (489004923 / 200000000) ≤ -Real.log (21681 / 250000) ∧
    -Real.log (21681 / 250000) ≤ (2445024619 / 1000000000) := by
  have h := checkLog_sound (w := (9569 / 52931)) (n := 12)
    (lo := (14623323 / 40000000)) (hi := (91395769 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 21681) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(31250 / 21681) = 1/(21681 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-2445024619 / 1000000000) (-489004923 / 200000000) (Real.log (21681 / 250000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (129876777 / 200000000) ≤ -Real.log (1000000 / 1914361) ∧
    -Real.log (1000000 / 1914361) ≤ (324691943 / 500000000) := by
  have h := checkLog_sound (w := (914361 / 2914361)) (n := 12)
    (lo := (129876777 / 200000000)) (hi := (324691943 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1914361 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1914361 / 1000000) = 1/(1000000 / 1914361) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (129876777 / 200000000) (324691943 / 500000000) (Real.log (1914361 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1914361 / 1000000) = -Real.log (1000000 / 1914361) := by
    rw [show ((1914361 / 1000000) : ℝ) = ((1000000 / 1914361) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (245761449 / 100000000) ≤ -Real.log (85639 / 1000000) ∧
    -Real.log (85639 / 1000000) ≤ (1228807247 / 500000000) := by
  have h := checkLog_sound (w := (39361 / 210639)) (n := 12)
    (lo := (7563459 / 20000000)) (hi := (378172951 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 85639) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125000 / 85639) = 1/(85639 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-1228807247 / 500000000) (-245761449 / 100000000) (Real.log (85639 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (3130513599 / 1000000000) ≤ -Real.log (2000000000 / 45771461329) ∧
    -Real.log (2000000000 / 45771461329) ≤ (782628401 / 250000000) := by
  have h := checkLog_sound (w := (13771461329 / 77771461329)) (n := 12)
    (lo := (357924879 / 1000000000)) (hi := (4474061 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((45771461329 / 32000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(45771461329 / 32000000000) = 1/(2000000000 / 45771461329) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (3130513599 / 1000000000) (782628401 / 250000000) (Real.log (45771461329 / 2000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (45771461329 / 2000000000) = -Real.log (2000000000 / 45771461329) := by
    rw [show ((45771461329 / 2000000000) : ℝ) = ((2000000000 / 45771461329) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (3142949199 / 1000000000) ≤ -Real.log (50000000000 / 1158605269519) ∧
    -Real.log (50000000000 / 1158605269519) ≤ (785737301 / 250000000) := by
  have h := checkLog_sound (w := (358605269519 / 1958605269519)) (n := 12)
    (lo := (370360479 / 1000000000)) (hi := (2314753 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1158605269519 / 800000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1158605269519 / 800000000000) = 1/(50000000000 / 1158605269519) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (3142949199 / 1000000000) (785737301 / 250000000) (Real.log (1158605269519 / 50000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1158605269519 / 50000000000) = -Real.log (50000000000 / 1158605269519) := by
    rw [show ((1158605269519 / 50000000000) : ℝ) = ((50000000000 / 1158605269519) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (309384157 / 100000000) ≤ -Real.log (500000000000 / 11030833448641) ∧
    -Real.log (500000000000 / 11030833448641) ≤ (123753663 / 40000000) := by
  have h := checkLog_sound (w := (3030833448641 / 19030833448641)) (n := 12)
    (lo := (6425057 / 20000000)) (hi := (321252851 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11030833448641 / 8000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(11030833448641 / 8000000000000) = 1/(500000000000 / 11030833448641) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (309384157 / 100000000) (123753663 / 40000000) (Real.log (11030833448641 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (11030833448641 / 500000000000) = -Real.log (500000000000 / 11030833448641) := by
    rw [show ((11030833448641 / 500000000000) : ℝ) = ((500000000000 / 11030833448641) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (24855987 / 8000000) ≤ -Real.log (500000000000 / 11176922897279) ∧
    -Real.log (500000000000 / 11176922897279) ≤ (155349919 / 50000000) := by
  have h := checkLog_sound (w := (3176922897279 / 19176922897279)) (n := 12)
    (lo := (66881931 / 200000000)) (hi := (41801207 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11176922897279 / 8000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(11176922897279 / 8000000000000) = 1/(500000000000 / 11176922897279) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (24855987 / 8000000) (155349919 / 50000000) (Real.log (11176922897279 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (11176922897279 / 500000000000) = -Real.log (500000000000 / 11176922897279) := by
    rw [show ((11176922897279 / 500000000000) : ℝ) = ((500000000000 / 11176922897279) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0171
