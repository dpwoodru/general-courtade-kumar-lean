import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0116
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

theorem reflection_log_1_neg : (133521799 / 200000000) ≤ -Real.log (25600 / 49909) ∧
    -Real.log (25600 / 49909) ≤ (166902249 / 250000000) := by
  have h := checkLog_sound (w := (24309 / 75509)) (n := 12)
    (lo := (133521799 / 200000000)) (hi := (166902249 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49909 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49909 / 25600) = 1/(25600 / 49909) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (133521799 / 200000000) (166902249 / 250000000) (Real.log (49909 / 25600)) := by
  have h := reflection_log_1_neg
  have he : Real.log (49909 / 25600) = -Real.log (25600 / 49909) := by
    rw [show ((49909 / 25600) : ℝ) = ((25600 / 49909) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (2987175237 / 1000000000) ≤ -Real.log (1291 / 25600) ∧
    -Real.log (1291 / 25600) ≤ (1493587621 / 500000000) := by
  have h := checkLog_sound (w := (309 / 2891)) (n := 12)
    (lo := (214586517 / 1000000000)) (hi := (107293259 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1291) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1600 / 1291) = 1/(1291 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-1493587621 / 500000000) (-2987175237 / 1000000000) (Real.log (1291 / 25600)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (66722823 / 100000000) ≤ -Real.log (2560 / 4989) ∧
    -Real.log (2560 / 4989) ≤ (667228231 / 1000000000) := by
  have h := checkLog_sound (w := (2429 / 7549)) (n := 12)
    (lo := (66722823 / 100000000)) (hi := (667228231 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4989 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4989 / 2560) = 1/(2560 / 4989) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (66722823 / 100000000) (667228231 / 1000000000) (Real.log (4989 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (4989 / 2560) = -Real.log (2560 / 4989) := by
    rw [show ((4989 / 2560) : ℝ) = ((2560 / 4989) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (743141303 / 250000000) ≤ -Real.log (131 / 2560) ∧
    -Real.log (131 / 2560) ≤ (2972565217 / 1000000000) := by
  have h := checkLog_sound (w := (29 / 291)) (n := 12)
    (lo := (49994123 / 250000000)) (hi := (199976493 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 131) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(160 / 131) = 1/(131 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-2972565217 / 1000000000) (-743141303 / 250000000) (Real.log (131 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (641401481 / 1000000000) ≤ -Real.log (12800 / 24309) ∧
    -Real.log (12800 / 24309) ≤ (320700741 / 500000000) := by
  have h := checkLog_sound (w := (11509 / 37109)) (n := 12)
    (lo := (641401481 / 1000000000)) (hi := (320700741 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24309 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24309 / 12800) = 1/(12800 / 24309) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (641401481 / 1000000000) (320700741 / 500000000) (Real.log (24309 / 12800)) := by
  have h := reflection_log_5_neg
  have he : Real.log (24309 / 12800) = -Real.log (12800 / 24309) := by
    rw [show ((24309 / 12800) : ℝ) = ((12800 / 24309) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (2294028057 / 1000000000) ≤ -Real.log (1291 / 12800) ∧
    -Real.log (1291 / 12800) ≤ (2294028061 / 1000000000) := by
  have h := checkLog_sound (w := (309 / 2891)) (n := 12)
    (lo := (214586517 / 1000000000)) (hi := (107293259 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1291) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1600 / 1291) = 1/(1291 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-2294028061 / 1000000000) (-2294028057 / 1000000000) (Real.log (1291 / 12800)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (160154893 / 250000000) ≤ -Real.log (1280 / 2429) ∧
    -Real.log (1280 / 2429) ≤ (640619573 / 1000000000) := by
  have h := checkLog_sound (w := (1149 / 3709)) (n := 12)
    (lo := (160154893 / 250000000)) (hi := (640619573 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2429 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2429 / 1280) = 1/(1280 / 2429) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (160154893 / 250000000) (640619573 / 1000000000) (Real.log (2429 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2429 / 1280) = -Real.log (1280 / 2429) := by
    rw [show ((2429 / 1280) : ℝ) = ((1280 / 2429) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (142463627 / 62500000) ≤ -Real.log (131 / 1280) ∧
    -Real.log (131 / 1280) ≤ (569854509 / 250000000) := by
  have h := checkLog_sound (w := (29 / 291)) (n := 12)
    (lo := (49994123 / 250000000)) (hi := (199976493 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 131) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(160 / 131) = 1/(131 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-569854509 / 250000000) (-142463627 / 62500000) (Real.log (131 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (672170193 / 1000000000) ≤ -Real.log (1000000 / 1958483) ∧
    -Real.log (1000000 / 1958483) ≤ (336085097 / 500000000) := by
  have h := checkLog_sound (w := (958483 / 2958483)) (n := 12)
    (lo := (672170193 / 1000000000)) (hi := (336085097 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1958483 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1958483 / 1000000) = 1/(1000000 / 1958483) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (672170193 / 1000000000) (336085097 / 500000000) (Real.log (1958483 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1958483 / 1000000) = -Real.log (1000000 / 1958483) := by
    rw [show ((1958483 / 1000000) : ℝ) = ((1000000 / 1958483) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (1590826147 / 500000000) ≤ -Real.log (41517 / 1000000) ∧
    -Real.log (41517 / 1000000) ≤ (3181652299 / 1000000000) := by
  have h := checkLog_sound (w := (20983 / 104017)) (n := 12)
    (lo := (204531787 / 500000000)) (hi := (16362543 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 41517) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 41517) = 1/(41517 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-3181652299 / 1000000000) (-1590826147 / 500000000) (Real.log (41517 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (67245813 / 100000000) ≤ -Real.log (1000000 / 1959047) ∧
    -Real.log (1000000 / 1959047) ≤ (672458131 / 1000000000) := by
  have h := checkLog_sound (w := (959047 / 2959047)) (n := 12)
    (lo := (67245813 / 100000000)) (hi := (672458131 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1959047 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1959047 / 1000000) = 1/(1000000 / 1959047) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (67245813 / 100000000) (672458131 / 1000000000) (Real.log (1959047 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1959047 / 1000000) = -Real.log (1000000 / 1959047) := by
    rw [show ((1959047 / 1000000) : ℝ) = ((1000000 / 1959047) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (3195330209 / 1000000000) ≤ -Real.log (40953 / 1000000) ∧
    -Real.log (40953 / 1000000) ≤ (1597665107 / 500000000) := by
  have h := checkLog_sound (w := (21547 / 103453)) (n := 12)
    (lo := (422741489 / 1000000000)) (hi := (42274149 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 40953) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 40953) = 1/(40953 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1597665107 / 500000000) (-3195330209 / 1000000000) (Real.log (40953 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (671911797 / 1000000000) ≤ -Real.log (1000000 / 1957977) ∧
    -Real.log (1000000 / 1957977) ≤ (335955899 / 500000000) := by
  have h := checkLog_sound (w := (957977 / 2957977)) (n := 12)
    (lo := (671911797 / 1000000000)) (hi := (335955899 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1957977 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1957977 / 1000000) = 1/(1000000 / 1957977) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (671911797 / 1000000000) (335955899 / 500000000) (Real.log (1957977 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1957977 / 1000000) = -Real.log (1000000 / 1957977) := by
    rw [show ((1957977 / 1000000) : ℝ) = ((1000000 / 1957977) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (3169538189 / 1000000000) ≤ -Real.log (42023 / 1000000) ∧
    -Real.log (42023 / 1000000) ≤ (1584769097 / 500000000) := by
  have h := checkLog_sound (w := (20477 / 104523)) (n := 12)
    (lo := (396949469 / 1000000000)) (hi := (39694947 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 42023) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 42023) = 1/(42023 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-1584769097 / 500000000) (-3169538189 / 1000000000) (Real.log (42023 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (672207977 / 1000000000) ≤ -Real.log (1000000 / 1958557) ∧
    -Real.log (1000000 / 1958557) ≤ (336103989 / 500000000) := by
  have h := checkLog_sound (w := (958557 / 2958557)) (n := 12)
    (lo := (672207977 / 1000000000)) (hi := (336103989 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1958557 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1958557 / 1000000) = 1/(1000000 / 1958557) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (672207977 / 1000000000) (336103989 / 500000000) (Real.log (1958557 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1958557 / 1000000) = -Real.log (1000000 / 1958557) := by
    rw [show ((1958557 / 1000000) : ℝ) = ((1000000 / 1958557) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (3183436287 / 1000000000) ≤ -Real.log (41443 / 1000000) ∧
    -Real.log (41443 / 1000000) ≤ (795859073 / 250000000) := by
  have h := checkLog_sound (w := (21057 / 103943)) (n := 12)
    (lo := (410847567 / 1000000000)) (hi := (25677973 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 41443) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 41443) = 1/(41443 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-795859073 / 250000000) (-3183436287 / 1000000000) (Real.log (41443 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (481727811 / 125000000) ≤ -Real.log (500000000000 / 23586518775441) ∧
    -Real.log (500000000000 / 23586518775441) ≤ (1926911247 / 500000000) := by
  have h := checkLog_sound (w := (7586518775441 / 39586518775441)) (n := 12)
    (lo := (97021647 / 250000000)) (hi := (388086589 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((23586518775441 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(23586518775441 / 16000000000000) = 1/(500000000000 / 23586518775441) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (481727811 / 125000000) (1926911247 / 500000000) (Real.log (23586518775441 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (23586518775441 / 500000000000) = -Real.log (500000000000 / 23586518775441) := by
    rw [show ((23586518775441 / 500000000000) : ℝ) = ((500000000000 / 23586518775441) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (3867788339 / 1000000000) ≤ -Real.log (500000000000 / 23918235538301) ∧
    -Real.log (500000000000 / 23918235538301) ≤ (773557669 / 200000000) := by
  have h := checkLog_sound (w := (7918235538301 / 39918235538301)) (n := 12)
    (lo := (402052439 / 1000000000)) (hi := (10051311 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((23918235538301 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(23918235538301 / 16000000000000) = 1/(500000000000 / 23918235538301) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (3867788339 / 1000000000) (773557669 / 200000000) (Real.log (23918235538301 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (23918235538301 / 500000000000) = -Real.log (500000000000 / 23918235538301) := by
    rw [show ((23918235538301 / 500000000000) : ℝ) = ((500000000000 / 23918235538301) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1920724993 / 500000000) ≤ -Real.log (25000000000 / 1164824619851) ∧
    -Real.log (25000000000 / 1164824619851) ≤ (480181249 / 125000000) := by
  have h := checkLog_sound (w := (364824619851 / 1964824619851)) (n := 12)
    (lo := (187857043 / 500000000)) (hi := (375714087 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1164824619851 / 800000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(1164824619851 / 800000000000) = 1/(25000000000 / 1164824619851) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (1920724993 / 500000000) (480181249 / 125000000) (Real.log (1164824619851 / 25000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (1164824619851 / 25000000000) = -Real.log (25000000000 / 1164824619851) := by
    rw [show ((1164824619851 / 25000000000) : ℝ) = ((25000000000 / 1164824619851) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (481955533 / 125000000) ≤ -Real.log (500000000000 / 23629527302561) ∧
    -Real.log (500000000000 / 23629527302561) ≤ (385564427 / 100000000) := by
  have h := checkLog_sound (w := (7629527302561 / 39629527302561)) (n := 12)
    (lo := (97477091 / 250000000)) (hi := (77981673 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((23629527302561 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(23629527302561 / 16000000000000) = 1/(500000000000 / 23629527302561) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (481955533 / 125000000) (385564427 / 100000000) (Real.log (23629527302561 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (23629527302561 / 500000000000) = -Real.log (500000000000 / 23629527302561) := by
    rw [show ((23629527302561 / 500000000000) : ℝ) = ((500000000000 / 23629527302561) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0116
