import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0261
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

theorem reflection_log_1_neg : (237878211 / 1000000000) ≤ -Real.log (1024 / 1299) ∧
    -Real.log (1024 / 1299) ≤ (59469553 / 250000000) := by
  have h := checkLog_sound (w := (275 / 2323)) (n := 12)
    (lo := (237878211 / 1000000000)) (hi := (59469553 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1299 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1299 / 1024) = 1/(1024 / 1299) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (237878211 / 1000000000) (59469553 / 250000000) (Real.log (1299 / 1024)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1299 / 1024) = -Real.log (1024 / 1299) := by
    rw [show ((1299 / 1024) : ℝ) = ((1024 / 1299) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (156366411 / 500000000) ≤ -Real.log (749 / 1024) ∧
    -Real.log (749 / 1024) ≤ (312732823 / 1000000000) := by
  have h := checkLog_sound (w := (275 / 1773)) (n := 12)
    (lo := (156366411 / 500000000)) (hi := (312732823 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 749) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 749) = 1/(749 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-312732823 / 1000000000) (-156366411 / 500000000) (Real.log (749 / 1024)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (23741621 / 100000000) ≤ -Real.log (1280 / 1623) ∧
    -Real.log (1280 / 1623) ≤ (237416211 / 1000000000) := by
  have h := checkLog_sound (w := (343 / 2903)) (n := 12)
    (lo := (23741621 / 100000000)) (hi := (237416211 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1623 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1623 / 1280) = 1/(1280 / 1623) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (23741621 / 100000000) (237416211 / 1000000000) (Real.log (1623 / 1280)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1623 / 1280) = -Real.log (1280 / 1623) := by
    rw [show ((1623 / 1280) : ℝ) = ((1280 / 1623) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (155966037 / 500000000) ≤ -Real.log (937 / 1280) ∧
    -Real.log (937 / 1280) ≤ (12477283 / 40000000) := by
  have h := checkLog_sound (w := (343 / 2217)) (n := 12)
    (lo := (155966037 / 500000000)) (hi := (12477283 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 937) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 937) = 1/(937 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-12477283 / 40000000) (-155966037 / 500000000) (Real.log (937 / 1280)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (429903623 / 1000000000) ≤ -Real.log (512 / 787) ∧
    -Real.log (512 / 787) ≤ (53737953 / 125000000) := by
  have h := checkLog_sound (w := (275 / 1299)) (n := 12)
    (lo := (429903623 / 1000000000)) (hi := (53737953 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((787 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(787 / 512) = 1/(512 / 787) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (429903623 / 1000000000) (53737953 / 125000000) (Real.log (787 / 512)) := by
  have h := reflection_log_5_neg
  have he : Real.log (787 / 512) = -Real.log (512 / 787) := by
    rw [show ((787 / 512) : ℝ) = ((512 / 787) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (770264483 / 1000000000) ≤ -Real.log (237 / 512) ∧
    -Real.log (237 / 512) ≤ (154052897 / 200000000) := by
  have h := checkLog_sound (w := (19 / 493)) (n := 12)
    (lo := (77117303 / 1000000000)) (hi := (9639663 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((256 / 237) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(256 / 237) = 1/(237 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-154052897 / 200000000) (-770264483 / 1000000000) (Real.log (237 / 512)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (429140943 / 1000000000) ≤ -Real.log (640 / 983) ∧
    -Real.log (640 / 983) ≤ (26821309 / 62500000) := by
  have h := checkLog_sound (w := (343 / 1623)) (n := 12)
    (lo := (429140943 / 1000000000)) (hi := (26821309 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((983 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(983 / 640) = 1/(640 / 983) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (429140943 / 1000000000) (26821309 / 62500000) (Real.log (983 / 640)) := by
  have h := reflection_log_7_neg
  have he : Real.log (983 / 640) = -Real.log (640 / 983) := by
    rw [show ((983 / 640) : ℝ) = ((640 / 983) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (191934009 / 250000000) ≤ -Real.log (297 / 640) ∧
    -Real.log (297 / 640) ≤ (383868019 / 500000000) := by
  have h := checkLog_sound (w := (23 / 617)) (n := 12)
    (lo := (9323607 / 125000000)) (hi := (74588857 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 297) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(320 / 297) = 1/(297 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-383868019 / 500000000) (-191934009 / 250000000) (Real.log (297 / 640)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (13003247 / 40000000) ≤ -Real.log (1000000 / 1384143) ∧
    -Real.log (1000000 / 1384143) ≤ (40635147 / 125000000) := by
  have h := checkLog_sound (w := (384143 / 2384143)) (n := 12)
    (lo := (13003247 / 40000000)) (hi := (40635147 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1384143 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1384143 / 1000000) = 1/(1000000 / 1384143) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (13003247 / 40000000) (40635147 / 125000000) (Real.log (1384143 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1384143 / 1000000) = -Real.log (1000000 / 1384143) := by
    rw [show ((1384143 / 1000000) : ℝ) = ((1000000 / 1384143) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (96948097 / 200000000) ≤ -Real.log (615857 / 1000000) ∧
    -Real.log (615857 / 1000000) ≤ (242370243 / 500000000) := by
  have h := checkLog_sound (w := (384143 / 1615857)) (n := 12)
    (lo := (96948097 / 200000000)) (hi := (242370243 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 615857) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 615857) = 1/(615857 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-242370243 / 500000000) (-96948097 / 200000000) (Real.log (615857 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (325707359 / 1000000000) ≤ -Real.log (100000 / 138501) ∧
    -Real.log (100000 / 138501) ≤ (2035671 / 6250000) := by
  have h := checkLog_sound (w := (38501 / 238501)) (n := 12)
    (lo := (325707359 / 1000000000)) (hi := (2035671 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((138501 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(138501 / 100000) = 1/(100000 / 138501) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (325707359 / 1000000000) (2035671 / 6250000) (Real.log (138501 / 100000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (138501 / 100000) = -Real.log (100000 / 138501) := by
    rw [show ((138501 / 100000) : ℝ) = ((100000 / 138501) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (486149271 / 1000000000) ≤ -Real.log (61499 / 100000) ∧
    -Real.log (61499 / 100000) ≤ (60768659 / 125000000) := by
  have h := checkLog_sound (w := (38501 / 161499)) (n := 12)
    (lo := (486149271 / 1000000000)) (hi := (60768659 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 61499) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 61499) = 1/(61499 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-60768659 / 125000000) (-486149271 / 1000000000) (Real.log (61499 / 100000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (249346047 / 1000000000) ≤ -Real.log (500000 / 641593) ∧
    -Real.log (500000 / 641593) ≤ (487004 / 1953125) := by
  have h := checkLog_sound (w := (141593 / 1141593)) (n := 12)
    (lo := (249346047 / 1000000000)) (hi := (487004 / 1953125))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((641593 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(641593 / 500000) = 1/(500000 / 641593) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (249346047 / 1000000000) (487004 / 1953125) (Real.log (641593 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (641593 / 500000) = -Real.log (500000 / 641593) := by
    rw [show ((641593 / 500000) : ℝ) = ((500000 / 641593) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (166469443 / 500000000) ≤ -Real.log (358407 / 500000) ∧
    -Real.log (358407 / 500000) ≤ (332938887 / 1000000000) := by
  have h := checkLog_sound (w := (141593 / 858407)) (n := 12)
    (lo := (166469443 / 500000000)) (hi := (332938887 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 358407) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 358407) = 1/(358407 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-332938887 / 1000000000) (-166469443 / 500000000) (Real.log (358407 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (124943371 / 500000000) ≤ -Real.log (25000 / 32097) ∧
    -Real.log (25000 / 32097) ≤ (249886743 / 1000000000) := by
  have h := checkLog_sound (w := (7097 / 57097)) (n := 12)
    (lo := (124943371 / 500000000)) (hi := (249886743 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((32097 / 25000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(32097 / 25000) = 1/(25000 / 32097) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (124943371 / 500000000) (249886743 / 1000000000) (Real.log (32097 / 25000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (32097 / 25000) = -Real.log (25000 / 32097) := by
    rw [show ((32097 / 25000) : ℝ) = ((25000 / 32097) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (41738441 / 125000000) ≤ -Real.log (17903 / 25000) ∧
    -Real.log (17903 / 25000) ≤ (333907529 / 1000000000) := by
  have h := checkLog_sound (w := (7097 / 42903)) (n := 12)
    (lo := (41738441 / 125000000)) (hi := (333907529 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 17903) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25000 / 17903) = 1/(17903 / 25000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-333907529 / 1000000000) (-41738441 / 125000000) (Real.log (17903 / 25000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (40491083 / 50000000) ≤ -Real.log (62500000000 / 140469195771) ∧
    -Real.log (62500000000 / 140469195771) ≤ (404910831 / 500000000) := by
  have h := checkLog_sound (w := (15469195771 / 265469195771)) (n := 12)
    (lo := (1458431 / 12500000)) (hi := (116674481 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((140469195771 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(140469195771 / 125000000000) = 1/(62500000000 / 140469195771) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (40491083 / 50000000) (404910831 / 500000000) (Real.log (140469195771 / 62500000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (140469195771 / 62500000000) = -Real.log (62500000000 / 140469195771) := by
    rw [show ((140469195771 / 62500000000) : ℝ) = ((62500000000 / 140469195771) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (81185663 / 100000000) ≤ -Real.log (250000000000 / 563021349941) ∧
    -Real.log (250000000000 / 563021349941) ≤ (101482079 / 125000000) := by
  have h := checkLog_sound (w := (63021349941 / 1063021349941)) (n := 12)
    (lo := (2374189 / 20000000)) (hi := (118709451 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((563021349941 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(563021349941 / 500000000000) = 1/(250000000000 / 563021349941) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (81185663 / 100000000) (101482079 / 125000000) (Real.log (563021349941 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (563021349941 / 250000000000) = -Real.log (250000000000 / 563021349941) := by
    rw [show ((563021349941 / 250000000000) : ℝ) = ((250000000000 / 563021349941) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (291142467 / 500000000) ≤ -Real.log (62500000000 / 111882754801) ∧
    -Real.log (62500000000 / 111882754801) ≤ (116456987 / 200000000) := by
  have h := checkLog_sound (w := (49382754801 / 174382754801)) (n := 12)
    (lo := (291142467 / 500000000)) (hi := (116456987 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((111882754801 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(111882754801 / 62500000000) = 1/(62500000000 / 111882754801) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (291142467 / 500000000) (116456987 / 200000000) (Real.log (111882754801 / 62500000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (111882754801 / 62500000000) = -Real.log (62500000000 / 111882754801) := by
    rw [show ((111882754801 / 62500000000) : ℝ) = ((62500000000 / 111882754801) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (583794271 / 1000000000) ≤ -Real.log (250000000000 / 448207004413) ∧
    -Real.log (250000000000 / 448207004413) ≤ (18243571 / 31250000) := by
  have h := checkLog_sound (w := (198207004413 / 698207004413)) (n := 12)
    (lo := (583794271 / 1000000000)) (hi := (18243571 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((448207004413 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(448207004413 / 250000000000) = 1/(250000000000 / 448207004413) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (583794271 / 1000000000) (18243571 / 31250000) (Real.log (448207004413 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (448207004413 / 250000000000) = -Real.log (250000000000 / 448207004413) := by
    rw [show ((448207004413 / 250000000000) : ℝ) = ((250000000000 / 448207004413) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0261
