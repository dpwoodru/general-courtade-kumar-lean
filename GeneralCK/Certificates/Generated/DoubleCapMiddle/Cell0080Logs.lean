import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0080
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

theorem reflection_log_1_neg : (175025747 / 500000000) ≤ -Real.log (2560 / 3633) ∧
    -Real.log (2560 / 3633) ≤ (70010299 / 200000000) := by
  have h := checkLog_sound (w := (1073 / 6193)) (n := 12)
    (lo := (175025747 / 500000000)) (hi := (70010299 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3633 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3633 / 2560) = 1/(2560 / 3633) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (175025747 / 500000000) (70010299 / 200000000) (Real.log (3633 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3633 / 2560) = -Real.log (2560 / 3633) := by
    rw [show ((3633 / 2560) : ℝ) = ((2560 / 3633) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (543246591 / 1000000000) ≤ -Real.log (1487 / 2560) ∧
    -Real.log (1487 / 2560) ≤ (2122057 / 3906250) := by
  have h := checkLog_sound (w := (1073 / 4047)) (n := 12)
    (lo := (543246591 / 1000000000)) (hi := (2122057 / 3906250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1487) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1487) = 1/(1487 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-2122057 / 3906250) (-543246591 / 1000000000) (Real.log (1487 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (349225389 / 1000000000) ≤ -Real.log (256 / 363) ∧
    -Real.log (256 / 363) ≤ (34922539 / 100000000) := by
  have h := checkLog_sound (w := (107 / 619)) (n := 12)
    (lo := (349225389 / 1000000000)) (hi := (34922539 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((363 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(363 / 256) = 1/(256 / 363) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (349225389 / 1000000000) (34922539 / 100000000) (Real.log (363 / 256)) := by
  have h := reflection_log_3_neg
  have he : Real.log (363 / 256) = -Real.log (256 / 363) := by
    rw [show ((363 / 256) : ℝ) = ((256 / 363) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (270615569 / 500000000) ≤ -Real.log (149 / 256) ∧
    -Real.log (149 / 256) ≤ (541231139 / 1000000000) := by
  have h := checkLog_sound (w := (107 / 405)) (n := 12)
    (lo := (270615569 / 500000000)) (hi := (541231139 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((256 / 149) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(256 / 149) = 1/(149 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-541231139 / 1000000000) (-270615569 / 500000000) (Real.log (149 / 256)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (608831031 / 1000000000) ≤ -Real.log (1280 / 2353) ∧
    -Real.log (1280 / 2353) ≤ (76103879 / 125000000) := by
  have h := checkLog_sound (w := (1073 / 3633)) (n := 12)
    (lo := (608831031 / 1000000000)) (hi := (76103879 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2353 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2353 / 1280) = 1/(1280 / 2353) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (608831031 / 1000000000) (76103879 / 125000000) (Real.log (2353 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2353 / 1280) = -Real.log (1280 / 2353) := by
    rw [show ((2353 / 1280) : ℝ) = ((1280 / 2353) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (910948281 / 500000000) ≤ -Real.log (207 / 1280) ∧
    -Real.log (207 / 1280) ≤ (364379313 / 200000000) := by
  have h := checkLog_sound (w := (113 / 527)) (n := 12)
    (lo := (217801101 / 500000000)) (hi := (435602203 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 207) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(320 / 207) = 1/(207 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-364379313 / 200000000) (-910948281 / 500000000) (Real.log (207 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (2430221 / 4000000) ≤ -Real.log (128 / 235) ∧
    -Real.log (128 / 235) ≤ (607555251 / 1000000000) := by
  have h := checkLog_sound (w := (107 / 363)) (n := 12)
    (lo := (2430221 / 4000000)) (hi := (607555251 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((235 / 128) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(235 / 128) = 1/(128 / 235) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (2430221 / 4000000) (607555251 / 1000000000) (Real.log (235 / 128)) := by
  have h := reflection_log_7_neg
  have he : Real.log (235 / 128) = -Real.log (128 / 235) := by
    rw [show ((235 / 128) : ℝ) = ((128 / 235) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (72300313 / 40000000) ≤ -Real.log (21 / 128) ∧
    -Real.log (21 / 128) ≤ (451876957 / 250000000) := by
  have h := checkLog_sound (w := (11 / 53)) (n := 12)
    (lo := (84242693 / 200000000)) (hi := (210606733 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((32 / 21) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(32 / 21) = 1/(21 / 128) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-451876957 / 250000000) (-72300313 / 40000000) (Real.log (21 / 128)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (96108579 / 200000000) ≤ -Real.log (125000 / 202119) ∧
    -Real.log (125000 / 202119) ≤ (30033931 / 62500000) := by
  have h := checkLog_sound (w := (77119 / 327119)) (n := 12)
    (lo := (96108579 / 200000000)) (hi := (30033931 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((202119 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(202119 / 125000) = 1/(125000 / 202119) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (96108579 / 200000000) (30033931 / 62500000) (Real.log (202119 / 125000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (202119 / 125000) = -Real.log (125000 / 202119) := by
    rw [show ((202119 / 125000) : ℝ) = ((125000 / 202119) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (95959497 / 100000000) ≤ -Real.log (47881 / 125000) ∧
    -Real.log (47881 / 125000) ≤ (239898743 / 250000000) := by
  have h := checkLog_sound (w := (14619 / 110381)) (n := 12)
    (lo := (26644779 / 100000000)) (hi := (266447791 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 47881) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(62500 / 47881) = 1/(47881 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-239898743 / 250000000) (-95959497 / 100000000) (Real.log (47881 / 125000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (24087963 / 50000000) ≤ -Real.log (25000 / 40473) ∧
    -Real.log (25000 / 40473) ≤ (481759261 / 1000000000) := by
  have h := checkLog_sound (w := (15473 / 65473)) (n := 12)
    (lo := (24087963 / 50000000)) (hi := (481759261 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40473 / 25000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40473 / 25000) = 1/(25000 / 40473) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (24087963 / 50000000) (481759261 / 1000000000) (Real.log (40473 / 25000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (40473 / 25000) = -Real.log (25000 / 40473) := by
    rw [show ((40473 / 25000) : ℝ) = ((25000 / 40473) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (964745951 / 1000000000) ≤ -Real.log (9527 / 25000) ∧
    -Real.log (9527 / 25000) ≤ (964745953 / 1000000000) := by
  have h := checkLog_sound (w := (2973 / 22027)) (n := 12)
    (lo := (271598771 / 1000000000)) (hi := (67899693 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12500 / 9527) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(12500 / 9527) = 1/(9527 / 25000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-964745953 / 1000000000) (-964745951 / 1000000000) (Real.log (9527 / 25000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (99216897 / 250000000) ≤ -Real.log (1000000 / 1487159) ∧
    -Real.log (1000000 / 1487159) ≤ (396867589 / 1000000000) := by
  have h := checkLog_sound (w := (487159 / 2487159)) (n := 12)
    (lo := (99216897 / 250000000)) (hi := (396867589 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1487159 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1487159 / 1000000) = 1/(1000000 / 1487159) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (99216897 / 250000000) (396867589 / 1000000000) (Real.log (1487159 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1487159 / 1000000) = -Real.log (1000000 / 1487159) := by
    rw [show ((1487159 / 1000000) : ℝ) = ((1000000 / 1487159) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (667789423 / 1000000000) ≤ -Real.log (512841 / 1000000) ∧
    -Real.log (512841 / 1000000) ≤ (41736839 / 62500000) := by
  have h := checkLog_sound (w := (487159 / 1512841)) (n := 12)
    (lo := (667789423 / 1000000000)) (hi := (41736839 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 512841) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 512841) = 1/(512841 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-41736839 / 62500000) (-667789423 / 1000000000) (Real.log (512841 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (398153107 / 1000000000) ≤ -Real.log (62500 / 93067) ∧
    -Real.log (62500 / 93067) ≤ (99538277 / 250000000) := by
  have h := checkLog_sound (w := (30567 / 155567)) (n := 12)
    (lo := (398153107 / 1000000000)) (hi := (99538277 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((93067 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(93067 / 62500) = 1/(62500 / 93067) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (398153107 / 1000000000) (99538277 / 250000000) (Real.log (93067 / 62500)) := by
  have h := reflection_log_15_neg
  have he : Real.log (93067 / 62500) = -Real.log (62500 / 93067) := by
    rw [show ((93067 / 62500) : ℝ) = ((62500 / 93067) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (335763299 / 500000000) ≤ -Real.log (31933 / 62500) ∧
    -Real.log (31933 / 62500) ≤ (671526599 / 1000000000) := by
  have h := checkLog_sound (w := (30567 / 94433)) (n := 12)
    (lo := (335763299 / 500000000)) (hi := (671526599 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 31933) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 31933) = 1/(31933 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-671526599 / 1000000000) (-335763299 / 500000000) (Real.log (31933 / 62500)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (288027573 / 200000000) ≤ -Real.log (100000000000 / 422127775109) ∧
    -Real.log (100000000000 / 422127775109) ≤ (360034467 / 250000000) := by
  have h := checkLog_sound (w := (22127775109 / 822127775109)) (n := 12)
    (lo := (10768701 / 200000000)) (hi := (26921753 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((422127775109 / 400000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(422127775109 / 400000000000) = 1/(100000000000 / 422127775109) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (288027573 / 200000000) (360034467 / 250000000) (Real.log (422127775109 / 100000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (422127775109 / 100000000000) = -Real.log (100000000000 / 422127775109) := by
    rw [show ((422127775109 / 100000000000) : ℝ) = ((100000000000 / 422127775109) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1446505211 / 1000000000) ≤ -Real.log (125000000000 / 531030229873) ∧
    -Real.log (125000000000 / 531030229873) ≤ (723252607 / 500000000) := by
  have h := checkLog_sound (w := (31030229873 / 1031030229873)) (n := 12)
    (lo := (60210851 / 1000000000)) (hi := (15052713 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((531030229873 / 500000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(531030229873 / 500000000000) = 1/(125000000000 / 531030229873) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1446505211 / 1000000000) (723252607 / 500000000) (Real.log (531030229873 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (531030229873 / 125000000000) = -Real.log (125000000000 / 531030229873) := by
    rw [show ((531030229873 / 125000000000) : ℝ) = ((125000000000 / 531030229873) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1064657011 / 1000000000) ≤ -Real.log (125000000000 / 362480525153) ∧
    -Real.log (125000000000 / 362480525153) ≤ (1064657013 / 1000000000) := by
  have h := checkLog_sound (w := (112480525153 / 612480525153)) (n := 12)
    (lo := (371509831 / 1000000000)) (hi := (46438729 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((362480525153 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(362480525153 / 250000000000) = 1/(125000000000 / 362480525153) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (1064657011 / 1000000000) (1064657013 / 1000000000) (Real.log (362480525153 / 125000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (362480525153 / 125000000000) = -Real.log (125000000000 / 362480525153) := by
    rw [show ((362480525153 / 125000000000) : ℝ) = ((125000000000 / 362480525153) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (213935941 / 200000000) ≤ -Real.log (250000000000 / 728611467761) ∧
    -Real.log (250000000000 / 728611467761) ≤ (1069679707 / 1000000000) := by
  have h := checkLog_sound (w := (228611467761 / 1228611467761)) (n := 12)
    (lo := (15061301 / 40000000)) (hi := (188266263 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((728611467761 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(728611467761 / 500000000000) = 1/(250000000000 / 728611467761) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (213935941 / 200000000) (1069679707 / 1000000000) (Real.log (728611467761 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (728611467761 / 250000000000) = -Real.log (250000000000 / 728611467761) := by
    rw [show ((728611467761 / 250000000000) : ℝ) = ((250000000000 / 728611467761) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0080
