import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0210
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

theorem reflection_log_1_neg : (130580809 / 500000000) ≤ -Real.log (640 / 831) ∧
    -Real.log (640 / 831) ≤ (261161619 / 1000000000) := by
  have h := checkLog_sound (w := (191 / 1471)) (n := 12)
    (lo := (130580809 / 500000000)) (hi := (261161619 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((831 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(831 / 640) = 1/(640 / 831) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (130580809 / 500000000) (261161619 / 1000000000) (Real.log (831 / 640)) := by
  have h := reflection_log_1_neg
  have he : Real.log (831 / 640) = -Real.log (640 / 831) := by
    rw [show ((831 / 640) : ℝ) = ((640 / 831) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (44305661 / 125000000) ≤ -Real.log (449 / 640) ∧
    -Real.log (449 / 640) ≤ (354445289 / 1000000000) := by
  have h := checkLog_sound (w := (191 / 1089)) (n := 12)
    (lo := (44305661 / 125000000)) (hi := (354445289 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 449) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 449) = 1/(449 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-354445289 / 1000000000) (-44305661 / 125000000) (Real.log (449 / 640)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (260710253 / 1000000000) ≤ -Real.log (1024 / 1329) ∧
    -Real.log (1024 / 1329) ≤ (130355127 / 500000000) := by
  have h := checkLog_sound (w := (305 / 2353)) (n := 12)
    (lo := (260710253 / 1000000000)) (hi := (130355127 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1329 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1329 / 1024) = 1/(1024 / 1329) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (260710253 / 1000000000) (130355127 / 500000000) (Real.log (1329 / 1024)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1329 / 1024) = -Real.log (1024 / 1329) := by
    rw [show ((1329 / 1024) : ℝ) = ((1024 / 1329) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (353610447 / 1000000000) ≤ -Real.log (719 / 1024) ∧
    -Real.log (719 / 1024) ≤ (22100653 / 62500000) := by
  have h := checkLog_sound (w := (305 / 1743)) (n := 12)
    (lo := (353610447 / 1000000000)) (hi := (22100653 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 719) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 719) = 1/(719 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-22100653 / 62500000) (-353610447 / 1000000000) (Real.log (719 / 1024)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (234024297 / 500000000) ≤ -Real.log (320 / 511) ∧
    -Real.log (320 / 511) ≤ (93609719 / 200000000) := by
  have h := checkLog_sound (w := (191 / 831)) (n := 12)
    (lo := (234024297 / 500000000)) (hi := (93609719 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((511 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(511 / 320) = 1/(320 / 511) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (234024297 / 500000000) (93609719 / 200000000) (Real.log (511 / 320)) := by
  have h := reflection_log_5_neg
  have he : Real.log (511 / 320) = -Real.log (320 / 511) := by
    rw [show ((511 / 320) : ℝ) = ((320 / 511) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (90850859 / 100000000) ≤ -Real.log (129 / 320) ∧
    -Real.log (129 / 320) ≤ (56781787 / 62500000) := by
  have h := checkLog_sound (w := (31 / 289)) (n := 12)
    (lo := (21536141 / 100000000)) (hi := (215361411 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 129) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(160 / 129) = 1/(129 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-56781787 / 62500000) (-90850859 / 100000000) (Real.log (129 / 320)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (467314469 / 1000000000) ≤ -Real.log (512 / 817) ∧
    -Real.log (512 / 817) ≤ (46731447 / 100000000) := by
  have h := checkLog_sound (w := (305 / 1329)) (n := 12)
    (lo := (467314469 / 1000000000)) (hi := (46731447 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((817 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(817 / 512) = 1/(512 / 817) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (467314469 / 1000000000) (46731447 / 100000000) (Real.log (817 / 512)) := by
  have h := reflection_log_7_neg
  have he : Real.log (817 / 512) = -Real.log (512 / 817) := by
    rw [show ((817 / 512) : ℝ) = ((512 / 817) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (905605831 / 1000000000) ≤ -Real.log (207 / 512) ∧
    -Real.log (207 / 512) ≤ (905605833 / 1000000000) := by
  have h := checkLog_sound (w := (49 / 463)) (n := 12)
    (lo := (212458651 / 1000000000)) (hi := (53114663 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((256 / 207) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(256 / 207) = 1/(207 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-905605833 / 1000000000) (-905605831 / 1000000000) (Real.log (207 / 512)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (356694243 / 1000000000) ≤ -Real.log (1000000 / 1428599) ∧
    -Real.log (1000000 / 1428599) ≤ (89173561 / 250000000) := by
  have h := checkLog_sound (w := (428599 / 2428599)) (n := 12)
    (lo := (356694243 / 1000000000)) (hi := (89173561 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1428599 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1428599 / 1000000) = 1/(1000000 / 1428599) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (356694243 / 1000000000) (89173561 / 250000000) (Real.log (1428599 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1428599 / 1000000) = -Real.log (1000000 / 1428599) := by
    rw [show ((1428599 / 1000000) : ℝ) = ((1000000 / 1428599) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (559664039 / 1000000000) ≤ -Real.log (571401 / 1000000) ∧
    -Real.log (571401 / 1000000) ≤ (13991601 / 25000000) := by
  have h := checkLog_sound (w := (428599 / 1571401)) (n := 12)
    (lo := (559664039 / 1000000000)) (hi := (13991601 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 571401) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 571401) = 1/(571401 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-13991601 / 25000000) (-559664039 / 1000000000) (Real.log (571401 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (178654671 / 500000000) ≤ -Real.log (500000 / 714739) ∧
    -Real.log (500000 / 714739) ≤ (357309343 / 1000000000) := by
  have h := checkLog_sound (w := (214739 / 1214739)) (n := 12)
    (lo := (178654671 / 500000000)) (hi := (357309343 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((714739 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(714739 / 500000) = 1/(500000 / 714739) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (178654671 / 500000000) (357309343 / 1000000000) (Real.log (714739 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (714739 / 500000) = -Real.log (500000 / 714739) := by
    rw [show ((714739 / 500000) : ℝ) = ((500000 / 714739) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (561203547 / 1000000000) ≤ -Real.log (285261 / 500000) ∧
    -Real.log (285261 / 500000) ≤ (140300887 / 250000000) := by
  have h := checkLog_sound (w := (214739 / 785261)) (n := 12)
    (lo := (561203547 / 1000000000)) (hi := (140300887 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 285261) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 285261) = 1/(285261 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-140300887 / 250000000) (-561203547 / 1000000000) (Real.log (285261 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (55415559 / 200000000) ≤ -Real.log (1000000 / 1319269) ∧
    -Real.log (1000000 / 1319269) ≤ (69269449 / 250000000) := by
  have h := checkLog_sound (w := (319269 / 2319269)) (n := 12)
    (lo := (55415559 / 200000000)) (hi := (69269449 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1319269 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1319269 / 1000000) = 1/(1000000 / 1319269) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (55415559 / 200000000) (69269449 / 250000000) (Real.log (1319269 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1319269 / 1000000) = -Real.log (1000000 / 1319269) := by
    rw [show ((1319269 / 1000000) : ℝ) = ((1000000 / 1319269) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (192294029 / 500000000) ≤ -Real.log (680731 / 1000000) ∧
    -Real.log (680731 / 1000000) ≤ (384588059 / 1000000000) := by
  have h := checkLog_sound (w := (319269 / 1680731)) (n := 12)
    (lo := (192294029 / 500000000)) (hi := (384588059 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 680731) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 680731) = 1/(680731 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-384588059 / 1000000000) (-192294029 / 500000000) (Real.log (680731 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (277627191 / 1000000000) ≤ -Real.log (500000 / 659997) ∧
    -Real.log (500000 / 659997) ≤ (34703399 / 125000000) := by
  have h := checkLog_sound (w := (159997 / 1159997)) (n := 12)
    (lo := (277627191 / 1000000000)) (hi := (34703399 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((659997 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(659997 / 500000) = 1/(500000 / 659997) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (277627191 / 1000000000) (34703399 / 125000000) (Real.log (659997 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (659997 / 500000) = -Real.log (500000 / 659997) := by
    rw [show ((659997 / 500000) : ℝ) = ((500000 / 659997) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (385653657 / 1000000000) ≤ -Real.log (340003 / 500000) ∧
    -Real.log (340003 / 500000) ≤ (192826829 / 500000000) := by
  have h := checkLog_sound (w := (159997 / 840003)) (n := 12)
    (lo := (385653657 / 1000000000)) (hi := (192826829 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 340003) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 340003) = 1/(340003 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-192826829 / 500000000) (-385653657 / 1000000000) (Real.log (340003 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (458179141 / 500000000) ≤ -Real.log (250000000000 / 625042220787) ∧
    -Real.log (250000000000 / 625042220787) ≤ (229089571 / 250000000) := by
  have h := checkLog_sound (w := (125042220787 / 1125042220787)) (n := 12)
    (lo := (111605551 / 500000000)) (hi := (223211103 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625042220787 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(625042220787 / 500000000000) = 1/(250000000000 / 625042220787) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (458179141 / 500000000) (229089571 / 250000000) (Real.log (625042220787 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (625042220787 / 250000000000) = -Real.log (250000000000 / 625042220787) := by
    rw [show ((625042220787 / 250000000000) : ℝ) = ((250000000000 / 625042220787) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (918512889 / 1000000000) ≤ -Real.log (500000000000 / 1252780786719) ∧
    -Real.log (500000000000 / 1252780786719) ≤ (918512891 / 1000000000) := by
  have h := checkLog_sound (w := (252780786719 / 2252780786719)) (n := 12)
    (lo := (225365709 / 1000000000)) (hi := (22536571 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1252780786719 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1252780786719 / 1000000000000) = 1/(500000000000 / 1252780786719) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (918512889 / 1000000000) (918512891 / 1000000000) (Real.log (1252780786719 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1252780786719 / 500000000000) = -Real.log (500000000000 / 1252780786719) := by
    rw [show ((1252780786719 / 500000000000) : ℝ) = ((500000000000 / 1252780786719) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (661665853 / 1000000000) ≤ -Real.log (125000000000 / 242252262641) ∧
    -Real.log (125000000000 / 242252262641) ≤ (330832927 / 500000000) := by
  have h := checkLog_sound (w := (117252262641 / 367252262641)) (n := 12)
    (lo := (661665853 / 1000000000)) (hi := (330832927 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((242252262641 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(242252262641 / 125000000000) = 1/(125000000000 / 242252262641) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (661665853 / 1000000000) (330832927 / 500000000) (Real.log (242252262641 / 125000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (242252262641 / 125000000000) = -Real.log (125000000000 / 242252262641) := by
    rw [show ((242252262641 / 125000000000) : ℝ) = ((125000000000 / 242252262641) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (41455053 / 62500000) ≤ -Real.log (500000000000 / 970575259631) ∧
    -Real.log (500000000000 / 970575259631) ≤ (663280849 / 1000000000) := by
  have h := checkLog_sound (w := (470575259631 / 1470575259631)) (n := 12)
    (lo := (41455053 / 62500000)) (hi := (663280849 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((970575259631 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(970575259631 / 500000000000) = 1/(500000000000 / 970575259631) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (41455053 / 62500000) (663280849 / 1000000000) (Real.log (970575259631 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (970575259631 / 500000000000) = -Real.log (500000000000 / 970575259631) := by
    rw [show ((970575259631 / 500000000000) : ℝ) = ((500000000000 / 970575259631) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0210
