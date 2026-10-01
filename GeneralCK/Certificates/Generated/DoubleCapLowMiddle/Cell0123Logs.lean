import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0123
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

theorem reflection_log_1_neg : (166235147 / 250000000) ≤ -Real.log (1600 / 3111) ∧
    -Real.log (1600 / 3111) ≤ (664940589 / 1000000000) := by
  have h := checkLog_sound (w := (1511 / 4711)) (n := 12)
    (lo := (166235147 / 250000000)) (hi := (664940589 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3111 / 1600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3111 / 1600) = 1/(1600 / 3111) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (166235147 / 250000000) (664940589 / 1000000000) (Real.log (3111 / 1600)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3111 / 1600) = -Real.log (1600 / 3111) := by
    rw [show ((3111 / 1600) : ℝ) = ((1600 / 3111) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (361140317 / 125000000) ≤ -Real.log (89 / 1600) ∧
    -Real.log (89 / 1600) ≤ (2889122541 / 1000000000) := by
  have h := checkLog_sound (w := (11 / 189)) (n := 12)
    (lo := (14566727 / 125000000)) (hi := (116533817 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100 / 89) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(100 / 89) = 1/(89 / 1600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-2889122541 / 1000000000) (-361140317 / 125000000) (Real.log (89 / 1600)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (132911761 / 200000000) ≤ -Real.log (25600 / 49757) ∧
    -Real.log (25600 / 49757) ≤ (332279403 / 500000000) := by
  have h := checkLog_sound (w := (24157 / 75357)) (n := 12)
    (lo := (132911761 / 200000000)) (hi := (332279403 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49757 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49757 / 25600) = 1/(25600 / 49757) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (132911761 / 200000000) (332279403 / 500000000) (Real.log (49757 / 25600)) := by
  have h := reflection_log_3_neg
  have he : Real.log (49757 / 25600) = -Real.log (25600 / 49757) := by
    rw [show ((49757 / 25600) : ℝ) = ((25600 / 49757) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (2875868069 / 1000000000) ≤ -Real.log (1443 / 25600) ∧
    -Real.log (1443 / 25600) ≤ (1437934037 / 500000000) := by
  have h := checkLog_sound (w := (157 / 3043)) (n := 12)
    (lo := (103279349 / 1000000000)) (hi := (2065587 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1443) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1600 / 1443) = 1/(1443 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-1437934037 / 500000000) (-2875868069 / 1000000000) (Real.log (1443 / 25600)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (317957617 / 500000000) ≤ -Real.log (800 / 1511) ∧
    -Real.log (800 / 1511) ≤ (127183047 / 200000000) := by
  have h := checkLog_sound (w := (711 / 2311)) (n := 12)
    (lo := (317957617 / 500000000)) (hi := (127183047 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1511 / 800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1511 / 800) = 1/(800 / 1511) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (317957617 / 500000000) (127183047 / 200000000) (Real.log (1511 / 800)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1511 / 800) = -Real.log (800 / 1511) := by
    rw [show ((1511 / 800) : ℝ) = ((800 / 1511) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (548993839 / 250000000) ≤ -Real.log (89 / 800) ∧
    -Real.log (89 / 800) ≤ (6862423 / 3125000) := by
  have h := checkLog_sound (w := (11 / 189)) (n := 12)
    (lo := (14566727 / 125000000)) (hi := (116533817 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100 / 89) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(100 / 89) = 1/(89 / 800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-6862423 / 3125000) (-548993839 / 250000000) (Real.log (89 / 800)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (317564511 / 500000000) ≤ -Real.log (12800 / 24157) ∧
    -Real.log (12800 / 24157) ≤ (635129023 / 1000000000) := by
  have h := checkLog_sound (w := (11357 / 36957)) (n := 12)
    (lo := (317564511 / 500000000)) (hi := (635129023 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24157 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24157 / 12800) = 1/(12800 / 24157) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (317564511 / 500000000) (635129023 / 1000000000) (Real.log (24157 / 12800)) := by
  have h := reflection_log_7_neg
  have he : Real.log (24157 / 12800) = -Real.log (12800 / 24157) := by
    rw [show ((24157 / 12800) : ℝ) = ((12800 / 24157) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (2182720889 / 1000000000) ≤ -Real.log (1443 / 12800) ∧
    -Real.log (1443 / 12800) ≤ (2182720893 / 1000000000) := by
  have h := checkLog_sound (w := (157 / 3043)) (n := 12)
    (lo := (103279349 / 1000000000)) (hi := (2065587 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1443) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1600 / 1443) = 1/(1443 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-2182720893 / 1000000000) (-2182720889 / 1000000000) (Real.log (1443 / 12800)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (167542427 / 250000000) ≤ -Real.log (1000000 / 1954569) ∧
    -Real.log (1000000 / 1954569) ≤ (670169709 / 1000000000) := by
  have h := checkLog_sound (w := (954569 / 2954569)) (n := 12)
    (lo := (167542427 / 250000000)) (hi := (670169709 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1954569 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1954569 / 1000000) = 1/(1000000 / 1954569) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (167542427 / 250000000) (670169709 / 1000000000) (Real.log (1954569 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1954569 / 1000000) = -Real.log (1000000 / 1954569) := by
    rw [show ((1954569 / 1000000) : ℝ) = ((1000000 / 1954569) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (618312117 / 200000000) ≤ -Real.log (45431 / 1000000) ∧
    -Real.log (45431 / 1000000) ≤ (309156059 / 100000000) := by
  have h := checkLog_sound (w := (17069 / 107931)) (n := 12)
    (lo := (63794373 / 200000000)) (hi := (159485933 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 45431) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 45431) = 1/(45431 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-309156059 / 100000000) (-618312117 / 200000000) (Real.log (45431 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (670454641 / 1000000000) ≤ -Real.log (500000 / 977563) ∧
    -Real.log (500000 / 977563) ≤ (335227321 / 500000000) := by
  have h := checkLog_sound (w := (477563 / 1477563)) (n := 12)
    (lo := (670454641 / 1000000000)) (hi := (335227321 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((977563 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(977563 / 500000) = 1/(500000 / 977563) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (670454641 / 1000000000) (335227321 / 500000000) (Real.log (977563 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (977563 / 500000) = -Real.log (500000 / 977563) := by
    rw [show ((977563 / 500000) : ℝ) = ((500000 / 977563) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1551948357 / 500000000) ≤ -Real.log (22437 / 500000) ∧
    -Real.log (22437 / 500000) ≤ (3103896719 / 1000000000) := by
  have h := checkLog_sound (w := (8813 / 53687)) (n := 12)
    (lo := (165653997 / 500000000)) (hi := (66261599 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 22437) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(31250 / 22437) = 1/(22437 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-3103896719 / 1000000000) (-1551948357 / 500000000) (Real.log (22437 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (669846823 / 1000000000) ≤ -Real.log (500000 / 976969) ∧
    -Real.log (500000 / 976969) ≤ (83730853 / 125000000) := by
  have h := checkLog_sound (w := (476969 / 1476969)) (n := 12)
    (lo := (669846823 / 1000000000)) (hi := (83730853 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((976969 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(976969 / 500000) = 1/(500000 / 976969) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (669846823 / 1000000000) (83730853 / 125000000) (Real.log (976969 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (976969 / 500000) = -Real.log (500000 / 976969) := by
    rw [show ((976969 / 500000) : ℝ) = ((500000 / 976969) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (3077766961 / 1000000000) ≤ -Real.log (23031 / 500000) ∧
    -Real.log (23031 / 500000) ≤ (1538883483 / 500000000) := by
  have h := checkLog_sound (w := (8219 / 54281)) (n := 12)
    (lo := (305178241 / 1000000000)) (hi := (152589121 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 23031) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(31250 / 23031) = 1/(23031 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-1538883483 / 500000000) (-3077766961 / 1000000000) (Real.log (23031 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (670141569 / 1000000000) ≤ -Real.log (500000 / 977257) ∧
    -Real.log (500000 / 977257) ≤ (67014157 / 100000000) := by
  have h := checkLog_sound (w := (477257 / 1477257)) (n := 12)
    (lo := (670141569 / 1000000000)) (hi := (67014157 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((977257 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(977257 / 500000) = 1/(500000 / 977257) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (670141569 / 1000000000) (67014157 / 100000000) (Real.log (977257 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (977257 / 500000) = -Real.log (500000 / 977257) := by
    rw [show ((977257 / 500000) : ℝ) = ((500000 / 977257) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (309035069 / 100000000) ≤ -Real.log (22743 / 500000) ∧
    -Real.log (22743 / 500000) ≤ (618070139 / 200000000) := by
  have h := checkLog_sound (w := (8507 / 53993)) (n := 12)
    (lo := (31776197 / 100000000)) (hi := (317761971 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 22743) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(31250 / 22743) = 1/(22743 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-618070139 / 200000000) (-309035069 / 100000000) (Real.log (22743 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (3761730293 / 1000000000) ≤ -Real.log (500000000000 / 21511401906187) ∧
    -Real.log (500000000000 / 21511401906187) ≤ (3761730299 / 1000000000) := by
  have h := checkLog_sound (w := (5511401906187 / 37511401906187)) (n := 12)
    (lo := (295994393 / 1000000000)) (hi := (147997197 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((21511401906187 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(21511401906187 / 16000000000000) = 1/(500000000000 / 21511401906187) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (3761730293 / 1000000000) (3761730299 / 1000000000) (Real.log (21511401906187 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (21511401906187 / 500000000000) = -Real.log (500000000000 / 21511401906187) := by
    rw [show ((21511401906187 / 500000000000) : ℝ) = ((500000000000 / 21511401906187) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (754870271 / 200000000) ≤ -Real.log (500000000000 / 21784619155859) ∧
    -Real.log (500000000000 / 21784619155859) ≤ (3774351361 / 1000000000) := by
  have h := checkLog_sound (w := (5784619155859 / 37784619155859)) (n := 12)
    (lo := (61723091 / 200000000)) (hi := (9644233 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((21784619155859 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(21784619155859 / 16000000000000) = 1/(500000000000 / 21784619155859) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (754870271 / 200000000) (3774351361 / 1000000000) (Real.log (21784619155859 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (21784619155859 / 500000000000) = -Real.log (500000000000 / 21784619155859) := by
    rw [show ((21784619155859 / 500000000000) : ℝ) = ((500000000000 / 21784619155859) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (468451723 / 125000000) ≤ -Real.log (250000000000 / 10604934653293) ∧
    -Real.log (250000000000 / 10604934653293) ≤ (374761379 / 100000000) := by
  have h := checkLog_sound (w := (2604934653293 / 18604934653293)) (n := 12)
    (lo := (70469471 / 250000000)) (hi := (56375577 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10604934653293 / 8000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(10604934653293 / 8000000000000) = 1/(250000000000 / 10604934653293) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (468451723 / 125000000) (374761379 / 100000000) (Real.log (10604934653293 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (10604934653293 / 250000000000) = -Real.log (250000000000 / 10604934653293) := by
    rw [show ((10604934653293 / 250000000000) : ℝ) = ((250000000000 / 10604934653293) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (3760492259 / 1000000000) ≤ -Real.log (500000000000 / 21484786527723) ∧
    -Real.log (500000000000 / 21484786527723) ≤ (752098453 / 200000000) := by
  have h := checkLog_sound (w := (5484786527723 / 37484786527723)) (n := 12)
    (lo := (294756359 / 1000000000)) (hi := (7368909 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((21484786527723 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(21484786527723 / 16000000000000) = 1/(500000000000 / 21484786527723) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (3760492259 / 1000000000) (752098453 / 200000000) (Real.log (21484786527723 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (21484786527723 / 500000000000) = -Real.log (500000000000 / 21484786527723) := by
    rw [show ((21484786527723 / 500000000000) : ℝ) = ((500000000000 / 21484786527723) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0123
