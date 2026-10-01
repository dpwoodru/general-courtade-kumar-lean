import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0269
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

theorem reflection_log_1_neg : (234176217 / 1000000000) ≤ -Real.log (5120 / 6471) ∧
    -Real.log (5120 / 6471) ≤ (117088109 / 500000000) := by
  have h := checkLog_sound (w := (1351 / 11591)) (n := 12)
    (lo := (234176217 / 1000000000)) (hi := (117088109 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6471 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6471 / 5120) = 1/(5120 / 6471) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (234176217 / 1000000000) (117088109 / 500000000) (Real.log (6471 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6471 / 5120) = -Real.log (5120 / 6471) := by
    rw [show ((6471 / 5120) : ℝ) = ((5120 / 6471) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (76586181 / 250000000) ≤ -Real.log (3769 / 5120) ∧
    -Real.log (3769 / 5120) ≤ (12253789 / 40000000) := by
  have h := checkLog_sound (w := (1351 / 8889)) (n := 12)
    (lo := (76586181 / 250000000)) (hi := (12253789 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3769) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3769) = 1/(3769 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-12253789 / 40000000) (-76586181 / 250000000) (Real.log (3769 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (116856251 / 500000000) ≤ -Real.log (1280 / 1617) ∧
    -Real.log (1280 / 1617) ≤ (233712503 / 1000000000) := by
  have h := checkLog_sound (w := (337 / 2897)) (n := 12)
    (lo := (116856251 / 500000000)) (hi := (233712503 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1617 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1617 / 1280) = 1/(1280 / 1617) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (116856251 / 500000000) (233712503 / 1000000000) (Real.log (1617 / 1280)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1617 / 1280) = -Real.log (1280 / 1617) := by
    rw [show ((1617 / 1280) : ℝ) = ((1280 / 1617) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (152774537 / 500000000) ≤ -Real.log (943 / 1280) ∧
    -Real.log (943 / 1280) ≤ (12221963 / 40000000) := by
  have h := checkLog_sound (w := (337 / 2223)) (n := 12)
    (lo := (152774537 / 500000000)) (hi := (12221963 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 943) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 943) = 1/(943 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-12221963 / 40000000) (-152774537 / 500000000) (Real.log (943 / 1280)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (423785837 / 1000000000) ≤ -Real.log (2560 / 3911) ∧
    -Real.log (2560 / 3911) ≤ (211892919 / 500000000) := by
  have h := checkLog_sound (w := (1351 / 6471)) (n := 12)
    (lo := (423785837 / 1000000000)) (hi := (211892919 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3911 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3911 / 2560) = 1/(2560 / 3911) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (423785837 / 1000000000) (211892919 / 500000000) (Real.log (3911 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (3911 / 2560) = -Real.log (2560 / 3911) := by
    rw [show ((3911 / 2560) : ℝ) = ((2560 / 3911) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (375106843 / 500000000) ≤ -Real.log (1209 / 2560) ∧
    -Real.log (1209 / 2560) ≤ (93776711 / 125000000) := by
  have h := checkLog_sound (w := (71 / 2489)) (n := 12)
    (lo := (28533253 / 500000000)) (hi := (57066507 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 1209) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 1209) = 1/(1209 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-93776711 / 125000000) (-375106843 / 500000000) (Real.log (1209 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (16920739 / 40000000) ≤ -Real.log (640 / 977) ∧
    -Real.log (640 / 977) ≤ (105754619 / 250000000) := by
  have h := checkLog_sound (w := (337 / 1617)) (n := 12)
    (lo := (16920739 / 40000000)) (hi := (105754619 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((977 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(977 / 640) = 1/(640 / 977) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (16920739 / 40000000) (105754619 / 250000000) (Real.log (977 / 640)) := by
  have h := reflection_log_7_neg
  have he : Real.log (977 / 640) = -Real.log (640 / 977) := by
    rw [show ((977 / 640) : ℝ) = ((640 / 977) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (74773537 / 100000000) ≤ -Real.log (303 / 640) ∧
    -Real.log (303 / 640) ≤ (186933843 / 250000000) := by
  have h := checkLog_sound (w := (17 / 623)) (n := 12)
    (lo := (5458819 / 100000000)) (hi := (54588191 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 303) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(320 / 303) = 1/(303 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-186933843 / 250000000) (-74773537 / 100000000) (Real.log (303 / 640)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (3200677 / 10000000) ≤ -Real.log (1000000 / 1377221) ∧
    -Real.log (1000000 / 1377221) ≤ (320067701 / 1000000000) := by
  have h := checkLog_sound (w := (377221 / 2377221)) (n := 12)
    (lo := (3200677 / 10000000)) (hi := (320067701 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1377221 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1377221 / 1000000) = 1/(1000000 / 1377221) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (3200677 / 10000000) (320067701 / 1000000000) (Real.log (1377221 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1377221 / 1000000) = -Real.log (1000000 / 1377221) := by
    rw [show ((1377221 / 1000000) : ℝ) = ((1000000 / 1377221) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (236781779 / 500000000) ≤ -Real.log (622779 / 1000000) ∧
    -Real.log (622779 / 1000000) ≤ (473563559 / 1000000000) := by
  have h := checkLog_sound (w := (377221 / 1622779)) (n := 12)
    (lo := (236781779 / 500000000)) (hi := (473563559 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 622779) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 622779) = 1/(622779 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-473563559 / 1000000000) (-236781779 / 500000000) (Real.log (622779 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (64139261 / 200000000) ≤ -Real.log (1000000 / 1378087) ∧
    -Real.log (1000000 / 1378087) ≤ (160348153 / 500000000) := by
  have h := checkLog_sound (w := (378087 / 2378087)) (n := 12)
    (lo := (64139261 / 200000000)) (hi := (160348153 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1378087 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1378087 / 1000000) = 1/(1000000 / 1378087) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (64139261 / 200000000) (160348153 / 500000000) (Real.log (1378087 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1378087 / 1000000) = -Real.log (1000000 / 1378087) := by
    rw [show ((1378087 / 1000000) : ℝ) = ((1000000 / 1378087) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (474955067 / 1000000000) ≤ -Real.log (621913 / 1000000) ∧
    -Real.log (621913 / 1000000) ≤ (118738767 / 250000000) := by
  have h := checkLog_sound (w := (378087 / 1621913)) (n := 12)
    (lo := (474955067 / 1000000000)) (hi := (118738767 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 621913) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 621913) = 1/(621913 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-118738767 / 250000000) (-474955067 / 1000000000) (Real.log (621913 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (245032627 / 1000000000) ≤ -Real.log (1000000 / 1277663) ∧
    -Real.log (1000000 / 1277663) ≤ (61258157 / 250000000) := by
  have h := checkLog_sound (w := (277663 / 2277663)) (n := 12)
    (lo := (245032627 / 1000000000)) (hi := (61258157 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1277663 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1277663 / 1000000) = 1/(1000000 / 1277663) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (245032627 / 1000000000) (61258157 / 250000000) (Real.log (1277663 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1277663 / 1000000) = -Real.log (1000000 / 1277663) := by
    rw [show ((1277663 / 1000000) : ℝ) = ((1000000 / 1277663) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (325263489 / 1000000000) ≤ -Real.log (722337 / 1000000) ∧
    -Real.log (722337 / 1000000) ≤ (32526349 / 100000000) := by
  have h := checkLog_sound (w := (277663 / 1722337)) (n := 12)
    (lo := (325263489 / 1000000000)) (hi := (32526349 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 722337) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 722337) = 1/(722337 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-32526349 / 100000000) (-325263489 / 1000000000) (Real.log (722337 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (61392937 / 250000000) ≤ -Real.log (62500 / 79897) ∧
    -Real.log (62500 / 79897) ≤ (245571749 / 1000000000) := by
  have h := checkLog_sound (w := (17397 / 142397)) (n := 12)
    (lo := (61392937 / 250000000)) (hi := (245571749 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((79897 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(79897 / 62500) = 1/(62500 / 79897) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (61392937 / 250000000) (245571749 / 1000000000) (Real.log (79897 / 62500)) := by
  have h := reflection_log_15_neg
  have he : Real.log (79897 / 62500) = -Real.log (62500 / 79897) := by
    rw [show ((79897 / 62500) : ℝ) = ((62500 / 79897) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (326217793 / 1000000000) ≤ -Real.log (45103 / 62500) ∧
    -Real.log (45103 / 62500) ≤ (163108897 / 500000000) := by
  have h := checkLog_sound (w := (17397 / 107603)) (n := 12)
    (lo := (326217793 / 1000000000)) (hi := (163108897 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 45103) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 45103) = 1/(45103 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-163108897 / 500000000) (-326217793 / 1000000000) (Real.log (45103 / 62500)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (396815629 / 500000000) ≤ -Real.log (125000000000 / 276426509243) ∧
    -Real.log (125000000000 / 276426509243) ≤ (39681563 / 50000000) := by
  have h := checkLog_sound (w := (26426509243 / 526426509243)) (n := 12)
    (lo := (50242039 / 500000000)) (hi := (100484079 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((276426509243 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(276426509243 / 250000000000) = 1/(125000000000 / 276426509243) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (396815629 / 500000000) (39681563 / 50000000) (Real.log (276426509243 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (276426509243 / 125000000000) = -Real.log (125000000000 / 276426509243) := by
    rw [show ((276426509243 / 125000000000) : ℝ) = ((125000000000 / 276426509243) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (198912843 / 250000000) ≤ -Real.log (31250000000 / 69246371679) ∧
    -Real.log (31250000000 / 69246371679) ≤ (397825687 / 500000000) := by
  have h := checkLog_sound (w := (6746371679 / 131746371679)) (n := 12)
    (lo := (400407 / 3906250)) (hi := (102504193 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((69246371679 / 62500000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(69246371679 / 62500000000) = 1/(31250000000 / 69246371679) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (198912843 / 250000000) (397825687 / 500000000) (Real.log (69246371679 / 31250000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (69246371679 / 31250000000) = -Real.log (31250000000 / 69246371679) := by
    rw [show ((69246371679 / 31250000000) : ℝ) = ((31250000000 / 69246371679) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (570296117 / 1000000000) ≤ -Real.log (500000000000 / 884395372243) ∧
    -Real.log (500000000000 / 884395372243) ≤ (285148059 / 500000000) := by
  have h := checkLog_sound (w := (384395372243 / 1384395372243)) (n := 12)
    (lo := (570296117 / 1000000000)) (hi := (285148059 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((884395372243 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(884395372243 / 500000000000) = 1/(500000000000 / 884395372243) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (570296117 / 1000000000) (285148059 / 500000000) (Real.log (884395372243 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (884395372243 / 500000000000) = -Real.log (500000000000 / 884395372243) := by
    rw [show ((884395372243 / 500000000000) : ℝ) = ((500000000000 / 884395372243) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (571789541 / 1000000000) ≤ -Real.log (500000000000 / 885717136333) ∧
    -Real.log (500000000000 / 885717136333) ≤ (285894771 / 500000000) := by
  have h := checkLog_sound (w := (385717136333 / 1385717136333)) (n := 12)
    (lo := (571789541 / 1000000000)) (hi := (285894771 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((885717136333 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(885717136333 / 500000000000) = 1/(500000000000 / 885717136333) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (571789541 / 1000000000) (285894771 / 500000000) (Real.log (885717136333 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (885717136333 / 500000000000) = -Real.log (500000000000 / 885717136333) := by
    rw [show ((885717136333 / 500000000000) : ℝ) = ((500000000000 / 885717136333) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0269
