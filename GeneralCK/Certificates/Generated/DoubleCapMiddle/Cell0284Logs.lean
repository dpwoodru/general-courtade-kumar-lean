import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0284
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

theorem reflection_log_1_neg : (113832283 / 500000000) ≤ -Real.log (5120 / 6429) ∧
    -Real.log (5120 / 6429) ≤ (227664567 / 1000000000) := by
  have h := checkLog_sound (w := (1309 / 11549)) (n := 12)
    (lo := (113832283 / 500000000)) (hi := (227664567 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6429 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6429 / 5120) = 1/(5120 / 6429) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (113832283 / 500000000) (227664567 / 1000000000) (Real.log (6429 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6429 / 5120) = -Real.log (5120 / 6429) := by
    rw [show ((6429 / 5120) : ℝ) = ((5120 / 6429) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (295262817 / 1000000000) ≤ -Real.log (3811 / 5120) ∧
    -Real.log (3811 / 5120) ≤ (147631409 / 500000000) := by
  have h := checkLog_sound (w := (1309 / 8931)) (n := 12)
    (lo := (295262817 / 1000000000)) (hi := (147631409 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3811) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3811) = 1/(3811 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-147631409 / 500000000) (-295262817 / 1000000000) (Real.log (3811 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (227431221 / 1000000000) ≤ -Real.log (2048 / 2571) ∧
    -Real.log (2048 / 2571) ≤ (113715611 / 500000000) := by
  have h := checkLog_sound (w := (523 / 4619)) (n := 12)
    (lo := (227431221 / 1000000000)) (hi := (113715611 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2571 / 2048) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2571 / 2048) = 1/(2048 / 2571) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (227431221 / 1000000000) (113715611 / 500000000) (Real.log (2571 / 2048)) := by
  have h := reflection_log_3_neg
  have he : Real.log (2571 / 2048) = -Real.log (2048 / 2571) := by
    rw [show ((2571 / 2048) : ℝ) = ((2048 / 2571) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (294869297 / 1000000000) ≤ -Real.log (1525 / 2048) ∧
    -Real.log (1525 / 2048) ≤ (147434649 / 500000000) := by
  have h := checkLog_sound (w := (523 / 3573)) (n := 12)
    (lo := (294869297 / 1000000000)) (hi := (147434649 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2048 / 1525) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2048 / 1525) = 1/(1525 / 2048) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-147434649 / 500000000) (-294869297 / 1000000000) (Real.log (1525 / 2048)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (412988817 / 1000000000) ≤ -Real.log (2560 / 3869) ∧
    -Real.log (2560 / 3869) ≤ (206494409 / 500000000) := by
  have h := checkLog_sound (w := (1309 / 6429)) (n := 12)
    (lo := (412988817 / 1000000000)) (hi := (206494409 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3869 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3869 / 2560) = 1/(2560 / 3869) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (412988817 / 1000000000) (206494409 / 500000000) (Real.log (3869 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (3869 / 2560) = -Real.log (2560 / 3869) := by
    rw [show ((3869 / 2560) : ℝ) = ((2560 / 3869) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (358032013 / 500000000) ≤ -Real.log (1251 / 2560) ∧
    -Real.log (1251 / 2560) ≤ (179016007 / 250000000) := by
  have h := checkLog_sound (w := (29 / 2531)) (n := 12)
    (lo := (11458423 / 500000000)) (hi := (22916847 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 1251) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 1251) = 1/(1251 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-179016007 / 250000000) (-358032013 / 500000000) (Real.log (1251 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (103150261 / 250000000) ≤ -Real.log (1024 / 1547) ∧
    -Real.log (1024 / 1547) ≤ (82520209 / 200000000) := by
  have h := checkLog_sound (w := (523 / 2571)) (n := 12)
    (lo := (103150261 / 250000000)) (hi := (82520209 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1547 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1547 / 1024) = 1/(1024 / 1547) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (103150261 / 250000000) (82520209 / 200000000) (Real.log (1547 / 1024)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1547 / 1024) = -Real.log (1024 / 1547) := by
    rw [show ((1547 / 1024) : ℝ) = ((1024 / 1547) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (714865703 / 1000000000) ≤ -Real.log (501 / 1024) ∧
    -Real.log (501 / 1024) ≤ (142973141 / 200000000) := by
  have h := checkLog_sound (w := (11 / 1013)) (n := 12)
    (lo := (21718523 / 1000000000)) (hi := (5429631 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 501) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(512 / 501) = 1/(501 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-142973141 / 200000000) (-714865703 / 1000000000) (Real.log (501 / 1024)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (311571923 / 1000000000) ≤ -Real.log (100000 / 136557) ∧
    -Real.log (100000 / 136557) ≤ (77892981 / 250000000) := by
  have h := checkLog_sound (w := (36557 / 236557)) (n := 12)
    (lo := (311571923 / 1000000000)) (hi := (77892981 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((136557 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(136557 / 100000) = 1/(100000 / 136557) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (311571923 / 1000000000) (77892981 / 250000000) (Real.log (136557 / 100000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (136557 / 100000) = -Real.log (100000 / 136557) := by
    rw [show ((136557 / 100000) : ℝ) = ((100000 / 136557) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (455028321 / 1000000000) ≤ -Real.log (63443 / 100000) ∧
    -Real.log (63443 / 100000) ≤ (227514161 / 500000000) := by
  have h := checkLog_sound (w := (36557 / 163443)) (n := 12)
    (lo := (455028321 / 1000000000)) (hi := (227514161 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 63443) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 63443) = 1/(63443 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-227514161 / 500000000) (-455028321 / 1000000000) (Real.log (63443 / 100000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (12475529 / 40000000) ≤ -Real.log (500000 / 683001) ∧
    -Real.log (500000 / 683001) ≤ (155944113 / 500000000) := by
  have h := checkLog_sound (w := (183001 / 1183001)) (n := 12)
    (lo := (12475529 / 40000000)) (hi := (155944113 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((683001 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(683001 / 500000) = 1/(500000 / 683001) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (12475529 / 40000000) (155944113 / 500000000) (Real.log (683001 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (683001 / 500000) = -Real.log (500000 / 683001) := by
    rw [show ((683001 / 500000) : ℝ) = ((500000 / 683001) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (455709479 / 1000000000) ≤ -Real.log (316999 / 500000) ∧
    -Real.log (316999 / 500000) ≤ (11392737 / 25000000) := by
  have h := checkLog_sound (w := (183001 / 816999)) (n := 12)
    (lo := (455709479 / 1000000000)) (hi := (11392737 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 316999) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 316999) = 1/(316999 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-11392737 / 25000000) (-455709479 / 1000000000) (Real.log (316999 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (237772031 / 1000000000) ≤ -Real.log (50000 / 63421) ∧
    -Real.log (50000 / 63421) ≤ (928797 / 3906250) := by
  have h := checkLog_sound (w := (13421 / 113421)) (n := 12)
    (lo := (237772031 / 1000000000)) (hi := (928797 / 3906250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((63421 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(63421 / 50000) = 1/(50000 / 63421) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (237772031 / 1000000000) (928797 / 3906250) (Real.log (63421 / 50000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (63421 / 50000) = -Real.log (50000 / 63421) := by
    rw [show ((63421 / 50000) : ℝ) = ((50000 / 63421) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (3125487 / 10000000) ≤ -Real.log (36579 / 50000) ∧
    -Real.log (36579 / 50000) ≤ (312548701 / 1000000000) := by
  have h := checkLog_sound (w := (13421 / 86579)) (n := 12)
    (lo := (3125487 / 10000000)) (hi := (312548701 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 36579) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 36579) = 1/(36579 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-312548701 / 1000000000) (-3125487 / 10000000) (Real.log (36579 / 50000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (238041621 / 1000000000) ≤ -Real.log (500000 / 634381) ∧
    -Real.log (500000 / 634381) ≤ (119020811 / 500000000) := by
  have h := checkLog_sound (w := (134381 / 1134381)) (n := 12)
    (lo := (238041621 / 1000000000)) (hi := (119020811 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((634381 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(634381 / 500000) = 1/(500000 / 634381) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (238041621 / 1000000000) (119020811 / 500000000) (Real.log (634381 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (634381 / 500000) = -Real.log (500000 / 634381) := by
    rw [show ((634381 / 500000) : ℝ) = ((500000 / 634381) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (31301629 / 100000000) ≤ -Real.log (365619 / 500000) ∧
    -Real.log (365619 / 500000) ≤ (313016291 / 1000000000) := by
  have h := checkLog_sound (w := (134381 / 865619)) (n := 12)
    (lo := (31301629 / 100000000)) (hi := (313016291 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 365619) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 365619) = 1/(365619 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-313016291 / 1000000000) (-31301629 / 100000000) (Real.log (365619 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (191650061 / 250000000) ≤ -Real.log (125000000000 / 269054505619) ∧
    -Real.log (125000000000 / 269054505619) ≤ (383300123 / 500000000) := by
  have h := checkLog_sound (w := (19054505619 / 519054505619)) (n := 12)
    (lo := (9181633 / 125000000)) (hi := (14690613 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((269054505619 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(269054505619 / 250000000000) = 1/(125000000000 / 269054505619) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (191650061 / 250000000) (383300123 / 500000000) (Real.log (269054505619 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (269054505619 / 125000000000) = -Real.log (125000000000 / 269054505619) := by
    rw [show ((269054505619 / 125000000000) : ℝ) = ((125000000000 / 269054505619) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (767597703 / 1000000000) ≤ -Real.log (500000000000 / 1077292041931) ∧
    -Real.log (500000000000 / 1077292041931) ≤ (153519541 / 200000000) := by
  have h := checkLog_sound (w := (77292041931 / 2077292041931)) (n := 12)
    (lo := (74450523 / 1000000000)) (hi := (18612631 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1077292041931 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1077292041931 / 1000000000000) = 1/(500000000000 / 1077292041931) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (767597703 / 1000000000) (153519541 / 200000000) (Real.log (1077292041931 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1077292041931 / 500000000000) = -Real.log (500000000000 / 1077292041931) := by
    rw [show ((1077292041931 / 500000000000) : ℝ) = ((500000000000 / 1077292041931) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (550320731 / 1000000000) ≤ -Real.log (500000000000 / 866904508051) ∧
    -Real.log (500000000000 / 866904508051) ≤ (137580183 / 250000000) := by
  have h := checkLog_sound (w := (366904508051 / 1366904508051)) (n := 12)
    (lo := (550320731 / 1000000000)) (hi := (137580183 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((866904508051 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(866904508051 / 500000000000) = 1/(500000000000 / 866904508051) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (550320731 / 1000000000) (137580183 / 250000000) (Real.log (866904508051 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (866904508051 / 500000000000) = -Real.log (500000000000 / 866904508051) := by
    rw [show ((866904508051 / 500000000000) : ℝ) = ((500000000000 / 866904508051) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (68882239 / 125000000) ≤ -Real.log (250000000000 / 433771904633) ∧
    -Real.log (250000000000 / 433771904633) ≤ (551057913 / 1000000000) := by
  have h := checkLog_sound (w := (183771904633 / 683771904633)) (n := 12)
    (lo := (68882239 / 125000000)) (hi := (551057913 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((433771904633 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(433771904633 / 250000000000) = 1/(250000000000 / 433771904633) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (68882239 / 125000000) (551057913 / 1000000000) (Real.log (433771904633 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (433771904633 / 250000000000) = -Real.log (250000000000 / 433771904633) := by
    rw [show ((433771904633 / 250000000000) : ℝ) = ((250000000000 / 433771904633) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0284
