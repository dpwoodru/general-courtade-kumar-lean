import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0183
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

theorem reflection_log_1_neg : (54654421 / 200000000) ≤ -Real.log (5120 / 6729) ∧
    -Real.log (5120 / 6729) ≤ (136636053 / 500000000) := by
  have h := checkLog_sound (w := (1609 / 11849)) (n := 12)
    (lo := (54654421 / 200000000)) (hi := (136636053 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6729 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6729 / 5120) = 1/(5120 / 6729) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (54654421 / 200000000) (136636053 / 500000000) (Real.log (6729 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6729 / 5120) = -Real.log (5120 / 6729) := by
    rw [show ((6729 / 5120) : ℝ) = ((5120 / 6729) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (377253541 / 1000000000) ≤ -Real.log (3511 / 5120) ∧
    -Real.log (3511 / 5120) ≤ (188626771 / 500000000) := by
  have h := checkLog_sound (w := (1609 / 8631)) (n := 12)
    (lo := (377253541 / 1000000000)) (hi := (188626771 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3511) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3511) = 1/(3511 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-188626771 / 500000000) (-377253541 / 1000000000) (Real.log (3511 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (136413087 / 500000000) ≤ -Real.log (2560 / 3363) ∧
    -Real.log (2560 / 3363) ≤ (10913047 / 40000000) := by
  have h := checkLog_sound (w := (803 / 5923)) (n := 12)
    (lo := (136413087 / 500000000)) (hi := (10913047 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3363 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3363 / 2560) = 1/(2560 / 3363) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (136413087 / 500000000) (10913047 / 40000000) (Real.log (3363 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3363 / 2560) = -Real.log (2560 / 3363) := by
    rw [show ((3363 / 2560) : ℝ) = ((2560 / 3363) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (376399449 / 1000000000) ≤ -Real.log (1757 / 2560) ∧
    -Real.log (1757 / 2560) ≤ (7527989 / 20000000) := by
  have h := checkLog_sound (w := (803 / 4317)) (n := 12)
    (lo := (376399449 / 1000000000)) (hi := (7527989 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1757) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1757) = 1/(1757 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-7527989 / 20000000) (-376399449 / 1000000000) (Real.log (1757 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (24383447 / 50000000) ≤ -Real.log (2560 / 4169) ∧
    -Real.log (2560 / 4169) ≤ (487668941 / 1000000000) := by
  have h := checkLog_sound (w := (1609 / 6729)) (n := 12)
    (lo := (24383447 / 50000000)) (hi := (487668941 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4169 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4169 / 2560) = 1/(2560 / 4169) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (24383447 / 50000000) (487668941 / 1000000000) (Real.log (4169 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (4169 / 2560) = -Real.log (2560 / 4169) := by
    rw [show ((4169 / 2560) : ℝ) = ((2560 / 4169) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (495124237 / 500000000) ≤ -Real.log (951 / 2560) ∧
    -Real.log (951 / 2560) ≤ (247562119 / 250000000) := by
  have h := checkLog_sound (w := (329 / 2231)) (n := 12)
    (lo := (148550647 / 500000000)) (hi := (59420259 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 951) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 951) = 1/(951 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-247562119 / 250000000) (-495124237 / 500000000) (Real.log (951 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (121737271 / 250000000) ≤ -Real.log (1280 / 2083) ∧
    -Real.log (1280 / 2083) ≤ (97389817 / 200000000) := by
  have h := checkLog_sound (w := (803 / 3363)) (n := 12)
    (lo := (121737271 / 250000000)) (hi := (97389817 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2083 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2083 / 1280) = 1/(1280 / 2083) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (121737271 / 250000000) (97389817 / 200000000) (Real.log (2083 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2083 / 1280) = -Real.log (1280 / 2083) := by
    rw [show ((2083 / 1280) : ℝ) = ((1280 / 2083) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (197419773 / 200000000) ≤ -Real.log (477 / 1280) ∧
    -Real.log (477 / 1280) ≤ (987098867 / 1000000000) := by
  have h := checkLog_sound (w := (163 / 1117)) (n := 12)
    (lo := (58790337 / 200000000)) (hi := (146975843 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 477) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 477) = 1/(477 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-987098867 / 1000000000) (-197419773 / 200000000) (Real.log (477 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (373218049 / 1000000000) ≤ -Real.log (1000000 / 1452401) ∧
    -Real.log (1000000 / 1452401) ≤ (7464361 / 20000000) := by
  have h := checkLog_sound (w := (452401 / 2452401)) (n := 12)
    (lo := (373218049 / 1000000000)) (hi := (7464361 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1452401 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1452401 / 1000000) = 1/(1000000 / 1452401) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (373218049 / 1000000000) (7464361 / 20000000) (Real.log (1452401 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1452401 / 1000000) = -Real.log (1000000 / 1452401) := by
    rw [show ((1452401 / 1000000) : ℝ) = ((1000000 / 1452401) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (602212011 / 1000000000) ≤ -Real.log (547599 / 1000000) ∧
    -Real.log (547599 / 1000000) ≤ (150553003 / 250000000) := by
  have h := checkLog_sound (w := (452401 / 1547599)) (n := 12)
    (lo := (602212011 / 1000000000)) (hi := (150553003 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 547599) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 547599) = 1/(547599 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-150553003 / 250000000) (-602212011 / 1000000000) (Real.log (547599 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (14953143 / 40000000) ≤ -Real.log (125000 / 181661) ∧
    -Real.log (125000 / 181661) ≤ (11682143 / 31250000) := by
  have h := checkLog_sound (w := (56661 / 306661)) (n := 12)
    (lo := (14953143 / 40000000)) (hi := (11682143 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((181661 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(181661 / 125000) = 1/(125000 / 181661) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (14953143 / 40000000) (11682143 / 31250000) (Real.log (181661 / 125000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (181661 / 125000) = -Real.log (125000 / 181661) := by
    rw [show ((181661 / 125000) : ℝ) = ((125000 / 181661) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (603833123 / 1000000000) ≤ -Real.log (68339 / 125000) ∧
    -Real.log (68339 / 125000) ≤ (150958281 / 250000000) := by
  have h := checkLog_sound (w := (56661 / 193339)) (n := 12)
    (lo := (603833123 / 1000000000)) (hi := (150958281 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 68339) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 68339) = 1/(68339 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-150958281 / 250000000) (-603833123 / 1000000000) (Real.log (68339 / 125000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (36495891 / 125000000) ≤ -Real.log (1000000 / 1339059) ∧
    -Real.log (1000000 / 1339059) ≤ (291967129 / 1000000000) := by
  have h := checkLog_sound (w := (339059 / 2339059)) (n := 12)
    (lo := (36495891 / 125000000)) (hi := (291967129 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1339059 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1339059 / 1000000) = 1/(1000000 / 1339059) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (36495891 / 125000000) (291967129 / 1000000000) (Real.log (1339059 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1339059 / 1000000) = -Real.log (1000000 / 1339059) := by
    rw [show ((1339059 / 1000000) : ℝ) = ((1000000 / 1339059) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (414090701 / 1000000000) ≤ -Real.log (660941 / 1000000) ∧
    -Real.log (660941 / 1000000) ≤ (207045351 / 500000000) := by
  have h := checkLog_sound (w := (339059 / 1660941)) (n := 12)
    (lo := (414090701 / 1000000000)) (hi := (207045351 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 660941) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 660941) = 1/(660941 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-207045351 / 500000000) (-414090701 / 1000000000) (Real.log (660941 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (73130647 / 250000000) ≤ -Real.log (1000000 / 1339803) ∧
    -Real.log (1000000 / 1339803) ≤ (292522589 / 1000000000) := by
  have h := checkLog_sound (w := (339803 / 2339803)) (n := 12)
    (lo := (73130647 / 250000000)) (hi := (292522589 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1339803 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1339803 / 1000000) = 1/(1000000 / 1339803) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (73130647 / 250000000) (292522589 / 1000000000) (Real.log (1339803 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1339803 / 1000000) = -Real.log (1000000 / 1339803) := by
    rw [show ((1339803 / 1000000) : ℝ) = ((1000000 / 1339803) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (415217003 / 1000000000) ≤ -Real.log (660197 / 1000000) ∧
    -Real.log (660197 / 1000000) ≤ (103804251 / 250000000) := by
  have h := checkLog_sound (w := (339803 / 1660197)) (n := 12)
    (lo := (415217003 / 1000000000)) (hi := (103804251 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 660197) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 660197) = 1/(660197 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-103804251 / 250000000) (-415217003 / 1000000000) (Real.log (660197 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (48771503 / 50000000) ≤ -Real.log (50000000000 / 132615380963) ∧
    -Real.log (50000000000 / 132615380963) ≤ (487715031 / 500000000) := by
  have h := checkLog_sound (w := (32615380963 / 232615380963)) (n := 12)
    (lo := (441067 / 1562500)) (hi := (282282881 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((132615380963 / 100000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(132615380963 / 100000000000) = 1/(50000000000 / 132615380963) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (48771503 / 50000000) (487715031 / 500000000) (Real.log (132615380963 / 50000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (132615380963 / 50000000000) = -Real.log (50000000000 / 132615380963) := by
    rw [show ((132615380963 / 50000000000) : ℝ) = ((50000000000 / 132615380963) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (488830849 / 500000000) ≤ -Real.log (500000000000 / 1329116609843) ∧
    -Real.log (500000000000 / 1329116609843) ≤ (9776617 / 10000000) := by
  have h := checkLog_sound (w := (329116609843 / 2329116609843)) (n := 12)
    (lo := (142257259 / 500000000)) (hi := (284514519 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1329116609843 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1329116609843 / 1000000000000) = 1/(500000000000 / 1329116609843) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (488830849 / 500000000) (9776617 / 10000000) (Real.log (1329116609843 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1329116609843 / 500000000000) = -Real.log (500000000000 / 1329116609843) := by
    rw [show ((1329116609843 / 500000000000) : ℝ) = ((500000000000 / 1329116609843) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (706057829 / 1000000000) ≤ -Real.log (62500000000 / 126624293999) ∧
    -Real.log (62500000000 / 126624293999) ≤ (706057831 / 1000000000) := by
  have h := checkLog_sound (w := (1624293999 / 251624293999)) (n := 12)
    (lo := (12910649 / 1000000000)) (hi := (258213 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((126624293999 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(126624293999 / 125000000000) = 1/(62500000000 / 126624293999) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (706057829 / 1000000000) (706057831 / 1000000000) (Real.log (126624293999 / 62500000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (126624293999 / 62500000000) = -Real.log (62500000000 / 126624293999) := by
    rw [show ((126624293999 / 62500000000) : ℝ) = ((62500000000 / 126624293999) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (707739591 / 1000000000) ≤ -Real.log (500000000000 / 1014699400331) ∧
    -Real.log (500000000000 / 1014699400331) ≤ (707739593 / 1000000000) := by
  have h := checkLog_sound (w := (14699400331 / 2014699400331)) (n := 12)
    (lo := (14592411 / 1000000000)) (hi := (3648103 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1014699400331 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1014699400331 / 1000000000000) = 1/(500000000000 / 1014699400331) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (707739591 / 1000000000) (707739593 / 1000000000) (Real.log (1014699400331 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1014699400331 / 500000000000) = -Real.log (500000000000 / 1014699400331) := by
    rw [show ((1014699400331 / 500000000000) : ℝ) = ((500000000000 / 1014699400331) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0183
