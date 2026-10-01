import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0211
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

theorem reflection_log_1_neg : (260710253 / 1000000000) ≤ -Real.log (1024 / 1329) ∧
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


theorem reflection_log_1 : Bounds (260710253 / 1000000000) (130355127 / 500000000) (Real.log (1329 / 1024)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1329 / 1024) = -Real.log (1024 / 1329) := by
    rw [show ((1329 / 1024) : ℝ) = ((1024 / 1329) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (353610447 / 1000000000) ≤ -Real.log (719 / 1024) ∧
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


theorem reflection_log_2 : Bounds (-22100653 / 62500000) (-353610447 / 1000000000) (Real.log (719 / 1024)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (260258683 / 1000000000) ≤ -Real.log (2560 / 3321) ∧
    -Real.log (2560 / 3321) ≤ (65064671 / 250000000) := by
  have h := checkLog_sound (w := (761 / 5881)) (n := 12)
    (lo := (260258683 / 1000000000)) (hi := (65064671 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3321 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3321 / 2560) = 1/(2560 / 3321) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (260258683 / 1000000000) (65064671 / 250000000) (Real.log (3321 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3321 / 2560) = -Real.log (2560 / 3321) := by
    rw [show ((3321 / 2560) : ℝ) = ((2560 / 3321) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (352776303 / 1000000000) ≤ -Real.log (1799 / 2560) ∧
    -Real.log (1799 / 2560) ≤ (22048519 / 62500000) := by
  have h := checkLog_sound (w := (761 / 4359)) (n := 12)
    (lo := (352776303 / 1000000000)) (hi := (22048519 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1799) = 1/(1799 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-22048519 / 62500000) (-352776303 / 1000000000) (Real.log (1799 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (467314469 / 1000000000) ≤ -Real.log (512 / 817) ∧
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


theorem reflection_log_5 : Bounds (467314469 / 1000000000) (46731447 / 100000000) (Real.log (817 / 512)) := by
  have h := reflection_log_5_neg
  have he : Real.log (817 / 512) = -Real.log (512 / 817) := by
    rw [show ((817 / 512) : ℝ) = ((512 / 817) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (905605831 / 1000000000) ≤ -Real.log (207 / 512) ∧
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


theorem reflection_log_6 : Bounds (-905605833 / 1000000000) (-905605831 / 1000000000) (Real.log (207 / 512)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (93315961 / 200000000) ≤ -Real.log (1280 / 2041) ∧
    -Real.log (1280 / 2041) ≤ (233289903 / 500000000) := by
  have h := checkLog_sound (w := (761 / 3321)) (n := 12)
    (lo := (93315961 / 200000000)) (hi := (233289903 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2041 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2041 / 1280) = 1/(1280 / 2041) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (93315961 / 200000000) (233289903 / 500000000) (Real.log (2041 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2041 / 1280) = -Real.log (1280 / 2041) := by
    rw [show ((2041 / 1280) : ℝ) = ((1280 / 2041) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (902711473 / 1000000000) ≤ -Real.log (519 / 1280) ∧
    -Real.log (519 / 1280) ≤ (36108459 / 40000000) := by
  have h := checkLog_sound (w := (121 / 1159)) (n := 12)
    (lo := (209564293 / 1000000000)) (hi := (104782147 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 519) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 519) = 1/(519 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-36108459 / 40000000) (-902711473 / 1000000000) (Real.log (519 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (178039733 / 500000000) ≤ -Real.log (1000000 / 1427721) ∧
    -Real.log (1000000 / 1427721) ≤ (356079467 / 1000000000) := by
  have h := checkLog_sound (w := (427721 / 2427721)) (n := 12)
    (lo := (178039733 / 500000000)) (hi := (356079467 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1427721 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1427721 / 1000000) = 1/(1000000 / 1427721) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (178039733 / 500000000) (356079467 / 1000000000) (Real.log (1427721 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1427721 / 1000000) = -Real.log (1000000 / 1427721) := by
    rw [show ((1427721 / 1000000) : ℝ) = ((1000000 / 1427721) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (139532161 / 250000000) ≤ -Real.log (572279 / 1000000) ∧
    -Real.log (572279 / 1000000) ≤ (111625729 / 200000000) := by
  have h := checkLog_sound (w := (427721 / 1572279)) (n := 12)
    (lo := (139532161 / 250000000)) (hi := (111625729 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 572279) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 572279) = 1/(572279 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-111625729 / 200000000) (-139532161 / 250000000) (Real.log (572279 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (356695643 / 1000000000) ≤ -Real.log (1000000 / 1428601) ∧
    -Real.log (1000000 / 1428601) ≤ (89173911 / 250000000) := by
  have h := checkLog_sound (w := (428601 / 2428601)) (n := 12)
    (lo := (356695643 / 1000000000)) (hi := (89173911 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1428601 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1428601 / 1000000) = 1/(1000000 / 1428601) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (356695643 / 1000000000) (89173911 / 250000000) (Real.log (1428601 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1428601 / 1000000) = -Real.log (1000000 / 1428601) := by
    rw [show ((1428601 / 1000000) : ℝ) = ((1000000 / 1428601) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (559667539 / 1000000000) ≤ -Real.log (571399 / 1000000) ∧
    -Real.log (571399 / 1000000) ≤ (27983377 / 50000000) := by
  have h := checkLog_sound (w := (428601 / 1571399)) (n := 12)
    (lo := (559667539 / 1000000000)) (hi := (27983377 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 571399) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 571399) = 1/(571399 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-27983377 / 50000000) (-559667539 / 1000000000) (Real.log (571399 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (138264807 / 500000000) ≤ -Real.log (500000 / 659273) ∧
    -Real.log (500000 / 659273) ≤ (55305923 / 200000000) := by
  have h := checkLog_sound (w := (159273 / 1159273)) (n := 12)
    (lo := (138264807 / 500000000)) (hi := (55305923 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((659273 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(659273 / 500000) = 1/(500000 / 659273) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (138264807 / 500000000) (55305923 / 200000000) (Real.log (659273 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (659273 / 500000) = -Real.log (500000 / 659273) := by
    rw [show ((659273 / 500000) : ℝ) = ((500000 / 659273) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (2996301 / 7812500) ≤ -Real.log (340727 / 500000) ∧
    -Real.log (340727 / 500000) ≤ (383526529 / 1000000000) := by
  have h := checkLog_sound (w := (159273 / 840727)) (n := 12)
    (lo := (2996301 / 7812500)) (hi := (383526529 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 340727) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 340727) = 1/(340727 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-383526529 / 1000000000) (-2996301 / 7812500) (Real.log (340727 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (277078553 / 1000000000) ≤ -Real.log (100000 / 131927) ∧
    -Real.log (100000 / 131927) ≤ (138539277 / 500000000) := by
  have h := checkLog_sound (w := (31927 / 231927)) (n := 12)
    (lo := (277078553 / 1000000000)) (hi := (138539277 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((131927 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(131927 / 100000) = 1/(100000 / 131927) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (277078553 / 1000000000) (138539277 / 500000000) (Real.log (131927 / 100000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (131927 / 100000) = -Real.log (100000 / 131927) := by
    rw [show ((131927 / 100000) : ℝ) = ((100000 / 131927) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (384589527 / 1000000000) ≤ -Real.log (68073 / 100000) ∧
    -Real.log (68073 / 100000) ≤ (48073691 / 125000000) := by
  have h := checkLog_sound (w := (31927 / 168073)) (n := 12)
    (lo := (384589527 / 1000000000)) (hi := (48073691 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 68073) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 68073) = 1/(68073 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-48073691 / 125000000) (-384589527 / 1000000000) (Real.log (68073 / 100000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (91420811 / 100000000) ≤ -Real.log (250000000000 / 623699716397) ∧
    -Real.log (250000000000 / 623699716397) ≤ (57138007 / 62500000) := by
  have h := checkLog_sound (w := (123699716397 / 1123699716397)) (n := 12)
    (lo := (22106093 / 100000000)) (hi := (221060931 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((623699716397 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(623699716397 / 500000000000) = 1/(250000000000 / 623699716397) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (91420811 / 100000000) (57138007 / 62500000) (Real.log (623699716397 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (623699716397 / 250000000000) = -Real.log (250000000000 / 623699716397) := by
    rw [show ((623699716397 / 250000000000) : ℝ) = ((250000000000 / 623699716397) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (458181591 / 500000000) ≤ -Real.log (500000000000 / 1250090567187) ∧
    -Real.log (500000000000 / 1250090567187) ≤ (57272699 / 62500000) := by
  have h := checkLog_sound (w := (250090567187 / 2250090567187)) (n := 12)
    (lo := (111608001 / 500000000)) (hi := (223216003 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250090567187 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1250090567187 / 1000000000000) = 1/(500000000000 / 1250090567187) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (458181591 / 500000000) (57272699 / 62500000) (Real.log (1250090567187 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1250090567187 / 500000000000) = -Real.log (500000000000 / 1250090567187) := by
    rw [show ((1250090567187 / 500000000000) : ℝ) = ((500000000000 / 1250090567187) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (330028071 / 500000000) ≤ -Real.log (500000000000 / 967450480883) ∧
    -Real.log (500000000000 / 967450480883) ≤ (660056143 / 1000000000) := by
  have h := checkLog_sound (w := (467450480883 / 1467450480883)) (n := 12)
    (lo := (330028071 / 500000000)) (hi := (660056143 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((967450480883 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(967450480883 / 500000000000) = 1/(500000000000 / 967450480883) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (330028071 / 500000000) (660056143 / 1000000000) (Real.log (967450480883 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (967450480883 / 500000000000) = -Real.log (500000000000 / 967450480883) := by
    rw [show ((967450480883 / 500000000000) : ℝ) = ((500000000000 / 967450480883) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (8270851 / 12500000) ≤ -Real.log (125000000000 / 242252802139) ∧
    -Real.log (125000000000 / 242252802139) ≤ (661668081 / 1000000000) := by
  have h := checkLog_sound (w := (117252802139 / 367252802139)) (n := 12)
    (lo := (8270851 / 12500000)) (hi := (661668081 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((242252802139 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(242252802139 / 125000000000) = 1/(125000000000 / 242252802139) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (8270851 / 12500000) (661668081 / 1000000000) (Real.log (242252802139 / 125000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (242252802139 / 125000000000) = -Real.log (125000000000 / 242252802139) := by
    rw [show ((242252802139 / 125000000000) : ℝ) = ((125000000000 / 242252802139) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0211
