import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0018
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

theorem reflection_log_1_neg : (399981349 / 1000000000) ≤ -Real.log (2560 / 3819) ∧
    -Real.log (2560 / 3819) ≤ (7999627 / 20000000) := by
  have h := checkLog_sound (w := (1259 / 6379)) (n := 12)
    (lo := (399981349 / 1000000000)) (hi := (7999627 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3819 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3819 / 2560) = 1/(2560 / 3819) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (399981349 / 1000000000) (7999627 / 20000000) (Real.log (3819 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3819 / 2560) = -Real.log (2560 / 3819) := by
    rw [show ((3819 / 2560) : ℝ) = ((2560 / 3819) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (338437029 / 500000000) ≤ -Real.log (1301 / 2560) ∧
    -Real.log (1301 / 2560) ≤ (676874059 / 1000000000) := by
  have h := checkLog_sound (w := (1259 / 3861)) (n := 12)
    (lo := (338437029 / 500000000)) (hi := (676874059 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1301) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1301) = 1/(1301 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-676874059 / 1000000000) (-338437029 / 500000000) (Real.log (1301 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (79839099 / 200000000) ≤ -Real.log (320 / 477) ∧
    -Real.log (320 / 477) ≤ (49899437 / 125000000) := by
  have h := checkLog_sound (w := (157 / 797)) (n := 12)
    (lo := (79839099 / 200000000)) (hi := (49899437 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((477 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(477 / 320) = 1/(320 / 477) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (79839099 / 200000000) (49899437 / 125000000) (Real.log (477 / 320)) := by
  have h := reflection_log_3_neg
  have he : Real.log (477 / 320) = -Real.log (320 / 477) := by
    rw [show ((477 / 320) : ℝ) = ((320 / 477) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (337285397 / 500000000) ≤ -Real.log (163 / 320) ∧
    -Real.log (163 / 320) ≤ (134914159 / 200000000) := by
  have h := checkLog_sound (w := (157 / 483)) (n := 12)
    (lo := (337285397 / 500000000)) (hi := (134914159 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 163) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(320 / 163) = 1/(163 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-134914159 / 200000000) (-337285397 / 500000000) (Real.log (163 / 320)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (42806889 / 62500000) ≤ -Real.log (1280 / 2539) ∧
    -Real.log (1280 / 2539) ≤ (27396409 / 40000000) := by
  have h := checkLog_sound (w := (1259 / 3819)) (n := 12)
    (lo := (42806889 / 62500000)) (hi := (27396409 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2539 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2539 / 1280) = 1/(1280 / 2539) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (42806889 / 62500000) (27396409 / 40000000) (Real.log (2539 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2539 / 1280) = -Real.log (1280 / 2539) := by
    rw [show ((2539 / 1280) : ℝ) = ((1280 / 2539) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1027523229 / 250000000) ≤ -Real.log (21 / 1280) ∧
    -Real.log (21 / 1280) ≤ (2055046461 / 500000000) := by
  have h := checkLog_sound (w := (19 / 61)) (n := 12)
    (lo := (80544627 / 125000000)) (hi := (644357017 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40 / 21) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(40 / 21) = 1/(21 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-2055046461 / 500000000) (-1027523229 / 250000000) (Real.log (21 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (341863979 / 500000000) ≤ -Real.log (160 / 317) ∧
    -Real.log (160 / 317) ≤ (683727959 / 1000000000) := by
  have h := checkLog_sound (w := (157 / 477)) (n := 12)
    (lo := (341863979 / 500000000)) (hi := (683727959 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((317 / 160) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(317 / 160) = 1/(160 / 317) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (341863979 / 500000000) (683727959 / 1000000000) (Real.log (317 / 160)) := by
  have h := reflection_log_7_neg
  have he : Real.log (317 / 160) = -Real.log (160 / 317) := by
    rw [show ((317 / 160) : ℝ) = ((160 / 317) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (3976561523 / 1000000000) ≤ -Real.log (3 / 160) ∧
    -Real.log (3 / 160) ≤ (3976561529 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 4)) (n := 12)
    (lo := (510825623 / 1000000000)) (hi := (63853203 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5 / 3) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(5 / 3) = 1/(3 / 160) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-3976561529 / 1000000000) (-3976561523 / 1000000000) (Real.log (3 / 160)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (561742667 / 1000000000) ≤ -Real.log (500000 / 876863) ∧
    -Real.log (500000 / 876863) ≤ (140435667 / 250000000) := by
  have h := checkLog_sound (w := (376863 / 1376863)) (n := 12)
    (lo := (561742667 / 1000000000)) (hi := (140435667 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((876863 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(876863 / 500000) = 1/(500000 / 876863) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (561742667 / 1000000000) (140435667 / 250000000) (Real.log (876863 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (876863 / 500000) = -Real.log (500000 / 876863) := by
    rw [show ((876863 / 500000) : ℝ) = ((500000 / 876863) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (70065527 / 50000000) ≤ -Real.log (123137 / 500000) ∧
    -Real.log (123137 / 500000) ≤ (1401310543 / 1000000000) := by
  have h := checkLog_sound (w := (1863 / 248137)) (n := 12)
    (lo := (750809 / 50000000)) (hi := (15016181 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 123137) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(125000 / 123137) = 1/(123137 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-1401310543 / 1000000000) (-70065527 / 50000000) (Real.log (123137 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (112669079 / 200000000) ≤ -Real.log (1000000 / 1756539) ∧
    -Real.log (1000000 / 1756539) ≤ (140836349 / 250000000) := by
  have h := checkLog_sound (w := (756539 / 2756539)) (n := 12)
    (lo := (112669079 / 200000000)) (hi := (140836349 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1756539 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1756539 / 1000000) = 1/(1000000 / 1756539) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (112669079 / 200000000) (140836349 / 250000000) (Real.log (1756539 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1756539 / 1000000) = -Real.log (1000000 / 1756539) := by
    rw [show ((1756539 / 1000000) : ℝ) = ((1000000 / 1756539) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (88299907 / 62500000) ≤ -Real.log (243461 / 1000000) ∧
    -Real.log (243461 / 1000000) ≤ (282559703 / 200000000) := by
  have h := checkLog_sound (w := (6539 / 493461)) (n := 12)
    (lo := (3313019 / 125000000)) (hi := (26504153 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 243461) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(250000 / 243461) = 1/(243461 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-282559703 / 200000000) (-88299907 / 62500000) (Real.log (243461 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (30530269 / 62500000) ≤ -Real.log (250000 / 407461) ∧
    -Real.log (250000 / 407461) ≤ (97696861 / 200000000) := by
  have h := checkLog_sound (w := (157461 / 657461)) (n := 12)
    (lo := (30530269 / 62500000)) (hi := (97696861 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((407461 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(407461 / 250000) = 1/(250000 / 407461) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (30530269 / 62500000) (97696861 / 200000000) (Real.log (407461 / 250000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (407461 / 250000) = -Real.log (250000 / 407461) := by
    rw [show ((407461 / 250000) : ℝ) = ((250000 / 407461) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (49691537 / 50000000) ≤ -Real.log (92539 / 250000) ∧
    -Real.log (92539 / 250000) ≤ (496915371 / 500000000) := by
  have h := checkLog_sound (w := (32461 / 217539)) (n := 12)
    (lo := (7517089 / 25000000)) (hi := (300683561 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 92539) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(125000 / 92539) = 1/(92539 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-496915371 / 500000000) (-49691537 / 50000000) (Real.log (92539 / 250000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (490404729 / 1000000000) ≤ -Real.log (1000000 / 1632977) ∧
    -Real.log (1000000 / 1632977) ≤ (49040473 / 100000000) := by
  have h := checkLog_sound (w := (632977 / 2632977)) (n := 12)
    (lo := (490404729 / 1000000000)) (hi := (49040473 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1632977 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1632977 / 1000000) = 1/(1000000 / 1632977) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (490404729 / 1000000000) (49040473 / 100000000) (Real.log (1632977 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1632977 / 1000000) = -Real.log (1000000 / 1632977) := by
    rw [show ((1632977 / 1000000) : ℝ) = ((1000000 / 1632977) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (501165381 / 500000000) ≤ -Real.log (367023 / 1000000) ∧
    -Real.log (367023 / 1000000) ≤ (250582691 / 250000000) := by
  have h := checkLog_sound (w := (132977 / 867023)) (n := 12)
    (lo := (154591791 / 500000000)) (hi := (309183583 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 367023) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 367023) = 1/(367023 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-250582691 / 250000000) (-501165381 / 500000000) (Real.log (367023 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (245381651 / 125000000) ≤ -Real.log (50000000000 / 356051795967) ∧
    -Real.log (50000000000 / 356051795967) ≤ (1963053211 / 1000000000) := by
  have h := checkLog_sound (w := (156051795967 / 556051795967)) (n := 12)
    (lo := (9011857 / 15625000)) (hi := (576758849 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((356051795967 / 200000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(356051795967 / 200000000000) = 1/(50000000000 / 356051795967) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (245381651 / 125000000) (1963053211 / 1000000000) (Real.log (356051795967 / 50000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (356051795967 / 50000000000) = -Real.log (50000000000 / 356051795967) := by
    rw [show ((356051795967 / 50000000000) : ℝ) = ((50000000000 / 356051795967) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (494035977 / 250000000) ≤ -Real.log (250000000000 / 1803717022439) ∧
    -Real.log (250000000000 / 1803717022439) ≤ (1976143911 / 1000000000) := by
  have h := checkLog_sound (w := (803717022439 / 2803717022439)) (n := 12)
    (lo := (147462387 / 250000000)) (hi := (589849549 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1803717022439 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1803717022439 / 1000000000000) = 1/(250000000000 / 1803717022439) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (494035977 / 250000000) (1976143911 / 1000000000) (Real.log (1803717022439 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1803717022439 / 250000000000) = -Real.log (250000000000 / 1803717022439) := by
    rw [show ((1803717022439 / 250000000000) : ℝ) = ((250000000000 / 1803717022439) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (370578761 / 250000000) ≤ -Real.log (500000000000 / 2201563665049) ∧
    -Real.log (500000000000 / 2201563665049) ≤ (1482315047 / 1000000000) := by
  have h := checkLog_sound (w := (201563665049 / 4201563665049)) (n := 12)
    (lo := (24005171 / 250000000)) (hi := (19204137 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2201563665049 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2201563665049 / 2000000000000) = 1/(500000000000 / 2201563665049) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (370578761 / 250000000) (1482315047 / 1000000000) (Real.log (2201563665049 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (2201563665049 / 500000000000) = -Real.log (500000000000 / 2201563665049) := by
    rw [show ((2201563665049 / 500000000000) : ℝ) = ((500000000000 / 2201563665049) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (149273549 / 100000000) ≤ -Real.log (500000000000 / 2224624887269) ∧
    -Real.log (500000000000 / 2224624887269) ≤ (1492735493 / 1000000000) := by
  have h := checkLog_sound (w := (224624887269 / 4224624887269)) (n := 12)
    (lo := (10644113 / 100000000)) (hi := (106441131 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2224624887269 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2224624887269 / 2000000000000) = 1/(500000000000 / 2224624887269) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (149273549 / 100000000) (1492735493 / 1000000000) (Real.log (2224624887269 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (2224624887269 / 500000000000) = -Real.log (500000000000 / 2224624887269) := by
    rw [show ((2224624887269 / 500000000000) : ℝ) = ((500000000000 / 2224624887269) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0018
