import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0077
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

theorem reflection_log_1_neg : (176262861 / 500000000) ≤ -Real.log (1280 / 1821) ∧
    -Real.log (1280 / 1821) ≤ (352525723 / 1000000000) := by
  have h := checkLog_sound (w := (541 / 3101)) (n := 12)
    (lo := (176262861 / 500000000)) (hi := (352525723 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1821 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1821 / 1280) = 1/(1280 / 1821) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (176262861 / 500000000) (352525723 / 1000000000) (Real.log (1821 / 1280)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1821 / 1280) = -Real.log (1280 / 1821) := by
    rw [show ((1821 / 1280) : ℝ) = ((1280 / 1821) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (109863487 / 200000000) ≤ -Real.log (739 / 1280) ∧
    -Real.log (739 / 1280) ≤ (137329359 / 250000000) := by
  have h := checkLog_sound (w := (541 / 2019)) (n := 12)
    (lo := (109863487 / 200000000)) (hi := (137329359 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 739) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 739) = 1/(739 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-137329359 / 250000000) (-109863487 / 200000000) (Real.log (739 / 1280)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (17585083 / 50000000) ≤ -Real.log (2560 / 3639) ∧
    -Real.log (2560 / 3639) ≤ (351701661 / 1000000000) := by
  have h := checkLog_sound (w := (1079 / 6199)) (n := 12)
    (lo := (17585083 / 50000000)) (hi := (351701661 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3639 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3639 / 2560) = 1/(2560 / 3639) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (17585083 / 50000000) (351701661 / 1000000000) (Real.log (3639 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3639 / 2560) = -Real.log (2560 / 3639) := by
    rw [show ((3639 / 2560) : ℝ) = ((2560 / 3639) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (547289723 / 1000000000) ≤ -Real.log (1481 / 2560) ∧
    -Real.log (1481 / 2560) ≤ (136822431 / 250000000) := by
  have h := checkLog_sound (w := (1079 / 4041)) (n := 12)
    (lo := (547289723 / 1000000000)) (hi := (136822431 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1481) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1481) = 1/(1481 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-136822431 / 250000000) (-547289723 / 1000000000) (Real.log (1481 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (612648639 / 1000000000) ≤ -Real.log (640 / 1181) ∧
    -Real.log (640 / 1181) ≤ (1914527 / 3125000) := by
  have h := checkLog_sound (w := (541 / 1821)) (n := 12)
    (lo := (612648639 / 1000000000)) (hi := (1914527 / 3125000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1181 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1181 / 640) = 1/(640 / 1181) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (612648639 / 1000000000) (1914527 / 3125000) (Real.log (1181 / 640)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1181 / 640) = -Real.log (640 / 1181) := by
    rw [show ((1181 / 640) : ℝ) = ((640 / 1181) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (74653933 / 40000000) ≤ -Real.log (99 / 640) ∧
    -Real.log (99 / 640) ≤ (233293541 / 125000000) := by
  have h := checkLog_sound (w := (61 / 259)) (n := 12)
    (lo := (96010793 / 200000000)) (hi := (240026983 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 99) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(160 / 99) = 1/(99 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-233293541 / 125000000) (-74653933 / 40000000) (Real.log (99 / 640)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (305688861 / 500000000) ≤ -Real.log (1280 / 2359) ∧
    -Real.log (1280 / 2359) ≤ (611377723 / 1000000000) := by
  have h := checkLog_sound (w := (1079 / 3639)) (n := 12)
    (lo := (305688861 / 500000000)) (hi := (611377723 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2359 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2359 / 1280) = 1/(1280 / 2359) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (305688861 / 500000000) (611377723 / 1000000000) (Real.log (2359 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2359 / 1280) = -Real.log (1280 / 2359) := by
    rw [show ((2359 / 1280) : ℝ) = ((1280 / 2359) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (1851310447 / 1000000000) ≤ -Real.log (201 / 1280) ∧
    -Real.log (201 / 1280) ≤ (37026209 / 20000000) := by
  have h := checkLog_sound (w := (119 / 521)) (n := 12)
    (lo := (465016087 / 1000000000)) (hi := (58127011 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 201) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(320 / 201) = 1/(201 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-37026209 / 20000000) (-1851310447 / 1000000000) (Real.log (201 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (484193721 / 1000000000) ≤ -Real.log (500000 / 811433) ∧
    -Real.log (500000 / 811433) ≤ (242096861 / 500000000) := by
  have h := checkLog_sound (w := (311433 / 1311433)) (n := 12)
    (lo := (484193721 / 1000000000)) (hi := (242096861 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((811433 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(811433 / 500000) = 1/(500000 / 811433) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (484193721 / 1000000000) (242096861 / 500000000) (Real.log (811433 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (811433 / 500000) = -Real.log (500000 / 811433) := by
    rw [show ((811433 / 500000) : ℝ) = ((500000 / 811433) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (243788679 / 250000000) ≤ -Real.log (188567 / 500000) ∧
    -Real.log (188567 / 500000) ≤ (487577359 / 500000000) := by
  have h := checkLog_sound (w := (61433 / 438567)) (n := 12)
    (lo := (17625471 / 62500000)) (hi := (282007537 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 188567) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 188567) = 1/(188567 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-487577359 / 500000000) (-243788679 / 250000000) (Real.log (188567 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (485413657 / 1000000000) ≤ -Real.log (1000000 / 1624847) ∧
    -Real.log (1000000 / 1624847) ≤ (242706829 / 500000000) := by
  have h := checkLog_sound (w := (624847 / 2624847)) (n := 12)
    (lo := (485413657 / 1000000000)) (hi := (242706829 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1624847 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1624847 / 1000000) = 1/(1000000 / 1624847) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (485413657 / 1000000000) (242706829 / 500000000) (Real.log (1624847 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1624847 / 1000000) = -Real.log (1000000 / 1624847) := by
    rw [show ((1624847 / 1000000) : ℝ) = ((1000000 / 1624847) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (196084267 / 200000000) ≤ -Real.log (375153 / 1000000) ∧
    -Real.log (375153 / 1000000) ≤ (980421337 / 1000000000) := by
  have h := checkLog_sound (w := (124847 / 875153)) (n := 12)
    (lo := (57454831 / 200000000)) (hi := (71818539 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 375153) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 375153) = 1/(375153 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-980421337 / 1000000000) (-196084267 / 200000000) (Real.log (375153 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (200366297 / 500000000) ≤ -Real.log (500000 / 746459) ∧
    -Real.log (500000 / 746459) ≤ (80146519 / 200000000) := by
  have h := checkLog_sound (w := (246459 / 1246459)) (n := 12)
    (lo := (200366297 / 500000000)) (hi := (80146519 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((746459 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(746459 / 500000) = 1/(500000 / 746459) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (200366297 / 500000000) (80146519 / 200000000) (Real.log (746459 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (746459 / 500000) = -Real.log (500000 / 746459) := by
    rw [show ((746459 / 500000) : ℝ) = ((500000 / 746459) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (84885319 / 125000000) ≤ -Real.log (253541 / 500000) ∧
    -Real.log (253541 / 500000) ≤ (679082553 / 1000000000) := by
  have h := checkLog_sound (w := (246459 / 753541)) (n := 12)
    (lo := (84885319 / 125000000)) (hi := (679082553 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 253541) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 253541) = 1/(253541 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-679082553 / 1000000000) (-84885319 / 125000000) (Real.log (253541 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (100507303 / 250000000) ≤ -Real.log (200000 / 298971) ∧
    -Real.log (200000 / 298971) ≤ (402029213 / 1000000000) := by
  have h := checkLog_sound (w := (98971 / 498971)) (n := 12)
    (lo := (100507303 / 250000000)) (hi := (402029213 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((298971 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(298971 / 200000) = 1/(200000 / 298971) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (100507303 / 250000000) (402029213 / 1000000000) (Real.log (298971 / 200000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (298971 / 200000) = -Real.log (200000 / 298971) := by
    rw [show ((298971 / 200000) : ℝ) = ((200000 / 298971) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (341454881 / 500000000) ≤ -Real.log (101029 / 200000) ∧
    -Real.log (101029 / 200000) ≤ (682909763 / 1000000000) := by
  have h := checkLog_sound (w := (98971 / 301029)) (n := 12)
    (lo := (341454881 / 500000000)) (hi := (682909763 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 101029) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 101029) = 1/(101029 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-682909763 / 1000000000) (-341454881 / 500000000) (Real.log (101029 / 200000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1459348437 / 1000000000) ≤ -Real.log (500000000000 / 2151577423409) ∧
    -Real.log (500000000000 / 2151577423409) ≤ (36483711 / 25000000) := by
  have h := checkLog_sound (w := (151577423409 / 4151577423409)) (n := 12)
    (lo := (73054077 / 1000000000)) (hi := (36527039 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2151577423409 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2151577423409 / 2000000000000) = 1/(500000000000 / 2151577423409) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1459348437 / 1000000000) (36483711 / 25000000) (Real.log (2151577423409 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (2151577423409 / 500000000000) = -Real.log (500000000000 / 2151577423409) := by
    rw [show ((2151577423409 / 500000000000) : ℝ) = ((500000000000 / 2151577423409) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (91614687 / 62500000) ≤ -Real.log (50000000000 / 216557911039) ∧
    -Real.log (50000000000 / 216557911039) ≤ (293166999 / 200000000) := by
  have h := checkLog_sound (w := (16557911039 / 416557911039)) (n := 12)
    (lo := (9942579 / 125000000)) (hi := (79540633 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((216557911039 / 200000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(216557911039 / 200000000000) = 1/(50000000000 / 216557911039) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (91614687 / 62500000) (293166999 / 200000000) (Real.log (216557911039 / 50000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (216557911039 / 50000000000) = -Real.log (50000000000 / 216557911039) := by
    rw [show ((216557911039 / 50000000000) : ℝ) = ((50000000000 / 216557911039) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (539907573 / 500000000) ≤ -Real.log (500000000000 / 1472067634031) ∧
    -Real.log (500000000000 / 1472067634031) ≤ (269953787 / 250000000) := by
  have h := checkLog_sound (w := (472067634031 / 2472067634031)) (n := 12)
    (lo := (193333983 / 500000000)) (hi := (386667967 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1472067634031 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1472067634031 / 1000000000000) = 1/(500000000000 / 1472067634031) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (539907573 / 500000000) (269953787 / 250000000) (Real.log (1472067634031 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (1472067634031 / 500000000000) = -Real.log (500000000000 / 1472067634031) := by
    rw [show ((1472067634031 / 500000000000) : ℝ) = ((500000000000 / 1472067634031) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (1084938973 / 1000000000) ≤ -Real.log (5000000000 / 14796296113) ∧
    -Real.log (5000000000 / 14796296113) ≤ (43397559 / 40000000) := by
  have h := checkLog_sound (w := (4796296113 / 24796296113)) (n := 12)
    (lo := (391791793 / 1000000000)) (hi := (195895897 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((14796296113 / 10000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(14796296113 / 10000000000) = 1/(5000000000 / 14796296113) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (1084938973 / 1000000000) (43397559 / 40000000) (Real.log (14796296113 / 5000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (14796296113 / 5000000000) = -Real.log (5000000000 / 14796296113) := by
    rw [show ((14796296113 / 5000000000) : ℝ) = ((5000000000 / 14796296113) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0077
