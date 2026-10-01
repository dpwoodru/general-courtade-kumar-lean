import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0182
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

theorem reflection_log_1_neg : (273717837 / 1000000000) ≤ -Real.log (1280 / 1683) ∧
    -Real.log (1280 / 1683) ≤ (136858919 / 500000000) := by
  have h := checkLog_sound (w := (403 / 2963)) (n := 12)
    (lo := (273717837 / 1000000000)) (hi := (136858919 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1683 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1683 / 1280) = 1/(1280 / 1683) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (273717837 / 1000000000) (136858919 / 500000000) (Real.log (1683 / 1280)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1683 / 1280) = -Real.log (1280 / 1683) := by
    rw [show ((1683 / 1280) : ℝ) = ((1280 / 1683) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (94527091 / 250000000) ≤ -Real.log (877 / 1280) ∧
    -Real.log (877 / 1280) ≤ (75621673 / 200000000) := by
  have h := checkLog_sound (w := (403 / 2157)) (n := 12)
    (lo := (94527091 / 250000000)) (hi := (75621673 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 877) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 877) = 1/(877 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-75621673 / 200000000) (-94527091 / 250000000) (Real.log (877 / 1280)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (54654421 / 200000000) ≤ -Real.log (5120 / 6729) ∧
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


theorem reflection_log_3 : Bounds (54654421 / 200000000) (136636053 / 500000000) (Real.log (6729 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6729 / 5120) = -Real.log (5120 / 6729) := by
    rw [show ((6729 / 5120) : ℝ) = ((5120 / 6729) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (377253541 / 1000000000) ≤ -Real.log (3511 / 5120) ∧
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


theorem reflection_log_4 : Bounds (-188626771 / 500000000) (-377253541 / 1000000000) (Real.log (3511 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (244194139 / 500000000) ≤ -Real.log (640 / 1043) ∧
    -Real.log (640 / 1043) ≤ (488388279 / 1000000000) := by
  have h := checkLog_sound (w := (403 / 1683)) (n := 12)
    (lo := (244194139 / 500000000)) (hi := (488388279 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1043 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1043 / 640) = 1/(640 / 1043) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (244194139 / 500000000) (488388279 / 1000000000) (Real.log (1043 / 640)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1043 / 640) = -Real.log (640 / 1043) := by
    rw [show ((1043 / 640) : ℝ) = ((640 / 1043) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (496704017 / 500000000) ≤ -Real.log (237 / 640) ∧
    -Real.log (237 / 640) ≤ (248352009 / 250000000) := by
  have h := checkLog_sound (w := (83 / 557)) (n := 12)
    (lo := (150130427 / 500000000)) (hi := (60052171 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 237) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(320 / 237) = 1/(237 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-248352009 / 250000000) (-496704017 / 500000000) (Real.log (237 / 640)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (24383447 / 50000000) ≤ -Real.log (2560 / 4169) ∧
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


theorem reflection_log_7 : Bounds (24383447 / 50000000) (487668941 / 1000000000) (Real.log (4169 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (4169 / 2560) = -Real.log (2560 / 4169) := by
    rw [show ((4169 / 2560) : ℝ) = ((2560 / 4169) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (495124237 / 500000000) ≤ -Real.log (951 / 2560) ∧
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


theorem reflection_log_8 : Bounds (-247562119 / 250000000) (-495124237 / 500000000) (Real.log (951 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (373827887 / 1000000000) ≤ -Real.log (1000000 / 1453287) ∧
    -Real.log (1000000 / 1453287) ≤ (23364243 / 62500000) := by
  have h := checkLog_sound (w := (453287 / 2453287)) (n := 12)
    (lo := (373827887 / 1000000000)) (hi := (23364243 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1453287 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1453287 / 1000000) = 1/(1000000 / 1453287) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (373827887 / 1000000000) (23364243 / 62500000) (Real.log (1453287 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1453287 / 1000000) = -Real.log (1000000 / 1453287) := by
    rw [show ((1453287 / 1000000) : ℝ) = ((1000000 / 1453287) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (301915647 / 500000000) ≤ -Real.log (546713 / 1000000) ∧
    -Real.log (546713 / 1000000) ≤ (120766259 / 200000000) := by
  have h := checkLog_sound (w := (453287 / 1546713)) (n := 12)
    (lo := (301915647 / 500000000)) (hi := (120766259 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 546713) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 546713) = 1/(546713 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-120766259 / 200000000) (-301915647 / 500000000) (Real.log (546713 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (374438041 / 1000000000) ≤ -Real.log (500000 / 727087) ∧
    -Real.log (500000 / 727087) ≤ (187219021 / 500000000) := by
  have h := checkLog_sound (w := (227087 / 1227087)) (n := 12)
    (lo := (374438041 / 1000000000)) (hi := (187219021 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((727087 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(727087 / 500000) = 1/(500000 / 727087) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (374438041 / 1000000000) (187219021 / 500000000) (Real.log (727087 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (727087 / 500000) = -Real.log (500000 / 727087) := by
    rw [show ((727087 / 500000) : ℝ) = ((500000 / 727087) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (121091007 / 200000000) ≤ -Real.log (272913 / 500000) ∧
    -Real.log (272913 / 500000) ≤ (151363759 / 250000000) := by
  have h := checkLog_sound (w := (227087 / 772913)) (n := 12)
    (lo := (121091007 / 200000000)) (hi := (151363759 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 272913) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 272913) = 1/(272913 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-151363759 / 250000000) (-121091007 / 200000000) (Real.log (272913 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (292521841 / 1000000000) ≤ -Real.log (500000 / 669901) ∧
    -Real.log (500000 / 669901) ≤ (146260921 / 500000000) := by
  have h := checkLog_sound (w := (169901 / 1169901)) (n := 12)
    (lo := (292521841 / 1000000000)) (hi := (146260921 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((669901 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(669901 / 500000) = 1/(500000 / 669901) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (292521841 / 1000000000) (146260921 / 500000000) (Real.log (669901 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (669901 / 500000) = -Real.log (500000 / 669901) := by
    rw [show ((669901 / 500000) : ℝ) = ((500000 / 669901) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (3243871 / 7812500) ≤ -Real.log (330099 / 500000) ∧
    -Real.log (330099 / 500000) ≤ (415215489 / 1000000000) := by
  have h := checkLog_sound (w := (169901 / 830099)) (n := 12)
    (lo := (3243871 / 7812500)) (hi := (415215489 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 330099) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 330099) = 1/(330099 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-415215489 / 1000000000) (-3243871 / 7812500) (Real.log (330099 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (293077739 / 1000000000) ≤ -Real.log (1000000 / 1340547) ∧
    -Real.log (1000000 / 1340547) ≤ (14653887 / 50000000) := by
  have h := checkLog_sound (w := (340547 / 2340547)) (n := 12)
    (lo := (293077739 / 1000000000)) (hi := (14653887 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1340547 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1340547 / 1000000) = 1/(1000000 / 1340547) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (293077739 / 1000000000) (14653887 / 50000000) (Real.log (1340547 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1340547 / 1000000) = -Real.log (1000000 / 1340547) := by
    rw [show ((1340547 / 1000000) : ℝ) = ((1000000 / 1340547) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (16653783 / 40000000) ≤ -Real.log (659453 / 1000000) ∧
    -Real.log (659453 / 1000000) ≤ (813173 / 1953125) := by
  have h := checkLog_sound (w := (340547 / 1659453)) (n := 12)
    (lo := (16653783 / 40000000)) (hi := (813173 / 1953125))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 659453) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 659453) = 1/(659453 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-813173 / 1953125) (-16653783 / 40000000) (Real.log (659453 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (977659181 / 1000000000) ≤ -Real.log (25000000000 / 66455663209) ∧
    -Real.log (25000000000 / 66455663209) ≤ (977659183 / 1000000000) := by
  have h := checkLog_sound (w := (16455663209 / 116455663209)) (n := 12)
    (lo := (284512001 / 1000000000)) (hi := (142256001 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((66455663209 / 50000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(66455663209 / 50000000000) = 1/(25000000000 / 66455663209) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (977659181 / 1000000000) (977659183 / 1000000000) (Real.log (66455663209 / 25000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (66455663209 / 25000000000) = -Real.log (25000000000 / 66455663209) := by
    rw [show ((66455663209 / 25000000000) : ℝ) = ((25000000000 / 66455663209) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (244973269 / 250000000) ≤ -Real.log (62500000000 / 166510710373) ∧
    -Real.log (62500000000 / 166510710373) ≤ (489946539 / 500000000) := by
  have h := checkLog_sound (w := (41510710373 / 291510710373)) (n := 12)
    (lo := (35843237 / 125000000)) (hi := (286745897 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((166510710373 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(166510710373 / 125000000000) = 1/(62500000000 / 166510710373) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (244973269 / 250000000) (489946539 / 500000000) (Real.log (166510710373 / 62500000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (166510710373 / 62500000000) = -Real.log (62500000000 / 166510710373) := by
    rw [show ((166510710373 / 62500000000) : ℝ) = ((62500000000 / 166510710373) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (70773733 / 100000000) ≤ -Real.log (500000000000 / 1014697106019) ∧
    -Real.log (500000000000 / 1014697106019) ≤ (176934333 / 250000000) := by
  have h := checkLog_sound (w := (14697106019 / 2014697106019)) (n := 12)
    (lo := (291803 / 20000000)) (hi := (14590151 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1014697106019 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1014697106019 / 1000000000000) = 1/(500000000000 / 1014697106019) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (70773733 / 100000000) (176934333 / 250000000) (Real.log (1014697106019 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (1014697106019 / 500000000000) = -Real.log (500000000000 / 1014697106019) := by
    rw [show ((1014697106019 / 500000000000) : ℝ) = ((500000000000 / 1014697106019) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (354711157 / 500000000) ≤ -Real.log (500000000000 / 1016408295967) ∧
    -Real.log (500000000000 / 1016408295967) ≤ (177355579 / 250000000) := by
  have h := checkLog_sound (w := (16408295967 / 2016408295967)) (n := 12)
    (lo := (8137567 / 500000000)) (hi := (3255027 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1016408295967 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1016408295967 / 1000000000000) = 1/(500000000000 / 1016408295967) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (354711157 / 500000000) (177355579 / 250000000) (Real.log (1016408295967 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1016408295967 / 500000000000) = -Real.log (500000000000 / 1016408295967) := by
    rw [show ((1016408295967 / 500000000000) : ℝ) = ((500000000000 / 1016408295967) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0182
