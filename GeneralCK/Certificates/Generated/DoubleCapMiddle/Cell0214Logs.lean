import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0214
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

theorem reflection_log_1_neg : (259354933 / 1000000000) ≤ -Real.log (1280 / 1659) ∧
    -Real.log (1280 / 1659) ≤ (129677467 / 500000000) := by
  have h := checkLog_sound (w := (379 / 2939)) (n := 12)
    (lo := (259354933 / 1000000000)) (hi := (129677467 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1659 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1659 / 1280) = 1/(1280 / 1659) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (259354933 / 1000000000) (129677467 / 500000000) (Real.log (1659 / 1280)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1659 / 1280) = -Real.log (1280 / 1659) := by
    rw [show ((1659 / 1280) : ℝ) = ((1280 / 1659) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (351110099 / 1000000000) ≤ -Real.log (901 / 1280) ∧
    -Real.log (901 / 1280) ≤ (3511101 / 10000000) := by
  have h := checkLog_sound (w := (379 / 2181)) (n := 12)
    (lo := (351110099 / 1000000000)) (hi := (3511101 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 901) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 901) = 1/(901 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-3511101 / 10000000) (-351110099 / 1000000000) (Real.log (901 / 1280)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (258902751 / 1000000000) ≤ -Real.log (5120 / 6633) ∧
    -Real.log (5120 / 6633) ≤ (8090711 / 31250000) := by
  have h := checkLog_sound (w := (1513 / 11753)) (n := 12)
    (lo := (258902751 / 1000000000)) (hi := (8090711 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6633 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6633 / 5120) = 1/(5120 / 6633) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (258902751 / 1000000000) (8090711 / 31250000) (Real.log (6633 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6633 / 5120) = -Real.log (5120 / 6633) := by
    rw [show ((6633 / 5120) : ℝ) = ((5120 / 6633) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (350278037 / 1000000000) ≤ -Real.log (3607 / 5120) ∧
    -Real.log (3607 / 5120) ≤ (175139019 / 500000000) := by
  have h := checkLog_sound (w := (1513 / 8727)) (n := 12)
    (lo := (350278037 / 1000000000)) (hi := (175139019 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3607) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3607) = 1/(3607 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-175139019 / 500000000) (-350278037 / 1000000000) (Real.log (3607 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (58138607 / 125000000) ≤ -Real.log (640 / 1019) ∧
    -Real.log (640 / 1019) ≤ (465108857 / 1000000000) := by
  have h := checkLog_sound (w := (379 / 1659)) (n := 12)
    (lo := (58138607 / 125000000)) (hi := (465108857 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1019 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1019 / 640) = 1/(640 / 1019) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (58138607 / 125000000) (465108857 / 1000000000) (Real.log (1019 / 640)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1019 / 640) = -Real.log (640 / 1019) := by
    rw [show ((1019 / 640) : ℝ) = ((640 / 1019) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (112118471 / 125000000) ≤ -Real.log (261 / 640) ∧
    -Real.log (261 / 640) ≤ (89694777 / 100000000) := by
  have h := checkLog_sound (w := (59 / 581)) (n := 12)
    (lo := (50950147 / 250000000)) (hi := (203800589 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 261) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(320 / 261) = 1/(261 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-89694777 / 100000000) (-112118471 / 125000000) (Real.log (261 / 640)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (46437257 / 100000000) ≤ -Real.log (2560 / 4073) ∧
    -Real.log (2560 / 4073) ≤ (464372571 / 1000000000) := by
  have h := checkLog_sound (w := (1513 / 6633)) (n := 12)
    (lo := (46437257 / 100000000)) (hi := (464372571 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4073 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4073 / 2560) = 1/(2560 / 4073) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (46437257 / 100000000) (464372571 / 1000000000) (Real.log (4073 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (4073 / 2560) = -Real.log (2560 / 4073) := by
    rw [show ((4073 / 2560) : ℝ) = ((2560 / 4073) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (447039163 / 500000000) ≤ -Real.log (1047 / 2560) ∧
    -Real.log (1047 / 2560) ≤ (111759791 / 125000000) := by
  have h := checkLog_sound (w := (233 / 2327)) (n := 12)
    (lo := (100465573 / 500000000)) (hi := (200931147 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 1047) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 1047) = 1/(1047 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-111759791 / 125000000) (-447039163 / 500000000) (Real.log (1047 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (354234267 / 1000000000) ≤ -Real.log (1000000 / 1425089) ∧
    -Real.log (1000000 / 1425089) ≤ (88558567 / 250000000) := by
  have h := checkLog_sound (w := (425089 / 2425089)) (n := 12)
    (lo := (354234267 / 1000000000)) (hi := (88558567 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1425089 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1425089 / 1000000) = 1/(1000000 / 1425089) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (354234267 / 1000000000) (88558567 / 250000000) (Real.log (1425089 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1425089 / 1000000) = -Real.log (1000000 / 1425089) := by
    rw [show ((1425089 / 1000000) : ℝ) = ((1000000 / 1425089) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (8649063 / 15625000) ≤ -Real.log (574911 / 1000000) ∧
    -Real.log (574911 / 1000000) ≤ (553540033 / 1000000000) := by
  have h := checkLog_sound (w := (425089 / 1574911)) (n := 12)
    (lo := (8649063 / 15625000)) (hi := (553540033 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 574911) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 574911) = 1/(574911 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-553540033 / 1000000000) (-8649063 / 15625000) (Real.log (574911 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (17742509 / 50000000) ≤ -Real.log (1000000 / 1425967) ∧
    -Real.log (1000000 / 1425967) ≤ (354850181 / 1000000000) := by
  have h := checkLog_sound (w := (425967 / 2425967)) (n := 12)
    (lo := (17742509 / 50000000)) (hi := (354850181 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1425967 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1425967 / 1000000) = 1/(1000000 / 1425967) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (17742509 / 50000000) (354850181 / 1000000000) (Real.log (1425967 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1425967 / 1000000) = -Real.log (1000000 / 1425967) := by
    rw [show ((1425967 / 1000000) : ℝ) = ((1000000 / 1425967) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (555068393 / 1000000000) ≤ -Real.log (574033 / 1000000) ∧
    -Real.log (574033 / 1000000) ≤ (277534197 / 500000000) := by
  have h := checkLog_sound (w := (425967 / 1574033)) (n := 12)
    (lo := (555068393 / 1000000000)) (hi := (277534197 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 574033) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 574033) = 1/(574033 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-277534197 / 500000000) (-555068393 / 1000000000) (Real.log (574033 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (8590197 / 31250000) ≤ -Real.log (1000000 / 1316381) ∧
    -Real.log (1000000 / 1316381) ≤ (54977261 / 200000000) := by
  have h := checkLog_sound (w := (316381 / 2316381)) (n := 12)
    (lo := (8590197 / 31250000)) (hi := (54977261 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1316381 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1316381 / 1000000) = 1/(1000000 / 1316381) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (8590197 / 31250000) (54977261 / 200000000) (Real.log (1316381 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1316381 / 1000000) = -Real.log (1000000 / 1316381) := by
    rw [show ((1316381 / 1000000) : ℝ) = ((1000000 / 1316381) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (190177267 / 500000000) ≤ -Real.log (683619 / 1000000) ∧
    -Real.log (683619 / 1000000) ≤ (76070907 / 200000000) := by
  have h := checkLog_sound (w := (316381 / 1683619)) (n := 12)
    (lo := (190177267 / 500000000)) (hi := (76070907 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 683619) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 683619) = 1/(683619 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-76070907 / 200000000) (-190177267 / 500000000) (Real.log (683619 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (275434627 / 1000000000) ≤ -Real.log (1000000 / 1317103) ∧
    -Real.log (1000000 / 1317103) ≤ (68858657 / 250000000) := by
  have h := checkLog_sound (w := (317103 / 2317103)) (n := 12)
    (lo := (275434627 / 1000000000)) (hi := (68858657 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1317103 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1317103 / 1000000) = 1/(1000000 / 1317103) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (275434627 / 1000000000) (68858657 / 250000000) (Real.log (1317103 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1317103 / 1000000) = -Real.log (1000000 / 1317103) := by
    rw [show ((1317103 / 1000000) : ℝ) = ((1000000 / 1317103) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (95352809 / 250000000) ≤ -Real.log (682897 / 1000000) ∧
    -Real.log (682897 / 1000000) ≤ (381411237 / 1000000000) := by
  have h := checkLog_sound (w := (317103 / 1682897)) (n := 12)
    (lo := (95352809 / 250000000)) (hi := (381411237 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 682897) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 682897) = 1/(682897 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-381411237 / 1000000000) (-95352809 / 250000000) (Real.log (682897 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (9077743 / 10000000) ≤ -Real.log (1250000000 / 3098499159) ∧
    -Real.log (1250000000 / 3098499159) ≤ (453887151 / 500000000) := by
  have h := checkLog_sound (w := (598499159 / 5598499159)) (n := 12)
    (lo := (2682839 / 12500000)) (hi := (214627121 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3098499159 / 2500000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(3098499159 / 2500000000) = 1/(1250000000 / 3098499159) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (9077743 / 10000000) (453887151 / 500000000) (Real.log (3098499159 / 1250000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (3098499159 / 1250000000) = -Real.log (1250000000 / 3098499159) := by
    rw [show ((3098499159 / 1250000000) : ℝ) = ((1250000000 / 3098499159) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (227479643 / 250000000) ≤ -Real.log (62500000000 / 155257515683) ∧
    -Real.log (62500000000 / 155257515683) ≤ (454959287 / 500000000) := by
  have h := checkLog_sound (w := (30257515683 / 280257515683)) (n := 12)
    (lo := (3387053 / 15625000)) (hi := (216771393 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((155257515683 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(155257515683 / 125000000000) = 1/(62500000000 / 155257515683) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (227479643 / 250000000) (454959287 / 500000000) (Real.log (155257515683 / 62500000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (155257515683 / 62500000000) = -Real.log (62500000000 / 155257515683) := by
    rw [show ((155257515683 / 62500000000) : ℝ) = ((62500000000 / 155257515683) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (327620419 / 500000000) ≤ -Real.log (500000000000 / 962803111089) ∧
    -Real.log (500000000000 / 962803111089) ≤ (655240839 / 1000000000) := by
  have h := checkLog_sound (w := (462803111089 / 1462803111089)) (n := 12)
    (lo := (327620419 / 500000000)) (hi := (655240839 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((962803111089 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(962803111089 / 500000000000) = 1/(500000000000 / 962803111089) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (327620419 / 500000000) (655240839 / 1000000000) (Real.log (962803111089 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (962803111089 / 500000000000) = -Real.log (500000000000 / 962803111089) := by
    rw [show ((962803111089 / 500000000000) : ℝ) = ((500000000000 / 962803111089) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (656845863 / 1000000000) ≤ -Real.log (125000000000 / 241087418747) ∧
    -Real.log (125000000000 / 241087418747) ≤ (82105733 / 125000000) := by
  have h := checkLog_sound (w := (116087418747 / 366087418747)) (n := 12)
    (lo := (656845863 / 1000000000)) (hi := (82105733 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((241087418747 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(241087418747 / 125000000000) = 1/(125000000000 / 241087418747) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (656845863 / 1000000000) (82105733 / 125000000) (Real.log (241087418747 / 125000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (241087418747 / 125000000000) = -Real.log (125000000000 / 241087418747) := by
    rw [show ((241087418747 / 125000000000) : ℝ) = ((125000000000 / 241087418747) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0214
