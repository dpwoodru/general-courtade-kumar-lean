import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0032
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

theorem reflection_log_1_neg : (77784557 / 200000000) ≤ -Real.log (2560 / 3777) ∧
    -Real.log (2560 / 3777) ≤ (194461393 / 500000000) := by
  have h := checkLog_sound (w := (1217 / 6337)) (n := 12)
    (lo := (77784557 / 200000000)) (hi := (194461393 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3777 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3777 / 2560) = 1/(2560 / 3777) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (77784557 / 200000000) (194461393 / 500000000) (Real.log (3777 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3777 / 2560) = -Real.log (2560 / 3777) := by
    rw [show ((3777 / 2560) : ℝ) = ((2560 / 3777) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (32255067 / 50000000) ≤ -Real.log (1343 / 2560) ∧
    -Real.log (1343 / 2560) ≤ (645101341 / 1000000000) := by
  have h := checkLog_sound (w := (1217 / 3903)) (n := 12)
    (lo := (32255067 / 50000000)) (hi := (645101341 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1343) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1343) = 1/(1343 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-645101341 / 1000000000) (-32255067 / 50000000) (Real.log (1343 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (97032047 / 250000000) ≤ -Real.log (1280 / 1887) ∧
    -Real.log (1280 / 1887) ≤ (388128189 / 1000000000) := by
  have h := checkLog_sound (w := (607 / 3167)) (n := 12)
    (lo := (97032047 / 250000000)) (hi := (388128189 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1887 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1887 / 1280) = 1/(1280 / 1887) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (97032047 / 250000000) (388128189 / 1000000000) (Real.log (1887 / 1280)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1887 / 1280) = -Real.log (1280 / 1887) := by
    rw [show ((1887 / 1280) : ℝ) = ((1280 / 1887) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (642870027 / 1000000000) ≤ -Real.log (673 / 1280) ∧
    -Real.log (673 / 1280) ≤ (160717507 / 250000000) := by
  have h := checkLog_sound (w := (607 / 1953)) (n := 12)
    (lo := (642870027 / 1000000000)) (hi := (160717507 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 673) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 673) = 1/(673 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-160717507 / 250000000) (-642870027 / 1000000000) (Real.log (673 / 1280)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (668229933 / 1000000000) ≤ -Real.log (1280 / 2497) ∧
    -Real.log (1280 / 2497) ≤ (334114967 / 500000000) := by
  have h := checkLog_sound (w := (1217 / 3777)) (n := 12)
    (lo := (668229933 / 1000000000)) (hi := (334114967 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2497 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2497 / 1280) = 1/(1280 / 2497) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (668229933 / 1000000000) (334114967 / 500000000) (Real.log (2497 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2497 / 1280) = -Real.log (1280 / 2497) := by
    rw [show ((2497 / 1280) : ℝ) = ((1280 / 2497) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (752870157 / 250000000) ≤ -Real.log (63 / 1280) ∧
    -Real.log (63 / 1280) ≤ (3011480633 / 1000000000) := by
  have h := checkLog_sound (w := (17 / 143)) (n := 12)
    (lo := (59722977 / 250000000)) (hi := (238891909 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80 / 63) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(80 / 63) = 1/(63 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-3011480633 / 1000000000) (-752870157 / 250000000) (Real.log (63 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (667027769 / 1000000000) ≤ -Real.log (640 / 1247) ∧
    -Real.log (640 / 1247) ≤ (66702777 / 100000000) := by
  have h := checkLog_sound (w := (607 / 1887)) (n := 12)
    (lo := (667027769 / 1000000000)) (hi := (66702777 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1247 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1247 / 640) = 1/(640 / 1247) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (667027769 / 1000000000) (66702777 / 100000000) (Real.log (1247 / 640)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1247 / 640) = -Real.log (640 / 1247) := by
    rw [show ((1247 / 640) : ℝ) = ((640 / 1247) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (741240153 / 250000000) ≤ -Real.log (33 / 640) ∧
    -Real.log (33 / 640) ≤ (2964960617 / 1000000000) := by
  have h := checkLog_sound (w := (7 / 73)) (n := 12)
    (lo := (48092973 / 250000000)) (hi := (192371893 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40 / 33) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(40 / 33) = 1/(33 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-2964960617 / 1000000000) (-741240153 / 250000000) (Real.log (33 / 640)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (541368601 / 1000000000) ≤ -Real.log (1000000 / 1718357) ∧
    -Real.log (1000000 / 1718357) ≤ (270684301 / 500000000) := by
  have h := checkLog_sound (w := (718357 / 2718357)) (n := 12)
    (lo := (541368601 / 1000000000)) (hi := (270684301 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1718357 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1718357 / 1000000) = 1/(1000000 / 1718357) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (541368601 / 1000000000) (270684301 / 500000000) (Real.log (1718357 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1718357 / 1000000) = -Real.log (1000000 / 1718357) := by
    rw [show ((1718357 / 1000000) : ℝ) = ((1000000 / 1718357) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (633557483 / 500000000) ≤ -Real.log (281643 / 1000000) ∧
    -Real.log (281643 / 1000000) ≤ (158389371 / 125000000) := by
  have h := checkLog_sound (w := (218357 / 781643)) (n := 12)
    (lo := (286983893 / 500000000)) (hi := (573967787 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 281643) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 281643) = 1/(281643 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-158389371 / 125000000) (-633557483 / 500000000) (Real.log (281643 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (542742807 / 1000000000) ≤ -Real.log (12500 / 21509) ∧
    -Real.log (12500 / 21509) ≤ (67842851 / 125000000) := by
  have h := checkLog_sound (w := (9009 / 34009)) (n := 12)
    (lo := (542742807 / 1000000000)) (hi := (67842851 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((21509 / 12500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(21509 / 12500) = 1/(12500 / 21509) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (542742807 / 1000000000) (67842851 / 125000000) (Real.log (21509 / 12500)) := by
  have h := reflection_log_11_neg
  have he : Real.log (21509 / 12500) = -Real.log (12500 / 21509) := by
    rw [show ((21509 / 12500) : ℝ) = ((12500 / 21509) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (255108083 / 200000000) ≤ -Real.log (3491 / 12500) ∧
    -Real.log (3491 / 12500) ≤ (1275540417 / 1000000000) := by
  have h := checkLog_sound (w := (2759 / 9741)) (n := 12)
    (lo := (116478647 / 200000000)) (hi := (145598309 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6250 / 3491) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(6250 / 3491) = 1/(3491 / 12500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1275540417 / 1000000000) (-255108083 / 200000000) (Real.log (3491 / 12500)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (116093987 / 250000000) ≤ -Real.log (1000000 / 1591021) ∧
    -Real.log (1000000 / 1591021) ≤ (464375949 / 1000000000) := by
  have h := checkLog_sound (w := (591021 / 2591021)) (n := 12)
    (lo := (116093987 / 250000000)) (hi := (464375949 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1591021 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1591021 / 1000000) = 1/(1000000 / 1591021) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (116093987 / 250000000) (464375949 / 1000000000) (Real.log (1591021 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1591021 / 1000000) = -Real.log (1000000 / 1591021) := by
    rw [show ((1591021 / 1000000) : ℝ) = ((1000000 / 1591021) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (223522867 / 250000000) ≤ -Real.log (408979 / 1000000) ∧
    -Real.log (408979 / 1000000) ≤ (89409147 / 100000000) := by
  have h := checkLog_sound (w := (91021 / 908979)) (n := 12)
    (lo := (6279509 / 31250000)) (hi := (200944289 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 408979) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 408979) = 1/(408979 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-89409147 / 100000000) (-223522867 / 250000000) (Real.log (408979 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (465980547 / 1000000000) ≤ -Real.log (125000 / 199197) ∧
    -Real.log (125000 / 199197) ≤ (116495137 / 250000000) := by
  have h := checkLog_sound (w := (74197 / 324197)) (n := 12)
    (lo := (465980547 / 1000000000)) (hi := (116495137 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((199197 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(199197 / 125000) = 1/(125000 / 199197) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (465980547 / 1000000000) (116495137 / 250000000) (Real.log (199197 / 125000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (199197 / 125000) = -Real.log (125000 / 199197) := by
    rw [show ((199197 / 125000) : ℝ) = ((125000 / 199197) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (112544791 / 125000000) ≤ -Real.log (50803 / 125000) ∧
    -Real.log (50803 / 125000) ≤ (90035833 / 100000000) := by
  have h := checkLog_sound (w := (11697 / 113303)) (n := 12)
    (lo := (51802787 / 250000000)) (hi := (207211149 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 50803) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(62500 / 50803) = 1/(50803 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-90035833 / 100000000) (-112544791 / 125000000) (Real.log (50803 / 125000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (113030223 / 62500000) ≤ -Real.log (250000000000 / 1525297095969) ∧
    -Real.log (250000000000 / 1525297095969) ≤ (1808483571 / 1000000000) := by
  have h := checkLog_sound (w := (525297095969 / 2525297095969)) (n := 12)
    (lo := (52773651 / 125000000)) (hi := (422189209 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1525297095969 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1525297095969 / 1000000000000) = 1/(250000000000 / 1525297095969) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (113030223 / 62500000) (1808483571 / 1000000000) (Real.log (1525297095969 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1525297095969 / 250000000000) = -Real.log (250000000000 / 1525297095969) := by
    rw [show ((1525297095969 / 250000000000) : ℝ) = ((250000000000 / 1525297095969) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (909141611 / 500000000) ≤ -Real.log (25000000000 / 154031796047) ∧
    -Real.log (25000000000 / 154031796047) ≤ (72731329 / 40000000) := by
  have h := checkLog_sound (w := (54031796047 / 254031796047)) (n := 12)
    (lo := (215994431 / 500000000)) (hi := (431988863 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((154031796047 / 100000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(154031796047 / 100000000000) = 1/(25000000000 / 154031796047) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (909141611 / 500000000) (72731329 / 40000000) (Real.log (154031796047 / 25000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (154031796047 / 25000000000) = -Real.log (25000000000 / 154031796047) := by
    rw [show ((154031796047 / 25000000000) : ℝ) = ((25000000000 / 154031796047) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (169808427 / 125000000) ≤ -Real.log (62500000000 / 243139164847) ∧
    -Real.log (62500000000 / 243139164847) ≤ (679233709 / 500000000) := by
  have h := checkLog_sound (w := (118139164847 / 368139164847)) (n := 12)
    (lo := (166330059 / 250000000)) (hi := (665320237 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((243139164847 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(243139164847 / 125000000000) = 1/(62500000000 / 243139164847) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (169808427 / 125000000) (679233709 / 500000000) (Real.log (243139164847 / 62500000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (243139164847 / 62500000000) = -Real.log (62500000000 / 243139164847) := by
    rw [show ((243139164847 / 62500000000) : ℝ) = ((62500000000 / 243139164847) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (341584719 / 250000000) ≤ -Real.log (500000000000 / 1960484617051) ∧
    -Real.log (500000000000 / 1960484617051) ≤ (683169439 / 500000000) := by
  have h := checkLog_sound (w := (960484617051 / 2960484617051)) (n := 12)
    (lo := (42074481 / 62500000)) (hi := (673191697 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1960484617051 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1960484617051 / 1000000000000) = 1/(500000000000 / 1960484617051) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (341584719 / 250000000) (683169439 / 500000000) (Real.log (1960484617051 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1960484617051 / 500000000000) = -Real.log (500000000000 / 1960484617051) := by
    rw [show ((1960484617051 / 500000000000) : ℝ) = ((500000000000 / 1960484617051) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0032
