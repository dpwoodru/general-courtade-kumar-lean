import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0098
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

theorem reflection_log_1_neg : (335076173 / 1000000000) ≤ -Real.log (2560 / 3579) ∧
    -Real.log (2560 / 3579) ≤ (167538087 / 500000000) := by
  have h := checkLog_sound (w := (1019 / 6139)) (n := 12)
    (lo := (335076173 / 1000000000)) (hi := (167538087 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3579 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3579 / 2560) = 1/(2560 / 3579) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (335076173 / 1000000000) (167538087 / 500000000) (Real.log (3579 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3579 / 2560) = -Real.log (2560 / 3579) := by
    rw [show ((3579 / 2560) : ℝ) = ((2560 / 3579) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (253787851 / 500000000) ≤ -Real.log (1541 / 2560) ∧
    -Real.log (1541 / 2560) ≤ (507575703 / 1000000000) := by
  have h := checkLog_sound (w := (1019 / 4101)) (n := 12)
    (lo := (253787851 / 500000000)) (hi := (507575703 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1541) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1541) = 1/(1541 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-507575703 / 1000000000) (-253787851 / 500000000) (Real.log (1541 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (167118799 / 500000000) ≤ -Real.log (320 / 447) ∧
    -Real.log (320 / 447) ≤ (334237599 / 1000000000) := by
  have h := checkLog_sound (w := (127 / 767)) (n := 12)
    (lo := (167118799 / 500000000)) (hi := (334237599 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((447 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(447 / 320) = 1/(320 / 447) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (167118799 / 500000000) (334237599 / 1000000000) (Real.log (447 / 320)) := by
  have h := reflection_log_3_neg
  have he : Real.log (447 / 320) = -Real.log (320 / 447) := by
    rw [show ((447 / 320) : ℝ) = ((320 / 447) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (252815403 / 500000000) ≤ -Real.log (193 / 320) ∧
    -Real.log (193 / 320) ≤ (505630807 / 1000000000) := by
  have h := checkLog_sound (w := (127 / 513)) (n := 12)
    (lo := (252815403 / 500000000)) (hi := (505630807 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 193) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(320 / 193) = 1/(193 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-505630807 / 1000000000) (-252815403 / 500000000) (Real.log (193 / 320)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (585614167 / 1000000000) ≤ -Real.log (1280 / 2299) ∧
    -Real.log (1280 / 2299) ≤ (73201771 / 125000000) := by
  have h := checkLog_sound (w := (1019 / 3579)) (n := 12)
    (lo := (585614167 / 1000000000)) (hi := (73201771 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2299 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2299 / 1280) = 1/(1280 / 2299) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (585614167 / 1000000000) (73201771 / 125000000) (Real.log (2299 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2299 / 1280) = -Real.log (1280 / 2299) := by
    rw [show ((2299 / 1280) : ℝ) = ((1280 / 2299) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (397523737 / 250000000) ≤ -Real.log (261 / 1280) ∧
    -Real.log (261 / 1280) ≤ (1590094951 / 1000000000) := by
  have h := checkLog_sound (w := (59 / 581)) (n := 12)
    (lo := (50950147 / 250000000)) (hi := (203800589 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 261) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(320 / 261) = 1/(261 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1590094951 / 1000000000) (-397523737 / 250000000) (Real.log (261 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (1460771 / 2500000) ≤ -Real.log (160 / 287) ∧
    -Real.log (160 / 287) ≤ (584308401 / 1000000000) := by
  have h := checkLog_sound (w := (127 / 447)) (n := 12)
    (lo := (1460771 / 2500000)) (hi := (584308401 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((287 / 160) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(287 / 160) = 1/(160 / 287) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (1460771 / 2500000) (584308401 / 1000000000) (Real.log (287 / 160)) := by
  have h := reflection_log_7_neg
  have he : Real.log (287 / 160) = -Real.log (160 / 287) := by
    rw [show ((287 / 160) : ℝ) = ((160 / 287) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (394666563 / 250000000) ≤ -Real.log (33 / 160) ∧
    -Real.log (33 / 160) ≤ (315733251 / 200000000) := by
  have h := checkLog_sound (w := (7 / 73)) (n := 12)
    (lo := (48092973 / 250000000)) (hi := (192371893 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40 / 33) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(40 / 33) = 1/(33 / 160) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-315733251 / 200000000) (-394666563 / 250000000) (Real.log (33 / 160)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (229395817 / 500000000) ≤ -Real.log (1000000 / 1582161) ∧
    -Real.log (1000000 / 1582161) ≤ (91758327 / 200000000) := by
  have h := checkLog_sound (w := (582161 / 2582161)) (n := 12)
    (lo := (229395817 / 500000000)) (hi := (91758327 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1582161 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1582161 / 1000000) = 1/(1000000 / 1582161) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (229395817 / 500000000) (91758327 / 200000000) (Real.log (1582161 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1582161 / 1000000) = -Real.log (1000000 / 1582161) := by
    rw [show ((1582161 / 1000000) : ℝ) = ((1000000 / 1582161) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (872659087 / 1000000000) ≤ -Real.log (417839 / 1000000) ∧
    -Real.log (417839 / 1000000) ≤ (872659089 / 1000000000) := by
  have h := checkLog_sound (w := (82161 / 917839)) (n := 12)
    (lo := (179511907 / 1000000000)) (hi := (44877977 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 417839) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 417839) = 1/(417839 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-872659089 / 1000000000) (-872659087 / 1000000000) (Real.log (417839 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (45999559 / 100000000) ≤ -Real.log (1000000 / 1584067) ∧
    -Real.log (1000000 / 1584067) ≤ (459995591 / 1000000000) := by
  have h := checkLog_sound (w := (584067 / 2584067)) (n := 12)
    (lo := (45999559 / 100000000)) (hi := (459995591 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1584067 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1584067 / 1000000) = 1/(1000000 / 1584067) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (45999559 / 100000000) (459995591 / 1000000000) (Real.log (1584067 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1584067 / 1000000) = -Real.log (1000000 / 1584067) := by
    rw [show ((1584067 / 1000000) : ℝ) = ((1000000 / 1584067) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (54826943 / 62500000) ≤ -Real.log (415933 / 1000000) ∧
    -Real.log (415933 / 1000000) ≤ (87723109 / 100000000) := by
  have h := checkLog_sound (w := (84067 / 915933)) (n := 12)
    (lo := (46020977 / 250000000)) (hi := (184083909 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 415933) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 415933) = 1/(415933 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-87723109 / 100000000) (-54826943 / 62500000) (Real.log (415933 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (18714509 / 50000000) ≤ -Real.log (1000000 / 1453959) ∧
    -Real.log (1000000 / 1453959) ≤ (374290181 / 1000000000) := by
  have h := checkLog_sound (w := (453959 / 2453959)) (n := 12)
    (lo := (18714509 / 50000000)) (hi := (374290181 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1453959 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1453959 / 1000000) = 1/(1000000 / 1453959) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (18714509 / 50000000) (374290181 / 1000000000) (Real.log (1453959 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1453959 / 1000000) = -Real.log (1000000 / 1453959) := by
    rw [show ((1453959 / 1000000) : ℝ) = ((1000000 / 1453959) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (302530607 / 500000000) ≤ -Real.log (546041 / 1000000) ∧
    -Real.log (546041 / 1000000) ≤ (121012243 / 200000000) := by
  have h := checkLog_sound (w := (453959 / 1546041)) (n := 12)
    (lo := (302530607 / 500000000)) (hi := (121012243 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 546041) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 546041) = 1/(546041 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-121012243 / 200000000) (-302530607 / 500000000) (Real.log (546041 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (11735017 / 31250000) ≤ -Real.log (1000000 / 1455749) ∧
    -Real.log (1000000 / 1455749) ≤ (75104109 / 200000000) := by
  have h := checkLog_sound (w := (455749 / 2455749)) (n := 12)
    (lo := (11735017 / 31250000)) (hi := (75104109 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1455749 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1455749 / 1000000) = 1/(1000000 / 1455749) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (11735017 / 31250000) (75104109 / 200000000) (Real.log (1455749 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1455749 / 1000000) = -Real.log (1000000 / 1455749) := by
    rw [show ((1455749 / 1000000) : ℝ) = ((1000000 / 1455749) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (608344741 / 1000000000) ≤ -Real.log (544251 / 1000000) ∧
    -Real.log (544251 / 1000000) ≤ (304172371 / 500000000) := by
  have h := checkLog_sound (w := (455749 / 1544251)) (n := 12)
    (lo := (608344741 / 1000000000)) (hi := (304172371 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 544251) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 544251) = 1/(544251 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-304172371 / 500000000) (-608344741 / 1000000000) (Real.log (544251 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1331450721 / 1000000000) ≤ -Real.log (500000000000 / 1893266305921) ∧
    -Real.log (500000000000 / 1893266305921) ≤ (1331450723 / 1000000000) := by
  have h := checkLog_sound (w := (893266305921 / 2893266305921)) (n := 12)
    (lo := (638303541 / 1000000000)) (hi := (319151771 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1893266305921 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1893266305921 / 1000000000000) = 1/(500000000000 / 1893266305921) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1331450721 / 1000000000) (1331450723 / 1000000000) (Real.log (1893266305921 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1893266305921 / 500000000000) = -Real.log (500000000000 / 1893266305921) := by
    rw [show ((1893266305921 / 500000000000) : ℝ) = ((500000000000 / 1893266305921) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1337226679 / 1000000000) ≤ -Real.log (250000000000 / 952116687063) ∧
    -Real.log (250000000000 / 952116687063) ≤ (1337226681 / 1000000000) := by
  have h := checkLog_sound (w := (452116687063 / 1452116687063)) (n := 12)
    (lo := (644079499 / 1000000000)) (hi := (1288159 / 2000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((952116687063 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(952116687063 / 500000000000) = 1/(250000000000 / 952116687063) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1337226679 / 1000000000) (1337226681 / 1000000000) (Real.log (952116687063 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (952116687063 / 250000000000) = -Real.log (250000000000 / 952116687063) := by
    rw [show ((952116687063 / 250000000000) : ℝ) = ((250000000000 / 952116687063) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (489675697 / 500000000) ≤ -Real.log (500000000000 / 1331364311471) ∧
    -Real.log (500000000000 / 1331364311471) ≤ (244837849 / 250000000) := by
  have h := checkLog_sound (w := (331364311471 / 2331364311471)) (n := 12)
    (lo := (143102107 / 500000000)) (hi := (57240843 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1331364311471 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1331364311471 / 1000000000000) = 1/(500000000000 / 1331364311471) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (489675697 / 500000000) (244837849 / 250000000) (Real.log (1331364311471 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (1331364311471 / 500000000000) = -Real.log (500000000000 / 1331364311471) := by
    rw [show ((1331364311471 / 500000000000) : ℝ) = ((500000000000 / 1331364311471) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (196773057 / 200000000) ≤ -Real.log (125000000000 / 334346882229) ∧
    -Real.log (125000000000 / 334346882229) ≤ (983865287 / 1000000000) := by
  have h := checkLog_sound (w := (84346882229 / 584346882229)) (n := 12)
    (lo := (58143621 / 200000000)) (hi := (145359053 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((334346882229 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(334346882229 / 250000000000) = 1/(125000000000 / 334346882229) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (196773057 / 200000000) (983865287 / 1000000000) (Real.log (334346882229 / 125000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (334346882229 / 125000000000) = -Real.log (125000000000 / 334346882229) := by
    rw [show ((334346882229 / 125000000000) : ℝ) = ((125000000000 / 334346882229) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0098
