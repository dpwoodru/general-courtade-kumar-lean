import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0089
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

theorem reflection_log_1_neg : (171295933 / 500000000) ≤ -Real.log (1280 / 1803) ∧
    -Real.log (1280 / 1803) ≤ (342591867 / 1000000000) := by
  have h := checkLog_sound (w := (523 / 3083)) (n := 12)
    (lo := (171295933 / 500000000)) (hi := (342591867 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1803 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1803 / 1280) = 1/(1280 / 1803) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (171295933 / 500000000) (342591867 / 1000000000) (Real.log (1803 / 1280)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1803 / 1280) = -Real.log (1280 / 1803) := by
    rw [show ((1803 / 1280) : ℝ) = ((1280 / 1803) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (525252103 / 1000000000) ≤ -Real.log (757 / 1280) ∧
    -Real.log (757 / 1280) ≤ (65656513 / 125000000) := by
  have h := checkLog_sound (w := (523 / 2037)) (n := 12)
    (lo := (525252103 / 1000000000)) (hi := (65656513 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 757) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 757) = 1/(757 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-65656513 / 125000000) (-525252103 / 1000000000) (Real.log (757 / 1280)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (341759573 / 1000000000) ≤ -Real.log (2560 / 3603) ∧
    -Real.log (2560 / 3603) ≤ (170879787 / 500000000) := by
  have h := checkLog_sound (w := (1043 / 6163)) (n := 12)
    (lo := (341759573 / 1000000000)) (hi := (170879787 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3603 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3603 / 2560) = 1/(2560 / 3603) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (341759573 / 1000000000) (170879787 / 500000000) (Real.log (3603 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3603 / 2560) = -Real.log (2560 / 3603) := by
    rw [show ((3603 / 2560) : ℝ) = ((2560 / 3603) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (261636279 / 500000000) ≤ -Real.log (1517 / 2560) ∧
    -Real.log (1517 / 2560) ≤ (523272559 / 1000000000) := by
  have h := checkLog_sound (w := (1043 / 4077)) (n := 12)
    (lo := (261636279 / 500000000)) (hi := (523272559 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1517) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1517) = 1/(1517 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-523272559 / 1000000000) (-261636279 / 500000000) (Real.log (1517 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (74661247 / 125000000) ≤ -Real.log (640 / 1163) ∧
    -Real.log (640 / 1163) ≤ (597289977 / 1000000000) := by
  have h := checkLog_sound (w := (523 / 1803)) (n := 12)
    (lo := (74661247 / 125000000)) (hi := (597289977 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1163 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1163 / 640) = 1/(640 / 1163) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (74661247 / 125000000) (597289977 / 1000000000) (Real.log (1163 / 640)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1163 / 640) = -Real.log (640 / 1163) := by
    rw [show ((1163 / 640) : ℝ) = ((640 / 1163) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (10620589 / 6250000) ≤ -Real.log (117 / 640) ∧
    -Real.log (117 / 640) ≤ (1699294243 / 1000000000) := by
  have h := checkLog_sound (w := (43 / 277)) (n := 12)
    (lo := (7824997 / 25000000)) (hi := (312999881 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 117) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(160 / 117) = 1/(117 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1699294243 / 1000000000) (-10620589 / 6250000) (Real.log (117 / 640)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (953599 / 1600000) ≤ -Real.log (1280 / 2323) ∧
    -Real.log (1280 / 2323) ≤ (37249961 / 62500000) := by
  have h := checkLog_sound (w := (1043 / 3603)) (n := 12)
    (lo := (953599 / 1600000)) (hi := (37249961 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2323 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2323 / 1280) = 1/(1280 / 2323) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (953599 / 1600000) (37249961 / 62500000) (Real.log (2323 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2323 / 1280) = -Real.log (1280 / 2323) := by
    rw [show ((2323 / 1280) : ℝ) = ((1280 / 2323) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (843277607 / 500000000) ≤ -Real.log (237 / 1280) ∧
    -Real.log (237 / 1280) ≤ (1686555217 / 1000000000) := by
  have h := checkLog_sound (w := (83 / 557)) (n := 12)
    (lo := (150130427 / 500000000)) (hi := (60052171 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 237) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(320 / 237) = 1/(237 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1686555217 / 1000000000) (-843277607 / 500000000) (Real.log (237 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (234820219 / 500000000) ≤ -Real.log (1000000 / 1599419) ∧
    -Real.log (1000000 / 1599419) ≤ (469640439 / 1000000000) := by
  have h := checkLog_sound (w := (599419 / 2599419)) (n := 12)
    (lo := (234820219 / 500000000)) (hi := (469640439 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1599419 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1599419 / 1000000) = 1/(1000000 / 1599419) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (234820219 / 500000000) (469640439 / 1000000000) (Real.log (1599419 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1599419 / 1000000) = -Real.log (1000000 / 1599419) := by
    rw [show ((1599419 / 1000000) : ℝ) = ((1000000 / 1599419) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (182967857 / 200000000) ≤ -Real.log (400581 / 1000000) ∧
    -Real.log (400581 / 1000000) ≤ (914839287 / 1000000000) := by
  have h := checkLog_sound (w := (99419 / 900581)) (n := 12)
    (lo := (44338421 / 200000000)) (hi := (110846053 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 400581) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 400581) = 1/(400581 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-914839287 / 1000000000) (-182967857 / 200000000) (Real.log (400581 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (3678507 / 7812500) ≤ -Real.log (1000000 / 1601353) ∧
    -Real.log (1000000 / 1601353) ≤ (470848897 / 1000000000) := by
  have h := checkLog_sound (w := (601353 / 2601353)) (n := 12)
    (lo := (3678507 / 7812500)) (hi := (470848897 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1601353 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1601353 / 1000000) = 1/(1000000 / 1601353) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (3678507 / 7812500) (470848897 / 1000000000) (Real.log (1601353 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1601353 / 1000000) = -Real.log (1000000 / 1601353) := by
    rw [show ((1601353 / 1000000) : ℝ) = ((1000000 / 1601353) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (229919741 / 250000000) ≤ -Real.log (398647 / 1000000) ∧
    -Real.log (398647 / 1000000) ≤ (459839483 / 500000000) := by
  have h := checkLog_sound (w := (101353 / 898647)) (n := 12)
    (lo := (28316473 / 125000000)) (hi := (45306357 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 398647) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 398647) = 1/(398647 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-459839483 / 500000000) (-229919741 / 250000000) (Real.log (398647 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (385456259 / 1000000000) ≤ -Real.log (200000 / 294057) ∧
    -Real.log (200000 / 294057) ≤ (19272813 / 50000000) := by
  have h := checkLog_sound (w := (94057 / 494057)) (n := 12)
    (lo := (385456259 / 1000000000)) (hi := (19272813 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((294057 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(294057 / 200000) = 1/(200000 / 294057) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (385456259 / 1000000000) (19272813 / 50000000) (Real.log (294057 / 200000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (294057 / 200000) = -Real.log (200000 / 294057) := by
    rw [show ((294057 / 200000) : ℝ) = ((200000 / 294057) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (79427019 / 125000000) ≤ -Real.log (105943 / 200000) ∧
    -Real.log (105943 / 200000) ≤ (635416153 / 1000000000) := by
  have h := checkLog_sound (w := (94057 / 305943)) (n := 12)
    (lo := (79427019 / 125000000)) (hi := (635416153 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 105943) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 105943) = 1/(105943 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-635416153 / 1000000000) (-79427019 / 125000000) (Real.log (105943 / 200000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (38671169 / 100000000) ≤ -Real.log (250000 / 368033) ∧
    -Real.log (250000 / 368033) ≤ (386711691 / 1000000000) := by
  have h := checkLog_sound (w := (118033 / 618033)) (n := 12)
    (lo := (38671169 / 100000000)) (hi := (386711691 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((368033 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(368033 / 250000) = 1/(250000 / 368033) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (38671169 / 100000000) (386711691 / 1000000000) (Real.log (368033 / 250000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (368033 / 250000) = -Real.log (250000 / 368033) := by
    rw [show ((368033 / 250000) : ℝ) = ((250000 / 368033) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (319454513 / 500000000) ≤ -Real.log (131967 / 250000) ∧
    -Real.log (131967 / 250000) ≤ (638909027 / 1000000000) := by
  have h := checkLog_sound (w := (118033 / 381967)) (n := 12)
    (lo := (319454513 / 500000000)) (hi := (638909027 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 131967) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 131967) = 1/(131967 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-638909027 / 1000000000) (-319454513 / 500000000) (Real.log (131967 / 250000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1384479723 / 1000000000) ≤ -Real.log (25000000000 / 99818700837) ∧
    -Real.log (25000000000 / 99818700837) ≤ (55379189 / 40000000) := by
  have h := checkLog_sound (w := (49818700837 / 149818700837)) (n := 12)
    (lo := (691332543 / 1000000000)) (hi := (10802071 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((99818700837 / 50000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(99818700837 / 50000000000) = 1/(25000000000 / 99818700837) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1384479723 / 1000000000) (55379189 / 40000000) (Real.log (99818700837 / 25000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (99818700837 / 25000000000) = -Real.log (25000000000 / 99818700837) := by
    rw [show ((99818700837 / 25000000000) : ℝ) = ((25000000000 / 99818700837) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1390527861 / 1000000000) ≤ -Real.log (100000000000 / 401696990069) ∧
    -Real.log (100000000000 / 401696990069) ≤ (173815983 / 125000000) := by
  have h := checkLog_sound (w := (1696990069 / 801696990069)) (n := 12)
    (lo := (4233501 / 1000000000)) (hi := (2116751 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((401696990069 / 400000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(401696990069 / 400000000000) = 1/(100000000000 / 401696990069) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1390527861 / 1000000000) (173815983 / 125000000) (Real.log (401696990069 / 100000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (401696990069 / 100000000000) = -Real.log (100000000000 / 401696990069) := by
    rw [show ((401696990069 / 100000000000) : ℝ) = ((100000000000 / 401696990069) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1020872411 / 1000000000) ≤ -Real.log (500000000000 / 1387807594649) ∧
    -Real.log (500000000000 / 1387807594649) ≤ (1020872413 / 1000000000) := by
  have h := checkLog_sound (w := (387807594649 / 2387807594649)) (n := 12)
    (lo := (327725231 / 1000000000)) (hi := (20482827 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1387807594649 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1387807594649 / 1000000000000) = 1/(500000000000 / 1387807594649) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (1020872411 / 1000000000) (1020872413 / 1000000000) (Real.log (1387807594649 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (1387807594649 / 500000000000) = -Real.log (500000000000 / 1387807594649) := by
    rw [show ((1387807594649 / 500000000000) : ℝ) = ((500000000000 / 1387807594649) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (256405179 / 250000000) ≤ -Real.log (500000000000 / 1394412997189) ∧
    -Real.log (500000000000 / 1394412997189) ≤ (512810359 / 500000000) := by
  have h := checkLog_sound (w := (394412997189 / 2394412997189)) (n := 12)
    (lo := (5194899 / 15625000)) (hi := (332473537 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1394412997189 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1394412997189 / 1000000000000) = 1/(500000000000 / 1394412997189) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (256405179 / 250000000) (512810359 / 500000000) (Real.log (1394412997189 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1394412997189 / 500000000000) = -Real.log (500000000000 / 1394412997189) := by
    rw [show ((1394412997189 / 500000000000) : ℝ) = ((500000000000 / 1394412997189) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0089
