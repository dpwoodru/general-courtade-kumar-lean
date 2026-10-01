import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0099
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

theorem reflection_log_1_neg : (167118799 / 500000000) ≤ -Real.log (320 / 447) ∧
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


theorem reflection_log_1 : Bounds (167118799 / 500000000) (334237599 / 1000000000) (Real.log (447 / 320)) := by
  have h := reflection_log_1_neg
  have he : Real.log (447 / 320) = -Real.log (320 / 447) := by
    rw [show ((447 / 320) : ℝ) = ((320 / 447) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (252815403 / 500000000) ≤ -Real.log (193 / 320) ∧
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


theorem reflection_log_2 : Bounds (-505630807 / 1000000000) (-252815403 / 500000000) (Real.log (193 / 320)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (4167479 / 12500000) ≤ -Real.log (2560 / 3573) ∧
    -Real.log (2560 / 3573) ≤ (333398321 / 1000000000) := by
  have h := checkLog_sound (w := (1013 / 6133)) (n := 12)
    (lo := (4167479 / 12500000)) (hi := (333398321 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3573 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3573 / 2560) = 1/(2560 / 3573) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (4167479 / 12500000) (333398321 / 1000000000) (Real.log (3573 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3573 / 2560) = -Real.log (2560 / 3573) := by
    rw [show ((3573 / 2560) : ℝ) = ((2560 / 3573) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (251844843 / 500000000) ≤ -Real.log (1547 / 2560) ∧
    -Real.log (1547 / 2560) ≤ (503689687 / 1000000000) := by
  have h := checkLog_sound (w := (1013 / 4107)) (n := 12)
    (lo := (251844843 / 500000000)) (hi := (503689687 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1547) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1547) = 1/(1547 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-503689687 / 1000000000) (-251844843 / 500000000) (Real.log (1547 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (1460771 / 2500000) ≤ -Real.log (160 / 287) ∧
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


theorem reflection_log_5 : Bounds (1460771 / 2500000) (584308401 / 1000000000) (Real.log (287 / 160)) := by
  have h := reflection_log_5_neg
  have he : Real.log (287 / 160) = -Real.log (160 / 287) := by
    rw [show ((287 / 160) : ℝ) = ((160 / 287) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (394666563 / 250000000) ≤ -Real.log (33 / 160) ∧
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


theorem reflection_log_6 : Bounds (-315733251 / 200000000) (-394666563 / 250000000) (Real.log (33 / 160)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (23320037 / 40000000) ≤ -Real.log (1280 / 2293) ∧
    -Real.log (1280 / 2293) ≤ (291500463 / 500000000) := by
  have h := checkLog_sound (w := (1013 / 3573)) (n := 12)
    (lo := (23320037 / 40000000)) (hi := (291500463 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2293 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2293 / 1280) = 1/(1280 / 2293) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (23320037 / 40000000) (291500463 / 500000000) (Real.log (2293 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2293 / 1280) = -Real.log (1280 / 2293) := by
    rw [show ((2293 / 1280) : ℝ) = ((1280 / 2293) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (1567366697 / 1000000000) ≤ -Real.log (267 / 1280) ∧
    -Real.log (267 / 1280) ≤ (15673667 / 10000000) := by
  have h := checkLog_sound (w := (53 / 587)) (n := 12)
    (lo := (181072337 / 1000000000)) (hi := (90536169 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 267) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(320 / 267) = 1/(267 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-15673667 / 10000000) (-1567366697 / 1000000000) (Real.log (267 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (457588757 / 1000000000) ≤ -Real.log (1000000 / 1580259) ∧
    -Real.log (1000000 / 1580259) ≤ (228794379 / 500000000) := by
  have h := checkLog_sound (w := (580259 / 2580259)) (n := 12)
    (lo := (457588757 / 1000000000)) (hi := (228794379 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1580259 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1580259 / 1000000) = 1/(1000000 / 1580259) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (457588757 / 1000000000) (228794379 / 500000000) (Real.log (1580259 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1580259 / 1000000) = -Real.log (1000000 / 1580259) := by
    rw [show ((1580259 / 1000000) : ℝ) = ((1000000 / 1580259) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (54257339 / 62500000) ≤ -Real.log (419741 / 1000000) ∧
    -Real.log (419741 / 1000000) ≤ (434058713 / 500000000) := by
  have h := checkLog_sound (w := (80259 / 919741)) (n := 12)
    (lo := (43742561 / 250000000)) (hi := (34994049 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 419741) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 419741) = 1/(419741 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-434058713 / 500000000) (-54257339 / 62500000) (Real.log (419741 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (229396133 / 500000000) ≤ -Real.log (500000 / 791081) ∧
    -Real.log (500000 / 791081) ≤ (458792267 / 1000000000) := by
  have h := checkLog_sound (w := (291081 / 1291081)) (n := 12)
    (lo := (229396133 / 500000000)) (hi := (458792267 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((791081 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(791081 / 500000) = 1/(500000 / 791081) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (229396133 / 500000000) (458792267 / 1000000000) (Real.log (791081 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (791081 / 500000) = -Real.log (500000 / 791081) := by
    rw [show ((791081 / 500000) : ℝ) = ((500000 / 791081) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (21816537 / 25000000) ≤ -Real.log (208919 / 500000) ∧
    -Real.log (208919 / 500000) ≤ (436330741 / 500000000) := by
  have h := checkLog_sound (w := (41081 / 458919)) (n := 12)
    (lo := (1795143 / 10000000)) (hi := (179514301 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 208919) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 208919) = 1/(208919 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-436330741 / 500000000) (-21816537 / 25000000) (Real.log (208919 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (373063121 / 1000000000) ≤ -Real.log (62500 / 90761) ∧
    -Real.log (62500 / 90761) ≤ (186531561 / 500000000) := by
  have h := checkLog_sound (w := (28261 / 153261)) (n := 12)
    (lo := (373063121 / 1000000000)) (hi := (186531561 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((90761 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(90761 / 62500) = 1/(62500 / 90761) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (373063121 / 1000000000) (186531561 / 500000000) (Real.log (90761 / 62500)) := by
  have h := reflection_log_13_neg
  have he : Real.log (90761 / 62500) = -Real.log (62500 / 90761) := by
    rw [show ((90761 / 62500) : ℝ) = ((62500 / 90761) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (601801211 / 1000000000) ≤ -Real.log (34239 / 62500) ∧
    -Real.log (34239 / 62500) ≤ (150450303 / 250000000) := by
  have h := checkLog_sound (w := (28261 / 96739)) (n := 12)
    (lo := (601801211 / 1000000000)) (hi := (150450303 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 34239) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 34239) = 1/(34239 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-150450303 / 250000000) (-601801211 / 1000000000) (Real.log (34239 / 62500)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (93572717 / 250000000) ≤ -Real.log (25000 / 36349) ∧
    -Real.log (25000 / 36349) ≤ (374290869 / 1000000000) := by
  have h := checkLog_sound (w := (11349 / 61349)) (n := 12)
    (lo := (93572717 / 250000000)) (hi := (374290869 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((36349 / 25000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(36349 / 25000) = 1/(25000 / 36349) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (93572717 / 250000000) (374290869 / 1000000000) (Real.log (36349 / 25000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (36349 / 25000) = -Real.log (25000 / 36349) := by
    rw [show ((36349 / 25000) : ℝ) = ((25000 / 36349) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (121012609 / 200000000) ≤ -Real.log (13651 / 25000) ∧
    -Real.log (13651 / 25000) ≤ (302531523 / 500000000) := by
  have h := checkLog_sound (w := (11349 / 38651)) (n := 12)
    (lo := (121012609 / 200000000)) (hi := (302531523 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 13651) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25000 / 13651) = 1/(13651 / 25000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-302531523 / 500000000) (-121012609 / 200000000) (Real.log (13651 / 25000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1325706181 / 1000000000) ≤ -Real.log (250000000000 / 941210770451) ∧
    -Real.log (250000000000 / 941210770451) ≤ (1325706183 / 1000000000) := by
  have h := checkLog_sound (w := (441210770451 / 1441210770451)) (n := 12)
    (lo := (632559001 / 1000000000)) (hi := (316279501 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((941210770451 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(941210770451 / 500000000000) = 1/(250000000000 / 941210770451) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1325706181 / 1000000000) (1325706183 / 1000000000) (Real.log (941210770451 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (941210770451 / 250000000000) = -Real.log (250000000000 / 941210770451) := by
    rw [show ((941210770451 / 250000000000) : ℝ) = ((250000000000 / 941210770451) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (665726873 / 500000000) ≤ -Real.log (500000000000 / 1893272033659) ∧
    -Real.log (500000000000 / 1893272033659) ≤ (332863437 / 250000000) := by
  have h := checkLog_sound (w := (893272033659 / 2893272033659)) (n := 12)
    (lo := (319153283 / 500000000)) (hi := (638306567 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1893272033659 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1893272033659 / 1000000000000) = 1/(500000000000 / 1893272033659) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (665726873 / 500000000) (332863437 / 250000000) (Real.log (1893272033659 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1893272033659 / 500000000000) = -Real.log (500000000000 / 1893272033659) := by
    rw [show ((1893272033659 / 500000000000) : ℝ) = ((500000000000 / 1893272033659) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (243716083 / 250000000) ≤ -Real.log (100000000000 / 265080755863) ∧
    -Real.log (100000000000 / 265080755863) ≤ (487432167 / 500000000) := by
  have h := checkLog_sound (w := (65080755863 / 465080755863)) (n := 12)
    (lo := (8803661 / 31250000)) (hi := (281717153 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((265080755863 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(265080755863 / 200000000000) = 1/(100000000000 / 265080755863) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (243716083 / 250000000) (487432167 / 500000000) (Real.log (265080755863 / 100000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (265080755863 / 100000000000) = -Real.log (100000000000 / 265080755863) := by
    rw [show ((265080755863 / 100000000000) : ℝ) = ((100000000000 / 265080755863) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (979353913 / 1000000000) ≤ -Real.log (500000000000 / 1331367665373) ∧
    -Real.log (500000000000 / 1331367665373) ≤ (195870783 / 200000000) := by
  have h := checkLog_sound (w := (331367665373 / 2331367665373)) (n := 12)
    (lo := (286206733 / 1000000000)) (hi := (143103367 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1331367665373 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1331367665373 / 1000000000000) = 1/(500000000000 / 1331367665373) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (979353913 / 1000000000) (195870783 / 200000000) (Real.log (1331367665373 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1331367665373 / 500000000000) = -Real.log (500000000000 / 1331367665373) := by
    rw [show ((1331367665373 / 500000000000) : ℝ) = ((500000000000 / 1331367665373) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0099
