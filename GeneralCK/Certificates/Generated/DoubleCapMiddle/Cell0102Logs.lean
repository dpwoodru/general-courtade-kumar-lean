import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0102
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

theorem reflection_log_1_neg : (331717647 / 1000000000) ≤ -Real.log (2560 / 3567) ∧
    -Real.log (2560 / 3567) ≤ (20732353 / 62500000) := by
  have h := checkLog_sound (w := (1007 / 6127)) (n := 12)
    (lo := (331717647 / 1000000000)) (hi := (20732353 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3567 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3567 / 2560) = 1/(2560 / 3567) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (331717647 / 1000000000) (20732353 / 62500000) (Real.log (3567 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3567 / 2560) = -Real.log (2560 / 3567) := by
    rw [show ((3567 / 2560) : ℝ) = ((2560 / 3567) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (249909357 / 500000000) ≤ -Real.log (1553 / 2560) ∧
    -Real.log (1553 / 2560) ≤ (99963743 / 200000000) := by
  have h := checkLog_sound (w := (1007 / 4113)) (n := 12)
    (lo := (249909357 / 500000000)) (hi := (99963743 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1553) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1553) = 1/(1553 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-99963743 / 200000000) (-249909357 / 500000000) (Real.log (1553 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (330876251 / 1000000000) ≤ -Real.log (640 / 891) ∧
    -Real.log (640 / 891) ≤ (82719063 / 250000000) := by
  have h := checkLog_sound (w := (251 / 1531)) (n := 12)
    (lo := (330876251 / 1000000000)) (hi := (82719063 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((891 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(891 / 640) = 1/(640 / 891) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (330876251 / 1000000000) (82719063 / 250000000) (Real.log (891 / 640)) := by
  have h := reflection_log_3_neg
  have he : Real.log (891 / 640) = -Real.log (640 / 891) := by
    rw [show ((891 / 640) : ℝ) = ((640 / 891) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (7779513 / 15625000) ≤ -Real.log (389 / 640) ∧
    -Real.log (389 / 640) ≤ (497888833 / 1000000000) := by
  have h := checkLog_sound (w := (251 / 1029)) (n := 12)
    (lo := (7779513 / 15625000)) (hi := (497888833 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 389) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 389) = 1/(389 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-497888833 / 1000000000) (-7779513 / 15625000) (Real.log (389 / 640)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (580380837 / 1000000000) ≤ -Real.log (1280 / 2287) ∧
    -Real.log (1280 / 2287) ≤ (290190419 / 500000000) := by
  have h := checkLog_sound (w := (1007 / 3567)) (n := 12)
    (lo := (580380837 / 1000000000)) (hi := (290190419 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2287 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2287 / 1280) = 1/(1280 / 2287) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (580380837 / 1000000000) (290190419 / 500000000) (Real.log (2287 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2287 / 1280) = -Real.log (1280 / 2287) := by
    rw [show ((2287 / 1280) : ℝ) = ((1280 / 2287) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (38628589 / 25000000) ≤ -Real.log (273 / 1280) ∧
    -Real.log (273 / 1280) ≤ (1545143563 / 1000000000) := by
  have h := checkLog_sound (w := (47 / 593)) (n := 12)
    (lo := (397123 / 2500000)) (hi := (158849201 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 273) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(320 / 273) = 1/(273 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1545143563 / 1000000000) (-38628589 / 25000000) (Real.log (273 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (579068213 / 1000000000) ≤ -Real.log (320 / 571) ∧
    -Real.log (320 / 571) ≤ (289534107 / 500000000) := by
  have h := checkLog_sound (w := (251 / 891)) (n := 12)
    (lo := (579068213 / 1000000000)) (hi := (289534107 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((571 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(571 / 320) = 1/(320 / 571) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (579068213 / 1000000000) (289534107 / 500000000) (Real.log (571 / 320)) := by
  have h := reflection_log_7_neg
  have he : Real.log (571 / 320) = -Real.log (320 / 571) := by
    rw [show ((571 / 320) : ℝ) = ((320 / 571) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (153421449 / 100000000) ≤ -Real.log (69 / 320) ∧
    -Real.log (69 / 320) ≤ (1534214493 / 1000000000) := by
  have h := checkLog_sound (w := (11 / 149)) (n := 12)
    (lo := (14792013 / 100000000)) (hi := (147920131 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80 / 69) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(80 / 69) = 1/(69 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1534214493 / 1000000000) (-153421449 / 100000000) (Real.log (69 / 320)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (28373849 / 62500000) ≤ -Real.log (1000000 / 1574569) ∧
    -Real.log (1000000 / 1574569) ≤ (90796317 / 200000000) := by
  have h := checkLog_sound (w := (574569 / 2574569)) (n := 12)
    (lo := (28373849 / 62500000)) (hi := (90796317 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1574569 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1574569 / 1000000) = 1/(1000000 / 1574569) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (28373849 / 62500000) (90796317 / 200000000) (Real.log (1574569 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1574569 / 1000000) = -Real.log (1000000 / 1574569) := by
    rw [show ((1574569 / 1000000) : ℝ) = ((1000000 / 1574569) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (170930501 / 200000000) ≤ -Real.log (425431 / 1000000) ∧
    -Real.log (425431 / 1000000) ≤ (854652507 / 1000000000) := by
  have h := checkLog_sound (w := (74569 / 925431)) (n := 12)
    (lo := (6460213 / 40000000)) (hi := (80752663 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 425431) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 425431) = 1/(425431 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-854652507 / 1000000000) (-170930501 / 200000000) (Real.log (425431 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (113796091 / 250000000) ≤ -Real.log (62500 / 98529) ∧
    -Real.log (62500 / 98529) ≤ (91036873 / 200000000) := by
  have h := checkLog_sound (w := (36029 / 161029)) (n := 12)
    (lo := (113796091 / 250000000)) (hi := (91036873 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((98529 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(98529 / 62500) = 1/(62500 / 98529) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (113796091 / 250000000) (91036873 / 200000000) (Real.log (98529 / 62500)) := by
  have h := reflection_log_11_neg
  have he : Real.log (98529 / 62500) = -Real.log (62500 / 98529) := by
    rw [show ((98529 / 62500) : ℝ) = ((62500 / 98529) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (429558381 / 500000000) ≤ -Real.log (26471 / 62500) ∧
    -Real.log (26471 / 62500) ≤ (214779191 / 250000000) := by
  have h := checkLog_sound (w := (4779 / 57721)) (n := 12)
    (lo := (82984791 / 500000000)) (hi := (165969583 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 26471) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(31250 / 26471) = 1/(26471 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-214779191 / 250000000) (-429558381 / 500000000) (Real.log (26471 / 62500)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (92349441 / 250000000) ≤ -Real.log (1000000 / 1446863) ∧
    -Real.log (1000000 / 1446863) ≤ (73879553 / 200000000) := by
  have h := checkLog_sound (w := (446863 / 2446863)) (n := 12)
    (lo := (92349441 / 250000000)) (hi := (73879553 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1446863 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1446863 / 1000000) = 1/(1000000 / 1446863) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (92349441 / 250000000) (73879553 / 200000000) (Real.log (1446863 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1446863 / 1000000) = -Real.log (1000000 / 1446863) := by
    rw [show ((1446863 / 1000000) : ℝ) = ((1000000 / 1446863) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (9252337 / 15625000) ≤ -Real.log (553137 / 1000000) ∧
    -Real.log (553137 / 1000000) ≤ (592149569 / 1000000000) := by
  have h := checkLog_sound (w := (446863 / 1553137)) (n := 12)
    (lo := (9252337 / 15625000)) (hi := (592149569 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 553137) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 553137) = 1/(553137 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-592149569 / 1000000000) (-9252337 / 15625000) (Real.log (553137 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (370617591 / 1000000000) ≤ -Real.log (1000000 / 1448629) ∧
    -Real.log (1000000 / 1448629) ≤ (46327199 / 125000000) := by
  have h := checkLog_sound (w := (448629 / 2448629)) (n := 12)
    (lo := (370617591 / 1000000000)) (hi := (46327199 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1448629 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1448629 / 1000000) = 1/(1000000 / 1448629) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (370617591 / 1000000000) (46327199 / 125000000) (Real.log (1448629 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1448629 / 1000000) = -Real.log (1000000 / 1448629) := by
    rw [show ((1448629 / 1000000) : ℝ) = ((1000000 / 1448629) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (4762779 / 8000000) ≤ -Real.log (551371 / 1000000) ∧
    -Real.log (551371 / 1000000) ≤ (37209211 / 62500000) := by
  have h := checkLog_sound (w := (448629 / 1551371)) (n := 12)
    (lo := (4762779 / 8000000)) (hi := (37209211 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 551371) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 551371) = 1/(551371 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-37209211 / 62500000) (-4762779 / 8000000) (Real.log (551371 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1308634089 / 1000000000) ≤ -Real.log (100000000000 / 370111486939) ∧
    -Real.log (100000000000 / 370111486939) ≤ (1308634091 / 1000000000) := by
  have h := checkLog_sound (w := (170111486939 / 570111486939)) (n := 12)
    (lo := (615486909 / 1000000000)) (hi := (61548691 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((370111486939 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(370111486939 / 200000000000) = 1/(100000000000 / 370111486939) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1308634089 / 1000000000) (1308634091 / 1000000000) (Real.log (370111486939 / 100000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (370111486939 / 100000000000) = -Real.log (100000000000 / 370111486939) := by
    rw [show ((370111486939 / 100000000000) : ℝ) = ((100000000000 / 370111486939) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (657150563 / 500000000) ≤ -Real.log (62500000000 / 232634297911) ∧
    -Real.log (62500000000 / 232634297911) ≤ (164287641 / 125000000) := by
  have h := checkLog_sound (w := (107634297911 / 357634297911)) (n := 12)
    (lo := (310576973 / 500000000)) (hi := (621153947 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((232634297911 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(232634297911 / 125000000000) = 1/(62500000000 / 232634297911) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (657150563 / 500000000) (164287641 / 125000000) (Real.log (232634297911 / 62500000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (232634297911 / 62500000000) = -Real.log (62500000000 / 232634297911) := by
    rw [show ((232634297911 / 62500000000) : ℝ) = ((62500000000 / 232634297911) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (240386833 / 250000000) ≤ -Real.log (20000000000 / 52314815317) ∧
    -Real.log (20000000000 / 52314815317) ≤ (480773667 / 500000000) := by
  have h := checkLog_sound (w := (12314815317 / 92314815317)) (n := 12)
    (lo := (33550019 / 125000000)) (hi := (268400153 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((52314815317 / 40000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(52314815317 / 40000000000) = 1/(20000000000 / 52314815317) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (240386833 / 250000000) (480773667 / 500000000) (Real.log (52314815317 / 20000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (52314815317 / 20000000000) = -Real.log (20000000000 / 52314815317) := by
    rw [show ((52314815317 / 20000000000) : ℝ) = ((20000000000 / 52314815317) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (482982483 / 500000000) ≤ -Real.log (250000000000 / 656830428151) ∧
    -Real.log (250000000000 / 656830428151) ≤ (120745621 / 125000000) := by
  have h := checkLog_sound (w := (156830428151 / 1156830428151)) (n := 12)
    (lo := (136408893 / 500000000)) (hi := (272817787 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((656830428151 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(656830428151 / 500000000000) = 1/(250000000000 / 656830428151) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (482982483 / 500000000) (120745621 / 125000000) (Real.log (656830428151 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (656830428151 / 250000000000) = -Real.log (250000000000 / 656830428151) := by
    rw [show ((656830428151 / 250000000000) : ℝ) = ((250000000000 / 656830428151) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0102
