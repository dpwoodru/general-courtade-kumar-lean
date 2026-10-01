import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0465
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

theorem reflection_log_1_neg : (184516411 / 1000000000) ≤ -Real.log (2048 / 2463) ∧
    -Real.log (2048 / 2463) ≤ (46129103 / 250000000) := by
  have h := checkLog_sound (w := (415 / 4511)) (n := 12)
    (lo := (184516411 / 1000000000)) (hi := (46129103 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2463 / 2048) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2463 / 2048) = 1/(2048 / 2463) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (184516411 / 1000000000) (46129103 / 250000000) (Real.log (2463 / 2048)) := by
  have h := reflection_log_1_neg
  have he : Real.log (2463 / 2048) = -Real.log (2048 / 2463) := by
    rw [show ((2463 / 2048) : ℝ) = ((2048 / 2463) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (226444893 / 1000000000) ≤ -Real.log (1633 / 2048) ∧
    -Real.log (1633 / 2048) ≤ (113222447 / 500000000) := by
  have h := checkLog_sound (w := (415 / 3681)) (n := 12)
    (lo := (226444893 / 1000000000)) (hi := (113222447 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2048 / 1633) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2048 / 1633) = 1/(1633 / 2048) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-113222447 / 500000000) (-226444893 / 1000000000) (Real.log (1633 / 2048)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (23034097 / 125000000) ≤ -Real.log (1280 / 1539) ∧
    -Real.log (1280 / 1539) ≤ (184272777 / 1000000000) := by
  have h := checkLog_sound (w := (259 / 2819)) (n := 12)
    (lo := (23034097 / 125000000)) (hi := (184272777 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1539 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1539 / 1280) = 1/(1280 / 1539) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (23034097 / 125000000) (184272777 / 1000000000) (Real.log (1539 / 1280)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1539 / 1280) = -Real.log (1280 / 1539) := by
    rw [show ((1539 / 1280) : ℝ) = ((1280 / 1539) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (113038769 / 500000000) ≤ -Real.log (1021 / 1280) ∧
    -Real.log (1021 / 1280) ≤ (226077539 / 1000000000) := by
  have h := checkLog_sound (w := (259 / 2301)) (n := 12)
    (lo := (113038769 / 500000000)) (hi := (226077539 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 1021) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 1021) = 1/(1021 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-226077539 / 1000000000) (-113038769 / 500000000) (Real.log (1021 / 1280)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (340231901 / 1000000000) ≤ -Real.log (1024 / 1439) ∧
    -Real.log (1024 / 1439) ≤ (170115951 / 500000000) := by
  have h := checkLog_sound (w := (415 / 2463)) (n := 12)
    (lo := (340231901 / 1000000000)) (hi := (170115951 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1439 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1439 / 1024) = 1/(1024 / 1439) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (340231901 / 1000000000) (170115951 / 500000000) (Real.log (1439 / 1024)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1439 / 1024) = -Real.log (1024 / 1439) := by
    rw [show ((1439 / 1024) : ℝ) = ((1024 / 1439) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (519653537 / 1000000000) ≤ -Real.log (609 / 1024) ∧
    -Real.log (609 / 1024) ≤ (259826769 / 500000000) := by
  have h := checkLog_sound (w := (415 / 1633)) (n := 12)
    (lo := (519653537 / 1000000000)) (hi := (259826769 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 609) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 609) = 1/(609 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-259826769 / 500000000) (-519653537 / 1000000000) (Real.log (609 / 1024)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (169907429 / 500000000) ≤ -Real.log (640 / 899) ∧
    -Real.log (640 / 899) ≤ (339814859 / 1000000000) := by
  have h := checkLog_sound (w := (259 / 1539)) (n := 12)
    (lo := (169907429 / 500000000)) (hi := (339814859 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((899 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(899 / 640) = 1/(640 / 899) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (169907429 / 500000000) (339814859 / 1000000000) (Real.log (899 / 640)) := by
  have h := reflection_log_7_neg
  have he : Real.log (899 / 640) = -Real.log (640 / 899) := by
    rw [show ((899 / 640) : ℝ) = ((640 / 899) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (518668801 / 1000000000) ≤ -Real.log (381 / 640) ∧
    -Real.log (381 / 640) ≤ (259334401 / 500000000) := by
  have h := checkLog_sound (w := (259 / 1021)) (n := 12)
    (lo := (518668801 / 1000000000)) (hi := (259334401 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 381) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 381) = 1/(381 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-259334401 / 500000000) (-518668801 / 1000000000) (Real.log (381 / 640)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (253288589 / 1000000000) ≤ -Real.log (200000 / 257651) ∧
    -Real.log (200000 / 257651) ≤ (25328859 / 100000000) := by
  have h := checkLog_sound (w := (57651 / 457651)) (n := 12)
    (lo := (253288589 / 1000000000)) (hi := (25328859 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((257651 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(257651 / 200000) = 1/(200000 / 257651) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (253288589 / 1000000000) (25328859 / 100000000) (Real.log (257651 / 200000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (257651 / 200000) = -Real.log (200000 / 257651) := by
    rw [show ((257651 / 200000) : ℝ) = ((200000 / 257651) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (340035577 / 1000000000) ≤ -Real.log (142349 / 200000) ∧
    -Real.log (142349 / 200000) ≤ (170017789 / 500000000) := by
  have h := checkLog_sound (w := (57651 / 342349)) (n := 12)
    (lo := (340035577 / 1000000000)) (hi := (170017789 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 142349) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 142349) = 1/(142349 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-170017789 / 500000000) (-340035577 / 1000000000) (Real.log (142349 / 200000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (126809219 / 500000000) ≤ -Real.log (25000 / 32217) ∧
    -Real.log (25000 / 32217) ≤ (253618439 / 1000000000) := by
  have h := checkLog_sound (w := (7217 / 57217)) (n := 12)
    (lo := (126809219 / 500000000)) (hi := (253618439 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((32217 / 25000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(32217 / 25000) = 1/(25000 / 32217) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (126809219 / 500000000) (253618439 / 1000000000) (Real.log (32217 / 25000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (32217 / 25000) = -Real.log (25000 / 32217) := by
    rw [show ((32217 / 25000) : ℝ) = ((25000 / 32217) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (4257911 / 12500000) ≤ -Real.log (17783 / 25000) ∧
    -Real.log (17783 / 25000) ≤ (340632881 / 1000000000) := by
  have h := checkLog_sound (w := (7217 / 42783)) (n := 12)
    (lo := (4257911 / 12500000)) (hi := (340632881 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 17783) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25000 / 17783) = 1/(17783 / 25000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-340632881 / 1000000000) (-4257911 / 12500000) (Real.log (17783 / 25000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (47371251 / 250000000) ≤ -Real.log (1000000 / 1208627) ∧
    -Real.log (1000000 / 1208627) ≤ (37897001 / 200000000) := by
  have h := checkLog_sound (w := (208627 / 2208627)) (n := 12)
    (lo := (47371251 / 250000000)) (hi := (37897001 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1208627 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1208627 / 1000000) = 1/(1000000 / 1208627) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (47371251 / 250000000) (37897001 / 200000000) (Real.log (1208627 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1208627 / 1000000) = -Real.log (1000000 / 1208627) := by
    rw [show ((1208627 / 1000000) : ℝ) = ((1000000 / 1208627) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (233985867 / 1000000000) ≤ -Real.log (791373 / 1000000) ∧
    -Real.log (791373 / 1000000) ≤ (58496467 / 250000000) := by
  have h := checkLog_sound (w := (208627 / 1791373)) (n := 12)
    (lo := (233985867 / 1000000000)) (hi := (58496467 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 791373) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 791373) = 1/(791373 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-58496467 / 250000000) (-233985867 / 1000000000) (Real.log (791373 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (189751387 / 1000000000) ≤ -Real.log (1000000 / 1208949) ∧
    -Real.log (1000000 / 1208949) ≤ (47437847 / 250000000) := by
  have h := checkLog_sound (w := (208949 / 2208949)) (n := 12)
    (lo := (189751387 / 1000000000)) (hi := (47437847 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1208949 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1208949 / 1000000) = 1/(1000000 / 1208949) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (189751387 / 1000000000) (47437847 / 250000000) (Real.log (1208949 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1208949 / 1000000) = -Real.log (1000000 / 1208949) := by
    rw [show ((1208949 / 1000000) : ℝ) = ((1000000 / 1208949) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (234392837 / 1000000000) ≤ -Real.log (791051 / 1000000) ∧
    -Real.log (791051 / 1000000) ≤ (117196419 / 500000000) := by
  have h := checkLog_sound (w := (208949 / 1791051)) (n := 12)
    (lo := (234392837 / 1000000000)) (hi := (117196419 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 791051) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 791051) = 1/(791051 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-117196419 / 500000000) (-234392837 / 1000000000) (Real.log (791051 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (593324167 / 1000000000) ≤ -Real.log (500000000000 / 904997576379) ∧
    -Real.log (500000000000 / 904997576379) ≤ (74165521 / 125000000) := by
  have h := checkLog_sound (w := (404997576379 / 1404997576379)) (n := 12)
    (lo := (593324167 / 1000000000)) (hi := (74165521 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((904997576379 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(904997576379 / 500000000000) = 1/(500000000000 / 904997576379) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (593324167 / 1000000000) (74165521 / 125000000) (Real.log (904997576379 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (904997576379 / 500000000000) = -Real.log (500000000000 / 904997576379) := by
    rw [show ((904997576379 / 500000000000) : ℝ) = ((500000000000 / 904997576379) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (297125659 / 500000000) ≤ -Real.log (500000000000 / 905837035371) ∧
    -Real.log (500000000000 / 905837035371) ≤ (594251319 / 1000000000) := by
  have h := checkLog_sound (w := (405837035371 / 1405837035371)) (n := 12)
    (lo := (297125659 / 500000000)) (hi := (594251319 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((905837035371 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(905837035371 / 500000000000) = 1/(500000000000 / 905837035371) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (297125659 / 500000000) (594251319 / 1000000000) (Real.log (905837035371 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (905837035371 / 500000000000) = -Real.log (500000000000 / 905837035371) := by
    rw [show ((905837035371 / 500000000000) : ℝ) = ((500000000000 / 905837035371) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (423470871 / 1000000000) ≤ -Real.log (500000000000 / 763626633711) ∧
    -Real.log (500000000000 / 763626633711) ≤ (52933859 / 125000000) := by
  have h := checkLog_sound (w := (263626633711 / 1263626633711)) (n := 12)
    (lo := (423470871 / 1000000000)) (hi := (52933859 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((763626633711 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(763626633711 / 500000000000) = 1/(500000000000 / 763626633711) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (423470871 / 1000000000) (52933859 / 125000000) (Real.log (763626633711 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (763626633711 / 500000000000) = -Real.log (500000000000 / 763626633711) := by
    rw [show ((763626633711 / 500000000000) : ℝ) = ((500000000000 / 763626633711) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (16965769 / 40000000) ≤ -Real.log (500000000000 / 764140997231) ∧
    -Real.log (500000000000 / 764140997231) ≤ (212072113 / 500000000) := by
  have h := checkLog_sound (w := (264140997231 / 1264140997231)) (n := 12)
    (lo := (16965769 / 40000000)) (hi := (212072113 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((764140997231 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(764140997231 / 500000000000) = 1/(500000000000 / 764140997231) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (16965769 / 40000000) (212072113 / 500000000) (Real.log (764140997231 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (764140997231 / 500000000000) = -Real.log (500000000000 / 764140997231) := by
    rw [show ((764140997231 / 500000000000) : ℝ) = ((500000000000 / 764140997231) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0465
