import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0230
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

theorem reflection_log_1_neg : (252095373 / 1000000000) ≤ -Real.log (1280 / 1647) ∧
    -Real.log (1280 / 1647) ≤ (126047687 / 500000000) := by
  have h := checkLog_sound (w := (367 / 2927)) (n := 12)
    (lo := (252095373 / 1000000000)) (hi := (126047687 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1647 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1647 / 1280) = 1/(1280 / 1647) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (252095373 / 1000000000) (126047687 / 500000000) (Real.log (1647 / 1280)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1647 / 1280) = -Real.log (1280 / 1647) := by
    rw [show ((1647 / 1280) : ℝ) = ((1280 / 1647) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (84469869 / 250000000) ≤ -Real.log (913 / 1280) ∧
    -Real.log (913 / 1280) ≤ (337879477 / 1000000000) := by
  have h := checkLog_sound (w := (367 / 2193)) (n := 12)
    (lo := (84469869 / 250000000)) (hi := (337879477 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 913) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 913) = 1/(913 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-337879477 / 1000000000) (-84469869 / 250000000) (Real.log (913 / 1280)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (31454987 / 125000000) ≤ -Real.log (1024 / 1317) ∧
    -Real.log (1024 / 1317) ≤ (251639897 / 1000000000) := by
  have h := checkLog_sound (w := (293 / 2341)) (n := 12)
    (lo := (31454987 / 125000000)) (hi := (251639897 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1317 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1317 / 1024) = 1/(1024 / 1317) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (31454987 / 125000000) (251639897 / 1000000000) (Real.log (1317 / 1024)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1317 / 1024) = -Real.log (1024 / 1317) := by
    rw [show ((1317 / 1024) : ℝ) = ((1024 / 1317) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (67411669 / 200000000) ≤ -Real.log (731 / 1024) ∧
    -Real.log (731 / 1024) ≤ (168529173 / 500000000) := by
  have h := checkLog_sound (w := (293 / 1755)) (n := 12)
    (lo := (67411669 / 200000000)) (hi := (168529173 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 731) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 731) = 1/(731 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-168529173 / 500000000) (-67411669 / 200000000) (Real.log (731 / 1024)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (113315679 / 250000000) ≤ -Real.log (640 / 1007) ∧
    -Real.log (640 / 1007) ≤ (453262717 / 1000000000) := by
  have h := checkLog_sound (w := (367 / 1647)) (n := 12)
    (lo := (113315679 / 250000000)) (hi := (453262717 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1007 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1007 / 640) = 1/(640 / 1007) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (113315679 / 250000000) (453262717 / 1000000000) (Real.log (1007 / 640)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1007 / 640) = -Real.log (640 / 1007) := by
    rw [show ((1007 / 640) : ℝ) = ((640 / 1007) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (42599819 / 50000000) ≤ -Real.log (273 / 640) ∧
    -Real.log (273 / 640) ≤ (425998191 / 500000000) := by
  have h := checkLog_sound (w := (47 / 593)) (n := 12)
    (lo := (397123 / 2500000)) (hi := (158849201 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 273) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(320 / 273) = 1/(273 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-425998191 / 500000000) (-42599819 / 50000000) (Real.log (273 / 640)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (113129413 / 250000000) ≤ -Real.log (512 / 805) ∧
    -Real.log (512 / 805) ≤ (452517653 / 1000000000) := by
  have h := checkLog_sound (w := (293 / 1317)) (n := 12)
    (lo := (113129413 / 250000000)) (hi := (452517653 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((805 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(805 / 512) = 1/(512 / 805) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (113129413 / 250000000) (452517653 / 1000000000) (Real.log (805 / 512)) := by
  have h := reflection_log_7_neg
  have he : Real.log (805 / 512) = -Real.log (512 / 805) := by
    rw [show ((805 / 512) : ℝ) = ((512 / 805) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (424626447 / 500000000) ≤ -Real.log (219 / 512) ∧
    -Real.log (219 / 512) ≤ (26539153 / 31250000) := by
  have h := checkLog_sound (w := (37 / 475)) (n := 12)
    (lo := (78052857 / 500000000)) (hi := (31221143 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((256 / 219) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(256 / 219) = 1/(219 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-26539153 / 31250000) (-424626447 / 500000000) (Real.log (219 / 512)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (10761371 / 31250000) ≤ -Real.log (250000 / 352773) ∧
    -Real.log (250000 / 352773) ≤ (344363873 / 1000000000) := by
  have h := checkLog_sound (w := (102773 / 602773)) (n := 12)
    (lo := (10761371 / 31250000)) (hi := (344363873 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((352773 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(352773 / 250000) = 1/(250000 / 352773) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (10761371 / 31250000) (344363873 / 1000000000) (Real.log (352773 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (352773 / 250000) = -Real.log (250000 / 352773) := by
    rw [show ((352773 / 250000) : ℝ) = ((250000 / 352773) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (66185663 / 125000000) ≤ -Real.log (147227 / 250000) ∧
    -Real.log (147227 / 250000) ≤ (105897061 / 200000000) := by
  have h := checkLog_sound (w := (102773 / 397227)) (n := 12)
    (lo := (66185663 / 125000000)) (hi := (105897061 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 147227) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 147227) = 1/(147227 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-105897061 / 200000000) (-66185663 / 125000000) (Real.log (147227 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (344983059 / 1000000000) ≤ -Real.log (500000 / 705983) ∧
    -Real.log (500000 / 705983) ≤ (17249153 / 50000000) := by
  have h := checkLog_sound (w := (205983 / 1205983)) (n := 12)
    (lo := (344983059 / 1000000000)) (hi := (17249153 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((705983 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(705983 / 500000) = 1/(500000 / 705983) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (344983059 / 1000000000) (17249153 / 50000000) (Real.log (705983 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (705983 / 500000) = -Real.log (500000 / 705983) := by
    rw [show ((705983 / 500000) : ℝ) = ((500000 / 705983) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (530970509 / 1000000000) ≤ -Real.log (294017 / 500000) ∧
    -Real.log (294017 / 500000) ≤ (53097051 / 100000000) := by
  have h := checkLog_sound (w := (205983 / 794017)) (n := 12)
    (lo := (530970509 / 1000000000)) (hi := (53097051 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 294017) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 294017) = 1/(294017 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-53097051 / 100000000) (-530970509 / 1000000000) (Real.log (294017 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (266148633 / 1000000000) ≤ -Real.log (1000000 / 1304929) ∧
    -Real.log (1000000 / 1304929) ≤ (133074317 / 500000000) := by
  have h := checkLog_sound (w := (304929 / 2304929)) (n := 12)
    (lo := (266148633 / 1000000000)) (hi := (133074317 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1304929 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1304929 / 1000000) = 1/(1000000 / 1304929) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (266148633 / 1000000000) (133074317 / 500000000) (Real.log (1304929 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1304929 / 1000000) = -Real.log (1000000 / 1304929) := by
    rw [show ((1304929 / 1000000) : ℝ) = ((1000000 / 1304929) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (2273383 / 6250000) ≤ -Real.log (695071 / 1000000) ∧
    -Real.log (695071 / 1000000) ≤ (363741281 / 1000000000) := by
  have h := checkLog_sound (w := (304929 / 1695071)) (n := 12)
    (lo := (2273383 / 6250000)) (hi := (363741281 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 695071) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 695071) = 1/(695071 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-363741281 / 1000000000) (-2273383 / 6250000) (Real.log (695071 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (266694107 / 1000000000) ≤ -Real.log (1000000 / 1305641) ∧
    -Real.log (1000000 / 1305641) ≤ (66673527 / 250000000) := by
  have h := checkLog_sound (w := (305641 / 2305641)) (n := 12)
    (lo := (266694107 / 1000000000)) (hi := (66673527 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1305641 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1305641 / 1000000) = 1/(1000000 / 1305641) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (266694107 / 1000000000) (66673527 / 250000000) (Real.log (1305641 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1305641 / 1000000) = -Real.log (1000000 / 1305641) := by
    rw [show ((1305641 / 1000000) : ℝ) = ((1000000 / 1305641) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (364766161 / 1000000000) ≤ -Real.log (694359 / 1000000) ∧
    -Real.log (694359 / 1000000) ≤ (182383081 / 500000000) := by
  have h := checkLog_sound (w := (305641 / 1694359)) (n := 12)
    (lo := (364766161 / 1000000000)) (hi := (182383081 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 694359) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 694359) = 1/(694359 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-182383081 / 500000000) (-364766161 / 1000000000) (Real.log (694359 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (109231147 / 125000000) ≤ -Real.log (100000000000 / 239611620151) ∧
    -Real.log (100000000000 / 239611620151) ≤ (436924589 / 500000000) := by
  have h := checkLog_sound (w := (39611620151 / 439611620151)) (n := 12)
    (lo := (45175499 / 250000000)) (hi := (180701997 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((239611620151 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(239611620151 / 200000000000) = 1/(100000000000 / 239611620151) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (109231147 / 125000000) (436924589 / 500000000) (Real.log (239611620151 / 100000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (239611620151 / 100000000000) = -Real.log (100000000000 / 239611620151) := by
    rw [show ((239611620151 / 100000000000) : ℝ) = ((100000000000 / 239611620151) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (27373549 / 31250000) ≤ -Real.log (25000000000 / 60029096957) ∧
    -Real.log (25000000000 / 60029096957) ≤ (87595357 / 100000000) := by
  have h := checkLog_sound (w := (10029096957 / 110029096957)) (n := 12)
    (lo := (45701597 / 250000000)) (hi := (182806389 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((60029096957 / 50000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(60029096957 / 50000000000) = 1/(25000000000 / 60029096957) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (27373549 / 31250000) (87595357 / 100000000) (Real.log (60029096957 / 25000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (60029096957 / 25000000000) = -Real.log (25000000000 / 60029096957) := by
    rw [show ((60029096957 / 25000000000) : ℝ) = ((25000000000 / 60029096957) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (629889913 / 1000000000) ≤ -Real.log (125000000000 / 234675486389) ∧
    -Real.log (125000000000 / 234675486389) ≤ (314944957 / 500000000) := by
  have h := checkLog_sound (w := (109675486389 / 359675486389)) (n := 12)
    (lo := (629889913 / 1000000000)) (hi := (314944957 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((234675486389 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(234675486389 / 125000000000) = 1/(125000000000 / 234675486389) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (629889913 / 1000000000) (314944957 / 500000000) (Real.log (234675486389 / 125000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (234675486389 / 125000000000) = -Real.log (125000000000 / 234675486389) := by
    rw [show ((234675486389 / 125000000000) : ℝ) = ((125000000000 / 234675486389) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (631460269 / 1000000000) ≤ -Real.log (500000000000 / 940177199403) ∧
    -Real.log (500000000000 / 940177199403) ≤ (63146027 / 100000000) := by
  have h := checkLog_sound (w := (440177199403 / 1440177199403)) (n := 12)
    (lo := (631460269 / 1000000000)) (hi := (63146027 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((940177199403 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(940177199403 / 500000000000) = 1/(500000000000 / 940177199403) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (631460269 / 1000000000) (63146027 / 100000000) (Real.log (940177199403 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (940177199403 / 500000000000) = -Real.log (500000000000 / 940177199403) := by
    rw [show ((940177199403 / 500000000000) : ℝ) = ((500000000000 / 940177199403) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0230
