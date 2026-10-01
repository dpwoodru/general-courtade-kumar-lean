import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell254
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed GeneralCK.Reflection

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

theorem reflection_log_1_neg : (168026811 / 500000000) ≤ -Real.log (1024 / 1433) ∧
    -Real.log (1024 / 1433) ≤ (336053623 / 1000000000) := by
  have h := checkLog_sound (w := (409 / 2457)) (n := 12)
    (lo := (168026811 / 500000000)) (hi := (336053623 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1433 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1433 / 1024) = 1/(1024 / 1433) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (168026811 / 500000000) (336053623 / 1000000000) (Real.log (1433 / 1024)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1433 / 1024) = -Real.log (1024 / 1433) := by
    rw [show ((1433 / 1024) : ℝ) = ((1024 / 1433) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (509849537 / 1000000000) ≤ -Real.log (615 / 1024) ∧
    -Real.log (615 / 1024) ≤ (254924769 / 500000000) := by
  have h := checkLog_sound (w := (409 / 1639)) (n := 12)
    (lo := (509849537 / 1000000000)) (hi := (254924769 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 615) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 615) = 1/(615 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-254924769 / 500000000) (-509849537 / 1000000000) (Real.log (615 / 1024)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (20977177 / 62500000) ≤ -Real.log (2560 / 3581) ∧
    -Real.log (2560 / 3581) ≤ (335634833 / 1000000000) := by
  have h := checkLog_sound (w := (1021 / 6141)) (n := 12)
    (lo := (20977177 / 62500000)) (hi := (335634833 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3581 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3581 / 2560) = 1/(2560 / 3581) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (20977177 / 62500000) (335634833 / 1000000000) (Real.log (3581 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3581 / 2560) = -Real.log (2560 / 3581) := by
    rw [show ((3581 / 2560) : ℝ) = ((2560 / 3581) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (508874403 / 1000000000) ≤ -Real.log (1539 / 2560) ∧
    -Real.log (1539 / 2560) ≤ (127218601 / 250000000) := by
  have h := checkLog_sound (w := (1021 / 4099)) (n := 12)
    (lo := (508874403 / 1000000000)) (hi := (127218601 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1539) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1539) = 1/(1539 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-127218601 / 250000000) (-508874403 / 1000000000) (Real.log (1539 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (49998689 / 200000000) ≤ -Real.log (1000000 / 1284017) ∧
    -Real.log (1000000 / 1284017) ≤ (124996723 / 500000000) := by
  have h := checkLog_sound (w := (284017 / 2284017)) (n := 12)
    (lo := (49998689 / 200000000)) (hi := (124996723 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1284017 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1284017 / 1000000) = 1/(1000000 / 1284017) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (49998689 / 200000000) (124996723 / 500000000) (Real.log (1284017 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1284017 / 1000000) = -Real.log (1000000 / 1284017) := by
    rw [show ((1284017 / 1000000) : ℝ) = ((1000000 / 1284017) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (66819771 / 200000000) ≤ -Real.log (715983 / 1000000) ∧
    -Real.log (715983 / 1000000) ≤ (41762357 / 125000000) := by
  have h := checkLog_sound (w := (284017 / 1715983)) (n := 12)
    (lo := (66819771 / 200000000)) (hi := (41762357 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 715983) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 715983) = 1/(715983 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-41762357 / 125000000) (-66819771 / 200000000) (Real.log (715983 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (125162191 / 500000000) ≤ -Real.log (500000 / 642221) ∧
    -Real.log (500000 / 642221) ≤ (250324383 / 1000000000) := by
  have h := checkLog_sound (w := (142221 / 1142221)) (n := 12)
    (lo := (125162191 / 500000000)) (hi := (250324383 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((642221 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(642221 / 500000) = 1/(500000 / 642221) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (125162191 / 500000000) (250324383 / 1000000000) (Real.log (642221 / 500000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (642221 / 500000) = -Real.log (500000 / 642221) := by
    rw [show ((642221 / 500000) : ℝ) = ((500000 / 642221) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (334692621 / 1000000000) ≤ -Real.log (357779 / 500000) ∧
    -Real.log (357779 / 500000) ≤ (167346311 / 500000000) := by
  have h := checkLog_sound (w := (142221 / 857779)) (n := 12)
    (lo := (334692621 / 1000000000)) (hi := (167346311 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 357779) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 357779) = 1/(357779 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-167346311 / 500000000) (-334692621 / 1000000000) (Real.log (357779 / 500000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (23353403 / 125000000) ≤ -Real.log (1000000 / 1205419) ∧
    -Real.log (1000000 / 1205419) ≤ (7473089 / 40000000) := by
  have h := checkLog_sound (w := (205419 / 2205419)) (n := 12)
    (lo := (23353403 / 125000000)) (hi := (7473089 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1205419 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1205419 / 1000000) = 1/(1000000 / 1205419) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (23353403 / 125000000) (7473089 / 40000000) (Real.log (1205419 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1205419 / 1000000) = -Real.log (1000000 / 1205419) := by
    rw [show ((1205419 / 1000000) : ℝ) = ((1000000 / 1205419) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (229940347 / 1000000000) ≤ -Real.log (794581 / 1000000) ∧
    -Real.log (794581 / 1000000) ≤ (57485087 / 250000000) := by
  have h := checkLog_sound (w := (205419 / 1794581)) (n := 12)
    (lo := (229940347 / 1000000000)) (hi := (57485087 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 794581) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 794581) = 1/(794581 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-57485087 / 250000000) (-229940347 / 1000000000) (Real.log (794581 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (37418863 / 200000000) ≤ -Real.log (1000000 / 1205741) ∧
    -Real.log (1000000 / 1205741) ≤ (46773579 / 250000000) := by
  have h := checkLog_sound (w := (205741 / 2205741)) (n := 12)
    (lo := (37418863 / 200000000)) (hi := (46773579 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1205741 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1205741 / 1000000) = 1/(1000000 / 1205741) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (37418863 / 200000000) (46773579 / 250000000) (Real.log (1205741 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1205741 / 1000000) = -Real.log (1000000 / 1205741) := by
    rw [show ((1205741 / 1000000) : ℝ) = ((1000000 / 1205741) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (115172837 / 500000000) ≤ -Real.log (794259 / 1000000) ∧
    -Real.log (794259 / 1000000) ≤ (9213827 / 40000000) := by
  have h := checkLog_sound (w := (205741 / 1794259)) (n := 12)
    (lo := (115172837 / 500000000)) (hi := (9213827 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 794259) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 794259) = 1/(794259 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-9213827 / 40000000) (-115172837 / 500000000) (Real.log (794259 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (168901847 / 200000000) ≤ -Real.log (62500000000 / 145427225471) ∧
    -Real.log (62500000000 / 145427225471) ≤ (844509237 / 1000000000) := by
  have h := checkLog_sound (w := (20427225471 / 270427225471)) (n := 12)
    (lo := (30272411 / 200000000)) (hi := (18920257 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((145427225471 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(145427225471 / 125000000000) = 1/(62500000000 / 145427225471) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (168901847 / 200000000) (844509237 / 1000000000) (Real.log (145427225471 / 62500000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (145427225471 / 62500000000) = -Real.log (62500000000 / 145427225471) := by
    rw [show ((145427225471 / 62500000000) : ℝ) = ((62500000000 / 145427225471) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (845903159 / 1000000000) ≤ -Real.log (500000000000 / 1165040650407) ∧
    -Real.log (500000000000 / 1165040650407) ≤ (845903161 / 1000000000) := by
  have h := checkLog_sound (w := (165040650407 / 2165040650407)) (n := 12)
    (lo := (152755979 / 1000000000)) (hi := (7637799 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1165040650407 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1165040650407 / 1000000000000) = 1/(500000000000 / 1165040650407) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (845903159 / 1000000000) (845903161 / 1000000000) (Real.log (1165040650407 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (1165040650407 / 500000000000) = -Real.log (500000000000 / 1165040650407) := by
    rw [show ((1165040650407 / 500000000000) : ℝ) = ((500000000000 / 1165040650407) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (5840923 / 10000000) ≤ -Real.log (250000000000 / 448340603059) ∧
    -Real.log (250000000000 / 448340603059) ≤ (584092301 / 1000000000) := by
  have h := checkLog_sound (w := (198340603059 / 698340603059)) (n := 12)
    (lo := (5840923 / 10000000)) (hi := (584092301 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((448340603059 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(448340603059 / 250000000000) = 1/(250000000000 / 448340603059) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (5840923 / 10000000) (584092301 / 1000000000) (Real.log (448340603059 / 250000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (448340603059 / 250000000000) = -Real.log (250000000000 / 448340603059) := by
    rw [show ((448340603059 / 250000000000) : ℝ) = ((250000000000 / 448340603059) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (585017003 / 1000000000) ≤ -Real.log (250000000000 / 448755376923) ∧
    -Real.log (250000000000 / 448755376923) ≤ (146254251 / 250000000) := by
  have h := checkLog_sound (w := (198755376923 / 698755376923)) (n := 12)
    (lo := (585017003 / 1000000000)) (hi := (146254251 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((448755376923 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(448755376923 / 250000000000) = 1/(250000000000 / 448755376923) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (585017003 / 1000000000) (146254251 / 250000000) (Real.log (448755376923 / 250000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (448755376923 / 250000000000) = -Real.log (250000000000 / 448755376923) := by
    rw [show ((448755376923 / 250000000000) : ℝ) = ((250000000000 / 448755376923) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (416767571 / 1000000000) ≤ -Real.log (250000000000 / 379262466633) ∧
    -Real.log (250000000000 / 379262466633) ≤ (104191893 / 250000000) := by
  have h := checkLog_sound (w := (129262466633 / 629262466633)) (n := 12)
    (lo := (416767571 / 1000000000)) (hi := (104191893 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((379262466633 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(379262466633 / 250000000000) = 1/(250000000000 / 379262466633) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (416767571 / 1000000000) (104191893 / 250000000) (Real.log (379262466633 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (379262466633 / 250000000000) = -Real.log (250000000000 / 379262466633) := by
    rw [show ((379262466633 / 250000000000) : ℝ) = ((250000000000 / 379262466633) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (41743999 / 100000000) ≤ -Real.log (500000000000 / 759035151003) ∧
    -Real.log (500000000000 / 759035151003) ≤ (417439991 / 1000000000) := by
  have h := checkLog_sound (w := (259035151003 / 1259035151003)) (n := 12)
    (lo := (41743999 / 100000000)) (hi := (417439991 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((759035151003 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(759035151003 / 500000000000) = 1/(500000000000 / 759035151003) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (41743999 / 100000000) (417439991 / 1000000000) (Real.log (759035151003 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (759035151003 / 500000000000) = -Real.log (500000000000 / 759035151003) := by
    rw [show ((759035151003 / 500000000000) : ℝ) = ((500000000000 / 759035151003) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (21625679 / 500000000) ≤ -Real.log (957670640919 / 1000000000000) ∧
    -Real.log (957670640919 / 1000000000000) ≤ (43251359 / 1000000000) := by
  have h := checkLog_sound (w := (42329359081 / 1957670640919)) (n := 12)
    (lo := (21625679 / 500000000)) (hi := (43251359 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 957670640919) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 957670640919) = 1/(957670640919 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-43251359 / 1000000000) (-21625679 / 500000000) (Real.log (957670640919 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (21556561 / 500000000) ≤ -Real.log (957803034439 / 1000000000000) ∧
    -Real.log (957803034439 / 1000000000000) ≤ (43113123 / 1000000000) := by
  have h := checkLog_sound (w := (42196965561 / 1957803034439)) (n := 12)
    (lo := (21556561 / 500000000)) (hi := (43113123 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 957803034439) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 957803034439) = 1/(957803034439 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-43113123 / 1000000000) (-21556561 / 500000000) (Real.log (957803034439 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell254
