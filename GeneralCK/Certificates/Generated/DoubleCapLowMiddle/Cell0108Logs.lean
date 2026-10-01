import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0108
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

theorem reflection_log_1_neg : (167472637 / 250000000) ≤ -Real.log (25600 / 50023) ∧
    -Real.log (25600 / 50023) ≤ (669890549 / 1000000000) := by
  have h := checkLog_sound (w := (24423 / 75623)) (n := 12)
    (lo := (167472637 / 250000000)) (hi := (669890549 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50023 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50023 / 25600) = 1/(25600 / 50023) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (167472637 / 250000000) (669890549 / 1000000000) (Real.log (50023 / 25600)) := by
  have h := reflection_log_1_neg
  have he : Real.log (50023 / 25600) = -Real.log (25600 / 50023) := by
    rw [show ((50023 / 25600) : ℝ) = ((25600 / 50023) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (19247647 / 6250000) ≤ -Real.log (1177 / 25600) ∧
    -Real.log (1177 / 25600) ≤ (123184941 / 40000000) := by
  have h := checkLog_sound (w := (423 / 2777)) (n := 12)
    (lo := (767587 / 2500000)) (hi := (307034801 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1177) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1600 / 1177) = 1/(1177 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-123184941 / 40000000) (-19247647 / 6250000) (Real.log (1177 / 25600)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (669700617 / 1000000000) ≤ -Real.log (51200 / 100027) ∧
    -Real.log (51200 / 100027) ≤ (334850309 / 500000000) := by
  have h := checkLog_sound (w := (48827 / 151227)) (n := 12)
    (lo := (669700617 / 1000000000)) (hi := (334850309 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100027 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100027 / 51200) = 1/(51200 / 100027) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (669700617 / 1000000000) (334850309 / 500000000) (Real.log (100027 / 51200)) := by
  have h := reflection_log_3_neg
  have he : Real.log (100027 / 51200) = -Real.log (51200 / 100027) := by
    rw [show ((100027 / 51200) : ℝ) = ((51200 / 100027) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (383948069 / 125000000) ≤ -Real.log (2373 / 51200) ∧
    -Real.log (2373 / 51200) ≤ (3071584557 / 1000000000) := by
  have h := checkLog_sound (w := (827 / 5573)) (n := 12)
    (lo := (37374479 / 125000000)) (hi := (298995833 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2373) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3200 / 2373) = 1/(2373 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-3071584557 / 1000000000) (-383948069 / 125000000) (Real.log (2373 / 51200)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (32304007 / 50000000) ≤ -Real.log (12800 / 24423) ∧
    -Real.log (12800 / 24423) ≤ (646080141 / 1000000000) := by
  have h := checkLog_sound (w := (11623 / 37223)) (n := 12)
    (lo := (32304007 / 50000000)) (hi := (646080141 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24423 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24423 / 12800) = 1/(12800 / 24423) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (32304007 / 50000000) (646080141 / 1000000000) (Real.log (24423 / 12800)) := by
  have h := reflection_log_5_neg
  have he : Real.log (24423 / 12800) = -Real.log (12800 / 24423) := by
    rw [show ((24423 / 12800) : ℝ) = ((12800 / 24423) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (119323817 / 50000000) ≤ -Real.log (1177 / 12800) ∧
    -Real.log (1177 / 12800) ≤ (298309543 / 125000000) := by
  have h := checkLog_sound (w := (423 / 2777)) (n := 12)
    (lo := (767587 / 2500000)) (hi := (307034801 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1177) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1600 / 1177) = 1/(1177 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-298309543 / 125000000) (-119323817 / 50000000) (Real.log (1177 / 12800)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (645691087 / 1000000000) ≤ -Real.log (25600 / 48827) ∧
    -Real.log (25600 / 48827) ≤ (40355693 / 62500000) := by
  have h := checkLog_sound (w := (23227 / 74427)) (n := 12)
    (lo := (645691087 / 1000000000)) (hi := (40355693 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((48827 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(48827 / 25600) = 1/(25600 / 48827) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (645691087 / 1000000000) (40355693 / 62500000) (Real.log (48827 / 25600)) := by
  have h := reflection_log_7_neg
  have he : Real.log (48827 / 25600) = -Real.log (25600 / 48827) := by
    rw [show ((48827 / 25600) : ℝ) = ((25600 / 48827) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (594609343 / 250000000) ≤ -Real.log (2373 / 25600) ∧
    -Real.log (2373 / 25600) ≤ (9290771 / 3906250) := by
  have h := checkLog_sound (w := (827 / 5573)) (n := 12)
    (lo := (37374479 / 125000000)) (hi := (298995833 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2373) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(3200 / 2373) = 1/(2373 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-9290771 / 3906250) (-594609343 / 250000000) (Real.log (2373 / 25600)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (674044887 / 1000000000) ≤ -Real.log (500000 / 981079) ∧
    -Real.log (500000 / 981079) ≤ (84255611 / 125000000) := by
  have h := checkLog_sound (w := (481079 / 1481079)) (n := 12)
    (lo := (674044887 / 1000000000)) (hi := (84255611 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((981079 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(981079 / 500000) = 1/(500000 / 981079) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (674044887 / 1000000000) (84255611 / 125000000) (Real.log (981079 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (981079 / 500000) = -Real.log (500000 / 981079) := by
    rw [show ((981079 / 500000) : ℝ) = ((500000 / 981079) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (3274335679 / 1000000000) ≤ -Real.log (18921 / 500000) ∧
    -Real.log (18921 / 500000) ≤ (818583921 / 250000000) := by
  have h := checkLog_sound (w := (12329 / 50171)) (n := 12)
    (lo := (501746959 / 1000000000)) (hi := (6271837 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 18921) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(31250 / 18921) = 1/(18921 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-818583921 / 250000000) (-3274335679 / 1000000000) (Real.log (18921 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (5393521 / 8000000) ≤ -Real.log (1000000 / 1962443) ∧
    -Real.log (1000000 / 1962443) ≤ (337095063 / 500000000) := by
  have h := checkLog_sound (w := (962443 / 2962443)) (n := 12)
    (lo := (5393521 / 8000000)) (hi := (337095063 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1962443 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1962443 / 1000000) = 1/(1000000 / 1962443) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (5393521 / 8000000) (337095063 / 500000000) (Real.log (1962443 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1962443 / 1000000) = -Real.log (1000000 / 1962443) := by
    rw [show ((1962443 / 1000000) : ℝ) = ((1000000 / 1962443) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (3281895497 / 1000000000) ≤ -Real.log (37557 / 1000000) ∧
    -Real.log (37557 / 1000000) ≤ (1640947751 / 500000000) := by
  have h := checkLog_sound (w := (24943 / 100057)) (n := 12)
    (lo := (509306777 / 1000000000)) (hi := (254653389 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 37557) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 37557) = 1/(37557 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1640947751 / 500000000) (-3281895497 / 1000000000) (Real.log (37557 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (673838971 / 1000000000) ≤ -Real.log (500000 / 980877) ∧
    -Real.log (500000 / 980877) ≤ (168459743 / 250000000) := by
  have h := checkLog_sound (w := (480877 / 1480877)) (n := 12)
    (lo := (673838971 / 1000000000)) (hi := (168459743 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((980877 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(980877 / 500000) = 1/(500000 / 980877) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (673838971 / 1000000000) (168459743 / 250000000) (Real.log (980877 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (980877 / 500000) = -Real.log (500000 / 980877) := by
    rw [show ((980877 / 500000) : ℝ) = ((500000 / 980877) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (3263716297 / 1000000000) ≤ -Real.log (19123 / 500000) ∧
    -Real.log (19123 / 500000) ≤ (1631858151 / 500000000) := by
  have h := checkLog_sound (w := (12127 / 50373)) (n := 12)
    (lo := (491127577 / 1000000000)) (hi := (245563789 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 19123) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(31250 / 19123) = 1/(19123 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-1631858151 / 500000000) (-3263716297 / 1000000000) (Real.log (19123 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (336993903 / 500000000) ≤ -Real.log (500000 / 981023) ∧
    -Real.log (500000 / 981023) ≤ (673987807 / 1000000000) := by
  have h := checkLog_sound (w := (481023 / 1481023)) (n := 12)
    (lo := (336993903 / 500000000)) (hi := (673987807 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((981023 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(981023 / 500000) = 1/(500000 / 981023) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (336993903 / 500000000) (673987807 / 1000000000) (Real.log (981023 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (981023 / 500000) = -Real.log (500000 / 981023) := by
    rw [show ((981023 / 500000) : ℝ) = ((500000 / 981023) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (408922547 / 125000000) ≤ -Real.log (18977 / 500000) ∧
    -Real.log (18977 / 500000) ≤ (3271380381 / 1000000000) := by
  have h := checkLog_sound (w := (12273 / 50227)) (n := 12)
    (lo := (62348957 / 125000000)) (hi := (498791657 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 18977) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(31250 / 18977) = 1/(18977 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-3271380381 / 1000000000) (-408922547 / 125000000) (Real.log (18977 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (3948380567 / 1000000000) ≤ -Real.log (62500000000 / 3240708075683) ∧
    -Real.log (62500000000 / 3240708075683) ≤ (3948380573 / 1000000000) := by
  have h := checkLog_sound (w := (1240708075683 / 5240708075683)) (n := 12)
    (lo := (482644667 / 1000000000)) (hi := (120661167 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3240708075683 / 2000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3240708075683 / 2000000000000) = 1/(62500000000 / 3240708075683) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (3948380567 / 1000000000) (3948380573 / 1000000000) (Real.log (3240708075683 / 62500000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (3240708075683 / 62500000000) = -Real.log (62500000000 / 3240708075683) := by
    rw [show ((3240708075683 / 62500000000) : ℝ) = ((62500000000 / 3240708075683) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1978042811 / 500000000) ≤ -Real.log (250000000000 / 13063097425247) ∧
    -Real.log (250000000000 / 13063097425247) ≤ (989021407 / 250000000) := by
  have h := checkLog_sound (w := (5063097425247 / 21063097425247)) (n := 12)
    (lo := (245174861 / 500000000)) (hi := (490349723 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((13063097425247 / 8000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(13063097425247 / 8000000000000) = 1/(250000000000 / 13063097425247) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1978042811 / 500000000) (989021407 / 250000000) (Real.log (13063097425247 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (13063097425247 / 250000000000) = -Real.log (250000000000 / 13063097425247) := by
    rw [show ((13063097425247 / 250000000000) : ℝ) = ((250000000000 / 13063097425247) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (3937555267 / 1000000000) ≤ -Real.log (50000000000 / 2564652512681) ∧
    -Real.log (50000000000 / 2564652512681) ≤ (3937555273 / 1000000000) := by
  have h := checkLog_sound (w := (964652512681 / 4164652512681)) (n := 12)
    (lo := (471819367 / 1000000000)) (hi := (58977421 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2564652512681 / 1600000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(2564652512681 / 1600000000000) = 1/(50000000000 / 2564652512681) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (3937555267 / 1000000000) (3937555273 / 1000000000) (Real.log (2564652512681 / 50000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (2564652512681 / 50000000000) = -Real.log (50000000000 / 2564652512681) := by
    rw [show ((2564652512681 / 50000000000) : ℝ) = ((50000000000 / 2564652512681) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (1972684091 / 500000000) ≤ -Real.log (250000000000 / 12923842019287) ∧
    -Real.log (250000000000 / 12923842019287) ≤ (986342047 / 250000000) := by
  have h := checkLog_sound (w := (4923842019287 / 20923842019287)) (n := 12)
    (lo := (239816141 / 500000000)) (hi := (479632283 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12923842019287 / 8000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(12923842019287 / 8000000000000) = 1/(250000000000 / 12923842019287) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (1972684091 / 500000000) (986342047 / 250000000) (Real.log (12923842019287 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (12923842019287 / 250000000000) = -Real.log (250000000000 / 12923842019287) := by
    rw [show ((12923842019287 / 250000000000) : ℝ) = ((250000000000 / 12923842019287) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0108
