import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0419
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

theorem reflection_log_1_neg : (97829969 / 500000000) ≤ -Real.log (10240 / 12453) ∧
    -Real.log (10240 / 12453) ≤ (195659939 / 1000000000) := by
  have h := checkLog_sound (w := (2213 / 22693)) (n := 12)
    (lo := (97829969 / 500000000)) (hi := (195659939 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12453 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12453 / 10240) = 1/(10240 / 12453) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (97829969 / 500000000) (195659939 / 1000000000) (Real.log (12453 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12453 / 10240) = -Real.log (10240 / 12453) := by
    rw [show ((12453 / 10240) : ℝ) = ((10240 / 12453) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (6087269 / 25000000) ≤ -Real.log (8027 / 10240) ∧
    -Real.log (8027 / 10240) ≤ (243490761 / 1000000000) := by
  have h := checkLog_sound (w := (2213 / 18267)) (n := 12)
    (lo := (6087269 / 25000000)) (hi := (243490761 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 8027) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 8027) = 1/(8027 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-243490761 / 1000000000) (-6087269 / 25000000) (Real.log (8027 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (195419003 / 1000000000) ≤ -Real.log (1024 / 1245) ∧
    -Real.log (1024 / 1245) ≤ (48854751 / 250000000) := by
  have h := checkLog_sound (w := (221 / 2269)) (n := 12)
    (lo := (195419003 / 1000000000)) (hi := (48854751 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1245 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1245 / 1024) = 1/(1024 / 1245) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (195419003 / 1000000000) (48854751 / 250000000) (Real.log (1245 / 1024)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1245 / 1024) = -Real.log (1024 / 1245) := by
    rw [show ((1245 / 1024) : ℝ) = ((1024 / 1245) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (243117091 / 1000000000) ≤ -Real.log (803 / 1024) ∧
    -Real.log (803 / 1024) ≤ (60779273 / 250000000) := by
  have h := checkLog_sound (w := (221 / 1827)) (n := 12)
    (lo := (243117091 / 1000000000)) (hi := (60779273 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 803) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 803) = 1/(803 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-60779273 / 250000000) (-243117091 / 1000000000) (Real.log (803 / 1024)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (35923027 / 100000000) ≤ -Real.log (5120 / 7333) ∧
    -Real.log (5120 / 7333) ≤ (359230271 / 1000000000) := by
  have h := checkLog_sound (w := (2213 / 12453)) (n := 12)
    (lo := (35923027 / 100000000)) (hi := (359230271 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7333 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7333 / 5120) = 1/(5120 / 7333) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (35923027 / 100000000) (359230271 / 1000000000) (Real.log (7333 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (7333 / 5120) = -Real.log (5120 / 7333) := by
    rw [show ((7333 / 5120) : ℝ) = ((5120 / 7333) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (566032817 / 1000000000) ≤ -Real.log (2907 / 5120) ∧
    -Real.log (2907 / 5120) ≤ (283016409 / 500000000) := by
  have h := checkLog_sound (w := (2213 / 8027)) (n := 12)
    (lo := (566032817 / 1000000000)) (hi := (283016409 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2907) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2907) = 1/(2907 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-283016409 / 500000000) (-566032817 / 1000000000) (Real.log (2907 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (89705269 / 250000000) ≤ -Real.log (512 / 733) ∧
    -Real.log (512 / 733) ≤ (358821077 / 1000000000) := by
  have h := checkLog_sound (w := (221 / 1245)) (n := 12)
    (lo := (89705269 / 250000000)) (hi := (358821077 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((733 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(733 / 512) = 1/(512 / 733) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (89705269 / 250000000) (358821077 / 1000000000) (Real.log (733 / 512)) := by
  have h := reflection_log_7_neg
  have he : Real.log (733 / 512) = -Real.log (512 / 733) := by
    rw [show ((733 / 512) : ℝ) = ((512 / 733) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (565001357 / 1000000000) ≤ -Real.log (291 / 512) ∧
    -Real.log (291 / 512) ≤ (282500679 / 500000000) := by
  have h := checkLog_sound (w := (221 / 803)) (n := 12)
    (lo := (565001357 / 1000000000)) (hi := (282500679 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 291) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 291) = 1/(291 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-282500679 / 500000000) (-565001357 / 1000000000) (Real.log (291 / 512)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (6708429 / 25000000) ≤ -Real.log (250000 / 326947) ∧
    -Real.log (250000 / 326947) ≤ (268337161 / 1000000000) := by
  have h := checkLog_sound (w := (76947 / 576947)) (n := 12)
    (lo := (6708429 / 25000000)) (hi := (268337161 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((326947 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(326947 / 250000) = 1/(250000 / 326947) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (6708429 / 25000000) (268337161 / 1000000000) (Real.log (326947 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (326947 / 250000) = -Real.log (250000 / 326947) := by
    rw [show ((326947 / 250000) : ℝ) = ((250000 / 326947) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (367863011 / 1000000000) ≤ -Real.log (173053 / 250000) ∧
    -Real.log (173053 / 250000) ≤ (91965753 / 250000000) := by
  have h := checkLog_sound (w := (76947 / 423053)) (n := 12)
    (lo := (367863011 / 1000000000)) (hi := (91965753 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 173053) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 173053) = 1/(173053 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-91965753 / 250000000) (-367863011 / 1000000000) (Real.log (173053 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (67165903 / 250000000) ≤ -Real.log (200000 / 261643) ∧
    -Real.log (200000 / 261643) ≤ (268663613 / 1000000000) := by
  have h := checkLog_sound (w := (61643 / 461643)) (n := 12)
    (lo := (67165903 / 250000000)) (hi := (268663613 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((261643 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(261643 / 200000) = 1/(200000 / 261643) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (67165903 / 250000000) (268663613 / 1000000000) (Real.log (261643 / 200000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (261643 / 200000) = -Real.log (200000 / 261643) := by
    rw [show ((261643 / 200000) : ℝ) = ((200000 / 261643) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (73696013 / 200000000) ≤ -Real.log (138357 / 200000) ∧
    -Real.log (138357 / 200000) ≤ (184240033 / 500000000) := by
  have h := checkLog_sound (w := (61643 / 338357)) (n := 12)
    (lo := (73696013 / 200000000)) (hi := (184240033 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 138357) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 138357) = 1/(138357 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-184240033 / 500000000) (-73696013 / 200000000) (Real.log (138357 / 200000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (201716421 / 1000000000) ≤ -Real.log (1000000 / 1223501) ∧
    -Real.log (1000000 / 1223501) ≤ (100858211 / 500000000) := by
  have h := checkLog_sound (w := (223501 / 2223501)) (n := 12)
    (lo := (201716421 / 1000000000)) (hi := (100858211 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1223501 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1223501 / 1000000) = 1/(1000000 / 1223501) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (201716421 / 1000000000) (100858211 / 500000000) (Real.log (1223501 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1223501 / 1000000) = -Real.log (1000000 / 1223501) := by
    rw [show ((1223501 / 1000000) : ℝ) = ((1000000 / 1223501) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (63239981 / 250000000) ≤ -Real.log (776499 / 1000000) ∧
    -Real.log (776499 / 1000000) ≤ (10118397 / 40000000) := by
  have h := checkLog_sound (w := (223501 / 1776499)) (n := 12)
    (lo := (63239981 / 250000000)) (hi := (10118397 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 776499) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 776499) = 1/(776499 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-10118397 / 40000000) (-63239981 / 250000000) (Real.log (776499 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (201983651 / 1000000000) ≤ -Real.log (250000 / 305957) ∧
    -Real.log (250000 / 305957) ≤ (50495913 / 250000000) := by
  have h := checkLog_sound (w := (55957 / 555957)) (n := 12)
    (lo := (201983651 / 1000000000)) (hi := (50495913 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((305957 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(305957 / 250000) = 1/(250000 / 305957) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (201983651 / 1000000000) (50495913 / 250000000) (Real.log (305957 / 250000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (305957 / 250000) = -Real.log (250000 / 305957) := by
    rw [show ((305957 / 250000) : ℝ) = ((250000 / 305957) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (253381133 / 1000000000) ≤ -Real.log (194043 / 250000) ∧
    -Real.log (194043 / 250000) ≤ (126690567 / 500000000) := by
  have h := checkLog_sound (w := (55957 / 444043)) (n := 12)
    (lo := (253381133 / 1000000000)) (hi := (126690567 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 194043) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 194043) = 1/(194043 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-126690567 / 500000000) (-253381133 / 1000000000) (Real.log (194043 / 250000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (159050043 / 250000000) ≤ -Real.log (100000000000 / 188928825273) ∧
    -Real.log (100000000000 / 188928825273) ≤ (636200173 / 1000000000) := by
  have h := checkLog_sound (w := (88928825273 / 288928825273)) (n := 12)
    (lo := (159050043 / 250000000)) (hi := (636200173 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((188928825273 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(188928825273 / 100000000000) = 1/(100000000000 / 188928825273) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (159050043 / 250000000) (636200173 / 1000000000) (Real.log (188928825273 / 100000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (188928825273 / 100000000000) = -Real.log (100000000000 / 188928825273) := by
    rw [show ((188928825273 / 100000000000) : ℝ) = ((100000000000 / 188928825273) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (637143677 / 1000000000) ≤ -Real.log (62500000000 / 118191977999) ∧
    -Real.log (62500000000 / 118191977999) ≤ (318571839 / 500000000) := by
  have h := checkLog_sound (w := (55691977999 / 180691977999)) (n := 12)
    (lo := (637143677 / 1000000000)) (hi := (318571839 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((118191977999 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(118191977999 / 62500000000) = 1/(62500000000 / 118191977999) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (637143677 / 1000000000) (318571839 / 500000000) (Real.log (118191977999 / 62500000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (118191977999 / 62500000000) = -Real.log (62500000000 / 118191977999) := by
    rw [show ((118191977999 / 62500000000) : ℝ) = ((62500000000 / 118191977999) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (90935269 / 200000000) ≤ -Real.log (500000000000 / 787831664947) ∧
    -Real.log (500000000000 / 787831664947) ≤ (227338173 / 500000000) := by
  have h := checkLog_sound (w := (287831664947 / 1287831664947)) (n := 12)
    (lo := (90935269 / 200000000)) (hi := (227338173 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((787831664947 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(787831664947 / 500000000000) = 1/(500000000000 / 787831664947) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (90935269 / 200000000) (227338173 / 500000000) (Real.log (787831664947 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (787831664947 / 500000000000) = -Real.log (500000000000 / 787831664947) := by
    rw [show ((787831664947 / 500000000000) : ℝ) = ((500000000000 / 787831664947) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (91072957 / 200000000) ≤ -Real.log (125000000000 / 197093556583) ∧
    -Real.log (125000000000 / 197093556583) ≤ (227682393 / 500000000) := by
  have h := checkLog_sound (w := (72093556583 / 322093556583)) (n := 12)
    (lo := (91072957 / 200000000)) (hi := (227682393 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((197093556583 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(197093556583 / 125000000000) = 1/(125000000000 / 197093556583) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (91072957 / 200000000) (227682393 / 500000000) (Real.log (197093556583 / 125000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (197093556583 / 125000000000) = -Real.log (125000000000 / 197093556583) := by
    rw [show ((197093556583 / 125000000000) : ℝ) = ((125000000000 / 197093556583) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0419
