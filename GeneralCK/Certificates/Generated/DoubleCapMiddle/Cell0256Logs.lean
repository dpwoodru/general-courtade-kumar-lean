import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0256
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

theorem reflection_log_1_neg : (240185017 / 1000000000) ≤ -Real.log (512 / 651) ∧
    -Real.log (512 / 651) ≤ (120092509 / 500000000) := by
  have h := checkLog_sound (w := (139 / 1163)) (n := 12)
    (lo := (240185017 / 1000000000)) (hi := (120092509 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((651 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(651 / 512) = 1/(512 / 651) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (240185017 / 1000000000) (120092509 / 500000000) (Real.log (651 / 512)) := by
  have h := reflection_log_1_neg
  have he : Real.log (651 / 512) = -Real.log (512 / 651) := by
    rw [show ((651 / 512) : ℝ) = ((512 / 651) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (63349241 / 200000000) ≤ -Real.log (373 / 512) ∧
    -Real.log (373 / 512) ≤ (158373103 / 500000000) := by
  have h := checkLog_sound (w := (139 / 885)) (n := 12)
    (lo := (63349241 / 200000000)) (hi := (158373103 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 373) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 373) = 1/(373 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-158373103 / 500000000) (-63349241 / 200000000) (Real.log (373 / 512)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (239724081 / 1000000000) ≤ -Real.log (5120 / 6507) ∧
    -Real.log (5120 / 6507) ≤ (119862041 / 500000000) := by
  have h := checkLog_sound (w := (1387 / 11627)) (n := 12)
    (lo := (239724081 / 1000000000)) (hi := (119862041 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6507 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6507 / 5120) = 1/(5120 / 6507) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (239724081 / 1000000000) (119862041 / 500000000) (Real.log (6507 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6507 / 5120) = -Real.log (5120 / 6507) := by
    rw [show ((6507 / 5120) : ℝ) = ((5120 / 6507) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (315942239 / 1000000000) ≤ -Real.log (3733 / 5120) ∧
    -Real.log (3733 / 5120) ≤ (1974639 / 6250000) := by
  have h := checkLog_sound (w := (1387 / 8853)) (n := 12)
    (lo := (315942239 / 1000000000)) (hi := (1974639 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3733) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3733) = 1/(3733 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-1974639 / 6250000) (-315942239 / 1000000000) (Real.log (3733 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (2710677 / 6250000) ≤ -Real.log (256 / 395) ∧
    -Real.log (256 / 395) ≤ (433708321 / 1000000000) := by
  have h := checkLog_sound (w := (139 / 651)) (n := 12)
    (lo := (2710677 / 6250000)) (hi := (433708321 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((395 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(395 / 256) = 1/(256 / 395) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (2710677 / 6250000) (433708321 / 1000000000) (Real.log (395 / 256)) := by
  have h := reflection_log_5_neg
  have he : Real.log (395 / 256) = -Real.log (256 / 395) := by
    rw [show ((395 / 256) : ℝ) = ((256 / 395) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (783003509 / 1000000000) ≤ -Real.log (117 / 256) ∧
    -Real.log (117 / 256) ≤ (783003511 / 1000000000) := by
  have h := checkLog_sound (w := (11 / 245)) (n := 12)
    (lo := (89856329 / 1000000000)) (hi := (8985633 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((128 / 117) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(128 / 117) = 1/(117 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-783003511 / 1000000000) (-783003509 / 1000000000) (Real.log (117 / 256)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (216474269 / 500000000) ≤ -Real.log (2560 / 3947) ∧
    -Real.log (2560 / 3947) ≤ (432948539 / 1000000000) := by
  have h := checkLog_sound (w := (1387 / 6507)) (n := 12)
    (lo := (216474269 / 500000000)) (hi := (432948539 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3947 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3947 / 2560) = 1/(2560 / 3947) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (216474269 / 500000000) (432948539 / 1000000000) (Real.log (3947 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (3947 / 2560) = -Real.log (2560 / 3947) := by
    rw [show ((3947 / 2560) : ℝ) = ((2560 / 3947) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (12194417 / 15625000) ≤ -Real.log (1173 / 2560) ∧
    -Real.log (1173 / 2560) ≤ (78044269 / 100000000) := by
  have h := checkLog_sound (w := (107 / 2453)) (n := 12)
    (lo := (21823877 / 250000000)) (hi := (87295509 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 1173) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 1173) = 1/(1173 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-78044269 / 100000000) (-12194417 / 15625000) (Real.log (1173 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (164103011 / 500000000) ≤ -Real.log (40000 / 55539) ∧
    -Real.log (40000 / 55539) ≤ (328206023 / 1000000000) := by
  have h := checkLog_sound (w := (15539 / 95539)) (n := 12)
    (lo := (164103011 / 500000000)) (hi := (328206023 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((55539 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(55539 / 40000) = 1/(40000 / 55539) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (164103011 / 500000000) (328206023 / 1000000000) (Real.log (55539 / 40000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (55539 / 40000) = -Real.log (40000 / 55539) := by
    rw [show ((55539 / 40000) : ℝ) = ((40000 / 55539) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (491799441 / 1000000000) ≤ -Real.log (24461 / 40000) ∧
    -Real.log (24461 / 40000) ≤ (245899721 / 500000000) := by
  have h := checkLog_sound (w := (15539 / 64461)) (n := 12)
    (lo := (491799441 / 1000000000)) (hi := (245899721 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000 / 24461) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000 / 24461) = 1/(24461 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-245899721 / 500000000) (-491799441 / 1000000000) (Real.log (24461 / 40000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (328830973 / 1000000000) ≤ -Real.log (1000000 / 1389343) ∧
    -Real.log (1000000 / 1389343) ≤ (164415487 / 500000000) := by
  have h := checkLog_sound (w := (389343 / 2389343)) (n := 12)
    (lo := (328830973 / 1000000000)) (hi := (164415487 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1389343 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1389343 / 1000000) = 1/(1000000 / 1389343) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (328830973 / 1000000000) (164415487 / 500000000) (Real.log (1389343 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1389343 / 1000000) = -Real.log (1000000 / 1389343) := by
    rw [show ((1389343 / 1000000) : ℝ) = ((1000000 / 1389343) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (123304963 / 250000000) ≤ -Real.log (610657 / 1000000) ∧
    -Real.log (610657 / 1000000) ≤ (493219853 / 1000000000) := by
  have h := checkLog_sound (w := (389343 / 1610657)) (n := 12)
    (lo := (123304963 / 250000000)) (hi := (493219853 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 610657) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 610657) = 1/(610657 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-493219853 / 1000000000) (-123304963 / 250000000) (Real.log (610657 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (252045827 / 1000000000) ≤ -Real.log (200000 / 257331) ∧
    -Real.log (200000 / 257331) ≤ (63011457 / 250000000) := by
  have h := checkLog_sound (w := (57331 / 457331)) (n := 12)
    (lo := (252045827 / 1000000000)) (hi := (63011457 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((257331 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(257331 / 200000) = 1/(200000 / 257331) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (252045827 / 1000000000) (63011457 / 250000000) (Real.log (257331 / 200000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (257331 / 200000) = -Real.log (200000 / 257331) := by
    rw [show ((257331 / 200000) : ℝ) = ((200000 / 257331) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (42223763 / 125000000) ≤ -Real.log (142669 / 200000) ∧
    -Real.log (142669 / 200000) ≤ (67558021 / 200000000) := by
  have h := checkLog_sound (w := (57331 / 342669)) (n := 12)
    (lo := (42223763 / 125000000)) (hi := (67558021 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 142669) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 142669) = 1/(142669 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-67558021 / 200000000) (-42223763 / 125000000) (Real.log (142669 / 200000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (50517479 / 200000000) ≤ -Real.log (125000 / 160919) ∧
    -Real.log (125000 / 160919) ≤ (63146849 / 250000000) := by
  have h := checkLog_sound (w := (35919 / 285919)) (n := 12)
    (lo := (50517479 / 200000000)) (hi := (63146849 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160919 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(160919 / 125000) = 1/(125000 / 160919) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (50517479 / 200000000) (63146849 / 250000000) (Real.log (160919 / 125000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (160919 / 125000) = -Real.log (125000 / 160919) := by
    rw [show ((160919 / 125000) : ℝ) = ((125000 / 160919) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (338767669 / 1000000000) ≤ -Real.log (89081 / 125000) ∧
    -Real.log (89081 / 125000) ≤ (33876767 / 100000000) := by
  have h := checkLog_sound (w := (35919 / 214081)) (n := 12)
    (lo := (338767669 / 1000000000)) (hi := (33876767 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 89081) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 89081) = 1/(89081 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-33876767 / 100000000) (-338767669 / 1000000000) (Real.log (89081 / 125000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (820005463 / 1000000000) ≤ -Real.log (50000000000 / 113525612199) ∧
    -Real.log (50000000000 / 113525612199) ≤ (164001093 / 200000000) := by
  have h := checkLog_sound (w := (13525612199 / 213525612199)) (n := 12)
    (lo := (126858283 / 1000000000)) (hi := (31714571 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((113525612199 / 100000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(113525612199 / 100000000000) = 1/(50000000000 / 113525612199) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (820005463 / 1000000000) (164001093 / 200000000) (Real.log (113525612199 / 50000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (113525612199 / 50000000000) = -Real.log (50000000000 / 113525612199) := by
    rw [show ((113525612199 / 50000000000) : ℝ) = ((50000000000 / 113525612199) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (32882033 / 40000000) ≤ -Real.log (15625000000 / 35549390861) ∧
    -Real.log (15625000000 / 35549390861) ≤ (822050827 / 1000000000) := by
  have h := checkLog_sound (w := (4299390861 / 66799390861)) (n := 12)
    (lo := (25780729 / 200000000)) (hi := (64451823 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((35549390861 / 31250000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(35549390861 / 31250000000) = 1/(15625000000 / 35549390861) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (32882033 / 40000000) (822050827 / 1000000000) (Real.log (35549390861 / 15625000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (35549390861 / 15625000000) = -Real.log (15625000000 / 35549390861) := by
    rw [show ((35549390861 / 15625000000) : ℝ) = ((15625000000 / 35549390861) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (147458983 / 250000000) ≤ -Real.log (250000000000 / 450923115743) ∧
    -Real.log (250000000000 / 450923115743) ≤ (589835933 / 1000000000) := by
  have h := checkLog_sound (w := (200923115743 / 700923115743)) (n := 12)
    (lo := (147458983 / 250000000)) (hi := (589835933 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((450923115743 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(450923115743 / 250000000000) = 1/(250000000000 / 450923115743) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (147458983 / 250000000) (589835933 / 1000000000) (Real.log (450923115743 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (450923115743 / 250000000000) = -Real.log (250000000000 / 450923115743) := by
    rw [show ((450923115743 / 250000000000) : ℝ) = ((250000000000 / 450923115743) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (73919383 / 125000000) ≤ -Real.log (250000000000 / 451608648309) ∧
    -Real.log (250000000000 / 451608648309) ≤ (118271013 / 200000000) := by
  have h := checkLog_sound (w := (201608648309 / 701608648309)) (n := 12)
    (lo := (73919383 / 125000000)) (hi := (118271013 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((451608648309 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(451608648309 / 250000000000) = 1/(250000000000 / 451608648309) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (73919383 / 125000000) (118271013 / 200000000) (Real.log (451608648309 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (451608648309 / 250000000000) = -Real.log (250000000000 / 451608648309) := by
    rw [show ((451608648309 / 250000000000) : ℝ) = ((250000000000 / 451608648309) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0256
