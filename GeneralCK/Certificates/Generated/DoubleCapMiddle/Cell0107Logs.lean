import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0107
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

theorem reflection_log_1_neg : (163751783 / 500000000) ≤ -Real.log (80 / 111) ∧
    -Real.log (80 / 111) ≤ (327503567 / 1000000000) := by
  have h := checkLog_sound (w := (31 / 191)) (n := 12)
    (lo := (163751783 / 500000000)) (hi := (327503567 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((111 / 80) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(111 / 80) = 1/(80 / 111) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (163751783 / 500000000) (327503567 / 1000000000) (Real.log (111 / 80)) := by
  have h := reflection_log_1_neg
  have he : Real.log (111 / 80) = -Real.log (80 / 111) := by
    rw [show ((111 / 80) : ℝ) = ((80 / 111) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (3829737 / 7812500) ≤ -Real.log (49 / 80) ∧
    -Real.log (49 / 80) ≤ (490206337 / 1000000000) := by
  have h := checkLog_sound (w := (31 / 129)) (n := 12)
    (lo := (3829737 / 7812500)) (hi := (490206337 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80 / 49) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(80 / 49) = 1/(49 / 80) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-490206337 / 1000000000) (-3829737 / 7812500) (Real.log (49 / 80)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (65331723 / 200000000) ≤ -Real.log (2560 / 3549) ∧
    -Real.log (2560 / 3549) ≤ (40832327 / 125000000) := by
  have h := checkLog_sound (w := (989 / 6109)) (n := 12)
    (lo := (65331723 / 200000000)) (hi := (40832327 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3549 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3549 / 2560) = 1/(2560 / 3549) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (65331723 / 200000000) (40832327 / 125000000) (Real.log (3549 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3549 / 2560) = -Real.log (2560 / 3549) := by
    rw [show ((3549 / 2560) : ℝ) = ((2560 / 3549) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (488294899 / 1000000000) ≤ -Real.log (1571 / 2560) ∧
    -Real.log (1571 / 2560) ≤ (4882949 / 10000000) := by
  have h := checkLog_sound (w := (989 / 4131)) (n := 12)
    (lo := (488294899 / 1000000000)) (hi := (4882949 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1571) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1571) = 1/(1571 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-4882949 / 10000000) (-488294899 / 1000000000) (Real.log (1571 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (286900211 / 500000000) ≤ -Real.log (40 / 71) ∧
    -Real.log (40 / 71) ≤ (573800423 / 1000000000) := by
  have h := checkLog_sound (w := (31 / 111)) (n := 12)
    (lo := (286900211 / 500000000)) (hi := (573800423 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((71 / 40) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(71 / 40) = 1/(40 / 71) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (286900211 / 500000000) (573800423 / 1000000000) (Real.log (71 / 40)) := by
  have h := reflection_log_5_neg
  have he : Real.log (71 / 40) = -Real.log (40 / 71) := by
    rw [show ((71 / 40) : ℝ) = ((40 / 71) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (11933239 / 8000000) ≤ -Real.log (9 / 40) ∧
    -Real.log (9 / 40) ≤ (745827439 / 500000000) := by
  have h := checkLog_sound (w := (1 / 19)) (n := 12)
    (lo := (21072103 / 200000000)) (hi := (26340129 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10 / 9) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(10 / 9) = 1/(9 / 40) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-745827439 / 500000000) (-11933239 / 8000000) (Real.log (9 / 40)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (572479127 / 1000000000) ≤ -Real.log (1280 / 2269) ∧
    -Real.log (1280 / 2269) ≤ (71559891 / 125000000) := by
  have h := checkLog_sound (w := (989 / 3549)) (n := 12)
    (lo := (572479127 / 1000000000)) (hi := (71559891 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2269 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2269 / 1280) = 1/(1280 / 2269) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (572479127 / 1000000000) (71559891 / 125000000) (Real.log (2269 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2269 / 1280) = -Real.log (1280 / 2269) := by
    rw [show ((2269 / 1280) : ℝ) = ((1280 / 2269) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (185161511 / 125000000) ≤ -Real.log (291 / 1280) ∧
    -Real.log (291 / 1280) ≤ (1481292091 / 1000000000) := by
  have h := checkLog_sound (w := (29 / 611)) (n := 12)
    (lo := (2968679 / 31250000)) (hi := (94997729 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 291) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(320 / 291) = 1/(291 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1481292091 / 1000000000) (-185161511 / 125000000) (Real.log (291 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (111993819 / 250000000) ≤ -Real.log (50000 / 78257) ∧
    -Real.log (50000 / 78257) ≤ (447975277 / 1000000000) := by
  have h := checkLog_sound (w := (28257 / 128257)) (n := 12)
    (lo := (111993819 / 250000000)) (hi := (447975277 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((78257 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(78257 / 50000) = 1/(50000 / 78257) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (111993819 / 250000000) (447975277 / 1000000000) (Real.log (78257 / 50000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (78257 / 50000) = -Real.log (50000 / 78257) := by
    rw [show ((78257 / 50000) : ℝ) = ((50000 / 78257) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (416365569 / 500000000) ≤ -Real.log (21743 / 50000) ∧
    -Real.log (21743 / 50000) ≤ (41636557 / 50000000) := by
  have h := checkLog_sound (w := (3257 / 46743)) (n := 12)
    (lo := (69791979 / 500000000)) (hi := (139583959 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 21743) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(25000 / 21743) = 1/(21743 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-41636557 / 50000000) (-416365569 / 500000000) (Real.log (21743 / 50000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (112294091 / 250000000) ≤ -Real.log (1000000 / 1567021) ∧
    -Real.log (1000000 / 1567021) ≤ (89835273 / 200000000) := by
  have h := checkLog_sound (w := (567021 / 2567021)) (n := 12)
    (lo := (112294091 / 250000000)) (hi := (89835273 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1567021 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1567021 / 1000000) = 1/(1000000 / 1567021) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (112294091 / 250000000) (89835273 / 200000000) (Real.log (1567021 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1567021 / 1000000) = -Real.log (1000000 / 1567021) := by
    rw [show ((1567021 / 1000000) : ℝ) = ((1000000 / 1567021) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (16741321 / 20000000) ≤ -Real.log (432979 / 1000000) ∧
    -Real.log (432979 / 1000000) ≤ (209266513 / 250000000) := by
  have h := checkLog_sound (w := (67021 / 932979)) (n := 12)
    (lo := (14391887 / 100000000)) (hi := (143918871 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 432979) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 432979) = 1/(432979 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-209266513 / 250000000) (-16741321 / 20000000) (Real.log (432979 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (72667619 / 200000000) ≤ -Real.log (500000 / 719061) ∧
    -Real.log (500000 / 719061) ≤ (22708631 / 62500000) := by
  have h := checkLog_sound (w := (219061 / 1219061)) (n := 12)
    (lo := (72667619 / 200000000)) (hi := (22708631 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((719061 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(719061 / 500000) = 1/(500000 / 719061) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (72667619 / 200000000) (22708631 / 62500000) (Real.log (719061 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (719061 / 500000) = -Real.log (500000 / 719061) := by
    rw [show ((719061 / 500000) : ℝ) = ((500000 / 719061) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (288235267 / 500000000) ≤ -Real.log (280939 / 500000) ∧
    -Real.log (280939 / 500000) ≤ (115294107 / 200000000) := by
  have h := checkLog_sound (w := (219061 / 780939)) (n := 12)
    (lo := (288235267 / 500000000)) (hi := (115294107 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 280939) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 280939) = 1/(280939 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-115294107 / 200000000) (-288235267 / 500000000) (Real.log (280939 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (182272943 / 500000000) ≤ -Real.log (50000 / 71993) ∧
    -Real.log (50000 / 71993) ≤ (364545887 / 1000000000) := by
  have h := checkLog_sound (w := (21993 / 121993)) (n := 12)
    (lo := (182272943 / 500000000)) (hi := (364545887 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((71993 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(71993 / 50000) = 1/(50000 / 71993) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (182272943 / 500000000) (364545887 / 1000000000) (Real.log (71993 / 50000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (71993 / 50000) = -Real.log (50000 / 71993) := by
    rw [show ((71993 / 50000) : ℝ) = ((50000 / 71993) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (289784263 / 500000000) ≤ -Real.log (28007 / 50000) ∧
    -Real.log (28007 / 50000) ≤ (579568527 / 1000000000) := by
  have h := checkLog_sound (w := (21993 / 78007)) (n := 12)
    (lo := (289784263 / 500000000)) (hi := (579568527 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 28007) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 28007) = 1/(28007 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-579568527 / 1000000000) (-289784263 / 500000000) (Real.log (28007 / 50000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (256141283 / 200000000) ≤ -Real.log (25000000000 / 89979533643) ∧
    -Real.log (25000000000 / 89979533643) ≤ (1280706417 / 1000000000) := by
  have h := checkLog_sound (w := (39979533643 / 139979533643)) (n := 12)
    (lo := (117511847 / 200000000)) (hi := (146889809 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((89979533643 / 50000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(89979533643 / 50000000000) = 1/(25000000000 / 89979533643) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (256141283 / 200000000) (1280706417 / 1000000000) (Real.log (89979533643 / 25000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (89979533643 / 25000000000) = -Real.log (25000000000 / 89979533643) := by
    rw [show ((89979533643 / 25000000000) : ℝ) = ((25000000000 / 89979533643) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (257248483 / 200000000) ≤ -Real.log (20000000000 / 72383233367) ∧
    -Real.log (20000000000 / 72383233367) ≤ (1286242417 / 1000000000) := by
  have h := checkLog_sound (w := (32383233367 / 112383233367)) (n := 12)
    (lo := (118619047 / 200000000)) (hi := (148273809 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((72383233367 / 40000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(72383233367 / 40000000000) = 1/(20000000000 / 72383233367) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (257248483 / 200000000) (1286242417 / 1000000000) (Real.log (72383233367 / 20000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (72383233367 / 20000000000) = -Real.log (20000000000 / 72383233367) := by
    rw [show ((72383233367 / 20000000000) : ℝ) = ((20000000000 / 72383233367) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (939808629 / 1000000000) ≤ -Real.log (62500000000 / 159968222639) ∧
    -Real.log (62500000000 / 159968222639) ≤ (939808631 / 1000000000) := by
  have h := checkLog_sound (w := (34968222639 / 284968222639)) (n := 12)
    (lo := (246661449 / 1000000000)) (hi := (4933229 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((159968222639 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(159968222639 / 125000000000) = 1/(62500000000 / 159968222639) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (939808629 / 1000000000) (939808631 / 1000000000) (Real.log (159968222639 / 62500000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (159968222639 / 62500000000) = -Real.log (62500000000 / 159968222639) := by
    rw [show ((159968222639 / 62500000000) : ℝ) = ((62500000000 / 159968222639) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (236028603 / 250000000) ≤ -Real.log (500000000000 / 1285267968723) ∧
    -Real.log (500000000000 / 1285267968723) ≤ (472057207 / 500000000) := by
  have h := checkLog_sound (w := (285267968723 / 2285267968723)) (n := 12)
    (lo := (3921363 / 15625000)) (hi := (250967233 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1285267968723 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1285267968723 / 1000000000000) = 1/(500000000000 / 1285267968723) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (236028603 / 250000000) (472057207 / 500000000) (Real.log (1285267968723 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1285267968723 / 500000000000) = -Real.log (500000000000 / 1285267968723) := by
    rw [show ((1285267968723 / 500000000000) : ℝ) = ((500000000000 / 1285267968723) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0107
