import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell009
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

theorem reflection_log_1_neg : (227820099 / 1000000000) ≤ -Real.log (512 / 643) ∧
    -Real.log (512 / 643) ≤ (2278201 / 10000000) := by
  have h := checkLog_sound (w := (131 / 1155)) (n := 12)
    (lo := (227820099 / 1000000000)) (hi := (2278201 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((643 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(643 / 512) = 1/(512 / 643) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (227820099 / 1000000000) (2278201 / 10000000) (Real.log (643 / 512)) := by
  have h := reflection_log_1_neg
  have he : Real.log (643 / 512) = -Real.log (512 / 643) := by
    rw [show ((643 / 512) : ℝ) = ((512 / 643) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (295525249 / 1000000000) ≤ -Real.log (381 / 512) ∧
    -Real.log (381 / 512) ≤ (1182101 / 4000000) := by
  have h := checkLog_sound (w := (131 / 893)) (n := 12)
    (lo := (295525249 / 1000000000)) (hi := (1182101 / 4000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 381) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 381) = 1/(381 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-1182101 / 4000000) (-295525249 / 1000000000) (Real.log (381 / 512)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (227353427 / 1000000000) ≤ -Real.log (5120 / 6427) ∧
    -Real.log (5120 / 6427) ≤ (56838357 / 250000000) := by
  have h := checkLog_sound (w := (1307 / 11547)) (n := 12)
    (lo := (227353427 / 1000000000)) (hi := (56838357 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6427 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6427 / 5120) = 1/(5120 / 6427) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (227353427 / 1000000000) (56838357 / 250000000) (Real.log (6427 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6427 / 5120) = -Real.log (5120 / 6427) := by
    rw [show ((6427 / 5120) : ℝ) = ((5120 / 6427) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (147369079 / 500000000) ≤ -Real.log (3813 / 5120) ∧
    -Real.log (3813 / 5120) ≤ (294738159 / 1000000000) := by
  have h := checkLog_sound (w := (1307 / 8933)) (n := 12)
    (lo := (147369079 / 500000000)) (hi := (294738159 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3813) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3813) = 1/(3813 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-294738159 / 1000000000) (-147369079 / 500000000) (Real.log (3813 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (166369157 / 1000000000) ≤ -Real.log (1000000 / 1181009) ∧
    -Real.log (1000000 / 1181009) ≤ (83184579 / 500000000) := by
  have h := checkLog_sound (w := (181009 / 2181009)) (n := 12)
    (lo := (166369157 / 1000000000)) (hi := (83184579 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1181009 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1181009 / 1000000) = 1/(1000000 / 1181009) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (166369157 / 1000000000) (83184579 / 500000000) (Real.log (1181009 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1181009 / 1000000) = -Real.log (1000000 / 1181009) := by
    rw [show ((1181009 / 1000000) : ℝ) = ((1000000 / 1181009) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (24960273 / 125000000) ≤ -Real.log (818991 / 1000000) ∧
    -Real.log (818991 / 1000000) ≤ (39936437 / 200000000) := by
  have h := checkLog_sound (w := (181009 / 1818991)) (n := 12)
    (lo := (24960273 / 125000000)) (hi := (39936437 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 818991) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 818991) = 1/(818991 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-39936437 / 200000000) (-24960273 / 125000000) (Real.log (818991 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (41680969 / 250000000) ≤ -Real.log (250000 / 295357) ∧
    -Real.log (250000 / 295357) ≤ (166723877 / 1000000000) := by
  have h := checkLog_sound (w := (45357 / 545357)) (n := 12)
    (lo := (41680969 / 250000000)) (hi := (166723877 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((295357 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(295357 / 250000) = 1/(250000 / 295357) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (41680969 / 250000000) (166723877 / 1000000000) (Real.log (295357 / 250000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (295357 / 250000) = -Real.log (250000 / 295357) := by
    rw [show ((295357 / 250000) : ℝ) = ((250000 / 295357) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (312803 / 1562500) ≤ -Real.log (204643 / 250000) ∧
    -Real.log (204643 / 250000) ≤ (200193921 / 1000000000) := by
  have h := checkLog_sound (w := (45357 / 454643)) (n := 12)
    (lo := (312803 / 1562500)) (hi := (200193921 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 204643) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 204643) = 1/(204643 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-200193921 / 1000000000) (-312803 / 1562500) (Real.log (204643 / 250000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (121478421 / 1000000000) ≤ -Real.log (200000 / 225833) ∧
    -Real.log (200000 / 225833) ≤ (60739211 / 500000000) := by
  have h := checkLog_sound (w := (25833 / 425833)) (n := 12)
    (lo := (121478421 / 1000000000)) (hi := (60739211 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((225833 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(225833 / 200000) = 1/(200000 / 225833) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (121478421 / 1000000000) (60739211 / 500000000) (Real.log (225833 / 200000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (225833 / 200000) = -Real.log (200000 / 225833) := by
    rw [show ((225833 / 200000) : ℝ) = ((200000 / 225833) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (138302757 / 1000000000) ≤ -Real.log (174167 / 200000) ∧
    -Real.log (174167 / 200000) ≤ (69151379 / 500000000) := by
  have h := checkLog_sound (w := (25833 / 374167)) (n := 12)
    (lo := (138302757 / 1000000000)) (hi := (69151379 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 174167) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 174167) = 1/(174167 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-69151379 / 500000000) (-138302757 / 1000000000) (Real.log (174167 / 200000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (7609281 / 62500000) ≤ -Real.log (100000 / 112947) ∧
    -Real.log (100000 / 112947) ≤ (121748497 / 1000000000) := by
  have h := checkLog_sound (w := (12947 / 212947)) (n := 12)
    (lo := (7609281 / 62500000)) (hi := (121748497 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((112947 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(112947 / 100000) = 1/(100000 / 112947) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (7609281 / 62500000) (121748497 / 1000000000) (Real.log (112947 / 100000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (112947 / 100000) = -Real.log (100000 / 112947) := by
    rw [show ((112947 / 100000) : ℝ) = ((100000 / 112947) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (138653057 / 1000000000) ≤ -Real.log (87053 / 100000) ∧
    -Real.log (87053 / 100000) ≤ (69326529 / 500000000) := by
  have h := checkLog_sound (w := (12947 / 187053)) (n := 12)
    (lo := (138653057 / 1000000000)) (hi := (69326529 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 87053) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 87053) = 1/(87053 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-69326529 / 500000000) (-138653057 / 1000000000) (Real.log (87053 / 100000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (104418317 / 200000000) ≤ -Real.log (500000000000 / 842774718069) ∧
    -Real.log (500000000000 / 842774718069) ≤ (261045793 / 500000000) := by
  have h := checkLog_sound (w := (342774718069 / 1342774718069)) (n := 12)
    (lo := (104418317 / 200000000)) (hi := (261045793 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((842774718069 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(842774718069 / 500000000000) = 1/(500000000000 / 842774718069) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (104418317 / 200000000) (261045793 / 500000000) (Real.log (842774718069 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (842774718069 / 500000000000) = -Real.log (500000000000 / 842774718069) := by
    rw [show ((842774718069 / 500000000000) : ℝ) = ((500000000000 / 842774718069) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (523345349 / 1000000000) ≤ -Real.log (250000000000 / 421916010499) ∧
    -Real.log (250000000000 / 421916010499) ≤ (10466907 / 20000000) := by
  have h := checkLog_sound (w := (171916010499 / 671916010499)) (n := 12)
    (lo := (523345349 / 1000000000)) (hi := (10466907 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((421916010499 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(421916010499 / 250000000000) = 1/(250000000000 / 421916010499) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (523345349 / 1000000000) (10466907 / 20000000) (Real.log (421916010499 / 250000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (421916010499 / 250000000000) = -Real.log (250000000000 / 421916010499) := by
    rw [show ((421916010499 / 250000000000) : ℝ) = ((250000000000 / 421916010499) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (183025671 / 500000000) ≤ -Real.log (62500000000 / 90126829843) ∧
    -Real.log (62500000000 / 90126829843) ≤ (366051343 / 1000000000) := by
  have h := checkLog_sound (w := (27626829843 / 152626829843)) (n := 12)
    (lo := (183025671 / 500000000)) (hi := (366051343 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((90126829843 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(90126829843 / 62500000000) = 1/(62500000000 / 90126829843) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (183025671 / 500000000) (366051343 / 1000000000) (Real.log (90126829843 / 62500000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (90126829843 / 62500000000) = -Real.log (62500000000 / 90126829843) := by
    rw [show ((90126829843 / 62500000000) : ℝ) = ((62500000000 / 90126829843) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (91729449 / 250000000) ≤ -Real.log (250000000000 / 360819817927) ∧
    -Real.log (250000000000 / 360819817927) ≤ (366917797 / 1000000000) := by
  have h := checkLog_sound (w := (110819817927 / 610819817927)) (n := 12)
    (lo := (91729449 / 250000000)) (hi := (366917797 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((360819817927 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(360819817927 / 250000000000) = 1/(250000000000 / 360819817927) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (91729449 / 250000000) (366917797 / 1000000000) (Real.log (360819817927 / 250000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (360819817927 / 250000000000) = -Real.log (250000000000 / 360819817927) := by
    rw [show ((360819817927 / 250000000000) : ℝ) = ((250000000000 / 360819817927) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (259781179 / 1000000000) ≤ -Real.log (500000000000 / 648323161103) ∧
    -Real.log (500000000000 / 648323161103) ≤ (12989059 / 50000000) := by
  have h := checkLog_sound (w := (148323161103 / 1148323161103)) (n := 12)
    (lo := (259781179 / 1000000000)) (hi := (12989059 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((648323161103 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(648323161103 / 500000000000) = 1/(500000000000 / 648323161103) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (259781179 / 1000000000) (12989059 / 50000000) (Real.log (648323161103 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (648323161103 / 500000000000) = -Real.log (500000000000 / 648323161103) := by
    rw [show ((648323161103 / 500000000000) : ℝ) = ((500000000000 / 648323161103) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (260401553 / 1000000000) ≤ -Real.log (50000000000 / 64872548907) ∧
    -Real.log (50000000000 / 64872548907) ≤ (130200777 / 500000000) := by
  have h := checkLog_sound (w := (14872548907 / 114872548907)) (n := 12)
    (lo := (260401553 / 1000000000)) (hi := (130200777 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((64872548907 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(64872548907 / 50000000000) = 1/(50000000000 / 64872548907) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (260401553 / 1000000000) (130200777 / 500000000) (Real.log (64872548907 / 50000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (64872548907 / 50000000000) = -Real.log (50000000000 / 64872548907) := by
    rw [show ((64872548907 / 50000000000) : ℝ) = ((50000000000 / 64872548907) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (16904561 / 1000000000) ≤ -Real.log (9832375191 / 10000000000) ∧
    -Real.log (9832375191 / 10000000000) ≤ (8452281 / 500000000) := by
  have h := checkLog_sound (w := (167624809 / 19832375191)) (n := 12)
    (lo := (16904561 / 1000000000)) (hi := (8452281 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 9832375191) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 9832375191) = 1/(9832375191 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-8452281 / 500000000) (-16904561 / 1000000000) (Real.log (9832375191 / 10000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (3364867 / 200000000) ≤ -Real.log (39332656111 / 40000000000) ∧
    -Real.log (39332656111 / 40000000000) ≤ (1051521 / 62500000) := by
  have h := checkLog_sound (w := (667343889 / 79332656111)) (n := 12)
    (lo := (3364867 / 200000000)) (hi := (1051521 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39332656111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39332656111) = 1/(39332656111 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-1051521 / 62500000) (-3364867 / 200000000) (Real.log (39332656111 / 40000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell009
