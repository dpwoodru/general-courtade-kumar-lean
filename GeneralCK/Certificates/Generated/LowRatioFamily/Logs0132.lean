import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_8448_neg : (8208401 / 500000000) ≤ -Real.log (61482326199 / 62500000000) ∧
    -Real.log (61482326199 / 62500000000) ≤ (16416803 / 1000000000) := by
  have h := checkLog_sound (w := (1017673801 / 123982326199)) (n := 12)
    (lo := (8208401 / 500000000)) (hi := (16416803 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 61482326199) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 61482326199) = 1/(61482326199 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8448 : Bounds (-16416803 / 1000000000) (-8208401 / 500000000) (Real.log (61482326199 / 62500000000)) := by
  have h := reflection_log_8448_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8449_neg : (256606857 / 1000000000) ≤ -Real.log (500000000000 / 646268437727) ∧
    -Real.log (500000000000 / 646268437727) ≤ (128303429 / 500000000) := by
  have h := checkLog_sound (w := (146268437727 / 1146268437727)) (n := 12)
    (lo := (256606857 / 1000000000)) (hi := (128303429 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((646268437727 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(646268437727 / 500000000000) = 1/(500000000000 / 646268437727) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8449 : Bounds (256606857 / 1000000000) (128303429 / 500000000) (Real.log (646268437727 / 500000000000)) := by
  have h := reflection_log_8449_neg
  have he : Real.log (646268437727 / 500000000000) = -Real.log (500000000000 / 646268437727) := by
    rw [show ((646268437727 / 500000000000) : ℝ) = ((500000000000 / 646268437727) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8450_neg : (257643809 / 1000000000) ≤ -Real.log (250000000000 / 323469467339) ∧
    -Real.log (250000000000 / 323469467339) ≤ (25764381 / 100000000) := by
  have h := checkLog_sound (w := (73469467339 / 573469467339)) (n := 12)
    (lo := (257643809 / 1000000000)) (hi := (25764381 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((323469467339 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(323469467339 / 250000000000) = 1/(250000000000 / 323469467339) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8450 : Bounds (257643809 / 1000000000) (25764381 / 100000000) (Real.log (323469467339 / 250000000000)) := by
  have h := reflection_log_8450_neg
  have he : Real.log (323469467339 / 250000000000) = -Real.log (250000000000 / 323469467339) := by
    rw [show ((323469467339 / 250000000000) : ℝ) = ((250000000000 / 323469467339) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8451_neg : (516162527 / 1000000000) ≤ -Real.log (25000000000 / 41889632107) ∧
    -Real.log (25000000000 / 41889632107) ≤ (16130079 / 31250000) := by
  have h := checkLog_sound (w := (16889632107 / 66889632107)) (n := 12)
    (lo := (516162527 / 1000000000)) (hi := (16130079 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((41889632107 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(41889632107 / 25000000000) = 1/(25000000000 / 41889632107) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8451 : Bounds (516162527 / 1000000000) (16130079 / 31250000) (Real.log (41889632107 / 25000000000)) := by
  have h := reflection_log_8451_neg
  have he : Real.log (41889632107 / 25000000000) = -Real.log (25000000000 / 41889632107) := by
    rw [show ((41889632107 / 25000000000) : ℝ) = ((25000000000 / 41889632107) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8452_neg : (517230769 / 1000000000) ≤ -Real.log (500000000000 / 838688085677) ∧
    -Real.log (500000000000 / 838688085677) ≤ (51723077 / 100000000) := by
  have h := checkLog_sound (w := (338688085677 / 1338688085677)) (n := 12)
    (lo := (517230769 / 1000000000)) (hi := (51723077 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((838688085677 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(838688085677 / 500000000000) = 1/(500000000000 / 838688085677) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8452 : Bounds (517230769 / 1000000000) (51723077 / 100000000) (Real.log (838688085677 / 500000000000)) := by
  have h := reflection_log_8452_neg
  have he : Real.log (838688085677 / 500000000000) = -Real.log (500000000000 / 838688085677) := by
    rw [show ((838688085677 / 500000000000) : ℝ) = ((500000000000 / 838688085677) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8453_neg : (112969819 / 500000000) ≤ -Real.log (2000 / 2507) ∧
    -Real.log (2000 / 2507) ≤ (225939639 / 1000000000) := by
  have h := checkLog_sound (w := (507 / 4507)) (n := 12)
    (lo := (112969819 / 500000000)) (hi := (225939639 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2507 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2507 / 2000) = 1/(2000 / 2507) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8453 : Bounds (112969819 / 500000000) (225939639 / 1000000000) (Real.log (2507 / 2000)) := by
  have h := reflection_log_8453_neg
  have he : Real.log (2507 / 2000) = -Real.log (2000 / 2507) := by
    rw [show ((2507 / 2000) : ℝ) = ((2000 / 2507) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8454_neg : (146179831 / 500000000) ≤ -Real.log (1493 / 2000) ∧
    -Real.log (1493 / 2000) ≤ (292359663 / 1000000000) := by
  have h := checkLog_sound (w := (507 / 3493)) (n := 12)
    (lo := (146179831 / 500000000)) (hi := (292359663 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1493) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1493) = 1/(1493 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8454 : Bounds (-292359663 / 1000000000) (-146179831 / 500000000) (Real.log (1493 / 2000)) := by
  have h := reflection_log_8454_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8455_neg : (253467 / 1000000000) ≤ -Real.log (2000000 / 2000507) ∧
    -Real.log (2000000 / 2000507) ≤ (63367 / 250000000) := by
  have h := checkLog_sound (w := (507 / 4000507)) (n := 12)
    (lo := (253467 / 1000000000)) (hi := (63367 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000507 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000507 / 2000000) = 1/(2000000 / 2000507) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8455 : Bounds (253467 / 1000000000) (63367 / 250000000) (Real.log (2000507 / 2000000)) := by
  have h := reflection_log_8455_neg
  have he : Real.log (2000507 / 2000000) = -Real.log (2000000 / 2000507) := by
    rw [show ((2000507 / 2000000) : ℝ) = ((2000000 / 2000507) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8456_neg : (63383 / 250000000) ≤ -Real.log (1999493 / 2000000) ∧
    -Real.log (1999493 / 2000000) ≤ (253533 / 1000000000) := by
  have h := checkLog_sound (w := (507 / 3999493)) (n := 12)
    (lo := (63383 / 250000000)) (hi := (253533 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999493) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999493) = 1/(1999493 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8456 : Bounds (-253533 / 1000000000) (-63383 / 250000000) (Real.log (1999493 / 2000000)) := by
  have h := reflection_log_8456_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8457_neg : (120324691 / 1000000000) ≤ -Real.log (1000000 / 1127863) ∧
    -Real.log (1000000 / 1127863) ≤ (30081173 / 250000000) := by
  have h := checkLog_sound (w := (127863 / 2127863)) (n := 12)
    (lo := (120324691 / 1000000000)) (hi := (30081173 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1127863 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1127863 / 1000000) = 1/(1000000 / 1127863) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8457 : Bounds (120324691 / 1000000000) (30081173 / 250000000) (Real.log (1127863 / 1000000)) := by
  have h := reflection_log_8457_neg
  have he : Real.log (1127863 / 1000000) = -Real.log (1000000 / 1127863) := by
    rw [show ((1127863 / 1000000) : ℝ) = ((1000000 / 1127863) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8458_neg : (136808757 / 1000000000) ≤ -Real.log (872137 / 1000000) ∧
    -Real.log (872137 / 1000000) ≤ (68404379 / 500000000) := by
  have h := checkLog_sound (w := (127863 / 1872137)) (n := 12)
    (lo := (136808757 / 1000000000)) (hi := (68404379 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 872137) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 872137) = 1/(872137 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8458 : Bounds (-68404379 / 500000000) (-136808757 / 1000000000) (Real.log (872137 / 1000000)) := by
  have h := reflection_log_8458_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8459_neg : (30194193 / 250000000) ≤ -Real.log (1000000 / 1128373) ∧
    -Real.log (1000000 / 1128373) ≤ (120776773 / 1000000000) := by
  have h := checkLog_sound (w := (128373 / 2128373)) (n := 12)
    (lo := (30194193 / 250000000)) (hi := (120776773 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1128373 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1128373 / 1000000) = 1/(1000000 / 1128373) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8459 : Bounds (30194193 / 250000000) (120776773 / 1000000000) (Real.log (1128373 / 1000000)) := by
  have h := reflection_log_8459_neg
  have he : Real.log (1128373 / 1000000) = -Real.log (1000000 / 1128373) := by
    rw [show ((1128373 / 1000000) : ℝ) = ((1000000 / 1128373) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8460_neg : (68696849 / 500000000) ≤ -Real.log (871627 / 1000000) ∧
    -Real.log (871627 / 1000000) ≤ (137393699 / 1000000000) := by
  have h := checkLog_sound (w := (128373 / 1871627)) (n := 12)
    (lo := (68696849 / 500000000)) (hi := (137393699 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 871627) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 871627) = 1/(871627 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8460 : Bounds (-137393699 / 1000000000) (-68696849 / 500000000) (Real.log (871627 / 1000000)) := by
  have h := reflection_log_8460_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8461_neg : (8308463 / 500000000) ≤ -Real.log (983520372871 / 1000000000000) ∧
    -Real.log (983520372871 / 1000000000000) ≤ (16616927 / 1000000000) := by
  have h := checkLog_sound (w := (16479627129 / 1983520372871)) (n := 12)
    (lo := (8308463 / 500000000)) (hi := (16616927 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 983520372871) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 983520372871) = 1/(983520372871 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8461 : Bounds (-16616927 / 1000000000) (-8308463 / 500000000) (Real.log (983520372871 / 1000000000000)) := by
  have h := reflection_log_8461_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8462_neg : (3296813 / 200000000) ≤ -Real.log (983651053231 / 1000000000000) ∧
    -Real.log (983651053231 / 1000000000000) ≤ (8242033 / 500000000) := by
  have h := checkLog_sound (w := (16348946769 / 1983651053231)) (n := 12)
    (lo := (3296813 / 200000000)) (hi := (8242033 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 983651053231) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 983651053231) = 1/(983651053231 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8462 : Bounds (-8242033 / 500000000) (-3296813 / 200000000) (Real.log (983651053231 / 1000000000000)) := by
  have h := reflection_log_8462_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8463_neg : (257133449 / 1000000000) ≤ -Real.log (125000000000 / 161652211751) ∧
    -Real.log (125000000000 / 161652211751) ≤ (5142669 / 20000000) := by
  have h := checkLog_sound (w := (36652211751 / 286652211751)) (n := 12)
    (lo := (257133449 / 1000000000)) (hi := (5142669 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((161652211751 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(161652211751 / 125000000000) = 1/(125000000000 / 161652211751) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8463 : Bounds (257133449 / 1000000000) (5142669 / 20000000) (Real.log (161652211751 / 125000000000)) := by
  have h := reflection_log_8463_neg
  have he : Real.log (161652211751 / 125000000000) = -Real.log (125000000000 / 161652211751) := by
    rw [show ((161652211751 / 125000000000) : ℝ) = ((125000000000 / 161652211751) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8464_neg : (258170471 / 1000000000) ≤ -Real.log (500000000000 / 647279742367) ∧
    -Real.log (500000000000 / 647279742367) ≤ (32271309 / 125000000) := by
  have h := checkLog_sound (w := (147279742367 / 1147279742367)) (n := 12)
    (lo := (258170471 / 1000000000)) (hi := (32271309 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((647279742367 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(647279742367 / 500000000000) = 1/(500000000000 / 647279742367) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8464 : Bounds (258170471 / 1000000000) (32271309 / 125000000) (Real.log (647279742367 / 500000000000)) := by
  have h := reflection_log_8464_neg
  have he : Real.log (647279742367 / 500000000000) = -Real.log (500000000000 / 647279742367) := by
    rw [show ((647279742367 / 500000000000) : ℝ) = ((500000000000 / 647279742367) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8465_neg : (517230769 / 1000000000) ≤ -Real.log (125000000000 / 209672021419) ∧
    -Real.log (125000000000 / 209672021419) ≤ (51723077 / 100000000) := by
  have h := checkLog_sound (w := (84672021419 / 334672021419)) (n := 12)
    (lo := (517230769 / 1000000000)) (hi := (51723077 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((209672021419 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(209672021419 / 125000000000) = 1/(125000000000 / 209672021419) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8465 : Bounds (517230769 / 1000000000) (51723077 / 100000000) (Real.log (209672021419 / 125000000000)) := by
  have h := reflection_log_8465_neg
  have he : Real.log (209672021419 / 125000000000) = -Real.log (125000000000 / 209672021419) := by
    rw [show ((209672021419 / 125000000000) : ℝ) = ((125000000000 / 209672021419) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8466_neg : (5182993 / 10000000) ≤ -Real.log (100000000000 / 167916945747) ∧
    -Real.log (100000000000 / 167916945747) ≤ (518299301 / 1000000000) := by
  have h := checkLog_sound (w := (67916945747 / 267916945747)) (n := 12)
    (lo := (5182993 / 10000000)) (hi := (518299301 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((167916945747 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(167916945747 / 100000000000) = 1/(100000000000 / 167916945747) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8466 : Bounds (5182993 / 10000000) (518299301 / 1000000000) (Real.log (167916945747 / 100000000000)) := by
  have h := reflection_log_8466_neg
  have he : Real.log (167916945747 / 100000000000) = -Real.log (100000000000 / 167916945747) := by
    rw [show ((167916945747 / 100000000000) : ℝ) = ((100000000000 / 167916945747) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8467_neg : (113169221 / 500000000) ≤ -Real.log (500 / 627) ∧
    -Real.log (500 / 627) ≤ (226338443 / 1000000000) := by
  have h := checkLog_sound (w := (127 / 1127)) (n := 12)
    (lo := (113169221 / 500000000)) (hi := (226338443 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((627 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(627 / 500) = 1/(500 / 627) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8467 : Bounds (113169221 / 500000000) (226338443 / 1000000000) (Real.log (627 / 500)) := by
  have h := reflection_log_8467_neg
  have he : Real.log (627 / 500) = -Real.log (500 / 627) := by
    rw [show ((627 / 500) : ℝ) = ((500 / 627) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8468_neg : (146514839 / 500000000) ≤ -Real.log (373 / 500) ∧
    -Real.log (373 / 500) ≤ (293029679 / 1000000000) := by
  have h := checkLog_sound (w := (127 / 873)) (n := 12)
    (lo := (146514839 / 500000000)) (hi := (293029679 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 373) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500 / 373) = 1/(373 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8468 : Bounds (-293029679 / 1000000000) (-146514839 / 500000000) (Real.log (373 / 500)) := by
  have h := reflection_log_8468_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8469_neg : (253967 / 1000000000) ≤ -Real.log (500000 / 500127) ∧
    -Real.log (500000 / 500127) ≤ (15873 / 62500000) := by
  have h := checkLog_sound (w := (127 / 1000127)) (n := 12)
    (lo := (253967 / 1000000000)) (hi := (15873 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500127 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500127 / 500000) = 1/(500000 / 500127) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8469 : Bounds (253967 / 1000000000) (15873 / 62500000) (Real.log (500127 / 500000)) := by
  have h := reflection_log_8469_neg
  have he : Real.log (500127 / 500000) = -Real.log (500000 / 500127) := by
    rw [show ((500127 / 500000) : ℝ) = ((500000 / 500127) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8470_neg : (15877 / 62500000) ≤ -Real.log (499873 / 500000) ∧
    -Real.log (499873 / 500000) ≤ (254033 / 1000000000) := by
  have h := checkLog_sound (w := (127 / 999873)) (n := 12)
    (lo := (15877 / 62500000)) (hi := (254033 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499873) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499873) = 1/(499873 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8470 : Bounds (-254033 / 1000000000) (-15877 / 62500000) (Real.log (499873 / 500000)) := by
  have h := reflection_log_8470_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8471_neg : (15069177 / 125000000) ≤ -Real.log (1000000 / 1128121) ∧
    -Real.log (1000000 / 1128121) ≤ (120553417 / 1000000000) := by
  have h := checkLog_sound (w := (128121 / 2128121)) (n := 12)
    (lo := (15069177 / 125000000)) (hi := (120553417 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1128121 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1128121 / 1000000) = 1/(1000000 / 1128121) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8471 : Bounds (15069177 / 125000000) (120553417 / 1000000000) (Real.log (1128121 / 1000000)) := by
  have h := reflection_log_8471_neg
  have he : Real.log (1128121 / 1000000) = -Real.log (1000000 / 1128121) := by
    rw [show ((1128121 / 1000000) : ℝ) = ((1000000 / 1128121) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8472_neg : (68552313 / 500000000) ≤ -Real.log (871879 / 1000000) ∧
    -Real.log (871879 / 1000000) ≤ (137104627 / 1000000000) := by
  have h := checkLog_sound (w := (128121 / 1871879)) (n := 12)
    (lo := (68552313 / 500000000)) (hi := (137104627 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 871879) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 871879) = 1/(871879 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8472 : Bounds (-137104627 / 1000000000) (-68552313 / 500000000) (Real.log (871879 / 1000000)) := by
  have h := reflection_log_8472_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8473_neg : (121006279 / 1000000000) ≤ -Real.log (125000 / 141079) ∧
    -Real.log (125000 / 141079) ≤ (3025157 / 25000000) := by
  have h := checkLog_sound (w := (16079 / 266079)) (n := 12)
    (lo := (121006279 / 1000000000)) (hi := (3025157 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((141079 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(141079 / 125000) = 1/(125000 / 141079) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8473 : Bounds (121006279 / 1000000000) (3025157 / 25000000) (Real.log (141079 / 125000)) := by
  have h := reflection_log_8473_neg
  have he : Real.log (141079 / 125000) = -Real.log (125000 / 141079) := by
    rw [show ((141079 / 125000) : ℝ) = ((125000 / 141079) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8474_neg : (17211361 / 125000000) ≤ -Real.log (108921 / 125000) ∧
    -Real.log (108921 / 125000) ≤ (137690889 / 1000000000) := by
  have h := checkLog_sound (w := (16079 / 233921)) (n := 12)
    (lo := (17211361 / 125000000)) (hi := (137690889 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 108921) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 108921) = 1/(108921 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8474 : Bounds (-137690889 / 1000000000) (-17211361 / 125000000) (Real.log (108921 / 125000)) := by
  have h := reflection_log_8474_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8475_neg : (260697 / 15625000) ≤ -Real.log (15366465759 / 15625000000) ∧
    -Real.log (15366465759 / 15625000000) ≤ (16684609 / 1000000000) := by
  have h := checkLog_sound (w := (258534241 / 30991465759)) (n := 12)
    (lo := (260697 / 15625000)) (hi := (16684609 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 15366465759) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 15366465759) = 1/(15366465759 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8475 : Bounds (-16684609 / 1000000000) (-260697 / 15625000) (Real.log (15366465759 / 15625000000)) := by
  have h := reflection_log_8475_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8476_neg : (16551209 / 1000000000) ≤ -Real.log (983585009359 / 1000000000000) ∧
    -Real.log (983585009359 / 1000000000000) ≤ (1655121 / 100000000) := by
  have h := checkLog_sound (w := (16414990641 / 1983585009359)) (n := 12)
    (lo := (16551209 / 1000000000)) (hi := (1655121 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 983585009359) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 983585009359) = 1/(983585009359 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8476 : Bounds (-1655121 / 100000000) (-16551209 / 1000000000) (Real.log (983585009359 / 1000000000000)) := by
  have h := reflection_log_8476_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8477_neg : (128829021 / 500000000) ≤ -Real.log (500000000000 / 646948143033) ∧
    -Real.log (500000000000 / 646948143033) ≤ (257658043 / 1000000000) := by
  have h := checkLog_sound (w := (146948143033 / 1146948143033)) (n := 12)
    (lo := (128829021 / 500000000)) (hi := (257658043 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((646948143033 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(646948143033 / 500000000000) = 1/(500000000000 / 646948143033) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8477 : Bounds (128829021 / 500000000) (257658043 / 1000000000) (Real.log (646948143033 / 500000000000)) := by
  have h := reflection_log_8477_neg
  have he : Real.log (646948143033 / 500000000000) = -Real.log (500000000000 / 646948143033) := by
    rw [show ((646948143033 / 500000000000) : ℝ) = ((500000000000 / 646948143033) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8478_neg : (16168573 / 62500000) ≤ -Real.log (31250000000 / 40476297041) ∧
    -Real.log (31250000000 / 40476297041) ≤ (258697169 / 1000000000) := by
  have h := checkLog_sound (w := (9226297041 / 71726297041)) (n := 12)
    (lo := (16168573 / 62500000)) (hi := (258697169 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40476297041 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40476297041 / 31250000000) = 1/(31250000000 / 40476297041) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8478 : Bounds (16168573 / 62500000) (258697169 / 1000000000) (Real.log (40476297041 / 31250000000)) := by
  have h := reflection_log_8478_neg
  have he : Real.log (40476297041 / 31250000000) = -Real.log (31250000000 / 40476297041) := by
    rw [show ((40476297041 / 31250000000) : ℝ) = ((31250000000 / 40476297041) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8479_neg : (5182993 / 10000000) ≤ -Real.log (250000000000 / 419792364367) ∧
    -Real.log (250000000000 / 419792364367) ≤ (518299301 / 1000000000) := by
  have h := checkLog_sound (w := (169792364367 / 669792364367)) (n := 12)
    (lo := (5182993 / 10000000)) (hi := (518299301 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((419792364367 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(419792364367 / 250000000000) = 1/(250000000000 / 419792364367) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8479 : Bounds (5182993 / 10000000) (518299301 / 1000000000) (Real.log (419792364367 / 250000000000)) := by
  have h := reflection_log_8479_neg
  have he : Real.log (419792364367 / 250000000000) = -Real.log (250000000000 / 419792364367) := by
    rw [show ((419792364367 / 250000000000) : ℝ) = ((250000000000 / 419792364367) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8480_neg : (12984203 / 25000000) ≤ -Real.log (500000000000 / 840482573727) ∧
    -Real.log (500000000000 / 840482573727) ≤ (519368121 / 1000000000) := by
  have h := checkLog_sound (w := (340482573727 / 1340482573727)) (n := 12)
    (lo := (12984203 / 25000000)) (hi := (519368121 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((840482573727 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(840482573727 / 500000000000) = 1/(500000000000 / 840482573727) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8480 : Bounds (12984203 / 25000000) (519368121 / 1000000000) (Real.log (840482573727 / 500000000000)) := by
  have h := reflection_log_8480_neg
  have he : Real.log (840482573727 / 500000000000) = -Real.log (500000000000 / 840482573727) := by
    rw [show ((840482573727 / 500000000000) : ℝ) = ((500000000000 / 840482573727) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8481_neg : (113368543 / 500000000) ≤ -Real.log (2000 / 2509) ∧
    -Real.log (2000 / 2509) ≤ (226737087 / 1000000000) := by
  have h := checkLog_sound (w := (509 / 4509)) (n := 12)
    (lo := (113368543 / 500000000)) (hi := (226737087 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2509 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2509 / 2000) = 1/(2000 / 2509) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8481 : Bounds (113368543 / 500000000) (226737087 / 1000000000) (Real.log (2509 / 2000)) := by
  have h := reflection_log_8481_neg
  have he : Real.log (2509 / 2000) = -Real.log (2000 / 2509) := by
    rw [show ((2509 / 2000) : ℝ) = ((2000 / 2509) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8482_neg : (18356259 / 62500000) ≤ -Real.log (1491 / 2000) ∧
    -Real.log (1491 / 2000) ≤ (58740029 / 200000000) := by
  have h := checkLog_sound (w := (509 / 3491)) (n := 12)
    (lo := (18356259 / 62500000)) (hi := (58740029 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1491) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1491) = 1/(1491 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8482 : Bounds (-58740029 / 200000000) (-18356259 / 62500000) (Real.log (1491 / 2000)) := by
  have h := reflection_log_8482_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8483_neg : (254467 / 1000000000) ≤ -Real.log (2000000 / 2000509) ∧
    -Real.log (2000000 / 2000509) ≤ (63617 / 250000000) := by
  have h := checkLog_sound (w := (509 / 4000509)) (n := 12)
    (lo := (254467 / 1000000000)) (hi := (63617 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000509 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000509 / 2000000) = 1/(2000000 / 2000509) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8483 : Bounds (254467 / 1000000000) (63617 / 250000000) (Real.log (2000509 / 2000000)) := by
  have h := reflection_log_8483_neg
  have he : Real.log (2000509 / 2000000) = -Real.log (2000000 / 2000509) := by
    rw [show ((2000509 / 2000000) : ℝ) = ((2000000 / 2000509) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8484_neg : (63633 / 250000000) ≤ -Real.log (1999491 / 2000000) ∧
    -Real.log (1999491 / 2000000) ≤ (254533 / 1000000000) := by
  have h := checkLog_sound (w := (509 / 3999491)) (n := 12)
    (lo := (63633 / 250000000)) (hi := (254533 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999491) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999491) = 1/(1999491 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8484 : Bounds (-254533 / 1000000000) (-63633 / 250000000) (Real.log (1999491 / 2000000)) := by
  have h := reflection_log_8484_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8485_neg : (4831319 / 40000000) ≤ -Real.log (50000 / 56419) ∧
    -Real.log (50000 / 56419) ≤ (943617 / 7812500) := by
  have h := checkLog_sound (w := (6419 / 106419)) (n := 12)
    (lo := (4831319 / 40000000)) (hi := (943617 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((56419 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(56419 / 50000) = 1/(50000 / 56419) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8485 : Bounds (4831319 / 40000000) (943617 / 7812500) (Real.log (56419 / 50000)) := by
  have h := reflection_log_8485_neg
  have he : Real.log (56419 / 50000) = -Real.log (50000 / 56419) := by
    rw [show ((56419 / 50000) : ℝ) = ((50000 / 56419) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8486_neg : (137401729 / 1000000000) ≤ -Real.log (43581 / 50000) ∧
    -Real.log (43581 / 50000) ≤ (13740173 / 100000000) := by
  have h := checkLog_sound (w := (6419 / 93581)) (n := 12)
    (lo := (137401729 / 1000000000)) (hi := (13740173 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 43581) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 43581) = 1/(43581 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8486 : Bounds (-13740173 / 100000000) (-137401729 / 1000000000) (Real.log (43581 / 50000)) := by
  have h := reflection_log_8486_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8487_neg : (60617867 / 500000000) ≤ -Real.log (1000000 / 1128891) ∧
    -Real.log (1000000 / 1128891) ≤ (24247147 / 200000000) := by
  have h := checkLog_sound (w := (128891 / 2128891)) (n := 12)
    (lo := (60617867 / 500000000)) (hi := (24247147 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1128891 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1128891 / 1000000) = 1/(1000000 / 1128891) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8487 : Bounds (60617867 / 500000000) (24247147 / 200000000) (Real.log (1128891 / 1000000)) := by
  have h := reflection_log_8487_neg
  have he : Real.log (1128891 / 1000000) = -Real.log (1000000 / 1128891) := by
    rw [show ((1128891 / 1000000) : ℝ) = ((1000000 / 1128891) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8488_neg : (68994083 / 500000000) ≤ -Real.log (871109 / 1000000) ∧
    -Real.log (871109 / 1000000) ≤ (137988167 / 1000000000) := by
  have h := checkLog_sound (w := (128891 / 1871109)) (n := 12)
    (lo := (68994083 / 500000000)) (hi := (137988167 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 871109) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 871109) = 1/(871109 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8488 : Bounds (-137988167 / 1000000000) (-68994083 / 500000000) (Real.log (871109 / 1000000)) := by
  have h := reflection_log_8488_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8489_neg : (16752431 / 1000000000) ≤ -Real.log (983387110119 / 1000000000000) ∧
    -Real.log (983387110119 / 1000000000000) ≤ (1047027 / 62500000) := by
  have h := checkLog_sound (w := (16612889881 / 1983387110119)) (n := 12)
    (lo := (16752431 / 1000000000)) (hi := (1047027 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 983387110119) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 983387110119) = 1/(983387110119 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8489 : Bounds (-1047027 / 62500000) (-16752431 / 1000000000) (Real.log (983387110119 / 1000000000000)) := by
  have h := reflection_log_8489_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8490_neg : (8309377 / 500000000) ≤ -Real.log (2458796439 / 2500000000) ∧
    -Real.log (2458796439 / 2500000000) ≤ (3323751 / 200000000) := by
  have h := checkLog_sound (w := (41203561 / 4958796439)) (n := 12)
    (lo := (8309377 / 500000000)) (hi := (3323751 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000000 / 2458796439) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000000 / 2458796439) = 1/(2458796439 / 2500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8490 : Bounds (-3323751 / 200000000) (-8309377 / 500000000) (Real.log (2458796439 / 2500000000)) := by
  have h := reflection_log_8490_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8491_neg : (51636941 / 200000000) ≤ -Real.log (125000000000 / 161822239049) ∧
    -Real.log (125000000000 / 161822239049) ≤ (129092353 / 500000000) := by
  have h := checkLog_sound (w := (36822239049 / 286822239049)) (n := 12)
    (lo := (51636941 / 200000000)) (hi := (129092353 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((161822239049 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(161822239049 / 125000000000) = 1/(125000000000 / 161822239049) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8491 : Bounds (51636941 / 200000000) (129092353 / 500000000) (Real.log (161822239049 / 125000000000)) := by
  have h := reflection_log_8491_neg
  have he : Real.log (161822239049 / 125000000000) = -Real.log (125000000000 / 161822239049) := by
    rw [show ((161822239049 / 125000000000) : ℝ) = ((125000000000 / 161822239049) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8492_neg : (259223901 / 1000000000) ≤ -Real.log (20000000000 / 25918478629) ∧
    -Real.log (20000000000 / 25918478629) ≤ (129611951 / 500000000) := by
  have h := checkLog_sound (w := (5918478629 / 45918478629)) (n := 12)
    (lo := (259223901 / 1000000000)) (hi := (129611951 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25918478629 / 20000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25918478629 / 20000000000) = 1/(20000000000 / 25918478629) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8492 : Bounds (259223901 / 1000000000) (129611951 / 500000000) (Real.log (25918478629 / 20000000000)) := by
  have h := reflection_log_8492_neg
  have he : Real.log (25918478629 / 20000000000) = -Real.log (20000000000 / 25918478629) := by
    rw [show ((25918478629 / 20000000000) : ℝ) = ((20000000000 / 25918478629) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8493_neg : (12984203 / 25000000) ≤ -Real.log (250000000000 / 420241286863) ∧
    -Real.log (250000000000 / 420241286863) ≤ (519368121 / 1000000000) := by
  have h := checkLog_sound (w := (170241286863 / 670241286863)) (n := 12)
    (lo := (12984203 / 25000000)) (hi := (519368121 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((420241286863 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(420241286863 / 250000000000) = 1/(250000000000 / 420241286863) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8493 : Bounds (12984203 / 25000000) (519368121 / 1000000000) (Real.log (420241286863 / 250000000000)) := by
  have h := reflection_log_8493_neg
  have he : Real.log (420241286863 / 250000000000) = -Real.log (250000000000 / 420241286863) := by
    rw [show ((420241286863 / 250000000000) : ℝ) = ((250000000000 / 420241286863) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8494_neg : (520437231 / 1000000000) ≤ -Real.log (15625000000 / 26293175721) ∧
    -Real.log (15625000000 / 26293175721) ≤ (32527327 / 62500000) := by
  have h := checkLog_sound (w := (10668175721 / 41918175721)) (n := 12)
    (lo := (520437231 / 1000000000)) (hi := (32527327 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((26293175721 / 15625000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(26293175721 / 15625000000) = 1/(15625000000 / 26293175721) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8494 : Bounds (520437231 / 1000000000) (32527327 / 62500000) (Real.log (26293175721 / 15625000000)) := by
  have h := reflection_log_8494_neg
  have he : Real.log (26293175721 / 15625000000) = -Real.log (15625000000 / 26293175721) := by
    rw [show ((26293175721 / 15625000000) : ℝ) = ((15625000000 / 26293175721) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8495_neg : (56783893 / 250000000) ≤ -Real.log (200 / 251) ∧
    -Real.log (200 / 251) ≤ (227135573 / 1000000000) := by
  have h := checkLog_sound (w := (51 / 451)) (n := 12)
    (lo := (56783893 / 250000000)) (hi := (227135573 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((251 / 200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(251 / 200) = 1/(200 / 251) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8495 : Bounds (56783893 / 250000000) (227135573 / 1000000000) (Real.log (251 / 200)) := by
  have h := reflection_log_8495_neg
  have he : Real.log (251 / 200) = -Real.log (200 / 251) := by
    rw [show ((251 / 200) : ℝ) = ((200 / 251) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8496_neg : (14718553 / 50000000) ≤ -Real.log (149 / 200) ∧
    -Real.log (149 / 200) ≤ (294371061 / 1000000000) := by
  have h := checkLog_sound (w := (51 / 349)) (n := 12)
    (lo := (14718553 / 50000000)) (hi := (294371061 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200 / 149) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200 / 149) = 1/(149 / 200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8496 : Bounds (-294371061 / 1000000000) (-14718553 / 50000000) (Real.log (149 / 200)) := by
  have h := reflection_log_8496_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8497_neg : (254967 / 1000000000) ≤ -Real.log (200000 / 200051) ∧
    -Real.log (200000 / 200051) ≤ (31871 / 125000000) := by
  have h := checkLog_sound (w := (51 / 400051)) (n := 12)
    (lo := (254967 / 1000000000)) (hi := (31871 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200051 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200051 / 200000) = 1/(200000 / 200051) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8497 : Bounds (254967 / 1000000000) (31871 / 125000000) (Real.log (200051 / 200000)) := by
  have h := reflection_log_8497_neg
  have he : Real.log (200051 / 200000) = -Real.log (200000 / 200051) := by
    rw [show ((200051 / 200000) : ℝ) = ((200000 / 200051) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8498_neg : (31879 / 125000000) ≤ -Real.log (199949 / 200000) ∧
    -Real.log (199949 / 200000) ≤ (255033 / 1000000000) := by
  have h := checkLog_sound (w := (51 / 399949)) (n := 12)
    (lo := (31879 / 125000000)) (hi := (255033 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 199949) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 199949) = 1/(199949 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8498 : Bounds (-255033 / 1000000000) (-31879 / 125000000) (Real.log (199949 / 200000)) := by
  have h := reflection_log_8498_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8499_neg : (60506241 / 500000000) ≤ -Real.log (1000000 / 1128639) ∧
    -Real.log (1000000 / 1128639) ≤ (121012483 / 1000000000) := by
  have h := checkLog_sound (w := (128639 / 2128639)) (n := 12)
    (lo := (60506241 / 500000000)) (hi := (121012483 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1128639 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1128639 / 1000000) = 1/(1000000 / 1128639) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8499 : Bounds (60506241 / 500000000) (121012483 / 1000000000) (Real.log (1128639 / 1000000)) := by
  have h := reflection_log_8499_neg
  have he : Real.log (1128639 / 1000000) = -Real.log (1000000 / 1128639) := by
    rw [show ((1128639 / 1000000) : ℝ) = ((1000000 / 1128639) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8500_neg : (137698921 / 1000000000) ≤ -Real.log (871361 / 1000000) ∧
    -Real.log (871361 / 1000000) ≤ (68849461 / 500000000) := by
  have h := checkLog_sound (w := (128639 / 1871361)) (n := 12)
    (lo := (137698921 / 1000000000)) (hi := (68849461 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 871361) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 871361) = 1/(871361 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8500 : Bounds (-68849461 / 500000000) (-137698921 / 1000000000) (Real.log (871361 / 1000000)) := by
  have h := reflection_log_8500_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8501_neg : (60733011 / 500000000) ≤ -Real.log (1000000 / 1129151) ∧
    -Real.log (1000000 / 1129151) ≤ (121466023 / 1000000000) := by
  have h := checkLog_sound (w := (129151 / 2129151)) (n := 12)
    (lo := (60733011 / 500000000)) (hi := (121466023 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1129151 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1129151 / 1000000) = 1/(1000000 / 1129151) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8501 : Bounds (60733011 / 500000000) (121466023 / 1000000000) (Real.log (1129151 / 1000000)) := by
  have h := reflection_log_8501_neg
  have he : Real.log (1129151 / 1000000) = -Real.log (1000000 / 1129151) := by
    rw [show ((1129151 / 1000000) : ℝ) = ((1000000 / 1129151) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8502_neg : (138286681 / 1000000000) ≤ -Real.log (870849 / 1000000) ∧
    -Real.log (870849 / 1000000) ≤ (69143341 / 500000000) := by
  have h := checkLog_sound (w := (129151 / 1870849)) (n := 12)
    (lo := (138286681 / 1000000000)) (hi := (69143341 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 870849) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 870849) = 1/(870849 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8502 : Bounds (-69143341 / 500000000) (-138286681 / 1000000000) (Real.log (870849 / 1000000)) := by
  have h := reflection_log_8502_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8503_neg : (8410329 / 500000000) ≤ -Real.log (983320019199 / 1000000000000) ∧
    -Real.log (983320019199 / 1000000000000) ≤ (16820659 / 1000000000) := by
  have h := checkLog_sound (w := (16679980801 / 1983320019199)) (n := 12)
    (lo := (8410329 / 500000000)) (hi := (16820659 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 983320019199) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 983320019199) = 1/(983320019199 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8503 : Bounds (-16820659 / 1000000000) (-8410329 / 500000000) (Real.log (983320019199 / 1000000000000)) := by
  have h := reflection_log_8503_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8504_neg : (16686439 / 1000000000) ≤ -Real.log (983452007679 / 1000000000000) ∧
    -Real.log (983452007679 / 1000000000000) ≤ (417161 / 25000000) := by
  have h := checkLog_sound (w := (16547992321 / 1983452007679)) (n := 12)
    (lo := (16686439 / 1000000000)) (hi := (417161 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 983452007679) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 983452007679) = 1/(983452007679 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8504 : Bounds (-417161 / 25000000) (-16686439 / 1000000000) (Real.log (983452007679 / 1000000000000)) := by
  have h := reflection_log_8504_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8505_neg : (258711403 / 1000000000) ≤ -Real.log (500000000000 / 647629971963) ∧
    -Real.log (500000000000 / 647629971963) ≤ (64677851 / 250000000) := by
  have h := checkLog_sound (w := (147629971963 / 1147629971963)) (n := 12)
    (lo := (258711403 / 1000000000)) (hi := (64677851 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((647629971963 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(647629971963 / 500000000000) = 1/(500000000000 / 647629971963) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8505 : Bounds (258711403 / 1000000000) (64677851 / 250000000) (Real.log (647629971963 / 500000000000)) := by
  have h := reflection_log_8505_neg
  have he : Real.log (647629971963 / 500000000000) = -Real.log (500000000000 / 647629971963) := by
    rw [show ((647629971963 / 500000000000) : ℝ) = ((500000000000 / 647629971963) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8506_neg : (1014659 / 3906250) ≤ -Real.log (125000000000 / 162076175089) ∧
    -Real.log (125000000000 / 162076175089) ≤ (51950541 / 200000000) := by
  have h := checkLog_sound (w := (37076175089 / 287076175089)) (n := 12)
    (lo := (1014659 / 3906250)) (hi := (51950541 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((162076175089 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(162076175089 / 125000000000) = 1/(125000000000 / 162076175089) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8506 : Bounds (1014659 / 3906250) (51950541 / 200000000) (Real.log (162076175089 / 125000000000)) := by
  have h := reflection_log_8506_neg
  have he : Real.log (162076175089 / 125000000000) = -Real.log (125000000000 / 162076175089) := by
    rw [show ((162076175089 / 125000000000) : ℝ) = ((125000000000 / 162076175089) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8507_neg : (520437231 / 1000000000) ≤ -Real.log (500000000000 / 841381623071) ∧
    -Real.log (500000000000 / 841381623071) ≤ (32527327 / 62500000) := by
  have h := checkLog_sound (w := (341381623071 / 1341381623071)) (n := 12)
    (lo := (520437231 / 1000000000)) (hi := (32527327 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((841381623071 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(841381623071 / 500000000000) = 1/(500000000000 / 841381623071) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8507 : Bounds (520437231 / 1000000000) (32527327 / 62500000) (Real.log (841381623071 / 500000000000)) := by
  have h := reflection_log_8507_neg
  have he : Real.log (841381623071 / 500000000000) = -Real.log (500000000000 / 841381623071) := by
    rw [show ((841381623071 / 500000000000) : ℝ) = ((500000000000 / 841381623071) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8508_neg : (521506633 / 1000000000) ≤ -Real.log (100000000000 / 168456375839) ∧
    -Real.log (100000000000 / 168456375839) ≤ (260753317 / 500000000) := by
  have h := checkLog_sound (w := (68456375839 / 268456375839)) (n := 12)
    (lo := (521506633 / 1000000000)) (hi := (260753317 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((168456375839 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(168456375839 / 100000000000) = 1/(100000000000 / 168456375839) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8508 : Bounds (521506633 / 1000000000) (260753317 / 500000000) (Real.log (168456375839 / 100000000000)) := by
  have h := reflection_log_8508_neg
  have he : Real.log (168456375839 / 100000000000) = -Real.log (100000000000 / 168456375839) := by
    rw [show ((168456375839 / 100000000000) : ℝ) = ((100000000000 / 168456375839) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8509_neg : (227533899 / 1000000000) ≤ -Real.log (2000 / 2511) ∧
    -Real.log (2000 / 2511) ≤ (2275339 / 10000000) := by
  have h := checkLog_sound (w := (511 / 4511)) (n := 12)
    (lo := (227533899 / 1000000000)) (hi := (2275339 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2511 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2511 / 2000) = 1/(2000 / 2511) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8509 : Bounds (227533899 / 1000000000) (2275339 / 10000000) (Real.log (2511 / 2000)) := by
  have h := reflection_log_8509_neg
  have he : Real.log (2511 / 2000) = -Real.log (2000 / 2511) := by
    rw [show ((2511 / 2000) : ℝ) = ((2000 / 2511) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8510_neg : (147521213 / 500000000) ≤ -Real.log (1489 / 2000) ∧
    -Real.log (1489 / 2000) ≤ (295042427 / 1000000000) := by
  have h := checkLog_sound (w := (511 / 3489)) (n := 12)
    (lo := (147521213 / 500000000)) (hi := (295042427 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1489) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1489) = 1/(1489 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8510 : Bounds (-295042427 / 1000000000) (-147521213 / 500000000) (Real.log (1489 / 2000)) := by
  have h := reflection_log_8510_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8511_neg : (255467 / 1000000000) ≤ -Real.log (2000000 / 2000511) ∧
    -Real.log (2000000 / 2000511) ≤ (63867 / 250000000) := by
  have h := checkLog_sound (w := (511 / 4000511)) (n := 12)
    (lo := (255467 / 1000000000)) (hi := (63867 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000511 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000511 / 2000000) = 1/(2000000 / 2000511) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8511 : Bounds (255467 / 1000000000) (63867 / 250000000) (Real.log (2000511 / 2000000)) := by
  have h := reflection_log_8511_neg
  have he : Real.log (2000511 / 2000000) = -Real.log (2000000 / 2000511) := by
    rw [show ((2000511 / 2000000) : ℝ) = ((2000000 / 2000511) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily
