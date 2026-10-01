import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0062
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

theorem reflection_log_1_neg : (18240293 / 50000000) ≤ -Real.log (2560 / 3687) ∧
    -Real.log (2560 / 3687) ≤ (364805861 / 1000000000) := by
  have h := checkLog_sound (w := (1127 / 6247)) (n := 12)
    (lo := (18240293 / 50000000)) (hi := (364805861 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3687 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3687 / 2560) = 1/(2560 / 3687) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (18240293 / 50000000) (364805861 / 1000000000) (Real.log (3687 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3687 / 2560) = -Real.log (2560 / 3687) := by
    rw [show ((3687 / 2560) : ℝ) = ((2560 / 3687) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (580237109 / 1000000000) ≤ -Real.log (1433 / 2560) ∧
    -Real.log (1433 / 2560) ≤ (58023711 / 100000000) := by
  have h := checkLog_sound (w := (1127 / 3993)) (n := 12)
    (lo := (580237109 / 1000000000)) (hi := (58023711 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1433) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1433) = 1/(1433 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-58023711 / 100000000) (-580237109 / 1000000000) (Real.log (1433 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (363991859 / 1000000000) ≤ -Real.log (640 / 921) ∧
    -Real.log (640 / 921) ≤ (18199593 / 50000000) := by
  have h := checkLog_sound (w := (281 / 1561)) (n := 12)
    (lo := (363991859 / 1000000000)) (hi := (18199593 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((921 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(921 / 640) = 1/(640 / 921) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (363991859 / 1000000000) (18199593 / 50000000) (Real.log (921 / 640)) := by
  have h := reflection_log_3_neg
  have he : Real.log (921 / 640) = -Real.log (640 / 921) := by
    rw [show ((921 / 640) : ℝ) = ((640 / 921) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (578145787 / 1000000000) ≤ -Real.log (359 / 640) ∧
    -Real.log (359 / 640) ≤ (144536447 / 250000000) := by
  have h := checkLog_sound (w := (281 / 999)) (n := 12)
    (lo := (578145787 / 1000000000)) (hi := (144536447 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 359) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 359) = 1/(359 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-144536447 / 250000000) (-578145787 / 1000000000) (Real.log (359 / 640)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (15788027 / 25000000) ≤ -Real.log (1280 / 2407) ∧
    -Real.log (1280 / 2407) ≤ (631521081 / 1000000000) := by
  have h := checkLog_sound (w := (1127 / 3687)) (n := 12)
    (lo := (15788027 / 25000000)) (hi := (631521081 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2407 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2407 / 1280) = 1/(1280 / 2407) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (15788027 / 25000000) (631521081 / 1000000000) (Real.log (2407 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2407 / 1280) = -Real.log (1280 / 2407) := by
    rw [show ((2407 / 1280) : ℝ) = ((1280 / 2407) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (2124177433 / 1000000000) ≤ -Real.log (153 / 1280) ∧
    -Real.log (153 / 1280) ≤ (2124177437 / 1000000000) := by
  have h := checkLog_sound (w := (7 / 313)) (n := 12)
    (lo := (44735893 / 1000000000)) (hi := (22367947 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 153) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(160 / 153) = 1/(153 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-2124177437 / 1000000000) (-2124177433 / 1000000000) (Real.log (153 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (315136969 / 500000000) ≤ -Real.log (320 / 601) ∧
    -Real.log (320 / 601) ≤ (630273939 / 1000000000) := by
  have h := checkLog_sound (w := (281 / 921)) (n := 12)
    (lo := (315136969 / 500000000)) (hi := (630273939 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((601 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(601 / 320) = 1/(320 / 601) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (315136969 / 500000000) (630273939 / 1000000000) (Real.log (601 / 320)) := by
  have h := reflection_log_7_neg
  have he : Real.log (601 / 320) = -Real.log (320 / 601) := by
    rw [show ((601 / 320) : ℝ) = ((320 / 601) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (2104759347 / 1000000000) ≤ -Real.log (39 / 320) ∧
    -Real.log (39 / 320) ≤ (2104759351 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 79)) (n := 12)
    (lo := (25317807 / 1000000000)) (hi := (1582363 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40 / 39) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(40 / 39) = 1/(39 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-2104759351 / 1000000000) (-2104759347 / 1000000000) (Real.log (39 / 320)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (50262993 / 100000000) ≤ -Real.log (1000000 / 1653063) ∧
    -Real.log (1000000 / 1653063) ≤ (502629931 / 1000000000) := by
  have h := checkLog_sound (w := (653063 / 2653063)) (n := 12)
    (lo := (50262993 / 100000000)) (hi := (502629931 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1653063 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1653063 / 1000000) = 1/(1000000 / 1653063) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (50262993 / 100000000) (502629931 / 1000000000) (Real.log (1653063 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1653063 / 1000000) = -Real.log (1000000 / 1653063) := by
    rw [show ((1653063 / 1000000) : ℝ) = ((1000000 / 1653063) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (1058612071 / 1000000000) ≤ -Real.log (346937 / 1000000) ∧
    -Real.log (346937 / 1000000) ≤ (1058612073 / 1000000000) := by
  have h := checkLog_sound (w := (153063 / 846937)) (n := 12)
    (lo := (365464891 / 1000000000)) (hi := (91366223 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 346937) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 346937) = 1/(346937 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-1058612073 / 1000000000) (-1058612071 / 1000000000) (Real.log (346937 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (503873513 / 1000000000) ≤ -Real.log (12500 / 20689) ∧
    -Real.log (12500 / 20689) ≤ (251936757 / 500000000) := by
  have h := checkLog_sound (w := (8189 / 33189)) (n := 12)
    (lo := (503873513 / 1000000000)) (hi := (251936757 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20689 / 12500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20689 / 12500) = 1/(12500 / 20689) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (503873513 / 1000000000) (251936757 / 500000000) (Real.log (20689 / 12500)) := by
  have h := reflection_log_11_neg
  have he : Real.log (20689 / 12500) = -Real.log (12500 / 20689) := by
    rw [show ((20689 / 12500) : ℝ) = ((12500 / 20689) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1064558747 / 1000000000) ≤ -Real.log (4311 / 12500) ∧
    -Real.log (4311 / 12500) ≤ (1064558749 / 1000000000) := by
  have h := checkLog_sound (w := (1939 / 10561)) (n := 12)
    (lo := (371411567 / 1000000000)) (hi := (23213223 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6250 / 4311) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(6250 / 4311) = 1/(4311 / 12500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1064558749 / 1000000000) (-1064558747 / 1000000000) (Real.log (4311 / 12500)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (210301639 / 500000000) ≤ -Real.log (3125 / 4759) ∧
    -Real.log (3125 / 4759) ≤ (420603279 / 1000000000) := by
  have h := checkLog_sound (w := (817 / 3942)) (n := 12)
    (lo := (210301639 / 500000000)) (hi := (420603279 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4759 / 3125) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4759 / 3125) = 1/(3125 / 4759) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (210301639 / 500000000) (420603279 / 1000000000) (Real.log (4759 / 3125)) := by
  have h := reflection_log_13_neg
  have he : Real.log (4759 / 3125) = -Real.log (3125 / 4759) := by
    rw [show ((4759 / 3125) : ℝ) = ((3125 / 4759) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (369993623 / 500000000) ≤ -Real.log (1491 / 3125) ∧
    -Real.log (1491 / 3125) ≤ (46249203 / 62500000) := by
  have h := checkLog_sound (w := (143 / 6107)) (n := 12)
    (lo := (23420033 / 500000000)) (hi := (46840067 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3125 / 2982) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(3125 / 2982) = 1/(1491 / 3125) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-46249203 / 62500000) (-369993623 / 500000000) (Real.log (1491 / 3125)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (421964901 / 1000000000) ≤ -Real.log (200000 / 304991) ∧
    -Real.log (200000 / 304991) ≤ (210982451 / 500000000) := by
  have h := checkLog_sound (w := (104991 / 504991)) (n := 12)
    (lo := (421964901 / 1000000000)) (hi := (210982451 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((304991 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(304991 / 200000) = 1/(200000 / 304991) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (421964901 / 1000000000) (210982451 / 500000000) (Real.log (304991 / 200000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (304991 / 200000) = -Real.log (200000 / 304991) := by
    rw [show ((304991 / 200000) : ℝ) = ((200000 / 304991) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (372172871 / 500000000) ≤ -Real.log (95009 / 200000) ∧
    -Real.log (95009 / 200000) ≤ (46521609 / 62500000) := by
  have h := checkLog_sound (w := (4991 / 195009)) (n := 12)
    (lo := (25599281 / 500000000)) (hi := (51198563 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 95009) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(100000 / 95009) = 1/(95009 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-46521609 / 62500000) (-372172871 / 500000000) (Real.log (95009 / 200000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1561242001 / 1000000000) ≤ -Real.log (500000000000 / 2382367692117) ∧
    -Real.log (500000000000 / 2382367692117) ≤ (390310501 / 250000000) := by
  have h := checkLog_sound (w := (382367692117 / 4382367692117)) (n := 12)
    (lo := (174947641 / 1000000000)) (hi := (87473821 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2382367692117 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2382367692117 / 2000000000000) = 1/(500000000000 / 2382367692117) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1561242001 / 1000000000) (390310501 / 250000000) (Real.log (2382367692117 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (2382367692117 / 500000000000) = -Real.log (500000000000 / 2382367692117) := by
    rw [show ((2382367692117 / 500000000000) : ℝ) = ((500000000000 / 2382367692117) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1568432261 / 1000000000) ≤ -Real.log (31250000000 / 149972454187) ∧
    -Real.log (31250000000 / 149972454187) ≤ (196054033 / 125000000) := by
  have h := checkLog_sound (w := (24972454187 / 274972454187)) (n := 12)
    (lo := (182137901 / 1000000000)) (hi := (91068951 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((149972454187 / 125000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(149972454187 / 125000000000) = 1/(31250000000 / 149972454187) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1568432261 / 1000000000) (196054033 / 125000000) (Real.log (149972454187 / 31250000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (149972454187 / 31250000000) = -Real.log (31250000000 / 149972454187) := by
    rw [show ((149972454187 / 31250000000) : ℝ) = ((31250000000 / 149972454187) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (46423621 / 40000000) ≤ -Real.log (500000000000 / 1595908786049) ∧
    -Real.log (500000000000 / 1595908786049) ≤ (1160590527 / 1000000000) := by
  have h := checkLog_sound (w := (595908786049 / 2595908786049)) (n := 12)
    (lo := (93488669 / 200000000)) (hi := (233721673 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1595908786049 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1595908786049 / 1000000000000) = 1/(500000000000 / 1595908786049) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (46423621 / 40000000) (1160590527 / 1000000000) (Real.log (1595908786049 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (1595908786049 / 500000000000) = -Real.log (500000000000 / 1595908786049) := by
    rw [show ((1595908786049 / 500000000000) : ℝ) = ((500000000000 / 1595908786049) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (1166310643 / 1000000000) ≤ -Real.log (100000000000 / 321012746161) ∧
    -Real.log (100000000000 / 321012746161) ≤ (233262129 / 200000000) := by
  have h := checkLog_sound (w := (121012746161 / 521012746161)) (n := 12)
    (lo := (473163463 / 1000000000)) (hi := (59145433 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((321012746161 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(321012746161 / 200000000000) = 1/(100000000000 / 321012746161) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (1166310643 / 1000000000) (233262129 / 200000000) (Real.log (321012746161 / 100000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (321012746161 / 100000000000) = -Real.log (100000000000 / 321012746161) := by
    rw [show ((321012746161 / 100000000000) : ℝ) = ((100000000000 / 321012746161) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0062
