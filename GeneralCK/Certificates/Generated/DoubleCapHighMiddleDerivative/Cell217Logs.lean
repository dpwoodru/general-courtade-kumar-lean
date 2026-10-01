import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell217
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

theorem reflection_log_1_neg : (40055049 / 125000000) ≤ -Real.log (2560 / 3527) ∧
    -Real.log (2560 / 3527) ≤ (320440393 / 1000000000) := by
  have h := checkLog_sound (w := (967 / 6087)) (n := 12)
    (lo := (40055049 / 125000000)) (hi := (320440393 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3527 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3527 / 2560) = 1/(2560 / 3527) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (40055049 / 125000000) (320440393 / 1000000000) (Real.log (3527 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3527 / 2560) = -Real.log (2560 / 3527) := by
    rw [show ((3527 / 2560) : ℝ) = ((2560 / 3527) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (474388227 / 1000000000) ≤ -Real.log (1593 / 2560) ∧
    -Real.log (1593 / 2560) ≤ (118597057 / 250000000) := by
  have h := checkLog_sound (w := (967 / 4153)) (n := 12)
    (lo := (474388227 / 1000000000)) (hi := (118597057 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1593) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1593) = 1/(1593 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-118597057 / 250000000) (-474388227 / 1000000000) (Real.log (1593 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (320015011 / 1000000000) ≤ -Real.log (5120 / 7051) ∧
    -Real.log (5120 / 7051) ≤ (80003753 / 250000000) := by
  have h := checkLog_sound (w := (1931 / 12171)) (n := 12)
    (lo := (320015011 / 1000000000)) (hi := (80003753 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7051 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7051 / 5120) = 1/(5120 / 7051) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (320015011 / 1000000000) (80003753 / 250000000) (Real.log (7051 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (7051 / 5120) = -Real.log (5120 / 7051) := by
    rw [show ((7051 / 5120) : ℝ) = ((5120 / 7051) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (473447051 / 1000000000) ≤ -Real.log (3189 / 5120) ∧
    -Real.log (3189 / 5120) ≤ (118361763 / 250000000) := by
  have h := checkLog_sound (w := (1931 / 8309)) (n := 12)
    (lo := (473447051 / 1000000000)) (hi := (118361763 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3189) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3189) = 1/(3189 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-118361763 / 250000000) (-473447051 / 1000000000) (Real.log (3189 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (237728669 / 1000000000) ≤ -Real.log (200000 / 253673) ∧
    -Real.log (200000 / 253673) ≤ (23772867 / 100000000) := by
  have h := checkLog_sound (w := (53673 / 453673)) (n := 12)
    (lo := (237728669 / 1000000000)) (hi := (23772867 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((253673 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(253673 / 200000) = 1/(200000 / 253673) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (237728669 / 1000000000) (23772867 / 100000000) (Real.log (253673 / 200000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (253673 / 200000) = -Real.log (200000 / 253673) := by
    rw [show ((253673 / 200000) : ℝ) = ((200000 / 253673) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (312473523 / 1000000000) ≤ -Real.log (146327 / 200000) ∧
    -Real.log (146327 / 200000) ≤ (78118381 / 250000000) := by
  have h := checkLog_sound (w := (53673 / 346327)) (n := 12)
    (lo := (312473523 / 1000000000)) (hi := (78118381 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 146327) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 146327) = 1/(146327 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-78118381 / 250000000) (-312473523 / 1000000000) (Real.log (146327 / 200000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (119031451 / 500000000) ≤ -Real.log (1000000 / 1268789) ∧
    -Real.log (1000000 / 1268789) ≤ (238062903 / 1000000000) := by
  have h := checkLog_sound (w := (268789 / 2268789)) (n := 12)
    (lo := (119031451 / 500000000)) (hi := (238062903 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1268789 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1268789 / 1000000) = 1/(1000000 / 1268789) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (119031451 / 500000000) (238062903 / 1000000000) (Real.log (1268789 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1268789 / 1000000) = -Real.log (1000000 / 1268789) := by
    rw [show ((1268789 / 1000000) : ℝ) = ((1000000 / 1268789) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (62610643 / 200000000) ≤ -Real.log (731211 / 1000000) ∧
    -Real.log (731211 / 1000000) ≤ (9782913 / 31250000) := by
  have h := checkLog_sound (w := (268789 / 1731211)) (n := 12)
    (lo := (62610643 / 200000000)) (hi := (9782913 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 731211) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 731211) = 1/(731211 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-9782913 / 31250000) (-62610643 / 200000000) (Real.log (731211 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (35398979 / 200000000) ≤ -Real.log (8000 / 9549) ∧
    -Real.log (8000 / 9549) ≤ (11062181 / 62500000) := by
  have h := checkLog_sound (w := (1549 / 17549)) (n := 12)
    (lo := (35398979 / 200000000)) (hi := (11062181 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9549 / 8000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(9549 / 8000) = 1/(8000 / 9549) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (35398979 / 200000000) (11062181 / 62500000) (Real.log (9549 / 8000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (9549 / 8000) = -Real.log (8000 / 9549) := by
    rw [show ((9549 / 8000) : ℝ) = ((8000 / 9549) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (13450399 / 62500000) ≤ -Real.log (6451 / 8000) ∧
    -Real.log (6451 / 8000) ≤ (43041277 / 200000000) := by
  have h := checkLog_sound (w := (1549 / 14451)) (n := 12)
    (lo := (13450399 / 62500000)) (hi := (43041277 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8000 / 6451) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(8000 / 6451) = 1/(6451 / 8000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-43041277 / 200000000) (-13450399 / 62500000) (Real.log (6451 / 8000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (7090451 / 40000000) ≤ -Real.log (1000000 / 1193943) ∧
    -Real.log (1000000 / 1193943) ≤ (44315319 / 250000000) := by
  have h := checkLog_sound (w := (193943 / 2193943)) (n := 12)
    (lo := (7090451 / 40000000)) (hi := (44315319 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1193943 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1193943 / 1000000) = 1/(1000000 / 1193943) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (7090451 / 40000000) (44315319 / 250000000) (Real.log (1193943 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1193943 / 1000000) = -Real.log (1000000 / 1193943) := by
    rw [show ((1193943 / 1000000) : ℝ) = ((1000000 / 1193943) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (215600819 / 1000000000) ≤ -Real.log (806057 / 1000000) ∧
    -Real.log (806057 / 1000000) ≤ (10780041 / 50000000) := by
  have h := checkLog_sound (w := (193943 / 1806057)) (n := 12)
    (lo := (215600819 / 1000000000)) (hi := (10780041 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 806057) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 806057) = 1/(806057 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-10780041 / 50000000) (-215600819 / 1000000000) (Real.log (806057 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (396731031 / 500000000) ≤ -Real.log (62500000000 / 138189871433) ∧
    -Real.log (62500000000 / 138189871433) ≤ (49591379 / 62500000) := by
  have h := checkLog_sound (w := (13189871433 / 263189871433)) (n := 12)
    (lo := (50157441 / 500000000)) (hi := (100314883 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((138189871433 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(138189871433 / 125000000000) = 1/(62500000000 / 138189871433) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (396731031 / 500000000) (49591379 / 62500000) (Real.log (138189871433 / 62500000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (138189871433 / 62500000000) = -Real.log (62500000000 / 138189871433) := by
    rw [show ((138189871433 / 62500000000) : ℝ) = ((62500000000 / 138189871433) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (794828619 / 1000000000) ≤ -Real.log (250000000000 / 553515379787) ∧
    -Real.log (250000000000 / 553515379787) ≤ (794828621 / 1000000000) := by
  have h := checkLog_sound (w := (53515379787 / 1053515379787)) (n := 12)
    (lo := (101681439 / 1000000000)) (hi := (635509 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((553515379787 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(553515379787 / 500000000000) = 1/(250000000000 / 553515379787) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (794828619 / 1000000000) (794828621 / 1000000000) (Real.log (553515379787 / 250000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (553515379787 / 250000000000) = -Real.log (250000000000 / 553515379787) := by
    rw [show ((553515379787 / 250000000000) : ℝ) = ((250000000000 / 553515379787) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (34387637 / 62500000) ≤ -Real.log (500000000000 / 866801752239) ∧
    -Real.log (500000000000 / 866801752239) ≤ (550202193 / 1000000000) := by
  have h := checkLog_sound (w := (366801752239 / 1366801752239)) (n := 12)
    (lo := (34387637 / 62500000)) (hi := (550202193 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((866801752239 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(866801752239 / 500000000000) = 1/(500000000000 / 866801752239) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (34387637 / 62500000) (550202193 / 1000000000) (Real.log (866801752239 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (866801752239 / 500000000000) = -Real.log (500000000000 / 866801752239) := by
    rw [show ((866801752239 / 500000000000) : ℝ) = ((500000000000 / 866801752239) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (551116117 / 1000000000) ≤ -Real.log (100000000000 / 173518861177) ∧
    -Real.log (100000000000 / 173518861177) ≤ (275558059 / 500000000) := by
  have h := checkLog_sound (w := (73518861177 / 273518861177)) (n := 12)
    (lo := (551116117 / 1000000000)) (hi := (275558059 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((173518861177 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(173518861177 / 100000000000) = 1/(100000000000 / 173518861177) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (551116117 / 1000000000) (275558059 / 500000000) (Real.log (173518861177 / 100000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (173518861177 / 100000000000) = -Real.log (100000000000 / 173518861177) := by
    rw [show ((173518861177 / 100000000000) : ℝ) = ((100000000000 / 173518861177) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (392201279 / 1000000000) ≤ -Real.log (62500000000 / 92514726399) ∧
    -Real.log (62500000000 / 92514726399) ≤ (1225629 / 3125000) := by
  have h := checkLog_sound (w := (30014726399 / 155014726399)) (n := 12)
    (lo := (392201279 / 1000000000)) (hi := (1225629 / 3125000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((92514726399 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(92514726399 / 62500000000) = 1/(62500000000 / 92514726399) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (392201279 / 1000000000) (1225629 / 3125000) (Real.log (92514726399 / 62500000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (92514726399 / 62500000000) = -Real.log (62500000000 / 92514726399) := by
    rw [show ((92514726399 / 62500000000) : ℝ) = ((62500000000 / 92514726399) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (196431047 / 500000000) ≤ -Real.log (125000000000 / 185151763461) ∧
    -Real.log (125000000000 / 185151763461) ≤ (78572419 / 200000000) := by
  have h := checkLog_sound (w := (60151763461 / 310151763461)) (n := 12)
    (lo := (196431047 / 500000000)) (hi := (78572419 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((185151763461 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(185151763461 / 125000000000) = 1/(125000000000 / 185151763461) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (196431047 / 500000000) (78572419 / 200000000) (Real.log (185151763461 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (185151763461 / 125000000000) = -Real.log (125000000000 / 185151763461) := by
    rw [show ((185151763461 / 125000000000) : ℝ) = ((125000000000 / 185151763461) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (4792443 / 125000000) ≤ -Real.log (962386112751 / 1000000000000) ∧
    -Real.log (962386112751 / 1000000000000) ≤ (7667909 / 200000000) := by
  have h := checkLog_sound (w := (37613887249 / 1962386112751)) (n := 12)
    (lo := (4792443 / 125000000)) (hi := (7667909 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 962386112751) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 962386112751) = 1/(962386112751 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-7667909 / 200000000) (-4792443 / 125000000) (Real.log (962386112751 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (1194109 / 31250000) ≤ -Real.log (61600599 / 64000000) ∧
    -Real.log (61600599 / 64000000) ≤ (38211489 / 1000000000) := by
  have h := checkLog_sound (w := (2399401 / 125600599)) (n := 12)
    (lo := (1194109 / 31250000)) (hi := (38211489 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((64000000 / 61600599) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(64000000 / 61600599) = 1/(61600599 / 64000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-38211489 / 1000000000) (-1194109 / 31250000) (Real.log (61600599 / 64000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell217
