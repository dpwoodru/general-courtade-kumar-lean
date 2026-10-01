import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0426
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

theorem reflection_log_1_neg : (96986087 / 500000000) ≤ -Real.log (640 / 777) ∧
    -Real.log (640 / 777) ≤ (7758887 / 40000000) := by
  have h := checkLog_sound (w := (137 / 1417)) (n := 12)
    (lo := (96986087 / 500000000)) (hi := (7758887 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((777 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(777 / 640) = 1/(640 / 777) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (96986087 / 500000000) (7758887 / 40000000) (Real.log (777 / 640)) := by
  have h := reflection_log_1_neg
  have he : Real.log (777 / 640) = -Real.log (640 / 777) := by
    rw [show ((777 / 640) : ℝ) = ((640 / 777) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (120439003 / 500000000) ≤ -Real.log (503 / 640) ∧
    -Real.log (503 / 640) ≤ (240878007 / 1000000000) := by
  have h := checkLog_sound (w := (137 / 1143)) (n := 12)
    (lo := (120439003 / 500000000)) (hi := (240878007 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 503) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 503) = 1/(503 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-240878007 / 1000000000) (-120439003 / 500000000) (Real.log (503 / 640)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (12108177 / 62500000) ≤ -Real.log (10240 / 12429) ∧
    -Real.log (10240 / 12429) ≤ (193730833 / 1000000000) := by
  have h := checkLog_sound (w := (2189 / 22669)) (n := 12)
    (lo := (12108177 / 62500000)) (hi := (193730833 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12429 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12429 / 10240) = 1/(10240 / 12429) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (12108177 / 62500000) (193730833 / 1000000000) (Real.log (12429 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12429 / 10240) = -Real.log (10240 / 12429) := by
    rw [show ((12429 / 10240) : ℝ) = ((10240 / 12429) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (7515791 / 31250000) ≤ -Real.log (8051 / 10240) ∧
    -Real.log (8051 / 10240) ≤ (240505313 / 1000000000) := by
  have h := checkLog_sound (w := (2189 / 18291)) (n := 12)
    (lo := (7515791 / 31250000)) (hi := (240505313 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 8051) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 8051) = 1/(8051 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-240505313 / 1000000000) (-7515791 / 31250000) (Real.log (8051 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (71272479 / 200000000) ≤ -Real.log (320 / 457) ∧
    -Real.log (320 / 457) ≤ (89090599 / 250000000) := by
  have h := checkLog_sound (w := (137 / 777)) (n := 12)
    (lo := (71272479 / 200000000)) (hi := (89090599 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((457 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(457 / 320) = 1/(320 / 457) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (71272479 / 200000000) (89090599 / 250000000) (Real.log (457 / 320)) := by
  have h := reflection_log_5_neg
  have he : Real.log (457 / 320) = -Real.log (320 / 457) := by
    rw [show ((457 / 320) : ℝ) = ((320 / 457) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (279417421 / 500000000) ≤ -Real.log (183 / 320) ∧
    -Real.log (183 / 320) ≤ (558834843 / 1000000000) := by
  have h := checkLog_sound (w := (137 / 503)) (n := 12)
    (lo := (279417421 / 500000000)) (hi := (558834843 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 183) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(320 / 183) = 1/(183 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-558834843 / 1000000000) (-279417421 / 500000000) (Real.log (183 / 320)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (177976013 / 500000000) ≤ -Real.log (5120 / 7309) ∧
    -Real.log (5120 / 7309) ≤ (355952027 / 1000000000) := by
  have h := checkLog_sound (w := (2189 / 12429)) (n := 12)
    (lo := (177976013 / 500000000)) (hi := (355952027 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7309 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7309 / 5120) = 1/(5120 / 7309) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (177976013 / 500000000) (355952027 / 1000000000) (Real.log (7309 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (7309 / 5120) = -Real.log (5120 / 7309) := by
    rw [show ((7309 / 5120) : ℝ) = ((5120 / 7309) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (557810777 / 1000000000) ≤ -Real.log (2931 / 5120) ∧
    -Real.log (2931 / 5120) ≤ (278905389 / 500000000) := by
  have h := checkLog_sound (w := (2189 / 8051)) (n := 12)
    (lo := (557810777 / 1000000000)) (hi := (278905389 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2931) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2931) = 1/(2931 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-278905389 / 500000000) (-557810777 / 1000000000) (Real.log (2931 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (133029101 / 500000000) ≤ -Real.log (1000000 / 1304811) ∧
    -Real.log (1000000 / 1304811) ≤ (266058203 / 1000000000) := by
  have h := checkLog_sound (w := (304811 / 2304811)) (n := 12)
    (lo := (133029101 / 500000000)) (hi := (266058203 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1304811 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1304811 / 1000000) = 1/(1000000 / 1304811) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (133029101 / 500000000) (266058203 / 1000000000) (Real.log (1304811 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1304811 / 1000000) = -Real.log (1000000 / 1304811) := by
    rw [show ((1304811 / 1000000) : ℝ) = ((1000000 / 1304811) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (363571527 / 1000000000) ≤ -Real.log (695189 / 1000000) ∧
    -Real.log (695189 / 1000000) ≤ (45446441 / 125000000) := by
  have h := checkLog_sound (w := (304811 / 1695189)) (n := 12)
    (lo := (363571527 / 1000000000)) (hi := (45446441 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 695189) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 695189) = 1/(695189 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-45446441 / 125000000) (-363571527 / 1000000000) (Real.log (695189 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (266385399 / 1000000000) ≤ -Real.log (500000 / 652619) ∧
    -Real.log (500000 / 652619) ≤ (1331927 / 5000000) := by
  have h := checkLog_sound (w := (152619 / 1152619)) (n := 12)
    (lo := (266385399 / 1000000000)) (hi := (1331927 / 5000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((652619 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(652619 / 500000) = 1/(500000 / 652619) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (266385399 / 1000000000) (1331927 / 5000000) (Real.log (652619 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (652619 / 500000) = -Real.log (500000 / 652619) := by
    rw [show ((652619 / 500000) : ℝ) = ((500000 / 652619) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (182092969 / 500000000) ≤ -Real.log (347381 / 500000) ∧
    -Real.log (347381 / 500000) ≤ (364185939 / 1000000000) := by
  have h := checkLog_sound (w := (152619 / 847381)) (n := 12)
    (lo := (182092969 / 500000000)) (hi := (364185939 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 347381) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 347381) = 1/(347381 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-364185939 / 1000000000) (-182092969 / 500000000) (Real.log (347381 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (199854453 / 1000000000) ≤ -Real.log (40000 / 48849) ∧
    -Real.log (40000 / 48849) ≤ (99927227 / 500000000) := by
  have h := checkLog_sound (w := (8849 / 88849)) (n := 12)
    (lo := (199854453 / 1000000000)) (hi := (99927227 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((48849 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(48849 / 40000) = 1/(40000 / 48849) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (199854453 / 1000000000) (99927227 / 500000000) (Real.log (48849 / 40000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (48849 / 40000) = -Real.log (40000 / 48849) := by
    rw [show ((48849 / 40000) : ℝ) = ((40000 / 48849) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (125016553 / 500000000) ≤ -Real.log (31151 / 40000) ∧
    -Real.log (31151 / 40000) ≤ (250033107 / 1000000000) := by
  have h := checkLog_sound (w := (8849 / 71151)) (n := 12)
    (lo := (125016553 / 500000000)) (hi := (250033107 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000 / 31151) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000 / 31151) = 1/(31151 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-250033107 / 1000000000) (-125016553 / 500000000) (Real.log (31151 / 40000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (100060681 / 500000000) ≤ -Real.log (1000000 / 1221551) ∧
    -Real.log (1000000 / 1221551) ≤ (200121363 / 1000000000) := by
  have h := checkLog_sound (w := (221551 / 2221551)) (n := 12)
    (lo := (100060681 / 500000000)) (hi := (200121363 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1221551 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1221551 / 1000000) = 1/(1000000 / 1221551) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (100060681 / 500000000) (200121363 / 1000000000) (Real.log (1221551 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1221551 / 1000000) = -Real.log (1000000 / 1221551) := by
    rw [show ((1221551 / 1000000) : ℝ) = ((1000000 / 1221551) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (1252259 / 5000000) ≤ -Real.log (778449 / 1000000) ∧
    -Real.log (778449 / 1000000) ≤ (250451801 / 1000000000) := by
  have h := checkLog_sound (w := (221551 / 1778449)) (n := 12)
    (lo := (1252259 / 5000000)) (hi := (250451801 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 778449) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 778449) = 1/(778449 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-250451801 / 1000000000) (-1252259 / 5000000) (Real.log (778449 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (62962973 / 100000000) ≤ -Real.log (250000000000 / 469228871573) ∧
    -Real.log (250000000000 / 469228871573) ≤ (629629731 / 1000000000) := by
  have h := checkLog_sound (w := (219228871573 / 719228871573)) (n := 12)
    (lo := (62962973 / 100000000)) (hi := (629629731 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((469228871573 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(469228871573 / 250000000000) = 1/(250000000000 / 469228871573) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (62962973 / 100000000) (629629731 / 1000000000) (Real.log (469228871573 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (469228871573 / 250000000000) = -Real.log (250000000000 / 469228871573) := by
    rw [show ((469228871573 / 250000000000) : ℝ) = ((250000000000 / 469228871573) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (630571337 / 1000000000) ≤ -Real.log (250000000000 / 469670908887) ∧
    -Real.log (250000000000 / 469670908887) ≤ (315285669 / 500000000) := by
  have h := checkLog_sound (w := (219670908887 / 719670908887)) (n := 12)
    (lo := (630571337 / 1000000000)) (hi := (315285669 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((469670908887 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(469670908887 / 250000000000) = 1/(250000000000 / 469670908887) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (630571337 / 1000000000) (315285669 / 500000000) (Real.log (469670908887 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (469670908887 / 250000000000) = -Real.log (250000000000 / 469670908887) := by
    rw [show ((469670908887 / 250000000000) : ℝ) = ((250000000000 / 469670908887) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (11247189 / 25000000) ≤ -Real.log (500000000000 / 784067927193) ∧
    -Real.log (500000000000 / 784067927193) ≤ (449887561 / 1000000000) := by
  have h := checkLog_sound (w := (284067927193 / 1284067927193)) (n := 12)
    (lo := (11247189 / 25000000)) (hi := (449887561 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((784067927193 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(784067927193 / 500000000000) = 1/(500000000000 / 784067927193) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (11247189 / 25000000) (449887561 / 1000000000) (Real.log (784067927193 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (784067927193 / 500000000000) = -Real.log (500000000000 / 784067927193) := by
    rw [show ((784067927193 / 500000000000) : ℝ) = ((500000000000 / 784067927193) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (450573163 / 1000000000) ≤ -Real.log (500000000000 / 784605671021) ∧
    -Real.log (500000000000 / 784605671021) ≤ (112643291 / 250000000) := by
  have h := checkLog_sound (w := (284605671021 / 1284605671021)) (n := 12)
    (lo := (450573163 / 1000000000)) (hi := (112643291 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((784605671021 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(784605671021 / 500000000000) = 1/(500000000000 / 784605671021) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (450573163 / 1000000000) (112643291 / 250000000) (Real.log (784605671021 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (784605671021 / 500000000000) = -Real.log (500000000000 / 784605671021) := by
    rw [show ((784605671021 / 500000000000) : ℝ) = ((500000000000 / 784605671021) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0426
