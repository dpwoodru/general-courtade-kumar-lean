import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0332
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

theorem reflection_log_1_neg : (13525133 / 62500000) ≤ -Real.log (5120 / 6357) ∧
    -Real.log (5120 / 6357) ≤ (216402129 / 1000000000) := by
  have h := checkLog_sound (w := (1237 / 11477)) (n := 12)
    (lo := (13525133 / 62500000)) (hi := (216402129 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6357 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6357 / 5120) = 1/(5120 / 6357) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (13525133 / 62500000) (216402129 / 1000000000) (Real.log (6357 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6357 / 5120) = -Real.log (5120 / 6357) := by
    rw [show ((6357 / 5120) : ℝ) = ((5120 / 6357) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (69136597 / 250000000) ≤ -Real.log (3883 / 5120) ∧
    -Real.log (3883 / 5120) ≤ (276546389 / 1000000000) := by
  have h := checkLog_sound (w := (1237 / 9003)) (n := 12)
    (lo := (69136597 / 250000000)) (hi := (276546389 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3883) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3883) = 1/(3883 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-276546389 / 1000000000) (-69136597 / 250000000) (Real.log (3883 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (10808307 / 50000000) ≤ -Real.log (10240 / 12711) ∧
    -Real.log (10240 / 12711) ≤ (216166141 / 1000000000) := by
  have h := checkLog_sound (w := (2471 / 22951)) (n := 12)
    (lo := (10808307 / 50000000)) (hi := (216166141 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12711 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12711 / 10240) = 1/(10240 / 12711) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (10808307 / 50000000) (216166141 / 1000000000) (Real.log (12711 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12711 / 10240) = -Real.log (10240 / 12711) := by
    rw [show ((12711 / 10240) : ℝ) = ((10240 / 12711) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (276160163 / 1000000000) ≤ -Real.log (7769 / 10240) ∧
    -Real.log (7769 / 10240) ≤ (69040041 / 250000000) := by
  have h := checkLog_sound (w := (2471 / 18009)) (n := 12)
    (lo := (276160163 / 1000000000)) (hi := (69040041 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7769) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7769) = 1/(7769 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-69040041 / 250000000) (-276160163 / 1000000000) (Real.log (7769 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (197102011 / 500000000) ≤ -Real.log (2560 / 3797) ∧
    -Real.log (2560 / 3797) ≤ (394204023 / 1000000000) := by
  have h := checkLog_sound (w := (1237 / 6357)) (n := 12)
    (lo := (197102011 / 500000000)) (hi := (394204023 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3797 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3797 / 2560) = 1/(2560 / 3797) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (197102011 / 500000000) (394204023 / 1000000000) (Real.log (3797 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (3797 / 2560) = -Real.log (2560 / 3797) := by
    rw [show ((3797 / 2560) : ℝ) = ((2560 / 3797) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (660105373 / 1000000000) ≤ -Real.log (1323 / 2560) ∧
    -Real.log (1323 / 2560) ≤ (330052687 / 500000000) := by
  have h := checkLog_sound (w := (1237 / 3883)) (n := 12)
    (lo := (660105373 / 1000000000)) (hi := (330052687 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1323) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1323) = 1/(1323 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-330052687 / 500000000) (-660105373 / 1000000000) (Real.log (1323 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (78761779 / 200000000) ≤ -Real.log (5120 / 7591) ∧
    -Real.log (5120 / 7591) ≤ (769158 / 1953125) := by
  have h := checkLog_sound (w := (2471 / 12711)) (n := 12)
    (lo := (78761779 / 200000000)) (hi := (769158 / 1953125))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7591 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7591 / 5120) = 1/(5120 / 7591) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (78761779 / 200000000) (769158 / 1953125) (Real.log (7591 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (7591 / 5120) = -Real.log (5120 / 7591) := by
    rw [show ((7591 / 5120) : ℝ) = ((5120 / 7591) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (164743057 / 250000000) ≤ -Real.log (2649 / 5120) ∧
    -Real.log (2649 / 5120) ≤ (658972229 / 1000000000) := by
  have h := checkLog_sound (w := (2471 / 7769)) (n := 12)
    (lo := (164743057 / 250000000)) (hi := (658972229 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2649) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2649) = 1/(2649 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-658972229 / 1000000000) (-164743057 / 250000000) (Real.log (2649 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (148174701 / 500000000) ≤ -Real.log (50000 / 67247) ∧
    -Real.log (50000 / 67247) ≤ (296349403 / 1000000000) := by
  have h := checkLog_sound (w := (17247 / 117247)) (n := 12)
    (lo := (148174701 / 500000000)) (hi := (296349403 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((67247 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(67247 / 50000) = 1/(50000 / 67247) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (148174701 / 500000000) (296349403 / 1000000000) (Real.log (67247 / 50000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (67247 / 50000) = -Real.log (50000 / 67247) := by
    rw [show ((67247 / 50000) : ℝ) = ((50000 / 67247) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (105757111 / 250000000) ≤ -Real.log (32753 / 50000) ∧
    -Real.log (32753 / 50000) ≤ (84605689 / 200000000) := by
  have h := checkLog_sound (w := (17247 / 82753)) (n := 12)
    (lo := (105757111 / 250000000)) (hi := (84605689 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 32753) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 32753) = 1/(32753 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-84605689 / 200000000) (-105757111 / 250000000) (Real.log (32753 / 50000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (74167267 / 250000000) ≤ -Real.log (100000 / 134537) ∧
    -Real.log (100000 / 134537) ≤ (296669069 / 1000000000) := by
  have h := checkLog_sound (w := (34537 / 234537)) (n := 12)
    (lo := (74167267 / 250000000)) (hi := (296669069 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((134537 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(134537 / 100000) = 1/(100000 / 134537) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (74167267 / 250000000) (296669069 / 1000000000) (Real.log (134537 / 100000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (134537 / 100000) = -Real.log (100000 / 134537) := by
    rw [show ((134537 / 100000) : ℝ) = ((100000 / 134537) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (13240159 / 31250000) ≤ -Real.log (65463 / 100000) ∧
    -Real.log (65463 / 100000) ≤ (423685089 / 1000000000) := by
  have h := checkLog_sound (w := (34537 / 165463)) (n := 12)
    (lo := (13240159 / 31250000)) (hi := (423685089 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 65463) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 65463) = 1/(65463 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-423685089 / 1000000000) (-13240159 / 31250000) (Real.log (65463 / 100000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (112456193 / 500000000) ≤ -Real.log (1000000 / 1252213) ∧
    -Real.log (1000000 / 1252213) ≤ (224912387 / 1000000000) := by
  have h := checkLog_sound (w := (252213 / 2252213)) (n := 12)
    (lo := (112456193 / 500000000)) (hi := (224912387 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1252213 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1252213 / 1000000) = 1/(1000000 / 1252213) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (112456193 / 500000000) (224912387 / 1000000000) (Real.log (1252213 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1252213 / 1000000) = -Real.log (1000000 / 1252213) := by
    rw [show ((1252213 / 1000000) : ℝ) = ((1000000 / 1252213) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (2906371 / 10000000) ≤ -Real.log (747787 / 1000000) ∧
    -Real.log (747787 / 1000000) ≤ (290637101 / 1000000000) := by
  have h := checkLog_sound (w := (252213 / 1747787)) (n := 12)
    (lo := (2906371 / 10000000)) (hi := (290637101 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 747787) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 747787) = 1/(747787 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-290637101 / 1000000000) (-2906371 / 10000000) (Real.log (747787 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (112590337 / 500000000) ≤ -Real.log (1000000 / 1252549) ∧
    -Real.log (1000000 / 1252549) ≤ (9007227 / 40000000) := by
  have h := checkLog_sound (w := (252549 / 2252549)) (n := 12)
    (lo := (112590337 / 500000000)) (hi := (9007227 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1252549 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1252549 / 1000000) = 1/(1000000 / 1252549) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (112590337 / 500000000) (9007227 / 40000000) (Real.log (1252549 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1252549 / 1000000) = -Real.log (1000000 / 1252549) := by
    rw [show ((1252549 / 1000000) : ℝ) = ((1000000 / 1252549) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (291086527 / 1000000000) ≤ -Real.log (747451 / 1000000) ∧
    -Real.log (747451 / 1000000) ≤ (4548227 / 15625000) := by
  have h := checkLog_sound (w := (252549 / 1747451)) (n := 12)
    (lo := (291086527 / 1000000000)) (hi := (4548227 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 747451) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 747451) = 1/(747451 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-4548227 / 15625000) (-291086527 / 1000000000) (Real.log (747451 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (359688923 / 500000000) ≤ -Real.log (500000000000 / 1026577718071) ∧
    -Real.log (500000000000 / 1026577718071) ≤ (89922231 / 125000000) := by
  have h := checkLog_sound (w := (26577718071 / 2026577718071)) (n := 12)
    (lo := (13115333 / 500000000)) (hi := (26230667 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1026577718071 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1026577718071 / 1000000000000) = 1/(500000000000 / 1026577718071) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (359688923 / 500000000) (89922231 / 125000000) (Real.log (1026577718071 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1026577718071 / 500000000000) = -Real.log (500000000000 / 1026577718071) := by
    rw [show ((1026577718071 / 500000000000) : ℝ) = ((500000000000 / 1026577718071) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (180088539 / 250000000) ≤ -Real.log (250000000000 / 513790232651) ∧
    -Real.log (250000000000 / 513790232651) ≤ (360177079 / 500000000) := by
  have h := checkLog_sound (w := (13790232651 / 1013790232651)) (n := 12)
    (lo := (425109 / 15625000)) (hi := (27206977 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((513790232651 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(513790232651 / 500000000000) = 1/(250000000000 / 513790232651) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (180088539 / 250000000) (360177079 / 500000000) (Real.log (513790232651 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (513790232651 / 250000000000) = -Real.log (250000000000 / 513790232651) := by
    rw [show ((513790232651 / 250000000000) : ℝ) = ((250000000000 / 513790232651) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (257774743 / 500000000) ≤ -Real.log (62500000000 / 104659899811) ∧
    -Real.log (62500000000 / 104659899811) ≤ (515549487 / 1000000000) := by
  have h := checkLog_sound (w := (42159899811 / 167159899811)) (n := 12)
    (lo := (257774743 / 500000000)) (hi := (515549487 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((104659899811 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(104659899811 / 62500000000) = 1/(62500000000 / 104659899811) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (257774743 / 500000000) (515549487 / 1000000000) (Real.log (104659899811 / 62500000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (104659899811 / 62500000000) = -Real.log (62500000000 / 104659899811) := by
    rw [show ((104659899811 / 62500000000) : ℝ) = ((62500000000 / 104659899811) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (258133601 / 500000000) ≤ -Real.log (250000000000 / 418940171329) ∧
    -Real.log (250000000000 / 418940171329) ≤ (516267203 / 1000000000) := by
  have h := checkLog_sound (w := (168940171329 / 668940171329)) (n := 12)
    (lo := (258133601 / 500000000)) (hi := (516267203 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((418940171329 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(418940171329 / 250000000000) = 1/(250000000000 / 418940171329) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (258133601 / 500000000) (516267203 / 1000000000) (Real.log (418940171329 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (418940171329 / 250000000000) = -Real.log (250000000000 / 418940171329) := by
    rw [show ((418940171329 / 250000000000) : ℝ) = ((250000000000 / 418940171329) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0332
