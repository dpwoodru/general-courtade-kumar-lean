import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0008
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

theorem reflection_log_1_neg : (170680483 / 250000000) ≤ -Real.log (25600 / 50669) ∧
    -Real.log (25600 / 50669) ≤ (682721933 / 1000000000) := by
  have h := checkLog_sound (w := (25069 / 76269)) (n := 12)
    (lo := (170680483 / 250000000)) (hi := (682721933 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50669 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50669 / 25600) = 1/(25600 / 50669) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (170680483 / 250000000) (682721933 / 1000000000) (Real.log (50669 / 25600)) := by
  have h := reflection_log_1_neg
  have he : Real.log (50669 / 25600) = -Real.log (25600 / 50669) := by
    rw [show ((50669 / 25600) : ℝ) = ((25600 / 50669) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (1937792803 / 500000000) ≤ -Real.log (531 / 25600) ∧
    -Real.log (531 / 25600) ≤ (968896403 / 250000000) := by
  have h := checkLog_sound (w := (269 / 1331)) (n := 12)
    (lo := (204924853 / 500000000)) (hi := (409849707 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 531) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(800 / 531) = 1/(531 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-968896403 / 250000000) (-1937792803 / 500000000) (Real.log (531 / 25600)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (341337529 / 500000000) ≤ -Real.log (500000000000 / 989582519531) ∧
    -Real.log (500000000000 / 989582519531) ≤ (682675059 / 1000000000) := by
  have h := checkLog_sound (w := (489582519531 / 1489582519531)) (n := 12)
    (lo := (341337529 / 500000000)) (hi := (682675059 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((989582519531 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(989582519531 / 500000000000) = 1/(500000000000 / 989582519531) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (341337529 / 500000000) (682675059 / 1000000000) (Real.log (989582519531 / 500000000000)) := by
  have h := reflection_log_3_neg
  have he : Real.log (989582519531 / 500000000000) = -Real.log (500000000000 / 989582519531) := by
    rw [show ((989582519531 / 500000000000) : ℝ) = ((500000000000 / 989582519531) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (1935561443 / 500000000) ≤ -Real.log (10417480469 / 500000000000) ∧
    -Real.log (10417480469 / 500000000000) ≤ (967780723 / 250000000) := by
  have h := checkLog_sound (w := (5207519531 / 26042480469)) (n := 12)
    (lo := (202693493 / 500000000)) (hi := (405386987 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 10417480469) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625000000 / 10417480469) = 1/(10417480469 / 500000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-967780723 / 250000000) (-1935561443 / 500000000) (Real.log (10417480469 / 500000000000)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (168046713 / 250000000) ≤ -Real.log (12800 / 25069) ∧
    -Real.log (12800 / 25069) ≤ (672186853 / 1000000000) := by
  have h := checkLog_sound (w := (12269 / 37869)) (n := 12)
    (lo := (168046713 / 250000000)) (hi := (672186853 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25069 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25069 / 12800) = 1/(12800 / 25069) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (168046713 / 250000000) (672186853 / 1000000000) (Real.log (25069 / 12800)) := by
  have h := reflection_log_5_neg
  have he : Real.log (25069 / 12800) = -Real.log (12800 / 25069) := by
    rw [show ((25069 / 12800) : ℝ) = ((12800 / 25069) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1591219213 / 500000000) ≤ -Real.log (531 / 12800) ∧
    -Real.log (531 / 12800) ≤ (3182438431 / 1000000000) := by
  have h := checkLog_sound (w := (269 / 1331)) (n := 12)
    (lo := (204924853 / 500000000)) (hi := (409849707 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 531) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(800 / 531) = 1/(531 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-3182438431 / 1000000000) (-1591219213 / 500000000) (Real.log (531 / 12800)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (672092109 / 1000000000) ≤ -Real.log (102400 / 200533) ∧
    -Real.log (102400 / 200533) ≤ (67209211 / 100000000) := by
  have h := checkLog_sound (w := (98133 / 302933)) (n := 12)
    (lo := (672092109 / 1000000000)) (hi := (67209211 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200533 / 102400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200533 / 102400) = 1/(102400 / 200533) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (672092109 / 1000000000) (67209211 / 100000000) (Real.log (200533 / 102400)) := by
  have h := reflection_log_7_neg
  have he : Real.log (200533 / 102400) = -Real.log (102400 / 200533) := by
    rw [show ((200533 / 102400) : ℝ) = ((102400 / 200533) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (1588987853 / 500000000) ≤ -Real.log (4267 / 102400) ∧
    -Real.log (4267 / 102400) ≤ (3177975711 / 1000000000) := by
  have h := checkLog_sound (w := (2133 / 10667)) (n := 12)
    (lo := (202693493 / 500000000)) (hi := (405386987 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6400 / 4267) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(6400 / 4267) = 1/(4267 / 102400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-3177975711 / 1000000000) (-1588987853 / 500000000) (Real.log (4267 / 102400)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (684260309 / 1000000000) ≤ -Real.log (200000 / 396461) ∧
    -Real.log (200000 / 396461) ≤ (68426031 / 100000000) := by
  have h := checkLog_sound (w := (196461 / 596461)) (n := 12)
    (lo := (684260309 / 1000000000)) (hi := (68426031 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((396461 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(396461 / 200000) = 1/(200000 / 396461) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (684260309 / 1000000000) (68426031 / 100000000) (Real.log (396461 / 200000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (396461 / 200000) = -Real.log (200000 / 396461) := by
    rw [show ((396461 / 200000) : ℝ) = ((200000 / 396461) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (2017236581 / 500000000) ≤ -Real.log (3539 / 200000) ∧
    -Real.log (3539 / 200000) ≤ (252154573 / 62500000) := by
  have h := checkLog_sound (w := (2711 / 9789)) (n := 12)
    (lo := (284368631 / 500000000)) (hi := (568737263 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6250 / 3539) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(6250 / 3539) = 1/(3539 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-252154573 / 62500000) (-2017236581 / 500000000) (Real.log (3539 / 200000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (684298647 / 1000000000) ≤ -Real.log (1000000 / 1982381) ∧
    -Real.log (1000000 / 1982381) ≤ (85537331 / 125000000) := by
  have h := checkLog_sound (w := (982381 / 2982381)) (n := 12)
    (lo := (684298647 / 1000000000)) (hi := (85537331 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1982381 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1982381 / 1000000) = 1/(1000000 / 1982381) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (684298647 / 1000000000) (85537331 / 125000000) (Real.log (1982381 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1982381 / 1000000) = -Real.log (1000000 / 1982381) := by
    rw [show ((1982381 / 1000000) : ℝ) = ((1000000 / 1982381) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (403877741 / 100000000) ≤ -Real.log (17619 / 1000000) ∧
    -Real.log (17619 / 1000000) ≤ (504847177 / 125000000) := by
  have h := checkLog_sound (w := (13631 / 48869)) (n := 12)
    (lo := (57304151 / 100000000)) (hi := (573041511 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 17619) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 17619) = 1/(17619 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-504847177 / 125000000) (-403877741 / 100000000) (Real.log (17619 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (171056501 / 250000000) ≤ -Real.log (1000000 / 1982237) ∧
    -Real.log (1000000 / 1982237) ≤ (136845201 / 200000000) := by
  have h := checkLog_sound (w := (982237 / 2982237)) (n := 12)
    (lo := (171056501 / 250000000)) (hi := (136845201 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1982237 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1982237 / 1000000) = 1/(1000000 / 1982237) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (171056501 / 250000000) (136845201 / 200000000) (Real.log (1982237 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1982237 / 1000000) = -Real.log (1000000 / 1982237) := by
    rw [show ((1982237 / 1000000) : ℝ) = ((1000000 / 1982237) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (4030637633 / 1000000000) ≤ -Real.log (17763 / 1000000) ∧
    -Real.log (17763 / 1000000) ≤ (4030637639 / 1000000000) := by
  have h := checkLog_sound (w := (13487 / 49013)) (n := 12)
    (lo := (564901733 / 1000000000)) (hi := (282450867 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 17763) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 17763) = 1/(17763 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-4030637639 / 1000000000) (-4030637633 / 1000000000) (Real.log (17763 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (684265353 / 1000000000) ≤ -Real.log (200000 / 396463) ∧
    -Real.log (200000 / 396463) ≤ (342132677 / 500000000) := by
  have h := checkLog_sound (w := (196463 / 596463)) (n := 12)
    (lo := (684265353 / 1000000000)) (hi := (342132677 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((396463 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(396463 / 200000) = 1/(200000 / 396463) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (684265353 / 1000000000) (342132677 / 500000000) (Real.log (396463 / 200000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (396463 / 200000) = -Real.log (200000 / 396463) := by
    rw [show ((396463 / 200000) : ℝ) = ((200000 / 396463) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (4035038453 / 1000000000) ≤ -Real.log (3537 / 200000) ∧
    -Real.log (3537 / 200000) ≤ (4035038459 / 1000000000) := by
  have h := checkLog_sound (w := (2713 / 9787)) (n := 12)
    (lo := (569302553 / 1000000000)) (hi := (284651277 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6250 / 3537) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(6250 / 3537) = 1/(3537 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-4035038459 / 1000000000) (-4035038453 / 1000000000) (Real.log (3537 / 200000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (471873347 / 100000000) ≤ -Real.log (62500000000 / 7001642413111) ∧
    -Real.log (62500000000 / 7001642413111) ≤ (4718733477 / 1000000000) := by
  have h := checkLog_sound (w := (3001642413111 / 11001642413111)) (n := 12)
    (lo := (55985039 / 100000000)) (hi := (559850391 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7001642413111 / 4000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(7001642413111 / 4000000000000) = 1/(62500000000 / 7001642413111) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (471873347 / 100000000) (4718733477 / 1000000000) (Real.log (7001642413111 / 62500000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (7001642413111 / 62500000000) = -Real.log (62500000000 / 7001642413111) := by
    rw [show ((7001642413111 / 62500000000) : ℝ) = ((62500000000 / 7001642413111) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (4723076057 / 1000000000) ≤ -Real.log (125000000000 / 14064227538453) ∧
    -Real.log (125000000000 / 14064227538453) ≤ (147596127 / 31250000) := by
  have h := checkLog_sound (w := (6064227538453 / 22064227538453)) (n := 12)
    (lo := (564192977 / 1000000000)) (hi := (282096489 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((14064227538453 / 8000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(14064227538453 / 8000000000000) = 1/(125000000000 / 14064227538453) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (4723076057 / 1000000000) (147596127 / 31250000) (Real.log (14064227538453 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (14064227538453 / 125000000000) = -Real.log (125000000000 / 14064227538453) := by
    rw [show ((14064227538453 / 125000000000) : ℝ) = ((125000000000 / 14064227538453) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (2357431819 / 500000000) ≤ -Real.log (500000000000 / 55796796712267) ∧
    -Real.log (500000000000 / 55796796712267) ≤ (942972729 / 200000000) := by
  have h := checkLog_sound (w := (23796796712267 / 87796796712267)) (n := 12)
    (lo := (277990279 / 500000000)) (hi := (555980559 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((55796796712267 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(55796796712267 / 32000000000000) = 1/(500000000000 / 55796796712267) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (2357431819 / 500000000) (942972729 / 200000000) (Real.log (55796796712267 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (55796796712267 / 500000000000) = -Real.log (500000000000 / 55796796712267) := by
    rw [show ((55796796712267 / 500000000000) : ℝ) = ((500000000000 / 55796796712267) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (2359651903 / 500000000) ≤ -Real.log (250000000000 / 28022547356517) ∧
    -Real.log (250000000000 / 28022547356517) ≤ (4719303813 / 1000000000) := by
  have h := checkLog_sound (w := (12022547356517 / 44022547356517)) (n := 12)
    (lo := (280210363 / 500000000)) (hi := (560420727 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((28022547356517 / 16000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(28022547356517 / 16000000000000) = 1/(250000000000 / 28022547356517) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (2359651903 / 500000000) (4719303813 / 1000000000) (Real.log (28022547356517 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (28022547356517 / 250000000000) = -Real.log (250000000000 / 28022547356517) := by
    rw [show ((28022547356517 / 250000000000) : ℝ) = ((250000000000 / 28022547356517) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0008
