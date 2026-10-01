import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0005
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

theorem reflection_log_1_neg : (34143127 / 50000000) ≤ -Real.log (1000000000000 / 1979536132813) ∧
    -Real.log (1000000000000 / 1979536132813) ≤ (682862541 / 1000000000) := by
  have h := checkLog_sound (w := (979536132813 / 2979536132813)) (n := 12)
    (lo := (34143127 / 50000000)) (hi := (682862541 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1979536132813 / 1000000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1979536132813 / 1000000000000) = 1/(1000000000000 / 1979536132813) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (34143127 / 50000000) (682862541 / 1000000000) (Real.log (1979536132813 / 1000000000000)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1979536132813 / 1000000000000) = -Real.log (1000000000000 / 1979536132813) := by
    rw [show ((1979536132813 / 1000000000000) : ℝ) = ((1000000000000 / 1979536132813) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (3889094521 / 1000000000) ≤ -Real.log (20463867187 / 1000000000000) ∧
    -Real.log (20463867187 / 1000000000000) ≤ (3889094527 / 1000000000) := by
  have h := checkLog_sound (w := (10786132813 / 51713867187)) (n := 12)
    (lo := (423358621 / 1000000000)) (hi := (211679311 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250000000 / 20463867187) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250000000 / 20463867187) = 1/(20463867187 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-3889094527 / 1000000000) (-3889094521 / 1000000000) (Real.log (20463867187 / 1000000000000)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (682815673 / 1000000000) ≤ -Real.log (20480 / 40539) ∧
    -Real.log (20480 / 40539) ≤ (341407837 / 500000000) := by
  have h := checkLog_sound (w := (20059 / 61019)) (n := 12)
    (lo := (682815673 / 1000000000)) (hi := (341407837 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40539 / 20480) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40539 / 20480) = 1/(20480 / 40539) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (682815673 / 1000000000) (341407837 / 500000000) (Real.log (40539 / 20480)) := by
  have h := reflection_log_3_neg
  have he : Real.log (40539 / 20480) = -Real.log (20480 / 40539) := by
    rw [show ((40539 / 20480) : ℝ) = ((20480 / 40539) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (1942285621 / 500000000) ≤ -Real.log (421 / 20480) ∧
    -Real.log (421 / 20480) ≤ (242785703 / 62500000) := by
  have h := checkLog_sound (w := (219 / 1061)) (n := 12)
    (lo := (209417671 / 500000000)) (hi := (418835343 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 421) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(640 / 421) = 1/(421 / 20480) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-242785703 / 62500000) (-1942285621 / 500000000) (Real.log (421 / 20480)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (672471027 / 1000000000) ≤ -Real.log (102400 / 200609) ∧
    -Real.log (102400 / 200609) ≤ (168117757 / 250000000) := by
  have h := checkLog_sound (w := (98209 / 303009)) (n := 12)
    (lo := (672471027 / 1000000000)) (hi := (168117757 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200609 / 102400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200609 / 102400) = 1/(102400 / 200609) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (672471027 / 1000000000) (168117757 / 250000000) (Real.log (200609 / 102400)) := by
  have h := reflection_log_5_neg
  have he : Real.log (200609 / 102400) = -Real.log (102400 / 200609) := by
    rw [show ((200609 / 102400) : ℝ) = ((102400 / 200609) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (3195947341 / 1000000000) ≤ -Real.log (4191 / 102400) ∧
    -Real.log (4191 / 102400) ≤ (1597973673 / 500000000) := by
  have h := checkLog_sound (w := (2209 / 10591)) (n := 12)
    (lo := (423358621 / 1000000000)) (hi := (211679311 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6400 / 4191) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(6400 / 4191) = 1/(4191 / 102400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1597973673 / 500000000) (-3195947341 / 1000000000) (Real.log (4191 / 102400)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (672376311 / 1000000000) ≤ -Real.log (10240 / 20059) ∧
    -Real.log (10240 / 20059) ≤ (84047039 / 125000000) := by
  have h := checkLog_sound (w := (9819 / 30299)) (n := 12)
    (lo := (672376311 / 1000000000)) (hi := (84047039 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20059 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20059 / 10240) = 1/(10240 / 20059) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (672376311 / 1000000000) (84047039 / 125000000) (Real.log (20059 / 10240)) := by
  have h := reflection_log_7_neg
  have he : Real.log (20059 / 10240) = -Real.log (10240 / 20059) := by
    rw [show ((20059 / 10240) : ℝ) = ((10240 / 20059) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (1595712031 / 500000000) ≤ -Real.log (421 / 10240) ∧
    -Real.log (421 / 10240) ≤ (3191424067 / 1000000000) := by
  have h := checkLog_sound (w := (219 / 1061)) (n := 12)
    (lo := (209417671 / 500000000)) (hi := (418835343 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 421) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(640 / 421) = 1/(421 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-3191424067 / 1000000000) (-1595712031 / 500000000) (Real.log (421 / 10240)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (136874963 / 200000000) ≤ -Real.log (250000 / 495633) ∧
    -Real.log (250000 / 495633) ≤ (21386713 / 31250000) := by
  have h := checkLog_sound (w := (245633 / 745633)) (n := 12)
    (lo := (136874963 / 200000000)) (hi := (21386713 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((495633 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(495633 / 250000) = 1/(250000 / 495633) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (136874963 / 200000000) (21386713 / 31250000) (Real.log (495633 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (495633 / 250000) = -Real.log (250000 / 495633) := by
    rw [show ((495633 / 250000) : ℝ) = ((250000 / 495633) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (12648077 / 3125000) ≤ -Real.log (4367 / 250000) ∧
    -Real.log (4367 / 250000) ≤ (2023692323 / 500000000) := by
  have h := checkLog_sound (w := (6891 / 24359)) (n := 12)
    (lo := (29082437 / 50000000)) (hi := (581648741 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 8734) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 8734) = 1/(4367 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-2023692323 / 500000000) (-12648077 / 3125000) (Real.log (4367 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (342206827 / 500000000) ≤ -Real.log (1000000 / 1982609) ∧
    -Real.log (1000000 / 1982609) ≤ (136882731 / 200000000) := by
  have h := checkLog_sound (w := (982609 / 2982609)) (n := 12)
    (lo := (342206827 / 500000000)) (hi := (136882731 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1982609 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1982609 / 1000000) = 1/(1000000 / 1982609) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (342206827 / 500000000) (136882731 / 200000000) (Real.log (1982609 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1982609 / 1000000) = -Real.log (1000000 / 1982609) := by
    rw [show ((1982609 / 1000000) : ℝ) = ((1000000 / 1982609) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (810360489 / 200000000) ≤ -Real.log (17391 / 1000000) ∧
    -Real.log (17391 / 1000000) ≤ (4051802451 / 1000000000) := by
  have h := checkLog_sound (w := (13859 / 48641)) (n := 12)
    (lo := (117213309 / 200000000)) (hi := (293033273 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 17391) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 17391) = 1/(17391 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-4051802451 / 1000000000) (-810360489 / 200000000) (Real.log (17391 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (171085381 / 250000000) ≤ -Real.log (500000 / 991233) ∧
    -Real.log (500000 / 991233) ≤ (27373661 / 40000000) := by
  have h := checkLog_sound (w := (491233 / 1491233)) (n := 12)
    (lo := (171085381 / 250000000)) (hi := (27373661 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((991233 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(991233 / 500000) = 1/(500000 / 991233) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (171085381 / 250000000) (27373661 / 40000000) (Real.log (991233 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (991233 / 500000) = -Real.log (500000 / 991233) := by
    rw [show ((991233 / 500000) : ℝ) = ((500000 / 991233) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (4043613423 / 1000000000) ≤ -Real.log (8767 / 500000) ∧
    -Real.log (8767 / 500000) ≤ (4043613429 / 1000000000) := by
  have h := checkLog_sound (w := (3429 / 12196)) (n := 12)
    (lo := (577877523 / 1000000000)) (hi := (144469381 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 8767) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 8767) = 1/(8767 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-4043613429 / 1000000000) (-4043613423 / 1000000000) (Real.log (8767 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (171095217 / 250000000) ≤ -Real.log (62500 / 123909) ∧
    -Real.log (62500 / 123909) ≤ (684380869 / 1000000000) := by
  have h := checkLog_sound (w := (61409 / 186409)) (n := 12)
    (lo := (171095217 / 250000000)) (hi := (684380869 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((123909 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(123909 / 62500) = 1/(62500 / 123909) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (171095217 / 250000000) (684380869 / 1000000000) (Real.log (123909 / 62500)) := by
  have h := reflection_log_15_neg
  have he : Real.log (123909 / 62500) = -Real.log (62500 / 123909) := by
    rw [show ((123909 / 62500) : ℝ) = ((62500 / 123909) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (4048071847 / 1000000000) ≤ -Real.log (1091 / 62500) ∧
    -Real.log (1091 / 62500) ≤ (4048071853 / 1000000000) := by
  have h := checkLog_sound (w := (6897 / 24353)) (n := 12)
    (lo := (582335947 / 1000000000)) (hi := (145583987 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 8728) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 8728) = 1/(1091 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-4048071853 / 1000000000) (-4048071847 / 1000000000) (Real.log (1091 / 62500)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (946351891 / 200000000) ≤ -Real.log (10000000000 / 1134950767117) ∧
    -Real.log (10000000000 / 1134950767117) ≤ (2365879731 / 500000000) := by
  have h := checkLog_sound (w := (494950767117 / 1774950767117)) (n := 12)
    (lo := (4583011 / 8000000)) (hi := (71609547 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1134950767117 / 640000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(1134950767117 / 640000000000) = 1/(10000000000 / 1134950767117) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (946351891 / 200000000) (2365879731 / 500000000) (Real.log (1134950767117 / 10000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1134950767117 / 10000000000) = -Real.log (10000000000 / 1134950767117) := by
    rw [show ((1134950767117 / 10000000000) : ℝ) = ((10000000000 / 1134950767117) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (2368108049 / 500000000) ≤ -Real.log (50000000000 / 5700100626761) ∧
    -Real.log (50000000000 / 5700100626761) ≤ (947243221 / 200000000) := by
  have h := checkLog_sound (w := (2500100626761 / 8900100626761)) (n := 12)
    (lo := (288666509 / 500000000)) (hi := (577333019 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5700100626761 / 3200000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(5700100626761 / 3200000000000) = 1/(50000000000 / 5700100626761) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (2368108049 / 500000000) (947243221 / 200000000) (Real.log (5700100626761 / 50000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (5700100626761 / 50000000000) = -Real.log (50000000000 / 5700100626761) := by
    rw [show ((5700100626761 / 50000000000) : ℝ) = ((50000000000 / 5700100626761) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (2363977473 / 500000000) ≤ -Real.log (500000000000 / 56532052013231) ∧
    -Real.log (500000000000 / 56532052013231) ≤ (4727954953 / 1000000000) := by
  have h := checkLog_sound (w := (24532052013231 / 88532052013231)) (n := 12)
    (lo := (284535933 / 500000000)) (hi := (569071867 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((56532052013231 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(56532052013231 / 32000000000000) = 1/(500000000000 / 56532052013231) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (2363977473 / 500000000) (4727954953 / 1000000000) (Real.log (56532052013231 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (56532052013231 / 500000000000) = -Real.log (500000000000 / 56532052013231) := by
    rw [show ((56532052013231 / 500000000000) : ℝ) = ((500000000000 / 56532052013231) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (946490543 / 200000000) ≤ -Real.log (500000000000 / 56786892758937) ∧
    -Real.log (500000000000 / 56786892758937) ≤ (2366226361 / 500000000) := by
  have h := checkLog_sound (w := (24786892758937 / 88786892758937)) (n := 12)
    (lo := (114713927 / 200000000)) (hi := (143392409 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((56786892758937 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(56786892758937 / 32000000000000) = 1/(500000000000 / 56786892758937) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (946490543 / 200000000) (2366226361 / 500000000) (Real.log (56786892758937 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (56786892758937 / 500000000000) = -Real.log (500000000000 / 56786892758937) := by
    rw [show ((56786892758937 / 500000000000) : ℝ) = ((500000000000 / 56786892758937) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0005
