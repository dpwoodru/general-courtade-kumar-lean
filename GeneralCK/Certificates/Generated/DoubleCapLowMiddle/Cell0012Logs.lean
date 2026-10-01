import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0012
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

theorem reflection_log_1_neg : (682534423 / 1000000000) ≤ -Real.log (51200 / 101319) ∧
    -Real.log (51200 / 101319) ≤ (85316803 / 125000000) := by
  have h := checkLog_sound (w := (50119 / 152519)) (n := 12)
    (lo := (682534423 / 1000000000)) (hi := (85316803 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((101319 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(101319 / 51200) = 1/(51200 / 101319) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (682534423 / 1000000000) (85316803 / 125000000) (Real.log (101319 / 51200)) := by
  have h := reflection_log_1_neg
  have he : Real.log (101319 / 51200) = -Real.log (51200 / 101319) := by
    rw [show ((101319 / 51200) : ℝ) = ((51200 / 101319) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (385785299 / 100000000) ≤ -Real.log (1081 / 51200) ∧
    -Real.log (1081 / 51200) ≤ (964463249 / 250000000) := by
  have h := checkLog_sound (w := (519 / 2681)) (n := 12)
    (lo := (39211709 / 100000000)) (hi := (392117091 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1081) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(1600 / 1081) = 1/(1081 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-964463249 / 250000000) (-385785299 / 100000000) (Real.log (1081 / 51200)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (34124377 / 50000000) ≤ -Real.log (31250000000 / 61837310791) ∧
    -Real.log (31250000000 / 61837310791) ≤ (682487541 / 1000000000) := by
  have h := checkLog_sound (w := (30587310791 / 93087310791)) (n := 12)
    (lo := (34124377 / 50000000)) (hi := (682487541 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((61837310791 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(61837310791 / 31250000000) = 1/(31250000000 / 61837310791) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (34124377 / 50000000) (682487541 / 1000000000) (Real.log (61837310791 / 31250000000)) := by
  have h := reflection_log_3_neg
  have he : Real.log (61837310791 / 31250000000) = -Real.log (31250000000 / 61837310791) := by
    rw [show ((61837310791 / 31250000000) : ℝ) = ((31250000000 / 61837310791) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (481683567 / 125000000) ≤ -Real.log (662689209 / 31250000000) ∧
    -Real.log (662689209 / 31250000000) ≤ (1926734271 / 500000000) := by
  have h := checkLog_sound (w := (313873291 / 1639251709)) (n := 12)
    (lo := (96933159 / 250000000)) (hi := (387732637 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((976562500 / 662689209) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(976562500 / 662689209) = 1/(662689209 / 31250000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-1926734271 / 500000000) (-481683567 / 125000000) (Real.log (662689209 / 31250000000)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (335903913 / 500000000) ≤ -Real.log (25600 / 50119) ∧
    -Real.log (25600 / 50119) ≤ (671807827 / 1000000000) := by
  have h := checkLog_sound (w := (24519 / 75719)) (n := 12)
    (lo := (335903913 / 500000000)) (hi := (671807827 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50119 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50119 / 25600) = 1/(25600 / 50119) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (335903913 / 500000000) (671807827 / 1000000000) (Real.log (50119 / 25600)) := by
  have h := reflection_log_5_neg
  have he : Real.log (50119 / 25600) = -Real.log (25600 / 50119) := by
    rw [show ((50119 / 25600) : ℝ) = ((25600 / 50119) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (316470581 / 100000000) ≤ -Real.log (1081 / 25600) ∧
    -Real.log (1081 / 25600) ≤ (632941163 / 200000000) := by
  have h := checkLog_sound (w := (519 / 2681)) (n := 12)
    (lo := (39211709 / 100000000)) (hi := (392117091 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1081) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1600 / 1081) = 1/(1081 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-632941163 / 200000000) (-316470581 / 100000000) (Real.log (1081 / 25600)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (671713047 / 1000000000) ≤ -Real.log (102400 / 200457) ∧
    -Real.log (102400 / 200457) ≤ (83964131 / 125000000) := by
  have h := checkLog_sound (w := (98057 / 302857)) (n := 12)
    (lo := (671713047 / 1000000000)) (hi := (83964131 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200457 / 102400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200457 / 102400) = 1/(102400 / 200457) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (671713047 / 1000000000) (83964131 / 125000000) (Real.log (200457 / 102400)) := by
  have h := reflection_log_7_neg
  have he : Real.log (200457 / 102400) = -Real.log (102400 / 200457) := by
    rw [show ((200457 / 102400) : ℝ) = ((102400 / 200457) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (790080339 / 250000000) ≤ -Real.log (4343 / 102400) ∧
    -Real.log (4343 / 102400) ≤ (3160321361 / 1000000000) := by
  have h := checkLog_sound (w := (2057 / 10743)) (n := 12)
    (lo := (96933159 / 250000000)) (hi := (387732637 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6400 / 4343) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(6400 / 4343) = 1/(4343 / 102400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-3160321361 / 1000000000) (-790080339 / 250000000) (Real.log (4343 / 102400)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (171026861 / 250000000) ≤ -Real.log (500000 / 991001) ∧
    -Real.log (500000 / 991001) ≤ (136821489 / 200000000) := by
  have h := checkLog_sound (w := (491001 / 1491001)) (n := 12)
    (lo := (171026861 / 250000000)) (hi := (136821489 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((991001 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(991001 / 500000) = 1/(500000 / 991001) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (171026861 / 250000000) (136821489 / 200000000) (Real.log (991001 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (991001 / 500000) = -Real.log (500000 / 991001) := by
    rw [show ((991001 / 500000) : ℝ) = ((500000 / 991001) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (803498927 / 200000000) ≤ -Real.log (8999 / 500000) ∧
    -Real.log (8999 / 500000) ≤ (4017494641 / 1000000000) := by
  have h := checkLog_sound (w := (3313 / 12312)) (n := 12)
    (lo := (110351747 / 200000000)) (hi := (34484921 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 8999) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 8999) = 1/(8999 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-4017494641 / 1000000000) (-803498927 / 200000000) (Real.log (8999 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (684146293 / 1000000000) ≤ -Real.log (1000000 / 1982079) ∧
    -Real.log (1000000 / 1982079) ≤ (342073147 / 500000000) := by
  have h := checkLog_sound (w := (982079 / 2982079)) (n := 12)
    (lo := (684146293 / 1000000000)) (hi := (342073147 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1982079 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1982079 / 1000000) = 1/(1000000 / 1982079) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (684146293 / 1000000000) (342073147 / 500000000) (Real.log (1982079 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1982079 / 1000000) = -Real.log (1000000 / 1982079) := by
    rw [show ((1982079 / 1000000) : ℝ) = ((1000000 / 1982079) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (2010891033 / 500000000) ≤ -Real.log (17921 / 1000000) ∧
    -Real.log (17921 / 1000000) ≤ (502722759 / 125000000) := by
  have h := checkLog_sound (w := (13329 / 49171)) (n := 12)
    (lo := (278023083 / 500000000)) (hi := (556046167 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 17921) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 17921) = 1/(17921 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-502722759 / 125000000) (-2010891033 / 500000000) (Real.log (17921 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (342036063 / 500000000) ≤ -Real.log (250000 / 495483) ∧
    -Real.log (250000 / 495483) ≤ (684072127 / 1000000000) := by
  have h := checkLog_sound (w := (245483 / 745483)) (n := 12)
    (lo := (342036063 / 500000000)) (hi := (684072127 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((495483 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(495483 / 250000) = 1/(250000 / 495483) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (342036063 / 500000000) (684072127 / 1000000000) (Real.log (495483 / 250000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (495483 / 250000) = -Real.log (250000 / 495483) := by
    rw [show ((495483 / 250000) : ℝ) = ((250000 / 495483) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (2006806429 / 500000000) ≤ -Real.log (4517 / 250000) ∧
    -Real.log (4517 / 250000) ≤ (62712701 / 15625000) := by
  have h := checkLog_sound (w := (6591 / 24659)) (n := 12)
    (lo := (273938479 / 500000000)) (hi := (547876959 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 9034) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 9034) = 1/(4517 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-62712701 / 15625000) (-2006806429 / 500000000) (Real.log (4517 / 250000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (5344617 / 7812500) ≤ -Real.log (1000000 / 1982009) ∧
    -Real.log (1000000 / 1982009) ≤ (684110977 / 1000000000) := by
  have h := checkLog_sound (w := (982009 / 2982009)) (n := 12)
    (lo := (5344617 / 7812500)) (hi := (684110977 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1982009 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1982009 / 1000000) = 1/(1000000 / 1982009) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (5344617 / 7812500) (684110977 / 1000000000) (Real.log (1982009 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1982009 / 1000000) = -Real.log (1000000 / 1982009) := by
    rw [show ((1982009 / 1000000) : ℝ) = ((1000000 / 1982009) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (4017883643 / 1000000000) ≤ -Real.log (17991 / 1000000) ∧
    -Real.log (17991 / 1000000) ≤ (4017883649 / 1000000000) := by
  have h := checkLog_sound (w := (13259 / 49241)) (n := 12)
    (lo := (552147743 / 1000000000)) (hi := (17254617 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 17991) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 17991) = 1/(17991 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-4017883649 / 1000000000) (-4017883643 / 1000000000) (Real.log (17991 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (4701602079 / 1000000000) ≤ -Real.log (500000000000 / 55061729081009) ∧
    -Real.log (500000000000 / 55061729081009) ≤ (2350801043 / 500000000) := by
  have h := checkLog_sound (w := (23061729081009 / 87061729081009)) (n := 12)
    (lo := (542718999 / 1000000000)) (hi := (542719 / 1000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((55061729081009 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(55061729081009 / 32000000000000) = 1/(500000000000 / 55061729081009) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (4701602079 / 1000000000) (2350801043 / 500000000) (Real.log (55061729081009 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (55061729081009 / 500000000000) = -Real.log (500000000000 / 55061729081009) := by
    rw [show ((55061729081009 / 500000000000) : ℝ) = ((500000000000 / 55061729081009) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (4705928359 / 1000000000) ≤ -Real.log (500000000000 / 55300457563753) ∧
    -Real.log (500000000000 / 55300457563753) ≤ (2352964183 / 500000000) := by
  have h := checkLog_sound (w := (23300457563753 / 87300457563753)) (n := 12)
    (lo := (547045279 / 1000000000)) (hi := (3419033 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((55300457563753 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(55300457563753 / 32000000000000) = 1/(500000000000 / 55300457563753) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (4705928359 / 1000000000) (2352964183 / 500000000) (Real.log (55300457563753 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (55300457563753 / 500000000000) = -Real.log (500000000000 / 55300457563753) := by
    rw [show ((55300457563753 / 500000000000) : ℝ) = ((500000000000 / 55300457563753) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (587210623 / 125000000) ≤ -Real.log (125000000000 / 13711617223821) ∧
    -Real.log (125000000000 / 13711617223821) ≤ (4697684991 / 1000000000) := by
  have h := checkLog_sound (w := (5711617223821 / 21711617223821)) (n := 12)
    (lo := (33675119 / 62500000)) (hi := (107760381 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((13711617223821 / 8000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(13711617223821 / 8000000000000) = 1/(125000000000 / 13711617223821) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (587210623 / 125000000) (4697684991 / 1000000000) (Real.log (13711617223821 / 125000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (13711617223821 / 125000000000) = -Real.log (125000000000 / 13711617223821) := by
    rw [show ((13711617223821 / 125000000000) : ℝ) = ((125000000000 / 13711617223821) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (4701994619 / 1000000000) ≤ -Real.log (500000000000 / 55083347229171) ∧
    -Real.log (500000000000 / 55083347229171) ≤ (2350997313 / 500000000) := by
  have h := checkLog_sound (w := (23083347229171 / 87083347229171)) (n := 12)
    (lo := (543111539 / 1000000000)) (hi := (27155577 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((55083347229171 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(55083347229171 / 32000000000000) = 1/(500000000000 / 55083347229171) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (4701994619 / 1000000000) (2350997313 / 500000000) (Real.log (55083347229171 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (55083347229171 / 500000000000) = -Real.log (500000000000 / 55083347229171) := by
    rw [show ((55083347229171 / 500000000000) : ℝ) = ((500000000000 / 55083347229171) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0012
