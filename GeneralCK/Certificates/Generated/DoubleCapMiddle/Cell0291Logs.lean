import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0291
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

theorem reflection_log_1_neg : (113015003 / 500000000) ≤ -Real.log (10240 / 12837) ∧
    -Real.log (10240 / 12837) ≤ (226030007 / 1000000000) := by
  have h := checkLog_sound (w := (2597 / 23077)) (n := 12)
    (lo := (113015003 / 500000000)) (hi := (226030007 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12837 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12837 / 10240) = 1/(10240 / 12837) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (113015003 / 500000000) (226030007 / 1000000000) (Real.log (12837 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12837 / 10240) = -Real.log (10240 / 12837) := by
    rw [show ((12837 / 10240) : ℝ) = ((10240 / 12837) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (292511423 / 1000000000) ≤ -Real.log (7643 / 10240) ∧
    -Real.log (7643 / 10240) ≤ (4570491 / 15625000) := by
  have h := checkLog_sound (w := (2597 / 17883)) (n := 12)
    (lo := (292511423 / 1000000000)) (hi := (4570491 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7643) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7643) = 1/(7643 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-4570491 / 15625000) (-292511423 / 1000000000) (Real.log (7643 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (225796279 / 1000000000) ≤ -Real.log (5120 / 6417) ∧
    -Real.log (5120 / 6417) ≤ (5644907 / 25000000) := by
  have h := checkLog_sound (w := (1297 / 11537)) (n := 12)
    (lo := (225796279 / 1000000000)) (hi := (5644907 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6417 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6417 / 5120) = 1/(5120 / 6417) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (225796279 / 1000000000) (5644907 / 25000000) (Real.log (6417 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6417 / 5120) = -Real.log (5120 / 6417) := by
    rw [show ((6417 / 5120) : ℝ) = ((5120 / 6417) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (36514873 / 125000000) ≤ -Real.log (3823 / 5120) ∧
    -Real.log (3823 / 5120) ≤ (58423797 / 200000000) := by
  have h := checkLog_sound (w := (1297 / 8943)) (n := 12)
    (lo := (36514873 / 125000000)) (hi := (58423797 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3823) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3823) = 1/(3823 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-58423797 / 200000000) (-36514873 / 125000000) (Real.log (3823 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (25641953 / 62500000) ≤ -Real.log (5120 / 7717) ∧
    -Real.log (5120 / 7717) ≤ (410271249 / 1000000000) := by
  have h := checkLog_sound (w := (2597 / 12837)) (n := 12)
    (lo := (25641953 / 62500000)) (hi := (410271249 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7717 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7717 / 5120) = 1/(5120 / 7717) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (25641953 / 62500000) (410271249 / 1000000000) (Real.log (7717 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (7717 / 5120) = -Real.log (5120 / 7717) := by
    rw [show ((7717 / 5120) : ℝ) = ((5120 / 7717) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (88463221 / 125000000) ≤ -Real.log (2523 / 5120) ∧
    -Real.log (2523 / 5120) ≤ (70770577 / 100000000) := by
  have h := checkLog_sound (w := (37 / 5083)) (n := 12)
    (lo := (3639647 / 250000000)) (hi := (14558589 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 2523) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(2560 / 2523) = 1/(2523 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-70770577 / 100000000) (-88463221 / 125000000) (Real.log (2523 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (20494121 / 50000000) ≤ -Real.log (2560 / 3857) ∧
    -Real.log (2560 / 3857) ≤ (409882421 / 1000000000) := by
  have h := checkLog_sound (w := (1297 / 6417)) (n := 12)
    (lo := (20494121 / 50000000)) (hi := (409882421 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3857 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3857 / 2560) = 1/(2560 / 3857) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (20494121 / 50000000) (409882421 / 1000000000) (Real.log (3857 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (3857 / 2560) = -Real.log (2560 / 3857) := by
    rw [show ((3857 / 2560) : ℝ) = ((2560 / 3857) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (353258707 / 500000000) ≤ -Real.log (1263 / 2560) ∧
    -Real.log (1263 / 2560) ≤ (88314677 / 125000000) := by
  have h := checkLog_sound (w := (17 / 2543)) (n := 12)
    (lo := (6685117 / 500000000)) (hi := (2674047 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 1263) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 1263) = 1/(1263 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-88314677 / 125000000) (-353258707 / 500000000) (Real.log (1263 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (309361613 / 1000000000) ≤ -Real.log (200000 / 272511) ∧
    -Real.log (200000 / 272511) ≤ (154680807 / 500000000) := by
  have h := checkLog_sound (w := (72511 / 472511)) (n := 12)
    (lo := (309361613 / 1000000000)) (hi := (154680807 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((272511 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(272511 / 200000) = 1/(200000 / 272511) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (309361613 / 1000000000) (154680807 / 500000000) (Real.log (272511 / 200000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (272511 / 200000) = -Real.log (200000 / 272511) := by
    rw [show ((272511 / 200000) : ℝ) = ((200000 / 272511) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (5628591 / 12500000) ≤ -Real.log (127489 / 200000) ∧
    -Real.log (127489 / 200000) ≤ (450287281 / 1000000000) := by
  have h := checkLog_sound (w := (72511 / 327489)) (n := 12)
    (lo := (5628591 / 12500000)) (hi := (450287281 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 127489) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 127489) = 1/(127489 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-450287281 / 1000000000) (-5628591 / 12500000) (Real.log (127489 / 200000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (154839307 / 500000000) ≤ -Real.log (1000000 / 1362987) ∧
    -Real.log (1000000 / 1362987) ≤ (61935723 / 200000000) := by
  have h := checkLog_sound (w := (362987 / 2362987)) (n := 12)
    (lo := (154839307 / 500000000)) (hi := (61935723 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1362987 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1362987 / 1000000) = 1/(1000000 / 1362987) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (154839307 / 500000000) (61935723 / 200000000) (Real.log (1362987 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1362987 / 1000000) = -Real.log (1000000 / 1362987) := by
    rw [show ((1362987 / 1000000) : ℝ) = ((1000000 / 1362987) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (90193043 / 200000000) ≤ -Real.log (637013 / 1000000) ∧
    -Real.log (637013 / 1000000) ≤ (14092663 / 31250000) := by
  have h := checkLog_sound (w := (362987 / 1637013)) (n := 12)
    (lo := (90193043 / 200000000)) (hi := (14092663 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 637013) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 637013) = 1/(637013 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-14092663 / 31250000) (-90193043 / 200000000) (Real.log (637013 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (29486641 / 125000000) ≤ -Real.log (1000000 / 1266039) ∧
    -Real.log (1000000 / 1266039) ≤ (235893129 / 1000000000) := by
  have h := checkLog_sound (w := (266039 / 2266039)) (n := 12)
    (lo := (29486641 / 125000000)) (hi := (235893129 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1266039 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1266039 / 1000000) = 1/(1000000 / 1266039) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (29486641 / 125000000) (235893129 / 1000000000) (Real.log (1266039 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1266039 / 1000000) = -Real.log (1000000 / 1266039) := by
    rw [show ((1266039 / 1000000) : ℝ) = ((1000000 / 1266039) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (61859877 / 200000000) ≤ -Real.log (733961 / 1000000) ∧
    -Real.log (733961 / 1000000) ≤ (154649693 / 500000000) := by
  have h := checkLog_sound (w := (266039 / 1733961)) (n := 12)
    (lo := (61859877 / 200000000)) (hi := (154649693 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 733961) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 733961) = 1/(733961 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-154649693 / 500000000) (-61859877 / 200000000) (Real.log (733961 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (59040609 / 250000000) ≤ -Real.log (50000 / 63319) ∧
    -Real.log (50000 / 63319) ≤ (236162437 / 1000000000) := by
  have h := checkLog_sound (w := (13319 / 113319)) (n := 12)
    (lo := (59040609 / 250000000)) (hi := (236162437 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((63319 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(63319 / 50000) = 1/(50000 / 63319) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (59040609 / 250000000) (236162437 / 1000000000) (Real.log (63319 / 50000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (63319 / 50000) = -Real.log (50000 / 63319) := by
    rw [show ((63319 / 50000) : ℝ) = ((50000 / 63319) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (61952819 / 200000000) ≤ -Real.log (36681 / 50000) ∧
    -Real.log (36681 / 50000) ≤ (605008 / 1953125) := by
  have h := checkLog_sound (w := (13319 / 86681)) (n := 12)
    (lo := (61952819 / 200000000)) (hi := (605008 / 1953125))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 36681) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 36681) = 1/(36681 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-605008 / 1953125) (-61952819 / 200000000) (Real.log (36681 / 50000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (759648893 / 1000000000) ≤ -Real.log (500000000000 / 1068762795221) ∧
    -Real.log (500000000000 / 1068762795221) ≤ (151929779 / 200000000) := by
  have h := checkLog_sound (w := (68762795221 / 2068762795221)) (n := 12)
    (lo := (66501713 / 1000000000)) (hi := (33250857 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1068762795221 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1068762795221 / 1000000000000) = 1/(500000000000 / 1068762795221) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (759648893 / 1000000000) (151929779 / 200000000) (Real.log (1068762795221 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1068762795221 / 500000000000) = -Real.log (500000000000 / 1068762795221) := by
    rw [show ((1068762795221 / 500000000000) : ℝ) = ((500000000000 / 1068762795221) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (760643829 / 1000000000) ≤ -Real.log (500000000000 / 1069826675437) ∧
    -Real.log (500000000000 / 1069826675437) ≤ (760643831 / 1000000000) := by
  have h := checkLog_sound (w := (69826675437 / 2069826675437)) (n := 12)
    (lo := (67496649 / 1000000000)) (hi := (1349933 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1069826675437 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1069826675437 / 1000000000000) = 1/(500000000000 / 1069826675437) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (760643829 / 1000000000) (760643831 / 1000000000) (Real.log (1069826675437 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1069826675437 / 500000000000) = -Real.log (500000000000 / 1069826675437) := by
    rw [show ((1069826675437 / 500000000000) : ℝ) = ((500000000000 / 1069826675437) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (272596257 / 500000000) ≤ -Real.log (250000000000 / 431235106497) ∧
    -Real.log (250000000000 / 431235106497) ≤ (109038503 / 200000000) := by
  have h := checkLog_sound (w := (181235106497 / 681235106497)) (n := 12)
    (lo := (272596257 / 500000000)) (hi := (109038503 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((431235106497 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(431235106497 / 250000000000) = 1/(250000000000 / 431235106497) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (272596257 / 500000000) (109038503 / 200000000) (Real.log (431235106497 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (431235106497 / 250000000000) = -Real.log (250000000000 / 431235106497) := by
    rw [show ((431235106497 / 250000000000) : ℝ) = ((250000000000 / 431235106497) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (136481633 / 250000000) ≤ -Real.log (500000000000 / 863103514081) ∧
    -Real.log (500000000000 / 863103514081) ≤ (545926533 / 1000000000) := by
  have h := checkLog_sound (w := (363103514081 / 1363103514081)) (n := 12)
    (lo := (136481633 / 250000000)) (hi := (545926533 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((863103514081 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(863103514081 / 500000000000) = 1/(500000000000 / 863103514081) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (136481633 / 250000000) (545926533 / 1000000000) (Real.log (863103514081 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (863103514081 / 500000000000) = -Real.log (500000000000 / 863103514081) := by
    rw [show ((863103514081 / 500000000000) : ℝ) = ((500000000000 / 863103514081) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0291
