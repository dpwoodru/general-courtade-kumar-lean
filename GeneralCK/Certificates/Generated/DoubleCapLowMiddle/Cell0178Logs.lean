import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0178
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

theorem reflection_log_1_neg : (314595911 / 500000000) ≤ -Real.log (6400 / 12007) ∧
    -Real.log (6400 / 12007) ≤ (629191823 / 1000000000) := by
  have h := checkLog_sound (w := (5607 / 18407)) (n := 12)
    (lo := (314595911 / 500000000)) (hi := (629191823 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12007 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12007 / 6400) = 1/(6400 / 12007) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (314595911 / 500000000) (629191823 / 1000000000) (Real.log (12007 / 6400)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12007 / 6400) = -Real.log (6400 / 12007) := by
    rw [show ((12007 / 6400) : ℝ) = ((6400 / 12007) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (1044115023 / 500000000) ≤ -Real.log (793 / 6400) ∧
    -Real.log (793 / 6400) ≤ (41764601 / 20000000) := by
  have h := checkLog_sound (w := (7 / 1593)) (n := 12)
    (lo := (4394253 / 500000000)) (hi := (8788507 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 793) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(800 / 793) = 1/(793 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-41764601 / 20000000) (-1044115023 / 500000000) (Real.log (793 / 6400)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (627608159 / 1000000000) ≤ -Real.log (1600 / 2997) ∧
    -Real.log (1600 / 2997) ≤ (3922551 / 6250000) := by
  have h := checkLog_sound (w := (1397 / 4597)) (n := 12)
    (lo := (627608159 / 1000000000)) (hi := (3922551 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2997 / 1600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2997 / 1600) = 1/(1600 / 2997) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (627608159 / 1000000000) (3922551 / 6250000) (Real.log (2997 / 1600)) := by
  have h := reflection_log_3_neg
  have he : Real.log (2997 / 1600) = -Real.log (1600 / 2997) := by
    rw [show ((2997 / 1600) : ℝ) = ((1600 / 2997) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (64517279 / 31250000) ≤ -Real.log (203 / 1600) ∧
    -Real.log (203 / 1600) ≤ (2064552931 / 1000000000) := by
  have h := checkLog_sound (w := (197 / 603)) (n := 12)
    (lo := (84782321 / 125000000)) (hi := (678258569 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 203) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(400 / 203) = 1/(203 / 1600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-2064552931 / 1000000000) (-64517279 / 31250000) (Real.log (203 / 1600)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (560865007 / 1000000000) ≤ -Real.log (3200 / 5607) ∧
    -Real.log (3200 / 5607) ≤ (35054063 / 62500000) := by
  have h := checkLog_sound (w := (2407 / 8807)) (n := 12)
    (lo := (560865007 / 1000000000)) (hi := (35054063 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5607 / 3200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5607 / 3200) = 1/(3200 / 5607) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (560865007 / 1000000000) (35054063 / 62500000) (Real.log (5607 / 3200)) := by
  have h := reflection_log_5_neg
  have he : Real.log (5607 / 3200) = -Real.log (3200 / 5607) := by
    rw [show ((5607 / 3200) : ℝ) = ((3200 / 5607) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (697541433 / 500000000) ≤ -Real.log (793 / 3200) ∧
    -Real.log (793 / 3200) ≤ (1395082869 / 1000000000) := by
  have h := checkLog_sound (w := (7 / 1593)) (n := 12)
    (lo := (4394253 / 500000000)) (hi := (8788507 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 793) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(800 / 793) = 1/(793 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1395082869 / 1000000000) (-697541433 / 500000000) (Real.log (793 / 3200)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (557470631 / 1000000000) ≤ -Real.log (800 / 1397) ∧
    -Real.log (800 / 1397) ≤ (69683829 / 125000000) := by
  have h := checkLog_sound (w := (597 / 2197)) (n := 12)
    (lo := (557470631 / 1000000000)) (hi := (69683829 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1397 / 800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1397 / 800) = 1/(800 / 1397) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (557470631 / 1000000000) (69683829 / 125000000) (Real.log (1397 / 800)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1397 / 800) = -Real.log (800 / 1397) := by
    rw [show ((1397 / 800) : ℝ) = ((800 / 1397) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (342851437 / 250000000) ≤ -Real.log (203 / 800) ∧
    -Real.log (203 / 800) ≤ (5485623 / 4000000) := by
  have h := checkLog_sound (w := (197 / 603)) (n := 12)
    (lo := (84782321 / 125000000)) (hi := (678258569 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 203) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(400 / 203) = 1/(203 / 800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-5485623 / 4000000) (-342851437 / 250000000) (Real.log (203 / 800)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (644791671 / 1000000000) ≤ -Real.log (100000 / 190559) ∧
    -Real.log (100000 / 190559) ≤ (80598959 / 125000000) := by
  have h := checkLog_sound (w := (90559 / 290559)) (n := 12)
    (lo := (644791671 / 1000000000)) (hi := (80598959 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((190559 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(190559 / 100000) = 1/(100000 / 190559) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (644791671 / 1000000000) (80598959 / 125000000) (Real.log (190559 / 100000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (190559 / 100000) = -Real.log (100000 / 190559) := by
    rw [show ((190559 / 100000) : ℝ) = ((100000 / 190559) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (2360108277 / 1000000000) ≤ -Real.log (9441 / 100000) ∧
    -Real.log (9441 / 100000) ≤ (2360108281 / 1000000000) := by
  have h := checkLog_sound (w := (3059 / 21941)) (n := 12)
    (lo := (280666737 / 1000000000)) (hi := (140333369 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12500 / 9441) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(12500 / 9441) = 1/(9441 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-2360108281 / 1000000000) (-2360108277 / 1000000000) (Real.log (9441 / 100000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (40362191 / 62500000) ≤ -Real.log (1000000 / 1907503) ∧
    -Real.log (1000000 / 1907503) ≤ (645795057 / 1000000000) := by
  have h := checkLog_sound (w := (907503 / 2907503)) (n := 12)
    (lo := (40362191 / 62500000)) (hi := (645795057 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1907503 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1907503 / 1000000) = 1/(1000000 / 1907503) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (40362191 / 62500000) (645795057 / 1000000000) (Real.log (1907503 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1907503 / 1000000) = -Real.log (1000000 / 1907503) := by
    rw [show ((1907503 / 1000000) : ℝ) = ((1000000 / 1907503) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (476115813 / 200000000) ≤ -Real.log (92497 / 1000000) ∧
    -Real.log (92497 / 1000000) ≤ (2380579069 / 1000000000) := by
  have h := checkLog_sound (w := (32503 / 217497)) (n := 12)
    (lo := (12045501 / 40000000)) (hi := (150568763 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 92497) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125000 / 92497) = 1/(92497 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-2380579069 / 1000000000) (-476115813 / 200000000) (Real.log (92497 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (321308639 / 500000000) ≤ -Real.log (1000000 / 1901451) ∧
    -Real.log (1000000 / 1901451) ≤ (642617279 / 1000000000) := by
  have h := checkLog_sound (w := (901451 / 2901451)) (n := 12)
    (lo := (321308639 / 500000000)) (hi := (642617279 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1901451 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1901451 / 1000000) = 1/(1000000 / 1901451) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (321308639 / 500000000) (642617279 / 1000000000) (Real.log (1901451 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1901451 / 1000000) = -Real.log (1000000 / 1901451) := by
    rw [show ((1901451 / 1000000) : ℝ) = ((1000000 / 1901451) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (231720139 / 100000000) ≤ -Real.log (98549 / 1000000) ∧
    -Real.log (98549 / 1000000) ≤ (1158600697 / 500000000) := by
  have h := checkLog_sound (w := (26451 / 223549)) (n := 12)
    (lo := (4755197 / 20000000)) (hi := (237759851 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 98549) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125000 / 98549) = 1/(98549 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-1158600697 / 500000000) (-231720139 / 100000000) (Real.log (98549 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (643741577 / 1000000000) ≤ -Real.log (100000 / 190359) ∧
    -Real.log (100000 / 190359) ≤ (321870789 / 500000000) := by
  have h := checkLog_sound (w := (90359 / 290359)) (n := 12)
    (lo := (643741577 / 1000000000)) (hi := (321870789 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((190359 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(190359 / 100000) = 1/(100000 / 190359) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (643741577 / 1000000000) (321870789 / 500000000) (Real.log (190359 / 100000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (190359 / 100000) = -Real.log (100000 / 190359) := by
    rw [show ((190359 / 100000) : ℝ) = ((100000 / 190359) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (1169572673 / 500000000) ≤ -Real.log (9641 / 100000) ∧
    -Real.log (9641 / 100000) ≤ (46782907 / 20000000) := by
  have h := checkLog_sound (w := (2859 / 22141)) (n := 12)
    (lo := (129851903 / 500000000)) (hi := (259703807 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12500 / 9641) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(12500 / 9641) = 1/(9641 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-46782907 / 20000000) (-1169572673 / 500000000) (Real.log (9641 / 100000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (751224987 / 250000000) ≤ -Real.log (31250000000 / 630756143417) ∧
    -Real.log (31250000000 / 630756143417) ≤ (3004899953 / 1000000000) := by
  have h := checkLog_sound (w := (130756143417 / 1130756143417)) (n := 12)
    (lo := (58077807 / 250000000)) (hi := (232311229 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((630756143417 / 500000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(630756143417 / 500000000000) = 1/(31250000000 / 630756143417) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (751224987 / 250000000) (3004899953 / 1000000000) (Real.log (630756143417 / 31250000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (630756143417 / 31250000000) = -Real.log (31250000000 / 630756143417) := by
    rw [show ((630756143417 / 31250000000) : ℝ) = ((31250000000 / 630756143417) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1513187061 / 500000000) ≤ -Real.log (250000000000 / 5155580721537) ∧
    -Real.log (250000000000 / 5155580721537) ≤ (3026374127 / 1000000000) := by
  have h := checkLog_sound (w := (1155580721537 / 9155580721537)) (n := 12)
    (lo := (126892701 / 500000000)) (hi := (253785403 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5155580721537 / 4000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(5155580721537 / 4000000000000) = 1/(250000000000 / 5155580721537) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1513187061 / 500000000) (3026374127 / 1000000000) (Real.log (5155580721537 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (5155580721537 / 250000000000) = -Real.log (250000000000 / 5155580721537) := by
    rw [show ((5155580721537 / 250000000000) : ℝ) = ((250000000000 / 5155580721537) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (2959818669 / 1000000000) ≤ -Real.log (250000000000 / 4823618200083) ∧
    -Real.log (250000000000 / 4823618200083) ≤ (1479909337 / 500000000) := by
  have h := checkLog_sound (w := (823618200083 / 8823618200083)) (n := 12)
    (lo := (187229949 / 1000000000)) (hi := (3744599 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4823618200083 / 4000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(4823618200083 / 4000000000000) = 1/(250000000000 / 4823618200083) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (2959818669 / 1000000000) (1479909337 / 500000000) (Real.log (4823618200083 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (4823618200083 / 250000000000) = -Real.log (250000000000 / 4823618200083) := by
    rw [show ((4823618200083 / 250000000000) : ℝ) = ((250000000000 / 4823618200083) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (2982886923 / 1000000000) ≤ -Real.log (250000000000 / 4936184005809) ∧
    -Real.log (250000000000 / 4936184005809) ≤ (186430433 / 62500000) := by
  have h := checkLog_sound (w := (936184005809 / 8936184005809)) (n := 12)
    (lo := (210298203 / 1000000000)) (hi := (52574551 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4936184005809 / 4000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(4936184005809 / 4000000000000) = 1/(250000000000 / 4936184005809) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (2982886923 / 1000000000) (186430433 / 62500000) (Real.log (4936184005809 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (4936184005809 / 250000000000) = -Real.log (250000000000 / 4936184005809) := by
    rw [show ((4936184005809 / 250000000000) : ℝ) = ((250000000000 / 4936184005809) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0178
