import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_12032_neg : (29734597 / 500000000) ≤ -Real.log (235566140119 / 250000000000) ∧
    -Real.log (235566140119 / 250000000000) ≤ (11893839 / 200000000) := by
  have h := checkLog_sound (w := (14433859881 / 485566140119)) (n := 12)
    (lo := (29734597 / 500000000)) (hi := (11893839 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 235566140119) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 235566140119) = 1/(235566140119 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12032 : Bounds (-11893839 / 200000000) (-29734597 / 500000000) (Real.log (235566140119 / 250000000000)) := by
  have h := reflection_log_12032_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12033_neg : (24507337 / 50000000) ≤ -Real.log (62500000000 / 102034735257) ∧
    -Real.log (62500000000 / 102034735257) ≤ (490146741 / 1000000000) := by
  have h := checkLog_sound (w := (39534735257 / 164534735257)) (n := 12)
    (lo := (24507337 / 50000000)) (hi := (490146741 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((102034735257 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(102034735257 / 62500000000) = 1/(62500000000 / 102034735257) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12033 : Bounds (24507337 / 50000000) (490146741 / 1000000000) (Real.log (102034735257 / 62500000000)) := by
  have h := reflection_log_12033_neg
  have he : Real.log (102034735257 / 62500000000) = -Real.log (62500000000 / 102034735257) := by
    rw [show ((102034735257 / 62500000000) : ℝ) = ((62500000000 / 102034735257) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12034_neg : (492286817 / 1000000000) ≤ -Real.log (500000000000 / 818026650499) ∧
    -Real.log (500000000000 / 818026650499) ≤ (246143409 / 500000000) := by
  have h := checkLog_sound (w := (318026650499 / 1318026650499)) (n := 12)
    (lo := (492286817 / 1000000000)) (hi := (246143409 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((818026650499 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(818026650499 / 500000000000) = 1/(500000000000 / 818026650499) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12034 : Bounds (492286817 / 1000000000) (246143409 / 500000000) (Real.log (818026650499 / 500000000000)) := by
  have h := reflection_log_12034_neg
  have he : Real.log (818026650499 / 500000000000) = -Real.log (500000000000 / 818026650499) := by
    rw [show ((818026650499 / 500000000000) : ℝ) = ((500000000000 / 818026650499) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12035_neg : (999702079 / 1000000000) ≤ -Real.log (500000000000 / 1358736059479) ∧
    -Real.log (500000000000 / 1358736059479) ≤ (999702081 / 1000000000) := by
  have h := checkLog_sound (w := (358736059479 / 2358736059479)) (n := 12)
    (lo := (306554899 / 1000000000)) (hi := (3065549 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1358736059479 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1358736059479 / 1000000000000) = 1/(500000000000 / 1358736059479) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12035 : Bounds (999702079 / 1000000000) (999702081 / 1000000000) (Real.log (1358736059479 / 500000000000)) := by
  have h := reflection_log_12035_neg
  have he : Real.log (1358736059479 / 500000000000) = -Real.log (500000000000 / 1358736059479) := by
    rw [show ((1358736059479 / 500000000000) : ℝ) = ((500000000000 / 1358736059479) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12036_neg : (200449261 / 200000000) ≤ -Real.log (125000000000 / 340549348231) ∧
    -Real.log (125000000000 / 340549348231) ≤ (1002246307 / 1000000000) := by
  have h := checkLog_sound (w := (90549348231 / 590549348231)) (n := 12)
    (lo := (2472793 / 8000000)) (hi := (154549563 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((340549348231 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(340549348231 / 250000000000) = 1/(125000000000 / 340549348231) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12036 : Bounds (200449261 / 200000000) (1002246307 / 1000000000) (Real.log (340549348231 / 125000000000)) := by
  have h := reflection_log_12036_neg
  have he : Real.log (340549348231 / 125000000000) = -Real.log (125000000000 / 340549348231) := by
    rw [show ((340549348231 / 125000000000) : ℝ) = ((125000000000 / 340549348231) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12037_neg : (76234483 / 200000000) ≤ -Real.log (125 / 183) ∧
    -Real.log (125 / 183) ≤ (5955819 / 15625000) := by
  have h := checkLog_sound (w := (29 / 154)) (n := 12)
    (lo := (76234483 / 200000000)) (hi := (5955819 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((183 / 125) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(183 / 125) = 1/(125 / 183) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12037 : Bounds (76234483 / 200000000) (5955819 / 15625000) (Real.log (183 / 125)) := by
  have h := reflection_log_12037_neg
  have he : Real.log (183 / 125) = -Real.log (125 / 183) := by
    rw [show ((183 / 125) : ℝ) = ((125 / 183) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12038_neg : (623621117 / 1000000000) ≤ -Real.log (67 / 125) ∧
    -Real.log (67 / 125) ≤ (311810559 / 500000000) := by
  have h := checkLog_sound (w := (29 / 96)) (n := 12)
    (lo := (623621117 / 1000000000)) (hi := (311810559 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 67) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125 / 67) = 1/(67 / 125) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12038 : Bounds (-311810559 / 500000000) (-623621117 / 1000000000) (Real.log (67 / 125)) := by
  have h := reflection_log_12038_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12039_neg : (115973 / 250000000) ≤ -Real.log (62500 / 62529) ∧
    -Real.log (62500 / 62529) ≤ (463893 / 1000000000) := by
  have h := checkLog_sound (w := (29 / 125029)) (n := 12)
    (lo := (115973 / 250000000)) (hi := (463893 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62529 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62529 / 62500) = 1/(62500 / 62529) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12039 : Bounds (115973 / 250000000) (463893 / 1000000000) (Real.log (62529 / 62500)) := by
  have h := reflection_log_12039_neg
  have he : Real.log (62529 / 62500) = -Real.log (62500 / 62529) := by
    rw [show ((62529 / 62500) : ℝ) = ((62500 / 62529) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12040_neg : (464107 / 1000000000) ≤ -Real.log (62471 / 62500) ∧
    -Real.log (62471 / 62500) ≤ (116027 / 250000000) := by
  have h := checkLog_sound (w := (29 / 124971)) (n := 12)
    (lo := (464107 / 1000000000)) (hi := (116027 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 62471) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 62471) = 1/(62471 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12040 : Bounds (-116027 / 250000000) (-464107 / 1000000000) (Real.log (62471 / 62500)) := by
  have h := reflection_log_12040_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12041_neg : (21579421 / 100000000) ≤ -Real.log (1000000 / 1240847) ∧
    -Real.log (1000000 / 1240847) ≤ (215794211 / 1000000000) := by
  have h := checkLog_sound (w := (240847 / 2240847)) (n := 12)
    (lo := (21579421 / 100000000)) (hi := (215794211 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1240847 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1240847 / 1000000) = 1/(1000000 / 1240847) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12041 : Bounds (21579421 / 100000000) (215794211 / 1000000000) (Real.log (1240847 / 1000000)) := by
  have h := reflection_log_12041_neg
  have he : Real.log (1240847 / 1000000) = -Real.log (1000000 / 1240847) := by
    rw [show ((1240847 / 1000000) : ℝ) = ((1000000 / 1240847) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12042_neg : (13777597 / 50000000) ≤ -Real.log (759153 / 1000000) ∧
    -Real.log (759153 / 1000000) ≤ (275551941 / 1000000000) := by
  have h := checkLog_sound (w := (240847 / 1759153)) (n := 12)
    (lo := (13777597 / 50000000)) (hi := (275551941 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 759153) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 759153) = 1/(759153 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12042 : Bounds (-275551941 / 1000000000) (-13777597 / 50000000) (Real.log (759153 / 1000000)) := by
  have h := reflection_log_12042_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12043_neg : (108303517 / 500000000) ≤ -Real.log (15625 / 19404) ∧
    -Real.log (15625 / 19404) ≤ (43321407 / 200000000) := by
  have h := checkLog_sound (w := (3779 / 35029)) (n := 12)
    (lo := (108303517 / 500000000)) (hi := (43321407 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((19404 / 15625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(19404 / 15625) = 1/(15625 / 19404) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12043 : Bounds (108303517 / 500000000) (43321407 / 200000000) (Real.log (19404 / 15625)) := by
  have h := reflection_log_12043_neg
  have he : Real.log (19404 / 15625) = -Real.log (15625 / 19404) := by
    rw [show ((19404 / 15625) : ℝ) = ((15625 / 19404) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12044_neg : (276881937 / 1000000000) ≤ -Real.log (11846 / 15625) ∧
    -Real.log (11846 / 15625) ≤ (138440969 / 500000000) := by
  have h := checkLog_sound (w := (3779 / 27471)) (n := 12)
    (lo := (276881937 / 1000000000)) (hi := (138440969 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 11846) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625 / 11846) = 1/(11846 / 15625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12044 : Bounds (-138440969 / 500000000) (-276881937 / 1000000000) (Real.log (11846 / 15625)) := by
  have h := reflection_log_12044_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12045_neg : (60274903 / 1000000000) ≤ -Real.log (229859784 / 244140625) ∧
    -Real.log (229859784 / 244140625) ≤ (7534363 / 125000000) := by
  have h := checkLog_sound (w := (14280841 / 474000409)) (n := 12)
    (lo := (60274903 / 1000000000)) (hi := (7534363 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((244140625 / 229859784) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(244140625 / 229859784) = 1/(229859784 / 244140625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12045 : Bounds (-7534363 / 125000000) (-60274903 / 1000000000) (Real.log (229859784 / 244140625)) := by
  have h := reflection_log_12045_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12046_neg : (59757729 / 1000000000) ≤ -Real.log (941992722591 / 1000000000000) ∧
    -Real.log (941992722591 / 1000000000000) ≤ (5975773 / 100000000) := by
  have h := checkLog_sound (w := (58007277409 / 1941992722591)) (n := 12)
    (lo := (59757729 / 1000000000)) (hi := (5975773 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 941992722591) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 941992722591) = 1/(941992722591 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12046 : Bounds (-5975773 / 100000000) (-59757729 / 1000000000) (Real.log (941992722591 / 1000000000000)) := by
  have h := reflection_log_12046_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12047_neg : (491346151 / 1000000000) ≤ -Real.log (15625000000 / 25539297579) ∧
    -Real.log (15625000000 / 25539297579) ≤ (61418269 / 125000000) := by
  have h := checkLog_sound (w := (9914297579 / 41164297579)) (n := 12)
    (lo := (491346151 / 1000000000)) (hi := (61418269 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25539297579 / 15625000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25539297579 / 15625000000) = 1/(15625000000 / 25539297579) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12047 : Bounds (491346151 / 1000000000) (61418269 / 125000000) (Real.log (25539297579 / 15625000000)) := by
  have h := reflection_log_12047_neg
  have he : Real.log (25539297579 / 15625000000) = -Real.log (15625000000 / 25539297579) := by
    rw [show ((25539297579 / 15625000000) : ℝ) = ((15625000000 / 25539297579) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12048_neg : (123372243 / 250000000) ≤ -Real.log (250000000000 / 409505318251) ∧
    -Real.log (250000000000 / 409505318251) ≤ (493488973 / 1000000000) := by
  have h := checkLog_sound (w := (159505318251 / 659505318251)) (n := 12)
    (lo := (123372243 / 250000000)) (hi := (493488973 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((409505318251 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(409505318251 / 250000000000) = 1/(250000000000 / 409505318251) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12048 : Bounds (123372243 / 250000000) (493488973 / 1000000000) (Real.log (409505318251 / 250000000000)) := by
  have h := reflection_log_12048_neg
  have he : Real.log (409505318251 / 250000000000) = -Real.log (250000000000 / 409505318251) := by
    rw [show ((409505318251 / 250000000000) : ℝ) = ((250000000000 / 409505318251) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12049_neg : (200449261 / 200000000) ≤ -Real.log (500000000000 / 1362197392923) ∧
    -Real.log (500000000000 / 1362197392923) ≤ (1002246307 / 1000000000) := by
  have h := checkLog_sound (w := (362197392923 / 2362197392923)) (n := 12)
    (lo := (2472793 / 8000000)) (hi := (154549563 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1362197392923 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1362197392923 / 1000000000000) = 1/(500000000000 / 1362197392923) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12049 : Bounds (200449261 / 200000000) (1002246307 / 1000000000) (Real.log (1362197392923 / 500000000000)) := by
  have h := reflection_log_12049_neg
  have he : Real.log (1362197392923 / 500000000000) = -Real.log (500000000000 / 1362197392923) := by
    rw [show ((1362197392923 / 500000000000) : ℝ) = ((500000000000 / 1362197392923) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12050_neg : (251198383 / 250000000) ≤ -Real.log (7812500000 / 21338619403) ∧
    -Real.log (7812500000 / 21338619403) ≤ (502396767 / 500000000) := by
  have h := checkLog_sound (w := (5713619403 / 36963619403)) (n := 12)
    (lo := (19477897 / 62500000)) (hi := (311646353 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((21338619403 / 15625000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(21338619403 / 15625000000) = 1/(7812500000 / 21338619403) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12050 : Bounds (251198383 / 250000000) (502396767 / 500000000) (Real.log (21338619403 / 7812500000)) := by
  have h := reflection_log_12050_neg
  have he : Real.log (21338619403 / 7812500000) = -Real.log (7812500000 / 21338619403) := by
    rw [show ((21338619403 / 7812500000) : ℝ) = ((7812500000 / 21338619403) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12051_neg : (190927621 / 500000000) ≤ -Real.log (200 / 293) ∧
    -Real.log (200 / 293) ≤ (381855243 / 1000000000) := by
  have h := checkLog_sound (w := (93 / 493)) (n := 12)
    (lo := (190927621 / 500000000)) (hi := (381855243 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((293 / 200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(293 / 200) = 1/(200 / 293) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12051 : Bounds (190927621 / 500000000) (381855243 / 1000000000) (Real.log (293 / 200)) := by
  have h := reflection_log_12051_neg
  have he : Real.log (293 / 200) = -Real.log (200 / 293) := by
    rw [show ((293 / 200) : ℝ) = ((200 / 293) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12052_neg : (156372133 / 250000000) ≤ -Real.log (107 / 200) ∧
    -Real.log (107 / 200) ≤ (625488533 / 1000000000) := by
  have h := checkLog_sound (w := (93 / 307)) (n := 12)
    (lo := (156372133 / 250000000)) (hi := (625488533 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200 / 107) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200 / 107) = 1/(107 / 200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12052 : Bounds (-625488533 / 1000000000) (-156372133 / 250000000) (Real.log (107 / 200)) := by
  have h := reflection_log_12052_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12053_neg : (464891 / 1000000000) ≤ -Real.log (200000 / 200093) ∧
    -Real.log (200000 / 200093) ≤ (116223 / 250000000) := by
  have h := checkLog_sound (w := (93 / 400093)) (n := 12)
    (lo := (464891 / 1000000000)) (hi := (116223 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200093 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200093 / 200000) = 1/(200000 / 200093) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12053 : Bounds (464891 / 1000000000) (116223 / 250000000) (Real.log (200093 / 200000)) := by
  have h := reflection_log_12053_neg
  have he : Real.log (200093 / 200000) = -Real.log (200000 / 200093) := by
    rw [show ((200093 / 200000) : ℝ) = ((200000 / 200093) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12054_neg : (116277 / 250000000) ≤ -Real.log (199907 / 200000) ∧
    -Real.log (199907 / 200000) ≤ (465109 / 1000000000) := by
  have h := checkLog_sound (w := (93 / 399907)) (n := 12)
    (lo := (116277 / 250000000)) (hi := (465109 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 199907) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 199907) = 1/(199907 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12054 : Bounds (-465109 / 1000000000) (-116277 / 250000000) (Real.log (199907 / 200000)) := by
  have h := reflection_log_12054_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12055_neg : (43249727 / 200000000) ≤ -Real.log (1000000 / 1241411) ∧
    -Real.log (1000000 / 1241411) ≤ (54062159 / 250000000) := by
  have h := checkLog_sound (w := (241411 / 2241411)) (n := 12)
    (lo := (43249727 / 200000000)) (hi := (54062159 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1241411 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1241411 / 1000000) = 1/(1000000 / 1241411) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12055 : Bounds (43249727 / 200000000) (54062159 / 250000000) (Real.log (1241411 / 1000000)) := by
  have h := reflection_log_12055_neg
  have he : Real.log (1241411 / 1000000) = -Real.log (1000000 / 1241411) := by
    rw [show ((1241411 / 1000000) : ℝ) = ((1000000 / 1241411) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12056_neg : (5525903 / 20000000) ≤ -Real.log (758589 / 1000000) ∧
    -Real.log (758589 / 1000000) ≤ (276295151 / 1000000000) := by
  have h := checkLog_sound (w := (241411 / 1758589)) (n := 12)
    (lo := (5525903 / 20000000)) (hi := (276295151 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 758589) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 758589) = 1/(758589 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12056 : Bounds (-276295151 / 1000000000) (-5525903 / 20000000) (Real.log (758589 / 1000000)) := by
  have h := reflection_log_12056_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12057_neg : (2170627 / 10000000) ≤ -Real.log (500000 / 621211) ∧
    -Real.log (500000 / 621211) ≤ (217062701 / 1000000000) := by
  have h := checkLog_sound (w := (121211 / 1121211)) (n := 12)
    (lo := (2170627 / 10000000)) (hi := (217062701 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((621211 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(621211 / 500000) = 1/(500000 / 621211) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12057 : Bounds (2170627 / 10000000) (217062701 / 1000000000) (Real.log (621211 / 500000)) := by
  have h := reflection_log_12057_neg
  have he : Real.log (621211 / 500000) = -Real.log (500000 / 621211) := by
    rw [show ((621211 / 500000) : ℝ) = ((500000 / 621211) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12058_neg : (34703597 / 125000000) ≤ -Real.log (378789 / 500000) ∧
    -Real.log (378789 / 500000) ≤ (277628777 / 1000000000) := by
  have h := checkLog_sound (w := (121211 / 878789)) (n := 12)
    (lo := (34703597 / 125000000)) (hi := (277628777 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 378789) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 378789) = 1/(378789 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12058 : Bounds (-277628777 / 1000000000) (-34703597 / 125000000) (Real.log (378789 / 500000)) := by
  have h := reflection_log_12058_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12059_neg : (15141519 / 250000000) ≤ -Real.log (235307893479 / 250000000000) ∧
    -Real.log (235307893479 / 250000000000) ≤ (60566077 / 1000000000) := by
  have h := checkLog_sound (w := (14692106521 / 485307893479)) (n := 12)
    (lo := (15141519 / 250000000)) (hi := (60566077 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 235307893479) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 235307893479) = 1/(235307893479 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12059 : Bounds (-60566077 / 1000000000) (-15141519 / 250000000) (Real.log (235307893479 / 250000000000)) := by
  have h := reflection_log_12059_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12060_neg : (30023257 / 500000000) ≤ -Real.log (941720729079 / 1000000000000) ∧
    -Real.log (941720729079 / 1000000000000) ≤ (12009303 / 200000000) := by
  have h := checkLog_sound (w := (58279270921 / 1941720729079)) (n := 12)
    (lo := (30023257 / 500000000)) (hi := (12009303 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 941720729079) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 941720729079) = 1/(941720729079 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12060 : Bounds (-12009303 / 200000000) (-30023257 / 500000000) (Real.log (941720729079 / 1000000000000)) := by
  have h := reflection_log_12060_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12061_neg : (246271893 / 500000000) ≤ -Real.log (500000000000 / 818236884531) ∧
    -Real.log (500000000000 / 818236884531) ≤ (492543787 / 1000000000) := by
  have h := checkLog_sound (w := (318236884531 / 1318236884531)) (n := 12)
    (lo := (246271893 / 500000000)) (hi := (492543787 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((818236884531 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(818236884531 / 500000000000) = 1/(500000000000 / 818236884531) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12061 : Bounds (246271893 / 500000000) (492543787 / 1000000000) (Real.log (818236884531 / 500000000000)) := by
  have h := reflection_log_12061_neg
  have he : Real.log (818236884531 / 500000000000) = -Real.log (500000000000 / 818236884531) := by
    rw [show ((818236884531 / 500000000000) : ℝ) = ((500000000000 / 818236884531) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12062_neg : (123672869 / 250000000) ≤ -Real.log (125000000000 / 204999023203) ∧
    -Real.log (125000000000 / 204999023203) ≤ (494691477 / 1000000000) := by
  have h := checkLog_sound (w := (79999023203 / 329999023203)) (n := 12)
    (lo := (123672869 / 250000000)) (hi := (494691477 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((204999023203 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(204999023203 / 125000000000) = 1/(125000000000 / 204999023203) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12062 : Bounds (123672869 / 250000000) (494691477 / 1000000000) (Real.log (204999023203 / 125000000000)) := by
  have h := reflection_log_12062_neg
  have he : Real.log (204999023203 / 125000000000) = -Real.log (125000000000 / 204999023203) := by
    rw [show ((204999023203 / 125000000000) : ℝ) = ((125000000000 / 204999023203) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12063_neg : (251198383 / 250000000) ≤ -Real.log (500000000000 / 1365671641791) ∧
    -Real.log (500000000000 / 1365671641791) ≤ (502396767 / 500000000) := by
  have h := checkLog_sound (w := (365671641791 / 2365671641791)) (n := 12)
    (lo := (19477897 / 62500000)) (hi := (311646353 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1365671641791 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1365671641791 / 1000000000000) = 1/(500000000000 / 1365671641791) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12063 : Bounds (251198383 / 250000000) (502396767 / 500000000) (Real.log (1365671641791 / 500000000000)) := by
  have h := reflection_log_12063_neg
  have he : Real.log (1365671641791 / 500000000000) = -Real.log (500000000000 / 1365671641791) := by
    rw [show ((1365671641791 / 500000000000) : ℝ) = ((500000000000 / 1365671641791) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12064_neg : (1007343773 / 1000000000) ≤ -Real.log (100000000000 / 273831775701) ∧
    -Real.log (100000000000 / 273831775701) ≤ (40293751 / 40000000) := by
  have h := checkLog_sound (w := (73831775701 / 473831775701)) (n := 12)
    (lo := (314196593 / 1000000000)) (hi := (157098297 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((273831775701 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(273831775701 / 200000000000) = 1/(100000000000 / 273831775701) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12064 : Bounds (1007343773 / 1000000000) (40293751 / 40000000) (Real.log (273831775701 / 100000000000)) := by
  have h := reflection_log_12064_neg
  have he : Real.log (273831775701 / 100000000000) = -Real.log (100000000000 / 273831775701) := by
    rw [show ((273831775701 / 100000000000) : ℝ) = ((100000000000 / 273831775701) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12065_neg : (382537603 / 1000000000) ≤ -Real.log (500 / 733) ∧
    -Real.log (500 / 733) ≤ (95634401 / 250000000) := by
  have h := checkLog_sound (w := (233 / 1233)) (n := 12)
    (lo := (382537603 / 1000000000)) (hi := (95634401 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((733 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(733 / 500) = 1/(500 / 733) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12065 : Bounds (382537603 / 1000000000) (95634401 / 250000000) (Real.log (733 / 500)) := by
  have h := reflection_log_12065_neg
  have he : Real.log (733 / 500) = -Real.log (500 / 733) := by
    rw [show ((733 / 500) : ℝ) = ((500 / 733) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12066_neg : (7841993 / 12500000) ≤ -Real.log (267 / 500) ∧
    -Real.log (267 / 500) ≤ (627359441 / 1000000000) := by
  have h := checkLog_sound (w := (233 / 767)) (n := 12)
    (lo := (7841993 / 12500000)) (hi := (627359441 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 267) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500 / 267) = 1/(267 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12066 : Bounds (-627359441 / 1000000000) (-7841993 / 12500000) (Real.log (267 / 500)) := by
  have h := reflection_log_12066_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12067_neg : (465891 / 1000000000) ≤ -Real.log (500000 / 500233) ∧
    -Real.log (500000 / 500233) ≤ (116473 / 250000000) := by
  have h := checkLog_sound (w := (233 / 1000233)) (n := 12)
    (lo := (465891 / 1000000000)) (hi := (116473 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500233 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500233 / 500000) = 1/(500000 / 500233) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12067 : Bounds (465891 / 1000000000) (116473 / 250000000) (Real.log (500233 / 500000)) := by
  have h := reflection_log_12067_neg
  have he : Real.log (500233 / 500000) = -Real.log (500000 / 500233) := by
    rw [show ((500233 / 500000) : ℝ) = ((500000 / 500233) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12068_neg : (116527 / 250000000) ≤ -Real.log (499767 / 500000) ∧
    -Real.log (499767 / 500000) ≤ (466109 / 1000000000) := by
  have h := checkLog_sound (w := (233 / 999767)) (n := 12)
    (lo := (116527 / 250000000)) (hi := (466109 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499767) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499767) = 1/(499767 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12068 : Bounds (-466109 / 1000000000) (-116527 / 250000000) (Real.log (499767 / 500000)) := by
  have h := reflection_log_12068_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12069_neg : (216703659 / 1000000000) ≤ -Real.log (125000 / 155247) ∧
    -Real.log (125000 / 155247) ≤ (10835183 / 50000000) := by
  have h := checkLog_sound (w := (30247 / 280247)) (n := 12)
    (lo := (216703659 / 1000000000)) (hi := (10835183 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((155247 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(155247 / 125000) = 1/(125000 / 155247) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12069 : Bounds (216703659 / 1000000000) (10835183 / 50000000) (Real.log (155247 / 125000)) := by
  have h := reflection_log_12069_neg
  have he : Real.log (155247 / 125000) = -Real.log (125000 / 155247) := by
    rw [show ((155247 / 125000) : ℝ) = ((125000 / 155247) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12070_neg : (277040231 / 1000000000) ≤ -Real.log (94753 / 125000) ∧
    -Real.log (94753 / 125000) ≤ (34630029 / 125000000) := by
  have h := checkLog_sound (w := (30247 / 219753)) (n := 12)
    (lo := (277040231 / 1000000000)) (hi := (34630029 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 94753) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 94753) = 1/(94753 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12070 : Bounds (-34630029 / 125000000) (-277040231 / 1000000000) (Real.log (94753 / 125000)) := by
  have h := reflection_log_12070_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12071_neg : (108759079 / 500000000) ≤ -Real.log (250000 / 310747) ∧
    -Real.log (250000 / 310747) ≤ (217518159 / 1000000000) := by
  have h := checkLog_sound (w := (60747 / 560747)) (n := 12)
    (lo := (108759079 / 500000000)) (hi := (217518159 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((310747 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(310747 / 250000) = 1/(250000 / 310747) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12071 : Bounds (108759079 / 500000000) (217518159 / 1000000000) (Real.log (310747 / 250000)) := by
  have h := reflection_log_12071_neg
  have he : Real.log (310747 / 250000) = -Real.log (250000 / 310747) := by
    rw [show ((310747 / 250000) : ℝ) = ((250000 / 310747) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12072_neg : (278376173 / 1000000000) ≤ -Real.log (189253 / 250000) ∧
    -Real.log (189253 / 250000) ≤ (139188087 / 500000000) := by
  have h := checkLog_sound (w := (60747 / 439253)) (n := 12)
    (lo := (278376173 / 1000000000)) (hi := (139188087 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 189253) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 189253) = 1/(189253 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12072 : Bounds (-139188087 / 500000000) (-278376173 / 1000000000) (Real.log (189253 / 250000)) := by
  have h := reflection_log_12072_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12073_neg : (12171603 / 200000000) ≤ -Real.log (58809801991 / 62500000000) ∧
    -Real.log (58809801991 / 62500000000) ≤ (1901813 / 31250000) := by
  have h := checkLog_sound (w := (3690198009 / 121309801991)) (n := 12)
    (lo := (12171603 / 200000000)) (hi := (1901813 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 58809801991) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 58809801991) = 1/(58809801991 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12073 : Bounds (-1901813 / 31250000) (-12171603 / 200000000) (Real.log (58809801991 / 62500000000)) := by
  have h := reflection_log_12073_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12074_neg : (60336571 / 1000000000) ≤ -Real.log (14710118991 / 15625000000) ∧
    -Real.log (14710118991 / 15625000000) ≤ (15084143 / 250000000) := by
  have h := checkLog_sound (w := (914881009 / 30335118991)) (n := 12)
    (lo := (60336571 / 1000000000)) (hi := (15084143 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 14710118991) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 14710118991) = 1/(14710118991 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12074 : Bounds (-15084143 / 250000000) (-60336571 / 1000000000) (Real.log (14710118991 / 15625000000)) := by
  have h := reflection_log_12074_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12075_neg : (493743891 / 1000000000) ≤ -Real.log (500000000000 / 819219444239) ∧
    -Real.log (500000000000 / 819219444239) ≤ (123435973 / 250000000) := by
  have h := checkLog_sound (w := (319219444239 / 1319219444239)) (n := 12)
    (lo := (493743891 / 1000000000)) (hi := (123435973 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((819219444239 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(819219444239 / 500000000000) = 1/(500000000000 / 819219444239) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12075 : Bounds (493743891 / 1000000000) (123435973 / 250000000) (Real.log (819219444239 / 500000000000)) := by
  have h := reflection_log_12075_neg
  have he : Real.log (819219444239 / 500000000000) = -Real.log (500000000000 / 819219444239) := by
    rw [show ((819219444239 / 500000000000) : ℝ) = ((500000000000 / 819219444239) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12076_neg : (123973583 / 250000000) ≤ -Real.log (500000000000 / 820983022727) ∧
    -Real.log (500000000000 / 820983022727) ≤ (495894333 / 1000000000) := by
  have h := checkLog_sound (w := (320983022727 / 1320983022727)) (n := 12)
    (lo := (123973583 / 250000000)) (hi := (495894333 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((820983022727 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(820983022727 / 500000000000) = 1/(500000000000 / 820983022727) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12076 : Bounds (123973583 / 250000000) (495894333 / 1000000000) (Real.log (820983022727 / 500000000000)) := by
  have h := reflection_log_12076_neg
  have he : Real.log (820983022727 / 500000000000) = -Real.log (500000000000 / 820983022727) := by
    rw [show ((820983022727 / 500000000000) : ℝ) = ((500000000000 / 820983022727) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12077_neg : (1007343773 / 1000000000) ≤ -Real.log (62500000000 / 171144859813) ∧
    -Real.log (62500000000 / 171144859813) ≤ (40293751 / 40000000) := by
  have h := checkLog_sound (w := (46144859813 / 296144859813)) (n := 12)
    (lo := (314196593 / 1000000000)) (hi := (157098297 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((171144859813 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(171144859813 / 125000000000) = 1/(62500000000 / 171144859813) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12077 : Bounds (1007343773 / 1000000000) (40293751 / 40000000) (Real.log (171144859813 / 62500000000)) := by
  have h := reflection_log_12077_neg
  have he : Real.log (171144859813 / 62500000000) = -Real.log (62500000000 / 171144859813) := by
    rw [show ((171144859813 / 62500000000) : ℝ) = ((62500000000 / 171144859813) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12078_neg : (504948521 / 500000000) ≤ -Real.log (50000000000 / 137265917603) ∧
    -Real.log (50000000000 / 137265917603) ≤ (252474261 / 250000000) := by
  have h := checkLog_sound (w := (37265917603 / 237265917603)) (n := 12)
    (lo := (158374931 / 500000000)) (hi := (316749863 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((137265917603 / 100000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(137265917603 / 100000000000) = 1/(50000000000 / 137265917603) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12078 : Bounds (504948521 / 500000000) (252474261 / 250000000) (Real.log (137265917603 / 50000000000)) := by
  have h := reflection_log_12078_neg
  have he : Real.log (137265917603 / 50000000000) = -Real.log (50000000000 / 137265917603) := by
    rw [show ((137265917603 / 50000000000) : ℝ) = ((50000000000 / 137265917603) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12079_neg : (383219499 / 1000000000) ≤ -Real.log (1000 / 1467) ∧
    -Real.log (1000 / 1467) ≤ (766439 / 2000000) := by
  have h := checkLog_sound (w := (467 / 2467)) (n := 12)
    (lo := (383219499 / 1000000000)) (hi := (766439 / 2000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1467 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1467 / 1000) = 1/(1000 / 1467) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12079 : Bounds (383219499 / 1000000000) (766439 / 2000000) (Real.log (1467 / 1000)) := by
  have h := reflection_log_12079_neg
  have he : Real.log (1467 / 1000) = -Real.log (1000 / 1467) := by
    rw [show ((1467 / 1000) : ℝ) = ((1000 / 1467) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12080_neg : (314616927 / 500000000) ≤ -Real.log (533 / 1000) ∧
    -Real.log (533 / 1000) ≤ (125846771 / 200000000) := by
  have h := checkLog_sound (w := (467 / 1533)) (n := 12)
    (lo := (314616927 / 500000000)) (hi := (125846771 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 533) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 533) = 1/(533 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12080 : Bounds (-125846771 / 200000000) (-314616927 / 500000000) (Real.log (533 / 1000)) := by
  have h := reflection_log_12080_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12081_neg : (46689 / 100000000) ≤ -Real.log (1000000 / 1000467) ∧
    -Real.log (1000000 / 1000467) ≤ (466891 / 1000000000) := by
  have h := checkLog_sound (w := (467 / 2000467)) (n := 12)
    (lo := (46689 / 100000000)) (hi := (466891 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000467 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000467 / 1000000) = 1/(1000000 / 1000467) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12081 : Bounds (46689 / 100000000) (466891 / 1000000000) (Real.log (1000467 / 1000000)) := by
  have h := reflection_log_12081_neg
  have he : Real.log (1000467 / 1000000) = -Real.log (1000000 / 1000467) := by
    rw [show ((1000467 / 1000000) : ℝ) = ((1000000 / 1000467) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12082_neg : (467109 / 1000000000) ≤ -Real.log (999533 / 1000000) ∧
    -Real.log (999533 / 1000000) ≤ (46711 / 100000000) := by
  have h := checkLog_sound (w := (467 / 1999533)) (n := 12)
    (lo := (467109 / 1000000000)) (hi := (46711 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999533) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999533) = 1/(999533 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12082 : Bounds (-46711 / 100000000) (-467109 / 1000000000) (Real.log (999533 / 1000000)) := by
  have h := reflection_log_12082_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12083_neg : (217159281 / 1000000000) ≤ -Real.log (500000 / 621271) ∧
    -Real.log (500000 / 621271) ≤ (108579641 / 500000000) := by
  have h := checkLog_sound (w := (121271 / 1121271)) (n := 12)
    (lo := (217159281 / 1000000000)) (hi := (108579641 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((621271 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(621271 / 500000) = 1/(500000 / 621271) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12083 : Bounds (217159281 / 1000000000) (108579641 / 500000000) (Real.log (621271 / 500000)) := by
  have h := reflection_log_12083_neg
  have he : Real.log (621271 / 500000) = -Real.log (500000 / 621271) := by
    rw [show ((621271 / 500000) : ℝ) = ((500000 / 621271) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12084_neg : (69446797 / 250000000) ≤ -Real.log (378729 / 500000) ∧
    -Real.log (378729 / 500000) ≤ (277787189 / 1000000000) := by
  have h := checkLog_sound (w := (121271 / 878729)) (n := 12)
    (lo := (69446797 / 250000000)) (hi := (277787189 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 378729) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 378729) = 1/(378729 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12084 : Bounds (-277787189 / 1000000000) (-69446797 / 250000000) (Real.log (378729 / 500000)) := by
  have h := reflection_log_12084_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12085_neg : (217973409 / 1000000000) ≤ -Real.log (500000 / 621777) ∧
    -Real.log (500000 / 621777) ≤ (21797341 / 100000000) := by
  have h := checkLog_sound (w := (121777 / 1121777)) (n := 12)
    (lo := (217973409 / 1000000000)) (hi := (21797341 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((621777 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(621777 / 500000) = 1/(500000 / 621777) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12085 : Bounds (217973409 / 1000000000) (21797341 / 100000000) (Real.log (621777 / 500000)) := by
  have h := reflection_log_12085_neg
  have he : Real.log (621777 / 500000) = -Real.log (500000 / 621777) := by
    rw [show ((621777 / 500000) : ℝ) = ((500000 / 621777) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12086_neg : (279124129 / 1000000000) ≤ -Real.log (378223 / 500000) ∧
    -Real.log (378223 / 500000) ≤ (27912413 / 100000000) := by
  have h := checkLog_sound (w := (121777 / 878223)) (n := 12)
    (lo := (279124129 / 1000000000)) (hi := (27912413 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 378223) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 378223) = 1/(378223 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12086 : Bounds (-27912413 / 100000000) (-279124129 / 1000000000) (Real.log (378223 / 500000)) := by
  have h := reflection_log_12086_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12087_neg : (23887 / 390625) ≤ -Real.log (235170362271 / 250000000000) ∧
    -Real.log (235170362271 / 250000000000) ≤ (61150721 / 1000000000) := by
  have h := checkLog_sound (w := (14829637729 / 485170362271)) (n := 12)
    (lo := (23887 / 390625)) (hi := (61150721 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 235170362271) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 235170362271) = 1/(235170362271 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12087 : Bounds (-61150721 / 1000000000) (-23887 / 390625) (Real.log (235170362271 / 250000000000)) := by
  have h := reflection_log_12087_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12088_neg : (60627907 / 1000000000) ≤ -Real.log (235293344559 / 250000000000) ∧
    -Real.log (235293344559 / 250000000000) ≤ (15156977 / 250000000) := by
  have h := checkLog_sound (w := (14706655441 / 485293344559)) (n := 12)
    (lo := (60627907 / 1000000000)) (hi := (15156977 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 235293344559) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 235293344559) = 1/(235293344559 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12088 : Bounds (-15156977 / 250000000) (-60627907 / 1000000000) (Real.log (235293344559 / 250000000000)) := by
  have h := reflection_log_12088_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12089_neg : (494946469 / 1000000000) ≤ -Real.log (250000000000 / 410102606349) ∧
    -Real.log (250000000000 / 410102606349) ≤ (49494647 / 100000000) := by
  have h := checkLog_sound (w := (160102606349 / 660102606349)) (n := 12)
    (lo := (494946469 / 1000000000)) (hi := (49494647 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((410102606349 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(410102606349 / 250000000000) = 1/(250000000000 / 410102606349) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12089 : Bounds (494946469 / 1000000000) (49494647 / 100000000) (Real.log (410102606349 / 250000000000)) := by
  have h := reflection_log_12089_neg
  have he : Real.log (410102606349 / 250000000000) = -Real.log (250000000000 / 410102606349) := by
    rw [show ((410102606349 / 250000000000) : ℝ) = ((250000000000 / 410102606349) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12090_neg : (248548769 / 500000000) ≤ -Real.log (250000000000 / 410985714777) ∧
    -Real.log (250000000000 / 410985714777) ≤ (497097539 / 1000000000) := by
  have h := checkLog_sound (w := (160985714777 / 660985714777)) (n := 12)
    (lo := (248548769 / 500000000)) (hi := (497097539 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((410985714777 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(410985714777 / 250000000000) = 1/(250000000000 / 410985714777) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12090 : Bounds (248548769 / 500000000) (497097539 / 1000000000) (Real.log (410985714777 / 250000000000)) := by
  have h := reflection_log_12090_neg
  have he : Real.log (410985714777 / 250000000000) = -Real.log (250000000000 / 410985714777) := by
    rw [show ((410985714777 / 250000000000) : ℝ) = ((250000000000 / 410985714777) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12091_neg : (504948521 / 500000000) ≤ -Real.log (500000000000 / 1372659176029) ∧
    -Real.log (500000000000 / 1372659176029) ≤ (252474261 / 250000000) := by
  have h := checkLog_sound (w := (372659176029 / 2372659176029)) (n := 12)
    (lo := (158374931 / 500000000)) (hi := (316749863 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1372659176029 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1372659176029 / 1000000000000) = 1/(500000000000 / 1372659176029) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12091 : Bounds (504948521 / 500000000) (252474261 / 250000000) (Real.log (1372659176029 / 500000000000)) := by
  have h := reflection_log_12091_neg
  have he : Real.log (1372659176029 / 500000000000) = -Real.log (500000000000 / 1372659176029) := by
    rw [show ((1372659176029 / 500000000000) : ℝ) = ((500000000000 / 1372659176029) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12092_neg : (1012453353 / 1000000000) ≤ -Real.log (12500000000 / 34404315197) ∧
    -Real.log (12500000000 / 34404315197) ≤ (202490671 / 200000000) := by
  have h := checkLog_sound (w := (9404315197 / 59404315197)) (n := 12)
    (lo := (319306173 / 1000000000)) (hi := (159653087 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((34404315197 / 25000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(34404315197 / 25000000000) = 1/(12500000000 / 34404315197) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12092 : Bounds (1012453353 / 1000000000) (202490671 / 200000000) (Real.log (34404315197 / 12500000000)) := by
  have h := reflection_log_12092_neg
  have he : Real.log (34404315197 / 12500000000) = -Real.log (12500000000 / 34404315197) := by
    rw [show ((34404315197 / 12500000000) : ℝ) = ((12500000000 / 34404315197) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12093_neg : (38390093 / 100000000) ≤ -Real.log (250 / 367) ∧
    -Real.log (250 / 367) ≤ (383900931 / 1000000000) := by
  have h := checkLog_sound (w := (117 / 617)) (n := 12)
    (lo := (38390093 / 100000000)) (hi := (383900931 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((367 / 250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(367 / 250) = 1/(250 / 367) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12093 : Bounds (38390093 / 100000000) (383900931 / 1000000000) (Real.log (367 / 250)) := by
  have h := reflection_log_12093_neg
  have he : Real.log (367 / 250) = -Real.log (250 / 367) := by
    rw [show ((367 / 250) : ℝ) = ((250 / 367) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12094_neg : (631111789 / 1000000000) ≤ -Real.log (133 / 250) ∧
    -Real.log (133 / 250) ≤ (63111179 / 100000000) := by
  have h := checkLog_sound (w := (117 / 383)) (n := 12)
    (lo := (631111789 / 1000000000)) (hi := (63111179 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250 / 133) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250 / 133) = 1/(133 / 250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12094 : Bounds (-63111179 / 100000000) (-631111789 / 1000000000) (Real.log (133 / 250)) := by
  have h := reflection_log_12094_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12095_neg : (46789 / 100000000) ≤ -Real.log (250000 / 250117) ∧
    -Real.log (250000 / 250117) ≤ (467891 / 1000000000) := by
  have h := checkLog_sound (w := (117 / 500117)) (n := 12)
    (lo := (46789 / 100000000)) (hi := (467891 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250117 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250117 / 250000) = 1/(250000 / 250117) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12095 : Bounds (46789 / 100000000) (467891 / 1000000000) (Real.log (250117 / 250000)) := by
  have h := reflection_log_12095_neg
  have he : Real.log (250117 / 250000) = -Real.log (250000 / 250117) := by
    rw [show ((250117 / 250000) : ℝ) = ((250000 / 250117) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily
