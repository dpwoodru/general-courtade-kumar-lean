import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0002
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

theorem reflection_log_1_neg : (683003129 / 1000000000) ≤ -Real.log (102400 / 202733) ∧
    -Real.log (102400 / 202733) ≤ (68300313 / 100000000) := by
  have h := checkLog_sound (w := (100333 / 305133)) (n := 12)
    (lo := (683003129 / 1000000000)) (hi := (68300313 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((202733 / 102400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(202733 / 102400) = 1/(102400 / 202733) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (683003129 / 1000000000) (68300313 / 100000000) (Real.log (202733 / 102400)) := by
  have h := reflection_log_1_neg
  have he : Real.log (202733 / 102400) = -Real.log (102400 / 202733) := by
    rw [show ((202733 / 102400) : ℝ) = ((102400 / 202733) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (3902788429 / 1000000000) ≤ -Real.log (2067 / 102400) ∧
    -Real.log (2067 / 102400) ≤ (780557687 / 200000000) := by
  have h := checkLog_sound (w := (1133 / 5267)) (n := 12)
    (lo := (437052529 / 1000000000)) (hi := (43705253 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2067) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3200 / 2067) = 1/(2067 / 102400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-780557687 / 200000000) (-3902788429 / 1000000000) (Real.log (2067 / 102400)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (682956269 / 1000000000) ≤ -Real.log (1000000000000 / 1979721679687) ∧
    -Real.log (1000000000000 / 1979721679687) ≤ (68295627 / 100000000) := by
  have h := checkLog_sound (w := (979721679687 / 2979721679687)) (n := 12)
    (lo := (682956269 / 1000000000)) (hi := (68295627 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1979721679687 / 1000000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1979721679687 / 1000000000000) = 1/(1000000000000 / 1979721679687) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (682956269 / 1000000000) (68295627 / 100000000) (Real.log (1979721679687 / 1000000000000)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1979721679687 / 1000000000000) = -Real.log (1000000000000 / 1979721679687) := by
    rw [show ((1979721679687 / 1000000000000) : ℝ) = ((1000000000000 / 1979721679687) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (155928117 / 40000000) ≤ -Real.log (20278320313 / 1000000000000) ∧
    -Real.log (20278320313 / 1000000000000) ≤ (3898202931 / 1000000000) := by
  have h := checkLog_sound (w := (10971679687 / 51528320313)) (n := 12)
    (lo := (17298681 / 40000000)) (hi := (216233513 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250000000 / 20278320313) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250000000 / 20278320313) = 1/(20278320313 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-3898202931 / 1000000000) (-155928117 / 40000000) (Real.log (20278320313 / 1000000000000)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (672755121 / 1000000000) ≤ -Real.log (51200 / 100333) ∧
    -Real.log (51200 / 100333) ≤ (336377561 / 500000000) := by
  have h := checkLog_sound (w := (49133 / 151533)) (n := 12)
    (lo := (672755121 / 1000000000)) (hi := (336377561 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100333 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100333 / 51200) = 1/(51200 / 100333) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (672755121 / 1000000000) (336377561 / 500000000) (Real.log (100333 / 51200)) := by
  have h := reflection_log_5_neg
  have he : Real.log (100333 / 51200) = -Real.log (51200 / 100333) := by
    rw [show ((100333 / 51200) : ℝ) = ((51200 / 100333) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (3209641249 / 1000000000) ≤ -Real.log (2067 / 51200) ∧
    -Real.log (2067 / 51200) ≤ (1604820627 / 500000000) := by
  have h := checkLog_sound (w := (1133 / 5267)) (n := 12)
    (lo := (437052529 / 1000000000)) (hi := (43705253 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2067) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3200 / 2067) = 1/(2067 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1604820627 / 500000000) (-3209641249 / 1000000000) (Real.log (2067 / 51200)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (42041277 / 62500000) ≤ -Real.log (102400 / 200647) ∧
    -Real.log (102400 / 200647) ≤ (672660433 / 1000000000) := by
  have h := checkLog_sound (w := (98247 / 303047)) (n := 12)
    (lo := (42041277 / 62500000)) (hi := (672660433 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200647 / 102400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200647 / 102400) = 1/(102400 / 200647) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (42041277 / 62500000) (672660433 / 1000000000) (Real.log (200647 / 102400)) := by
  have h := reflection_log_7_neg
  have he : Real.log (200647 / 102400) = -Real.log (102400 / 200647) := by
    rw [show ((200647 / 102400) : ℝ) = ((102400 / 200647) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (641011149 / 200000000) ≤ -Real.log (4153 / 102400) ∧
    -Real.log (4153 / 102400) ≤ (12820223 / 4000000) := by
  have h := checkLog_sound (w := (2247 / 10553)) (n := 12)
    (lo := (17298681 / 40000000)) (hi := (216233513 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6400 / 4153) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(6400 / 4153) = 1/(4153 / 102400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-12820223 / 4000000) (-641011149 / 200000000) (Real.log (4153 / 102400)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (684489309 / 1000000000) ≤ -Real.log (1000000 / 1982759) ∧
    -Real.log (1000000 / 1982759) ≤ (68448931 / 100000000) := by
  have h := checkLog_sound (w := (982759 / 2982759)) (n := 12)
    (lo := (684489309 / 1000000000)) (hi := (68448931 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1982759 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1982759 / 1000000) = 1/(1000000 / 1982759) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (684489309 / 1000000000) (68448931 / 100000000) (Real.log (1982759 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1982759 / 1000000) = -Real.log (1000000 / 1982759) := by
    rw [show ((1982759 / 1000000) : ℝ) = ((1000000 / 1982759) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (4060465007 / 1000000000) ≤ -Real.log (17241 / 1000000) ∧
    -Real.log (17241 / 1000000) ≤ (4060465013 / 1000000000) := by
  have h := checkLog_sound (w := (14009 / 48491)) (n := 12)
    (lo := (594729107 / 1000000000)) (hi := (148682277 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 17241) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 17241) = 1/(17241 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-4060465013 / 1000000000) (-4060465007 / 1000000000) (Real.log (17241 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (684528143 / 1000000000) ≤ -Real.log (250000 / 495709) ∧
    -Real.log (250000 / 495709) ≤ (42783009 / 62500000) := by
  have h := checkLog_sound (w := (245709 / 745709)) (n := 12)
    (lo := (684528143 / 1000000000)) (hi := (42783009 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((495709 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(495709 / 250000) = 1/(250000 / 495709) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (684528143 / 1000000000) (42783009 / 62500000) (Real.log (495709 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (495709 / 250000) = -Real.log (250000 / 495709) := by
    rw [show ((495709 / 250000) : ℝ) = ((250000 / 495709) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (4064941109 / 1000000000) ≤ -Real.log (4291 / 250000) ∧
    -Real.log (4291 / 250000) ≤ (812988223 / 200000000) := by
  have h := checkLog_sound (w := (7043 / 24207)) (n := 12)
    (lo := (599205209 / 1000000000)) (hi := (59920521 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 8582) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 8582) = 1/(4291 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-812988223 / 200000000) (-4064941109 / 1000000000) (Real.log (4291 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (342228767 / 500000000) ≤ -Real.log (125000 / 247837) ∧
    -Real.log (125000 / 247837) ≤ (136891507 / 200000000) := by
  have h := checkLog_sound (w := (122837 / 372837)) (n := 12)
    (lo := (342228767 / 500000000)) (hi := (136891507 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((247837 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(247837 / 125000) = 1/(125000 / 247837) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (342228767 / 500000000) (136891507 / 200000000) (Real.log (247837 / 125000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (247837 / 125000) = -Real.log (125000 / 247837) := by
    rw [show ((247837 / 125000) : ℝ) = ((125000 / 247837) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (4056817587 / 1000000000) ≤ -Real.log (2163 / 125000) ∧
    -Real.log (2163 / 125000) ≤ (4056817593 / 1000000000) := by
  have h := checkLog_sound (w := (6973 / 24277)) (n := 12)
    (lo := (591081687 / 1000000000)) (hi := (73885211 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 8652) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 8652) = 1/(2163 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-4056817593 / 1000000000) (-4056817587 / 1000000000) (Real.log (2163 / 125000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (684496369 / 1000000000) ≤ -Real.log (1000000 / 1982773) ∧
    -Real.log (1000000 / 1982773) ≤ (68449637 / 100000000) := by
  have h := checkLog_sound (w := (982773 / 2982773)) (n := 12)
    (lo := (684496369 / 1000000000)) (hi := (68449637 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1982773 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1982773 / 1000000) = 1/(1000000 / 1982773) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (684496369 / 1000000000) (68449637 / 100000000) (Real.log (1982773 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1982773 / 1000000) = -Real.log (1000000 / 1982773) := by
    rw [show ((1982773 / 1000000) : ℝ) = ((1000000 / 1982773) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (812255471 / 200000000) ≤ -Real.log (17227 / 1000000) ∧
    -Real.log (17227 / 1000000) ≤ (4061277361 / 1000000000) := by
  have h := checkLog_sound (w := (14023 / 48477)) (n := 12)
    (lo := (119108291 / 200000000)) (hi := (37221341 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 17227) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 17227) = 1/(17227 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-4061277361 / 1000000000) (-812255471 / 200000000) (Real.log (17227 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1186238579 / 250000000) ≤ -Real.log (62500000000 / 7187659503509) ∧
    -Real.log (62500000000 / 7187659503509) ≤ (4744954323 / 1000000000) := by
  have h := checkLog_sound (w := (3187659503509 / 11187659503509)) (n := 12)
    (lo := (146517809 / 250000000)) (hi := (586071237 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7187659503509 / 4000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(7187659503509 / 4000000000000) = 1/(62500000000 / 7187659503509) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1186238579 / 250000000) (4744954323 / 1000000000) (Real.log (7187659503509 / 62500000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (7187659503509 / 62500000000) = -Real.log (62500000000 / 7187659503509) := by
    rw [show ((7187659503509 / 62500000000) : ℝ) = ((62500000000 / 7187659503509) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (4749469251 / 1000000000) ≤ -Real.log (50000000000 / 5776147751107) ∧
    -Real.log (50000000000 / 5776147751107) ≤ (2374734629 / 500000000) := by
  have h := checkLog_sound (w := (2576147751107 / 8976147751107)) (n := 12)
    (lo := (590586171 / 1000000000)) (hi := (147646543 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5776147751107 / 3200000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(5776147751107 / 3200000000000) = 1/(50000000000 / 5776147751107) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (4749469251 / 1000000000) (2374734629 / 500000000) (Real.log (5776147751107 / 50000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (5776147751107 / 50000000000) = -Real.log (50000000000 / 5776147751107) := by
    rw [show ((5776147751107 / 50000000000) : ℝ) = ((50000000000 / 5776147751107) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (4741275121 / 1000000000) ≤ -Real.log (100000000000 / 11458021266759) ∧
    -Real.log (100000000000 / 11458021266759) ≤ (592659391 / 125000000) := by
  have h := checkLog_sound (w := (5058021266759 / 17858021266759)) (n := 12)
    (lo := (582392041 / 1000000000)) (hi := (291196021 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11458021266759 / 6400000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(11458021266759 / 6400000000000) = 1/(100000000000 / 11458021266759) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (4741275121 / 1000000000) (592659391 / 125000000) (Real.log (11458021266759 / 100000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (11458021266759 / 100000000000) = -Real.log (100000000000 / 11458021266759) := by
    rw [show ((11458021266759 / 100000000000) : ℝ) = ((100000000000 / 11458021266759) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (189830949 / 40000000) ≤ -Real.log (250000000000 / 28774206187961) ∧
    -Real.log (250000000000 / 28774206187961) ≤ (1186443433 / 250000000) := by
  have h := checkLog_sound (w := (12774206187961 / 44774206187961)) (n := 12)
    (lo := (117378129 / 200000000)) (hi := (293445323 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((28774206187961 / 16000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(28774206187961 / 16000000000000) = 1/(250000000000 / 28774206187961) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (189830949 / 40000000) (1186443433 / 250000000) (Real.log (28774206187961 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (28774206187961 / 250000000000) = -Real.log (250000000000 / 28774206187961) := by
    rw [show ((28774206187961 / 250000000000) : ℝ) = ((250000000000 / 28774206187961) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0002
