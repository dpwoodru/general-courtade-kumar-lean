import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell016
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

theorem reflection_log_1_neg : (115540359 / 500000000) ≤ -Real.log (5120 / 6451) ∧
    -Real.log (5120 / 6451) ≤ (231080719 / 1000000000) := by
  have h := checkLog_sound (w := (1331 / 11571)) (n := 12)
    (lo := (115540359 / 500000000)) (hi := (231080719 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6451 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6451 / 5120) = 1/(5120 / 6451) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (115540359 / 500000000) (231080719 / 1000000000) (Real.log (6451 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6451 / 5120) = -Real.log (5120 / 6451) := by
    rw [show ((6451 / 5120) : ℝ) = ((5120 / 6451) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (301052307 / 1000000000) ≤ -Real.log (3789 / 5120) ∧
    -Real.log (3789 / 5120) ≤ (75263077 / 250000000) := by
  have h := checkLog_sound (w := (1331 / 8909)) (n := 12)
    (lo := (301052307 / 1000000000)) (hi := (75263077 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3789) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3789) = 1/(3789 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-75263077 / 250000000) (-301052307 / 1000000000) (Real.log (3789 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (115307783 / 500000000) ≤ -Real.log (320 / 403) ∧
    -Real.log (320 / 403) ≤ (230615567 / 1000000000) := by
  have h := checkLog_sound (w := (83 / 723)) (n := 12)
    (lo := (115307783 / 500000000)) (hi := (230615567 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((403 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(403 / 320) = 1/(320 / 403) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (115307783 / 500000000) (230615567 / 1000000000) (Real.log (403 / 320)) := by
  have h := reflection_log_3_neg
  have he : Real.log (403 / 320) = -Real.log (320 / 403) := by
    rw [show ((403 / 320) : ℝ) = ((320 / 403) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (150130427 / 500000000) ≤ -Real.log (237 / 320) ∧
    -Real.log (237 / 320) ≤ (60052171 / 200000000) := by
  have h := checkLog_sound (w := (83 / 557)) (n := 12)
    (lo := (150130427 / 500000000)) (hi := (60052171 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 237) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(320 / 237) = 1/(237 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-60052171 / 200000000) (-150130427 / 500000000) (Real.log (237 / 320)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (168842791 / 1000000000) ≤ -Real.log (500000 / 591967) ∧
    -Real.log (500000 / 591967) ≤ (21105349 / 125000000) := by
  have h := checkLog_sound (w := (91967 / 1091967)) (n := 12)
    (lo := (168842791 / 1000000000)) (hi := (21105349 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((591967 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(591967 / 500000) = 1/(500000 / 591967) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (168842791 / 1000000000) (21105349 / 125000000) (Real.log (591967 / 500000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (591967 / 500000) = -Real.log (500000 / 591967) := by
    rw [show ((591967 / 500000) : ℝ) = ((500000 / 591967) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (50815011 / 250000000) ≤ -Real.log (408033 / 500000) ∧
    -Real.log (408033 / 500000) ≤ (40652009 / 200000000) := by
  have h := checkLog_sound (w := (91967 / 908033)) (n := 12)
    (lo := (50815011 / 250000000)) (hi := (40652009 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 408033) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 408033) = 1/(408033 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-40652009 / 200000000) (-50815011 / 250000000) (Real.log (408033 / 500000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (169196633 / 1000000000) ≤ -Real.log (1000000 / 1184353) ∧
    -Real.log (1000000 / 1184353) ≤ (84598317 / 500000000) := by
  have h := checkLog_sound (w := (184353 / 2184353)) (n := 12)
    (lo := (169196633 / 1000000000)) (hi := (84598317 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1184353 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1184353 / 1000000) = 1/(1000000 / 1184353) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (169196633 / 1000000000) (84598317 / 500000000) (Real.log (1184353 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1184353 / 1000000) = -Real.log (1000000 / 1184353) := by
    rw [show ((1184353 / 1000000) : ℝ) = ((1000000 / 1184353) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (40754723 / 200000000) ≤ -Real.log (815647 / 1000000) ∧
    -Real.log (815647 / 1000000) ≤ (12735851 / 62500000) := by
  have h := checkLog_sound (w := (184353 / 1815647)) (n := 12)
    (lo := (40754723 / 200000000)) (hi := (12735851 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 815647) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 815647) = 1/(815647 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-12735851 / 62500000) (-40754723 / 200000000) (Real.log (815647 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (61680171 / 500000000) ≤ -Real.log (250000 / 282823) ∧
    -Real.log (250000 / 282823) ≤ (123360343 / 1000000000) := by
  have h := checkLog_sound (w := (32823 / 532823)) (n := 12)
    (lo := (61680171 / 500000000)) (hi := (123360343 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((282823 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(282823 / 250000) = 1/(250000 / 282823) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (61680171 / 500000000) (123360343 / 1000000000) (Real.log (282823 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (282823 / 250000) = -Real.log (250000 / 282823) := by
    rw [show ((282823 / 250000) : ℝ) = ((250000 / 282823) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (35187057 / 250000000) ≤ -Real.log (217177 / 250000) ∧
    -Real.log (217177 / 250000) ≤ (140748229 / 1000000000) := by
  have h := checkLog_sound (w := (32823 / 467177)) (n := 12)
    (lo := (35187057 / 250000000)) (hi := (140748229 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 217177) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 217177) = 1/(217177 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-140748229 / 1000000000) (-35187057 / 250000000) (Real.log (217177 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (123629909 / 1000000000) ≤ -Real.log (1000000 / 1131597) ∧
    -Real.log (1000000 / 1131597) ≤ (12362991 / 100000000) := by
  have h := checkLog_sound (w := (131597 / 2131597)) (n := 12)
    (lo := (123629909 / 1000000000)) (hi := (12362991 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1131597 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1131597 / 1000000) = 1/(1000000 / 1131597) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (123629909 / 1000000000) (12362991 / 100000000) (Real.log (1131597 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1131597 / 1000000) = -Real.log (1000000 / 1131597) := by
    rw [show ((1131597 / 1000000) : ℝ) = ((1000000 / 1131597) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (70549693 / 500000000) ≤ -Real.log (868403 / 1000000) ∧
    -Real.log (868403 / 1000000) ≤ (141099387 / 1000000000) := by
  have h := checkLog_sound (w := (131597 / 1868403)) (n := 12)
    (lo := (70549693 / 500000000)) (hi := (141099387 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 868403) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 868403) = 1/(868403 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-141099387 / 1000000000) (-70549693 / 500000000) (Real.log (868403 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (26543821 / 50000000) ≤ -Real.log (15625000000 / 26569092827) ∧
    -Real.log (15625000000 / 26569092827) ≤ (530876421 / 1000000000) := by
  have h := checkLog_sound (w := (10944092827 / 42194092827)) (n := 12)
    (lo := (26543821 / 50000000)) (hi := (530876421 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((26569092827 / 15625000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(26569092827 / 15625000000) = 1/(15625000000 / 26569092827) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (26543821 / 50000000) (530876421 / 1000000000) (Real.log (26569092827 / 15625000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (26569092827 / 15625000000) = -Real.log (15625000000 / 26569092827) := by
    rw [show ((26569092827 / 15625000000) : ℝ) = ((15625000000 / 26569092827) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (21285321 / 40000000) ≤ -Real.log (250000000000 / 425640010557) ∧
    -Real.log (250000000000 / 425640010557) ≤ (266066513 / 500000000) := by
  have h := checkLog_sound (w := (175640010557 / 675640010557)) (n := 12)
    (lo := (21285321 / 40000000)) (hi := (266066513 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((425640010557 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(425640010557 / 250000000000) = 1/(250000000000 / 425640010557) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (21285321 / 40000000) (266066513 / 500000000) (Real.log (425640010557 / 250000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (425640010557 / 250000000000) = -Real.log (250000000000 / 425640010557) := by
    rw [show ((425640010557 / 250000000000) : ℝ) = ((250000000000 / 425640010557) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (93025709 / 250000000) ≤ -Real.log (125000000000 / 181347770891) ∧
    -Real.log (125000000000 / 181347770891) ≤ (372102837 / 1000000000) := by
  have h := checkLog_sound (w := (56347770891 / 306347770891)) (n := 12)
    (lo := (93025709 / 250000000)) (hi := (372102837 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((181347770891 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(181347770891 / 125000000000) = 1/(125000000000 / 181347770891) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (93025709 / 250000000) (372102837 / 1000000000) (Real.log (181347770891 / 125000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (181347770891 / 125000000000) = -Real.log (125000000000 / 181347770891) := by
    rw [show ((181347770891 / 125000000000) : ℝ) = ((125000000000 / 181347770891) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (372970249 / 1000000000) ≤ -Real.log (250000000000 / 363010285087) ∧
    -Real.log (250000000000 / 363010285087) ≤ (1491881 / 4000000) := by
  have h := checkLog_sound (w := (113010285087 / 613010285087)) (n := 12)
    (lo := (372970249 / 1000000000)) (hi := (1491881 / 4000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((363010285087 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(363010285087 / 250000000000) = 1/(250000000000 / 363010285087) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (372970249 / 1000000000) (1491881 / 4000000) (Real.log (363010285087 / 250000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (363010285087 / 250000000000) = -Real.log (250000000000 / 363010285087) := by
    rw [show ((363010285087 / 250000000000) : ℝ) = ((250000000000 / 363010285087) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (264108571 / 1000000000) ≤ -Real.log (250000000000 / 325567394337) ∧
    -Real.log (250000000000 / 325567394337) ≤ (66027143 / 250000000) := by
  have h := checkLog_sound (w := (75567394337 / 575567394337)) (n := 12)
    (lo := (264108571 / 1000000000)) (hi := (66027143 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((325567394337 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(325567394337 / 250000000000) = 1/(250000000000 / 325567394337) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (264108571 / 1000000000) (66027143 / 250000000) (Real.log (325567394337 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (325567394337 / 250000000000) = -Real.log (250000000000 / 325567394337) := by
    rw [show ((325567394337 / 250000000000) : ℝ) = ((250000000000 / 325567394337) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (52945859 / 200000000) ≤ -Real.log (500000000000 / 651539089571) ∧
    -Real.log (500000000000 / 651539089571) ≤ (16545581 / 62500000) := by
  have h := checkLog_sound (w := (151539089571 / 1151539089571)) (n := 12)
    (lo := (52945859 / 200000000)) (hi := (16545581 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((651539089571 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(651539089571 / 500000000000) = 1/(500000000000 / 651539089571) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (52945859 / 200000000) (16545581 / 62500000) (Real.log (651539089571 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (651539089571 / 500000000000) = -Real.log (500000000000 / 651539089571) := by
    rw [show ((651539089571 / 500000000000) : ℝ) = ((500000000000 / 651539089571) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (17469477 / 1000000000) ≤ -Real.log (982682229591 / 1000000000000) ∧
    -Real.log (982682229591 / 1000000000000) ≤ (8734739 / 500000000) := by
  have h := checkLog_sound (w := (17317770409 / 1982682229591)) (n := 12)
    (lo := (17469477 / 1000000000)) (hi := (8734739 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 982682229591) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 982682229591) = 1/(982682229591 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-8734739 / 500000000) (-17469477 / 1000000000) (Real.log (982682229591 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (8693943 / 500000000) ≤ -Real.log (61422650671 / 62500000000) ∧
    -Real.log (61422650671 / 62500000000) ≤ (17387887 / 1000000000) := by
  have h := checkLog_sound (w := (1077349329 / 123922650671)) (n := 12)
    (lo := (8693943 / 500000000)) (hi := (17387887 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 61422650671) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 61422650671) = 1/(61422650671 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-17387887 / 1000000000) (-8693943 / 500000000) (Real.log (61422650671 / 62500000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell016
