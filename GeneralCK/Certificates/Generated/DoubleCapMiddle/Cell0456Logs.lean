import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0456
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

theorem reflection_log_1_neg : (9335323 / 50000000) ≤ -Real.log (5120 / 6171) ∧
    -Real.log (5120 / 6171) ≤ (186706461 / 1000000000) := by
  have h := checkLog_sound (w := (1051 / 11291)) (n := 12)
    (lo := (9335323 / 50000000)) (hi := (186706461 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6171 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6171 / 5120) = 1/(5120 / 6171) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (9335323 / 50000000) (186706461 / 1000000000) (Real.log (6171 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6171 / 5120) = -Real.log (5120 / 6171) := by
    rw [show ((6171 / 5120) : ℝ) = ((5120 / 6171) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (22975717 / 100000000) ≤ -Real.log (4069 / 5120) ∧
    -Real.log (4069 / 5120) ≤ (229757171 / 1000000000) := by
  have h := checkLog_sound (w := (1051 / 9189)) (n := 12)
    (lo := (22975717 / 100000000)) (hi := (229757171 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 4069) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 4069) = 1/(4069 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-229757171 / 1000000000) (-22975717 / 100000000) (Real.log (4069 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (93231679 / 500000000) ≤ -Real.log (10240 / 12339) ∧
    -Real.log (10240 / 12339) ≤ (186463359 / 1000000000) := by
  have h := checkLog_sound (w := (2099 / 22579)) (n := 12)
    (lo := (93231679 / 500000000)) (hi := (186463359 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12339 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12339 / 10240) = 1/(10240 / 12339) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (93231679 / 500000000) (186463359 / 1000000000) (Real.log (12339 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12339 / 10240) = -Real.log (10240 / 12339) := by
    rw [show ((12339 / 10240) : ℝ) = ((10240 / 12339) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (229388597 / 1000000000) ≤ -Real.log (8141 / 10240) ∧
    -Real.log (8141 / 10240) ≤ (114694299 / 500000000) := by
  have h := checkLog_sound (w := (2099 / 18381)) (n := 12)
    (lo := (229388597 / 1000000000)) (hi := (114694299 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 8141) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 8141) = 1/(8141 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-114694299 / 500000000) (-229388597 / 1000000000) (Real.log (8141 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (343977483 / 1000000000) ≤ -Real.log (2560 / 3611) ∧
    -Real.log (2560 / 3611) ≤ (85994371 / 250000000) := by
  have h := checkLog_sound (w := (1051 / 6171)) (n := 12)
    (lo := (343977483 / 1000000000)) (hi := (85994371 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3611 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3611 / 2560) = 1/(2560 / 3611) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (343977483 / 1000000000) (85994371 / 250000000) (Real.log (3611 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (3611 / 2560) = -Real.log (2560 / 3611) := by
    rw [show ((3611 / 2560) : ℝ) = ((2560 / 3611) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (264280039 / 500000000) ≤ -Real.log (1509 / 2560) ∧
    -Real.log (1509 / 2560) ≤ (528560079 / 1000000000) := by
  have h := checkLog_sound (w := (1051 / 4069)) (n := 12)
    (lo := (264280039 / 500000000)) (hi := (528560079 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1509) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1509) = 1/(1509 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-528560079 / 1000000000) (-264280039 / 500000000) (Real.log (1509 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (171781 / 500000) ≤ -Real.log (5120 / 7219) ∧
    -Real.log (5120 / 7219) ≤ (343562001 / 1000000000) := by
  have h := checkLog_sound (w := (2099 / 12339)) (n := 12)
    (lo := (171781 / 500000)) (hi := (343562001 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7219 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7219 / 5120) = 1/(5120 / 7219) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (171781 / 500000) (343562001 / 1000000000) (Real.log (7219 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (7219 / 5120) = -Real.log (5120 / 7219) := by
    rw [show ((7219 / 5120) : ℝ) = ((5120 / 7219) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (65945817 / 125000000) ≤ -Real.log (3021 / 5120) ∧
    -Real.log (3021 / 5120) ≤ (527566537 / 1000000000) := by
  have h := checkLog_sound (w := (2099 / 8141)) (n := 12)
    (lo := (65945817 / 125000000)) (hi := (527566537 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3021) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3021) = 1/(3021 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-527566537 / 1000000000) (-65945817 / 125000000) (Real.log (3021 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (256246357 / 1000000000) ≤ -Real.log (1000000 / 1292071) ∧
    -Real.log (1000000 / 1292071) ≤ (128123179 / 500000000) := by
  have h := checkLog_sound (w := (292071 / 2292071)) (n := 12)
    (lo := (256246357 / 1000000000)) (hi := (128123179 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1292071 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1292071 / 1000000) = 1/(1000000 / 1292071) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (256246357 / 1000000000) (128123179 / 500000000) (Real.log (1292071 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1292071 / 1000000) = -Real.log (1000000 / 1292071) := by
    rw [show ((1292071 / 1000000) : ℝ) = ((1000000 / 1292071) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (21588217 / 62500000) ≤ -Real.log (707929 / 1000000) ∧
    -Real.log (707929 / 1000000) ≤ (345411473 / 1000000000) := by
  have h := checkLog_sound (w := (292071 / 1707929)) (n := 12)
    (lo := (21588217 / 62500000)) (hi := (345411473 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 707929) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 707929) = 1/(707929 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-345411473 / 1000000000) (-21588217 / 62500000) (Real.log (707929 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (1002247 / 3906250) ≤ -Real.log (62500 / 80781) ∧
    -Real.log (62500 / 80781) ≤ (256575233 / 1000000000) := by
  have h := checkLog_sound (w := (18281 / 143281)) (n := 12)
    (lo := (1002247 / 3906250)) (hi := (256575233 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80781 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(80781 / 62500) = 1/(62500 / 80781) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (1002247 / 3906250) (256575233 / 1000000000) (Real.log (80781 / 62500)) := by
  have h := reflection_log_11_neg
  have he : Real.log (80781 / 62500) = -Real.log (62500 / 80781) := by
    rw [show ((80781 / 62500) : ℝ) = ((62500 / 80781) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (69202399 / 200000000) ≤ -Real.log (44219 / 62500) ∧
    -Real.log (44219 / 62500) ≤ (86502999 / 250000000) := by
  have h := checkLog_sound (w := (18281 / 106719)) (n := 12)
    (lo := (69202399 / 200000000)) (hi := (86502999 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 44219) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 44219) = 1/(44219 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-86502999 / 250000000) (-69202399 / 200000000) (Real.log (44219 / 62500)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (9593871 / 50000000) ≤ -Real.log (500000 / 605761) ∧
    -Real.log (500000 / 605761) ≤ (191877421 / 1000000000) := by
  have h := checkLog_sound (w := (105761 / 1105761)) (n := 12)
    (lo := (9593871 / 50000000)) (hi := (191877421 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((605761 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(605761 / 500000) = 1/(500000 / 605761) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (9593871 / 50000000) (191877421 / 1000000000) (Real.log (605761 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (605761 / 500000) = -Real.log (500000 / 605761) := by
    rw [show ((605761 / 500000) : ℝ) = ((500000 / 605761) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (118825387 / 500000000) ≤ -Real.log (394239 / 500000) ∧
    -Real.log (394239 / 500000) ≤ (9506031 / 40000000) := by
  have h := checkLog_sound (w := (105761 / 894239)) (n := 12)
    (lo := (118825387 / 500000000)) (hi := (9506031 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 394239) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 394239) = 1/(394239 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-9506031 / 40000000) (-118825387 / 500000000) (Real.log (394239 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (192143991 / 1000000000) ≤ -Real.log (200000 / 242369) ∧
    -Real.log (200000 / 242369) ≤ (24017999 / 125000000) := by
  have h := checkLog_sound (w := (42369 / 442369)) (n := 12)
    (lo := (192143991 / 1000000000)) (hi := (24017999 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((242369 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(242369 / 200000) = 1/(200000 / 242369) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (192143991 / 1000000000) (24017999 / 125000000) (Real.log (242369 / 200000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (242369 / 200000) = -Real.log (200000 / 242369) := by
    rw [show ((242369 / 200000) : ℝ) = ((200000 / 242369) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (238060507 / 1000000000) ≤ -Real.log (157631 / 200000) ∧
    -Real.log (157631 / 200000) ≤ (59515127 / 250000000) := by
  have h := checkLog_sound (w := (42369 / 357631)) (n := 12)
    (lo := (238060507 / 1000000000)) (hi := (59515127 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 157631) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 157631) = 1/(157631 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-59515127 / 250000000) (-238060507 / 1000000000) (Real.log (157631 / 200000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (60165783 / 100000000) ≤ -Real.log (100000000000 / 182514206933) ∧
    -Real.log (100000000000 / 182514206933) ≤ (601657831 / 1000000000) := by
  have h := checkLog_sound (w := (82514206933 / 282514206933)) (n := 12)
    (lo := (60165783 / 100000000)) (hi := (601657831 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((182514206933 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(182514206933 / 100000000000) = 1/(100000000000 / 182514206933) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (60165783 / 100000000) (601657831 / 1000000000) (Real.log (182514206933 / 100000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (182514206933 / 100000000000) = -Real.log (100000000000 / 182514206933) := by
    rw [show ((182514206933 / 100000000000) : ℝ) = ((100000000000 / 182514206933) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (150646807 / 250000000) ≤ -Real.log (500000000000 / 913419570773) ∧
    -Real.log (500000000000 / 913419570773) ≤ (602587229 / 1000000000) := by
  have h := checkLog_sound (w := (413419570773 / 1413419570773)) (n := 12)
    (lo := (150646807 / 250000000)) (hi := (602587229 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((913419570773 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(913419570773 / 500000000000) = 1/(500000000000 / 913419570773) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (150646807 / 250000000) (602587229 / 1000000000) (Real.log (913419570773 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (913419570773 / 500000000000) = -Real.log (500000000000 / 913419570773) := by
    rw [show ((913419570773 / 500000000000) : ℝ) = ((500000000000 / 913419570773) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (214764097 / 500000000) ≤ -Real.log (500000000000 / 768266204003) ∧
    -Real.log (500000000000 / 768266204003) ≤ (85905639 / 200000000) := by
  have h := checkLog_sound (w := (268266204003 / 1268266204003)) (n := 12)
    (lo := (214764097 / 500000000)) (hi := (85905639 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((768266204003 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(768266204003 / 500000000000) = 1/(500000000000 / 768266204003) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (214764097 / 500000000) (85905639 / 200000000) (Real.log (768266204003 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (768266204003 / 500000000000) = -Real.log (500000000000 / 768266204003) := by
    rw [show ((768266204003 / 500000000000) : ℝ) = ((500000000000 / 768266204003) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (430204499 / 1000000000) ≤ -Real.log (500000000000 / 768785962153) ∧
    -Real.log (500000000000 / 768785962153) ≤ (860409 / 2000000) := by
  have h := checkLog_sound (w := (268785962153 / 1268785962153)) (n := 12)
    (lo := (430204499 / 1000000000)) (hi := (860409 / 2000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((768785962153 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(768785962153 / 500000000000) = 1/(500000000000 / 768785962153) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (430204499 / 1000000000) (860409 / 2000000) (Real.log (768785962153 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (768785962153 / 500000000000) = -Real.log (500000000000 / 768785962153) := by
    rw [show ((768785962153 / 500000000000) : ℝ) = ((500000000000 / 768785962153) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0456
