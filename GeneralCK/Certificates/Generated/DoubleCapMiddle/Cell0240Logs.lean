import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0240
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

theorem reflection_log_1_neg : (247531239 / 1000000000) ≤ -Real.log (2560 / 3279) ∧
    -Real.log (2560 / 3279) ≤ (6188281 / 25000000) := by
  have h := checkLog_sound (w := (719 / 5839)) (n := 12)
    (lo := (247531239 / 1000000000)) (hi := (6188281 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3279 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3279 / 2560) = 1/(2560 / 3279) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (247531239 / 1000000000) (6188281 / 25000000) (Real.log (3279 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3279 / 2560) = -Real.log (2560 / 3279) := by
    rw [show ((3279 / 2560) : ℝ) = ((2560 / 3279) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (82424589 / 250000000) ≤ -Real.log (1841 / 2560) ∧
    -Real.log (1841 / 2560) ≤ (329698357 / 1000000000) := by
  have h := checkLog_sound (w := (719 / 4401)) (n := 12)
    (lo := (82424589 / 250000000)) (hi := (329698357 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1841) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1841) = 1/(1841 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-329698357 / 1000000000) (-82424589 / 250000000) (Real.log (1841 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (123536839 / 500000000) ≤ -Real.log (1024 / 1311) ∧
    -Real.log (1024 / 1311) ≤ (247073679 / 1000000000) := by
  have h := checkLog_sound (w := (287 / 2335)) (n := 12)
    (lo := (123536839 / 500000000)) (hi := (247073679 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1311 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1311 / 1024) = 1/(1024 / 1311) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (123536839 / 500000000) (247073679 / 1000000000) (Real.log (1311 / 1024)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1311 / 1024) = -Real.log (1024 / 1311) := by
    rw [show ((1311 / 1024) : ℝ) = ((1024 / 1311) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (328883913 / 1000000000) ≤ -Real.log (737 / 1024) ∧
    -Real.log (737 / 1024) ≤ (164441957 / 500000000) := by
  have h := checkLog_sound (w := (287 / 1761)) (n := 12)
    (lo := (328883913 / 1000000000)) (hi := (164441957 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 737) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 737) = 1/(737 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-164441957 / 500000000) (-328883913 / 1000000000) (Real.log (737 / 1024)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (445786977 / 1000000000) ≤ -Real.log (1280 / 1999) ∧
    -Real.log (1280 / 1999) ≤ (222893489 / 500000000) := by
  have h := checkLog_sound (w := (719 / 3279)) (n := 12)
    (lo := (445786977 / 1000000000)) (hi := (222893489 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1999 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1999 / 1280) = 1/(1280 / 1999) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (445786977 / 1000000000) (222893489 / 500000000) (Real.log (1999 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1999 / 1280) = -Real.log (1280 / 1999) := by
    rw [show ((1999 / 1280) : ℝ) = ((1280 / 1999) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (16497889 / 20000000) ≤ -Real.log (561 / 1280) ∧
    -Real.log (561 / 1280) ≤ (206223613 / 250000000) := by
  have h := checkLog_sound (w := (79 / 1201)) (n := 12)
    (lo := (13174727 / 100000000)) (hi := (131747271 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 561) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 561) = 1/(561 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-206223613 / 250000000) (-16497889 / 20000000) (Real.log (561 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (2781477 / 6250000) ≤ -Real.log (512 / 799) ∧
    -Real.log (512 / 799) ≤ (445036321 / 1000000000) := by
  have h := checkLog_sound (w := (287 / 1311)) (n := 12)
    (lo := (2781477 / 6250000)) (hi := (445036321 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((799 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(799 / 512) = 1/(512 / 799) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (2781477 / 6250000) (445036321 / 1000000000) (Real.log (799 / 512)) := by
  have h := reflection_log_7_neg
  have he : Real.log (799 / 512) = -Real.log (512 / 799) := by
    rw [show ((799 / 512) : ℝ) = ((512 / 799) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (411112111 / 500000000) ≤ -Real.log (225 / 512) ∧
    -Real.log (225 / 512) ≤ (25694507 / 31250000) := by
  have h := checkLog_sound (w := (31 / 481)) (n := 12)
    (lo := (64538521 / 500000000)) (hi := (129077043 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((256 / 225) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(256 / 225) = 1/(225 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-25694507 / 31250000) (-411112111 / 500000000) (Real.log (225 / 512)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (338167227 / 1000000000) ≤ -Real.log (8000 / 11219) ∧
    -Real.log (8000 / 11219) ≤ (84541807 / 250000000) := by
  have h := checkLog_sound (w := (3219 / 19219)) (n := 12)
    (lo := (338167227 / 1000000000)) (hi := (84541807 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11219 / 8000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11219 / 8000) = 1/(8000 / 11219) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (338167227 / 1000000000) (84541807 / 250000000) (Real.log (11219 / 8000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (11219 / 8000) = -Real.log (8000 / 11219) := by
    rw [show ((11219 / 8000) : ℝ) = ((8000 / 11219) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (128697953 / 250000000) ≤ -Real.log (4781 / 8000) ∧
    -Real.log (4781 / 8000) ≤ (514791813 / 1000000000) := by
  have h := checkLog_sound (w := (3219 / 12781)) (n := 12)
    (lo := (128697953 / 250000000)) (hi := (514791813 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8000 / 4781) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(8000 / 4781) = 1/(4781 / 8000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-514791813 / 1000000000) (-128697953 / 250000000) (Real.log (4781 / 8000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (84697209 / 250000000) ≤ -Real.log (1000000 / 1403247) ∧
    -Real.log (1000000 / 1403247) ≤ (338788837 / 1000000000) := by
  have h := checkLog_sound (w := (403247 / 2403247)) (n := 12)
    (lo := (84697209 / 250000000)) (hi := (338788837 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1403247 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1403247 / 1000000) = 1/(1000000 / 1403247) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (84697209 / 250000000) (338788837 / 1000000000) (Real.log (1403247 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1403247 / 1000000) = -Real.log (1000000 / 1403247) := by
    rw [show ((1403247 / 1000000) : ℝ) = ((1000000 / 1403247) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (258125993 / 500000000) ≤ -Real.log (596753 / 1000000) ∧
    -Real.log (596753 / 1000000) ≤ (516251987 / 1000000000) := by
  have h := checkLog_sound (w := (403247 / 1596753)) (n := 12)
    (lo := (258125993 / 500000000)) (hi := (516251987 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 596753) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 596753) = 1/(596753 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-516251987 / 1000000000) (-258125993 / 500000000) (Real.log (596753 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (814723 / 3125000) ≤ -Real.log (1000000 / 1297853) ∧
    -Real.log (1000000 / 1297853) ≤ (260711361 / 1000000000) := by
  have h := checkLog_sound (w := (297853 / 2297853)) (n := 12)
    (lo := (814723 / 3125000)) (hi := (260711361 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1297853 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1297853 / 1000000) = 1/(1000000 / 1297853) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (814723 / 3125000) (260711361 / 1000000000) (Real.log (1297853 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1297853 / 1000000) = -Real.log (1000000 / 1297853) := by
    rw [show ((1297853 / 1000000) : ℝ) = ((1000000 / 1297853) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (70722499 / 200000000) ≤ -Real.log (702147 / 1000000) ∧
    -Real.log (702147 / 1000000) ≤ (22100781 / 62500000) := by
  have h := checkLog_sound (w := (297853 / 1702147)) (n := 12)
    (lo := (70722499 / 200000000)) (hi := (22100781 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 702147) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 702147) = 1/(702147 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-22100781 / 62500000) (-70722499 / 200000000) (Real.log (702147 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (65313797 / 250000000) ≤ -Real.log (1000000 / 1298559) ∧
    -Real.log (1000000 / 1298559) ≤ (261255189 / 1000000000) := by
  have h := checkLog_sound (w := (298559 / 2298559)) (n := 12)
    (lo := (65313797 / 250000000)) (hi := (261255189 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1298559 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1298559 / 1000000) = 1/(1000000 / 1298559) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (65313797 / 250000000) (261255189 / 1000000000) (Real.log (1298559 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1298559 / 1000000) = -Real.log (1000000 / 1298559) := by
    rw [show ((1298559 / 1000000) : ℝ) = ((1000000 / 1298559) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (44327311 / 125000000) ≤ -Real.log (701441 / 1000000) ∧
    -Real.log (701441 / 1000000) ≤ (354618489 / 1000000000) := by
  have h := checkLog_sound (w := (298559 / 1701441)) (n := 12)
    (lo := (44327311 / 125000000)) (hi := (354618489 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 701441) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 701441) = 1/(701441 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-354618489 / 1000000000) (-44327311 / 125000000) (Real.log (701441 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (852959039 / 1000000000) ≤ -Real.log (31250000000 / 73330631667) ∧
    -Real.log (31250000000 / 73330631667) ≤ (852959041 / 1000000000) := by
  have h := checkLog_sound (w := (10830631667 / 135830631667)) (n := 12)
    (lo := (159811859 / 1000000000)) (hi := (7990593 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((73330631667 / 62500000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(73330631667 / 62500000000) = 1/(31250000000 / 73330631667) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (852959039 / 1000000000) (852959041 / 1000000000) (Real.log (73330631667 / 31250000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (73330631667 / 31250000000) = -Real.log (31250000000 / 73330631667) := by
    rw [show ((73330631667 / 31250000000) : ℝ) = ((31250000000 / 73330631667) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (427520411 / 500000000) ≤ -Real.log (12500000000 / 29393379673) ∧
    -Real.log (12500000000 / 29393379673) ≤ (106880103 / 125000000) := by
  have h := checkLog_sound (w := (4393379673 / 54393379673)) (n := 12)
    (lo := (80946821 / 500000000)) (hi := (161893643 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((29393379673 / 25000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(29393379673 / 25000000000) = 1/(12500000000 / 29393379673) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (427520411 / 500000000) (106880103 / 125000000) (Real.log (29393379673 / 12500000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (29393379673 / 12500000000) = -Real.log (12500000000 / 29393379673) := by
    rw [show ((29393379673 / 12500000000) : ℝ) = ((12500000000 / 29393379673) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (122864771 / 200000000) ≤ -Real.log (250000000000 / 462101596959) ∧
    -Real.log (250000000000 / 462101596959) ≤ (38395241 / 62500000) := by
  have h := checkLog_sound (w := (212101596959 / 712101596959)) (n := 12)
    (lo := (122864771 / 200000000)) (hi := (38395241 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((462101596959 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(462101596959 / 250000000000) = 1/(250000000000 / 462101596959) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (122864771 / 200000000) (38395241 / 62500000) (Real.log (462101596959 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (462101596959 / 250000000000) = -Real.log (250000000000 / 462101596959) := by
    rw [show ((462101596959 / 250000000000) : ℝ) = ((250000000000 / 462101596959) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (153968419 / 250000000) ≤ -Real.log (500000000000 / 925636653689) ∧
    -Real.log (500000000000 / 925636653689) ≤ (615873677 / 1000000000) := by
  have h := checkLog_sound (w := (425636653689 / 1425636653689)) (n := 12)
    (lo := (153968419 / 250000000)) (hi := (615873677 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((925636653689 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(925636653689 / 500000000000) = 1/(500000000000 / 925636653689) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (153968419 / 250000000) (615873677 / 1000000000) (Real.log (925636653689 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (925636653689 / 500000000000) = -Real.log (500000000000 / 925636653689) := by
    rw [show ((925636653689 / 500000000000) : ℝ) = ((500000000000 / 925636653689) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0240
