import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0390
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

theorem reflection_log_1_neg : (40524383 / 200000000) ≤ -Real.log (512 / 627) ∧
    -Real.log (512 / 627) ≤ (50655479 / 250000000) := by
  have h := checkLog_sound (w := (115 / 1139)) (n := 12)
    (lo := (40524383 / 200000000)) (hi := (50655479 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((627 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(627 / 512) = 1/(512 / 627) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (40524383 / 200000000) (50655479 / 250000000) (Real.log (627 / 512)) := by
  have h := reflection_log_1_neg
  have he : Real.log (627 / 512) = -Real.log (512 / 627) := by
    rw [show ((627 / 512) : ℝ) = ((512 / 627) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (31798543 / 125000000) ≤ -Real.log (397 / 512) ∧
    -Real.log (397 / 512) ≤ (50877669 / 200000000) := by
  have h := checkLog_sound (w := (115 / 909)) (n := 12)
    (lo := (31798543 / 125000000)) (hi := (50877669 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 397) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 397) = 1/(397 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-50877669 / 200000000) (-31798543 / 125000000) (Real.log (397 / 512)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (50595663 / 250000000) ≤ -Real.log (10240 / 12537) ∧
    -Real.log (10240 / 12537) ≤ (202382653 / 1000000000) := by
  have h := checkLog_sound (w := (2297 / 22777)) (n := 12)
    (lo := (50595663 / 250000000)) (hi := (202382653 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12537 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12537 / 10240) = 1/(10240 / 12537) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (50595663 / 250000000) (202382653 / 1000000000) (Real.log (12537 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12537 / 10240) = -Real.log (10240 / 12537) := by
    rw [show ((12537 / 10240) : ℝ) = ((10240 / 12537) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (254010581 / 1000000000) ≤ -Real.log (7943 / 10240) ∧
    -Real.log (7943 / 10240) ≤ (127005291 / 500000000) := by
  have h := checkLog_sound (w := (2297 / 18183)) (n := 12)
    (lo := (254010581 / 1000000000)) (hi := (127005291 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7943) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7943) = 1/(7943 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-127005291 / 500000000) (-254010581 / 1000000000) (Real.log (7943 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (185512309 / 500000000) ≤ -Real.log (256 / 371) ∧
    -Real.log (256 / 371) ≤ (371024619 / 1000000000) := by
  have h := checkLog_sound (w := (115 / 627)) (n := 12)
    (lo := (185512309 / 500000000)) (hi := (371024619 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((371 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(371 / 256) = 1/(256 / 371) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (185512309 / 500000000) (371024619 / 1000000000) (Real.log (371 / 256)) := by
  have h := reflection_log_5_neg
  have he : Real.log (371 / 256) = -Real.log (256 / 371) := by
    rw [show ((371 / 256) : ℝ) = ((256 / 371) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (298208777 / 500000000) ≤ -Real.log (141 / 256) ∧
    -Real.log (141 / 256) ≤ (119283511 / 200000000) := by
  have h := checkLog_sound (w := (115 / 397)) (n := 12)
    (lo := (298208777 / 500000000)) (hi := (119283511 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((256 / 141) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(256 / 141) = 1/(141 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-119283511 / 200000000) (-298208777 / 500000000) (Real.log (141 / 256)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (370620223 / 1000000000) ≤ -Real.log (5120 / 7417) ∧
    -Real.log (5120 / 7417) ≤ (5790941 / 15625000) := by
  have h := checkLog_sound (w := (2297 / 12537)) (n := 12)
    (lo := (370620223 / 1000000000)) (hi := (5790941 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7417 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7417 / 5120) = 1/(5120 / 7417) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (370620223 / 1000000000) (5790941 / 15625000) (Real.log (7417 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (7417 / 5120) = -Real.log (5120 / 7417) := by
    rw [show ((7417 / 5120) : ℝ) = ((5120 / 7417) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (595354289 / 1000000000) ≤ -Real.log (2823 / 5120) ∧
    -Real.log (2823 / 5120) ≤ (59535429 / 100000000) := by
  have h := checkLog_sound (w := (2297 / 7943)) (n := 12)
    (lo := (595354289 / 1000000000)) (hi := (59535429 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2823) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2823) = 1/(2823 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-59535429 / 100000000) (-595354289 / 1000000000) (Real.log (2823 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (277737791 / 1000000000) ≤ -Real.log (50000 / 66007) ∧
    -Real.log (50000 / 66007) ≤ (4339653 / 15625000) := by
  have h := checkLog_sound (w := (16007 / 116007)) (n := 12)
    (lo := (277737791 / 1000000000)) (hi := (4339653 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((66007 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(66007 / 50000) = 1/(50000 / 66007) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (277737791 / 1000000000) (4339653 / 15625000) (Real.log (66007 / 50000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (66007 / 50000) = -Real.log (50000 / 66007) := by
    rw [show ((66007 / 50000) : ℝ) = ((50000 / 66007) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (12058387 / 31250000) ≤ -Real.log (33993 / 50000) ∧
    -Real.log (33993 / 50000) ≤ (77173677 / 200000000) := by
  have h := checkLog_sound (w := (16007 / 83993)) (n := 12)
    (lo := (12058387 / 31250000)) (hi := (77173677 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 33993) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 33993) = 1/(33993 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-77173677 / 200000000) (-12058387 / 31250000) (Real.log (33993 / 50000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (278061947 / 1000000000) ≤ -Real.log (125000 / 165071) ∧
    -Real.log (125000 / 165071) ≤ (69515487 / 250000000) := by
  have h := checkLog_sound (w := (40071 / 290071)) (n := 12)
    (lo := (278061947 / 1000000000)) (hi := (69515487 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((165071 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(165071 / 125000) = 1/(125000 / 165071) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (278061947 / 1000000000) (69515487 / 250000000) (Real.log (165071 / 125000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (165071 / 125000) = -Real.log (125000 / 165071) := by
    rw [show ((165071 / 125000) : ℝ) = ((125000 / 165071) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (386498123 / 1000000000) ≤ -Real.log (84929 / 125000) ∧
    -Real.log (84929 / 125000) ≤ (96624531 / 250000000) := by
  have h := checkLog_sound (w := (40071 / 209929)) (n := 12)
    (lo := (386498123 / 1000000000)) (hi := (96624531 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 84929) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 84929) = 1/(84929 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-96624531 / 250000000) (-386498123 / 1000000000) (Real.log (84929 / 125000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (52359109 / 250000000) ≤ -Real.log (1000000 / 1232983) ∧
    -Real.log (1000000 / 1232983) ≤ (209436437 / 1000000000) := by
  have h := checkLog_sound (w := (232983 / 2232983)) (n := 12)
    (lo := (52359109 / 250000000)) (hi := (209436437 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1232983 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1232983 / 1000000) = 1/(1000000 / 1232983) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (52359109 / 250000000) (209436437 / 1000000000) (Real.log (1232983 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1232983 / 1000000) = -Real.log (1000000 / 1232983) := by
    rw [show ((1232983 / 1000000) : ℝ) = ((1000000 / 1232983) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (265246313 / 1000000000) ≤ -Real.log (767017 / 1000000) ∧
    -Real.log (767017 / 1000000) ≤ (132623157 / 500000000) := by
  have h := checkLog_sound (w := (232983 / 1767017)) (n := 12)
    (lo := (265246313 / 1000000000)) (hi := (132623157 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 767017) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 767017) = 1/(767017 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-132623157 / 500000000) (-265246313 / 1000000000) (Real.log (767017 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (52426011 / 250000000) ≤ -Real.log (1000000 / 1233313) ∧
    -Real.log (1000000 / 1233313) ≤ (41940809 / 200000000) := by
  have h := checkLog_sound (w := (233313 / 2233313)) (n := 12)
    (lo := (52426011 / 250000000)) (hi := (41940809 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1233313 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1233313 / 1000000) = 1/(1000000 / 1233313) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (52426011 / 250000000) (41940809 / 200000000) (Real.log (1233313 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1233313 / 1000000) = -Real.log (1000000 / 1233313) := by
    rw [show ((1233313 / 1000000) : ℝ) = ((1000000 / 1233313) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (66419161 / 250000000) ≤ -Real.log (766687 / 1000000) ∧
    -Real.log (766687 / 1000000) ≤ (53135329 / 200000000) := by
  have h := checkLog_sound (w := (233313 / 1766687)) (n := 12)
    (lo := (66419161 / 250000000)) (hi := (53135329 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 766687) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 766687) = 1/(766687 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-53135329 / 200000000) (-66419161 / 250000000) (Real.log (766687 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (26544247 / 40000000) ≤ -Real.log (500000000000 / 970891065807) ∧
    -Real.log (500000000000 / 970891065807) ≤ (20737693 / 31250000) := by
  have h := checkLog_sound (w := (470891065807 / 1470891065807)) (n := 12)
    (lo := (26544247 / 40000000)) (hi := (20737693 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((970891065807 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(970891065807 / 500000000000) = 1/(500000000000 / 970891065807) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (26544247 / 40000000) (20737693 / 31250000) (Real.log (970891065807 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (970891065807 / 500000000000) = -Real.log (500000000000 / 970891065807) := by
    rw [show ((970891065807 / 500000000000) : ℝ) = ((500000000000 / 970891065807) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (664560071 / 1000000000) ≤ -Real.log (125000000000 / 242954408977) ∧
    -Real.log (125000000000 / 242954408977) ≤ (83070009 / 125000000) := by
  have h := checkLog_sound (w := (117954408977 / 367954408977)) (n := 12)
    (lo := (664560071 / 1000000000)) (hi := (83070009 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((242954408977 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(242954408977 / 125000000000) = 1/(125000000000 / 242954408977) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (664560071 / 1000000000) (83070009 / 125000000) (Real.log (242954408977 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (242954408977 / 125000000000) = -Real.log (125000000000 / 242954408977) := by
    rw [show ((242954408977 / 125000000000) : ℝ) = ((125000000000 / 242954408977) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1898731 / 4000000) ≤ -Real.log (125000000000 / 200938017019) ∧
    -Real.log (125000000000 / 200938017019) ≤ (474682751 / 1000000000) := by
  have h := checkLog_sound (w := (75938017019 / 325938017019)) (n := 12)
    (lo := (1898731 / 4000000)) (hi := (474682751 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200938017019 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200938017019 / 125000000000) = 1/(125000000000 / 200938017019) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (1898731 / 4000000) (474682751 / 1000000000) (Real.log (200938017019 / 125000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (200938017019 / 125000000000) = -Real.log (125000000000 / 200938017019) := by
    rw [show ((200938017019 / 125000000000) : ℝ) = ((125000000000 / 200938017019) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (29711293 / 62500000) ≤ -Real.log (62500000000 / 100539154179) ∧
    -Real.log (62500000000 / 100539154179) ≤ (475380689 / 1000000000) := by
  have h := checkLog_sound (w := (38039154179 / 163039154179)) (n := 12)
    (lo := (29711293 / 62500000)) (hi := (475380689 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100539154179 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100539154179 / 62500000000) = 1/(62500000000 / 100539154179) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (29711293 / 62500000) (475380689 / 1000000000) (Real.log (100539154179 / 62500000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (100539154179 / 62500000000) = -Real.log (62500000000 / 100539154179) := by
    rw [show ((100539154179 / 62500000000) : ℝ) = ((62500000000 / 100539154179) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0390
