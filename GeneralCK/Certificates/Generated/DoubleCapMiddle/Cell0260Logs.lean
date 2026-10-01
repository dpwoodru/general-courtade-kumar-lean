import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0260
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

theorem reflection_log_1_neg : (119169999 / 500000000) ≤ -Real.log (2560 / 3249) ∧
    -Real.log (2560 / 3249) ≤ (238339999 / 1000000000) := by
  have h := checkLog_sound (w := (689 / 5809)) (n := 12)
    (lo := (119169999 / 500000000)) (hi := (238339999 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3249 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3249 / 2560) = 1/(2560 / 3249) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (119169999 / 500000000) (238339999 / 1000000000) (Real.log (3249 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3249 / 2560) = -Real.log (2560 / 3249) := by
    rw [show ((3249 / 2560) : ℝ) = ((2560 / 3249) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (313534211 / 1000000000) ≤ -Real.log (1871 / 2560) ∧
    -Real.log (1871 / 2560) ≤ (78383553 / 250000000) := by
  have h := checkLog_sound (w := (689 / 4431)) (n := 12)
    (lo := (313534211 / 1000000000)) (hi := (78383553 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1871) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1871) = 1/(1871 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-78383553 / 250000000) (-313534211 / 1000000000) (Real.log (1871 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (237878211 / 1000000000) ≤ -Real.log (1024 / 1299) ∧
    -Real.log (1024 / 1299) ≤ (59469553 / 250000000) := by
  have h := checkLog_sound (w := (275 / 2323)) (n := 12)
    (lo := (237878211 / 1000000000)) (hi := (59469553 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1299 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1299 / 1024) = 1/(1024 / 1299) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (237878211 / 1000000000) (59469553 / 250000000) (Real.log (1299 / 1024)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1299 / 1024) = -Real.log (1024 / 1299) := by
    rw [show ((1299 / 1024) : ℝ) = ((1024 / 1299) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (156366411 / 500000000) ≤ -Real.log (749 / 1024) ∧
    -Real.log (749 / 1024) ≤ (312732823 / 1000000000) := by
  have h := checkLog_sound (w := (275 / 1773)) (n := 12)
    (lo := (156366411 / 500000000)) (hi := (312732823 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 749) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 749) = 1/(749 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-312732823 / 1000000000) (-156366411 / 500000000) (Real.log (749 / 1024)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (430665721 / 1000000000) ≤ -Real.log (1280 / 1969) ∧
    -Real.log (1280 / 1969) ≤ (215332861 / 500000000) := by
  have h := checkLog_sound (w := (689 / 3249)) (n := 12)
    (lo := (430665721 / 1000000000)) (hi := (215332861 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1969 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1969 / 1280) = 1/(1280 / 1969) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (430665721 / 1000000000) (215332861 / 500000000) (Real.log (1969 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1969 / 1280) = -Real.log (1280 / 1969) := by
    rw [show ((1969 / 1280) : ℝ) = ((1280 / 1969) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (386399669 / 500000000) ≤ -Real.log (591 / 1280) ∧
    -Real.log (591 / 1280) ≤ (38639967 / 50000000) := by
  have h := checkLog_sound (w := (49 / 1231)) (n := 12)
    (lo := (39826079 / 500000000)) (hi := (79652159 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 591) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 591) = 1/(591 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-38639967 / 50000000) (-386399669 / 500000000) (Real.log (591 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (429903623 / 1000000000) ≤ -Real.log (512 / 787) ∧
    -Real.log (512 / 787) ≤ (53737953 / 125000000) := by
  have h := checkLog_sound (w := (275 / 1299)) (n := 12)
    (lo := (429903623 / 1000000000)) (hi := (53737953 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((787 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(787 / 512) = 1/(512 / 787) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (429903623 / 1000000000) (53737953 / 125000000) (Real.log (787 / 512)) := by
  have h := reflection_log_7_neg
  have he : Real.log (787 / 512) = -Real.log (512 / 787) := by
    rw [show ((787 / 512) : ℝ) = ((512 / 787) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (770264483 / 1000000000) ≤ -Real.log (237 / 512) ∧
    -Real.log (237 / 512) ≤ (154052897 / 200000000) := by
  have h := checkLog_sound (w := (19 / 493)) (n := 12)
    (lo := (77117303 / 1000000000)) (hi := (9639663 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((256 / 237) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(256 / 237) = 1/(237 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-154052897 / 200000000) (-770264483 / 1000000000) (Real.log (237 / 512)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (325706637 / 1000000000) ≤ -Real.log (1000000 / 1385009) ∧
    -Real.log (1000000 / 1385009) ≤ (162853319 / 500000000) := by
  have h := checkLog_sound (w := (385009 / 2385009)) (n := 12)
    (lo := (325706637 / 1000000000)) (hi := (162853319 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1385009 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1385009 / 1000000) = 1/(1000000 / 1385009) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (325706637 / 1000000000) (162853319 / 500000000) (Real.log (1385009 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1385009 / 1000000) = -Real.log (1000000 / 1385009) := by
    rw [show ((1385009 / 1000000) : ℝ) = ((1000000 / 1385009) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (97229529 / 200000000) ≤ -Real.log (614991 / 1000000) ∧
    -Real.log (614991 / 1000000) ≤ (243073823 / 500000000) := by
  have h := checkLog_sound (w := (385009 / 1614991)) (n := 12)
    (lo := (97229529 / 200000000)) (hi := (243073823 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 614991) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 614991) = 1/(614991 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-243073823 / 500000000) (-97229529 / 200000000) (Real.log (614991 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (32633243 / 100000000) ≤ -Real.log (250000 / 346469) ∧
    -Real.log (250000 / 346469) ≤ (326332431 / 1000000000) := by
  have h := checkLog_sound (w := (96469 / 596469)) (n := 12)
    (lo := (32633243 / 100000000)) (hi := (326332431 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((346469 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(346469 / 250000) = 1/(250000 / 346469) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (32633243 / 100000000) (326332431 / 1000000000) (Real.log (346469 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (346469 / 250000) = -Real.log (250000 / 346469) := by
    rw [show ((346469 / 250000) : ℝ) = ((250000 / 346469) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (30472401 / 62500000) ≤ -Real.log (153531 / 250000) ∧
    -Real.log (153531 / 250000) ≤ (487558417 / 1000000000) := by
  have h := checkLog_sound (w := (96469 / 403531)) (n := 12)
    (lo := (30472401 / 62500000)) (hi := (487558417 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 153531) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 153531) = 1/(153531 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-487558417 / 1000000000) (-30472401 / 62500000) (Real.log (153531 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (62471491 / 250000000) ≤ -Real.log (1000000 / 1283879) ∧
    -Real.log (1000000 / 1283879) ≤ (49977193 / 200000000) := by
  have h := checkLog_sound (w := (283879 / 2283879)) (n := 12)
    (lo := (62471491 / 250000000)) (hi := (49977193 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1283879 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1283879 / 1000000) = 1/(1000000 / 1283879) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (62471491 / 250000000) (49977193 / 200000000) (Real.log (1283879 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1283879 / 1000000) = -Real.log (1000000 / 1283879) := by
    rw [show ((1283879 / 1000000) : ℝ) = ((1000000 / 1283879) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (333906131 / 1000000000) ≤ -Real.log (716121 / 1000000) ∧
    -Real.log (716121 / 1000000) ≤ (83476533 / 250000000) := by
  have h := checkLog_sound (w := (283879 / 1716121)) (n := 12)
    (lo := (333906131 / 1000000000)) (hi := (83476533 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 716121) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 716121) = 1/(716121 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-83476533 / 250000000) (-333906131 / 1000000000) (Real.log (716121 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (250426367 / 1000000000) ≤ -Real.log (1000000 / 1284573) ∧
    -Real.log (1000000 / 1284573) ≤ (489114 / 1953125) := by
  have h := checkLog_sound (w := (284573 / 2284573)) (n := 12)
    (lo := (250426367 / 1000000000)) (hi := (489114 / 1953125))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1284573 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1284573 / 1000000) = 1/(1000000 / 1284573) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (250426367 / 1000000000) (489114 / 1953125) (Real.log (1284573 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1284573 / 1000000) = -Real.log (1000000 / 1284573) := by
    rw [show ((1284573 / 1000000) : ℝ) = ((1000000 / 1284573) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (334875711 / 1000000000) ≤ -Real.log (715427 / 1000000) ∧
    -Real.log (715427 / 1000000) ≤ (5232433 / 15625000) := by
  have h := checkLog_sound (w := (284573 / 1715427)) (n := 12)
    (lo := (334875711 / 1000000000)) (hi := (5232433 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 715427) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 715427) = 1/(715427 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-5232433 / 15625000) (-334875711 / 1000000000) (Real.log (715427 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (405927141 / 500000000) ≤ -Real.log (50000000000 / 112604005587) ∧
    -Real.log (50000000000 / 112604005587) ≤ (202963571 / 250000000) := by
  have h := checkLog_sound (w := (12604005587 / 212604005587)) (n := 12)
    (lo := (59353551 / 500000000)) (hi := (118707103 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((112604005587 / 100000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(112604005587 / 100000000000) = 1/(50000000000 / 112604005587) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (405927141 / 500000000) (202963571 / 250000000) (Real.log (112604005587 / 50000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (112604005587 / 50000000000) = -Real.log (50000000000 / 112604005587) := by
    rw [show ((112604005587 / 50000000000) : ℝ) = ((50000000000 / 112604005587) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (406945423 / 500000000) ≤ -Real.log (50000000000 / 112833564557) ∧
    -Real.log (50000000000 / 112833564557) ≤ (25434089 / 31250000) := by
  have h := checkLog_sound (w := (12833564557 / 212833564557)) (n := 12)
    (lo := (60371833 / 500000000)) (hi := (120743667 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((112833564557 / 100000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(112833564557 / 100000000000) = 1/(50000000000 / 112833564557) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (406945423 / 500000000) (25434089 / 31250000) (Real.log (112833564557 / 50000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (112833564557 / 50000000000) = -Real.log (50000000000 / 112833564557) := by
    rw [show ((112833564557 / 50000000000) : ℝ) = ((50000000000 / 112833564557) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (116758419 / 200000000) ≤ -Real.log (100000000000 / 179282411771) ∧
    -Real.log (100000000000 / 179282411771) ≤ (18243503 / 31250000) := by
  have h := checkLog_sound (w := (79282411771 / 279282411771)) (n := 12)
    (lo := (116758419 / 200000000)) (hi := (18243503 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((179282411771 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(179282411771 / 100000000000) = 1/(100000000000 / 179282411771) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (116758419 / 200000000) (18243503 / 31250000) (Real.log (179282411771 / 100000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (179282411771 / 100000000000) = -Real.log (100000000000 / 179282411771) := by
    rw [show ((179282411771 / 100000000000) : ℝ) = ((100000000000 / 179282411771) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (585302079 / 1000000000) ≤ -Real.log (10000000000 / 17955332969) ∧
    -Real.log (10000000000 / 17955332969) ≤ (1829069 / 3125000) := by
  have h := checkLog_sound (w := (7955332969 / 27955332969)) (n := 12)
    (lo := (585302079 / 1000000000)) (hi := (1829069 / 3125000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((17955332969 / 10000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(17955332969 / 10000000000) = 1/(10000000000 / 17955332969) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (585302079 / 1000000000) (1829069 / 3125000) (Real.log (17955332969 / 10000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (17955332969 / 10000000000) = -Real.log (10000000000 / 17955332969) := by
    rw [show ((17955332969 / 10000000000) : ℝ) = ((10000000000 / 17955332969) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0260
