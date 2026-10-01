import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_704_neg : (10132549 / 125000000) ≤ -Real.log (461069 / 500000) ∧
    -Real.log (461069 / 500000) ≤ (81060393 / 1000000000) := by
  have h := checkLog_sound (w := (38931 / 961069)) (n := 12)
    (lo := (10132549 / 125000000)) (hi := (81060393 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 461069) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 461069) = 1/(461069 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_704 : Bounds (-81060393 / 1000000000) (-10132549 / 125000000) (Real.log (461069 / 500000)) := by
  have h := reflection_log_704_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_705_neg : (1503411 / 20000000) ≤ -Real.log (250000 / 269517) ∧
    -Real.log (250000 / 269517) ≤ (75170551 / 1000000000) := by
  have h := checkLog_sound (w := (19517 / 519517)) (n := 12)
    (lo := (1503411 / 20000000)) (hi := (75170551 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((269517 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(269517 / 250000) = 1/(250000 / 269517) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_705 : Bounds (1503411 / 20000000) (75170551 / 1000000000) (Real.log (269517 / 250000)) := by
  have h := reflection_log_705_neg
  have he : Real.log (269517 / 250000) = -Real.log (250000 / 269517) := by
    rw [show ((269517 / 250000) : ℝ) = ((250000 / 269517) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_706_neg : (8128381 / 100000000) ≤ -Real.log (230483 / 250000) ∧
    -Real.log (230483 / 250000) ≤ (81283811 / 1000000000) := by
  have h := checkLog_sound (w := (19517 / 480483)) (n := 12)
    (lo := (8128381 / 100000000)) (hi := (81283811 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 230483) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 230483) = 1/(230483 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_706 : Bounds (-81283811 / 1000000000) (-8128381 / 100000000) (Real.log (230483 / 250000)) := by
  have h := reflection_log_706_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_707_neg : (305663 / 50000000) ≤ -Real.log (62119086711 / 62500000000) ∧
    -Real.log (62119086711 / 62500000000) ≤ (6113261 / 1000000000) := by
  have h := checkLog_sound (w := (380913289 / 124619086711)) (n := 12)
    (lo := (305663 / 50000000)) (hi := (6113261 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 62119086711) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 62119086711) = 1/(62119086711 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_707 : Bounds (-6113261 / 1000000000) (-305663 / 50000000) (Real.log (62119086711 / 62500000000)) := by
  have h := reflection_log_707_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_708_neg : (3040471 / 500000000) ≤ -Real.log (248484377239 / 250000000000) ∧
    -Real.log (248484377239 / 250000000000) ≤ (6080943 / 1000000000) := by
  have h := checkLog_sound (w := (1515622761 / 498484377239)) (n := 12)
    (lo := (3040471 / 500000000)) (hi := (6080943 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248484377239) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248484377239) = 1/(248484377239 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_708 : Bounds (-6080943 / 1000000000) (-3040471 / 500000000) (Real.log (248484377239 / 250000000000)) := by
  have h := reflection_log_708_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_709_neg : (156039841 / 1000000000) ≤ -Real.log (500000000000 / 584436385877) ∧
    -Real.log (500000000000 / 584436385877) ≤ (78019921 / 500000000) := by
  have h := checkLog_sound (w := (84436385877 / 1084436385877)) (n := 12)
    (lo := (156039841 / 1000000000)) (hi := (78019921 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((584436385877 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(584436385877 / 500000000000) = 1/(500000000000 / 584436385877) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_709 : Bounds (156039841 / 1000000000) (78019921 / 500000000) (Real.log (584436385877 / 500000000000)) := by
  have h := reflection_log_709_neg
  have he : Real.log (584436385877 / 500000000000) = -Real.log (500000000000 / 584436385877) := by
    rw [show ((584436385877 / 500000000000) : ℝ) = ((500000000000 / 584436385877) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_710_neg : (156454361 / 1000000000) ≤ -Real.log (500000000000 / 584678696477) ∧
    -Real.log (500000000000 / 584678696477) ≤ (78227181 / 500000000) := by
  have h := checkLog_sound (w := (84678696477 / 1084678696477)) (n := 12)
    (lo := (156454361 / 1000000000)) (hi := (78227181 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((584678696477 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(584678696477 / 500000000000) = 1/(500000000000 / 584678696477) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_710 : Bounds (156454361 / 1000000000) (78227181 / 500000000) (Real.log (584678696477 / 500000000000)) := by
  have h := reflection_log_710_neg
  have he : Real.log (584678696477 / 500000000000) = -Real.log (500000000000 / 584678696477) := by
    rw [show ((584678696477 / 500000000000) : ℝ) = ((500000000000 / 584678696477) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_711_neg : (62585771 / 200000000) ≤ -Real.log (125000000000 / 170928030303) ∧
    -Real.log (125000000000 / 170928030303) ≤ (39116107 / 125000000) := by
  have h := checkLog_sound (w := (45928030303 / 295928030303)) (n := 12)
    (lo := (62585771 / 200000000)) (hi := (39116107 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((170928030303 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(170928030303 / 125000000000) = 1/(125000000000 / 170928030303) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_711 : Bounds (62585771 / 200000000) (39116107 / 125000000) (Real.log (170928030303 / 125000000000)) := by
  have h := reflection_log_711_neg
  have he : Real.log (170928030303 / 125000000000) = -Real.log (125000000000 / 170928030303) := by
    rw [show ((170928030303 / 125000000000) : ℝ) = ((125000000000 / 170928030303) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_712_neg : (156566897 / 500000000) ≤ -Real.log (500000000000 / 683852255239) ∧
    -Real.log (500000000000 / 683852255239) ≤ (62626759 / 200000000) := by
  have h := checkLog_sound (w := (183852255239 / 1183852255239)) (n := 12)
    (lo := (156566897 / 500000000)) (hi := (62626759 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((683852255239 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(683852255239 / 500000000000) = 1/(500000000000 / 683852255239) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_712 : Bounds (156566897 / 500000000) (62626759 / 200000000) (Real.log (683852255239 / 500000000000)) := by
  have h := reflection_log_712_neg
  have he : Real.log (683852255239 / 500000000000) = -Real.log (500000000000 / 683852255239) := by
    rw [show ((683852255239 / 500000000000) : ℝ) = ((500000000000 / 683852255239) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_713_neg : (36111651 / 250000000) ≤ -Real.log (5000 / 5777) ∧
    -Real.log (5000 / 5777) ≤ (28889321 / 200000000) := by
  have h := checkLog_sound (w := (777 / 10777)) (n := 12)
    (lo := (36111651 / 250000000)) (hi := (28889321 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5777 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5777 / 5000) = 1/(5000 / 5777) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_713 : Bounds (36111651 / 250000000) (28889321 / 200000000) (Real.log (5777 / 5000)) := by
  have h := reflection_log_713_neg
  have he : Real.log (5777 / 5000) = -Real.log (5000 / 5777) := by
    rw [show ((5777 / 5000) : ℝ) = ((5000 / 5777) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_714_neg : (21111517 / 125000000) ≤ -Real.log (4223 / 5000) ∧
    -Real.log (4223 / 5000) ≤ (168892137 / 1000000000) := by
  have h := checkLog_sound (w := (777 / 9223)) (n := 12)
    (lo := (21111517 / 125000000)) (hi := (168892137 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4223) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4223) = 1/(4223 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_714 : Bounds (-168892137 / 1000000000) (-21111517 / 125000000) (Real.log (4223 / 5000)) := by
  have h := reflection_log_714_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_715_neg : (155387 / 1000000000) ≤ -Real.log (5000000 / 5000777) ∧
    -Real.log (5000000 / 5000777) ≤ (38847 / 250000000) := by
  have h := checkLog_sound (w := (777 / 10000777)) (n := 12)
    (lo := (155387 / 1000000000)) (hi := (38847 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000777 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000777 / 5000000) = 1/(5000000 / 5000777) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_715 : Bounds (155387 / 1000000000) (38847 / 250000000) (Real.log (5000777 / 5000000)) := by
  have h := reflection_log_715_neg
  have he : Real.log (5000777 / 5000000) = -Real.log (5000000 / 5000777) := by
    rw [show ((5000777 / 5000000) : ℝ) = ((5000000 / 5000777) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_716_neg : (38853 / 250000000) ≤ -Real.log (4999223 / 5000000) ∧
    -Real.log (4999223 / 5000000) ≤ (155413 / 1000000000) := by
  have h := checkLog_sound (w := (777 / 9999223)) (n := 12)
    (lo := (38853 / 250000000)) (hi := (155413 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999223) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999223) = 1/(4999223 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_716 : Bounds (-155413 / 1000000000) (-38853 / 250000000) (Real.log (4999223 / 5000000)) := by
  have h := reflection_log_716_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_717_neg : (18756459 / 250000000) ≤ -Real.log (125000 / 134739) ∧
    -Real.log (125000 / 134739) ≤ (75025837 / 1000000000) := by
  have h := checkLog_sound (w := (9739 / 259739)) (n := 12)
    (lo := (18756459 / 250000000)) (hi := (75025837 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((134739 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(134739 / 125000) = 1/(125000 / 134739) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_717 : Bounds (18756459 / 250000000) (75025837 / 1000000000) (Real.log (134739 / 125000)) := by
  have h := reflection_log_717_neg
  have he : Real.log (134739 / 125000) = -Real.log (125000 / 134739) := by
    rw [show ((134739 / 125000) : ℝ) = ((125000 / 134739) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_718_neg : (16222923 / 200000000) ≤ -Real.log (115261 / 125000) ∧
    -Real.log (115261 / 125000) ≤ (10139327 / 125000000) := by
  have h := checkLog_sound (w := (9739 / 240261)) (n := 12)
    (lo := (16222923 / 200000000)) (hi := (10139327 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 115261) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 115261) = 1/(115261 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_718 : Bounds (-10139327 / 125000000) (-16222923 / 200000000) (Real.log (115261 / 125000)) := by
  have h := reflection_log_718_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_719_neg : (1175279 / 15625000) ≤ -Real.log (1000000 / 1078119) ∧
    -Real.log (1000000 / 1078119) ≤ (75217857 / 1000000000) := by
  have h := checkLog_sound (w := (78119 / 2078119)) (n := 12)
    (lo := (1175279 / 15625000)) (hi := (75217857 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1078119 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1078119 / 1000000) = 1/(1000000 / 1078119) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_719 : Bounds (1175279 / 15625000) (75217857 / 1000000000) (Real.log (1078119 / 1000000)) := by
  have h := reflection_log_719_neg
  have he : Real.log (1078119 / 1000000) = -Real.log (1000000 / 1078119) := by
    rw [show ((1078119 / 1000000) : ℝ) = ((1000000 / 1078119) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_720_neg : (81339131 / 1000000000) ≤ -Real.log (921881 / 1000000) ∧
    -Real.log (921881 / 1000000) ≤ (20334783 / 250000000) := by
  have h := checkLog_sound (w := (78119 / 1921881)) (n := 12)
    (lo := (81339131 / 1000000000)) (hi := (20334783 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 921881) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 921881) = 1/(921881 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_720 : Bounds (-20334783 / 250000000) (-81339131 / 1000000000) (Real.log (921881 / 1000000)) := by
  have h := reflection_log_720_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_721_neg : (3060637 / 500000000) ≤ -Real.log (993897421839 / 1000000000000) ∧
    -Real.log (993897421839 / 1000000000000) ≤ (244851 / 40000000) := by
  have h := checkLog_sound (w := (6102578161 / 1993897421839)) (n := 12)
    (lo := (3060637 / 500000000)) (hi := (244851 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993897421839) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993897421839) = 1/(993897421839 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_721 : Bounds (-244851 / 40000000) (-3060637 / 500000000) (Real.log (993897421839 / 1000000000000)) := by
  have h := reflection_log_721_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_722_neg : (3044389 / 500000000) ≤ -Real.log (15530151879 / 15625000000) ∧
    -Real.log (15530151879 / 15625000000) ≤ (6088779 / 1000000000) := by
  have h := checkLog_sound (w := (94848121 / 31155151879)) (n := 12)
    (lo := (3044389 / 500000000)) (hi := (6088779 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 15530151879) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 15530151879) = 1/(15530151879 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_722 : Bounds (-6088779 / 1000000000) (-3044389 / 500000000) (Real.log (15530151879 / 15625000000)) := by
  have h := reflection_log_722_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_723_neg : (156140451 / 1000000000) ≤ -Real.log (500000000000 / 584495189179) ∧
    -Real.log (500000000000 / 584495189179) ≤ (39035113 / 250000000) := by
  have h := checkLog_sound (w := (84495189179 / 1084495189179)) (n := 12)
    (lo := (156140451 / 1000000000)) (hi := (39035113 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((584495189179 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(584495189179 / 500000000000) = 1/(500000000000 / 584495189179) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_723 : Bounds (156140451 / 1000000000) (39035113 / 250000000) (Real.log (584495189179 / 500000000000)) := by
  have h := reflection_log_723_neg
  have he : Real.log (584495189179 / 500000000000) = -Real.log (500000000000 / 584495189179) := by
    rw [show ((584495189179 / 500000000000) : ℝ) = ((500000000000 / 584495189179) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_724_neg : (156556987 / 1000000000) ≤ -Real.log (250000000000 / 292369351359) ∧
    -Real.log (250000000000 / 292369351359) ≤ (39139247 / 250000000) := by
  have h := checkLog_sound (w := (42369351359 / 542369351359)) (n := 12)
    (lo := (156556987 / 1000000000)) (hi := (39139247 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((292369351359 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(292369351359 / 250000000000) = 1/(250000000000 / 292369351359) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_724 : Bounds (156556987 / 1000000000) (39139247 / 250000000) (Real.log (292369351359 / 250000000000)) := by
  have h := reflection_log_724_neg
  have he : Real.log (292369351359 / 250000000000) = -Real.log (250000000000 / 292369351359) := by
    rw [show ((292369351359 / 250000000000) : ℝ) = ((250000000000 / 292369351359) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_725_neg : (156566897 / 500000000) ≤ -Real.log (250000000000 / 341926127619) ∧
    -Real.log (250000000000 / 341926127619) ≤ (62626759 / 200000000) := by
  have h := checkLog_sound (w := (91926127619 / 591926127619)) (n := 12)
    (lo := (156566897 / 500000000)) (hi := (62626759 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((341926127619 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(341926127619 / 250000000000) = 1/(250000000000 / 341926127619) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_725 : Bounds (156566897 / 500000000) (62626759 / 200000000) (Real.log (341926127619 / 250000000000)) := by
  have h := reflection_log_725_neg
  have he : Real.log (341926127619 / 250000000000) = -Real.log (250000000000 / 341926127619) := by
    rw [show ((341926127619 / 250000000000) : ℝ) = ((250000000000 / 341926127619) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_726_neg : (15666937 / 50000000) ≤ -Real.log (500000000000 / 683992422449) ∧
    -Real.log (500000000000 / 683992422449) ≤ (313338741 / 1000000000) := by
  have h := checkLog_sound (w := (183992422449 / 1183992422449)) (n := 12)
    (lo := (15666937 / 50000000)) (hi := (313338741 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((683992422449 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(683992422449 / 500000000000) = 1/(500000000000 / 683992422449) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_726 : Bounds (15666937 / 50000000) (313338741 / 1000000000) (Real.log (683992422449 / 500000000000)) := by
  have h := reflection_log_726_neg
  have he : Real.log (683992422449 / 500000000000) = -Real.log (500000000000 / 683992422449) := by
    rw [show ((683992422449 / 500000000000) : ℝ) = ((500000000000 / 683992422449) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_727_neg : (2890663 / 20000000) ≤ -Real.log (2000 / 2311) ∧
    -Real.log (2000 / 2311) ≤ (144533151 / 1000000000) := by
  have h := checkLog_sound (w := (311 / 4311)) (n := 12)
    (lo := (2890663 / 20000000)) (hi := (144533151 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2311 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2311 / 2000) = 1/(2000 / 2311) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_727 : Bounds (2890663 / 20000000) (144533151 / 1000000000) (Real.log (2311 / 2000)) := by
  have h := reflection_log_727_neg
  have he : Real.log (2311 / 2000) = -Real.log (2000 / 2311) := by
    rw [show ((2311 / 2000) : ℝ) = ((2000 / 2311) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_728_neg : (84505271 / 500000000) ≤ -Real.log (1689 / 2000) ∧
    -Real.log (1689 / 2000) ≤ (169010543 / 1000000000) := by
  have h := checkLog_sound (w := (311 / 3689)) (n := 12)
    (lo := (84505271 / 500000000)) (hi := (169010543 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1689) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1689) = 1/(1689 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_728 : Bounds (-169010543 / 1000000000) (-84505271 / 500000000) (Real.log (1689 / 2000)) := by
  have h := reflection_log_728_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_729_neg : (155487 / 1000000000) ≤ -Real.log (2000000 / 2000311) ∧
    -Real.log (2000000 / 2000311) ≤ (4859 / 31250000) := by
  have h := checkLog_sound (w := (311 / 4000311)) (n := 12)
    (lo := (155487 / 1000000000)) (hi := (4859 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000311 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000311 / 2000000) = 1/(2000000 / 2000311) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_729 : Bounds (155487 / 1000000000) (4859 / 31250000) (Real.log (2000311 / 2000000)) := by
  have h := reflection_log_729_neg
  have he : Real.log (2000311 / 2000000) = -Real.log (2000000 / 2000311) := by
    rw [show ((2000311 / 2000000) : ℝ) = ((2000000 / 2000311) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_730_neg : (19439 / 125000000) ≤ -Real.log (1999689 / 2000000) ∧
    -Real.log (1999689 / 2000000) ≤ (155513 / 1000000000) := by
  have h := checkLog_sound (w := (311 / 3999689)) (n := 12)
    (lo := (19439 / 125000000)) (hi := (155513 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999689) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999689) = 1/(1999689 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_730 : Bounds (-155513 / 1000000000) (-19439 / 125000000) (Real.log (1999689 / 2000000)) := by
  have h := reflection_log_730_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_731_neg : (75073149 / 1000000000) ≤ -Real.log (1000000 / 1077963) ∧
    -Real.log (1000000 / 1077963) ≤ (1501463 / 20000000) := by
  have h := checkLog_sound (w := (77963 / 2077963)) (n := 12)
    (lo := (75073149 / 1000000000)) (hi := (1501463 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1077963 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1077963 / 1000000) = 1/(1000000 / 1077963) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_731 : Bounds (75073149 / 1000000000) (1501463 / 20000000) (Real.log (1077963 / 1000000)) := by
  have h := reflection_log_731_neg
  have he : Real.log (1077963 / 1000000) = -Real.log (1000000 / 1077963) := by
    rw [show ((1077963 / 1000000) : ℝ) = ((1000000 / 1077963) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_732_neg : (40584963 / 500000000) ≤ -Real.log (922037 / 1000000) ∧
    -Real.log (922037 / 1000000) ≤ (81169927 / 1000000000) := by
  have h := checkLog_sound (w := (77963 / 1922037)) (n := 12)
    (lo := (40584963 / 500000000)) (hi := (81169927 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 922037) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 922037) = 1/(922037 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_732 : Bounds (-81169927 / 1000000000) (-40584963 / 500000000) (Real.log (922037 / 1000000)) := by
  have h := reflection_log_732_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_733_neg : (75264231 / 1000000000) ≤ -Real.log (1000000 / 1078169) ∧
    -Real.log (1000000 / 1078169) ≤ (9408029 / 125000000) := by
  have h := checkLog_sound (w := (78169 / 2078169)) (n := 12)
    (lo := (75264231 / 1000000000)) (hi := (9408029 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1078169 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1078169 / 1000000) = 1/(1000000 / 1078169) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_733 : Bounds (75264231 / 1000000000) (9408029 / 125000000) (Real.log (1078169 / 1000000)) := by
  have h := reflection_log_733_neg
  have he : Real.log (1078169 / 1000000) = -Real.log (1000000 / 1078169) := by
    rw [show ((1078169 / 1000000) : ℝ) = ((1000000 / 1078169) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_734_neg : (81393369 / 1000000000) ≤ -Real.log (921831 / 1000000) ∧
    -Real.log (921831 / 1000000) ≤ (8139337 / 100000000) := by
  have h := checkLog_sound (w := (78169 / 1921831)) (n := 12)
    (lo := (81393369 / 1000000000)) (hi := (8139337 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 921831) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 921831) = 1/(921831 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_734 : Bounds (-8139337 / 100000000) (-81393369 / 1000000000) (Real.log (921831 / 1000000)) := by
  have h := reflection_log_734_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_735_neg : (6129137 / 1000000000) ≤ -Real.log (993889607439 / 1000000000000) ∧
    -Real.log (993889607439 / 1000000000000) ≤ (3064569 / 500000000) := by
  have h := checkLog_sound (w := (6110392561 / 1993889607439)) (n := 12)
    (lo := (6129137 / 1000000000)) (hi := (3064569 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993889607439) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993889607439) = 1/(993889607439 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_735 : Bounds (-3064569 / 500000000) (-6129137 / 1000000000) (Real.log (993889607439 / 1000000000000)) := by
  have h := reflection_log_735_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_736_neg : (6096777 / 1000000000) ≤ -Real.log (993921770631 / 1000000000000) ∧
    -Real.log (993921770631 / 1000000000000) ≤ (3048389 / 500000000) := by
  have h := checkLog_sound (w := (6078229369 / 1993921770631)) (n := 12)
    (lo := (6096777 / 1000000000)) (hi := (3048389 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993921770631) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993921770631) = 1/(993921770631 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_736 : Bounds (-3048389 / 500000000) (-6096777 / 1000000000) (Real.log (993921770631 / 1000000000000)) := by
  have h := reflection_log_736_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_737_neg : (6249723 / 40000000) ≤ -Real.log (500000000000 / 584555175117) ∧
    -Real.log (500000000000 / 584555175117) ≤ (39060769 / 250000000) := by
  have h := checkLog_sound (w := (84555175117 / 1084555175117)) (n := 12)
    (lo := (6249723 / 40000000)) (hi := (39060769 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((584555175117 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(584555175117 / 500000000000) = 1/(500000000000 / 584555175117) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_737 : Bounds (6249723 / 40000000) (39060769 / 250000000) (Real.log (584555175117 / 500000000000)) := by
  have h := reflection_log_737_neg
  have he : Real.log (584555175117 / 500000000000) = -Real.log (500000000000 / 584555175117) := by
    rw [show ((584555175117 / 500000000000) : ℝ) = ((500000000000 / 584555175117) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_738_neg : (156657601 / 1000000000) ≤ -Real.log (125000000000 / 146199384703) ∧
    -Real.log (125000000000 / 146199384703) ≤ (78328801 / 500000000) := by
  have h := checkLog_sound (w := (21199384703 / 271199384703)) (n := 12)
    (lo := (156657601 / 1000000000)) (hi := (78328801 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((146199384703 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(146199384703 / 125000000000) = 1/(125000000000 / 146199384703) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_738 : Bounds (156657601 / 1000000000) (78328801 / 500000000) (Real.log (146199384703 / 125000000000)) := by
  have h := reflection_log_738_neg
  have he : Real.log (146199384703 / 125000000000) = -Real.log (125000000000 / 146199384703) := by
    rw [show ((146199384703 / 125000000000) : ℝ) = ((125000000000 / 146199384703) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_739_neg : (15666937 / 50000000) ≤ -Real.log (31250000000 / 42749526403) ∧
    -Real.log (31250000000 / 42749526403) ≤ (313338741 / 1000000000) := by
  have h := checkLog_sound (w := (11499526403 / 73999526403)) (n := 12)
    (lo := (15666937 / 50000000)) (hi := (313338741 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((42749526403 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(42749526403 / 31250000000) = 1/(31250000000 / 42749526403) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_739 : Bounds (15666937 / 50000000) (313338741 / 1000000000) (Real.log (42749526403 / 31250000000)) := by
  have h := reflection_log_739_neg
  have he : Real.log (42749526403 / 31250000000) = -Real.log (31250000000 / 42749526403) := by
    rw [show ((42749526403 / 31250000000) : ℝ) = ((31250000000 / 42749526403) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_740_neg : (313543693 / 1000000000) ≤ -Real.log (250000000000 / 342066311427) ∧
    -Real.log (250000000000 / 342066311427) ≤ (156771847 / 500000000) := by
  have h := checkLog_sound (w := (92066311427 / 592066311427)) (n := 12)
    (lo := (313543693 / 1000000000)) (hi := (156771847 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((342066311427 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(342066311427 / 250000000000) = 1/(250000000000 / 342066311427) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_740 : Bounds (313543693 / 1000000000) (156771847 / 500000000) (Real.log (342066311427 / 250000000000)) := by
  have h := reflection_log_740_neg
  have he : Real.log (342066311427 / 250000000000) = -Real.log (250000000000 / 342066311427) := by
    rw [show ((342066311427 / 250000000000) : ℝ) = ((250000000000 / 342066311427) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_741_neg : (144619689 / 1000000000) ≤ -Real.log (2500 / 2889) ∧
    -Real.log (2500 / 2889) ≤ (14461969 / 100000000) := by
  have h := checkLog_sound (w := (389 / 5389)) (n := 12)
    (lo := (144619689 / 1000000000)) (hi := (14461969 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2889 / 2500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2889 / 2500) = 1/(2500 / 2889) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_741 : Bounds (144619689 / 1000000000) (14461969 / 100000000) (Real.log (2889 / 2500)) := by
  have h := reflection_log_741_neg
  have he : Real.log (2889 / 2500) = -Real.log (2500 / 2889) := by
    rw [show ((2889 / 2500) : ℝ) = ((2500 / 2889) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_742_neg : (169128963 / 1000000000) ≤ -Real.log (2111 / 2500) ∧
    -Real.log (2111 / 2500) ≤ (42282241 / 250000000) := by
  have h := checkLog_sound (w := (389 / 4611)) (n := 12)
    (lo := (169128963 / 1000000000)) (hi := (42282241 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500 / 2111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500 / 2111) = 1/(2111 / 2500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_742 : Bounds (-42282241 / 250000000) (-169128963 / 1000000000) (Real.log (2111 / 2500)) := by
  have h := reflection_log_742_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_743_neg : (155587 / 1000000000) ≤ -Real.log (2500000 / 2500389) ∧
    -Real.log (2500000 / 2500389) ≤ (38897 / 250000000) := by
  have h := checkLog_sound (w := (389 / 5000389)) (n := 12)
    (lo := (155587 / 1000000000)) (hi := (38897 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500389 / 2500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500389 / 2500000) = 1/(2500000 / 2500389) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_743 : Bounds (155587 / 1000000000) (38897 / 250000000) (Real.log (2500389 / 2500000)) := by
  have h := reflection_log_743_neg
  have he : Real.log (2500389 / 2500000) = -Real.log (2500000 / 2500389) := by
    rw [show ((2500389 / 2500000) : ℝ) = ((2500000 / 2500389) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_744_neg : (38903 / 250000000) ≤ -Real.log (2499611 / 2500000) ∧
    -Real.log (2499611 / 2500000) ≤ (155613 / 1000000000) := by
  have h := checkLog_sound (w := (389 / 4999611)) (n := 12)
    (lo := (38903 / 250000000)) (hi := (155613 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000 / 2499611) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000 / 2499611) = 1/(2499611 / 2500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_744 : Bounds (-155613 / 1000000000) (-38903 / 250000000) (Real.log (2499611 / 2500000)) := by
  have h := reflection_log_744_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_745_neg : (75120459 / 1000000000) ≤ -Real.log (500000 / 539007) ∧
    -Real.log (500000 / 539007) ≤ (3756023 / 50000000) := by
  have h := checkLog_sound (w := (39007 / 1039007)) (n := 12)
    (lo := (75120459 / 1000000000)) (hi := (3756023 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((539007 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(539007 / 500000) = 1/(500000 / 539007) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_745 : Bounds (75120459 / 1000000000) (3756023 / 50000000) (Real.log (539007 / 500000)) := by
  have h := reflection_log_745_neg
  have he : Real.log (539007 / 500000) = -Real.log (500000 / 539007) := by
    rw [show ((539007 / 500000) : ℝ) = ((500000 / 539007) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_746_neg : (81225239 / 1000000000) ≤ -Real.log (460993 / 500000) ∧
    -Real.log (460993 / 500000) ≤ (2030631 / 25000000) := by
  have h := checkLog_sound (w := (39007 / 960993)) (n := 12)
    (lo := (81225239 / 1000000000)) (hi := (2030631 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 460993) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 460993) = 1/(460993 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_746 : Bounds (-2030631 / 25000000) (-81225239 / 1000000000) (Real.log (460993 / 500000)) := by
  have h := reflection_log_746_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_747_neg : (75311533 / 1000000000) ≤ -Real.log (50000 / 53911) ∧
    -Real.log (50000 / 53911) ≤ (37655767 / 500000000) := by
  have h := checkLog_sound (w := (3911 / 103911)) (n := 12)
    (lo := (75311533 / 1000000000)) (hi := (37655767 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((53911 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(53911 / 50000) = 1/(50000 / 53911) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_747 : Bounds (75311533 / 1000000000) (37655767 / 500000000) (Real.log (53911 / 50000)) := by
  have h := reflection_log_747_neg
  have he : Real.log (53911 / 50000) = -Real.log (50000 / 53911) := by
    rw [show ((53911 / 50000) : ℝ) = ((50000 / 53911) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_748_neg : (16289739 / 200000000) ≤ -Real.log (46089 / 50000) ∧
    -Real.log (46089 / 50000) ≤ (10181087 / 125000000) := by
  have h := checkLog_sound (w := (3911 / 96089)) (n := 12)
    (lo := (16289739 / 200000000)) (hi := (10181087 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 46089) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 46089) = 1/(46089 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_748 : Bounds (-10181087 / 125000000) (-16289739 / 200000000) (Real.log (46089 / 50000)) := by
  have h := reflection_log_748_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_749_neg : (3068581 / 500000000) ≤ -Real.log (2484704079 / 2500000000) ∧
    -Real.log (2484704079 / 2500000000) ≤ (6137163 / 1000000000) := by
  have h := checkLog_sound (w := (15295921 / 4984704079)) (n := 12)
    (lo := (3068581 / 500000000)) (hi := (6137163 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000000 / 2484704079) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000000 / 2484704079) = 1/(2484704079 / 2500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_749 : Bounds (-6137163 / 1000000000) (-3068581 / 500000000) (Real.log (2484704079 / 2500000000)) := by
  have h := reflection_log_749_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_750_neg : (305239 / 50000000) ≤ -Real.log (248478453951 / 250000000000) ∧
    -Real.log (248478453951 / 250000000000) ≤ (6104781 / 1000000000) := by
  have h := checkLog_sound (w := (1521546049 / 498478453951)) (n := 12)
    (lo := (305239 / 50000000)) (hi := (6104781 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248478453951) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248478453951) = 1/(248478453951 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_750 : Bounds (-6104781 / 1000000000) (-305239 / 50000000) (Real.log (248478453951 / 250000000000)) := by
  have h := reflection_log_750_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_751_neg : (156345699 / 1000000000) ≤ -Real.log (125000000000 / 146153791923) ∧
    -Real.log (125000000000 / 146153791923) ≤ (1563457 / 10000000) := by
  have h := checkLog_sound (w := (21153791923 / 271153791923)) (n := 12)
    (lo := (156345699 / 1000000000)) (hi := (1563457 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((146153791923 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(146153791923 / 125000000000) = 1/(125000000000 / 146153791923) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_751 : Bounds (156345699 / 1000000000) (1563457 / 10000000) (Real.log (146153791923 / 125000000000)) := by
  have h := reflection_log_751_neg
  have he : Real.log (146153791923 / 125000000000) = -Real.log (125000000000 / 146153791923) := by
    rw [show ((146153791923 / 125000000000) : ℝ) = ((125000000000 / 146153791923) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_752_neg : (39190057 / 250000000) ≤ -Real.log (500000000000 / 584857558203) ∧
    -Real.log (500000000000 / 584857558203) ≤ (156760229 / 1000000000) := by
  have h := checkLog_sound (w := (84857558203 / 1084857558203)) (n := 12)
    (lo := (39190057 / 250000000)) (hi := (156760229 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((584857558203 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(584857558203 / 500000000000) = 1/(500000000000 / 584857558203) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_752 : Bounds (39190057 / 250000000) (156760229 / 1000000000) (Real.log (584857558203 / 500000000000)) := by
  have h := reflection_log_752_neg
  have he : Real.log (584857558203 / 500000000000) = -Real.log (500000000000 / 584857558203) := by
    rw [show ((584857558203 / 500000000000) : ℝ) = ((500000000000 / 584857558203) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_753_neg : (313543693 / 1000000000) ≤ -Real.log (500000000000 / 684132622853) ∧
    -Real.log (500000000000 / 684132622853) ≤ (156771847 / 500000000) := by
  have h := checkLog_sound (w := (184132622853 / 1184132622853)) (n := 12)
    (lo := (313543693 / 1000000000)) (hi := (156771847 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((684132622853 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(684132622853 / 500000000000) = 1/(500000000000 / 684132622853) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_753 : Bounds (313543693 / 1000000000) (156771847 / 500000000) (Real.log (684132622853 / 500000000000)) := by
  have h := reflection_log_753_neg
  have he : Real.log (684132622853 / 500000000000) = -Real.log (500000000000 / 684132622853) := by
    rw [show ((684132622853 / 500000000000) : ℝ) = ((500000000000 / 684132622853) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_754_neg : (78437163 / 250000000) ≤ -Real.log (500000000000 / 684272856467) ∧
    -Real.log (500000000000 / 684272856467) ≤ (313748653 / 1000000000) := by
  have h := checkLog_sound (w := (184272856467 / 1184272856467)) (n := 12)
    (lo := (78437163 / 250000000)) (hi := (313748653 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((684272856467 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(684272856467 / 500000000000) = 1/(500000000000 / 684272856467) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_754 : Bounds (78437163 / 250000000) (313748653 / 1000000000) (Real.log (684272856467 / 500000000000)) := by
  have h := reflection_log_754_neg
  have he : Real.log (684272856467 / 500000000000) = -Real.log (500000000000 / 684272856467) := by
    rw [show ((684272856467 / 500000000000) : ℝ) = ((500000000000 / 684272856467) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_755_neg : (7235311 / 50000000) ≤ -Real.log (10000 / 11557) ∧
    -Real.log (10000 / 11557) ≤ (144706221 / 1000000000) := by
  have h := checkLog_sound (w := (1557 / 21557)) (n := 12)
    (lo := (7235311 / 50000000)) (hi := (144706221 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11557 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11557 / 10000) = 1/(10000 / 11557) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_755 : Bounds (7235311 / 50000000) (144706221 / 1000000000) (Real.log (11557 / 10000)) := by
  have h := reflection_log_755_neg
  have he : Real.log (11557 / 10000) = -Real.log (10000 / 11557) := by
    rw [show ((11557 / 10000) : ℝ) = ((10000 / 11557) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_756_neg : (169247397 / 1000000000) ≤ -Real.log (8443 / 10000) ∧
    -Real.log (8443 / 10000) ≤ (84623699 / 500000000) := by
  have h := checkLog_sound (w := (1557 / 18443)) (n := 12)
    (lo := (169247397 / 1000000000)) (hi := (84623699 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8443) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8443) = 1/(8443 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_756 : Bounds (-84623699 / 500000000) (-169247397 / 1000000000) (Real.log (8443 / 10000)) := by
  have h := reflection_log_756_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_757_neg : (155687 / 1000000000) ≤ -Real.log (10000000 / 10001557) ∧
    -Real.log (10000000 / 10001557) ≤ (19461 / 125000000) := by
  have h := checkLog_sound (w := (1557 / 20001557)) (n := 12)
    (lo := (155687 / 1000000000)) (hi := (19461 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001557 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001557 / 10000000) = 1/(10000000 / 10001557) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_757 : Bounds (155687 / 1000000000) (19461 / 125000000) (Real.log (10001557 / 10000000)) := by
  have h := reflection_log_757_neg
  have he : Real.log (10001557 / 10000000) = -Real.log (10000000 / 10001557) := by
    rw [show ((10001557 / 10000000) : ℝ) = ((10000000 / 10001557) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_758_neg : (2433 / 15625000) ≤ -Real.log (9998443 / 10000000) ∧
    -Real.log (9998443 / 10000000) ≤ (155713 / 1000000000) := by
  have h := checkLog_sound (w := (1557 / 19998443)) (n := 12)
    (lo := (2433 / 15625000)) (hi := (155713 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998443) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998443) = 1/(9998443 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_758 : Bounds (-155713 / 1000000000) (-2433 / 15625000) (Real.log (9998443 / 10000000)) := by
  have h := reflection_log_758_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_759_neg : (75166839 / 1000000000) ≤ -Real.log (62500 / 67379) ∧
    -Real.log (62500 / 67379) ≤ (1879171 / 25000000) := by
  have h := checkLog_sound (w := (4879 / 129879)) (n := 12)
    (lo := (75166839 / 1000000000)) (hi := (1879171 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((67379 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(67379 / 62500) = 1/(62500 / 67379) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_759 : Bounds (75166839 / 1000000000) (1879171 / 25000000) (Real.log (67379 / 62500)) := by
  have h := reflection_log_759_neg
  have he : Real.log (67379 / 62500) = -Real.log (62500 / 67379) := by
    rw [show ((67379 / 62500) : ℝ) = ((62500 / 67379) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_760_neg : (5079967 / 62500000) ≤ -Real.log (57621 / 62500) ∧
    -Real.log (57621 / 62500) ≤ (81279473 / 1000000000) := by
  have h := checkLog_sound (w := (4879 / 120121)) (n := 12)
    (lo := (5079967 / 62500000)) (hi := (81279473 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 57621) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 57621) = 1/(57621 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_760 : Bounds (-81279473 / 1000000000) (-5079967 / 62500000) (Real.log (57621 / 62500)) := by
  have h := reflection_log_760_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_761_neg : (4709927 / 62500000) ≤ -Real.log (1000000 / 1078271) ∧
    -Real.log (1000000 / 1078271) ≤ (75358833 / 1000000000) := by
  have h := checkLog_sound (w := (78271 / 2078271)) (n := 12)
    (lo := (4709927 / 62500000)) (hi := (75358833 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1078271 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1078271 / 1000000) = 1/(1000000 / 1078271) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_761 : Bounds (4709927 / 62500000) (75358833 / 1000000000) (Real.log (1078271 / 1000000)) := by
  have h := reflection_log_761_neg
  have he : Real.log (1078271 / 1000000) = -Real.log (1000000 / 1078271) := by
    rw [show ((1078271 / 1000000) : ℝ) = ((1000000 / 1078271) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_762_neg : (10188003 / 125000000) ≤ -Real.log (921729 / 1000000) ∧
    -Real.log (921729 / 1000000) ≤ (3260161 / 40000000) := by
  have h := checkLog_sound (w := (78271 / 1921729)) (n := 12)
    (lo := (10188003 / 125000000)) (hi := (3260161 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 921729) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 921729) = 1/(921729 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_762 : Bounds (-3260161 / 40000000) (-10188003 / 125000000) (Real.log (921729 / 1000000)) := by
  have h := reflection_log_762_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_763_neg : (768149 / 125000000) ≤ -Real.log (993873650559 / 1000000000000) ∧
    -Real.log (993873650559 / 1000000000000) ≤ (6145193 / 1000000000) := by
  have h := checkLog_sound (w := (6126349441 / 1993873650559)) (n := 12)
    (lo := (768149 / 125000000)) (hi := (6145193 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993873650559) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993873650559) = 1/(993873650559 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_763 : Bounds (-6145193 / 1000000000) (-768149 / 125000000) (Real.log (993873650559 / 1000000000000)) := by
  have h := reflection_log_763_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_764_neg : (764079 / 125000000) ≤ -Real.log (3882445359 / 3906250000) ∧
    -Real.log (3882445359 / 3906250000) ≤ (6112633 / 1000000000) := by
  have h := checkLog_sound (w := (23804641 / 7788695359)) (n := 12)
    (lo := (764079 / 125000000)) (hi := (6112633 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3906250000 / 3882445359) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3906250000 / 3882445359) = 1/(3882445359 / 3906250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_764 : Bounds (-6112633 / 1000000000) (-764079 / 125000000) (Real.log (3882445359 / 3906250000)) := by
  have h := reflection_log_764_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_765_neg : (19555789 / 125000000) ≤ -Real.log (100000000000 / 116934798077) ∧
    -Real.log (100000000000 / 116934798077) ≤ (156446313 / 1000000000) := by
  have h := checkLog_sound (w := (16934798077 / 216934798077)) (n := 12)
    (lo := (19555789 / 125000000)) (hi := (156446313 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((116934798077 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(116934798077 / 100000000000) = 1/(100000000000 / 116934798077) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_765 : Bounds (19555789 / 125000000) (156446313 / 1000000000) (Real.log (116934798077 / 100000000000)) := by
  have h := reflection_log_765_neg
  have he : Real.log (116934798077 / 100000000000) = -Real.log (100000000000 / 116934798077) := by
    rw [show ((116934798077 / 100000000000) : ℝ) = ((100000000000 / 116934798077) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_766_neg : (156862857 / 1000000000) ≤ -Real.log (125000000000 / 146229396059) ∧
    -Real.log (125000000000 / 146229396059) ≤ (78431429 / 500000000) := by
  have h := checkLog_sound (w := (21229396059 / 271229396059)) (n := 12)
    (lo := (156862857 / 1000000000)) (hi := (78431429 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((146229396059 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(146229396059 / 125000000000) = 1/(125000000000 / 146229396059) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_766 : Bounds (156862857 / 1000000000) (78431429 / 500000000) (Real.log (146229396059 / 125000000000)) := by
  have h := reflection_log_766_neg
  have he : Real.log (146229396059 / 125000000000) = -Real.log (125000000000 / 146229396059) := by
    rw [show ((146229396059 / 125000000000) : ℝ) = ((125000000000 / 146229396059) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_767_neg : (78437163 / 250000000) ≤ -Real.log (250000000000 / 342136428233) ∧
    -Real.log (250000000000 / 342136428233) ≤ (313748653 / 1000000000) := by
  have h := checkLog_sound (w := (92136428233 / 592136428233)) (n := 12)
    (lo := (78437163 / 250000000)) (hi := (313748653 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((342136428233 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(342136428233 / 250000000000) = 1/(250000000000 / 342136428233) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_767 : Bounds (78437163 / 250000000) (313748653 / 1000000000) (Real.log (342136428233 / 250000000000)) := by
  have h := reflection_log_767_neg
  have he : Real.log (342136428233 / 250000000000) = -Real.log (250000000000 / 342136428233) := by
    rw [show ((342136428233 / 250000000000) : ℝ) = ((250000000000 / 342136428233) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily
