import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0144
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

theorem reflection_log_1_neg : (73938717 / 250000000) ≤ -Real.log (2560 / 3441) ∧
    -Real.log (2560 / 3441) ≤ (295754869 / 1000000000) := by
  have h := checkLog_sound (w := (881 / 6001)) (n := 12)
    (lo := (73938717 / 250000000)) (hi := (295754869 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3441 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3441 / 2560) = 1/(2560 / 3441) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (73938717 / 250000000) (295754869 / 1000000000) (Real.log (3441 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3441 / 2560) = -Real.log (2560 / 3441) := by
    rw [show ((3441 / 2560) : ℝ) = ((2560 / 3441) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (5272611 / 12500000) ≤ -Real.log (1679 / 2560) ∧
    -Real.log (1679 / 2560) ≤ (421808881 / 1000000000) := by
  have h := checkLog_sound (w := (881 / 4239)) (n := 12)
    (lo := (5272611 / 12500000)) (hi := (421808881 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1679) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1679) = 1/(1679 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-421808881 / 1000000000) (-5272611 / 12500000) (Real.log (1679 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (36860331 / 125000000) ≤ -Real.log (1280 / 1719) ∧
    -Real.log (1280 / 1719) ≤ (294882649 / 1000000000) := by
  have h := checkLog_sound (w := (439 / 2999)) (n := 12)
    (lo := (36860331 / 125000000)) (hi := (294882649 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1719 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1719 / 1280) = 1/(1280 / 1719) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (36860331 / 125000000) (294882649 / 1000000000) (Real.log (1719 / 1280)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1719 / 1280) = -Real.log (1280 / 1719) := by
    rw [show ((1719 / 1280) : ℝ) = ((1280 / 1719) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (26251481 / 62500000) ≤ -Real.log (841 / 1280) ∧
    -Real.log (841 / 1280) ≤ (420023697 / 1000000000) := by
  have h := checkLog_sound (w := (439 / 2121)) (n := 12)
    (lo := (26251481 / 62500000)) (hi := (420023697 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 841) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 841) = 1/(841 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-420023697 / 1000000000) (-26251481 / 62500000) (Real.log (841 / 1280)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (523710999 / 1000000000) ≤ -Real.log (1280 / 2161) ∧
    -Real.log (1280 / 2161) ≤ (523711 / 1000000) := by
  have h := checkLog_sound (w := (881 / 3441)) (n := 12)
    (lo := (523710999 / 1000000000)) (hi := (523711 / 1000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2161 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2161 / 1280) = 1/(1280 / 2161) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (523710999 / 1000000000) (523711 / 1000000) (Real.log (2161 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2161 / 1280) = -Real.log (1280 / 2161) := by
    rw [show ((2161 / 1280) : ℝ) = ((1280 / 2161) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1165653939 / 1000000000) ≤ -Real.log (399 / 1280) ∧
    -Real.log (399 / 1280) ≤ (1165653941 / 1000000000) := by
  have h := checkLog_sound (w := (241 / 1039)) (n := 12)
    (lo := (472506759 / 1000000000)) (hi := (11812669 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 399) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 399) = 1/(399 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1165653941 / 1000000000) (-1165653939 / 1000000000) (Real.log (399 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (130580447 / 250000000) ≤ -Real.log (640 / 1079) ∧
    -Real.log (640 / 1079) ≤ (522321789 / 1000000000) := by
  have h := checkLog_sound (w := (439 / 1719)) (n := 12)
    (lo := (130580447 / 250000000)) (hi := (522321789 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1079 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1079 / 640) = 1/(640 / 1079) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (130580447 / 250000000) (522321789 / 1000000000) (Real.log (1079 / 640)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1079 / 640) = -Real.log (640 / 1079) := by
    rw [show ((1079 / 640) : ℝ) = ((640 / 1079) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (1158163267 / 1000000000) ≤ -Real.log (201 / 640) ∧
    -Real.log (201 / 640) ≤ (1158163269 / 1000000000) := by
  have h := checkLog_sound (w := (119 / 521)) (n := 12)
    (lo := (465016087 / 1000000000)) (hi := (58127011 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 201) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(320 / 201) = 1/(201 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1158163269 / 1000000000) (-1158163267 / 1000000000) (Real.log (201 / 640)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (100879971 / 250000000) ≤ -Real.log (200000 / 299417) ∧
    -Real.log (200000 / 299417) ≤ (80703977 / 200000000) := by
  have h := checkLog_sound (w := (99417 / 499417)) (n := 12)
    (lo := (100879971 / 250000000)) (hi := (80703977 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((299417 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(299417 / 200000) = 1/(200000 / 299417) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (100879971 / 250000000) (80703977 / 200000000) (Real.log (299417 / 200000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (299417 / 200000) = -Real.log (200000 / 299417) := by
    rw [show ((299417 / 200000) : ℝ) = ((200000 / 299417) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (687334109 / 1000000000) ≤ -Real.log (100583 / 200000) ∧
    -Real.log (100583 / 200000) ≤ (68733411 / 100000000) := by
  have h := checkLog_sound (w := (99417 / 300583)) (n := 12)
    (lo := (687334109 / 1000000000)) (hi := (68733411 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 100583) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 100583) = 1/(100583 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-68733411 / 100000000) (-687334109 / 1000000000) (Real.log (100583 / 200000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (50590771 / 125000000) ≤ -Real.log (250000 / 374723) ∧
    -Real.log (250000 / 374723) ≤ (404726169 / 1000000000) := by
  have h := checkLog_sound (w := (124723 / 624723)) (n := 12)
    (lo := (50590771 / 125000000)) (hi := (404726169 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((374723 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(374723 / 250000) = 1/(250000 / 374723) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (50590771 / 125000000) (404726169 / 1000000000) (Real.log (374723 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (374723 / 250000) = -Real.log (250000 / 374723) := by
    rw [show ((374723 / 250000) : ℝ) = ((250000 / 374723) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (5397919 / 7812500) ≤ -Real.log (125277 / 250000) ∧
    -Real.log (125277 / 250000) ≤ (690933633 / 1000000000) := by
  have h := checkLog_sound (w := (124723 / 375277)) (n := 12)
    (lo := (5397919 / 7812500)) (hi := (690933633 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 125277) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 125277) = 1/(125277 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-690933633 / 1000000000) (-5397919 / 7812500) (Real.log (125277 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (80013113 / 250000000) ≤ -Real.log (2500 / 3443) ∧
    -Real.log (2500 / 3443) ≤ (320052453 / 1000000000) := by
  have h := checkLog_sound (w := (943 / 5943)) (n := 12)
    (lo := (80013113 / 250000000)) (hi := (320052453 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3443 / 2500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3443 / 2500) = 1/(2500 / 3443) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (80013113 / 250000000) (320052453 / 1000000000) (Real.log (3443 / 2500)) := by
  have h := reflection_log_13_neg
  have he : Real.log (3443 / 2500) = -Real.log (2500 / 3443) := by
    rw [show ((3443 / 2500) : ℝ) = ((2500 / 3443) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (473529839 / 1000000000) ≤ -Real.log (1557 / 2500) ∧
    -Real.log (1557 / 2500) ≤ (5919123 / 12500000) := by
  have h := checkLog_sound (w := (943 / 4057)) (n := 12)
    (lo := (473529839 / 1000000000)) (hi := (5919123 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500 / 1557) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500 / 1557) = 1/(1557 / 2500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-5919123 / 12500000) (-473529839 / 1000000000) (Real.log (1557 / 2500)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (160596261 / 500000000) ≤ -Real.log (1000000 / 1378771) ∧
    -Real.log (1000000 / 1378771) ≤ (321192523 / 1000000000) := by
  have h := checkLog_sound (w := (378771 / 2378771)) (n := 12)
    (lo := (160596261 / 500000000)) (hi := (321192523 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1378771 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1378771 / 1000000) = 1/(1000000 / 1378771) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (160596261 / 500000000) (321192523 / 1000000000) (Real.log (1378771 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1378771 / 1000000) = -Real.log (1000000 / 1378771) := by
    rw [show ((1378771 / 1000000) : ℝ) = ((1000000 / 1378771) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (29753469 / 62500000) ≤ -Real.log (621229 / 1000000) ∧
    -Real.log (621229 / 1000000) ≤ (95211101 / 200000000) := by
  have h := checkLog_sound (w := (378771 / 1621229)) (n := 12)
    (lo := (29753469 / 62500000)) (hi := (95211101 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 621229) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 621229) = 1/(621229 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-95211101 / 200000000) (-29753469 / 62500000) (Real.log (621229 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (136356749 / 125000000) ≤ -Real.log (250000000000 / 744203791893) ∧
    -Real.log (250000000000 / 744203791893) ≤ (545426997 / 500000000) := by
  have h := checkLog_sound (w := (244203791893 / 1244203791893)) (n := 12)
    (lo := (99426703 / 250000000)) (hi := (397706813 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((744203791893 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(744203791893 / 500000000000) = 1/(250000000000 / 744203791893) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (136356749 / 125000000) (545426997 / 500000000) (Real.log (744203791893 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (744203791893 / 250000000000) = -Real.log (250000000000 / 744203791893) := by
    rw [show ((744203791893 / 250000000000) : ℝ) = ((250000000000 / 744203791893) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (5478299 / 5000000) ≤ -Real.log (500000000000 / 1495577799597) ∧
    -Real.log (500000000000 / 1495577799597) ≤ (547829901 / 500000000) := by
  have h := checkLog_sound (w := (495577799597 / 2495577799597)) (n := 12)
    (lo := (20125631 / 50000000)) (hi := (402512621 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1495577799597 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1495577799597 / 1000000000000) = 1/(500000000000 / 1495577799597) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (5478299 / 5000000) (547829901 / 500000000) (Real.log (1495577799597 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1495577799597 / 500000000000) = -Real.log (500000000000 / 1495577799597) := by
    rw [show ((1495577799597 / 500000000000) : ℝ) = ((500000000000 / 1495577799597) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (79358229 / 100000000) ≤ -Real.log (500000000000 / 1105651894669) ∧
    -Real.log (500000000000 / 1105651894669) ≤ (198395573 / 250000000) := by
  have h := checkLog_sound (w := (105651894669 / 2105651894669)) (n := 12)
    (lo := (10043511 / 100000000)) (hi := (100435111 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1105651894669 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1105651894669 / 1000000000000) = 1/(500000000000 / 1105651894669) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (79358229 / 100000000) (198395573 / 250000000) (Real.log (1105651894669 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (1105651894669 / 500000000000) = -Real.log (500000000000 / 1105651894669) := by
    rw [show ((1105651894669 / 500000000000) : ℝ) = ((500000000000 / 1105651894669) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (797248027 / 1000000000) ≤ -Real.log (500000000000 / 1109712360499) ∧
    -Real.log (500000000000 / 1109712360499) ≤ (797248029 / 1000000000) := by
  have h := checkLog_sound (w := (109712360499 / 2109712360499)) (n := 12)
    (lo := (104100847 / 1000000000)) (hi := (6506303 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1109712360499 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1109712360499 / 1000000000000) = 1/(500000000000 / 1109712360499) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (797248027 / 1000000000) (797248029 / 1000000000) (Real.log (1109712360499 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1109712360499 / 500000000000) = -Real.log (500000000000 / 1109712360499) := by
    rw [show ((1109712360499 / 500000000000) : ℝ) = ((500000000000 / 1109712360499) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0144
