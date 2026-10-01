import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0027
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

theorem reflection_log_1_neg : (15715453 / 40000000) ≤ -Real.log (160 / 237) ∧
    -Real.log (160 / 237) ≤ (196443163 / 500000000) := by
  have h := checkLog_sound (w := (77 / 397)) (n := 12)
    (lo := (15715453 / 40000000)) (hi := (196443163 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((237 / 160) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(237 / 160) = 1/(160 / 237) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (15715453 / 40000000) (196443163 / 500000000) (Real.log (237 / 160)) := by
  have h := reflection_log_1_neg
  have he : Real.log (237 / 160) = -Real.log (160 / 237) := by
    rw [show ((237 / 160) : ℝ) = ((160 / 237) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (656333207 / 1000000000) ≤ -Real.log (83 / 160) ∧
    -Real.log (83 / 160) ≤ (82041651 / 125000000) := by
  have h := checkLog_sound (w := (77 / 243)) (n := 12)
    (lo := (656333207 / 1000000000)) (hi := (82041651 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 83) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(160 / 83) = 1/(83 / 160) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-82041651 / 125000000) (-656333207 / 1000000000) (Real.log (83 / 160)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (392094873 / 1000000000) ≤ -Real.log (2560 / 3789) ∧
    -Real.log (2560 / 3789) ≤ (196047437 / 500000000) := by
  have h := checkLog_sound (w := (1229 / 6349)) (n := 12)
    (lo := (392094873 / 1000000000)) (hi := (196047437 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3789 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3789 / 2560) = 1/(2560 / 3789) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (392094873 / 1000000000) (196047437 / 500000000) (Real.log (3789 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3789 / 2560) = -Real.log (2560 / 3789) := by
    rw [show ((3789 / 2560) : ℝ) = ((2560 / 3789) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (654076719 / 1000000000) ≤ -Real.log (1331 / 2560) ∧
    -Real.log (1331 / 2560) ≤ (8175959 / 12500000) := by
  have h := checkLog_sound (w := (1229 / 3891)) (n := 12)
    (lo := (654076719 / 1000000000)) (hi := (8175959 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1331) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1331) = 1/(1331 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-8175959 / 12500000) (-654076719 / 1000000000) (Real.log (1331 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (67421917 / 100000000) ≤ -Real.log (80 / 157) ∧
    -Real.log (80 / 157) ≤ (674219171 / 1000000000) := by
  have h := checkLog_sound (w := (77 / 237)) (n := 12)
    (lo := (67421917 / 100000000)) (hi := (674219171 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((157 / 80) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(157 / 80) = 1/(80 / 157) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (67421917 / 100000000) (674219171 / 1000000000) (Real.log (157 / 80)) := by
  have h := reflection_log_5_neg
  have he : Real.log (157 / 80) = -Real.log (80 / 157) := by
    rw [show ((157 / 80) : ℝ) = ((80 / 157) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (3283414343 / 1000000000) ≤ -Real.log (3 / 80) ∧
    -Real.log (3 / 80) ≤ (820853587 / 250000000) := by
  have h := checkLog_sound (w := (1 / 4)) (n := 12)
    (lo := (510825623 / 1000000000)) (hi := (63853203 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5 / 3) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(5 / 3) = 1/(3 / 80) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-820853587 / 250000000) (-3283414343 / 1000000000) (Real.log (3 / 80)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (673024189 / 1000000000) ≤ -Real.log (1280 / 2509) ∧
    -Real.log (1280 / 2509) ≤ (67302419 / 100000000) := by
  have h := checkLog_sound (w := (1229 / 3789)) (n := 12)
    (lo := (673024189 / 1000000000)) (hi := (67302419 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2509 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2509 / 1280) = 1/(1280 / 2509) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (673024189 / 1000000000) (67302419 / 100000000) (Real.log (2509 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2509 / 1280) = -Real.log (1280 / 2509) := by
    rw [show ((2509 / 1280) : ℝ) = ((1280 / 2509) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (3222789721 / 1000000000) ≤ -Real.log (51 / 1280) ∧
    -Real.log (51 / 1280) ≤ (1611394863 / 500000000) := by
  have h := checkLog_sound (w := (29 / 131)) (n := 12)
    (lo := (450201001 / 1000000000)) (hi := (225100501 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80 / 51) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(80 / 51) = 1/(51 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1611394863 / 500000000) (-3222789721 / 1000000000) (Real.log (51 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (137083381 / 250000000) ≤ -Real.log (1000000 / 1730367) ∧
    -Real.log (1000000 / 1730367) ≤ (21933341 / 40000000) := by
  have h := checkLog_sound (w := (730367 / 2730367)) (n := 12)
    (lo := (137083381 / 250000000)) (hi := (21933341 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1730367 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1730367 / 1000000) = 1/(1000000 / 1730367) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (137083381 / 250000000) (21933341 / 40000000) (Real.log (1730367 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1730367 / 1000000) = -Real.log (1000000 / 1730367) := by
    rw [show ((1730367 / 1000000) : ℝ) = ((1000000 / 1730367) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (1310693503 / 1000000000) ≤ -Real.log (269633 / 1000000) ∧
    -Real.log (269633 / 1000000) ≤ (262138701 / 200000000) := by
  have h := checkLog_sound (w := (230367 / 769633)) (n := 12)
    (lo := (617546323 / 1000000000)) (hi := (154386581 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 269633) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 269633) = 1/(269633 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-262138701 / 200000000) (-1310693503 / 1000000000) (Real.log (269633 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (137439843 / 250000000) ≤ -Real.log (250000 / 433209) ∧
    -Real.log (250000 / 433209) ≤ (549759373 / 1000000000) := by
  have h := checkLog_sound (w := (183209 / 683209)) (n := 12)
    (lo := (137439843 / 250000000)) (hi := (549759373 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((433209 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(433209 / 250000) = 1/(250000 / 433209) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (137439843 / 250000000) (549759373 / 1000000000) (Real.log (433209 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (433209 / 250000) = -Real.log (250000 / 433209) := by
    rw [show ((433209 / 250000) : ℝ) = ((250000 / 433209) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (41246643 / 31250000) ≤ -Real.log (66791 / 250000) ∧
    -Real.log (66791 / 250000) ≤ (659946289 / 500000000) := by
  have h := checkLog_sound (w := (58209 / 191791)) (n := 12)
    (lo := (156686349 / 250000000)) (hi := (626745397 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 66791) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(125000 / 66791) = 1/(66791 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-659946289 / 500000000) (-41246643 / 31250000) (Real.log (66791 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (94508331 / 200000000) ≤ -Real.log (500000 / 802033) ∧
    -Real.log (500000 / 802033) ≤ (59067707 / 125000000) := by
  have h := checkLog_sound (w := (302033 / 1302033)) (n := 12)
    (lo := (94508331 / 200000000)) (hi := (59067707 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((802033 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(802033 / 500000) = 1/(500000 / 802033) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (94508331 / 200000000) (59067707 / 125000000) (Real.log (802033 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (802033 / 500000) = -Real.log (500000 / 802033) := by
    rw [show ((802033 / 500000) : ℝ) = ((500000 / 802033) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (926507747 / 1000000000) ≤ -Real.log (197967 / 500000) ∧
    -Real.log (197967 / 500000) ≤ (926507749 / 1000000000) := by
  have h := checkLog_sound (w := (52033 / 447967)) (n := 12)
    (lo := (233360567 / 1000000000)) (hi := (29170071 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 197967) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 197967) = 1/(197967 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-926507749 / 1000000000) (-926507747 / 1000000000) (Real.log (197967 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (94844817 / 200000000) ≤ -Real.log (1000000 / 1606767) ∧
    -Real.log (1000000 / 1606767) ≤ (237112043 / 500000000) := by
  have h := checkLog_sound (w := (606767 / 2606767)) (n := 12)
    (lo := (94844817 / 200000000)) (hi := (237112043 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1606767 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1606767 / 1000000) = 1/(1000000 / 1606767) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (94844817 / 200000000) (237112043 / 500000000) (Real.log (1606767 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1606767 / 1000000) = -Real.log (1000000 / 1606767) := by
    rw [show ((1606767 / 1000000) : ℝ) = ((1000000 / 1606767) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (466676483 / 500000000) ≤ -Real.log (393233 / 1000000) ∧
    -Real.log (393233 / 1000000) ≤ (116669121 / 125000000) := by
  have h := checkLog_sound (w := (106767 / 893233)) (n := 12)
    (lo := (120102893 / 500000000)) (hi := (240205787 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 393233) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 393233) = 1/(393233 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-116669121 / 125000000) (-466676483 / 500000000) (Real.log (393233 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1859027027 / 1000000000) ≤ -Real.log (12500000000 / 80218621237) ∧
    -Real.log (12500000000 / 80218621237) ≤ (185902703 / 100000000) := by
  have h := checkLog_sound (w := (30218621237 / 130218621237)) (n := 12)
    (lo := (472732667 / 1000000000)) (hi := (118183167 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80218621237 / 50000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(80218621237 / 50000000000) = 1/(12500000000 / 80218621237) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1859027027 / 1000000000) (185902703 / 100000000) (Real.log (80218621237 / 12500000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (80218621237 / 12500000000) = -Real.log (12500000000 / 80218621237) := by
    rw [show ((80218621237 / 12500000000) : ℝ) = ((12500000000 / 80218621237) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (467412987 / 250000000) ≤ -Real.log (62500000000 / 405377408633) ∧
    -Real.log (62500000000 / 405377408633) ≤ (1869651951 / 1000000000) := by
  have h := checkLog_sound (w := (155377408633 / 655377408633)) (n := 12)
    (lo := (120839397 / 250000000)) (hi := (483357589 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((405377408633 / 250000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(405377408633 / 250000000000) = 1/(62500000000 / 405377408633) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (467412987 / 250000000) (1869651951 / 1000000000) (Real.log (405377408633 / 62500000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (405377408633 / 62500000000) = -Real.log (62500000000 / 405377408633) := by
    rw [show ((405377408633 / 62500000000) : ℝ) = ((62500000000 / 405377408633) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (699524701 / 500000000) ≤ -Real.log (50000000000 / 202567347083) ∧
    -Real.log (50000000000 / 202567347083) ≤ (279809881 / 200000000) := by
  have h := checkLog_sound (w := (2567347083 / 402567347083)) (n := 12)
    (lo := (6377521 / 500000000)) (hi := (12755043 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((202567347083 / 200000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(202567347083 / 200000000000) = 1/(50000000000 / 202567347083) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (699524701 / 500000000) (279809881 / 200000000) (Real.log (202567347083 / 50000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (202567347083 / 50000000000) = -Real.log (50000000000 / 202567347083) := by
    rw [show ((202567347083 / 50000000000) : ℝ) = ((50000000000 / 202567347083) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (1407577051 / 1000000000) ≤ -Real.log (250000000000 / 1021510783683) ∧
    -Real.log (250000000000 / 1021510783683) ≤ (703788527 / 500000000) := by
  have h := checkLog_sound (w := (21510783683 / 2021510783683)) (n := 12)
    (lo := (21282691 / 1000000000)) (hi := (5320673 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1021510783683 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1021510783683 / 1000000000000) = 1/(250000000000 / 1021510783683) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (1407577051 / 1000000000) (703788527 / 500000000) (Real.log (1021510783683 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1021510783683 / 250000000000) = -Real.log (250000000000 / 1021510783683) := by
    rw [show ((1021510783683 / 250000000000) : ℝ) = ((250000000000 / 1021510783683) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0027
