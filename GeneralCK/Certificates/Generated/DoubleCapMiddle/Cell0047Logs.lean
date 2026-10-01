import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0047
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

theorem reflection_log_1_neg : (5889641 / 15625000) ≤ -Real.log (640 / 933) ∧
    -Real.log (640 / 933) ≤ (15077481 / 40000000) := by
  have h := checkLog_sound (w := (293 / 1573)) (n := 12)
    (lo := (5889641 / 15625000)) (hi := (15077481 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((933 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(933 / 640) = 1/(640 / 933) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (5889641 / 15625000) (15077481 / 40000000) (Real.log (933 / 640)) := by
  have h := reflection_log_1_neg
  have he : Real.log (933 / 640) = -Real.log (640 / 933) := by
    rw [show ((933 / 640) : ℝ) = ((640 / 933) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (153035849 / 250000000) ≤ -Real.log (347 / 640) ∧
    -Real.log (347 / 640) ≤ (612143397 / 1000000000) := by
  have h := checkLog_sound (w := (293 / 987)) (n := 12)
    (lo := (153035849 / 250000000)) (hi := (612143397 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 347) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 347) = 1/(347 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-612143397 / 1000000000) (-153035849 / 250000000) (Real.log (347 / 640)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (188066421 / 500000000) ≤ -Real.log (2560 / 3729) ∧
    -Real.log (2560 / 3729) ≤ (376132843 / 1000000000) := by
  have h := checkLog_sound (w := (1169 / 6289)) (n := 12)
    (lo := (188066421 / 500000000)) (hi := (376132843 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3729 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3729 / 2560) = 1/(2560 / 3729) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (188066421 / 500000000) (376132843 / 1000000000) (Real.log (3729 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3729 / 2560) = -Real.log (2560 / 3729) := by
    rw [show ((3729 / 2560) : ℝ) = ((2560 / 3729) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (121996869 / 200000000) ≤ -Real.log (1391 / 2560) ∧
    -Real.log (1391 / 2560) ≤ (304992173 / 500000000) := by
  have h := checkLog_sound (w := (1169 / 3951)) (n := 12)
    (lo := (121996869 / 200000000)) (hi := (304992173 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1391) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1391) = 1/(1391 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-304992173 / 500000000) (-121996869 / 200000000) (Real.log (1391 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (32502197 / 50000000) ≤ -Real.log (320 / 613) ∧
    -Real.log (320 / 613) ≤ (650043941 / 1000000000) := by
  have h := checkLog_sound (w := (293 / 933)) (n := 12)
    (lo := (32502197 / 50000000)) (hi := (650043941 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((613 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(613 / 320) = 1/(320 / 613) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (32502197 / 50000000) (650043941 / 1000000000) (Real.log (613 / 320)) := by
  have h := reflection_log_5_neg
  have he : Real.log (613 / 320) = -Real.log (320 / 613) := by
    rw [show ((613 / 320) : ℝ) = ((320 / 613) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (77265129 / 31250000) ≤ -Real.log (27 / 320) ∧
    -Real.log (27 / 320) ≤ (618121033 / 250000000) := by
  have h := checkLog_sound (w := (13 / 67)) (n := 12)
    (lo := (98260647 / 250000000)) (hi := (393042589 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40 / 27) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(40 / 27) = 1/(27 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-618121033 / 250000000) (-77265129 / 31250000) (Real.log (27 / 320)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (6488197 / 10000000) ≤ -Real.log (1280 / 2449) ∧
    -Real.log (1280 / 2449) ≤ (648819701 / 1000000000) := by
  have h := checkLog_sound (w := (1169 / 3729)) (n := 12)
    (lo := (6488197 / 10000000)) (hi := (648819701 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2449 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2449 / 1280) = 1/(1280 / 2449) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (6488197 / 10000000) (648819701 / 1000000000) (Real.log (2449 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2449 / 1280) = -Real.log (1280 / 2449) := by
    rw [show ((2449 / 1280) : ℝ) = ((1280 / 2449) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (2445085153 / 1000000000) ≤ -Real.log (111 / 1280) ∧
    -Real.log (111 / 1280) ≤ (2445085157 / 1000000000) := by
  have h := checkLog_sound (w := (49 / 271)) (n := 12)
    (lo := (365643613 / 1000000000)) (hi := (182821807 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 111) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(160 / 111) = 1/(111 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-2445085157 / 1000000000) (-2445085153 / 1000000000) (Real.log (111 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (521544767 / 1000000000) ≤ -Real.log (250000 / 421157) ∧
    -Real.log (250000 / 421157) ≤ (8149137 / 15625000) := by
  have h := checkLog_sound (w := (171157 / 671157)) (n := 12)
    (lo := (521544767 / 1000000000)) (hi := (8149137 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((421157 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(421157 / 250000) = 1/(250000 / 421157) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (521544767 / 1000000000) (8149137 / 15625000) (Real.log (421157 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (421157 / 250000) = -Real.log (250000 / 421157) := by
    rw [show ((421157 / 250000) : ℝ) = ((250000 / 421157) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (1154002383 / 1000000000) ≤ -Real.log (78843 / 250000) ∧
    -Real.log (78843 / 250000) ≤ (230800477 / 200000000) := by
  have h := checkLog_sound (w := (46157 / 203843)) (n := 12)
    (lo := (460855203 / 1000000000)) (hi := (115213801 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 78843) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(125000 / 78843) = 1/(78843 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-230800477 / 200000000) (-1154002383 / 1000000000) (Real.log (78843 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (522832057 / 1000000000) ≤ -Real.log (500000 / 843399) ∧
    -Real.log (500000 / 843399) ≤ (261416029 / 500000000) := by
  have h := checkLog_sound (w := (343399 / 1343399)) (n := 12)
    (lo := (522832057 / 1000000000)) (hi := (261416029 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((843399 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(843399 / 500000) = 1/(500000 / 843399) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (522832057 / 1000000000) (261416029 / 500000000) (Real.log (843399 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (843399 / 500000) = -Real.log (500000 / 843399) := by
    rw [show ((843399 / 500000) : ℝ) = ((500000 / 843399) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (72556683 / 62500000) ≤ -Real.log (156601 / 500000) ∧
    -Real.log (156601 / 500000) ≤ (116090693 / 100000000) := by
  have h := checkLog_sound (w := (93399 / 406601)) (n := 12)
    (lo := (116939937 / 250000000)) (hi := (467759749 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 156601) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 156601) = 1/(156601 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-116090693 / 100000000) (-72556683 / 62500000) (Real.log (156601 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (441625373 / 1000000000) ≤ -Real.log (1000000 / 1555233) ∧
    -Real.log (1000000 / 1555233) ≤ (220812687 / 500000000) := by
  have h := checkLog_sound (w := (555233 / 2555233)) (n := 12)
    (lo := (441625373 / 1000000000)) (hi := (220812687 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1555233 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1555233 / 1000000) = 1/(1000000 / 1555233) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (441625373 / 1000000000) (220812687 / 500000000) (Real.log (1555233 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1555233 / 1000000) = -Real.log (1000000 / 1555233) := by
    rw [show ((1555233 / 1000000) : ℝ) = ((1000000 / 1555233) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (101275591 / 125000000) ≤ -Real.log (444767 / 1000000) ∧
    -Real.log (444767 / 1000000) ≤ (81020473 / 100000000) := by
  have h := checkLog_sound (w := (55233 / 944767)) (n := 12)
    (lo := (29264387 / 250000000)) (hi := (117057549 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 444767) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 444767) = 1/(444767 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-81020473 / 100000000) (-101275591 / 125000000) (Real.log (444767 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (88616009 / 200000000) ≤ -Real.log (1000000 / 1557497) ∧
    -Real.log (1000000 / 1557497) ≤ (221540023 / 500000000) := by
  have h := checkLog_sound (w := (557497 / 2557497)) (n := 12)
    (lo := (88616009 / 200000000)) (hi := (221540023 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1557497 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1557497 / 1000000) = 1/(1000000 / 1557497) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (88616009 / 200000000) (221540023 / 500000000) (Real.log (1557497 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1557497 / 1000000) = -Real.log (1000000 / 1557497) := by
    rw [show ((1557497 / 1000000) : ℝ) = ((1000000 / 1557497) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (407654017 / 500000000) ≤ -Real.log (442503 / 1000000) ∧
    -Real.log (442503 / 1000000) ≤ (203827009 / 250000000) := by
  have h := checkLog_sound (w := (57497 / 942503)) (n := 12)
    (lo := (61080427 / 500000000)) (hi := (24432171 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 442503) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 442503) = 1/(442503 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-203827009 / 250000000) (-407654017 / 500000000) (Real.log (442503 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1675547151 / 1000000000) ≤ -Real.log (250000000000 / 1335429270829) ∧
    -Real.log (250000000000 / 1335429270829) ≤ (837773577 / 500000000) := by
  have h := checkLog_sound (w := (335429270829 / 2335429270829)) (n := 12)
    (lo := (289252791 / 1000000000)) (hi := (36156599 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1335429270829 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1335429270829 / 1000000000000) = 1/(250000000000 / 1335429270829) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1675547151 / 1000000000) (837773577 / 500000000) (Real.log (1335429270829 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1335429270829 / 250000000000) = -Real.log (250000000000 / 1335429270829) := by
    rw [show ((1335429270829 / 250000000000) : ℝ) = ((250000000000 / 1335429270829) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (336747797 / 200000000) ≤ -Real.log (62500000000 / 336603454001) ∧
    -Real.log (62500000000 / 336603454001) ≤ (420934747 / 250000000) := by
  have h := checkLog_sound (w := (86603454001 / 586603454001)) (n := 12)
    (lo := (2379557 / 8000000)) (hi := (148722313 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((336603454001 / 250000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(336603454001 / 250000000000) = 1/(62500000000 / 336603454001) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (336747797 / 200000000) (420934747 / 250000000) (Real.log (336603454001 / 62500000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (336603454001 / 62500000000) = -Real.log (62500000000 / 336603454001) := by
    rw [show ((336603454001 / 62500000000) : ℝ) = ((62500000000 / 336603454001) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (625915051 / 500000000) ≤ -Real.log (62500000000 / 218546030843) ∧
    -Real.log (62500000000 / 218546030843) ≤ (156478763 / 125000000) := by
  have h := checkLog_sound (w := (93546030843 / 343546030843)) (n := 12)
    (lo := (279341461 / 500000000)) (hi := (558682923 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((218546030843 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(218546030843 / 125000000000) = 1/(62500000000 / 218546030843) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (625915051 / 500000000) (156478763 / 125000000) (Real.log (218546030843 / 62500000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (218546030843 / 62500000000) = -Real.log (62500000000 / 218546030843) := by
    rw [show ((218546030843 / 62500000000) : ℝ) = ((62500000000 / 218546030843) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (1258388079 / 1000000000) ≤ -Real.log (250000000000 / 879935842243) ∧
    -Real.log (250000000000 / 879935842243) ≤ (1258388081 / 1000000000) := by
  have h := checkLog_sound (w := (379935842243 / 1379935842243)) (n := 12)
    (lo := (565240899 / 1000000000)) (hi := (5652409 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((879935842243 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(879935842243 / 500000000000) = 1/(250000000000 / 879935842243) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (1258388079 / 1000000000) (1258388081 / 1000000000) (Real.log (879935842243 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (879935842243 / 250000000000) = -Real.log (250000000000 / 879935842243) := by
    rw [show ((879935842243 / 250000000000) : ℝ) = ((250000000000 / 879935842243) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0047
