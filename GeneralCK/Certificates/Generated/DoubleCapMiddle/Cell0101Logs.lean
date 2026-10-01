import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0101
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

theorem reflection_log_1_neg : (332558337 / 1000000000) ≤ -Real.log (256 / 357) ∧
    -Real.log (256 / 357) ≤ (166279169 / 500000000) := by
  have h := checkLog_sound (w := (101 / 613)) (n := 12)
    (lo := (332558337 / 1000000000)) (hi := (166279169 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((357 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(357 / 256) = 1/(256 / 357) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (332558337 / 1000000000) (166279169 / 500000000) (Real.log (357 / 256)) := by
  have h := reflection_log_1_neg
  have he : Real.log (357 / 256) = -Real.log (256 / 357) := by
    rw [show ((357 / 256) : ℝ) = ((256 / 357) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (501752327 / 1000000000) ≤ -Real.log (155 / 256) ∧
    -Real.log (155 / 256) ≤ (62719041 / 125000000) := by
  have h := checkLog_sound (w := (101 / 411)) (n := 12)
    (lo := (501752327 / 1000000000)) (hi := (62719041 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((256 / 155) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(256 / 155) = 1/(155 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-62719041 / 125000000) (-501752327 / 1000000000) (Real.log (155 / 256)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (331717647 / 1000000000) ≤ -Real.log (2560 / 3567) ∧
    -Real.log (2560 / 3567) ≤ (20732353 / 62500000) := by
  have h := checkLog_sound (w := (1007 / 6127)) (n := 12)
    (lo := (331717647 / 1000000000)) (hi := (20732353 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3567 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3567 / 2560) = 1/(2560 / 3567) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (331717647 / 1000000000) (20732353 / 62500000) (Real.log (3567 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3567 / 2560) = -Real.log (2560 / 3567) := by
    rw [show ((3567 / 2560) : ℝ) = ((2560 / 3567) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (249909357 / 500000000) ≤ -Real.log (1553 / 2560) ∧
    -Real.log (1553 / 2560) ≤ (99963743 / 200000000) := by
  have h := checkLog_sound (w := (1007 / 4113)) (n := 12)
    (lo := (249909357 / 500000000)) (hi := (99963743 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1553) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1553) = 1/(1553 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-99963743 / 200000000) (-249909357 / 500000000) (Real.log (1553 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (581691739 / 1000000000) ≤ -Real.log (128 / 229) ∧
    -Real.log (128 / 229) ≤ (29084587 / 50000000) := by
  have h := checkLog_sound (w := (101 / 357)) (n := 12)
    (lo := (581691739 / 1000000000)) (hi := (29084587 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((229 / 128) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(229 / 128) = 1/(128 / 229) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (581691739 / 1000000000) (29084587 / 50000000) (Real.log (229 / 128)) := by
  have h := reflection_log_5_neg
  have he : Real.log (229 / 128) = -Real.log (128 / 229) := by
    rw [show ((229 / 128) : ℝ) = ((128 / 229) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (389048349 / 250000000) ≤ -Real.log (27 / 128) ∧
    -Real.log (27 / 128) ≤ (1556193399 / 1000000000) := by
  have h := checkLog_sound (w := (5 / 59)) (n := 12)
    (lo := (42474759 / 250000000)) (hi := (169899037 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((32 / 27) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(32 / 27) = 1/(27 / 128) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1556193399 / 1000000000) (-389048349 / 250000000) (Real.log (27 / 128)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (580380837 / 1000000000) ≤ -Real.log (1280 / 2287) ∧
    -Real.log (1280 / 2287) ≤ (290190419 / 500000000) := by
  have h := checkLog_sound (w := (1007 / 3567)) (n := 12)
    (lo := (580380837 / 1000000000)) (hi := (290190419 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2287 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2287 / 1280) = 1/(1280 / 2287) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (580380837 / 1000000000) (290190419 / 500000000) (Real.log (2287 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2287 / 1280) = -Real.log (1280 / 2287) := by
    rw [show ((2287 / 1280) : ℝ) = ((1280 / 2287) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (38628589 / 25000000) ≤ -Real.log (273 / 1280) ∧
    -Real.log (273 / 1280) ≤ (1545143563 / 1000000000) := by
  have h := checkLog_sound (w := (47 / 593)) (n := 12)
    (lo := (397123 / 2500000)) (hi := (158849201 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 273) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(320 / 273) = 1/(273 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1545143563 / 1000000000) (-38628589 / 25000000) (Real.log (273 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (45518373 / 100000000) ≤ -Real.log (1000000 / 1576463) ∧
    -Real.log (1000000 / 1576463) ≤ (455183731 / 1000000000) := by
  have h := checkLog_sound (w := (576463 / 2576463)) (n := 12)
    (lo := (45518373 / 100000000)) (hi := (455183731 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1576463 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1576463 / 1000000) = 1/(1000000 / 1576463) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (45518373 / 100000000) (455183731 / 1000000000) (Real.log (1576463 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1576463 / 1000000) = -Real.log (1000000 / 1576463) := by
    rw [show ((1576463 / 1000000) : ℝ) = ((1000000 / 1576463) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (1073893 / 1250000) ≤ -Real.log (423537 / 1000000) ∧
    -Real.log (423537 / 1000000) ≤ (429557201 / 500000000) := by
  have h := checkLog_sound (w := (76463 / 923537)) (n := 12)
    (lo := (8298361 / 50000000)) (hi := (165967221 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 423537) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 423537) = 1/(423537 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-429557201 / 500000000) (-1073893 / 1250000) (Real.log (423537 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (1140969 / 2500000) ≤ -Real.log (500000 / 789181) ∧
    -Real.log (500000 / 789181) ≤ (456387601 / 1000000000) := by
  have h := checkLog_sound (w := (289181 / 1289181)) (n := 12)
    (lo := (1140969 / 2500000)) (hi := (456387601 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((789181 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(789181 / 500000) = 1/(500000 / 789181) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (1140969 / 2500000) (456387601 / 1000000000) (Real.log (789181 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (789181 / 500000) = -Real.log (500000 / 789181) := by
    rw [show ((789181 / 500000) : ℝ) = ((500000 / 789181) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (107951019 / 125000000) ≤ -Real.log (210819 / 500000) ∧
    -Real.log (210819 / 500000) ≤ (431804077 / 500000000) := by
  have h := checkLog_sound (w := (39181 / 460819)) (n := 12)
    (lo := (42615243 / 250000000)) (hi := (170460973 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 210819) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 210819) = 1/(210819 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-431804077 / 500000000) (-107951019 / 125000000) (Real.log (210819 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (370616901 / 1000000000) ≤ -Real.log (250000 / 362157) ∧
    -Real.log (250000 / 362157) ≤ (185308451 / 500000000) := by
  have h := checkLog_sound (w := (112157 / 612157)) (n := 12)
    (lo := (370616901 / 1000000000)) (hi := (185308451 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((362157 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(362157 / 250000) = 1/(250000 / 362157) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (370616901 / 1000000000) (185308451 / 500000000) (Real.log (362157 / 250000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (362157 / 250000) = -Real.log (250000 / 362157) := by
    rw [show ((362157 / 250000) : ℝ) = ((250000 / 362157) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (595345561 / 1000000000) ≤ -Real.log (137843 / 250000) ∧
    -Real.log (137843 / 250000) ≤ (297672781 / 500000000) := by
  have h := checkLog_sound (w := (112157 / 387843)) (n := 12)
    (lo := (595345561 / 1000000000)) (hi := (297672781 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 137843) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 137843) = 1/(137843 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-297672781 / 500000000) (-595345561 / 1000000000) (Real.log (137843 / 250000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (18591969 / 50000000) ≤ -Real.log (1250 / 1813) ∧
    -Real.log (1250 / 1813) ≤ (371839381 / 1000000000) := by
  have h := checkLog_sound (w := (563 / 3063)) (n := 12)
    (lo := (18591969 / 50000000)) (hi := (371839381 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1813 / 1250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1813 / 1250) = 1/(1250 / 1813) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (18591969 / 50000000) (371839381 / 1000000000) (Real.log (1813 / 1250)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1813 / 1250) = -Real.log (1250 / 1813) := by
    rw [show ((1813 / 1250) : ℝ) = ((1250 / 1813) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (299282269 / 500000000) ≤ -Real.log (687 / 1250) ∧
    -Real.log (687 / 1250) ≤ (598564539 / 1000000000) := by
  have h := checkLog_sound (w := (563 / 1937)) (n := 12)
    (lo := (299282269 / 500000000)) (hi := (598564539 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250 / 687) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1250 / 687) = 1/(687 / 1250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-598564539 / 1000000000) (-299282269 / 500000000) (Real.log (687 / 1250)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (131429813 / 100000000) ≤ -Real.log (125000000000 / 465267202157) ∧
    -Real.log (125000000000 / 465267202157) ≤ (328574533 / 250000000) := by
  have h := checkLog_sound (w := (215267202157 / 715267202157)) (n := 12)
    (lo := (12423019 / 20000000)) (hi := (621150951 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((465267202157 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(465267202157 / 250000000000) = 1/(125000000000 / 465267202157) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (131429813 / 100000000) (328574533 / 250000000) (Real.log (465267202157 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (465267202157 / 125000000000) = -Real.log (125000000000 / 465267202157) := by
    rw [show ((465267202157 / 125000000000) : ℝ) = ((125000000000 / 465267202157) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (164999469 / 125000000) ≤ -Real.log (250000000000 / 935851370133) ∧
    -Real.log (250000000000 / 935851370133) ≤ (659997877 / 500000000) := by
  have h := checkLog_sound (w := (435851370133 / 1435851370133)) (n := 12)
    (lo := (156712143 / 250000000)) (hi := (626848573 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((935851370133 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(935851370133 / 500000000000) = 1/(250000000000 / 935851370133) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (164999469 / 125000000) (659997877 / 500000000) (Real.log (935851370133 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (935851370133 / 250000000000) = -Real.log (250000000000 / 935851370133) := by
    rw [show ((935851370133 / 250000000000) : ℝ) = ((250000000000 / 935851370133) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (482981231 / 500000000) ≤ -Real.log (250000000000 / 656828783471) ∧
    -Real.log (250000000000 / 656828783471) ≤ (30186327 / 31250000) := by
  have h := checkLog_sound (w := (156828783471 / 1156828783471)) (n := 12)
    (lo := (136407641 / 500000000)) (hi := (272815283 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((656828783471 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(656828783471 / 500000000000) = 1/(250000000000 / 656828783471) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (482981231 / 500000000) (30186327 / 31250000) (Real.log (656828783471 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (656828783471 / 250000000000) = -Real.log (250000000000 / 656828783471) := by
    rw [show ((656828783471 / 250000000000) : ℝ) = ((250000000000 / 656828783471) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (970403917 / 1000000000) ≤ -Real.log (100000000000 / 263901018923) ∧
    -Real.log (100000000000 / 263901018923) ≤ (970403919 / 1000000000) := by
  have h := checkLog_sound (w := (63901018923 / 463901018923)) (n := 12)
    (lo := (277256737 / 1000000000)) (hi := (138628369 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((263901018923 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(263901018923 / 200000000000) = 1/(100000000000 / 263901018923) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (970403917 / 1000000000) (970403919 / 1000000000) (Real.log (263901018923 / 100000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (263901018923 / 100000000000) = -Real.log (100000000000 / 263901018923) := by
    rw [show ((263901018923 / 100000000000) : ℝ) = ((100000000000 / 263901018923) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0101
