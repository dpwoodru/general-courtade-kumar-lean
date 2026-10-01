import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell058
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

theorem reflection_log_1_neg : (10016971 / 40000000) ≤ -Real.log (5120 / 6577) ∧
    -Real.log (5120 / 6577) ≤ (62606069 / 250000000) := by
  have h := checkLog_sound (w := (1457 / 11697)) (n := 12)
    (lo := (10016971 / 40000000)) (hi := (62606069 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6577 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6577 / 5120) = 1/(5120 / 6577) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (10016971 / 40000000) (62606069 / 250000000) (Real.log (6577 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6577 / 5120) = -Real.log (5120 / 6577) := by
    rw [show ((6577 / 5120) : ℝ) = ((5120 / 6577) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (66974391 / 200000000) ≤ -Real.log (3663 / 5120) ∧
    -Real.log (3663 / 5120) ≤ (83717989 / 250000000) := by
  have h := checkLog_sound (w := (1457 / 8783)) (n := 12)
    (lo := (66974391 / 200000000)) (hi := (83717989 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3663) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3663) = 1/(3663 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-83717989 / 250000000) (-66974391 / 200000000) (Real.log (3663 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (62492009 / 250000000) ≤ -Real.log (2560 / 3287) ∧
    -Real.log (2560 / 3287) ≤ (249968037 / 1000000000) := by
  have h := checkLog_sound (w := (727 / 5847)) (n := 12)
    (lo := (62492009 / 250000000)) (hi := (249968037 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3287 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3287 / 2560) = 1/(2560 / 3287) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (62492009 / 250000000) (249968037 / 1000000000) (Real.log (3287 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3287 / 2560) = -Real.log (2560 / 3287) := by
    rw [show ((3287 / 2560) : ℝ) = ((2560 / 3287) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (334053289 / 1000000000) ≤ -Real.log (1833 / 2560) ∧
    -Real.log (1833 / 2560) ≤ (33405329 / 100000000) := by
  have h := checkLog_sound (w := (727 / 4393)) (n := 12)
    (lo := (334053289 / 1000000000)) (hi := (33405329 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1833) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1833) = 1/(1833 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-33405329 / 100000000) (-334053289 / 1000000000) (Real.log (1833 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (183574937 / 1000000000) ≤ -Real.log (200000 / 240301) ∧
    -Real.log (200000 / 240301) ≤ (91787469 / 500000000) := by
  have h := checkLog_sound (w := (40301 / 440301)) (n := 12)
    (lo := (183574937 / 1000000000)) (hi := (91787469 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((240301 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(240301 / 200000) = 1/(200000 / 240301) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (183574937 / 1000000000) (91787469 / 500000000) (Real.log (240301 / 200000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (240301 / 200000) = -Real.log (200000 / 240301) := by
    rw [show ((240301 / 200000) : ℝ) = ((200000 / 240301) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (225026573 / 1000000000) ≤ -Real.log (159699 / 200000) ∧
    -Real.log (159699 / 200000) ≤ (112513287 / 500000000) := by
  have h := checkLog_sound (w := (40301 / 359699)) (n := 12)
    (lo := (225026573 / 1000000000)) (hi := (112513287 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 159699) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 159699) = 1/(159699 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-112513287 / 500000000) (-225026573 / 1000000000) (Real.log (159699 / 200000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (91962219 / 500000000) ≤ -Real.log (40000 / 48077) ∧
    -Real.log (40000 / 48077) ≤ (183924439 / 1000000000) := by
  have h := checkLog_sound (w := (8077 / 88077)) (n := 12)
    (lo := (91962219 / 500000000)) (hi := (183924439 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((48077 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(48077 / 40000) = 1/(40000 / 48077) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (91962219 / 500000000) (183924439 / 1000000000) (Real.log (48077 / 40000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (48077 / 40000) = -Real.log (40000 / 48077) := by
    rw [show ((48077 / 40000) : ℝ) = ((40000 / 48077) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (2255527 / 10000000) ≤ -Real.log (31923 / 40000) ∧
    -Real.log (31923 / 40000) ≤ (225552701 / 1000000000) := by
  have h := checkLog_sound (w := (8077 / 71923)) (n := 12)
    (lo := (2255527 / 10000000)) (hi := (225552701 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000 / 31923) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000 / 31923) = 1/(31923 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-225552701 / 1000000000) (-2255527 / 10000000) (Real.log (31923 / 40000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (6731221 / 50000000) ≤ -Real.log (1000000 / 1144107) ∧
    -Real.log (1000000 / 1144107) ≤ (134624421 / 1000000000) := by
  have h := checkLog_sound (w := (144107 / 2144107)) (n := 12)
    (lo := (6731221 / 50000000)) (hi := (134624421 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1144107 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1144107 / 1000000) = 1/(1000000 / 1144107) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (6731221 / 50000000) (134624421 / 1000000000) (Real.log (1144107 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1144107 / 1000000) = -Real.log (1000000 / 1144107) := by
    rw [show ((1144107 / 1000000) : ℝ) = ((1000000 / 1144107) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (15560991 / 100000000) ≤ -Real.log (855893 / 1000000) ∧
    -Real.log (855893 / 1000000) ≤ (155609911 / 1000000000) := by
  have h := checkLog_sound (w := (144107 / 1855893)) (n := 12)
    (lo := (15560991 / 100000000)) (hi := (155609911 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 855893) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 855893) = 1/(855893 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-155609911 / 1000000000) (-15560991 / 100000000) (Real.log (855893 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (26978543 / 200000000) ≤ -Real.log (500000 / 572207) ∧
    -Real.log (500000 / 572207) ≤ (33723179 / 250000000) := by
  have h := checkLog_sound (w := (72207 / 1072207)) (n := 12)
    (lo := (26978543 / 200000000)) (hi := (33723179 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((572207 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(572207 / 500000) = 1/(500000 / 572207) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (26978543 / 200000000) (33723179 / 250000000) (Real.log (572207 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (572207 / 500000) = -Real.log (500000 / 572207) := by
    rw [show ((572207 / 500000) : ℝ) = ((500000 / 572207) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (19496083 / 125000000) ≤ -Real.log (427793 / 500000) ∧
    -Real.log (427793 / 500000) ≤ (31193733 / 200000000) := by
  have h := checkLog_sound (w := (72207 / 927793)) (n := 12)
    (lo := (19496083 / 125000000)) (hi := (31193733 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 427793) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 427793) = 1/(427793 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-31193733 / 200000000) (-19496083 / 125000000) (Real.log (427793 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (23360853 / 40000000) ≤ -Real.log (50000000000 / 89661756683) ∧
    -Real.log (50000000000 / 89661756683) ≤ (292010663 / 500000000) := by
  have h := checkLog_sound (w := (39661756683 / 139661756683)) (n := 12)
    (lo := (23360853 / 40000000)) (hi := (292010663 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((89661756683 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(89661756683 / 50000000000) = 1/(50000000000 / 89661756683) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (23360853 / 40000000) (292010663 / 500000000) (Real.log (89661756683 / 50000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (89661756683 / 50000000000) = -Real.log (50000000000 / 89661756683) := by
    rw [show ((89661756683 / 50000000000) : ℝ) = ((50000000000 / 89661756683) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (58529623 / 100000000) ≤ -Real.log (250000000000 / 448880698881) ∧
    -Real.log (250000000000 / 448880698881) ≤ (585296231 / 1000000000) := by
  have h := checkLog_sound (w := (198880698881 / 698880698881)) (n := 12)
    (lo := (58529623 / 100000000)) (hi := (585296231 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((448880698881 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(448880698881 / 250000000000) = 1/(250000000000 / 448880698881) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (58529623 / 100000000) (585296231 / 1000000000) (Real.log (448880698881 / 250000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (448880698881 / 250000000000) = -Real.log (250000000000 / 448880698881) := by
    rw [show ((448880698881 / 250000000000) : ℝ) = ((250000000000 / 448880698881) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (40860151 / 100000000) ≤ -Real.log (100000000000 / 150471198943) ∧
    -Real.log (100000000000 / 150471198943) ≤ (408601511 / 1000000000) := by
  have h := checkLog_sound (w := (50471198943 / 250471198943)) (n := 12)
    (lo := (40860151 / 100000000)) (hi := (408601511 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((150471198943 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(150471198943 / 100000000000) = 1/(100000000000 / 150471198943) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (40860151 / 100000000) (408601511 / 1000000000) (Real.log (150471198943 / 100000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (150471198943 / 100000000000) = -Real.log (100000000000 / 150471198943) := by
    rw [show ((150471198943 / 100000000000) : ℝ) = ((100000000000 / 150471198943) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (409477139 / 1000000000) ≤ -Real.log (500000000000 / 753015067507) ∧
    -Real.log (500000000000 / 753015067507) ≤ (20473857 / 50000000) := by
  have h := checkLog_sound (w := (253015067507 / 1253015067507)) (n := 12)
    (lo := (409477139 / 1000000000)) (hi := (20473857 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((753015067507 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(753015067507 / 500000000000) = 1/(500000000000 / 753015067507) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (409477139 / 1000000000) (20473857 / 50000000) (Real.log (753015067507 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (753015067507 / 500000000000) = -Real.log (500000000000 / 753015067507) := by
    rw [show ((753015067507 / 500000000000) : ℝ) = ((500000000000 / 753015067507) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (29023433 / 100000000) ≤ -Real.log (250000000000 / 334185172679) ∧
    -Real.log (250000000000 / 334185172679) ≤ (290234331 / 1000000000) := by
  have h := checkLog_sound (w := (84185172679 / 584185172679)) (n := 12)
    (lo := (29023433 / 100000000)) (hi := (290234331 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((334185172679 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(334185172679 / 250000000000) = 1/(250000000000 / 334185172679) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (29023433 / 100000000) (290234331 / 1000000000) (Real.log (334185172679 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (334185172679 / 250000000000) = -Real.log (250000000000 / 334185172679) := by
    rw [show ((334185172679 / 250000000000) : ℝ) = ((250000000000 / 334185172679) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (14543069 / 50000000) ≤ -Real.log (250000000000 / 334394789069) ∧
    -Real.log (250000000000 / 334394789069) ≤ (290861381 / 1000000000) := by
  have h := checkLog_sound (w := (84394789069 / 584394789069)) (n := 12)
    (lo := (14543069 / 50000000)) (hi := (290861381 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((334394789069 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(334394789069 / 250000000000) = 1/(250000000000 / 334394789069) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (14543069 / 50000000) (290861381 / 1000000000) (Real.log (334394789069 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (334394789069 / 250000000000) = -Real.log (250000000000 / 334394789069) := by
    rw [show ((334394789069 / 250000000000) : ℝ) = ((250000000000 / 334394789069) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (21075949 / 1000000000) ≤ -Real.log (244786149151 / 250000000000) ∧
    -Real.log (244786149151 / 250000000000) ≤ (421519 / 20000000) := by
  have h := checkLog_sound (w := (5213850849 / 494786149151)) (n := 12)
    (lo := (21075949 / 1000000000)) (hi := (421519 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 244786149151) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 244786149151) = 1/(244786149151 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-421519 / 20000000) (-21075949 / 1000000000) (Real.log (244786149151 / 250000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (2098549 / 100000000) ≤ -Real.log (979233172551 / 1000000000000) ∧
    -Real.log (979233172551 / 1000000000000) ≤ (20985491 / 1000000000) := by
  have h := checkLog_sound (w := (20766827449 / 1979233172551)) (n := 12)
    (lo := (2098549 / 100000000)) (hi := (20985491 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 979233172551) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 979233172551) = 1/(979233172551 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-20985491 / 1000000000) (-2098549 / 100000000) (Real.log (979233172551 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell058
