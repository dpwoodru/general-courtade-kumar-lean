import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell083
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

theorem reflection_log_1_neg : (130881561 / 500000000) ≤ -Real.log (1280 / 1663) ∧
    -Real.log (1280 / 1663) ≤ (261763123 / 1000000000) := by
  have h := checkLog_sound (w := (383 / 2943)) (n := 12)
    (lo := (130881561 / 500000000)) (hi := (261763123 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1663 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1663 / 1280) = 1/(1280 / 1663) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (130881561 / 500000000) (261763123 / 1000000000) (Real.log (1663 / 1280)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1663 / 1280) = -Real.log (1280 / 1663) := by
    rw [show ((1663 / 1280) : ℝ) = ((1280 / 1663) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (177779747 / 500000000) ≤ -Real.log (897 / 1280) ∧
    -Real.log (897 / 1280) ≤ (71111899 / 200000000) := by
  have h := checkLog_sound (w := (383 / 2177)) (n := 12)
    (lo := (177779747 / 500000000)) (hi := (71111899 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 897) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 897) = 1/(897 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-71111899 / 200000000) (-177779747 / 500000000) (Real.log (897 / 1280)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (65328007 / 250000000) ≤ -Real.log (5120 / 6649) ∧
    -Real.log (5120 / 6649) ≤ (261312029 / 1000000000) := by
  have h := checkLog_sound (w := (1529 / 11769)) (n := 12)
    (lo := (65328007 / 250000000)) (hi := (261312029 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6649 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6649 / 5120) = 1/(5120 / 6649) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (65328007 / 250000000) (261312029 / 1000000000) (Real.log (6649 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6649 / 5120) = -Real.log (5120 / 6649) := by
    rw [show ((6649 / 5120) : ℝ) = ((5120 / 6649) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (354723723 / 1000000000) ≤ -Real.log (3591 / 5120) ∧
    -Real.log (3591 / 5120) ≤ (88680931 / 250000000) := by
  have h := checkLog_sound (w := (1529 / 8711)) (n := 12)
    (lo := (354723723 / 1000000000)) (hi := (88680931 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3591) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3591) = 1/(3591 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-88680931 / 250000000) (-354723723 / 1000000000) (Real.log (3591 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (38451077 / 200000000) ≤ -Real.log (50000 / 60599) ∧
    -Real.log (50000 / 60599) ≤ (96127693 / 500000000) := by
  have h := checkLog_sound (w := (10599 / 110599)) (n := 12)
    (lo := (38451077 / 200000000)) (hi := (96127693 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((60599 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(60599 / 50000) = 1/(50000 / 60599) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (38451077 / 200000000) (96127693 / 500000000) (Real.log (60599 / 50000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (60599 / 50000) = -Real.log (50000 / 60599) := by
    rw [show ((60599 / 50000) : ℝ) = ((50000 / 60599) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (930593 / 3906250) ≤ -Real.log (39401 / 50000) ∧
    -Real.log (39401 / 50000) ≤ (238231809 / 1000000000) := by
  have h := checkLog_sound (w := (10599 / 89401)) (n := 12)
    (lo := (930593 / 3906250)) (hi := (238231809 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 39401) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 39401) = 1/(39401 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-238231809 / 1000000000) (-930593 / 3906250) (Real.log (39401 / 50000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (96300933 / 500000000) ≤ -Real.log (2500 / 3031) ∧
    -Real.log (2500 / 3031) ≤ (192601867 / 1000000000) := by
  have h := checkLog_sound (w := (531 / 5531)) (n := 12)
    (lo := (96300933 / 500000000)) (hi := (192601867 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3031 / 2500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3031 / 2500) = 1/(2500 / 3031) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (96300933 / 500000000) (192601867 / 1000000000) (Real.log (3031 / 2500)) := by
  have h := reflection_log_7_neg
  have he : Real.log (3031 / 2500) = -Real.log (2500 / 3031) := by
    rw [show ((3031 / 2500) : ℝ) = ((2500 / 3031) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (59691233 / 250000000) ≤ -Real.log (1969 / 2500) ∧
    -Real.log (1969 / 2500) ≤ (238764933 / 1000000000) := by
  have h := checkLog_sound (w := (531 / 4469)) (n := 12)
    (lo := (59691233 / 250000000)) (hi := (238764933 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500 / 1969) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500 / 1969) = 1/(1969 / 2500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-238764933 / 1000000000) (-59691233 / 250000000) (Real.log (1969 / 2500)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (35327577 / 250000000) ≤ -Real.log (500000 / 575891) ∧
    -Real.log (500000 / 575891) ≤ (141310309 / 1000000000) := by
  have h := checkLog_sound (w := (75891 / 1075891)) (n := 12)
    (lo := (35327577 / 250000000)) (hi := (141310309 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((575891 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(575891 / 500000) = 1/(500000 / 575891) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (35327577 / 250000000) (141310309 / 1000000000) (Real.log (575891 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (575891 / 500000) = -Real.log (500000 / 575891) := by
    rw [show ((575891 / 500000) : ℝ) = ((500000 / 575891) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (51443 / 312500) ≤ -Real.log (424109 / 500000) ∧
    -Real.log (424109 / 500000) ≤ (164617601 / 1000000000) := by
  have h := checkLog_sound (w := (75891 / 924109)) (n := 12)
    (lo := (51443 / 312500)) (hi := (164617601 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 424109) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 424109) = 1/(424109 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-164617601 / 1000000000) (-51443 / 312500) (Real.log (424109 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (17697319 / 125000000) ≤ -Real.log (1000000 / 1152091) ∧
    -Real.log (1000000 / 1152091) ≤ (141578553 / 1000000000) := by
  have h := checkLog_sound (w := (152091 / 2152091)) (n := 12)
    (lo := (17697319 / 125000000)) (hi := (141578553 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1152091 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1152091 / 1000000) = 1/(1000000 / 1152091) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (17697319 / 125000000) (141578553 / 1000000000) (Real.log (1152091 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1152091 / 1000000) = -Real.log (1000000 / 1152091) := by
    rw [show ((1152091 / 1000000) : ℝ) = ((1000000 / 1152091) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (4124549 / 25000000) ≤ -Real.log (847909 / 1000000) ∧
    -Real.log (847909 / 1000000) ≤ (164981961 / 1000000000) := by
  have h := checkLog_sound (w := (152091 / 1847909)) (n := 12)
    (lo := (4124549 / 25000000)) (hi := (164981961 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 847909) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 847909) = 1/(847909 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-164981961 / 1000000000) (-4124549 / 25000000) (Real.log (847909 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (77004469 / 125000000) ≤ -Real.log (31250000000 / 57861668059) ∧
    -Real.log (31250000000 / 57861668059) ≤ (616035753 / 1000000000) := by
  have h := checkLog_sound (w := (26611668059 / 89111668059)) (n := 12)
    (lo := (77004469 / 125000000)) (hi := (616035753 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((57861668059 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(57861668059 / 31250000000) = 1/(31250000000 / 57861668059) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (77004469 / 125000000) (616035753 / 1000000000) (Real.log (57861668059 / 31250000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (57861668059 / 31250000000) = -Real.log (31250000000 / 57861668059) := by
    rw [show ((57861668059 / 31250000000) : ℝ) = ((31250000000 / 57861668059) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (617322617 / 1000000000) ≤ -Real.log (125000000000 / 231744704571) ∧
    -Real.log (125000000000 / 231744704571) ≤ (308661309 / 500000000) := by
  have h := checkLog_sound (w := (106744704571 / 356744704571)) (n := 12)
    (lo := (617322617 / 1000000000)) (hi := (308661309 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((231744704571 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(231744704571 / 125000000000) = 1/(125000000000 / 231744704571) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (617322617 / 1000000000) (308661309 / 500000000) (Real.log (231744704571 / 125000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (231744704571 / 125000000000) = -Real.log (125000000000 / 231744704571) := by
    rw [show ((231744704571 / 125000000000) : ℝ) = ((125000000000 / 231744704571) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (215243597 / 500000000) ≤ -Real.log (125000000000 / 192250831197) ∧
    -Real.log (125000000000 / 192250831197) ≤ (86097439 / 200000000) := by
  have h := checkLog_sound (w := (67250831197 / 317250831197)) (n := 12)
    (lo := (215243597 / 500000000)) (hi := (86097439 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((192250831197 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(192250831197 / 125000000000) = 1/(125000000000 / 192250831197) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (215243597 / 500000000) (86097439 / 200000000) (Real.log (192250831197 / 125000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (192250831197 / 125000000000) = -Real.log (125000000000 / 192250831197) := by
    rw [show ((192250831197 / 125000000000) : ℝ) = ((125000000000 / 192250831197) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (215683399 / 500000000) ≤ -Real.log (50000000000 / 76968004063) ∧
    -Real.log (50000000000 / 76968004063) ≤ (431366799 / 1000000000) := by
  have h := checkLog_sound (w := (26968004063 / 126968004063)) (n := 12)
    (lo := (215683399 / 500000000)) (hi := (431366799 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((76968004063 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(76968004063 / 50000000000) = 1/(50000000000 / 76968004063) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (215683399 / 500000000) (431366799 / 1000000000) (Real.log (76968004063 / 50000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (76968004063 / 50000000000) = -Real.log (50000000000 / 76968004063) := by
    rw [show ((76968004063 / 50000000000) : ℝ) = ((50000000000 / 76968004063) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (305927909 / 1000000000) ≤ -Real.log (100000000000 / 135788441179) ∧
    -Real.log (100000000000 / 135788441179) ≤ (30592791 / 100000000) := by
  have h := checkLog_sound (w := (35788441179 / 235788441179)) (n := 12)
    (lo := (305927909 / 1000000000)) (hi := (30592791 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((135788441179 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(135788441179 / 100000000000) = 1/(100000000000 / 135788441179) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (305927909 / 1000000000) (30592791 / 100000000) (Real.log (135788441179 / 100000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (135788441179 / 100000000000) = -Real.log (100000000000 / 135788441179) := by
    rw [show ((135788441179 / 100000000000) : ℝ) = ((100000000000 / 135788441179) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (598751 / 1953125) ≤ -Real.log (500000000000 / 679371842969) ∧
    -Real.log (500000000000 / 679371842969) ≤ (306560513 / 1000000000) := by
  have h := checkLog_sound (w := (179371842969 / 1179371842969)) (n := 12)
    (lo := (598751 / 1953125)) (hi := (306560513 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((679371842969 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(679371842969 / 500000000000) = 1/(500000000000 / 679371842969) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (598751 / 1953125) (306560513 / 1000000000) (Real.log (679371842969 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (679371842969 / 500000000000) = -Real.log (500000000000 / 679371842969) := by
    rw [show ((679371842969 / 500000000000) : ℝ) = ((500000000000 / 679371842969) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1462713 / 62500000) ≤ -Real.log (976868327719 / 1000000000000) ∧
    -Real.log (976868327719 / 1000000000000) ≤ (23403409 / 1000000000) := by
  have h := checkLog_sound (w := (23131672281 / 1976868327719)) (n := 12)
    (lo := (1462713 / 62500000)) (hi := (23403409 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 976868327719) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 976868327719) = 1/(976868327719 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-23403409 / 1000000000) (-1462713 / 62500000) (Real.log (976868327719 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (5826823 / 250000000) ≤ -Real.log (244240556119 / 250000000000) ∧
    -Real.log (244240556119 / 250000000000) ≤ (23307293 / 1000000000) := by
  have h := checkLog_sound (w := (5759443881 / 494240556119)) (n := 12)
    (lo := (5826823 / 250000000)) (hi := (23307293 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 244240556119) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 244240556119) = 1/(244240556119 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-23307293 / 1000000000) (-5826823 / 250000000) (Real.log (244240556119 / 250000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell083
