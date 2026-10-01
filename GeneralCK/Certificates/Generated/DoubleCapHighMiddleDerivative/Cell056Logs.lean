import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell056
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

theorem reflection_log_1_neg : (62377897 / 250000000) ≤ -Real.log (5120 / 6571) ∧
    -Real.log (5120 / 6571) ≤ (249511589 / 1000000000) := by
  have h := checkLog_sound (w := (1451 / 11691)) (n := 12)
    (lo := (62377897 / 250000000)) (hi := (249511589 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6571 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6571 / 5120) = 1/(5120 / 6571) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (62377897 / 250000000) (249511589 / 1000000000) (Real.log (6571 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6571 / 5120) = -Real.log (5120 / 6571) := by
    rw [show ((6571 / 5120) : ℝ) = ((5120 / 6571) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (333235293 / 1000000000) ≤ -Real.log (3669 / 5120) ∧
    -Real.log (3669 / 5120) ≤ (166617647 / 500000000) := by
  have h := checkLog_sound (w := (1451 / 8789)) (n := 12)
    (lo := (333235293 / 1000000000)) (hi := (166617647 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3669) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3669) = 1/(3669 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-166617647 / 500000000) (-333235293 / 1000000000) (Real.log (3669 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (249054933 / 1000000000) ≤ -Real.log (640 / 821) ∧
    -Real.log (640 / 821) ≤ (124527467 / 500000000) := by
  have h := checkLog_sound (w := (181 / 1461)) (n := 12)
    (lo := (249054933 / 1000000000)) (hi := (124527467 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((821 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(821 / 640) = 1/(640 / 821) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (249054933 / 1000000000) (124527467 / 500000000) (Real.log (821 / 640)) := by
  have h := reflection_log_3_neg
  have he : Real.log (821 / 640) = -Real.log (640 / 821) := by
    rw [show ((821 / 640) : ℝ) = ((640 / 821) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (166208983 / 500000000) ≤ -Real.log (459 / 640) ∧
    -Real.log (459 / 640) ≤ (332417967 / 1000000000) := by
  have h := checkLog_sound (w := (181 / 1099)) (n := 12)
    (lo := (166208983 / 500000000)) (hi := (332417967 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 459) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 459) = 1/(459 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-332417967 / 1000000000) (-166208983 / 500000000) (Real.log (459 / 640)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (45719517 / 250000000) ≤ -Real.log (250000 / 300167) ∧
    -Real.log (250000 / 300167) ≤ (182878069 / 1000000000) := by
  have h := checkLog_sound (w := (50167 / 550167)) (n := 12)
    (lo := (45719517 / 250000000)) (hi := (182878069 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((300167 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(300167 / 250000) = 1/(250000 / 300167) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (45719517 / 250000000) (182878069 / 1000000000) (Real.log (300167 / 250000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (300167 / 250000) = -Real.log (250000 / 300167) := by
    rw [show ((300167 / 250000) : ℝ) = ((250000 / 300167) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (2239789 / 10000000) ≤ -Real.log (199833 / 250000) ∧
    -Real.log (199833 / 250000) ≤ (223978901 / 1000000000) := by
  have h := checkLog_sound (w := (50167 / 449833)) (n := 12)
    (lo := (2239789 / 10000000)) (hi := (223978901 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 199833) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 199833) = 1/(199833 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-223978901 / 1000000000) (-2239789 / 10000000) (Real.log (199833 / 250000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (9161349 / 50000000) ≤ -Real.log (1000000 / 1201087) ∧
    -Real.log (1000000 / 1201087) ≤ (183226981 / 1000000000) := by
  have h := checkLog_sound (w := (201087 / 2201087)) (n := 12)
    (lo := (9161349 / 50000000)) (hi := (183226981 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1201087 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1201087 / 1000000) = 1/(1000000 / 1201087) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (9161349 / 50000000) (183226981 / 1000000000) (Real.log (1201087 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1201087 / 1000000) = -Real.log (1000000 / 1201087) := by
    rw [show ((1201087 / 1000000) : ℝ) = ((1000000 / 1201087) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (8980129 / 40000000) ≤ -Real.log (798913 / 1000000) ∧
    -Real.log (798913 / 1000000) ≤ (112251613 / 500000000) := by
  have h := checkLog_sound (w := (201087 / 1798913)) (n := 12)
    (lo := (8980129 / 40000000)) (hi := (112251613 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 798913) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 798913) = 1/(798913 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-112251613 / 500000000) (-8980129 / 40000000) (Real.log (798913 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (134089361 / 1000000000) ≤ -Real.log (200000 / 228699) ∧
    -Real.log (200000 / 228699) ≤ (67044681 / 500000000) := by
  have h := checkLog_sound (w := (28699 / 428699)) (n := 12)
    (lo := (134089361 / 1000000000)) (hi := (67044681 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((228699 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(228699 / 200000) = 1/(200000 / 228699) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (134089361 / 1000000000) (67044681 / 500000000) (Real.log (228699 / 200000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (228699 / 200000) = -Real.log (200000 / 228699) := by
    rw [show ((228699 / 200000) : ℝ) = ((200000 / 228699) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (154895123 / 1000000000) ≤ -Real.log (171301 / 200000) ∧
    -Real.log (171301 / 200000) ≤ (38723781 / 250000000) := by
  have h := checkLog_sound (w := (28699 / 371301)) (n := 12)
    (lo := (154895123 / 1000000000)) (hi := (38723781 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 171301) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 171301) = 1/(171301 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-38723781 / 250000000) (-154895123 / 1000000000) (Real.log (171301 / 200000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (134357801 / 1000000000) ≤ -Real.log (500000 / 571901) ∧
    -Real.log (500000 / 571901) ≤ (67178901 / 500000000) := by
  have h := checkLog_sound (w := (71901 / 1071901)) (n := 12)
    (lo := (134357801 / 1000000000)) (hi := (67178901 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((571901 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(571901 / 500000) = 1/(500000 / 571901) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (134357801 / 1000000000) (67178901 / 500000000) (Real.log (571901 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (571901 / 500000) = -Real.log (500000 / 571901) := by
    rw [show ((571901 / 500000) : ℝ) = ((500000 / 571901) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (155253621 / 1000000000) ≤ -Real.log (428099 / 500000) ∧
    -Real.log (428099 / 500000) ≤ (77626811 / 500000000) := by
  have h := checkLog_sound (w := (71901 / 928099)) (n := 12)
    (lo := (155253621 / 1000000000)) (hi := (77626811 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 428099) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 428099) = 1/(428099 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-77626811 / 500000000) (-155253621 / 1000000000) (Real.log (428099 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (581472899 / 1000000000) ≤ -Real.log (250000000000 / 447167755991) ∧
    -Real.log (250000000000 / 447167755991) ≤ (5814729 / 10000000) := by
  have h := checkLog_sound (w := (197167755991 / 697167755991)) (n := 12)
    (lo := (581472899 / 1000000000)) (hi := (5814729 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((447167755991 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(447167755991 / 250000000000) = 1/(250000000000 / 447167755991) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (581472899 / 1000000000) (5814729 / 10000000) (Real.log (447167755991 / 250000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (447167755991 / 250000000000) = -Real.log (250000000000 / 447167755991) := by
    rw [show ((447167755991 / 250000000000) : ℝ) = ((250000000000 / 447167755991) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (291373441 / 500000000) ≤ -Real.log (500000000000 / 895475606433) ∧
    -Real.log (500000000000 / 895475606433) ≤ (582746883 / 1000000000) := by
  have h := checkLog_sound (w := (395475606433 / 1395475606433)) (n := 12)
    (lo := (291373441 / 500000000)) (hi := (582746883 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((895475606433 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(895475606433 / 500000000000) = 1/(500000000000 / 895475606433) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (291373441 / 500000000) (582746883 / 1000000000) (Real.log (895475606433 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (895475606433 / 500000000000) = -Real.log (500000000000 / 895475606433) := by
    rw [show ((895475606433 / 500000000000) : ℝ) = ((500000000000 / 895475606433) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (50857121 / 125000000) ≤ -Real.log (500000000000 / 751044622259) ∧
    -Real.log (500000000000 / 751044622259) ≤ (406856969 / 1000000000) := by
  have h := checkLog_sound (w := (251044622259 / 1251044622259)) (n := 12)
    (lo := (50857121 / 125000000)) (hi := (406856969 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((751044622259 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(751044622259 / 500000000000) = 1/(500000000000 / 751044622259) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (50857121 / 125000000) (406856969 / 1000000000) (Real.log (751044622259 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (751044622259 / 500000000000) = -Real.log (500000000000 / 751044622259) := by
    rw [show ((751044622259 / 500000000000) : ℝ) = ((500000000000 / 751044622259) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (81546041 / 200000000) ≤ -Real.log (62500000000 / 93962593549) ∧
    -Real.log (62500000000 / 93962593549) ≤ (203865103 / 500000000) := by
  have h := checkLog_sound (w := (31462593549 / 156462593549)) (n := 12)
    (lo := (81546041 / 200000000)) (hi := (203865103 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((93962593549 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(93962593549 / 62500000000) = 1/(62500000000 / 93962593549) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (81546041 / 200000000) (203865103 / 500000000) (Real.log (93962593549 / 62500000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (93962593549 / 62500000000) = -Real.log (62500000000 / 93962593549) := by
    rw [show ((93962593549 / 62500000000) : ℝ) = ((62500000000 / 93962593549) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (57796897 / 200000000) ≤ -Real.log (500000000000 / 667535507673) ∧
    -Real.log (500000000000 / 667535507673) ≤ (144492243 / 500000000) := by
  have h := checkLog_sound (w := (167535507673 / 1167535507673)) (n := 12)
    (lo := (57796897 / 200000000)) (hi := (144492243 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((667535507673 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(667535507673 / 500000000000) = 1/(500000000000 / 667535507673) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (57796897 / 200000000) (144492243 / 500000000) (Real.log (667535507673 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (667535507673 / 500000000000) = -Real.log (500000000000 / 667535507673) := by
    rw [show ((667535507673 / 500000000000) : ℝ) = ((500000000000 / 667535507673) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (144805711 / 500000000) ≤ -Real.log (500000000000 / 667954141449) ∧
    -Real.log (500000000000 / 667954141449) ≤ (289611423 / 1000000000) := by
  have h := checkLog_sound (w := (167954141449 / 1167954141449)) (n := 12)
    (lo := (144805711 / 500000000)) (hi := (289611423 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((667954141449 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(667954141449 / 500000000000) = 1/(500000000000 / 667954141449) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (144805711 / 500000000) (289611423 / 1000000000) (Real.log (667954141449 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (667954141449 / 500000000000) = -Real.log (500000000000 / 667954141449) := by
    rw [show ((667954141449 / 500000000000) : ℝ) = ((500000000000 / 667954141449) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1044791 / 50000000) ≤ -Real.log (244830246199 / 250000000000) ∧
    -Real.log (244830246199 / 250000000000) ≤ (20895821 / 1000000000) := by
  have h := checkLog_sound (w := (5169753801 / 494830246199)) (n := 12)
    (lo := (1044791 / 50000000)) (hi := (20895821 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 244830246199) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 244830246199) = 1/(244830246199 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-20895821 / 1000000000) (-1044791 / 50000000) (Real.log (244830246199 / 250000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (20805761 / 1000000000) ≤ -Real.log (39176367399 / 40000000000) ∧
    -Real.log (39176367399 / 40000000000) ≤ (10402881 / 500000000) := by
  have h := checkLog_sound (w := (823632601 / 79176367399)) (n := 12)
    (lo := (20805761 / 1000000000)) (hi := (10402881 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39176367399) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39176367399) = 1/(39176367399 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-10402881 / 500000000) (-20805761 / 1000000000) (Real.log (39176367399 / 40000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell056
