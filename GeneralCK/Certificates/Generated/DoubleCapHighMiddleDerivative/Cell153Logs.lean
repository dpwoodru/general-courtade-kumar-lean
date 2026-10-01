import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell153
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

theorem reflection_log_1_neg : (58568901 / 200000000) ≤ -Real.log (2560 / 3431) ∧
    -Real.log (2560 / 3431) ≤ (146422253 / 500000000) := by
  have h := checkLog_sound (w := (871 / 5991)) (n := 12)
    (lo := (58568901 / 200000000)) (hi := (146422253 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3431 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3431 / 2560) = 1/(2560 / 3431) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (58568901 / 200000000) (146422253 / 500000000) (Real.log (3431 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3431 / 2560) = -Real.log (2560 / 3431) := by
    rw [show ((3431 / 2560) : ℝ) = ((2560 / 3431) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (20793531 / 50000000) ≤ -Real.log (1689 / 2560) ∧
    -Real.log (1689 / 2560) ≤ (415870621 / 1000000000) := by
  have h := checkLog_sound (w := (871 / 4249)) (n := 12)
    (lo := (20793531 / 50000000)) (hi := (415870621 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1689) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1689) = 1/(1689 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-415870621 / 1000000000) (-20793531 / 50000000) (Real.log (1689 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (292407219 / 1000000000) ≤ -Real.log (5120 / 6859) ∧
    -Real.log (5120 / 6859) ≤ (14620361 / 50000000) := by
  have h := checkLog_sound (w := (1739 / 11979)) (n := 12)
    (lo := (292407219 / 1000000000)) (hi := (14620361 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6859 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6859 / 5120) = 1/(5120 / 6859) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (292407219 / 1000000000) (14620361 / 50000000) (Real.log (6859 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6859 / 5120) = -Real.log (5120 / 6859) := by
    rw [show ((6859 / 5120) : ℝ) = ((5120 / 6859) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (82996583 / 200000000) ≤ -Real.log (3381 / 5120) ∧
    -Real.log (3381 / 5120) ≤ (103745729 / 250000000) := by
  have h := checkLog_sound (w := (1739 / 8501)) (n := 12)
    (lo := (82996583 / 200000000)) (hi := (103745729 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3381) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3381) = 1/(3381 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-103745729 / 250000000) (-82996583 / 200000000) (Real.log (3381 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (13513979 / 62500000) ≤ -Real.log (50000 / 62069) ∧
    -Real.log (50000 / 62069) ≤ (43244733 / 200000000) := by
  have h := checkLog_sound (w := (12069 / 112069)) (n := 12)
    (lo := (13513979 / 62500000)) (hi := (43244733 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62069 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62069 / 50000) = 1/(50000 / 62069) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (13513979 / 62500000) (43244733 / 200000000) (Real.log (62069 / 50000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (62069 / 50000) = -Real.log (50000 / 62069) := by
    rw [show ((62069 / 50000) : ℝ) = ((50000 / 62069) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (55250857 / 200000000) ≤ -Real.log (37931 / 50000) ∧
    -Real.log (37931 / 50000) ≤ (138127143 / 500000000) := by
  have h := checkLog_sound (w := (12069 / 87931)) (n := 12)
    (lo := (55250857 / 200000000)) (hi := (138127143 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 37931) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 37931) = 1/(37931 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-138127143 / 500000000) (-55250857 / 200000000) (Real.log (37931 / 50000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (4331271 / 20000000) ≤ -Real.log (500000 / 620901) ∧
    -Real.log (500000 / 620901) ≤ (216563551 / 1000000000) := by
  have h := checkLog_sound (w := (120901 / 1120901)) (n := 12)
    (lo := (4331271 / 20000000)) (hi := (216563551 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((620901 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(620901 / 500000) = 1/(500000 / 620901) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (4331271 / 20000000) (216563551 / 1000000000) (Real.log (620901 / 500000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (620901 / 500000) = -Real.log (500000 / 620901) := by
    rw [show ((620901 / 500000) : ℝ) = ((500000 / 620901) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (276810713 / 1000000000) ≤ -Real.log (379099 / 500000) ∧
    -Real.log (379099 / 500000) ≤ (138405357 / 500000000) := by
  have h := checkLog_sound (w := (120901 / 879099)) (n := 12)
    (lo := (276810713 / 1000000000)) (hi := (138405357 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 379099) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 379099) = 1/(379099 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-138405357 / 500000000) (-276810713 / 1000000000) (Real.log (379099 / 500000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (159975397 / 1000000000) ≤ -Real.log (500000 / 586741) ∧
    -Real.log (500000 / 586741) ≤ (79987699 / 500000000) := by
  have h := checkLog_sound (w := (86741 / 1086741)) (n := 12)
    (lo := (159975397 / 1000000000)) (hi := (79987699 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((586741 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(586741 / 500000) = 1/(500000 / 586741) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (159975397 / 1000000000) (79987699 / 500000000) (Real.log (586741 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (586741 / 500000) = -Real.log (500000 / 586741) := by
    rw [show ((586741 / 500000) : ℝ) = ((500000 / 586741) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (190533583 / 1000000000) ≤ -Real.log (413259 / 500000) ∧
    -Real.log (413259 / 500000) ≤ (11908349 / 62500000) := by
  have h := checkLog_sound (w := (86741 / 913259)) (n := 12)
    (lo := (190533583 / 1000000000)) (hi := (11908349 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 413259) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 413259) = 1/(413259 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-11908349 / 62500000) (-190533583 / 1000000000) (Real.log (413259 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (160242089 / 1000000000) ≤ -Real.log (200000 / 234759) ∧
    -Real.log (200000 / 234759) ≤ (16024209 / 100000000) := by
  have h := checkLog_sound (w := (34759 / 434759)) (n := 12)
    (lo := (160242089 / 1000000000)) (hi := (16024209 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((234759 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(234759 / 200000) = 1/(200000 / 234759) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (160242089 / 1000000000) (16024209 / 100000000) (Real.log (234759 / 200000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (234759 / 200000) = -Real.log (200000 / 234759) := by
    rw [show ((234759 / 200000) : ℝ) = ((200000 / 234759) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (5966011 / 31250000) ≤ -Real.log (165241 / 200000) ∧
    -Real.log (165241 / 200000) ≤ (190912353 / 1000000000) := by
  have h := checkLog_sound (w := (34759 / 365241)) (n := 12)
    (lo := (5966011 / 31250000)) (hi := (190912353 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 165241) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 165241) = 1/(165241 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-190912353 / 1000000000) (-5966011 / 31250000) (Real.log (165241 / 200000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (353695067 / 500000000) ≤ -Real.log (250000000000 / 507172434191) ∧
    -Real.log (250000000000 / 507172434191) ≤ (88423767 / 125000000) := by
  have h := checkLog_sound (w := (7172434191 / 1007172434191)) (n := 12)
    (lo := (7121477 / 500000000)) (hi := (2848591 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((507172434191 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(507172434191 / 500000000000) = 1/(250000000000 / 507172434191) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (353695067 / 500000000) (88423767 / 125000000) (Real.log (507172434191 / 250000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (507172434191 / 250000000000) = -Real.log (250000000000 / 507172434191) := by
    rw [show ((507172434191 / 250000000000) : ℝ) = ((250000000000 / 507172434191) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (5669721 / 8000000) ≤ -Real.log (500000000000 / 1015689757253) ∧
    -Real.log (500000000000 / 1015689757253) ≤ (708715127 / 1000000000) := by
  have h := checkLog_sound (w := (15689757253 / 2015689757253)) (n := 12)
    (lo := (3113589 / 200000000)) (hi := (7783973 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1015689757253 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1015689757253 / 1000000000000) = 1/(500000000000 / 1015689757253) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (5669721 / 8000000) (708715127 / 1000000000) (Real.log (1015689757253 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (1015689757253 / 500000000000) = -Real.log (500000000000 / 1015689757253) := by
    rw [show ((1015689757253 / 500000000000) : ℝ) = ((500000000000 / 1015689757253) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (492477949 / 1000000000) ≤ -Real.log (50000000000 / 81818301653) ∧
    -Real.log (50000000000 / 81818301653) ≤ (9849559 / 20000000) := by
  have h := checkLog_sound (w := (31818301653 / 131818301653)) (n := 12)
    (lo := (492477949 / 1000000000)) (hi := (9849559 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((81818301653 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(81818301653 / 50000000000) = 1/(50000000000 / 81818301653) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (492477949 / 1000000000) (9849559 / 20000000) (Real.log (81818301653 / 50000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (81818301653 / 50000000000) = -Real.log (50000000000 / 81818301653) := by
    rw [show ((81818301653 / 50000000000) : ℝ) = ((50000000000 / 81818301653) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (61671783 / 125000000) ≤ -Real.log (62500000000 / 102364586823) ∧
    -Real.log (62500000000 / 102364586823) ≤ (98674853 / 200000000) := by
  have h := checkLog_sound (w := (39864586823 / 164864586823)) (n := 12)
    (lo := (61671783 / 125000000)) (hi := (98674853 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((102364586823 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(102364586823 / 62500000000) = 1/(62500000000 / 102364586823) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (61671783 / 125000000) (98674853 / 200000000) (Real.log (102364586823 / 62500000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (102364586823 / 62500000000) = -Real.log (62500000000 / 102364586823) := by
    rw [show ((102364586823 / 62500000000) : ℝ) = ((62500000000 / 102364586823) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (17525449 / 50000000) ≤ -Real.log (500000000000 / 709895005311) ∧
    -Real.log (500000000000 / 709895005311) ≤ (350508981 / 1000000000) := by
  have h := checkLog_sound (w := (209895005311 / 1209895005311)) (n := 12)
    (lo := (17525449 / 50000000)) (hi := (350508981 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((709895005311 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(709895005311 / 500000000000) = 1/(500000000000 / 709895005311) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (17525449 / 50000000) (350508981 / 1000000000) (Real.log (709895005311 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (709895005311 / 500000000000) = -Real.log (500000000000 / 709895005311) := by
    rw [show ((709895005311 / 500000000000) : ℝ) = ((500000000000 / 709895005311) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (351154441 / 1000000000) ≤ -Real.log (100000000000 / 142070672533) ∧
    -Real.log (100000000000 / 142070672533) ≤ (175577221 / 500000000) := by
  have h := checkLog_sound (w := (42070672533 / 242070672533)) (n := 12)
    (lo := (351154441 / 1000000000)) (hi := (175577221 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((142070672533 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(142070672533 / 100000000000) = 1/(100000000000 / 142070672533) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (351154441 / 1000000000) (175577221 / 500000000) (Real.log (142070672533 / 100000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (142070672533 / 100000000000) = -Real.log (100000000000 / 142070672533) := by
    rw [show ((142070672533 / 100000000000) : ℝ) = ((100000000000 / 142070672533) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (15335131 / 500000000) ≤ -Real.log (38791811919 / 40000000000) ∧
    -Real.log (38791811919 / 40000000000) ≤ (30670263 / 1000000000) := by
  have h := checkLog_sound (w := (1208188081 / 78791811919)) (n := 12)
    (lo := (15335131 / 500000000)) (hi := (30670263 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 38791811919) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 38791811919) = 1/(38791811919 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-30670263 / 1000000000) (-15335131 / 500000000) (Real.log (38791811919 / 40000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (6111637 / 200000000) ≤ -Real.log (242475998919 / 250000000000) ∧
    -Real.log (242475998919 / 250000000000) ≤ (15279093 / 500000000) := by
  have h := checkLog_sound (w := (7524001081 / 492475998919)) (n := 12)
    (lo := (6111637 / 200000000)) (hi := (15279093 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 242475998919) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 242475998919) = 1/(242475998919 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-15279093 / 500000000) (-6111637 / 200000000) (Real.log (242475998919 / 250000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell153
