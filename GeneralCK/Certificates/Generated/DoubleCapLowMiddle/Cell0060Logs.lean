import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0060
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

theorem reflection_log_1_neg : (678117811 / 1000000000) ≤ -Real.log (20480 / 40349) ∧
    -Real.log (20480 / 40349) ≤ (169529453 / 250000000) := by
  have h := checkLog_sound (w := (19869 / 60829)) (n := 12)
    (lo := (678117811 / 1000000000)) (hi := (169529453 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40349 / 20480) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40349 / 20480) = 1/(20480 / 40349) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (678117811 / 1000000000) (169529453 / 250000000) (Real.log (40349 / 20480)) := by
  have h := reflection_log_1_neg
  have he : Real.log (40349 / 20480) = -Real.log (20480 / 40349) := by
    rw [show ((40349 / 20480) : ℝ) = ((20480 / 40349) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (3512107117 / 1000000000) ≤ -Real.log (611 / 20480) ∧
    -Real.log (611 / 20480) ≤ (3512107123 / 1000000000) := by
  have h := checkLog_sound (w := (29 / 1251)) (n := 12)
    (lo := (46371217 / 1000000000)) (hi := (23185609 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 611) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(640 / 611) = 1/(611 / 20480) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-3512107123 / 1000000000) (-3512107117 / 1000000000) (Real.log (611 / 20480)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (169505907 / 250000000) ≤ -Real.log (51200 / 100863) ∧
    -Real.log (51200 / 100863) ≤ (678023629 / 1000000000) := by
  have h := checkLog_sound (w := (49663 / 152063)) (n := 12)
    (lo := (169505907 / 250000000)) (hi := (678023629 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100863 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100863 / 51200) = 1/(51200 / 100863) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (169505907 / 250000000) (678023629 / 1000000000) (Real.log (100863 / 51200)) := by
  have h := reflection_log_3_neg
  have he : Real.log (100863 / 51200) = -Real.log (51200 / 100863) := by
    rw [show ((100863 / 51200) : ℝ) = ((51200 / 100863) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (438238383 / 125000000) ≤ -Real.log (1537 / 51200) ∧
    -Real.log (1537 / 51200) ≤ (350590707 / 100000000) := by
  have h := checkLog_sound (w := (63 / 3137)) (n := 12)
    (lo := (10042791 / 250000000)) (hi := (8034233 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1537) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(1600 / 1537) = 1/(1537 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-350590707 / 100000000) (-438238383 / 125000000) (Real.log (1537 / 51200)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (165714777 / 250000000) ≤ -Real.log (10240 / 19869) ∧
    -Real.log (10240 / 19869) ≤ (662859109 / 1000000000) := by
  have h := checkLog_sound (w := (9629 / 30109)) (n := 12)
    (lo := (165714777 / 250000000)) (hi := (662859109 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((19869 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(19869 / 10240) = 1/(10240 / 19869) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (165714777 / 250000000) (662859109 / 1000000000) (Real.log (19869 / 10240)) := by
  have h := reflection_log_5_neg
  have he : Real.log (19869 / 10240) = -Real.log (10240 / 19869) := by
    rw [show ((19869 / 10240) : ℝ) = ((10240 / 19869) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (2818959937 / 1000000000) ≤ -Real.log (611 / 10240) ∧
    -Real.log (611 / 10240) ≤ (1409479971 / 500000000) := by
  have h := checkLog_sound (w := (29 / 1251)) (n := 12)
    (lo := (46371217 / 1000000000)) (hi := (23185609 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 611) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(640 / 611) = 1/(611 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1409479971 / 500000000) (-2818959937 / 1000000000) (Real.log (611 / 10240)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (662667837 / 1000000000) ≤ -Real.log (25600 / 49663) ∧
    -Real.log (25600 / 49663) ≤ (331333919 / 500000000) := by
  have h := checkLog_sound (w := (24063 / 75263)) (n := 12)
    (lo := (662667837 / 1000000000)) (hi := (331333919 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49663 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49663 / 25600) = 1/(25600 / 49663) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (662667837 / 1000000000) (331333919 / 500000000) (Real.log (49663 / 25600)) := by
  have h := reflection_log_7_neg
  have he : Real.log (49663 / 25600) = -Real.log (25600 / 49663) := by
    rw [show ((49663 / 25600) : ℝ) = ((25600 / 49663) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (703189971 / 250000000) ≤ -Real.log (1537 / 25600) ∧
    -Real.log (1537 / 25600) ≤ (2812759889 / 1000000000) := by
  have h := checkLog_sound (w := (63 / 3137)) (n := 12)
    (lo := (10042791 / 250000000)) (hi := (8034233 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1537) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1600 / 1537) = 1/(1537 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-2812759889 / 1000000000) (-703189971 / 250000000) (Real.log (1537 / 25600)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (680519789 / 1000000000) ≤ -Real.log (125000 / 246863) ∧
    -Real.log (125000 / 246863) ≤ (68051979 / 100000000) := by
  have h := checkLog_sound (w := (121863 / 371863)) (n := 12)
    (lo := (680519789 / 1000000000)) (hi := (68051979 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((246863 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(246863 / 125000) = 1/(125000 / 246863) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (680519789 / 1000000000) (68051979 / 100000000) (Real.log (246863 / 125000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (246863 / 125000) = -Real.log (125000 / 246863) := by
    rw [show ((246863 / 125000) : ℝ) = ((125000 / 246863) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (737009361 / 200000000) ≤ -Real.log (3137 / 125000) ∧
    -Real.log (3137 / 125000) ≤ (3685046811 / 1000000000) := by
  have h := checkLog_sound (w := (3077 / 28173)) (n := 12)
    (lo := (43862181 / 200000000)) (hi := (109655453 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 12548) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 12548) = 1/(3137 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-3685046811 / 1000000000) (-737009361 / 200000000) (Real.log (3137 / 125000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (680595233 / 1000000000) ≤ -Real.log (1000000 / 1975053) ∧
    -Real.log (1000000 / 1975053) ≤ (340297617 / 500000000) := by
  have h := checkLog_sound (w := (975053 / 2975053)) (n := 12)
    (lo := (680595233 / 1000000000)) (hi := (340297617 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1975053 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1975053 / 1000000) = 1/(1000000 / 1975053) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (680595233 / 1000000000) (340297617 / 500000000) (Real.log (1975053 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1975053 / 1000000) = -Real.log (1000000 / 1975053) := by
    rw [show ((1975053 / 1000000) : ℝ) = ((1000000 / 1975053) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (3691001701 / 1000000000) ≤ -Real.log (24947 / 1000000) ∧
    -Real.log (24947 / 1000000) ≤ (3691001707 / 1000000000) := by
  have h := checkLog_sound (w := (6303 / 56197)) (n := 12)
    (lo := (225265801 / 1000000000)) (hi := (112632901 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 24947) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 24947) = 1/(24947 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-3691001707 / 1000000000) (-3691001701 / 1000000000) (Real.log (24947 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (34022141 / 50000000) ≤ -Real.log (31250 / 61711) ∧
    -Real.log (31250 / 61711) ≤ (680442821 / 1000000000) := by
  have h := checkLog_sound (w := (30461 / 92961)) (n := 12)
    (lo := (34022141 / 50000000)) (hi := (680442821 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((61711 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(61711 / 31250) = 1/(31250 / 61711) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (34022141 / 50000000) (680442821 / 1000000000) (Real.log (61711 / 31250)) := by
  have h := reflection_log_13_neg
  have he : Real.log (61711 / 31250) = -Real.log (31250 / 61711) := by
    rw [show ((61711 / 31250) : ℝ) = ((31250 / 61711) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (3679008331 / 1000000000) ≤ -Real.log (789 / 31250) ∧
    -Real.log (789 / 31250) ≤ (3679008337 / 1000000000) := by
  have h := checkLog_sound (w := (3001 / 28249)) (n := 12)
    (lo := (213272431 / 1000000000)) (hi := (13329527 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 12624) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 12624) = 1/(789 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-3679008337 / 1000000000) (-3679008331 / 1000000000) (Real.log (789 / 31250)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (680519283 / 1000000000) ≤ -Real.log (1000000 / 1974903) ∧
    -Real.log (1000000 / 1974903) ≤ (170129821 / 250000000) := by
  have h := checkLog_sound (w := (974903 / 2974903)) (n := 12)
    (lo := (680519283 / 1000000000)) (hi := (170129821 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1974903 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1974903 / 1000000) = 1/(1000000 / 1974903) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (680519283 / 1000000000) (170129821 / 250000000) (Real.log (1974903 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1974903 / 1000000) = -Real.log (1000000 / 1974903) := by
    rw [show ((1974903 / 1000000) : ℝ) = ((1000000 / 1974903) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (3685006959 / 1000000000) ≤ -Real.log (25097 / 1000000) ∧
    -Real.log (25097 / 1000000) ≤ (737001393 / 200000000) := by
  have h := checkLog_sound (w := (6153 / 56347)) (n := 12)
    (lo := (219271059 / 1000000000)) (hi := (10963553 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 25097) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 25097) = 1/(25097 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-737001393 / 200000000) (-3685006959 / 1000000000) (Real.log (25097 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (2182783297 / 500000000) ≤ -Real.log (500000000000 / 39346987567739) ∧
    -Real.log (500000000000 / 39346987567739) ≤ (4365566601 / 1000000000) := by
  have h := checkLog_sound (w := (7346987567739 / 71346987567739)) (n := 12)
    (lo := (103341757 / 500000000)) (hi := (41336703 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((39346987567739 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(39346987567739 / 32000000000000) = 1/(500000000000 / 39346987567739) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (2182783297 / 500000000) (4365566601 / 1000000000) (Real.log (39346987567739 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (39346987567739 / 500000000000) = -Real.log (500000000000 / 39346987567739) := by
    rw [show ((39346987567739 / 500000000000) : ℝ) = ((500000000000 / 39346987567739) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (2185798467 / 500000000) ≤ -Real.log (100000000000 / 7916996031587) ∧
    -Real.log (100000000000 / 7916996031587) ≤ (4371596941 / 1000000000) := by
  have h := checkLog_sound (w := (1516996031587 / 14316996031587)) (n := 12)
    (lo := (106356927 / 500000000)) (hi := (42542771 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7916996031587 / 6400000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(7916996031587 / 6400000000000) = 1/(100000000000 / 7916996031587) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (2185798467 / 500000000) (4371596941 / 1000000000) (Real.log (7916996031587 / 100000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (7916996031587 / 100000000000) = -Real.log (100000000000 / 7916996031587) := by
    rw [show ((7916996031587 / 100000000000) : ℝ) = ((100000000000 / 7916996031587) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (4359451151 / 1000000000) ≤ -Real.log (31250000000 / 2444193599493) ∧
    -Real.log (31250000000 / 2444193599493) ≤ (2179725579 / 500000000) := by
  have h := checkLog_sound (w := (444193599493 / 4444193599493)) (n := 12)
    (lo := (200568071 / 1000000000)) (hi := (25071009 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2444193599493 / 2000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(2444193599493 / 2000000000000) = 1/(31250000000 / 2444193599493) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (4359451151 / 1000000000) (2179725579 / 500000000) (Real.log (2444193599493 / 31250000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (2444193599493 / 31250000000) = -Real.log (31250000000 / 2444193599493) := by
    rw [show ((2444193599493 / 31250000000) : ℝ) = ((31250000000 / 2444193599493) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (4365526241 / 1000000000) ≤ -Real.log (125000000000 / 9836349962147) ∧
    -Real.log (125000000000 / 9836349962147) ≤ (545690781 / 125000000) := by
  have h := checkLog_sound (w := (1836349962147 / 17836349962147)) (n := 12)
    (lo := (206643161 / 1000000000)) (hi := (103321581 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9836349962147 / 8000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(9836349962147 / 8000000000000) = 1/(125000000000 / 9836349962147) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (4365526241 / 1000000000) (545690781 / 125000000) (Real.log (9836349962147 / 125000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (9836349962147 / 125000000000) = -Real.log (125000000000 / 9836349962147) := by
    rw [show ((9836349962147 / 125000000000) : ℝ) = ((125000000000 / 9836349962147) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0060
