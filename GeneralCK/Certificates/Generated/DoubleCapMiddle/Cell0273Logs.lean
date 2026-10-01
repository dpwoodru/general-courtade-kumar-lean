import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0273
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

theorem reflection_log_1_neg : (232320067 / 1000000000) ≤ -Real.log (5120 / 6459) ∧
    -Real.log (5120 / 6459) ≤ (58080017 / 250000000) := by
  have h := checkLog_sound (w := (1339 / 11579)) (n := 12)
    (lo := (232320067 / 1000000000)) (hi := (58080017 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6459 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6459 / 5120) = 1/(5120 / 6459) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (232320067 / 1000000000) (58080017 / 250000000) (Real.log (6459 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6459 / 5120) = -Real.log (5120 / 6459) := by
    rw [show ((6459 / 5120) : ℝ) = ((5120 / 6459) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (151582957 / 500000000) ≤ -Real.log (3781 / 5120) ∧
    -Real.log (3781 / 5120) ≤ (60633183 / 200000000) := by
  have h := checkLog_sound (w := (1339 / 8901)) (n := 12)
    (lo := (151582957 / 500000000)) (hi := (60633183 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3781) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3781) = 1/(3781 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-60633183 / 200000000) (-151582957 / 500000000) (Real.log (3781 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (231855491 / 1000000000) ≤ -Real.log (640 / 807) ∧
    -Real.log (640 / 807) ≤ (57963873 / 250000000) := by
  have h := checkLog_sound (w := (167 / 1447)) (n := 12)
    (lo := (231855491 / 1000000000)) (hi := (57963873 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((807 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(807 / 640) = 1/(640 / 807) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (231855491 / 1000000000) (57963873 / 250000000) (Real.log (807 / 640)) := by
  have h := reflection_log_3_neg
  have he : Real.log (807 / 640) = -Real.log (640 / 807) := by
    rw [show ((807 / 640) : ℝ) = ((640 / 807) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (302372787 / 1000000000) ≤ -Real.log (473 / 640) ∧
    -Real.log (473 / 640) ≤ (75593197 / 250000000) := by
  have h := checkLog_sound (w := (167 / 1113)) (n := 12)
    (lo := (302372787 / 1000000000)) (hi := (75593197 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 473) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 473) = 1/(473 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-75593197 / 250000000) (-302372787 / 1000000000) (Real.log (473 / 640)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (420712851 / 1000000000) ≤ -Real.log (2560 / 3899) ∧
    -Real.log (2560 / 3899) ≤ (105178213 / 250000000) := by
  have h := checkLog_sound (w := (1339 / 6459)) (n := 12)
    (lo := (420712851 / 1000000000)) (hi := (105178213 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3899 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3899 / 2560) = 1/(2560 / 3899) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (420712851 / 1000000000) (105178213 / 250000000) (Real.log (3899 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (3899 / 2560) = -Real.log (2560 / 3899) := by
    rw [show ((3899 / 2560) : ℝ) = ((2560 / 3899) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (370168531 / 500000000) ≤ -Real.log (1221 / 2560) ∧
    -Real.log (1221 / 2560) ≤ (92542133 / 125000000) := by
  have h := checkLog_sound (w := (59 / 2501)) (n := 12)
    (lo := (23594941 / 500000000)) (hi := (47189883 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 1221) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 1221) = 1/(1221 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-92542133 / 125000000) (-370168531 / 500000000) (Real.log (1221 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (419943127 / 1000000000) ≤ -Real.log (320 / 487) ∧
    -Real.log (320 / 487) ≤ (52492891 / 125000000) := by
  have h := checkLog_sound (w := (167 / 807)) (n := 12)
    (lo := (419943127 / 1000000000)) (hi := (52492891 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((487 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(487 / 320) = 1/(320 / 487) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (419943127 / 1000000000) (52492891 / 125000000) (Real.log (487 / 320)) := by
  have h := reflection_log_7_neg
  have he : Real.log (487 / 320) = -Real.log (320 / 487) := by
    rw [show ((487 / 320) : ℝ) = ((320 / 487) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (737883073 / 1000000000) ≤ -Real.log (153 / 320) ∧
    -Real.log (153 / 320) ≤ (29515323 / 40000000) := by
  have h := checkLog_sound (w := (7 / 313)) (n := 12)
    (lo := (44735893 / 1000000000)) (hi := (22367947 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 153) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(160 / 153) = 1/(153 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-29515323 / 40000000) (-737883073 / 1000000000) (Real.log (153 / 320)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (63511029 / 200000000) ≤ -Real.log (200000 / 274753) ∧
    -Real.log (200000 / 274753) ≤ (158777573 / 500000000) := by
  have h := checkLog_sound (w := (74753 / 474753)) (n := 12)
    (lo := (63511029 / 200000000)) (hi := (158777573 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((274753 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(274753 / 200000) = 1/(200000 / 274753) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (63511029 / 200000000) (158777573 / 500000000) (Real.log (274753 / 200000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (274753 / 200000) = -Real.log (200000 / 274753) := by
    rw [show ((274753 / 200000) : ℝ) = ((200000 / 274753) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (234014789 / 500000000) ≤ -Real.log (125247 / 200000) ∧
    -Real.log (125247 / 200000) ≤ (468029579 / 1000000000) := by
  have h := checkLog_sound (w := (74753 / 325247)) (n := 12)
    (lo := (234014789 / 500000000)) (hi := (468029579 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 125247) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 125247) = 1/(125247 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-468029579 / 1000000000) (-234014789 / 500000000) (Real.log (125247 / 200000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (318184603 / 1000000000) ≤ -Real.log (100000 / 137463) ∧
    -Real.log (100000 / 137463) ≤ (79546151 / 250000000) := by
  have h := checkLog_sound (w := (37463 / 237463)) (n := 12)
    (lo := (318184603 / 1000000000)) (hi := (79546151 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((137463 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(137463 / 100000) = 1/(100000 / 137463) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (318184603 / 1000000000) (79546151 / 250000000) (Real.log (137463 / 100000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (137463 / 100000) = -Real.log (100000 / 137463) := by
    rw [show ((137463 / 100000) : ℝ) = ((100000 / 137463) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (117352951 / 250000000) ≤ -Real.log (62537 / 100000) ∧
    -Real.log (62537 / 100000) ≤ (93882361 / 200000000) := by
  have h := checkLog_sound (w := (37463 / 162537)) (n := 12)
    (lo := (117352951 / 250000000)) (hi := (93882361 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 62537) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 62537) = 1/(62537 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-93882361 / 200000000) (-117352951 / 250000000) (Real.log (62537 / 100000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (9715149 / 40000000) ≤ -Real.log (500000 / 637457) ∧
    -Real.log (500000 / 637457) ≤ (121439363 / 500000000) := by
  have h := checkLog_sound (w := (137457 / 1137457)) (n := 12)
    (lo := (9715149 / 40000000)) (hi := (121439363 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((637457 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(637457 / 500000) = 1/(500000 / 637457) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (9715149 / 40000000) (121439363 / 500000000) (Real.log (637457 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (637457 / 500000) = -Real.log (500000 / 637457) := by
    rw [show ((637457 / 500000) : ℝ) = ((500000 / 637457) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (32146501 / 100000000) ≤ -Real.log (362543 / 500000) ∧
    -Real.log (362543 / 500000) ≤ (321465011 / 1000000000) := by
  have h := checkLog_sound (w := (137457 / 862543)) (n := 12)
    (lo := (32146501 / 100000000)) (hi := (321465011 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 362543) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 362543) = 1/(362543 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-321465011 / 1000000000) (-32146501 / 100000000) (Real.log (362543 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (15213639 / 62500000) ≤ -Real.log (500000 / 637801) ∧
    -Real.log (500000 / 637801) ≤ (9736729 / 40000000) := by
  have h := checkLog_sound (w := (137801 / 1137801)) (n := 12)
    (lo := (15213639 / 62500000)) (hi := (9736729 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((637801 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(637801 / 500000) = 1/(500000 / 637801) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (15213639 / 62500000) (9736729 / 40000000) (Real.log (637801 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (637801 / 500000) = -Real.log (500000 / 637801) := by
    rw [show ((637801 / 500000) : ℝ) = ((500000 / 637801) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (322414313 / 1000000000) ≤ -Real.log (362199 / 500000) ∧
    -Real.log (362199 / 500000) ≤ (161207157 / 500000000) := by
  have h := checkLog_sound (w := (137801 / 862199)) (n := 12)
    (lo := (322414313 / 1000000000)) (hi := (161207157 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 362199) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 362199) = 1/(362199 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-161207157 / 500000000) (-322414313 / 1000000000) (Real.log (362199 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (196396181 / 250000000) ≤ -Real.log (500000000000 / 1096844635001) ∧
    -Real.log (500000000000 / 1096844635001) ≤ (392792363 / 500000000) := by
  have h := checkLog_sound (w := (96844635001 / 2096844635001)) (n := 12)
    (lo := (11554693 / 125000000)) (hi := (18487509 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1096844635001 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1096844635001 / 1000000000000) = 1/(500000000000 / 1096844635001) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (196396181 / 250000000) (392792363 / 500000000) (Real.log (1096844635001 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1096844635001 / 500000000000) = -Real.log (500000000000 / 1096844635001) := by
    rw [show ((1096844635001 / 500000000000) : ℝ) = ((500000000000 / 1096844635001) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (787596407 / 1000000000) ≤ -Real.log (500000000000 / 1099053360411) ∧
    -Real.log (500000000000 / 1099053360411) ≤ (787596409 / 1000000000) := by
  have h := checkLog_sound (w := (99053360411 / 2099053360411)) (n := 12)
    (lo := (94449227 / 1000000000)) (hi := (23612307 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1099053360411 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1099053360411 / 1000000000000) = 1/(500000000000 / 1099053360411) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (787596407 / 1000000000) (787596409 / 1000000000) (Real.log (1099053360411 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1099053360411 / 500000000000) = -Real.log (500000000000 / 1099053360411) := by
    rw [show ((1099053360411 / 500000000000) : ℝ) = ((500000000000 / 1099053360411) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (112868747 / 200000000) ≤ -Real.log (500000000000 / 879146749489) ∧
    -Real.log (500000000000 / 879146749489) ≤ (70542967 / 125000000) := by
  have h := checkLog_sound (w := (379146749489 / 1379146749489)) (n := 12)
    (lo := (112868747 / 200000000)) (hi := (70542967 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((879146749489 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(879146749489 / 500000000000) = 1/(500000000000 / 879146749489) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (112868747 / 200000000) (70542967 / 125000000) (Real.log (879146749489 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (879146749489 / 500000000000) = -Real.log (500000000000 / 879146749489) := by
    rw [show ((879146749489 / 500000000000) : ℝ) = ((500000000000 / 879146749489) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (565832537 / 1000000000) ≤ -Real.log (20000000000 / 35218263993) ∧
    -Real.log (20000000000 / 35218263993) ≤ (282916269 / 500000000) := by
  have h := checkLog_sound (w := (15218263993 / 55218263993)) (n := 12)
    (lo := (565832537 / 1000000000)) (hi := (282916269 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((35218263993 / 20000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(35218263993 / 20000000000) = 1/(20000000000 / 35218263993) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (565832537 / 1000000000) (282916269 / 500000000) (Real.log (35218263993 / 20000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (35218263993 / 20000000000) = -Real.log (20000000000 / 35218263993) := by
    rw [show ((35218263993 / 20000000000) : ℝ) = ((20000000000 / 35218263993) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0273
