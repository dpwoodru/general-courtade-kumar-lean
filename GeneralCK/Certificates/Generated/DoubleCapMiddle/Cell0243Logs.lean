import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0243
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

theorem reflection_log_1_neg : (246157927 / 1000000000) ≤ -Real.log (5120 / 6549) ∧
    -Real.log (5120 / 6549) ≤ (30769741 / 125000000) := by
  have h := checkLog_sound (w := (1429 / 11669)) (n := 12)
    (lo := (246157927 / 1000000000)) (hi := (30769741 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6549 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6549 / 5120) = 1/(5120 / 6549) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (246157927 / 1000000000) (30769741 / 125000000) (Real.log (6549 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6549 / 5120) = -Real.log (5120 / 6549) := by
    rw [show ((6549 / 5120) : ℝ) = ((5120 / 6549) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (65451403 / 200000000) ≤ -Real.log (3691 / 5120) ∧
    -Real.log (3691 / 5120) ≤ (40907127 / 125000000) := by
  have h := checkLog_sound (w := (1429 / 8811)) (n := 12)
    (lo := (65451403 / 200000000)) (hi := (40907127 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3691) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3691) = 1/(3691 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-40907127 / 125000000) (-65451403 / 200000000) (Real.log (3691 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (245699737 / 1000000000) ≤ -Real.log (2560 / 3273) ∧
    -Real.log (2560 / 3273) ≤ (122849869 / 500000000) := by
  have h := checkLog_sound (w := (713 / 5833)) (n := 12)
    (lo := (245699737 / 1000000000)) (hi := (122849869 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3273 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3273 / 2560) = 1/(2560 / 3273) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (245699737 / 1000000000) (122849869 / 500000000) (Real.log (3273 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3273 / 2560) = -Real.log (2560 / 3273) := by
    rw [show ((3273 / 2560) : ℝ) = ((2560 / 3273) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (326444557 / 1000000000) ≤ -Real.log (1847 / 2560) ∧
    -Real.log (1847 / 2560) ≤ (163222279 / 500000000) := by
  have h := checkLog_sound (w := (713 / 4407)) (n := 12)
    (lo := (326444557 / 1000000000)) (hi := (163222279 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1847) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1847) = 1/(1847 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-163222279 / 500000000) (-326444557 / 1000000000) (Real.log (1847 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (221766657 / 500000000) ≤ -Real.log (2560 / 3989) ∧
    -Real.log (2560 / 3989) ≤ (88706663 / 200000000) := by
  have h := checkLog_sound (w := (1429 / 6549)) (n := 12)
    (lo := (221766657 / 500000000)) (hi := (88706663 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3989 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3989 / 2560) = 1/(2560 / 3989) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (221766657 / 500000000) (88706663 / 200000000) (Real.log (3989 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (3989 / 2560) = -Real.log (2560 / 3989) := by
    rw [show ((3989 / 2560) : ℝ) = ((2560 / 3989) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (40845253 / 50000000) ≤ -Real.log (1131 / 2560) ∧
    -Real.log (1131 / 2560) ≤ (408452531 / 500000000) := by
  have h := checkLog_sound (w := (149 / 2411)) (n := 12)
    (lo := (3093947 / 25000000)) (hi := (123757881 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 1131) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 1131) = 1/(1131 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-408452531 / 500000000) (-40845253 / 50000000) (Real.log (1131 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (442780963 / 1000000000) ≤ -Real.log (1280 / 1993) ∧
    -Real.log (1280 / 1993) ≤ (110695241 / 250000000) := by
  have h := checkLog_sound (w := (713 / 3273)) (n := 12)
    (lo := (442780963 / 1000000000)) (hi := (110695241 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1993 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1993 / 1280) = 1/(1280 / 1993) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (442780963 / 1000000000) (110695241 / 250000000) (Real.log (1993 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1993 / 1280) = -Real.log (1280 / 1993) := by
    rw [show ((1993 / 1280) : ℝ) = ((1280 / 1993) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (203564013 / 250000000) ≤ -Real.log (567 / 1280) ∧
    -Real.log (567 / 1280) ≤ (407128027 / 500000000) := by
  have h := checkLog_sound (w := (73 / 1207)) (n := 12)
    (lo := (15138609 / 125000000)) (hi := (121108873 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 567) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 567) = 1/(567 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-407128027 / 500000000) (-203564013 / 250000000) (Real.log (567 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (67260873 / 200000000) ≤ -Real.log (200000 / 279953) ∧
    -Real.log (200000 / 279953) ≤ (168152183 / 500000000) := by
  have h := checkLog_sound (w := (79953 / 479953)) (n := 12)
    (lo := (67260873 / 200000000)) (hi := (168152183 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((279953 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(279953 / 200000) = 1/(200000 / 279953) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (67260873 / 200000000) (168152183 / 500000000) (Real.log (279953 / 200000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (279953 / 200000) = -Real.log (200000 / 279953) := by
    rw [show ((279953 / 200000) : ℝ) = ((200000 / 279953) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (510434033 / 1000000000) ≤ -Real.log (120047 / 200000) ∧
    -Real.log (120047 / 200000) ≤ (255217017 / 500000000) := by
  have h := checkLog_sound (w := (79953 / 320047)) (n := 12)
    (lo := (510434033 / 1000000000)) (hi := (255217017 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 120047) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 120047) = 1/(120047 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-255217017 / 500000000) (-510434033 / 1000000000) (Real.log (120047 / 200000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (336926419 / 1000000000) ≤ -Real.log (250000 / 350159) ∧
    -Real.log (250000 / 350159) ≤ (16846321 / 50000000) := by
  have h := checkLog_sound (w := (100159 / 600159)) (n := 12)
    (lo := (336926419 / 1000000000)) (hi := (16846321 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((350159 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(350159 / 250000) = 1/(250000 / 350159) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (336926419 / 1000000000) (16846321 / 50000000) (Real.log (350159 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (350159 / 250000) = -Real.log (250000 / 350159) := by
    rw [show ((350159 / 250000) : ℝ) = ((250000 / 350159) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (102377237 / 200000000) ≤ -Real.log (149841 / 250000) ∧
    -Real.log (149841 / 250000) ≤ (255943093 / 500000000) := by
  have h := checkLog_sound (w := (100159 / 399841)) (n := 12)
    (lo := (102377237 / 200000000)) (hi := (255943093 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 149841) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 149841) = 1/(149841 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-255943093 / 500000000) (-102377237 / 200000000) (Real.log (149841 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (16192719 / 62500000) ≤ -Real.log (500000 / 647871) ∧
    -Real.log (500000 / 647871) ≤ (51816701 / 200000000) := by
  have h := checkLog_sound (w := (147871 / 1147871)) (n := 12)
    (lo := (16192719 / 62500000)) (hi := (51816701 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((647871 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(647871 / 500000) = 1/(500000 / 647871) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (16192719 / 62500000) (51816701 / 200000000) (Real.log (647871 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (647871 / 500000) = -Real.log (500000 / 647871) := by
    rw [show ((647871 / 500000) : ℝ) = ((500000 / 647871) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (21913157 / 62500000) ≤ -Real.log (352129 / 500000) ∧
    -Real.log (352129 / 500000) ≤ (350610513 / 1000000000) := by
  have h := checkLog_sound (w := (147871 / 852129)) (n := 12)
    (lo := (21913157 / 62500000)) (hi := (350610513 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 352129) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 352129) = 1/(352129 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-350610513 / 1000000000) (-21913157 / 62500000) (Real.log (352129 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (51925489 / 200000000) ≤ -Real.log (1000000 / 1296447) ∧
    -Real.log (1000000 / 1296447) ≤ (129813723 / 500000000) := by
  have h := checkLog_sound (w := (296447 / 2296447)) (n := 12)
    (lo := (51925489 / 200000000)) (hi := (129813723 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1296447 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1296447 / 1000000) = 1/(1000000 / 1296447) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (51925489 / 200000000) (129813723 / 500000000) (Real.log (1296447 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1296447 / 1000000) = -Real.log (1000000 / 1296447) := by
    rw [show ((1296447 / 1000000) : ℝ) = ((1000000 / 1296447) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (351612067 / 1000000000) ≤ -Real.log (703553 / 1000000) ∧
    -Real.log (703553 / 1000000) ≤ (87903017 / 250000000) := by
  have h := checkLog_sound (w := (296447 / 1703553)) (n := 12)
    (lo := (351612067 / 1000000000)) (hi := (87903017 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 703553) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 703553) = 1/(703553 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-87903017 / 250000000) (-351612067 / 1000000000) (Real.log (703553 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (423369199 / 500000000) ≤ -Real.log (25000000000 / 58300707223) ∧
    -Real.log (25000000000 / 58300707223) ≤ (1058423 / 1250000) := by
  have h := checkLog_sound (w := (8300707223 / 108300707223)) (n := 12)
    (lo := (76795609 / 500000000)) (hi := (153591219 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((58300707223 / 50000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(58300707223 / 50000000000) = 1/(25000000000 / 58300707223) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (423369199 / 500000000) (1058423 / 1250000) (Real.log (58300707223 / 25000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (58300707223 / 25000000000) = -Real.log (25000000000 / 58300707223) := by
    rw [show ((58300707223 / 25000000000) : ℝ) = ((25000000000 / 58300707223) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (212203151 / 250000000) ≤ -Real.log (125000000000 / 292108801997) ∧
    -Real.log (125000000000 / 292108801997) ≤ (424406303 / 500000000) := by
  have h := checkLog_sound (w := (42108801997 / 542108801997)) (n := 12)
    (lo := (9729089 / 62500000)) (hi := (6226617 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((292108801997 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(292108801997 / 250000000000) = 1/(125000000000 / 292108801997) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (212203151 / 250000000) (424406303 / 500000000) (Real.log (292108801997 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (292108801997 / 125000000000) = -Real.log (125000000000 / 292108801997) := by
    rw [show ((292108801997 / 125000000000) : ℝ) = ((125000000000 / 292108801997) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (9526469 / 15625000) ≤ -Real.log (500000000000 / 919934171851) ∧
    -Real.log (500000000000 / 919934171851) ≤ (609694017 / 1000000000) := by
  have h := checkLog_sound (w := (419934171851 / 1419934171851)) (n := 12)
    (lo := (9526469 / 15625000)) (hi := (609694017 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((919934171851 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(919934171851 / 500000000000) = 1/(500000000000 / 919934171851) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (9526469 / 15625000) (609694017 / 1000000000) (Real.log (919934171851 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (919934171851 / 500000000000) = -Real.log (500000000000 / 919934171851) := by
    rw [show ((919934171851 / 500000000000) : ℝ) = ((500000000000 / 919934171851) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (611239513 / 1000000000) ≤ -Real.log (62500000000 / 115169628301) ∧
    -Real.log (62500000000 / 115169628301) ≤ (305619757 / 500000000) := by
  have h := checkLog_sound (w := (52669628301 / 177669628301)) (n := 12)
    (lo := (611239513 / 1000000000)) (hi := (305619757 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((115169628301 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(115169628301 / 62500000000) = 1/(62500000000 / 115169628301) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (611239513 / 1000000000) (305619757 / 500000000) (Real.log (115169628301 / 62500000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (115169628301 / 62500000000) = -Real.log (62500000000 / 115169628301) := by
    rw [show ((115169628301 / 62500000000) : ℝ) = ((62500000000 / 115169628301) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0243
