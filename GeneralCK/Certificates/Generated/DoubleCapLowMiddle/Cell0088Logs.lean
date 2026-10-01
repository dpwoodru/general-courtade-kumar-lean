import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0088
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

theorem reflection_log_1_neg : (134736321 / 200000000) ≤ -Real.log (25600 / 50213) ∧
    -Real.log (25600 / 50213) ≤ (336840803 / 500000000) := by
  have h := checkLog_sound (w := (24613 / 75813)) (n := 12)
    (lo := (134736321 / 200000000)) (hi := (336840803 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50213 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50213 / 25600) = 1/(25600 / 50213) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (134736321 / 200000000) (336840803 / 500000000) (Real.log (50213 / 25600)) := by
  have h := reflection_log_1_neg
  have he : Real.log (50213 / 25600) = -Real.log (25600 / 50213) := by
    rw [show ((50213 / 25600) : ℝ) = ((25600 / 50213) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (813919397 / 250000000) ≤ -Real.log (987 / 25600) ∧
    -Real.log (987 / 25600) ≤ (3255677593 / 1000000000) := by
  have h := checkLog_sound (w := (613 / 2587)) (n := 12)
    (lo := (120772217 / 250000000)) (hi := (483088869 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 987) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1600 / 987) = 1/(987 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-3255677593 / 1000000000) (-813919397 / 250000000) (Real.log (987 / 25600)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (673492393 / 1000000000) ≤ -Real.log (51200 / 100407) ∧
    -Real.log (51200 / 100407) ≤ (336746197 / 500000000) := by
  have h := checkLog_sound (w := (49207 / 151607)) (n := 12)
    (lo := (673492393 / 1000000000)) (hi := (336746197 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100407 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100407 / 51200) = 1/(51200 / 100407) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (673492393 / 1000000000) (336746197 / 500000000) (Real.log (100407 / 51200)) := by
  have h := reflection_log_3_neg
  have he : Real.log (100407 / 51200) = -Real.log (51200 / 100407) := by
    rw [show ((100407 / 51200) : ℝ) = ((51200 / 100407) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (405762311 / 125000000) ≤ -Real.log (1993 / 51200) ∧
    -Real.log (1993 / 51200) ≤ (3246098493 / 1000000000) := by
  have h := checkLog_sound (w := (1207 / 5193)) (n := 12)
    (lo := (59188721 / 125000000)) (hi := (473509769 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 1993) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3200 / 1993) = 1/(1993 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-3246098493 / 1000000000) (-405762311 / 125000000) (Real.log (1993 / 51200)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (653829587 / 1000000000) ≤ -Real.log (12800 / 24613) ∧
    -Real.log (12800 / 24613) ≤ (163457397 / 250000000) := by
  have h := checkLog_sound (w := (11813 / 37413)) (n := 12)
    (lo := (653829587 / 1000000000)) (hi := (163457397 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24613 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24613 / 12800) = 1/(12800 / 24613) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (653829587 / 1000000000) (163457397 / 250000000) (Real.log (24613 / 12800)) := by
  have h := reflection_log_5_neg
  have he : Real.log (24613 / 12800) = -Real.log (12800 / 24613) := by
    rw [show ((24613 / 12800) : ℝ) = ((12800 / 24613) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (320316301 / 125000000) ≤ -Real.log (987 / 12800) ∧
    -Real.log (987 / 12800) ≤ (640632603 / 250000000) := by
  have h := checkLog_sound (w := (613 / 2587)) (n := 12)
    (lo := (120772217 / 250000000)) (hi := (483088869 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 987) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1600 / 987) = 1/(987 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-640632603 / 250000000) (-320316301 / 125000000) (Real.log (987 / 12800)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (326721769 / 500000000) ≤ -Real.log (25600 / 49207) ∧
    -Real.log (25600 / 49207) ≤ (653443539 / 1000000000) := by
  have h := checkLog_sound (w := (23607 / 74807)) (n := 12)
    (lo := (326721769 / 500000000)) (hi := (653443539 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49207 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49207 / 25600) = 1/(25600 / 49207) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (326721769 / 500000000) (653443539 / 1000000000) (Real.log (49207 / 25600)) := by
  have h := reflection_log_7_neg
  have he : Real.log (49207 / 25600) = -Real.log (25600 / 49207) := by
    rw [show ((49207 / 25600) : ℝ) = ((25600 / 49207) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (638237827 / 250000000) ≤ -Real.log (1993 / 25600) ∧
    -Real.log (1993 / 25600) ≤ (159559457 / 62500000) := by
  have h := checkLog_sound (w := (1207 / 5193)) (n := 12)
    (lo := (59188721 / 125000000)) (hi := (473509769 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 1993) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(3200 / 1993) = 1/(1993 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-159559457 / 62500000) (-638237827 / 250000000) (Real.log (1993 / 25600)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (67696241 / 100000000) ≤ -Real.log (1000000 / 1967891) ∧
    -Real.log (1000000 / 1967891) ≤ (676962411 / 1000000000) := by
  have h := checkLog_sound (w := (967891 / 2967891)) (n := 12)
    (lo := (67696241 / 100000000)) (hi := (676962411 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1967891 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1967891 / 1000000) = 1/(1000000 / 1967891) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (67696241 / 100000000) (676962411 / 1000000000) (Real.log (1967891 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1967891 / 1000000) = -Real.log (1000000 / 1967891) := by
    rw [show ((1967891 / 1000000) : ℝ) = ((1000000 / 1967891) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (107456841 / 31250000) ≤ -Real.log (32109 / 1000000) ∧
    -Real.log (32109 / 1000000) ≤ (3438618917 / 1000000000) := by
  have h := checkLog_sound (w := (30391 / 94609)) (n := 12)
    (lo := (41626887 / 62500000)) (hi := (666030193 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 32109) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 32109) = 1/(32109 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-3438618917 / 1000000000) (-107456841 / 31250000) (Real.log (32109 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (135421953 / 200000000) ≤ -Real.log (1000000 / 1968181) ∧
    -Real.log (1000000 / 1968181) ≤ (338554883 / 500000000) := by
  have h := checkLog_sound (w := (968181 / 2968181)) (n := 12)
    (lo := (135421953 / 200000000)) (hi := (338554883 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1968181 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1968181 / 1000000) = 1/(1000000 / 1968181) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (135421953 / 200000000) (338554883 / 500000000) (Real.log (1968181 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1968181 / 1000000) = -Real.log (1000000 / 1968181) := by
    rw [show ((1968181 / 1000000) : ℝ) = ((1000000 / 1968181) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (3447691681 / 1000000000) ≤ -Real.log (31819 / 1000000) ∧
    -Real.log (31819 / 1000000) ≤ (1723845843 / 500000000) := by
  have h := checkLog_sound (w := (30681 / 94319)) (n := 12)
    (lo := (675102961 / 1000000000)) (hi := (337551481 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 31819) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 31819) = 1/(31819 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1723845843 / 500000000) (-3447691681 / 1000000000) (Real.log (31819 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (338411837 / 500000000) ≤ -Real.log (500000 / 983809) ∧
    -Real.log (500000 / 983809) ≤ (27072947 / 40000000) := by
  have h := checkLog_sound (w := (483809 / 1483809)) (n := 12)
    (lo := (338411837 / 500000000)) (hi := (27072947 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((983809 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(983809 / 500000) = 1/(500000 / 983809) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (338411837 / 500000000) (27072947 / 40000000) (Real.log (983809 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (983809 / 500000) = -Real.log (500000 / 983809) := by
    rw [show ((983809 / 500000) : ℝ) = ((500000 / 983809) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (3430152563 / 1000000000) ≤ -Real.log (16191 / 500000) ∧
    -Real.log (16191 / 500000) ≤ (428769071 / 125000000) := by
  have h := checkLog_sound (w := (15059 / 47441)) (n := 12)
    (lo := (657563843 / 1000000000)) (hi := (164390961 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 16191) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(31250 / 16191) = 1/(16191 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-428769071 / 125000000) (-3430152563 / 1000000000) (Real.log (16191 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (338487049 / 500000000) ≤ -Real.log (500000 / 983957) ∧
    -Real.log (500000 / 983957) ≤ (676974099 / 1000000000) := by
  have h := checkLog_sound (w := (483957 / 1483957)) (n := 12)
    (lo := (338487049 / 500000000)) (hi := (676974099 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((983957 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(983957 / 500000) = 1/(500000 / 983957) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (338487049 / 500000000) (676974099 / 1000000000) (Real.log (983957 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (983957 / 500000) = -Real.log (500000 / 983957) := by
    rw [show ((983957 / 500000) : ℝ) = ((500000 / 983957) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (1719667739 / 500000000) ≤ -Real.log (16043 / 500000) ∧
    -Real.log (16043 / 500000) ≤ (3439335483 / 1000000000) := by
  have h := checkLog_sound (w := (15207 / 47293)) (n := 12)
    (lo := (333373379 / 500000000)) (hi := (666746759 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 16043) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(31250 / 16043) = 1/(16043 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-3439335483 / 1000000000) (-1719667739 / 500000000) (Real.log (16043 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (2057790661 / 500000000) ≤ -Real.log (250000000000 / 15321958018001) ∧
    -Real.log (250000000000 / 15321958018001) ≤ (257223833 / 62500000) := by
  have h := checkLog_sound (w := (7321958018001 / 23321958018001)) (n := 12)
    (lo := (324922711 / 500000000)) (hi := (649845423 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15321958018001 / 8000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15321958018001 / 8000000000000) = 1/(250000000000 / 15321958018001) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (2057790661 / 500000000) (257223833 / 62500000) (Real.log (15321958018001 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (15321958018001 / 250000000000) = -Real.log (250000000000 / 15321958018001) := by
    rw [show ((15321958018001 / 250000000000) : ℝ) = ((250000000000 / 15321958018001) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (2062400723 / 500000000) ≤ -Real.log (500000000000 / 30927763286087) ∧
    -Real.log (500000000000 / 30927763286087) ≤ (1031200363 / 250000000) := by
  have h := checkLog_sound (w := (14927763286087 / 46927763286087)) (n := 12)
    (lo := (329532773 / 500000000)) (hi := (659065547 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((30927763286087 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(30927763286087 / 16000000000000) = 1/(500000000000 / 30927763286087) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (2062400723 / 500000000) (1031200363 / 250000000) (Real.log (30927763286087 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (30927763286087 / 500000000000) = -Real.log (500000000000 / 30927763286087) := by
    rw [show ((30927763286087 / 500000000000) : ℝ) = ((500000000000 / 30927763286087) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (4106976237 / 1000000000) ≤ -Real.log (62500000000 / 3797669229819) ∧
    -Real.log (62500000000 / 3797669229819) ≤ (4106976243 / 1000000000) := by
  have h := checkLog_sound (w := (1797669229819 / 5797669229819)) (n := 12)
    (lo := (641240337 / 1000000000)) (hi := (320620169 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3797669229819 / 2000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3797669229819 / 2000000000000) = 1/(62500000000 / 3797669229819) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (4106976237 / 1000000000) (4106976243 / 1000000000) (Real.log (3797669229819 / 62500000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (3797669229819 / 62500000000) = -Real.log (62500000000 / 3797669229819) := by
    rw [show ((3797669229819 / 62500000000) : ℝ) = ((62500000000 / 3797669229819) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (514538697 / 125000000) ≤ -Real.log (125000000000 / 7666560182011) ∧
    -Real.log (125000000000 / 7666560182011) ≤ (2058154791 / 500000000) := by
  have h := checkLog_sound (w := (3666560182011 / 11666560182011)) (n := 12)
    (lo := (162643419 / 250000000)) (hi := (650573677 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7666560182011 / 4000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(7666560182011 / 4000000000000) = 1/(125000000000 / 7666560182011) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (514538697 / 125000000) (2058154791 / 500000000) (Real.log (7666560182011 / 125000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (7666560182011 / 125000000000) = -Real.log (125000000000 / 7666560182011) := by
    rw [show ((7666560182011 / 125000000000) : ℝ) = ((125000000000 / 7666560182011) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0088
