import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0298
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

theorem reflection_log_1_neg : (22439277 / 100000000) ≤ -Real.log (640 / 801) ∧
    -Real.log (640 / 801) ≤ (224392771 / 1000000000) := by
  have h := checkLog_sound (w := (161 / 1441)) (n := 12)
    (lo := (22439277 / 100000000)) (hi := (224392771 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((801 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(801 / 640) = 1/(640 / 801) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (22439277 / 100000000) (224392771 / 1000000000) (Real.log (801 / 640)) := by
  have h := reflection_log_1_neg
  have he : Real.log (801 / 640) = -Real.log (640 / 801) := by
    rw [show ((801 / 640) : ℝ) = ((640 / 801) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (144883789 / 500000000) ≤ -Real.log (479 / 640) ∧
    -Real.log (479 / 640) ≤ (289767579 / 1000000000) := by
  have h := checkLog_sound (w := (161 / 1119)) (n := 12)
    (lo := (144883789 / 500000000)) (hi := (289767579 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 479) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 479) = 1/(479 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-289767579 / 1000000000) (-144883789 / 500000000) (Real.log (479 / 640)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (11207933 / 50000000) ≤ -Real.log (10240 / 12813) ∧
    -Real.log (10240 / 12813) ≤ (224158661 / 1000000000) := by
  have h := checkLog_sound (w := (2573 / 23053)) (n := 12)
    (lo := (11207933 / 50000000)) (hi := (224158661 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12813 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12813 / 10240) = 1/(10240 / 12813) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (11207933 / 50000000) (224158661 / 1000000000) (Real.log (12813 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12813 / 10240) = -Real.log (10240 / 12813) := by
    rw [show ((12813 / 10240) : ℝ) = ((10240 / 12813) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (57875243 / 200000000) ≤ -Real.log (7667 / 10240) ∧
    -Real.log (7667 / 10240) ≤ (36172027 / 125000000) := by
  have h := checkLog_sound (w := (2573 / 17907)) (n := 12)
    (lo := (57875243 / 200000000)) (hi := (36172027 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7667) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7667) = 1/(7667 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-36172027 / 125000000) (-57875243 / 200000000) (Real.log (7667 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (203773137 / 500000000) ≤ -Real.log (320 / 481) ∧
    -Real.log (320 / 481) ≤ (16301851 / 40000000) := by
  have h := checkLog_sound (w := (161 / 801)) (n := 12)
    (lo := (203773137 / 500000000)) (hi := (16301851 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((481 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(481 / 320) = 1/(320 / 481) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (203773137 / 500000000) (16301851 / 40000000) (Real.log (481 / 320)) := by
  have h := reflection_log_5_neg
  have he : Real.log (481 / 320) = -Real.log (320 / 481) := by
    rw [show ((481 / 320) : ℝ) = ((320 / 481) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (699416793 / 1000000000) ≤ -Real.log (159 / 320) ∧
    -Real.log (159 / 320) ≤ (139883359 / 200000000) := by
  have h := checkLog_sound (w := (1 / 319)) (n := 12)
    (lo := (6269613 / 1000000000)) (hi := (3134807 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 159) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(160 / 159) = 1/(159 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-139883359 / 200000000) (-699416793 / 1000000000) (Real.log (159 / 320)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (81431277 / 200000000) ≤ -Real.log (5120 / 7693) ∧
    -Real.log (5120 / 7693) ≤ (203578193 / 500000000) := by
  have h := checkLog_sound (w := (2573 / 12813)) (n := 12)
    (lo := (81431277 / 200000000)) (hi := (203578193 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7693 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7693 / 5120) = 1/(5120 / 7693) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (81431277 / 200000000) (203578193 / 500000000) (Real.log (7693 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (7693 / 5120) = -Real.log (5120 / 7693) := by
    rw [show ((7693 / 5120) : ℝ) = ((5120 / 7693) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (349119121 / 500000000) ≤ -Real.log (2547 / 5120) ∧
    -Real.log (2547 / 5120) ≤ (174559561 / 250000000) := by
  have h := checkLog_sound (w := (13 / 5107)) (n := 12)
    (lo := (2545531 / 500000000)) (hi := (5091063 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 2547) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(2560 / 2547) = 1/(2547 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-174559561 / 250000000) (-349119121 / 500000000) (Real.log (2547 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (153573939 / 500000000) ≤ -Real.log (500000 / 679771) ∧
    -Real.log (500000 / 679771) ≤ (307147879 / 1000000000) := by
  have h := checkLog_sound (w := (179771 / 1179771)) (n := 12)
    (lo := (153573939 / 500000000)) (hi := (307147879 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((679771 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(679771 / 500000) = 1/(500000 / 679771) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (153573939 / 500000000) (307147879 / 1000000000) (Real.log (679771 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (679771 / 500000) = -Real.log (500000 / 679771) := by
    rw [show ((679771 / 500000) : ℝ) = ((500000 / 679771) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (445571733 / 1000000000) ≤ -Real.log (320229 / 500000) ∧
    -Real.log (320229 / 500000) ≤ (222785867 / 500000000) := by
  have h := checkLog_sound (w := (179771 / 820229)) (n := 12)
    (lo := (445571733 / 1000000000)) (hi := (222785867 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 320229) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 320229) = 1/(320229 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-222785867 / 500000000) (-445571733 / 1000000000) (Real.log (320229 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (307465581 / 1000000000) ≤ -Real.log (500000 / 679987) ∧
    -Real.log (500000 / 679987) ≤ (153732791 / 500000000) := by
  have h := checkLog_sound (w := (179987 / 1179987)) (n := 12)
    (lo := (307465581 / 1000000000)) (hi := (153732791 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((679987 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(679987 / 500000) = 1/(500000 / 679987) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (307465581 / 1000000000) (153732791 / 500000000) (Real.log (679987 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (679987 / 500000) = -Real.log (500000 / 679987) := by
    rw [show ((679987 / 500000) : ℝ) = ((500000 / 679987) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (223123239 / 500000000) ≤ -Real.log (320013 / 500000) ∧
    -Real.log (320013 / 500000) ≤ (446246479 / 1000000000) := by
  have h := checkLog_sound (w := (179987 / 820013)) (n := 12)
    (lo := (223123239 / 500000000)) (hi := (446246479 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 320013) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 320013) = 1/(320013 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-446246479 / 1000000000) (-223123239 / 500000000) (Real.log (320013 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (234015437 / 1000000000) ≤ -Real.log (62500 / 78979) ∧
    -Real.log (62500 / 78979) ≤ (117007719 / 500000000) := by
  have h := checkLog_sound (w := (16479 / 141479)) (n := 12)
    (lo := (234015437 / 1000000000)) (hi := (117007719 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((78979 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(78979 / 62500) = 1/(62500 / 78979) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (234015437 / 1000000000) (117007719 / 500000000) (Real.log (78979 / 62500)) := by
  have h := reflection_log_13_neg
  have he : Real.log (78979 / 62500) = -Real.log (62500 / 78979) := by
    rw [show ((78979 / 62500) : ℝ) = ((62500 / 78979) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (153034371 / 500000000) ≤ -Real.log (46021 / 62500) ∧
    -Real.log (46021 / 62500) ≤ (306068743 / 1000000000) := by
  have h := checkLog_sound (w := (16479 / 108521)) (n := 12)
    (lo := (153034371 / 500000000)) (hi := (306068743 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 46021) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 46021) = 1/(46021 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-306068743 / 1000000000) (-153034371 / 500000000) (Real.log (46021 / 62500)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (11714223 / 50000000) ≤ -Real.log (250000 / 316001) ∧
    -Real.log (250000 / 316001) ≤ (234284461 / 1000000000) := by
  have h := checkLog_sound (w := (66001 / 566001)) (n := 12)
    (lo := (11714223 / 50000000)) (hi := (234284461 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((316001 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(316001 / 250000) = 1/(250000 / 316001) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (11714223 / 50000000) (234284461 / 1000000000) (Real.log (316001 / 250000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (316001 / 250000) = -Real.log (250000 / 316001) := by
    rw [show ((316001 / 250000) : ℝ) = ((250000 / 316001) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (61306119 / 200000000) ≤ -Real.log (183999 / 250000) ∧
    -Real.log (183999 / 250000) ≤ (76632649 / 250000000) := by
  have h := checkLog_sound (w := (66001 / 433999)) (n := 12)
    (lo := (61306119 / 200000000)) (hi := (76632649 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 183999) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 183999) = 1/(183999 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-76632649 / 250000000) (-61306119 / 200000000) (Real.log (183999 / 250000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (752719611 / 1000000000) ≤ -Real.log (500000000000 / 1061382635551) ∧
    -Real.log (500000000000 / 1061382635551) ≤ (752719613 / 1000000000) := by
  have h := checkLog_sound (w := (61382635551 / 2061382635551)) (n := 12)
    (lo := (59572431 / 1000000000)) (hi := (3723277 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1061382635551 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1061382635551 / 1000000000000) = 1/(500000000000 / 1061382635551) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (752719611 / 1000000000) (752719613 / 1000000000) (Real.log (1061382635551 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1061382635551 / 500000000000) = -Real.log (500000000000 / 1061382635551) := by
    rw [show ((1061382635551 / 500000000000) : ℝ) = ((500000000000 / 1061382635551) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (753712059 / 1000000000) ≤ -Real.log (500000000000 / 1062436526017) ∧
    -Real.log (500000000000 / 1062436526017) ≤ (753712061 / 1000000000) := by
  have h := checkLog_sound (w := (62436526017 / 2062436526017)) (n := 12)
    (lo := (60564879 / 1000000000)) (hi := (757061 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1062436526017 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1062436526017 / 1000000000000) = 1/(500000000000 / 1062436526017) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (753712059 / 1000000000) (753712061 / 1000000000) (Real.log (1062436526017 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1062436526017 / 500000000000) = -Real.log (500000000000 / 1062436526017) := by
    rw [show ((1062436526017 / 500000000000) : ℝ) = ((500000000000 / 1062436526017) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (27004209 / 50000000) ≤ -Real.log (500000000000 / 858075661111) ∧
    -Real.log (500000000000 / 858075661111) ≤ (540084181 / 1000000000) := by
  have h := checkLog_sound (w := (358075661111 / 1358075661111)) (n := 12)
    (lo := (27004209 / 50000000)) (hi := (540084181 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((858075661111 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(858075661111 / 500000000000) = 1/(500000000000 / 858075661111) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (27004209 / 50000000) (540084181 / 1000000000) (Real.log (858075661111 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (858075661111 / 500000000000) = -Real.log (500000000000 / 858075661111) := by
    rw [show ((858075661111 / 500000000000) : ℝ) = ((500000000000 / 858075661111) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (108163011 / 200000000) ≤ -Real.log (50000000000 / 85870303643) ∧
    -Real.log (50000000000 / 85870303643) ≤ (33800941 / 62500000) := by
  have h := checkLog_sound (w := (35870303643 / 135870303643)) (n := 12)
    (lo := (108163011 / 200000000)) (hi := (33800941 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((85870303643 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(85870303643 / 50000000000) = 1/(50000000000 / 85870303643) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (108163011 / 200000000) (33800941 / 62500000) (Real.log (85870303643 / 50000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (85870303643 / 50000000000) = -Real.log (50000000000 / 85870303643) := by
    rw [show ((85870303643 / 50000000000) : ℝ) = ((50000000000 / 85870303643) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0298
