import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0178
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

theorem reflection_log_1_neg : (275498781 / 1000000000) ≤ -Real.log (640 / 843) ∧
    -Real.log (640 / 843) ≤ (137749391 / 500000000) := by
  have h := checkLog_sound (w := (203 / 1483)) (n := 12)
    (lo := (275498781 / 1000000000)) (hi := (137749391 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((843 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(843 / 640) = 1/(640 / 843) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (275498781 / 1000000000) (137749391 / 500000000) (Real.log (843 / 640)) := by
  have h := reflection_log_1_neg
  have he : Real.log (843 / 640) = -Real.log (640 / 843) := by
    rw [show ((843 / 640) : ℝ) = ((640 / 843) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (381534981 / 1000000000) ≤ -Real.log (437 / 640) ∧
    -Real.log (437 / 640) ≤ (190767491 / 500000000) := by
  have h := checkLog_sound (w := (203 / 1077)) (n := 12)
    (lo := (381534981 / 1000000000)) (hi := (190767491 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 437) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 437) = 1/(437 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-190767491 / 500000000) (-381534981 / 1000000000) (Real.log (437 / 640)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (137526921 / 500000000) ≤ -Real.log (5120 / 6741) ∧
    -Real.log (5120 / 6741) ≤ (275053843 / 1000000000) := by
  have h := checkLog_sound (w := (1621 / 11861)) (n := 12)
    (lo := (137526921 / 500000000)) (hi := (275053843 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6741 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6741 / 5120) = 1/(5120 / 6741) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (137526921 / 500000000) (275053843 / 1000000000) (Real.log (6741 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6741 / 5120) = -Real.log (5120 / 6741) := by
    rw [show ((6741 / 5120) : ℝ) = ((5120 / 6741) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (15227089 / 40000000) ≤ -Real.log (3499 / 5120) ∧
    -Real.log (3499 / 5120) ≤ (190338613 / 500000000) := by
  have h := checkLog_sound (w := (1621 / 8619)) (n := 12)
    (lo := (15227089 / 40000000)) (hi := (190338613 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3499) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3499) = 1/(3499 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-190338613 / 500000000) (-15227089 / 40000000) (Real.log (3499 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (122815117 / 250000000) ≤ -Real.log (320 / 523) ∧
    -Real.log (320 / 523) ≤ (491260469 / 1000000000) := by
  have h := checkLog_sound (w := (203 / 843)) (n := 12)
    (lo := (122815117 / 250000000)) (hi := (491260469 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((523 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(523 / 320) = 1/(320 / 523) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (122815117 / 250000000) (491260469 / 1000000000) (Real.log (523 / 320)) := by
  have h := reflection_log_5_neg
  have he : Real.log (523 / 320) = -Real.log (320 / 523) := by
    rw [show ((523 / 320) : ℝ) = ((320 / 523) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (50307353 / 50000000) ≤ -Real.log (117 / 320) ∧
    -Real.log (117 / 320) ≤ (503073531 / 500000000) := by
  have h := checkLog_sound (w := (43 / 277)) (n := 12)
    (lo := (7824997 / 25000000)) (hi := (312999881 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 117) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(160 / 117) = 1/(117 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-503073531 / 500000000) (-50307353 / 50000000) (Real.log (117 / 320)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (490543193 / 1000000000) ≤ -Real.log (2560 / 4181) ∧
    -Real.log (2560 / 4181) ≤ (245271597 / 500000000) := by
  have h := checkLog_sound (w := (1621 / 6741)) (n := 12)
    (lo := (490543193 / 1000000000)) (hi := (245271597 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4181 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4181 / 2560) = 1/(2560 / 4181) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (490543193 / 1000000000) (245271597 / 500000000) (Real.log (4181 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (4181 / 2560) = -Real.log (2560 / 4181) := by
    rw [show ((4181 / 2560) : ℝ) = ((2560 / 4181) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (1002947057 / 1000000000) ≤ -Real.log (939 / 2560) ∧
    -Real.log (939 / 2560) ≤ (1002947059 / 1000000000) := by
  have h := checkLog_sound (w := (341 / 2219)) (n := 12)
    (lo := (309799877 / 1000000000)) (hi := (154899939 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 939) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 939) = 1/(939 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1002947059 / 1000000000) (-1002947057 / 1000000000) (Real.log (939 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (75252843 / 200000000) ≤ -Real.log (15625 / 22763) ∧
    -Real.log (15625 / 22763) ≤ (47033027 / 125000000) := by
  have h := checkLog_sound (w := (3569 / 19194)) (n := 12)
    (lo := (75252843 / 200000000)) (hi := (47033027 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((22763 / 15625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(22763 / 15625) = 1/(15625 / 22763) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (75252843 / 200000000) (47033027 / 125000000) (Real.log (22763 / 15625)) := by
  have h := reflection_log_9_neg
  have he : Real.log (22763 / 15625) = -Real.log (15625 / 22763) := by
    rw [show ((22763 / 15625) : ℝ) = ((15625 / 22763) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (305168307 / 500000000) ≤ -Real.log (8487 / 15625) ∧
    -Real.log (8487 / 15625) ≤ (122067323 / 200000000) := by
  have h := checkLog_sound (w := (3569 / 12056)) (n := 12)
    (lo := (305168307 / 500000000)) (hi := (122067323 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 8487) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625 / 8487) = 1/(8487 / 15625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-122067323 / 200000000) (-305168307 / 500000000) (Real.log (8487 / 15625)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (376874257 / 1000000000) ≤ -Real.log (1000000 / 1457721) ∧
    -Real.log (1000000 / 1457721) ≤ (188437129 / 500000000) := by
  have h := checkLog_sound (w := (457721 / 2457721)) (n := 12)
    (lo := (376874257 / 1000000000)) (hi := (188437129 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1457721 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1457721 / 1000000) = 1/(1000000 / 1457721) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (376874257 / 1000000000) (188437129 / 500000000) (Real.log (1457721 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1457721 / 1000000) = -Real.log (1000000 / 1457721) := by
    rw [show ((1457721 / 1000000) : ℝ) = ((1000000 / 1457721) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (611974649 / 1000000000) ≤ -Real.log (542279 / 1000000) ∧
    -Real.log (542279 / 1000000) ≤ (12239493 / 20000000) := by
  have h := checkLog_sound (w := (457721 / 1542279)) (n := 12)
    (lo := (611974649 / 1000000000)) (hi := (12239493 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 542279) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 542279) = 1/(542279 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-12239493 / 20000000) (-611974649 / 1000000000) (Real.log (542279 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (294743581 / 1000000000) ≤ -Real.log (500000 / 671391) ∧
    -Real.log (500000 / 671391) ≤ (147371791 / 500000000) := by
  have h := checkLog_sound (w := (171391 / 1171391)) (n := 12)
    (lo := (294743581 / 1000000000)) (hi := (147371791 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((671391 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(671391 / 500000) = 1/(500000 / 671391) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (294743581 / 1000000000) (147371791 / 500000000) (Real.log (671391 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (671391 / 500000) = -Real.log (500000 / 671391) := by
    rw [show ((671391 / 500000) : ℝ) = ((500000 / 671391) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (26233719 / 62500000) ≤ -Real.log (328609 / 500000) ∧
    -Real.log (328609 / 500000) ≤ (83947901 / 200000000) := by
  have h := checkLog_sound (w := (171391 / 828609)) (n := 12)
    (lo := (26233719 / 62500000)) (hi := (83947901 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 328609) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 328609) = 1/(328609 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-83947901 / 200000000) (-26233719 / 62500000) (Real.log (328609 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (147650239 / 500000000) ≤ -Real.log (100000 / 134353) ∧
    -Real.log (100000 / 134353) ≤ (295300479 / 1000000000) := by
  have h := checkLog_sound (w := (34353 / 234353)) (n := 12)
    (lo := (147650239 / 500000000)) (hi := (295300479 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((134353 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(134353 / 100000) = 1/(100000 / 134353) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (147650239 / 500000000) (295300479 / 1000000000) (Real.log (134353 / 100000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (134353 / 100000) = -Real.log (100000 / 134353) := by
    rw [show ((134353 / 100000) : ℝ) = ((100000 / 134353) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (420878283 / 1000000000) ≤ -Real.log (65647 / 100000) ∧
    -Real.log (65647 / 100000) ≤ (105219571 / 250000000) := by
  have h := checkLog_sound (w := (34353 / 165647)) (n := 12)
    (lo := (420878283 / 1000000000)) (hi := (105219571 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 65647) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 65647) = 1/(65647 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-105219571 / 250000000) (-420878283 / 1000000000) (Real.log (65647 / 100000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (986600829 / 1000000000) ≤ -Real.log (100000000000 / 268210203841) ∧
    -Real.log (100000000000 / 268210203841) ≤ (986600831 / 1000000000) := by
  have h := checkLog_sound (w := (68210203841 / 468210203841)) (n := 12)
    (lo := (293453649 / 1000000000)) (hi := (5869073 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((268210203841 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(268210203841 / 200000000000) = 1/(100000000000 / 268210203841) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (986600829 / 1000000000) (986600831 / 1000000000) (Real.log (268210203841 / 100000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (268210203841 / 100000000000) = -Real.log (100000000000 / 268210203841) := by
    rw [show ((268210203841 / 100000000000) : ℝ) = ((100000000000 / 268210203841) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (494424453 / 500000000) ≤ -Real.log (500000000000 / 1344069196853) ∧
    -Real.log (500000000000 / 1344069196853) ≤ (247212227 / 250000000) := by
  have h := checkLog_sound (w := (344069196853 / 2344069196853)) (n := 12)
    (lo := (147850863 / 500000000)) (hi := (295701727 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1344069196853 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1344069196853 / 1000000000000) = 1/(500000000000 / 1344069196853) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (494424453 / 500000000) (247212227 / 250000000) (Real.log (1344069196853 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1344069196853 / 500000000000) = -Real.log (500000000000 / 1344069196853) := by
    rw [show ((1344069196853 / 500000000000) : ℝ) = ((500000000000 / 1344069196853) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (178620771 / 250000000) ≤ -Real.log (31250000000 / 63847821423) ∧
    -Real.log (31250000000 / 63847821423) ≤ (357241543 / 500000000) := by
  have h := checkLog_sound (w := (1347821423 / 126347821423)) (n := 12)
    (lo := (666747 / 31250000)) (hi := (4267181 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((63847821423 / 62500000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(63847821423 / 62500000000) = 1/(31250000000 / 63847821423) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (178620771 / 250000000) (357241543 / 500000000) (Real.log (63847821423 / 31250000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (63847821423 / 31250000000) = -Real.log (31250000000 / 63847821423) := by
    rw [show ((63847821423 / 31250000000) : ℝ) = ((31250000000 / 63847821423) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (716178761 / 1000000000) ≤ -Real.log (500000000000 / 1023298856003) ∧
    -Real.log (500000000000 / 1023298856003) ≤ (716178763 / 1000000000) := by
  have h := checkLog_sound (w := (23298856003 / 2023298856003)) (n := 12)
    (lo := (23031581 / 1000000000)) (hi := (11515791 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1023298856003 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1023298856003 / 1000000000000) = 1/(500000000000 / 1023298856003) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (716178761 / 1000000000) (716178763 / 1000000000) (Real.log (1023298856003 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1023298856003 / 500000000000) = -Real.log (500000000000 / 1023298856003) := by
    rw [show ((1023298856003 / 500000000000) : ℝ) = ((500000000000 / 1023298856003) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0178
