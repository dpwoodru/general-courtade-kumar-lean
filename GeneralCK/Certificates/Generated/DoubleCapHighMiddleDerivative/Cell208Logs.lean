import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell208
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

theorem reflection_log_1_neg : (316605433 / 1000000000) ≤ -Real.log (5120 / 7027) ∧
    -Real.log (5120 / 7027) ≤ (158302717 / 500000000) := by
  have h := checkLog_sound (w := (1907 / 12147)) (n := 12)
    (lo := (316605433 / 1000000000)) (hi := (158302717 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7027 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7027 / 5120) = 1/(5120 / 7027) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (316605433 / 1000000000) (158302717 / 500000000) (Real.log (7027 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (7027 / 5120) = -Real.log (5120 / 7027) := by
    rw [show ((7027 / 5120) : ℝ) = ((5120 / 7027) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (232974679 / 500000000) ≤ -Real.log (3213 / 5120) ∧
    -Real.log (3213 / 5120) ≤ (465949359 / 1000000000) := by
  have h := checkLog_sound (w := (1907 / 8333)) (n := 12)
    (lo := (232974679 / 500000000)) (hi := (465949359 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3213) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3213) = 1/(3213 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-465949359 / 1000000000) (-232974679 / 500000000) (Real.log (3213 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (316178417 / 1000000000) ≤ -Real.log (320 / 439) ∧
    -Real.log (320 / 439) ≤ (158089209 / 500000000) := by
  have h := checkLog_sound (w := (119 / 759)) (n := 12)
    (lo := (316178417 / 1000000000)) (hi := (158089209 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((439 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(439 / 320) = 1/(320 / 439) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (316178417 / 1000000000) (158089209 / 500000000) (Real.log (439 / 320)) := by
  have h := reflection_log_3_neg
  have he : Real.log (439 / 320) = -Real.log (320 / 439) := by
    rw [show ((439 / 320) : ℝ) = ((320 / 439) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (465016087 / 1000000000) ≤ -Real.log (201 / 320) ∧
    -Real.log (201 / 320) ≤ (58127011 / 125000000) := by
  have h := checkLog_sound (w := (119 / 521)) (n := 12)
    (lo := (465016087 / 1000000000)) (hi := (58127011 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 201) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(320 / 201) = 1/(201 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-58127011 / 125000000) (-465016087 / 1000000000) (Real.log (201 / 320)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (117363699 / 500000000) ≤ -Real.log (250000 / 316141) ∧
    -Real.log (250000 / 316141) ≤ (234727399 / 1000000000) := by
  have h := checkLog_sound (w := (66141 / 566141)) (n := 12)
    (lo := (117363699 / 500000000)) (hi := (234727399 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((316141 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(316141 / 250000) = 1/(250000 / 316141) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (117363699 / 500000000) (234727399 / 1000000000) (Real.log (316141 / 250000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (316141 / 250000) = -Real.log (250000 / 316141) := by
    rw [show ((316141 / 250000) : ℝ) = ((250000 / 316141) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (153645879 / 500000000) ≤ -Real.log (183859 / 250000) ∧
    -Real.log (183859 / 250000) ≤ (307291759 / 1000000000) := by
  have h := checkLog_sound (w := (66141 / 433859)) (n := 12)
    (lo := (153645879 / 500000000)) (hi := (307291759 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 183859) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 183859) = 1/(183859 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-307291759 / 1000000000) (-153645879 / 500000000) (Real.log (183859 / 250000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (47012369 / 200000000) ≤ -Real.log (1000000 / 1264987) ∧
    -Real.log (1000000 / 1264987) ≤ (117530923 / 500000000) := by
  have h := checkLog_sound (w := (264987 / 2264987)) (n := 12)
    (lo := (47012369 / 200000000)) (hi := (117530923 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1264987 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1264987 / 1000000) = 1/(1000000 / 1264987) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (47012369 / 200000000) (117530923 / 500000000) (Real.log (1264987 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1264987 / 1000000) = -Real.log (1000000 / 1264987) := by
    rw [show ((1264987 / 1000000) : ℝ) = ((1000000 / 1264987) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (76966773 / 250000000) ≤ -Real.log (735013 / 1000000) ∧
    -Real.log (735013 / 1000000) ≤ (307867093 / 1000000000) := by
  have h := checkLog_sound (w := (264987 / 1735013)) (n := 12)
    (lo := (76966773 / 250000000)) (hi := (307867093 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 735013) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 735013) = 1/(735013 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-307867093 / 1000000000) (-76966773 / 250000000) (Real.log (735013 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (43650669 / 250000000) ≤ -Real.log (1000000 / 1190773) ∧
    -Real.log (1000000 / 1190773) ≤ (174602677 / 1000000000) := by
  have h := checkLog_sound (w := (190773 / 2190773)) (n := 12)
    (lo := (43650669 / 250000000)) (hi := (174602677 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1190773 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1190773 / 1000000) = 1/(1000000 / 1190773) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (43650669 / 250000000) (174602677 / 1000000000) (Real.log (1190773 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1190773 / 1000000) = -Real.log (1000000 / 1190773) := by
    rw [show ((1190773 / 1000000) : ℝ) = ((1000000 / 1190773) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (211675807 / 1000000000) ≤ -Real.log (809227 / 1000000) ∧
    -Real.log (809227 / 1000000) ≤ (6614869 / 31250000) := by
  have h := checkLog_sound (w := (190773 / 1809227)) (n := 12)
    (lo := (211675807 / 1000000000)) (hi := (6614869 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 809227) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 809227) = 1/(809227 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-6614869 / 31250000) (-211675807 / 1000000000) (Real.log (809227 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (174869693 / 1000000000) ≤ -Real.log (1000000 / 1191091) ∧
    -Real.log (1000000 / 1191091) ≤ (87434847 / 500000000) := by
  have h := checkLog_sound (w := (191091 / 2191091)) (n := 12)
    (lo := (174869693 / 1000000000)) (hi := (87434847 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1191091 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1191091 / 1000000) = 1/(1000000 / 1191091) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (174869693 / 1000000000) (87434847 / 500000000) (Real.log (1191091 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1191091 / 1000000) = -Real.log (1000000 / 1191091) := by
    rw [show ((1191091 / 1000000) : ℝ) = ((1000000 / 1191091) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (53017213 / 250000000) ≤ -Real.log (808909 / 1000000) ∧
    -Real.log (808909 / 1000000) ≤ (212068853 / 1000000000) := by
  have h := checkLog_sound (w := (191091 / 1808909)) (n := 12)
    (lo := (53017213 / 250000000)) (hi := (212068853 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 808909) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 808909) = 1/(808909 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-212068853 / 1000000000) (-53017213 / 250000000) (Real.log (808909 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (97649313 / 125000000) ≤ -Real.log (100000000000 / 218407960199) ∧
    -Real.log (100000000000 / 218407960199) ≤ (390597253 / 500000000) := by
  have h := checkLog_sound (w := (18407960199 / 418407960199)) (n := 12)
    (lo := (22011831 / 250000000)) (hi := (3521893 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((218407960199 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(218407960199 / 200000000000) = 1/(100000000000 / 218407960199) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (97649313 / 125000000) (390597253 / 500000000) (Real.log (218407960199 / 100000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (218407960199 / 100000000000) = -Real.log (100000000000 / 218407960199) := by
    rw [show ((218407960199 / 100000000000) : ℝ) = ((100000000000 / 218407960199) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (782554791 / 1000000000) ≤ -Real.log (500000000000 / 1093526299409) ∧
    -Real.log (500000000000 / 1093526299409) ≤ (782554793 / 1000000000) := by
  have h := checkLog_sound (w := (93526299409 / 2093526299409)) (n := 12)
    (lo := (89407611 / 1000000000)) (hi := (22351903 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1093526299409 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1093526299409 / 1000000000000) = 1/(500000000000 / 1093526299409) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (782554791 / 1000000000) (782554793 / 1000000000) (Real.log (1093526299409 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (1093526299409 / 500000000000) = -Real.log (500000000000 / 1093526299409) := by
    rw [show ((1093526299409 / 500000000000) : ℝ) = ((500000000000 / 1093526299409) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (542019157 / 1000000000) ≤ -Real.log (500000000000 / 859737625027) ∧
    -Real.log (500000000000 / 859737625027) ≤ (271009579 / 500000000) := by
  have h := checkLog_sound (w := (359737625027 / 1359737625027)) (n := 12)
    (lo := (542019157 / 1000000000)) (hi := (271009579 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((859737625027 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(859737625027 / 500000000000) = 1/(500000000000 / 859737625027) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (542019157 / 1000000000) (271009579 / 500000000) (Real.log (859737625027 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (859737625027 / 500000000000) = -Real.log (500000000000 / 859737625027) := by
    rw [show ((859737625027 / 500000000000) : ℝ) = ((500000000000 / 859737625027) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (271464469 / 500000000) ≤ -Real.log (250000000000 / 430260077033) ∧
    -Real.log (250000000000 / 430260077033) ≤ (542928939 / 1000000000) := by
  have h := checkLog_sound (w := (180260077033 / 680260077033)) (n := 12)
    (lo := (271464469 / 500000000)) (hi := (542928939 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((430260077033 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(430260077033 / 250000000000) = 1/(250000000000 / 430260077033) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (271464469 / 500000000) (542928939 / 1000000000) (Real.log (430260077033 / 250000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (430260077033 / 250000000000) = -Real.log (250000000000 / 430260077033) := by
    rw [show ((430260077033 / 250000000000) : ℝ) = ((250000000000 / 430260077033) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (96569621 / 250000000) ≤ -Real.log (500000000000 / 735747200723) ∧
    -Real.log (500000000000 / 735747200723) ≤ (77255697 / 200000000) := by
  have h := checkLog_sound (w := (235747200723 / 1235747200723)) (n := 12)
    (lo := (96569621 / 250000000)) (hi := (77255697 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((735747200723 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(735747200723 / 500000000000) = 1/(500000000000 / 735747200723) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (96569621 / 250000000) (77255697 / 200000000) (Real.log (735747200723 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (735747200723 / 500000000000) = -Real.log (500000000000 / 735747200723) := by
    rw [show ((735747200723 / 500000000000) : ℝ) = ((500000000000 / 735747200723) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (193469273 / 500000000) ≤ -Real.log (500000000000 / 736233000251) ∧
    -Real.log (500000000000 / 736233000251) ≤ (386938547 / 1000000000) := by
  have h := checkLog_sound (w := (236233000251 / 1236233000251)) (n := 12)
    (lo := (193469273 / 500000000)) (hi := (386938547 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((736233000251 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(736233000251 / 500000000000) = 1/(500000000000 / 736233000251) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (193469273 / 500000000) (386938547 / 1000000000) (Real.log (736233000251 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (736233000251 / 500000000000) = -Real.log (500000000000 / 736233000251) := by
    rw [show ((736233000251 / 500000000000) : ℝ) = ((500000000000 / 736233000251) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (18599579 / 500000000) ≤ -Real.log (963484229719 / 1000000000000) ∧
    -Real.log (963484229719 / 1000000000000) ≤ (37199159 / 1000000000) := by
  have h := checkLog_sound (w := (36515770281 / 1963484229719)) (n := 12)
    (lo := (18599579 / 500000000)) (hi := (37199159 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 963484229719) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 963484229719) = 1/(963484229719 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-37199159 / 1000000000) (-18599579 / 500000000) (Real.log (963484229719 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (37073131 / 1000000000) ≤ -Real.log (963605662471 / 1000000000000) ∧
    -Real.log (963605662471 / 1000000000000) ≤ (9268283 / 250000000) := by
  have h := checkLog_sound (w := (36394337529 / 1963605662471)) (n := 12)
    (lo := (37073131 / 1000000000)) (hi := (9268283 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 963605662471) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 963605662471) = 1/(963605662471 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-9268283 / 250000000) (-37073131 / 1000000000) (Real.log (963605662471 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell208
