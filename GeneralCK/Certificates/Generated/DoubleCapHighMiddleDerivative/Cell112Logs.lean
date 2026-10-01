import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell112
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

theorem reflection_log_1_neg : (137378553 / 500000000) ≤ -Real.log (5120 / 6739) ∧
    -Real.log (5120 / 6739) ≤ (274757107 / 1000000000) := by
  have h := checkLog_sound (w := (1619 / 11859)) (n := 12)
    (lo := (137378553 / 500000000)) (hi := (274757107 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6739 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6739 / 5120) = 1/(5120 / 6739) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (137378553 / 500000000) (274757107 / 1000000000) (Real.log (6739 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6739 / 5120) = -Real.log (5120 / 6739) := by
    rw [show ((6739 / 5120) : ℝ) = ((5120 / 6739) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (380105797 / 1000000000) ≤ -Real.log (3501 / 5120) ∧
    -Real.log (3501 / 5120) ≤ (190052899 / 500000000) := by
  have h := checkLog_sound (w := (1619 / 8621)) (n := 12)
    (lo := (380105797 / 1000000000)) (hi := (190052899 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3501) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3501) = 1/(3501 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-190052899 / 500000000) (-380105797 / 1000000000) (Real.log (3501 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (274311837 / 1000000000) ≤ -Real.log (320 / 421) ∧
    -Real.log (320 / 421) ≤ (137155919 / 500000000) := by
  have h := checkLog_sound (w := (101 / 741)) (n := 12)
    (lo := (274311837 / 1000000000)) (hi := (137155919 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((421 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(421 / 320) = 1/(320 / 421) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (274311837 / 1000000000) (137155919 / 500000000) (Real.log (421 / 320)) := by
  have h := reflection_log_3_neg
  have he : Real.log (421 / 320) = -Real.log (320 / 421) := by
    rw [show ((421 / 320) : ℝ) = ((320 / 421) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (75849853 / 200000000) ≤ -Real.log (219 / 320) ∧
    -Real.log (219 / 320) ≤ (189624633 / 500000000) := by
  have h := checkLog_sound (w := (101 / 539)) (n := 12)
    (lo := (75849853 / 200000000)) (hi := (189624633 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 219) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(320 / 219) = 1/(219 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-189624633 / 500000000) (-75849853 / 200000000) (Real.log (219 / 320)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (101122137 / 500000000) ≤ -Real.log (1000000 / 1224147) ∧
    -Real.log (1000000 / 1224147) ≤ (8089771 / 40000000) := by
  have h := checkLog_sound (w := (224147 / 2224147)) (n := 12)
    (lo := (101122137 / 500000000)) (hi := (8089771 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1224147 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1224147 / 1000000) = 1/(1000000 / 1224147) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (101122137 / 500000000) (8089771 / 40000000) (Real.log (1224147 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1224147 / 1000000) = -Real.log (1000000 / 1224147) := by
    rw [show ((1224147 / 1000000) : ℝ) = ((1000000 / 1224147) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (253792209 / 1000000000) ≤ -Real.log (775853 / 1000000) ∧
    -Real.log (775853 / 1000000) ≤ (25379221 / 100000000) := by
  have h := checkLog_sound (w := (224147 / 1775853)) (n := 12)
    (lo := (253792209 / 1000000000)) (hi := (25379221 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 775853) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 775853) = 1/(775853 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-25379221 / 100000000) (-253792209 / 1000000000) (Real.log (775853 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (6330879 / 31250000) ≤ -Real.log (125000 / 153071) ∧
    -Real.log (125000 / 153071) ≤ (202588129 / 1000000000) := by
  have h := checkLog_sound (w := (28071 / 278071)) (n := 12)
    (lo := (6330879 / 31250000)) (hi := (202588129 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((153071 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(153071 / 125000) = 1/(125000 / 153071) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (6330879 / 31250000) (202588129 / 1000000000) (Real.log (153071 / 125000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (153071 / 125000) = -Real.log (125000 / 153071) := by
    rw [show ((153071 / 125000) : ℝ) = ((125000 / 153071) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (50866997 / 200000000) ≤ -Real.log (96929 / 125000) ∧
    -Real.log (96929 / 125000) ≤ (127167493 / 500000000) := by
  have h := checkLog_sound (w := (28071 / 221929)) (n := 12)
    (lo := (50866997 / 200000000)) (hi := (127167493 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 96929) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 96929) = 1/(96929 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-127167493 / 500000000) (-50866997 / 200000000) (Real.log (96929 / 125000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (74525851 / 500000000) ≤ -Real.log (1000000 / 1160733) ∧
    -Real.log (1000000 / 1160733) ≤ (149051703 / 1000000000) := by
  have h := checkLog_sound (w := (160733 / 2160733)) (n := 12)
    (lo := (74525851 / 500000000)) (hi := (149051703 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1160733 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1160733 / 1000000) = 1/(1000000 / 1160733) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (74525851 / 500000000) (149051703 / 1000000000) (Real.log (1160733 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1160733 / 1000000) = -Real.log (1000000 / 1160733) := by
    rw [show ((1160733 / 1000000) : ℝ) = ((1000000 / 1160733) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (175226387 / 1000000000) ≤ -Real.log (839267 / 1000000) ∧
    -Real.log (839267 / 1000000) ≤ (43806597 / 250000000) := by
  have h := checkLog_sound (w := (160733 / 1839267)) (n := 12)
    (lo := (175226387 / 1000000000)) (hi := (43806597 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 839267) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 839267) = 1/(839267 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-43806597 / 250000000) (-175226387 / 1000000000) (Real.log (839267 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (373299 / 2500000) ≤ -Real.log (250000 / 290261) ∧
    -Real.log (250000 / 290261) ≤ (149319601 / 1000000000) := by
  have h := checkLog_sound (w := (40261 / 540261)) (n := 12)
    (lo := (373299 / 2500000)) (hi := (149319601 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((290261 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(290261 / 250000) = 1/(250000 / 290261) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (373299 / 2500000) (149319601 / 1000000000) (Real.log (290261 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (290261 / 250000) = -Real.log (250000 / 290261) := by
    rw [show ((290261 / 250000) : ℝ) = ((250000 / 290261) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (175597017 / 1000000000) ≤ -Real.log (209739 / 250000) ∧
    -Real.log (209739 / 250000) ≤ (87798509 / 500000000) := by
  have h := checkLog_sound (w := (40261 / 459739)) (n := 12)
    (lo := (175597017 / 1000000000)) (hi := (87798509 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 209739) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 209739) = 1/(209739 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-87798509 / 500000000) (-175597017 / 1000000000) (Real.log (209739 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (653561103 / 1000000000) ≤ -Real.log (500000000000 / 961187214611) ∧
    -Real.log (500000000000 / 961187214611) ≤ (40847569 / 62500000) := by
  have h := checkLog_sound (w := (461187214611 / 1461187214611)) (n := 12)
    (lo := (653561103 / 1000000000)) (hi := (40847569 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((961187214611 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(961187214611 / 500000000000) = 1/(500000000000 / 961187214611) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (653561103 / 1000000000) (40847569 / 62500000) (Real.log (961187214611 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (961187214611 / 500000000000) = -Real.log (500000000000 / 961187214611) := by
    rw [show ((961187214611 / 500000000000) : ℝ) = ((500000000000 / 961187214611) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (654862903 / 1000000000) ≤ -Real.log (500000000000 / 962439303057) ∧
    -Real.log (500000000000 / 962439303057) ≤ (81857863 / 125000000) := by
  have h := checkLog_sound (w := (462439303057 / 1462439303057)) (n := 12)
    (lo := (654862903 / 1000000000)) (hi := (81857863 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((962439303057 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(962439303057 / 500000000000) = 1/(500000000000 / 962439303057) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (654862903 / 1000000000) (81857863 / 125000000) (Real.log (962439303057 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (962439303057 / 500000000000) = -Real.log (500000000000 / 962439303057) := by
    rw [show ((962439303057 / 500000000000) : ℝ) = ((500000000000 / 962439303057) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (114009121 / 250000000) ≤ -Real.log (62500000000 / 98612994343) ∧
    -Real.log (62500000000 / 98612994343) ≤ (91207297 / 200000000) := by
  have h := checkLog_sound (w := (36112994343 / 161112994343)) (n := 12)
    (lo := (114009121 / 250000000)) (hi := (91207297 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((98612994343 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(98612994343 / 62500000000) = 1/(62500000000 / 98612994343) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (114009121 / 250000000) (91207297 / 200000000) (Real.log (98612994343 / 62500000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (98612994343 / 62500000000) = -Real.log (62500000000 / 98612994343) := by
    rw [show ((98612994343 / 62500000000) : ℝ) = ((62500000000 / 98612994343) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (228461557 / 500000000) ≤ -Real.log (250000000000 / 394801865283) ∧
    -Real.log (250000000000 / 394801865283) ≤ (91384623 / 200000000) := by
  have h := checkLog_sound (w := (144801865283 / 644801865283)) (n := 12)
    (lo := (228461557 / 500000000)) (hi := (91384623 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((394801865283 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(394801865283 / 250000000000) = 1/(250000000000 / 394801865283) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (228461557 / 500000000) (91384623 / 200000000) (Real.log (394801865283 / 250000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (394801865283 / 250000000000) = -Real.log (250000000000 / 394801865283) := by
    rw [show ((394801865283 / 250000000000) : ℝ) = ((250000000000 / 394801865283) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (324278089 / 1000000000) ≤ -Real.log (125000000000 / 172878982493) ∧
    -Real.log (125000000000 / 172878982493) ≤ (32427809 / 100000000) := by
  have h := checkLog_sound (w := (47878982493 / 297878982493)) (n := 12)
    (lo := (324278089 / 1000000000)) (hi := (32427809 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((172878982493 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(172878982493 / 125000000000) = 1/(125000000000 / 172878982493) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (324278089 / 1000000000) (32427809 / 100000000) (Real.log (172878982493 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (172878982493 / 125000000000) = -Real.log (125000000000 / 172878982493) := by
    rw [show ((172878982493 / 125000000000) : ℝ) = ((125000000000 / 172878982493) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (324916617 / 1000000000) ≤ -Real.log (500000000000 / 691957623523) ∧
    -Real.log (500000000000 / 691957623523) ≤ (162458309 / 500000000) := by
  have h := checkLog_sound (w := (191957623523 / 1191957623523)) (n := 12)
    (lo := (324916617 / 1000000000)) (hi := (162458309 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((691957623523 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(691957623523 / 500000000000) = 1/(500000000000 / 691957623523) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (324916617 / 1000000000) (162458309 / 500000000) (Real.log (691957623523 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (691957623523 / 500000000000) = -Real.log (500000000000 / 691957623523) := by
    rw [show ((691957623523 / 500000000000) : ℝ) = ((500000000000 / 691957623523) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (3284677 / 125000000) ≤ -Real.log (60879051879 / 62500000000) ∧
    -Real.log (60879051879 / 62500000000) ≤ (26277417 / 1000000000) := by
  have h := checkLog_sound (w := (1620948121 / 123379051879)) (n := 12)
    (lo := (3284677 / 125000000)) (hi := (26277417 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 60879051879) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 60879051879) = 1/(60879051879 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-26277417 / 1000000000) (-3284677 / 125000000) (Real.log (60879051879 / 62500000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (5234937 / 200000000) ≤ -Real.log (974164902711 / 1000000000000) ∧
    -Real.log (974164902711 / 1000000000000) ≤ (13087343 / 500000000) := by
  have h := checkLog_sound (w := (25835097289 / 1974164902711)) (n := 12)
    (lo := (5234937 / 200000000)) (hi := (13087343 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 974164902711) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 974164902711) = 1/(974164902711 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-13087343 / 500000000) (-5234937 / 200000000) (Real.log (974164902711 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell112
