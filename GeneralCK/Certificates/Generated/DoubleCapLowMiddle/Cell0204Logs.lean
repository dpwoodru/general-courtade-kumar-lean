import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0204
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

theorem reflection_log_1_neg : (578893067 / 1000000000) ≤ -Real.log (3200 / 5709) ∧
    -Real.log (3200 / 5709) ≤ (144723267 / 250000000) := by
  have h := checkLog_sound (w := (2509 / 8909)) (n := 12)
    (lo := (578893067 / 1000000000)) (hi := (144723267 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5709 / 3200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5709 / 3200) = 1/(3200 / 5709) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (578893067 / 1000000000) (144723267 / 250000000) (Real.log (5709 / 3200)) := by
  have h := reflection_log_1_neg
  have he : Real.log (5709 / 3200) = -Real.log (3200 / 5709) := by
    rw [show ((5709 / 3200) : ℝ) = ((3200 / 5709) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (1532766263 / 1000000000) ≤ -Real.log (691 / 3200) ∧
    -Real.log (691 / 3200) ≤ (766383133 / 500000000) := by
  have h := checkLog_sound (w := (109 / 1491)) (n := 12)
    (lo := (146471903 / 1000000000)) (hi := (4577247 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 691) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(800 / 691) = 1/(691 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-766383133 / 500000000) (-1532766263 / 1000000000) (Real.log (691 / 3200)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (287779719 / 500000000) ≤ -Real.log (320 / 569) ∧
    -Real.log (320 / 569) ≤ (575559439 / 1000000000) := by
  have h := checkLog_sound (w := (249 / 889)) (n := 12)
    (lo := (287779719 / 500000000)) (hi := (575559439 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((569 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(569 / 320) = 1/(320 / 569) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (287779719 / 500000000) (575559439 / 1000000000) (Real.log (569 / 320)) := by
  have h := reflection_log_3_neg
  have he : Real.log (569 / 320) = -Real.log (320 / 569) := by
    rw [show ((569 / 320) : ℝ) = ((320 / 569) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (1505641117 / 1000000000) ≤ -Real.log (71 / 320) ∧
    -Real.log (71 / 320) ≤ (9410257 / 6250000) := by
  have h := checkLog_sound (w := (9 / 151)) (n := 12)
    (lo := (119346757 / 1000000000)) (hi := (59673379 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80 / 71) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(80 / 71) = 1/(71 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-9410257 / 6250000) (-1505641117 / 1000000000) (Real.log (71 / 320)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (224940319 / 500000000) ≤ -Real.log (1600 / 2509) ∧
    -Real.log (1600 / 2509) ≤ (449880639 / 1000000000) := by
  have h := checkLog_sound (w := (909 / 4109)) (n := 12)
    (lo := (224940319 / 500000000)) (hi := (449880639 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2509 / 1600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2509 / 1600) = 1/(1600 / 2509) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (224940319 / 500000000) (449880639 / 1000000000) (Real.log (2509 / 1600)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2509 / 1600) = -Real.log (1600 / 2509) := by
    rw [show ((2509 / 1600) : ℝ) = ((1600 / 2509) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (839619083 / 1000000000) ≤ -Real.log (691 / 1600) ∧
    -Real.log (691 / 1600) ≤ (167923817 / 200000000) := by
  have h := checkLog_sound (w := (109 / 1491)) (n := 12)
    (lo := (146471903 / 1000000000)) (hi := (4577247 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 691) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(800 / 691) = 1/(691 / 1600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-167923817 / 200000000) (-839619083 / 1000000000) (Real.log (691 / 1600)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (442279081 / 1000000000) ≤ -Real.log (160 / 249) ∧
    -Real.log (160 / 249) ≤ (221139541 / 500000000) := by
  have h := checkLog_sound (w := (89 / 409)) (n := 12)
    (lo := (442279081 / 1000000000)) (hi := (221139541 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((249 / 160) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(249 / 160) = 1/(160 / 249) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (442279081 / 1000000000) (221139541 / 500000000) (Real.log (249 / 160)) := by
  have h := reflection_log_7_neg
  have he : Real.log (249 / 160) = -Real.log (160 / 249) := by
    rw [show ((249 / 160) : ℝ) = ((160 / 249) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (812493937 / 1000000000) ≤ -Real.log (71 / 160) ∧
    -Real.log (71 / 160) ≤ (812493939 / 1000000000) := by
  have h := checkLog_sound (w := (9 / 151)) (n := 12)
    (lo := (119346757 / 1000000000)) (hi := (59673379 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80 / 71) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(80 / 71) = 1/(71 / 160) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-812493939 / 1000000000) (-812493937 / 1000000000) (Real.log (71 / 160)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (76992021 / 125000000) ≤ -Real.log (1000000 / 1851389) ∧
    -Real.log (1000000 / 1851389) ≤ (615936169 / 1000000000) := by
  have h := checkLog_sound (w := (851389 / 2851389)) (n := 12)
    (lo := (76992021 / 125000000)) (hi := (615936169 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1851389 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1851389 / 1000000) = 1/(1000000 / 1851389) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (76992021 / 125000000) (615936169 / 1000000000) (Real.log (1851389 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1851389 / 1000000) = -Real.log (1000000 / 1851389) := by
    rw [show ((1851389 / 1000000) : ℝ) = ((1000000 / 1851389) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (476605781 / 250000000) ≤ -Real.log (148611 / 1000000) ∧
    -Real.log (148611 / 1000000) ≤ (1906423127 / 1000000000) := by
  have h := checkLog_sound (w := (101389 / 398611)) (n := 12)
    (lo := (130032191 / 250000000)) (hi := (104025753 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 148611) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(250000 / 148611) = 1/(148611 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-1906423127 / 1000000000) (-476605781 / 250000000) (Real.log (148611 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (308773047 / 500000000) ≤ -Real.log (250000 / 463593) ∧
    -Real.log (250000 / 463593) ≤ (123509219 / 200000000) := by
  have h := checkLog_sound (w := (213593 / 713593)) (n := 12)
    (lo := (308773047 / 500000000)) (hi := (123509219 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((463593 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(463593 / 250000) = 1/(250000 / 463593) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (308773047 / 500000000) (123509219 / 200000000) (Real.log (463593 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (463593 / 250000) = -Real.log (250000 / 463593) := by
    rw [show ((463593 / 250000) : ℝ) = ((250000 / 463593) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (481674963 / 250000000) ≤ -Real.log (36407 / 250000) ∧
    -Real.log (36407 / 250000) ≤ (385339971 / 200000000) := by
  have h := checkLog_sound (w := (26093 / 98907)) (n := 12)
    (lo := (135101373 / 250000000)) (hi := (540405493 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 36407) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(62500 / 36407) = 1/(36407 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-385339971 / 200000000) (-481674963 / 250000000) (Real.log (36407 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (303672899 / 500000000) ≤ -Real.log (1000000 / 1835553) ∧
    -Real.log (1000000 / 1835553) ≤ (607345799 / 1000000000) := by
  have h := checkLog_sound (w := (835553 / 2835553)) (n := 12)
    (lo := (303672899 / 500000000)) (hi := (607345799 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1835553 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1835553 / 1000000) = 1/(1000000 / 1835553) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (303672899 / 500000000) (607345799 / 1000000000) (Real.log (1835553 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1835553 / 1000000) = -Real.log (1000000 / 1835553) := by
    rw [show ((1835553 / 1000000) : ℝ) = ((1000000 / 1835553) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (451291737 / 250000000) ≤ -Real.log (164447 / 1000000) ∧
    -Real.log (164447 / 1000000) ≤ (1805166951 / 1000000000) := by
  have h := checkLog_sound (w := (85553 / 414447)) (n := 12)
    (lo := (104718147 / 250000000)) (hi := (418872589 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 164447) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(250000 / 164447) = 1/(164447 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-1805166951 / 1000000000) (-451291737 / 250000000) (Real.log (164447 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (38095061 / 62500000) ≤ -Real.log (20000 / 36791) ∧
    -Real.log (20000 / 36791) ≤ (609520977 / 1000000000) := by
  have h := checkLog_sound (w := (16791 / 56791)) (n := 12)
    (lo := (38095061 / 62500000)) (hi := (609520977 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((36791 / 20000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(36791 / 20000) = 1/(20000 / 36791) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (38095061 / 62500000) (609520977 / 1000000000) (Real.log (36791 / 20000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (36791 / 20000) = -Real.log (20000 / 36791) := by
    rw [show ((36791 / 20000) : ℝ) = ((20000 / 36791) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (182977291 / 100000000) ≤ -Real.log (3209 / 20000) ∧
    -Real.log (3209 / 20000) ≤ (1829772913 / 1000000000) := by
  have h := checkLog_sound (w := (1791 / 8209)) (n := 12)
    (lo := (8869571 / 20000000)) (hi := (443478551 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 3209) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(5000 / 3209) = 1/(3209 / 20000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-1829772913 / 1000000000) (-182977291 / 100000000) (Real.log (3209 / 20000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (2522359291 / 1000000000) ≤ -Real.log (500000000000 / 6228976993627) ∧
    -Real.log (500000000000 / 6228976993627) ≤ (504471859 / 200000000) := by
  have h := checkLog_sound (w := (2228976993627 / 10228976993627)) (n := 12)
    (lo := (442917751 / 1000000000)) (hi := (55364719 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6228976993627 / 4000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(6228976993627 / 4000000000000) = 1/(500000000000 / 6228976993627) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (2522359291 / 1000000000) (504471859 / 200000000) (Real.log (6228976993627 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (6228976993627 / 500000000000) = -Real.log (500000000000 / 6228976993627) := by
    rw [show ((6228976993627 / 500000000000) : ℝ) = ((500000000000 / 6228976993627) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1272122973 / 500000000) ≤ -Real.log (125000000000 / 1591702831873) ∧
    -Real.log (125000000000 / 1591702831873) ≤ (50884919 / 20000000) := by
  have h := checkLog_sound (w := (591702831873 / 2591702831873)) (n := 12)
    (lo := (232402203 / 500000000)) (hi := (464804407 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1591702831873 / 1000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1591702831873 / 1000000000000) = 1/(125000000000 / 1591702831873) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1272122973 / 500000000) (50884919 / 20000000) (Real.log (1591702831873 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1591702831873 / 125000000000) = -Real.log (125000000000 / 1591702831873) := by
    rw [show ((1591702831873 / 125000000000) : ℝ) = ((125000000000 / 1591702831873) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (482502549 / 200000000) ≤ -Real.log (250000000000 / 2790493289631) ∧
    -Real.log (250000000000 / 2790493289631) ≤ (2412512749 / 1000000000) := by
  have h := checkLog_sound (w := (790493289631 / 4790493289631)) (n := 12)
    (lo := (66614241 / 200000000)) (hi := (166535603 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2790493289631 / 2000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(2790493289631 / 2000000000000) = 1/(250000000000 / 2790493289631) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (482502549 / 200000000) (2412512749 / 1000000000) (Real.log (2790493289631 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (2790493289631 / 250000000000) = -Real.log (250000000000 / 2790493289631) := by
    rw [show ((2790493289631 / 250000000000) : ℝ) = ((250000000000 / 2790493289631) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (1219646943 / 500000000) ≤ -Real.log (500000000000 / 5732471174821) ∧
    -Real.log (500000000000 / 5732471174821) ≤ (243929389 / 100000000) := by
  have h := checkLog_sound (w := (1732471174821 / 9732471174821)) (n := 12)
    (lo := (179926173 / 500000000)) (hi := (359852347 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5732471174821 / 4000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(5732471174821 / 4000000000000) = 1/(500000000000 / 5732471174821) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (1219646943 / 500000000) (243929389 / 100000000) (Real.log (5732471174821 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (5732471174821 / 500000000000) = -Real.log (500000000000 / 5732471174821) := by
    rw [show ((5732471174821 / 500000000000) : ℝ) = ((500000000000 / 5732471174821) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0204
