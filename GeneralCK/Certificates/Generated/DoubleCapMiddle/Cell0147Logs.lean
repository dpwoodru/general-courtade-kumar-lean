import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0147
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

theorem reflection_log_1_neg : (293135923 / 1000000000) ≤ -Real.log (320 / 429) ∧
    -Real.log (320 / 429) ≤ (73283981 / 250000000) := by
  have h := checkLog_sound (w := (109 / 749)) (n := 12)
    (lo := (293135923 / 1000000000)) (hi := (73283981 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((429 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(429 / 320) = 1/(320 / 429) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (293135923 / 1000000000) (73283981 / 250000000) (Real.log (429 / 320)) := by
  have h := reflection_log_1_neg
  have he : Real.log (429 / 320) = -Real.log (320 / 429) := by
    rw [show ((429 / 320) : ℝ) = ((320 / 429) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (208231431 / 500000000) ≤ -Real.log (211 / 320) ∧
    -Real.log (211 / 320) ≤ (416462863 / 1000000000) := by
  have h := checkLog_sound (w := (109 / 531)) (n := 12)
    (lo := (208231431 / 500000000)) (hi := (416462863 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 211) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(320 / 211) = 1/(211 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-416462863 / 1000000000) (-208231431 / 500000000) (Real.log (211 / 320)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (146130707 / 500000000) ≤ -Real.log (2560 / 3429) ∧
    -Real.log (2560 / 3429) ≤ (58452283 / 200000000) := by
  have h := checkLog_sound (w := (869 / 5989)) (n := 12)
    (lo := (146130707 / 500000000)) (hi := (58452283 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3429 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3429 / 2560) = 1/(2560 / 3429) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (146130707 / 500000000) (58452283 / 200000000) (Real.log (3429 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3429 / 2560) = -Real.log (2560 / 3429) := by
    rw [show ((3429 / 2560) : ℝ) = ((2560 / 3429) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (103671797 / 250000000) ≤ -Real.log (1691 / 2560) ∧
    -Real.log (1691 / 2560) ≤ (414687189 / 1000000000) := by
  have h := checkLog_sound (w := (869 / 4251)) (n := 12)
    (lo := (103671797 / 250000000)) (hi := (414687189 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1691) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1691) = 1/(1691 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-414687189 / 1000000000) (-103671797 / 250000000) (Real.log (1691 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (129884391 / 250000000) ≤ -Real.log (160 / 269) ∧
    -Real.log (160 / 269) ≤ (103907513 / 200000000) := by
  have h := checkLog_sound (w := (109 / 429)) (n := 12)
    (lo := (129884391 / 250000000)) (hi := (103907513 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((269 / 160) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(269 / 160) = 1/(160 / 269) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (129884391 / 250000000) (103907513 / 200000000) (Real.log (269 / 160)) := by
  have h := reflection_log_5_neg
  have he : Real.log (269 / 160) = -Real.log (160 / 269) := by
    rw [show ((269 / 160) : ℝ) = ((160 / 269) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1143348181 / 1000000000) ≤ -Real.log (51 / 160) ∧
    -Real.log (51 / 160) ≤ (1143348183 / 1000000000) := by
  have h := checkLog_sound (w := (29 / 131)) (n := 12)
    (lo := (450201001 / 1000000000)) (hi := (225100501 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80 / 51) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(80 / 51) = 1/(51 / 160) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1143348183 / 1000000000) (-1143348181 / 1000000000) (Real.log (51 / 160)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (518142539 / 1000000000) ≤ -Real.log (1280 / 2149) ∧
    -Real.log (1280 / 2149) ≤ (25907127 / 50000000) := by
  have h := checkLog_sound (w := (869 / 3429)) (n := 12)
    (lo := (518142539 / 1000000000)) (hi := (25907127 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2149 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2149 / 1280) = 1/(1280 / 2149) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (518142539 / 1000000000) (25907127 / 50000000) (Real.log (2149 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2149 / 1280) = -Real.log (1280 / 2149) := by
    rw [show ((2149 / 1280) : ℝ) = ((1280 / 2149) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (1136022141 / 1000000000) ≤ -Real.log (411 / 1280) ∧
    -Real.log (411 / 1280) ≤ (1136022143 / 1000000000) := by
  have h := checkLog_sound (w := (229 / 1051)) (n := 12)
    (lo := (442874961 / 1000000000)) (hi := (221437481 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 411) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 411) = 1/(411 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1136022143 / 1000000000) (-1136022141 / 1000000000) (Real.log (411 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (2499377 / 6250000) ≤ -Real.log (250000 / 372919) ∧
    -Real.log (250000 / 372919) ≤ (399900321 / 1000000000) := by
  have h := checkLog_sound (w := (122919 / 622919)) (n := 12)
    (lo := (2499377 / 6250000)) (hi := (399900321 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((372919 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(372919 / 250000) = 1/(250000 / 372919) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (2499377 / 6250000) (399900321 / 1000000000) (Real.log (372919 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (372919 / 250000) = -Real.log (250000 / 372919) := by
    rw [show ((372919 / 250000) : ℝ) = ((250000 / 372919) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (676636239 / 1000000000) ≤ -Real.log (127081 / 250000) ∧
    -Real.log (127081 / 250000) ≤ (8457953 / 12500000) := by
  have h := checkLog_sound (w := (122919 / 377081)) (n := 12)
    (lo := (676636239 / 1000000000)) (hi := (8457953 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 127081) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 127081) = 1/(127081 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-8457953 / 12500000) (-676636239 / 1000000000) (Real.log (127081 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (100276907 / 250000000) ≤ -Real.log (500000 / 746739) ∧
    -Real.log (500000 / 746739) ≤ (401107629 / 1000000000) := by
  have h := checkLog_sound (w := (246739 / 1246739)) (n := 12)
    (lo := (100276907 / 250000000)) (hi := (401107629 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((746739 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(746739 / 500000) = 1/(500000 / 746739) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (100276907 / 250000000) (401107629 / 1000000000) (Real.log (746739 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (746739 / 500000) = -Real.log (500000 / 746739) := by
    rw [show ((746739 / 500000) : ℝ) = ((500000 / 746739) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1062793 / 1562500) ≤ -Real.log (253261 / 500000) ∧
    -Real.log (253261 / 500000) ≤ (680187521 / 1000000000) := by
  have h := checkLog_sound (w := (246739 / 753261)) (n := 12)
    (lo := (1062793 / 1562500)) (hi := (680187521 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 253261) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 253261) = 1/(253261 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-680187521 / 1000000000) (-1062793 / 1562500) (Real.log (253261 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (15832059 / 50000000) ≤ -Real.log (100000 / 137251) ∧
    -Real.log (100000 / 137251) ≤ (316641181 / 1000000000) := by
  have h := checkLog_sound (w := (37251 / 237251)) (n := 12)
    (lo := (15832059 / 50000000)) (hi := (316641181 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((137251 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(137251 / 100000) = 1/(100000 / 137251) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (15832059 / 50000000) (316641181 / 1000000000) (Real.log (137251 / 100000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (137251 / 100000) = -Real.log (100000 / 137251) := by
    rw [show ((137251 / 100000) : ℝ) = ((100000 / 137251) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (58253443 / 125000000) ≤ -Real.log (62749 / 100000) ∧
    -Real.log (62749 / 100000) ≤ (93205509 / 200000000) := by
  have h := checkLog_sound (w := (37251 / 162749)) (n := 12)
    (lo := (58253443 / 125000000)) (hi := (93205509 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 62749) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 62749) = 1/(62749 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-93205509 / 200000000) (-58253443 / 125000000) (Real.log (62749 / 100000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (158888569 / 500000000) ≤ -Real.log (100000 / 137407) ∧
    -Real.log (100000 / 137407) ≤ (317777139 / 1000000000) := by
  have h := checkLog_sound (w := (37407 / 237407)) (n := 12)
    (lo := (158888569 / 500000000)) (hi := (317777139 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((137407 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(137407 / 100000) = 1/(100000 / 137407) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (158888569 / 500000000) (317777139 / 1000000000) (Real.log (137407 / 100000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (137407 / 100000) = -Real.log (100000 / 137407) := by
    rw [show ((137407 / 100000) : ℝ) = ((100000 / 137407) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (93703347 / 200000000) ≤ -Real.log (62593 / 100000) ∧
    -Real.log (62593 / 100000) ≤ (3660287 / 7812500) := by
  have h := checkLog_sound (w := (37407 / 162593)) (n := 12)
    (lo := (93703347 / 200000000)) (hi := (3660287 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 62593) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 62593) = 1/(62593 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-3660287 / 7812500) (-93703347 / 200000000) (Real.log (62593 / 100000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (538268279 / 500000000) ≤ -Real.log (25000000000 / 73362461737) ∧
    -Real.log (25000000000 / 73362461737) ≤ (13456707 / 12500000) := by
  have h := checkLog_sound (w := (23362461737 / 123362461737)) (n := 12)
    (lo := (191694689 / 500000000)) (hi := (383389379 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((73362461737 / 50000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(73362461737 / 50000000000) = 1/(25000000000 / 73362461737) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (538268279 / 500000000) (13456707 / 12500000) (Real.log (73362461737 / 25000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (73362461737 / 25000000000) = -Real.log (25000000000 / 73362461737) := by
    rw [show ((73362461737 / 25000000000) : ℝ) = ((25000000000 / 73362461737) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (270323787 / 250000000) ≤ -Real.log (500000000000 / 1474247910259) ∧
    -Real.log (500000000000 / 1474247910259) ≤ (21625903 / 20000000) := by
  have h := checkLog_sound (w := (474247910259 / 2474247910259)) (n := 12)
    (lo := (1516203 / 3906250)) (hi := (388147969 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1474247910259 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1474247910259 / 1000000000000) = 1/(500000000000 / 1474247910259) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (270323787 / 250000000) (21625903 / 20000000) (Real.log (1474247910259 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1474247910259 / 500000000000) = -Real.log (500000000000 / 1474247910259) := by
    rw [show ((1474247910259 / 500000000000) : ℝ) = ((500000000000 / 1474247910259) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (195667181 / 250000000) ≤ -Real.log (250000000000 / 546825447417) ∧
    -Real.log (250000000000 / 546825447417) ≤ (391334363 / 500000000) := by
  have h := checkLog_sound (w := (46825447417 / 1046825447417)) (n := 12)
    (lo := (11190193 / 125000000)) (hi := (17904309 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((546825447417 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(546825447417 / 500000000000) = 1/(250000000000 / 546825447417) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (195667181 / 250000000) (391334363 / 500000000) (Real.log (546825447417 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (546825447417 / 250000000000) = -Real.log (250000000000 / 546825447417) := by
    rw [show ((546825447417 / 250000000000) : ℝ) = ((250000000000 / 546825447417) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (786293873 / 1000000000) ≤ -Real.log (500000000000 / 1097622737367) ∧
    -Real.log (500000000000 / 1097622737367) ≤ (6290351 / 8000000) := by
  have h := checkLog_sound (w := (97622737367 / 2097622737367)) (n := 12)
    (lo := (93146693 / 1000000000)) (hi := (46573347 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1097622737367 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1097622737367 / 1000000000000) = 1/(500000000000 / 1097622737367) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (786293873 / 1000000000) (6290351 / 8000000) (Real.log (1097622737367 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1097622737367 / 500000000000) = -Real.log (500000000000 / 1097622737367) := by
    rw [show ((1097622737367 / 500000000000) : ℝ) = ((500000000000 / 1097622737367) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0147
