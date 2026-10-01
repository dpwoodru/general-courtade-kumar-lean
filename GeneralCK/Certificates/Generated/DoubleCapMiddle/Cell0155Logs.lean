import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0155
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

theorem reflection_log_1_neg : (5722367 / 20000000) ≤ -Real.log (160 / 213) ∧
    -Real.log (160 / 213) ≤ (286118351 / 1000000000) := by
  have h := checkLog_sound (w := (53 / 373)) (n := 12)
    (lo := (5722367 / 20000000)) (hi := (286118351 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((213 / 160) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(213 / 160) = 1/(160 / 213) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (5722367 / 20000000) (286118351 / 1000000000) (Real.log (213 / 160)) := by
  have h := reflection_log_1_neg
  have he : Real.log (213 / 160) = -Real.log (160 / 213) := by
    rw [show ((213 / 160) : ℝ) = ((160 / 213) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (20117249 / 50000000) ≤ -Real.log (107 / 160) ∧
    -Real.log (107 / 160) ≤ (402344981 / 1000000000) := by
  have h := checkLog_sound (w := (53 / 267)) (n := 12)
    (lo := (20117249 / 50000000)) (hi := (402344981 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 107) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(160 / 107) = 1/(107 / 160) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-402344981 / 1000000000) (-20117249 / 50000000) (Real.log (107 / 160)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (285237681 / 1000000000) ≤ -Real.log (512 / 681) ∧
    -Real.log (512 / 681) ≤ (142618841 / 500000000) := by
  have h := checkLog_sound (w := (169 / 1193)) (n := 12)
    (lo := (285237681 / 1000000000)) (hi := (142618841 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((681 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(681 / 512) = 1/(512 / 681) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (285237681 / 1000000000) (142618841 / 500000000) (Real.log (681 / 512)) := by
  have h := reflection_log_3_neg
  have he : Real.log (681 / 512) = -Real.log (512 / 681) := by
    rw [show ((681 / 512) : ℝ) = ((512 / 681) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (400594177 / 1000000000) ≤ -Real.log (343 / 512) ∧
    -Real.log (343 / 512) ≤ (200297089 / 500000000) := by
  have h := checkLog_sound (w := (169 / 855)) (n := 12)
    (lo := (400594177 / 1000000000)) (hi := (200297089 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 343) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 343) = 1/(343 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-200297089 / 500000000) (-400594177 / 1000000000) (Real.log (343 / 512)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (508322493 / 1000000000) ≤ -Real.log (80 / 133) ∧
    -Real.log (80 / 133) ≤ (254161247 / 500000000) := by
  have h := checkLog_sound (w := (53 / 213)) (n := 12)
    (lo := (508322493 / 1000000000)) (hi := (254161247 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((133 / 80) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(133 / 80) = 1/(80 / 133) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (508322493 / 1000000000) (254161247 / 500000000) (Real.log (133 / 80)) := by
  have h := reflection_log_5_neg
  have he : Real.log (133 / 80) = -Real.log (80 / 133) := by
    rw [show ((133 / 80) : ℝ) = ((80 / 133) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (135773721 / 125000000) ≤ -Real.log (27 / 80) ∧
    -Real.log (27 / 80) ≤ (108618977 / 100000000) := by
  have h := checkLog_sound (w := (13 / 67)) (n := 12)
    (lo := (98260647 / 250000000)) (hi := (393042589 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40 / 27) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(40 / 27) = 1/(27 / 80) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-108618977 / 100000000) (-135773721 / 125000000) (Real.log (27 / 80)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (126727931 / 250000000) ≤ -Real.log (256 / 425) ∧
    -Real.log (256 / 425) ≤ (20276469 / 40000000) := by
  have h := checkLog_sound (w := (169 / 681)) (n := 12)
    (lo := (126727931 / 250000000)) (hi := (20276469 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((425 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(425 / 256) = 1/(256 / 425) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (126727931 / 250000000) (20276469 / 40000000) (Real.log (425 / 256)) := by
  have h := reflection_log_7_neg
  have he : Real.log (425 / 256) = -Real.log (256 / 425) := by
    rw [show ((425 / 256) : ℝ) = ((256 / 425) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (43170773 / 40000000) ≤ -Real.log (87 / 256) ∧
    -Real.log (87 / 256) ≤ (1079269327 / 1000000000) := by
  have h := checkLog_sound (w := (41 / 215)) (n := 12)
    (lo := (77224429 / 200000000)) (hi := (193061073 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((128 / 87) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(128 / 87) = 1/(87 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1079269327 / 1000000000) (-43170773 / 40000000) (Real.log (87 / 256)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (390228281 / 1000000000) ≤ -Real.log (500000 / 738659) ∧
    -Real.log (500000 / 738659) ≤ (195114141 / 500000000) := by
  have h := checkLog_sound (w := (238659 / 1238659)) (n := 12)
    (lo := (390228281 / 1000000000)) (hi := (195114141 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((738659 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(738659 / 500000) = 1/(500000 / 738659) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (390228281 / 1000000000) (195114141 / 500000000) (Real.log (738659 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (738659 / 500000) = -Real.log (500000 / 738659) := by
    rw [show ((738659 / 500000) : ℝ) = ((500000 / 738659) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (64878203 / 100000000) ≤ -Real.log (261341 / 500000) ∧
    -Real.log (261341 / 500000) ≤ (648782031 / 1000000000) := by
  have h := checkLog_sound (w := (238659 / 761341)) (n := 12)
    (lo := (64878203 / 100000000)) (hi := (648782031 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 261341) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 261341) = 1/(261341 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-648782031 / 1000000000) (-64878203 / 100000000) (Real.log (261341 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (391439203 / 1000000000) ≤ -Real.log (250000 / 369777) ∧
    -Real.log (250000 / 369777) ≤ (97859801 / 250000000) := by
  have h := checkLog_sound (w := (119777 / 619777)) (n := 12)
    (lo := (391439203 / 1000000000)) (hi := (97859801 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((369777 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(369777 / 250000) = 1/(250000 / 369777) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (391439203 / 1000000000) (97859801 / 250000000) (Real.log (369777 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (369777 / 250000) = -Real.log (250000 / 369777) := by
    rw [show ((369777 / 250000) : ℝ) = ((250000 / 369777) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (81526569 / 125000000) ≤ -Real.log (130223 / 250000) ∧
    -Real.log (130223 / 250000) ≤ (652212553 / 1000000000) := by
  have h := checkLog_sound (w := (119777 / 380223)) (n := 12)
    (lo := (81526569 / 125000000)) (hi := (652212553 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 130223) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 130223) = 1/(130223 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-652212553 / 1000000000) (-81526569 / 125000000) (Real.log (130223 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (307602339 / 1000000000) ≤ -Real.log (6250 / 8501) ∧
    -Real.log (6250 / 8501) ≤ (15380117 / 50000000) := by
  have h := checkLog_sound (w := (2251 / 14751)) (n := 12)
    (lo := (307602339 / 1000000000)) (hi := (15380117 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8501 / 6250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(8501 / 6250) = 1/(6250 / 8501) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (307602339 / 1000000000) (15380117 / 50000000) (Real.log (8501 / 6250)) := by
  have h := reflection_log_13_neg
  have he : Real.log (8501 / 6250) = -Real.log (6250 / 8501) := by
    rw [show ((8501 / 6250) : ℝ) = ((6250 / 8501) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (446537133 / 1000000000) ≤ -Real.log (3999 / 6250) ∧
    -Real.log (3999 / 6250) ≤ (223268567 / 500000000) := by
  have h := checkLog_sound (w := (2251 / 10249)) (n := 12)
    (lo := (446537133 / 1000000000)) (hi := (223268567 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6250 / 3999) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6250 / 3999) = 1/(3999 / 6250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-223268567 / 500000000) (-446537133 / 1000000000) (Real.log (3999 / 6250)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (154364389 / 500000000) ≤ -Real.log (1000000 / 1361693) ∧
    -Real.log (1000000 / 1361693) ≤ (308728779 / 1000000000) := by
  have h := checkLog_sound (w := (361693 / 2361693)) (n := 12)
    (lo := (154364389 / 500000000)) (hi := (308728779 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1361693 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1361693 / 1000000) = 1/(1000000 / 1361693) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (154364389 / 500000000) (308728779 / 1000000000) (Real.log (1361693 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1361693 / 1000000) = -Real.log (1000000 / 1361693) := by
    rw [show ((1361693 / 1000000) : ℝ) = ((1000000 / 1361693) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (5611699 / 12500000) ≤ -Real.log (638307 / 1000000) ∧
    -Real.log (638307 / 1000000) ≤ (448935921 / 1000000000) := by
  have h := checkLog_sound (w := (361693 / 1638307)) (n := 12)
    (lo := (5611699 / 12500000)) (hi := (448935921 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 638307) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 638307) = 1/(638307 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-448935921 / 1000000000) (-5611699 / 12500000) (Real.log (638307 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1039010311 / 1000000000) ≤ -Real.log (125000000000 / 353302294703) ∧
    -Real.log (125000000000 / 353302294703) ≤ (1039010313 / 1000000000) := by
  have h := checkLog_sound (w := (103302294703 / 603302294703)) (n := 12)
    (lo := (345863131 / 1000000000)) (hi := (86465783 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((353302294703 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(353302294703 / 250000000000) = 1/(125000000000 / 353302294703) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1039010311 / 1000000000) (1039010313 / 1000000000) (Real.log (353302294703 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (353302294703 / 125000000000) = -Real.log (125000000000 / 353302294703) := by
    rw [show ((353302294703 / 125000000000) : ℝ) = ((125000000000 / 353302294703) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (208730351 / 200000000) ≤ -Real.log (250000000000 / 709891877779) ∧
    -Real.log (250000000000 / 709891877779) ≤ (1043651757 / 1000000000) := by
  have h := checkLog_sound (w := (209891877779 / 1209891877779)) (n := 12)
    (lo := (14020183 / 40000000)) (hi := (2738317 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((709891877779 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(709891877779 / 500000000000) = 1/(250000000000 / 709891877779) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (208730351 / 200000000) (1043651757 / 1000000000) (Real.log (709891877779 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (709891877779 / 250000000000) = -Real.log (250000000000 / 709891877779) := by
    rw [show ((709891877779 / 250000000000) : ℝ) = ((250000000000 / 709891877779) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (754139473 / 1000000000) ≤ -Real.log (12500000000 / 26572268067) ∧
    -Real.log (12500000000 / 26572268067) ≤ (30165579 / 40000000) := by
  have h := checkLog_sound (w := (1572268067 / 51572268067)) (n := 12)
    (lo := (60992293 / 1000000000)) (hi := (30496147 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((26572268067 / 25000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(26572268067 / 25000000000) = 1/(12500000000 / 26572268067) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (754139473 / 1000000000) (30165579 / 40000000) (Real.log (26572268067 / 12500000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (26572268067 / 12500000000) = -Real.log (12500000000 / 26572268067) := by
    rw [show ((26572268067 / 12500000000) : ℝ) = ((12500000000 / 26572268067) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (378832349 / 500000000) ≤ -Real.log (250000000000 / 533322131827) ∧
    -Real.log (250000000000 / 533322131827) ≤ (7576647 / 10000000) := by
  have h := checkLog_sound (w := (33322131827 / 1033322131827)) (n := 12)
    (lo := (32258759 / 500000000)) (hi := (64517519 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((533322131827 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(533322131827 / 500000000000) = 1/(250000000000 / 533322131827) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (378832349 / 500000000) (7576647 / 10000000) (Real.log (533322131827 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (533322131827 / 250000000000) = -Real.log (250000000000 / 533322131827) := by
    rw [show ((533322131827 / 250000000000) : ℝ) = ((250000000000 / 533322131827) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0155
