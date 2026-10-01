import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell243
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

theorem reflection_log_1_neg : (16571863 / 50000000) ≤ -Real.log (1280 / 1783) ∧
    -Real.log (1280 / 1783) ≤ (331437261 / 1000000000) := by
  have h := checkLog_sound (w := (503 / 3063)) (n := 12)
    (lo := (16571863 / 50000000)) (hi := (331437261 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1783 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1783 / 1280) = 1/(1280 / 1783) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (16571863 / 50000000) (331437261 / 1000000000) (Real.log (1783 / 1280)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1783 / 1280) = -Real.log (1280 / 1783) := by
    rw [show ((1783 / 1280) : ℝ) = ((1280 / 1783) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (249587503 / 500000000) ≤ -Real.log (777 / 1280) ∧
    -Real.log (777 / 1280) ≤ (499175007 / 1000000000) := by
  have h := checkLog_sound (w := (503 / 2057)) (n := 12)
    (lo := (249587503 / 500000000)) (hi := (499175007 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 777) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 777) = 1/(777 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-499175007 / 1000000000) (-249587503 / 500000000) (Real.log (777 / 1280)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (331016533 / 1000000000) ≤ -Real.log (5120 / 7129) ∧
    -Real.log (5120 / 7129) ≤ (165508267 / 500000000) := by
  have h := checkLog_sound (w := (2009 / 12249)) (n := 12)
    (lo := (331016533 / 1000000000)) (hi := (165508267 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7129 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7129 / 5120) = 1/(5120 / 7129) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (331016533 / 1000000000) (165508267 / 500000000) (Real.log (7129 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (7129 / 5120) = -Real.log (5120 / 7129) := by
    rw [show ((7129 / 5120) : ℝ) = ((5120 / 7129) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (498210221 / 1000000000) ≤ -Real.log (3111 / 5120) ∧
    -Real.log (3111 / 5120) ≤ (249105111 / 500000000) := by
  have h := checkLog_sound (w := (2009 / 8231)) (n := 12)
    (lo := (498210221 / 1000000000)) (hi := (249105111 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3111) = 1/(3111 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-249105111 / 500000000) (-498210221 / 1000000000) (Real.log (3111 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (15397497 / 62500000) ≤ -Real.log (3125 / 3998) ∧
    -Real.log (3125 / 3998) ≤ (246359953 / 1000000000) := by
  have h := checkLog_sound (w := (873 / 7123)) (n := 12)
    (lo := (15397497 / 62500000)) (hi := (246359953 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3998 / 3125) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3998 / 3125) = 1/(3125 / 3998) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (15397497 / 62500000) (246359953 / 1000000000) (Real.log (3998 / 3125)) := by
  have h := reflection_log_5_neg
  have he : Real.log (3998 / 3125) = -Real.log (3125 / 3998) := by
    rw [show ((3998 / 3125) : ℝ) = ((3125 / 3998) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (81903893 / 250000000) ≤ -Real.log (2252 / 3125) ∧
    -Real.log (2252 / 3125) ≤ (327615573 / 1000000000) := by
  have h := checkLog_sound (w := (873 / 5377)) (n := 12)
    (lo := (81903893 / 250000000)) (hi := (327615573 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3125 / 2252) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3125 / 2252) = 1/(2252 / 3125) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-327615573 / 1000000000) (-81903893 / 250000000) (Real.log (2252 / 3125)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (246691313 / 1000000000) ≤ -Real.log (125000 / 159973) ∧
    -Real.log (125000 / 159973) ≤ (123345657 / 500000000) := by
  have h := checkLog_sound (w := (34973 / 284973)) (n := 12)
    (lo := (246691313 / 1000000000)) (hi := (123345657 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((159973 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(159973 / 125000) = 1/(125000 / 159973) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (246691313 / 1000000000) (123345657 / 500000000) (Real.log (159973 / 125000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (159973 / 125000) = -Real.log (125000 / 159973) := by
    rw [show ((159973 / 125000) : ℝ) = ((125000 / 159973) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (328204111 / 1000000000) ≤ -Real.log (90027 / 125000) ∧
    -Real.log (90027 / 125000) ≤ (20512757 / 62500000) := by
  have h := checkLog_sound (w := (34973 / 215027)) (n := 12)
    (lo := (328204111 / 1000000000)) (hi := (20512757 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 90027) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 90027) = 1/(90027 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-20512757 / 62500000) (-328204111 / 1000000000) (Real.log (90027 / 125000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (183904469 / 1000000000) ≤ -Real.log (1000000 / 1201901) ∧
    -Real.log (1000000 / 1201901) ≤ (18390447 / 100000000) := by
  have h := checkLog_sound (w := (201901 / 2201901)) (n := 12)
    (lo := (183904469 / 1000000000)) (hi := (18390447 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1201901 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1201901 / 1000000) = 1/(1000000 / 1201901) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (183904469 / 1000000000) (18390447 / 100000000) (Real.log (1201901 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1201901 / 1000000) = -Real.log (1000000 / 1201901) := by
    rw [show ((1201901 / 1000000) : ℝ) = ((1000000 / 1201901) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (225522629 / 1000000000) ≤ -Real.log (798099 / 1000000) ∧
    -Real.log (798099 / 1000000) ≤ (22552263 / 100000000) := by
  have h := checkLog_sound (w := (201901 / 1798099)) (n := 12)
    (lo := (225522629 / 1000000000)) (hi := (22552263 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 798099) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 798099) = 1/(798099 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-22552263 / 100000000) (-225522629 / 1000000000) (Real.log (798099 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (184170679 / 1000000000) ≤ -Real.log (1000000 / 1202221) ∧
    -Real.log (1000000 / 1202221) ≤ (4604267 / 25000000) := by
  have h := checkLog_sound (w := (202221 / 2202221)) (n := 12)
    (lo := (184170679 / 1000000000)) (hi := (4604267 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1202221 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1202221 / 1000000) = 1/(1000000 / 1202221) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (184170679 / 1000000000) (4604267 / 25000000) (Real.log (1202221 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1202221 / 1000000) = -Real.log (1000000 / 1202221) := by
    rw [show ((1202221 / 1000000) : ℝ) = ((1000000 / 1202221) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (112961831 / 500000000) ≤ -Real.log (797779 / 1000000) ∧
    -Real.log (797779 / 1000000) ≤ (225923663 / 1000000000) := by
  have h := checkLog_sound (w := (202221 / 1797779)) (n := 12)
    (lo := (112961831 / 500000000)) (hi := (225923663 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 797779) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 797779) = 1/(797779 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-225923663 / 1000000000) (-112961831 / 500000000) (Real.log (797779 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (829226753 / 1000000000) ≤ -Real.log (500000000000 / 1145773063323) ∧
    -Real.log (500000000000 / 1145773063323) ≤ (165845351 / 200000000) := by
  have h := checkLog_sound (w := (145773063323 / 2145773063323)) (n := 12)
    (lo := (136079573 / 1000000000)) (hi := (68039787 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1145773063323 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1145773063323 / 1000000000000) = 1/(500000000000 / 1145773063323) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (829226753 / 1000000000) (165845351 / 200000000) (Real.log (1145773063323 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1145773063323 / 500000000000) = -Real.log (500000000000 / 1145773063323) := by
    rw [show ((1145773063323 / 500000000000) : ℝ) = ((500000000000 / 1145773063323) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (415306133 / 500000000) ≤ -Real.log (250000000000 / 573680823681) ∧
    -Real.log (250000000000 / 573680823681) ≤ (207653067 / 250000000) := by
  have h := checkLog_sound (w := (73680823681 / 1073680823681)) (n := 12)
    (lo := (68732543 / 500000000)) (hi := (137465087 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((573680823681 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(573680823681 / 500000000000) = 1/(250000000000 / 573680823681) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (415306133 / 500000000) (207653067 / 250000000) (Real.log (573680823681 / 250000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (573680823681 / 250000000000) = -Real.log (250000000000 / 573680823681) := by
    rw [show ((573680823681 / 250000000000) : ℝ) = ((250000000000 / 573680823681) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (22959021 / 40000000) ≤ -Real.log (250000000000 / 443827708703) ∧
    -Real.log (250000000000 / 443827708703) ≤ (286987763 / 500000000) := by
  have h := checkLog_sound (w := (193827708703 / 693827708703)) (n := 12)
    (lo := (22959021 / 40000000)) (hi := (286987763 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((443827708703 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(443827708703 / 250000000000) = 1/(250000000000 / 443827708703) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (22959021 / 40000000) (286987763 / 500000000) (Real.log (443827708703 / 250000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (443827708703 / 250000000000) = -Real.log (250000000000 / 443827708703) := by
    rw [show ((443827708703 / 250000000000) : ℝ) = ((250000000000 / 443827708703) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (22995817 / 40000000) ≤ -Real.log (100000000000 / 177694469437) ∧
    -Real.log (100000000000 / 177694469437) ≤ (287447713 / 500000000) := by
  have h := checkLog_sound (w := (77694469437 / 277694469437)) (n := 12)
    (lo := (22995817 / 40000000)) (hi := (287447713 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((177694469437 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(177694469437 / 100000000000) = 1/(100000000000 / 177694469437) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (22995817 / 40000000) (287447713 / 500000000) (Real.log (177694469437 / 100000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (177694469437 / 100000000000) = -Real.log (100000000000 / 177694469437) := by
    rw [show ((177694469437 / 100000000000) : ℝ) = ((100000000000 / 177694469437) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (409427099 / 1000000000) ≤ -Real.log (500000000000 / 752977387517) ∧
    -Real.log (500000000000 / 752977387517) ≤ (4094271 / 10000000) := by
  have h := checkLog_sound (w := (252977387517 / 1252977387517)) (n := 12)
    (lo := (409427099 / 1000000000)) (hi := (4094271 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((752977387517 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(752977387517 / 500000000000) = 1/(500000000000 / 752977387517) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (409427099 / 1000000000) (4094271 / 10000000) (Real.log (752977387517 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (752977387517 / 500000000000) = -Real.log (500000000000 / 752977387517) := by
    rw [show ((752977387517 / 500000000000) : ℝ) = ((500000000000 / 752977387517) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (410094341 / 1000000000) ≤ -Real.log (250000000000 / 376739986889) ∧
    -Real.log (250000000000 / 376739986889) ≤ (205047171 / 500000000) := by
  have h := checkLog_sound (w := (126739986889 / 626739986889)) (n := 12)
    (lo := (410094341 / 1000000000)) (hi := (205047171 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((376739986889 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(376739986889 / 250000000000) = 1/(250000000000 / 376739986889) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (410094341 / 1000000000) (205047171 / 500000000) (Real.log (376739986889 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (376739986889 / 250000000000) = -Real.log (250000000000 / 376739986889) := by
    rw [show ((376739986889 / 250000000000) : ℝ) = ((250000000000 / 376739986889) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (20876491 / 500000000) ≤ -Real.log (959106667159 / 1000000000000) ∧
    -Real.log (959106667159 / 1000000000000) ≤ (41752983 / 1000000000) := by
  have h := checkLog_sound (w := (40893332841 / 1959106667159)) (n := 12)
    (lo := (20876491 / 500000000)) (hi := (41752983 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 959106667159) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 959106667159) = 1/(959106667159 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-41752983 / 1000000000) (-20876491 / 500000000) (Real.log (959106667159 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (41618159 / 1000000000) ≤ -Real.log (959235986199 / 1000000000000) ∧
    -Real.log (959235986199 / 1000000000000) ≤ (520227 / 12500000) := by
  have h := checkLog_sound (w := (40764013801 / 1959235986199)) (n := 12)
    (lo := (41618159 / 1000000000)) (hi := (520227 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 959235986199) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 959235986199) = 1/(959235986199 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-520227 / 12500000) (-41618159 / 1000000000) (Real.log (959235986199 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell243
