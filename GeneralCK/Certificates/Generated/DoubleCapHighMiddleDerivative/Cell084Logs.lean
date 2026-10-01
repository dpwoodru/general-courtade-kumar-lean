import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell084
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

theorem reflection_log_1_neg : (65553503 / 250000000) ≤ -Real.log (1024 / 1331) ∧
    -Real.log (1024 / 1331) ≤ (262214013 / 1000000000) := by
  have h := checkLog_sound (w := (307 / 2355)) (n := 12)
    (lo := (65553503 / 250000000)) (hi := (262214013 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1331 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1331 / 1024) = 1/(1024 / 1331) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (65553503 / 250000000) (262214013 / 1000000000) (Real.log (1331 / 1024)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1331 / 1024) = -Real.log (1024 / 1331) := by
    rw [show ((1331 / 1024) : ℝ) = ((1024 / 1331) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (89098991 / 250000000) ≤ -Real.log (717 / 1024) ∧
    -Real.log (717 / 1024) ≤ (71279193 / 200000000) := by
  have h := checkLog_sound (w := (307 / 1741)) (n := 12)
    (lo := (89098991 / 250000000)) (hi := (71279193 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 717) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 717) = 1/(717 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-71279193 / 200000000) (-89098991 / 250000000) (Real.log (717 / 1024)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (130881561 / 500000000) ≤ -Real.log (1280 / 1663) ∧
    -Real.log (1280 / 1663) ≤ (261763123 / 1000000000) := by
  have h := checkLog_sound (w := (383 / 2943)) (n := 12)
    (lo := (130881561 / 500000000)) (hi := (261763123 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1663 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1663 / 1280) = 1/(1280 / 1663) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (130881561 / 500000000) (261763123 / 1000000000) (Real.log (1663 / 1280)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1663 / 1280) = -Real.log (1280 / 1663) := by
    rw [show ((1663 / 1280) : ℝ) = ((1280 / 1663) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (177779747 / 500000000) ≤ -Real.log (897 / 1280) ∧
    -Real.log (897 / 1280) ≤ (71111899 / 200000000) := by
  have h := checkLog_sound (w := (383 / 2177)) (n := 12)
    (lo := (177779747 / 500000000)) (hi := (71111899 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 897) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 897) = 1/(897 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-71111899 / 200000000) (-177779747 / 500000000) (Real.log (897 / 1280)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (192601041 / 1000000000) ≤ -Real.log (1000000 / 1212399) ∧
    -Real.log (1000000 / 1212399) ≤ (96300521 / 500000000) := by
  have h := checkLog_sound (w := (212399 / 2212399)) (n := 12)
    (lo := (192601041 / 1000000000)) (hi := (96300521 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1212399 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1212399 / 1000000) = 1/(1000000 / 1212399) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (192601041 / 1000000000) (96300521 / 500000000) (Real.log (1212399 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1212399 / 1000000) = -Real.log (1000000 / 1212399) := by
    rw [show ((1212399 / 1000000) : ℝ) = ((1000000 / 1212399) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (119381831 / 500000000) ≤ -Real.log (787601 / 1000000) ∧
    -Real.log (787601 / 1000000) ≤ (238763663 / 1000000000) := by
  have h := checkLog_sound (w := (212399 / 1787601)) (n := 12)
    (lo := (119381831 / 500000000)) (hi := (238763663 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 787601) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 787601) = 1/(787601 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-238763663 / 1000000000) (-119381831 / 500000000) (Real.log (787601 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (96473701 / 500000000) ≤ -Real.log (1000000 / 1212819) ∧
    -Real.log (1000000 / 1212819) ≤ (192947403 / 1000000000) := by
  have h := checkLog_sound (w := (212819 / 2212819)) (n := 12)
    (lo := (96473701 / 500000000)) (hi := (192947403 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1212819 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1212819 / 1000000) = 1/(1000000 / 1212819) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (96473701 / 500000000) (192947403 / 1000000000) (Real.log (1212819 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1212819 / 1000000) = -Real.log (1000000 / 1212819) := by
    rw [show ((1212819 / 1000000) : ℝ) = ((1000000 / 1212819) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (239297069 / 1000000000) ≤ -Real.log (787181 / 1000000) ∧
    -Real.log (787181 / 1000000) ≤ (23929707 / 100000000) := by
  have h := checkLog_sound (w := (212819 / 1787181)) (n := 12)
    (lo := (239297069 / 1000000000)) (hi := (23929707 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 787181) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 787181) = 1/(787181 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-23929707 / 100000000) (-239297069 / 1000000000) (Real.log (787181 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (35394421 / 250000000) ≤ -Real.log (100000 / 115209) ∧
    -Real.log (100000 / 115209) ≤ (28315537 / 200000000) := by
  have h := checkLog_sound (w := (15209 / 215209)) (n := 12)
    (lo := (35394421 / 250000000)) (hi := (28315537 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((115209 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(115209 / 100000) = 1/(100000 / 115209) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (35394421 / 250000000) (28315537 / 200000000) (Real.log (115209 / 100000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (115209 / 100000) = -Real.log (100000 / 115209) := by
    rw [show ((115209 / 100000) : ℝ) = ((100000 / 115209) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (8249039 / 50000000) ≤ -Real.log (84791 / 100000) ∧
    -Real.log (84791 / 100000) ≤ (164980781 / 1000000000) := by
  have h := checkLog_sound (w := (15209 / 184791)) (n := 12)
    (lo := (8249039 / 50000000)) (hi := (164980781 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 84791) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 84791) = 1/(84791 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-164980781 / 1000000000) (-8249039 / 50000000) (Real.log (84791 / 100000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (4432683 / 31250000) ≤ -Real.log (1000000 / 1152399) ∧
    -Real.log (1000000 / 1152399) ≤ (141845857 / 1000000000) := by
  have h := checkLog_sound (w := (152399 / 2152399)) (n := 12)
    (lo := (4432683 / 31250000)) (hi := (141845857 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1152399 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1152399 / 1000000) = 1/(1000000 / 1152399) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (4432683 / 31250000) (141845857 / 1000000000) (Real.log (1152399 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1152399 / 1000000) = -Real.log (1000000 / 1152399) := by
    rw [show ((1152399 / 1000000) : ℝ) = ((1000000 / 1152399) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (20668159 / 125000000) ≤ -Real.log (847601 / 1000000) ∧
    -Real.log (847601 / 1000000) ≤ (165345273 / 1000000000) := by
  have h := checkLog_sound (w := (152399 / 1847601)) (n := 12)
    (lo := (20668159 / 125000000)) (hi := (165345273 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 847601) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 847601) = 1/(847601 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-165345273 / 1000000000) (-20668159 / 125000000) (Real.log (847601 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (617322617 / 1000000000) ≤ -Real.log (500000000000 / 926978818283) ∧
    -Real.log (500000000000 / 926978818283) ≤ (308661309 / 500000000) := by
  have h := checkLog_sound (w := (426978818283 / 1426978818283)) (n := 12)
    (lo := (617322617 / 1000000000)) (hi := (308661309 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((926978818283 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(926978818283 / 500000000000) = 1/(500000000000 / 926978818283) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (617322617 / 1000000000) (308661309 / 500000000) (Real.log (926978818283 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (926978818283 / 500000000000) = -Real.log (500000000000 / 926978818283) := by
    rw [show ((926978818283 / 500000000000) : ℝ) = ((500000000000 / 926978818283) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (618609977 / 1000000000) ≤ -Real.log (250000000000 / 464086471409) ∧
    -Real.log (250000000000 / 464086471409) ≤ (309304989 / 500000000) := by
  have h := checkLog_sound (w := (214086471409 / 714086471409)) (n := 12)
    (lo := (618609977 / 1000000000)) (hi := (309304989 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((464086471409 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(464086471409 / 250000000000) = 1/(250000000000 / 464086471409) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (618609977 / 1000000000) (309304989 / 500000000) (Real.log (464086471409 / 250000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (464086471409 / 250000000000) = -Real.log (250000000000 / 464086471409) := by
    rw [show ((464086471409 / 250000000000) : ℝ) = ((250000000000 / 464086471409) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (431364703 / 1000000000) ≤ -Real.log (3906250000 / 6013112723) ∧
    -Real.log (3906250000 / 6013112723) ≤ (13480147 / 31250000) := by
  have h := checkLog_sound (w := (2106862723 / 9919362723)) (n := 12)
    (lo := (431364703 / 1000000000)) (hi := (13480147 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6013112723 / 3906250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6013112723 / 3906250000) = 1/(3906250000 / 6013112723) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (431364703 / 1000000000) (13480147 / 31250000) (Real.log (6013112723 / 3906250000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (6013112723 / 3906250000) = -Real.log (3906250000 / 6013112723) := by
    rw [show ((6013112723 / 3906250000) : ℝ) = ((3906250000 / 6013112723) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (432244471 / 1000000000) ≤ -Real.log (500000000000 / 770355864789) ∧
    -Real.log (500000000000 / 770355864789) ≤ (54030559 / 125000000) := by
  have h := checkLog_sound (w := (270355864789 / 1270355864789)) (n := 12)
    (lo := (432244471 / 1000000000)) (hi := (54030559 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((770355864789 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(770355864789 / 500000000000) = 1/(500000000000 / 770355864789) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (432244471 / 1000000000) (54030559 / 125000000) (Real.log (770355864789 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (770355864789 / 500000000000) = -Real.log (500000000000 / 770355864789) := by
    rw [show ((770355864789 / 500000000000) : ℝ) = ((500000000000 / 770355864789) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (61311693 / 200000000) ≤ -Real.log (125000000000 / 169842613013) ∧
    -Real.log (125000000000 / 169842613013) ≤ (153279233 / 500000000) := by
  have h := checkLog_sound (w := (44842613013 / 294842613013)) (n := 12)
    (lo := (61311693 / 200000000)) (hi := (153279233 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((169842613013 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(169842613013 / 125000000000) = 1/(125000000000 / 169842613013) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (61311693 / 200000000) (153279233 / 500000000) (Real.log (169842613013 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (169842613013 / 125000000000) = -Real.log (125000000000 / 169842613013) := by
    rw [show ((169842613013 / 125000000000) : ℝ) = ((125000000000 / 169842613013) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (307191129 / 1000000000) ≤ -Real.log (500000000000 / 679800401369) ∧
    -Real.log (500000000000 / 679800401369) ≤ (30719113 / 100000000) := by
  have h := checkLog_sound (w := (179800401369 / 1179800401369)) (n := 12)
    (lo := (307191129 / 1000000000)) (hi := (30719113 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((679800401369 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(679800401369 / 500000000000) = 1/(500000000000 / 679800401369) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (307191129 / 1000000000) (30719113 / 100000000) (Real.log (679800401369 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (679800401369 / 500000000000) = -Real.log (500000000000 / 679800401369) := by
    rw [show ((679800401369 / 500000000000) : ℝ) = ((500000000000 / 679800401369) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (2937427 / 125000000) ≤ -Real.log (976774544799 / 1000000000000) ∧
    -Real.log (976774544799 / 1000000000000) ≤ (23499417 / 1000000000) := by
  have h := checkLog_sound (w := (23225455201 / 1976774544799)) (n := 12)
    (lo := (2937427 / 125000000)) (hi := (23499417 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 976774544799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 976774544799) = 1/(976774544799 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-23499417 / 1000000000) (-2937427 / 125000000) (Real.log (976774544799 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (2925387 / 125000000) ≤ -Real.log (9768686319 / 10000000000) ∧
    -Real.log (9768686319 / 10000000000) ≤ (23403097 / 1000000000) := by
  have h := checkLog_sound (w := (231313681 / 19768686319)) (n := 12)
    (lo := (2925387 / 125000000)) (hi := (23403097 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 9768686319) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 9768686319) = 1/(9768686319 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-23403097 / 1000000000) (-2925387 / 125000000) (Real.log (9768686319 / 10000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell084
