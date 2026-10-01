import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0207
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

theorem reflection_log_1_neg : (113771731 / 200000000) ≤ -Real.log (800 / 1413) ∧
    -Real.log (800 / 1413) ≤ (17776833 / 31250000) := by
  have h := checkLog_sound (w := (613 / 2213)) (n := 12)
    (lo := (113771731 / 200000000)) (hi := (17776833 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1413 / 800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1413 / 800) = 1/(800 / 1413) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (113771731 / 200000000) (17776833 / 31250000) (Real.log (1413 / 800)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1413 / 800) = -Real.log (800 / 1413) := by
    rw [show ((1413 / 800) : ℝ) = ((800 / 1413) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (1453503109 / 1000000000) ≤ -Real.log (187 / 800) ∧
    -Real.log (187 / 800) ≤ (181687889 / 125000000) := by
  have h := checkLog_sound (w := (13 / 387)) (n := 12)
    (lo := (67208749 / 1000000000)) (hi := (53767 / 800000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200 / 187) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(200 / 187) = 1/(187 / 800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-181687889 / 125000000) (-1453503109 / 1000000000) (Real.log (187 / 800)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (11309827 / 20000000) ≤ -Real.log (3200 / 5633) ∧
    -Real.log (3200 / 5633) ≤ (565491351 / 1000000000) := by
  have h := checkLog_sound (w := (2433 / 8833)) (n := 12)
    (lo := (11309827 / 20000000)) (hi := (565491351 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5633 / 3200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5633 / 3200) = 1/(3200 / 5633) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (11309827 / 20000000) (565491351 / 1000000000) (Real.log (5633 / 3200)) := by
  have h := reflection_log_3_neg
  have he : Real.log (5633 / 3200) = -Real.log (3200 / 5633) := by
    rw [show ((5633 / 3200) : ℝ) = ((3200 / 5633) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (714209643 / 500000000) ≤ -Real.log (767 / 3200) ∧
    -Real.log (767 / 3200) ≤ (1428419289 / 1000000000) := by
  have h := checkLog_sound (w := (33 / 1567)) (n := 12)
    (lo := (21062463 / 500000000)) (hi := (42124927 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 767) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(800 / 767) = 1/(767 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-1428419289 / 1000000000) (-714209643 / 500000000) (Real.log (767 / 3200)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (106725097 / 250000000) ≤ -Real.log (400 / 613) ∧
    -Real.log (400 / 613) ≤ (426900389 / 1000000000) := by
  have h := checkLog_sound (w := (213 / 1013)) (n := 12)
    (lo := (106725097 / 250000000)) (hi := (426900389 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((613 / 400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(613 / 400) = 1/(400 / 613) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (106725097 / 250000000) (426900389 / 1000000000) (Real.log (613 / 400)) := by
  have h := reflection_log_5_neg
  have he : Real.log (613 / 400) = -Real.log (400 / 613) := by
    rw [show ((613 / 400) : ℝ) = ((400 / 613) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (760355929 / 1000000000) ≤ -Real.log (187 / 400) ∧
    -Real.log (187 / 400) ≤ (760355931 / 1000000000) := by
  have h := checkLog_sound (w := (13 / 387)) (n := 12)
    (lo := (67208749 / 1000000000)) (hi := (53767 / 800000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200 / 187) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(200 / 187) = 1/(187 / 400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-760355931 / 1000000000) (-760355929 / 1000000000) (Real.log (187 / 400)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (209560717 / 500000000) ≤ -Real.log (1600 / 2433) ∧
    -Real.log (1600 / 2433) ≤ (83824287 / 200000000) := by
  have h := checkLog_sound (w := (833 / 4033)) (n := 12)
    (lo := (209560717 / 500000000)) (hi := (83824287 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2433 / 1600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2433 / 1600) = 1/(1600 / 2433) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (209560717 / 500000000) (83824287 / 200000000) (Real.log (2433 / 1600)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2433 / 1600) = -Real.log (1600 / 2433) := by
    rw [show ((2433 / 1600) : ℝ) = ((1600 / 2433) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (367636053 / 500000000) ≤ -Real.log (767 / 1600) ∧
    -Real.log (767 / 1600) ≤ (183818027 / 250000000) := by
  have h := checkLog_sound (w := (33 / 1567)) (n := 12)
    (lo := (21062463 / 500000000)) (hi := (42124927 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 767) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(800 / 767) = 1/(767 / 1600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-183818027 / 250000000) (-367636053 / 500000000) (Real.log (767 / 1600)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (611275843 / 1000000000) ≤ -Real.log (1000000 / 1842781) ∧
    -Real.log (1000000 / 1842781) ≤ (152818961 / 250000000) := by
  have h := checkLog_sound (w := (842781 / 2842781)) (n := 12)
    (lo := (611275843 / 1000000000)) (hi := (152818961 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1842781 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1842781 / 1000000) = 1/(1000000 / 1842781) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (611275843 / 1000000000) (152818961 / 250000000) (Real.log (1842781 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1842781 / 1000000) = -Real.log (1000000 / 1842781) := by
    rw [show ((1842781 / 1000000) : ℝ) = ((1000000 / 1842781) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (92505777 / 50000000) ≤ -Real.log (157219 / 1000000) ∧
    -Real.log (157219 / 1000000) ≤ (1850115543 / 1000000000) := by
  have h := checkLog_sound (w := (92781 / 407219)) (n := 12)
    (lo := (23191059 / 50000000)) (hi := (463821181 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 157219) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(250000 / 157219) = 1/(157219 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-1850115543 / 1000000000) (-92505777 / 50000000) (Real.log (157219 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (306400859 / 500000000) ≤ -Real.log (200000 / 369119) ∧
    -Real.log (200000 / 369119) ≤ (612801719 / 1000000000) := by
  have h := checkLog_sound (w := (169119 / 569119)) (n := 12)
    (lo := (306400859 / 500000000)) (hi := (612801719 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((369119 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(369119 / 200000) = 1/(200000 / 369119) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (306400859 / 500000000) (612801719 / 1000000000) (Real.log (369119 / 200000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (369119 / 200000) = -Real.log (200000 / 369119) := by
    rw [show ((369119 / 200000) : ℝ) = ((200000 / 369119) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1868176257 / 1000000000) ≤ -Real.log (30881 / 200000) ∧
    -Real.log (30881 / 200000) ≤ (93408813 / 50000000) := by
  have h := checkLog_sound (w := (19119 / 80881)) (n := 12)
    (lo := (481881897 / 1000000000)) (hi := (240940949 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 30881) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(50000 / 30881) = 1/(30881 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-93408813 / 50000000) (-1868176257 / 1000000000) (Real.log (30881 / 200000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (300419171 / 500000000) ≤ -Real.log (1000000 / 1823647) ∧
    -Real.log (1000000 / 1823647) ≤ (600838343 / 1000000000) := by
  have h := checkLog_sound (w := (823647 / 2823647)) (n := 12)
    (lo := (300419171 / 500000000)) (hi := (600838343 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1823647 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1823647 / 1000000) = 1/(1000000 / 1823647) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (300419171 / 500000000) (600838343 / 1000000000) (Real.log (1823647 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1823647 / 1000000) = -Real.log (1000000 / 1823647) := by
    rw [show ((1823647 / 1000000) : ℝ) = ((1000000 / 1823647) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (1735267609 / 1000000000) ≤ -Real.log (176353 / 1000000) ∧
    -Real.log (176353 / 1000000) ≤ (433816903 / 250000000) := by
  have h := checkLog_sound (w := (73647 / 426353)) (n := 12)
    (lo := (348973249 / 1000000000)) (hi := (1395893 / 4000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 176353) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(250000 / 176353) = 1/(176353 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-433816903 / 250000000) (-1735267609 / 1000000000) (Real.log (176353 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (75375659 / 125000000) ≤ -Real.log (1000000 / 1827603) ∧
    -Real.log (1000000 / 1827603) ≤ (603005273 / 1000000000) := by
  have h := checkLog_sound (w := (827603 / 2827603)) (n := 12)
    (lo := (75375659 / 125000000)) (hi := (603005273 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1827603 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1827603 / 1000000) = 1/(1000000 / 1827603) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (75375659 / 125000000) (603005273 / 1000000000) (Real.log (1827603 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1827603 / 1000000) = -Real.log (1000000 / 1827603) := by
    rw [show ((1827603 / 1000000) : ℝ) = ((1000000 / 1827603) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (1757955321 / 1000000000) ≤ -Real.log (172397 / 1000000) ∧
    -Real.log (172397 / 1000000) ≤ (439488831 / 250000000) := by
  have h := checkLog_sound (w := (77603 / 422397)) (n := 12)
    (lo := (371660961 / 1000000000)) (hi := (185830481 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 172397) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(250000 / 172397) = 1/(172397 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-439488831 / 250000000) (-1757955321 / 1000000000) (Real.log (172397 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (2461391383 / 1000000000) ≤ -Real.log (195312500 / 2289279057) ∧
    -Real.log (195312500 / 2289279057) ≤ (2461391387 / 1000000000) := by
  have h := checkLog_sound (w := (726779057 / 3851779057)) (n := 12)
    (lo := (381949843 / 1000000000)) (hi := (95487461 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2289279057 / 1562500000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(2289279057 / 1562500000) = 1/(195312500 / 2289279057) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (2461391383 / 1000000000) (2461391387 / 1000000000) (Real.log (2289279057 / 195312500)) := by
  have h := reflection_log_17_neg
  have he : Real.log (2289279057 / 195312500) = -Real.log (195312500 / 2289279057) := by
    rw [show ((2289279057 / 195312500) : ℝ) = ((195312500 / 2289279057) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (99239119 / 40000000) ≤ -Real.log (250000000000 / 2988237103721) ∧
    -Real.log (250000000000 / 2988237103721) ≤ (2480977979 / 1000000000) := by
  have h := checkLog_sound (w := (988237103721 / 4988237103721)) (n := 12)
    (lo := (80307287 / 200000000)) (hi := (100384109 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2988237103721 / 2000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(2988237103721 / 2000000000000) = 1/(250000000000 / 2988237103721) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (99239119 / 40000000) (2480977979 / 1000000000) (Real.log (2988237103721 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (2988237103721 / 250000000000) = -Real.log (250000000000 / 2988237103721) := by
    rw [show ((2988237103721 / 250000000000) : ℝ) = ((250000000000 / 2988237103721) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (2336105951 / 1000000000) ≤ -Real.log (500000000000 / 5170445073233) ∧
    -Real.log (500000000000 / 5170445073233) ≤ (467221191 / 200000000) := by
  have h := checkLog_sound (w := (1170445073233 / 9170445073233)) (n := 12)
    (lo := (256664411 / 1000000000)) (hi := (64166103 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5170445073233 / 4000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(5170445073233 / 4000000000000) = 1/(500000000000 / 5170445073233) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (2336105951 / 1000000000) (467221191 / 200000000) (Real.log (5170445073233 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (5170445073233 / 500000000000) = -Real.log (500000000000 / 5170445073233) := by
    rw [show ((5170445073233 / 500000000000) : ℝ) = ((500000000000 / 5170445073233) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (147560037 / 62500000) ≤ -Real.log (500000000000 / 5300564975029) ∧
    -Real.log (500000000000 / 5300564975029) ≤ (590240149 / 250000000) := by
  have h := checkLog_sound (w := (1300564975029 / 9300564975029)) (n := 12)
    (lo := (70379763 / 250000000)) (hi := (281519053 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5300564975029 / 4000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(5300564975029 / 4000000000000) = 1/(500000000000 / 5300564975029) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (147560037 / 62500000) (590240149 / 250000000) (Real.log (5300564975029 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (5300564975029 / 500000000000) = -Real.log (500000000000 / 5300564975029) := by
    rw [show ((5300564975029 / 500000000000) : ℝ) = ((500000000000 / 5300564975029) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0207
