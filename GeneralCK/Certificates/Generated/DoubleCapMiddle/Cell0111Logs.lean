import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0111
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

theorem reflection_log_1_neg : (81029867 / 250000000) ≤ -Real.log (128 / 177) ∧
    -Real.log (128 / 177) ≤ (324119469 / 1000000000) := by
  have h := checkLog_sound (w := (49 / 305)) (n := 12)
    (lo := (81029867 / 250000000)) (hi := (324119469 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((177 / 128) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(177 / 128) = 1/(128 / 177) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (81029867 / 250000000) (324119469 / 1000000000) (Real.log (177 / 128)) := by
  have h := reflection_log_1_neg
  have he : Real.log (177 / 128) = -Real.log (128 / 177) := by
    rw [show ((177 / 128) : ℝ) = ((128 / 177) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (482582411 / 1000000000) ≤ -Real.log (79 / 128) ∧
    -Real.log (79 / 128) ≤ (120645603 / 250000000) := by
  have h := checkLog_sound (w := (49 / 207)) (n := 12)
    (lo := (482582411 / 1000000000)) (hi := (120645603 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((128 / 79) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(128 / 79) = 1/(79 / 128) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-120645603 / 250000000) (-482582411 / 1000000000) (Real.log (79 / 128)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (323271651 / 1000000000) ≤ -Real.log (2560 / 3537) ∧
    -Real.log (2560 / 3537) ≤ (80817913 / 250000000) := by
  have h := checkLog_sound (w := (977 / 6097)) (n := 12)
    (lo := (323271651 / 1000000000)) (hi := (80817913 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3537 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3537 / 2560) = 1/(2560 / 3537) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (323271651 / 1000000000) (80817913 / 250000000) (Real.log (3537 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3537 / 2560) = -Real.log (2560 / 3537) := by
    rw [show ((3537 / 2560) : ℝ) = ((2560 / 3537) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (480685477 / 1000000000) ≤ -Real.log (1583 / 2560) ∧
    -Real.log (1583 / 2560) ≤ (240342739 / 500000000) := by
  have h := checkLog_sound (w := (977 / 4143)) (n := 12)
    (lo := (480685477 / 1000000000)) (hi := (240342739 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1583) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1583) = 1/(1583 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-240342739 / 500000000) (-480685477 / 1000000000) (Real.log (1583 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (113700947 / 200000000) ≤ -Real.log (64 / 113) ∧
    -Real.log (64 / 113) ≤ (17765773 / 31250000) := by
  have h := checkLog_sound (w := (49 / 177)) (n := 12)
    (lo := (113700947 / 200000000)) (hi := (17765773 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((113 / 64) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(113 / 64) = 1/(64 / 113) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (113700947 / 200000000) (17765773 / 31250000) (Real.log (113 / 64)) := by
  have h := reflection_log_5_neg
  have he : Real.log (113 / 64) = -Real.log (64 / 113) := by
    rw [show ((113 / 64) : ℝ) = ((64 / 113) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1450832881 / 1000000000) ≤ -Real.log (15 / 64) ∧
    -Real.log (15 / 64) ≤ (362708221 / 250000000) := by
  have h := checkLog_sound (w := (1 / 31)) (n := 12)
    (lo := (64538521 / 1000000000)) (hi := (32269261 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((16 / 15) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(16 / 15) = 1/(15 / 64) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-362708221 / 250000000) (-1450832881 / 1000000000) (Real.log (15 / 64)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (567176419 / 1000000000) ≤ -Real.log (1280 / 2257) ∧
    -Real.log (1280 / 2257) ≤ (28358821 / 50000000) := by
  have h := checkLog_sound (w := (977 / 3537)) (n := 12)
    (lo := (567176419 / 1000000000)) (hi := (28358821 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2257 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2257 / 1280) = 1/(1280 / 2257) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (567176419 / 1000000000) (28358821 / 50000000) (Real.log (2257 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2257 / 1280) = -Real.log (1280 / 2257) := by
    rw [show ((2257 / 1280) : ℝ) = ((1280 / 2257) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (28817651 / 20000000) ≤ -Real.log (303 / 1280) ∧
    -Real.log (303 / 1280) ≤ (1440882553 / 1000000000) := by
  have h := checkLog_sound (w := (17 / 623)) (n := 12)
    (lo := (5458819 / 100000000)) (hi := (54588191 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 303) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(320 / 303) = 1/(303 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1440882553 / 1000000000) (-28817651 / 20000000) (Real.log (303 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (443173781 / 1000000000) ≤ -Real.log (1000000 / 1557643) ∧
    -Real.log (1000000 / 1557643) ≤ (221586891 / 500000000) := by
  have h := checkLog_sound (w := (557643 / 2557643)) (n := 12)
    (lo := (443173781 / 1000000000)) (hi := (221586891 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1557643 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1557643 / 1000000) = 1/(1000000 / 1557643) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (443173781 / 1000000000) (221586891 / 500000000) (Real.log (1557643 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1557643 / 1000000) = -Real.log (1000000 / 1557643) := by
    rw [show ((1557643 / 1000000) : ℝ) = ((1000000 / 1557643) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (81563803 / 100000000) ≤ -Real.log (442357 / 1000000) ∧
    -Real.log (442357 / 1000000) ≤ (50977377 / 62500000) := by
  have h := checkLog_sound (w := (57643 / 942357)) (n := 12)
    (lo := (2449817 / 20000000)) (hi := (122490851 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 442357) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 442357) = 1/(442357 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-50977377 / 62500000) (-81563803 / 100000000) (Real.log (442357 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (222187117 / 500000000) ≤ -Real.log (500000 / 779757) ∧
    -Real.log (500000 / 779757) ≤ (88874847 / 200000000) := by
  have h := checkLog_sound (w := (279757 / 1279757)) (n := 12)
    (lo := (222187117 / 500000000)) (hi := (88874847 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((779757 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(779757 / 500000) = 1/(500000 / 779757) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (222187117 / 500000000) (88874847 / 200000000) (Real.log (779757 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (779757 / 500000) = -Real.log (500000 / 779757) := by
    rw [show ((779757 / 500000) : ℝ) = ((500000 / 779757) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (163975323 / 200000000) ≤ -Real.log (220243 / 500000) ∧
    -Real.log (220243 / 500000) ≤ (819876617 / 1000000000) := by
  have h := checkLog_sound (w := (29757 / 470243)) (n := 12)
    (lo := (25345887 / 200000000)) (hi := (31682359 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 220243) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 220243) = 1/(220243 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-819876617 / 1000000000) (-163975323 / 200000000) (Real.log (220243 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (358531419 / 1000000000) ≤ -Real.log (500000 / 715613) ∧
    -Real.log (500000 / 715613) ≤ (17926571 / 50000000) := by
  have h := checkLog_sound (w := (215613 / 1215613)) (n := 12)
    (lo := (358531419 / 1000000000)) (hi := (17926571 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((715613 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(715613 / 500000) = 1/(500000 / 715613) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (358531419 / 1000000000) (17926571 / 50000000) (Real.log (715613 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (715613 / 500000) = -Real.log (500000 / 715613) := by
    rw [show ((715613 / 500000) : ℝ) = ((500000 / 715613) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (564272111 / 1000000000) ≤ -Real.log (284387 / 500000) ∧
    -Real.log (284387 / 500000) ≤ (35267007 / 62500000) := by
  have h := checkLog_sound (w := (215613 / 784387)) (n := 12)
    (lo := (564272111 / 1000000000)) (hi := (35267007 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 284387) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 284387) = 1/(284387 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-35267007 / 62500000) (-564272111 / 1000000000) (Real.log (284387 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (359730371 / 1000000000) ≤ -Real.log (1000000 / 1432943) ∧
    -Real.log (1000000 / 1432943) ≤ (89932593 / 250000000) := by
  have h := checkLog_sound (w := (432943 / 2432943)) (n := 12)
    (lo := (359730371 / 1000000000)) (hi := (89932593 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1432943 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1432943 / 1000000) = 1/(1000000 / 1432943) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (359730371 / 1000000000) (89932593 / 250000000) (Real.log (1432943 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1432943 / 1000000) = -Real.log (1000000 / 1432943) := by
    rw [show ((1432943 / 1000000) : ℝ) = ((1000000 / 1432943) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (567295451 / 1000000000) ≤ -Real.log (567057 / 1000000) ∧
    -Real.log (567057 / 1000000) ≤ (141823863 / 250000000) := by
  have h := checkLog_sound (w := (432943 / 1567057)) (n := 12)
    (lo := (567295451 / 1000000000)) (hi := (141823863 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 567057) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 567057) = 1/(567057 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-141823863 / 250000000) (-567295451 / 1000000000) (Real.log (567057 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1258811811 / 1000000000) ≤ -Real.log (500000000000 / 1760617555503) ∧
    -Real.log (500000000000 / 1760617555503) ≤ (1258811813 / 1000000000) := by
  have h := checkLog_sound (w := (760617555503 / 2760617555503)) (n := 12)
    (lo := (565664631 / 1000000000)) (hi := (70708079 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1760617555503 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1760617555503 / 1000000000000) = 1/(500000000000 / 1760617555503) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1258811811 / 1000000000) (1258811813 / 1000000000) (Real.log (1760617555503 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1760617555503 / 500000000000) = -Real.log (500000000000 / 1760617555503) := by
    rw [show ((1760617555503 / 500000000000) : ℝ) = ((500000000000 / 1760617555503) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1264250849 / 1000000000) ≤ -Real.log (62500000000 / 221277463983) ∧
    -Real.log (62500000000 / 221277463983) ≤ (1264250851 / 1000000000) := by
  have h := checkLog_sound (w := (96277463983 / 346277463983)) (n := 12)
    (lo := (571103669 / 1000000000)) (hi := (57110367 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((221277463983 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(221277463983 / 125000000000) = 1/(62500000000 / 221277463983) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1264250849 / 1000000000) (1264250851 / 1000000000) (Real.log (221277463983 / 62500000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (221277463983 / 62500000000) = -Real.log (62500000000 / 221277463983) := by
    rw [show ((221277463983 / 62500000000) : ℝ) = ((62500000000 / 221277463983) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (92280353 / 100000000) ≤ -Real.log (250000000000 / 629083783717) ∧
    -Real.log (250000000000 / 629083783717) ≤ (230700883 / 250000000) := by
  have h := checkLog_sound (w := (129083783717 / 1129083783717)) (n := 12)
    (lo := (4593127 / 20000000)) (hi := (229656351 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((629083783717 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(629083783717 / 500000000000) = 1/(250000000000 / 629083783717) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (92280353 / 100000000) (230700883 / 250000000) (Real.log (629083783717 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (629083783717 / 250000000000) = -Real.log (250000000000 / 629083783717) := by
    rw [show ((629083783717 / 250000000000) : ℝ) = ((250000000000 / 629083783717) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (463512911 / 500000000) ≤ -Real.log (500000000000 / 1263491148157) ∧
    -Real.log (500000000000 / 1263491148157) ≤ (28969557 / 31250000) := by
  have h := checkLog_sound (w := (263491148157 / 2263491148157)) (n := 12)
    (lo := (116939321 / 500000000)) (hi := (233878643 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1263491148157 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1263491148157 / 1000000000000) = 1/(500000000000 / 1263491148157) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (463512911 / 500000000) (28969557 / 31250000) (Real.log (1263491148157 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1263491148157 / 500000000000) = -Real.log (500000000000 / 1263491148157) := by
    rw [show ((1263491148157 / 500000000000) : ℝ) = ((500000000000 / 1263491148157) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0111
