import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0160
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

theorem reflection_log_1_neg : (322835303 / 500000000) ≤ -Real.log (12800 / 24413) ∧
    -Real.log (12800 / 24413) ≤ (645670607 / 1000000000) := by
  have h := checkLog_sound (w := (11613 / 37213)) (n := 12)
    (lo := (322835303 / 500000000)) (hi := (645670607 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24413 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24413 / 12800) = 1/(12800 / 24413) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (322835303 / 500000000) (645670607 / 1000000000) (Real.log (24413 / 12800)) := by
  have h := reflection_log_1_neg
  have he : Real.log (24413 / 12800) = -Real.log (12800 / 24413) := by
    rw [show ((24413 / 12800) : ℝ) = ((12800 / 24413) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (2378016053 / 1000000000) ≤ -Real.log (1187 / 12800) ∧
    -Real.log (1187 / 12800) ≤ (2378016057 / 1000000000) := by
  have h := checkLog_sound (w := (413 / 2787)) (n := 12)
    (lo := (298574513 / 1000000000)) (hi := (149287257 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1187) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1600 / 1187) = 1/(1187 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-2378016057 / 1000000000) (-2378016053 / 1000000000) (Real.log (1187 / 12800)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (644892029 / 1000000000) ≤ -Real.log (6400 / 12197) ∧
    -Real.log (6400 / 12197) ≤ (64489203 / 100000000) := by
  have h := checkLog_sound (w := (5797 / 18597)) (n := 12)
    (lo := (644892029 / 1000000000)) (hi := (64489203 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12197 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12197 / 6400) = 1/(6400 / 12197) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (644892029 / 1000000000) (64489203 / 100000000) (Real.log (12197 / 6400)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12197 / 6400) = -Real.log (6400 / 12197) := by
    rw [show ((12197 / 6400) : ℝ) = ((6400 / 12197) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (236213607 / 100000000) ≤ -Real.log (603 / 6400) ∧
    -Real.log (603 / 6400) ≤ (1181068037 / 500000000) := by
  have h := checkLog_sound (w := (197 / 1403)) (n := 12)
    (lo := (28269453 / 100000000)) (hi := (282694531 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 603) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(800 / 603) = 1/(603 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-1181068037 / 500000000) (-236213607 / 100000000) (Real.log (603 / 6400)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (595827169 / 1000000000) ≤ -Real.log (6400 / 11613) ∧
    -Real.log (6400 / 11613) ≤ (59582717 / 100000000) := by
  have h := checkLog_sound (w := (5213 / 18013)) (n := 12)
    (lo := (595827169 / 1000000000)) (hi := (59582717 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11613 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11613 / 6400) = 1/(6400 / 11613) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (595827169 / 1000000000) (59582717 / 100000000) (Real.log (11613 / 6400)) := by
  have h := reflection_log_5_neg
  have he : Real.log (11613 / 6400) = -Real.log (6400 / 11613) := by
    rw [show ((11613 / 6400) : ℝ) = ((6400 / 11613) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1684868873 / 1000000000) ≤ -Real.log (1187 / 6400) ∧
    -Real.log (1187 / 6400) ≤ (421217219 / 250000000) := by
  have h := checkLog_sound (w := (413 / 2787)) (n := 12)
    (lo := (298574513 / 1000000000)) (hi := (149287257 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1187) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1600 / 1187) = 1/(1187 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-421217219 / 250000000) (-1684868873 / 1000000000) (Real.log (1187 / 6400)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (148547433 / 250000000) ≤ -Real.log (3200 / 5797) ∧
    -Real.log (3200 / 5797) ≤ (594189733 / 1000000000) := by
  have h := checkLog_sound (w := (2597 / 8997)) (n := 12)
    (lo := (148547433 / 250000000)) (hi := (594189733 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5797 / 3200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5797 / 3200) = 1/(3200 / 5797) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (148547433 / 250000000) (594189733 / 1000000000) (Real.log (5797 / 3200)) := by
  have h := reflection_log_7_neg
  have he : Real.log (5797 / 3200) = -Real.log (3200 / 5797) := by
    rw [show ((5797 / 3200) : ℝ) = ((3200 / 5797) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (166898889 / 100000000) ≤ -Real.log (603 / 3200) ∧
    -Real.log (603 / 3200) ≤ (1668988893 / 1000000000) := by
  have h := checkLog_sound (w := (197 / 1403)) (n := 12)
    (lo := (28269453 / 100000000)) (hi := (282694531 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 603) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(800 / 603) = 1/(603 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1668988893 / 1000000000) (-166898889 / 100000000) (Real.log (603 / 3200)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (656141851 / 1000000000) ≤ -Real.log (500000 / 963671) ∧
    -Real.log (500000 / 963671) ≤ (164035463 / 250000000) := by
  have h := checkLog_sound (w := (463671 / 1463671)) (n := 12)
    (lo := (656141851 / 1000000000)) (hi := (164035463 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((963671 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(963671 / 500000) = 1/(500000 / 963671) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (656141851 / 1000000000) (164035463 / 250000000) (Real.log (963671 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (963671 / 500000) = -Real.log (500000 / 963671) := by
    rw [show ((963671 / 500000) : ℝ) = ((500000 / 963671) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (81937243 / 31250000) ≤ -Real.log (36329 / 500000) ∧
    -Real.log (36329 / 500000) ≤ (131099589 / 50000000) := by
  have h := checkLog_sound (w := (26171 / 98829)) (n := 12)
    (lo := (135637559 / 250000000)) (hi := (542550237 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 36329) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(62500 / 36329) = 1/(36329 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-131099589 / 50000000) (-81937243 / 31250000) (Real.log (36329 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (328337543 / 500000000) ≤ -Real.log (100000 / 192837) ∧
    -Real.log (100000 / 192837) ≤ (656675087 / 1000000000) := by
  have h := checkLog_sound (w := (92837 / 292837)) (n := 12)
    (lo := (328337543 / 500000000)) (hi := (656675087 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((192837 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(192837 / 100000) = 1/(100000 / 192837) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (328337543 / 500000000) (656675087 / 1000000000) (Real.log (192837 / 100000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (192837 / 100000) = -Real.log (100000 / 192837) := by
    rw [show ((192837 / 100000) : ℝ) = ((100000 / 192837) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (164765081 / 62500000) ≤ -Real.log (7163 / 100000) ∧
    -Real.log (7163 / 100000) ≤ (26362413 / 10000000) := by
  have h := checkLog_sound (w := (5337 / 19663)) (n := 12)
    (lo := (139199939 / 250000000)) (hi := (556799757 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12500 / 7163) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(12500 / 7163) = 1/(7163 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-26362413 / 10000000) (-164765081 / 62500000) (Real.log (7163 / 100000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (655072969 / 1000000000) ≤ -Real.log (1000000 / 1925283) ∧
    -Real.log (1000000 / 1925283) ≤ (65507297 / 100000000) := by
  have h := checkLog_sound (w := (925283 / 2925283)) (n := 12)
    (lo := (655072969 / 1000000000)) (hi := (65507297 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1925283 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1925283 / 1000000) = 1/(1000000 / 1925283) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (655072969 / 1000000000) (65507297 / 100000000) (Real.log (1925283 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1925283 / 1000000) = -Real.log (1000000 / 1925283) := by
    rw [show ((1925283 / 1000000) : ℝ) = ((1000000 / 1925283) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (1297023817 / 500000000) ≤ -Real.log (74717 / 1000000) ∧
    -Real.log (74717 / 1000000) ≤ (1297023819 / 500000000) := by
  have h := checkLog_sound (w := (50283 / 199717)) (n := 12)
    (lo := (257303047 / 500000000)) (hi := (102921219 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 74717) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125000 / 74717) = 1/(74717 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-1297023819 / 500000000) (-1297023817 / 500000000) (Real.log (74717 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (655645189 / 1000000000) ≤ -Real.log (200000 / 385277) ∧
    -Real.log (200000 / 385277) ≤ (65564519 / 100000000) := by
  have h := checkLog_sound (w := (185277 / 585277)) (n := 12)
    (lo := (655645189 / 1000000000)) (hi := (65564519 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((385277 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(385277 / 200000) = 1/(200000 / 385277) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (655645189 / 1000000000) (65564519 / 100000000) (Real.log (385277 / 200000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (385277 / 200000) = -Real.log (200000 / 385277) := by
    rw [show ((385277 / 200000) : ℝ) = ((200000 / 385277) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (2608906467 / 1000000000) ≤ -Real.log (14723 / 200000) ∧
    -Real.log (14723 / 200000) ≤ (2608906471 / 1000000000) := by
  have h := checkLog_sound (w := (10277 / 39723)) (n := 12)
    (lo := (529464927 / 1000000000)) (hi := (16545779 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 14723) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(25000 / 14723) = 1/(14723 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-2608906471 / 1000000000) (-2608906467 / 1000000000) (Real.log (14723 / 200000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (3278133627 / 1000000000) ≤ -Real.log (250000000000 / 6631554680833) ∧
    -Real.log (250000000000 / 6631554680833) ≤ (25610419 / 7812500) := by
  have h := checkLog_sound (w := (2631554680833 / 10631554680833)) (n := 12)
    (lo := (505544907 / 1000000000)) (hi := (126386227 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6631554680833 / 4000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(6631554680833 / 4000000000000) = 1/(250000000000 / 6631554680833) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (3278133627 / 1000000000) (25610419 / 7812500) (Real.log (6631554680833 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (6631554680833 / 250000000000) = -Real.log (250000000000 / 6631554680833) := by
    rw [show ((6631554680833 / 250000000000) : ℝ) = ((250000000000 / 6631554680833) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1646458191 / 500000000) ≤ -Real.log (500000000000 / 13460631020523) ∧
    -Real.log (500000000000 / 13460631020523) ≤ (3292916387 / 1000000000) := by
  have h := checkLog_sound (w := (5460631020523 / 21460631020523)) (n := 12)
    (lo := (260163831 / 500000000)) (hi := (520327663 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((13460631020523 / 8000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(13460631020523 / 8000000000000) = 1/(500000000000 / 13460631020523) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1646458191 / 500000000) (3292916387 / 1000000000) (Real.log (13460631020523 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (13460631020523 / 500000000000) = -Real.log (500000000000 / 13460631020523) := by
    rw [show ((13460631020523 / 500000000000) : ℝ) = ((500000000000 / 13460631020523) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (3249120603 / 1000000000) ≤ -Real.log (250000000000 / 6441917502041) ∧
    -Real.log (250000000000 / 6441917502041) ≤ (101535019 / 31250000) := by
  have h := checkLog_sound (w := (2441917502041 / 10441917502041)) (n := 12)
    (lo := (476531883 / 1000000000)) (hi := (119132971 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6441917502041 / 4000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(6441917502041 / 4000000000000) = 1/(250000000000 / 6441917502041) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (3249120603 / 1000000000) (101535019 / 31250000) (Real.log (6441917502041 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (6441917502041 / 250000000000) = -Real.log (250000000000 / 6441917502041) := by
    rw [show ((6441917502041 / 250000000000) : ℝ) = ((250000000000 / 6441917502041) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (408068957 / 125000000) ≤ -Real.log (250000000000 / 6542094002581) ∧
    -Real.log (250000000000 / 6542094002581) ≤ (3264551661 / 1000000000) := by
  have h := checkLog_sound (w := (2542094002581 / 10542094002581)) (n := 12)
    (lo := (61495367 / 125000000)) (hi := (491962937 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6542094002581 / 4000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(6542094002581 / 4000000000000) = 1/(250000000000 / 6542094002581) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (408068957 / 125000000) (3264551661 / 1000000000) (Real.log (6542094002581 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (6542094002581 / 250000000000) = -Real.log (250000000000 / 6542094002581) := by
    rw [show ((6542094002581 / 250000000000) : ℝ) = ((250000000000 / 6542094002581) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0160
