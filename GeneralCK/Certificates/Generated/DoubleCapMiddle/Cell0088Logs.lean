import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0088
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

theorem reflection_log_1_neg : (343423467 / 1000000000) ≤ -Real.log (2560 / 3609) ∧
    -Real.log (2560 / 3609) ≤ (85855867 / 250000000) := by
  have h := checkLog_sound (w := (1049 / 6169)) (n := 12)
    (lo := (343423467 / 1000000000)) (hi := (85855867 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3609 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3609 / 2560) = 1/(2560 / 3609) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (343423467 / 1000000000) (85855867 / 250000000) (Real.log (3609 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3609 / 2560) = -Real.log (2560 / 3609) := by
    rw [show ((3609 / 2560) : ℝ) = ((2560 / 3609) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (21089423 / 40000000) ≤ -Real.log (1511 / 2560) ∧
    -Real.log (1511 / 2560) ≤ (65904447 / 125000000) := by
  have h := checkLog_sound (w := (1049 / 4071)) (n := 12)
    (lo := (21089423 / 40000000)) (hi := (65904447 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1511) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1511) = 1/(1511 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-65904447 / 125000000) (-21089423 / 40000000) (Real.log (1511 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (171295933 / 500000000) ≤ -Real.log (1280 / 1803) ∧
    -Real.log (1280 / 1803) ≤ (342591867 / 1000000000) := by
  have h := checkLog_sound (w := (523 / 3083)) (n := 12)
    (lo := (171295933 / 500000000)) (hi := (342591867 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1803 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1803 / 1280) = 1/(1280 / 1803) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (171295933 / 500000000) (342591867 / 1000000000) (Real.log (1803 / 1280)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1803 / 1280) = -Real.log (1280 / 1803) := by
    rw [show ((1803 / 1280) : ℝ) = ((1280 / 1803) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (525252103 / 1000000000) ≤ -Real.log (757 / 1280) ∧
    -Real.log (757 / 1280) ≤ (65656513 / 125000000) := by
  have h := checkLog_sound (w := (523 / 2037)) (n := 12)
    (lo := (525252103 / 1000000000)) (hi := (65656513 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 757) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 757) = 1/(757 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-65656513 / 125000000) (-525252103 / 1000000000) (Real.log (757 / 1280)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (18705591 / 31250000) ≤ -Real.log (1280 / 2329) ∧
    -Real.log (1280 / 2329) ≤ (598578913 / 1000000000) := by
  have h := checkLog_sound (w := (1049 / 3609)) (n := 12)
    (lo := (18705591 / 31250000)) (hi := (598578913 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2329 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2329 / 1280) = 1/(1280 / 2329) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (18705591 / 31250000) (598578913 / 1000000000) (Real.log (2329 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2329 / 1280) = -Real.log (1280 / 2329) := by
    rw [show ((2329 / 1280) : ℝ) = ((1280 / 2329) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (342439529 / 200000000) ≤ -Real.log (231 / 1280) ∧
    -Real.log (231 / 1280) ≤ (107012353 / 62500000) := by
  have h := checkLog_sound (w := (89 / 551)) (n := 12)
    (lo := (65180657 / 200000000)) (hi := (162951643 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 231) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(320 / 231) = 1/(231 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-107012353 / 62500000) (-342439529 / 200000000) (Real.log (231 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (74661247 / 125000000) ≤ -Real.log (640 / 1163) ∧
    -Real.log (640 / 1163) ≤ (597289977 / 1000000000) := by
  have h := checkLog_sound (w := (523 / 1803)) (n := 12)
    (lo := (74661247 / 125000000)) (hi := (597289977 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1163 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1163 / 640) = 1/(640 / 1163) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (74661247 / 125000000) (597289977 / 1000000000) (Real.log (1163 / 640)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1163 / 640) = -Real.log (640 / 1163) := by
    rw [show ((1163 / 640) : ℝ) = ((640 / 1163) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (10620589 / 6250000) ≤ -Real.log (117 / 640) ∧
    -Real.log (117 / 640) ≤ (1699294243 / 1000000000) := by
  have h := checkLog_sound (w := (43 / 277)) (n := 12)
    (lo := (7824997 / 25000000)) (hi := (312999881 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 117) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(160 / 117) = 1/(117 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1699294243 / 1000000000) (-10620589 / 6250000) (Real.log (117 / 640)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (29428017 / 62500000) ≤ -Real.log (125000 / 200169) ∧
    -Real.log (125000 / 200169) ≤ (470848273 / 1000000000) := by
  have h := checkLog_sound (w := (75169 / 325169)) (n := 12)
    (lo := (29428017 / 62500000)) (hi := (470848273 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200169 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200169 / 125000) = 1/(125000 / 200169) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (29428017 / 62500000) (470848273 / 1000000000) (Real.log (200169 / 125000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (200169 / 125000) = -Real.log (125000 / 200169) := by
    rw [show ((200169 / 125000) : ℝ) = ((125000 / 200169) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (114959557 / 125000000) ≤ -Real.log (49831 / 125000) ∧
    -Real.log (49831 / 125000) ≤ (459838229 / 500000000) := by
  have h := checkLog_sound (w := (12669 / 112331)) (n := 12)
    (lo := (56632319 / 250000000)) (hi := (226529277 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 49831) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(62500 / 49831) = 1/(49831 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-459838229 / 500000000) (-114959557 / 125000000) (Real.log (49831 / 125000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (472058391 / 1000000000) ≤ -Real.log (1000000 / 1603291) ∧
    -Real.log (1000000 / 1603291) ≤ (59007299 / 125000000) := by
  have h := checkLog_sound (w := (603291 / 2603291)) (n := 12)
    (lo := (472058391 / 1000000000)) (hi := (59007299 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1603291 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1603291 / 1000000) = 1/(1000000 / 1603291) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (472058391 / 1000000000) (59007299 / 125000000) (Real.log (1603291 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1603291 / 1000000) = -Real.log (1000000 / 1603291) := by
    rw [show ((1603291 / 1000000) : ℝ) = ((1000000 / 1603291) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (924552263 / 1000000000) ≤ -Real.log (396709 / 1000000) ∧
    -Real.log (396709 / 1000000) ≤ (184910453 / 200000000) := by
  have h := checkLog_sound (w := (103291 / 896709)) (n := 12)
    (lo := (231405083 / 1000000000)) (hi := (57851271 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 396709) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 396709) = 1/(396709 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-184910453 / 200000000) (-924552263 / 1000000000) (Real.log (396709 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (38671101 / 100000000) ≤ -Real.log (1000000 / 1472131) ∧
    -Real.log (1000000 / 1472131) ≤ (386711011 / 1000000000) := by
  have h := checkLog_sound (w := (472131 / 2472131)) (n := 12)
    (lo := (38671101 / 100000000)) (hi := (386711011 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1472131 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1472131 / 1000000) = 1/(1000000 / 1472131) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (38671101 / 100000000) (386711011 / 1000000000) (Real.log (1472131 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1472131 / 1000000) = -Real.log (1000000 / 1472131) := by
    rw [show ((1472131 / 1000000) : ℝ) = ((1000000 / 1472131) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (159726783 / 250000000) ≤ -Real.log (527869 / 1000000) ∧
    -Real.log (527869 / 1000000) ≤ (638907133 / 1000000000) := by
  have h := checkLog_sound (w := (472131 / 1527869)) (n := 12)
    (lo := (159726783 / 250000000)) (hi := (638907133 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 527869) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 527869) = 1/(527869 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-638907133 / 1000000000) (-159726783 / 250000000) (Real.log (527869 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (77594059 / 200000000) ≤ -Real.log (500000 / 736993) ∧
    -Real.log (500000 / 736993) ≤ (48496287 / 125000000) := by
  have h := checkLog_sound (w := (236993 / 1236993)) (n := 12)
    (lo := (77594059 / 200000000)) (hi := (48496287 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((736993 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(736993 / 500000) = 1/(500000 / 736993) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (77594059 / 200000000) (48496287 / 125000000) (Real.log (736993 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (736993 / 500000) = -Real.log (500000 / 736993) := by
    rw [show ((736993 / 500000) : ℝ) = ((500000 / 736993) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (12848549 / 20000000) ≤ -Real.log (263007 / 500000) ∧
    -Real.log (263007 / 500000) ≤ (642427451 / 1000000000) := by
  have h := checkLog_sound (w := (236993 / 763007)) (n := 12)
    (lo := (12848549 / 20000000)) (hi := (642427451 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 263007) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 263007) = 1/(263007 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-642427451 / 1000000000) (-12848549 / 20000000) (Real.log (263007 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (173815591 / 125000000) ≤ -Real.log (500000000000 / 2008478657863) ∧
    -Real.log (500000000000 / 2008478657863) ≤ (1390524731 / 1000000000) := by
  have h := checkLog_sound (w := (8478657863 / 4008478657863)) (n := 12)
    (lo := (132199 / 31250000)) (hi := (4230369 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2008478657863 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2008478657863 / 2000000000000) = 1/(500000000000 / 2008478657863) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (173815591 / 125000000) (1390524731 / 1000000000) (Real.log (2008478657863 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (2008478657863 / 500000000000) = -Real.log (500000000000 / 2008478657863) := by
    rw [show ((2008478657863 / 500000000000) : ℝ) = ((500000000000 / 2008478657863) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (279322131 / 200000000) ≤ -Real.log (125000000000 / 505184845819) ∧
    -Real.log (125000000000 / 505184845819) ≤ (698305329 / 500000000) := by
  have h := checkLog_sound (w := (5184845819 / 1005184845819)) (n := 12)
    (lo := (2063259 / 200000000)) (hi := (1289537 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((505184845819 / 500000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(505184845819 / 500000000000) = 1/(125000000000 / 505184845819) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (279322131 / 200000000) (698305329 / 500000000) (Real.log (505184845819 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (505184845819 / 125000000000) = -Real.log (125000000000 / 505184845819) := by
    rw [show ((505184845819 / 125000000000) : ℝ) = ((125000000000 / 505184845819) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (512809071 / 500000000) ≤ -Real.log (250000000000 / 697204704197) ∧
    -Real.log (250000000000 / 697204704197) ≤ (32050567 / 31250000) := by
  have h := checkLog_sound (w := (197204704197 / 1197204704197)) (n := 12)
    (lo := (166235481 / 500000000)) (hi := (332470963 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((697204704197 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(697204704197 / 500000000000) = 1/(250000000000 / 697204704197) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (512809071 / 500000000) (32050567 / 31250000) (Real.log (697204704197 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (697204704197 / 250000000000) = -Real.log (250000000000 / 697204704197) := by
    rw [show ((697204704197 / 250000000000) : ℝ) = ((250000000000 / 697204704197) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (206079549 / 200000000) ≤ -Real.log (100000000000 / 280218017011) ∧
    -Real.log (100000000000 / 280218017011) ≤ (1030397747 / 1000000000) := by
  have h := checkLog_sound (w := (80218017011 / 480218017011)) (n := 12)
    (lo := (67450113 / 200000000)) (hi := (168625283 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((280218017011 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(280218017011 / 200000000000) = 1/(100000000000 / 280218017011) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (206079549 / 200000000) (1030397747 / 1000000000) (Real.log (280218017011 / 100000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (280218017011 / 100000000000) = -Real.log (100000000000 / 280218017011) := by
    rw [show ((280218017011 / 100000000000) : ℝ) = ((100000000000 / 280218017011) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0088
