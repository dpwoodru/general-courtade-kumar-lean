import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0069
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

theorem reflection_log_1_neg : (677269847 / 1000000000) ≤ -Real.log (51200 / 100787) ∧
    -Real.log (51200 / 100787) ≤ (84658731 / 125000000) := by
  have h := checkLog_sound (w := (49587 / 151987)) (n := 12)
    (lo := (677269847 / 1000000000)) (hi := (84658731 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100787 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100787 / 51200) = 1/(51200 / 100787) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (677269847 / 1000000000) (84658731 / 125000000) (Real.log (100787 / 51200)) := by
  have h := reflection_log_1_neg
  have he : Real.log (100787 / 51200) = -Real.log (51200 / 100787) := by
    rw [show ((100787 / 51200) : ℝ) = ((51200 / 100787) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (345764373 / 100000000) ≤ -Real.log (1613 / 51200) ∧
    -Real.log (1613 / 51200) ≤ (691528747 / 200000000) := by
  have h := checkLog_sound (w := (1587 / 4813)) (n := 12)
    (lo := (68505501 / 100000000)) (hi := (685055011 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 1613) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3200 / 1613) = 1/(1613 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-691528747 / 200000000) (-345764373 / 100000000) (Real.log (1613 / 51200)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (21158791 / 31250000) ≤ -Real.log (1600 / 3149) ∧
    -Real.log (1600 / 3149) ≤ (677081313 / 1000000000) := by
  have h := checkLog_sound (w := (1549 / 4749)) (n := 12)
    (lo := (21158791 / 31250000)) (hi := (677081313 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3149 / 1600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3149 / 1600) = 1/(1600 / 3149) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (21158791 / 31250000) (677081313 / 1000000000) (Real.log (3149 / 1600)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3149 / 1600) = -Real.log (1600 / 3149) := by
    rw [show ((3149 / 1600) : ℝ) = ((1600 / 3149) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (3445933273 / 1000000000) ≤ -Real.log (51 / 1600) ∧
    -Real.log (51 / 1600) ≤ (1722966639 / 500000000) := by
  have h := checkLog_sound (w := (49 / 151)) (n := 12)
    (lo := (673344553 / 1000000000)) (hi := (336672277 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100 / 51) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(100 / 51) = 1/(51 / 1600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-1722966639 / 500000000) (-3445933273 / 1000000000) (Real.log (51 / 1600)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (661136351 / 1000000000) ≤ -Real.log (25600 / 49587) ∧
    -Real.log (25600 / 49587) ≤ (20660511 / 31250000) := by
  have h := checkLog_sound (w := (23987 / 75187)) (n := 12)
    (lo := (661136351 / 1000000000)) (hi := (20660511 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49587 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49587 / 25600) = 1/(25600 / 49587) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (661136351 / 1000000000) (20660511 / 31250000) (Real.log (49587 / 25600)) := by
  have h := reflection_log_5_neg
  have he : Real.log (49587 / 25600) = -Real.log (25600 / 49587) := by
    rw [show ((49587 / 25600) : ℝ) = ((25600 / 49587) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (55289931 / 20000000) ≤ -Real.log (1613 / 25600) ∧
    -Real.log (1613 / 25600) ≤ (1382248277 / 500000000) := by
  have h := checkLog_sound (w := (1587 / 4813)) (n := 12)
    (lo := (68505501 / 100000000)) (hi := (685055011 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 1613) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(3200 / 1613) = 1/(1613 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1382248277 / 500000000) (-55289931 / 20000000) (Real.log (1613 / 25600)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (82594139 / 125000000) ≤ -Real.log (800 / 1549) ∧
    -Real.log (800 / 1549) ≤ (660753113 / 1000000000) := by
  have h := checkLog_sound (w := (749 / 2349)) (n := 12)
    (lo := (82594139 / 125000000)) (hi := (660753113 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1549 / 800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1549 / 800) = 1/(800 / 1549) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (82594139 / 125000000) (660753113 / 1000000000) (Real.log (1549 / 800)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1549 / 800) = -Real.log (800 / 1549) := by
    rw [show ((1549 / 800) : ℝ) = ((800 / 1549) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (2752786093 / 1000000000) ≤ -Real.log (51 / 800) ∧
    -Real.log (51 / 800) ≤ (2752786097 / 1000000000) := by
  have h := checkLog_sound (w := (49 / 151)) (n := 12)
    (lo := (673344553 / 1000000000)) (hi := (336672277 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100 / 51) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(100 / 51) = 1/(51 / 800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-2752786097 / 1000000000) (-2752786093 / 1000000000) (Real.log (51 / 800)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (135954629 / 200000000) ≤ -Real.log (100000 / 197343) ∧
    -Real.log (100000 / 197343) ≤ (339886573 / 500000000) := by
  have h := checkLog_sound (w := (97343 / 297343)) (n := 12)
    (lo := (135954629 / 200000000)) (hi := (339886573 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((197343 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(197343 / 100000) = 1/(100000 / 197343) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (135954629 / 200000000) (339886573 / 500000000) (Real.log (197343 / 100000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (197343 / 100000) = -Real.log (100000 / 197343) := by
    rw [show ((197343 / 100000) : ℝ) = ((100000 / 197343) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (906993129 / 250000000) ≤ -Real.log (2657 / 100000) ∧
    -Real.log (2657 / 100000) ≤ (1813986261 / 500000000) := by
  have h := checkLog_sound (w := (234 / 2891)) (n := 12)
    (lo := (20279577 / 125000000)) (hi := (162236617 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3125 / 2657) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3125 / 2657) = 1/(2657 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-1813986261 / 500000000) (-906993129 / 250000000) (Real.log (2657 / 100000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (339961563 / 500000000) ≤ -Real.log (500000 / 986863) ∧
    -Real.log (500000 / 986863) ≤ (679923127 / 1000000000) := by
  have h := checkLog_sound (w := (486863 / 1486863)) (n := 12)
    (lo := (339961563 / 500000000)) (hi := (679923127 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((986863 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(986863 / 500000) = 1/(500000 / 986863) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (339961563 / 500000000) (679923127 / 1000000000) (Real.log (986863 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (986863 / 500000) = -Real.log (500000 / 986863) := by
    rw [show ((986863 / 500000) : ℝ) = ((500000 / 986863) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (3639175419 / 1000000000) ≤ -Real.log (13137 / 500000) ∧
    -Real.log (13137 / 500000) ≤ (145567017 / 40000000) := by
  have h := checkLog_sound (w := (1244 / 14381)) (n := 12)
    (lo := (173439519 / 1000000000)) (hi := (1083997 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 13137) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 13137) = 1/(13137 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-145567017 / 40000000) (-3639175419 / 1000000000) (Real.log (13137 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (679685477 / 1000000000) ≤ -Real.log (1000000 / 1973257) ∧
    -Real.log (1000000 / 1973257) ≤ (339842739 / 500000000) := by
  have h := checkLog_sound (w := (973257 / 2973257)) (n := 12)
    (lo := (679685477 / 1000000000)) (hi := (339842739 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1973257 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1973257 / 1000000) = 1/(1000000 / 1973257) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (679685477 / 1000000000) (339842739 / 500000000) (Real.log (1973257 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1973257 / 1000000) = -Real.log (1000000 / 1973257) := by
    rw [show ((1973257 / 1000000) : ℝ) = ((1000000 / 1973257) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (3621482519 / 1000000000) ≤ -Real.log (26743 / 1000000) ∧
    -Real.log (26743 / 1000000) ≤ (144859301 / 40000000) := by
  have h := checkLog_sound (w := (4507 / 57993)) (n := 12)
    (lo := (155746619 / 1000000000)) (hi := (7787331 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 26743) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 26743) = 1/(26743 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-144859301 / 40000000) (-3621482519 / 1000000000) (Real.log (26743 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (679836991 / 1000000000) ≤ -Real.log (250000 / 493389) ∧
    -Real.log (250000 / 493389) ≤ (10622453 / 15625000) := by
  have h := checkLog_sound (w := (243389 / 743389)) (n := 12)
    (lo := (679836991 / 1000000000)) (hi := (10622453 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((493389 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(493389 / 250000) = 1/(250000 / 493389) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (679836991 / 1000000000) (10622453 / 15625000) (Real.log (493389 / 250000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (493389 / 250000) = -Real.log (250000 / 493389) := by
    rw [show ((493389 / 250000) : ℝ) = ((250000 / 493389) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (1816362993 / 500000000) ≤ -Real.log (6611 / 250000) ∧
    -Real.log (6611 / 250000) ≤ (454090749 / 125000000) := by
  have h := checkLog_sound (w := (2403 / 28847)) (n := 12)
    (lo := (83495043 / 500000000)) (hi := (166990087 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 13222) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 13222) = 1/(6611 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-454090749 / 125000000) (-1816362993 / 500000000) (Real.log (6611 / 250000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (4307745661 / 1000000000) ≤ -Real.log (1562500000 / 116051350207) ∧
    -Real.log (1562500000 / 116051350207) ≤ (1076936417 / 250000000) := by
  have h := checkLog_sound (w := (16051350207 / 216051350207)) (n := 12)
    (lo := (148862581 / 1000000000)) (hi := (74431291 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((116051350207 / 100000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(116051350207 / 100000000000) = 1/(1562500000 / 116051350207) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (4307745661 / 1000000000) (1076936417 / 250000000) (Real.log (116051350207 / 1562500000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (116051350207 / 1562500000) = -Real.log (1562500000 / 116051350207) := by
    rw [show ((116051350207 / 1562500000) : ℝ) = ((1562500000 / 116051350207) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (863819709 / 200000000) ≤ -Real.log (500000000000 / 37560439978687) ∧
    -Real.log (500000000000 / 37560439978687) ≤ (539887319 / 125000000) := by
  have h := checkLog_sound (w := (5560439978687 / 69560439978687)) (n := 12)
    (lo := (32043093 / 200000000)) (hi := (80107733 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((37560439978687 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(37560439978687 / 32000000000000) = 1/(500000000000 / 37560439978687) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (863819709 / 200000000) (539887319 / 125000000) (Real.log (37560439978687 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (37560439978687 / 500000000000) = -Real.log (500000000000 / 37560439978687) := by
    rw [show ((37560439978687 / 500000000000) : ℝ) = ((500000000000 / 37560439978687) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (860233599 / 200000000) ≤ -Real.log (50000000000 / 3689296264443) ∧
    -Real.log (50000000000 / 3689296264443) ≤ (2150584001 / 500000000) := by
  have h := checkLog_sound (w := (489296264443 / 6889296264443)) (n := 12)
    (lo := (28456983 / 200000000)) (hi := (35571229 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3689296264443 / 3200000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(3689296264443 / 3200000000000) = 1/(50000000000 / 3689296264443) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (860233599 / 200000000) (2150584001 / 500000000) (Real.log (3689296264443 / 50000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (3689296264443 / 50000000000) = -Real.log (50000000000 / 3689296264443) := by
    rw [show ((3689296264443 / 50000000000) : ℝ) = ((50000000000 / 3689296264443) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (4312562977 / 1000000000) ≤ -Real.log (500000000000 / 37315761609439) ∧
    -Real.log (500000000000 / 37315761609439) ≤ (539070373 / 125000000) := by
  have h := checkLog_sound (w := (5315761609439 / 69315761609439)) (n := 12)
    (lo := (153679897 / 1000000000)) (hi := (76839949 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((37315761609439 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(37315761609439 / 32000000000000) = 1/(500000000000 / 37315761609439) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (4312562977 / 1000000000) (539070373 / 125000000) (Real.log (37315761609439 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (37315761609439 / 500000000000) = -Real.log (500000000000 / 37315761609439) := by
    rw [show ((37315761609439 / 500000000000) : ℝ) = ((500000000000 / 37315761609439) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0069
