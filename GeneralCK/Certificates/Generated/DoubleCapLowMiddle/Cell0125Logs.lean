import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0125
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

theorem reflection_log_1_neg : (166044219 / 250000000) ≤ -Real.log (12800 / 24869) ∧
    -Real.log (12800 / 24869) ≤ (664176877 / 1000000000) := by
  have h := checkLog_sound (w := (12069 / 37669)) (n := 12)
    (lo := (166044219 / 250000000)) (hi := (664176877 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24869 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24869 / 12800) = 1/(12800 / 24869) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (166044219 / 250000000) (664176877 / 1000000000) (Real.log (24869 / 12800)) := by
  have h := reflection_log_1_neg
  have he : Real.log (24869 / 12800) = -Real.log (12800 / 24869) := by
    rw [show ((24869 / 12800) : ℝ) = ((12800 / 24869) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (2862786987 / 1000000000) ≤ -Real.log (731 / 12800) ∧
    -Real.log (731 / 12800) ≤ (178924187 / 62500000) := by
  have h := checkLog_sound (w := (69 / 1531)) (n := 12)
    (lo := (90198267 / 1000000000)) (hi := (22549567 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 731) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(800 / 731) = 1/(731 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-178924187 / 62500000) (-2862786987 / 1000000000) (Real.log (731 / 12800)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (331897401 / 500000000) ≤ -Real.log (25600 / 49719) ∧
    -Real.log (25600 / 49719) ≤ (663794803 / 1000000000) := by
  have h := checkLog_sound (w := (24119 / 75319)) (n := 12)
    (lo := (331897401 / 500000000)) (hi := (663794803 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49719 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49719 / 25600) = 1/(25600 / 49719) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (331897401 / 500000000) (663794803 / 1000000000) (Real.log (49719 / 25600)) := by
  have h := reflection_log_3_neg
  have he : Real.log (49719 / 25600) = -Real.log (25600 / 49719) := by
    rw [show ((49719 / 25600) : ℝ) = ((25600 / 49719) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (2849874813 / 1000000000) ≤ -Real.log (1481 / 25600) ∧
    -Real.log (1481 / 25600) ≤ (1424937409 / 500000000) := by
  have h := checkLog_sound (w := (119 / 3081)) (n := 12)
    (lo := (77286093 / 1000000000)) (hi := (38643047 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1481) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1600 / 1481) = 1/(1481 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-1424937409 / 500000000) (-2849874813 / 1000000000) (Real.log (1481 / 25600)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (634342191 / 1000000000) ≤ -Real.log (6400 / 12069) ∧
    -Real.log (6400 / 12069) ≤ (39646387 / 62500000) := by
  have h := checkLog_sound (w := (5669 / 18469)) (n := 12)
    (lo := (634342191 / 1000000000)) (hi := (39646387 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12069 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12069 / 6400) = 1/(6400 / 12069) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (634342191 / 1000000000) (39646387 / 62500000) (Real.log (12069 / 6400)) := by
  have h := reflection_log_5_neg
  have he : Real.log (12069 / 6400) = -Real.log (6400 / 12069) := by
    rw [show ((12069 / 6400) : ℝ) = ((6400 / 12069) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (2169639807 / 1000000000) ≤ -Real.log (731 / 6400) ∧
    -Real.log (731 / 6400) ≤ (2169639811 / 1000000000) := by
  have h := checkLog_sound (w := (69 / 1531)) (n := 12)
    (lo := (90198267 / 1000000000)) (hi := (22549567 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 731) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(800 / 731) = 1/(731 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-2169639811 / 1000000000) (-2169639807 / 1000000000) (Real.log (731 / 6400)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (31677737 / 50000000) ≤ -Real.log (12800 / 24119) ∧
    -Real.log (12800 / 24119) ≤ (633554741 / 1000000000) := by
  have h := checkLog_sound (w := (11319 / 36919)) (n := 12)
    (lo := (31677737 / 50000000)) (hi := (633554741 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24119 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24119 / 12800) = 1/(12800 / 24119) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (31677737 / 50000000) (633554741 / 1000000000) (Real.log (24119 / 12800)) := by
  have h := reflection_log_7_neg
  have he : Real.log (24119 / 12800) = -Real.log (12800 / 24119) := by
    rw [show ((24119 / 12800) : ℝ) = ((12800 / 24119) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (2156727633 / 1000000000) ≤ -Real.log (1481 / 12800) ∧
    -Real.log (1481 / 12800) ≤ (2156727637 / 1000000000) := by
  have h := checkLog_sound (w := (119 / 3081)) (n := 12)
    (lo := (77286093 / 1000000000)) (hi := (38643047 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1481) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1600 / 1481) = 1/(1481 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-2156727637 / 1000000000) (-2156727633 / 1000000000) (Real.log (1481 / 12800)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (669601647 / 1000000000) ≤ -Real.log (1000000 / 1953459) ∧
    -Real.log (1000000 / 1953459) ≤ (41850103 / 62500000) := by
  have h := checkLog_sound (w := (953459 / 2953459)) (n := 12)
    (lo := (669601647 / 1000000000)) (hi := (41850103 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1953459 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1953459 / 1000000) = 1/(1000000 / 1953459) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (669601647 / 1000000000) (41850103 / 62500000) (Real.log (1953459 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1953459 / 1000000) = -Real.log (1000000 / 1953459) := by
    rw [show ((1953459 / 1000000) : ℝ) = ((1000000 / 1953459) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (47928463 / 15625000) ≤ -Real.log (46541 / 1000000) ∧
    -Real.log (46541 / 1000000) ≤ (3067421637 / 1000000000) := by
  have h := checkLog_sound (w := (15959 / 109041)) (n := 12)
    (lo := (18427057 / 62500000)) (hi := (294832913 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 46541) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 46541) = 1/(46541 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-3067421637 / 1000000000) (-47928463 / 15625000) (Real.log (46541 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (334942859 / 500000000) ≤ -Real.log (500000 / 977007) ∧
    -Real.log (500000 / 977007) ≤ (669885719 / 1000000000) := by
  have h := checkLog_sound (w := (477007 / 1477007)) (n := 12)
    (lo := (334942859 / 500000000)) (hi := (669885719 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((977007 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(977007 / 500000) = 1/(500000 / 977007) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (334942859 / 500000000) (669885719 / 1000000000) (Real.log (977007 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (977007 / 500000) = -Real.log (500000 / 977007) := by
    rw [show ((977007 / 500000) : ℝ) = ((500000 / 977007) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1539709137 / 500000000) ≤ -Real.log (22993 / 500000) ∧
    -Real.log (22993 / 500000) ≤ (3079418279 / 1000000000) := by
  have h := checkLog_sound (w := (8257 / 54243)) (n := 12)
    (lo := (153414777 / 500000000)) (hi := (61365911 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 22993) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(31250 / 22993) = 1/(22993 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-3079418279 / 1000000000) (-1539709137 / 500000000) (Real.log (22993 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (669259119 / 1000000000) ≤ -Real.log (100000 / 195279) ∧
    -Real.log (100000 / 195279) ≤ (8365739 / 12500000) := by
  have h := checkLog_sound (w := (95279 / 295279)) (n := 12)
    (lo := (669259119 / 1000000000)) (hi := (8365739 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((195279 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(195279 / 100000) = 1/(100000 / 195279) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (669259119 / 1000000000) (8365739 / 12500000) (Real.log (195279 / 100000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (195279 / 100000) = -Real.log (100000 / 195279) := by
    rw [show ((195279 / 100000) : ℝ) = ((100000 / 195279) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (1526574771 / 500000000) ≤ -Real.log (4721 / 100000) ∧
    -Real.log (4721 / 100000) ≤ (3053149547 / 1000000000) := by
  have h := checkLog_sound (w := (1529 / 10971)) (n := 12)
    (lo := (140280411 / 500000000)) (hi := (280560823 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6250 / 4721) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(6250 / 4721) = 1/(4721 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-3053149547 / 1000000000) (-1526574771 / 500000000) (Real.log (4721 / 100000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (334776763 / 500000000) ≤ -Real.log (200000 / 390673) ∧
    -Real.log (200000 / 390673) ≤ (669553527 / 1000000000) := by
  have h := checkLog_sound (w := (190673 / 590673)) (n := 12)
    (lo := (334776763 / 500000000)) (hi := (669553527 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((390673 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(390673 / 200000) = 1/(200000 / 390673) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (334776763 / 500000000) (669553527 / 1000000000) (Real.log (390673 / 200000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (390673 / 200000) = -Real.log (200000 / 390673) := by
    rw [show ((390673 / 200000) : ℝ) = ((200000 / 390673) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (383175493 / 125000000) ≤ -Real.log (9327 / 200000) ∧
    -Real.log (9327 / 200000) ≤ (3065403949 / 1000000000) := by
  have h := checkLog_sound (w := (3173 / 21827)) (n := 12)
    (lo := (36601903 / 125000000)) (hi := (11712609 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12500 / 9327) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(12500 / 9327) = 1/(9327 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-3065403949 / 1000000000) (-383175493 / 125000000) (Real.log (9327 / 200000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1868511639 / 500000000) ≤ -Real.log (250000000000 / 10493215659311) ∧
    -Real.log (250000000000 / 10493215659311) ≤ (934255821 / 250000000) := by
  have h := checkLog_sound (w := (2493215659311 / 18493215659311)) (n := 12)
    (lo := (135643689 / 500000000)) (hi := (271287379 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10493215659311 / 8000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(10493215659311 / 8000000000000) = 1/(250000000000 / 10493215659311) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1868511639 / 500000000) (934255821 / 250000000) (Real.log (10493215659311 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (10493215659311 / 250000000000) = -Real.log (250000000000 / 10493215659311) := by
    rw [show ((10493215659311 / 250000000000) : ℝ) = ((250000000000 / 10493215659311) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (468662999 / 125000000) ≤ -Real.log (31250000000 / 1327859294133) ∧
    -Real.log (31250000000 / 1327859294133) ≤ (1874651999 / 500000000) := by
  have h := checkLog_sound (w := (327859294133 / 2327859294133)) (n := 12)
    (lo := (70892023 / 250000000)) (hi := (283568093 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1327859294133 / 1000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(1327859294133 / 1000000000000) = 1/(31250000000 / 1327859294133) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (468662999 / 125000000) (1874651999 / 500000000) (Real.log (1327859294133 / 31250000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1327859294133 / 31250000000) = -Real.log (31250000000 / 1327859294133) := by
    rw [show ((1327859294133 / 31250000000) : ℝ) = ((31250000000 / 1327859294133) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (186120433 / 50000000) ≤ -Real.log (7812500000 / 323155515251) ∧
    -Real.log (7812500000 / 323155515251) ≤ (1861204333 / 500000000) := by
  have h := checkLog_sound (w := (73155515251 / 573155515251)) (n := 12)
    (lo := (6416819 / 25000000)) (hi := (256672761 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((323155515251 / 250000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(323155515251 / 250000000000) = 1/(7812500000 / 323155515251) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (186120433 / 50000000) (1861204333 / 500000000) (Real.log (323155515251 / 7812500000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (323155515251 / 7812500000) = -Real.log (7812500000 / 323155515251) := by
    rw [show ((323155515251 / 7812500000) : ℝ) = ((7812500000 / 323155515251) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (373495747 / 100000000) ≤ -Real.log (500000000000 / 20943122118581) ∧
    -Real.log (500000000000 / 20943122118581) ≤ (933739369 / 250000000) := by
  have h := checkLog_sound (w := (4943122118581 / 36943122118581)) (n := 12)
    (lo := (26922157 / 100000000)) (hi := (269221571 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20943122118581 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(20943122118581 / 16000000000000) = 1/(500000000000 / 20943122118581) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (373495747 / 100000000) (933739369 / 250000000) (Real.log (20943122118581 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (20943122118581 / 500000000000) = -Real.log (500000000000 / 20943122118581) := by
    rw [show ((20943122118581 / 500000000000) : ℝ) = ((500000000000 / 20943122118581) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0125
