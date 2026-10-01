import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0093
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

theorem reflection_log_1_neg : (339258529 / 1000000000) ≤ -Real.log (1280 / 1797) ∧
    -Real.log (1280 / 1797) ≤ (33925853 / 100000000) := by
  have h := checkLog_sound (w := (517 / 3077)) (n := 12)
    (lo := (339258529 / 1000000000)) (hi := (33925853 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1797 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1797 / 1280) = 1/(1280 / 1797) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (339258529 / 1000000000) (33925853 / 100000000) (Real.log (1797 / 1280)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1797 / 1280) = -Real.log (1280 / 1797) := by
    rw [show ((1797 / 1280) : ℝ) = ((1280 / 1797) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (20694293 / 40000000) ≤ -Real.log (763 / 1280) ∧
    -Real.log (763 / 1280) ≤ (258678663 / 500000000) := by
  have h := checkLog_sound (w := (517 / 2043)) (n := 12)
    (lo := (20694293 / 40000000)) (hi := (258678663 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 763) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 763) = 1/(763 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-258678663 / 500000000) (-20694293 / 40000000) (Real.log (763 / 1280)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (10575733 / 31250000) ≤ -Real.log (2560 / 3591) ∧
    -Real.log (2560 / 3591) ≤ (338423457 / 1000000000) := by
  have h := checkLog_sound (w := (1031 / 6151)) (n := 12)
    (lo := (10575733 / 31250000)) (hi := (338423457 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3591 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3591 / 2560) = 1/(2560 / 3591) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (10575733 / 31250000) (338423457 / 1000000000) (Real.log (3591 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3591 / 2560) = -Real.log (2560 / 3591) := by
    rw [show ((3591 / 2560) : ℝ) = ((2560 / 3591) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (515393331 / 1000000000) ≤ -Real.log (1529 / 2560) ∧
    -Real.log (1529 / 2560) ≤ (128848333 / 250000000) := by
  have h := checkLog_sound (w := (1031 / 4089)) (n := 12)
    (lo := (515393331 / 1000000000)) (hi := (128848333 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1529) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1529) = 1/(1529 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-128848333 / 250000000) (-515393331 / 1000000000) (Real.log (1529 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (11842351 / 20000000) ≤ -Real.log (640 / 1157) ∧
    -Real.log (640 / 1157) ≤ (592117551 / 1000000000) := by
  have h := checkLog_sound (w := (517 / 1797)) (n := 12)
    (lo := (11842351 / 20000000)) (hi := (592117551 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1157 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1157 / 640) = 1/(640 / 1157) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (11842351 / 20000000) (592117551 / 1000000000) (Real.log (1157 / 640)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1157 / 640) = -Real.log (640 / 1157) := by
    rw [show ((1157 / 640) : ℝ) = ((640 / 1157) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1649283819 / 1000000000) ≤ -Real.log (123 / 640) ∧
    -Real.log (123 / 640) ≤ (824641911 / 500000000) := by
  have h := checkLog_sound (w := (37 / 283)) (n := 12)
    (lo := (262989459 / 1000000000)) (hi := (13149473 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 123) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(160 / 123) = 1/(123 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-824641911 / 500000000) (-1649283819 / 1000000000) (Real.log (123 / 640)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (590820253 / 1000000000) ≤ -Real.log (1280 / 2311) ∧
    -Real.log (1280 / 2311) ≤ (295410127 / 500000000) := by
  have h := checkLog_sound (w := (1031 / 3591)) (n := 12)
    (lo := (590820253 / 1000000000)) (hi := (295410127 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2311 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2311 / 1280) = 1/(1280 / 2311) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (590820253 / 1000000000) (295410127 / 500000000) (Real.log (2311 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2311 / 1280) = -Real.log (1280 / 2311) := by
    rw [show ((2311 / 1280) : ℝ) = ((1280 / 2311) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (1637162459 / 1000000000) ≤ -Real.log (249 / 1280) ∧
    -Real.log (249 / 1280) ≤ (818581231 / 500000000) := by
  have h := checkLog_sound (w := (71 / 569)) (n := 12)
    (lo := (250868099 / 1000000000)) (hi := (2508681 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 249) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(320 / 249) = 1/(249 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-818581231 / 500000000) (-1637162459 / 1000000000) (Real.log (249 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (464813307 / 1000000000) ≤ -Real.log (1000000 / 1591717) ∧
    -Real.log (1000000 / 1591717) ≤ (116203327 / 250000000) := by
  have h := checkLog_sound (w := (591717 / 2591717)) (n := 12)
    (lo := (464813307 / 1000000000)) (hi := (116203327 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1591717 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1591717 / 1000000) = 1/(1000000 / 1591717) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (464813307 / 1000000000) (116203327 / 250000000) (Real.log (1591717 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1591717 / 1000000) = -Real.log (1000000 / 1591717) := by
    rw [show ((1591717 / 1000000) : ℝ) = ((1000000 / 1591717) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (895794717 / 1000000000) ≤ -Real.log (408283 / 1000000) ∧
    -Real.log (408283 / 1000000) ≤ (895794719 / 1000000000) := by
  have h := checkLog_sound (w := (91717 / 908283)) (n := 12)
    (lo := (202647537 / 1000000000)) (hi := (101323769 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 408283) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 408283) = 1/(408283 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-895794719 / 1000000000) (-895794717 / 1000000000) (Real.log (408283 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (116504863 / 250000000) ≤ -Real.log (500000 / 796819) ∧
    -Real.log (500000 / 796819) ≤ (466019453 / 1000000000) := by
  have h := checkLog_sound (w := (296819 / 1296819)) (n := 12)
    (lo := (116504863 / 250000000)) (hi := (466019453 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((796819 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(796819 / 500000) = 1/(500000 / 796819) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (116504863 / 250000000) (466019453 / 1000000000) (Real.log (796819 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (796819 / 500000) = -Real.log (500000 / 796819) := by
    rw [show ((796819 / 500000) : ℝ) = ((500000 / 796819) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (90051089 / 100000000) ≤ -Real.log (203181 / 500000) ∧
    -Real.log (203181 / 500000) ≤ (225127723 / 250000000) := by
  have h := checkLog_sound (w := (46819 / 453181)) (n := 12)
    (lo := (20736371 / 100000000)) (hi := (207363711 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 203181) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 203181) = 1/(203181 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-225127723 / 250000000) (-90051089 / 100000000) (Real.log (203181 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (190232599 / 500000000) ≤ -Real.log (200000 / 292593) ∧
    -Real.log (200000 / 292593) ≤ (380465199 / 1000000000) := by
  have h := checkLog_sound (w := (92593 / 492593)) (n := 12)
    (lo := (190232599 / 500000000)) (hi := (380465199 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((292593 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(292593 / 200000) = 1/(200000 / 292593) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (190232599 / 500000000) (380465199 / 1000000000) (Real.log (292593 / 200000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (292593 / 200000) = -Real.log (200000 / 292593) := by
    rw [show ((292593 / 200000) : ℝ) = ((200000 / 292593) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (621692009 / 1000000000) ≤ -Real.log (107407 / 200000) ∧
    -Real.log (107407 / 200000) ≤ (62169201 / 100000000) := by
  have h := checkLog_sound (w := (92593 / 307407)) (n := 12)
    (lo := (621692009 / 1000000000)) (hi := (62169201 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 107407) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 107407) = 1/(107407 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-62169201 / 100000000) (-621692009 / 1000000000) (Real.log (107407 / 200000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (95427289 / 250000000) ≤ -Real.log (500000 / 732393) ∧
    -Real.log (500000 / 732393) ≤ (381709157 / 1000000000) := by
  have h := checkLog_sound (w := (232393 / 1232393)) (n := 12)
    (lo := (95427289 / 250000000)) (hi := (381709157 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((732393 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(732393 / 500000) = 1/(500000 / 732393) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (95427289 / 250000000) (381709157 / 1000000000) (Real.log (732393 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (732393 / 500000) = -Real.log (500000 / 732393) := by
    rw [show ((732393 / 500000) : ℝ) = ((500000 / 732393) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (156272153 / 250000000) ≤ -Real.log (267607 / 500000) ∧
    -Real.log (267607 / 500000) ≤ (625088613 / 1000000000) := by
  have h := checkLog_sound (w := (232393 / 767607)) (n := 12)
    (lo := (156272153 / 250000000)) (hi := (625088613 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 267607) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 267607) = 1/(267607 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-625088613 / 1000000000) (-156272153 / 250000000) (Real.log (267607 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (170076003 / 125000000) ≤ -Real.log (500000000000 / 1949281503271) ∧
    -Real.log (500000000000 / 1949281503271) ≤ (680304013 / 500000000) := by
  have h := checkLog_sound (w := (949281503271 / 2949281503271)) (n := 12)
    (lo := (166865211 / 250000000)) (hi := (133492169 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1949281503271 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1949281503271 / 1000000000000) = 1/(500000000000 / 1949281503271) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (170076003 / 125000000) (680304013 / 500000000) (Real.log (1949281503271 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1949281503271 / 500000000000) = -Real.log (500000000000 / 1949281503271) := by
    rw [show ((1949281503271 / 500000000000) : ℝ) = ((500000000000 / 1949281503271) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1366530343 / 1000000000) ≤ -Real.log (500000000000 / 1960860021361) ∧
    -Real.log (500000000000 / 1960860021361) ≤ (273306069 / 200000000) := by
  have h := checkLog_sound (w := (960860021361 / 2960860021361)) (n := 12)
    (lo := (673383163 / 1000000000)) (hi := (168345791 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1960860021361 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1960860021361 / 1000000000000) = 1/(500000000000 / 1960860021361) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1366530343 / 1000000000) (273306069 / 200000000) (Real.log (1960860021361 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1960860021361 / 500000000000) = -Real.log (500000000000 / 1960860021361) := by
    rw [show ((1960860021361 / 500000000000) : ℝ) = ((500000000000 / 1960860021361) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1002157207 / 1000000000) ≤ -Real.log (125000000000 / 340519007141) ∧
    -Real.log (125000000000 / 340519007141) ≤ (1002157209 / 1000000000) := by
  have h := checkLog_sound (w := (90519007141 / 590519007141)) (n := 12)
    (lo := (309010027 / 1000000000)) (hi := (77252507 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((340519007141 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(340519007141 / 250000000000) = 1/(125000000000 / 340519007141) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (1002157207 / 1000000000) (1002157209 / 1000000000) (Real.log (340519007141 / 125000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (340519007141 / 125000000000) = -Real.log (125000000000 / 340519007141) := by
    rw [show ((340519007141 / 125000000000) : ℝ) = ((125000000000 / 340519007141) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (125849721 / 125000000) ≤ -Real.log (5000000000 / 13684115139) ∧
    -Real.log (5000000000 / 13684115139) ≤ (100679777 / 100000000) := by
  have h := checkLog_sound (w := (3684115139 / 23684115139)) (n := 12)
    (lo := (78412647 / 250000000)) (hi := (313650589 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((13684115139 / 10000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(13684115139 / 10000000000) = 1/(5000000000 / 13684115139) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (125849721 / 125000000) (100679777 / 100000000) (Real.log (13684115139 / 5000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (13684115139 / 5000000000) = -Real.log (5000000000 / 13684115139) := by
    rw [show ((13684115139 / 5000000000) : ℝ) = ((5000000000 / 13684115139) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0093
