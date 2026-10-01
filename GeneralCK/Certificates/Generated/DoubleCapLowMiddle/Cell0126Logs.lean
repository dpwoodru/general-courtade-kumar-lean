import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0126
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

theorem reflection_log_1_neg : (331897401 / 500000000) ≤ -Real.log (25600 / 49719) ∧
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


theorem reflection_log_1 : Bounds (331897401 / 500000000) (663794803 / 1000000000) (Real.log (49719 / 25600)) := by
  have h := reflection_log_1_neg
  have he : Real.log (49719 / 25600) = -Real.log (25600 / 49719) := by
    rw [show ((49719 / 25600) : ℝ) = ((25600 / 49719) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (2849874813 / 1000000000) ≤ -Real.log (1481 / 25600) ∧
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


theorem reflection_log_2 : Bounds (-1424937409 / 500000000) (-2849874813 / 1000000000) (Real.log (1481 / 25600)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (663412581 / 1000000000) ≤ -Real.log (256 / 497) ∧
    -Real.log (256 / 497) ≤ (331706291 / 500000000) := by
  have h := checkLog_sound (w := (241 / 753)) (n := 12)
    (lo := (663412581 / 1000000000)) (hi := (331706291 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((497 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(497 / 256) = 1/(256 / 497) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (663412581 / 1000000000) (331706291 / 500000000) (Real.log (497 / 256)) := by
  have h := reflection_log_3_neg
  have he : Real.log (497 / 256) = -Real.log (256 / 497) := by
    rw [show ((497 / 256) : ℝ) = ((256 / 497) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (2837127241 / 1000000000) ≤ -Real.log (15 / 256) ∧
    -Real.log (15 / 256) ≤ (1418563623 / 500000000) := by
  have h := checkLog_sound (w := (1 / 31)) (n := 12)
    (lo := (64538521 / 1000000000)) (hi := (32269261 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((16 / 15) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(16 / 15) = 1/(15 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-1418563623 / 500000000) (-2837127241 / 1000000000) (Real.log (15 / 256)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (31677737 / 50000000) ≤ -Real.log (12800 / 24119) ∧
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


theorem reflection_log_5 : Bounds (31677737 / 50000000) (633554741 / 1000000000) (Real.log (24119 / 12800)) := by
  have h := reflection_log_5_neg
  have he : Real.log (24119 / 12800) = -Real.log (12800 / 24119) := by
    rw [show ((24119 / 12800) : ℝ) = ((12800 / 24119) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (2156727633 / 1000000000) ≤ -Real.log (1481 / 12800) ∧
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


theorem reflection_log_6 : Bounds (-2156727637 / 1000000000) (-2156727633 / 1000000000) (Real.log (1481 / 12800)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (632766669 / 1000000000) ≤ -Real.log (128 / 241) ∧
    -Real.log (128 / 241) ≤ (63276667 / 100000000) := by
  have h := checkLog_sound (w := (113 / 369)) (n := 12)
    (lo := (632766669 / 1000000000)) (hi := (63276667 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((241 / 128) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(241 / 128) = 1/(128 / 241) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (632766669 / 1000000000) (63276667 / 100000000) (Real.log (241 / 128)) := by
  have h := reflection_log_7_neg
  have he : Real.log (241 / 128) = -Real.log (128 / 241) := by
    rw [show ((241 / 128) : ℝ) = ((128 / 241) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (2143980061 / 1000000000) ≤ -Real.log (15 / 128) ∧
    -Real.log (15 / 128) ≤ (428796013 / 200000000) := by
  have h := checkLog_sound (w := (1 / 31)) (n := 12)
    (lo := (64538521 / 1000000000)) (hi := (32269261 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((16 / 15) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(16 / 15) = 1/(15 / 128) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-428796013 / 200000000) (-2143980061 / 1000000000) (Real.log (15 / 128)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (669318007 / 1000000000) ≤ -Real.log (200000 / 390581) ∧
    -Real.log (200000 / 390581) ≤ (83664751 / 125000000) := by
  have h := checkLog_sound (w := (190581 / 590581)) (n := 12)
    (lo := (669318007 / 1000000000)) (hi := (83664751 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((390581 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(390581 / 200000) = 1/(200000 / 390581) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (669318007 / 1000000000) (83664751 / 125000000) (Real.log (390581 / 200000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (390581 / 200000) = -Real.log (200000 / 390581) := by
    rw [show ((390581 / 200000) : ℝ) = ((200000 / 390581) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (1527794219 / 500000000) ≤ -Real.log (9419 / 200000) ∧
    -Real.log (9419 / 200000) ≤ (3055588443 / 1000000000) := by
  have h := checkLog_sound (w := (3081 / 21919)) (n := 12)
    (lo := (141499859 / 500000000)) (hi := (282999719 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12500 / 9419) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(12500 / 9419) = 1/(9419 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-3055588443 / 1000000000) (-1527794219 / 500000000) (Real.log (9419 / 200000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (669602159 / 1000000000) ≤ -Real.log (50000 / 97673) ∧
    -Real.log (50000 / 97673) ≤ (8370027 / 12500000) := by
  have h := checkLog_sound (w := (47673 / 147673)) (n := 12)
    (lo := (669602159 / 1000000000)) (hi := (8370027 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((97673 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(97673 / 50000) = 1/(50000 / 97673) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (669602159 / 1000000000) (8370027 / 12500000) (Real.log (97673 / 50000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (97673 / 50000) = -Real.log (50000 / 97673) := by
    rw [show ((97673 / 50000) : ℝ) = ((50000 / 97673) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1533721559 / 500000000) ≤ -Real.log (2327 / 50000) ∧
    -Real.log (2327 / 50000) ≤ (3067443123 / 1000000000) := by
  have h := checkLog_sound (w := (399 / 2726)) (n := 12)
    (lo := (147427199 / 500000000)) (hi := (294854399 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3125 / 2327) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3125 / 2327) = 1/(2327 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-3067443123 / 1000000000) (-1533721559 / 500000000) (Real.log (2327 / 50000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (668965137 / 1000000000) ≤ -Real.log (125000 / 244027) ∧
    -Real.log (125000 / 244027) ≤ (334482569 / 500000000) := by
  have h := checkLog_sound (w := (119027 / 369027)) (n := 12)
    (lo := (668965137 / 1000000000)) (hi := (334482569 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((244027 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(244027 / 125000) = 1/(125000 / 244027) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (668965137 / 1000000000) (334482569 / 500000000) (Real.log (244027 / 125000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (244027 / 125000) = -Real.log (125000 / 244027) := by
    rw [show ((244027 / 125000) : ℝ) = ((125000 / 244027) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (3041064421 / 1000000000) ≤ -Real.log (5973 / 125000) ∧
    -Real.log (5973 / 125000) ≤ (1520532213 / 500000000) := by
  have h := checkLog_sound (w := (3679 / 27571)) (n := 12)
    (lo := (268475701 / 1000000000)) (hi := (134237851 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 11946) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(15625 / 11946) = 1/(5973 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-1520532213 / 500000000) (-3041064421 / 1000000000) (Real.log (5973 / 125000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (669259631 / 1000000000) ≤ -Real.log (1000000 / 1952791) ∧
    -Real.log (1000000 / 1952791) ≤ (41828727 / 62500000) := by
  have h := checkLog_sound (w := (952791 / 2952791)) (n := 12)
    (lo := (669259631 / 1000000000)) (hi := (41828727 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1952791 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1952791 / 1000000) = 1/(1000000 / 1952791) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (669259631 / 1000000000) (41828727 / 62500000) (Real.log (1952791 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1952791 / 1000000) = -Real.log (1000000 / 1952791) := by
    rw [show ((1952791 / 1000000) : ℝ) = ((1000000 / 1952791) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (763292681 / 250000000) ≤ -Real.log (47209 / 1000000) ∧
    -Real.log (47209 / 1000000) ≤ (3053170729 / 1000000000) := by
  have h := checkLog_sound (w := (15291 / 109709)) (n := 12)
    (lo := (70145501 / 250000000)) (hi := (56116401 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 47209) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 47209) = 1/(47209 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-3053170729 / 1000000000) (-763292681 / 250000000) (Real.log (47209 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (744981289 / 200000000) ≤ -Real.log (100000000000 / 4146735322221) ∧
    -Real.log (100000000000 / 4146735322221) ≤ (3724906451 / 1000000000) := by
  have h := checkLog_sound (w := (946735322221 / 7346735322221)) (n := 12)
    (lo := (51834109 / 200000000)) (hi := (129585273 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4146735322221 / 3200000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(4146735322221 / 3200000000000) = 1/(100000000000 / 4146735322221) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (744981289 / 200000000) (3724906451 / 1000000000) (Real.log (4146735322221 / 100000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (4146735322221 / 100000000000) = -Real.log (100000000000 / 4146735322221) := by
    rw [show ((4146735322221 / 100000000000) : ℝ) = ((100000000000 / 4146735322221) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (3737045277 / 1000000000) ≤ -Real.log (500000000000 / 20986892995273) ∧
    -Real.log (500000000000 / 20986892995273) ≤ (3737045283 / 1000000000) := by
  have h := checkLog_sound (w := (4986892995273 / 36986892995273)) (n := 12)
    (lo := (271309377 / 1000000000)) (hi := (135654689 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20986892995273 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(20986892995273 / 16000000000000) = 1/(500000000000 / 20986892995273) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (3737045277 / 1000000000) (3737045283 / 1000000000) (Real.log (20986892995273 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (20986892995273 / 500000000000) = -Real.log (500000000000 / 20986892995273) := by
    rw [show ((20986892995273 / 500000000000) : ℝ) = ((500000000000 / 20986892995273) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1855014779 / 500000000) ≤ -Real.log (62500000000 / 2553438389419) ∧
    -Real.log (62500000000 / 2553438389419) ≤ (927507391 / 250000000) := by
  have h := checkLog_sound (w := (553438389419 / 4553438389419)) (n := 12)
    (lo := (122146829 / 500000000)) (hi := (244293659 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2553438389419 / 2000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(2553438389419 / 2000000000000) = 1/(62500000000 / 2553438389419) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (1855014779 / 500000000) (927507391 / 250000000) (Real.log (2553438389419 / 62500000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (2553438389419 / 62500000000) = -Real.log (62500000000 / 2553438389419) := by
    rw [show ((2553438389419 / 62500000000) : ℝ) = ((62500000000 / 2553438389419) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (744486071 / 200000000) ≤ -Real.log (500000000000 / 20682401660701) ∧
    -Real.log (500000000000 / 20682401660701) ≤ (3722430361 / 1000000000) := by
  have h := checkLog_sound (w := (4682401660701 / 36682401660701)) (n := 12)
    (lo := (51338891 / 200000000)) (hi := (32086807 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20682401660701 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(20682401660701 / 16000000000000) = 1/(500000000000 / 20682401660701) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (744486071 / 200000000) (3722430361 / 1000000000) (Real.log (20682401660701 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (20682401660701 / 500000000000) = -Real.log (500000000000 / 20682401660701) := by
    rw [show ((20682401660701 / 500000000000) : ℝ) = ((500000000000 / 20682401660701) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0126
