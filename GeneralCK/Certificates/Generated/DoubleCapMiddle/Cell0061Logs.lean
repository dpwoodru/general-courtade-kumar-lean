import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0061
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

theorem reflection_log_1_neg : (365619199 / 1000000000) ≤ -Real.log (256 / 369) ∧
    -Real.log (256 / 369) ≤ (28564 / 78125) := by
  have h := checkLog_sound (w := (113 / 625)) (n := 12)
    (lo := (365619199 / 1000000000)) (hi := (28564 / 78125))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((369 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(369 / 256) = 1/(256 / 369) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (365619199 / 1000000000) (28564 / 78125) (Real.log (369 / 256)) := by
  have h := reflection_log_1_neg
  have he : Real.log (369 / 256) = -Real.log (256 / 369) := by
    rw [show ((369 / 256) : ℝ) = ((256 / 369) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (291166407 / 500000000) ≤ -Real.log (143 / 256) ∧
    -Real.log (143 / 256) ≤ (116466563 / 200000000) := by
  have h := checkLog_sound (w := (113 / 399)) (n := 12)
    (lo := (291166407 / 500000000)) (hi := (116466563 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((256 / 143) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(256 / 143) = 1/(143 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-116466563 / 200000000) (-291166407 / 500000000) (Real.log (143 / 256)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (18240293 / 50000000) ≤ -Real.log (2560 / 3687) ∧
    -Real.log (2560 / 3687) ≤ (364805861 / 1000000000) := by
  have h := checkLog_sound (w := (1127 / 6247)) (n := 12)
    (lo := (18240293 / 50000000)) (hi := (364805861 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3687 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3687 / 2560) = 1/(2560 / 3687) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (18240293 / 50000000) (364805861 / 1000000000) (Real.log (3687 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3687 / 2560) = -Real.log (2560 / 3687) := by
    rw [show ((3687 / 2560) : ℝ) = ((2560 / 3687) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (580237109 / 1000000000) ≤ -Real.log (1433 / 2560) ∧
    -Real.log (1433 / 2560) ≤ (58023711 / 100000000) := by
  have h := checkLog_sound (w := (1127 / 3993)) (n := 12)
    (lo := (580237109 / 1000000000)) (hi := (58023711 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1433) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1433) = 1/(1433 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-58023711 / 100000000) (-580237109 / 1000000000) (Real.log (1433 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (632766669 / 1000000000) ≤ -Real.log (128 / 241) ∧
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


theorem reflection_log_5 : Bounds (632766669 / 1000000000) (63276667 / 100000000) (Real.log (241 / 128)) := by
  have h := reflection_log_5_neg
  have he : Real.log (241 / 128) = -Real.log (128 / 241) := by
    rw [show ((241 / 128) : ℝ) = ((128 / 241) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (2143980061 / 1000000000) ≤ -Real.log (15 / 128) ∧
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


theorem reflection_log_6 : Bounds (-428796013 / 200000000) (-2143980061 / 1000000000) (Real.log (15 / 128)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (15788027 / 25000000) ≤ -Real.log (1280 / 2407) ∧
    -Real.log (1280 / 2407) ≤ (631521081 / 1000000000) := by
  have h := checkLog_sound (w := (1127 / 3687)) (n := 12)
    (lo := (15788027 / 25000000)) (hi := (631521081 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2407 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2407 / 1280) = 1/(1280 / 2407) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (15788027 / 25000000) (631521081 / 1000000000) (Real.log (2407 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2407 / 1280) = -Real.log (1280 / 2407) := by
    rw [show ((2407 / 1280) : ℝ) = ((1280 / 2407) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (2124177433 / 1000000000) ≤ -Real.log (153 / 1280) ∧
    -Real.log (153 / 1280) ≤ (2124177437 / 1000000000) := by
  have h := checkLog_sound (w := (7 / 313)) (n := 12)
    (lo := (44735893 / 1000000000)) (hi := (22367947 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 153) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(160 / 153) = 1/(153 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-2124177437 / 1000000000) (-2124177433 / 1000000000) (Real.log (153 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (503872909 / 1000000000) ≤ -Real.log (1000000 / 1655119) ∧
    -Real.log (1000000 / 1655119) ≤ (50387291 / 100000000) := by
  have h := checkLog_sound (w := (655119 / 2655119)) (n := 12)
    (lo := (503872909 / 1000000000)) (hi := (50387291 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1655119 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1655119 / 1000000) = 1/(1000000 / 1655119) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (503872909 / 1000000000) (50387291 / 100000000) (Real.log (1655119 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1655119 / 1000000) = -Real.log (1000000 / 1655119) := by
    rw [show ((1655119 / 1000000) : ℝ) = ((1000000 / 1655119) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (133069481 / 125000000) ≤ -Real.log (344881 / 1000000) ∧
    -Real.log (344881 / 1000000) ≤ (21291117 / 20000000) := by
  have h := checkLog_sound (w := (155119 / 844881)) (n := 12)
    (lo := (92852167 / 250000000)) (hi := (371408669 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 344881) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 344881) = 1/(344881 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-21291117 / 20000000) (-133069481 / 125000000) (Real.log (344881 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (505118569 / 1000000000) ≤ -Real.log (500000 / 828591) ∧
    -Real.log (500000 / 828591) ≤ (50511857 / 100000000) := by
  have h := checkLog_sound (w := (328591 / 1328591)) (n := 12)
    (lo := (505118569 / 1000000000)) (hi := (50511857 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((828591 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(828591 / 500000) = 1/(500000 / 828591) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (505118569 / 1000000000) (50511857 / 100000000) (Real.log (828591 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (828591 / 500000) = -Real.log (500000 / 828591) := by
    rw [show ((828591 / 500000) : ℝ) = ((500000 / 828591) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (16727431 / 15625000) ≤ -Real.log (171409 / 500000) ∧
    -Real.log (171409 / 500000) ≤ (535277793 / 500000000) := by
  have h := checkLog_sound (w := (78591 / 421409)) (n := 12)
    (lo := (94352101 / 250000000)) (hi := (75481681 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 171409) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 171409) = 1/(171409 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-535277793 / 500000000) (-16727431 / 15625000) (Real.log (171409 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (84392849 / 200000000) ≤ -Real.log (500000 / 762477) ∧
    -Real.log (500000 / 762477) ≤ (210982123 / 500000000) := by
  have h := checkLog_sound (w := (262477 / 1262477)) (n := 12)
    (lo := (84392849 / 200000000)) (hi := (210982123 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((762477 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(762477 / 500000) = 1/(500000 / 762477) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (84392849 / 200000000) (210982123 / 500000000) (Real.log (762477 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (762477 / 500000) = -Real.log (500000 / 762477) := by
    rw [show ((762477 / 500000) : ℝ) = ((500000 / 762477) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (186085909 / 250000000) ≤ -Real.log (237523 / 500000) ∧
    -Real.log (237523 / 500000) ≤ (372171819 / 500000000) := by
  have h := checkLog_sound (w := (12477 / 487523)) (n := 12)
    (lo := (6399557 / 125000000)) (hi := (51196457 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 237523) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 237523) = 1/(237523 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-372171819 / 500000000) (-186085909 / 250000000) (Real.log (237523 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (423331221 / 1000000000) ≤ -Real.log (3125 / 4772) ∧
    -Real.log (3125 / 4772) ≤ (211665611 / 500000000) := by
  have h := checkLog_sound (w := (1647 / 7897)) (n := 12)
    (lo := (423331221 / 1000000000)) (hi := (211665611 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4772 / 3125) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4772 / 3125) = 1/(3125 / 4772) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (423331221 / 1000000000) (211665611 / 500000000) (Real.log (4772 / 3125)) := by
  have h := reflection_log_15_neg
  have he : Real.log (4772 / 3125) = -Real.log (3125 / 4772) := by
    rw [show ((4772 / 3125) : ℝ) = ((3125 / 4772) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (37437223 / 50000000) ≤ -Real.log (1478 / 3125) ∧
    -Real.log (1478 / 3125) ≤ (374372231 / 500000000) := by
  have h := checkLog_sound (w := (169 / 6081)) (n := 12)
    (lo := (347483 / 6250000)) (hi := (55597281 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3125 / 2956) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(3125 / 2956) = 1/(1478 / 3125) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-374372231 / 500000000) (-37437223 / 50000000) (Real.log (1478 / 3125)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1568428757 / 1000000000) ≤ -Real.log (500000000000 / 2399550859571) ∧
    -Real.log (500000000000 / 2399550859571) ≤ (39210719 / 25000000) := by
  have h := checkLog_sound (w := (399550859571 / 4399550859571)) (n := 12)
    (lo := (182134397 / 1000000000)) (hi := (91067199 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2399550859571 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2399550859571 / 2000000000000) = 1/(500000000000 / 2399550859571) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1568428757 / 1000000000) (39210719 / 25000000) (Real.log (2399550859571 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (2399550859571 / 500000000000) = -Real.log (500000000000 / 2399550859571) := by
    rw [show ((2399550859571 / 500000000000) : ℝ) = ((500000000000 / 2399550859571) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1575674153 / 1000000000) ≤ -Real.log (500000000000 / 2416999690799) ∧
    -Real.log (500000000000 / 2416999690799) ≤ (393918539 / 250000000) := by
  have h := checkLog_sound (w := (416999690799 / 4416999690799)) (n := 12)
    (lo := (189379793 / 1000000000)) (hi := (94689897 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2416999690799 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2416999690799 / 2000000000000) = 1/(500000000000 / 2416999690799) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1575674153 / 1000000000) (393918539 / 250000000) (Real.log (2416999690799 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (2416999690799 / 500000000000) = -Real.log (500000000000 / 2416999690799) := by
    rw [show ((2416999690799 / 500000000000) : ℝ) = ((500000000000 / 2416999690799) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (583153941 / 500000000) ≤ -Real.log (1562500000 / 5015810311) ∧
    -Real.log (1562500000 / 5015810311) ≤ (291576971 / 250000000) := by
  have h := checkLog_sound (w := (1890810311 / 8140810311)) (n := 12)
    (lo := (236580351 / 500000000)) (hi := (473160703 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5015810311 / 3125000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(5015810311 / 3125000000) = 1/(1562500000 / 5015810311) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (583153941 / 500000000) (291576971 / 250000000) (Real.log (5015810311 / 1562500000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (5015810311 / 1562500000) = -Real.log (1562500000 / 5015810311) := by
    rw [show ((5015810311 / 1562500000) : ℝ) = ((1562500000 / 5015810311) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (1172075681 / 1000000000) ≤ -Real.log (250000000000 / 807171853857) ∧
    -Real.log (250000000000 / 807171853857) ≤ (1172075683 / 1000000000) := by
  have h := checkLog_sound (w := (307171853857 / 1307171853857)) (n := 12)
    (lo := (478928501 / 1000000000)) (hi := (239464251 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((807171853857 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(807171853857 / 500000000000) = 1/(250000000000 / 807171853857) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (1172075681 / 1000000000) (1172075683 / 1000000000) (Real.log (807171853857 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (807171853857 / 250000000000) = -Real.log (250000000000 / 807171853857) := by
    rw [show ((807171853857 / 250000000000) : ℝ) = ((250000000000 / 807171853857) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0061
