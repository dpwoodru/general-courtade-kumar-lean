import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0450
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

theorem reflection_log_1_neg : (23520479 / 125000000) ≤ -Real.log (256 / 309) ∧
    -Real.log (256 / 309) ≤ (188163833 / 1000000000) := by
  have h := checkLog_sound (w := (53 / 565)) (n := 12)
    (lo := (23520479 / 125000000)) (hi := (188163833 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((309 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(309 / 256) = 1/(256 / 309) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (23520479 / 125000000) (188163833 / 1000000000) (Real.log (309 / 256)) := by
  have h := reflection_log_1_neg
  have he : Real.log (309 / 256) = -Real.log (256 / 309) := by
    rw [show ((309 / 256) : ℝ) = ((256 / 309) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (46394293 / 200000000) ≤ -Real.log (203 / 256) ∧
    -Real.log (203 / 256) ≤ (115985733 / 500000000) := by
  have h := checkLog_sound (w := (53 / 459)) (n := 12)
    (lo := (46394293 / 200000000)) (hi := (115985733 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((256 / 203) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(256 / 203) = 1/(203 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-115985733 / 500000000) (-46394293 / 200000000) (Real.log (203 / 256)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (46980271 / 250000000) ≤ -Real.log (10240 / 12357) ∧
    -Real.log (10240 / 12357) ≤ (37584217 / 200000000) := by
  have h := checkLog_sound (w := (2117 / 22597)) (n := 12)
    (lo := (46980271 / 250000000)) (hi := (37584217 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12357 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12357 / 10240) = 1/(10240 / 12357) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (46980271 / 250000000) (37584217 / 200000000) (Real.log (12357 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12357 / 10240) = -Real.log (10240 / 12357) := by
    rw [show ((12357 / 10240) : ℝ) = ((10240 / 12357) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (9264083 / 40000000) ≤ -Real.log (8123 / 10240) ∧
    -Real.log (8123 / 10240) ≤ (57900519 / 250000000) := by
  have h := checkLog_sound (w := (2117 / 18363)) (n := 12)
    (lo := (9264083 / 40000000)) (hi := (57900519 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 8123) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 8123) = 1/(8123 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-57900519 / 250000000) (-9264083 / 40000000) (Real.log (8123 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (346466767 / 1000000000) ≤ -Real.log (128 / 181) ∧
    -Real.log (128 / 181) ≤ (21654173 / 62500000) := by
  have h := checkLog_sound (w := (53 / 309)) (n := 12)
    (lo := (346466767 / 1000000000)) (hi := (21654173 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((181 / 128) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(181 / 128) = 1/(128 / 181) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (346466767 / 1000000000) (21654173 / 62500000) (Real.log (181 / 128)) := by
  have h := reflection_log_5_neg
  have he : Real.log (181 / 128) = -Real.log (128 / 181) := by
    rw [show ((181 / 128) : ℝ) = ((128 / 181) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (10690843 / 20000000) ≤ -Real.log (75 / 128) ∧
    -Real.log (75 / 128) ≤ (534542151 / 1000000000) := by
  have h := checkLog_sound (w := (53 / 203)) (n := 12)
    (lo := (10690843 / 20000000)) (hi := (534542151 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((128 / 75) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(128 / 75) = 1/(75 / 128) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-534542151 / 1000000000) (-10690843 / 20000000) (Real.log (75 / 128)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (86513079 / 250000000) ≤ -Real.log (5120 / 7237) ∧
    -Real.log (5120 / 7237) ≤ (346052317 / 1000000000) := by
  have h := checkLog_sound (w := (2117 / 12357)) (n := 12)
    (lo := (86513079 / 250000000)) (hi := (346052317 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7237 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7237 / 5120) = 1/(5120 / 7237) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (86513079 / 250000000) (346052317 / 1000000000) (Real.log (7237 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (7237 / 5120) = -Real.log (5120 / 7237) := by
    rw [show ((7237 / 5120) : ℝ) = ((5120 / 7237) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (10670853 / 20000000) ≤ -Real.log (3003 / 5120) ∧
    -Real.log (3003 / 5120) ≤ (533542651 / 1000000000) := by
  have h := checkLog_sound (w := (2117 / 8123)) (n := 12)
    (lo := (10670853 / 20000000)) (hi := (533542651 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3003) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3003) = 1/(3003 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-533542651 / 1000000000) (-10670853 / 20000000) (Real.log (3003 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (129107449 / 500000000) ≤ -Real.log (1000000 / 1294617) ∧
    -Real.log (1000000 / 1294617) ≤ (258214899 / 1000000000) := by
  have h := checkLog_sound (w := (294617 / 2294617)) (n := 12)
    (lo := (129107449 / 500000000)) (hi := (258214899 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1294617 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1294617 / 1000000) = 1/(1000000 / 1294617) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (129107449 / 500000000) (258214899 / 1000000000) (Real.log (1294617 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1294617 / 1000000) = -Real.log (1000000 / 1294617) := by
    rw [show ((1294617 / 1000000) : ℝ) = ((1000000 / 1294617) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (349014361 / 1000000000) ≤ -Real.log (705383 / 1000000) ∧
    -Real.log (705383 / 1000000) ≤ (174507181 / 500000000) := by
  have h := checkLog_sound (w := (294617 / 1705383)) (n := 12)
    (lo := (349014361 / 1000000000)) (hi := (174507181 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 705383) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 705383) = 1/(705383 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-174507181 / 500000000) (-349014361 / 1000000000) (Real.log (705383 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (258543127 / 1000000000) ≤ -Real.log (500000 / 647521) ∧
    -Real.log (500000 / 647521) ≤ (32317891 / 125000000) := by
  have h := checkLog_sound (w := (147521 / 1147521)) (n := 12)
    (lo := (258543127 / 1000000000)) (hi := (32317891 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((647521 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(647521 / 500000) = 1/(500000 / 647521) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (258543127 / 1000000000) (32317891 / 125000000) (Real.log (647521 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (647521 / 500000) = -Real.log (500000 / 647521) := by
    rw [show ((647521 / 500000) : ℝ) = ((500000 / 647521) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (87404263 / 250000000) ≤ -Real.log (352479 / 500000) ∧
    -Real.log (352479 / 500000) ≤ (349617053 / 1000000000) := by
  have h := checkLog_sound (w := (147521 / 852479)) (n := 12)
    (lo := (87404263 / 250000000)) (hi := (349617053 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 352479) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 352479) = 1/(352479 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-349617053 / 1000000000) (-87404263 / 250000000) (Real.log (352479 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (96736243 / 500000000) ≤ -Real.log (62500 / 75841) ∧
    -Real.log (62500 / 75841) ≤ (193472487 / 1000000000) := by
  have h := checkLog_sound (w := (13341 / 138341)) (n := 12)
    (lo := (96736243 / 500000000)) (hi := (193472487 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((75841 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(75841 / 62500) = 1/(62500 / 75841) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (96736243 / 500000000) (193472487 / 1000000000) (Real.log (75841 / 62500)) := by
  have h := reflection_log_13_neg
  have he : Real.log (75841 / 62500) = -Real.log (62500 / 75841) := by
    rw [show ((75841 / 62500) : ℝ) = ((62500 / 75841) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (240106613 / 1000000000) ≤ -Real.log (49159 / 62500) ∧
    -Real.log (49159 / 62500) ≤ (120053307 / 500000000) := by
  have h := checkLog_sound (w := (13341 / 111659)) (n := 12)
    (lo := (240106613 / 1000000000)) (hi := (120053307 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 49159) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 49159) = 1/(49159 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-120053307 / 500000000) (-240106613 / 1000000000) (Real.log (49159 / 62500)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (193738633 / 1000000000) ≤ -Real.log (1000000 / 1213779) ∧
    -Real.log (1000000 / 1213779) ≤ (96869317 / 500000000) := by
  have h := checkLog_sound (w := (213779 / 2213779)) (n := 12)
    (lo := (193738633 / 1000000000)) (hi := (96869317 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1213779 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1213779 / 1000000) = 1/(1000000 / 1213779) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (193738633 / 1000000000) (96869317 / 500000000) (Real.log (1213779 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1213779 / 1000000) = -Real.log (1000000 / 1213779) := by
    rw [show ((1213779 / 1000000) : ℝ) = ((1000000 / 1213779) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (48103471 / 200000000) ≤ -Real.log (786221 / 1000000) ∧
    -Real.log (786221 / 1000000) ≤ (60129339 / 250000000) := by
  have h := checkLog_sound (w := (213779 / 1786221)) (n := 12)
    (lo := (48103471 / 200000000)) (hi := (60129339 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 786221) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 786221) = 1/(786221 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-60129339 / 250000000) (-48103471 / 200000000) (Real.log (786221 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (607229259 / 1000000000) ≤ -Real.log (500000000000 / 917669549733) ∧
    -Real.log (500000000000 / 917669549733) ≤ (30361463 / 50000000) := by
  have h := checkLog_sound (w := (417669549733 / 1417669549733)) (n := 12)
    (lo := (607229259 / 1000000000)) (hi := (30361463 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((917669549733 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(917669549733 / 500000000000) = 1/(500000000000 / 917669549733) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (607229259 / 1000000000) (30361463 / 50000000) (Real.log (917669549733 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (917669549733 / 500000000000) = -Real.log (500000000000 / 917669549733) := by
    rw [show ((917669549733 / 500000000000) : ℝ) = ((500000000000 / 917669549733) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (608160179 / 1000000000) ≤ -Real.log (500000000000 / 918524224139) ∧
    -Real.log (500000000000 / 918524224139) ≤ (30408009 / 50000000) := by
  have h := checkLog_sound (w := (418524224139 / 1418524224139)) (n := 12)
    (lo := (608160179 / 1000000000)) (hi := (30408009 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((918524224139 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(918524224139 / 500000000000) = 1/(500000000000 / 918524224139) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (608160179 / 1000000000) (30408009 / 50000000) (Real.log (918524224139 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (918524224139 / 500000000000) = -Real.log (500000000000 / 918524224139) := by
    rw [show ((918524224139 / 500000000000) : ℝ) = ((500000000000 / 918524224139) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (4335791 / 10000000) ≤ -Real.log (250000000000 / 385692345247) ∧
    -Real.log (250000000000 / 385692345247) ≤ (433579101 / 1000000000) := by
  have h := checkLog_sound (w := (135692345247 / 635692345247)) (n := 12)
    (lo := (4335791 / 10000000)) (hi := (433579101 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((385692345247 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(385692345247 / 250000000000) = 1/(250000000000 / 385692345247) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (4335791 / 10000000) (433579101 / 1000000000) (Real.log (385692345247 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (385692345247 / 250000000000) = -Real.log (250000000000 / 385692345247) := by
    rw [show ((385692345247 / 250000000000) : ℝ) = ((250000000000 / 385692345247) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (108563997 / 250000000) ≤ -Real.log (100000000000 / 154381401667) ∧
    -Real.log (100000000000 / 154381401667) ≤ (434255989 / 1000000000) := by
  have h := checkLog_sound (w := (54381401667 / 254381401667)) (n := 12)
    (lo := (108563997 / 250000000)) (hi := (434255989 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((154381401667 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(154381401667 / 100000000000) = 1/(100000000000 / 154381401667) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (108563997 / 250000000) (434255989 / 1000000000) (Real.log (154381401667 / 100000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (154381401667 / 100000000000) = -Real.log (100000000000 / 154381401667) := by
    rw [show ((154381401667 / 100000000000) : ℝ) = ((100000000000 / 154381401667) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0450
