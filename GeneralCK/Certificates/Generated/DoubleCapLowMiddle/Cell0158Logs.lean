import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0158
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

theorem reflection_log_1_neg : (647225943 / 1000000000) ≤ -Real.log (12800 / 24451) ∧
    -Real.log (12800 / 24451) ≤ (80903243 / 125000000) := by
  have h := checkLog_sound (w := (11651 / 37251)) (n := 12)
    (lo := (647225943 / 1000000000)) (hi := (80903243 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24451 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24451 / 12800) = 1/(12800 / 24451) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (647225943 / 1000000000) (80903243 / 125000000) (Real.log (24451 / 12800)) := by
  have h := reflection_log_1_neg
  have he : Real.log (24451 / 12800) = -Real.log (12800 / 24451) := by
    rw [show ((24451 / 12800) : ℝ) = ((12800 / 24451) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (241055317 / 100000000) ≤ -Real.log (1149 / 12800) ∧
    -Real.log (1149 / 12800) ≤ (1205276587 / 500000000) := by
  have h := checkLog_sound (w := (451 / 2749)) (n := 12)
    (lo := (33111163 / 100000000)) (hi := (331111631 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1149) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1600 / 1149) = 1/(1149 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-1205276587 / 500000000) (-241055317 / 100000000) (Real.log (1149 / 12800)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (646448577 / 1000000000) ≤ -Real.log (800 / 1527) ∧
    -Real.log (800 / 1527) ≤ (323224289 / 500000000) := by
  have h := checkLog_sound (w := (727 / 2327)) (n := 12)
    (lo := (646448577 / 1000000000)) (hi := (323224289 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1527 / 800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1527 / 800) = 1/(800 / 1527) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (646448577 / 1000000000) (323224289 / 500000000) (Real.log (1527 / 800)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1527 / 800) = -Real.log (800 / 1527) := by
    rw [show ((1527 / 800) : ℝ) = ((800 / 1527) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (598538071 / 250000000) ≤ -Real.log (73 / 800) ∧
    -Real.log (73 / 800) ≤ (74817259 / 31250000) := by
  have h := checkLog_sound (w := (27 / 173)) (n := 12)
    (lo := (39338843 / 125000000)) (hi := (62942149 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100 / 73) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(100 / 73) = 1/(73 / 800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-74817259 / 31250000) (-598538071 / 250000000) (Real.log (73 / 800)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (299547011 / 500000000) ≤ -Real.log (6400 / 11651) ∧
    -Real.log (6400 / 11651) ≤ (599094023 / 1000000000) := by
  have h := checkLog_sound (w := (5251 / 18051)) (n := 12)
    (lo := (299547011 / 500000000)) (hi := (599094023 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11651 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11651 / 6400) = 1/(6400 / 11651) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (299547011 / 500000000) (599094023 / 1000000000) (Real.log (11651 / 6400)) := by
  have h := reflection_log_5_neg
  have he : Real.log (11651 / 6400) = -Real.log (6400 / 11651) := by
    rw [show ((11651 / 6400) : ℝ) = ((6400 / 11651) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (171740599 / 100000000) ≤ -Real.log (1149 / 6400) ∧
    -Real.log (1149 / 6400) ≤ (1717405993 / 1000000000) := by
  have h := checkLog_sound (w := (451 / 2749)) (n := 12)
    (lo := (33111163 / 100000000)) (hi := (331111631 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1149) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1600 / 1149) = 1/(1149 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1717405993 / 1000000000) (-171740599 / 100000000) (Real.log (1149 / 6400)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (59746193 / 100000000) ≤ -Real.log (400 / 727) ∧
    -Real.log (400 / 727) ≤ (597461931 / 1000000000) := by
  have h := checkLog_sound (w := (327 / 1127)) (n := 12)
    (lo := (59746193 / 100000000)) (hi := (597461931 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((727 / 400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(727 / 400) = 1/(400 / 727) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (59746193 / 100000000) (597461931 / 1000000000) (Real.log (727 / 400)) := by
  have h := reflection_log_7_neg
  have he : Real.log (727 / 400) = -Real.log (400 / 727) := by
    rw [show ((727 / 400) : ℝ) = ((400 / 727) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (106312819 / 62500000) ≤ -Real.log (73 / 400) ∧
    -Real.log (73 / 400) ≤ (1701005107 / 1000000000) := by
  have h := checkLog_sound (w := (27 / 173)) (n := 12)
    (lo := (39338843 / 125000000)) (hi := (62942149 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100 / 73) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(100 / 73) = 1/(73 / 400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1701005107 / 1000000000) (-106312819 / 62500000) (Real.log (73 / 400)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (657208037 / 1000000000) ≤ -Real.log (500000 / 964699) ∧
    -Real.log (500000 / 964699) ≤ (328604019 / 500000000) := by
  have h := checkLog_sound (w := (464699 / 1464699)) (n := 12)
    (lo := (657208037 / 1000000000)) (hi := (328604019 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((964699 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(964699 / 500000) = 1/(500000 / 964699) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (657208037 / 1000000000) (328604019 / 500000000) (Real.log (964699 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (964699 / 500000) = -Real.log (500000 / 964699) := by
    rw [show ((964699 / 500000) : ℝ) = ((500000 / 964699) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (662674201 / 250000000) ≤ -Real.log (35301 / 500000) ∧
    -Real.log (35301 / 500000) ≤ (331337101 / 125000000) := by
  have h := checkLog_sound (w := (27199 / 97801)) (n := 12)
    (lo := (17851727 / 31250000)) (hi := (114251053 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 35301) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(62500 / 35301) = 1/(35301 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-331337101 / 125000000) (-662674201 / 250000000) (Real.log (35301 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (164435953 / 250000000) ≤ -Real.log (15625 / 30163) ∧
    -Real.log (15625 / 30163) ≤ (657743813 / 1000000000) := by
  have h := checkLog_sound (w := (7269 / 22894)) (n := 12)
    (lo := (164435953 / 250000000)) (hi := (657743813 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((30163 / 15625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(30163 / 15625) = 1/(15625 / 30163) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (164435953 / 250000000) (657743813 / 1000000000) (Real.log (30163 / 15625)) := by
  have h := reflection_log_11_neg
  have he : Real.log (30163 / 15625) = -Real.log (15625 / 30163) := by
    rw [show ((30163 / 15625) : ℝ) = ((15625 / 30163) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (533090117 / 200000000) ≤ -Real.log (1087 / 15625) ∧
    -Real.log (1087 / 15625) ≤ (2665450589 / 1000000000) := by
  have h := checkLog_sound (w := (6929 / 24321)) (n := 12)
    (lo := (117201809 / 200000000)) (hi := (293004523 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 8696) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(15625 / 8696) = 1/(1087 / 15625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-2665450589 / 1000000000) (-533090117 / 200000000) (Real.log (1087 / 15625)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (656217081 / 1000000000) ≤ -Real.log (1000000 / 1927487) ∧
    -Real.log (1000000 / 1927487) ≤ (328108541 / 500000000) := by
  have h := checkLog_sound (w := (927487 / 2927487)) (n := 12)
    (lo := (656217081 / 1000000000)) (hi := (328108541 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1927487 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1927487 / 1000000) = 1/(1000000 / 1927487) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (656217081 / 1000000000) (328108541 / 500000000) (Real.log (1927487 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1927487 / 1000000) = -Real.log (1000000 / 1927487) := by
    rw [show ((1927487 / 1000000) : ℝ) = ((1000000 / 1927487) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (2623989421 / 1000000000) ≤ -Real.log (72513 / 1000000) ∧
    -Real.log (72513 / 1000000) ≤ (104959577 / 40000000) := by
  have h := checkLog_sound (w := (52487 / 197513)) (n := 12)
    (lo := (544547881 / 1000000000)) (hi := (272273941 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 72513) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125000 / 72513) = 1/(72513 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-104959577 / 40000000) (-2623989421 / 1000000000) (Real.log (72513 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (328395101 / 500000000) ≤ -Real.log (62500 / 120537) ∧
    -Real.log (62500 / 120537) ≤ (656790203 / 1000000000) := by
  have h := checkLog_sound (w := (58037 / 183037)) (n := 12)
    (lo := (328395101 / 500000000)) (hi := (656790203 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((120537 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(120537 / 62500) = 1/(62500 / 120537) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (328395101 / 500000000) (656790203 / 1000000000) (Real.log (120537 / 62500)) := by
  have h := reflection_log_15_neg
  have he : Real.log (120537 / 62500) = -Real.log (62500 / 120537) := by
    rw [show ((120537 / 62500) : ℝ) = ((62500 / 120537) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (2639345369 / 1000000000) ≤ -Real.log (4463 / 62500) ∧
    -Real.log (4463 / 62500) ≤ (2639345373 / 1000000000) := by
  have h := checkLog_sound (w := (6699 / 24551)) (n := 12)
    (lo := (559903829 / 1000000000)) (hi := (55990383 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 8926) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(15625 / 8926) = 1/(4463 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-2639345373 / 1000000000) (-2639345369 / 1000000000) (Real.log (4463 / 62500)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (3307904841 / 1000000000) ≤ -Real.log (500000000000 / 13663904705249) ∧
    -Real.log (500000000000 / 13663904705249) ≤ (1653952423 / 500000000) := by
  have h := checkLog_sound (w := (5663904705249 / 21663904705249)) (n := 12)
    (lo := (535316121 / 1000000000)) (hi := (267658061 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((13663904705249 / 8000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(13663904705249 / 8000000000000) = 1/(500000000000 / 13663904705249) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (3307904841 / 1000000000) (1653952423 / 500000000) (Real.log (13663904705249 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (13663904705249 / 500000000000) = -Real.log (500000000000 / 13663904705249) := by
    rw [show ((13663904705249 / 500000000000) : ℝ) = ((500000000000 / 13663904705249) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (3323194397 / 1000000000) ≤ -Real.log (500000000 / 13874425023) ∧
    -Real.log (500000000 / 13874425023) ≤ (1661597201 / 500000000) := by
  have h := checkLog_sound (w := (5874425023 / 21874425023)) (n := 12)
    (lo := (550605677 / 1000000000)) (hi := (275302839 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((13874425023 / 8000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(13874425023 / 8000000000) = 1/(500000000 / 13874425023) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (3323194397 / 1000000000) (1661597201 / 500000000) (Real.log (13874425023 / 500000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (13874425023 / 500000000) = -Real.log (500000000 / 13874425023) := by
    rw [show ((13874425023 / 500000000) : ℝ) = ((500000000 / 13874425023) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1640103251 / 500000000) ≤ -Real.log (500000000000 / 13290630645539) ∧
    -Real.log (500000000000 / 13290630645539) ≤ (3280206507 / 1000000000) := by
  have h := checkLog_sound (w := (5290630645539 / 21290630645539)) (n := 12)
    (lo := (253808891 / 500000000)) (hi := (507617783 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((13290630645539 / 8000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(13290630645539 / 8000000000000) = 1/(500000000000 / 13290630645539) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (1640103251 / 500000000) (3280206507 / 1000000000) (Real.log (13290630645539 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (13290630645539 / 500000000000) = -Real.log (500000000000 / 13290630645539) := by
    rw [show ((13290630645539 / 500000000000) : ℝ) = ((500000000000 / 13290630645539) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (3296135571 / 1000000000) ≤ -Real.log (500000000000 / 13504033161551) ∧
    -Real.log (500000000000 / 13504033161551) ≤ (412016947 / 125000000) := by
  have h := checkLog_sound (w := (5504033161551 / 21504033161551)) (n := 12)
    (lo := (523546851 / 1000000000)) (hi := (130886713 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((13504033161551 / 8000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(13504033161551 / 8000000000000) = 1/(500000000000 / 13504033161551) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (3296135571 / 1000000000) (412016947 / 125000000) (Real.log (13504033161551 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (13504033161551 / 500000000000) = -Real.log (500000000000 / 13504033161551) := by
    rw [show ((13504033161551 / 500000000000) : ℝ) = ((500000000000 / 13504033161551) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0158
