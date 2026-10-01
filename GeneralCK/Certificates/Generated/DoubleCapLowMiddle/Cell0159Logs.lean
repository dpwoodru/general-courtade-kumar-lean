import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0159
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

theorem reflection_log_1_neg : (646448577 / 1000000000) ≤ -Real.log (800 / 1527) ∧
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


theorem reflection_log_1 : Bounds (646448577 / 1000000000) (323224289 / 500000000) (Real.log (1527 / 800)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1527 / 800) = -Real.log (800 / 1527) := by
    rw [show ((1527 / 800) : ℝ) = ((800 / 1527) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (598538071 / 250000000) ≤ -Real.log (73 / 800) ∧
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


theorem reflection_log_2 : Bounds (-74817259 / 31250000) (-598538071 / 250000000) (Real.log (73 / 800)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (322835303 / 500000000) ≤ -Real.log (12800 / 24413) ∧
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


theorem reflection_log_3 : Bounds (322835303 / 500000000) (645670607 / 1000000000) (Real.log (24413 / 12800)) := by
  have h := reflection_log_3_neg
  have he : Real.log (24413 / 12800) = -Real.log (12800 / 24413) := by
    rw [show ((24413 / 12800) : ℝ) = ((12800 / 24413) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (2378016053 / 1000000000) ≤ -Real.log (1187 / 12800) ∧
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


theorem reflection_log_4 : Bounds (-2378016057 / 1000000000) (-2378016053 / 1000000000) (Real.log (1187 / 12800)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (59746193 / 100000000) ≤ -Real.log (400 / 727) ∧
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


theorem reflection_log_5 : Bounds (59746193 / 100000000) (597461931 / 1000000000) (Real.log (727 / 400)) := by
  have h := reflection_log_5_neg
  have he : Real.log (727 / 400) = -Real.log (400 / 727) := by
    rw [show ((727 / 400) : ℝ) = ((400 / 727) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (106312819 / 62500000) ≤ -Real.log (73 / 400) ∧
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


theorem reflection_log_6 : Bounds (-1701005107 / 1000000000) (-106312819 / 62500000) (Real.log (73 / 400)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (595827169 / 1000000000) ≤ -Real.log (6400 / 11613) ∧
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


theorem reflection_log_7 : Bounds (595827169 / 1000000000) (59582717 / 100000000) (Real.log (11613 / 6400)) := by
  have h := reflection_log_7_neg
  have he : Real.log (11613 / 6400) = -Real.log (6400 / 11613) := by
    rw [show ((11613 / 6400) : ℝ) = ((6400 / 11613) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (1684868873 / 1000000000) ≤ -Real.log (1187 / 6400) ∧
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


theorem reflection_log_8 : Bounds (-421217219 / 250000000) (-1684868873 / 1000000000) (Real.log (1187 / 6400)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (656674049 / 1000000000) ≤ -Real.log (62500 / 120523) ∧
    -Real.log (62500 / 120523) ≤ (13133481 / 20000000) := by
  have h := checkLog_sound (w := (58023 / 183023)) (n := 12)
    (lo := (656674049 / 1000000000)) (hi := (13133481 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((120523 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(120523 / 62500) = 1/(62500 / 120523) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (656674049 / 1000000000) (13133481 / 20000000) (Real.log (120523 / 62500)) := by
  have h := reflection_log_9_neg
  have he : Real.log (120523 / 62500) = -Real.log (62500 / 120523) := by
    rw [show ((120523 / 62500) : ℝ) = ((62500 / 120523) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (21089707 / 8000000) ≤ -Real.log (4477 / 62500) ∧
    -Real.log (4477 / 62500) ≤ (2636213379 / 1000000000) := by
  have h := checkLog_sound (w := (6671 / 24579)) (n := 12)
    (lo := (111354367 / 200000000)) (hi := (139192959 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 8954) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(15625 / 8954) = 1/(4477 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-2636213379 / 1000000000) (-21089707 / 8000000) (Real.log (4477 / 62500)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (131441711 / 200000000) ≤ -Real.log (1000000 / 1929399) ∧
    -Real.log (1000000 / 1929399) ≤ (164302139 / 250000000) := by
  have h := checkLog_sound (w := (929399 / 2929399)) (n := 12)
    (lo := (131441711 / 200000000)) (hi := (164302139 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1929399 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1929399 / 1000000) = 1/(1000000 / 1929399) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (131441711 / 200000000) (164302139 / 250000000) (Real.log (1929399 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1929399 / 1000000) = -Real.log (1000000 / 1929399) := by
    rw [show ((1929399 / 1000000) : ℝ) = ((1000000 / 1929399) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (331338871 / 125000000) ≤ -Real.log (70601 / 1000000) ∧
    -Real.log (70601 / 1000000) ≤ (662677743 / 250000000) := by
  have h := checkLog_sound (w := (54399 / 195601)) (n := 12)
    (lo := (142817357 / 250000000)) (hi := (571269429 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 70601) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125000 / 70601) = 1/(70601 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-662677743 / 250000000) (-331338871 / 125000000) (Real.log (70601 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (65564467 / 100000000) ≤ -Real.log (62500 / 120399) ∧
    -Real.log (62500 / 120399) ≤ (655644671 / 1000000000) := by
  have h := checkLog_sound (w := (57899 / 182899)) (n := 12)
    (lo := (65564467 / 100000000)) (hi := (655644671 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((120399 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(120399 / 62500) = 1/(62500 / 120399) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (65564467 / 100000000) (655644671 / 1000000000) (Real.log (120399 / 62500)) := by
  have h := reflection_log_13_neg
  have he : Real.log (120399 / 62500) = -Real.log (62500 / 120399) := by
    rw [show ((120399 / 62500) : ℝ) = ((62500 / 120399) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (2608892883 / 1000000000) ≤ -Real.log (4601 / 62500) ∧
    -Real.log (4601 / 62500) ≤ (2608892887 / 1000000000) := by
  have h := checkLog_sound (w := (6423 / 24827)) (n := 12)
    (lo := (529451343 / 1000000000)) (hi := (33090709 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 9202) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(15625 / 9202) = 1/(4601 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-2608892887 / 1000000000) (-2608892883 / 1000000000) (Real.log (4601 / 62500)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (51267 / 78125) ≤ -Real.log (15625 / 30117) ∧
    -Real.log (15625 / 30117) ≤ (656217601 / 1000000000) := by
  have h := checkLog_sound (w := (7246 / 22871)) (n := 12)
    (lo := (51267 / 78125)) (hi := (656217601 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((30117 / 15625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(30117 / 15625) = 1/(15625 / 30117) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (51267 / 78125) (656217601 / 1000000000) (Real.log (30117 / 15625)) := by
  have h := reflection_log_15_neg
  have he : Real.log (30117 / 15625) = -Real.log (15625 / 30117) := by
    rw [show ((30117 / 15625) : ℝ) = ((15625 / 30117) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (2624003211 / 1000000000) ≤ -Real.log (1133 / 15625) ∧
    -Real.log (1133 / 15625) ≤ (524800643 / 200000000) := by
  have h := checkLog_sound (w := (6561 / 24689)) (n := 12)
    (lo := (544561671 / 1000000000)) (hi := (68070209 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 9064) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(15625 / 9064) = 1/(1133 / 15625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-524800643 / 200000000) (-2624003211 / 1000000000) (Real.log (1133 / 15625)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (25725683 / 7812500) ≤ -Real.log (62500000000 / 1682530154121) ∧
    -Real.log (62500000000 / 1682530154121) ≤ (3292887429 / 1000000000) := by
  have h := checkLog_sound (w := (682530154121 / 2682530154121)) (n := 12)
    (lo := (32518669 / 62500000)) (hi := (104059741 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1682530154121 / 1000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1682530154121 / 1000000000000) = 1/(62500000000 / 1682530154121) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (25725683 / 7812500) (3292887429 / 1000000000) (Real.log (1682530154121 / 62500000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1682530154121 / 62500000000) = -Real.log (62500000000 / 1682530154121) := by
    rw [show ((1682530154121 / 62500000000) : ℝ) = ((62500000000 / 1682530154121) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (3307919523 / 1000000000) ≤ -Real.log (1953125000 / 53375411423) ∧
    -Real.log (1953125000 / 53375411423) ≤ (413489941 / 125000000) := by
  have h := checkLog_sound (w := (22125411423 / 84625411423)) (n := 12)
    (lo := (535330803 / 1000000000)) (hi := (133832701 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((53375411423 / 31250000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(53375411423 / 31250000000) = 1/(1953125000 / 53375411423) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (3307919523 / 1000000000) (413489941 / 125000000) (Real.log (53375411423 / 1953125000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (53375411423 / 1953125000) = -Real.log (1953125000 / 53375411423) := by
    rw [show ((53375411423 / 1953125000) : ℝ) = ((1953125000 / 53375411423) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (3264537553 / 1000000000) ≤ -Real.log (244140625 / 6388673573) ∧
    -Real.log (244140625 / 6388673573) ≤ (1632268779 / 500000000) := by
  have h := checkLog_sound (w := (2482423573 / 10294923573)) (n := 12)
    (lo := (491948833 / 1000000000)) (hi := (245974417 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6388673573 / 3906250000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(6388673573 / 3906250000) = 1/(244140625 / 6388673573) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (3264537553 / 1000000000) (1632268779 / 500000000) (Real.log (6388673573 / 244140625)) := by
  have h := reflection_log_19_neg
  have he : Real.log (6388673573 / 244140625) = -Real.log (244140625 / 6388673573) := by
    rw [show ((6388673573 / 244140625) : ℝ) = ((244140625 / 6388673573) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (820055203 / 250000000) ≤ -Real.log (62500000000 / 1661352603707) ∧
    -Real.log (62500000000 / 1661352603707) ≤ (3280220817 / 1000000000) := by
  have h := checkLog_sound (w := (661352603707 / 2661352603707)) (n := 12)
    (lo := (126908023 / 250000000)) (hi := (507632093 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1661352603707 / 1000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1661352603707 / 1000000000000) = 1/(62500000000 / 1661352603707) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (820055203 / 250000000) (3280220817 / 1000000000) (Real.log (1661352603707 / 62500000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1661352603707 / 62500000000) = -Real.log (62500000000 / 1661352603707) := by
    rw [show ((1661352603707 / 62500000000) : ℝ) = ((62500000000 / 1661352603707) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0159
