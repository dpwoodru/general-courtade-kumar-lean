import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0034
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

theorem reflection_log_1_neg : (387332959 / 1000000000) ≤ -Real.log (2560 / 3771) ∧
    -Real.log (2560 / 3771) ≤ (2420831 / 6250000) := by
  have h := checkLog_sound (w := (1211 / 6331)) (n := 12)
    (lo := (387332959 / 1000000000)) (hi := (2420831 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3771 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3771 / 2560) = 1/(2560 / 3771) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (387332959 / 1000000000) (2420831 / 6250000) (Real.log (3771 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3771 / 2560) = -Real.log (2560 / 3771) := by
    rw [show ((3771 / 2560) : ℝ) = ((2560 / 3771) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (640643681 / 1000000000) ≤ -Real.log (1349 / 2560) ∧
    -Real.log (1349 / 2560) ≤ (320321841 / 500000000) := by
  have h := checkLog_sound (w := (1211 / 3909)) (n := 12)
    (lo := (640643681 / 1000000000)) (hi := (320321841 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1349) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1349) = 1/(1349 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-320321841 / 500000000) (-640643681 / 1000000000) (Real.log (1349 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (193268549 / 500000000) ≤ -Real.log (320 / 471) ∧
    -Real.log (320 / 471) ≤ (386537099 / 1000000000) := by
  have h := checkLog_sound (w := (151 / 791)) (n := 12)
    (lo := (193268549 / 500000000)) (hi := (386537099 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((471 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(471 / 320) = 1/(320 / 471) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (193268549 / 500000000) (386537099 / 1000000000) (Real.log (471 / 320)) := by
  have h := reflection_log_3_neg
  have he : Real.log (471 / 320) = -Real.log (320 / 471) := by
    rw [show ((471 / 320) : ℝ) = ((320 / 471) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (15960557 / 25000000) ≤ -Real.log (169 / 320) ∧
    -Real.log (169 / 320) ≤ (638422281 / 1000000000) := by
  have h := checkLog_sound (w := (151 / 489)) (n := 12)
    (lo := (15960557 / 25000000)) (hi := (638422281 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 169) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(320 / 169) = 1/(169 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-638422281 / 1000000000) (-15960557 / 25000000) (Real.log (169 / 320)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (332912079 / 500000000) ≤ -Real.log (1280 / 2491) ∧
    -Real.log (1280 / 2491) ≤ (665824159 / 1000000000) := by
  have h := checkLog_sound (w := (1211 / 3771)) (n := 12)
    (lo := (332912079 / 500000000)) (hi := (665824159 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2491 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2491 / 1280) = 1/(1280 / 2491) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (332912079 / 500000000) (665824159 / 1000000000) (Real.log (2491 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2491 / 1280) = -Real.log (1280 / 2491) := by
    rw [show ((2491 / 1280) : ℝ) = ((1280 / 2491) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (58410177 / 20000000) ≤ -Real.log (69 / 1280) ∧
    -Real.log (69 / 1280) ≤ (584101771 / 200000000) := by
  have h := checkLog_sound (w := (11 / 149)) (n := 12)
    (lo := (14792013 / 100000000)) (hi := (147920131 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80 / 69) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(80 / 69) = 1/(69 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-584101771 / 200000000) (-58410177 / 20000000) (Real.log (69 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (83077387 / 125000000) ≤ -Real.log (160 / 311) ∧
    -Real.log (160 / 311) ≤ (664619097 / 1000000000) := by
  have h := checkLog_sound (w := (151 / 471)) (n := 12)
    (lo := (83077387 / 125000000)) (hi := (664619097 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((311 / 160) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(311 / 160) = 1/(160 / 311) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (83077387 / 125000000) (664619097 / 1000000000) (Real.log (311 / 160)) := by
  have h := reflection_log_7_neg
  have he : Real.log (311 / 160) = -Real.log (160 / 311) := by
    rw [show ((311 / 160) : ℝ) = ((160 / 311) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (575589847 / 200000000) ≤ -Real.log (9 / 160) ∧
    -Real.log (9 / 160) ≤ (71948731 / 25000000) := by
  have h := checkLog_sound (w := (1 / 19)) (n := 12)
    (lo := (21072103 / 200000000)) (hi := (26340129 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10 / 9) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(10 / 9) = 1/(9 / 160) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-71948731 / 25000000) (-575589847 / 200000000) (Real.log (9 / 160)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (538645439 / 1000000000) ≤ -Real.log (250000 / 428421) ∧
    -Real.log (250000 / 428421) ≤ (1683267 / 3125000) := by
  have h := checkLog_sound (w := (178421 / 678421)) (n := 12)
    (lo := (538645439 / 1000000000)) (hi := (1683267 / 3125000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((428421 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(428421 / 250000) = 1/(250000 / 428421) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (538645439 / 1000000000) (1683267 / 3125000) (Real.log (428421 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (428421 / 250000) = -Real.log (250000 / 428421) := by
    rw [show ((428421 / 250000) : ℝ) = ((250000 / 428421) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (625329591 / 500000000) ≤ -Real.log (71579 / 250000) ∧
    -Real.log (71579 / 250000) ≤ (78166199 / 62500000) := by
  have h := checkLog_sound (w := (53421 / 196579)) (n := 12)
    (lo := (278756001 / 500000000)) (hi := (557512003 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 71579) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(125000 / 71579) = 1/(71579 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-78166199 / 62500000) (-625329591 / 500000000) (Real.log (71579 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (67500447 / 125000000) ≤ -Real.log (1000000 / 1716013) ∧
    -Real.log (1000000 / 1716013) ≤ (540003577 / 1000000000) := by
  have h := checkLog_sound (w := (716013 / 2716013)) (n := 12)
    (lo := (67500447 / 125000000)) (hi := (540003577 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1716013 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1716013 / 1000000) = 1/(1000000 / 1716013) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (67500447 / 125000000) (540003577 / 1000000000) (Real.log (1716013 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1716013 / 1000000) = -Real.log (1000000 / 1716013) := by
    rw [show ((1716013 / 1000000) : ℝ) = ((1000000 / 1716013) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (251765363 / 200000000) ≤ -Real.log (283987 / 1000000) ∧
    -Real.log (283987 / 1000000) ≤ (1258826817 / 1000000000) := by
  have h := checkLog_sound (w := (216013 / 783987)) (n := 12)
    (lo := (113135927 / 200000000)) (hi := (141419909 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 283987) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 283987) = 1/(283987 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1258826817 / 1000000000) (-251765363 / 200000000) (Real.log (283987 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (230603463 / 500000000) ≤ -Real.log (1000000 / 1585987) ∧
    -Real.log (1000000 / 1585987) ≤ (461206927 / 1000000000) := by
  have h := checkLog_sound (w := (585987 / 2585987)) (n := 12)
    (lo := (230603463 / 500000000)) (hi := (461206927 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1585987 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1585987 / 1000000) = 1/(1000000 / 1585987) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (230603463 / 500000000) (461206927 / 1000000000) (Real.log (1585987 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1585987 / 1000000) = -Real.log (1000000 / 1585987) := by
    rw [show ((1585987 / 1000000) : ℝ) = ((1000000 / 1585987) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (55116119 / 62500000) ≤ -Real.log (414013 / 1000000) ∧
    -Real.log (414013 / 1000000) ≤ (440928953 / 500000000) := by
  have h := checkLog_sound (w := (85987 / 914013)) (n := 12)
    (lo := (47177681 / 250000000)) (hi := (7548429 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 414013) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 414013) = 1/(414013 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-440928953 / 500000000) (-55116119 / 62500000) (Real.log (414013 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (57848221 / 125000000) ≤ -Real.log (1000000 / 1588493) ∧
    -Real.log (1000000 / 1588493) ≤ (462785769 / 1000000000) := by
  have h := checkLog_sound (w := (588493 / 2588493)) (n := 12)
    (lo := (57848221 / 125000000)) (hi := (462785769 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1588493 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1588493 / 1000000) = 1/(1000000 / 1588493) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (57848221 / 125000000) (462785769 / 1000000000) (Real.log (1588493 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1588493 / 1000000) = -Real.log (1000000 / 1588493) := by
    rw [show ((1588493 / 1000000) : ℝ) = ((1000000 / 1588493) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (887929247 / 1000000000) ≤ -Real.log (411507 / 1000000) ∧
    -Real.log (411507 / 1000000) ≤ (887929249 / 1000000000) := by
  have h := checkLog_sound (w := (88493 / 911507)) (n := 12)
    (lo := (194782067 / 1000000000)) (hi := (48695517 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 411507) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 411507) = 1/(411507 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-887929249 / 1000000000) (-887929247 / 1000000000) (Real.log (411507 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1789304621 / 1000000000) ≤ -Real.log (250000000000 / 1496322245351) ∧
    -Real.log (250000000000 / 1496322245351) ≤ (111831539 / 62500000) := by
  have h := checkLog_sound (w := (496322245351 / 2496322245351)) (n := 12)
    (lo := (403010261 / 1000000000)) (hi := (201505131 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1496322245351 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1496322245351 / 1000000000000) = 1/(250000000000 / 1496322245351) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1789304621 / 1000000000) (111831539 / 62500000) (Real.log (1496322245351 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1496322245351 / 250000000000) = -Real.log (250000000000 / 1496322245351) := by
    rw [show ((1496322245351 / 250000000000) : ℝ) = ((250000000000 / 1496322245351) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (224853799 / 125000000) ≤ -Real.log (12500000000 / 75532198657) ∧
    -Real.log (12500000000 / 75532198657) ≤ (359766079 / 200000000) := by
  have h := checkLog_sound (w := (25532198657 / 125532198657)) (n := 12)
    (lo := (12891751 / 31250000)) (hi := (412536033 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((75532198657 / 50000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(75532198657 / 50000000000) = 1/(12500000000 / 75532198657) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (224853799 / 125000000) (359766079 / 200000000) (Real.log (75532198657 / 12500000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (75532198657 / 12500000000) = -Real.log (12500000000 / 75532198657) := by
    rw [show ((75532198657 / 12500000000) : ℝ) = ((12500000000 / 75532198657) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (134306483 / 100000000) ≤ -Real.log (100000000000 / 383076618367) ∧
    -Real.log (100000000000 / 383076618367) ≤ (5246347 / 3906250) := by
  have h := checkLog_sound (w := (183076618367 / 583076618367)) (n := 12)
    (lo := (12998353 / 20000000)) (hi := (649917651 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((383076618367 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(383076618367 / 200000000000) = 1/(100000000000 / 383076618367) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (134306483 / 100000000) (5246347 / 3906250) (Real.log (383076618367 / 100000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (383076618367 / 100000000000) = -Real.log (100000000000 / 383076618367) := by
    rw [show ((383076618367 / 100000000000) : ℝ) = ((100000000000 / 383076618367) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (270143003 / 200000000) ≤ -Real.log (62500000000 / 241261539901) ∧
    -Real.log (62500000000 / 241261539901) ≤ (1350715017 / 1000000000) := by
  have h := checkLog_sound (w := (116261539901 / 366261539901)) (n := 12)
    (lo := (131513567 / 200000000)) (hi := (164391959 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((241261539901 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(241261539901 / 125000000000) = 1/(62500000000 / 241261539901) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (270143003 / 200000000) (1350715017 / 1000000000) (Real.log (241261539901 / 62500000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (241261539901 / 62500000000) = -Real.log (62500000000 / 241261539901) := by
    rw [show ((241261539901 / 62500000000) : ℝ) = ((62500000000 / 241261539901) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0034
