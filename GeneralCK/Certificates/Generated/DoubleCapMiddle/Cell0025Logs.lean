import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0025
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

theorem reflection_log_1_neg : (394467353 / 1000000000) ≤ -Real.log (1280 / 1899) ∧
    -Real.log (1280 / 1899) ≤ (197233677 / 500000000) := by
  have h := checkLog_sound (w := (619 / 3179)) (n := 12)
    (lo := (394467353 / 1000000000)) (hi := (197233677 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1899 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1899 / 1280) = 1/(1280 / 1899) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (394467353 / 1000000000) (197233677 / 500000000) (Real.log (1899 / 1280)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1899 / 1280) = -Real.log (1280 / 1899) := by
    rw [show ((1899 / 1280) : ℝ) = ((1280 / 1899) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (660861517 / 1000000000) ≤ -Real.log (661 / 1280) ∧
    -Real.log (661 / 1280) ≤ (330430759 / 500000000) := by
  have h := checkLog_sound (w := (619 / 1941)) (n := 12)
    (lo := (660861517 / 1000000000)) (hi := (330430759 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 661) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 661) = 1/(661 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-330430759 / 500000000) (-660861517 / 1000000000) (Real.log (661 / 1280)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (12302411 / 31250000) ≤ -Real.log (512 / 759) ∧
    -Real.log (512 / 759) ≤ (393677153 / 1000000000) := by
  have h := checkLog_sound (w := (247 / 1271)) (n := 12)
    (lo := (12302411 / 31250000)) (hi := (393677153 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((759 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(759 / 512) = 1/(512 / 759) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (12302411 / 31250000) (393677153 / 1000000000) (Real.log (759 / 512)) := by
  have h := reflection_log_3_neg
  have he : Real.log (759 / 512) = -Real.log (512 / 759) := by
    rw [show ((759 / 512) : ℝ) = ((512 / 759) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (658594799 / 1000000000) ≤ -Real.log (265 / 512) ∧
    -Real.log (265 / 512) ≤ (1646487 / 2500000) := by
  have h := checkLog_sound (w := (247 / 777)) (n := 12)
    (lo := (658594799 / 1000000000)) (hi := (1646487 / 2500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 265) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 265) = 1/(265 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-1646487 / 2500000) (-658594799 / 1000000000) (Real.log (265 / 512)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (676604857 / 1000000000) ≤ -Real.log (640 / 1259) ∧
    -Real.log (640 / 1259) ≤ (338302429 / 500000000) := by
  have h := checkLog_sound (w := (619 / 1899)) (n := 12)
    (lo := (676604857 / 1000000000)) (hi := (338302429 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1259 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1259 / 640) = 1/(640 / 1259) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (676604857 / 1000000000) (338302429 / 500000000) (Real.log (1259 / 640)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1259 / 640) = -Real.log (640 / 1259) := by
    rw [show ((1259 / 640) : ℝ) = ((640 / 1259) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (427118217 / 125000000) ≤ -Real.log (21 / 640) ∧
    -Real.log (21 / 640) ≤ (3416945741 / 1000000000) := by
  have h := checkLog_sound (w := (19 / 61)) (n := 12)
    (lo := (80544627 / 125000000)) (hi := (644357017 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40 / 21) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(40 / 21) = 1/(21 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-3416945741 / 1000000000) (-427118217 / 125000000) (Real.log (21 / 640)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (27016509 / 40000000) ≤ -Real.log (256 / 503) ∧
    -Real.log (256 / 503) ≤ (337706363 / 500000000) := by
  have h := checkLog_sound (w := (247 / 759)) (n := 12)
    (lo := (27016509 / 40000000)) (hi := (337706363 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((503 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(503 / 256) = 1/(256 / 503) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (27016509 / 40000000) (337706363 / 500000000) (Real.log (503 / 256)) := by
  have h := reflection_log_7_neg
  have he : Real.log (503 / 256) = -Real.log (256 / 503) := by
    rw [show ((503 / 256) : ℝ) = ((256 / 503) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (104623527 / 31250000) ≤ -Real.log (9 / 256) ∧
    -Real.log (9 / 256) ≤ (3347952869 / 1000000000) := by
  have h := checkLog_sound (w := (7 / 25)) (n := 12)
    (lo := (35960259 / 62500000)) (hi := (115072829 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((16 / 9) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(16 / 9) = 1/(9 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-3347952869 / 1000000000) (-104623527 / 31250000) (Real.log (9 / 256)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (137799111 / 250000000) ≤ -Real.log (31250 / 54229) ∧
    -Real.log (31250 / 54229) ≤ (110239289 / 200000000) := by
  have h := checkLog_sound (w := (22979 / 85479)) (n := 12)
    (lo := (137799111 / 250000000)) (hi := (110239289 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((54229 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(54229 / 31250) = 1/(31250 / 54229) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (137799111 / 250000000) (110239289 / 200000000) (Real.log (54229 / 31250)) := by
  have h := reflection_log_9_neg
  have he : Real.log (54229 / 31250) = -Real.log (31250 / 54229) := by
    rw [show ((54229 / 31250) : ℝ) = ((31250 / 54229) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (664631977 / 500000000) ≤ -Real.log (8271 / 31250) ∧
    -Real.log (8271 / 31250) ≤ (332315989 / 250000000) := by
  have h := checkLog_sound (w := (3677 / 11948)) (n := 12)
    (lo := (318058387 / 500000000)) (hi := (25444671 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 8271) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(15625 / 8271) = 1/(8271 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-332315989 / 250000000) (-664631977 / 500000000) (Real.log (8271 / 31250)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (138162323 / 250000000) ≤ -Real.log (1000000 / 1737851) ∧
    -Real.log (1000000 / 1737851) ≤ (552649293 / 1000000000) := by
  have h := checkLog_sound (w := (737851 / 2737851)) (n := 12)
    (lo := (138162323 / 250000000)) (hi := (552649293 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1737851 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1737851 / 1000000) = 1/(1000000 / 1737851) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (138162323 / 250000000) (552649293 / 1000000000) (Real.log (1737851 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1737851 / 1000000) = -Real.log (1000000 / 1737851) := by
    rw [show ((1737851 / 1000000) : ℝ) = ((1000000 / 1737851) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (669421117 / 500000000) ≤ -Real.log (262149 / 1000000) ∧
    -Real.log (262149 / 1000000) ≤ (334710559 / 250000000) := by
  have h := checkLog_sound (w := (237851 / 762149)) (n := 12)
    (lo := (322847527 / 500000000)) (hi := (129139011 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 262149) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 262149) = 1/(262149 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-334710559 / 250000000) (-669421117 / 500000000) (Real.log (262149 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (475923571 / 1000000000) ≤ -Real.log (2000 / 3219) ∧
    -Real.log (2000 / 3219) ≤ (118980893 / 250000000) := by
  have h := checkLog_sound (w := (1219 / 5219)) (n := 12)
    (lo := (475923571 / 1000000000)) (hi := (118980893 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3219 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3219 / 2000) = 1/(2000 / 3219) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (475923571 / 1000000000) (118980893 / 250000000) (Real.log (3219 / 2000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (3219 / 2000) = -Real.log (2000 / 3219) := by
    rw [show ((3219 / 2000) : ℝ) = ((2000 / 3219) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (940327309 / 1000000000) ≤ -Real.log (781 / 2000) ∧
    -Real.log (781 / 2000) ≤ (940327311 / 1000000000) := by
  have h := checkLog_sound (w := (219 / 1781)) (n := 12)
    (lo := (247180129 / 1000000000)) (hi := (24718013 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 781) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1000 / 781) = 1/(781 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-940327311 / 1000000000) (-940327309 / 1000000000) (Real.log (781 / 2000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (14926367 / 31250000) ≤ -Real.log (1000000 / 1612271) ∧
    -Real.log (1000000 / 1612271) ≤ (95528749 / 200000000) := by
  have h := checkLog_sound (w := (612271 / 2612271)) (n := 12)
    (lo := (14926367 / 31250000)) (hi := (95528749 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1612271 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1612271 / 1000000) = 1/(1000000 / 1612271) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (14926367 / 31250000) (95528749 / 200000000) (Real.log (1612271 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1612271 / 1000000) = -Real.log (1000000 / 1612271) := by
    rw [show ((1612271 / 1000000) : ℝ) = ((1000000 / 1612271) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (236862159 / 250000000) ≤ -Real.log (387729 / 1000000) ∧
    -Real.log (387729 / 1000000) ≤ (473724319 / 500000000) := by
  have h := checkLog_sound (w := (112271 / 887729)) (n := 12)
    (lo := (15893841 / 62500000)) (hi := (254301457 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 387729) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 387729) = 1/(387729 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-473724319 / 500000000) (-236862159 / 250000000) (Real.log (387729 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (940230199 / 500000000) ≤ -Real.log (125000000000 / 819565348809) ∧
    -Real.log (125000000000 / 819565348809) ≤ (1880460401 / 1000000000) := by
  have h := checkLog_sound (w := (319565348809 / 1319565348809)) (n := 12)
    (lo := (247083019 / 500000000)) (hi := (494166039 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((819565348809 / 500000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(819565348809 / 500000000000) = 1/(125000000000 / 819565348809) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (940230199 / 500000000) (1880460401 / 1000000000) (Real.log (819565348809 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (819565348809 / 125000000000) = -Real.log (125000000000 / 819565348809) := by
    rw [show ((819565348809 / 125000000000) : ℝ) = ((125000000000 / 819565348809) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (75659661 / 40000000) ≤ -Real.log (500000000000 / 3314624507437) ∧
    -Real.log (500000000000 / 3314624507437) ≤ (236436441 / 125000000) := by
  have h := checkLog_sound (w := (1314624507437 / 5314624507437)) (n := 12)
    (lo := (101039433 / 200000000)) (hi := (252598583 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3314624507437 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(3314624507437 / 2000000000000) = 1/(500000000000 / 3314624507437) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (75659661 / 40000000) (236436441 / 125000000) (Real.log (3314624507437 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (3314624507437 / 500000000000) = -Real.log (500000000000 / 3314624507437) := by
    rw [show ((3314624507437 / 500000000000) : ℝ) = ((500000000000 / 3314624507437) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (553223 / 390625) ≤ -Real.log (500000000000 / 2060819462227) ∧
    -Real.log (500000000000 / 2060819462227) ≤ (1416250883 / 1000000000) := by
  have h := checkLog_sound (w := (60819462227 / 4060819462227)) (n := 12)
    (lo := (748913 / 25000000)) (hi := (29956521 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2060819462227 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2060819462227 / 2000000000000) = 1/(500000000000 / 2060819462227) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (553223 / 390625) (1416250883 / 1000000000) (Real.log (2060819462227 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (2060819462227 / 500000000000) = -Real.log (500000000000 / 2060819462227) := by
    rw [show ((2060819462227 / 500000000000) : ℝ) = ((500000000000 / 2060819462227) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (1425092379 / 1000000000) ≤ -Real.log (500000000000 / 2079120983987) ∧
    -Real.log (500000000000 / 2079120983987) ≤ (712546191 / 500000000) := by
  have h := checkLog_sound (w := (79120983987 / 4079120983987)) (n := 12)
    (lo := (38798019 / 1000000000)) (hi := (1939901 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2079120983987 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2079120983987 / 2000000000000) = 1/(500000000000 / 2079120983987) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (1425092379 / 1000000000) (712546191 / 500000000) (Real.log (2079120983987 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (2079120983987 / 500000000000) = -Real.log (500000000000 / 2079120983987) := by
    rw [show ((2079120983987 / 500000000000) : ℝ) = ((500000000000 / 2079120983987) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0025
