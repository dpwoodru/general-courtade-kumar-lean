import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0051
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

theorem reflection_log_1_neg : (10608829 / 15625000) ≤ -Real.log (25600 / 50479) ∧
    -Real.log (25600 / 50479) ≤ (678965057 / 1000000000) := by
  have h := checkLog_sound (w := (24879 / 76079)) (n := 12)
    (lo := (10608829 / 15625000)) (hi := (678965057 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50479 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50479 / 25600) = 1/(25600 / 50479) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (10608829 / 15625000) (678965057 / 1000000000) (Real.log (50479 / 25600)) := by
  have h := reflection_log_1_neg
  have he : Real.log (50479 / 25600) = -Real.log (25600 / 50479) := by
    rw [show ((50479 / 25600) : ℝ) = ((25600 / 50479) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (356970849 / 100000000) ≤ -Real.log (721 / 25600) ∧
    -Real.log (721 / 25600) ≤ (223106781 / 62500000) := by
  have h := checkLog_sound (w := (79 / 1521)) (n := 12)
    (lo := (10397259 / 100000000)) (hi := (103972591 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 721) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(800 / 721) = 1/(721 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-223106781 / 62500000) (-356970849 / 100000000) (Real.log (721 / 25600)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (678870953 / 1000000000) ≤ -Real.log (102400 / 201897) ∧
    -Real.log (102400 / 201897) ≤ (339435477 / 500000000) := by
  have h := checkLog_sound (w := (99497 / 304297)) (n := 12)
    (lo := (678870953 / 1000000000)) (hi := (339435477 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((201897 / 102400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(201897 / 102400) = 1/(102400 / 201897) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (678870953 / 1000000000) (339435477 / 500000000) (Real.log (201897 / 102400)) := by
  have h := reflection_log_3_neg
  have he : Real.log (201897 / 102400) = -Real.log (102400 / 201897) := by
    rw [show ((201897 / 102400) : ℝ) = ((102400 / 201897) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (445392753 / 125000000) ≤ -Real.log (2903 / 102400) ∧
    -Real.log (2903 / 102400) ≤ (356314203 / 100000000) := by
  have h := checkLog_sound (w := (297 / 6103)) (n := 12)
    (lo := (24351531 / 250000000)) (hi := (779249 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2903) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3200 / 2903) = 1/(2903 / 102400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-356314203 / 100000000) (-445392753 / 125000000) (Real.log (2903 / 102400)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (664578903 / 1000000000) ≤ -Real.log (12800 / 24879) ∧
    -Real.log (12800 / 24879) ≤ (83072363 / 125000000) := by
  have h := checkLog_sound (w := (12079 / 37679)) (n := 12)
    (lo := (664578903 / 1000000000)) (hi := (83072363 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24879 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24879 / 12800) = 1/(12800 / 24879) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (664578903 / 1000000000) (83072363 / 125000000) (Real.log (24879 / 12800)) := by
  have h := reflection_log_5_neg
  have he : Real.log (24879 / 12800) = -Real.log (12800 / 24879) := by
    rw [show ((24879 / 12800) : ℝ) = ((12800 / 24879) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (287656131 / 100000000) ≤ -Real.log (721 / 12800) ∧
    -Real.log (721 / 12800) ≤ (575312263 / 200000000) := by
  have h := checkLog_sound (w := (79 / 1521)) (n := 12)
    (lo := (10397259 / 100000000)) (hi := (103972591 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 721) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(800 / 721) = 1/(721 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-575312263 / 200000000) (-287656131 / 100000000) (Real.log (721 / 12800)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (16609699 / 25000000) ≤ -Real.log (51200 / 99497) ∧
    -Real.log (51200 / 99497) ≤ (664387961 / 1000000000) := by
  have h := checkLog_sound (w := (48297 / 150697)) (n := 12)
    (lo := (16609699 / 25000000)) (hi := (664387961 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((99497 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(99497 / 51200) = 1/(51200 / 99497) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (16609699 / 25000000) (664387961 / 1000000000) (Real.log (99497 / 51200)) := by
  have h := reflection_log_7_neg
  have he : Real.log (99497 / 51200) = -Real.log (51200 / 99497) := by
    rw [show ((99497 / 51200) : ℝ) = ((51200 / 99497) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (717498711 / 250000000) ≤ -Real.log (2903 / 51200) ∧
    -Real.log (2903 / 51200) ≤ (2869994849 / 1000000000) := by
  have h := checkLog_sound (w := (297 / 6103)) (n := 12)
    (lo := (24351531 / 250000000)) (hi := (779249 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2903) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3200 / 2903) = 1/(2903 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-2869994849 / 1000000000) (-717498711 / 250000000) (Real.log (2903 / 51200)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (27247761 / 40000000) ≤ -Real.log (250000 / 494059) ∧
    -Real.log (250000 / 494059) ≤ (340597013 / 500000000) := by
  have h := checkLog_sound (w := (244059 / 744059)) (n := 12)
    (lo := (27247761 / 40000000)) (hi := (340597013 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((494059 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(494059 / 250000) = 1/(250000 / 494059) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (27247761 / 40000000) (340597013 / 500000000) (Real.log (494059 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (494059 / 250000) = -Real.log (250000 / 494059) := by
    rw [show ((494059 / 250000) : ℝ) = ((250000 / 494059) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (747916689 / 200000000) ≤ -Real.log (5941 / 250000) ∧
    -Real.log (5941 / 250000) ≤ (3739583451 / 1000000000) := by
  have h := checkLog_sound (w := (3743 / 27507)) (n := 12)
    (lo := (54769509 / 200000000)) (hi := (136923773 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 11882) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 11882) = 1/(5941 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-3739583451 / 1000000000) (-747916689 / 200000000) (Real.log (5941 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (170317481 / 250000000) ≤ -Real.log (500000 / 988193) ∧
    -Real.log (500000 / 988193) ≤ (27250797 / 40000000) := by
  have h := checkLog_sound (w := (488193 / 1488193)) (n := 12)
    (lo := (170317481 / 250000000)) (hi := (27250797 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((988193 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(988193 / 500000) = 1/(500000 / 988193) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (170317481 / 250000000) (27250797 / 40000000) (Real.log (988193 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (988193 / 500000) = -Real.log (500000 / 988193) := by
    rw [show ((988193 / 500000) : ℝ) = ((500000 / 988193) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (3745915519 / 1000000000) ≤ -Real.log (11807 / 500000) ∧
    -Real.log (11807 / 500000) ≤ (149836621 / 40000000) := by
  have h := checkLog_sound (w := (1909 / 13716)) (n := 12)
    (lo := (280179619 / 1000000000)) (hi := (14008981 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 11807) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 11807) = 1/(11807 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-149836621 / 40000000) (-3745915519 / 1000000000) (Real.log (11807 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (681126723 / 1000000000) ≤ -Real.log (1000000 / 1976103) ∧
    -Real.log (1000000 / 1976103) ≤ (170281681 / 250000000) := by
  have h := checkLog_sound (w := (976103 / 2976103)) (n := 12)
    (lo := (681126723 / 1000000000)) (hi := (170281681 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1976103 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1976103 / 1000000) = 1/(1000000 / 1976103) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (681126723 / 1000000000) (170281681 / 250000000) (Real.log (1976103 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1976103 / 1000000) = -Real.log (1000000 / 1976103) := by
    rw [show ((1976103 / 1000000) : ℝ) = ((1000000 / 1976103) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (933500587 / 250000000) ≤ -Real.log (23897 / 1000000) ∧
    -Real.log (23897 / 1000000) ≤ (1867001177 / 500000000) := by
  have h := checkLog_sound (w := (7353 / 55147)) (n := 12)
    (lo := (16766653 / 62500000)) (hi := (268266449 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 23897) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 23897) = 1/(23897 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-1867001177 / 500000000) (-933500587 / 250000000) (Real.log (23897 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (681203133 / 1000000000) ≤ -Real.log (500000 / 988127) ∧
    -Real.log (500000 / 988127) ≤ (340601567 / 500000000) := by
  have h := checkLog_sound (w := (488127 / 1488127)) (n := 12)
    (lo := (681203133 / 1000000000)) (hi := (340601567 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((988127 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(988127 / 500000) = 1/(500000 / 988127) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (681203133 / 1000000000) (340601567 / 500000000) (Real.log (988127 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (988127 / 500000) = -Real.log (500000 / 988127) := by
    rw [show ((988127 / 500000) : ℝ) = ((500000 / 988127) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (187017059 / 50000000) ≤ -Real.log (11873 / 500000) ∧
    -Real.log (11873 / 500000) ≤ (1870170593 / 500000000) := by
  have h := checkLog_sound (w := (1876 / 13749)) (n := 12)
    (lo := (1716283 / 6250000)) (hi := (274605281 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 11873) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 11873) = 1/(11873 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-1870170593 / 500000000) (-187017059 / 50000000) (Real.log (11873 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (442077747 / 100000000) ≤ -Real.log (500000000000 / 41580457835381) ∧
    -Real.log (500000000000 / 41580457835381) ≤ (4420777477 / 1000000000) := by
  have h := checkLog_sound (w := (9580457835381 / 73580457835381)) (n := 12)
    (lo := (26189439 / 100000000)) (hi := (261894391 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((41580457835381 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(41580457835381 / 32000000000000) = 1/(500000000000 / 41580457835381) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (442077747 / 100000000) (4420777477 / 1000000000) (Real.log (41580457835381 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (41580457835381 / 500000000000) = -Real.log (500000000000 / 41580457835381) := by
    rw [show ((41580457835381 / 500000000000) : ℝ) = ((500000000000 / 41580457835381) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (4427185443 / 1000000000) ≤ -Real.log (500000000000 / 41847759803507) ∧
    -Real.log (500000000000 / 41847759803507) ≤ (88543709 / 20000000) := by
  have h := checkLog_sound (w := (9847759803507 / 73847759803507)) (n := 12)
    (lo := (268302363 / 1000000000)) (hi := (67075591 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((41847759803507 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(41847759803507 / 32000000000000) = 1/(500000000000 / 41847759803507) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (4427185443 / 1000000000) (88543709 / 20000000) (Real.log (41847759803507 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (41847759803507 / 500000000000) = -Real.log (500000000000 / 41847759803507) := by
    rw [show ((41847759803507 / 500000000000) : ℝ) = ((500000000000 / 41847759803507) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (4415129071 / 1000000000) ≤ -Real.log (125000000000 / 10336564213081) ∧
    -Real.log (125000000000 / 10336564213081) ≤ (2207564539 / 500000000) := by
  have h := checkLog_sound (w := (2336564213081 / 18336564213081)) (n := 12)
    (lo := (256245991 / 1000000000)) (hi := (32030749 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10336564213081 / 8000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(10336564213081 / 8000000000000) = 1/(125000000000 / 10336564213081) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (4415129071 / 1000000000) (2207564539 / 500000000) (Real.log (10336564213081 / 125000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (10336564213081 / 125000000000) = -Real.log (125000000000 / 10336564213081) := by
    rw [show ((10336564213081 / 125000000000) : ℝ) = ((125000000000 / 10336564213081) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (4421544313 / 1000000000) ≤ -Real.log (250000000000 / 20806177882591) ∧
    -Real.log (250000000000 / 20806177882591) ≤ (6908663 / 1562500) := by
  have h := checkLog_sound (w := (4806177882591 / 36806177882591)) (n := 12)
    (lo := (262661233 / 1000000000)) (hi := (131330617 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20806177882591 / 16000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(20806177882591 / 16000000000000) = 1/(250000000000 / 20806177882591) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (4421544313 / 1000000000) (6908663 / 1562500) (Real.log (20806177882591 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (20806177882591 / 250000000000) = -Real.log (250000000000 / 20806177882591) := by
    rw [show ((20806177882591 / 250000000000) : ℝ) = ((250000000000 / 20806177882591) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0051
