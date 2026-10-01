import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0050
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

theorem reflection_log_1_neg : (13581183 / 20000000) ≤ -Real.log (20480 / 40387) ∧
    -Real.log (20480 / 40387) ≤ (679059151 / 1000000000) := by
  have h := checkLog_sound (w := (19907 / 60867)) (n := 12)
    (lo := (13581183 / 20000000)) (hi := (679059151 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40387 / 20480) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40387 / 20480) = 1/(20480 / 40387) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (13581183 / 20000000) (679059151 / 1000000000) (Real.log (40387 / 20480)) := by
  have h := reflection_log_1_neg
  have he : Real.log (40387 / 20480) = -Real.log (20480 / 40387) := by
    rw [show ((40387 / 20480) : ℝ) = ((20480 / 40387) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (3576318359 / 1000000000) ≤ -Real.log (573 / 20480) ∧
    -Real.log (573 / 20480) ≤ (715263673 / 200000000) := by
  have h := checkLog_sound (w := (67 / 1213)) (n := 12)
    (lo := (110582459 / 1000000000)) (hi := (5529123 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 573) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(640 / 573) = 1/(573 / 20480) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-715263673 / 200000000) (-3576318359 / 1000000000) (Real.log (573 / 20480)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (10608829 / 15625000) ≤ -Real.log (25600 / 50479) ∧
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


theorem reflection_log_3 : Bounds (10608829 / 15625000) (678965057 / 1000000000) (Real.log (50479 / 25600)) := by
  have h := reflection_log_3_neg
  have he : Real.log (50479 / 25600) = -Real.log (25600 / 50479) := by
    rw [show ((50479 / 25600) : ℝ) = ((25600 / 50479) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (356970849 / 100000000) ≤ -Real.log (721 / 25600) ∧
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


theorem reflection_log_4 : Bounds (-223106781 / 62500000) (-356970849 / 100000000) (Real.log (721 / 25600)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (664769809 / 1000000000) ≤ -Real.log (10240 / 19907) ∧
    -Real.log (10240 / 19907) ≤ (66476981 / 100000000) := by
  have h := checkLog_sound (w := (9667 / 30147)) (n := 12)
    (lo := (664769809 / 1000000000)) (hi := (66476981 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((19907 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(19907 / 10240) = 1/(10240 / 19907) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (664769809 / 1000000000) (66476981 / 100000000) (Real.log (19907 / 10240)) := by
  have h := reflection_log_5_neg
  have he : Real.log (19907 / 10240) = -Real.log (10240 / 19907) := by
    rw [show ((19907 / 10240) : ℝ) = ((10240 / 19907) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (2883171179 / 1000000000) ≤ -Real.log (573 / 10240) ∧
    -Real.log (573 / 10240) ≤ (180198199 / 62500000) := by
  have h := checkLog_sound (w := (67 / 1213)) (n := 12)
    (lo := (110582459 / 1000000000)) (hi := (5529123 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 573) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(640 / 573) = 1/(573 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-180198199 / 62500000) (-2883171179 / 1000000000) (Real.log (573 / 10240)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (664578903 / 1000000000) ≤ -Real.log (12800 / 24879) ∧
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


theorem reflection_log_7 : Bounds (664578903 / 1000000000) (83072363 / 125000000) (Real.log (24879 / 12800)) := by
  have h := reflection_log_7_neg
  have he : Real.log (24879 / 12800) = -Real.log (12800 / 24879) := by
    rw [show ((24879 / 12800) : ℝ) = ((12800 / 24879) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (287656131 / 100000000) ≤ -Real.log (721 / 12800) ∧
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


theorem reflection_log_8 : Bounds (-575312263 / 200000000) (-287656131 / 100000000) (Real.log (721 / 12800)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (340634709 / 500000000) ≤ -Real.log (200000 / 395277) ∧
    -Real.log (200000 / 395277) ≤ (681269419 / 1000000000) := by
  have h := checkLog_sound (w := (195277 / 595277)) (n := 12)
    (lo := (340634709 / 500000000)) (hi := (681269419 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((395277 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(395277 / 200000) = 1/(200000 / 395277) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (340634709 / 500000000) (681269419 / 1000000000) (Real.log (395277 / 200000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (395277 / 200000) = -Real.log (200000 / 395277) := by
    rw [show ((395277 / 200000) : ℝ) = ((200000 / 395277) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (936468293 / 250000000) ≤ -Real.log (4723 / 200000) ∧
    -Real.log (4723 / 200000) ≤ (1872936589 / 500000000) := by
  have h := checkLog_sound (w := (1527 / 10973)) (n := 12)
    (lo := (35017159 / 125000000)) (hi := (280137273 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6250 / 4723) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(6250 / 4723) = 1/(4723 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-1872936589 / 500000000) (-936468293 / 250000000) (Real.log (4723 / 200000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (136268961 / 200000000) ≤ -Real.log (500000 / 988267) ∧
    -Real.log (500000 / 988267) ≤ (340672403 / 500000000) := by
  have h := checkLog_sound (w := (488267 / 1488267)) (n := 12)
    (lo := (136268961 / 200000000)) (hi := (340672403 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((988267 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(988267 / 500000) = 1/(500000 / 988267) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (136268961 / 200000000) (340672403 / 500000000) (Real.log (988267 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (988267 / 500000) = -Real.log (500000 / 988267) := by
    rw [show ((988267 / 500000) : ℝ) = ((500000 / 988267) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (3752202711 / 1000000000) ≤ -Real.log (11733 / 500000) ∧
    -Real.log (11733 / 500000) ≤ (3752202717 / 1000000000) := by
  have h := checkLog_sound (w := (1946 / 13679)) (n := 12)
    (lo := (286466811 / 1000000000)) (hi := (71616703 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 11733) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 11733) = 1/(11733 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-3752202717 / 1000000000) (-3752202711 / 1000000000) (Real.log (11733 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (681202627 / 1000000000) ≤ -Real.log (1000000 / 1976253) ∧
    -Real.log (1000000 / 1976253) ≤ (170300657 / 250000000) := by
  have h := checkLog_sound (w := (976253 / 2976253)) (n := 12)
    (lo := (681202627 / 1000000000)) (hi := (170300657 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1976253 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1976253 / 1000000) = 1/(1000000 / 1976253) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (681202627 / 1000000000) (170300657 / 250000000) (Real.log (1976253 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1976253 / 1000000) = -Real.log (1000000 / 1976253) := by
    rw [show ((1976253 / 1000000) : ℝ) = ((1000000 / 1976253) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (3740299069 / 1000000000) ≤ -Real.log (23747 / 1000000) ∧
    -Real.log (23747 / 1000000) ≤ (149611963 / 40000000) := by
  have h := checkLog_sound (w := (7503 / 54997)) (n := 12)
    (lo := (274563169 / 1000000000)) (hi := (27456317 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 23747) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 23747) = 1/(23747 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-149611963 / 40000000) (-3740299069 / 1000000000) (Real.log (23747 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (681279031 / 1000000000) ≤ -Real.log (250000 / 494101) ∧
    -Real.log (250000 / 494101) ≤ (85159879 / 125000000) := by
  have h := checkLog_sound (w := (244101 / 744101)) (n := 12)
    (lo := (681279031 / 1000000000)) (hi := (85159879 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((494101 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(494101 / 250000) = 1/(250000 / 494101) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (681279031 / 1000000000) (85159879 / 125000000) (Real.log (494101 / 250000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (494101 / 250000) = -Real.log (250000 / 494101) := by
    rw [show ((494101 / 250000) : ℝ) = ((250000 / 494101) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (374667807 / 100000000) ≤ -Real.log (5899 / 250000) ∧
    -Real.log (5899 / 250000) ≤ (936669519 / 250000000) := by
  have h := checkLog_sound (w := (3827 / 27423)) (n := 12)
    (lo := (28094217 / 100000000)) (hi := (280942171 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 11798) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 11798) = 1/(5899 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-936669519 / 250000000) (-374667807 / 100000000) (Real.log (5899 / 250000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (442714259 / 100000000) ≤ -Real.log (250000000000 / 20922983273343) ∧
    -Real.log (250000000000 / 20922983273343) ≤ (4427142597 / 1000000000) := by
  have h := checkLog_sound (w := (4922983273343 / 36922983273343)) (n := 12)
    (lo := (26825951 / 100000000)) (hi := (268259511 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20922983273343 / 16000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(20922983273343 / 16000000000000) = 1/(250000000000 / 20922983273343) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (442714259 / 100000000) (4427142597 / 1000000000) (Real.log (20922983273343 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (20922983273343 / 250000000000) = -Real.log (250000000000 / 20922983273343) := by
    rw [show ((20922983273343 / 250000000000) : ℝ) = ((250000000000 / 20922983273343) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1108386879 / 250000000) ≤ -Real.log (5000000000 / 421148470127) ∧
    -Real.log (5000000000 / 421148470127) ≤ (4433547523 / 1000000000) := by
  have h := checkLog_sound (w := (101148470127 / 741148470127)) (n := 12)
    (lo := (68666109 / 250000000)) (hi := (274664437 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((421148470127 / 320000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(421148470127 / 320000000000) = 1/(5000000000 / 421148470127) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1108386879 / 250000000) (4433547523 / 1000000000) (Real.log (421148470127 / 5000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (421148470127 / 5000000000) = -Real.log (5000000000 / 421148470127) := by
    rw [show ((421148470127 / 5000000000) : ℝ) = ((5000000000 / 421148470127) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (17271491 / 3906250) ≤ -Real.log (250000000000 / 20805291194677) ∧
    -Real.log (250000000000 / 20805291194677) ≤ (4421501703 / 1000000000) := by
  have h := checkLog_sound (w := (4805291194677 / 36805291194677)) (n := 12)
    (lo := (32827327 / 125000000)) (hi := (262618617 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20805291194677 / 16000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(20805291194677 / 16000000000000) = 1/(250000000000 / 20805291194677) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (17271491 / 3906250) (4421501703 / 1000000000) (Real.log (20805291194677 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (20805291194677 / 250000000000) = -Real.log (250000000000 / 20805291194677) := by
    rw [show ((20805291194677 / 250000000000) : ℝ) = ((250000000000 / 20805291194677) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (4427957101 / 1000000000) ≤ -Real.log (250000000000 / 20940032208849) ∧
    -Real.log (250000000000 / 20940032208849) ≤ (1106989277 / 250000000) := by
  have h := checkLog_sound (w := (4940032208849 / 36940032208849)) (n := 12)
    (lo := (269074021 / 1000000000)) (hi := (134537011 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20940032208849 / 16000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(20940032208849 / 16000000000000) = 1/(250000000000 / 20940032208849) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (4427957101 / 1000000000) (1106989277 / 250000000) (Real.log (20940032208849 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (20940032208849 / 250000000000) = -Real.log (250000000000 / 20940032208849) := by
    rw [show ((20940032208849 / 250000000000) : ℝ) = ((250000000000 / 20940032208849) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0050
