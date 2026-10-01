import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0050
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

theorem reflection_log_1_neg : (46815317 / 125000000) ≤ -Real.log (2560 / 3723) ∧
    -Real.log (2560 / 3723) ≤ (374522537 / 1000000000) := by
  have h := checkLog_sound (w := (1163 / 6283)) (n := 12)
    (lo := (46815317 / 125000000)) (hi := (374522537 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3723 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3723 / 2560) = 1/(2560 / 3723) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (46815317 / 125000000) (374522537 / 1000000000) (Real.log (3723 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3723 / 2560) = -Real.log (2560 / 3723) := by
    rw [show ((3723 / 2560) : ℝ) = ((2560 / 3723) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (302840089 / 500000000) ≤ -Real.log (1397 / 2560) ∧
    -Real.log (1397 / 2560) ≤ (605680179 / 1000000000) := by
  have h := checkLog_sound (w := (1163 / 3957)) (n := 12)
    (lo := (302840089 / 500000000)) (hi := (605680179 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1397) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1397) = 1/(1397 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-605680179 / 1000000000) (-302840089 / 500000000) (Real.log (1397 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (373716409 / 1000000000) ≤ -Real.log (64 / 93) ∧
    -Real.log (64 / 93) ≤ (37371641 / 100000000) := by
  have h := checkLog_sound (w := (29 / 157)) (n := 12)
    (lo := (373716409 / 1000000000)) (hi := (37371641 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((93 / 64) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(93 / 64) = 1/(64 / 93) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (373716409 / 1000000000) (37371641 / 100000000) (Real.log (93 / 64)) := by
  have h := reflection_log_3_neg
  have he : Real.log (93 / 64) = -Real.log (64 / 93) := by
    rw [show ((93 / 64) : ℝ) = ((64 / 93) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (603535021 / 1000000000) ≤ -Real.log (35 / 64) ∧
    -Real.log (35 / 64) ≤ (301767511 / 500000000) := by
  have h := checkLog_sound (w := (29 / 99)) (n := 12)
    (lo := (603535021 / 1000000000)) (hi := (301767511 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((64 / 35) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(64 / 35) = 1/(35 / 64) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-301767511 / 500000000) (-603535021 / 1000000000) (Real.log (35 / 64)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (323183357 / 500000000) ≤ -Real.log (1280 / 2443) ∧
    -Real.log (1280 / 2443) ≤ (129273343 / 200000000) := by
  have h := checkLog_sound (w := (1163 / 3723)) (n := 12)
    (lo := (323183357 / 500000000)) (hi := (129273343 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2443 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2443 / 1280) = 1/(1280 / 2443) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (323183357 / 500000000) (129273343 / 200000000) (Real.log (2443 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2443 / 1280) = -Real.log (1280 / 2443) := by
    rw [show ((2443 / 1280) : ℝ) = ((1280 / 2443) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (119622071 / 50000000) ≤ -Real.log (117 / 1280) ∧
    -Real.log (117 / 1280) ≤ (149527589 / 62500000) := by
  have h := checkLog_sound (w := (43 / 277)) (n := 12)
    (lo := (7824997 / 25000000)) (hi := (312999881 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 117) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(160 / 117) = 1/(117 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-149527589 / 62500000) (-119622071 / 50000000) (Real.log (117 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (645137961 / 1000000000) ≤ -Real.log (32 / 61) ∧
    -Real.log (32 / 61) ≤ (322568981 / 500000000) := by
  have h := checkLog_sound (w := (29 / 93)) (n := 12)
    (lo := (645137961 / 1000000000)) (hi := (322568981 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((61 / 32) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(61 / 32) = 1/(32 / 61) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (645137961 / 1000000000) (322568981 / 500000000) (Real.log (61 / 32)) := by
  have h := reflection_log_7_neg
  have he : Real.log (61 / 32) = -Real.log (32 / 61) := by
    rw [show ((61 / 32) : ℝ) = ((32 / 61) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (591780903 / 250000000) ≤ -Real.log (3 / 32) ∧
    -Real.log (3 / 32) ≤ (73972613 / 31250000) := by
  have h := checkLog_sound (w := (1 / 7)) (n := 12)
    (lo := (35960259 / 125000000)) (hi := (287682073 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4 / 3) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(4 / 3) = 1/(3 / 32) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-73972613 / 31250000) (-591780903 / 250000000) (Real.log (3 / 32)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (103541617 / 200000000) ≤ -Real.log (1000000 / 1678177) ∧
    -Real.log (1000000 / 1678177) ≤ (258854043 / 500000000) := by
  have h := checkLog_sound (w := (678177 / 2678177)) (n := 12)
    (lo := (103541617 / 200000000)) (hi := (258854043 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1678177 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1678177 / 1000000) = 1/(1000000 / 1678177) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (103541617 / 200000000) (258854043 / 500000000) (Real.log (1678177 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1678177 / 1000000) = -Real.log (1000000 / 1678177) := by
    rw [show ((1678177 / 1000000) : ℝ) = ((1000000 / 1678177) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (1133753573 / 1000000000) ≤ -Real.log (321823 / 1000000) ∧
    -Real.log (321823 / 1000000) ≤ (45350143 / 40000000) := by
  have h := checkLog_sound (w := (178177 / 821823)) (n := 12)
    (lo := (440606393 / 1000000000)) (hi := (220303197 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 321823) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 321823) = 1/(321823 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-45350143 / 40000000) (-1133753573 / 1000000000) (Real.log (321823 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (518984251 / 1000000000) ≤ -Real.log (3125 / 5251) ∧
    -Real.log (3125 / 5251) ≤ (129746063 / 250000000) := by
  have h := checkLog_sound (w := (1063 / 4188)) (n := 12)
    (lo := (518984251 / 1000000000)) (hi := (129746063 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5251 / 3125) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5251 / 3125) = 1/(3125 / 5251) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (518984251 / 1000000000) (129746063 / 250000000) (Real.log (5251 / 3125)) := by
  have h := reflection_log_11_neg
  have he : Real.log (5251 / 3125) = -Real.log (3125 / 5251) := by
    rw [show ((5251 / 3125) : ℝ) = ((3125 / 5251) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (570217391 / 500000000) ≤ -Real.log (999 / 3125) ∧
    -Real.log (999 / 3125) ≤ (35638587 / 31250000) := by
  have h := checkLog_sound (w := (1127 / 5123)) (n := 12)
    (lo := (223643801 / 500000000)) (hi := (447287603 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3125 / 1998) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(3125 / 1998) = 1/(999 / 3125) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-35638587 / 31250000) (-570217391 / 500000000) (Real.log (999 / 3125)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (87461477 / 200000000) ≤ -Real.log (250000 / 387133) ∧
    -Real.log (250000 / 387133) ≤ (218653693 / 500000000) := by
  have h := checkLog_sound (w := (137133 / 637133)) (n := 12)
    (lo := (87461477 / 200000000)) (hi := (218653693 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((387133 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(387133 / 250000) = 1/(250000 / 387133) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (87461477 / 200000000) (218653693 / 500000000) (Real.log (387133 / 250000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (387133 / 250000) = -Real.log (250000 / 387133) := by
    rw [show ((387133 / 250000) : ℝ) = ((250000 / 387133) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (397625391 / 500000000) ≤ -Real.log (112867 / 250000) ∧
    -Real.log (112867 / 250000) ≤ (24851587 / 31250000) := by
  have h := checkLog_sound (w := (12133 / 237867)) (n := 12)
    (lo := (51051801 / 500000000)) (hi := (102103603 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 112867) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(125000 / 112867) = 1/(112867 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-24851587 / 31250000) (-397625391 / 500000000) (Real.log (112867 / 250000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (219369987 / 500000000) ≤ -Real.log (31250 / 48461) ∧
    -Real.log (31250 / 48461) ≤ (17549599 / 40000000) := by
  have h := checkLog_sound (w := (17211 / 79711)) (n := 12)
    (lo := (219369987 / 500000000)) (hi := (17549599 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((48461 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(48461 / 31250) = 1/(31250 / 48461) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (219369987 / 500000000) (17549599 / 40000000) (Real.log (48461 / 31250)) := by
  have h := reflection_log_15_neg
  have he : Real.log (48461 / 31250) = -Real.log (31250 / 48461) := by
    rw [show ((48461 / 31250) : ℝ) = ((31250 / 48461) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (200045051 / 250000000) ≤ -Real.log (14039 / 31250) ∧
    -Real.log (14039 / 31250) ≤ (400090103 / 500000000) := by
  have h := checkLog_sound (w := (793 / 14832)) (n := 12)
    (lo := (1672391 / 15625000)) (hi := (4281321 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 14039) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(15625 / 14039) = 1/(14039 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-400090103 / 500000000) (-200045051 / 250000000) (Real.log (14039 / 31250)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (825730829 / 500000000) ≤ -Real.log (500000000000 / 2607298111073) ∧
    -Real.log (500000000000 / 2607298111073) ≤ (1651461661 / 1000000000) := by
  have h := checkLog_sound (w := (607298111073 / 4607298111073)) (n := 12)
    (lo := (132583649 / 500000000)) (hi := (265167299 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2607298111073 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2607298111073 / 2000000000000) = 1/(500000000000 / 2607298111073) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (825730829 / 500000000) (1651461661 / 1000000000) (Real.log (2607298111073 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (2607298111073 / 500000000000) = -Real.log (500000000000 / 2607298111073) := by
    rw [show ((2607298111073 / 500000000000) : ℝ) = ((500000000000 / 2607298111073) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1659419033 / 1000000000) ≤ -Real.log (500000000000 / 2628128128129) ∧
    -Real.log (500000000000 / 2628128128129) ≤ (414854759 / 250000000) := by
  have h := checkLog_sound (w := (628128128129 / 4628128128129)) (n := 12)
    (lo := (273124673 / 1000000000)) (hi := (136562337 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2628128128129 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2628128128129 / 2000000000000) = 1/(500000000000 / 2628128128129) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1659419033 / 1000000000) (414854759 / 250000000) (Real.log (2628128128129 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (2628128128129 / 500000000000) = -Real.log (500000000000 / 2628128128129) := by
    rw [show ((2628128128129 / 500000000000) : ℝ) = ((500000000000 / 2628128128129) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (154069771 / 125000000) ≤ -Real.log (100000000000 / 342999282341) ∧
    -Real.log (100000000000 / 342999282341) ≤ (123255817 / 100000000) := by
  have h := checkLog_sound (w := (142999282341 / 542999282341)) (n := 12)
    (lo := (134852747 / 250000000)) (hi := (539410989 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((342999282341 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(342999282341 / 200000000000) = 1/(100000000000 / 342999282341) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (154069771 / 125000000) (123255817 / 100000000) (Real.log (342999282341 / 100000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (342999282341 / 100000000000) = -Real.log (100000000000 / 342999282341) := by
    rw [show ((342999282341 / 100000000000) : ℝ) = ((100000000000 / 342999282341) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (1238920179 / 1000000000) ≤ -Real.log (500000000000 / 1725942018663) ∧
    -Real.log (500000000000 / 1725942018663) ≤ (1238920181 / 1000000000) := by
  have h := checkLog_sound (w := (725942018663 / 2725942018663)) (n := 12)
    (lo := (545772999 / 1000000000)) (hi := (545773 / 1000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1725942018663 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1725942018663 / 1000000000000) = 1/(500000000000 / 1725942018663) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (1238920179 / 1000000000) (1238920181 / 1000000000) (Real.log (1725942018663 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1725942018663 / 500000000000) = -Real.log (500000000000 / 1725942018663) := by
    rw [show ((1725942018663 / 500000000000) : ℝ) = ((500000000000 / 1725942018663) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0050
