import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0110
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

theorem reflection_log_1_neg : (13390213 / 20000000) ≤ -Real.log (6400 / 12501) ∧
    -Real.log (6400 / 12501) ≤ (669510651 / 1000000000) := by
  have h := checkLog_sound (w := (6101 / 18901)) (n := 12)
    (lo := (13390213 / 20000000)) (hi := (669510651 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12501 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12501 / 6400) = 1/(6400 / 12501) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (13390213 / 20000000) (669510651 / 1000000000) (Real.log (12501 / 6400)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12501 / 6400) = -Real.log (6400 / 12501) := by
    rw [show ((12501 / 6400) : ℝ) = ((6400 / 12501) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (3063609693 / 1000000000) ≤ -Real.log (299 / 6400) ∧
    -Real.log (299 / 6400) ≤ (1531804849 / 500000000) := by
  have h := checkLog_sound (w := (101 / 699)) (n := 12)
    (lo := (291020973 / 1000000000)) (hi := (145510487 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 299) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(400 / 299) = 1/(299 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-1531804849 / 500000000) (-3063609693 / 1000000000) (Real.log (299 / 6400)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (669320647 / 1000000000) ≤ -Real.log (51200 / 99989) ∧
    -Real.log (51200 / 99989) ≤ (83665081 / 125000000) := by
  have h := checkLog_sound (w := (48789 / 151189)) (n := 12)
    (lo := (669320647 / 1000000000)) (hi := (83665081 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((99989 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(99989 / 51200) = 1/(51200 / 99989) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (669320647 / 1000000000) (83665081 / 125000000) (Real.log (99989 / 51200)) := by
  have h := reflection_log_3_neg
  have he : Real.log (99989 / 51200) = -Real.log (51200 / 99989) := by
    rw [show ((99989 / 51200) : ℝ) = ((51200 / 99989) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (305569793 / 100000000) ≤ -Real.log (2411 / 51200) ∧
    -Real.log (2411 / 51200) ≤ (611139587 / 200000000) := by
  have h := checkLog_sound (w := (789 / 5611)) (n := 12)
    (lo := (28310921 / 100000000)) (hi := (283109211 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2411) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3200 / 2411) = 1/(2411 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-611139587 / 200000000) (-305569793 / 100000000) (Real.log (2411 / 51200)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (322650941 / 500000000) ≤ -Real.log (3200 / 6101) ∧
    -Real.log (3200 / 6101) ≤ (645301883 / 1000000000) := by
  have h := checkLog_sound (w := (2901 / 9301)) (n := 12)
    (lo := (322650941 / 500000000)) (hi := (645301883 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6101 / 3200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6101 / 3200) = 1/(3200 / 6101) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (322650941 / 500000000) (645301883 / 1000000000) (Real.log (6101 / 3200)) := by
  have h := reflection_log_5_neg
  have he : Real.log (6101 / 3200) = -Real.log (3200 / 6101) := by
    rw [show ((6101 / 3200) : ℝ) = ((3200 / 6101) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (2370462513 / 1000000000) ≤ -Real.log (299 / 3200) ∧
    -Real.log (299 / 3200) ≤ (2370462517 / 1000000000) := by
  have h := checkLog_sound (w := (101 / 699)) (n := 12)
    (lo := (291020973 / 1000000000)) (hi := (145510487 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 299) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(400 / 299) = 1/(299 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-2370462517 / 1000000000) (-2370462513 / 1000000000) (Real.log (299 / 3200)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (322456263 / 500000000) ≤ -Real.log (25600 / 48789) ∧
    -Real.log (25600 / 48789) ≤ (644912527 / 1000000000) := by
  have h := checkLog_sound (w := (23189 / 74389)) (n := 12)
    (lo := (322456263 / 500000000)) (hi := (644912527 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((48789 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(48789 / 25600) = 1/(25600 / 48789) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (322456263 / 500000000) (644912527 / 1000000000) (Real.log (48789 / 25600)) := by
  have h := reflection_log_7_neg
  have he : Real.log (48789 / 25600) = -Real.log (25600 / 48789) := by
    rw [show ((48789 / 25600) : ℝ) = ((25600 / 48789) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (9450203 / 4000000) ≤ -Real.log (2411 / 25600) ∧
    -Real.log (2411 / 25600) ≤ (1181275377 / 500000000) := by
  have h := checkLog_sound (w := (789 / 5611)) (n := 12)
    (lo := (28310921 / 100000000)) (hi := (283109211 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2411) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(3200 / 2411) = 1/(2411 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1181275377 / 500000000) (-9450203 / 4000000) (Real.log (2411 / 25600)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (84219421 / 125000000) ≤ -Real.log (100000 / 196159) ∧
    -Real.log (100000 / 196159) ≤ (673755369 / 1000000000) := by
  have h := checkLog_sound (w := (96159 / 296159)) (n := 12)
    (lo := (84219421 / 125000000)) (hi := (673755369 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((196159 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(196159 / 100000) = 1/(100000 / 196159) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (84219421 / 125000000) (673755369 / 1000000000) (Real.log (196159 / 100000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (196159 / 100000) = -Real.log (100000 / 196159) := by
    rw [show ((196159 / 100000) : ℝ) = ((100000 / 196159) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (1629718717 / 500000000) ≤ -Real.log (3841 / 100000) ∧
    -Real.log (3841 / 100000) ≤ (3259437439 / 1000000000) := by
  have h := checkLog_sound (w := (2409 / 10091)) (n := 12)
    (lo := (243424357 / 500000000)) (hi := (97369743 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6250 / 3841) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(6250 / 3841) = 1/(3841 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-3259437439 / 1000000000) (-1629718717 / 500000000) (Real.log (3841 / 100000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (84237581 / 125000000) ≤ -Real.log (1600 / 3139) ∧
    -Real.log (1600 / 3139) ≤ (673900649 / 1000000000) := by
  have h := checkLog_sound (w := (1539 / 4739)) (n := 12)
    (lo := (84237581 / 125000000)) (hi := (673900649 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3139 / 1600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3139 / 1600) = 1/(1600 / 3139) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (84237581 / 125000000) (673900649 / 1000000000) (Real.log (3139 / 1600)) := by
  have h := reflection_log_11_neg
  have he : Real.log (3139 / 1600) = -Real.log (1600 / 3139) := by
    rw [show ((3139 / 1600) : ℝ) = ((1600 / 3139) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (3266885041 / 1000000000) ≤ -Real.log (61 / 1600) ∧
    -Real.log (61 / 1600) ≤ (1633442523 / 500000000) := by
  have h := checkLog_sound (w := (39 / 161)) (n := 12)
    (lo := (494296321 / 1000000000)) (hi := (247148161 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100 / 61) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(100 / 61) = 1/(61 / 1600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1633442523 / 500000000) (-3266885041 / 1000000000) (Real.log (61 / 1600)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (673541743 / 1000000000) ≤ -Real.log (1000000 / 1961171) ∧
    -Real.log (1000000 / 1961171) ≤ (42096359 / 62500000) := by
  have h := checkLog_sound (w := (961171 / 2961171)) (n := 12)
    (lo := (673541743 / 1000000000)) (hi := (42096359 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1961171 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1961171 / 1000000) = 1/(1000000 / 1961171) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (673541743 / 1000000000) (42096359 / 62500000) (Real.log (1961171 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1961171 / 1000000) = -Real.log (1000000 / 1961171) := by
    rw [show ((1961171 / 1000000) : ℝ) = ((1000000 / 1961171) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (1624293943 / 500000000) ≤ -Real.log (38829 / 1000000) ∧
    -Real.log (38829 / 1000000) ≤ (3248587891 / 1000000000) := by
  have h := checkLog_sound (w := (23671 / 101329)) (n := 12)
    (lo := (237999583 / 500000000)) (hi := (475999167 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 38829) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 38829) = 1/(38829 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-3248587891 / 1000000000) (-1624293943 / 500000000) (Real.log (38829 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (673690623 / 1000000000) ≤ -Real.log (1000000 / 1961463) ∧
    -Real.log (1000000 / 1961463) ≤ (1315802 / 1953125) := by
  have h := checkLog_sound (w := (961463 / 2961463)) (n := 12)
    (lo := (673690623 / 1000000000)) (hi := (1315802 / 1953125))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1961463 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1961463 / 1000000) = 1/(1000000 / 1961463) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (673690623 / 1000000000) (1315802 / 1953125) (Real.log (1961463 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1961463 / 1000000) = -Real.log (1000000 / 1961463) := by
    rw [show ((1961463 / 1000000) : ℝ) = ((1000000 / 1961463) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (3256136457 / 1000000000) ≤ -Real.log (38537 / 1000000) ∧
    -Real.log (38537 / 1000000) ≤ (1628068231 / 500000000) := by
  have h := checkLog_sound (w := (23963 / 101037)) (n := 12)
    (lo := (483547737 / 1000000000)) (hi := (241773869 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 38537) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 38537) = 1/(38537 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-1628068231 / 500000000) (-3256136457 / 1000000000) (Real.log (38537 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1966596401 / 500000000) ≤ -Real.log (250000000000 / 12767443374121) ∧
    -Real.log (250000000000 / 12767443374121) ≤ (491649101 / 125000000) := by
  have h := checkLog_sound (w := (4767443374121 / 20767443374121)) (n := 12)
    (lo := (233728451 / 500000000)) (hi := (467456903 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12767443374121 / 8000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(12767443374121 / 8000000000000) = 1/(250000000000 / 12767443374121) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1966596401 / 500000000) (491649101 / 125000000) (Real.log (12767443374121 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (12767443374121 / 250000000000) = -Real.log (250000000000 / 12767443374121) := by
    rw [show ((12767443374121 / 250000000000) : ℝ) = ((250000000000 / 12767443374121) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (3940785689 / 1000000000) ≤ -Real.log (250000000000 / 12864754098361) ∧
    -Real.log (250000000000 / 12864754098361) ≤ (788157139 / 200000000) := by
  have h := checkLog_sound (w := (4864754098361 / 20864754098361)) (n := 12)
    (lo := (475049789 / 1000000000)) (hi := (47504979 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12864754098361 / 8000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(12864754098361 / 8000000000000) = 1/(250000000000 / 12864754098361) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (3940785689 / 1000000000) (788157139 / 200000000) (Real.log (12864754098361 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (12864754098361 / 250000000000) = -Real.log (250000000000 / 12864754098361) := by
    rw [show ((12864754098361 / 250000000000) : ℝ) = ((250000000000 / 12864754098361) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (3922129629 / 1000000000) ≤ -Real.log (100000000000 / 5050789358469) ∧
    -Real.log (100000000000 / 5050789358469) ≤ (784425927 / 200000000) := by
  have h := checkLog_sound (w := (1850789358469 / 8250789358469)) (n := 12)
    (lo := (456393729 / 1000000000)) (hi := (45639373 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5050789358469 / 3200000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(5050789358469 / 3200000000000) = 1/(100000000000 / 5050789358469) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (3922129629 / 1000000000) (784425927 / 200000000) (Real.log (5050789358469 / 100000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (5050789358469 / 100000000000) = -Real.log (100000000000 / 5050789358469) := by
    rw [show ((5050789358469 / 100000000000) : ℝ) = ((100000000000 / 5050789358469) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (98245677 / 25000000) ≤ -Real.log (500000000000 / 25449087889561) ∧
    -Real.log (500000000000 / 25449087889561) ≤ (1964913543 / 500000000) := by
  have h := checkLog_sound (w := (9449087889561 / 41449087889561)) (n := 12)
    (lo := (23204559 / 50000000)) (hi := (464091181 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25449087889561 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(25449087889561 / 16000000000000) = 1/(500000000000 / 25449087889561) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (98245677 / 25000000) (1964913543 / 500000000) (Real.log (25449087889561 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (25449087889561 / 500000000000) = -Real.log (500000000000 / 25449087889561) := by
    rw [show ((25449087889561 / 500000000000) : ℝ) = ((500000000000 / 25449087889561) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0110
