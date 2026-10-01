import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0111
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

theorem reflection_log_1_neg : (669320647 / 1000000000) ≤ -Real.log (51200 / 99989) ∧
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


theorem reflection_log_1 : Bounds (669320647 / 1000000000) (83665081 / 125000000) (Real.log (99989 / 51200)) := by
  have h := reflection_log_1_neg
  have he : Real.log (99989 / 51200) = -Real.log (51200 / 99989) := by
    rw [show ((99989 / 51200) : ℝ) = ((51200 / 99989) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (305569793 / 100000000) ≤ -Real.log (2411 / 51200) ∧
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


theorem reflection_log_2 : Bounds (-611139587 / 200000000) (-305569793 / 100000000) (Real.log (2411 / 51200)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (41820663 / 62500000) ≤ -Real.log (5120 / 9997) ∧
    -Real.log (5120 / 9997) ≤ (669130609 / 1000000000) := by
  have h := checkLog_sound (w := (4877 / 15117)) (n := 12)
    (lo := (41820663 / 62500000)) (hi := (669130609 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9997 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(9997 / 5120) = 1/(5120 / 9997) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (41820663 / 62500000) (669130609 / 1000000000) (Real.log (9997 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (9997 / 5120) = -Real.log (5120 / 9997) := by
    rw [show ((9997 / 5120) : ℝ) = ((5120 / 9997) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (190490517 / 62500000) ≤ -Real.log (243 / 5120) ∧
    -Real.log (243 / 5120) ≤ (3047848277 / 1000000000) := by
  have h := checkLog_sound (w := (77 / 563)) (n := 12)
    (lo := (8601861 / 31250000)) (hi := (275259553 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 243) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(320 / 243) = 1/(243 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-3047848277 / 1000000000) (-190490517 / 62500000) (Real.log (243 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (322456263 / 500000000) ≤ -Real.log (25600 / 48789) ∧
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


theorem reflection_log_5 : Bounds (322456263 / 500000000) (644912527 / 1000000000) (Real.log (48789 / 25600)) := by
  have h := reflection_log_5_neg
  have he : Real.log (48789 / 25600) = -Real.log (25600 / 48789) := by
    rw [show ((48789 / 25600) : ℝ) = ((25600 / 48789) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (9450203 / 4000000) ≤ -Real.log (2411 / 25600) ∧
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


theorem reflection_log_6 : Bounds (-1181275377 / 500000000) (-9450203 / 4000000) (Real.log (2411 / 25600)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (322261509 / 500000000) ≤ -Real.log (2560 / 4877) ∧
    -Real.log (2560 / 4877) ≤ (644523019 / 1000000000) := by
  have h := checkLog_sound (w := (2317 / 7437)) (n := 12)
    (lo := (322261509 / 500000000)) (hi := (644523019 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4877 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4877 / 2560) = 1/(2560 / 4877) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (322261509 / 500000000) (644523019 / 1000000000) (Real.log (4877 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (4877 / 2560) = -Real.log (2560 / 4877) := by
    rw [show ((4877 / 2560) : ℝ) = ((2560 / 4877) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (588675273 / 250000000) ≤ -Real.log (243 / 2560) ∧
    -Real.log (243 / 2560) ≤ (294337637 / 125000000) := by
  have h := checkLog_sound (w := (77 / 563)) (n := 12)
    (lo := (8601861 / 31250000)) (hi := (275259553 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 243) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(320 / 243) = 1/(243 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-294337637 / 125000000) (-588675273 / 250000000) (Real.log (243 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (673610577 / 1000000000) ≤ -Real.log (500000 / 980653) ∧
    -Real.log (500000 / 980653) ≤ (336805289 / 500000000) := by
  have h := checkLog_sound (w := (480653 / 1480653)) (n := 12)
    (lo := (673610577 / 1000000000)) (hi := (336805289 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((980653 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(980653 / 500000) = 1/(500000 / 980653) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (673610577 / 1000000000) (336805289 / 500000000) (Real.log (980653 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (980653 / 500000) = -Real.log (500000 / 980653) := by
    rw [show ((980653 / 500000) : ℝ) = ((500000 / 980653) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (3252070727 / 1000000000) ≤ -Real.log (19347 / 500000) ∧
    -Real.log (19347 / 500000) ≤ (813017683 / 250000000) := by
  have h := checkLog_sound (w := (11903 / 50597)) (n := 12)
    (lo := (479482007 / 1000000000)) (hi := (59935251 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 19347) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(31250 / 19347) = 1/(19347 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-813017683 / 250000000) (-3252070727 / 1000000000) (Real.log (19347 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (336877939 / 500000000) ≤ -Real.log (1000000 / 1961591) ∧
    -Real.log (1000000 / 1961591) ≤ (673755879 / 1000000000) := by
  have h := checkLog_sound (w := (961591 / 2961591)) (n := 12)
    (lo := (336877939 / 500000000)) (hi := (673755879 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1961591 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1961591 / 1000000) = 1/(1000000 / 1961591) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (336877939 / 500000000) (673755879 / 1000000000) (Real.log (1961591 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1961591 / 1000000) = -Real.log (1000000 / 1961591) := by
    rw [show ((1961591 / 1000000) : ℝ) = ((1000000 / 1961591) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (3259463469 / 1000000000) ≤ -Real.log (38409 / 1000000) ∧
    -Real.log (38409 / 1000000) ≤ (1629731737 / 500000000) := by
  have h := checkLog_sound (w := (24091 / 100909)) (n := 12)
    (lo := (486874749 / 1000000000)) (hi := (1947499 / 4000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 38409) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 38409) = 1/(38409 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1629731737 / 500000000) (-3259463469 / 1000000000) (Real.log (38409 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (84174169 / 125000000) ≤ -Real.log (12500 / 24511) ∧
    -Real.log (12500 / 24511) ≤ (673393353 / 1000000000) := by
  have h := checkLog_sound (w := (12011 / 37011)) (n := 12)
    (lo := (84174169 / 125000000)) (hi := (673393353 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24511 / 12500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24511 / 12500) = 1/(12500 / 24511) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (84174169 / 125000000) (673393353 / 1000000000) (Real.log (24511 / 12500)) := by
  have h := reflection_log_13_neg
  have he : Real.log (24511 / 12500) = -Real.log (12500 / 24511) := by
    rw [show ((24511 / 12500) : ℝ) = ((12500 / 24511) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (3241121431 / 1000000000) ≤ -Real.log (489 / 12500) ∧
    -Real.log (489 / 12500) ≤ (810280359 / 250000000) := by
  have h := checkLog_sound (w := (1169 / 5081)) (n := 12)
    (lo := (468532711 / 1000000000)) (hi := (58566589 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3125 / 1956) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3125 / 1956) = 1/(489 / 12500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-810280359 / 250000000) (-3241121431 / 1000000000) (Real.log (489 / 12500)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (673542253 / 1000000000) ≤ -Real.log (250000 / 490293) ∧
    -Real.log (250000 / 490293) ≤ (336771127 / 500000000) := by
  have h := checkLog_sound (w := (240293 / 740293)) (n := 12)
    (lo := (673542253 / 1000000000)) (hi := (336771127 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((490293 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(490293 / 250000) = 1/(250000 / 490293) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (673542253 / 1000000000) (336771127 / 500000000) (Real.log (490293 / 250000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (490293 / 250000) = -Real.log (250000 / 490293) := by
    rw [show ((490293 / 250000) : ℝ) = ((250000 / 490293) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (81215341 / 25000000) ≤ -Real.log (9707 / 250000) ∧
    -Real.log (9707 / 250000) ≤ (649722729 / 200000000) := by
  have h := checkLog_sound (w := (2959 / 12666)) (n := 12)
    (lo := (11900623 / 25000000)) (hi := (476024921 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 9707) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(15625 / 9707) = 1/(9707 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-649722729 / 200000000) (-81215341 / 25000000) (Real.log (9707 / 250000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (490710163 / 125000000) ≤ -Real.log (250000000000 / 12671900036181) ∧
    -Real.log (250000000000 / 12671900036181) ≤ (392568131 / 100000000) := by
  have h := checkLog_sound (w := (4671900036181 / 20671900036181)) (n := 12)
    (lo := (114986351 / 250000000)) (hi := (91989081 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12671900036181 / 8000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(12671900036181 / 8000000000000) = 1/(250000000000 / 12671900036181) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (490710163 / 125000000) (392568131 / 100000000) (Real.log (12671900036181 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (12671900036181 / 250000000000) = -Real.log (250000000000 / 12671900036181) := by
    rw [show ((12671900036181 / 250000000000) : ℝ) = ((250000000000 / 12671900036181) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (3933219347 / 1000000000) ≤ -Real.log (250000000000 / 12767782290609) ∧
    -Real.log (250000000000 / 12767782290609) ≤ (3933219353 / 1000000000) := by
  have h := checkLog_sound (w := (4767782290609 / 20767782290609)) (n := 12)
    (lo := (467483447 / 1000000000)) (hi := (58435431 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12767782290609 / 8000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(12767782290609 / 8000000000000) = 1/(250000000000 / 12767782290609) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (3933219347 / 1000000000) (3933219353 / 1000000000) (Real.log (12767782290609 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (12767782290609 / 250000000000) = -Real.log (250000000000 / 12767782290609) := by
    rw [show ((12767782290609 / 250000000000) : ℝ) = ((250000000000 / 12767782290609) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (3914514783 / 1000000000) ≤ -Real.log (500000000000 / 25062372188139) ∧
    -Real.log (500000000000 / 25062372188139) ≤ (3914514789 / 1000000000) := by
  have h := checkLog_sound (w := (9062372188139 / 41062372188139)) (n := 12)
    (lo := (448778883 / 1000000000)) (hi := (112194721 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25062372188139 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(25062372188139 / 16000000000000) = 1/(500000000000 / 25062372188139) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (3914514783 / 1000000000) (3914514789 / 1000000000) (Real.log (25062372188139 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (25062372188139 / 500000000000) = -Real.log (500000000000 / 25062372188139) := by
    rw [show ((25062372188139 / 500000000000) : ℝ) = ((500000000000 / 25062372188139) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (1961077947 / 500000000) ≤ -Real.log (125000000000 / 6313652518801) ∧
    -Real.log (125000000000 / 6313652518801) ≤ (39221559 / 10000000) := by
  have h := checkLog_sound (w := (2313652518801 / 10313652518801)) (n := 12)
    (lo := (228209997 / 500000000)) (hi := (91283999 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6313652518801 / 4000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(6313652518801 / 4000000000000) = 1/(125000000000 / 6313652518801) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (1961077947 / 500000000) (39221559 / 10000000) (Real.log (6313652518801 / 125000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (6313652518801 / 125000000000) = -Real.log (125000000000 / 6313652518801) := by
    rw [show ((6313652518801 / 125000000000) : ℝ) = ((125000000000 / 6313652518801) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0111
