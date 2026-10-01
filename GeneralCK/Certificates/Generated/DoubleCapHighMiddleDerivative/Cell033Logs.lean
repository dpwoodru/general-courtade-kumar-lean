import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell033
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed GeneralCK.Reflection

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

theorem reflection_log_1_neg : (119477691 / 500000000) ≤ -Real.log (2560 / 3251) ∧
    -Real.log (2560 / 3251) ≤ (238955383 / 1000000000) := by
  have h := checkLog_sound (w := (691 / 5811)) (n := 12)
    (lo := (119477691 / 500000000)) (hi := (238955383 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3251 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3251 / 2560) = 1/(2560 / 3251) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (119477691 / 500000000) (238955383 / 1000000000) (Real.log (3251 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3251 / 2560) = -Real.log (2560 / 3251) := by
    rw [show ((3251 / 2560) : ℝ) = ((2560 / 3251) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (31460373 / 100000000) ≤ -Real.log (1869 / 2560) ∧
    -Real.log (1869 / 2560) ≤ (314603731 / 1000000000) := by
  have h := checkLog_sound (w := (691 / 4429)) (n := 12)
    (lo := (31460373 / 100000000)) (hi := (314603731 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1869) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1869) = 1/(1869 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-314603731 / 1000000000) (-31460373 / 100000000) (Real.log (1869 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (238493879 / 1000000000) ≤ -Real.log (5120 / 6499) ∧
    -Real.log (5120 / 6499) ≤ (5962347 / 25000000) := by
  have h := checkLog_sound (w := (1379 / 11619)) (n := 12)
    (lo := (238493879 / 1000000000)) (hi := (5962347 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6499 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6499 / 5120) = 1/(5120 / 6499) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (238493879 / 1000000000) (5962347 / 25000000) (Real.log (6499 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6499 / 5120) = -Real.log (5120 / 6499) := by
    rw [show ((6499 / 5120) : ℝ) = ((5120 / 6499) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (313801483 / 1000000000) ≤ -Real.log (3741 / 5120) ∧
    -Real.log (3741 / 5120) ≤ (78450371 / 250000000) := by
  have h := checkLog_sound (w := (1379 / 8861)) (n := 12)
    (lo := (313801483 / 1000000000)) (hi := (78450371 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3741) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3741) = 1/(3741 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-78450371 / 250000000) (-313801483 / 1000000000) (Real.log (3741 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (87414277 / 500000000) ≤ -Real.log (500000 / 595521) ∧
    -Real.log (500000 / 595521) ≤ (34965711 / 200000000) := by
  have h := checkLog_sound (w := (95521 / 1095521)) (n := 12)
    (lo := (87414277 / 500000000)) (hi := (34965711 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((595521 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(595521 / 500000) = 1/(500000 / 595521) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (87414277 / 500000000) (34965711 / 200000000) (Real.log (595521 / 500000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (595521 / 500000) = -Real.log (500000 / 595521) := by
    rw [show ((595521 / 500000) : ℝ) = ((500000 / 595521) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (212008279 / 1000000000) ≤ -Real.log (404479 / 500000) ∧
    -Real.log (404479 / 500000) ≤ (5300207 / 25000000) := by
  have h := checkLog_sound (w := (95521 / 904479)) (n := 12)
    (lo := (212008279 / 1000000000)) (hi := (5300207 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 404479) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 404479) = 1/(404479 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-5300207 / 25000000) (-212008279 / 1000000000) (Real.log (404479 / 500000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (43795281 / 250000000) ≤ -Real.log (500000 / 595731) ∧
    -Real.log (500000 / 595731) ≤ (1401449 / 8000000) := by
  have h := checkLog_sound (w := (95731 / 1095731)) (n := 12)
    (lo := (43795281 / 250000000)) (hi := (1401449 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((595731 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(595731 / 500000) = 1/(500000 / 595731) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (43795281 / 250000000) (1401449 / 8000000) (Real.log (595731 / 500000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (595731 / 500000) = -Real.log (500000 / 595731) := by
    rw [show ((595731 / 500000) : ℝ) = ((500000 / 595731) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (531319 / 2500000) ≤ -Real.log (404269 / 500000) ∧
    -Real.log (404269 / 500000) ≤ (212527601 / 1000000000) := by
  have h := checkLog_sound (w := (95731 / 904269)) (n := 12)
    (lo := (531319 / 2500000)) (hi := (212527601 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 404269) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 404269) = 1/(404269 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-212527601 / 1000000000) (-531319 / 2500000) (Real.log (404269 / 500000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (127925207 / 1000000000) ≤ -Real.log (250000 / 284117) ∧
    -Real.log (250000 / 284117) ≤ (15990651 / 125000000) := by
  have h := checkLog_sound (w := (34117 / 534117)) (n := 12)
    (lo := (127925207 / 1000000000)) (hi := (15990651 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((284117 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(284117 / 250000) = 1/(250000 / 284117) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (127925207 / 1000000000) (15990651 / 125000000) (Real.log (284117 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (284117 / 250000) = -Real.log (250000 / 284117) := by
    rw [show ((284117 / 250000) : ℝ) = ((250000 / 284117) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (146724323 / 1000000000) ≤ -Real.log (215883 / 250000) ∧
    -Real.log (215883 / 250000) ≤ (36681081 / 250000000) := by
  have h := checkLog_sound (w := (34117 / 465883)) (n := 12)
    (lo := (146724323 / 1000000000)) (hi := (36681081 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 215883) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 215883) = 1/(215883 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-36681081 / 250000000) (-146724323 / 1000000000) (Real.log (215883 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (64097653 / 500000000) ≤ -Real.log (40000 / 45471) ∧
    -Real.log (40000 / 45471) ≤ (128195307 / 1000000000) := by
  have h := checkLog_sound (w := (5471 / 85471)) (n := 12)
    (lo := (64097653 / 500000000)) (hi := (128195307 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((45471 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(45471 / 40000) = 1/(40000 / 45471) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (64097653 / 500000000) (128195307 / 1000000000) (Real.log (45471 / 40000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (45471 / 40000) = -Real.log (40000 / 45471) := by
    rw [show ((45471 / 40000) : ℝ) = ((40000 / 45471) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (147079903 / 1000000000) ≤ -Real.log (34529 / 40000) ∧
    -Real.log (34529 / 40000) ≤ (4596247 / 31250000) := by
  have h := checkLog_sound (w := (5471 / 74529)) (n := 12)
    (lo := (147079903 / 1000000000)) (hi := (4596247 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000 / 34529) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000 / 34529) = 1/(34529 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-4596247 / 31250000) (-147079903 / 1000000000) (Real.log (34529 / 40000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (552295363 / 1000000000) ≤ -Real.log (500000000000 / 868618016573) ∧
    -Real.log (500000000000 / 868618016573) ≤ (138073841 / 250000000) := by
  have h := checkLog_sound (w := (368618016573 / 1368618016573)) (n := 12)
    (lo := (552295363 / 1000000000)) (hi := (138073841 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((868618016573 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(868618016573 / 500000000000) = 1/(500000000000 / 868618016573) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (552295363 / 1000000000) (138073841 / 250000000) (Real.log (868618016573 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (868618016573 / 500000000000) = -Real.log (500000000000 / 868618016573) := by
    rw [show ((868618016573 / 500000000000) : ℝ) = ((500000000000 / 868618016573) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (69194889 / 125000000) ≤ -Real.log (500000000000 / 869716425897) ∧
    -Real.log (500000000000 / 869716425897) ≤ (553559113 / 1000000000) := by
  have h := checkLog_sound (w := (369716425897 / 1369716425897)) (n := 12)
    (lo := (69194889 / 125000000)) (hi := (553559113 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((869716425897 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(869716425897 / 500000000000) = 1/(500000000000 / 869716425897) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (69194889 / 125000000) (553559113 / 1000000000) (Real.log (869716425897 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (869716425897 / 500000000000) = -Real.log (500000000000 / 869716425897) := by
    rw [show ((869716425897 / 500000000000) : ℝ) = ((500000000000 / 869716425897) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (386836833 / 1000000000) ≤ -Real.log (500000000000 / 736158119457) ∧
    -Real.log (500000000000 / 736158119457) ≤ (193418417 / 500000000) := by
  have h := checkLog_sound (w := (236158119457 / 1236158119457)) (n := 12)
    (lo := (386836833 / 1000000000)) (hi := (193418417 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((736158119457 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(736158119457 / 500000000000) = 1/(500000000000 / 736158119457) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (386836833 / 1000000000) (193418417 / 500000000) (Real.log (736158119457 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (736158119457 / 500000000000) = -Real.log (500000000000 / 736158119457) := by
    rw [show ((736158119457 / 500000000000) : ℝ) = ((500000000000 / 736158119457) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (96927181 / 250000000) ≤ -Real.log (500000000000 / 736800249339) ∧
    -Real.log (500000000000 / 736800249339) ≤ (15508349 / 40000000) := by
  have h := checkLog_sound (w := (236800249339 / 1236800249339)) (n := 12)
    (lo := (96927181 / 250000000)) (hi := (15508349 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((736800249339 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(736800249339 / 500000000000) = 1/(500000000000 / 736800249339) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (96927181 / 250000000) (15508349 / 40000000) (Real.log (736800249339 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (736800249339 / 500000000000) = -Real.log (500000000000 / 736800249339) := by
    rw [show ((736800249339 / 500000000000) : ℝ) = ((500000000000 / 736800249339) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (27464953 / 100000000) ≤ -Real.log (50000000000 / 65803467619) ∧
    -Real.log (50000000000 / 65803467619) ≤ (274649531 / 1000000000) := by
  have h := checkLog_sound (w := (15803467619 / 115803467619)) (n := 12)
    (lo := (27464953 / 100000000)) (hi := (274649531 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((65803467619 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(65803467619 / 50000000000) = 1/(50000000000 / 65803467619) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (27464953 / 100000000) (274649531 / 1000000000) (Real.log (65803467619 / 50000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (65803467619 / 50000000000) = -Real.log (50000000000 / 65803467619) := by
    rw [show ((65803467619 / 50000000000) : ℝ) = ((50000000000 / 65803467619) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (275275209 / 1000000000) ≤ -Real.log (500000000000 / 658446523213) ∧
    -Real.log (500000000000 / 658446523213) ≤ (27527521 / 100000000) := by
  have h := checkLog_sound (w := (158446523213 / 1158446523213)) (n := 12)
    (lo := (275275209 / 1000000000)) (hi := (27527521 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((658446523213 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(658446523213 / 500000000000) = 1/(500000000000 / 658446523213) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (275275209 / 1000000000) (27527521 / 100000000) (Real.log (658446523213 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (658446523213 / 500000000000) = -Real.log (500000000000 / 658446523213) := by
    rw [show ((658446523213 / 500000000000) : ℝ) = ((500000000000 / 658446523213) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (18884597 / 1000000000) ≤ -Real.log (1570068159 / 1600000000) ∧
    -Real.log (1570068159 / 1600000000) ≤ (9442299 / 500000000) := by
  have h := checkLog_sound (w := (29931841 / 3170068159)) (n := 12)
    (lo := (18884597 / 1000000000)) (hi := (9442299 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600000000 / 1570068159) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1600000000 / 1570068159) = 1/(1570068159 / 1600000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-9442299 / 500000000) (-18884597 / 1000000000) (Real.log (1570068159 / 1600000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (4699779 / 250000000) ≤ -Real.log (61336030311 / 62500000000) ∧
    -Real.log (61336030311 / 62500000000) ≤ (18799117 / 1000000000) := by
  have h := checkLog_sound (w := (1163969689 / 123836030311)) (n := 12)
    (lo := (4699779 / 250000000)) (hi := (18799117 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 61336030311) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 61336030311) = 1/(61336030311 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-18799117 / 1000000000) (-4699779 / 250000000) (Real.log (61336030311 / 62500000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell033
