import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0117
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

theorem reflection_log_1_neg : (66722823 / 100000000) ≤ -Real.log (2560 / 4989) ∧
    -Real.log (2560 / 4989) ≤ (667228231 / 1000000000) := by
  have h := checkLog_sound (w := (2429 / 7549)) (n := 12)
    (lo := (66722823 / 100000000)) (hi := (667228231 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4989 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4989 / 2560) = 1/(2560 / 4989) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (66722823 / 100000000) (667228231 / 1000000000) (Real.log (4989 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (4989 / 2560) = -Real.log (2560 / 4989) := by
    rw [show ((4989 / 2560) : ℝ) = ((2560 / 4989) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (743141303 / 250000000) ≤ -Real.log (131 / 2560) ∧
    -Real.log (131 / 2560) ≤ (2972565217 / 1000000000) := by
  have h := checkLog_sound (w := (29 / 291)) (n := 12)
    (lo := (49994123 / 250000000)) (hi := (199976493 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 131) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(160 / 131) = 1/(131 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-2972565217 / 1000000000) (-743141303 / 250000000) (Real.log (131 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (16671183 / 25000000) ≤ -Real.log (25600 / 49871) ∧
    -Real.log (25600 / 49871) ≤ (666847321 / 1000000000) := by
  have h := checkLog_sound (w := (24271 / 75471)) (n := 12)
    (lo := (16671183 / 25000000)) (hi := (666847321 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49871 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49871 / 25600) = 1/(25600 / 49871) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (16671183 / 25000000) (666847321 / 1000000000) (Real.log (49871 / 25600)) := by
  have h := reflection_log_3_neg
  have he : Real.log (49871 / 25600) = -Real.log (25600 / 49871) := by
    rw [show ((49871 / 25600) : ℝ) = ((25600 / 49871) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (2958165569 / 1000000000) ≤ -Real.log (1329 / 25600) ∧
    -Real.log (1329 / 25600) ≤ (1479082787 / 500000000) := by
  have h := checkLog_sound (w := (271 / 2929)) (n := 12)
    (lo := (185576849 / 1000000000)) (hi := (3711537 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1329) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1600 / 1329) = 1/(1329 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-1479082787 / 500000000) (-2958165569 / 1000000000) (Real.log (1329 / 25600)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (160154893 / 250000000) ≤ -Real.log (1280 / 2429) ∧
    -Real.log (1280 / 2429) ≤ (640619573 / 1000000000) := by
  have h := checkLog_sound (w := (1149 / 3709)) (n := 12)
    (lo := (160154893 / 250000000)) (hi := (640619573 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2429 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2429 / 1280) = 1/(1280 / 2429) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (160154893 / 250000000) (640619573 / 1000000000) (Real.log (2429 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2429 / 1280) = -Real.log (1280 / 2429) := by
    rw [show ((2429 / 1280) : ℝ) = ((1280 / 2429) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (142463627 / 62500000) ≤ -Real.log (131 / 1280) ∧
    -Real.log (131 / 1280) ≤ (569854509 / 250000000) := by
  have h := checkLog_sound (w := (29 / 291)) (n := 12)
    (lo := (49994123 / 250000000)) (hi := (199976493 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 131) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(160 / 131) = 1/(131 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-569854509 / 250000000) (-142463627 / 62500000) (Real.log (131 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (639837051 / 1000000000) ≤ -Real.log (12800 / 24271) ∧
    -Real.log (12800 / 24271) ≤ (159959263 / 250000000) := by
  have h := checkLog_sound (w := (11471 / 37071)) (n := 12)
    (lo := (639837051 / 1000000000)) (hi := (159959263 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24271 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24271 / 12800) = 1/(12800 / 24271) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (639837051 / 1000000000) (159959263 / 250000000) (Real.log (24271 / 12800)) := by
  have h := reflection_log_7_neg
  have he : Real.log (24271 / 12800) = -Real.log (12800 / 24271) := by
    rw [show ((24271 / 12800) : ℝ) = ((12800 / 24271) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (2265018389 / 1000000000) ≤ -Real.log (1329 / 12800) ∧
    -Real.log (1329 / 12800) ≤ (2265018393 / 1000000000) := by
  have h := checkLog_sound (w := (271 / 2929)) (n := 12)
    (lo := (185576849 / 1000000000)) (hi := (3711537 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1329) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1600 / 1329) = 1/(1329 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-2265018393 / 1000000000) (-2265018389 / 1000000000) (Real.log (1329 / 12800)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (167970799 / 250000000) ≤ -Real.log (1000000 / 1957921) ∧
    -Real.log (1000000 / 1957921) ≤ (671883197 / 1000000000) := by
  have h := checkLog_sound (w := (957921 / 2957921)) (n := 12)
    (lo := (167970799 / 250000000)) (hi := (671883197 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1957921 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1957921 / 1000000) = 1/(1000000 / 1957921) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (167970799 / 250000000) (671883197 / 1000000000) (Real.log (1957921 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1957921 / 1000000) = -Real.log (1000000 / 1957921) := by
    rw [show ((1957921 / 1000000) : ℝ) = ((1000000 / 1957921) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (396025809 / 125000000) ≤ -Real.log (42079 / 1000000) ∧
    -Real.log (42079 / 1000000) ≤ (3168206477 / 1000000000) := by
  have h := checkLog_sound (w := (20421 / 104579)) (n := 12)
    (lo := (49452219 / 125000000)) (hi := (395617753 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 42079) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 42079) = 1/(42079 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-3168206477 / 1000000000) (-396025809 / 125000000) (Real.log (42079 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (42010669 / 62500000) ≤ -Real.log (250000 / 489621) ∧
    -Real.log (250000 / 489621) ≤ (134434141 / 200000000) := by
  have h := checkLog_sound (w := (239621 / 739621)) (n := 12)
    (lo := (42010669 / 62500000)) (hi := (134434141 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((489621 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(489621 / 250000) = 1/(250000 / 489621) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (42010669 / 62500000) (134434141 / 200000000) (Real.log (489621 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (489621 / 250000) = -Real.log (250000 / 489621) := by
    rw [show ((489621 / 250000) : ℝ) = ((250000 / 489621) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (3181676381 / 1000000000) ≤ -Real.log (10379 / 250000) ∧
    -Real.log (10379 / 250000) ≤ (1590838193 / 500000000) := by
  have h := checkLog_sound (w := (2623 / 13002)) (n := 12)
    (lo := (409087661 / 1000000000)) (hi := (204543831 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 10379) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(15625 / 10379) = 1/(10379 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1590838193 / 500000000) (-3181676381 / 1000000000) (Real.log (10379 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (16790401 / 25000000) ≤ -Real.log (500000 / 978699) ∧
    -Real.log (500000 / 978699) ≤ (671616041 / 1000000000) := by
  have h := checkLog_sound (w := (478699 / 1478699)) (n := 12)
    (lo := (16790401 / 25000000)) (hi := (671616041 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((978699 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(978699 / 500000) = 1/(500000 / 978699) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (16790401 / 25000000) (671616041 / 1000000000) (Real.log (978699 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (978699 / 500000) = -Real.log (500000 / 978699) := by
    rw [show ((978699 / 500000) : ℝ) = ((500000 / 978699) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (788963519 / 250000000) ≤ -Real.log (21301 / 500000) ∧
    -Real.log (21301 / 500000) ≤ (3155854081 / 1000000000) := by
  have h := checkLog_sound (w := (9949 / 52551)) (n := 12)
    (lo := (95816339 / 250000000)) (hi := (383265357 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 21301) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(31250 / 21301) = 1/(21301 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-3155854081 / 1000000000) (-788963519 / 250000000) (Real.log (21301 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (167978077 / 250000000) ≤ -Real.log (500000 / 978989) ∧
    -Real.log (500000 / 978989) ≤ (671912309 / 1000000000) := by
  have h := checkLog_sound (w := (478989 / 1478989)) (n := 12)
    (lo := (167978077 / 250000000)) (hi := (671912309 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((978989 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(978989 / 500000) = 1/(500000 / 978989) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (167978077 / 250000000) (671912309 / 1000000000) (Real.log (978989 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (978989 / 500000) = -Real.log (500000 / 978989) := by
    rw [show ((978989 / 500000) : ℝ) = ((500000 / 978989) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (1584780993 / 500000000) ≤ -Real.log (21011 / 500000) ∧
    -Real.log (21011 / 500000) ≤ (3169561991 / 1000000000) := by
  have h := checkLog_sound (w := (10239 / 52261)) (n := 12)
    (lo := (198486633 / 500000000)) (hi := (396973267 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 21011) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(31250 / 21011) = 1/(21011 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-3169561991 / 1000000000) (-1584780993 / 500000000) (Real.log (21011 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (960022417 / 250000000) ≤ -Real.log (250000000000 / 11632411654269) ∧
    -Real.log (250000000000 / 11632411654269) ≤ (1920044837 / 500000000) := by
  have h := checkLog_sound (w := (3632411654269 / 19632411654269)) (n := 12)
    (lo := (46794221 / 125000000)) (hi := (374353769 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11632411654269 / 8000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(11632411654269 / 8000000000000) = 1/(250000000000 / 11632411654269) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (960022417 / 250000000) (1920044837 / 500000000) (Real.log (11632411654269 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (11632411654269 / 250000000000) = -Real.log (250000000000 / 11632411654269) := by
    rw [show ((11632411654269 / 250000000000) : ℝ) = ((250000000000 / 11632411654269) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (770769417 / 200000000) ≤ -Real.log (500000000000 / 23587098949803) ∧
    -Real.log (500000000000 / 23587098949803) ≤ (3853847091 / 1000000000) := by
  have h := checkLog_sound (w := (7587098949803 / 39587098949803)) (n := 12)
    (lo := (77622237 / 200000000)) (hi := (194055593 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((23587098949803 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(23587098949803 / 16000000000000) = 1/(500000000000 / 23587098949803) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (770769417 / 200000000) (3853847091 / 1000000000) (Real.log (23587098949803 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (23587098949803 / 500000000000) = -Real.log (500000000000 / 23587098949803) := by
    rw [show ((23587098949803 / 500000000000) : ℝ) = ((500000000000 / 23587098949803) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (765494023 / 200000000) ≤ -Real.log (50000000000 / 2297307638139) ∧
    -Real.log (50000000000 / 2297307638139) ≤ (3827470121 / 1000000000) := by
  have h := checkLog_sound (w := (697307638139 / 3897307638139)) (n := 12)
    (lo := (72346843 / 200000000)) (hi := (45216777 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2297307638139 / 1600000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(2297307638139 / 1600000000000) = 1/(50000000000 / 2297307638139) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (765494023 / 200000000) (3827470121 / 1000000000) (Real.log (2297307638139 / 50000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (2297307638139 / 50000000000) = -Real.log (50000000000 / 2297307638139) := by
    rw [show ((2297307638139 / 50000000000) : ℝ) = ((50000000000 / 2297307638139) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (3841474293 / 1000000000) ≤ -Real.log (500000000000 / 23297058683547) ∧
    -Real.log (500000000000 / 23297058683547) ≤ (3841474299 / 1000000000) := by
  have h := checkLog_sound (w := (7297058683547 / 39297058683547)) (n := 12)
    (lo := (375738393 / 1000000000)) (hi := (187869197 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((23297058683547 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(23297058683547 / 16000000000000) = 1/(500000000000 / 23297058683547) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (3841474293 / 1000000000) (3841474299 / 1000000000) (Real.log (23297058683547 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (23297058683547 / 500000000000) = -Real.log (500000000000 / 23297058683547) := by
    rw [show ((23297058683547 / 500000000000) : ℝ) = ((500000000000 / 23297058683547) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0117
