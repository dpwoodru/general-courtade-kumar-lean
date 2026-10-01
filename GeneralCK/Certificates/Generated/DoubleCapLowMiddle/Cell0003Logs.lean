import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0003
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

theorem reflection_log_1_neg : (682956269 / 1000000000) ≤ -Real.log (125000000000 / 247465209961) ∧
    -Real.log (125000000000 / 247465209961) ≤ (68295627 / 100000000) := by
  have h := checkLog_sound (w := (122465209961 / 372465209961)) (n := 12)
    (lo := (682956269 / 1000000000)) (hi := (68295627 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((247465209961 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(247465209961 / 125000000000) = 1/(125000000000 / 247465209961) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (682956269 / 1000000000) (68295627 / 100000000) (Real.log (247465209961 / 125000000000)) := by
  have h := reflection_log_1_neg
  have he : Real.log (247465209961 / 125000000000) = -Real.log (125000000000 / 247465209961) := by
    rw [show ((247465209961 / 125000000000) : ℝ) = ((125000000000 / 247465209961) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (155928117 / 40000000) ≤ -Real.log (2534790039 / 125000000000) ∧
    -Real.log (2534790039 / 125000000000) ≤ (3898202931 / 1000000000) := by
  have h := checkLog_sound (w := (1371459961 / 6441040039)) (n := 12)
    (lo := (17298681 / 40000000)) (hi := (216233513 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3906250000 / 2534790039) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3906250000 / 2534790039) = 1/(2534790039 / 125000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-3898202931 / 1000000000) (-155928117 / 40000000) (Real.log (2534790039 / 125000000000)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (341454703 / 500000000) ≤ -Real.log (51200 / 101357) ∧
    -Real.log (51200 / 101357) ≤ (682909407 / 1000000000) := by
  have h := checkLog_sound (w := (50157 / 152557)) (n := 12)
    (lo := (341454703 / 500000000)) (hi := (682909407 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((101357 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(101357 / 51200) = 1/(51200 / 101357) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (341454703 / 500000000) (682909407 / 1000000000) (Real.log (101357 / 51200)) := by
  have h := reflection_log_3_neg
  have he : Real.log (101357 / 51200) = -Real.log (51200 / 101357) := by
    rw [show ((101357 / 51200) : ℝ) = ((51200 / 101357) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (3893638353 / 1000000000) ≤ -Real.log (1043 / 51200) ∧
    -Real.log (1043 / 51200) ≤ (3893638359 / 1000000000) := by
  have h := checkLog_sound (w := (557 / 2643)) (n := 12)
    (lo := (427902453 / 1000000000)) (hi := (213951227 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1043) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(1600 / 1043) = 1/(1043 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-3893638359 / 1000000000) (-3893638353 / 1000000000) (Real.log (1043 / 51200)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (42041277 / 62500000) ≤ -Real.log (102400 / 200647) ∧
    -Real.log (102400 / 200647) ≤ (672660433 / 1000000000) := by
  have h := checkLog_sound (w := (98247 / 303047)) (n := 12)
    (lo := (42041277 / 62500000)) (hi := (672660433 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200647 / 102400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200647 / 102400) = 1/(102400 / 200647) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (42041277 / 62500000) (672660433 / 1000000000) (Real.log (200647 / 102400)) := by
  have h := reflection_log_5_neg
  have he : Real.log (200647 / 102400) = -Real.log (102400 / 200647) := by
    rw [show ((200647 / 102400) : ℝ) = ((102400 / 200647) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (641011149 / 200000000) ≤ -Real.log (4153 / 102400) ∧
    -Real.log (4153 / 102400) ≤ (12820223 / 4000000) := by
  have h := checkLog_sound (w := (2247 / 10553)) (n := 12)
    (lo := (17298681 / 40000000)) (hi := (216233513 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6400 / 4153) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(6400 / 4153) = 1/(4153 / 102400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-12820223 / 4000000) (-641011149 / 200000000) (Real.log (4153 / 102400)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (336282867 / 500000000) ≤ -Real.log (25600 / 50157) ∧
    -Real.log (25600 / 50157) ≤ (134513147 / 200000000) := by
  have h := checkLog_sound (w := (24557 / 75757)) (n := 12)
    (lo := (336282867 / 500000000)) (hi := (134513147 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50157 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50157 / 25600) = 1/(25600 / 50157) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (336282867 / 500000000) (134513147 / 200000000) (Real.log (50157 / 25600)) := by
  have h := reflection_log_7_neg
  have he : Real.log (50157 / 25600) = -Real.log (25600 / 50157) := by
    rw [show ((50157 / 25600) : ℝ) = ((25600 / 50157) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (3200491173 / 1000000000) ≤ -Real.log (1043 / 25600) ∧
    -Real.log (1043 / 25600) ≤ (1600245589 / 500000000) := by
  have h := checkLog_sound (w := (557 / 2643)) (n := 12)
    (lo := (427902453 / 1000000000)) (hi := (213951227 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1043) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1600 / 1043) = 1/(1043 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1600245589 / 500000000) (-3200491173 / 1000000000) (Real.log (1043 / 25600)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (684450977 / 1000000000) ≤ -Real.log (1000000 / 1982683) ∧
    -Real.log (1000000 / 1982683) ≤ (342225489 / 500000000) := by
  have h := checkLog_sound (w := (982683 / 2982683)) (n := 12)
    (lo := (684450977 / 1000000000)) (hi := (342225489 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1982683 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1982683 / 1000000) = 1/(1000000 / 1982683) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (684450977 / 1000000000) (342225489 / 500000000) (Real.log (1982683 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1982683 / 1000000) = -Real.log (1000000 / 1982683) := by
    rw [show ((1982683 / 1000000) : ℝ) = ((1000000 / 1982683) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (2028033299 / 500000000) ≤ -Real.log (17317 / 1000000) ∧
    -Real.log (17317 / 1000000) ≤ (1014016651 / 250000000) := by
  have h := checkLog_sound (w := (13933 / 48567)) (n := 12)
    (lo := (295165349 / 500000000)) (hi := (590330699 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 17317) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 17317) = 1/(17317 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-1014016651 / 250000000) (-2028033299 / 500000000) (Real.log (17317 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (684489813 / 1000000000) ≤ -Real.log (25000 / 49569) ∧
    -Real.log (25000 / 49569) ≤ (342244907 / 500000000) := by
  have h := checkLog_sound (w := (24569 / 74569)) (n := 12)
    (lo := (684489813 / 1000000000)) (hi := (342244907 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49569 / 25000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49569 / 25000) = 1/(25000 / 49569) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (684489813 / 1000000000) (342244907 / 500000000) (Real.log (49569 / 25000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (49569 / 25000) = -Real.log (25000 / 49569) := by
    rw [show ((49569 / 25000) : ℝ) = ((25000 / 49569) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (406052301 / 100000000) ≤ -Real.log (431 / 25000) ∧
    -Real.log (431 / 25000) ≤ (507565377 / 125000000) := by
  have h := checkLog_sound (w := (1401 / 4849)) (n := 12)
    (lo := (59478711 / 100000000)) (hi := (594787111 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3125 / 1724) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3125 / 1724) = 1/(431 / 25000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-507565377 / 125000000) (-406052301 / 100000000) (Real.log (431 / 25000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (684418697 / 1000000000) ≤ -Real.log (1000000 / 1982619) ∧
    -Real.log (1000000 / 1982619) ≤ (342209349 / 500000000) := by
  have h := checkLog_sound (w := (982619 / 2982619)) (n := 12)
    (lo := (684418697 / 1000000000)) (hi := (342209349 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1982619 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1982619 / 1000000) = 1/(1000000 / 1982619) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (684418697 / 1000000000) (342209349 / 500000000) (Real.log (1982619 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1982619 / 1000000) = -Real.log (1000000 / 1982619) := by
    rw [show ((1982619 / 1000000) : ℝ) = ((1000000 / 1982619) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (202618881 / 50000000) ≤ -Real.log (17381 / 1000000) ∧
    -Real.log (17381 / 1000000) ≤ (2026188813 / 500000000) := by
  have h := checkLog_sound (w := (13869 / 48631)) (n := 12)
    (lo := (14666043 / 25000000)) (hi := (586641721 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 17381) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 17381) = 1/(17381 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-2026188813 / 500000000) (-202618881 / 50000000) (Real.log (17381 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (684458039 / 1000000000) ≤ -Real.log (1000000 / 1982697) ∧
    -Real.log (1000000 / 1982697) ≤ (17111451 / 25000000) := by
  have h := checkLog_sound (w := (982697 / 2982697)) (n := 12)
    (lo := (684458039 / 1000000000)) (hi := (17111451 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1982697 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1982697 / 1000000) = 1/(1000000 / 1982697) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (684458039 / 1000000000) (17111451 / 25000000) (Real.log (1982697 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1982697 / 1000000) = -Real.log (1000000 / 1982697) := by
    rw [show ((1982697 / 1000000) : ℝ) = ((1000000 / 1982697) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (4056875379 / 1000000000) ≤ -Real.log (17303 / 1000000) ∧
    -Real.log (17303 / 1000000) ≤ (811375077 / 200000000) := by
  have h := checkLog_sound (w := (13947 / 48553)) (n := 12)
    (lo := (591139479 / 1000000000)) (hi := (14778487 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 17303) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 17303) = 1/(17303 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-811375077 / 200000000) (-4056875379 / 1000000000) (Real.log (17303 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (189620703 / 40000000) ≤ -Real.log (125000000000 / 14311680718369) ∧
    -Real.log (125000000000 / 14311680718369) ≤ (2370258791 / 500000000) := by
  have h := checkLog_sound (w := (6311680718369 / 22311680718369)) (n := 12)
    (lo := (116326899 / 200000000)) (hi := (9088039 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((14311680718369 / 8000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(14311680718369 / 8000000000000) = 1/(125000000000 / 14311680718369) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (189620703 / 40000000) (2370258791 / 500000000) (Real.log (14311680718369 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (14311680718369 / 125000000000) = -Real.log (125000000000 / 14311680718369) := by
    rw [show ((14311680718369 / 125000000000) : ℝ) = ((125000000000 / 14311680718369) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (4745012823 / 1000000000) ≤ -Real.log (50000000000 / 5750464037123) ∧
    -Real.log (50000000000 / 5750464037123) ≤ (474501283 / 100000000) := by
  have h := checkLog_sound (w := (2550464037123 / 8950464037123)) (n := 12)
    (lo := (586129743 / 1000000000)) (hi := (36633109 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5750464037123 / 3200000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(5750464037123 / 3200000000000) = 1/(50000000000 / 5750464037123) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (4745012823 / 1000000000) (474501283 / 100000000) (Real.log (5750464037123 / 50000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (5750464037123 / 50000000000) = -Real.log (50000000000 / 5750464037123) := by
    rw [show ((5750464037123 / 50000000000) : ℝ) = ((50000000000 / 5750464037123) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (4736796317 / 1000000000) ≤ -Real.log (500000000000 / 57034088947701) ∧
    -Real.log (500000000000 / 57034088947701) ≤ (1184199081 / 250000000) := by
  have h := checkLog_sound (w := (25034088947701 / 89034088947701)) (n := 12)
    (lo := (577913237 / 1000000000)) (hi := (288956619 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((57034088947701 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(57034088947701 / 32000000000000) = 1/(500000000000 / 57034088947701) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (4736796317 / 1000000000) (1184199081 / 250000000) (Real.log (57034088947701 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (57034088947701 / 500000000000) = -Real.log (500000000000 / 57034088947701) := by
    rw [show ((57034088947701 / 500000000000) : ℝ) = ((500000000000 / 57034088947701) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (4741333417 / 1000000000) ≤ -Real.log (500000000000 / 57293446223199) ∧
    -Real.log (500000000000 / 57293446223199) ≤ (296333339 / 62500000) := by
  have h := checkLog_sound (w := (25293446223199 / 89293446223199)) (n := 12)
    (lo := (582450337 / 1000000000)) (hi := (291225169 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((57293446223199 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(57293446223199 / 32000000000000) = 1/(500000000000 / 57293446223199) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (4741333417 / 1000000000) (296333339 / 62500000) (Real.log (57293446223199 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (57293446223199 / 500000000000) = -Real.log (500000000000 / 57293446223199) := by
    rw [show ((57293446223199 / 500000000000) : ℝ) = ((500000000000 / 57293446223199) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0003
