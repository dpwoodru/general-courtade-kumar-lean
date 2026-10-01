import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0334
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

theorem reflection_log_1_neg : (13495631 / 62500000) ≤ -Real.log (2560 / 3177) ∧
    -Real.log (2560 / 3177) ≤ (215930097 / 1000000000) := by
  have h := checkLog_sound (w := (617 / 5737)) (n := 12)
    (lo := (13495631 / 62500000)) (hi := (215930097 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3177 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3177 / 2560) = 1/(2560 / 3177) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (13495631 / 62500000) (215930097 / 1000000000) (Real.log (3177 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3177 / 2560) = -Real.log (2560 / 3177) := by
    rw [show ((3177 / 2560) : ℝ) = ((2560 / 3177) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (34471761 / 125000000) ≤ -Real.log (1943 / 2560) ∧
    -Real.log (1943 / 2560) ≤ (275774089 / 1000000000) := by
  have h := checkLog_sound (w := (617 / 4503)) (n := 12)
    (lo := (34471761 / 125000000)) (hi := (275774089 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1943) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1943) = 1/(1943 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-275774089 / 1000000000) (-34471761 / 125000000) (Real.log (1943 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (215693997 / 1000000000) ≤ -Real.log (2048 / 2541) ∧
    -Real.log (2048 / 2541) ≤ (107846999 / 500000000) := by
  have h := checkLog_sound (w := (493 / 4589)) (n := 12)
    (lo := (215693997 / 1000000000)) (hi := (107846999 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2541 / 2048) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2541 / 2048) = 1/(2048 / 2541) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (215693997 / 1000000000) (107846999 / 500000000) (Real.log (2541 / 2048)) := by
  have h := reflection_log_3_neg
  have he : Real.log (2541 / 2048) = -Real.log (2048 / 2541) := by
    rw [show ((2541 / 2048) : ℝ) = ((2048 / 2541) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (275388161 / 1000000000) ≤ -Real.log (1555 / 2048) ∧
    -Real.log (1555 / 2048) ≤ (137694081 / 500000000) := by
  have h := checkLog_sound (w := (493 / 3603)) (n := 12)
    (lo := (275388161 / 1000000000)) (hi := (137694081 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2048 / 1555) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2048 / 1555) = 1/(1555 / 2048) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-137694081 / 500000000) (-275388161 / 1000000000) (Real.log (1555 / 2048)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (393413613 / 1000000000) ≤ -Real.log (1280 / 1897) ∧
    -Real.log (1280 / 1897) ≤ (196706807 / 500000000) := by
  have h := checkLog_sound (w := (617 / 3177)) (n := 12)
    (lo := (393413613 / 1000000000)) (hi := (196706807 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1897 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1897 / 1280) = 1/(1280 / 1897) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (393413613 / 1000000000) (196706807 / 500000000) (Real.log (1897 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1897 / 1280) = -Real.log (1280 / 1897) := by
    rw [show ((1897 / 1280) : ℝ) = ((1280 / 1897) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (328920183 / 500000000) ≤ -Real.log (663 / 1280) ∧
    -Real.log (663 / 1280) ≤ (657840367 / 1000000000) := by
  have h := checkLog_sound (w := (617 / 1943)) (n := 12)
    (lo := (328920183 / 500000000)) (hi := (657840367 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 663) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 663) = 1/(663 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-657840367 / 1000000000) (-328920183 / 500000000) (Real.log (663 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (393018173 / 1000000000) ≤ -Real.log (1024 / 1517) ∧
    -Real.log (1024 / 1517) ≤ (196509087 / 500000000) := by
  have h := checkLog_sound (w := (493 / 2541)) (n := 12)
    (lo := (393018173 / 1000000000)) (hi := (196509087 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1517 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1517 / 1024) = 1/(1024 / 1517) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (393018173 / 1000000000) (196509087 / 500000000) (Real.log (1517 / 1024)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1517 / 1024) = -Real.log (1024 / 1517) := by
    rw [show ((1517 / 1024) : ℝ) = ((1024 / 1517) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (82088723 / 125000000) ≤ -Real.log (531 / 1024) ∧
    -Real.log (531 / 1024) ≤ (131341957 / 200000000) := by
  have h := checkLog_sound (w := (493 / 1555)) (n := 12)
    (lo := (82088723 / 125000000)) (hi := (131341957 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 531) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 531) = 1/(531 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-131341957 / 200000000) (-82088723 / 125000000) (Real.log (531 / 1024)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (73927999 / 250000000) ≤ -Real.log (1000000 / 1344083) ∧
    -Real.log (1000000 / 1344083) ≤ (295711997 / 1000000000) := by
  have h := checkLog_sound (w := (344083 / 2344083)) (n := 12)
    (lo := (73927999 / 250000000)) (hi := (295711997 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1344083 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1344083 / 1000000) = 1/(1000000 / 1344083) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (73927999 / 250000000) (295711997 / 1000000000) (Real.log (1344083 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1344083 / 1000000) = -Real.log (1000000 / 1344083) := by
    rw [show ((1344083 / 1000000) : ℝ) = ((1000000 / 1344083) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (210860511 / 500000000) ≤ -Real.log (655917 / 1000000) ∧
    -Real.log (655917 / 1000000) ≤ (421721023 / 1000000000) := by
  have h := checkLog_sound (w := (344083 / 1655917)) (n := 12)
    (lo := (210860511 / 500000000)) (hi := (421721023 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 655917) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 655917) = 1/(655917 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-421721023 / 1000000000) (-210860511 / 500000000) (Real.log (655917 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (296031121 / 1000000000) ≤ -Real.log (15625 / 21008) ∧
    -Real.log (15625 / 21008) ≤ (148015561 / 500000000) := by
  have h := checkLog_sound (w := (5383 / 36633)) (n := 12)
    (lo := (296031121 / 1000000000)) (hi := (148015561 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((21008 / 15625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(21008 / 15625) = 1/(15625 / 21008) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (296031121 / 1000000000) (148015561 / 500000000) (Real.log (21008 / 15625)) := by
  have h := reflection_log_11_neg
  have he : Real.log (21008 / 15625) = -Real.log (15625 / 21008) := by
    rw [show ((21008 / 15625) : ℝ) = ((15625 / 21008) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (211187641 / 500000000) ≤ -Real.log (10242 / 15625) ∧
    -Real.log (10242 / 15625) ≤ (422375283 / 1000000000) := by
  have h := checkLog_sound (w := (5383 / 25867)) (n := 12)
    (lo := (211187641 / 500000000)) (hi := (422375283 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 10242) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625 / 10242) = 1/(10242 / 15625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-422375283 / 1000000000) (-211187641 / 500000000) (Real.log (10242 / 15625)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (224377989 / 1000000000) ≤ -Real.log (125000 / 156443) ∧
    -Real.log (125000 / 156443) ≤ (22437799 / 100000000) := by
  have h := checkLog_sound (w := (31443 / 281443)) (n := 12)
    (lo := (224377989 / 1000000000)) (hi := (22437799 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((156443 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(156443 / 125000) = 1/(125000 / 156443) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (224377989 / 1000000000) (22437799 / 100000000) (Real.log (156443 / 125000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (156443 / 125000) = -Real.log (125000 / 156443) := by
    rw [show ((156443 / 125000) : ℝ) = ((125000 / 156443) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (289742861 / 1000000000) ≤ -Real.log (93557 / 125000) ∧
    -Real.log (93557 / 125000) ≤ (144871431 / 500000000) := by
  have h := checkLog_sound (w := (31443 / 218557)) (n := 12)
    (lo := (289742861 / 1000000000)) (hi := (144871431 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 93557) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 93557) = 1/(93557 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-144871431 / 500000000) (-289742861 / 1000000000) (Real.log (93557 / 125000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (112322811 / 500000000) ≤ -Real.log (1000000 / 1251879) ∧
    -Real.log (1000000 / 1251879) ≤ (224645623 / 1000000000) := by
  have h := checkLog_sound (w := (251879 / 2251879)) (n := 12)
    (lo := (112322811 / 500000000)) (hi := (224645623 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1251879 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1251879 / 1000000) = 1/(1000000 / 1251879) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (112322811 / 500000000) (224645623 / 1000000000) (Real.log (1251879 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1251879 / 1000000) = -Real.log (1000000 / 1251879) := by
    rw [show ((1251879 / 1000000) : ℝ) = ((1000000 / 1251879) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (290190549 / 1000000000) ≤ -Real.log (748121 / 1000000) ∧
    -Real.log (748121 / 1000000) ≤ (5803811 / 20000000) := by
  have h := checkLog_sound (w := (251879 / 1748121)) (n := 12)
    (lo := (290190549 / 1000000000)) (hi := (5803811 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 748121) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 748121) = 1/(748121 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-5803811 / 20000000) (-290190549 / 1000000000) (Real.log (748121 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (358716509 / 500000000) ≤ -Real.log (250000000000 / 512291570427) ∧
    -Real.log (250000000000 / 512291570427) ≤ (35871651 / 50000000) := by
  have h := checkLog_sound (w := (12291570427 / 1012291570427)) (n := 12)
    (lo := (12142919 / 500000000)) (hi := (24285839 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512291570427 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(512291570427 / 500000000000) = 1/(250000000000 / 512291570427) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (358716509 / 500000000) (35871651 / 50000000) (Real.log (512291570427 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (512291570427 / 250000000000) = -Real.log (250000000000 / 512291570427) := by
    rw [show ((512291570427 / 250000000000) : ℝ) = ((250000000000 / 512291570427) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (718406403 / 1000000000) ≤ -Real.log (500000000000 / 1025580941223) ∧
    -Real.log (500000000000 / 1025580941223) ≤ (143681281 / 200000000) := by
  have h := checkLog_sound (w := (25580941223 / 2025580941223)) (n := 12)
    (lo := (25259223 / 1000000000)) (hi := (3157403 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1025580941223 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1025580941223 / 1000000000000) = 1/(500000000000 / 1025580941223) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (718406403 / 1000000000) (143681281 / 200000000) (Real.log (1025580941223 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1025580941223 / 500000000000) = -Real.log (500000000000 / 1025580941223) := by
    rw [show ((1025580941223 / 500000000000) : ℝ) = ((500000000000 / 1025580941223) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (10282417 / 20000000) ≤ -Real.log (50000000000 / 83608388469) ∧
    -Real.log (50000000000 / 83608388469) ≤ (514120851 / 1000000000) := by
  have h := checkLog_sound (w := (33608388469 / 133608388469)) (n := 12)
    (lo := (10282417 / 20000000)) (hi := (514120851 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((83608388469 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(83608388469 / 50000000000) = 1/(50000000000 / 83608388469) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (10282417 / 20000000) (514120851 / 1000000000) (Real.log (83608388469 / 50000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (83608388469 / 50000000000) = -Real.log (50000000000 / 83608388469) := by
    rw [show ((83608388469 / 50000000000) : ℝ) = ((50000000000 / 83608388469) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (128709043 / 250000000) ≤ -Real.log (20000000000 / 33467286709) ∧
    -Real.log (20000000000 / 33467286709) ≤ (514836173 / 1000000000) := by
  have h := checkLog_sound (w := (13467286709 / 53467286709)) (n := 12)
    (lo := (128709043 / 250000000)) (hi := (514836173 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((33467286709 / 20000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(33467286709 / 20000000000) = 1/(20000000000 / 33467286709) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (128709043 / 250000000) (514836173 / 1000000000) (Real.log (33467286709 / 20000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (33467286709 / 20000000000) = -Real.log (20000000000 / 33467286709) := by
    rw [show ((33467286709 / 20000000000) : ℝ) = ((20000000000 / 33467286709) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0334
