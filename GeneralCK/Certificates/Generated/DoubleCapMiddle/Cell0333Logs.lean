import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0333
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

theorem reflection_log_1_neg : (10808307 / 50000000) ≤ -Real.log (10240 / 12711) ∧
    -Real.log (10240 / 12711) ≤ (216166141 / 1000000000) := by
  have h := checkLog_sound (w := (2471 / 22951)) (n := 12)
    (lo := (10808307 / 50000000)) (hi := (216166141 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12711 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12711 / 10240) = 1/(10240 / 12711) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (10808307 / 50000000) (216166141 / 1000000000) (Real.log (12711 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12711 / 10240) = -Real.log (10240 / 12711) := by
    rw [show ((12711 / 10240) : ℝ) = ((10240 / 12711) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (276160163 / 1000000000) ≤ -Real.log (7769 / 10240) ∧
    -Real.log (7769 / 10240) ≤ (69040041 / 250000000) := by
  have h := checkLog_sound (w := (2471 / 18009)) (n := 12)
    (lo := (276160163 / 1000000000)) (hi := (69040041 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7769) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7769) = 1/(7769 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-69040041 / 250000000) (-276160163 / 1000000000) (Real.log (7769 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (13495631 / 62500000) ≤ -Real.log (2560 / 3177) ∧
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


theorem reflection_log_3 : Bounds (13495631 / 62500000) (215930097 / 1000000000) (Real.log (3177 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3177 / 2560) = -Real.log (2560 / 3177) := by
    rw [show ((3177 / 2560) : ℝ) = ((2560 / 3177) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (34471761 / 125000000) ≤ -Real.log (1943 / 2560) ∧
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


theorem reflection_log_4 : Bounds (-275774089 / 1000000000) (-34471761 / 125000000) (Real.log (1943 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (78761779 / 200000000) ≤ -Real.log (5120 / 7591) ∧
    -Real.log (5120 / 7591) ≤ (769158 / 1953125) := by
  have h := checkLog_sound (w := (2471 / 12711)) (n := 12)
    (lo := (78761779 / 200000000)) (hi := (769158 / 1953125))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7591 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7591 / 5120) = 1/(5120 / 7591) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (78761779 / 200000000) (769158 / 1953125) (Real.log (7591 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (7591 / 5120) = -Real.log (5120 / 7591) := by
    rw [show ((7591 / 5120) : ℝ) = ((5120 / 7591) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (164743057 / 250000000) ≤ -Real.log (2649 / 5120) ∧
    -Real.log (2649 / 5120) ≤ (658972229 / 1000000000) := by
  have h := checkLog_sound (w := (2471 / 7769)) (n := 12)
    (lo := (164743057 / 250000000)) (hi := (658972229 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2649) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2649) = 1/(2649 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-658972229 / 1000000000) (-164743057 / 250000000) (Real.log (2649 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (393413613 / 1000000000) ≤ -Real.log (1280 / 1897) ∧
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


theorem reflection_log_7 : Bounds (393413613 / 1000000000) (196706807 / 500000000) (Real.log (1897 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1897 / 1280) = -Real.log (1280 / 1897) := by
    rw [show ((1897 / 1280) : ℝ) = ((1280 / 1897) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (328920183 / 500000000) ≤ -Real.log (663 / 1280) ∧
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


theorem reflection_log_8 : Bounds (-657840367 / 1000000000) (-328920183 / 500000000) (Real.log (663 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (148015189 / 500000000) ≤ -Real.log (1000000 / 1344511) ∧
    -Real.log (1000000 / 1344511) ≤ (296030379 / 1000000000) := by
  have h := checkLog_sound (w := (344511 / 2344511)) (n := 12)
    (lo := (148015189 / 500000000)) (hi := (296030379 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1344511 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1344511 / 1000000) = 1/(1000000 / 1344511) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (148015189 / 500000000) (296030379 / 1000000000) (Real.log (1344511 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1344511 / 1000000) = -Real.log (1000000 / 1344511) := by
    rw [show ((1344511 / 1000000) : ℝ) = ((1000000 / 1344511) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (422373757 / 1000000000) ≤ -Real.log (655489 / 1000000) ∧
    -Real.log (655489 / 1000000) ≤ (211186879 / 500000000) := by
  have h := checkLog_sound (w := (344511 / 1655489)) (n := 12)
    (lo := (422373757 / 1000000000)) (hi := (211186879 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 655489) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 655489) = 1/(655489 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-211186879 / 500000000) (-422373757 / 1000000000) (Real.log (655489 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (59270029 / 200000000) ≤ -Real.log (1000000 / 1344941) ∧
    -Real.log (1000000 / 1344941) ≤ (148175073 / 500000000) := by
  have h := checkLog_sound (w := (344941 / 2344941)) (n := 12)
    (lo := (59270029 / 200000000)) (hi := (148175073 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1344941 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1344941 / 1000000) = 1/(1000000 / 1344941) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (59270029 / 200000000) (148175073 / 500000000) (Real.log (1344941 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1344941 / 1000000) = -Real.log (1000000 / 1344941) := by
    rw [show ((1344941 / 1000000) : ℝ) = ((1000000 / 1344941) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (423029971 / 1000000000) ≤ -Real.log (655059 / 1000000) ∧
    -Real.log (655059 / 1000000) ≤ (105757493 / 250000000) := by
  have h := checkLog_sound (w := (344941 / 1655059)) (n := 12)
    (lo := (423029971 / 1000000000)) (hi := (105757493 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 655059) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 655059) = 1/(655059 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-105757493 / 250000000) (-423029971 / 1000000000) (Real.log (655059 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (224644823 / 1000000000) ≤ -Real.log (500000 / 625939) ∧
    -Real.log (500000 / 625939) ≤ (28080603 / 125000000) := by
  have h := checkLog_sound (w := (125939 / 1125939)) (n := 12)
    (lo := (224644823 / 1000000000)) (hi := (28080603 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625939 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625939 / 500000) = 1/(500000 / 625939) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (224644823 / 1000000000) (28080603 / 125000000) (Real.log (625939 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (625939 / 500000) = -Real.log (500000 / 625939) := by
    rw [show ((625939 / 500000) : ℝ) = ((500000 / 625939) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (72547303 / 250000000) ≤ -Real.log (374061 / 500000) ∧
    -Real.log (374061 / 500000) ≤ (290189213 / 1000000000) := by
  have h := checkLog_sound (w := (125939 / 874061)) (n := 12)
    (lo := (72547303 / 250000000)) (hi := (290189213 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 374061) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 374061) = 1/(374061 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-290189213 / 1000000000) (-72547303 / 250000000) (Real.log (374061 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (7028537 / 31250000) ≤ -Real.log (500000 / 626107) ∧
    -Real.log (500000 / 626107) ≤ (44982637 / 200000000) := by
  have h := checkLog_sound (w := (126107 / 1126107)) (n := 12)
    (lo := (7028537 / 31250000)) (hi := (44982637 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((626107 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(626107 / 500000) = 1/(500000 / 626107) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (7028537 / 31250000) (44982637 / 200000000) (Real.log (626107 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (626107 / 500000) = -Real.log (500000 / 626107) := by
    rw [show ((626107 / 500000) : ℝ) = ((500000 / 626107) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (145319219 / 500000000) ≤ -Real.log (373893 / 500000) ∧
    -Real.log (373893 / 500000) ≤ (290638439 / 1000000000) := by
  have h := checkLog_sound (w := (126107 / 873893)) (n := 12)
    (lo := (145319219 / 500000000)) (hi := (290638439 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 373893) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 373893) = 1/(373893 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-290638439 / 1000000000) (-145319219 / 500000000) (Real.log (373893 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (359202067 / 500000000) ≤ -Real.log (125000000000 / 256394653457) ∧
    -Real.log (125000000000 / 256394653457) ≤ (89800517 / 125000000) := by
  have h := checkLog_sound (w := (6394653457 / 506394653457)) (n := 12)
    (lo := (12628477 / 500000000)) (hi := (5051391 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((256394653457 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(256394653457 / 250000000000) = 1/(125000000000 / 256394653457) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (359202067 / 500000000) (89800517 / 125000000) (Real.log (256394653457 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (256394653457 / 125000000000) = -Real.log (125000000000 / 256394653457) := by
    rw [show ((256394653457 / 125000000000) : ℝ) = ((125000000000 / 256394653457) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (179845029 / 250000000) ≤ -Real.log (100000000000 / 205316009703) ∧
    -Real.log (100000000000 / 205316009703) ≤ (359690059 / 500000000) := by
  have h := checkLog_sound (w := (5316009703 / 405316009703)) (n := 12)
    (lo := (3279117 / 125000000)) (hi := (26232937 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((205316009703 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(205316009703 / 200000000000) = 1/(100000000000 / 205316009703) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (179845029 / 250000000) (359690059 / 500000000) (Real.log (205316009703 / 100000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (205316009703 / 100000000000) = -Real.log (100000000000 / 205316009703) := by
    rw [show ((205316009703 / 100000000000) : ℝ) = ((100000000000 / 205316009703) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (128708509 / 250000000) ≤ -Real.log (500000000000 / 836680381007) ∧
    -Real.log (500000000000 / 836680381007) ≤ (514834037 / 1000000000) := by
  have h := checkLog_sound (w := (336680381007 / 1336680381007)) (n := 12)
    (lo := (128708509 / 250000000)) (hi := (514834037 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((836680381007 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(836680381007 / 500000000000) = 1/(500000000000 / 836680381007) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (128708509 / 250000000) (514834037 / 1000000000) (Real.log (836680381007 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (836680381007 / 500000000000) = -Real.log (500000000000 / 836680381007) := by
    rw [show ((836680381007 / 500000000000) : ℝ) = ((500000000000 / 836680381007) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (257775811 / 500000000) ≤ -Real.log (500000000000 / 837280986807) ∧
    -Real.log (500000000000 / 837280986807) ≤ (515551623 / 1000000000) := by
  have h := checkLog_sound (w := (337280986807 / 1337280986807)) (n := 12)
    (lo := (257775811 / 500000000)) (hi := (515551623 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((837280986807 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(837280986807 / 500000000000) = 1/(500000000000 / 837280986807) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (257775811 / 500000000) (515551623 / 1000000000) (Real.log (837280986807 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (837280986807 / 500000000000) = -Real.log (500000000000 / 837280986807) := by
    rw [show ((837280986807 / 500000000000) : ℝ) = ((500000000000 / 837280986807) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0333
