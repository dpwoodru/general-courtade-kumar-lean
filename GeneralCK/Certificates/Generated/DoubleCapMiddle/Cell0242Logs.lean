import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0242
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

theorem reflection_log_1_neg : (246615907 / 1000000000) ≤ -Real.log (640 / 819) ∧
    -Real.log (640 / 819) ≤ (61653977 / 250000000) := by
  have h := checkLog_sound (w := (179 / 1459)) (n := 12)
    (lo := (246615907 / 1000000000)) (hi := (61653977 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((819 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(819 / 640) = 1/(640 / 819) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (246615907 / 1000000000) (61653977 / 250000000) (Real.log (819 / 640)) := by
  have h := reflection_log_1_neg
  have he : Real.log (819 / 640) = -Real.log (640 / 819) := by
    rw [show ((819 / 640) : ℝ) = ((640 / 819) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (328070133 / 1000000000) ≤ -Real.log (461 / 640) ∧
    -Real.log (461 / 640) ≤ (164035067 / 500000000) := by
  have h := checkLog_sound (w := (179 / 1101)) (n := 12)
    (lo := (328070133 / 1000000000)) (hi := (164035067 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 461) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 461) = 1/(461 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-164035067 / 500000000) (-328070133 / 1000000000) (Real.log (461 / 640)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (246157927 / 1000000000) ≤ -Real.log (5120 / 6549) ∧
    -Real.log (5120 / 6549) ≤ (30769741 / 125000000) := by
  have h := checkLog_sound (w := (1429 / 11669)) (n := 12)
    (lo := (246157927 / 1000000000)) (hi := (30769741 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6549 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6549 / 5120) = 1/(5120 / 6549) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (246157927 / 1000000000) (30769741 / 125000000) (Real.log (6549 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6549 / 5120) = -Real.log (5120 / 6549) := by
    rw [show ((6549 / 5120) : ℝ) = ((5120 / 6549) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (65451403 / 200000000) ≤ -Real.log (3691 / 5120) ∧
    -Real.log (3691 / 5120) ≤ (40907127 / 125000000) := by
  have h := checkLog_sound (w := (1429 / 8811)) (n := 12)
    (lo := (65451403 / 200000000)) (hi := (40907127 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3691) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3691) = 1/(3691 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-40907127 / 125000000) (-65451403 / 200000000) (Real.log (3691 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (444285099 / 1000000000) ≤ -Real.log (320 / 499) ∧
    -Real.log (320 / 499) ≤ (4442851 / 10000000) := by
  have h := checkLog_sound (w := (179 / 819)) (n := 12)
    (lo := (444285099 / 1000000000)) (hi := (4442851 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((499 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(499 / 320) = 1/(320 / 499) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (444285099 / 1000000000) (4442851 / 10000000) (Real.log (499 / 320)) := by
  have h := reflection_log_5_neg
  have he : Real.log (499 / 320) = -Real.log (320 / 499) := by
    rw [show ((499 / 320) : ℝ) = ((320 / 499) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (51222569 / 62500000) ≤ -Real.log (141 / 320) ∧
    -Real.log (141 / 320) ≤ (409780553 / 500000000) := by
  have h := checkLog_sound (w := (19 / 301)) (n := 12)
    (lo := (31603481 / 250000000)) (hi := (5056557 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 141) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(160 / 141) = 1/(141 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-409780553 / 500000000) (-51222569 / 62500000) (Real.log (141 / 320)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (221766657 / 500000000) ≤ -Real.log (2560 / 3989) ∧
    -Real.log (2560 / 3989) ≤ (88706663 / 200000000) := by
  have h := checkLog_sound (w := (1429 / 6549)) (n := 12)
    (lo := (221766657 / 500000000)) (hi := (88706663 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3989 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3989 / 2560) = 1/(2560 / 3989) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (221766657 / 500000000) (88706663 / 200000000) (Real.log (3989 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (3989 / 2560) = -Real.log (2560 / 3989) := by
    rw [show ((3989 / 2560) : ℝ) = ((2560 / 3989) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (40845253 / 50000000) ≤ -Real.log (1131 / 2560) ∧
    -Real.log (1131 / 2560) ≤ (408452531 / 500000000) := by
  have h := checkLog_sound (w := (149 / 2411)) (n := 12)
    (lo := (3093947 / 25000000)) (hi := (123757881 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 1131) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 1131) = 1/(1131 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-408452531 / 500000000) (-40845253 / 50000000) (Real.log (1131 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (67385141 / 200000000) ≤ -Real.log (200000 / 280127) ∧
    -Real.log (200000 / 280127) ≤ (168462853 / 500000000) := by
  have h := checkLog_sound (w := (80127 / 480127)) (n := 12)
    (lo := (67385141 / 200000000)) (hi := (168462853 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((280127 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(280127 / 200000) = 1/(200000 / 280127) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (67385141 / 200000000) (168462853 / 500000000) (Real.log (280127 / 200000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (280127 / 200000) = -Real.log (200000 / 280127) := by
    rw [show ((280127 / 200000) : ℝ) = ((200000 / 280127) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (511884517 / 1000000000) ≤ -Real.log (119873 / 200000) ∧
    -Real.log (119873 / 200000) ≤ (255942259 / 500000000) := by
  have h := checkLog_sound (w := (80127 / 319873)) (n := 12)
    (lo := (511884517 / 1000000000)) (hi := (255942259 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 119873) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 119873) = 1/(119873 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-255942259 / 500000000) (-511884517 / 1000000000) (Real.log (119873 / 200000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (84386843 / 250000000) ≤ -Real.log (500000 / 700753) ∧
    -Real.log (500000 / 700753) ≤ (337547373 / 1000000000) := by
  have h := checkLog_sound (w := (200753 / 1200753)) (n := 12)
    (lo := (84386843 / 250000000)) (hi := (337547373 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((700753 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(700753 / 500000) = 1/(500000 / 700753) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (84386843 / 250000000) (337547373 / 1000000000) (Real.log (700753 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (700753 / 500000) = -Real.log (500000 / 700753) := by
    rw [show ((700753 / 500000) : ℝ) = ((500000 / 700753) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (513338779 / 1000000000) ≤ -Real.log (299247 / 500000) ∧
    -Real.log (299247 / 500000) ≤ (25666939 / 50000000) := by
  have h := checkLog_sound (w := (200753 / 799247)) (n := 12)
    (lo := (513338779 / 1000000000)) (hi := (25666939 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 299247) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 299247) = 1/(299247 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-25666939 / 50000000) (-513338779 / 1000000000) (Real.log (299247 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (129813337 / 500000000) ≤ -Real.log (500000 / 648223) ∧
    -Real.log (500000 / 648223) ≤ (10385067 / 40000000) := by
  have h := checkLog_sound (w := (148223 / 1148223)) (n := 12)
    (lo := (129813337 / 500000000)) (hi := (10385067 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((648223 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(648223 / 500000) = 1/(500000 / 648223) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (129813337 / 500000000) (10385067 / 40000000) (Real.log (648223 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (648223 / 500000) = -Real.log (500000 / 648223) := by
    rw [show ((648223 / 500000) : ℝ) = ((500000 / 648223) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (175805323 / 500000000) ≤ -Real.log (351777 / 500000) ∧
    -Real.log (351777 / 500000) ≤ (351610647 / 1000000000) := by
  have h := checkLog_sound (w := (148223 / 851777)) (n := 12)
    (lo := (175805323 / 500000000)) (hi := (351610647 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 351777) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 351777) = 1/(351777 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-351610647 / 1000000000) (-175805323 / 500000000) (Real.log (351777 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (5203391 / 20000000) ≤ -Real.log (20000 / 25943) ∧
    -Real.log (20000 / 25943) ≤ (260169551 / 1000000000) := by
  have h := checkLog_sound (w := (5943 / 45943)) (n := 12)
    (lo := (5203391 / 20000000)) (hi := (260169551 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25943 / 20000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25943 / 20000) = 1/(20000 / 25943) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (5203391 / 20000000) (260169551 / 1000000000) (Real.log (25943 / 20000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (25943 / 20000) = -Real.log (20000 / 25943) := by
    rw [show ((25943 / 20000) : ℝ) = ((20000 / 25943) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (352611781 / 1000000000) ≤ -Real.log (14057 / 20000) ∧
    -Real.log (14057 / 20000) ≤ (176305891 / 500000000) := by
  have h := checkLog_sound (w := (5943 / 34057)) (n := 12)
    (lo := (352611781 / 1000000000)) (hi := (176305891 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20000 / 14057) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20000 / 14057) = 1/(14057 / 20000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-176305891 / 500000000) (-352611781 / 1000000000) (Real.log (14057 / 20000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (424405111 / 500000000) ≤ -Real.log (100000000000 / 233686484863) ∧
    -Real.log (100000000000 / 233686484863) ≤ (53050639 / 62500000) := by
  have h := checkLog_sound (w := (33686484863 / 433686484863)) (n := 12)
    (lo := (77831521 / 500000000)) (hi := (155663043 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((233686484863 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(233686484863 / 200000000000) = 1/(100000000000 / 233686484863) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (424405111 / 500000000) (53050639 / 62500000) (Real.log (233686484863 / 100000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (233686484863 / 100000000000) = -Real.log (100000000000 / 233686484863) := by
    rw [show ((233686484863 / 100000000000) : ℝ) = ((100000000000 / 233686484863) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (850886151 / 1000000000) ≤ -Real.log (500000000000 / 1170860526589) ∧
    -Real.log (500000000000 / 1170860526589) ≤ (850886153 / 1000000000) := by
  have h := checkLog_sound (w := (170860526589 / 2170860526589)) (n := 12)
    (lo := (157738971 / 1000000000)) (hi := (39434743 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1170860526589 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1170860526589 / 1000000000000) = 1/(500000000000 / 1170860526589) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (850886151 / 1000000000) (850886153 / 1000000000) (Real.log (1170860526589 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1170860526589 / 500000000000) = -Real.log (500000000000 / 1170860526589) := by
    rw [show ((1170860526589 / 500000000000) : ℝ) = ((500000000000 / 1170860526589) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (15280933 / 25000000) ≤ -Real.log (250000000000 / 460677503077) ∧
    -Real.log (250000000000 / 460677503077) ≤ (611237321 / 1000000000) := by
  have h := checkLog_sound (w := (210677503077 / 710677503077)) (n := 12)
    (lo := (15280933 / 25000000)) (hi := (611237321 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((460677503077 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(460677503077 / 250000000000) = 1/(250000000000 / 460677503077) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (15280933 / 25000000) (611237321 / 1000000000) (Real.log (460677503077 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (460677503077 / 250000000000) = -Real.log (250000000000 / 460677503077) := by
    rw [show ((460677503077 / 250000000000) : ℝ) = ((250000000000 / 460677503077) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (612781331 / 1000000000) ≤ -Real.log (62500000000 / 115347335847) ∧
    -Real.log (62500000000 / 115347335847) ≤ (153195333 / 250000000) := by
  have h := checkLog_sound (w := (52847335847 / 177847335847)) (n := 12)
    (lo := (612781331 / 1000000000)) (hi := (153195333 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((115347335847 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(115347335847 / 62500000000) = 1/(62500000000 / 115347335847) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (612781331 / 1000000000) (153195333 / 250000000) (Real.log (115347335847 / 62500000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (115347335847 / 62500000000) = -Real.log (62500000000 / 115347335847) := by
    rw [show ((115347335847 / 62500000000) : ℝ) = ((62500000000 / 115347335847) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0242
