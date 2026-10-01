import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell188
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

theorem reflection_log_1_neg : (77007569 / 250000000) ≤ -Real.log (5120 / 6967) ∧
    -Real.log (5120 / 6967) ≤ (308030277 / 1000000000) := by
  have h := checkLog_sound (w := (1847 / 12087)) (n := 12)
    (lo := (77007569 / 250000000)) (hi := (308030277 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6967 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6967 / 5120) = 1/(5120 / 6967) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (77007569 / 250000000) (308030277 / 1000000000) (Real.log (6967 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6967 / 5120) = -Real.log (5120 / 6967) := by
    rw [show ((6967 / 5120) : ℝ) = ((5120 / 6967) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (447447443 / 1000000000) ≤ -Real.log (3273 / 5120) ∧
    -Real.log (3273 / 5120) ≤ (111861861 / 250000000) := by
  have h := checkLog_sound (w := (1847 / 8393)) (n := 12)
    (lo := (447447443 / 1000000000)) (hi := (111861861 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3273) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3273) = 1/(3273 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-111861861 / 250000000) (-447447443 / 1000000000) (Real.log (3273 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (153799791 / 500000000) ≤ -Real.log (1280 / 1741) ∧
    -Real.log (1280 / 1741) ≤ (307599583 / 1000000000) := by
  have h := checkLog_sound (w := (461 / 3021)) (n := 12)
    (lo := (153799791 / 500000000)) (hi := (307599583 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1741 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1741 / 1280) = 1/(1280 / 1741) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (153799791 / 500000000) (307599583 / 1000000000) (Real.log (1741 / 1280)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1741 / 1280) = -Real.log (1280 / 1741) := by
    rw [show ((1741 / 1280) : ℝ) = ((1280 / 1741) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (446531273 / 1000000000) ≤ -Real.log (819 / 1280) ∧
    -Real.log (819 / 1280) ≤ (223265637 / 500000000) := by
  have h := checkLog_sound (w := (461 / 2099)) (n := 12)
    (lo := (446531273 / 1000000000)) (hi := (223265637 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 819) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 819) = 1/(819 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-223265637 / 500000000) (-446531273 / 1000000000) (Real.log (819 / 1280)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (228030789 / 1000000000) ≤ -Real.log (250000 / 314031) ∧
    -Real.log (250000 / 314031) ≤ (22803079 / 100000000) := by
  have h := checkLog_sound (w := (64031 / 564031)) (n := 12)
    (lo := (228030789 / 1000000000)) (hi := (22803079 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((314031 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(314031 / 250000) = 1/(250000 / 314031) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (228030789 / 1000000000) (22803079 / 100000000) (Real.log (314031 / 250000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (314031 / 250000) = -Real.log (250000 / 314031) := by
    rw [show ((314031 / 250000) : ℝ) = ((250000 / 314031) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (73970231 / 250000000) ≤ -Real.log (185969 / 250000) ∧
    -Real.log (185969 / 250000) ≤ (11835237 / 40000000) := by
  have h := checkLog_sound (w := (64031 / 435969)) (n := 12)
    (lo := (73970231 / 250000000)) (hi := (11835237 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 185969) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 185969) = 1/(185969 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-11835237 / 40000000) (-73970231 / 250000000) (Real.log (185969 / 250000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (114183741 / 500000000) ≤ -Real.log (1000000 / 1256547) ∧
    -Real.log (1000000 / 1256547) ≤ (228367483 / 1000000000) := by
  have h := checkLog_sound (w := (256547 / 2256547)) (n := 12)
    (lo := (114183741 / 500000000)) (hi := (228367483 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1256547 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1256547 / 1000000) = 1/(1000000 / 1256547) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (114183741 / 500000000) (228367483 / 1000000000) (Real.log (1256547 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1256547 / 1000000) = -Real.log (1000000 / 1256547) := by
    rw [show ((1256547 / 1000000) : ℝ) = ((1000000 / 1256547) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (296449729 / 1000000000) ≤ -Real.log (743453 / 1000000) ∧
    -Real.log (743453 / 1000000) ≤ (29644973 / 100000000) := by
  have h := checkLog_sound (w := (256547 / 1743453)) (n := 12)
    (lo := (296449729 / 1000000000)) (hi := (29644973 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 743453) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 743453) = 1/(743453 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-29644973 / 100000000) (-296449729 / 1000000000) (Real.log (743453 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (16928613 / 100000000) ≤ -Real.log (1000000 / 1184459) ∧
    -Real.log (1000000 / 1184459) ≤ (169286131 / 1000000000) := by
  have h := checkLog_sound (w := (184459 / 2184459)) (n := 12)
    (lo := (16928613 / 100000000)) (hi := (169286131 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1184459 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1184459 / 1000000) = 1/(1000000 / 1184459) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (16928613 / 100000000) (169286131 / 1000000000) (Real.log (1184459 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1184459 / 1000000) = -Real.log (1000000 / 1184459) := by
    rw [show ((1184459 / 1000000) : ℝ) = ((1000000 / 1184459) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (101951791 / 500000000) ≤ -Real.log (815541 / 1000000) ∧
    -Real.log (815541 / 1000000) ≤ (203903583 / 1000000000) := by
  have h := checkLog_sound (w := (184459 / 1815541)) (n := 12)
    (lo := (101951791 / 500000000)) (hi := (203903583 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 815541) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 815541) = 1/(815541 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-203903583 / 1000000000) (-101951791 / 500000000) (Real.log (815541 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (169552883 / 1000000000) ≤ -Real.log (40000 / 47391) ∧
    -Real.log (40000 / 47391) ≤ (42388221 / 250000000) := by
  have h := checkLog_sound (w := (7391 / 87391)) (n := 12)
    (lo := (169552883 / 1000000000)) (hi := (42388221 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((47391 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(47391 / 40000) = 1/(40000 / 47391) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (169552883 / 1000000000) (42388221 / 250000000) (Real.log (47391 / 40000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (47391 / 40000) = -Real.log (40000 / 47391) := by
    rw [show ((47391 / 40000) : ℝ) = ((40000 / 47391) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (20429113 / 100000000) ≤ -Real.log (32609 / 40000) ∧
    -Real.log (32609 / 40000) ≤ (204291131 / 1000000000) := by
  have h := checkLog_sound (w := (7391 / 72609)) (n := 12)
    (lo := (20429113 / 100000000)) (hi := (204291131 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000 / 32609) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000 / 32609) = 1/(32609 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-204291131 / 1000000000) (-20429113 / 100000000) (Real.log (32609 / 40000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (150826171 / 200000000) ≤ -Real.log (500000000000 / 1062881562881) ∧
    -Real.log (500000000000 / 1062881562881) ≤ (754130857 / 1000000000) := by
  have h := checkLog_sound (w := (62881562881 / 2062881562881)) (n := 12)
    (lo := (2439347 / 40000000)) (hi := (15245919 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1062881562881 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1062881562881 / 1000000000000) = 1/(500000000000 / 1062881562881) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (150826171 / 200000000) (754130857 / 1000000000) (Real.log (1062881562881 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1062881562881 / 500000000000) = -Real.log (500000000000 / 1062881562881) := by
    rw [show ((1062881562881 / 500000000000) : ℝ) = ((500000000000 / 1062881562881) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (755477719 / 1000000000) ≤ -Real.log (250000000000 / 532157042469) ∧
    -Real.log (250000000000 / 532157042469) ≤ (755477721 / 1000000000) := by
  have h := checkLog_sound (w := (32157042469 / 1032157042469)) (n := 12)
    (lo := (62330539 / 1000000000)) (hi := (3116527 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((532157042469 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(532157042469 / 500000000000) = 1/(250000000000 / 532157042469) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (755477719 / 1000000000) (755477721 / 1000000000) (Real.log (532157042469 / 250000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (532157042469 / 250000000000) = -Real.log (250000000000 / 532157042469) := by
    rw [show ((532157042469 / 250000000000) : ℝ) = ((250000000000 / 532157042469) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (523911713 / 1000000000) ≤ -Real.log (15625000000 / 26384689787) ∧
    -Real.log (15625000000 / 26384689787) ≤ (261955857 / 500000000) := by
  have h := checkLog_sound (w := (10759689787 / 42009689787)) (n := 12)
    (lo := (523911713 / 1000000000)) (hi := (261955857 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((26384689787 / 15625000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(26384689787 / 15625000000) = 1/(15625000000 / 26384689787) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (523911713 / 1000000000) (261955857 / 500000000) (Real.log (26384689787 / 15625000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (26384689787 / 15625000000) = -Real.log (15625000000 / 26384689787) := by
    rw [show ((26384689787 / 15625000000) : ℝ) = ((15625000000 / 26384689787) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (131204303 / 250000000) ≤ -Real.log (500000000000 / 845074940851) ∧
    -Real.log (500000000000 / 845074940851) ≤ (524817213 / 1000000000) := by
  have h := checkLog_sound (w := (345074940851 / 1345074940851)) (n := 12)
    (lo := (131204303 / 250000000)) (hi := (524817213 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((845074940851 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(845074940851 / 500000000000) = 1/(500000000000 / 845074940851) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (131204303 / 250000000) (524817213 / 1000000000) (Real.log (845074940851 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (845074940851 / 500000000000) = -Real.log (500000000000 / 845074940851) := by
    rw [show ((845074940851 / 500000000000) : ℝ) = ((500000000000 / 845074940851) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (23324357 / 62500000) ≤ -Real.log (125000000000 / 181544980571) ∧
    -Real.log (125000000000 / 181544980571) ≤ (373189713 / 1000000000) := by
  have h := checkLog_sound (w := (56544980571 / 306544980571)) (n := 12)
    (lo := (23324357 / 62500000)) (hi := (373189713 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((181544980571 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(181544980571 / 125000000000) = 1/(125000000000 / 181544980571) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (23324357 / 62500000) (373189713 / 1000000000) (Real.log (181544980571 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (181544980571 / 125000000000) = -Real.log (125000000000 / 181544980571) := by
    rw [show ((181544980571 / 125000000000) : ℝ) = ((125000000000 / 181544980571) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (373844013 / 1000000000) ≤ -Real.log (100000000000 / 145331043577) ∧
    -Real.log (100000000000 / 145331043577) ≤ (186922007 / 500000000) := by
  have h := checkLog_sound (w := (45331043577 / 245331043577)) (n := 12)
    (lo := (373844013 / 1000000000)) (hi := (186922007 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((145331043577 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(145331043577 / 100000000000) = 1/(100000000000 / 145331043577) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (373844013 / 1000000000) (186922007 / 500000000) (Real.log (145331043577 / 100000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (145331043577 / 100000000000) = -Real.log (100000000000 / 145331043577) := by
    rw [show ((145331043577 / 100000000000) : ℝ) = ((100000000000 / 145331043577) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (34738247 / 1000000000) ≤ -Real.log (1545373119 / 1600000000) ∧
    -Real.log (1545373119 / 1600000000) ≤ (4342281 / 125000000) := by
  have h := checkLog_sound (w := (54626881 / 3145373119)) (n := 12)
    (lo := (34738247 / 1000000000)) (hi := (4342281 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600000000 / 1545373119) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1600000000 / 1545373119) = 1/(1545373119 / 1600000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-4342281 / 125000000) (-34738247 / 1000000000) (Real.log (1545373119 / 1600000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (8654363 / 250000000) ≤ -Real.log (965974877319 / 1000000000000) ∧
    -Real.log (965974877319 / 1000000000000) ≤ (34617453 / 1000000000) := by
  have h := checkLog_sound (w := (34025122681 / 1965974877319)) (n := 12)
    (lo := (8654363 / 250000000)) (hi := (34617453 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 965974877319) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 965974877319) = 1/(965974877319 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-34617453 / 1000000000) (-8654363 / 250000000) (Real.log (965974877319 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell188
