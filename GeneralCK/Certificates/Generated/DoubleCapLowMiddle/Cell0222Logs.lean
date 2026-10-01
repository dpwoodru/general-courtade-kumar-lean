import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0222
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

theorem reflection_log_1_neg : (513571849 / 1000000000) ≤ -Real.log (800 / 1337) ∧
    -Real.log (800 / 1337) ≤ (10271437 / 20000000) := by
  have h := checkLog_sound (w := (537 / 2137)) (n := 12)
    (lo := (513571849 / 1000000000)) (hi := (10271437 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1337 / 800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1337 / 800) = 1/(800 / 1337) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (513571849 / 1000000000) (10271437 / 20000000) (Real.log (1337 / 800)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1337 / 800) = -Real.log (800 / 1337) := by
    rw [show ((1337 / 800) : ℝ) = ((800 / 1337) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (556228847 / 500000000) ≤ -Real.log (263 / 800) ∧
    -Real.log (263 / 800) ≤ (34764303 / 31250000) := by
  have h := checkLog_sound (w := (137 / 663)) (n := 12)
    (lo := (209655257 / 500000000)) (hi := (83862103 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 263) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(400 / 263) = 1/(263 / 800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-34764303 / 31250000) (-556228847 / 500000000) (Real.log (263 / 800)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (20257641 / 40000000) ≤ -Real.log (320 / 531) ∧
    -Real.log (320 / 531) ≤ (253220513 / 500000000) := by
  have h := checkLog_sound (w := (211 / 851)) (n := 12)
    (lo := (20257641 / 40000000)) (hi := (253220513 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((531 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(531 / 320) = 1/(320 / 531) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (20257641 / 40000000) (253220513 / 500000000) (Real.log (531 / 320)) := by
  have h := reflection_log_3_neg
  have he : Real.log (531 / 320) = -Real.log (320 / 531) := by
    rw [show ((531 / 320) : ℝ) = ((320 / 531) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (1076973113 / 1000000000) ≤ -Real.log (109 / 320) ∧
    -Real.log (109 / 320) ≤ (215394623 / 200000000) := by
  have h := checkLog_sound (w := (51 / 269)) (n := 12)
    (lo := (383825933 / 1000000000)) (hi := (191912967 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 109) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(160 / 109) = 1/(109 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-215394623 / 200000000) (-1076973113 / 1000000000) (Real.log (109 / 320)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (294533547 / 1000000000) ≤ -Real.log (400 / 537) ∧
    -Real.log (400 / 537) ≤ (73633387 / 250000000) := by
  have h := checkLog_sound (w := (137 / 937)) (n := 12)
    (lo := (294533547 / 1000000000)) (hi := (73633387 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((537 / 400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(537 / 400) = 1/(400 / 537) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (294533547 / 1000000000) (73633387 / 250000000) (Real.log (537 / 400)) := by
  have h := reflection_log_5_neg
  have he : Real.log (537 / 400) = -Real.log (400 / 537) := by
    rw [show ((537 / 400) : ℝ) = ((400 / 537) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (209655257 / 500000000) ≤ -Real.log (263 / 400) ∧
    -Real.log (263 / 400) ≤ (83862103 / 200000000) := by
  have h := checkLog_sound (w := (137 / 663)) (n := 12)
    (lo := (209655257 / 500000000)) (hi := (83862103 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 263) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400 / 263) = 1/(263 / 400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-83862103 / 200000000) (-209655257 / 500000000) (Real.log (263 / 400)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (138342159 / 500000000) ≤ -Real.log (160 / 211) ∧
    -Real.log (160 / 211) ≤ (276684319 / 1000000000) := by
  have h := checkLog_sound (w := (51 / 371)) (n := 12)
    (lo := (138342159 / 500000000)) (hi := (276684319 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((211 / 160) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(211 / 160) = 1/(160 / 211) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (138342159 / 500000000) (276684319 / 1000000000) (Real.log (211 / 160)) := by
  have h := reflection_log_7_neg
  have he : Real.log (211 / 160) = -Real.log (160 / 211) := by
    rw [show ((211 / 160) : ℝ) = ((160 / 211) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (383825933 / 1000000000) ≤ -Real.log (109 / 160) ∧
    -Real.log (109 / 160) ≤ (191912967 / 500000000) := by
  have h := checkLog_sound (w := (51 / 269)) (n := 12)
    (lo := (383825933 / 1000000000)) (hi := (191912967 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 109) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(160 / 109) = 1/(109 / 160) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-191912967 / 500000000) (-383825933 / 1000000000) (Real.log (109 / 160)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (294988521 / 500000000) ≤ -Real.log (1000000 / 1803947) ∧
    -Real.log (1000000 / 1803947) ≤ (589977043 / 1000000000) := by
  have h := checkLog_sound (w := (803947 / 2803947)) (n := 12)
    (lo := (294988521 / 500000000)) (hi := (589977043 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1803947 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1803947 / 1000000) = 1/(1000000 / 1803947) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (294988521 / 500000000) (589977043 / 1000000000) (Real.log (1803947 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1803947 / 1000000) = -Real.log (1000000 / 1803947) := by
    rw [show ((1803947 / 1000000) : ℝ) = ((1000000 / 1803947) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (1629370247 / 1000000000) ≤ -Real.log (196053 / 1000000) ∧
    -Real.log (196053 / 1000000) ≤ (6517481 / 4000000) := by
  have h := checkLog_sound (w := (53947 / 446053)) (n := 12)
    (lo := (243075887 / 1000000000)) (hi := (15192243 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 196053) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(250000 / 196053) = 1/(196053 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-6517481 / 4000000) (-1629370247 / 1000000000) (Real.log (196053 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (592003871 / 1000000000) ≤ -Real.log (1000000 / 1807607) ∧
    -Real.log (1000000 / 1807607) ≤ (18500121 / 31250000) := by
  have h := checkLog_sound (w := (807607 / 2807607)) (n := 12)
    (lo := (592003871 / 1000000000)) (hi := (18500121 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1807607 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1807607 / 1000000) = 1/(1000000 / 1807607) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (592003871 / 1000000000) (18500121 / 31250000) (Real.log (1807607 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1807607 / 1000000) = -Real.log (1000000 / 1807607) := by
    rw [show ((1807607 / 1000000) : ℝ) = ((1000000 / 1807607) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (824107561 / 500000000) ≤ -Real.log (192393 / 1000000) ∧
    -Real.log (192393 / 1000000) ≤ (13185721 / 8000000) := by
  have h := checkLog_sound (w := (57607 / 442393)) (n := 12)
    (lo := (130960381 / 500000000)) (hi := (261920763 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 192393) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(250000 / 192393) = 1/(192393 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-13185721 / 8000000) (-824107561 / 500000000) (Real.log (192393 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (141064961 / 250000000) ≤ -Real.log (500000 / 879073) ∧
    -Real.log (500000 / 879073) ≤ (112851969 / 200000000) := by
  have h := checkLog_sound (w := (379073 / 1379073)) (n := 12)
    (lo := (141064961 / 250000000)) (hi := (112851969 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((879073 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(879073 / 500000) = 1/(500000 / 879073) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (141064961 / 250000000) (112851969 / 200000000) (Real.log (879073 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (879073 / 500000) = -Real.log (500000 / 879073) := by
    rw [show ((879073 / 500000) : ℝ) = ((500000 / 879073) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (1419421039 / 1000000000) ≤ -Real.log (120927 / 500000) ∧
    -Real.log (120927 / 500000) ≤ (709710521 / 500000000) := by
  have h := checkLog_sound (w := (4073 / 245927)) (n := 12)
    (lo := (33126679 / 1000000000)) (hi := (828167 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 120927) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(125000 / 120927) = 1/(120927 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-709710521 / 500000000) (-1419421039 / 1000000000) (Real.log (120927 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (56855061 / 100000000) ≤ -Real.log (500000 / 882853) ∧
    -Real.log (500000 / 882853) ≤ (568550611 / 1000000000) := by
  have h := checkLog_sound (w := (382853 / 1382853)) (n := 12)
    (lo := (56855061 / 100000000)) (hi := (568550611 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((882853 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(882853 / 500000) = 1/(500000 / 882853) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (56855061 / 100000000) (568550611 / 1000000000) (Real.log (882853 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (882853 / 500000) = -Real.log (500000 / 882853) := by
    rw [show ((882853 / 500000) : ℝ) = ((500000 / 882853) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (72558927 / 50000000) ≤ -Real.log (117147 / 500000) ∧
    -Real.log (117147 / 500000) ≤ (1451178543 / 1000000000) := by
  have h := checkLog_sound (w := (7853 / 242147)) (n := 12)
    (lo := (3244209 / 50000000)) (hi := (64884181 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 117147) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(125000 / 117147) = 1/(117147 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-1451178543 / 1000000000) (-72558927 / 50000000) (Real.log (117147 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (277418411 / 125000000) ≤ -Real.log (500000000000 / 4600661555803) ∧
    -Real.log (500000000000 / 4600661555803) ≤ (554836823 / 250000000) := by
  have h := checkLog_sound (w := (600661555803 / 8600661555803)) (n := 12)
    (lo := (34976437 / 250000000)) (hi := (139905749 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4600661555803 / 4000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(4600661555803 / 4000000000000) = 1/(500000000000 / 4600661555803) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (277418411 / 125000000) (554836823 / 250000000) (Real.log (4600661555803 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (4600661555803 / 500000000000) = -Real.log (500000000000 / 4600661555803) := by
    rw [show ((4600661555803 / 500000000000) : ℝ) = ((500000000000 / 4600661555803) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (2240218993 / 1000000000) ≤ -Real.log (62500000000 / 587211787851) ∧
    -Real.log (62500000000 / 587211787851) ≤ (2240218997 / 1000000000) := by
  have h := checkLog_sound (w := (87211787851 / 1087211787851)) (n := 12)
    (lo := (160777453 / 1000000000)) (hi := (80388727 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((587211787851 / 500000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(587211787851 / 500000000000) = 1/(62500000000 / 587211787851) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (2240218993 / 1000000000) (2240218997 / 1000000000) (Real.log (587211787851 / 62500000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (587211787851 / 62500000000) = -Real.log (62500000000 / 587211787851) := by
    rw [show ((587211787851 / 62500000000) : ℝ) = ((62500000000 / 587211787851) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (495920221 / 250000000) ≤ -Real.log (500000000000 / 3634725909019) ∧
    -Real.log (500000000000 / 3634725909019) ≤ (1983680887 / 1000000000) := by
  have h := checkLog_sound (w := (1634725909019 / 5634725909019)) (n := 12)
    (lo := (149346631 / 250000000)) (hi := (23895461 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3634725909019 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(3634725909019 / 2000000000000) = 1/(500000000000 / 3634725909019) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (495920221 / 250000000) (1983680887 / 1000000000) (Real.log (3634725909019 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (3634725909019 / 500000000000) = -Real.log (500000000000 / 3634725909019) := by
    rw [show ((3634725909019 / 500000000000) : ℝ) = ((500000000000 / 3634725909019) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (2019729151 / 1000000000) ≤ -Real.log (500000000000 / 3768141736451) ∧
    -Real.log (500000000000 / 3768141736451) ≤ (1009864577 / 500000000) := by
  have h := checkLog_sound (w := (1768141736451 / 5768141736451)) (n := 12)
    (lo := (633434791 / 1000000000)) (hi := (79179349 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3768141736451 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(3768141736451 / 2000000000000) = 1/(500000000000 / 3768141736451) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (2019729151 / 1000000000) (1009864577 / 500000000) (Real.log (3768141736451 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (3768141736451 / 500000000000) = -Real.log (500000000000 / 3768141736451) := by
    rw [show ((3768141736451 / 500000000000) : ℝ) = ((500000000000 / 3768141736451) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0222
