import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0095
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

theorem reflection_log_1_neg : (672356369 / 1000000000) ≤ -Real.log (51200 / 100293) ∧
    -Real.log (51200 / 100293) ≤ (67235637 / 100000000) := by
  have h := checkLog_sound (w := (49093 / 151493)) (n := 12)
    (lo := (672356369 / 1000000000)) (hi := (67235637 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100293 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100293 / 51200) = 1/(51200 / 100293) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (672356369 / 1000000000) (67235637 / 100000000) (Real.log (100293 / 51200)) := by
  have h := reflection_log_1_neg
  have he : Real.log (100293 / 51200) = -Real.log (51200 / 100293) := by
    rw [show ((100293 / 51200) : ℝ) = ((51200 / 100293) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (1595237197 / 500000000) ≤ -Real.log (2107 / 51200) ∧
    -Real.log (2107 / 51200) ≤ (3190474399 / 1000000000) := by
  have h := checkLog_sound (w := (1093 / 5307)) (n := 12)
    (lo := (208942837 / 500000000)) (hi := (16715427 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2107) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3200 / 2107) = 1/(2107 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-3190474399 / 1000000000) (-1595237197 / 500000000) (Real.log (2107 / 51200)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (336083453 / 500000000) ≤ -Real.log (25600 / 50137) ∧
    -Real.log (25600 / 50137) ≤ (672166907 / 1000000000) := by
  have h := checkLog_sound (w := (24537 / 75737)) (n := 12)
    (lo := (336083453 / 500000000)) (hi := (672166907 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50137 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50137 / 25600) = 1/(25600 / 50137) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (336083453 / 500000000) (672166907 / 1000000000) (Real.log (50137 / 25600)) := by
  have h := reflection_log_3_neg
  have he : Real.log (50137 / 25600) = -Real.log (25600 / 50137) := by
    rw [show ((50137 / 25600) : ℝ) = ((25600 / 50137) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (3181497249 / 1000000000) ≤ -Real.log (1063 / 25600) ∧
    -Real.log (1063 / 25600) ≤ (1590748627 / 500000000) := by
  have h := checkLog_sound (w := (537 / 2663)) (n := 12)
    (lo := (408908529 / 1000000000)) (hi := (40890853 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1063) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1600 / 1063) = 1/(1063 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-1590748627 / 500000000) (-3181497249 / 1000000000) (Real.log (1063 / 25600)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (325562053 / 500000000) ≤ -Real.log (25600 / 49093) ∧
    -Real.log (25600 / 49093) ≤ (651124107 / 1000000000) := by
  have h := checkLog_sound (w := (23493 / 74693)) (n := 12)
    (lo := (325562053 / 500000000)) (hi := (651124107 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49093 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49093 / 25600) = 1/(25600 / 49093) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (325562053 / 500000000) (651124107 / 1000000000) (Real.log (49093 / 25600)) := by
  have h := reflection_log_5_neg
  have he : Real.log (49093 / 25600) = -Real.log (25600 / 49093) := by
    rw [show ((49093 / 25600) : ℝ) = ((25600 / 49093) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1248663607 / 500000000) ≤ -Real.log (2107 / 25600) ∧
    -Real.log (2107 / 25600) ≤ (1248663609 / 500000000) := by
  have h := checkLog_sound (w := (1093 / 5307)) (n := 12)
    (lo := (208942837 / 500000000)) (hi := (16715427 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2107) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(3200 / 2107) = 1/(2107 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1248663609 / 500000000) (-1248663607 / 500000000) (Real.log (2107 / 25600)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (650737011 / 1000000000) ≤ -Real.log (12800 / 24537) ∧
    -Real.log (12800 / 24537) ≤ (162684253 / 250000000) := by
  have h := checkLog_sound (w := (11737 / 37337)) (n := 12)
    (lo := (650737011 / 1000000000)) (hi := (162684253 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24537 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24537 / 12800) = 1/(12800 / 24537) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (650737011 / 1000000000) (162684253 / 250000000) (Real.log (24537 / 12800)) := by
  have h := reflection_log_7_neg
  have he : Real.log (24537 / 12800) = -Real.log (12800 / 24537) := by
    rw [show ((24537 / 12800) : ℝ) = ((12800 / 24537) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (2488350069 / 1000000000) ≤ -Real.log (1063 / 12800) ∧
    -Real.log (1063 / 12800) ≤ (2488350073 / 1000000000) := by
  have h := checkLog_sound (w := (537 / 2663)) (n := 12)
    (lo := (408908529 / 1000000000)) (hi := (40890853 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1063) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1600 / 1063) = 1/(1063 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-2488350073 / 1000000000) (-2488350069 / 1000000000) (Real.log (1063 / 12800)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (675936421 / 1000000000) ≤ -Real.log (1000000 / 1965873) ∧
    -Real.log (1000000 / 1965873) ≤ (337968211 / 500000000) := by
  have h := checkLog_sound (w := (965873 / 2965873)) (n := 12)
    (lo := (675936421 / 1000000000)) (hi := (337968211 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1965873 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1965873 / 1000000) = 1/(1000000 / 1965873) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (675936421 / 1000000000) (337968211 / 500000000) (Real.log (1965873 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1965873 / 1000000) = -Real.log (1000000 / 1965873) := by
    rw [show ((1965873 / 1000000) : ℝ) = ((1000000 / 1965873) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (211104151 / 62500000) ≤ -Real.log (34127 / 1000000) ∧
    -Real.log (34127 / 1000000) ≤ (3377666421 / 1000000000) := by
  have h := checkLog_sound (w := (28373 / 96627)) (n := 12)
    (lo := (9454339 / 15625000)) (hi := (605077697 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 34127) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 34127) = 1/(34127 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-3377666421 / 1000000000) (-211104151 / 62500000) (Real.log (34127 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (676083419 / 1000000000) ≤ -Real.log (500000 / 983081) ∧
    -Real.log (500000 / 983081) ≤ (33804171 / 50000000) := by
  have h := checkLog_sound (w := (483081 / 1483081)) (n := 12)
    (lo := (676083419 / 1000000000)) (hi := (33804171 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((983081 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(983081 / 500000) = 1/(500000 / 983081) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (676083419 / 1000000000) (33804171 / 50000000) (Real.log (983081 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (983081 / 500000) = -Real.log (500000 / 983081) := by
    rw [show ((983081 / 500000) : ℝ) = ((500000 / 983081) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (677234169 / 200000000) ≤ -Real.log (16919 / 500000) ∧
    -Real.log (16919 / 500000) ≤ (67723417 / 20000000) := by
  have h := checkLog_sound (w := (14331 / 48169)) (n := 12)
    (lo := (4908657 / 8000000)) (hi := (306791063 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 16919) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(31250 / 16919) = 1/(16919 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-67723417 / 20000000) (-677234169 / 200000000) (Real.log (16919 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (337888087 / 500000000) ≤ -Real.log (500000 / 982779) ∧
    -Real.log (500000 / 982779) ≤ (27031047 / 40000000) := by
  have h := checkLog_sound (w := (482779 / 1482779)) (n := 12)
    (lo := (337888087 / 500000000)) (hi := (27031047 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((982779 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(982779 / 500000) = 1/(500000 / 982779) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (337888087 / 500000000) (27031047 / 40000000) (Real.log (982779 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (982779 / 500000) = -Real.log (500000 / 982779) := by
    rw [show ((982779 / 500000) : ℝ) = ((500000 / 982779) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (1684239263 / 500000000) ≤ -Real.log (17221 / 500000) ∧
    -Real.log (17221 / 500000) ≤ (3368478531 / 1000000000) := by
  have h := checkLog_sound (w := (14029 / 48471)) (n := 12)
    (lo := (297944903 / 500000000)) (hi := (595889807 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 17221) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(31250 / 17221) = 1/(17221 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-3368478531 / 1000000000) (-1684239263 / 500000000) (Real.log (17221 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (675926247 / 1000000000) ≤ -Real.log (1000000 / 1965853) ∧
    -Real.log (1000000 / 1965853) ≤ (84490781 / 125000000) := by
  have h := checkLog_sound (w := (965853 / 2965853)) (n := 12)
    (lo := (675926247 / 1000000000)) (hi := (84490781 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1965853 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1965853 / 1000000) = 1/(1000000 / 1965853) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (675926247 / 1000000000) (84490781 / 125000000) (Real.log (1965853 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1965853 / 1000000) = -Real.log (1000000 / 1965853) := by
    rw [show ((1965853 / 1000000) : ℝ) = ((1000000 / 1965853) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (1688540271 / 500000000) ≤ -Real.log (34147 / 1000000) ∧
    -Real.log (34147 / 1000000) ≤ (3377080547 / 1000000000) := by
  have h := checkLog_sound (w := (28353 / 96647)) (n := 12)
    (lo := (302245911 / 500000000)) (hi := (604491823 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 34147) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 34147) = 1/(34147 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-3377080547 / 1000000000) (-1688540271 / 500000000) (Real.log (34147 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (4053602837 / 1000000000) ≤ -Real.log (500000000000 / 28802311952413) ∧
    -Real.log (500000000000 / 28802311952413) ≤ (4053602843 / 1000000000) := by
  have h := checkLog_sound (w := (12802311952413 / 44802311952413)) (n := 12)
    (lo := (587866937 / 1000000000)) (hi := (293933469 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((28802311952413 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(28802311952413 / 16000000000000) = 1/(500000000000 / 28802311952413) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (4053602837 / 1000000000) (4053602843 / 1000000000) (Real.log (28802311952413 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (28802311952413 / 500000000000) = -Real.log (500000000000 / 28802311952413) := by
    rw [show ((28802311952413 / 500000000000) : ℝ) = ((500000000000 / 28802311952413) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (4062254263 / 1000000000) ≤ -Real.log (250000000000 / 14526287014599) ∧
    -Real.log (250000000000 / 14526287014599) ≤ (4062254269 / 1000000000) := by
  have h := checkLog_sound (w := (6526287014599 / 22526287014599)) (n := 12)
    (lo := (596518363 / 1000000000)) (hi := (149129591 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((14526287014599 / 8000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(14526287014599 / 8000000000000) = 1/(250000000000 / 14526287014599) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (4062254263 / 1000000000) (4062254269 / 1000000000) (Real.log (14526287014599 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (14526287014599 / 250000000000) = -Real.log (250000000000 / 14526287014599) := by
    rw [show ((14526287014599 / 250000000000) : ℝ) = ((250000000000 / 14526287014599) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (40442547 / 10000000) ≤ -Real.log (500000000000 / 28534318564543) ∧
    -Real.log (500000000000 / 28534318564543) ≤ (2022127353 / 500000000) := by
  have h := checkLog_sound (w := (12534318564543 / 44534318564543)) (n := 12)
    (lo := (1446297 / 2500000)) (hi := (578518801 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((28534318564543 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(28534318564543 / 16000000000000) = 1/(500000000000 / 28534318564543) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (40442547 / 10000000) (2022127353 / 500000000) (Real.log (28534318564543 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (28534318564543 / 500000000000) = -Real.log (500000000000 / 28534318564543) := by
    rw [show ((28534318564543 / 500000000000) : ℝ) = ((500000000000 / 28534318564543) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (4053006789 / 1000000000) ≤ -Real.log (500000000000 / 28785149500689) ∧
    -Real.log (500000000000 / 28785149500689) ≤ (810601359 / 200000000) := by
  have h := checkLog_sound (w := (12785149500689 / 44785149500689)) (n := 12)
    (lo := (587270889 / 1000000000)) (hi := (58727089 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((28785149500689 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(28785149500689 / 16000000000000) = 1/(500000000000 / 28785149500689) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (4053006789 / 1000000000) (810601359 / 200000000) (Real.log (28785149500689 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (28785149500689 / 500000000000) = -Real.log (500000000000 / 28785149500689) := by
    rw [show ((28785149500689 / 500000000000) : ℝ) = ((500000000000 / 28785149500689) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0095
