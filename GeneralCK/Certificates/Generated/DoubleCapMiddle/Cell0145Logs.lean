import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0145
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

theorem reflection_log_1_neg : (36860331 / 125000000) ≤ -Real.log (1280 / 1719) ∧
    -Real.log (1280 / 1719) ≤ (294882649 / 1000000000) := by
  have h := checkLog_sound (w := (439 / 2999)) (n := 12)
    (lo := (36860331 / 125000000)) (hi := (294882649 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1719 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1719 / 1280) = 1/(1280 / 1719) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (36860331 / 125000000) (294882649 / 1000000000) (Real.log (1719 / 1280)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1719 / 1280) = -Real.log (1280 / 1719) := by
    rw [show ((1719 / 1280) : ℝ) = ((1280 / 1719) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (26251481 / 62500000) ≤ -Real.log (841 / 1280) ∧
    -Real.log (841 / 1280) ≤ (420023697 / 1000000000) := by
  have h := checkLog_sound (w := (439 / 2121)) (n := 12)
    (lo := (26251481 / 62500000)) (hi := (420023697 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 841) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 841) = 1/(841 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-420023697 / 1000000000) (-26251481 / 62500000) (Real.log (841 / 1280)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (294009667 / 1000000000) ≤ -Real.log (512 / 687) ∧
    -Real.log (512 / 687) ≤ (73502417 / 250000000) := by
  have h := checkLog_sound (w := (175 / 1199)) (n := 12)
    (lo := (294009667 / 1000000000)) (hi := (73502417 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((687 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(687 / 512) = 1/(512 / 687) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (294009667 / 1000000000) (73502417 / 250000000) (Real.log (687 / 512)) := by
  have h := reflection_log_3_neg
  have he : Real.log (687 / 512) = -Real.log (512 / 687) := by
    rw [show ((687 / 512) : ℝ) = ((512 / 687) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (209120847 / 500000000) ≤ -Real.log (337 / 512) ∧
    -Real.log (337 / 512) ≤ (83648339 / 200000000) := by
  have h := checkLog_sound (w := (175 / 849)) (n := 12)
    (lo := (209120847 / 500000000)) (hi := (83648339 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 337) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 337) = 1/(337 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-83648339 / 200000000) (-209120847 / 500000000) (Real.log (337 / 512)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (130580447 / 250000000) ≤ -Real.log (640 / 1079) ∧
    -Real.log (640 / 1079) ≤ (522321789 / 1000000000) := by
  have h := checkLog_sound (w := (439 / 1719)) (n := 12)
    (lo := (130580447 / 250000000)) (hi := (522321789 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1079 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1079 / 640) = 1/(640 / 1079) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (130580447 / 250000000) (522321789 / 1000000000) (Real.log (1079 / 640)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1079 / 640) = -Real.log (640 / 1079) := by
    rw [show ((1079 / 640) : ℝ) = ((640 / 1079) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1158163267 / 1000000000) ≤ -Real.log (201 / 640) ∧
    -Real.log (201 / 640) ≤ (1158163269 / 1000000000) := by
  have h := checkLog_sound (w := (119 / 521)) (n := 12)
    (lo := (465016087 / 1000000000)) (hi := (58127011 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 201) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(320 / 201) = 1/(201 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1158163269 / 1000000000) (-1158163267 / 1000000000) (Real.log (201 / 640)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (104186129 / 200000000) ≤ -Real.log (256 / 431) ∧
    -Real.log (256 / 431) ≤ (260465323 / 500000000) := by
  have h := checkLog_sound (w := (175 / 687)) (n := 12)
    (lo := (104186129 / 200000000)) (hi := (260465323 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((431 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(431 / 256) = 1/(256 / 431) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (104186129 / 200000000) (260465323 / 500000000) (Real.log (431 / 256)) := by
  have h := reflection_log_7_neg
  have he : Real.log (431 / 256) = -Real.log (256 / 431) := by
    rw [show ((431 / 256) : ℝ) = ((256 / 431) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (1150728289 / 1000000000) ≤ -Real.log (81 / 256) ∧
    -Real.log (81 / 256) ≤ (1150728291 / 1000000000) := by
  have h := checkLog_sound (w := (47 / 209)) (n := 12)
    (lo := (457581109 / 1000000000)) (hi := (45758111 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((128 / 81) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(128 / 81) = 1/(81 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1150728291 / 1000000000) (-1150728289 / 1000000000) (Real.log (81 / 256)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (10057837 / 25000000) ≤ -Real.log (12500 / 18691) ∧
    -Real.log (12500 / 18691) ≤ (402313481 / 1000000000) := by
  have h := checkLog_sound (w := (6191 / 31191)) (n := 12)
    (lo := (10057837 / 25000000)) (hi := (402313481 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((18691 / 12500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(18691 / 12500) = 1/(12500 / 18691) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (10057837 / 25000000) (402313481 / 1000000000) (Real.log (18691 / 12500)) := by
  have h := reflection_log_9_neg
  have he : Real.log (18691 / 12500) = -Real.log (12500 / 18691) := by
    rw [show ((18691 / 12500) : ℝ) = ((12500 / 18691) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (341875729 / 500000000) ≤ -Real.log (6309 / 12500) ∧
    -Real.log (6309 / 12500) ≤ (683751459 / 1000000000) := by
  have h := checkLog_sound (w := (6191 / 18809)) (n := 12)
    (lo := (341875729 / 500000000)) (hi := (683751459 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12500 / 6309) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12500 / 6309) = 1/(6309 / 12500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-683751459 / 1000000000) (-341875729 / 500000000) (Real.log (6309 / 12500)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (50440069 / 125000000) ≤ -Real.log (500000 / 748543) ∧
    -Real.log (500000 / 748543) ≤ (403520553 / 1000000000) := by
  have h := checkLog_sound (w := (248543 / 1248543)) (n := 12)
    (lo := (50440069 / 125000000)) (hi := (403520553 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((748543 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(748543 / 500000) = 1/(500000 / 748543) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (50440069 / 125000000) (403520553 / 1000000000) (Real.log (748543 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (748543 / 500000) = -Real.log (500000 / 748543) := by
    rw [show ((748543 / 500000) : ℝ) = ((500000 / 748543) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (687336097 / 1000000000) ≤ -Real.log (251457 / 500000) ∧
    -Real.log (251457 / 500000) ≤ (343668049 / 500000000) := by
  have h := checkLog_sound (w := (248543 / 751457)) (n := 12)
    (lo := (687336097 / 1000000000)) (hi := (343668049 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 251457) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 251457) = 1/(251457 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-343668049 / 500000000) (-687336097 / 1000000000) (Real.log (251457 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (79728497 / 250000000) ≤ -Real.log (1000000 / 1375633) ∧
    -Real.log (1000000 / 1375633) ≤ (318913989 / 1000000000) := by
  have h := checkLog_sound (w := (375633 / 2375633)) (n := 12)
    (lo := (79728497 / 250000000)) (hi := (318913989 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1375633 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1375633 / 1000000) = 1/(1000000 / 1375633) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (79728497 / 250000000) (318913989 / 1000000000) (Real.log (1375633 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1375633 / 1000000) = -Real.log (1000000 / 1375633) := by
    rw [show ((1375633 / 1000000) : ℝ) = ((1000000 / 1375633) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (235508471 / 500000000) ≤ -Real.log (624367 / 1000000) ∧
    -Real.log (624367 / 1000000) ≤ (471016943 / 1000000000) := by
  have h := checkLog_sound (w := (375633 / 1624367)) (n := 12)
    (lo := (235508471 / 500000000)) (hi := (471016943 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 624367) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 624367) = 1/(624367 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-471016943 / 1000000000) (-235508471 / 500000000) (Real.log (624367 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (160026589 / 500000000) ≤ -Real.log (1000000 / 1377201) ∧
    -Real.log (1000000 / 1377201) ≤ (320053179 / 1000000000) := by
  have h := checkLog_sound (w := (377201 / 2377201)) (n := 12)
    (lo := (160026589 / 500000000)) (hi := (320053179 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1377201 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1377201 / 1000000) = 1/(1000000 / 1377201) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (160026589 / 500000000) (320053179 / 1000000000) (Real.log (1377201 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1377201 / 1000000) = -Real.log (1000000 / 1377201) := by
    rw [show ((1377201 / 1000000) : ℝ) = ((1000000 / 1377201) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (118382861 / 250000000) ≤ -Real.log (622799 / 1000000) ∧
    -Real.log (622799 / 1000000) ≤ (94706289 / 200000000) := by
  have h := checkLog_sound (w := (377201 / 1622799)) (n := 12)
    (lo := (118382861 / 250000000)) (hi := (94706289 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 622799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 622799) = 1/(622799 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-94706289 / 200000000) (-118382861 / 250000000) (Real.log (622799 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (543032469 / 500000000) ≤ -Real.log (500000000000 / 1481296560469) ∧
    -Real.log (500000000000 / 1481296560469) ≤ (54303247 / 50000000) := by
  have h := checkLog_sound (w := (481296560469 / 2481296560469)) (n := 12)
    (lo := (196458879 / 500000000)) (hi := (392917759 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1481296560469 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1481296560469 / 1000000000000) = 1/(500000000000 / 1481296560469) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (543032469 / 500000000) (54303247 / 50000000) (Real.log (1481296560469 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1481296560469 / 500000000000) = -Real.log (500000000000 / 1481296560469) := by
    rw [show ((1481296560469 / 500000000000) : ℝ) = ((500000000000 / 1481296560469) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1090856649 / 1000000000) ≤ -Real.log (12500000000 / 37210288439) ∧
    -Real.log (12500000000 / 37210288439) ≤ (1090856651 / 1000000000) := by
  have h := checkLog_sound (w := (12210288439 / 62210288439)) (n := 12)
    (lo := (397709469 / 1000000000)) (hi := (39770947 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((37210288439 / 25000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(37210288439 / 25000000000) = 1/(12500000000 / 37210288439) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1090856649 / 1000000000) (1090856651 / 1000000000) (Real.log (37210288439 / 12500000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (37210288439 / 12500000000) = -Real.log (12500000000 / 37210288439) := by
    rw [show ((37210288439 / 12500000000) : ℝ) = ((12500000000 / 37210288439) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (78993093 / 100000000) ≤ -Real.log (250000000000 / 550811061443) ∧
    -Real.log (250000000000 / 550811061443) ≤ (197482733 / 250000000) := by
  have h := checkLog_sound (w := (50811061443 / 1050811061443)) (n := 12)
    (lo := (77427 / 800000)) (hi := (96783751 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((550811061443 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(550811061443 / 500000000000) = 1/(250000000000 / 550811061443) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (78993093 / 100000000) (197482733 / 250000000) (Real.log (550811061443 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (550811061443 / 250000000000) = -Real.log (250000000000 / 550811061443) := by
    rw [show ((550811061443 / 250000000000) : ℝ) = ((250000000000 / 550811061443) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (396792311 / 500000000) ≤ -Real.log (62500000000 / 138206809099) ∧
    -Real.log (62500000000 / 138206809099) ≤ (49599039 / 62500000) := by
  have h := checkLog_sound (w := (13206809099 / 263206809099)) (n := 12)
    (lo := (50218721 / 500000000)) (hi := (100437443 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((138206809099 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(138206809099 / 125000000000) = 1/(62500000000 / 138206809099) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (396792311 / 500000000) (49599039 / 62500000) (Real.log (138206809099 / 62500000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (138206809099 / 62500000000) = -Real.log (62500000000 / 138206809099) := by
    rw [show ((138206809099 / 62500000000) : ℝ) = ((62500000000 / 138206809099) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0145
