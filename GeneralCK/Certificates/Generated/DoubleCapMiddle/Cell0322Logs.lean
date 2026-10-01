import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0322
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

theorem reflection_log_1_neg : (27344869 / 125000000) ≤ -Real.log (1280 / 1593) ∧
    -Real.log (1280 / 1593) ≤ (218758953 / 1000000000) := by
  have h := checkLog_sound (w := (313 / 2873)) (n := 12)
    (lo := (27344869 / 125000000)) (hi := (218758953 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1593 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1593 / 1280) = 1/(1280 / 1593) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (27344869 / 125000000) (218758953 / 1000000000) (Real.log (1593 / 1280)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1593 / 1280) = -Real.log (1280 / 1593) := by
    rw [show ((1593 / 1280) : ℝ) = ((1280 / 1593) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (280416861 / 1000000000) ≤ -Real.log (967 / 1280) ∧
    -Real.log (967 / 1280) ≤ (140208431 / 500000000) := by
  have h := checkLog_sound (w := (313 / 2247)) (n := 12)
    (lo := (280416861 / 1000000000)) (hi := (140208431 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 967) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 967) = 1/(967 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-140208431 / 500000000) (-280416861 / 1000000000) (Real.log (967 / 1280)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (341443 / 1562500) ≤ -Real.log (10240 / 12741) ∧
    -Real.log (10240 / 12741) ≤ (218523521 / 1000000000) := by
  have h := checkLog_sound (w := (2501 / 22981)) (n := 12)
    (lo := (341443 / 1562500)) (hi := (218523521 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12741 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12741 / 10240) = 1/(10240 / 12741) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (341443 / 1562500) (218523521 / 1000000000) (Real.log (12741 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12741 / 10240) = -Real.log (10240 / 12741) := by
    rw [show ((12741 / 10240) : ℝ) = ((10240 / 12741) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (280029139 / 1000000000) ≤ -Real.log (7739 / 10240) ∧
    -Real.log (7739 / 10240) ≤ (14001457 / 50000000) := by
  have h := checkLog_sound (w := (2501 / 17979)) (n := 12)
    (lo := (280029139 / 1000000000)) (hi := (14001457 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7739) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7739) = 1/(7739 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-14001457 / 50000000) (-280029139 / 1000000000) (Real.log (7739 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (398146727 / 1000000000) ≤ -Real.log (640 / 953) ∧
    -Real.log (640 / 953) ≤ (49768341 / 125000000) := by
  have h := checkLog_sound (w := (313 / 1593)) (n := 12)
    (lo := (398146727 / 1000000000)) (hi := (49768341 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((953 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(953 / 640) = 1/(640 / 953) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (398146727 / 1000000000) (49768341 / 125000000) (Real.log (953 / 640)) := by
  have h := reflection_log_5_neg
  have he : Real.log (953 / 640) = -Real.log (640 / 953) := by
    rw [show ((953 / 640) : ℝ) = ((640 / 953) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (134301601 / 200000000) ≤ -Real.log (327 / 640) ∧
    -Real.log (327 / 640) ≤ (335754003 / 500000000) := by
  have h := checkLog_sound (w := (313 / 967)) (n := 12)
    (lo := (134301601 / 200000000)) (hi := (335754003 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 327) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 327) = 1/(327 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-335754003 / 500000000) (-134301601 / 200000000) (Real.log (327 / 640)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (79550631 / 200000000) ≤ -Real.log (5120 / 7621) ∧
    -Real.log (5120 / 7621) ≤ (99438289 / 250000000) := by
  have h := checkLog_sound (w := (2501 / 12741)) (n := 12)
    (lo := (79550631 / 200000000)) (hi := (99438289 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7621 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7621 / 5120) = 1/(5120 / 7621) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (79550631 / 200000000) (99438289 / 250000000) (Real.log (7621 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (7621 / 5120) = -Real.log (5120 / 7621) := by
    rw [show ((7621 / 5120) : ℝ) = ((5120 / 7621) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (670361873 / 1000000000) ≤ -Real.log (2619 / 5120) ∧
    -Real.log (2619 / 5120) ≤ (335180937 / 500000000) := by
  have h := checkLog_sound (w := (2501 / 7739)) (n := 12)
    (lo := (670361873 / 1000000000)) (hi := (335180937 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2619) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2619) = 1/(2619 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-335180937 / 500000000) (-670361873 / 1000000000) (Real.log (2619 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (299534059 / 1000000000) ≤ -Real.log (100000 / 134923) ∧
    -Real.log (100000 / 134923) ≤ (14976703 / 50000000) := by
  have h := checkLog_sound (w := (34923 / 234923)) (n := 12)
    (lo := (299534059 / 1000000000)) (hi := (14976703 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((134923 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(134923 / 100000) = 1/(100000 / 134923) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (299534059 / 1000000000) (14976703 / 50000000) (Real.log (134923 / 100000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (134923 / 100000) = -Real.log (100000 / 134923) := by
    rw [show ((134923 / 100000) : ℝ) = ((100000 / 134923) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (429599001 / 1000000000) ≤ -Real.log (65077 / 100000) ∧
    -Real.log (65077 / 100000) ≤ (214799501 / 500000000) := by
  have h := checkLog_sound (w := (34923 / 165077)) (n := 12)
    (lo := (429599001 / 1000000000)) (hi := (214799501 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 65077) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 65077) = 1/(65077 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-214799501 / 500000000) (-429599001 / 1000000000) (Real.log (65077 / 100000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (74963177 / 250000000) ≤ -Real.log (50000 / 67483) ∧
    -Real.log (50000 / 67483) ≤ (299852709 / 1000000000) := by
  have h := checkLog_sound (w := (17483 / 117483)) (n := 12)
    (lo := (74963177 / 250000000)) (hi := (299852709 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((67483 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(67483 / 50000) = 1/(50000 / 67483) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (74963177 / 250000000) (299852709 / 1000000000) (Real.log (67483 / 50000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (67483 / 50000) = -Real.log (50000 / 67483) := by
    rw [show ((67483 / 50000) : ℝ) = ((50000 / 67483) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (17210399 / 40000000) ≤ -Real.log (32517 / 50000) ∧
    -Real.log (32517 / 50000) ≤ (53782497 / 125000000) := by
  have h := checkLog_sound (w := (17483 / 82517)) (n := 12)
    (lo := (17210399 / 40000000)) (hi := (53782497 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 32517) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 32517) = 1/(32517 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-53782497 / 125000000) (-17210399 / 40000000) (Real.log (32517 / 50000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (227587263 / 1000000000) ≤ -Real.log (1000000 / 1255567) ∧
    -Real.log (1000000 / 1255567) ≤ (3556051 / 15625000) := by
  have h := checkLog_sound (w := (255567 / 2255567)) (n := 12)
    (lo := (227587263 / 1000000000)) (hi := (3556051 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1255567 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1255567 / 1000000) = 1/(1000000 / 1255567) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (227587263 / 1000000000) (3556051 / 15625000) (Real.log (1255567 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1255567 / 1000000) = -Real.log (1000000 / 1255567) := by
    rw [show ((1255567 / 1000000) : ℝ) = ((1000000 / 1255567) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (36891553 / 125000000) ≤ -Real.log (744433 / 1000000) ∧
    -Real.log (744433 / 1000000) ≤ (11805297 / 40000000) := by
  have h := checkLog_sound (w := (255567 / 1744433)) (n := 12)
    (lo := (36891553 / 125000000)) (hi := (11805297 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 744433) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 744433) = 1/(744433 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-11805297 / 40000000) (-36891553 / 125000000) (Real.log (744433 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (14240977 / 62500000) ≤ -Real.log (31250 / 39247) ∧
    -Real.log (31250 / 39247) ≤ (227855633 / 1000000000) := by
  have h := checkLog_sound (w := (7997 / 70497)) (n := 12)
    (lo := (14240977 / 62500000)) (hi := (227855633 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((39247 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(39247 / 31250) = 1/(31250 / 39247) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (14240977 / 62500000) (227855633 / 1000000000) (Real.log (39247 / 31250)) := by
  have h := reflection_log_15_neg
  have he : Real.log (39247 / 31250) = -Real.log (31250 / 39247) := by
    rw [show ((39247 / 31250) : ℝ) = ((31250 / 39247) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (14779261 / 50000000) ≤ -Real.log (23253 / 31250) ∧
    -Real.log (23253 / 31250) ≤ (295585221 / 1000000000) := by
  have h := checkLog_sound (w := (7997 / 54503)) (n := 12)
    (lo := (14779261 / 50000000)) (hi := (295585221 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 23253) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31250 / 23253) = 1/(23253 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-295585221 / 1000000000) (-14779261 / 50000000) (Real.log (23253 / 31250)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (36456653 / 50000000) ≤ -Real.log (500000000000 / 1036641209643) ∧
    -Real.log (500000000000 / 1036641209643) ≤ (364566531 / 500000000) := by
  have h := checkLog_sound (w := (36641209643 / 2036641209643)) (n := 12)
    (lo := (899647 / 25000000)) (hi := (35985881 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1036641209643 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1036641209643 / 1000000000000) = 1/(500000000000 / 1036641209643) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (36456653 / 50000000) (364566531 / 500000000) (Real.log (1036641209643 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1036641209643 / 500000000000) = -Real.log (500000000000 / 1036641209643) := by
    rw [show ((1036641209643 / 500000000000) : ℝ) = ((500000000000 / 1036641209643) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (182528171 / 250000000) ≤ -Real.log (125000000000 / 259414306363) ∧
    -Real.log (125000000000 / 259414306363) ≤ (365056343 / 500000000) := by
  have h := checkLog_sound (w := (9414306363 / 509414306363)) (n := 12)
    (lo := (288793 / 7812500)) (hi := (7393101 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((259414306363 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(259414306363 / 250000000000) = 1/(125000000000 / 259414306363) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (182528171 / 250000000) (365056343 / 500000000) (Real.log (259414306363 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (259414306363 / 125000000000) = -Real.log (125000000000 / 259414306363) := by
    rw [show ((259414306363 / 125000000000) : ℝ) = ((125000000000 / 259414306363) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (522719687 / 1000000000) ≤ -Real.log (100000000000 / 168660846577) ∧
    -Real.log (100000000000 / 168660846577) ≤ (65339961 / 125000000) := by
  have h := checkLog_sound (w := (68660846577 / 268660846577)) (n := 12)
    (lo := (522719687 / 1000000000)) (hi := (65339961 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((168660846577 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(168660846577 / 100000000000) = 1/(100000000000 / 168660846577) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (522719687 / 1000000000) (65339961 / 125000000) (Real.log (168660846577 / 100000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (168660846577 / 100000000000) = -Real.log (100000000000 / 168660846577) := by
    rw [show ((168660846577 / 100000000000) : ℝ) = ((100000000000 / 168660846577) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (130860213 / 250000000) ≤ -Real.log (500000000000 / 843912613427) ∧
    -Real.log (500000000000 / 843912613427) ≤ (523440853 / 1000000000) := by
  have h := checkLog_sound (w := (343912613427 / 1343912613427)) (n := 12)
    (lo := (130860213 / 250000000)) (hi := (523440853 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((843912613427 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(843912613427 / 500000000000) = 1/(500000000000 / 843912613427) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (130860213 / 250000000) (523440853 / 1000000000) (Real.log (843912613427 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (843912613427 / 500000000000) = -Real.log (500000000000 / 843912613427) := by
    rw [show ((843912613427 / 500000000000) : ℝ) = ((500000000000 / 843912613427) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0322
