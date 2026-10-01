import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0286
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

theorem reflection_log_1_neg : (227197821 / 1000000000) ≤ -Real.log (2560 / 3213) ∧
    -Real.log (2560 / 3213) ≤ (113598911 / 500000000) := by
  have h := checkLog_sound (w := (653 / 5773)) (n := 12)
    (lo := (227197821 / 1000000000)) (hi := (113598911 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3213 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3213 / 2560) = 1/(2560 / 3213) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (227197821 / 1000000000) (113598911 / 500000000) (Real.log (3213 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3213 / 2560) = -Real.log (2560 / 3213) := by
    rw [show ((3213 / 2560) : ℝ) = ((2560 / 3213) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (294475931 / 1000000000) ≤ -Real.log (1907 / 2560) ∧
    -Real.log (1907 / 2560) ≤ (73618983 / 250000000) := by
  have h := checkLog_sound (w := (653 / 4467)) (n := 12)
    (lo := (294475931 / 1000000000)) (hi := (73618983 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1907) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1907) = 1/(1907 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-73618983 / 250000000) (-294475931 / 1000000000) (Real.log (1907 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (226964367 / 1000000000) ≤ -Real.log (10240 / 12849) ∧
    -Real.log (10240 / 12849) ≤ (14185273 / 62500000) := by
  have h := checkLog_sound (w := (2609 / 23089)) (n := 12)
    (lo := (226964367 / 1000000000)) (hi := (14185273 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12849 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12849 / 10240) = 1/(10240 / 12849) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (226964367 / 1000000000) (14185273 / 62500000) (Real.log (12849 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12849 / 10240) = -Real.log (10240 / 12849) := by
    rw [show ((12849 / 10240) : ℝ) = ((10240 / 12849) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (294082721 / 1000000000) ≤ -Real.log (7631 / 10240) ∧
    -Real.log (7631 / 10240) ≤ (147041361 / 500000000) := by
  have h := checkLog_sound (w := (2609 / 17871)) (n := 12)
    (lo := (294082721 / 1000000000)) (hi := (147041361 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7631) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7631) = 1/(7631 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-147041361 / 500000000) (-294082721 / 1000000000) (Real.log (7631 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (206106561 / 500000000) ≤ -Real.log (1280 / 1933) ∧
    -Real.log (1280 / 1933) ≤ (412213123 / 1000000000) := by
  have h := checkLog_sound (w := (653 / 3213)) (n := 12)
    (lo := (206106561 / 500000000)) (hi := (412213123 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1933 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1933 / 1280) = 1/(1280 / 1933) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (206106561 / 500000000) (412213123 / 1000000000) (Real.log (1933 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1933 / 1280) = -Real.log (1280 / 1933) := by
    rw [show ((1933 / 1280) : ℝ) = ((1280 / 1933) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (142733763 / 200000000) ≤ -Real.log (627 / 1280) ∧
    -Real.log (627 / 1280) ≤ (713668817 / 1000000000) := by
  have h := checkLog_sound (w := (13 / 1267)) (n := 12)
    (lo := (4104327 / 200000000)) (hi := (5130409 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 627) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 627) = 1/(627 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-713668817 / 1000000000) (-142733763 / 200000000) (Real.log (627 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (411825049 / 1000000000) ≤ -Real.log (5120 / 7729) ∧
    -Real.log (5120 / 7729) ≤ (8236501 / 20000000) := by
  have h := checkLog_sound (w := (2609 / 12849)) (n := 12)
    (lo := (411825049 / 1000000000)) (hi := (8236501 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7729 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7729 / 5120) = 1/(5120 / 7729) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (411825049 / 1000000000) (8236501 / 20000000) (Real.log (7729 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (7729 / 5120) = -Real.log (5120 / 7729) := by
    rw [show ((7729 / 5120) : ℝ) = ((5120 / 7729) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (356236679 / 500000000) ≤ -Real.log (2511 / 5120) ∧
    -Real.log (2511 / 5120) ≤ (8905917 / 12500000) := by
  have h := checkLog_sound (w := (49 / 5071)) (n := 12)
    (lo := (9663089 / 500000000)) (hi := (19326179 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 2511) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(2560 / 2511) = 1/(2511 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-8905917 / 12500000) (-356236679 / 500000000) (Real.log (2511 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (155470243 / 500000000) ≤ -Real.log (250000 / 341177) ∧
    -Real.log (250000 / 341177) ≤ (310940487 / 1000000000) := by
  have h := checkLog_sound (w := (91177 / 591177)) (n := 12)
    (lo := (155470243 / 500000000)) (hi := (310940487 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((341177 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(341177 / 250000) = 1/(250000 / 341177) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (155470243 / 500000000) (310940487 / 1000000000) (Real.log (341177 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (341177 / 250000) = -Real.log (250000 / 341177) := by
    rw [show ((341177 / 250000) : ℝ) = ((250000 / 341177) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (453670543 / 1000000000) ≤ -Real.log (158823 / 250000) ∧
    -Real.log (158823 / 250000) ≤ (28354409 / 62500000) := by
  have h := checkLog_sound (w := (91177 / 408823)) (n := 12)
    (lo := (453670543 / 1000000000)) (hi := (28354409 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 158823) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 158823) = 1/(158823 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-28354409 / 62500000) (-453670543 / 1000000000) (Real.log (158823 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (311256987 / 1000000000) ≤ -Real.log (50000 / 68257) ∧
    -Real.log (50000 / 68257) ≤ (77814247 / 250000000) := by
  have h := checkLog_sound (w := (18257 / 118257)) (n := 12)
    (lo := (311256987 / 1000000000)) (hi := (77814247 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((68257 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(68257 / 50000) = 1/(50000 / 68257) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (311256987 / 1000000000) (77814247 / 250000000) (Real.log (68257 / 50000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (68257 / 50000) = -Real.log (50000 / 68257) := by
    rw [show ((68257 / 50000) : ℝ) = ((50000 / 68257) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (56793847 / 125000000) ≤ -Real.log (31743 / 50000) ∧
    -Real.log (31743 / 50000) ≤ (454350777 / 1000000000) := by
  have h := checkLog_sound (w := (18257 / 81743)) (n := 12)
    (lo := (56793847 / 125000000)) (hi := (454350777 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 31743) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 31743) = 1/(31743 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-454350777 / 1000000000) (-56793847 / 125000000) (Real.log (31743 / 50000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (118617499 / 500000000) ≤ -Real.log (1000000 / 1267739) ∧
    -Real.log (1000000 / 1267739) ≤ (237234999 / 1000000000) := by
  have h := checkLog_sound (w := (267739 / 2267739)) (n := 12)
    (lo := (118617499 / 500000000)) (hi := (237234999 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1267739 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1267739 / 1000000) = 1/(1000000 / 1267739) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (118617499 / 500000000) (237234999 / 1000000000) (Real.log (1267739 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1267739 / 1000000) = -Real.log (1000000 / 1267739) := by
    rw [show ((1267739 / 1000000) : ℝ) = ((1000000 / 1267739) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (311618271 / 1000000000) ≤ -Real.log (732261 / 1000000) ∧
    -Real.log (732261 / 1000000) ≤ (9738071 / 31250000) := by
  have h := checkLog_sound (w := (267739 / 1732261)) (n := 12)
    (lo := (311618271 / 1000000000)) (hi := (9738071 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 732261) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 732261) = 1/(732261 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-9738071 / 31250000) (-311618271 / 1000000000) (Real.log (732261 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (47500789 / 200000000) ≤ -Real.log (12500 / 15851) ∧
    -Real.log (12500 / 15851) ≤ (118751973 / 500000000) := by
  have h := checkLog_sound (w := (3351 / 28351)) (n := 12)
    (lo := (47500789 / 200000000)) (hi := (118751973 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15851 / 12500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15851 / 12500) = 1/(12500 / 15851) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (47500789 / 200000000) (118751973 / 500000000) (Real.log (15851 / 12500)) := by
  have h := reflection_log_15_neg
  have he : Real.log (15851 / 12500) = -Real.log (12500 / 15851) := by
    rw [show ((15851 / 12500) : ℝ) = ((12500 / 15851) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (15604203 / 50000000) ≤ -Real.log (9149 / 12500) ∧
    -Real.log (9149 / 12500) ≤ (312084061 / 1000000000) := by
  have h := checkLog_sound (w := (3351 / 21649)) (n := 12)
    (lo := (15604203 / 50000000)) (hi := (312084061 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12500 / 9149) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12500 / 9149) = 1/(9149 / 12500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-312084061 / 1000000000) (-15604203 / 50000000) (Real.log (9149 / 12500)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (764611029 / 1000000000) ≤ -Real.log (100000000000 / 214815864201) ∧
    -Real.log (100000000000 / 214815864201) ≤ (764611031 / 1000000000) := by
  have h := checkLog_sound (w := (14815864201 / 414815864201)) (n := 12)
    (lo := (71463849 / 1000000000)) (hi := (1429277 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((214815864201 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(214815864201 / 200000000000) = 1/(100000000000 / 214815864201) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (764611029 / 1000000000) (764611031 / 1000000000) (Real.log (214815864201 / 100000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (214815864201 / 100000000000) = -Real.log (100000000000 / 214815864201) := by
    rw [show ((214815864201 / 100000000000) : ℝ) = ((100000000000 / 214815864201) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (765607763 / 1000000000) ≤ -Real.log (250000000000 / 537575213433) ∧
    -Real.log (250000000000 / 537575213433) ≤ (153121553 / 200000000) := by
  have h := checkLog_sound (w := (37575213433 / 1037575213433)) (n := 12)
    (lo := (72460583 / 1000000000)) (hi := (9057573 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((537575213433 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(537575213433 / 500000000000) = 1/(250000000000 / 537575213433) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (765607763 / 1000000000) (153121553 / 200000000) (Real.log (537575213433 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (537575213433 / 250000000000) = -Real.log (250000000000 / 537575213433) := by
    rw [show ((537575213433 / 250000000000) : ℝ) = ((250000000000 / 537575213433) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (54885327 / 100000000) ≤ -Real.log (250000000000 / 432816645977) ∧
    -Real.log (250000000000 / 432816645977) ≤ (548853271 / 1000000000) := by
  have h := checkLog_sound (w := (182816645977 / 682816645977)) (n := 12)
    (lo := (54885327 / 100000000)) (hi := (548853271 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((432816645977 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(432816645977 / 250000000000) = 1/(250000000000 / 432816645977) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (54885327 / 100000000) (548853271 / 1000000000) (Real.log (432816645977 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (432816645977 / 250000000000) = -Real.log (250000000000 / 432816645977) := by
    rw [show ((432816645977 / 250000000000) : ℝ) = ((250000000000 / 432816645977) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (274794003 / 500000000) ≤ -Real.log (100000000000 / 173253907531) ∧
    -Real.log (100000000000 / 173253907531) ≤ (549588007 / 1000000000) := by
  have h := checkLog_sound (w := (73253907531 / 273253907531)) (n := 12)
    (lo := (274794003 / 500000000)) (hi := (549588007 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((173253907531 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(173253907531 / 100000000000) = 1/(100000000000 / 173253907531) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (274794003 / 500000000) (549588007 / 1000000000) (Real.log (173253907531 / 100000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (173253907531 / 100000000000) = -Real.log (100000000000 / 173253907531) := by
    rw [show ((173253907531 / 100000000000) : ℝ) = ((100000000000 / 173253907531) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0286
