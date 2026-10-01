import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0021
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

theorem reflection_log_1_neg : (136356807 / 200000000) ≤ -Real.log (51200 / 101243) ∧
    -Real.log (51200 / 101243) ≤ (170446009 / 250000000) := by
  have h := checkLog_sound (w := (50043 / 152443)) (n := 12)
    (lo := (136356807 / 200000000)) (hi := (170446009 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((101243 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(101243 / 51200) = 1/(51200 / 101243) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (136356807 / 200000000) (170446009 / 250000000) (Real.log (101243 / 51200)) := by
  have h := reflection_log_1_neg
  have he : Real.log (101243 / 51200) = -Real.log (51200 / 101243) := by
    rw [show ((101243 / 51200) : ℝ) = ((51200 / 101243) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (3789909081 / 1000000000) ≤ -Real.log (1157 / 51200) ∧
    -Real.log (1157 / 51200) ≤ (3789909087 / 1000000000) := by
  have h := checkLog_sound (w := (443 / 2757)) (n := 12)
    (lo := (324173181 / 1000000000)) (hi := (162086591 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1157) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(1600 / 1157) = 1/(1157 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-3789909087 / 1000000000) (-3789909081 / 1000000000) (Real.log (1157 / 51200)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (681690197 / 1000000000) ≤ -Real.log (102400 / 202467) ∧
    -Real.log (102400 / 202467) ≤ (340845099 / 500000000) := by
  have h := checkLog_sound (w := (100067 / 304867)) (n := 12)
    (lo := (681690197 / 1000000000)) (hi := (340845099 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((202467 / 102400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(202467 / 102400) = 1/(102400 / 202467) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (681690197 / 1000000000) (340845099 / 500000000) (Real.log (202467 / 102400)) := by
  have h := reflection_log_3_neg
  have he : Real.log (202467 / 102400) = -Real.log (102400 / 202467) := by
    rw [show ((202467 / 102400) : ℝ) = ((102400 / 202467) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (945432929 / 250000000) ≤ -Real.log (2333 / 102400) ∧
    -Real.log (2333 / 102400) ≤ (1890865861 / 500000000) := by
  have h := checkLog_sound (w := (867 / 5533)) (n := 12)
    (lo := (39499477 / 125000000)) (hi := (315995817 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2333) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3200 / 2333) = 1/(2333 / 102400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-1890865861 / 500000000) (-945432929 / 250000000) (Real.log (2333 / 102400)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (167572571 / 250000000) ≤ -Real.log (25600 / 50043) ∧
    -Real.log (25600 / 50043) ≤ (134058057 / 200000000) := by
  have h := checkLog_sound (w := (24443 / 75643)) (n := 12)
    (lo := (167572571 / 250000000)) (hi := (134058057 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50043 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50043 / 25600) = 1/(25600 / 50043) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (167572571 / 250000000) (134058057 / 200000000) (Real.log (50043 / 25600)) := by
  have h := reflection_log_5_neg
  have he : Real.log (50043 / 25600) = -Real.log (25600 / 50043) := by
    rw [show ((50043 / 25600) : ℝ) = ((25600 / 50043) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (3096761901 / 1000000000) ≤ -Real.log (1157 / 25600) ∧
    -Real.log (1157 / 25600) ≤ (1548380953 / 500000000) := by
  have h := checkLog_sound (w := (443 / 2757)) (n := 12)
    (lo := (324173181 / 1000000000)) (hi := (162086591 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1157) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1600 / 1157) = 1/(1157 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1548380953 / 500000000) (-3096761901 / 1000000000) (Real.log (1157 / 25600)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (670100429 / 1000000000) ≤ -Real.log (51200 / 100067) ∧
    -Real.log (51200 / 100067) ≤ (67010043 / 100000000) := by
  have h := checkLog_sound (w := (48867 / 151267)) (n := 12)
    (lo := (670100429 / 1000000000)) (hi := (67010043 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100067 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100067 / 51200) = 1/(51200 / 100067) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (670100429 / 1000000000) (67010043 / 100000000) (Real.log (100067 / 51200)) := by
  have h := reflection_log_7_neg
  have he : Real.log (100067 / 51200) = -Real.log (51200 / 100067) := by
    rw [show ((100067 / 51200) : ℝ) = ((51200 / 100067) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (386073067 / 125000000) ≤ -Real.log (2333 / 51200) ∧
    -Real.log (2333 / 51200) ≤ (3088584541 / 1000000000) := by
  have h := checkLog_sound (w := (867 / 5533)) (n := 12)
    (lo := (39499477 / 125000000)) (hi := (315995817 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2333) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3200 / 2333) = 1/(2333 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-3088584541 / 1000000000) (-386073067 / 125000000) (Real.log (2333 / 51200)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (68345991 / 100000000) ≤ -Real.log (1000000 / 1980719) ∧
    -Real.log (1000000 / 1980719) ≤ (683459911 / 1000000000) := by
  have h := checkLog_sound (w := (980719 / 2980719)) (n := 12)
    (lo := (68345991 / 100000000)) (hi := (683459911 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1980719 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1980719 / 1000000) = 1/(1000000 / 1980719) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (68345991 / 100000000) (683459911 / 1000000000) (Real.log (1980719 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1980719 / 1000000) = -Real.log (1000000 / 1980719) := by
    rw [show ((1980719 / 1000000) : ℝ) = ((1000000 / 1980719) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (3948635121 / 1000000000) ≤ -Real.log (19281 / 1000000) ∧
    -Real.log (19281 / 1000000) ≤ (3948635127 / 1000000000) := by
  have h := checkLog_sound (w := (11969 / 50531)) (n := 12)
    (lo := (482899221 / 1000000000)) (hi := (241449611 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 19281) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 19281) = 1/(19281 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-3948635127 / 1000000000) (-3948635121 / 1000000000) (Real.log (19281 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (341768323 / 500000000) ≤ -Real.log (1000000 / 1980871) ∧
    -Real.log (1000000 / 1980871) ≤ (683536647 / 1000000000) := by
  have h := checkLog_sound (w := (980871 / 2980871)) (n := 12)
    (lo := (341768323 / 500000000)) (hi := (683536647 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1980871 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1980871 / 1000000) = 1/(1000000 / 1980871) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (341768323 / 500000000) (683536647 / 1000000000) (Real.log (1980871 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1980871 / 1000000) = -Real.log (1000000 / 1980871) := by
    rw [show ((1980871 / 1000000) : ℝ) = ((1000000 / 1980871) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (494568721 / 125000000) ≤ -Real.log (19129 / 1000000) ∧
    -Real.log (19129 / 1000000) ≤ (1978274887 / 500000000) := by
  have h := checkLog_sound (w := (12121 / 50379)) (n := 12)
    (lo := (122703467 / 250000000)) (hi := (490813869 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 19129) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 19129) = 1/(19129 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1978274887 / 500000000) (-494568721 / 125000000) (Real.log (19129 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (68341851 / 100000000) ≤ -Real.log (1000000 / 1980637) ∧
    -Real.log (1000000 / 1980637) ≤ (683418511 / 1000000000) := by
  have h := checkLog_sound (w := (980637 / 2980637)) (n := 12)
    (lo := (68341851 / 100000000)) (hi := (683418511 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1980637 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1980637 / 1000000) = 1/(1000000 / 1980637) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (68341851 / 100000000) (683418511 / 1000000000) (Real.log (1980637 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1980637 / 1000000) = -Real.log (1000000 / 1980637) := by
    rw [show ((1980637 / 1000000) : ℝ) = ((1000000 / 1980637) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (3944391247 / 1000000000) ≤ -Real.log (19363 / 1000000) ∧
    -Real.log (19363 / 1000000) ≤ (3944391253 / 1000000000) := by
  have h := checkLog_sound (w := (11887 / 50613)) (n := 12)
    (lo := (478655347 / 1000000000)) (hi := (119663837 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 19363) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 19363) = 1/(19363 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-3944391253 / 1000000000) (-3944391247 / 1000000000) (Real.log (19363 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (136699151 / 200000000) ≤ -Real.log (100000 / 198079) ∧
    -Real.log (100000 / 198079) ≤ (170873939 / 250000000) := by
  have h := checkLog_sound (w := (98079 / 298079)) (n := 12)
    (lo := (136699151 / 200000000)) (hi := (170873939 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((198079 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(198079 / 100000) = 1/(100000 / 198079) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (136699151 / 200000000) (170873939 / 250000000) (Real.log (198079 / 100000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (198079 / 100000) = -Real.log (100000 / 198079) := by
    rw [show ((198079 / 100000) : ℝ) = ((100000 / 198079) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (3952324299 / 1000000000) ≤ -Real.log (1921 / 100000) ∧
    -Real.log (1921 / 100000) ≤ (790464861 / 200000000) := by
  have h := checkLog_sound (w := (602 / 2523)) (n := 12)
    (lo := (486588399 / 1000000000)) (hi := (1216471 / 2500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3125 / 1921) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3125 / 1921) = 1/(1921 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-790464861 / 200000000) (-3952324299 / 1000000000) (Real.log (1921 / 100000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (463209503 / 100000000) ≤ -Real.log (125000000000 / 12841132462009) ∧
    -Real.log (125000000000 / 12841132462009) ≤ (4632095037 / 1000000000) := by
  have h := checkLog_sound (w := (4841132462009 / 20841132462009)) (n := 12)
    (lo := (9464239 / 20000000)) (hi := (473211951 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12841132462009 / 8000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(12841132462009 / 8000000000000) = 1/(125000000000 / 12841132462009) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (463209503 / 100000000) (4632095037 / 1000000000) (Real.log (12841132462009 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (12841132462009 / 125000000000) = -Real.log (125000000000 / 12841132462009) := by
    rw [show ((12841132462009 / 125000000000) : ℝ) = ((125000000000 / 12841132462009) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (2320043207 / 500000000) ≤ -Real.log (500000000000 / 51776648021329) ∧
    -Real.log (500000000000 / 51776648021329) ≤ (4640086421 / 1000000000) := by
  have h := checkLog_sound (w := (19776648021329 / 83776648021329)) (n := 12)
    (lo := (240601667 / 500000000)) (hi := (96240667 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((51776648021329 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(51776648021329 / 32000000000000) = 1/(500000000000 / 51776648021329) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (2320043207 / 500000000) (4640086421 / 1000000000) (Real.log (51776648021329 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (51776648021329 / 500000000000) = -Real.log (500000000000 / 51776648021329) := by
    rw [show ((51776648021329 / 500000000000) : ℝ) = ((500000000000 / 51776648021329) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (4627809757 / 1000000000) ≤ -Real.log (6250000000 / 639311121727) ∧
    -Real.log (6250000000 / 639311121727) ≤ (1156952441 / 250000000) := by
  have h := checkLog_sound (w := (239311121727 / 1039311121727)) (n := 12)
    (lo := (468926677 / 1000000000)) (hi := (234463339 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((639311121727 / 400000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(639311121727 / 400000000000) = 1/(6250000000 / 639311121727) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (4627809757 / 1000000000) (1156952441 / 250000000) (Real.log (639311121727 / 6250000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (639311121727 / 6250000000) = -Real.log (6250000000 / 639311121727) := by
    rw [show ((639311121727 / 6250000000) : ℝ) = ((6250000000 / 639311121727) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (4635820053 / 1000000000) ≤ -Real.log (62500000000 / 6444527589797) ∧
    -Real.log (62500000000 / 6444527589797) ≤ (231791003 / 50000000) := by
  have h := checkLog_sound (w := (2444527589797 / 10444527589797)) (n := 12)
    (lo := (476936973 / 1000000000)) (hi := (238468487 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6444527589797 / 4000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(6444527589797 / 4000000000000) = 1/(62500000000 / 6444527589797) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (4635820053 / 1000000000) (231791003 / 50000000) (Real.log (6444527589797 / 62500000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (6444527589797 / 62500000000) = -Real.log (62500000000 / 6444527589797) := by
    rw [show ((6444527589797 / 62500000000) : ℝ) = ((62500000000 / 6444527589797) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0021
