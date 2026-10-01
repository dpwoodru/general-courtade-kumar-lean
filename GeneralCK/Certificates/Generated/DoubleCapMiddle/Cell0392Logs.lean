import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0392
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

theorem reflection_log_1_neg : (50535833 / 250000000) ≤ -Real.log (5120 / 6267) ∧
    -Real.log (5120 / 6267) ≤ (202143333 / 1000000000) := by
  have h := checkLog_sound (w := (1147 / 11387)) (n := 12)
    (lo := (50535833 / 250000000)) (hi := (202143333 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6267 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6267 / 5120) = 1/(5120 / 6267) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (50535833 / 250000000) (202143333 / 1000000000) (Real.log (6267 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6267 / 5120) = -Real.log (5120 / 6267) := by
    rw [show ((6267 / 5120) : ℝ) = ((5120 / 6267) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (126816481 / 500000000) ≤ -Real.log (3973 / 5120) ∧
    -Real.log (3973 / 5120) ≤ (253632963 / 1000000000) := by
  have h := checkLog_sound (w := (1147 / 9093)) (n := 12)
    (lo := (126816481 / 500000000)) (hi := (253632963 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3973) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3973) = 1/(3973 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-253632963 / 1000000000) (-126816481 / 500000000) (Real.log (3973 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (100951977 / 500000000) ≤ -Real.log (10240 / 12531) ∧
    -Real.log (10240 / 12531) ≤ (40380791 / 200000000) := by
  have h := checkLog_sound (w := (2291 / 22771)) (n := 12)
    (lo := (100951977 / 500000000)) (hi := (40380791 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12531 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12531 / 10240) = 1/(10240 / 12531) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (100951977 / 500000000) (40380791 / 200000000) (Real.log (12531 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12531 / 10240) = -Real.log (10240 / 12531) := by
    rw [show ((12531 / 10240) : ℝ) = ((10240 / 12531) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (50651097 / 200000000) ≤ -Real.log (7949 / 10240) ∧
    -Real.log (7949 / 10240) ≤ (126627743 / 500000000) := by
  have h := checkLog_sound (w := (2291 / 18189)) (n := 12)
    (lo := (50651097 / 200000000)) (hi := (126627743 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7949) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7949) = 1/(7949 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-126627743 / 500000000) (-50651097 / 200000000) (Real.log (7949 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (74043133 / 200000000) ≤ -Real.log (2560 / 3707) ∧
    -Real.log (2560 / 3707) ≤ (185107833 / 500000000) := by
  have h := checkLog_sound (w := (1147 / 6267)) (n := 12)
    (lo := (74043133 / 200000000)) (hi := (185107833 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3707 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3707 / 2560) = 1/(2560 / 3707) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (74043133 / 200000000) (185107833 / 500000000) (Real.log (3707 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (3707 / 2560) = -Real.log (2560 / 3707) := by
    rw [show ((3707 / 2560) : ℝ) = ((2560 / 3707) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (297146077 / 500000000) ≤ -Real.log (1413 / 2560) ∧
    -Real.log (1413 / 2560) ≤ (118858431 / 200000000) := by
  have h := checkLog_sound (w := (1147 / 3973)) (n := 12)
    (lo := (297146077 / 500000000)) (hi := (118858431 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1413) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1413) = 1/(1413 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-118858431 / 200000000) (-297146077 / 500000000) (Real.log (1413 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (369810943 / 1000000000) ≤ -Real.log (5120 / 7411) ∧
    -Real.log (5120 / 7411) ≤ (722287 / 1953125) := by
  have h := checkLog_sound (w := (2291 / 12531)) (n := 12)
    (lo := (369810943 / 1000000000)) (hi := (722287 / 1953125))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7411 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7411 / 5120) = 1/(5120 / 7411) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (369810943 / 1000000000) (722287 / 1953125) (Real.log (7411 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (7411 / 5120) = -Real.log (5120 / 7411) := by
    rw [show ((7411 / 5120) : ℝ) = ((5120 / 7411) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (296615573 / 500000000) ≤ -Real.log (2829 / 5120) ∧
    -Real.log (2829 / 5120) ≤ (593231147 / 1000000000) := by
  have h := checkLog_sound (w := (2291 / 7949)) (n := 12)
    (lo := (296615573 / 500000000)) (hi := (593231147 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2829) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2829) = 1/(2829 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-593231147 / 1000000000) (-296615573 / 500000000) (Real.log (2829 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (277092197 / 1000000000) ≤ -Real.log (125000 / 164911) ∧
    -Real.log (125000 / 164911) ≤ (138546099 / 500000000) := by
  have h := checkLog_sound (w := (39911 / 289911)) (n := 12)
    (lo := (277092197 / 1000000000)) (hi := (138546099 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((164911 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(164911 / 125000) = 1/(125000 / 164911) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (277092197 / 1000000000) (138546099 / 500000000) (Real.log (164911 / 125000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (164911 / 125000) = -Real.log (125000 / 164911) := by
    rw [show ((164911 / 125000) : ℝ) = ((125000 / 164911) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (384615969 / 1000000000) ≤ -Real.log (85089 / 125000) ∧
    -Real.log (85089 / 125000) ≤ (38461597 / 100000000) := by
  have h := checkLog_sound (w := (39911 / 210089)) (n := 12)
    (lo := (384615969 / 1000000000)) (hi := (38461597 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 85089) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 85089) = 1/(85089 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-38461597 / 100000000) (-384615969 / 1000000000) (Real.log (85089 / 125000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (69353951 / 250000000) ≤ -Real.log (200000 / 263943) ∧
    -Real.log (200000 / 263943) ≤ (55483161 / 200000000) := by
  have h := checkLog_sound (w := (63943 / 463943)) (n := 12)
    (lo := (69353951 / 250000000)) (hi := (55483161 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((263943 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(263943 / 200000) = 1/(200000 / 263943) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (69353951 / 250000000) (55483161 / 200000000) (Real.log (263943 / 200000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (263943 / 200000) = -Real.log (200000 / 263943) := by
    rw [show ((263943 / 200000) : ℝ) = ((200000 / 263943) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (7704869 / 20000000) ≤ -Real.log (136057 / 200000) ∧
    -Real.log (136057 / 200000) ≤ (385243451 / 1000000000) := by
  have h := checkLog_sound (w := (63943 / 336057)) (n := 12)
    (lo := (7704869 / 20000000)) (hi := (385243451 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 136057) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 136057) = 1/(136057 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-385243451 / 1000000000) (-7704869 / 20000000) (Real.log (136057 / 200000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (2611293 / 12500000) ≤ -Real.log (500000 / 616163) ∧
    -Real.log (500000 / 616163) ≤ (208903441 / 1000000000) := by
  have h := checkLog_sound (w := (116163 / 1116163)) (n := 12)
    (lo := (2611293 / 12500000)) (hi := (208903441 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((616163 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(616163 / 500000) = 1/(500000 / 616163) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (2611293 / 12500000) (208903441 / 1000000000) (Real.log (616163 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (616163 / 500000) = -Real.log (500000 / 616163) := by
    rw [show ((616163 / 500000) : ℝ) = ((500000 / 616163) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (52878023 / 200000000) ≤ -Real.log (383837 / 500000) ∧
    -Real.log (383837 / 500000) ≤ (66097529 / 250000000) := by
  have h := checkLog_sound (w := (116163 / 883837)) (n := 12)
    (lo := (52878023 / 200000000)) (hi := (66097529 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 383837) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 383837) = 1/(383837 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-66097529 / 250000000) (-52878023 / 200000000) (Real.log (383837 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (20917119 / 100000000) ≤ -Real.log (62500 / 77041) ∧
    -Real.log (62500 / 77041) ≤ (209171191 / 1000000000) := by
  have h := checkLog_sound (w := (14541 / 139541)) (n := 12)
    (lo := (20917119 / 100000000)) (hi := (209171191 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((77041 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(77041 / 62500) = 1/(62500 / 77041) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (20917119 / 100000000) (209171191 / 1000000000) (Real.log (77041 / 62500)) := by
  have h := reflection_log_15_neg
  have he : Real.log (77041 / 62500) = -Real.log (62500 / 77041) := by
    rw [show ((77041 / 62500) : ℝ) = ((62500 / 77041) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (264820077 / 1000000000) ≤ -Real.log (47959 / 62500) ∧
    -Real.log (47959 / 62500) ≤ (132410039 / 500000000) := by
  have h := checkLog_sound (w := (14541 / 110459)) (n := 12)
    (lo := (264820077 / 1000000000)) (hi := (132410039 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 47959) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 47959) = 1/(47959 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-132410039 / 500000000) (-264820077 / 1000000000) (Real.log (47959 / 62500)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (330854083 / 500000000) ≤ -Real.log (500000000000 / 969050053473) ∧
    -Real.log (500000000000 / 969050053473) ≤ (661708167 / 1000000000) := by
  have h := checkLog_sound (w := (469050053473 / 1469050053473)) (n := 12)
    (lo := (330854083 / 500000000)) (hi := (661708167 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((969050053473 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(969050053473 / 500000000000) = 1/(500000000000 / 969050053473) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (330854083 / 500000000) (661708167 / 1000000000) (Real.log (969050053473 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (969050053473 / 500000000000) = -Real.log (500000000000 / 969050053473) := by
    rw [show ((969050053473 / 500000000000) : ℝ) = ((500000000000 / 969050053473) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (132531851 / 200000000) ≤ -Real.log (125000000000 / 242493036007) ∧
    -Real.log (125000000000 / 242493036007) ≤ (82832407 / 125000000) := by
  have h := checkLog_sound (w := (117493036007 / 367493036007)) (n := 12)
    (lo := (132531851 / 200000000)) (hi := (82832407 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((242493036007 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(242493036007 / 125000000000) = 1/(125000000000 / 242493036007) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (132531851 / 200000000) (82832407 / 125000000) (Real.log (242493036007 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (242493036007 / 125000000000) = -Real.log (125000000000 / 242493036007) := by
    rw [show ((242493036007 / 125000000000) : ℝ) = ((125000000000 / 242493036007) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (94658711 / 200000000) ≤ -Real.log (500000000000 / 802636275293) ∧
    -Real.log (500000000000 / 802636275293) ≤ (118323389 / 250000000) := by
  have h := checkLog_sound (w := (302636275293 / 1302636275293)) (n := 12)
    (lo := (94658711 / 200000000)) (hi := (118323389 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((802636275293 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(802636275293 / 500000000000) = 1/(500000000000 / 802636275293) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (94658711 / 200000000) (118323389 / 250000000) (Real.log (802636275293 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (802636275293 / 500000000000) = -Real.log (500000000000 / 802636275293) := by
    rw [show ((802636275293 / 500000000000) : ℝ) = ((500000000000 / 802636275293) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (118497817 / 250000000) ≤ -Real.log (500000000000 / 803196480327) ∧
    -Real.log (500000000000 / 803196480327) ≤ (473991269 / 1000000000) := by
  have h := checkLog_sound (w := (303196480327 / 1303196480327)) (n := 12)
    (lo := (118497817 / 250000000)) (hi := (473991269 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((803196480327 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(803196480327 / 500000000000) = 1/(500000000000 / 803196480327) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (118497817 / 250000000) (473991269 / 1000000000) (Real.log (803196480327 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (803196480327 / 500000000000) = -Real.log (500000000000 / 803196480327) := by
    rw [show ((803196480327 / 500000000000) : ℝ) = ((500000000000 / 803196480327) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0392
