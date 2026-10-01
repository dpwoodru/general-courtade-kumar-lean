import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell040
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

theorem reflection_log_1_neg : (242179953 / 1000000000) ≤ -Real.log (5120 / 6523) ∧
    -Real.log (5120 / 6523) ≤ (121089977 / 500000000) := by
  have h := checkLog_sound (w := (1403 / 11643)) (n := 12)
    (lo := (242179953 / 1000000000)) (hi := (121089977 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6523 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6523 / 5120) = 1/(5120 / 6523) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (242179953 / 1000000000) (121089977 / 500000000) (Real.log (6523 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6523 / 5120) = -Real.log (5120 / 6523) := by
    rw [show ((6523 / 5120) : ℝ) = ((5120 / 6523) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (320237547 / 1000000000) ≤ -Real.log (3717 / 5120) ∧
    -Real.log (3717 / 5120) ≤ (80059387 / 250000000) := by
  have h := checkLog_sound (w := (1403 / 8837)) (n := 12)
    (lo := (320237547 / 1000000000)) (hi := (80059387 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3717) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3717) = 1/(3717 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-80059387 / 250000000) (-320237547 / 1000000000) (Real.log (3717 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (1888437 / 7812500) ≤ -Real.log (128 / 163) ∧
    -Real.log (128 / 163) ≤ (241719937 / 1000000000) := by
  have h := checkLog_sound (w := (35 / 291)) (n := 12)
    (lo := (1888437 / 7812500)) (hi := (241719937 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((163 / 128) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(163 / 128) = 1/(128 / 163) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (1888437 / 7812500) (241719937 / 1000000000) (Real.log (163 / 128)) := by
  have h := reflection_log_3_neg
  have he : Real.log (163 / 128) = -Real.log (128 / 163) := by
    rw [show ((163 / 128) : ℝ) = ((128 / 163) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (31943077 / 100000000) ≤ -Real.log (93 / 128) ∧
    -Real.log (93 / 128) ≤ (319430771 / 1000000000) := by
  have h := checkLog_sound (w := (35 / 221)) (n := 12)
    (lo := (31943077 / 100000000)) (hi := (319430771 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((128 / 93) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(128 / 93) = 1/(93 / 128) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-319430771 / 1000000000) (-31943077 / 100000000) (Real.log (93 / 128)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (88642363 / 500000000) ≤ -Real.log (1000000 / 1193971) ∧
    -Real.log (1000000 / 1193971) ≤ (177284727 / 1000000000) := by
  have h := checkLog_sound (w := (193971 / 2193971)) (n := 12)
    (lo := (88642363 / 500000000)) (hi := (177284727 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1193971 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1193971 / 1000000) = 1/(1000000 / 1193971) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (88642363 / 500000000) (177284727 / 1000000000) (Real.log (1193971 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1193971 / 1000000) = -Real.log (1000000 / 1193971) := by
    rw [show ((1193971 / 1000000) : ℝ) = ((1000000 / 1193971) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (53908889 / 250000000) ≤ -Real.log (806029 / 1000000) ∧
    -Real.log (806029 / 1000000) ≤ (215635557 / 1000000000) := by
  have h := checkLog_sound (w := (193971 / 1806029)) (n := 12)
    (lo := (53908889 / 250000000)) (hi := (215635557 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 806029) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 806029) = 1/(806029 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-215635557 / 1000000000) (-53908889 / 250000000) (Real.log (806029 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (88817797 / 500000000) ≤ -Real.log (100000 / 119439) ∧
    -Real.log (100000 / 119439) ≤ (35527119 / 200000000) := by
  have h := checkLog_sound (w := (19439 / 219439)) (n := 12)
    (lo := (88817797 / 500000000)) (hi := (35527119 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((119439 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(119439 / 100000) = 1/(100000 / 119439) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (88817797 / 500000000) (35527119 / 200000000) (Real.log (119439 / 100000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (119439 / 100000) = -Real.log (100000 / 119439) := by
    rw [show ((119439 / 100000) : ℝ) = ((100000 / 119439) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (54038881 / 250000000) ≤ -Real.log (80561 / 100000) ∧
    -Real.log (80561 / 100000) ≤ (8646221 / 40000000) := by
  have h := checkLog_sound (w := (19439 / 180561)) (n := 12)
    (lo := (54038881 / 250000000)) (hi := (8646221 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 80561) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 80561) = 1/(80561 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-8646221 / 40000000) (-54038881 / 250000000) (Real.log (80561 / 100000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (16225259 / 125000000) ≤ -Real.log (1000000 / 1138603) ∧
    -Real.log (1000000 / 1138603) ≤ (129802073 / 1000000000) := by
  have h := checkLog_sound (w := (138603 / 2138603)) (n := 12)
    (lo := (16225259 / 125000000)) (hi := (129802073 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1138603 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1138603 / 1000000) = 1/(1000000 / 1138603) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (16225259 / 125000000) (129802073 / 1000000000) (Real.log (1138603 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1138603 / 1000000) = -Real.log (1000000 / 1138603) := by
    rw [show ((1138603 / 1000000) : ℝ) = ((1000000 / 1138603) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (149199789 / 1000000000) ≤ -Real.log (861397 / 1000000) ∧
    -Real.log (861397 / 1000000) ≤ (14919979 / 100000000) := by
  have h := checkLog_sound (w := (138603 / 1861397)) (n := 12)
    (lo := (149199789 / 1000000000)) (hi := (14919979 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 861397) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 861397) = 1/(861397 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-14919979 / 100000000) (-149199789 / 1000000000) (Real.log (861397 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (8129479 / 62500000) ≤ -Real.log (100000 / 113891) ∧
    -Real.log (100000 / 113891) ≤ (26014333 / 200000000) := by
  have h := checkLog_sound (w := (13891 / 213891)) (n := 12)
    (lo := (8129479 / 62500000)) (hi := (26014333 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((113891 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(113891 / 100000) = 1/(100000 / 113891) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (8129479 / 62500000) (26014333 / 200000000) (Real.log (113891 / 100000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (113891 / 100000) = -Real.log (100000 / 113891) := by
    rw [show ((113891 / 100000) : ℝ) = ((100000 / 113891) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (23929 / 160000) ≤ -Real.log (86109 / 100000) ∧
    -Real.log (86109 / 100000) ≤ (149556251 / 1000000000) := by
  have h := checkLog_sound (w := (13891 / 186109)) (n := 12)
    (lo := (23929 / 160000)) (hi := (149556251 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 86109) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 86109) = 1/(86109 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-149556251 / 1000000000) (-23929 / 160000) (Real.log (86109 / 100000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (561150707 / 1000000000) ≤ -Real.log (500000000000 / 876344086021) ∧
    -Real.log (500000000000 / 876344086021) ≤ (140287677 / 250000000) := by
  have h := checkLog_sound (w := (376344086021 / 1376344086021)) (n := 12)
    (lo := (561150707 / 1000000000)) (hi := (140287677 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((876344086021 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(876344086021 / 500000000000) = 1/(500000000000 / 876344086021) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (561150707 / 1000000000) (140287677 / 250000000) (Real.log (876344086021 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (876344086021 / 500000000000) = -Real.log (500000000000 / 876344086021) := by
    rw [show ((876344086021 / 500000000000) : ℝ) = ((500000000000 / 876344086021) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (562417501 / 1000000000) ≤ -Real.log (500000000000 / 877454936777) ∧
    -Real.log (500000000000 / 877454936777) ≤ (281208751 / 500000000) := by
  have h := checkLog_sound (w := (377454936777 / 1377454936777)) (n := 12)
    (lo := (562417501 / 1000000000)) (hi := (281208751 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((877454936777 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(877454936777 / 500000000000) = 1/(500000000000 / 877454936777) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (562417501 / 1000000000) (281208751 / 500000000) (Real.log (877454936777 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (877454936777 / 500000000000) = -Real.log (500000000000 / 877454936777) := by
    rw [show ((877454936777 / 500000000000) : ℝ) = ((500000000000 / 877454936777) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (392920283 / 1000000000) ≤ -Real.log (15625000000 / 23145317197) ∧
    -Real.log (15625000000 / 23145317197) ≤ (98230071 / 250000000) := by
  have h := checkLog_sound (w := (7520317197 / 38770317197)) (n := 12)
    (lo := (392920283 / 1000000000)) (hi := (98230071 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((23145317197 / 15625000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(23145317197 / 15625000000) = 1/(15625000000 / 23145317197) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (392920283 / 1000000000) (98230071 / 250000000) (Real.log (23145317197 / 15625000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (23145317197 / 15625000000) = -Real.log (15625000000 / 23145317197) := by
    rw [show ((23145317197 / 15625000000) : ℝ) = ((15625000000 / 23145317197) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (393791119 / 1000000000) ≤ -Real.log (500000000000 / 741295415897) ∧
    -Real.log (500000000000 / 741295415897) ≤ (4922389 / 12500000) := by
  have h := checkLog_sound (w := (241295415897 / 1241295415897)) (n := 12)
    (lo := (393791119 / 1000000000)) (hi := (4922389 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((741295415897 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(741295415897 / 500000000000) = 1/(500000000000 / 741295415897) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (393791119 / 1000000000) (4922389 / 12500000) (Real.log (741295415897 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (741295415897 / 500000000000) = -Real.log (500000000000 / 741295415897) := by
    rw [show ((741295415897 / 500000000000) : ℝ) = ((500000000000 / 741295415897) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (279001861 / 1000000000) ≤ -Real.log (500000000000 / 660904902153) ∧
    -Real.log (500000000000 / 660904902153) ≤ (139500931 / 500000000) := by
  have h := checkLog_sound (w := (160904902153 / 1160904902153)) (n := 12)
    (lo := (279001861 / 1000000000)) (hi := (139500931 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((660904902153 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(660904902153 / 500000000000) = 1/(500000000000 / 660904902153) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (279001861 / 1000000000) (139500931 / 500000000) (Real.log (660904902153 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (660904902153 / 500000000000) = -Real.log (500000000000 / 660904902153) := by
    rw [show ((660904902153 / 500000000000) : ℝ) = ((500000000000 / 660904902153) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (55925583 / 200000000) ≤ -Real.log (500000000000 / 661318793623) ∧
    -Real.log (500000000000 / 661318793623) ≤ (69906979 / 250000000) := by
  have h := checkLog_sound (w := (161318793623 / 1161318793623)) (n := 12)
    (lo := (55925583 / 200000000)) (hi := (69906979 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((661318793623 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(661318793623 / 500000000000) = 1/(500000000000 / 661318793623) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (55925583 / 200000000) (69906979 / 250000000) (Real.log (661318793623 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (661318793623 / 500000000000) = -Real.log (500000000000 / 661318793623) := by
    rw [show ((661318793623 / 500000000000) : ℝ) = ((500000000000 / 661318793623) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (3896917 / 200000000) ≤ -Real.log (9807040119 / 10000000000) ∧
    -Real.log (9807040119 / 10000000000) ≤ (9742293 / 500000000) := by
  have h := checkLog_sound (w := (192959881 / 19807040119)) (n := 12)
    (lo := (3896917 / 200000000)) (hi := (9742293 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 9807040119) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 9807040119) = 1/(9807040119 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-9742293 / 500000000) (-3896917 / 200000000) (Real.log (9807040119 / 10000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (4849429 / 250000000) ≤ -Real.log (980789208391 / 1000000000000) ∧
    -Real.log (980789208391 / 1000000000000) ≤ (19397717 / 1000000000) := by
  have h := checkLog_sound (w := (19210791609 / 1980789208391)) (n := 12)
    (lo := (4849429 / 250000000)) (hi := (19397717 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 980789208391) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 980789208391) = 1/(980789208391 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-19397717 / 1000000000) (-4849429 / 250000000) (Real.log (980789208391 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell040
