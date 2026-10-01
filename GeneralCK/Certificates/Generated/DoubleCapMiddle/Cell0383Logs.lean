import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0383
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

theorem reflection_log_1_neg : (51073789 / 250000000) ≤ -Real.log (10240 / 12561) ∧
    -Real.log (10240 / 12561) ≤ (204295157 / 1000000000) := by
  have h := checkLog_sound (w := (2321 / 22801)) (n := 12)
    (lo := (51073789 / 250000000)) (hi := (204295157 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12561 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12561 / 10240) = 1/(10240 / 12561) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (51073789 / 250000000) (204295157 / 1000000000) (Real.log (12561 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12561 / 10240) = -Real.log (10240 / 12561) := by
    rw [show ((12561 / 10240) : ℝ) = ((10240 / 12561) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (64259171 / 250000000) ≤ -Real.log (7919 / 10240) ∧
    -Real.log (7919 / 10240) ≤ (51407337 / 200000000) := by
  have h := checkLog_sound (w := (2321 / 18159)) (n := 12)
    (lo := (64259171 / 250000000)) (hi := (51407337 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7919) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7919) = 1/(7919 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-51407337 / 200000000) (-64259171 / 250000000) (Real.log (7919 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (204056293 / 1000000000) ≤ -Real.log (5120 / 6279) ∧
    -Real.log (5120 / 6279) ≤ (102028147 / 500000000) := by
  have h := checkLog_sound (w := (1159 / 11399)) (n := 12)
    (lo := (204056293 / 1000000000)) (hi := (102028147 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6279 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6279 / 5120) = 1/(5120 / 6279) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (204056293 / 1000000000) (102028147 / 500000000) (Real.log (6279 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6279 / 5120) = -Real.log (5120 / 6279) := by
    rw [show ((6279 / 5120) : ℝ) = ((5120 / 6279) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (100257 / 390625) ≤ -Real.log (3961 / 5120) ∧
    -Real.log (3961 / 5120) ≤ (256657921 / 1000000000) := by
  have h := checkLog_sound (w := (1159 / 9081)) (n := 12)
    (lo := (100257 / 390625)) (hi := (256657921 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3961) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3961) = 1/(3961 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-256657921 / 1000000000) (-100257 / 390625) (Real.log (3961 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (373850809 / 1000000000) ≤ -Real.log (5120 / 7441) ∧
    -Real.log (5120 / 7441) ≤ (37385081 / 100000000) := by
  have h := checkLog_sound (w := (2321 / 12561)) (n := 12)
    (lo := (373850809 / 1000000000)) (hi := (37385081 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7441 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7441 / 5120) = 1/(5120 / 7441) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (373850809 / 1000000000) (37385081 / 100000000) (Real.log (7441 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (7441 / 5120) = -Real.log (5120 / 7441) := by
    rw [show ((7441 / 5120) : ℝ) = ((5120 / 7441) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (150973057 / 250000000) ≤ -Real.log (2799 / 5120) ∧
    -Real.log (2799 / 5120) ≤ (603892229 / 1000000000) := by
  have h := checkLog_sound (w := (2321 / 7919)) (n := 12)
    (lo := (150973057 / 250000000)) (hi := (603892229 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2799) = 1/(2799 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-603892229 / 1000000000) (-150973057 / 250000000) (Real.log (2799 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (93361889 / 250000000) ≤ -Real.log (2560 / 3719) ∧
    -Real.log (2560 / 3719) ≤ (373447557 / 1000000000) := by
  have h := checkLog_sound (w := (1159 / 6279)) (n := 12)
    (lo := (93361889 / 250000000)) (hi := (373447557 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3719 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3719 / 2560) = 1/(2560 / 3719) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (93361889 / 250000000) (373447557 / 1000000000) (Real.log (3719 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (3719 / 2560) = -Real.log (2560 / 3719) := by
    rw [show ((3719 / 2560) : ℝ) = ((2560 / 3719) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (602820991 / 1000000000) ≤ -Real.log (1401 / 2560) ∧
    -Real.log (1401 / 2560) ≤ (4709539 / 7812500) := by
  have h := checkLog_sound (w := (1159 / 3961)) (n := 12)
    (lo := (602820991 / 1000000000)) (hi := (4709539 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1401) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1401) = 1/(1401 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-4709539 / 7812500) (-602820991 / 1000000000) (Real.log (1401 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (139998937 / 500000000) ≤ -Real.log (1000000 / 1323127) ∧
    -Real.log (1000000 / 1323127) ≤ (2239983 / 8000000) := by
  have h := checkLog_sound (w := (323127 / 2323127)) (n := 12)
    (lo := (139998937 / 500000000)) (hi := (2239983 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1323127 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1323127 / 1000000) = 1/(1000000 / 1323127) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (139998937 / 500000000) (2239983 / 8000000) (Real.log (1323127 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1323127 / 1000000) = -Real.log (1000000 / 1323127) := by
    rw [show ((1323127 / 1000000) : ℝ) = ((1000000 / 1323127) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (78054323 / 200000000) ≤ -Real.log (676873 / 1000000) ∧
    -Real.log (676873 / 1000000) ≤ (3048997 / 7812500) := by
  have h := checkLog_sound (w := (323127 / 1676873)) (n := 12)
    (lo := (78054323 / 200000000)) (hi := (3048997 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 676873) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 676873) = 1/(676873 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-3048997 / 7812500) (-78054323 / 200000000) (Real.log (676873 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (140160271 / 500000000) ≤ -Real.log (500000 / 661777) ∧
    -Real.log (500000 / 661777) ≤ (280320543 / 1000000000) := by
  have h := checkLog_sound (w := (161777 / 1161777)) (n := 12)
    (lo := (140160271 / 500000000)) (hi := (280320543 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((661777 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(661777 / 500000) = 1/(500000 / 661777) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (140160271 / 500000000) (280320543 / 1000000000) (Real.log (661777 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (661777 / 500000) = -Real.log (500000 / 661777) := by
    rw [show ((661777 / 500000) : ℝ) = ((500000 / 661777) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (390902657 / 1000000000) ≤ -Real.log (338223 / 500000) ∧
    -Real.log (338223 / 500000) ≤ (195451329 / 500000000) := by
  have h := checkLog_sound (w := (161777 / 838223)) (n := 12)
    (lo := (390902657 / 1000000000)) (hi := (195451329 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 338223) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 338223) = 1/(338223 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-195451329 / 500000000) (-390902657 / 1000000000) (Real.log (338223 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (13206357 / 62500000) ≤ -Real.log (200000 / 247057) ∧
    -Real.log (200000 / 247057) ≤ (211301713 / 1000000000) := by
  have h := checkLog_sound (w := (47057 / 447057)) (n := 12)
    (lo := (13206357 / 62500000)) (hi := (211301713 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((247057 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(247057 / 200000) = 1/(200000 / 247057) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (13206357 / 62500000) (211301713 / 1000000000) (Real.log (247057 / 200000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (247057 / 200000) = -Real.log (200000 / 247057) := by
    rw [show ((247057 / 200000) : ℝ) = ((200000 / 247057) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (268252063 / 1000000000) ≤ -Real.log (152943 / 200000) ∧
    -Real.log (152943 / 200000) ≤ (8382877 / 31250000) := by
  have h := checkLog_sound (w := (47057 / 352943)) (n := 12)
    (lo := (268252063 / 1000000000)) (hi := (8382877 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 152943) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 152943) = 1/(152943 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-8382877 / 31250000) (-268252063 / 1000000000) (Real.log (152943 / 200000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (211568821 / 1000000000) ≤ -Real.log (200000 / 247123) ∧
    -Real.log (200000 / 247123) ≤ (105784411 / 500000000) := by
  have h := checkLog_sound (w := (47123 / 447123)) (n := 12)
    (lo := (211568821 / 1000000000)) (hi := (105784411 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((247123 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(247123 / 200000) = 1/(200000 / 247123) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (211568821 / 1000000000) (105784411 / 500000000) (Real.log (247123 / 200000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (247123 / 200000) = -Real.log (200000 / 247123) := by
    rw [show ((247123 / 200000) : ℝ) = ((200000 / 247123) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (26868369 / 100000000) ≤ -Real.log (152877 / 200000) ∧
    -Real.log (152877 / 200000) ≤ (268683691 / 1000000000) := by
  have h := checkLog_sound (w := (47123 / 352877)) (n := 12)
    (lo := (26868369 / 100000000)) (hi := (268683691 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 152877) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 152877) = 1/(152877 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-268683691 / 1000000000) (-26868369 / 100000000) (Real.log (152877 / 200000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (67026949 / 100000000) ≤ -Real.log (100000000000 / 195476403993) ∧
    -Real.log (100000000000 / 195476403993) ≤ (670269491 / 1000000000) := by
  have h := checkLog_sound (w := (95476403993 / 295476403993)) (n := 12)
    (lo := (67026949 / 100000000)) (hi := (670269491 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((195476403993 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(195476403993 / 100000000000) = 1/(100000000000 / 195476403993) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (67026949 / 100000000) (670269491 / 1000000000) (Real.log (195476403993 / 100000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (195476403993 / 100000000000) = -Real.log (100000000000 / 195476403993) := by
    rw [show ((195476403993 / 100000000000) : ℝ) = ((100000000000 / 195476403993) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (671223199 / 1000000000) ≤ -Real.log (31250000000 / 61144662693) ∧
    -Real.log (31250000000 / 61144662693) ≤ (839029 / 1250000) := by
  have h := checkLog_sound (w := (29894662693 / 92394662693)) (n := 12)
    (lo := (671223199 / 1000000000)) (hi := (839029 / 1250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((61144662693 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(61144662693 / 31250000000) = 1/(31250000000 / 61144662693) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (671223199 / 1000000000) (839029 / 1250000) (Real.log (61144662693 / 31250000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (61144662693 / 31250000000) = -Real.log (31250000000 / 61144662693) := by
    rw [show ((61144662693 / 31250000000) : ℝ) = ((31250000000 / 61144662693) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (29972111 / 62500000) ≤ -Real.log (250000000000 / 403838358081) ∧
    -Real.log (250000000000 / 403838358081) ≤ (479553777 / 1000000000) := by
  have h := checkLog_sound (w := (153838358081 / 653838358081)) (n := 12)
    (lo := (29972111 / 62500000)) (hi := (479553777 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((403838358081 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(403838358081 / 250000000000) = 1/(250000000000 / 403838358081) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (29972111 / 62500000) (479553777 / 1000000000) (Real.log (403838358081 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (403838358081 / 250000000000) = -Real.log (250000000000 / 403838358081) := by
    rw [show ((403838358081 / 250000000000) : ℝ) = ((250000000000 / 403838358081) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (480252511 / 1000000000) ≤ -Real.log (100000000000 / 161648253171) ∧
    -Real.log (100000000000 / 161648253171) ≤ (15007891 / 31250000) := by
  have h := checkLog_sound (w := (61648253171 / 261648253171)) (n := 12)
    (lo := (480252511 / 1000000000)) (hi := (15007891 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((161648253171 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(161648253171 / 100000000000) = 1/(100000000000 / 161648253171) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (480252511 / 1000000000) (15007891 / 31250000) (Real.log (161648253171 / 100000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (161648253171 / 100000000000) = -Real.log (100000000000 / 161648253171) := by
    rw [show ((161648253171 / 100000000000) : ℝ) = ((100000000000 / 161648253171) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0383
