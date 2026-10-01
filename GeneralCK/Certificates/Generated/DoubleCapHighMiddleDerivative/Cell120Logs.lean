import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell120
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

theorem reflection_log_1_neg : (278312139 / 1000000000) ≤ -Real.log (5120 / 6763) ∧
    -Real.log (5120 / 6763) ≤ (13915607 / 50000000) := by
  have h := checkLog_sound (w := (1643 / 11883)) (n := 12)
    (lo := (278312139 / 1000000000)) (hi := (13915607 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6763 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6763 / 5120) = 1/(5120 / 6763) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (278312139 / 1000000000) (13915607 / 50000000) (Real.log (6763 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6763 / 5120) = -Real.log (5120 / 6763) := by
    rw [show ((6763 / 5120) : ℝ) = ((5120 / 6763) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (193492293 / 500000000) ≤ -Real.log (3477 / 5120) ∧
    -Real.log (3477 / 5120) ≤ (386984587 / 1000000000) := by
  have h := checkLog_sound (w := (1643 / 8597)) (n := 12)
    (lo := (193492293 / 500000000)) (hi := (386984587 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3477) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3477) = 1/(3477 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-386984587 / 1000000000) (-193492293 / 500000000) (Real.log (3477 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (277868451 / 1000000000) ≤ -Real.log (128 / 169) ∧
    -Real.log (128 / 169) ≤ (69467113 / 250000000) := by
  have h := checkLog_sound (w := (41 / 297)) (n := 12)
    (lo := (277868451 / 1000000000)) (hi := (69467113 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((169 / 128) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(169 / 128) = 1/(128 / 169) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (277868451 / 1000000000) (69467113 / 250000000) (Real.log (169 / 128)) := by
  have h := reflection_log_3_neg
  have he : Real.log (169 / 128) = -Real.log (128 / 169) := by
    rw [show ((169 / 128) : ℝ) = ((128 / 169) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (77224429 / 200000000) ≤ -Real.log (87 / 128) ∧
    -Real.log (87 / 128) ≤ (193061073 / 500000000) := by
  have h := checkLog_sound (w := (41 / 215)) (n := 12)
    (lo := (77224429 / 200000000)) (hi := (193061073 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((128 / 87) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(128 / 87) = 1/(87 / 128) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-193061073 / 500000000) (-77224429 / 200000000) (Real.log (87 / 128)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (51246117 / 250000000) ≤ -Real.log (500000 / 613753) ∧
    -Real.log (500000 / 613753) ≤ (204984469 / 1000000000) := by
  have h := checkLog_sound (w := (113753 / 1113753)) (n := 12)
    (lo := (51246117 / 250000000)) (hi := (204984469 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((613753 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(613753 / 500000) = 1/(500000 / 613753) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (51246117 / 250000000) (204984469 / 1000000000) (Real.log (613753 / 500000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (613753 / 500000) = -Real.log (500000 / 613753) := by
    rw [show ((613753 / 500000) : ℝ) = ((500000 / 613753) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (258131037 / 1000000000) ≤ -Real.log (386247 / 500000) ∧
    -Real.log (386247 / 500000) ≤ (129065519 / 500000000) := by
  have h := checkLog_sound (w := (113753 / 886247)) (n := 12)
    (lo := (258131037 / 1000000000)) (hi := (129065519 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 386247) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 386247) = 1/(386247 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-129065519 / 500000000) (-258131037 / 1000000000) (Real.log (386247 / 500000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (205327381 / 1000000000) ≤ -Real.log (1000000 / 1227927) ∧
    -Real.log (1000000 / 1227927) ≤ (102663691 / 500000000) := by
  have h := checkLog_sound (w := (227927 / 2227927)) (n := 12)
    (lo := (205327381 / 1000000000)) (hi := (102663691 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1227927 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1227927 / 1000000) = 1/(1000000 / 1227927) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (205327381 / 1000000000) (102663691 / 500000000) (Real.log (1227927 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1227927 / 1000000) = -Real.log (1000000 / 1227927) := by
    rw [show ((1227927 / 1000000) : ℝ) = ((1000000 / 1227927) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (258676173 / 1000000000) ≤ -Real.log (772073 / 1000000) ∧
    -Real.log (772073 / 1000000) ≤ (129338087 / 500000000) := by
  have h := checkLog_sound (w := (227927 / 1772073)) (n := 12)
    (lo := (258676173 / 1000000000)) (hi := (129338087 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 772073) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 772073) = 1/(772073 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-129338087 / 500000000) (-258676173 / 1000000000) (Real.log (772073 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (18898143 / 125000000) ≤ -Real.log (250000 / 290803) ∧
    -Real.log (250000 / 290803) ≤ (30237029 / 200000000) := by
  have h := checkLog_sound (w := (40803 / 540803)) (n := 12)
    (lo := (18898143 / 125000000)) (hi := (30237029 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((290803 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(290803 / 250000) = 1/(250000 / 290803) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (18898143 / 125000000) (30237029 / 200000000) (Real.log (290803 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (290803 / 250000) = -Real.log (250000 / 290803) := by
    rw [show ((290803 / 250000) : ℝ) = ((250000 / 290803) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (89092263 / 500000000) ≤ -Real.log (209197 / 250000) ∧
    -Real.log (209197 / 250000) ≤ (178184527 / 1000000000) := by
  have h := checkLog_sound (w := (40803 / 459197)) (n := 12)
    (lo := (89092263 / 500000000)) (hi := (178184527 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 209197) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 209197) = 1/(209197 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-178184527 / 1000000000) (-89092263 / 500000000) (Real.log (209197 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (151452471 / 1000000000) ≤ -Real.log (1000000 / 1163523) ∧
    -Real.log (1000000 / 1163523) ≤ (18931559 / 125000000) := by
  have h := checkLog_sound (w := (163523 / 2163523)) (n := 12)
    (lo := (151452471 / 1000000000)) (hi := (18931559 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1163523 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1163523 / 1000000) = 1/(1000000 / 1163523) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (151452471 / 1000000000) (18931559 / 125000000) (Real.log (1163523 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1163523 / 1000000) = -Real.log (1000000 / 1163523) := by
    rw [show ((1163523 / 1000000) : ℝ) = ((1000000 / 1163523) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (89278127 / 500000000) ≤ -Real.log (836477 / 1000000) ∧
    -Real.log (836477 / 1000000) ≤ (35711251 / 200000000) := by
  have h := checkLog_sound (w := (163523 / 1836477)) (n := 12)
    (lo := (89278127 / 500000000)) (hi := (35711251 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 836477) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 836477) = 1/(836477 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-35711251 / 200000000) (-89278127 / 500000000) (Real.log (836477 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (165997649 / 250000000) ≤ -Real.log (62500000000 / 121408045977) ∧
    -Real.log (62500000000 / 121408045977) ≤ (663990597 / 1000000000) := by
  have h := checkLog_sound (w := (58908045977 / 183908045977)) (n := 12)
    (lo := (165997649 / 250000000)) (hi := (663990597 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((121408045977 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(121408045977 / 62500000000) = 1/(62500000000 / 121408045977) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (165997649 / 250000000) (663990597 / 1000000000) (Real.log (121408045977 / 62500000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (121408045977 / 62500000000) = -Real.log (62500000000 / 121408045977) := by
    rw [show ((121408045977 / 62500000000) : ℝ) = ((62500000000 / 121408045977) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (26611869 / 40000000) ≤ -Real.log (500000000000 / 972533793501) ∧
    -Real.log (500000000000 / 972533793501) ≤ (332648363 / 500000000) := by
  have h := checkLog_sound (w := (472533793501 / 1472533793501)) (n := 12)
    (lo := (26611869 / 40000000)) (hi := (332648363 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((972533793501 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(972533793501 / 500000000000) = 1/(500000000000 / 972533793501) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (26611869 / 40000000) (332648363 / 500000000) (Real.log (972533793501 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (972533793501 / 500000000000) = -Real.log (500000000000 / 972533793501) := by
    rw [show ((972533793501 / 500000000000) : ℝ) = ((500000000000 / 972533793501) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (92623101 / 200000000) ≤ -Real.log (500000000000 / 794508436311) ∧
    -Real.log (500000000000 / 794508436311) ≤ (231557753 / 500000000) := by
  have h := checkLog_sound (w := (294508436311 / 1294508436311)) (n := 12)
    (lo := (92623101 / 200000000)) (hi := (231557753 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((794508436311 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(794508436311 / 500000000000) = 1/(500000000000 / 794508436311) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (92623101 / 200000000) (231557753 / 500000000) (Real.log (794508436311 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (794508436311 / 500000000000) = -Real.log (500000000000 / 794508436311) := by
    rw [show ((794508436311 / 500000000000) : ℝ) = ((500000000000 / 794508436311) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (92800711 / 200000000) ≤ -Real.log (500000000000 / 795214312637) ∧
    -Real.log (500000000000 / 795214312637) ≤ (116000889 / 250000000) := by
  have h := checkLog_sound (w := (295214312637 / 1295214312637)) (n := 12)
    (lo := (92800711 / 200000000)) (hi := (116000889 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((795214312637 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(795214312637 / 500000000000) = 1/(500000000000 / 795214312637) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (92800711 / 200000000) (116000889 / 250000000) (Real.log (795214312637 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (795214312637 / 500000000000) = -Real.log (500000000000 / 795214312637) := by
    rw [show ((795214312637 / 500000000000) : ℝ) = ((500000000000 / 795214312637) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (32936967 / 100000000) ≤ -Real.log (62500000000 / 86880727257) ∧
    -Real.log (62500000000 / 86880727257) ≤ (329369671 / 1000000000) := by
  have h := checkLog_sound (w := (24380727257 / 149380727257)) (n := 12)
    (lo := (32936967 / 100000000)) (hi := (329369671 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((86880727257 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(86880727257 / 62500000000) = 1/(62500000000 / 86880727257) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (32936967 / 100000000) (329369671 / 1000000000) (Real.log (86880727257 / 62500000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (86880727257 / 62500000000) = -Real.log (62500000000 / 86880727257) := by
    rw [show ((86880727257 / 62500000000) : ℝ) = ((62500000000 / 86880727257) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (13200349 / 40000000) ≤ -Real.log (500000000000 / 695490133023) ∧
    -Real.log (500000000000 / 695490133023) ≤ (165004363 / 500000000) := by
  have h := checkLog_sound (w := (195490133023 / 1195490133023)) (n := 12)
    (lo := (13200349 / 40000000)) (hi := (165004363 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((695490133023 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(695490133023 / 500000000000) = 1/(500000000000 / 695490133023) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (13200349 / 40000000) (165004363 / 500000000) (Real.log (695490133023 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (695490133023 / 500000000000) = -Real.log (500000000000 / 695490133023) := by
    rw [show ((695490133023 / 500000000000) : ℝ) = ((500000000000 / 695490133023) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (13551891 / 500000000) ≤ -Real.log (973260228471 / 1000000000000) ∧
    -Real.log (973260228471 / 1000000000000) ≤ (27103783 / 1000000000) := by
  have h := checkLog_sound (w := (26739771529 / 1973260228471)) (n := 12)
    (lo := (13551891 / 500000000)) (hi := (27103783 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 973260228471) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 973260228471) = 1/(973260228471 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-27103783 / 1000000000) (-13551891 / 500000000) (Real.log (973260228471 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (13499691 / 500000000) ≤ -Real.log (60835115191 / 62500000000) ∧
    -Real.log (60835115191 / 62500000000) ≤ (26999383 / 1000000000) := by
  have h := checkLog_sound (w := (1664884809 / 123335115191)) (n := 12)
    (lo := (13499691 / 500000000)) (hi := (26999383 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 60835115191) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 60835115191) = 1/(60835115191 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-26999383 / 1000000000) (-13499691 / 500000000) (Real.log (60835115191 / 62500000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell120
