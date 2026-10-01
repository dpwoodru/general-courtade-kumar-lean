import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0404
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

theorem reflection_log_1_neg : (199267011 / 1000000000) ≤ -Real.log (5120 / 6249) ∧
    -Real.log (5120 / 6249) ≤ (49816753 / 250000000) := by
  have h := checkLog_sound (w := (1129 / 11369)) (n := 12)
    (lo := (199267011 / 1000000000)) (hi := (49816753 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6249 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6249 / 5120) = 1/(5120 / 6249) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (199267011 / 1000000000) (49816753 / 250000000) (Real.log (6249 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6249 / 5120) = -Real.log (5120 / 6249) := by
    rw [show ((6249 / 5120) : ℝ) = ((5120 / 6249) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (62278153 / 250000000) ≤ -Real.log (3991 / 5120) ∧
    -Real.log (3991 / 5120) ≤ (249112613 / 1000000000) := by
  have h := checkLog_sound (w := (1129 / 9111)) (n := 12)
    (lo := (62278153 / 250000000)) (hi := (249112613 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3991) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3991) = 1/(3991 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-249112613 / 1000000000) (-62278153 / 250000000) (Real.log (3991 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (777449 / 3906250) ≤ -Real.log (2048 / 2499) ∧
    -Real.log (2048 / 2499) ≤ (39805389 / 200000000) := by
  have h := checkLog_sound (w := (451 / 4547)) (n := 12)
    (lo := (777449 / 3906250)) (hi := (39805389 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2499 / 2048) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2499 / 2048) = 1/(2048 / 2499) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (777449 / 3906250) (39805389 / 200000000) (Real.log (2499 / 2048)) := by
  have h := reflection_log_3_neg
  have he : Real.log (2499 / 2048) = -Real.log (2048 / 2499) := by
    rw [show ((2499 / 2048) : ℝ) = ((2048 / 2499) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (248736837 / 1000000000) ≤ -Real.log (1597 / 2048) ∧
    -Real.log (1597 / 2048) ≤ (124368419 / 500000000) := by
  have h := checkLog_sound (w := (451 / 3645)) (n := 12)
    (lo := (248736837 / 1000000000)) (hi := (124368419 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2048 / 1597) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2048 / 1597) = 1/(1597 / 2048) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-124368419 / 500000000) (-248736837 / 1000000000) (Real.log (1597 / 2048)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (1141713 / 3125000) ≤ -Real.log (2560 / 3689) ∧
    -Real.log (2560 / 3689) ≤ (365348161 / 1000000000) := by
  have h := checkLog_sound (w := (1129 / 6249)) (n := 12)
    (lo := (1141713 / 3125000)) (hi := (365348161 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3689 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3689 / 2560) = 1/(2560 / 3689) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (1141713 / 3125000) (365348161 / 1000000000) (Real.log (3689 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (3689 / 2560) = -Real.log (2560 / 3689) := by
    rw [show ((3689 / 2560) : ℝ) = ((2560 / 3689) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (581633757 / 1000000000) ≤ -Real.log (1431 / 2560) ∧
    -Real.log (1431 / 2560) ≤ (290816879 / 500000000) := by
  have h := checkLog_sound (w := (1129 / 3991)) (n := 12)
    (lo := (581633757 / 1000000000)) (hi := (290816879 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1431) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1431) = 1/(1431 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-290816879 / 500000000) (-581633757 / 1000000000) (Real.log (1431 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (364941463 / 1000000000) ≤ -Real.log (1024 / 1475) ∧
    -Real.log (1024 / 1475) ≤ (45617683 / 125000000) := by
  have h := checkLog_sound (w := (451 / 2499)) (n := 12)
    (lo := (364941463 / 1000000000)) (hi := (45617683 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1475 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1475 / 1024) = 1/(1024 / 1475) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (364941463 / 1000000000) (45617683 / 125000000) (Real.log (1475 / 1024)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1475 / 1024) = -Real.log (1024 / 1475) := by
    rw [show ((1475 / 1024) : ℝ) = ((1024 / 1475) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (72573261 / 125000000) ≤ -Real.log (573 / 1024) ∧
    -Real.log (573 / 1024) ≤ (580586089 / 1000000000) := by
  have h := checkLog_sound (w := (451 / 1597)) (n := 12)
    (lo := (72573261 / 125000000)) (hi := (580586089 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 573) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 573) = 1/(573 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-580586089 / 1000000000) (-72573261 / 125000000) (Real.log (573 / 1024)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (273208331 / 1000000000) ≤ -Real.log (500000 / 657087) ∧
    -Real.log (500000 / 657087) ≤ (68302083 / 250000000) := by
  have h := checkLog_sound (w := (157087 / 1157087)) (n := 12)
    (lo := (273208331 / 1000000000)) (hi := (68302083 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((657087 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(657087 / 500000) = 1/(500000 / 657087) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (273208331 / 1000000000) (68302083 / 250000000) (Real.log (657087 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (657087 / 500000) = -Real.log (500000 / 657087) := by
    rw [show ((657087 / 500000) : ℝ) = ((500000 / 657087) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (377131327 / 1000000000) ≤ -Real.log (342913 / 500000) ∧
    -Real.log (342913 / 500000) ≤ (5892677 / 15625000) := by
  have h := checkLog_sound (w := (157087 / 842913)) (n := 12)
    (lo := (377131327 / 1000000000)) (hi := (5892677 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 342913) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 342913) = 1/(342913 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-5892677 / 15625000) (-377131327 / 1000000000) (Real.log (342913 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (273533197 / 1000000000) ≤ -Real.log (1000000 / 1314601) ∧
    -Real.log (1000000 / 1314601) ≤ (136766599 / 500000000) := by
  have h := checkLog_sound (w := (314601 / 2314601)) (n := 12)
    (lo := (273533197 / 1000000000)) (hi := (136766599 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1314601 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1314601 / 1000000) = 1/(1000000 / 1314601) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (273533197 / 1000000000) (136766599 / 500000000) (Real.log (1314601 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1314601 / 1000000) = -Real.log (1000000 / 1314601) := by
    rw [show ((1314601 / 1000000) : ℝ) = ((1000000 / 1314601) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (23609633 / 62500000) ≤ -Real.log (685399 / 1000000) ∧
    -Real.log (685399 / 1000000) ≤ (377754129 / 1000000000) := by
  have h := checkLog_sound (w := (314601 / 1685399)) (n := 12)
    (lo := (23609633 / 62500000)) (hi := (377754129 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 685399) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 685399) = 1/(685399 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-377754129 / 1000000000) (-23609633 / 62500000) (Real.log (685399 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (205708439 / 1000000000) ≤ -Real.log (200000 / 245679) ∧
    -Real.log (200000 / 245679) ≤ (5142711 / 25000000) := by
  have h := checkLog_sound (w := (45679 / 445679)) (n := 12)
    (lo := (205708439 / 1000000000)) (hi := (5142711 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((245679 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(245679 / 200000) = 1/(200000 / 245679) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (205708439 / 1000000000) (5142711 / 25000000) (Real.log (245679 / 200000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (245679 / 200000) = -Real.log (200000 / 245679) := by
    rw [show ((245679 / 200000) : ℝ) = ((200000 / 245679) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (259282517 / 1000000000) ≤ -Real.log (154321 / 200000) ∧
    -Real.log (154321 / 200000) ≤ (129641259 / 500000000) := by
  have h := checkLog_sound (w := (45679 / 354321)) (n := 12)
    (lo := (259282517 / 1000000000)) (hi := (129641259 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 154321) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 154321) = 1/(154321 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-129641259 / 500000000) (-259282517 / 1000000000) (Real.log (154321 / 200000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (102987709 / 500000000) ≤ -Real.log (1000000 / 1228723) ∧
    -Real.log (1000000 / 1228723) ≤ (205975419 / 1000000000) := by
  have h := checkLog_sound (w := (228723 / 2228723)) (n := 12)
    (lo := (102987709 / 500000000)) (hi := (205975419 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1228723 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1228723 / 1000000) = 1/(1000000 / 1228723) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (102987709 / 500000000) (205975419 / 1000000000) (Real.log (1228723 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1228723 / 1000000) = -Real.log (1000000 / 1228723) := by
    rw [show ((1228723 / 1000000) : ℝ) = ((1000000 / 1228723) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (16231731 / 62500000) ≤ -Real.log (771277 / 1000000) ∧
    -Real.log (771277 / 1000000) ≤ (259707697 / 1000000000) := by
  have h := checkLog_sound (w := (228723 / 1771277)) (n := 12)
    (lo := (16231731 / 62500000)) (hi := (259707697 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 771277) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 771277) = 1/(771277 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-259707697 / 1000000000) (-16231731 / 62500000) (Real.log (771277 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (650339659 / 1000000000) ≤ -Real.log (125000000000 / 239523946307) ∧
    -Real.log (125000000000 / 239523946307) ≤ (32516983 / 50000000) := by
  have h := checkLog_sound (w := (114523946307 / 364523946307)) (n := 12)
    (lo := (650339659 / 1000000000)) (hi := (32516983 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((239523946307 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(239523946307 / 125000000000) = 1/(125000000000 / 239523946307) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (650339659 / 1000000000) (32516983 / 50000000) (Real.log (239523946307 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (239523946307 / 125000000000) = -Real.log (125000000000 / 239523946307) := by
    rw [show ((239523946307 / 125000000000) : ℝ) = ((125000000000 / 239523946307) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (325643663 / 500000000) ≤ -Real.log (500000000000 / 959004171293) ∧
    -Real.log (500000000000 / 959004171293) ≤ (651287327 / 1000000000) := by
  have h := checkLog_sound (w := (459004171293 / 1459004171293)) (n := 12)
    (lo := (325643663 / 500000000)) (hi := (651287327 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((959004171293 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(959004171293 / 500000000000) = 1/(500000000000 / 959004171293) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (325643663 / 500000000) (651287327 / 1000000000) (Real.log (959004171293 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (959004171293 / 500000000000) = -Real.log (500000000000 / 959004171293) := by
    rw [show ((959004171293 / 500000000000) : ℝ) = ((500000000000 / 959004171293) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (464990957 / 1000000000) ≤ -Real.log (390625000 / 621874919) ∧
    -Real.log (390625000 / 621874919) ≤ (232495479 / 500000000) := by
  have h := checkLog_sound (w := (231249919 / 1012499919)) (n := 12)
    (lo := (464990957 / 1000000000)) (hi := (232495479 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((621874919 / 390625000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(621874919 / 390625000) = 1/(390625000 / 621874919) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (464990957 / 1000000000) (232495479 / 500000000) (Real.log (621874919 / 390625000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (621874919 / 390625000) = -Real.log (390625000 / 621874919) := by
    rw [show ((621874919 / 390625000) : ℝ) = ((390625000 / 621874919) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (232841557 / 500000000) ≤ -Real.log (500000000000 / 796551044567) ∧
    -Real.log (500000000000 / 796551044567) ≤ (93136623 / 200000000) := by
  have h := checkLog_sound (w := (296551044567 / 1296551044567)) (n := 12)
    (lo := (232841557 / 500000000)) (hi := (93136623 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((796551044567 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(796551044567 / 500000000000) = 1/(500000000000 / 796551044567) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (232841557 / 500000000) (93136623 / 200000000) (Real.log (796551044567 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (796551044567 / 500000000000) = -Real.log (500000000000 / 796551044567) := by
    rw [show ((796551044567 / 500000000000) : ℝ) = ((500000000000 / 796551044567) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0404
