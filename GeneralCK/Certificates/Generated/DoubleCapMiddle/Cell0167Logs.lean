import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0167
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

theorem reflection_log_1_neg : (280380087 / 1000000000) ≤ -Real.log (5120 / 6777) ∧
    -Real.log (5120 / 6777) ≤ (35047511 / 125000000) := by
  have h := checkLog_sound (w := (1657 / 11897)) (n := 12)
    (lo := (280380087 / 1000000000)) (hi := (35047511 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6777 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6777 / 5120) = 1/(5120 / 6777) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (280380087 / 1000000000) (35047511 / 125000000) (Real.log (6777 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6777 / 5120) = -Real.log (5120 / 6777) := by
    rw [show ((6777 / 5120) : ℝ) = ((5120 / 6777) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (391019173 / 1000000000) ≤ -Real.log (3463 / 5120) ∧
    -Real.log (3463 / 5120) ≤ (195509587 / 500000000) := by
  have h := checkLog_sound (w := (1657 / 8583)) (n := 12)
    (lo := (391019173 / 1000000000)) (hi := (195509587 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3463) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3463) = 1/(3463 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-195509587 / 500000000) (-391019173 / 1000000000) (Real.log (3463 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (55987463 / 200000000) ≤ -Real.log (2560 / 3387) ∧
    -Real.log (2560 / 3387) ≤ (69984329 / 250000000) := by
  have h := checkLog_sound (w := (827 / 5947)) (n := 12)
    (lo := (55987463 / 200000000)) (hi := (69984329 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3387 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3387 / 2560) = 1/(2560 / 3387) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (55987463 / 200000000) (69984329 / 250000000) (Real.log (3387 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3387 / 2560) = -Real.log (2560 / 3387) := by
    rw [show ((3387 / 2560) : ℝ) = ((2560 / 3387) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (390153247 / 1000000000) ≤ -Real.log (1733 / 2560) ∧
    -Real.log (1733 / 2560) ≤ (12192289 / 31250000) := by
  have h := checkLog_sound (w := (827 / 4293)) (n := 12)
    (lo := (390153247 / 1000000000)) (hi := (12192289 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1733) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1733) = 1/(1733 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-12192289 / 31250000) (-390153247 / 1000000000) (Real.log (1733 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (124779179 / 250000000) ≤ -Real.log (2560 / 4217) ∧
    -Real.log (2560 / 4217) ≤ (499116717 / 1000000000) := by
  have h := checkLog_sound (w := (1657 / 6777)) (n := 12)
    (lo := (124779179 / 250000000)) (hi := (499116717 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4217 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4217 / 2560) = 1/(2560 / 4217) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (124779179 / 250000000) (499116717 / 1000000000) (Real.log (4217 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (4217 / 2560) = -Real.log (2560 / 4217) := by
    rw [show ((4217 / 2560) : ℝ) = ((2560 / 4217) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1042039983 / 1000000000) ≤ -Real.log (903 / 2560) ∧
    -Real.log (903 / 2560) ≤ (208407997 / 200000000) := by
  have h := checkLog_sound (w := (377 / 2183)) (n := 12)
    (lo := (348892803 / 1000000000)) (hi := (87223201 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 903) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 903) = 1/(903 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-208407997 / 200000000) (-1042039983 / 1000000000) (Real.log (903 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (7787579 / 15625000) ≤ -Real.log (1280 / 2107) ∧
    -Real.log (1280 / 2107) ≤ (498405057 / 1000000000) := by
  have h := checkLog_sound (w := (827 / 3387)) (n := 12)
    (lo := (7787579 / 15625000)) (hi := (498405057 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2107 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2107 / 1280) = 1/(1280 / 2107) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (7787579 / 15625000) (498405057 / 1000000000) (Real.log (2107 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2107 / 1280) = -Real.log (1280 / 2107) := by
    rw [show ((2107 / 1280) : ℝ) = ((1280 / 2107) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (103872323 / 100000000) ≤ -Real.log (453 / 1280) ∧
    -Real.log (453 / 1280) ≤ (32460101 / 31250000) := by
  have h := checkLog_sound (w := (187 / 1093)) (n := 12)
    (lo := (6911521 / 20000000)) (hi := (345576051 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 453) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 453) = 1/(453 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-32460101 / 31250000) (-103872323 / 100000000) (Real.log (453 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (382952251 / 1000000000) ≤ -Real.log (62500 / 91663) ∧
    -Real.log (62500 / 91663) ≤ (95738063 / 250000000) := by
  have h := checkLog_sound (w := (29163 / 154163)) (n := 12)
    (lo := (382952251 / 1000000000)) (hi := (95738063 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((91663 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(91663 / 62500) = 1/(62500 / 91663) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (382952251 / 1000000000) (95738063 / 250000000) (Real.log (91663 / 62500)) := by
  have h := reflection_log_9_neg
  have he : Real.log (91663 / 62500) = -Real.log (62500 / 91663) := by
    rw [show ((91663 / 62500) : ℝ) = ((62500 / 91663) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (125699733 / 200000000) ≤ -Real.log (33337 / 62500) ∧
    -Real.log (33337 / 62500) ≤ (314249333 / 500000000) := by
  have h := checkLog_sound (w := (29163 / 95837)) (n := 12)
    (lo := (125699733 / 200000000)) (hi := (314249333 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 33337) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 33337) = 1/(33337 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-314249333 / 500000000) (-125699733 / 200000000) (Real.log (33337 / 62500)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (23972517 / 62500000) ≤ -Real.log (400 / 587) ∧
    -Real.log (400 / 587) ≤ (383560273 / 1000000000) := by
  have h := checkLog_sound (w := (187 / 987)) (n := 12)
    (lo := (23972517 / 62500000)) (hi := (383560273 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((587 / 400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(587 / 400) = 1/(400 / 587) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (23972517 / 62500000) (383560273 / 1000000000) (Real.log (587 / 400)) := by
  have h := reflection_log_11_neg
  have he : Real.log (587 / 400) = -Real.log (400 / 587) := by
    rw [show ((587 / 400) : ℝ) = ((400 / 587) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (630172381 / 1000000000) ≤ -Real.log (213 / 400) ∧
    -Real.log (213 / 400) ≤ (315086191 / 500000000) := by
  have h := checkLog_sound (w := (187 / 613)) (n := 12)
    (lo := (630172381 / 1000000000)) (hi := (315086191 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 213) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400 / 213) = 1/(213 / 400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-315086191 / 500000000) (-630172381 / 1000000000) (Real.log (213 / 400)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (150437333 / 500000000) ≤ -Real.log (3125 / 4222) ∧
    -Real.log (3125 / 4222) ≤ (300874667 / 1000000000) := by
  have h := checkLog_sound (w := (1097 / 7347)) (n := 12)
    (lo := (150437333 / 500000000)) (hi := (300874667 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4222 / 3125) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4222 / 3125) = 1/(3125 / 4222) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (150437333 / 500000000) (300874667 / 1000000000) (Real.log (4222 / 3125)) := by
  have h := reflection_log_13_neg
  have he : Real.log (4222 / 3125) = -Real.log (3125 / 4222) := by
    rw [show ((4222 / 3125) : ℝ) = ((3125 / 4222) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (432384197 / 1000000000) ≤ -Real.log (2028 / 3125) ∧
    -Real.log (2028 / 3125) ≤ (216192099 / 500000000) := by
  have h := checkLog_sound (w := (1097 / 5153)) (n := 12)
    (lo := (432384197 / 1000000000)) (hi := (216192099 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3125 / 2028) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3125 / 2028) = 1/(2028 / 3125) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-216192099 / 500000000) (-432384197 / 1000000000) (Real.log (2028 / 3125)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (150717409 / 500000000) ≤ -Real.log (1000000 / 1351797) ∧
    -Real.log (1000000 / 1351797) ≤ (301434819 / 1000000000) := by
  have h := checkLog_sound (w := (351797 / 2351797)) (n := 12)
    (lo := (150717409 / 500000000)) (hi := (301434819 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1351797 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1351797 / 1000000) = 1/(1000000 / 1351797) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (150717409 / 500000000) (301434819 / 1000000000) (Real.log (1351797 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1351797 / 1000000) = -Real.log (1000000 / 1351797) := by
    rw [show ((1351797 / 1000000) : ℝ) = ((1000000 / 1351797) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (169356 / 390625) ≤ -Real.log (648203 / 1000000) ∧
    -Real.log (648203 / 1000000) ≤ (433551361 / 1000000000) := by
  have h := checkLog_sound (w := (351797 / 1648203)) (n := 12)
    (lo := (169356 / 390625)) (hi := (433551361 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 648203) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 648203) = 1/(648203 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-433551361 / 1000000000) (-169356 / 390625) (Real.log (648203 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (252862729 / 250000000) ≤ -Real.log (100000000000 / 274958754537) ∧
    -Real.log (100000000000 / 274958754537) ≤ (505725459 / 500000000) := by
  have h := checkLog_sound (w := (74958754537 / 474958754537)) (n := 12)
    (lo := (39787967 / 125000000)) (hi := (318303737 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((274958754537 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(274958754537 / 200000000000) = 1/(100000000000 / 274958754537) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (252862729 / 250000000) (505725459 / 500000000) (Real.log (274958754537 / 100000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (274958754537 / 100000000000) = -Real.log (100000000000 / 274958754537) := by
    rw [show ((274958754537 / 100000000000) : ℝ) = ((100000000000 / 274958754537) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1013732653 / 1000000000) ≤ -Real.log (500000000000 / 1377934272301) ∧
    -Real.log (500000000000 / 1377934272301) ≤ (202746531 / 200000000) := by
  have h := checkLog_sound (w := (377934272301 / 2377934272301)) (n := 12)
    (lo := (320585473 / 1000000000)) (hi := (160292737 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1377934272301 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1377934272301 / 1000000000000) = 1/(500000000000 / 1377934272301) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1013732653 / 1000000000) (202746531 / 200000000) (Real.log (1377934272301 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1377934272301 / 500000000000) = -Real.log (500000000000 / 1377934272301) := by
    rw [show ((1377934272301 / 500000000000) : ℝ) = ((500000000000 / 1377934272301) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (733258863 / 1000000000) ≤ -Real.log (3906250000 / 8132242357) ∧
    -Real.log (3906250000 / 8132242357) ≤ (146651773 / 200000000) := by
  have h := checkLog_sound (w := (319742357 / 15944742357)) (n := 12)
    (lo := (40111683 / 1000000000)) (hi := (10027921 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8132242357 / 7812500000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(8132242357 / 7812500000) = 1/(3906250000 / 8132242357) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (733258863 / 1000000000) (146651773 / 200000000) (Real.log (8132242357 / 3906250000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (8132242357 / 3906250000) = -Real.log (3906250000 / 8132242357) := by
    rw [show ((8132242357 / 3906250000) : ℝ) = ((3906250000 / 8132242357) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (734986177 / 1000000000) ≤ -Real.log (500000000000 / 1042726584111) ∧
    -Real.log (500000000000 / 1042726584111) ≤ (734986179 / 1000000000) := by
  have h := checkLog_sound (w := (42726584111 / 2042726584111)) (n := 12)
    (lo := (41838997 / 1000000000)) (hi := (20919499 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1042726584111 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1042726584111 / 1000000000000) = 1/(500000000000 / 1042726584111) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (734986177 / 1000000000) (734986179 / 1000000000) (Real.log (1042726584111 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1042726584111 / 500000000000) = -Real.log (500000000000 / 1042726584111) := by
    rw [show ((1042726584111 / 500000000000) : ℝ) = ((500000000000 / 1042726584111) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0167
