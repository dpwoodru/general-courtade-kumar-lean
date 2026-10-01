import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell027
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

theorem reflection_log_1_neg : (59045791 / 250000000) ≤ -Real.log (1280 / 1621) ∧
    -Real.log (1280 / 1621) ≤ (47236633 / 200000000) := by
  have h := checkLog_sound (w := (341 / 2901)) (n := 12)
    (lo := (59045791 / 250000000)) (hi := (47236633 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1621 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1621 / 1280) = 1/(1280 / 1621) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (59045791 / 250000000) (47236633 / 200000000) (Real.log (1621 / 1280)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1621 / 1280) = -Real.log (1280 / 1621) := by
    rw [show ((1621 / 1280) : ℝ) = ((1280 / 1621) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (309799877 / 1000000000) ≤ -Real.log (939 / 1280) ∧
    -Real.log (939 / 1280) ≤ (154899939 / 500000000) := by
  have h := checkLog_sound (w := (341 / 2219)) (n := 12)
    (lo := (309799877 / 1000000000)) (hi := (154899939 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 939) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 939) = 1/(939 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-154899939 / 500000000) (-309799877 / 1000000000) (Real.log (939 / 1280)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (11786019 / 50000000) ≤ -Real.log (5120 / 6481) ∧
    -Real.log (5120 / 6481) ≤ (235720381 / 1000000000) := by
  have h := checkLog_sound (w := (1361 / 11601)) (n := 12)
    (lo := (11786019 / 50000000)) (hi := (235720381 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6481 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6481 / 5120) = 1/(5120 / 6481) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (11786019 / 50000000) (235720381 / 1000000000) (Real.log (6481 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6481 / 5120) = -Real.log (5120 / 6481) := by
    rw [show ((6481 / 5120) : ℝ) = ((5120 / 6481) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (154500737 / 500000000) ≤ -Real.log (3759 / 5120) ∧
    -Real.log (3759 / 5120) ≤ (12360059 / 40000000) := by
  have h := checkLog_sound (w := (1361 / 8879)) (n := 12)
    (lo := (154500737 / 500000000)) (hi := (12360059 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3759) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3759) = 1/(3759 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-12360059 / 40000000) (-154500737 / 500000000) (Real.log (3759 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (172719773 / 1000000000) ≤ -Real.log (1000000 / 1188533) ∧
    -Real.log (1000000 / 1188533) ≤ (86359887 / 500000000) := by
  have h := checkLog_sound (w := (188533 / 2188533)) (n := 12)
    (lo := (172719773 / 1000000000)) (hi := (86359887 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1188533 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1188533 / 1000000) = 1/(1000000 / 1188533) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (172719773 / 1000000000) (86359887 / 500000000) (Real.log (1188533 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1188533 / 1000000) = -Real.log (1000000 / 1188533) := by
    rw [show ((1188533 / 1000000) : ℝ) = ((1000000 / 1188533) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (104455779 / 500000000) ≤ -Real.log (811467 / 1000000) ∧
    -Real.log (811467 / 1000000) ≤ (208911559 / 1000000000) := by
  have h := checkLog_sound (w := (188533 / 1811467)) (n := 12)
    (lo := (104455779 / 500000000)) (hi := (208911559 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 811467) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 811467) = 1/(811467 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-208911559 / 1000000000) (-104455779 / 500000000) (Real.log (811467 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (86536123 / 500000000) ≤ -Real.log (125000 / 148619) ∧
    -Real.log (125000 / 148619) ≤ (173072247 / 1000000000) := by
  have h := checkLog_sound (w := (23619 / 273619)) (n := 12)
    (lo := (86536123 / 500000000)) (hi := (173072247 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((148619 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(148619 / 125000) = 1/(125000 / 148619) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (86536123 / 500000000) (173072247 / 1000000000) (Real.log (148619 / 125000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (148619 / 125000) = -Real.log (125000 / 148619) := by
    rw [show ((148619 / 125000) : ℝ) = ((125000 / 148619) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (5235701 / 25000000) ≤ -Real.log (101381 / 125000) ∧
    -Real.log (101381 / 125000) ≤ (209428041 / 1000000000) := by
  have h := checkLog_sound (w := (23619 / 226381)) (n := 12)
    (lo := (5235701 / 25000000)) (hi := (209428041 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 101381) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 101381) = 1/(101381 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-209428041 / 1000000000) (-5235701 / 25000000) (Real.log (101381 / 125000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (63157269 / 500000000) ≤ -Real.log (1000000 / 1134639) ∧
    -Real.log (1000000 / 1134639) ≤ (126314539 / 1000000000) := by
  have h := checkLog_sound (w := (134639 / 2134639)) (n := 12)
    (lo := (63157269 / 500000000)) (hi := (126314539 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1134639 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1134639 / 1000000) = 1/(1000000 / 1134639) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (63157269 / 500000000) (126314539 / 1000000000) (Real.log (1134639 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1134639 / 1000000) = -Real.log (1000000 / 1134639) := by
    rw [show ((1134639 / 1000000) : ℝ) = ((1000000 / 1134639) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (72304259 / 500000000) ≤ -Real.log (865361 / 1000000) ∧
    -Real.log (865361 / 1000000) ≤ (144608519 / 1000000000) := by
  have h := checkLog_sound (w := (134639 / 1865361)) (n := 12)
    (lo := (72304259 / 500000000)) (hi := (144608519 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 865361) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 865361) = 1/(865361 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-144608519 / 1000000000) (-72304259 / 500000000) (Real.log (865361 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (126584191 / 1000000000) ≤ -Real.log (200000 / 226989) ∧
    -Real.log (200000 / 226989) ≤ (988939 / 7812500) := by
  have h := checkLog_sound (w := (26989 / 426989)) (n := 12)
    (lo := (126584191 / 1000000000)) (hi := (988939 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((226989 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(226989 / 200000) = 1/(200000 / 226989) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (126584191 / 1000000000) (988939 / 7812500) (Real.log (226989 / 200000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (226989 / 200000) = -Real.log (200000 / 226989) := by
    rw [show ((226989 / 200000) : ℝ) = ((200000 / 226989) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (14496219 / 100000000) ≤ -Real.log (173011 / 200000) ∧
    -Real.log (173011 / 200000) ≤ (144962191 / 1000000000) := by
  have h := checkLog_sound (w := (26989 / 373011)) (n := 12)
    (lo := (14496219 / 100000000)) (hi := (144962191 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 173011) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 173011) = 1/(173011 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-144962191 / 1000000000) (-14496219 / 100000000) (Real.log (173011 / 200000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (272360927 / 500000000) ≤ -Real.log (62500000000 / 107758047353) ∧
    -Real.log (62500000000 / 107758047353) ≤ (108944371 / 200000000) := by
  have h := checkLog_sound (w := (45258047353 / 170258047353)) (n := 12)
    (lo := (272360927 / 500000000)) (hi := (108944371 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((107758047353 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(107758047353 / 62500000000) = 1/(62500000000 / 107758047353) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (272360927 / 500000000) (108944371 / 200000000) (Real.log (107758047353 / 62500000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (107758047353 / 62500000000) = -Real.log (62500000000 / 107758047353) := by
    rw [show ((107758047353 / 62500000000) : ℝ) = ((62500000000 / 107758047353) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (272991521 / 500000000) ≤ -Real.log (50000000000 / 86315228967) ∧
    -Real.log (50000000000 / 86315228967) ≤ (545983043 / 1000000000) := by
  have h := checkLog_sound (w := (36315228967 / 136315228967)) (n := 12)
    (lo := (272991521 / 500000000)) (hi := (545983043 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((86315228967 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(86315228967 / 50000000000) = 1/(50000000000 / 86315228967) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (272991521 / 500000000) (545983043 / 1000000000) (Real.log (86315228967 / 50000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (86315228967 / 50000000000) = -Real.log (50000000000 / 86315228967) := by
    rw [show ((86315228967 / 50000000000) : ℝ) = ((50000000000 / 86315228967) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (381631331 / 1000000000) ≤ -Real.log (100000000000 / 146467200761) ∧
    -Real.log (100000000000 / 146467200761) ≤ (95407833 / 250000000) := by
  have h := checkLog_sound (w := (46467200761 / 246467200761)) (n := 12)
    (lo := (381631331 / 1000000000)) (hi := (95407833 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((146467200761 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(146467200761 / 100000000000) = 1/(100000000000 / 146467200761) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (381631331 / 1000000000) (95407833 / 250000000) (Real.log (146467200761 / 100000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (146467200761 / 100000000000) = -Real.log (100000000000 / 146467200761) := by
    rw [show ((146467200761 / 100000000000) : ℝ) = ((100000000000 / 146467200761) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (382500287 / 1000000000) ≤ -Real.log (100000000000 / 146594529547) ∧
    -Real.log (100000000000 / 146594529547) ≤ (5976567 / 15625000) := by
  have h := checkLog_sound (w := (46594529547 / 246594529547)) (n := 12)
    (lo := (382500287 / 1000000000)) (hi := (5976567 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((146594529547 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(146594529547 / 100000000000) = 1/(100000000000 / 146594529547) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (382500287 / 1000000000) (5976567 / 15625000) (Real.log (146594529547 / 100000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (146594529547 / 100000000000) = -Real.log (100000000000 / 146594529547) := by
    rw [show ((146594529547 / 100000000000) : ℝ) = ((100000000000 / 146594529547) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (16932691 / 62500000) ≤ -Real.log (500000000000 / 655587090243) ∧
    -Real.log (500000000000 / 655587090243) ≤ (270923057 / 1000000000) := by
  have h := checkLog_sound (w := (155587090243 / 1155587090243)) (n := 12)
    (lo := (16932691 / 62500000)) (hi := (270923057 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((655587090243 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(655587090243 / 500000000000) = 1/(500000000000 / 655587090243) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (16932691 / 62500000) (270923057 / 1000000000) (Real.log (655587090243 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (655587090243 / 500000000000) = -Real.log (500000000000 / 655587090243) := by
    rw [show ((655587090243 / 500000000000) : ℝ) = ((500000000000 / 655587090243) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (271546381 / 1000000000) ≤ -Real.log (100000000000 / 131199172307) ∧
    -Real.log (100000000000 / 131199172307) ≤ (135773191 / 500000000) := by
  have h := checkLog_sound (w := (31199172307 / 231199172307)) (n := 12)
    (lo := (271546381 / 1000000000)) (hi := (135773191 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((131199172307 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(131199172307 / 100000000000) = 1/(100000000000 / 131199172307) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (271546381 / 1000000000) (135773191 / 500000000) (Real.log (131199172307 / 100000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (131199172307 / 100000000000) = -Real.log (100000000000 / 131199172307) := by
    rw [show ((131199172307 / 100000000000) : ℝ) = ((100000000000 / 131199172307) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (9188999 / 500000000) ≤ -Real.log (39271593879 / 40000000000) ∧
    -Real.log (39271593879 / 40000000000) ≤ (18377999 / 1000000000) := by
  have h := checkLog_sound (w := (728406121 / 79271593879)) (n := 12)
    (lo := (9188999 / 500000000)) (hi := (18377999 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39271593879) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39271593879) = 1/(39271593879 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-18377999 / 1000000000) (-9188999 / 500000000) (Real.log (39271593879 / 40000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (18293979 / 1000000000) ≤ -Real.log (981872339679 / 1000000000000) ∧
    -Real.log (981872339679 / 1000000000000) ≤ (914699 / 50000000) := by
  have h := checkLog_sound (w := (18127660321 / 1981872339679)) (n := 12)
    (lo := (18293979 / 1000000000)) (hi := (914699 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 981872339679) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 981872339679) = 1/(981872339679 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-914699 / 50000000) (-18293979 / 1000000000) (Real.log (981872339679 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell027
