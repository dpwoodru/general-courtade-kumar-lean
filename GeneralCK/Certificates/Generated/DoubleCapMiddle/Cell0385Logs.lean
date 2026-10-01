import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0385
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

theorem reflection_log_1_neg : (50954343 / 250000000) ≤ -Real.log (2048 / 2511) ∧
    -Real.log (2048 / 2511) ≤ (203817373 / 1000000000) := by
  have h := checkLog_sound (w := (463 / 4559)) (n := 12)
    (lo := (50954343 / 250000000)) (hi := (203817373 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2511 / 2048) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2511 / 2048) = 1/(2048 / 2511) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (50954343 / 250000000) (203817373 / 1000000000) (Real.log (2511 / 2048)) := by
  have h := reflection_log_1_neg
  have he : Real.log (2511 / 2048) = -Real.log (2048 / 2511) := by
    rw [show ((2511 / 2048) : ℝ) = ((2048 / 2511) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (256279299 / 1000000000) ≤ -Real.log (1585 / 2048) ∧
    -Real.log (1585 / 2048) ≤ (2562793 / 10000000) := by
  have h := checkLog_sound (w := (463 / 3633)) (n := 12)
    (lo := (256279299 / 1000000000)) (hi := (2562793 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2048 / 1585) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2048 / 1585) = 1/(1585 / 2048) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-2562793 / 10000000) (-256279299 / 1000000000) (Real.log (1585 / 2048)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (40715679 / 200000000) ≤ -Real.log (1280 / 1569) ∧
    -Real.log (1280 / 1569) ≤ (50894599 / 250000000) := by
  have h := checkLog_sound (w := (289 / 2849)) (n := 12)
    (lo := (40715679 / 200000000)) (hi := (50894599 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1569 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1569 / 1280) = 1/(1280 / 1569) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (40715679 / 200000000) (50894599 / 250000000) (Real.log (1569 / 1280)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1569 / 1280) = -Real.log (1280 / 1569) := by
    rw [show ((1569 / 1280) : ℝ) = ((1280 / 1569) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (127950411 / 500000000) ≤ -Real.log (991 / 1280) ∧
    -Real.log (991 / 1280) ≤ (255900823 / 1000000000) := by
  have h := checkLog_sound (w := (289 / 2271)) (n := 12)
    (lo := (127950411 / 500000000)) (hi := (255900823 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 991) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 991) = 1/(991 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-255900823 / 1000000000) (-127950411 / 500000000) (Real.log (991 / 1280)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (18652207 / 50000000) ≤ -Real.log (1024 / 1487) ∧
    -Real.log (1024 / 1487) ≤ (373044141 / 1000000000) := by
  have h := checkLog_sound (w := (463 / 2511)) (n := 12)
    (lo := (18652207 / 50000000)) (hi := (373044141 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1487 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1487 / 1024) = 1/(1024 / 1487) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (18652207 / 50000000) (373044141 / 1000000000) (Real.log (1487 / 1024)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1487 / 1024) = -Real.log (1024 / 1487) := by
    rw [show ((1487 / 1024) : ℝ) = ((1024 / 1487) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (6017509 / 10000000) ≤ -Real.log (561 / 1024) ∧
    -Real.log (561 / 1024) ≤ (601750901 / 1000000000) := by
  have h := checkLog_sound (w := (463 / 1585)) (n := 12)
    (lo := (6017509 / 10000000)) (hi := (601750901 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 561) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 561) = 1/(561 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-601750901 / 1000000000) (-6017509 / 10000000) (Real.log (561 / 1024)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (186320281 / 500000000) ≤ -Real.log (640 / 929) ∧
    -Real.log (640 / 929) ≤ (372640563 / 1000000000) := by
  have h := checkLog_sound (w := (289 / 1569)) (n := 12)
    (lo := (186320281 / 500000000)) (hi := (372640563 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((929 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(929 / 640) = 1/(640 / 929) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (186320281 / 500000000) (372640563 / 1000000000) (Real.log (929 / 640)) := by
  have h := reflection_log_7_neg
  have he : Real.log (929 / 640) = -Real.log (640 / 929) := by
    rw [show ((929 / 640) : ℝ) = ((640 / 929) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (18771311 / 31250000) ≤ -Real.log (351 / 640) ∧
    -Real.log (351 / 640) ≤ (600681953 / 1000000000) := by
  have h := checkLog_sound (w := (289 / 991)) (n := 12)
    (lo := (18771311 / 31250000)) (hi := (600681953 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 351) = 1/(351 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-600681953 / 1000000000) (-18771311 / 31250000) (Real.log (351 / 640)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (11174089 / 40000000) ≤ -Real.log (1000000 / 1322273) ∧
    -Real.log (1000000 / 1322273) ≤ (139676113 / 500000000) := by
  have h := checkLog_sound (w := (322273 / 2322273)) (n := 12)
    (lo := (11174089 / 40000000)) (hi := (139676113 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1322273 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1322273 / 1000000) = 1/(1000000 / 1322273) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (11174089 / 40000000) (139676113 / 500000000) (Real.log (1322273 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1322273 / 1000000) = -Real.log (1000000 / 1322273) := by
    rw [show ((1322273 / 1000000) : ℝ) = ((1000000 / 1322273) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (194505363 / 500000000) ≤ -Real.log (677727 / 1000000) ∧
    -Real.log (677727 / 1000000) ≤ (389010727 / 1000000000) := by
  have h := checkLog_sound (w := (322273 / 1677727)) (n := 12)
    (lo := (194505363 / 500000000)) (hi := (389010727 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 677727) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 677727) = 1/(677727 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-389010727 / 1000000000) (-194505363 / 500000000) (Real.log (677727 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (139837929 / 500000000) ≤ -Real.log (1000000 / 1322701) ∧
    -Real.log (1000000 / 1322701) ≤ (279675859 / 1000000000) := by
  have h := checkLog_sound (w := (322701 / 2322701)) (n := 12)
    (lo := (139837929 / 500000000)) (hi := (279675859 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1322701 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1322701 / 1000000) = 1/(1000000 / 1322701) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (139837929 / 500000000) (279675859 / 1000000000) (Real.log (1322701 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1322701 / 1000000) = -Real.log (1000000 / 1322701) := by
    rw [show ((1322701 / 1000000) : ℝ) = ((1000000 / 1322701) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (389642449 / 1000000000) ≤ -Real.log (677299 / 1000000) ∧
    -Real.log (677299 / 1000000) ≤ (7792849 / 20000000) := by
  have h := checkLog_sound (w := (322701 / 1677299)) (n := 12)
    (lo := (389642449 / 1000000000)) (hi := (7792849 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 677299) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 677299) = 1/(677299 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-7792849 / 20000000) (-389642449 / 1000000000) (Real.log (677299 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (2107689 / 10000000) ≤ -Real.log (1000000 / 1234627) ∧
    -Real.log (1000000 / 1234627) ≤ (210768901 / 1000000000) := by
  have h := checkLog_sound (w := (234627 / 2234627)) (n := 12)
    (lo := (2107689 / 10000000)) (hi := (210768901 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1234627 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1234627 / 1000000) = 1/(1000000 / 1234627) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (2107689 / 10000000) (210768901 / 1000000000) (Real.log (1234627 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1234627 / 1000000) = -Real.log (1000000 / 1234627) := by
    rw [show ((1234627 / 1000000) : ℝ) = ((1000000 / 1234627) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (133695991 / 500000000) ≤ -Real.log (765373 / 1000000) ∧
    -Real.log (765373 / 1000000) ≤ (267391983 / 1000000000) := by
  have h := checkLog_sound (w := (234627 / 1765373)) (n := 12)
    (lo := (133695991 / 500000000)) (hi := (267391983 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 765373) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 765373) = 1/(765373 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-267391983 / 1000000000) (-133695991 / 500000000) (Real.log (765373 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (211036151 / 1000000000) ≤ -Real.log (1000000 / 1234957) ∧
    -Real.log (1000000 / 1234957) ≤ (26379519 / 125000000) := by
  have h := checkLog_sound (w := (234957 / 2234957)) (n := 12)
    (lo := (211036151 / 1000000000)) (hi := (26379519 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1234957 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1234957 / 1000000) = 1/(1000000 / 1234957) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (211036151 / 1000000000) (26379519 / 125000000) (Real.log (1234957 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1234957 / 1000000) = -Real.log (1000000 / 1234957) := by
    rw [show ((1234957 / 1000000) : ℝ) = ((1000000 / 1234957) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (267823237 / 1000000000) ≤ -Real.log (765043 / 1000000) ∧
    -Real.log (765043 / 1000000) ≤ (133911619 / 500000000) := by
  have h := checkLog_sound (w := (234957 / 1765043)) (n := 12)
    (lo := (267823237 / 1000000000)) (hi := (133911619 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 765043) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 765043) = 1/(765043 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-133911619 / 500000000) (-267823237 / 1000000000) (Real.log (765043 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (83545369 / 125000000) ≤ -Real.log (500000000000 / 975520379149) ∧
    -Real.log (500000000000 / 975520379149) ≤ (668362953 / 1000000000) := by
  have h := checkLog_sound (w := (475520379149 / 1475520379149)) (n := 12)
    (lo := (83545369 / 125000000)) (hi := (668362953 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((975520379149 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(975520379149 / 500000000000) = 1/(500000000000 / 975520379149) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (83545369 / 125000000) (668362953 / 1000000000) (Real.log (975520379149 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (975520379149 / 500000000000) = -Real.log (500000000000 / 975520379149) := by
    rw [show ((975520379149 / 500000000000) : ℝ) = ((500000000000 / 975520379149) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (669318307 / 1000000000) ≤ -Real.log (500000000000 / 976452792637) ∧
    -Real.log (500000000000 / 976452792637) ≤ (167329577 / 250000000) := by
  have h := checkLog_sound (w := (476452792637 / 1476452792637)) (n := 12)
    (lo := (669318307 / 1000000000)) (hi := (167329577 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((976452792637 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(976452792637 / 500000000000) = 1/(500000000000 / 976452792637) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (669318307 / 1000000000) (167329577 / 250000000) (Real.log (976452792637 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (976452792637 / 500000000000) = -Real.log (500000000000 / 976452792637) := by
    rw [show ((976452792637 / 500000000000) : ℝ) = ((500000000000 / 976452792637) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (239080441 / 500000000) ≤ -Real.log (500000000000 / 806552491399) ∧
    -Real.log (500000000000 / 806552491399) ≤ (478160883 / 1000000000) := by
  have h := checkLog_sound (w := (306552491399 / 1306552491399)) (n := 12)
    (lo := (239080441 / 500000000)) (hi := (478160883 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((806552491399 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(806552491399 / 500000000000) = 1/(500000000000 / 806552491399) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (239080441 / 500000000) (478160883 / 1000000000) (Real.log (806552491399 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (806552491399 / 500000000000) = -Real.log (500000000000 / 806552491399) := by
    rw [show ((806552491399 / 500000000000) : ℝ) = ((500000000000 / 806552491399) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (478859389 / 1000000000) ≤ -Real.log (2500000000 / 4035580353) ∧
    -Real.log (2500000000 / 4035580353) ≤ (47885939 / 100000000) := by
  have h := checkLog_sound (w := (1535580353 / 6535580353)) (n := 12)
    (lo := (478859389 / 1000000000)) (hi := (47885939 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4035580353 / 2500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4035580353 / 2500000000) = 1/(2500000000 / 4035580353) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (478859389 / 1000000000) (47885939 / 100000000) (Real.log (4035580353 / 2500000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (4035580353 / 2500000000) = -Real.log (2500000000 / 4035580353) := by
    rw [show ((4035580353 / 2500000000) : ℝ) = ((2500000000 / 4035580353) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0385
