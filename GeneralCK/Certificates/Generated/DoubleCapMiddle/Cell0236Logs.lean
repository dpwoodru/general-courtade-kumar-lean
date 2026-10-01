import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0236
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

theorem reflection_log_1_neg : (249359393 / 1000000000) ≤ -Real.log (512 / 657) ∧
    -Real.log (512 / 657) ≤ (124679697 / 500000000) := by
  have h := checkLog_sound (w := (145 / 1169)) (n := 12)
    (lo := (249359393 / 1000000000)) (hi := (124679697 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((657 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(657 / 512) = 1/(512 / 657) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (249359393 / 1000000000) (124679697 / 500000000) (Real.log (657 / 512)) := by
  have h := reflection_log_1_neg
  have he : Real.log (657 / 512) = -Real.log (512 / 657) := by
    rw [show ((657 / 512) : ℝ) = ((512 / 657) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (41620347 / 125000000) ≤ -Real.log (367 / 512) ∧
    -Real.log (367 / 512) ≤ (332962777 / 1000000000) := by
  have h := checkLog_sound (w := (145 / 879)) (n := 12)
    (lo := (41620347 / 125000000)) (hi := (332962777 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 367) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 367) = 1/(367 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-332962777 / 1000000000) (-41620347 / 125000000) (Real.log (367 / 512)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (62225667 / 250000000) ≤ -Real.log (5120 / 6567) ∧
    -Real.log (5120 / 6567) ≤ (248902669 / 1000000000) := by
  have h := checkLog_sound (w := (1447 / 11687)) (n := 12)
    (lo := (62225667 / 250000000)) (hi := (248902669 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6567 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6567 / 5120) = 1/(5120 / 6567) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (62225667 / 250000000) (248902669 / 1000000000) (Real.log (6567 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6567 / 5120) = -Real.log (5120 / 6567) := by
    rw [show ((6567 / 5120) : ℝ) = ((5120 / 6567) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (41518209 / 125000000) ≤ -Real.log (3673 / 5120) ∧
    -Real.log (3673 / 5120) ≤ (332145673 / 1000000000) := by
  have h := checkLog_sound (w := (1447 / 8793)) (n := 12)
    (lo := (41518209 / 125000000)) (hi := (332145673 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3673) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3673) = 1/(3673 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-332145673 / 1000000000) (-41518209 / 125000000) (Real.log (3673 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (224391991 / 500000000) ≤ -Real.log (256 / 401) ∧
    -Real.log (256 / 401) ≤ (448783983 / 1000000000) := by
  have h := checkLog_sound (w := (145 / 657)) (n := 12)
    (lo := (224391991 / 500000000)) (hi := (448783983 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((401 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(401 / 256) = 1/(256 / 401) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (224391991 / 500000000) (448783983 / 1000000000) (Real.log (401 / 256)) := by
  have h := reflection_log_5_neg
  have he : Real.log (401 / 256) = -Real.log (256 / 401) := by
    rw [show ((401 / 256) : ℝ) = ((256 / 401) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (417823621 / 500000000) ≤ -Real.log (111 / 256) ∧
    -Real.log (111 / 256) ≤ (208911811 / 250000000) := by
  have h := checkLog_sound (w := (17 / 239)) (n := 12)
    (lo := (71250031 / 500000000)) (hi := (142500063 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((128 / 111) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(128 / 111) = 1/(111 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-208911811 / 250000000) (-417823621 / 500000000) (Real.log (111 / 256)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (448035573 / 1000000000) ≤ -Real.log (2560 / 4007) ∧
    -Real.log (2560 / 4007) ≤ (224017787 / 500000000) := by
  have h := checkLog_sound (w := (1447 / 6567)) (n := 12)
    (lo := (448035573 / 1000000000)) (hi := (224017787 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4007 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4007 / 2560) = 1/(2560 / 4007) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (448035573 / 1000000000) (224017787 / 500000000) (Real.log (4007 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (4007 / 2560) = -Real.log (2560 / 4007) := by
    rw [show ((4007 / 2560) : ℝ) = ((2560 / 4007) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (166589637 / 200000000) ≤ -Real.log (1113 / 2560) ∧
    -Real.log (1113 / 2560) ≤ (832948187 / 1000000000) := by
  have h := checkLog_sound (w := (167 / 2393)) (n := 12)
    (lo := (27960201 / 200000000)) (hi := (69900503 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 1113) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 1113) = 1/(1113 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-832948187 / 1000000000) (-166589637 / 200000000) (Real.log (1113 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (340648503 / 1000000000) ≤ -Real.log (1000000 / 1405859) ∧
    -Real.log (1000000 / 1405859) ≤ (42581063 / 125000000) := by
  have h := checkLog_sound (w := (405859 / 2405859)) (n := 12)
    (lo := (340648503 / 1000000000)) (hi := (42581063 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1405859 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1405859 / 1000000) = 1/(1000000 / 1405859) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (340648503 / 1000000000) (42581063 / 125000000) (Real.log (1405859 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1405859 / 1000000) = -Real.log (1000000 / 1405859) := by
    rw [show ((1405859 / 1000000) : ℝ) = ((1000000 / 1405859) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (260319307 / 500000000) ≤ -Real.log (594141 / 1000000) ∧
    -Real.log (594141 / 1000000) ≤ (104127723 / 200000000) := by
  have h := checkLog_sound (w := (405859 / 1594141)) (n := 12)
    (lo := (260319307 / 500000000)) (hi := (104127723 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 594141) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 594141) = 1/(594141 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-104127723 / 200000000) (-260319307 / 500000000) (Real.log (594141 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (341269283 / 1000000000) ≤ -Real.log (250000 / 351683) ∧
    -Real.log (250000 / 351683) ≤ (85317321 / 250000000) := by
  have h := checkLog_sound (w := (101683 / 601683)) (n := 12)
    (lo := (341269283 / 1000000000)) (hi := (85317321 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((351683 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(351683 / 250000) = 1/(250000 / 351683) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (341269283 / 1000000000) (85317321 / 250000000) (Real.log (351683 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (351683 / 250000) = -Real.log (250000 / 351683) := by
    rw [show ((351683 / 250000) : ℝ) = ((250000 / 351683) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (261054521 / 500000000) ≤ -Real.log (148317 / 250000) ∧
    -Real.log (148317 / 250000) ≤ (522109043 / 1000000000) := by
  have h := checkLog_sound (w := (101683 / 398317)) (n := 12)
    (lo := (261054521 / 500000000)) (hi := (522109043 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 148317) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 148317) = 1/(148317 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-522109043 / 1000000000) (-261054521 / 500000000) (Real.log (148317 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (262884129 / 1000000000) ≤ -Real.log (250000 / 325169) ∧
    -Real.log (250000 / 325169) ≤ (26288413 / 100000000) := by
  have h := checkLog_sound (w := (75169 / 575169)) (n := 12)
    (lo := (262884129 / 1000000000)) (hi := (26288413 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((325169 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(325169 / 250000) = 1/(250000 / 325169) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (262884129 / 1000000000) (26288413 / 100000000) (Real.log (325169 / 250000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (325169 / 250000) = -Real.log (250000 / 325169) := by
    rw [show ((325169 / 250000) : ℝ) = ((250000 / 325169) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (89410281 / 250000000) ≤ -Real.log (174831 / 250000) ∧
    -Real.log (174831 / 250000) ≤ (2861129 / 8000000) := by
  have h := checkLog_sound (w := (75169 / 424831)) (n := 12)
    (lo := (89410281 / 250000000)) (hi := (2861129 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 174831) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 174831) = 1/(174831 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-2861129 / 8000000) (-89410281 / 250000000) (Real.log (174831 / 250000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (263429081 / 1000000000) ≤ -Real.log (200000 / 260277) ∧
    -Real.log (200000 / 260277) ≤ (131714541 / 500000000) := by
  have h := checkLog_sound (w := (60277 / 460277)) (n := 12)
    (lo := (263429081 / 1000000000)) (hi := (131714541 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((260277 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(260277 / 200000) = 1/(200000 / 260277) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (263429081 / 1000000000) (131714541 / 500000000) (Real.log (260277 / 200000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (260277 / 200000) = -Real.log (200000 / 260277) := by
    rw [show ((260277 / 200000) : ℝ) = ((200000 / 260277) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (14346219 / 40000000) ≤ -Real.log (139723 / 200000) ∧
    -Real.log (139723 / 200000) ≤ (89663869 / 250000000) := by
  have h := checkLog_sound (w := (60277 / 339723)) (n := 12)
    (lo := (14346219 / 40000000)) (hi := (89663869 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 139723) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 139723) = 1/(139723 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-89663869 / 250000000) (-14346219 / 40000000) (Real.log (139723 / 200000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (861287117 / 1000000000) ≤ -Real.log (500000000000 / 1183102159251) ∧
    -Real.log (500000000000 / 1183102159251) ≤ (861287119 / 1000000000) := by
  have h := checkLog_sound (w := (183102159251 / 2183102159251)) (n := 12)
    (lo := (168139937 / 1000000000)) (hi := (84069969 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1183102159251 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1183102159251 / 1000000000000) = 1/(500000000000 / 1183102159251) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (861287117 / 1000000000) (861287119 / 1000000000) (Real.log (1183102159251 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1183102159251 / 500000000000) = -Real.log (500000000000 / 1183102159251) := by
    rw [show ((1183102159251 / 500000000000) : ℝ) = ((500000000000 / 1183102159251) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (431689163 / 500000000) ≤ -Real.log (500000000000 / 1185578861493) ∧
    -Real.log (500000000000 / 1185578861493) ≤ (107922291 / 125000000) := by
  have h := checkLog_sound (w := (185578861493 / 2185578861493)) (n := 12)
    (lo := (85115573 / 500000000)) (hi := (170231147 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1185578861493 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1185578861493 / 1000000000000) = 1/(500000000000 / 1185578861493) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (431689163 / 500000000) (107922291 / 125000000) (Real.log (1185578861493 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1185578861493 / 500000000000) = -Real.log (500000000000 / 1185578861493) := by
    rw [show ((1185578861493 / 500000000000) : ℝ) = ((500000000000 / 1185578861493) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (310262627 / 500000000) ≤ -Real.log (500000000000 / 929952353987) ∧
    -Real.log (500000000000 / 929952353987) ≤ (124105051 / 200000000) := by
  have h := checkLog_sound (w := (429952353987 / 1429952353987)) (n := 12)
    (lo := (310262627 / 500000000)) (hi := (124105051 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((929952353987 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(929952353987 / 500000000000) = 1/(500000000000 / 929952353987) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (310262627 / 500000000) (124105051 / 200000000) (Real.log (929952353987 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (929952353987 / 500000000000) = -Real.log (500000000000 / 929952353987) := by
    rw [show ((929952353987 / 500000000000) : ℝ) = ((500000000000 / 929952353987) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (622084557 / 1000000000) ≤ -Real.log (125000000000 / 232850890691) ∧
    -Real.log (125000000000 / 232850890691) ≤ (311042279 / 500000000) := by
  have h := checkLog_sound (w := (107850890691 / 357850890691)) (n := 12)
    (lo := (622084557 / 1000000000)) (hi := (311042279 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((232850890691 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(232850890691 / 125000000000) = 1/(125000000000 / 232850890691) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (622084557 / 1000000000) (311042279 / 500000000) (Real.log (232850890691 / 125000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (232850890691 / 125000000000) = -Real.log (125000000000 / 232850890691) := by
    rw [show ((232850890691 / 125000000000) : ℝ) = ((125000000000 / 232850890691) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0236
