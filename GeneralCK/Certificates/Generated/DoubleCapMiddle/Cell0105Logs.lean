import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0105
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

theorem reflection_log_1_neg : (32919133 / 100000000) ≤ -Real.log (1280 / 1779) ∧
    -Real.log (1280 / 1779) ≤ (329191331 / 1000000000) := by
  have h := checkLog_sound (w := (499 / 3059)) (n := 12)
    (lo := (32919133 / 100000000)) (hi := (329191331 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1779 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1779 / 1280) = 1/(1280 / 1779) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (32919133 / 100000000) (329191331 / 1000000000) (Real.log (1779 / 1280)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1779 / 1280) = -Real.log (1280 / 1779) := by
    rw [show ((1779 / 1280) : ℝ) = ((1280 / 1779) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (494040207 / 1000000000) ≤ -Real.log (781 / 1280) ∧
    -Real.log (781 / 1280) ≤ (30877513 / 62500000) := by
  have h := checkLog_sound (w := (499 / 2061)) (n := 12)
    (lo := (494040207 / 1000000000)) (hi := (30877513 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 781) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 781) = 1/(781 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-30877513 / 62500000) (-494040207 / 1000000000) (Real.log (781 / 1280)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (82086951 / 250000000) ≤ -Real.log (512 / 711) ∧
    -Real.log (512 / 711) ≤ (65669561 / 200000000) := by
  have h := checkLog_sound (w := (199 / 1223)) (n := 12)
    (lo := (82086951 / 250000000)) (hi := (65669561 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((711 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(711 / 512) = 1/(512 / 711) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (82086951 / 250000000) (65669561 / 200000000) (Real.log (711 / 512)) := by
  have h := reflection_log_3_neg
  have he : Real.log (711 / 512) = -Real.log (512 / 711) := by
    rw [show ((711 / 512) : ℝ) = ((512 / 711) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (246060717 / 500000000) ≤ -Real.log (313 / 512) ∧
    -Real.log (313 / 512) ≤ (98424287 / 200000000) := by
  have h := checkLog_sound (w := (199 / 825)) (n := 12)
    (lo := (246060717 / 500000000)) (hi := (98424287 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 313) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 313) = 1/(313 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-98424287 / 200000000) (-246060717 / 500000000) (Real.log (313 / 512)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (576437787 / 1000000000) ≤ -Real.log (640 / 1139) ∧
    -Real.log (640 / 1139) ≤ (144109447 / 250000000) := by
  have h := checkLog_sound (w := (499 / 1779)) (n := 12)
    (lo := (576437787 / 1000000000)) (hi := (144109447 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1139 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1139 / 640) = 1/(640 / 1139) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (576437787 / 1000000000) (144109447 / 250000000) (Real.log (1139 / 640)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1139 / 640) = -Real.log (640 / 1139) := by
    rw [show ((1139 / 640) : ℝ) = ((640 / 1139) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (378177071 / 250000000) ≤ -Real.log (141 / 640) ∧
    -Real.log (141 / 640) ≤ (1512708287 / 1000000000) := by
  have h := checkLog_sound (w := (19 / 301)) (n := 12)
    (lo := (31603481 / 250000000)) (hi := (5056557 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 141) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(160 / 141) = 1/(141 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1512708287 / 1000000000) (-378177071 / 250000000) (Real.log (141 / 640)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (287559987 / 500000000) ≤ -Real.log (256 / 455) ∧
    -Real.log (256 / 455) ≤ (23004799 / 40000000) := by
  have h := checkLog_sound (w := (199 / 711)) (n := 12)
    (lo := (287559987 / 500000000)) (hi := (23004799 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((455 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(455 / 256) = 1/(256 / 455) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (287559987 / 500000000) (23004799 / 40000000) (Real.log (455 / 256)) := by
  have h := reflection_log_7_neg
  have he : Real.log (455 / 256) = -Real.log (256 / 455) := by
    rw [show ((455 / 256) : ℝ) = ((256 / 455) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (60085047 / 40000000) ≤ -Real.log (57 / 256) ∧
    -Real.log (57 / 256) ≤ (751063089 / 500000000) := by
  have h := checkLog_sound (w := (7 / 121)) (n := 12)
    (lo := (23166363 / 200000000)) (hi := (14478977 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((64 / 57) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(64 / 57) = 1/(57 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-751063089 / 500000000) (-60085047 / 40000000) (Real.log (57 / 256)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (450376649 / 1000000000) ≤ -Real.log (1000000 / 1568903) ∧
    -Real.log (1000000 / 1568903) ≤ (9007533 / 20000000) := by
  have h := checkLog_sound (w := (568903 / 2568903)) (n := 12)
    (lo := (450376649 / 1000000000)) (hi := (9007533 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1568903 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1568903 / 1000000) = 1/(1000000 / 1568903) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (450376649 / 1000000000) (9007533 / 20000000) (Real.log (1568903 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1568903 / 1000000) = -Real.log (1000000 / 1568903) := by
    rw [show ((1568903 / 1000000) : ℝ) = ((1000000 / 1568903) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (168284431 / 200000000) ≤ -Real.log (431097 / 1000000) ∧
    -Real.log (431097 / 1000000) ≤ (841422157 / 1000000000) := by
  have h := checkLog_sound (w := (68903 / 931097)) (n := 12)
    (lo := (5930999 / 40000000)) (hi := (4633593 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 431097) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 431097) = 1/(431097 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-841422157 / 1000000000) (-168284431 / 200000000) (Real.log (431097 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (451578677 / 1000000000) ≤ -Real.log (100000 / 157079) ∧
    -Real.log (100000 / 157079) ≤ (225789339 / 500000000) := by
  have h := checkLog_sound (w := (57079 / 257079)) (n := 12)
    (lo := (451578677 / 1000000000)) (hi := (225789339 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((157079 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(157079 / 100000) = 1/(100000 / 157079) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (451578677 / 1000000000) (225789339 / 500000000) (Real.log (157079 / 100000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (157079 / 100000) = -Real.log (100000 / 157079) := by
    rw [show ((157079 / 100000) : ℝ) = ((100000 / 157079) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (105726121 / 125000000) ≤ -Real.log (42921 / 100000) ∧
    -Real.log (42921 / 100000) ≤ (84580897 / 100000000) := by
  have h := checkLog_sound (w := (7079 / 92921)) (n := 12)
    (lo := (38165447 / 250000000)) (hi := (152661789 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 42921) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(50000 / 42921) = 1/(42921 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-84580897 / 100000000) (-105726121 / 125000000) (Real.log (42921 / 100000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (365754301 / 1000000000) ≤ -Real.log (1000000 / 1441601) ∧
    -Real.log (1000000 / 1441601) ≤ (182877151 / 500000000) := by
  have h := checkLog_sound (w := (441601 / 2441601)) (n := 12)
    (lo := (365754301 / 1000000000)) (hi := (182877151 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1441601 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1441601 / 1000000) = 1/(1000000 / 1441601) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (365754301 / 1000000000) (182877151 / 500000000) (Real.log (1441601 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1441601 / 1000000) = -Real.log (1000000 / 1441601) := by
    rw [show ((1441601 / 1000000) : ℝ) = ((1000000 / 1441601) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (291340759 / 500000000) ≤ -Real.log (558399 / 1000000) ∧
    -Real.log (558399 / 1000000) ≤ (582681519 / 1000000000) := by
  have h := checkLog_sound (w := (441601 / 1558399)) (n := 12)
    (lo := (291340759 / 500000000)) (hi := (582681519 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 558399) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 558399) = 1/(558399 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-582681519 / 1000000000) (-291340759 / 500000000) (Real.log (558399 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (366967493 / 1000000000) ≤ -Real.log (1000000 / 1443351) ∧
    -Real.log (1000000 / 1443351) ≤ (183483747 / 500000000) := by
  have h := checkLog_sound (w := (443351 / 2443351)) (n := 12)
    (lo := (366967493 / 1000000000)) (hi := (183483747 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1443351 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1443351 / 1000000) = 1/(1000000 / 1443351) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (366967493 / 1000000000) (183483747 / 500000000) (Real.log (1443351 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1443351 / 1000000) = -Real.log (1000000 / 1443351) := by
    rw [show ((1443351 / 1000000) : ℝ) = ((1000000 / 1443351) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (585820399 / 1000000000) ≤ -Real.log (556649 / 1000000) ∧
    -Real.log (556649 / 1000000) ≤ (1464551 / 2500000) := by
  have h := checkLog_sound (w := (443351 / 1556649)) (n := 12)
    (lo := (585820399 / 1000000000)) (hi := (1464551 / 2500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 556649) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 556649) = 1/(556649 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-1464551 / 2500000) (-585820399 / 1000000000) (Real.log (556649 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (322949701 / 250000000) ≤ -Real.log (500000000000 / 1819663555997) ∧
    -Real.log (500000000000 / 1819663555997) ≤ (645899403 / 500000000) := by
  have h := checkLog_sound (w := (819663555997 / 2819663555997)) (n := 12)
    (lo := (74831453 / 125000000)) (hi := (4789213 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1819663555997 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1819663555997 / 1000000000000) = 1/(500000000000 / 1819663555997) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (322949701 / 250000000) (645899403 / 500000000) (Real.log (1819663555997 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1819663555997 / 500000000000) = -Real.log (500000000000 / 1819663555997) := by
    rw [show ((1819663555997 / 500000000000) : ℝ) = ((500000000000 / 1819663555997) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (648693823 / 500000000) ≤ -Real.log (500000000000 / 1829861839193) ∧
    -Real.log (500000000000 / 1829861839193) ≤ (10135841 / 7812500) := by
  have h := checkLog_sound (w := (829861839193 / 2829861839193)) (n := 12)
    (lo := (302120233 / 500000000)) (hi := (604240467 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1829861839193 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1829861839193 / 1000000000000) = 1/(500000000000 / 1829861839193) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (648693823 / 500000000) (10135841 / 7812500) (Real.log (1829861839193 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1829861839193 / 500000000000) = -Real.log (500000000000 / 1829861839193) := by
    rw [show ((1829861839193 / 500000000000) : ℝ) = ((500000000000 / 1829861839193) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (948435819 / 1000000000) ≤ -Real.log (500000000000 / 1290834152639) ∧
    -Real.log (500000000000 / 1290834152639) ≤ (948435821 / 1000000000) := by
  have h := checkLog_sound (w := (290834152639 / 2290834152639)) (n := 12)
    (lo := (255288639 / 1000000000)) (hi := (797777 / 3125000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1290834152639 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1290834152639 / 1000000000000) = 1/(500000000000 / 1290834152639) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (948435819 / 1000000000) (948435821 / 1000000000) (Real.log (1290834152639 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (1290834152639 / 500000000000) = -Real.log (500000000000 / 1290834152639) := by
    rw [show ((1290834152639 / 500000000000) : ℝ) = ((500000000000 / 1290834152639) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (238196973 / 250000000) ≤ -Real.log (125000000000 / 324116049791) ∧
    -Real.log (125000000000 / 324116049791) ≤ (476393947 / 500000000) := by
  have h := checkLog_sound (w := (74116049791 / 574116049791)) (n := 12)
    (lo := (32455089 / 125000000)) (hi := (259640713 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((324116049791 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(324116049791 / 250000000000) = 1/(125000000000 / 324116049791) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (238196973 / 250000000) (476393947 / 500000000) (Real.log (324116049791 / 125000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (324116049791 / 125000000000) = -Real.log (125000000000 / 324116049791) := by
    rw [show ((324116049791 / 125000000000) : ℝ) = ((125000000000 / 324116049791) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0105
