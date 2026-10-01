import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0277
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

theorem reflection_log_1_neg : (230460467 / 1000000000) ≤ -Real.log (5120 / 6447) ∧
    -Real.log (5120 / 6447) ≤ (57615117 / 250000000) := by
  have h := checkLog_sound (w := (1327 / 11567)) (n := 12)
    (lo := (230460467 / 1000000000)) (hi := (57615117 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6447 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6447 / 5120) = 1/(5120 / 6447) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (230460467 / 1000000000) (57615117 / 250000000) (Real.log (6447 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6447 / 5120) = -Real.log (5120 / 6447) := by
    rw [show ((6447 / 5120) : ℝ) = ((5120 / 6447) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (37499647 / 125000000) ≤ -Real.log (3793 / 5120) ∧
    -Real.log (3793 / 5120) ≤ (299997177 / 1000000000) := by
  have h := checkLog_sound (w := (1327 / 8913)) (n := 12)
    (lo := (37499647 / 125000000)) (hi := (299997177 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3793) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3793) = 1/(3793 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-299997177 / 1000000000) (-37499647 / 125000000) (Real.log (3793 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (114997513 / 500000000) ≤ -Real.log (1280 / 1611) ∧
    -Real.log (1280 / 1611) ≤ (229995027 / 1000000000) := by
  have h := checkLog_sound (w := (331 / 2891)) (n := 12)
    (lo := (114997513 / 500000000)) (hi := (229995027 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1611 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1611 / 1280) = 1/(1280 / 1611) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (114997513 / 500000000) (229995027 / 1000000000) (Real.log (1611 / 1280)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1611 / 1280) = -Real.log (1280 / 1611) := by
    rw [show ((1611 / 1280) : ℝ) = ((1280 / 1611) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (149603279 / 500000000) ≤ -Real.log (949 / 1280) ∧
    -Real.log (949 / 1280) ≤ (299206559 / 1000000000) := by
  have h := checkLog_sound (w := (331 / 2229)) (n := 12)
    (lo := (149603279 / 500000000)) (hi := (299206559 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 949) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 949) = 1/(949 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-299206559 / 1000000000) (-149603279 / 500000000) (Real.log (949 / 1280)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (417630393 / 1000000000) ≤ -Real.log (2560 / 3887) ∧
    -Real.log (2560 / 3887) ≤ (208815197 / 500000000) := by
  have h := checkLog_sound (w := (1327 / 6447)) (n := 12)
    (lo := (417630393 / 1000000000)) (hi := (208815197 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3887 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3887 / 2560) = 1/(2560 / 3887) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (417630393 / 1000000000) (208815197 / 500000000) (Real.log (3887 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (3887 / 2560) = -Real.log (2560 / 3887) := by
    rw [show ((3887 / 2560) : ℝ) = ((2560 / 3887) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (730557033 / 1000000000) ≤ -Real.log (1233 / 2560) ∧
    -Real.log (1233 / 2560) ≤ (146111407 / 200000000) := by
  have h := checkLog_sound (w := (47 / 2513)) (n := 12)
    (lo := (37409853 / 1000000000)) (hi := (18704927 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 1233) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 1233) = 1/(1233 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-146111407 / 200000000) (-730557033 / 1000000000) (Real.log (1233 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (416858291 / 1000000000) ≤ -Real.log (640 / 971) ∧
    -Real.log (640 / 971) ≤ (104214573 / 250000000) := by
  have h := checkLog_sound (w := (331 / 1611)) (n := 12)
    (lo := (416858291 / 1000000000)) (hi := (104214573 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((971 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(971 / 640) = 1/(640 / 971) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (416858291 / 1000000000) (104214573 / 250000000) (Real.log (971 / 640)) := by
  have h := reflection_log_7_neg
  have he : Real.log (971 / 640) = -Real.log (640 / 971) := by
    rw [show ((971 / 640) : ℝ) = ((640 / 971) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (364063449 / 500000000) ≤ -Real.log (309 / 640) ∧
    -Real.log (309 / 640) ≤ (7281269 / 10000000) := by
  have h := checkLog_sound (w := (11 / 629)) (n := 12)
    (lo := (17489859 / 500000000)) (hi := (34979719 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 309) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(320 / 309) = 1/(309 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-7281269 / 10000000) (-364063449 / 500000000) (Real.log (309 / 640)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (15751959 / 50000000) ≤ -Real.log (1000000 / 1370313) ∧
    -Real.log (1000000 / 1370313) ≤ (315039181 / 1000000000) := by
  have h := checkLog_sound (w := (370313 / 2370313)) (n := 12)
    (lo := (15751959 / 50000000)) (hi := (315039181 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1370313 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1370313 / 1000000) = 1/(1000000 / 1370313) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (15751959 / 50000000) (315039181 / 1000000000) (Real.log (1370313 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1370313 / 1000000) = -Real.log (1000000 / 1370313) := by
    rw [show ((1370313 / 1000000) : ℝ) = ((1000000 / 1370313) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (57816551 / 125000000) ≤ -Real.log (629687 / 1000000) ∧
    -Real.log (629687 / 1000000) ≤ (462532409 / 1000000000) := by
  have h := checkLog_sound (w := (370313 / 1629687)) (n := 12)
    (lo := (57816551 / 125000000)) (hi := (462532409 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 629687) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 629687) = 1/(629687 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-462532409 / 1000000000) (-57816551 / 125000000) (Real.log (629687 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (63133899 / 200000000) ≤ -Real.log (1000000 / 1371177) ∧
    -Real.log (1000000 / 1371177) ≤ (39458687 / 125000000) := by
  have h := checkLog_sound (w := (371177 / 2371177)) (n := 12)
    (lo := (63133899 / 200000000)) (hi := (39458687 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1371177 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1371177 / 1000000) = 1/(1000000 / 1371177) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (63133899 / 200000000) (39458687 / 125000000) (Real.log (1371177 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1371177 / 1000000) = -Real.log (1000000 / 1371177) := by
    rw [show ((1371177 / 1000000) : ℝ) = ((1000000 / 1371177) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (23195273 / 50000000) ≤ -Real.log (628823 / 1000000) ∧
    -Real.log (628823 / 1000000) ≤ (463905461 / 1000000000) := by
  have h := checkLog_sound (w := (371177 / 1628823)) (n := 12)
    (lo := (23195273 / 50000000)) (hi := (463905461 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 628823) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 628823) = 1/(628823 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-463905461 / 1000000000) (-23195273 / 50000000) (Real.log (628823 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (15045453 / 62500000) ≤ -Real.log (500000 / 636087) ∧
    -Real.log (500000 / 636087) ≤ (240727249 / 1000000000) := by
  have h := checkLog_sound (w := (136087 / 1136087)) (n := 12)
    (lo := (15045453 / 62500000)) (hi := (240727249 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((636087 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(636087 / 500000) = 1/(500000 / 636087) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (15045453 / 62500000) (240727249 / 1000000000) (Real.log (636087 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (636087 / 500000) = -Real.log (500000 / 636087) := by
    rw [show ((636087 / 500000) : ℝ) = ((500000 / 636087) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (31769327 / 100000000) ≤ -Real.log (363913 / 500000) ∧
    -Real.log (363913 / 500000) ≤ (317693271 / 1000000000) := by
  have h := checkLog_sound (w := (136087 / 863913)) (n := 12)
    (lo := (31769327 / 100000000)) (hi := (317693271 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 363913) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 363913) = 1/(363913 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-317693271 / 1000000000) (-31769327 / 100000000) (Real.log (363913 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (241265551 / 1000000000) ≤ -Real.log (1000000 / 1272859) ∧
    -Real.log (1000000 / 1272859) ≤ (15079097 / 62500000) := by
  have h := checkLog_sound (w := (272859 / 2272859)) (n := 12)
    (lo := (241265551 / 1000000000)) (hi := (15079097 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1272859 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1272859 / 1000000) = 1/(1000000 / 1272859) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (241265551 / 1000000000) (15079097 / 62500000) (Real.log (1272859 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1272859 / 1000000) = -Real.log (1000000 / 1272859) := by
    rw [show ((1272859 / 1000000) : ℝ) = ((1000000 / 1272859) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (39829359 / 125000000) ≤ -Real.log (727141 / 1000000) ∧
    -Real.log (727141 / 1000000) ≤ (318634873 / 1000000000) := by
  have h := checkLog_sound (w := (272859 / 1727141)) (n := 12)
    (lo := (39829359 / 125000000)) (hi := (318634873 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 727141) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 727141) = 1/(727141 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-318634873 / 1000000000) (-39829359 / 125000000) (Real.log (727141 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (194392897 / 250000000) ≤ -Real.log (500000000000 / 1088090591039) ∧
    -Real.log (500000000000 / 1088090591039) ≤ (77757159 / 100000000) := by
  have h := checkLog_sound (w := (88090591039 / 2088090591039)) (n := 12)
    (lo := (10553051 / 125000000)) (hi := (84424409 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1088090591039 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1088090591039 / 1000000000000) = 1/(500000000000 / 1088090591039) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (194392897 / 250000000) (77757159 / 100000000) (Real.log (1088090591039 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1088090591039 / 500000000000) = -Real.log (500000000000 / 1088090591039) := by
    rw [show ((1088090591039 / 500000000000) : ℝ) = ((500000000000 / 1088090591039) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (155914991 / 200000000) ≤ -Real.log (125000000000 / 272568155109) ∧
    -Real.log (125000000000 / 272568155109) ≤ (779574957 / 1000000000) := by
  have h := checkLog_sound (w := (22568155109 / 522568155109)) (n := 12)
    (lo := (3457111 / 40000000)) (hi := (675217 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((272568155109 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(272568155109 / 250000000000) = 1/(125000000000 / 272568155109) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (155914991 / 200000000) (779574957 / 1000000000) (Real.log (272568155109 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (272568155109 / 125000000000) = -Real.log (125000000000 / 272568155109) := by
    rw [show ((272568155109 / 125000000000) : ℝ) = ((125000000000 / 272568155109) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (279210259 / 500000000) ≤ -Real.log (500000000000 / 873954763913) ∧
    -Real.log (500000000000 / 873954763913) ≤ (558420519 / 1000000000) := by
  have h := checkLog_sound (w := (373954763913 / 1373954763913)) (n := 12)
    (lo := (279210259 / 500000000)) (hi := (558420519 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((873954763913 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(873954763913 / 500000000000) = 1/(500000000000 / 873954763913) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (279210259 / 500000000) (558420519 / 1000000000) (Real.log (873954763913 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (873954763913 / 500000000000) = -Real.log (500000000000 / 873954763913) := by
    rw [show ((873954763913 / 500000000000) : ℝ) = ((500000000000 / 873954763913) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (559900423 / 1000000000) ≤ -Real.log (62500000000 / 109406136499) ∧
    -Real.log (62500000000 / 109406136499) ≤ (69987553 / 125000000) := by
  have h := checkLog_sound (w := (46906136499 / 171906136499)) (n := 12)
    (lo := (559900423 / 1000000000)) (hi := (69987553 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((109406136499 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(109406136499 / 62500000000) = 1/(62500000000 / 109406136499) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (559900423 / 1000000000) (69987553 / 125000000) (Real.log (109406136499 / 62500000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (109406136499 / 62500000000) = -Real.log (62500000000 / 109406136499) := by
    rw [show ((109406136499 / 62500000000) : ℝ) = ((62500000000 / 109406136499) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0277
