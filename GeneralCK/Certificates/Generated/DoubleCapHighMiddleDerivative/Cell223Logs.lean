import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell223
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

theorem reflection_log_1_neg : (161494443 / 500000000) ≤ -Real.log (160 / 221) ∧
    -Real.log (160 / 221) ≤ (322988887 / 1000000000) := by
  have h := checkLog_sound (w := (61 / 381)) (n := 12)
    (lo := (161494443 / 500000000)) (hi := (322988887 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((221 / 160) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(221 / 160) = 1/(160 / 221) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (161494443 / 500000000) (322988887 / 1000000000) (Real.log (221 / 160)) := by
  have h := reflection_log_1_neg
  have he : Real.log (221 / 160) = -Real.log (160 / 221) := by
    rw [show ((221 / 160) : ℝ) = ((160 / 221) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (96010793 / 200000000) ≤ -Real.log (99 / 160) ∧
    -Real.log (99 / 160) ≤ (240026983 / 500000000) := by
  have h := checkLog_sound (w := (61 / 259)) (n := 12)
    (lo := (96010793 / 200000000)) (hi := (240026983 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 99) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(160 / 99) = 1/(99 / 160) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-240026983 / 500000000) (-96010793 / 200000000) (Real.log (99 / 160)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (80641147 / 250000000) ≤ -Real.log (5120 / 7069) ∧
    -Real.log (5120 / 7069) ≤ (322564589 / 1000000000) := by
  have h := checkLog_sound (w := (1949 / 12189)) (n := 12)
    (lo := (80641147 / 250000000)) (hi := (322564589 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7069 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7069 / 5120) = 1/(5120 / 7069) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (80641147 / 250000000) (322564589 / 1000000000) (Real.log (7069 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (7069 / 5120) = -Real.log (5120 / 7069) := by
    rw [show ((7069 / 5120) : ℝ) = ((5120 / 7069) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (479107443 / 1000000000) ≤ -Real.log (3171 / 5120) ∧
    -Real.log (3171 / 5120) ≤ (119776861 / 250000000) := by
  have h := checkLog_sound (w := (1949 / 8291)) (n := 12)
    (lo := (479107443 / 1000000000)) (hi := (119776861 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3171) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3171) = 1/(3171 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-119776861 / 250000000) (-479107443 / 1000000000) (Real.log (3171 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (239726097 / 1000000000) ≤ -Real.log (1000000 / 1270901) ∧
    -Real.log (1000000 / 1270901) ≤ (119863049 / 500000000) := by
  have h := checkLog_sound (w := (270901 / 2270901)) (n := 12)
    (lo := (239726097 / 1000000000)) (hi := (119863049 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1270901 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1270901 / 1000000) = 1/(1000000 / 1270901) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (239726097 / 1000000000) (119863049 / 500000000) (Real.log (1270901 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1270901 / 1000000) = -Real.log (1000000 / 1270901) := by
    rw [show ((1270901 / 1000000) : ℝ) = ((1000000 / 1270901) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (315945753 / 1000000000) ≤ -Real.log (729099 / 1000000) ∧
    -Real.log (729099 / 1000000) ≤ (157972877 / 500000000) := by
  have h := checkLog_sound (w := (270901 / 1729099)) (n := 12)
    (lo := (315945753 / 1000000000)) (hi := (157972877 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 729099) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 729099) = 1/(729099 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-157972877 / 500000000) (-315945753 / 1000000000) (Real.log (729099 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (240058877 / 1000000000) ≤ -Real.log (250000 / 317831) ∧
    -Real.log (250000 / 317831) ≤ (120029439 / 500000000) := by
  have h := checkLog_sound (w := (67831 / 567831)) (n := 12)
    (lo := (240058877 / 1000000000)) (hi := (120029439 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((317831 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(317831 / 250000) = 1/(250000 / 317831) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (240058877 / 1000000000) (120029439 / 500000000) (Real.log (317831 / 250000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (317831 / 250000) = -Real.log (250000 / 317831) := by
    rw [show ((317831 / 250000) : ℝ) = ((250000 / 317831) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (31652609 / 100000000) ≤ -Real.log (182169 / 250000) ∧
    -Real.log (182169 / 250000) ≤ (316526091 / 1000000000) := by
  have h := checkLog_sound (w := (67831 / 432169)) (n := 12)
    (lo := (31652609 / 100000000)) (hi := (316526091 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 182169) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 182169) = 1/(182169 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-316526091 / 1000000000) (-31652609 / 100000000) (Real.log (182169 / 250000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (178589601 / 1000000000) ≤ -Real.log (100000 / 119553) ∧
    -Real.log (100000 / 119553) ≤ (89294801 / 500000000) := by
  have h := checkLog_sound (w := (19553 / 219553)) (n := 12)
    (lo := (178589601 / 1000000000)) (hi := (89294801 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((119553 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(119553 / 100000) = 1/(100000 / 119553) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (178589601 / 1000000000) (89294801 / 500000000) (Real.log (119553 / 100000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (119553 / 100000) = -Real.log (100000 / 119553) := by
    rw [show ((119553 / 100000) : ℝ) = ((100000 / 119553) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (217571603 / 1000000000) ≤ -Real.log (80447 / 100000) ∧
    -Real.log (80447 / 100000) ≤ (54392901 / 250000000) := by
  have h := checkLog_sound (w := (19553 / 180447)) (n := 12)
    (lo := (217571603 / 1000000000)) (hi := (54392901 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 80447) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 80447) = 1/(80447 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-54392901 / 250000000) (-217571603 / 1000000000) (Real.log (80447 / 100000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (178856393 / 1000000000) ≤ -Real.log (1000000 / 1195849) ∧
    -Real.log (1000000 / 1195849) ≤ (89428197 / 500000000) := by
  have h := checkLog_sound (w := (195849 / 2195849)) (n := 12)
    (lo := (178856393 / 1000000000)) (hi := (89428197 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1195849 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1195849 / 1000000) = 1/(1000000 / 1195849) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (178856393 / 1000000000) (89428197 / 500000000) (Real.log (1195849 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1195849 / 1000000) = -Real.log (1000000 / 1195849) := by
    rw [show ((1195849 / 1000000) : ℝ) = ((1000000 / 1195849) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (27246027 / 125000000) ≤ -Real.log (804151 / 1000000) ∧
    -Real.log (804151 / 1000000) ≤ (217968217 / 1000000000) := by
  have h := checkLog_sound (w := (195849 / 1804151)) (n := 12)
    (lo := (27246027 / 125000000)) (hi := (217968217 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 804151) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 804151) = 1/(804151 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-217968217 / 1000000000) (-27246027 / 125000000) (Real.log (804151 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (801672031 / 1000000000) ≤ -Real.log (50000000000 / 111463260801) ∧
    -Real.log (50000000000 / 111463260801) ≤ (801672033 / 1000000000) := by
  have h := checkLog_sound (w := (11463260801 / 211463260801)) (n := 12)
    (lo := (108524851 / 1000000000)) (hi := (27131213 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((111463260801 / 100000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(111463260801 / 100000000000) = 1/(50000000000 / 111463260801) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (801672031 / 1000000000) (801672033 / 1000000000) (Real.log (111463260801 / 50000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (111463260801 / 50000000000) = -Real.log (50000000000 / 111463260801) := by
    rw [show ((111463260801 / 50000000000) : ℝ) = ((50000000000 / 111463260801) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (16060857 / 20000000) ≤ -Real.log (250000000000 / 558080808081) ∧
    -Real.log (250000000000 / 558080808081) ≤ (200760713 / 250000000) := by
  have h := checkLog_sound (w := (58080808081 / 1058080808081)) (n := 12)
    (lo := (10989567 / 100000000)) (hi := (109895671 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((558080808081 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(558080808081 / 500000000000) = 1/(250000000000 / 558080808081) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (16060857 / 20000000) (200760713 / 250000000) (Real.log (558080808081 / 250000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (558080808081 / 250000000000) = -Real.log (250000000000 / 558080808081) := by
    rw [show ((558080808081 / 250000000000) : ℝ) = ((250000000000 / 558080808081) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (555671851 / 1000000000) ≤ -Real.log (500000000000 / 871555851811) ∧
    -Real.log (500000000000 / 871555851811) ≤ (138917963 / 250000000) := by
  have h := checkLog_sound (w := (371555851811 / 1371555851811)) (n := 12)
    (lo := (555671851 / 1000000000)) (hi := (138917963 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((871555851811 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(871555851811 / 500000000000) = 1/(500000000000 / 871555851811) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (555671851 / 1000000000) (138917963 / 250000000) (Real.log (871555851811 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (871555851811 / 500000000000) = -Real.log (500000000000 / 871555851811) := by
    rw [show ((871555851811 / 500000000000) : ℝ) = ((500000000000 / 871555851811) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (556584967 / 1000000000) ≤ -Real.log (250000000000 / 436176023363) ∧
    -Real.log (250000000000 / 436176023363) ≤ (69573121 / 125000000) := by
  have h := checkLog_sound (w := (186176023363 / 686176023363)) (n := 12)
    (lo := (556584967 / 1000000000)) (hi := (69573121 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((436176023363 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(436176023363 / 250000000000) = 1/(250000000000 / 436176023363) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (556584967 / 1000000000) (69573121 / 125000000) (Real.log (436176023363 / 250000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (436176023363 / 250000000000) = -Real.log (250000000000 / 436176023363) := by
    rw [show ((436176023363 / 250000000000) : ℝ) = ((250000000000 / 436176023363) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (79232241 / 200000000) ≤ -Real.log (500000000000 / 743054433353) ∧
    -Real.log (500000000000 / 743054433353) ≤ (198080603 / 500000000) := by
  have h := checkLog_sound (w := (243054433353 / 1243054433353)) (n := 12)
    (lo := (79232241 / 200000000)) (hi := (198080603 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((743054433353 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(743054433353 / 500000000000) = 1/(500000000000 / 743054433353) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (79232241 / 200000000) (198080603 / 500000000) (Real.log (743054433353 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (743054433353 / 500000000000) = -Real.log (500000000000 / 743054433353) := by
    rw [show ((743054433353 / 500000000000) : ℝ) = ((500000000000 / 743054433353) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (396824609 / 1000000000) ≤ -Real.log (15625000000 / 23235860709) ∧
    -Real.log (15625000000 / 23235860709) ≤ (39682461 / 100000000) := by
  have h := checkLog_sound (w := (7610860709 / 38860860709)) (n := 12)
    (lo := (396824609 / 1000000000)) (hi := (39682461 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((23235860709 / 15625000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(23235860709 / 15625000000) = 1/(15625000000 / 23235860709) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (396824609 / 1000000000) (39682461 / 100000000) (Real.log (23235860709 / 15625000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (23235860709 / 15625000000) = -Real.log (15625000000 / 23235860709) := by
    rw [show ((23235860709 / 15625000000) : ℝ) = ((15625000000 / 23235860709) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (39111823 / 1000000000) ≤ -Real.log (961643169199 / 1000000000000) ∧
    -Real.log (961643169199 / 1000000000000) ≤ (2444489 / 62500000) := by
  have h := checkLog_sound (w := (38356830801 / 1961643169199)) (n := 12)
    (lo := (39111823 / 1000000000)) (hi := (2444489 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 961643169199) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 961643169199) = 1/(961643169199 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-2444489 / 62500000) (-39111823 / 1000000000) (Real.log (961643169199 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (38982001 / 1000000000) ≤ -Real.log (9617680191 / 10000000000) ∧
    -Real.log (9617680191 / 10000000000) ≤ (19491001 / 500000000) := by
  have h := checkLog_sound (w := (382319809 / 19617680191)) (n := 12)
    (lo := (38982001 / 1000000000)) (hi := (19491001 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 9617680191) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 9617680191) = 1/(9617680191 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-19491001 / 500000000) (-38982001 / 1000000000) (Real.log (9617680191 / 10000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell223
