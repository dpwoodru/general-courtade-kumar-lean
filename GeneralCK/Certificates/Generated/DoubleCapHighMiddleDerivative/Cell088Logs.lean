import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell088
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

theorem reflection_log_1_neg : (33001943 / 125000000) ≤ -Real.log (5120 / 6667) ∧
    -Real.log (5120 / 6667) ≤ (52803109 / 200000000) := by
  have h := checkLog_sound (w := (1547 / 11787)) (n := 12)
    (lo := (33001943 / 125000000)) (hi := (52803109 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6667 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6667 / 5120) = 1/(5120 / 6667) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (33001943 / 125000000) (52803109 / 200000000) (Real.log (6667 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6667 / 5120) = -Real.log (5120 / 6667) := by
    rw [show ((6667 / 5120) : ℝ) = ((5120 / 6667) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (17987443 / 50000000) ≤ -Real.log (3573 / 5120) ∧
    -Real.log (3573 / 5120) ≤ (359748861 / 1000000000) := by
  have h := checkLog_sound (w := (1547 / 8693)) (n := 12)
    (lo := (17987443 / 50000000)) (hi := (359748861 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3573) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3573) = 1/(3573 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-359748861 / 1000000000) (-17987443 / 50000000) (Real.log (3573 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (52713093 / 200000000) ≤ -Real.log (640 / 833) ∧
    -Real.log (640 / 833) ≤ (131782733 / 500000000) := by
  have h := checkLog_sound (w := (193 / 1473)) (n := 12)
    (lo := (52713093 / 200000000)) (hi := (131782733 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((833 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(833 / 640) = 1/(640 / 833) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (52713093 / 200000000) (131782733 / 500000000) (Real.log (833 / 640)) := by
  have h := reflection_log_3_neg
  have he : Real.log (833 / 640) = -Real.log (640 / 833) := by
    rw [show ((833 / 640) : ℝ) = ((640 / 833) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (358909581 / 1000000000) ≤ -Real.log (447 / 640) ∧
    -Real.log (447 / 640) ≤ (179454791 / 500000000) := by
  have h := checkLog_sound (w := (193 / 1087)) (n := 12)
    (lo := (358909581 / 1000000000)) (hi := (179454791 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 447) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 447) = 1/(447 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-179454791 / 500000000) (-358909581 / 1000000000) (Real.log (447 / 640)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (193983293 / 1000000000) ≤ -Real.log (250000 / 303519) ∧
    -Real.log (250000 / 303519) ≤ (96991647 / 500000000) := by
  have h := checkLog_sound (w := (53519 / 553519)) (n := 12)
    (lo := (193983293 / 1000000000)) (hi := (96991647 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((303519 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(303519 / 250000) = 1/(250000 / 303519) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (193983293 / 1000000000) (96991647 / 500000000) (Real.log (303519 / 250000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (303519 / 250000) = -Real.log (250000 / 303519) := by
    rw [show ((303519 / 250000) : ℝ) = ((250000 / 303519) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (240895183 / 1000000000) ≤ -Real.log (196481 / 250000) ∧
    -Real.log (196481 / 250000) ≤ (15055949 / 62500000) := by
  have h := checkLog_sound (w := (53519 / 446481)) (n := 12)
    (lo := (240895183 / 1000000000)) (hi := (15055949 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 196481) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 196481) = 1/(196481 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-15055949 / 62500000) (-240895183 / 1000000000) (Real.log (196481 / 250000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (194329999 / 1000000000) ≤ -Real.log (1000000 / 1214497) ∧
    -Real.log (1000000 / 1214497) ≤ (19433 / 100000) := by
  have h := checkLog_sound (w := (214497 / 2214497)) (n := 12)
    (lo := (194329999 / 1000000000)) (hi := (19433 / 100000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1214497 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1214497 / 1000000) = 1/(1000000 / 1214497) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (194329999 / 1000000000) (19433 / 100000) (Real.log (1214497 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1214497 / 1000000) = -Real.log (1000000 / 1214497) := by
    rw [show ((1214497 / 1000000) : ℝ) = ((1000000 / 1214497) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (120715501 / 500000000) ≤ -Real.log (785503 / 1000000) ∧
    -Real.log (785503 / 1000000) ≤ (241431003 / 1000000000) := by
  have h := checkLog_sound (w := (214497 / 1785503)) (n := 12)
    (lo := (120715501 / 500000000)) (hi := (241431003 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 785503) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 785503) = 1/(785503 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-241431003 / 1000000000) (-120715501 / 500000000) (Real.log (785503 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (142646473 / 1000000000) ≤ -Real.log (500000 / 576661) ∧
    -Real.log (500000 / 576661) ≤ (71323237 / 500000000) := by
  have h := checkLog_sound (w := (76661 / 1076661)) (n := 12)
    (lo := (142646473 / 1000000000)) (hi := (71323237 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((576661 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(576661 / 500000) = 1/(500000 / 576661) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (142646473 / 1000000000) (71323237 / 500000000) (Real.log (576661 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (576661 / 500000) = -Real.log (500000 / 576661) := by
    rw [show ((576661 / 500000) : ℝ) = ((500000 / 576661) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (166434821 / 1000000000) ≤ -Real.log (423339 / 500000) ∧
    -Real.log (423339 / 500000) ≤ (83217411 / 500000000) := by
  have h := checkLog_sound (w := (76661 / 923339)) (n := 12)
    (lo := (166434821 / 1000000000)) (hi := (83217411 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 423339) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 423339) = 1/(423339 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-83217411 / 500000000) (-166434821 / 1000000000) (Real.log (423339 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (142914359 / 1000000000) ≤ -Real.log (1000000 / 1153631) ∧
    -Real.log (1000000 / 1153631) ≤ (3572859 / 25000000) := by
  have h := checkLog_sound (w := (153631 / 2153631)) (n := 12)
    (lo := (142914359 / 1000000000)) (hi := (3572859 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1153631 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1153631 / 1000000) = 1/(1000000 / 1153631) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (142914359 / 1000000000) (3572859 / 25000000) (Real.log (1153631 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1153631 / 1000000) = -Real.log (1000000 / 1153631) := by
    rw [show ((1153631 / 1000000) : ℝ) = ((1000000 / 1153631) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (41699961 / 250000000) ≤ -Real.log (846369 / 1000000) ∧
    -Real.log (846369 / 1000000) ≤ (33359969 / 200000000) := by
  have h := checkLog_sound (w := (153631 / 1846369)) (n := 12)
    (lo := (41699961 / 250000000)) (hi := (33359969 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 846369) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 846369) = 1/(846369 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-33359969 / 200000000) (-41699961 / 250000000) (Real.log (846369 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (622475047 / 1000000000) ≤ -Real.log (500000000000 / 931767337807) ∧
    -Real.log (500000000000 / 931767337807) ≤ (77809381 / 125000000) := by
  have h := checkLog_sound (w := (431767337807 / 1431767337807)) (n := 12)
    (lo := (622475047 / 1000000000)) (hi := (77809381 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((931767337807 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(931767337807 / 500000000000) = 1/(500000000000 / 931767337807) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (622475047 / 1000000000) (77809381 / 125000000) (Real.log (931767337807 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (931767337807 / 500000000000) = -Real.log (500000000000 / 931767337807) := by
    rw [show ((931767337807 / 500000000000) : ℝ) = ((500000000000 / 931767337807) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (155941101 / 250000000) ≤ -Real.log (500000000000 / 932969493423) ∧
    -Real.log (500000000000 / 932969493423) ≤ (124752881 / 200000000) := by
  have h := checkLog_sound (w := (432969493423 / 1432969493423)) (n := 12)
    (lo := (155941101 / 250000000)) (hi := (124752881 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((932969493423 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(932969493423 / 500000000000) = 1/(500000000000 / 932969493423) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (155941101 / 250000000) (124752881 / 200000000) (Real.log (932969493423 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (932969493423 / 500000000000) = -Real.log (500000000000 / 932969493423) := by
    rw [show ((932969493423 / 500000000000) : ℝ) = ((500000000000 / 932969493423) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (108719619 / 250000000) ≤ -Real.log (500000000000 / 772387660893) ∧
    -Real.log (500000000000 / 772387660893) ≤ (434878477 / 1000000000) := by
  have h := checkLog_sound (w := (272387660893 / 1272387660893)) (n := 12)
    (lo := (108719619 / 250000000)) (hi := (434878477 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((772387660893 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(772387660893 / 500000000000) = 1/(500000000000 / 772387660893) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (108719619 / 250000000) (434878477 / 1000000000) (Real.log (772387660893 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (772387660893 / 500000000000) = -Real.log (500000000000 / 772387660893) := by
    rw [show ((772387660893 / 500000000000) : ℝ) = ((500000000000 / 772387660893) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (435761001 / 1000000000) ≤ -Real.log (6250000000 / 9663370159) ∧
    -Real.log (6250000000 / 9663370159) ≤ (217880501 / 500000000) := by
  have h := checkLog_sound (w := (3413370159 / 15913370159)) (n := 12)
    (lo := (435761001 / 1000000000)) (hi := (217880501 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9663370159 / 6250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(9663370159 / 6250000000) = 1/(6250000000 / 9663370159) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (435761001 / 1000000000) (217880501 / 500000000) (Real.log (9663370159 / 6250000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (9663370159 / 6250000000) = -Real.log (6250000000 / 9663370159) := by
    rw [show ((9663370159 / 6250000000) : ℝ) = ((6250000000 / 9663370159) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (61816259 / 200000000) ≤ -Real.log (7812500000 / 10641977381) ∧
    -Real.log (7812500000 / 10641977381) ≤ (19317581 / 62500000) := by
  have h := checkLog_sound (w := (2829477381 / 18454477381)) (n := 12)
    (lo := (61816259 / 200000000)) (hi := (19317581 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10641977381 / 7812500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10641977381 / 7812500000) = 1/(7812500000 / 10641977381) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (61816259 / 200000000) (19317581 / 62500000) (Real.log (10641977381 / 7812500000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (10641977381 / 7812500000) = -Real.log (7812500000 / 10641977381) := by
    rw [show ((10641977381 / 7812500000) : ℝ) = ((7812500000 / 10641977381) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (309714203 / 1000000000) ≤ -Real.log (500000000000 / 681517754077) ∧
    -Real.log (500000000000 / 681517754077) ≤ (77428551 / 250000000) := by
  have h := checkLog_sound (w := (181517754077 / 1181517754077)) (n := 12)
    (lo := (309714203 / 1000000000)) (hi := (77428551 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((681517754077 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(681517754077 / 500000000000) = 1/(500000000000 / 681517754077) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (309714203 / 1000000000) (77428551 / 250000000) (Real.log (681517754077 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (681517754077 / 500000000000) = -Real.log (500000000000 / 681517754077) := by
    rw [show ((681517754077 / 500000000000) : ℝ) = ((500000000000 / 681517754077) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (5971371 / 250000000) ≤ -Real.log (976397515839 / 1000000000000) ∧
    -Real.log (976397515839 / 1000000000000) ≤ (4777097 / 200000000) := by
  have h := checkLog_sound (w := (23602484161 / 1976397515839)) (n := 12)
    (lo := (5971371 / 250000000)) (hi := (4777097 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 976397515839) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 976397515839) = 1/(976397515839 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-4777097 / 200000000) (-5971371 / 250000000) (Real.log (976397515839 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (5947087 / 250000000) ≤ -Real.log (244123091079 / 250000000000) ∧
    -Real.log (244123091079 / 250000000000) ≤ (23788349 / 1000000000) := by
  have h := checkLog_sound (w := (5876908921 / 494123091079)) (n := 12)
    (lo := (5947087 / 250000000)) (hi := (23788349 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 244123091079) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 244123091079) = 1/(244123091079 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-23788349 / 1000000000) (-5947087 / 250000000) (Real.log (244123091079 / 250000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell088
