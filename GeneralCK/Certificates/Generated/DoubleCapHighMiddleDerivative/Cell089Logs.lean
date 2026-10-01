import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell089
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

theorem reflection_log_1_neg : (13223271 / 50000000) ≤ -Real.log (512 / 667) ∧
    -Real.log (512 / 667) ≤ (264465421 / 1000000000) := by
  have h := checkLog_sound (w := (155 / 1179)) (n := 12)
    (lo := (13223271 / 50000000)) (hi := (264465421 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((667 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(667 / 512) = 1/(512 / 667) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (13223271 / 50000000) (264465421 / 1000000000) (Real.log (667 / 512)) := by
  have h := reflection_log_1_neg
  have he : Real.log (667 / 512) = -Real.log (512 / 667) := by
    rw [show ((667 / 512) : ℝ) = ((512 / 667) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (360588843 / 1000000000) ≤ -Real.log (357 / 512) ∧
    -Real.log (357 / 512) ≤ (90147211 / 250000000) := by
  have h := checkLog_sound (w := (155 / 869)) (n := 12)
    (lo := (360588843 / 1000000000)) (hi := (90147211 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 357) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 357) = 1/(357 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-90147211 / 250000000) (-360588843 / 1000000000) (Real.log (357 / 512)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (33001943 / 125000000) ≤ -Real.log (5120 / 6667) ∧
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


theorem reflection_log_3 : Bounds (33001943 / 125000000) (52803109 / 200000000) (Real.log (6667 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6667 / 5120) = -Real.log (5120 / 6667) := by
    rw [show ((6667 / 5120) : ℝ) = ((5120 / 6667) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (17987443 / 50000000) ≤ -Real.log (3573 / 5120) ∧
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


theorem reflection_log_4 : Bounds (-359748861 / 1000000000) (-17987443 / 50000000) (Real.log (3573 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (7773167 / 40000000) ≤ -Real.log (31250 / 37953) ∧
    -Real.log (31250 / 37953) ≤ (24291147 / 125000000) := by
  have h := checkLog_sound (w := (6703 / 69203)) (n := 12)
    (lo := (7773167 / 40000000)) (hi := (24291147 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((37953 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(37953 / 31250) = 1/(31250 / 37953) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (7773167 / 40000000) (24291147 / 125000000) (Real.log (37953 / 31250)) := by
  have h := reflection_log_5_neg
  have he : Real.log (37953 / 31250) = -Real.log (31250 / 37953) := by
    rw [show ((37953 / 31250) : ℝ) = ((31250 / 37953) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (241429729 / 1000000000) ≤ -Real.log (24547 / 31250) ∧
    -Real.log (24547 / 31250) ≤ (24142973 / 100000000) := by
  have h := checkLog_sound (w := (6703 / 55797)) (n := 12)
    (lo := (241429729 / 1000000000)) (hi := (24142973 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 24547) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31250 / 24547) = 1/(24547 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-24142973 / 100000000) (-241429729 / 1000000000) (Real.log (24547 / 31250)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (97337469 / 500000000) ≤ -Real.log (250000 / 303729) ∧
    -Real.log (250000 / 303729) ≤ (194674939 / 1000000000) := by
  have h := checkLog_sound (w := (53729 / 553729)) (n := 12)
    (lo := (97337469 / 500000000)) (hi := (194674939 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((303729 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(303729 / 250000) = 1/(250000 / 303729) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (97337469 / 500000000) (194674939 / 1000000000) (Real.log (303729 / 250000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (303729 / 250000) = -Real.log (250000 / 303729) := by
    rw [show ((303729 / 250000) : ℝ) = ((250000 / 303729) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (3024557 / 12500000) ≤ -Real.log (196271 / 250000) ∧
    -Real.log (196271 / 250000) ≤ (241964561 / 1000000000) := by
  have h := checkLog_sound (w := (53729 / 446271)) (n := 12)
    (lo := (3024557 / 12500000)) (hi := (241964561 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 196271) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 196271) = 1/(196271 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-241964561 / 1000000000) (-3024557 / 12500000) (Real.log (196271 / 250000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (35728373 / 250000000) ≤ -Real.log (100000 / 115363) ∧
    -Real.log (100000 / 115363) ≤ (142913493 / 1000000000) := by
  have h := checkLog_sound (w := (15363 / 215363)) (n := 12)
    (lo := (35728373 / 250000000)) (hi := (142913493 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((115363 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(115363 / 100000) = 1/(100000 / 115363) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (35728373 / 250000000) (142913493 / 1000000000) (Real.log (115363 / 100000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (115363 / 100000) = -Real.log (100000 / 115363) := by
    rw [show ((115363 / 100000) : ℝ) = ((100000 / 115363) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (83399331 / 500000000) ≤ -Real.log (84637 / 100000) ∧
    -Real.log (84637 / 100000) ≤ (166798663 / 1000000000) := by
  have h := checkLog_sound (w := (15363 / 184637)) (n := 12)
    (lo := (83399331 / 500000000)) (hi := (166798663 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 84637) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 84637) = 1/(84637 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-166798663 / 1000000000) (-83399331 / 500000000) (Real.log (84637 / 100000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (143181307 / 1000000000) ≤ -Real.log (1000000 / 1153939) ∧
    -Real.log (1000000 / 1153939) ≤ (35795327 / 250000000) := by
  have h := checkLog_sound (w := (153939 / 2153939)) (n := 12)
    (lo := (143181307 / 1000000000)) (hi := (35795327 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1153939 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1153939 / 1000000) = 1/(1000000 / 1153939) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (143181307 / 1000000000) (35795327 / 250000000) (Real.log (1153939 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1153939 / 1000000) = -Real.log (1000000 / 1153939) := by
    rw [show ((1153939 / 1000000) : ℝ) = ((1000000 / 1153939) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (167163817 / 1000000000) ≤ -Real.log (846061 / 1000000) ∧
    -Real.log (846061 / 1000000) ≤ (83581909 / 500000000) := by
  have h := checkLog_sound (w := (153939 / 1846061)) (n := 12)
    (lo := (167163817 / 1000000000)) (hi := (83581909 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 846061) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 846061) = 1/(846061 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-83581909 / 500000000) (-167163817 / 1000000000) (Real.log (846061 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (155941101 / 250000000) ≤ -Real.log (250000000000 / 466484746711) ∧
    -Real.log (250000000000 / 466484746711) ≤ (124752881 / 200000000) := by
  have h := checkLog_sound (w := (216484746711 / 716484746711)) (n := 12)
    (lo := (155941101 / 250000000)) (hi := (124752881 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((466484746711 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(466484746711 / 250000000000) = 1/(250000000000 / 466484746711) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (155941101 / 250000000) (124752881 / 200000000) (Real.log (466484746711 / 250000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (466484746711 / 250000000000) = -Real.log (250000000000 / 466484746711) := by
    rw [show ((466484746711 / 250000000000) : ℝ) = ((250000000000 / 466484746711) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (78131783 / 125000000) ≤ -Real.log (125000000000 / 233543417367) ∧
    -Real.log (125000000000 / 233543417367) ≤ (125010853 / 200000000) := by
  have h := checkLog_sound (w := (108543417367 / 358543417367)) (n := 12)
    (lo := (78131783 / 125000000)) (hi := (125010853 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((233543417367 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(233543417367 / 125000000000) = 1/(125000000000 / 233543417367) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (78131783 / 125000000) (125010853 / 200000000) (Real.log (233543417367 / 125000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (233543417367 / 125000000000) = -Real.log (125000000000 / 233543417367) := by
    rw [show ((233543417367 / 125000000000) : ℝ) = ((125000000000 / 233543417367) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (54469863 / 125000000) ≤ -Real.log (100000000000 / 154613598403) ∧
    -Real.log (100000000000 / 154613598403) ≤ (87151781 / 200000000) := by
  have h := checkLog_sound (w := (54613598403 / 254613598403)) (n := 12)
    (lo := (54469863 / 125000000)) (hi := (87151781 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((154613598403 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(154613598403 / 100000000000) = 1/(100000000000 / 154613598403) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (54469863 / 125000000) (87151781 / 200000000) (Real.log (154613598403 / 100000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (154613598403 / 100000000000) = -Real.log (100000000000 / 154613598403) := by
    rw [show ((154613598403 / 100000000000) : ℝ) = ((100000000000 / 154613598403) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (436639499 / 1000000000) ≤ -Real.log (500000000000 / 773749051057) ∧
    -Real.log (500000000000 / 773749051057) ≤ (873279 / 2000000) := by
  have h := checkLog_sound (w := (273749051057 / 1273749051057)) (n := 12)
    (lo := (436639499 / 1000000000)) (hi := (873279 / 2000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((773749051057 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(773749051057 / 500000000000) = 1/(500000000000 / 773749051057) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (436639499 / 1000000000) (873279 / 2000000) (Real.log (773749051057 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (773749051057 / 500000000000) = -Real.log (500000000000 / 773749051057) := by
    rw [show ((773749051057 / 500000000000) : ℝ) = ((500000000000 / 773749051057) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (61942431 / 200000000) ≤ -Real.log (500000000000 / 681516358093) ∧
    -Real.log (500000000000 / 681516358093) ≤ (77428039 / 250000000) := by
  have h := checkLog_sound (w := (181516358093 / 1181516358093)) (n := 12)
    (lo := (61942431 / 200000000)) (hi := (77428039 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((681516358093 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(681516358093 / 500000000000) = 1/(500000000000 / 681516358093) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (61942431 / 200000000) (77428039 / 250000000) (Real.log (681516358093 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (681516358093 / 500000000000) = -Real.log (500000000000 / 681516358093) := by
    rw [show ((681516358093 / 500000000000) : ℝ) = ((500000000000 / 681516358093) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (2482761 / 8000000) ≤ -Real.log (100000000000 / 136389574747) ∧
    -Real.log (100000000000 / 136389574747) ≤ (155172563 / 500000000) := by
  have h := checkLog_sound (w := (36389574747 / 236389574747)) (n := 12)
    (lo := (2482761 / 8000000)) (hi := (155172563 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((136389574747 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(136389574747 / 100000000000) = 1/(100000000000 / 136389574747) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (2482761 / 8000000) (155172563 / 500000000) (Real.log (136389574747 / 100000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (136389574747 / 100000000000) = -Real.log (100000000000 / 136389574747) := by
    rw [show ((136389574747 / 100000000000) : ℝ) = ((100000000000 / 136389574747) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (2398251 / 100000000) ≤ -Real.log (976302784279 / 1000000000000) ∧
    -Real.log (976302784279 / 1000000000000) ≤ (23982511 / 1000000000) := by
  have h := checkLog_sound (w := (23697215721 / 1976302784279)) (n := 12)
    (lo := (2398251 / 100000000)) (hi := (23982511 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 976302784279) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 976302784279) = 1/(976302784279 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-23982511 / 1000000000) (-2398251 / 100000000) (Real.log (976302784279 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (23885169 / 1000000000) ≤ -Real.log (9763978231 / 10000000000) ∧
    -Real.log (9763978231 / 10000000000) ≤ (2388517 / 100000000) := by
  have h := checkLog_sound (w := (236021769 / 19763978231)) (n := 12)
    (lo := (23885169 / 1000000000)) (hi := (2388517 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 9763978231) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 9763978231) = 1/(9763978231 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-2388517 / 100000000) (-23885169 / 1000000000) (Real.log (9763978231 / 10000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell089
