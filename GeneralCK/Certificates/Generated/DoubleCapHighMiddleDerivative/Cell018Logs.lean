import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell018
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

theorem reflection_log_1_neg : (116005187 / 500000000) ≤ -Real.log (5120 / 6457) ∧
    -Real.log (5120 / 6457) ≤ (1856083 / 8000000) := by
  have h := checkLog_sound (w := (1337 / 11577)) (n := 12)
    (lo := (116005187 / 500000000)) (hi := (1856083 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6457 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6457 / 5120) = 1/(5120 / 6457) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (116005187 / 500000000) (1856083 / 8000000) (Real.log (6457 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6457 / 5120) = -Real.log (5120 / 6457) := by
    rw [show ((6457 / 5120) : ℝ) = ((5120 / 6457) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (302637093 / 1000000000) ≤ -Real.log (3783 / 5120) ∧
    -Real.log (3783 / 5120) ≤ (151318547 / 500000000) := by
  have h := checkLog_sound (w := (1337 / 8903)) (n := 12)
    (lo := (302637093 / 1000000000)) (hi := (151318547 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3783) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3783) = 1/(3783 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-151318547 / 500000000) (-302637093 / 1000000000) (Real.log (3783 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (115772827 / 500000000) ≤ -Real.log (2560 / 3227) ∧
    -Real.log (2560 / 3227) ≤ (46309131 / 200000000) := by
  have h := checkLog_sound (w := (667 / 5787)) (n := 12)
    (lo := (115772827 / 500000000)) (hi := (46309131 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3227 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3227 / 2560) = 1/(2560 / 3227) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (115772827 / 500000000) (46309131 / 200000000) (Real.log (3227 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3227 / 2560) = -Real.log (2560 / 3227) := by
    rw [show ((3227 / 2560) : ℝ) = ((2560 / 3227) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (150922193 / 500000000) ≤ -Real.log (1893 / 2560) ∧
    -Real.log (1893 / 2560) ≤ (301844387 / 1000000000) := by
  have h := checkLog_sound (w := (667 / 4453)) (n := 12)
    (lo := (150922193 / 500000000)) (hi := (301844387 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1893) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1893) = 1/(1893 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-301844387 / 1000000000) (-150922193 / 500000000) (Real.log (1893 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (84774331 / 500000000) ≤ -Real.log (100000 / 118477) ∧
    -Real.log (100000 / 118477) ≤ (169548663 / 1000000000) := by
  have h := checkLog_sound (w := (18477 / 218477)) (n := 12)
    (lo := (84774331 / 500000000)) (hi := (169548663 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((118477 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(118477 / 100000) = 1/(100000 / 118477) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (84774331 / 500000000) (169548663 / 1000000000) (Real.log (118477 / 100000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (118477 / 100000) = -Real.log (100000 / 118477) := by
    rw [show ((118477 / 100000) : ℝ) = ((100000 / 118477) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (51071249 / 250000000) ≤ -Real.log (81523 / 100000) ∧
    -Real.log (81523 / 100000) ≤ (204284997 / 1000000000) := by
  have h := checkLog_sound (w := (18477 / 181523)) (n := 12)
    (lo := (51071249 / 250000000)) (hi := (204284997 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 81523) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 81523) = 1/(81523 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-204284997 / 1000000000) (-51071249 / 250000000) (Real.log (81523 / 100000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (33980451 / 200000000) ≤ -Real.log (1000000 / 1185189) ∧
    -Real.log (1000000 / 1185189) ≤ (10618891 / 62500000) := by
  have h := checkLog_sound (w := (185189 / 2185189)) (n := 12)
    (lo := (33980451 / 200000000)) (hi := (10618891 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1185189 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1185189 / 1000000) = 1/(1000000 / 1185189) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (33980451 / 200000000) (10618891 / 62500000) (Real.log (1185189 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1185189 / 1000000) = -Real.log (1000000 / 1185189) := by
    rw [show ((1185189 / 1000000) : ℝ) = ((1000000 / 1185189) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (102399547 / 500000000) ≤ -Real.log (814811 / 1000000) ∧
    -Real.log (814811 / 1000000) ≤ (40959819 / 200000000) := by
  have h := checkLog_sound (w := (185189 / 1814811)) (n := 12)
    (lo := (102399547 / 500000000)) (hi := (40959819 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 814811) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 814811) = 1/(814811 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-40959819 / 200000000) (-102399547 / 500000000) (Real.log (814811 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (30974409 / 250000000) ≤ -Real.log (10000 / 11319) ∧
    -Real.log (10000 / 11319) ≤ (123897637 / 1000000000) := by
  have h := checkLog_sound (w := (1319 / 21319)) (n := 12)
    (lo := (30974409 / 250000000)) (hi := (123897637 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11319 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11319 / 10000) = 1/(10000 / 11319) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (30974409 / 250000000) (123897637 / 1000000000) (Real.log (11319 / 10000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (11319 / 10000) = -Real.log (10000 / 11319) := by
    rw [show ((11319 / 10000) : ℝ) = ((10000 / 11319) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (141448363 / 1000000000) ≤ -Real.log (8681 / 10000) ∧
    -Real.log (8681 / 10000) ≤ (35362091 / 250000000) := by
  have h := checkLog_sound (w := (1319 / 18681)) (n := 12)
    (lo := (141448363 / 1000000000)) (hi := (35362091 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8681) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8681) = 1/(8681 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-35362091 / 250000000) (-141448363 / 1000000000) (Real.log (8681 / 10000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (62083529 / 500000000) ≤ -Real.log (200000 / 226441) ∧
    -Real.log (200000 / 226441) ≤ (124167059 / 1000000000) := by
  have h := checkLog_sound (w := (26441 / 426441)) (n := 12)
    (lo := (62083529 / 500000000)) (hi := (124167059 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((226441 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(226441 / 200000) = 1/(200000 / 226441) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (62083529 / 500000000) (124167059 / 1000000000) (Real.log (226441 / 200000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (226441 / 200000) = -Real.log (200000 / 226441) := by
    rw [show ((226441 / 200000) : ℝ) = ((200000 / 226441) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (141799767 / 1000000000) ≤ -Real.log (173559 / 200000) ∧
    -Real.log (173559 / 200000) ≤ (17724971 / 125000000) := by
  have h := checkLog_sound (w := (26441 / 373559)) (n := 12)
    (lo := (141799767 / 1000000000)) (hi := (17724971 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 173559) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 173559) = 1/(173559 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-17724971 / 125000000) (-141799767 / 1000000000) (Real.log (173559 / 200000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (13334751 / 25000000) ≤ -Real.log (500000000000 / 852350765979) ∧
    -Real.log (500000000000 / 852350765979) ≤ (533390041 / 1000000000) := by
  have h := checkLog_sound (w := (352350765979 / 1352350765979)) (n := 12)
    (lo := (13334751 / 25000000)) (hi := (533390041 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((852350765979 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(852350765979 / 500000000000) = 1/(500000000000 / 852350765979) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (13334751 / 25000000) (533390041 / 1000000000) (Real.log (852350765979 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (852350765979 / 500000000000) = -Real.log (500000000000 / 852350765979) := by
    rw [show ((852350765979 / 500000000000) : ℝ) = ((500000000000 / 852350765979) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (534647467 / 1000000000) ≤ -Real.log (250000000000 / 426711604547) ∧
    -Real.log (250000000000 / 426711604547) ≤ (133661867 / 250000000) := by
  have h := checkLog_sound (w := (176711604547 / 676711604547)) (n := 12)
    (lo := (534647467 / 1000000000)) (hi := (133661867 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((426711604547 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(426711604547 / 250000000000) = 1/(250000000000 / 426711604547) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (534647467 / 1000000000) (133661867 / 250000000) (Real.log (426711604547 / 250000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (426711604547 / 250000000000) = -Real.log (250000000000 / 426711604547) := by
    rw [show ((426711604547 / 250000000000) : ℝ) = ((250000000000 / 426711604547) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (373833659 / 1000000000) ≤ -Real.log (100000000000 / 145329538903) ∧
    -Real.log (100000000000 / 145329538903) ≤ (18691683 / 50000000) := by
  have h := checkLog_sound (w := (45329538903 / 245329538903)) (n := 12)
    (lo := (373833659 / 1000000000)) (hi := (18691683 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((145329538903 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(145329538903 / 100000000000) = 1/(100000000000 / 145329538903) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (373833659 / 1000000000) (18691683 / 50000000) (Real.log (145329538903 / 100000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (145329538903 / 100000000000) = -Real.log (100000000000 / 145329538903) := by
    rw [show ((145329538903 / 100000000000) : ℝ) = ((100000000000 / 145329538903) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (7494027 / 20000000) ≤ -Real.log (31250000000 / 45454904573) ∧
    -Real.log (31250000000 / 45454904573) ≤ (374701351 / 1000000000) := by
  have h := checkLog_sound (w := (14204904573 / 76704904573)) (n := 12)
    (lo := (7494027 / 20000000)) (hi := (374701351 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((45454904573 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(45454904573 / 31250000000) = 1/(31250000000 / 45454904573) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (7494027 / 20000000) (374701351 / 1000000000) (Real.log (45454904573 / 31250000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (45454904573 / 31250000000) = -Real.log (31250000000 / 45454904573) := by
    rw [show ((45454904573 / 31250000000) : ℝ) = ((31250000000 / 45454904573) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (132673 / 500000) ≤ -Real.log (500000000000 / 651941020619) ∧
    -Real.log (500000000000 / 651941020619) ≤ (265346001 / 1000000000) := by
  have h := checkLog_sound (w := (151941020619 / 1151941020619)) (n := 12)
    (lo := (132673 / 500000)) (hi := (265346001 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((651941020619 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(651941020619 / 500000000000) = 1/(500000000000 / 651941020619) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (132673 / 500000) (265346001 / 1000000000) (Real.log (651941020619 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (651941020619 / 500000000000) = -Real.log (500000000000 / 651941020619) := by
    rw [show ((651941020619 / 500000000000) : ℝ) = ((500000000000 / 651941020619) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (132983413 / 500000000) ≤ -Real.log (250000000000 / 326172944071) ∧
    -Real.log (250000000000 / 326172944071) ≤ (265966827 / 1000000000) := by
  have h := checkLog_sound (w := (76172944071 / 576172944071)) (n := 12)
    (lo := (132983413 / 500000000)) (hi := (265966827 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((326172944071 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(326172944071 / 250000000000) = 1/(250000000000 / 326172944071) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (132983413 / 500000000) (265966827 / 1000000000) (Real.log (326172944071 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (326172944071 / 250000000000) = -Real.log (250000000000 / 326172944071) := by
    rw [show ((326172944071 / 250000000000) : ℝ) = ((250000000000 / 326172944071) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (4408177 / 250000000) ≤ -Real.log (39300873519 / 40000000000) ∧
    -Real.log (39300873519 / 40000000000) ≤ (17632709 / 1000000000) := by
  have h := checkLog_sound (w := (699126481 / 79300873519)) (n := 12)
    (lo := (4408177 / 250000000)) (hi := (17632709 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39300873519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39300873519) = 1/(39300873519 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-17632709 / 1000000000) (-4408177 / 250000000) (Real.log (39300873519 / 40000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (8775363 / 500000000) ≤ -Real.log (98260239 / 100000000) ∧
    -Real.log (98260239 / 100000000) ≤ (17550727 / 1000000000) := by
  have h := checkLog_sound (w := (1739761 / 198260239)) (n := 12)
    (lo := (8775363 / 500000000)) (hi := (17550727 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000000 / 98260239) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000000 / 98260239) = 1/(98260239 / 100000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-17550727 / 1000000000) (-8775363 / 500000000) (Real.log (98260239 / 100000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell018
