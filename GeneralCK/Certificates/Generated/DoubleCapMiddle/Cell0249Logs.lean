import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0249
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

theorem reflection_log_1_neg : (243405631 / 1000000000) ≤ -Real.log (5120 / 6531) ∧
    -Real.log (5120 / 6531) ≤ (3803213 / 15625000) := by
  have h := checkLog_sound (w := (1411 / 11651)) (n := 12)
    (lo := (243405631 / 1000000000)) (hi := (3803213 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6531 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6531 / 5120) = 1/(5120 / 6531) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (243405631 / 1000000000) (3803213 / 15625000) (Real.log (6531 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6531 / 5120) = -Real.log (5120 / 6531) := by
    rw [show ((6531 / 5120) : ℝ) = ((5120 / 6531) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (16119607 / 50000000) ≤ -Real.log (3709 / 5120) ∧
    -Real.log (3709 / 5120) ≤ (322392141 / 1000000000) := by
  have h := checkLog_sound (w := (1411 / 8829)) (n := 12)
    (lo := (16119607 / 50000000)) (hi := (322392141 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3709) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3709) = 1/(3709 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-322392141 / 1000000000) (-16119607 / 50000000) (Real.log (3709 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (121473089 / 500000000) ≤ -Real.log (40 / 51) ∧
    -Real.log (40 / 51) ≤ (242946179 / 1000000000) := by
  have h := checkLog_sound (w := (11 / 91)) (n := 12)
    (lo := (121473089 / 500000000)) (hi := (242946179 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((51 / 40) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(51 / 40) = 1/(40 / 51) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (121473089 / 500000000) (242946179 / 1000000000) (Real.log (51 / 40)) := by
  have h := reflection_log_3_neg
  have he : Real.log (51 / 40) = -Real.log (40 / 51) := by
    rw [show ((51 / 40) : ℝ) = ((40 / 51) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (40197953 / 125000000) ≤ -Real.log (29 / 40) ∧
    -Real.log (29 / 40) ≤ (2572669 / 8000000) := by
  have h := checkLog_sound (w := (11 / 69)) (n := 12)
    (lo := (40197953 / 125000000)) (hi := (2572669 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40 / 29) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40 / 29) = 1/(29 / 40) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-2572669 / 8000000) (-40197953 / 125000000) (Real.log (29 / 40)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (439010693 / 1000000000) ≤ -Real.log (2560 / 3971) ∧
    -Real.log (2560 / 3971) ≤ (219505347 / 500000000) := by
  have h := checkLog_sound (w := (1411 / 6531)) (n := 12)
    (lo := (439010693 / 1000000000)) (hi := (219505347 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3971 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3971 / 2560) = 1/(2560 / 3971) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (439010693 / 1000000000) (219505347 / 500000000) (Real.log (3971 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (3971 / 2560) = -Real.log (2560 / 3971) := by
    rw [show ((3971 / 2560) : ℝ) = ((2560 / 3971) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (801115259 / 1000000000) ≤ -Real.log (1149 / 2560) ∧
    -Real.log (1149 / 2560) ≤ (801115261 / 1000000000) := by
  have h := checkLog_sound (w := (131 / 2429)) (n := 12)
    (lo := (107968079 / 1000000000)) (hi := (1349601 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 1149) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 1149) = 1/(1149 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-801115261 / 1000000000) (-801115259 / 1000000000) (Real.log (1149 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (43825493 / 100000000) ≤ -Real.log (20 / 31) ∧
    -Real.log (20 / 31) ≤ (438254931 / 1000000000) := by
  have h := checkLog_sound (w := (11 / 51)) (n := 12)
    (lo := (43825493 / 100000000)) (hi := (438254931 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31 / 20) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31 / 20) = 1/(20 / 31) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (43825493 / 100000000) (438254931 / 1000000000) (Real.log (31 / 20)) := by
  have h := reflection_log_7_neg
  have he : Real.log (31 / 20) = -Real.log (20 / 31) := by
    rw [show ((31 / 20) : ℝ) = ((20 / 31) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (159701539 / 200000000) ≤ -Real.log (9 / 20) ∧
    -Real.log (9 / 20) ≤ (798507697 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 19)) (n := 12)
    (lo := (21072103 / 200000000)) (hi := (26340129 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10 / 9) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(10 / 9) = 1/(9 / 20) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-798507697 / 1000000000) (-159701539 / 200000000) (Real.log (9 / 20)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (166285891 / 500000000) ≤ -Real.log (20000 / 27891) ∧
    -Real.log (20000 / 27891) ≤ (332571783 / 1000000000) := by
  have h := checkLog_sound (w := (7891 / 47891)) (n := 12)
    (lo := (166285891 / 500000000)) (hi := (332571783 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((27891 / 20000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(27891 / 20000) = 1/(20000 / 27891) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (166285891 / 500000000) (332571783 / 1000000000) (Real.log (27891 / 20000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (27891 / 20000) = -Real.log (20000 / 27891) := by
    rw [show ((27891 / 20000) : ℝ) = ((20000 / 27891) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (100356659 / 200000000) ≤ -Real.log (12109 / 20000) ∧
    -Real.log (12109 / 20000) ≤ (1960091 / 3906250) := by
  have h := checkLog_sound (w := (7891 / 32109)) (n := 12)
    (lo := (100356659 / 200000000)) (hi := (1960091 / 3906250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20000 / 12109) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20000 / 12109) = 1/(12109 / 20000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-1960091 / 3906250) (-100356659 / 200000000) (Real.log (12109 / 20000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (41649341 / 125000000) ≤ -Real.log (1000000 / 1395419) ∧
    -Real.log (1000000 / 1395419) ≤ (333194729 / 1000000000) := by
  have h := checkLog_sound (w := (395419 / 2395419)) (n := 12)
    (lo := (41649341 / 125000000)) (hi := (333194729 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1395419 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1395419 / 1000000) = 1/(1000000 / 1395419) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (41649341 / 125000000) (333194729 / 1000000000) (Real.log (1395419 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1395419 / 1000000) = -Real.log (1000000 / 1395419) := by
    rw [show ((1395419 / 1000000) : ℝ) = ((1000000 / 1395419) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (251609811 / 500000000) ≤ -Real.log (604581 / 1000000) ∧
    -Real.log (604581 / 1000000) ≤ (503219623 / 1000000000) := by
  have h := checkLog_sound (w := (395419 / 1604581)) (n := 12)
    (lo := (251609811 / 500000000)) (hi := (503219623 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 604581) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 604581) = 1/(604581 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-503219623 / 1000000000) (-251609811 / 500000000) (Real.log (604581 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (255832207 / 1000000000) ≤ -Real.log (62500 / 80721) ∧
    -Real.log (62500 / 80721) ≤ (15989513 / 62500000) := by
  have h := checkLog_sound (w := (18221 / 143221)) (n := 12)
    (lo := (255832207 / 1000000000)) (hi := (15989513 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80721 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(80721 / 62500) = 1/(62500 / 80721) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (255832207 / 1000000000) (15989513 / 62500000) (Real.log (80721 / 62500)) := by
  have h := reflection_log_13_neg
  have he : Real.log (80721 / 62500) = -Real.log (62500 / 80721) := by
    rw [show ((80721 / 62500) : ℝ) = ((62500 / 80721) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (10770501 / 31250000) ≤ -Real.log (44279 / 62500) ∧
    -Real.log (44279 / 62500) ≤ (344656033 / 1000000000) := by
  have h := checkLog_sound (w := (18221 / 106779)) (n := 12)
    (lo := (10770501 / 31250000)) (hi := (344656033 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 44279) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 44279) = 1/(44279 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-344656033 / 1000000000) (-10770501 / 31250000) (Real.log (44279 / 62500)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (10254993 / 40000000) ≤ -Real.log (1000000 / 1292237) ∧
    -Real.log (1000000 / 1292237) ≤ (128187413 / 500000000) := by
  have h := checkLog_sound (w := (292237 / 2292237)) (n := 12)
    (lo := (10254993 / 40000000)) (hi := (128187413 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1292237 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1292237 / 1000000) = 1/(1000000 / 1292237) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (10254993 / 40000000) (128187413 / 500000000) (Real.log (1292237 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1292237 / 1000000) = -Real.log (1000000 / 1292237) := by
    rw [show ((1292237 / 1000000) : ℝ) = ((1000000 / 1292237) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (345645987 / 1000000000) ≤ -Real.log (707763 / 1000000) ∧
    -Real.log (707763 / 1000000) ≤ (86411497 / 250000000) := by
  have h := checkLog_sound (w := (292237 / 1707763)) (n := 12)
    (lo := (345645987 / 1000000000)) (hi := (86411497 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 707763) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 707763) = 1/(707763 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-86411497 / 250000000) (-345645987 / 1000000000) (Real.log (707763 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (834355077 / 1000000000) ≤ -Real.log (500000000000 / 1151664051531) ∧
    -Real.log (500000000000 / 1151664051531) ≤ (834355079 / 1000000000) := by
  have h := checkLog_sound (w := (151664051531 / 2151664051531)) (n := 12)
    (lo := (141207897 / 1000000000)) (hi := (70603949 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1151664051531 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1151664051531 / 1000000000000) = 1/(500000000000 / 1151664051531) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (834355077 / 1000000000) (834355079 / 1000000000) (Real.log (1151664051531 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1151664051531 / 500000000000) = -Real.log (500000000000 / 1151664051531) := by
    rw [show ((1151664051531 / 500000000000) : ℝ) = ((500000000000 / 1151664051531) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (16728287 / 20000000) ≤ -Real.log (500000000000 / 1154038085881) ∧
    -Real.log (500000000000 / 1154038085881) ≤ (52275897 / 62500000) := by
  have h := checkLog_sound (w := (154038085881 / 2154038085881)) (n := 12)
    (lo := (14326717 / 100000000)) (hi := (143267171 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1154038085881 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1154038085881 / 1000000000000) = 1/(500000000000 / 1154038085881) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (16728287 / 20000000) (52275897 / 62500000) (Real.log (1154038085881 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1154038085881 / 500000000000) = -Real.log (500000000000 / 1154038085881) := by
    rw [show ((1154038085881 / 500000000000) : ℝ) = ((500000000000 / 1154038085881) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (7506103 / 12500000) ≤ -Real.log (500000000000 / 911504324849) ∧
    -Real.log (500000000000 / 911504324849) ≤ (600488241 / 1000000000) := by
  have h := checkLog_sound (w := (411504324849 / 1411504324849)) (n := 12)
    (lo := (7506103 / 12500000)) (hi := (600488241 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((911504324849 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(911504324849 / 500000000000) = 1/(500000000000 / 911504324849) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (7506103 / 12500000) (600488241 / 1000000000) (Real.log (911504324849 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (911504324849 / 500000000000) = -Real.log (500000000000 / 911504324849) := by
    rw [show ((911504324849 / 500000000000) : ℝ) = ((500000000000 / 911504324849) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (150505203 / 250000000) ≤ -Real.log (125000000000 / 228225585401) ∧
    -Real.log (125000000000 / 228225585401) ≤ (602020813 / 1000000000) := by
  have h := checkLog_sound (w := (103225585401 / 353225585401)) (n := 12)
    (lo := (150505203 / 250000000)) (hi := (602020813 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((228225585401 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(228225585401 / 125000000000) = 1/(125000000000 / 228225585401) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (150505203 / 250000000) (602020813 / 1000000000) (Real.log (228225585401 / 125000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (228225585401 / 125000000000) = -Real.log (125000000000 / 228225585401) := by
    rw [show ((228225585401 / 125000000000) : ℝ) = ((125000000000 / 228225585401) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0249
