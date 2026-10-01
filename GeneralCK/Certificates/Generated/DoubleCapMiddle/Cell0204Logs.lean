import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0204
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

theorem reflection_log_1_neg : (13193277 / 50000000) ≤ -Real.log (2560 / 3333) ∧
    -Real.log (2560 / 3333) ≤ (263865541 / 1000000000) := by
  have h := checkLog_sound (w := (773 / 5893)) (n := 12)
    (lo := (13193277 / 50000000)) (hi := (263865541 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3333 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3333 / 2560) = 1/(2560 / 3333) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (13193277 / 50000000) (263865541 / 1000000000) (Real.log (3333 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3333 / 2560) = -Real.log (2560 / 3333) := by
    rw [show ((3333 / 2560) : ℝ) = ((2560 / 3333) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (179734511 / 500000000) ≤ -Real.log (1787 / 2560) ∧
    -Real.log (1787 / 2560) ≤ (359469023 / 1000000000) := by
  have h := checkLog_sound (w := (773 / 4347)) (n := 12)
    (lo := (179734511 / 500000000)) (hi := (359469023 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1787) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1787) = 1/(1787 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-359469023 / 1000000000) (-179734511 / 500000000) (Real.log (1787 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (131707697 / 500000000) ≤ -Real.log (5120 / 6663) ∧
    -Real.log (5120 / 6663) ≤ (52683079 / 200000000) := by
  have h := checkLog_sound (w := (1543 / 11783)) (n := 12)
    (lo := (131707697 / 500000000)) (hi := (52683079 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6663 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6663 / 5120) = 1/(5120 / 6663) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (131707697 / 500000000) (52683079 / 200000000) (Real.log (6663 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6663 / 5120) = -Real.log (5120 / 6663) := by
    rw [show ((6663 / 5120) : ℝ) = ((5120 / 6663) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (179314989 / 500000000) ≤ -Real.log (3577 / 5120) ∧
    -Real.log (3577 / 5120) ≤ (358629979 / 1000000000) := by
  have h := checkLog_sound (w := (1543 / 8697)) (n := 12)
    (lo := (179314989 / 500000000)) (hi := (358629979 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3577) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3577) = 1/(3577 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-358629979 / 1000000000) (-179314989 / 500000000) (Real.log (3577 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (23622103 / 50000000) ≤ -Real.log (1280 / 2053) ∧
    -Real.log (1280 / 2053) ≤ (472442061 / 1000000000) := by
  have h := checkLog_sound (w := (773 / 3333)) (n := 12)
    (lo := (23622103 / 50000000)) (hi := (472442061 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2053 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2053 / 1280) = 1/(1280 / 2053) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (23622103 / 50000000) (472442061 / 1000000000) (Real.log (2053 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2053 / 1280) = -Real.log (1280 / 2053) := by
    rw [show ((2053 / 1280) : ℝ) = ((1280 / 2053) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (28940761 / 31250000) ≤ -Real.log (507 / 1280) ∧
    -Real.log (507 / 1280) ≤ (463052177 / 500000000) := by
  have h := checkLog_sound (w := (133 / 1147)) (n := 12)
    (lo := (58239293 / 250000000)) (hi := (232957173 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 507) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 507) = 1/(507 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-463052177 / 500000000) (-28940761 / 31250000) (Real.log (507 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (235855577 / 500000000) ≤ -Real.log (2560 / 4103) ∧
    -Real.log (2560 / 4103) ≤ (94342231 / 200000000) := by
  have h := checkLog_sound (w := (1543 / 6663)) (n := 12)
    (lo := (235855577 / 500000000)) (hi := (94342231 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4103 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4103 / 2560) = 1/(2560 / 4103) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (235855577 / 500000000) (94342231 / 200000000) (Real.log (4103 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (4103 / 2560) = -Real.log (2560 / 4103) := by
    rw [show ((4103 / 2560) : ℝ) = ((2560 / 4103) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (46157507 / 50000000) ≤ -Real.log (1017 / 2560) ∧
    -Real.log (1017 / 2560) ≤ (461575071 / 500000000) := by
  have h := checkLog_sound (w := (263 / 2297)) (n := 12)
    (lo := (2875037 / 12500000)) (hi := (230002961 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 1017) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 1017) = 1/(1017 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-461575071 / 500000000) (-46157507 / 50000000) (Real.log (1017 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (360377779 / 1000000000) ≤ -Real.log (1000000 / 1433871) ∧
    -Real.log (1000000 / 1433871) ≤ (18018889 / 50000000) := by
  have h := checkLog_sound (w := (433871 / 2433871)) (n := 12)
    (lo := (360377779 / 1000000000)) (hi := (18018889 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1433871 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1433871 / 1000000) = 1/(1000000 / 1433871) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (360377779 / 1000000000) (18018889 / 50000000) (Real.log (1433871 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1433871 / 1000000) = -Real.log (1000000 / 1433871) := by
    rw [show ((1433871 / 1000000) : ℝ) = ((1000000 / 1433871) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (568933311 / 1000000000) ≤ -Real.log (566129 / 1000000) ∧
    -Real.log (566129 / 1000000) ≤ (8889583 / 15625000) := by
  have h := checkLog_sound (w := (433871 / 1566129)) (n := 12)
    (lo := (568933311 / 1000000000)) (hi := (8889583 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 566129) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 566129) = 1/(566129 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-8889583 / 15625000) (-568933311 / 1000000000) (Real.log (566129 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (180495657 / 500000000) ≤ -Real.log (1000000 / 1434751) ∧
    -Real.log (1000000 / 1434751) ≤ (72198263 / 200000000) := by
  have h := checkLog_sound (w := (434751 / 2434751)) (n := 12)
    (lo := (180495657 / 500000000)) (hi := (72198263 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1434751 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1434751 / 1000000) = 1/(1000000 / 1434751) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (180495657 / 500000000) (72198263 / 200000000) (Real.log (1434751 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1434751 / 1000000) = -Real.log (1000000 / 1434751) := by
    rw [show ((1434751 / 1000000) : ℝ) = ((1000000 / 1434751) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (71311117 / 125000000) ≤ -Real.log (565249 / 1000000) ∧
    -Real.log (565249 / 1000000) ≤ (570488937 / 1000000000) := by
  have h := checkLog_sound (w := (434751 / 1565249)) (n := 12)
    (lo := (71311117 / 125000000)) (hi := (570488937 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 565249) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 565249) = 1/(565249 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-570488937 / 1000000000) (-71311117 / 125000000) (Real.log (565249 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (280372673 / 1000000000) ≤ -Real.log (1000000 / 1323623) ∧
    -Real.log (1000000 / 1323623) ≤ (140186337 / 500000000) := by
  have h := checkLog_sound (w := (323623 / 2323623)) (n := 12)
    (lo := (280372673 / 1000000000)) (hi := (140186337 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1323623 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1323623 / 1000000) = 1/(1000000 / 1323623) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (280372673 / 1000000000) (140186337 / 500000000) (Real.log (1323623 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1323623 / 1000000) = -Real.log (1000000 / 1323623) := by
    rw [show ((1323623 / 1000000) : ℝ) = ((1000000 / 1323623) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (195502333 / 500000000) ≤ -Real.log (676377 / 1000000) ∧
    -Real.log (676377 / 1000000) ≤ (391004667 / 1000000000) := by
  have h := checkLog_sound (w := (323623 / 1676377)) (n := 12)
    (lo := (195502333 / 500000000)) (hi := (391004667 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 676377) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 676377) = 1/(676377 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-391004667 / 1000000000) (-195502333 / 500000000) (Real.log (676377 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (280923283 / 1000000000) ≤ -Real.log (15625 / 20693) ∧
    -Real.log (15625 / 20693) ≤ (70230821 / 250000000) := by
  have h := checkLog_sound (w := (2534 / 18159)) (n := 12)
    (lo := (280923283 / 1000000000)) (hi := (70230821 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20693 / 15625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20693 / 15625) = 1/(15625 / 20693) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (280923283 / 1000000000) (70230821 / 250000000) (Real.log (20693 / 15625)) := by
  have h := reflection_log_15_neg
  have he : Real.log (20693 / 15625) = -Real.log (15625 / 20693) := by
    rw [show ((20693 / 15625) : ℝ) = ((15625 / 20693) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (49010381 / 125000000) ≤ -Real.log (10557 / 15625) ∧
    -Real.log (10557 / 15625) ≤ (392083049 / 1000000000) := by
  have h := checkLog_sound (w := (2534 / 13091)) (n := 12)
    (lo := (49010381 / 125000000)) (hi := (392083049 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 10557) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625 / 10557) = 1/(10557 / 15625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-392083049 / 1000000000) (-49010381 / 125000000) (Real.log (10557 / 15625)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (92931109 / 100000000) ≤ -Real.log (50000000000 / 126638186703) ∧
    -Real.log (50000000000 / 126638186703) ≤ (232327773 / 250000000) := by
  have h := checkLog_sound (w := (26638186703 / 226638186703)) (n := 12)
    (lo := (23616391 / 100000000)) (hi := (236163911 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((126638186703 / 100000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(126638186703 / 100000000000) = 1/(50000000000 / 126638186703) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (92931109 / 100000000) (232327773 / 250000000) (Real.log (126638186703 / 50000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (126638186703 / 50000000000) = -Real.log (50000000000 / 126638186703) := by
    rw [show ((126638186703 / 50000000000) : ℝ) = ((50000000000 / 126638186703) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (931480251 / 1000000000) ≤ -Real.log (31250000000 / 79320739621) ∧
    -Real.log (31250000000 / 79320739621) ≤ (931480253 / 1000000000) := by
  have h := checkLog_sound (w := (16820739621 / 141820739621)) (n := 12)
    (lo := (238333071 / 1000000000)) (hi := (14895817 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((79320739621 / 62500000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(79320739621 / 62500000000) = 1/(31250000000 / 79320739621) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (931480251 / 1000000000) (931480253 / 1000000000) (Real.log (79320739621 / 31250000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (79320739621 / 31250000000) = -Real.log (31250000000 / 79320739621) := by
    rw [show ((79320739621 / 31250000000) : ℝ) = ((31250000000 / 79320739621) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (671377339 / 1000000000) ≤ -Real.log (12500000000 / 24461635301) ∧
    -Real.log (12500000000 / 24461635301) ≤ (33568867 / 50000000) := by
  have h := checkLog_sound (w := (11961635301 / 36961635301)) (n := 12)
    (lo := (671377339 / 1000000000)) (hi := (33568867 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24461635301 / 12500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24461635301 / 12500000000) = 1/(12500000000 / 24461635301) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (671377339 / 1000000000) (33568867 / 50000000) (Real.log (24461635301 / 12500000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (24461635301 / 12500000000) = -Real.log (12500000000 / 24461635301) := by
    rw [show ((24461635301 / 12500000000) : ℝ) = ((12500000000 / 24461635301) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (673006331 / 1000000000) ≤ -Real.log (125000000000 / 245015155821) ∧
    -Real.log (125000000000 / 245015155821) ≤ (168251583 / 250000000) := by
  have h := checkLog_sound (w := (120015155821 / 370015155821)) (n := 12)
    (lo := (673006331 / 1000000000)) (hi := (168251583 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((245015155821 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(245015155821 / 125000000000) = 1/(125000000000 / 245015155821) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (673006331 / 1000000000) (168251583 / 250000000) (Real.log (245015155821 / 125000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (245015155821 / 125000000000) = -Real.log (125000000000 / 245015155821) := by
    rw [show ((245015155821 / 125000000000) : ℝ) = ((125000000000 / 245015155821) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0204
