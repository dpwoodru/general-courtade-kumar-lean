import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0065
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

theorem reflection_log_1_neg : (84705851 / 125000000) ≤ -Real.log (2048 / 4033) ∧
    -Real.log (2048 / 4033) ≤ (677646809 / 1000000000) := by
  have h := checkLog_sound (w := (1985 / 6081)) (n := 12)
    (lo := (84705851 / 125000000)) (hi := (677646809 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4033 / 2048) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4033 / 2048) = 1/(2048 / 4033) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (84705851 / 125000000) (677646809 / 1000000000) (Real.log (4033 / 2048)) := by
  have h := reflection_log_1_neg
  have he : Real.log (4033 / 2048) = -Real.log (2048 / 4033) := by
    rw [show ((4033 / 2048) : ℝ) = ((2048 / 4033) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (108796383 / 31250000) ≤ -Real.log (63 / 2048) ∧
    -Real.log (63 / 2048) ≤ (1740742131 / 500000000) := by
  have h := checkLog_sound (w := (1 / 127)) (n := 12)
    (lo := (3937089 / 250000000)) (hi := (15748357 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((64 / 63) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(64 / 63) = 1/(63 / 2048) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-1740742131 / 500000000) (-108796383 / 31250000) (Real.log (63 / 2048)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (677552581 / 1000000000) ≤ -Real.log (102400 / 201631) ∧
    -Real.log (102400 / 201631) ≤ (338776291 / 500000000) := by
  have h := checkLog_sound (w := (99231 / 304031)) (n := 12)
    (lo := (677552581 / 1000000000)) (hi := (338776291 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((201631 / 102400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(201631 / 102400) = 1/(102400 / 201631) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (677552581 / 1000000000) (338776291 / 500000000) (Real.log (201631 / 102400)) := by
  have h := reflection_log_3_neg
  have he : Real.log (201631 / 102400) = -Real.log (102400 / 201631) := by
    rw [show ((201631 / 102400) : ℝ) = ((102400 / 201631) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (3475470629 / 1000000000) ≤ -Real.log (3169 / 102400) ∧
    -Real.log (3169 / 102400) ≤ (695094127 / 200000000) := by
  have h := checkLog_sound (w := (31 / 6369)) (n := 12)
    (lo := (9734729 / 1000000000)) (hi := (973473 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 3169) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3200 / 3169) = 1/(3169 / 102400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-695094127 / 200000000) (-3475470629 / 1000000000) (Real.log (3169 / 102400)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (661902387 / 1000000000) ≤ -Real.log (1024 / 1985) ∧
    -Real.log (1024 / 1985) ≤ (165475597 / 250000000) := by
  have h := checkLog_sound (w := (961 / 3009)) (n := 12)
    (lo := (661902387 / 1000000000)) (hi := (165475597 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1985 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1985 / 1024) = 1/(1024 / 1985) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (661902387 / 1000000000) (165475597 / 250000000) (Real.log (1985 / 1024)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1985 / 1024) = -Real.log (1024 / 1985) := by
    rw [show ((1985 / 1024) : ℝ) = ((1024 / 1985) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (697084269 / 250000000) ≤ -Real.log (63 / 1024) ∧
    -Real.log (63 / 1024) ≤ (2788337081 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 127)) (n := 12)
    (lo := (3937089 / 250000000)) (hi := (15748357 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((64 / 63) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(64 / 63) = 1/(63 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-2788337081 / 1000000000) (-697084269 / 250000000) (Real.log (63 / 1024)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (661710933 / 1000000000) ≤ -Real.log (51200 / 99231) ∧
    -Real.log (51200 / 99231) ≤ (330855467 / 500000000) := by
  have h := checkLog_sound (w := (48031 / 150431)) (n := 12)
    (lo := (661710933 / 1000000000)) (hi := (330855467 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((99231 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(99231 / 51200) = 1/(51200 / 99231) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (661710933 / 1000000000) (330855467 / 500000000) (Real.log (99231 / 51200)) := by
  have h := reflection_log_7_neg
  have he : Real.log (99231 / 51200) = -Real.log (51200 / 99231) := by
    rw [show ((99231 / 51200) : ℝ) = ((51200 / 99231) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (2782323449 / 1000000000) ≤ -Real.log (3169 / 51200) ∧
    -Real.log (3169 / 51200) ≤ (1391161727 / 500000000) := by
  have h := checkLog_sound (w := (31 / 6369)) (n := 12)
    (lo := (9734729 / 1000000000)) (hi := (973473 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 3169) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3200 / 3169) = 1/(3169 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1391161727 / 500000000) (-2782323449 / 1000000000) (Real.log (3169 / 51200)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (68014603 / 100000000) ≤ -Real.log (500000 / 987083) ∧
    -Real.log (500000 / 987083) ≤ (680146031 / 1000000000) := by
  have h := checkLog_sound (w := (487083 / 1487083)) (n := 12)
    (lo := (68014603 / 100000000)) (hi := (680146031 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((987083 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(987083 / 500000) = 1/(500000 / 987083) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (68014603 / 100000000) (680146031 / 1000000000) (Real.log (987083 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (987083 / 500000) = -Real.log (500000 / 987083) := by
    rw [show ((987083 / 500000) : ℝ) = ((500000 / 987083) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (1828031911 / 500000000) ≤ -Real.log (12917 / 500000) ∧
    -Real.log (12917 / 500000) ≤ (914015957 / 250000000) := by
  have h := checkLog_sound (w := (1354 / 14271)) (n := 12)
    (lo := (95163961 / 500000000)) (hi := (190327923 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 12917) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 12917) = 1/(12917 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-914015957 / 250000000) (-1828031911 / 500000000) (Real.log (12917 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (340110751 / 500000000) ≤ -Real.log (200000 / 394863) ∧
    -Real.log (200000 / 394863) ≤ (680221503 / 1000000000) := by
  have h := checkLog_sound (w := (194863 / 594863)) (n := 12)
    (lo := (340110751 / 500000000)) (hi := (680221503 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((394863 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(394863 / 200000) = 1/(200000 / 394863) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (340110751 / 500000000) (680221503 / 1000000000) (Real.log (394863 / 200000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (394863 / 200000) = -Real.log (200000 / 394863) := by
    rw [show ((394863 / 200000) : ℝ) = ((200000 / 394863) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (228865507 / 62500000) ≤ -Real.log (5137 / 200000) ∧
    -Real.log (5137 / 200000) ≤ (1830924059 / 500000000) := by
  have h := checkLog_sound (w := (1113 / 11387)) (n := 12)
    (lo := (49028053 / 250000000)) (hi := (196112213 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6250 / 5137) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(6250 / 5137) = 1/(5137 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1830924059 / 500000000) (-228865507 / 62500000) (Real.log (5137 / 200000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (680063967 / 1000000000) ≤ -Real.log (250000 / 493501) ∧
    -Real.log (250000 / 493501) ≤ (21251999 / 31250000) := by
  have h := checkLog_sound (w := (243501 / 743501)) (n := 12)
    (lo := (680063967 / 1000000000)) (hi := (21251999 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((493501 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(493501 / 250000) = 1/(250000 / 493501) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (680063967 / 1000000000) (21251999 / 31250000) (Real.log (493501 / 250000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (493501 / 250000) = -Real.log (250000 / 493501) := by
    rw [show ((493501 / 250000) : ℝ) = ((250000 / 493501) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (912453149 / 250000000) ≤ -Real.log (6499 / 250000) ∧
    -Real.log (6499 / 250000) ≤ (1824906301 / 500000000) := by
  have h := checkLog_sound (w := (2627 / 28623)) (n := 12)
    (lo := (23009587 / 125000000)) (hi := (184076697 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 12998) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 12998) = 1/(6499 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-1824906301 / 500000000) (-912453149 / 250000000) (Real.log (6499 / 250000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (42508747 / 62500000) ≤ -Real.log (500000 / 987077) ∧
    -Real.log (500000 / 987077) ≤ (680139953 / 1000000000) := by
  have h := checkLog_sound (w := (487077 / 1487077)) (n := 12)
    (lo := (42508747 / 62500000)) (hi := (680139953 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((987077 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(987077 / 500000) = 1/(500000 / 987077) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (42508747 / 62500000) (680139953 / 1000000000) (Real.log (987077 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (987077 / 500000) = -Real.log (500000 / 987077) := by
    rw [show ((987077 / 500000) : ℝ) = ((500000 / 987077) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (1827799713 / 500000000) ≤ -Real.log (12923 / 500000) ∧
    -Real.log (12923 / 500000) ≤ (456949929 / 125000000) := by
  have h := checkLog_sound (w := (1351 / 14274)) (n := 12)
    (lo := (94931763 / 500000000)) (hi := (189863527 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 12923) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 12923) = 1/(12923 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-456949929 / 125000000) (-1827799713 / 500000000) (Real.log (12923 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1084052463 / 250000000) ≤ -Real.log (125000000000 / 9552169621429) ∧
    -Real.log (125000000000 / 9552169621429) ≤ (4336209859 / 1000000000) := by
  have h := checkLog_sound (w := (1552169621429 / 17552169621429)) (n := 12)
    (lo := (44331693 / 250000000)) (hi := (177326773 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9552169621429 / 8000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(9552169621429 / 8000000000000) = 1/(125000000000 / 9552169621429) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1084052463 / 250000000) (4336209859 / 1000000000) (Real.log (9552169621429 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (9552169621429 / 125000000000) = -Real.log (125000000000 / 9552169621429) := by
    rw [show ((9552169621429 / 125000000000) : ℝ) = ((125000000000 / 9552169621429) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (2171034807 / 500000000) ≤ -Real.log (125000000000 / 9608307377847) ∧
    -Real.log (125000000000 / 9608307377847) ≤ (4342069621 / 1000000000) := by
  have h := checkLog_sound (w := (1608307377847 / 17608307377847)) (n := 12)
    (lo := (91593267 / 500000000)) (hi := (36637307 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9608307377847 / 8000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(9608307377847 / 8000000000000) = 1/(125000000000 / 9608307377847) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (2171034807 / 500000000) (4342069621 / 1000000000) (Real.log (9608307377847 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (9608307377847 / 125000000000) = -Real.log (125000000000 / 9608307377847) := by
    rw [show ((9608307377847 / 125000000000) : ℝ) = ((125000000000 / 9608307377847) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (2164938281 / 500000000) ≤ -Real.log (250000000000 / 18983728265887) ∧
    -Real.log (250000000000 / 18983728265887) ≤ (4329876569 / 1000000000) := by
  have h := checkLog_sound (w := (2983728265887 / 34983728265887)) (n := 12)
    (lo := (85496741 / 500000000)) (hi := (170993483 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((18983728265887 / 16000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(18983728265887 / 16000000000000) = 1/(250000000000 / 18983728265887) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (2164938281 / 500000000) (4329876569 / 1000000000) (Real.log (18983728265887 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (18983728265887 / 250000000000) = -Real.log (250000000000 / 18983728265887) := by
    rw [show ((18983728265887 / 250000000000) : ℝ) = ((250000000000 / 18983728265887) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (4335739377 / 1000000000) ≤ -Real.log (500000000000 / 38190706492301) ∧
    -Real.log (500000000000 / 38190706492301) ≤ (541967423 / 125000000) := by
  have h := checkLog_sound (w := (6190706492301 / 70190706492301)) (n := 12)
    (lo := (176856297 / 1000000000)) (hi := (88428149 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((38190706492301 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(38190706492301 / 32000000000000) = 1/(500000000000 / 38190706492301) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (4335739377 / 1000000000) (541967423 / 125000000) (Real.log (38190706492301 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (38190706492301 / 500000000000) = -Real.log (500000000000 / 38190706492301) := by
    rw [show ((38190706492301 / 500000000000) : ℝ) = ((500000000000 / 38190706492301) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0065
