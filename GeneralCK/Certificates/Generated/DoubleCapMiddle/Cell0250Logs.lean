import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0250
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

theorem reflection_log_1_neg : (121473089 / 500000000) ≤ -Real.log (40 / 51) ∧
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


theorem reflection_log_1 : Bounds (121473089 / 500000000) (242946179 / 1000000000) (Real.log (51 / 40)) := by
  have h := reflection_log_1_neg
  have he : Real.log (51 / 40) = -Real.log (40 / 51) := by
    rw [show ((51 / 40) : ℝ) = ((40 / 51) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (40197953 / 125000000) ≤ -Real.log (29 / 40) ∧
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


theorem reflection_log_2 : Bounds (-2572669 / 8000000) (-40197953 / 125000000) (Real.log (29 / 40)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (121243257 / 500000000) ≤ -Real.log (1024 / 1305) ∧
    -Real.log (1024 / 1305) ≤ (48497303 / 200000000) := by
  have h := checkLog_sound (w := (281 / 2329)) (n := 12)
    (lo := (121243257 / 500000000)) (hi := (48497303 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1305 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1305 / 1024) = 1/(1024 / 1305) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (121243257 / 500000000) (48497303 / 200000000) (Real.log (1305 / 1024)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1305 / 1024) = -Real.log (1024 / 1305) := by
    rw [show ((1305 / 1024) : ℝ) = ((1024 / 1305) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (4009697 / 12500000) ≤ -Real.log (743 / 1024) ∧
    -Real.log (743 / 1024) ≤ (320775761 / 1000000000) := by
  have h := checkLog_sound (w := (281 / 1767)) (n := 12)
    (lo := (4009697 / 12500000)) (hi := (320775761 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 743) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 743) = 1/(743 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-320775761 / 1000000000) (-4009697 / 12500000) (Real.log (743 / 1024)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (43825493 / 100000000) ≤ -Real.log (20 / 31) ∧
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


theorem reflection_log_5 : Bounds (43825493 / 100000000) (438254931 / 1000000000) (Real.log (31 / 20)) := by
  have h := reflection_log_5_neg
  have he : Real.log (31 / 20) = -Real.log (20 / 31) := by
    rw [show ((31 / 20) : ℝ) = ((20 / 31) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (159701539 / 200000000) ≤ -Real.log (9 / 20) ∧
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


theorem reflection_log_6 : Bounds (-798507697 / 1000000000) (-159701539 / 200000000) (Real.log (9 / 20)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (109374649 / 250000000) ≤ -Real.log (512 / 793) ∧
    -Real.log (512 / 793) ≤ (437498597 / 1000000000) := by
  have h := checkLog_sound (w := (281 / 1305)) (n := 12)
    (lo := (109374649 / 250000000)) (hi := (437498597 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((793 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(793 / 512) = 1/(512 / 793) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (109374649 / 250000000) (437498597 / 1000000000) (Real.log (793 / 512)) := by
  have h := reflection_log_7_neg
  have he : Real.log (793 / 512) = -Real.log (512 / 793) := by
    rw [show ((793 / 512) : ℝ) = ((512 / 793) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (795906913 / 1000000000) ≤ -Real.log (231 / 512) ∧
    -Real.log (231 / 512) ≤ (159181383 / 200000000) := by
  have h := checkLog_sound (w := (25 / 487)) (n := 12)
    (lo := (102759733 / 1000000000)) (hi := (51379867 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((256 / 231) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(256 / 231) = 1/(231 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-159181383 / 200000000) (-795906913 / 1000000000) (Real.log (231 / 512)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (10373389 / 31250000) ≤ -Real.log (1000000 / 1393681) ∧
    -Real.log (1000000 / 1393681) ≤ (331948449 / 1000000000) := by
  have h := checkLog_sound (w := (393681 / 2393681)) (n := 12)
    (lo := (10373389 / 31250000)) (hi := (331948449 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1393681 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1393681 / 1000000) = 1/(1000000 / 1393681) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (10373389 / 31250000) (331948449 / 1000000000) (Real.log (1393681 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1393681 / 1000000) = -Real.log (1000000 / 1393681) := by
    rw [show ((1393681 / 1000000) : ℝ) = ((1000000 / 1393681) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (125087257 / 250000000) ≤ -Real.log (606319 / 1000000) ∧
    -Real.log (606319 / 1000000) ≤ (500349029 / 1000000000) := by
  have h := checkLog_sound (w := (393681 / 1606319)) (n := 12)
    (lo := (125087257 / 250000000)) (hi := (500349029 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 606319) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 606319) = 1/(606319 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-500349029 / 1000000000) (-125087257 / 250000000) (Real.log (606319 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (332572499 / 1000000000) ≤ -Real.log (1000000 / 1394551) ∧
    -Real.log (1000000 / 1394551) ≤ (133029 / 400000) := by
  have h := checkLog_sound (w := (394551 / 2394551)) (n := 12)
    (lo := (332572499 / 1000000000)) (hi := (133029 / 400000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1394551 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1394551 / 1000000) = 1/(1000000 / 1394551) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (332572499 / 1000000000) (133029 / 400000) (Real.log (1394551 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1394551 / 1000000) = -Real.log (1000000 / 1394551) := by
    rw [show ((1394551 / 1000000) : ℝ) = ((1000000 / 1394551) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (501784947 / 1000000000) ≤ -Real.log (605449 / 1000000) ∧
    -Real.log (605449 / 1000000) ≤ (125446237 / 250000000) := by
  have h := checkLog_sound (w := (394551 / 1605449)) (n := 12)
    (lo := (501784947 / 1000000000)) (hi := (125446237 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 605449) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 605449) = 1/(605449 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-125446237 / 250000000) (-501784947 / 1000000000) (Real.log (605449 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (51058169 / 200000000) ≤ -Real.log (1000000 / 1290837) ∧
    -Real.log (1000000 / 1290837) ≤ (127645423 / 500000000) := by
  have h := checkLog_sound (w := (290837 / 2290837)) (n := 12)
    (lo := (51058169 / 200000000)) (hi := (127645423 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1290837 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1290837 / 1000000) = 1/(1000000 / 1290837) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (51058169 / 200000000) (127645423 / 500000000) (Real.log (1290837 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1290837 / 1000000) = -Real.log (1000000 / 1290837) := by
    rw [show ((1290837 / 1000000) : ℝ) = ((1000000 / 1290837) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (343669877 / 1000000000) ≤ -Real.log (709163 / 1000000) ∧
    -Real.log (709163 / 1000000) ≤ (171834939 / 500000000) := by
  have h := checkLog_sound (w := (290837 / 1709163)) (n := 12)
    (lo := (343669877 / 1000000000)) (hi := (171834939 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 709163) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 709163) = 1/(709163 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-171834939 / 500000000) (-343669877 / 1000000000) (Real.log (709163 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (127916491 / 500000000) ≤ -Real.log (1000000 / 1291537) ∧
    -Real.log (1000000 / 1291537) ≤ (255832983 / 1000000000) := by
  have h := checkLog_sound (w := (291537 / 2291537)) (n := 12)
    (lo := (127916491 / 500000000)) (hi := (255832983 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1291537 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1291537 / 1000000) = 1/(1000000 / 1291537) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (127916491 / 500000000) (255832983 / 1000000000) (Real.log (1291537 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1291537 / 1000000) = -Real.log (1000000 / 1291537) := by
    rw [show ((1291537 / 1000000) : ℝ) = ((1000000 / 1291537) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (86164361 / 250000000) ≤ -Real.log (708463 / 1000000) ∧
    -Real.log (708463 / 1000000) ≤ (68931489 / 200000000) := by
  have h := checkLog_sound (w := (291537 / 1708463)) (n := 12)
    (lo := (86164361 / 250000000)) (hi := (68931489 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 708463) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 708463) = 1/(708463 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-68931489 / 200000000) (-86164361 / 250000000) (Real.log (708463 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (208074369 / 250000000) ≤ -Real.log (500000000000 / 1149296822299) ∧
    -Real.log (500000000000 / 1149296822299) ≤ (416148739 / 500000000) := by
  have h := checkLog_sound (w := (149296822299 / 2149296822299)) (n := 12)
    (lo := (17393787 / 125000000)) (hi := (139150297 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1149296822299 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1149296822299 / 1000000000000) = 1/(500000000000 / 1149296822299) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (208074369 / 250000000) (416148739 / 500000000) (Real.log (1149296822299 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1149296822299 / 500000000000) = -Real.log (500000000000 / 1149296822299) := by
    rw [show ((1149296822299 / 500000000000) : ℝ) = ((500000000000 / 1149296822299) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (417178723 / 500000000) ≤ -Real.log (500000000000 / 1151666779531) ∧
    -Real.log (500000000000 / 1151666779531) ≤ (104294681 / 125000000) := by
  have h := checkLog_sound (w := (151666779531 / 2151666779531)) (n := 12)
    (lo := (70605133 / 500000000)) (hi := (141210267 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1151666779531 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1151666779531 / 1000000000000) = 1/(500000000000 / 1151666779531) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (417178723 / 500000000) (104294681 / 125000000) (Real.log (1151666779531 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1151666779531 / 500000000000) = -Real.log (500000000000 / 1151666779531) := by
    rw [show ((1151666779531 / 500000000000) : ℝ) = ((500000000000 / 1151666779531) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (299480361 / 500000000) ≤ -Real.log (500000000000 / 910113048763) ∧
    -Real.log (500000000000 / 910113048763) ≤ (598960723 / 1000000000) := by
  have h := checkLog_sound (w := (410113048763 / 1410113048763)) (n := 12)
    (lo := (299480361 / 500000000)) (hi := (598960723 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((910113048763 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(910113048763 / 500000000000) = 1/(500000000000 / 910113048763) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (299480361 / 500000000) (598960723 / 1000000000) (Real.log (910113048763 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (910113048763 / 500000000000) = -Real.log (500000000000 / 910113048763) := by
    rw [show ((910113048763 / 500000000000) : ℝ) = ((500000000000 / 910113048763) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (300245213 / 500000000) ≤ -Real.log (500000000000 / 911506317197) ∧
    -Real.log (500000000000 / 911506317197) ≤ (600490427 / 1000000000) := by
  have h := checkLog_sound (w := (411506317197 / 1411506317197)) (n := 12)
    (lo := (300245213 / 500000000)) (hi := (600490427 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((911506317197 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(911506317197 / 500000000000) = 1/(500000000000 / 911506317197) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (300245213 / 500000000) (600490427 / 1000000000) (Real.log (911506317197 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (911506317197 / 500000000000) = -Real.log (500000000000 / 911506317197) := by
    rw [show ((911506317197 / 500000000000) : ℝ) = ((500000000000 / 911506317197) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0250
