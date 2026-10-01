import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0084
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

theorem reflection_log_1_neg : (134887619 / 200000000) ≤ -Real.log (25600 / 50251) ∧
    -Real.log (25600 / 50251) ≤ (42152381 / 62500000) := by
  have h := checkLog_sound (w := (24651 / 75851)) (n := 12)
    (lo := (134887619 / 200000000)) (hi := (42152381 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50251 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50251 / 25600) = 1/(25600 / 50251) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (134887619 / 200000000) (42152381 / 62500000) (Real.log (50251 / 25600)) := by
  have h := reflection_log_1_neg
  have he : Real.log (50251 / 25600) = -Real.log (25600 / 50251) := by
    rw [show ((50251 / 25600) : ℝ) = ((25600 / 50251) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (3294938829 / 1000000000) ≤ -Real.log (949 / 25600) ∧
    -Real.log (949 / 25600) ≤ (1647469417 / 500000000) := by
  have h := checkLog_sound (w := (651 / 2549)) (n := 12)
    (lo := (522350109 / 1000000000)) (hi := (52235011 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 949) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1600 / 949) = 1/(949 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-1647469417 / 500000000) (-3294938829 / 1000000000) (Real.log (949 / 25600)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (337124513 / 500000000) ≤ -Real.log (51200 / 100483) ∧
    -Real.log (51200 / 100483) ≤ (674249027 / 1000000000) := by
  have h := checkLog_sound (w := (49283 / 151683)) (n := 12)
    (lo := (337124513 / 500000000)) (hi := (674249027 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100483 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100483 / 51200) = 1/(51200 / 100483) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (337124513 / 500000000) (674249027 / 1000000000) (Real.log (100483 / 51200)) := by
  have h := reflection_log_3_neg
  have he : Real.log (100483 / 51200) = -Real.log (51200 / 100483) := by
    rw [show ((100483 / 51200) : ℝ) = ((51200 / 100483) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (656995613 / 200000000) ≤ -Real.log (1917 / 51200) ∧
    -Real.log (1917 / 51200) ≤ (328497807 / 100000000) := by
  have h := checkLog_sound (w := (1283 / 5117)) (n := 12)
    (lo := (102477869 / 200000000)) (hi := (256194673 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 1917) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3200 / 1917) = 1/(1917 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-328497807 / 100000000) (-656995613 / 200000000) (Real.log (1917 / 51200)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (81921537 / 125000000) ≤ -Real.log (12800 / 24651) ∧
    -Real.log (12800 / 24651) ≤ (655372297 / 1000000000) := by
  have h := checkLog_sound (w := (11851 / 37451)) (n := 12)
    (lo := (81921537 / 125000000)) (hi := (655372297 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24651 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24651 / 12800) = 1/(12800 / 24651) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (81921537 / 125000000) (655372297 / 1000000000) (Real.log (24651 / 12800)) := by
  have h := reflection_log_5_neg
  have he : Real.log (24651 / 12800) = -Real.log (12800 / 24651) := by
    rw [show ((24651 / 12800) : ℝ) = ((12800 / 24651) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (2601791649 / 1000000000) ≤ -Real.log (949 / 12800) ∧
    -Real.log (949 / 12800) ≤ (2601791653 / 1000000000) := by
  have h := checkLog_sound (w := (651 / 2549)) (n := 12)
    (lo := (522350109 / 1000000000)) (hi := (52235011 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 949) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1600 / 949) = 1/(949 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-2601791653 / 1000000000) (-2601791649 / 1000000000) (Real.log (949 / 12800)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (327493421 / 500000000) ≤ -Real.log (25600 / 49283) ∧
    -Real.log (25600 / 49283) ≤ (654986843 / 1000000000) := by
  have h := checkLog_sound (w := (23683 / 74883)) (n := 12)
    (lo := (327493421 / 500000000)) (hi := (654986843 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49283 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49283 / 25600) = 1/(25600 / 49283) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (327493421 / 500000000) (654986843 / 1000000000) (Real.log (49283 / 25600)) := by
  have h := reflection_log_7_neg
  have he : Real.log (49283 / 25600) = -Real.log (25600 / 49283) := by
    rw [show ((49283 / 25600) : ℝ) = ((25600 / 49283) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (518366177 / 200000000) ≤ -Real.log (1917 / 25600) ∧
    -Real.log (1917 / 25600) ≤ (2591830889 / 1000000000) := by
  have h := checkLog_sound (w := (1283 / 5117)) (n := 12)
    (lo := (102477869 / 200000000)) (hi := (256194673 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 1917) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(3200 / 1917) = 1/(1917 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-2591830889 / 1000000000) (-518366177 / 200000000) (Real.log (1917 / 25600)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (135510137 / 200000000) ≤ -Real.log (1000000 / 1969049) ∧
    -Real.log (1000000 / 1969049) ≤ (338775343 / 500000000) := by
  have h := checkLog_sound (w := (969049 / 2969049)) (n := 12)
    (lo := (135510137 / 200000000)) (hi := (338775343 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1969049 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1969049 / 1000000) = 1/(1000000 / 1969049) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (135510137 / 200000000) (338775343 / 500000000) (Real.log (1969049 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1969049 / 1000000) = -Real.log (1000000 / 1969049) := by
    rw [show ((1969049 / 1000000) : ℝ) = ((1000000 / 1969049) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (3475349967 / 1000000000) ≤ -Real.log (30951 / 1000000) ∧
    -Real.log (30951 / 1000000) ≤ (3475349973 / 1000000000) := by
  have h := checkLog_sound (w := (299 / 62201)) (n := 12)
    (lo := (9614067 / 1000000000)) (hi := (2403517 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 30951) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 30951) = 1/(30951 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-3475349973 / 1000000000) (-3475349967 / 1000000000) (Real.log (30951 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (677698969 / 1000000000) ≤ -Real.log (1000000 / 1969341) ∧
    -Real.log (1000000 / 1969341) ≤ (67769897 / 100000000) := by
  have h := checkLog_sound (w := (969341 / 2969341)) (n := 12)
    (lo := (677698969 / 1000000000)) (hi := (67769897 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1969341 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1969341 / 1000000) = 1/(1000000 / 1969341) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (677698969 / 1000000000) (67769897 / 100000000) (Real.log (1969341 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1969341 / 1000000) = -Real.log (1000000 / 1969341) := by
    rw [show ((1969341 / 1000000) : ℝ) = ((1000000 / 1969341) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (3484829019 / 1000000000) ≤ -Real.log (30659 / 1000000) ∧
    -Real.log (30659 / 1000000) ≤ (139393161 / 40000000) := by
  have h := checkLog_sound (w := (591 / 61909)) (n := 12)
    (lo := (19093119 / 1000000000)) (hi := (29833 / 1562500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 30659) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 30659) = 1/(30659 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-139393161 / 40000000) (-3484829019 / 1000000000) (Real.log (30659 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (33871211 / 50000000) ≤ -Real.log (1250 / 2461) ∧
    -Real.log (1250 / 2461) ≤ (677424221 / 1000000000) := by
  have h := checkLog_sound (w := (1211 / 3711)) (n := 12)
    (lo := (33871211 / 50000000)) (hi := (677424221 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2461 / 1250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2461 / 1250) = 1/(1250 / 2461) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (33871211 / 50000000) (677424221 / 1000000000) (Real.log (2461 / 1250)) := by
  have h := reflection_log_13_neg
  have he : Real.log (2461 / 1250) = -Real.log (1250 / 2461) := by
    rw [show ((2461 / 1250) : ℝ) = ((1250 / 2461) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (3467337181 / 1000000000) ≤ -Real.log (39 / 1250) ∧
    -Real.log (39 / 1250) ≤ (3467337187 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 1249)) (n := 12)
    (lo := (1601281 / 1000000000)) (hi := (800641 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625 / 624) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(625 / 624) = 1/(39 / 1250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-3467337187 / 1000000000) (-3467337181 / 1000000000) (Real.log (39 / 1250)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (338787531 / 500000000) ≤ -Real.log (1000000 / 1969097) ∧
    -Real.log (1000000 / 1969097) ≤ (677575063 / 1000000000) := by
  have h := checkLog_sound (w := (969097 / 2969097)) (n := 12)
    (lo := (338787531 / 500000000)) (hi := (677575063 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1969097 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1969097 / 1000000) = 1/(1000000 / 1969097) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (338787531 / 500000000) (677575063 / 1000000000) (Real.log (1969097 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1969097 / 1000000) = -Real.log (1000000 / 1969097) := by
    rw [show ((1969097 / 1000000) : ℝ) = ((1000000 / 1969097) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (3476902009 / 1000000000) ≤ -Real.log (30903 / 1000000) ∧
    -Real.log (30903 / 1000000) ≤ (695380403 / 200000000) := by
  have h := checkLog_sound (w := (347 / 62153)) (n := 12)
    (lo := (11166109 / 1000000000)) (hi := (1116611 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 30903) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 30903) = 1/(30903 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-695380403 / 200000000) (-3476902009 / 1000000000) (Real.log (30903 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1038225163 / 250000000) ≤ -Real.log (500000000000 / 31809133792123) ∧
    -Real.log (500000000000 / 31809133792123) ≤ (2076450329 / 500000000) := by
  have h := checkLog_sound (w := (15809133792123 / 47809133792123)) (n := 12)
    (lo := (42947797 / 62500000)) (hi := (687164753 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31809133792123 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31809133792123 / 16000000000000) = 1/(500000000000 / 31809133792123) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1038225163 / 250000000) (2076450329 / 500000000) (Real.log (31809133792123 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (31809133792123 / 500000000000) = -Real.log (500000000000 / 31809133792123) := by
    rw [show ((31809133792123 / 500000000000) : ℝ) = ((500000000000 / 31809133792123) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (4162527987 / 1000000000) ≤ -Real.log (500000000000 / 32116849864641) ∧
    -Real.log (500000000000 / 32116849864641) ≤ (2081263997 / 500000000) := by
  have h := checkLog_sound (w := (116849864641 / 64116849864641)) (n := 12)
    (lo := (3644907 / 1000000000)) (hi := (911227 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((32116849864641 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(32116849864641 / 32000000000000) = 1/(500000000000 / 32116849864641) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (4162527987 / 1000000000) (2081263997 / 500000000) (Real.log (32116849864641 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (32116849864641 / 500000000000) = -Real.log (500000000000 / 32116849864641) := by
    rw [show ((32116849864641 / 500000000000) : ℝ) = ((500000000000 / 32116849864641) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (4144761401 / 1000000000) ≤ -Real.log (250000000000 / 15775641025641) ∧
    -Real.log (250000000000 / 15775641025641) ≤ (4144761407 / 1000000000) := by
  have h := checkLog_sound (w := (7775641025641 / 23775641025641)) (n := 12)
    (lo := (679025501 / 1000000000)) (hi := (339512751 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15775641025641 / 8000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15775641025641 / 8000000000000) = 1/(250000000000 / 15775641025641) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (4144761401 / 1000000000) (4144761407 / 1000000000) (Real.log (15775641025641 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (15775641025641 / 250000000000) = -Real.log (250000000000 / 15775641025641) := by
    rw [show ((15775641025641 / 250000000000) : ℝ) = ((250000000000 / 15775641025641) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (4154477071 / 1000000000) ≤ -Real.log (25000000000 / 1592965893279) ∧
    -Real.log (25000000000 / 1592965893279) ≤ (4154477077 / 1000000000) := by
  have h := checkLog_sound (w := (792965893279 / 2392965893279)) (n := 12)
    (lo := (688741171 / 1000000000)) (hi := (172185293 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1592965893279 / 800000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(1592965893279 / 800000000000) = 1/(25000000000 / 1592965893279) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (4154477071 / 1000000000) (4154477077 / 1000000000) (Real.log (1592965893279 / 25000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1592965893279 / 25000000000) = -Real.log (25000000000 / 1592965893279) := by
    rw [show ((1592965893279 / 25000000000) : ℝ) = ((25000000000 / 1592965893279) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0084
