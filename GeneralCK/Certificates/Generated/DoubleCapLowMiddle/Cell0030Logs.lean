import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0030
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

theorem reflection_log_1_neg : (85117397 / 125000000) ≤ -Real.log (20480 / 40463) ∧
    -Real.log (20480 / 40463) ≤ (680939177 / 1000000000) := by
  have h := checkLog_sound (w := (19983 / 60943)) (n := 12)
    (lo := (85117397 / 125000000)) (hi := (680939177 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40463 / 20480) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40463 / 20480) = 1/(20480 / 40463) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (85117397 / 125000000) (680939177 / 1000000000) (Real.log (40463 / 20480)) := by
  have h := reflection_log_1_neg
  have he : Real.log (40463 / 20480) = -Real.log (20480 / 40463) := by
    rw [show ((40463 / 20480) : ℝ) = ((20480 / 40463) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (74372281 / 20000000) ≤ -Real.log (497 / 20480) ∧
    -Real.log (497 / 20480) ≤ (464826757 / 125000000) := by
  have h := checkLog_sound (w := (143 / 1137)) (n := 12)
    (lo := (5057563 / 20000000)) (hi := (252878151 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 497) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(640 / 497) = 1/(497 / 20480) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-464826757 / 125000000) (-74372281 / 20000000) (Real.log (497 / 20480)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (340422629 / 500000000) ≤ -Real.log (12800 / 25287) ∧
    -Real.log (12800 / 25287) ≤ (680845259 / 1000000000) := by
  have h := checkLog_sound (w := (12487 / 38087)) (n := 12)
    (lo := (340422629 / 500000000)) (hi := (680845259 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25287 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25287 / 12800) = 1/(12800 / 25287) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (340422629 / 500000000) (680845259 / 1000000000) (Real.log (25287 / 12800)) := by
  have h := reflection_log_3_neg
  have he : Real.log (25287 / 12800) = -Real.log (12800 / 25287) := by
    rw [show ((25287 / 12800) : ℝ) = ((12800 / 25287) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (463874657 / 125000000) ≤ -Real.log (313 / 12800) ∧
    -Real.log (313 / 12800) ≤ (1855498631 / 500000000) := by
  have h := checkLog_sound (w := (87 / 713)) (n := 12)
    (lo := (61315339 / 250000000)) (hi := (245261357 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 313) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(400 / 313) = 1/(313 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-1855498631 / 500000000) (-463874657 / 125000000) (Real.log (313 / 12800)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (167145073 / 250000000) ≤ -Real.log (10240 / 19983) ∧
    -Real.log (10240 / 19983) ≤ (668580293 / 1000000000) := by
  have h := checkLog_sound (w := (9743 / 30223)) (n := 12)
    (lo := (167145073 / 250000000)) (hi := (668580293 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((19983 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(19983 / 10240) = 1/(10240 / 19983) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (167145073 / 250000000) (668580293 / 1000000000) (Real.log (19983 / 10240)) := by
  have h := reflection_log_5_neg
  have he : Real.log (19983 / 10240) = -Real.log (10240 / 19983) := by
    rw [show ((19983 / 10240) : ℝ) = ((10240 / 19983) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (302546687 / 100000000) ≤ -Real.log (497 / 10240) ∧
    -Real.log (497 / 10240) ≤ (4840747 / 1600000) := by
  have h := checkLog_sound (w := (143 / 1137)) (n := 12)
    (lo := (5057563 / 20000000)) (hi := (252878151 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 497) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(640 / 497) = 1/(497 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-4840747 / 1600000) (-302546687 / 100000000) (Real.log (497 / 10240)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (20887191 / 31250000) ≤ -Real.log (6400 / 12487) ∧
    -Real.log (6400 / 12487) ≤ (668390113 / 1000000000) := by
  have h := checkLog_sound (w := (6087 / 18887)) (n := 12)
    (lo := (20887191 / 31250000)) (hi := (668390113 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12487 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12487 / 6400) = 1/(6400 / 12487) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (20887191 / 31250000) (668390113 / 1000000000) (Real.log (12487 / 6400)) := by
  have h := reflection_log_7_neg
  have he : Real.log (12487 / 6400) = -Real.log (6400 / 12487) := by
    rw [show ((12487 / 6400) : ℝ) = ((6400 / 12487) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (754462519 / 250000000) ≤ -Real.log (313 / 6400) ∧
    -Real.log (313 / 6400) ≤ (3017850081 / 1000000000) := by
  have h := checkLog_sound (w := (87 / 713)) (n := 12)
    (lo := (61315339 / 250000000)) (hi := (245261357 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 313) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(400 / 313) = 1/(313 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-3017850081 / 1000000000) (-754462519 / 250000000) (Real.log (313 / 6400)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (682777601 / 1000000000) ≤ -Real.log (125000 / 247421) ∧
    -Real.log (125000 / 247421) ≤ (341388801 / 500000000) := by
  have h := checkLog_sound (w := (122421 / 372421)) (n := 12)
    (lo := (682777601 / 1000000000)) (hi := (341388801 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((247421 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(247421 / 125000) = 1/(125000 / 247421) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (682777601 / 1000000000) (341388801 / 500000000) (Real.log (247421 / 125000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (247421 / 125000) = -Real.log (125000 / 247421) := by
    rw [show ((247421 / 125000) : ℝ) = ((125000 / 247421) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (3880912007 / 1000000000) ≤ -Real.log (2579 / 125000) ∧
    -Real.log (2579 / 125000) ≤ (3880912013 / 1000000000) := by
  have h := checkLog_sound (w := (5309 / 25941)) (n := 12)
    (lo := (415176107 / 1000000000)) (hi := (103794027 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 10316) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 10316) = 1/(2579 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-3880912013 / 1000000000) (-3880912007 / 1000000000) (Real.log (2579 / 125000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (34142669 / 50000000) ≤ -Real.log (500000 / 989759) ∧
    -Real.log (500000 / 989759) ≤ (682853381 / 1000000000) := by
  have h := checkLog_sound (w := (489759 / 1489759)) (n := 12)
    (lo := (34142669 / 50000000)) (hi := (682853381 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((989759 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(989759 / 500000) = 1/(500000 / 989759) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (34142669 / 50000000) (682853381 / 1000000000) (Real.log (989759 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (989759 / 500000) = -Real.log (500000 / 989759) := by
    rw [show ((989759 / 500000) : ℝ) = ((500000 / 989759) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (486026103 / 125000000) ≤ -Real.log (10241 / 500000) ∧
    -Real.log (10241 / 500000) ≤ (388820883 / 100000000) := by
  have h := checkLog_sound (w := (2692 / 12933)) (n := 12)
    (lo := (105618231 / 250000000)) (hi := (16898917 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 10241) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 10241) = 1/(10241 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-388820883 / 100000000) (-486026103 / 125000000) (Real.log (10241 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (136545719 / 200000000) ≤ -Real.log (1000000 / 1979271) ∧
    -Real.log (1000000 / 1979271) ≤ (170682149 / 250000000) := by
  have h := checkLog_sound (w := (979271 / 2979271)) (n := 12)
    (lo := (136545719 / 200000000)) (hi := (170682149 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1979271 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1979271 / 1000000) = 1/(1000000 / 1979271) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (136545719 / 200000000) (170682149 / 250000000) (Real.log (1979271 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1979271 / 1000000) = -Real.log (1000000 / 1979271) := by
    rw [show ((1979271 / 1000000) : ℝ) = ((1000000 / 1979271) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (387622159 / 100000000) ≤ -Real.log (20729 / 1000000) ∧
    -Real.log (20729 / 1000000) ≤ (969055399 / 250000000) := by
  have h := checkLog_sound (w := (10521 / 51979)) (n := 12)
    (lo := (41048569 / 100000000)) (hi := (410485691 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 20729) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 20729) = 1/(20729 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-969055399 / 250000000) (-387622159 / 100000000) (Real.log (20729 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (682805893 / 1000000000) ≤ -Real.log (31250 / 61857) ∧
    -Real.log (31250 / 61857) ≤ (341402947 / 500000000) := by
  have h := checkLog_sound (w := (30607 / 93107)) (n := 12)
    (lo := (682805893 / 1000000000)) (hi := (341402947 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((61857 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(61857 / 31250) = 1/(31250 / 61857) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (682805893 / 1000000000) (341402947 / 500000000) (Real.log (61857 / 31250)) := by
  have h := reflection_log_15_neg
  have he : Real.log (61857 / 31250) = -Real.log (31250 / 61857) := by
    rw [show ((61857 / 31250) : ℝ) = ((31250 / 61857) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (485453741 / 125000000) ≤ -Real.log (643 / 31250) ∧
    -Real.log (643 / 31250) ≤ (1941814967 / 500000000) := by
  have h := checkLog_sound (w := (5337 / 25913)) (n := 12)
    (lo := (104473507 / 250000000)) (hi := (417894029 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 10288) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 10288) = 1/(643 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-1941814967 / 500000000) (-485453741 / 125000000) (Real.log (643 / 31250)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (570461201 / 125000000) ≤ -Real.log (50000000000 / 4796839860411) ∧
    -Real.log (50000000000 / 4796839860411) ≤ (912737923 / 200000000) := by
  have h := checkLog_sound (w := (1596839860411 / 7996839860411)) (n := 12)
    (lo := (3162551 / 7812500)) (hi := (404806529 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4796839860411 / 3200000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(4796839860411 / 3200000000000) = 1/(50000000000 / 4796839860411) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (570461201 / 125000000) (912737923 / 200000000) (Real.log (4796839860411 / 50000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (4796839860411 / 50000000000) = -Real.log (50000000000 / 4796839860411) := by
    rw [show ((4796839860411 / 50000000000) : ℝ) = ((50000000000 / 4796839860411) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1142765551 / 250000000) ≤ -Real.log (250000000000 / 24161678547017) ∧
    -Real.log (250000000000 / 24161678547017) ≤ (4571062211 / 1000000000) := by
  have h := checkLog_sound (w := (8161678547017 / 40161678547017)) (n := 12)
    (lo := (103044781 / 250000000)) (hi := (3297433 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24161678547017 / 16000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(24161678547017 / 16000000000000) = 1/(250000000000 / 24161678547017) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1142765551 / 250000000) (4571062211 / 1000000000) (Real.log (24161678547017 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (24161678547017 / 250000000000) = -Real.log (250000000000 / 24161678547017) := by
    rw [show ((24161678547017 / 250000000000) : ℝ) = ((250000000000 / 24161678547017) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (569868773 / 125000000) ≤ -Real.log (250000000000 / 23870796951131) ∧
    -Real.log (250000000000 / 23870796951131) ≤ (4558950191 / 1000000000) := by
  have h := checkLog_sound (w := (7870796951131 / 39870796951131)) (n := 12)
    (lo := (12502097 / 31250000)) (hi := (80013421 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((23870796951131 / 16000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(23870796951131 / 16000000000000) = 1/(250000000000 / 23870796951131) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (569868773 / 125000000) (4558950191 / 1000000000) (Real.log (23870796951131 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (23870796951131 / 250000000000) = -Real.log (250000000000 / 23870796951131) := by
    rw [show ((23870796951131 / 250000000000) : ℝ) = ((250000000000 / 23870796951131) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (228321791 / 50000000) ≤ -Real.log (500000000000 / 48100311041991) ∧
    -Real.log (500000000000 / 48100311041991) ≤ (4566435827 / 1000000000) := by
  have h := checkLog_sound (w := (16100311041991 / 80100311041991)) (n := 12)
    (lo := (20377637 / 50000000)) (hi := (407552741 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((48100311041991 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(48100311041991 / 32000000000000) = 1/(500000000000 / 48100311041991) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (228321791 / 50000000) (4566435827 / 1000000000) (Real.log (48100311041991 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (48100311041991 / 500000000000) = -Real.log (500000000000 / 48100311041991) := by
    rw [show ((48100311041991 / 500000000000) : ℝ) = ((500000000000 / 48100311041991) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0030
