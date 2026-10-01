import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0029
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

theorem reflection_log_1_neg : (170258271 / 250000000) ≤ -Real.log (51200 / 101167) ∧
    -Real.log (51200 / 101167) ≤ (136206617 / 200000000) := by
  have h := checkLog_sound (w := (49967 / 152367)) (n := 12)
    (lo := (170258271 / 250000000)) (hi := (136206617 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((101167 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(101167 / 51200) = 1/(51200 / 101167) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (170258271 / 250000000) (136206617 / 200000000) (Real.log (101167 / 51200)) := by
  have h := reflection_log_1_neg
  have he : Real.log (101167 / 51200) = -Real.log (51200 / 101167) := by
    rw [show ((101167 / 51200) : ℝ) = ((51200 / 101167) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (745257861 / 200000000) ≤ -Real.log (1233 / 51200) ∧
    -Real.log (1233 / 51200) ≤ (3726289311 / 1000000000) := by
  have h := checkLog_sound (w := (367 / 2833)) (n := 12)
    (lo := (52110681 / 200000000)) (hi := (130276703 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1233) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(1600 / 1233) = 1/(1233 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-3726289311 / 1000000000) (-745257861 / 200000000) (Real.log (1233 / 51200)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (85117397 / 125000000) ≤ -Real.log (20480 / 40463) ∧
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


theorem reflection_log_3 : Bounds (85117397 / 125000000) (680939177 / 1000000000) (Real.log (40463 / 20480)) := by
  have h := reflection_log_3_neg
  have he : Real.log (40463 / 20480) = -Real.log (20480 / 40463) := by
    rw [show ((40463 / 20480) : ℝ) = ((20480 / 40463) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (74372281 / 20000000) ≤ -Real.log (497 / 20480) ∧
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


theorem reflection_log_4 : Bounds (-464826757 / 125000000) (-74372281 / 20000000) (Real.log (497 / 20480)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (167192609 / 250000000) ≤ -Real.log (25600 / 49967) ∧
    -Real.log (25600 / 49967) ≤ (668770437 / 1000000000) := by
  have h := checkLog_sound (w := (24367 / 75567)) (n := 12)
    (lo := (167192609 / 250000000)) (hi := (668770437 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49967 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49967 / 25600) = 1/(25600 / 49967) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (167192609 / 250000000) (668770437 / 1000000000) (Real.log (49967 / 25600)) := by
  have h := reflection_log_5_neg
  have he : Real.log (49967 / 25600) = -Real.log (25600 / 49967) := by
    rw [show ((49967 / 25600) : ℝ) = ((25600 / 49967) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (24265137 / 8000000) ≤ -Real.log (1233 / 25600) ∧
    -Real.log (1233 / 25600) ≤ (303314213 / 100000000) := by
  have h := checkLog_sound (w := (367 / 2833)) (n := 12)
    (lo := (52110681 / 200000000)) (hi := (130276703 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1233) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1600 / 1233) = 1/(1233 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-303314213 / 100000000) (-24265137 / 8000000) (Real.log (1233 / 25600)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (167145073 / 250000000) ≤ -Real.log (10240 / 19983) ∧
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


theorem reflection_log_7 : Bounds (167145073 / 250000000) (668580293 / 1000000000) (Real.log (19983 / 10240)) := by
  have h := reflection_log_7_neg
  have he : Real.log (19983 / 10240) = -Real.log (10240 / 19983) := by
    rw [show ((19983 / 10240) : ℝ) = ((10240 / 19983) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (302546687 / 100000000) ≤ -Real.log (497 / 10240) ∧
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


theorem reflection_log_8 : Bounds (-4840747 / 1600000) (-302546687 / 100000000) (Real.log (497 / 10240)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (5462823 / 8000000) ≤ -Real.log (1000000 / 1979517) ∧
    -Real.log (1000000 / 1979517) ≤ (170713219 / 250000000) := by
  have h := checkLog_sound (w := (979517 / 2979517)) (n := 12)
    (lo := (5462823 / 8000000)) (hi := (170713219 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1979517 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1979517 / 1000000) = 1/(1000000 / 1979517) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (5462823 / 8000000) (170713219 / 250000000) (Real.log (1979517 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1979517 / 1000000) = -Real.log (1000000 / 1979517) := by
    rw [show ((1979517 / 1000000) : ℝ) = ((1000000 / 1979517) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (1944080001 / 500000000) ≤ -Real.log (20483 / 1000000) ∧
    -Real.log (20483 / 1000000) ≤ (486020001 / 125000000) := by
  have h := checkLog_sound (w := (10767 / 51733)) (n := 12)
    (lo := (211212051 / 500000000)) (hi := (422424103 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 20483) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 20483) = 1/(20483 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-486020001 / 125000000) (-1944080001 / 500000000) (Real.log (20483 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (682929153 / 1000000000) ≤ -Real.log (250000 / 494917) ∧
    -Real.log (250000 / 494917) ≤ (341464577 / 500000000) := by
  have h := checkLog_sound (w := (244917 / 744917)) (n := 12)
    (lo := (682929153 / 1000000000)) (hi := (341464577 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((494917 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(494917 / 250000) = 1/(250000 / 494917) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (682929153 / 1000000000) (341464577 / 500000000) (Real.log (494917 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (494917 / 250000) = -Real.log (250000 / 494917) := by
    rw [show ((494917 / 250000) : ℝ) = ((250000 / 494917) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (973889819 / 250000000) ≤ -Real.log (5083 / 250000) ∧
    -Real.log (5083 / 250000) ≤ (1947779641 / 500000000) := by
  have h := checkLog_sound (w := (5459 / 25791)) (n := 12)
    (lo := (26863961 / 62500000)) (hi := (429823377 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 10166) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 10166) = 1/(5083 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1947779641 / 500000000) (-973889819 / 250000000) (Real.log (5083 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (170701347 / 250000000) ≤ -Real.log (1000000 / 1979423) ∧
    -Real.log (1000000 / 1979423) ≤ (682805389 / 1000000000) := by
  have h := checkLog_sound (w := (979423 / 2979423)) (n := 12)
    (lo := (170701347 / 250000000)) (hi := (682805389 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1979423 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1979423 / 1000000) = 1/(1000000 / 1979423) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (170701347 / 250000000) (682805389 / 1000000000) (Real.log (1979423 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1979423 / 1000000) = -Real.log (1000000 / 1979423) := by
    rw [show ((1979423 / 1000000) : ℝ) = ((1000000 / 1979423) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (242723833 / 62500000) ≤ -Real.log (20577 / 1000000) ∧
    -Real.log (20577 / 1000000) ≤ (1941790667 / 500000000) := by
  have h := checkLog_sound (w := (10673 / 51827)) (n := 12)
    (lo := (104461357 / 250000000)) (hi := (417845429 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 20577) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 20577) = 1/(20577 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-1941790667 / 500000000) (-242723833 / 62500000) (Real.log (20577 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (27315287 / 40000000) ≤ -Real.log (40000 / 79183) ∧
    -Real.log (40000 / 79183) ≤ (5335017 / 7812500) := by
  have h := checkLog_sound (w := (39183 / 119183)) (n := 12)
    (lo := (27315287 / 40000000)) (hi := (5335017 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((79183 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(79183 / 40000) = 1/(40000 / 79183) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (27315287 / 40000000) (5335017 / 7812500) (Real.log (79183 / 40000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (79183 / 40000) = -Real.log (40000 / 79183) := by
    rw [show ((79183 / 40000) : ℝ) = ((40000 / 79183) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (778199127 / 200000000) ≤ -Real.log (817 / 40000) ∧
    -Real.log (817 / 40000) ≤ (3890995641 / 1000000000) := by
  have h := checkLog_sound (w := (433 / 2067)) (n := 12)
    (lo := (85051947 / 200000000)) (hi := (53157467 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250 / 817) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(1250 / 817) = 1/(817 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-3890995641 / 1000000000) (-778199127 / 200000000) (Real.log (817 / 40000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (4571012877 / 1000000000) ≤ -Real.log (500000000000 / 48320973490211) ∧
    -Real.log (500000000000 / 48320973490211) ≤ (1142753221 / 250000000) := by
  have h := checkLog_sound (w := (16320973490211 / 80320973490211)) (n := 12)
    (lo := (412129797 / 1000000000)) (hi := (206064899 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((48320973490211 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(48320973490211 / 32000000000000) = 1/(500000000000 / 48320973490211) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (4571012877 / 1000000000) (1142753221 / 250000000) (Real.log (48320973490211 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (48320973490211 / 500000000000) = -Real.log (500000000000 / 48320973490211) := by
    rw [show ((48320973490211 / 500000000000) : ℝ) = ((500000000000 / 48320973490211) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (4578488429 / 1000000000) ≤ -Real.log (500000000000 / 48683553019871) ∧
    -Real.log (500000000000 / 48683553019871) ≤ (1144622109 / 250000000) := by
  have h := checkLog_sound (w := (16683553019871 / 80683553019871)) (n := 12)
    (lo := (419605349 / 1000000000)) (hi := (8392107 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((48683553019871 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(48683553019871 / 32000000000000) = 1/(500000000000 / 48683553019871) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (4578488429 / 1000000000) (1144622109 / 250000000) (Real.log (48683553019871 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (48683553019871 / 500000000000) = -Real.log (500000000000 / 48683553019871) := by
    rw [show ((48683553019871 / 500000000000) : ℝ) = ((500000000000 / 48683553019871) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1141596679 / 250000000) ≤ -Real.log (100000000000 / 9619589833309) ∧
    -Real.log (100000000000 / 9619589833309) ≤ (4566386723 / 1000000000) := by
  have h := checkLog_sound (w := (3219589833309 / 16019589833309)) (n := 12)
    (lo := (101875909 / 250000000)) (hi := (407503637 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9619589833309 / 6400000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(9619589833309 / 6400000000000) = 1/(100000000000 / 9619589833309) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (1141596679 / 250000000) (4566386723 / 1000000000) (Real.log (9619589833309 / 100000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (9619589833309 / 100000000000) = -Real.log (100000000000 / 9619589833309) := by
    rw [show ((9619589833309 / 100000000000) : ℝ) = ((100000000000 / 9619589833309) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (457387781 / 100000000) ≤ -Real.log (250000000000 / 24229804161567) ∧
    -Real.log (250000000000 / 24229804161567) ≤ (4573877817 / 1000000000) := by
  have h := checkLog_sound (w := (8229804161567 / 40229804161567)) (n := 12)
    (lo := (41499473 / 100000000)) (hi := (414994731 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24229804161567 / 16000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(24229804161567 / 16000000000000) = 1/(250000000000 / 24229804161567) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (457387781 / 100000000) (4573877817 / 1000000000) (Real.log (24229804161567 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (24229804161567 / 250000000000) = -Real.log (250000000000 / 24229804161567) := by
    rw [show ((24229804161567 / 250000000000) : ℝ) = ((250000000000 / 24229804161567) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0029
