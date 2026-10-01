import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0043
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

theorem reflection_log_1_neg : (679717561 / 1000000000) ≤ -Real.log (25600 / 50517) ∧
    -Real.log (25600 / 50517) ≤ (339858781 / 500000000) := by
  have h := checkLog_sound (w := (24917 / 76117)) (n := 12)
    (lo := (679717561 / 1000000000)) (hi := (339858781 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50517 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50517 / 25600) = 1/(25600 / 50517) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (679717561 / 1000000000) (339858781 / 500000000) (Real.log (50517 / 25600)) := by
  have h := reflection_log_1_neg
  have he : Real.log (50517 / 25600) = -Real.log (25600 / 50517) := by
    rw [show ((50517 / 25600) : ℝ) = ((25600 / 50517) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (113245399 / 31250000) ≤ -Real.log (683 / 25600) ∧
    -Real.log (683 / 25600) ≤ (1811926387 / 500000000) := by
  have h := checkLog_sound (w := (117 / 1483)) (n := 12)
    (lo := (39529217 / 250000000)) (hi := (158116869 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 683) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(800 / 683) = 1/(683 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-1811926387 / 500000000) (-113245399 / 31250000) (Real.log (683 / 25600)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (679623529 / 1000000000) ≤ -Real.log (102400 / 202049) ∧
    -Real.log (102400 / 202049) ≤ (67962353 / 100000000) := by
  have h := checkLog_sound (w := (99649 / 304449)) (n := 12)
    (lo := (679623529 / 1000000000)) (hi := (67962353 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((202049 / 102400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(202049 / 102400) = 1/(102400 / 202049) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (679623529 / 1000000000) (67962353 / 100000000) (Real.log (202049 / 102400)) := by
  have h := reflection_log_3_neg
  have he : Real.log (202049 / 102400) = -Real.log (102400 / 202049) := by
    rw [show ((202049 / 102400) : ℝ) = ((102400 / 202049) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (3616922227 / 1000000000) ≤ -Real.log (2751 / 102400) ∧
    -Real.log (2751 / 102400) ≤ (3616922233 / 1000000000) := by
  have h := checkLog_sound (w := (449 / 5951)) (n := 12)
    (lo := (151186327 / 1000000000)) (hi := (18898291 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2751) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3200 / 2751) = 1/(2751 / 102400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-3616922233 / 1000000000) (-3616922227 / 1000000000) (Real.log (2751 / 102400)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (66610513 / 100000000) ≤ -Real.log (12800 / 24917) ∧
    -Real.log (12800 / 24917) ≤ (666105131 / 1000000000) := by
  have h := checkLog_sound (w := (12117 / 37717)) (n := 12)
    (lo := (66610513 / 100000000)) (hi := (666105131 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24917 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24917 / 12800) = 1/(12800 / 24917) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (66610513 / 100000000) (666105131 / 1000000000) (Real.log (24917 / 12800)) := by
  have h := reflection_log_5_neg
  have he : Real.log (24917 / 12800) = -Real.log (12800 / 24917) := by
    rw [show ((24917 / 12800) : ℝ) = ((12800 / 24917) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (732676397 / 250000000) ≤ -Real.log (683 / 12800) ∧
    -Real.log (683 / 12800) ≤ (2930705593 / 1000000000) := by
  have h := checkLog_sound (w := (117 / 1483)) (n := 12)
    (lo := (39529217 / 250000000)) (hi := (158116869 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 683) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(800 / 683) = 1/(683 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-2930705593 / 1000000000) (-732676397 / 250000000) (Real.log (683 / 12800)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (665914479 / 1000000000) ≤ -Real.log (51200 / 99649) ∧
    -Real.log (51200 / 99649) ≤ (8323931 / 12500000) := by
  have h := checkLog_sound (w := (48449 / 150849)) (n := 12)
    (lo := (665914479 / 1000000000)) (hi := (8323931 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((99649 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(99649 / 51200) = 1/(51200 / 99649) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (665914479 / 1000000000) (8323931 / 12500000) (Real.log (99649 / 51200)) := by
  have h := reflection_log_7_neg
  have he : Real.log (99649 / 51200) = -Real.log (51200 / 99649) := by
    rw [show ((99649 / 51200) : ℝ) = ((51200 / 99649) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (2923775047 / 1000000000) ≤ -Real.log (2751 / 51200) ∧
    -Real.log (2751 / 51200) ≤ (730943763 / 250000000) := by
  have h := checkLog_sound (w := (449 / 5951)) (n := 12)
    (lo := (151186327 / 1000000000)) (hi := (18898291 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2751) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3200 / 2751) = 1/(2751 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-730943763 / 250000000) (-2923775047 / 1000000000) (Real.log (2751 / 51200)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (681795493 / 1000000000) ≤ -Real.log (40000 / 79097) ∧
    -Real.log (40000 / 79097) ≤ (340897747 / 500000000) := by
  have h := checkLog_sound (w := (39097 / 119097)) (n := 12)
    (lo := (681795493 / 1000000000)) (hi := (340897747 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((79097 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(79097 / 40000) = 1/(40000 / 79097) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (681795493 / 1000000000) (340897747 / 500000000) (Real.log (79097 / 40000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (79097 / 40000) = -Real.log (40000 / 79097) := by
    rw [show ((79097 / 40000) : ℝ) = ((40000 / 79097) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (236932011 / 62500000) ≤ -Real.log (903 / 40000) ∧
    -Real.log (903 / 40000) ≤ (1895456091 / 500000000) := by
  have h := checkLog_sound (w := (347 / 2153)) (n := 12)
    (lo := (81294069 / 250000000)) (hi := (325176277 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250 / 903) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(1250 / 903) = 1/(903 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-1895456091 / 500000000) (-236932011 / 62500000) (Real.log (903 / 40000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (340935673 / 500000000) ≤ -Real.log (40000 / 79103) ∧
    -Real.log (40000 / 79103) ≤ (681871347 / 1000000000) := by
  have h := checkLog_sound (w := (39103 / 119103)) (n := 12)
    (lo := (340935673 / 500000000)) (hi := (681871347 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((79103 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(79103 / 40000) = 1/(40000 / 79103) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (340935673 / 500000000) (681871347 / 1000000000) (Real.log (79103 / 40000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (79103 / 40000) = -Real.log (40000 / 79103) := by
    rw [show ((79103 / 40000) : ℝ) = ((40000 / 79103) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (949394717 / 250000000) ≤ -Real.log (897 / 40000) ∧
    -Real.log (897 / 40000) ≤ (1898789437 / 500000000) := by
  have h := checkLog_sound (w := (353 / 2147)) (n := 12)
    (lo := (41480371 / 125000000)) (hi := (331842969 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250 / 897) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(1250 / 897) = 1/(897 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1898789437 / 500000000) (-949394717 / 250000000) (Real.log (897 / 40000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (681735817 / 1000000000) ≤ -Real.log (1000000 / 1977307) ∧
    -Real.log (1000000 / 1977307) ≤ (340867909 / 500000000) := by
  have h := checkLog_sound (w := (977307 / 2977307)) (n := 12)
    (lo := (681735817 / 1000000000)) (hi := (340867909 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1977307 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1977307 / 1000000) = 1/(1000000 / 1977307) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (681735817 / 1000000000) (340867909 / 500000000) (Real.log (1977307 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1977307 / 1000000) = -Real.log (1000000 / 1977307) := by
    rw [show ((1977307 / 1000000) : ℝ) = ((1000000 / 1977307) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (3785698769 / 1000000000) ≤ -Real.log (22693 / 1000000) ∧
    -Real.log (22693 / 1000000) ≤ (151427951 / 40000000) := by
  have h := checkLog_sound (w := (8557 / 53943)) (n := 12)
    (lo := (319962869 / 1000000000)) (hi := (31996287 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 22693) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 22693) = 1/(22693 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-151427951 / 40000000) (-3785698769 / 1000000000) (Real.log (22693 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (681812687 / 1000000000) ≤ -Real.log (1000000 / 1977459) ∧
    -Real.log (1000000 / 1977459) ≤ (42613293 / 62500000) := by
  have h := checkLog_sound (w := (977459 / 2977459)) (n := 12)
    (lo := (681812687 / 1000000000)) (hi := (42613293 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1977459 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1977459 / 1000000) = 1/(1000000 / 1977459) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (681812687 / 1000000000) (42613293 / 62500000) (Real.log (1977459 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1977459 / 1000000) = -Real.log (1000000 / 1977459) := by
    rw [show ((1977459 / 1000000) : ℝ) = ((1000000 / 1977459) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (1896209701 / 500000000) ≤ -Real.log (22541 / 1000000) ∧
    -Real.log (22541 / 1000000) ≤ (237026213 / 62500000) := by
  have h := checkLog_sound (w := (8709 / 53791)) (n := 12)
    (lo := (163341751 / 500000000)) (hi := (326683503 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 22541) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 22541) = 1/(22541 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-237026213 / 62500000) (-1896209701 / 500000000) (Real.log (22541 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (4472707669 / 1000000000) ≤ -Real.log (250000000000 / 21898394241417) ∧
    -Real.log (250000000000 / 21898394241417) ≤ (1118176919 / 250000000) := by
  have h := checkLog_sound (w := (5898394241417 / 37898394241417)) (n := 12)
    (lo := (313824589 / 1000000000)) (hi := (31382459 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((21898394241417 / 16000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(21898394241417 / 16000000000000) = 1/(250000000000 / 21898394241417) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (4472707669 / 1000000000) (1118176919 / 250000000) (Real.log (21898394241417 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (21898394241417 / 250000000000) = -Real.log (250000000000 / 21898394241417) := by
    rw [show ((21898394241417 / 250000000000) : ℝ) = ((250000000000 / 21898394241417) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (2239725107 / 500000000) ≤ -Real.log (500000000000 / 44093088071349) ∧
    -Real.log (500000000000 / 44093088071349) ≤ (4479450221 / 1000000000) := by
  have h := checkLog_sound (w := (12093088071349 / 76093088071349)) (n := 12)
    (lo := (160283567 / 500000000)) (hi := (64113427 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((44093088071349 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(44093088071349 / 32000000000000) = 1/(500000000000 / 44093088071349) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (2239725107 / 500000000) (4479450221 / 1000000000) (Real.log (44093088071349 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (44093088071349 / 500000000000) = -Real.log (500000000000 / 44093088071349) := by
    rw [show ((44093088071349 / 500000000000) : ℝ) = ((500000000000 / 44093088071349) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (2233717293 / 500000000) ≤ -Real.log (125000000000 / 10891613052483) ∧
    -Real.log (125000000000 / 10891613052483) ≤ (4467434593 / 1000000000) := by
  have h := checkLog_sound (w := (2891613052483 / 18891613052483)) (n := 12)
    (lo := (154275753 / 500000000)) (hi := (308551507 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10891613052483 / 8000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(10891613052483 / 8000000000000) = 1/(125000000000 / 10891613052483) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (2233717293 / 500000000) (4467434593 / 1000000000) (Real.log (10891613052483 / 125000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (10891613052483 / 125000000000) = -Real.log (125000000000 / 10891613052483) := by
    rw [show ((10891613052483 / 125000000000) : ℝ) = ((125000000000 / 10891613052483) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (4474232089 / 1000000000) ≤ -Real.log (250000000000 / 21931802049599) ∧
    -Real.log (250000000000 / 21931802049599) ≤ (139819753 / 31250000) := by
  have h := checkLog_sound (w := (5931802049599 / 37931802049599)) (n := 12)
    (lo := (315349009 / 1000000000)) (hi := (31534901 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((21931802049599 / 16000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(21931802049599 / 16000000000000) = 1/(250000000000 / 21931802049599) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (4474232089 / 1000000000) (139819753 / 31250000) (Real.log (21931802049599 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (21931802049599 / 250000000000) = -Real.log (250000000000 / 21931802049599) := by
    rw [show ((21931802049599 / 250000000000) : ℝ) = ((250000000000 / 21931802049599) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0043
