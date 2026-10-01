import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0121
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

theorem reflection_log_1_neg : (665703717 / 1000000000) ≤ -Real.log (12800 / 24907) ∧
    -Real.log (12800 / 24907) ≤ (332851859 / 500000000) := by
  have h := checkLog_sound (w := (12107 / 37707)) (n := 12)
    (lo := (665703717 / 1000000000)) (hi := (332851859 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24907 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24907 / 12800) = 1/(12800 / 24907) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (665703717 / 1000000000) (332851859 / 500000000) (Real.log (24907 / 12800)) := by
  have h := reflection_log_1_neg
  have he : Real.log (24907 / 12800) = -Real.log (12800 / 24907) := by
    rw [show ((24907 / 12800) : ℝ) = ((12800 / 24907) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (182260653 / 62500000) ≤ -Real.log (693 / 12800) ∧
    -Real.log (693 / 12800) ≤ (2916170453 / 1000000000) := by
  have h := checkLog_sound (w := (107 / 1493)) (n := 12)
    (lo := (4486929 / 31250000)) (hi := (143581729 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 693) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(800 / 693) = 1/(693 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-2916170453 / 1000000000) (-182260653 / 62500000) (Real.log (693 / 12800)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (26612889 / 40000000) ≤ -Real.log (5120 / 9959) ∧
    -Real.log (5120 / 9959) ≤ (332661113 / 500000000) := by
  have h := checkLog_sound (w := (4839 / 15079)) (n := 12)
    (lo := (26612889 / 40000000)) (hi := (332661113 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9959 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(9959 / 5120) = 1/(5120 / 9959) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (26612889 / 40000000) (332661113 / 500000000) (Real.log (9959 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (9959 / 5120) = -Real.log (5120 / 9959) := by
    rw [show ((9959 / 5120) : ℝ) = ((5120 / 9959) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (1451277523 / 500000000) ≤ -Real.log (281 / 5120) ∧
    -Real.log (281 / 5120) ≤ (2902555051 / 1000000000) := by
  have h := checkLog_sound (w := (39 / 601)) (n := 12)
    (lo := (64983163 / 500000000)) (hi := (129966327 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 281) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(320 / 281) = 1/(281 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-2902555051 / 1000000000) (-1451277523 / 500000000) (Real.log (281 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (637485807 / 1000000000) ≤ -Real.log (6400 / 12107) ∧
    -Real.log (6400 / 12107) ≤ (39842863 / 62500000) := by
  have h := checkLog_sound (w := (5707 / 18507)) (n := 12)
    (lo := (637485807 / 1000000000)) (hi := (39842863 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12107 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12107 / 6400) = 1/(6400 / 12107) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (637485807 / 1000000000) (39842863 / 62500000) (Real.log (12107 / 6400)) := by
  have h := reflection_log_5_neg
  have he : Real.log (12107 / 6400) = -Real.log (6400 / 12107) := by
    rw [show ((12107 / 6400) : ℝ) = ((6400 / 12107) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (555755817 / 250000000) ≤ -Real.log (693 / 6400) ∧
    -Real.log (693 / 6400) ≤ (277877909 / 125000000) := by
  have h := checkLog_sound (w := (107 / 1493)) (n := 12)
    (lo := (4486929 / 31250000)) (hi := (143581729 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 693) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(800 / 693) = 1/(693 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-277877909 / 125000000) (-555755817 / 250000000) (Real.log (693 / 6400)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (636700829 / 1000000000) ≤ -Real.log (2560 / 4839) ∧
    -Real.log (2560 / 4839) ≤ (63670083 / 100000000) := by
  have h := checkLog_sound (w := (2279 / 7399)) (n := 12)
    (lo := (636700829 / 1000000000)) (hi := (63670083 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4839 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4839 / 2560) = 1/(2560 / 4839) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (636700829 / 1000000000) (63670083 / 100000000) (Real.log (4839 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (4839 / 2560) = -Real.log (2560 / 4839) := by
    rw [show ((4839 / 2560) : ℝ) = ((2560 / 4839) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (1104703933 / 500000000) ≤ -Real.log (281 / 2560) ∧
    -Real.log (281 / 2560) ≤ (220940787 / 100000000) := by
  have h := checkLog_sound (w := (39 / 601)) (n := 12)
    (lo := (64983163 / 500000000)) (hi := (129966327 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 281) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(320 / 281) = 1/(281 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-220940787 / 100000000) (-1104703933 / 500000000) (Real.log (281 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (670739493 / 1000000000) ≤ -Real.log (1000000 / 1955683) ∧
    -Real.log (1000000 / 1955683) ≤ (335369747 / 500000000) := by
  have h := checkLog_sound (w := (955683 / 2955683)) (n := 12)
    (lo := (670739493 / 1000000000)) (hi := (335369747 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1955683 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1955683 / 1000000) = 1/(1000000 / 1955683) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (670739493 / 1000000000) (335369747 / 500000000) (Real.log (1955683 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1955683 / 1000000) = -Real.log (1000000 / 1955683) := by
    rw [show ((1955683 / 1000000) : ℝ) = ((1000000 / 1955683) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (1558193463 / 500000000) ≤ -Real.log (44317 / 1000000) ∧
    -Real.log (44317 / 1000000) ≤ (3116386931 / 1000000000) := by
  have h := checkLog_sound (w := (18183 / 106817)) (n := 12)
    (lo := (171899103 / 500000000)) (hi := (343798207 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 44317) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 44317) = 1/(44317 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-3116386931 / 1000000000) (-1558193463 / 500000000) (Real.log (44317 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (134205057 / 200000000) ≤ -Real.log (500000 / 978121) ∧
    -Real.log (500000 / 978121) ≤ (335512643 / 500000000) := by
  have h := checkLog_sound (w := (478121 / 1478121)) (n := 12)
    (lo := (134205057 / 200000000)) (hi := (335512643 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((978121 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(978121 / 500000) = 1/(500000 / 978121) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (134205057 / 200000000) (335512643 / 500000000) (Real.log (978121 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (978121 / 500000) = -Real.log (500000 / 978121) := by
    rw [show ((978121 / 500000) : ℝ) = ((500000 / 978121) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (3129080823 / 1000000000) ≤ -Real.log (21879 / 500000) ∧
    -Real.log (21879 / 500000) ≤ (782270207 / 250000000) := by
  have h := checkLog_sound (w := (9371 / 53129)) (n := 12)
    (lo := (356492103 / 1000000000)) (hi := (44561513 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 21879) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(31250 / 21879) = 1/(21879 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-782270207 / 250000000) (-3129080823 / 1000000000) (Real.log (21879 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (167608929 / 250000000) ≤ -Real.log (1000000 / 1955089) ∧
    -Real.log (1000000 / 1955089) ≤ (670435717 / 1000000000) := by
  have h := checkLog_sound (w := (955089 / 2955089)) (n := 12)
    (lo := (167608929 / 250000000)) (hi := (670435717 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1955089 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1955089 / 1000000) = 1/(1000000 / 1955089) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (167608929 / 250000000) (670435717 / 1000000000) (Real.log (1955089 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1955089 / 1000000) = -Real.log (1000000 / 1955089) := by
    rw [show ((1955089 / 1000000) : ℝ) = ((1000000 / 1955089) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (3103072523 / 1000000000) ≤ -Real.log (44911 / 1000000) ∧
    -Real.log (44911 / 1000000) ≤ (193942033 / 62500000) := by
  have h := checkLog_sound (w := (17589 / 107411)) (n := 12)
    (lo := (330483803 / 1000000000)) (hi := (82620951 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 44911) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 44911) = 1/(44911 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-193942033 / 62500000) (-3103072523 / 1000000000) (Real.log (44911 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (1676827 / 2500000) ≤ -Real.log (500000 / 977833) ∧
    -Real.log (500000 / 977833) ≤ (670730801 / 1000000000) := by
  have h := checkLog_sound (w := (477833 / 1477833)) (n := 12)
    (lo := (1676827 / 2500000)) (hi := (670730801 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((977833 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(977833 / 500000) = 1/(500000 / 977833) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (1676827 / 2500000) (670730801 / 1000000000) (Real.log (977833 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (977833 / 500000) = -Real.log (500000 / 977833) := by
    rw [show ((977833 / 500000) : ℝ) = ((500000 / 977833) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (3116003399 / 1000000000) ≤ -Real.log (22167 / 500000) ∧
    -Real.log (22167 / 500000) ≤ (779000851 / 250000000) := by
  have h := checkLog_sound (w := (9083 / 53417)) (n := 12)
    (lo := (343414679 / 1000000000)) (hi := (8585367 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 22167) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(31250 / 22167) = 1/(22167 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-779000851 / 250000000) (-3116003399 / 1000000000) (Real.log (22167 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1893563209 / 500000000) ≤ -Real.log (10000000000 / 441294085791) ∧
    -Real.log (10000000000 / 441294085791) ≤ (473390803 / 125000000) := by
  have h := checkLog_sound (w := (121294085791 / 761294085791)) (n := 12)
    (lo := (160695259 / 500000000)) (hi := (321390519 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((441294085791 / 320000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(441294085791 / 320000000000) = 1/(10000000000 / 441294085791) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1893563209 / 500000000) (473390803 / 125000000) (Real.log (441294085791 / 10000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (441294085791 / 10000000000) = -Real.log (10000000000 / 441294085791) := by
    rw [show ((441294085791 / 10000000000) : ℝ) = ((10000000000 / 441294085791) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (950026527 / 250000000) ≤ -Real.log (100000000000 / 4470592805887) ∧
    -Real.log (100000000000 / 4470592805887) ≤ (1900053057 / 500000000) := by
  have h := checkLog_sound (w := (1270592805887 / 7670592805887)) (n := 12)
    (lo := (10449069 / 31250000)) (hi := (334370209 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4470592805887 / 3200000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(4470592805887 / 3200000000000) = 1/(100000000000 / 4470592805887) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (950026527 / 250000000) (1900053057 / 500000000) (Real.log (4470592805887 / 100000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (4470592805887 / 100000000000) = -Real.log (100000000000 / 4470592805887) := by
    rw [show ((4470592805887 / 100000000000) : ℝ) = ((100000000000 / 4470592805887) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (3773508239 / 1000000000) ≤ -Real.log (250000000000 / 10883129968159) ∧
    -Real.log (250000000000 / 10883129968159) ≤ (754701649 / 200000000) := by
  have h := checkLog_sound (w := (2883129968159 / 18883129968159)) (n := 12)
    (lo := (307772339 / 1000000000)) (hi := (15388617 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10883129968159 / 8000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(10883129968159 / 8000000000000) = 1/(250000000000 / 10883129968159) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (3773508239 / 1000000000) (754701649 / 200000000) (Real.log (10883129968159 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (10883129968159 / 250000000000) = -Real.log (250000000000 / 10883129968159) := by
    rw [show ((10883129968159 / 250000000000) : ℝ) = ((250000000000 / 10883129968159) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (3786734199 / 1000000000) ≤ -Real.log (100000000000 / 4411210357739) ∧
    -Real.log (100000000000 / 4411210357739) ≤ (757346841 / 200000000) := by
  have h := checkLog_sound (w := (1211210357739 / 7611210357739)) (n := 12)
    (lo := (320998299 / 1000000000)) (hi := (3209983 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4411210357739 / 3200000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(4411210357739 / 3200000000000) = 1/(100000000000 / 4411210357739) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (3786734199 / 1000000000) (757346841 / 200000000) (Real.log (4411210357739 / 100000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (4411210357739 / 100000000000) = -Real.log (100000000000 / 4411210357739) := by
    rw [show ((4411210357739 / 100000000000) : ℝ) = ((100000000000 / 4411210357739) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0121
