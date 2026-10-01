import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0196
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

theorem reflection_log_1_neg : (53491887 / 200000000) ≤ -Real.log (512 / 669) ∧
    -Real.log (512 / 669) ≤ (66864859 / 250000000) := by
  have h := checkLog_sound (w := (157 / 1181)) (n := 12)
    (lo := (53491887 / 200000000)) (hi := (66864859 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((669 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(669 / 512) = 1/(512 / 669) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (53491887 / 200000000) (66864859 / 250000000) (Real.log (669 / 512)) := by
  have h := reflection_log_1_neg
  have he : Real.log (669 / 512) = -Real.log (512 / 669) := by
    rw [show ((669 / 512) : ℝ) = ((512 / 669) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (73241367 / 200000000) ≤ -Real.log (355 / 512) ∧
    -Real.log (355 / 512) ≤ (91551709 / 250000000) := by
  have h := checkLog_sound (w := (157 / 867)) (n := 12)
    (lo := (73241367 / 200000000)) (hi := (91551709 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 355) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 355) = 1/(355 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-91551709 / 250000000) (-73241367 / 200000000) (Real.log (355 / 512)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (33376363 / 125000000) ≤ -Real.log (5120 / 6687) ∧
    -Real.log (5120 / 6687) ≤ (53402181 / 200000000) := by
  have h := checkLog_sound (w := (1567 / 11807)) (n := 12)
    (lo := (33376363 / 125000000)) (hi := (53402181 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6687 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6687 / 5120) = 1/(5120 / 6687) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (33376363 / 125000000) (53402181 / 200000000) (Real.log (6687 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6687 / 5120) = -Real.log (5120 / 6687) := by
    rw [show ((6687 / 5120) : ℝ) = ((5120 / 6687) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (182681061 / 500000000) ≤ -Real.log (3553 / 5120) ∧
    -Real.log (3553 / 5120) ≤ (365362123 / 1000000000) := by
  have h := checkLog_sound (w := (1567 / 8673)) (n := 12)
    (lo := (182681061 / 500000000)) (hi := (365362123 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3553) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3553) = 1/(3553 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-365362123 / 1000000000) (-182681061 / 500000000) (Real.log (3553 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (119567537 / 250000000) ≤ -Real.log (256 / 413) ∧
    -Real.log (256 / 413) ≤ (478270149 / 1000000000) := by
  have h := checkLog_sound (w := (157 / 669)) (n := 12)
    (lo := (119567537 / 250000000)) (hi := (478270149 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((413 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(413 / 256) = 1/(256 / 413) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (119567537 / 250000000) (478270149 / 1000000000) (Real.log (413 / 256)) := by
  have h := reflection_log_5_neg
  have he : Real.log (413 / 256) = -Real.log (256 / 413) := by
    rw [show ((413 / 256) : ℝ) = ((256 / 413) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (950057593 / 1000000000) ≤ -Real.log (99 / 256) ∧
    -Real.log (99 / 256) ≤ (190011519 / 200000000) := by
  have h := checkLog_sound (w := (29 / 227)) (n := 12)
    (lo := (256910413 / 1000000000)) (hi := (128455207 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((128 / 99) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(128 / 99) = 1/(99 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-190011519 / 200000000) (-950057593 / 1000000000) (Real.log (99 / 256)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (119385873 / 250000000) ≤ -Real.log (2560 / 4127) ∧
    -Real.log (2560 / 4127) ≤ (477543493 / 1000000000) := by
  have h := checkLog_sound (w := (1567 / 6687)) (n := 12)
    (lo := (119385873 / 250000000)) (hi := (477543493 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4127 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4127 / 2560) = 1/(2560 / 4127) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (119385873 / 250000000) (477543493 / 1000000000) (Real.log (4127 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (4127 / 2560) = -Real.log (2560 / 4127) := by
    rw [show ((4127 / 2560) : ℝ) = ((2560 / 4127) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (14797373 / 15625000) ≤ -Real.log (993 / 2560) ∧
    -Real.log (993 / 2560) ≤ (473515937 / 500000000) := by
  have h := checkLog_sound (w := (287 / 2273)) (n := 12)
    (lo := (63471173 / 250000000)) (hi := (253884693 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 993) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 993) = 1/(993 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-473515937 / 500000000) (-14797373 / 15625000) (Real.log (993 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (45659791 / 125000000) ≤ -Real.log (200000 / 288183) ∧
    -Real.log (200000 / 288183) ≤ (365278329 / 1000000000) := by
  have h := checkLog_sound (w := (88183 / 488183)) (n := 12)
    (lo := (45659791 / 125000000)) (hi := (365278329 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((288183 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(288183 / 200000) = 1/(200000 / 288183) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (45659791 / 125000000) (365278329 / 1000000000) (Real.log (288183 / 200000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (288183 / 200000) = -Real.log (200000 / 288183) := by
    rw [show ((288183 / 200000) : ℝ) = ((200000 / 288183) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (1817043 / 3125000) ≤ -Real.log (111817 / 200000) ∧
    -Real.log (111817 / 200000) ≤ (581453761 / 1000000000) := by
  have h := checkLog_sound (w := (88183 / 311817)) (n := 12)
    (lo := (1817043 / 3125000)) (hi := (581453761 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 111817) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 111817) = 1/(111817 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-581453761 / 1000000000) (-1817043 / 3125000) (Real.log (111817 / 200000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (73178189 / 200000000) ≤ -Real.log (500000 / 720899) ∧
    -Real.log (500000 / 720899) ≤ (182945473 / 500000000) := by
  have h := checkLog_sound (w := (220899 / 1220899)) (n := 12)
    (lo := (73178189 / 200000000)) (hi := (182945473 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((720899 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(720899 / 500000) = 1/(500000 / 720899) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (73178189 / 200000000) (182945473 / 500000000) (Real.log (720899 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (720899 / 500000) = -Real.log (500000 / 720899) := by
    rw [show ((720899 / 500000) : ℝ) = ((500000 / 720899) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (291517187 / 500000000) ≤ -Real.log (279101 / 500000) ∧
    -Real.log (279101 / 500000) ≤ (186571 / 320000) := by
  have h := checkLog_sound (w := (220899 / 779101)) (n := 12)
    (lo := (291517187 / 500000000)) (hi := (186571 / 320000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 279101) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 279101) = 1/(279101 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-186571 / 320000) (-291517187 / 500000000) (Real.log (279101 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (284777357 / 1000000000) ≤ -Real.log (500000 / 664733) ∧
    -Real.log (500000 / 664733) ≤ (142388679 / 500000000) := by
  have h := checkLog_sound (w := (164733 / 1164733)) (n := 12)
    (lo := (284777357 / 1000000000)) (hi := (142388679 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((664733 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(664733 / 500000) = 1/(500000 / 664733) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (284777357 / 1000000000) (142388679 / 500000000) (Real.log (664733 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (664733 / 500000) = -Real.log (500000 / 664733) := by
    rw [show ((664733 / 500000) : ℝ) = ((500000 / 664733) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (399680869 / 1000000000) ≤ -Real.log (335267 / 500000) ∧
    -Real.log (335267 / 500000) ≤ (39968087 / 100000000) := by
  have h := checkLog_sound (w := (164733 / 835267)) (n := 12)
    (lo := (399680869 / 1000000000)) (hi := (39968087 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 335267) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 335267) = 1/(335267 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-39968087 / 100000000) (-399680869 / 1000000000) (Real.log (335267 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (142665029 / 500000000) ≤ -Real.log (1000000 / 1330201) ∧
    -Real.log (1000000 / 1330201) ≤ (285330059 / 1000000000) := by
  have h := checkLog_sound (w := (330201 / 2330201)) (n := 12)
    (lo := (142665029 / 500000000)) (hi := (285330059 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1330201 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1330201 / 1000000) = 1/(1000000 / 1330201) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (142665029 / 500000000) (285330059 / 1000000000) (Real.log (1330201 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1330201 / 1000000) = -Real.log (1000000 / 1330201) := by
    rw [show ((1330201 / 1000000) : ℝ) = ((1000000 / 1330201) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (400777611 / 1000000000) ≤ -Real.log (669799 / 1000000) ∧
    -Real.log (669799 / 1000000) ≤ (100194403 / 250000000) := by
  have h := checkLog_sound (w := (330201 / 1669799)) (n := 12)
    (lo := (400777611 / 1000000000)) (hi := (100194403 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 669799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 669799) = 1/(669799 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-100194403 / 250000000) (-400777611 / 1000000000) (Real.log (669799 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (118341511 / 125000000) ≤ -Real.log (50000000000 / 128863679047) ∧
    -Real.log (50000000000 / 128863679047) ≤ (94673209 / 100000000) := by
  have h := checkLog_sound (w := (28863679047 / 228863679047)) (n := 12)
    (lo := (63396227 / 250000000)) (hi := (253584909 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((128863679047 / 100000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(128863679047 / 100000000000) = 1/(50000000000 / 128863679047) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (118341511 / 125000000) (94673209 / 100000000) (Real.log (128863679047 / 50000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (128863679047 / 50000000000) = -Real.log (50000000000 / 128863679047) := by
    rw [show ((128863679047 / 50000000000) : ℝ) = ((50000000000 / 128863679047) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (23723133 / 25000000) ≤ -Real.log (100000000000 / 258293234349) ∧
    -Real.log (100000000000 / 258293234349) ≤ (474462661 / 500000000) := by
  have h := checkLog_sound (w := (58293234349 / 458293234349)) (n := 12)
    (lo := (12788907 / 50000000)) (hi := (255778141 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((258293234349 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(258293234349 / 200000000000) = 1/(100000000000 / 258293234349) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (23723133 / 25000000) (474462661 / 500000000) (Real.log (258293234349 / 100000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (258293234349 / 100000000000) = -Real.log (100000000000 / 258293234349) := by
    rw [show ((258293234349 / 100000000000) : ℝ) = ((100000000000 / 258293234349) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (342229113 / 500000000) ≤ -Real.log (50000000000 / 99134868627) ∧
    -Real.log (50000000000 / 99134868627) ≤ (684458227 / 1000000000) := by
  have h := checkLog_sound (w := (49134868627 / 149134868627)) (n := 12)
    (lo := (342229113 / 500000000)) (hi := (684458227 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((99134868627 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(99134868627 / 50000000000) = 1/(50000000000 / 99134868627) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (342229113 / 500000000) (684458227 / 1000000000) (Real.log (99134868627 / 50000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (99134868627 / 50000000000) = -Real.log (50000000000 / 99134868627) := by
    rw [show ((99134868627 / 50000000000) : ℝ) = ((50000000000 / 99134868627) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (68610767 / 100000000) ≤ -Real.log (125000000000 / 248246302249) ∧
    -Real.log (125000000000 / 248246302249) ≤ (686107671 / 1000000000) := by
  have h := checkLog_sound (w := (123246302249 / 373246302249)) (n := 12)
    (lo := (68610767 / 100000000)) (hi := (686107671 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((248246302249 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(248246302249 / 125000000000) = 1/(125000000000 / 248246302249) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (68610767 / 100000000) (686107671 / 1000000000) (Real.log (248246302249 / 125000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (248246302249 / 125000000000) = -Real.log (125000000000 / 248246302249) := by
    rw [show ((248246302249 / 125000000000) : ℝ) = ((125000000000 / 248246302249) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0196
