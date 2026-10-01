import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0096
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

theorem reflection_log_1_neg : (67350243 / 200000000) ≤ -Real.log (512 / 717) ∧
    -Real.log (512 / 717) ≤ (21046951 / 62500000) := by
  have h := checkLog_sound (w := (205 / 1229)) (n := 12)
    (lo := (67350243 / 200000000)) (hi := (21046951 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((717 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(717 / 512) = 1/(512 / 717) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (67350243 / 200000000) (21046951 / 62500000) (Real.log (717 / 512)) := by
  have h := reflection_log_1_neg
  have he : Real.log (717 / 512) = -Real.log (512 / 717) := by
    rw [show ((717 / 512) : ℝ) = ((512 / 717) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (511476877 / 1000000000) ≤ -Real.log (307 / 512) ∧
    -Real.log (307 / 512) ≤ (255738439 / 500000000) := by
  have h := checkLog_sound (w := (205 / 819)) (n := 12)
    (lo := (511476877 / 1000000000)) (hi := (255738439 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 307) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 307) = 1/(307 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-255738439 / 500000000) (-511476877 / 1000000000) (Real.log (307 / 512)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (67182809 / 200000000) ≤ -Real.log (1280 / 1791) ∧
    -Real.log (1280 / 1791) ≤ (167957023 / 500000000) := by
  have h := checkLog_sound (w := (511 / 3071)) (n := 12)
    (lo := (67182809 / 200000000)) (hi := (167957023 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1791 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1791 / 1280) = 1/(1280 / 1791) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (67182809 / 200000000) (167957023 / 500000000) (Real.log (1791 / 1280)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1791 / 1280) = -Real.log (1280 / 1791) := by
    rw [show ((1791 / 1280) : ℝ) = ((1280 / 1791) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (509524387 / 1000000000) ≤ -Real.log (769 / 1280) ∧
    -Real.log (769 / 1280) ≤ (127381097 / 250000000) := by
  have h := checkLog_sound (w := (511 / 2049)) (n := 12)
    (lo := (509524387 / 1000000000)) (hi := (127381097 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 769) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 769) = 1/(769 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-127381097 / 250000000) (-509524387 / 1000000000) (Real.log (769 / 1280)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (294110299 / 500000000) ≤ -Real.log (256 / 461) ∧
    -Real.log (256 / 461) ≤ (588220599 / 1000000000) := by
  have h := checkLog_sound (w := (205 / 717)) (n := 12)
    (lo := (294110299 / 500000000)) (hi := (588220599 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((461 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(461 / 256) = 1/(256 / 461) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (294110299 / 500000000) (588220599 / 1000000000) (Real.log (461 / 256)) := by
  have h := reflection_log_5_neg
  have he : Real.log (461 / 256) = -Real.log (256 / 461) := by
    rw [show ((461 / 256) : ℝ) = ((256 / 461) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (161335181 / 100000000) ≤ -Real.log (51 / 256) ∧
    -Real.log (51 / 256) ≤ (1613351813 / 1000000000) := by
  have h := checkLog_sound (w := (13 / 115)) (n := 12)
    (lo := (4541149 / 20000000)) (hi := (227057451 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((64 / 51) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(64 / 51) = 1/(51 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1613351813 / 1000000000) (-161335181 / 100000000) (Real.log (51 / 256)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (73364779 / 125000000) ≤ -Real.log (640 / 1151) ∧
    -Real.log (640 / 1151) ≤ (586918233 / 1000000000) := by
  have h := checkLog_sound (w := (511 / 1791)) (n := 12)
    (lo := (73364779 / 125000000)) (hi := (586918233 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1151 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1151 / 640) = 1/(640 / 1151) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (73364779 / 125000000) (586918233 / 1000000000) (Real.log (1151 / 640)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1151 / 640) = -Real.log (640 / 1151) := by
    rw [show ((1151 / 640) : ℝ) = ((640 / 1151) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (160165577 / 100000000) ≤ -Real.log (129 / 640) ∧
    -Real.log (129 / 640) ≤ (1601655773 / 1000000000) := by
  have h := checkLog_sound (w := (31 / 289)) (n := 12)
    (lo := (21536141 / 100000000)) (hi := (215361411 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 129) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(160 / 129) = 1/(129 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1601655773 / 1000000000) (-160165577 / 100000000) (Real.log (129 / 640)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (461198729 / 1000000000) ≤ -Real.log (500000 / 792987) ∧
    -Real.log (500000 / 792987) ≤ (46119873 / 100000000) := by
  have h := checkLog_sound (w := (292987 / 1292987)) (n := 12)
    (lo := (461198729 / 1000000000)) (hi := (46119873 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((792987 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(792987 / 500000) = 1/(500000 / 792987) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (461198729 / 1000000000) (46119873 / 100000000) (Real.log (792987 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (792987 / 500000) = -Real.log (500000 / 792987) := by
    rw [show ((792987 / 500000) : ℝ) = ((500000 / 792987) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (110228313 / 125000000) ≤ -Real.log (207013 / 500000) ∧
    -Real.log (207013 / 500000) ≤ (440913253 / 500000000) := by
  have h := checkLog_sound (w := (42987 / 457013)) (n := 12)
    (lo := (47169831 / 250000000)) (hi := (7547173 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 207013) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 207013) = 1/(207013 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-440913253 / 500000000) (-110228313 / 125000000) (Real.log (207013 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (462403571 / 1000000000) ≤ -Real.log (500000 / 793943) ∧
    -Real.log (500000 / 793943) ≤ (115600893 / 250000000) := by
  have h := checkLog_sound (w := (293943 / 1293943)) (n := 12)
    (lo := (462403571 / 1000000000)) (hi := (115600893 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((793943 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(793943 / 500000) = 1/(500000 / 793943) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (462403571 / 1000000000) (115600893 / 250000000) (Real.log (793943 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (793943 / 500000) = -Real.log (500000 / 793943) := by
    rw [show ((793943 / 500000) : ℝ) = ((500000 / 793943) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (221613817 / 250000000) ≤ -Real.log (206057 / 500000) ∧
    -Real.log (206057 / 500000) ≤ (88645527 / 100000000) := by
  have h := checkLog_sound (w := (43943 / 456057)) (n := 12)
    (lo := (24163511 / 125000000)) (hi := (193308089 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 206057) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 206057) = 1/(206057 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-88645527 / 100000000) (-221613817 / 250000000) (Real.log (206057 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (376752141 / 1000000000) ≤ -Real.log (1000000 / 1457543) ∧
    -Real.log (1000000 / 1457543) ≤ (188376071 / 500000000) := by
  have h := checkLog_sound (w := (457543 / 2457543)) (n := 12)
    (lo := (376752141 / 1000000000)) (hi := (188376071 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1457543 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1457543 / 1000000) = 1/(1000000 / 1457543) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (376752141 / 1000000000) (188376071 / 500000000) (Real.log (1457543 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1457543 / 1000000) = -Real.log (1000000 / 1457543) := by
    rw [show ((1457543 / 1000000) : ℝ) = ((1000000 / 1457543) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (611646459 / 1000000000) ≤ -Real.log (542457 / 1000000) ∧
    -Real.log (542457 / 1000000) ≤ (30582323 / 50000000) := by
  have h := checkLog_sound (w := (457543 / 1542457)) (n := 12)
    (lo := (611646459 / 1000000000)) (hi := (30582323 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 542457) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 542457) = 1/(542457 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-30582323 / 50000000) (-611646459 / 1000000000) (Real.log (542457 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (47248463 / 125000000) ≤ -Real.log (200000 / 291869) ∧
    -Real.log (200000 / 291869) ≤ (75597541 / 200000000) := by
  have h := checkLog_sound (w := (91869 / 491869)) (n := 12)
    (lo := (47248463 / 125000000)) (hi := (75597541 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((291869 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(291869 / 200000) = 1/(200000 / 291869) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (47248463 / 125000000) (75597541 / 200000000) (Real.log (291869 / 200000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (291869 / 200000) = -Real.log (200000 / 291869) := by
    rw [show ((291869 / 200000) : ℝ) = ((200000 / 291869) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (614973911 / 1000000000) ≤ -Real.log (108131 / 200000) ∧
    -Real.log (108131 / 200000) ≤ (76871739 / 125000000) := by
  have h := checkLog_sound (w := (91869 / 308131)) (n := 12)
    (lo := (614973911 / 1000000000)) (hi := (76871739 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 108131) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 108131) = 1/(108131 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-76871739 / 125000000) (-614973911 / 1000000000) (Real.log (108131 / 200000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (671512617 / 500000000) ≤ -Real.log (100000000000 / 383061450247) ∧
    -Real.log (100000000000 / 383061450247) ≤ (335756309 / 250000000) := by
  have h := checkLog_sound (w := (183061450247 / 583061450247)) (n := 12)
    (lo := (324939027 / 500000000)) (hi := (129975611 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((383061450247 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(383061450247 / 200000000000) = 1/(100000000000 / 383061450247) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (671512617 / 500000000) (335756309 / 250000000) (Real.log (383061450247 / 100000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (383061450247 / 100000000000) = -Real.log (100000000000 / 383061450247) := by
    rw [show ((383061450247 / 100000000000) : ℝ) = ((100000000000 / 383061450247) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (33721471 / 25000000) ≤ -Real.log (250000000000 / 963256526107) ∧
    -Real.log (250000000000 / 963256526107) ≤ (674429421 / 500000000) := by
  have h := checkLog_sound (w := (463256526107 / 1463256526107)) (n := 12)
    (lo := (32785583 / 50000000)) (hi := (655711661 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((963256526107 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(963256526107 / 500000000000) = 1/(250000000000 / 963256526107) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (33721471 / 25000000) (674429421 / 500000000) (Real.log (963256526107 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (963256526107 / 250000000000) = -Real.log (250000000000 / 963256526107) := by
    rw [show ((963256526107 / 250000000000) : ℝ) = ((250000000000 / 963256526107) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (4941993 / 5000000) ≤ -Real.log (500000000000 / 1343464090241) ∧
    -Real.log (500000000000 / 1343464090241) ≤ (494199301 / 500000000) := by
  have h := checkLog_sound (w := (343464090241 / 2343464090241)) (n := 12)
    (lo := (14762571 / 50000000)) (hi := (295251421 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1343464090241 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1343464090241 / 1000000000000) = 1/(500000000000 / 1343464090241) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (4941993 / 5000000) (494199301 / 500000000) (Real.log (1343464090241 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (1343464090241 / 500000000000) = -Real.log (500000000000 / 1343464090241) := by
    rw [show ((1343464090241 / 500000000000) : ℝ) = ((500000000000 / 1343464090241) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (198592323 / 200000000) ≤ -Real.log (500000000000 / 1349608345433) ∧
    -Real.log (500000000000 / 1349608345433) ≤ (992961617 / 1000000000) := by
  have h := checkLog_sound (w := (349608345433 / 2349608345433)) (n := 12)
    (lo := (59962887 / 200000000)) (hi := (74953609 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1349608345433 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1349608345433 / 1000000000000) = 1/(500000000000 / 1349608345433) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (198592323 / 200000000) (992961617 / 1000000000) (Real.log (1349608345433 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1349608345433 / 500000000000) = -Real.log (500000000000 / 1349608345433) := by
    rw [show ((1349608345433 / 500000000000) : ℝ) = ((500000000000 / 1349608345433) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0096
