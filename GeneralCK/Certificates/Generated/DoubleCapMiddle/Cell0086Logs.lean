import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0086
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

theorem reflection_log_1_neg : (345084597 / 1000000000) ≤ -Real.log (512 / 723) ∧
    -Real.log (512 / 723) ≤ (172542299 / 500000000) := by
  have h := checkLog_sound (w := (211 / 1235)) (n := 12)
    (lo := (345084597 / 1000000000)) (hi := (172542299 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((723 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(723 / 512) = 1/(512 / 723) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (345084597 / 1000000000) (172542299 / 500000000) (Real.log (723 / 512)) := by
  have h := reflection_log_1_neg
  have he : Real.log (723 / 512) = -Real.log (512 / 723) := by
    rw [show ((723 / 512) : ℝ) = ((512 / 723) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (13280359 / 25000000) ≤ -Real.log (301 / 512) ∧
    -Real.log (301 / 512) ≤ (531214361 / 1000000000) := by
  have h := checkLog_sound (w := (211 / 813)) (n := 12)
    (lo := (13280359 / 25000000)) (hi := (531214361 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 301) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 301) = 1/(301 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-531214361 / 1000000000) (-13280359 / 25000000) (Real.log (301 / 512)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (344254377 / 1000000000) ≤ -Real.log (640 / 903) ∧
    -Real.log (640 / 903) ≤ (172127189 / 500000000) := by
  have h := checkLog_sound (w := (263 / 1543)) (n := 12)
    (lo := (344254377 / 1000000000)) (hi := (172127189 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((903 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(903 / 640) = 1/(640 / 903) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (344254377 / 1000000000) (172127189 / 500000000) (Real.log (903 / 640)) := by
  have h := reflection_log_3_neg
  have he : Real.log (903 / 640) = -Real.log (640 / 903) := by
    rw [show ((903 / 640) : ℝ) = ((640 / 903) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (132305747 / 250000000) ≤ -Real.log (377 / 640) ∧
    -Real.log (377 / 640) ≤ (529222989 / 1000000000) := by
  have h := checkLog_sound (w := (263 / 1017)) (n := 12)
    (lo := (132305747 / 250000000)) (hi := (529222989 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 377) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 377) = 1/(377 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-529222989 / 1000000000) (-132305747 / 250000000) (Real.log (377 / 640)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (601151813 / 1000000000) ≤ -Real.log (256 / 467) ∧
    -Real.log (256 / 467) ≤ (300575907 / 500000000) := by
  have h := checkLog_sound (w := (211 / 723)) (n := 12)
    (lo := (601151813 / 1000000000)) (hi := (300575907 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((467 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(467 / 256) = 1/(256 / 467) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (601151813 / 1000000000) (300575907 / 500000000) (Real.log (467 / 256)) := by
  have h := reflection_log_5_neg
  have he : Real.log (467 / 256) = -Real.log (256 / 467) := by
    rw [show ((467 / 256) : ℝ) = ((256 / 467) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1738514953 / 1000000000) ≤ -Real.log (45 / 256) ∧
    -Real.log (45 / 256) ≤ (434628739 / 250000000) := by
  have h := checkLog_sound (w := (19 / 109)) (n := 12)
    (lo := (352220593 / 1000000000)) (hi := (176110297 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((64 / 45) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(64 / 45) = 1/(45 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-434628739 / 250000000) (-1738514953 / 1000000000) (Real.log (45 / 256)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (59986619 / 100000000) ≤ -Real.log (320 / 583) ∧
    -Real.log (320 / 583) ≤ (599866191 / 1000000000) := by
  have h := checkLog_sound (w := (263 / 903)) (n := 12)
    (lo := (59986619 / 100000000)) (hi := (599866191 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((583 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(583 / 320) = 1/(320 / 583) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (59986619 / 100000000) (599866191 / 1000000000) (Real.log (583 / 320)) := by
  have h := reflection_log_7_neg
  have he : Real.log (583 / 320) = -Real.log (320 / 583) := by
    rw [show ((583 / 320) : ℝ) = ((320 / 583) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (862634863 / 500000000) ≤ -Real.log (57 / 320) ∧
    -Real.log (57 / 320) ≤ (1725269729 / 1000000000) := by
  have h := checkLog_sound (w := (23 / 137)) (n := 12)
    (lo := (169487683 / 500000000)) (hi := (338975367 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80 / 57) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(80 / 57) = 1/(57 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1725269729 / 1000000000) (-862634863 / 500000000) (Real.log (57 / 320)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (59158381 / 125000000) ≤ -Real.log (100000 / 160523) ∧
    -Real.log (100000 / 160523) ≤ (473267049 / 1000000000) := by
  have h := checkLog_sound (w := (60523 / 260523)) (n := 12)
    (lo := (59158381 / 125000000)) (hi := (473267049 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160523 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(160523 / 100000) = 1/(100000 / 160523) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (59158381 / 125000000) (473267049 / 1000000000) (Real.log (160523 / 100000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (160523 / 100000) = -Real.log (100000 / 160523) := by
    rw [show ((160523 / 100000) : ℝ) = ((100000 / 160523) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (929451961 / 1000000000) ≤ -Real.log (39477 / 100000) ∧
    -Real.log (39477 / 100000) ≤ (929451963 / 1000000000) := by
  have h := checkLog_sound (w := (10523 / 89477)) (n := 12)
    (lo := (236304781 / 1000000000)) (hi := (118152391 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 39477) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(50000 / 39477) = 1/(39477 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-929451963 / 1000000000) (-929451961 / 1000000000) (Real.log (39477 / 100000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (474478601 / 1000000000) ≤ -Real.log (125000 / 200897) ∧
    -Real.log (125000 / 200897) ≤ (237239301 / 500000000) := by
  have h := checkLog_sound (w := (75897 / 325897)) (n := 12)
    (lo := (474478601 / 1000000000)) (hi := (237239301 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200897 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200897 / 125000) = 1/(125000 / 200897) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (474478601 / 1000000000) (237239301 / 500000000) (Real.log (200897 / 125000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (200897 / 125000) = -Real.log (125000 / 200897) := by
    rw [show ((200897 / 125000) : ℝ) = ((125000 / 200897) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (233598401 / 250000000) ≤ -Real.log (49103 / 125000) ∧
    -Real.log (49103 / 125000) ≤ (467196803 / 500000000) := by
  have h := checkLog_sound (w := (13397 / 111603)) (n := 12)
    (lo := (30155803 / 125000000)) (hi := (9649857 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 49103) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(62500 / 49103) = 1/(49103 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-467196803 / 500000000) (-233598401 / 250000000) (Real.log (49103 / 125000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (389230707 / 1000000000) ≤ -Real.log (200000 / 295169) ∧
    -Real.log (200000 / 295169) ≤ (97307677 / 250000000) := by
  have h := checkLog_sound (w := (95169 / 495169)) (n := 12)
    (lo := (389230707 / 1000000000)) (hi := (97307677 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((295169 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(295169 / 200000) = 1/(200000 / 295169) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (389230707 / 1000000000) (97307677 / 250000000) (Real.log (295169 / 200000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (295169 / 200000) = -Real.log (200000 / 295169) := by
    rw [show ((295169 / 200000) : ℝ) = ((200000 / 295169) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (161491959 / 250000000) ≤ -Real.log (104831 / 200000) ∧
    -Real.log (104831 / 200000) ≤ (645967837 / 1000000000) := by
  have h := checkLog_sound (w := (95169 / 304831)) (n := 12)
    (lo := (161491959 / 250000000)) (hi := (645967837 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 104831) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 104831) = 1/(104831 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-645967837 / 1000000000) (-161491959 / 250000000) (Real.log (104831 / 200000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (390496299 / 1000000000) ≤ -Real.log (500000 / 738857) ∧
    -Real.log (500000 / 738857) ≤ (3904963 / 10000000) := by
  have h := checkLog_sound (w := (238857 / 1238857)) (n := 12)
    (lo := (390496299 / 1000000000)) (hi := (3904963 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((738857 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(738857 / 500000) = 1/(500000 / 738857) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (390496299 / 1000000000) (3904963 / 10000000) (Real.log (738857 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (738857 / 500000) = -Real.log (500000 / 738857) := by
    rw [show ((738857 / 500000) : ℝ) = ((500000 / 738857) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (162384987 / 250000000) ≤ -Real.log (261143 / 500000) ∧
    -Real.log (261143 / 500000) ≤ (649539949 / 1000000000) := by
  have h := checkLog_sound (w := (238857 / 761143)) (n := 12)
    (lo := (162384987 / 250000000)) (hi := (649539949 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 261143) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 261143) = 1/(261143 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-649539949 / 1000000000) (-162384987 / 250000000) (Real.log (261143 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1402719009 / 1000000000) ≤ -Real.log (500000000000 / 2033120551207) ∧
    -Real.log (500000000000 / 2033120551207) ≤ (350679753 / 250000000) := by
  have h := checkLog_sound (w := (33120551207 / 4033120551207)) (n := 12)
    (lo := (16424649 / 1000000000)) (hi := (328493 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2033120551207 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2033120551207 / 2000000000000) = 1/(500000000000 / 2033120551207) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1402719009 / 1000000000) (350679753 / 250000000) (Real.log (2033120551207 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (2033120551207 / 500000000000) = -Real.log (500000000000 / 2033120551207) := by
    rw [show ((2033120551207 / 500000000000) : ℝ) = ((500000000000 / 2033120551207) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (281774441 / 200000000) ≤ -Real.log (4000000000 / 16365354459) ∧
    -Real.log (4000000000 / 16365354459) ≤ (88054513 / 62500000) := by
  have h := checkLog_sound (w := (365354459 / 32365354459)) (n := 12)
    (lo := (4515569 / 200000000)) (hi := (11288923 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((16365354459 / 16000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(16365354459 / 16000000000) = 1/(4000000000 / 16365354459) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (281774441 / 200000000) (88054513 / 62500000) (Real.log (16365354459 / 4000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (16365354459 / 4000000000) = -Real.log (4000000000 / 16365354459) := by
    rw [show ((16365354459 / 4000000000) : ℝ) = ((4000000000 / 16365354459) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1035198543 / 1000000000) ≤ -Real.log (500000000000 / 1407832606767) ∧
    -Real.log (500000000000 / 1407832606767) ≤ (207039709 / 200000000) := by
  have h := checkLog_sound (w := (407832606767 / 2407832606767)) (n := 12)
    (lo := (342051363 / 1000000000)) (hi := (85512841 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1407832606767 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1407832606767 / 1000000000000) = 1/(500000000000 / 1407832606767) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (1035198543 / 1000000000) (207039709 / 200000000) (Real.log (1407832606767 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (1407832606767 / 500000000000) = -Real.log (500000000000 / 1407832606767) := by
    rw [show ((1407832606767 / 500000000000) : ℝ) = ((500000000000 / 1407832606767) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (520018123 / 500000000) ≤ -Real.log (500000000000 / 1414659784103) ∧
    -Real.log (500000000000 / 1414659784103) ≤ (130004531 / 125000000) := by
  have h := checkLog_sound (w := (414659784103 / 2414659784103)) (n := 12)
    (lo := (173444533 / 500000000)) (hi := (346889067 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1414659784103 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1414659784103 / 1000000000000) = 1/(500000000000 / 1414659784103) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (520018123 / 500000000) (130004531 / 125000000) (Real.log (1414659784103 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1414659784103 / 500000000000) = -Real.log (500000000000 / 1414659784103) := by
    rw [show ((1414659784103 / 500000000000) : ℝ) = ((500000000000 / 1414659784103) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0086
