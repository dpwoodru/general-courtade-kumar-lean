import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0210
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

theorem reflection_log_1_neg : (558722531 / 1000000000) ≤ -Real.log (640 / 1119) ∧
    -Real.log (640 / 1119) ≤ (139680633 / 250000000) := by
  have h := checkLog_sound (w := (479 / 1759)) (n := 12)
    (lo := (558722531 / 1000000000)) (hi := (139680633 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1119 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1119 / 640) = 1/(640 / 1119) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (558722531 / 1000000000) (139680633 / 250000000) (Real.log (1119 / 640)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1119 / 640) = -Real.log (640 / 1119) := by
    rw [show ((1119 / 640) : ℝ) = ((640 / 1119) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (138006381 / 100000000) ≤ -Real.log (161 / 640) ∧
    -Real.log (161 / 640) ≤ (345015953 / 250000000) := by
  have h := checkLog_sound (w := (159 / 481)) (n := 12)
    (lo := (68691663 / 100000000)) (hi := (686916631 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 161) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(320 / 161) = 1/(161 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-345015953 / 250000000) (-138006381 / 100000000) (Real.log (161 / 640)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (555320863 / 1000000000) ≤ -Real.log (400 / 697) ∧
    -Real.log (400 / 697) ≤ (17353777 / 31250000) := by
  have h := checkLog_sound (w := (297 / 1097)) (n := 12)
    (lo := (555320863 / 1000000000)) (hi := (17353777 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((697 / 400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(697 / 400) = 1/(400 / 697) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (555320863 / 1000000000) (17353777 / 31250000) (Real.log (697 / 400)) := by
  have h := reflection_log_3_neg
  have he : Real.log (697 / 400) = -Real.log (400 / 697) := by
    rw [show ((697 / 400) : ℝ) = ((400 / 697) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (678367779 / 500000000) ≤ -Real.log (103 / 400) ∧
    -Real.log (103 / 400) ≤ (33918389 / 25000000) := by
  have h := checkLog_sound (w := (97 / 303)) (n := 12)
    (lo := (331794189 / 500000000)) (hi := (663588379 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200 / 103) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(200 / 103) = 1/(103 / 400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-33918389 / 25000000) (-678367779 / 500000000) (Real.log (103 / 400)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (403379601 / 1000000000) ≤ -Real.log (320 / 479) ∧
    -Real.log (320 / 479) ≤ (201689801 / 500000000) := by
  have h := checkLog_sound (w := (159 / 799)) (n := 12)
    (lo := (403379601 / 1000000000)) (hi := (201689801 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((479 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(479 / 320) = 1/(320 / 479) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (403379601 / 1000000000) (201689801 / 500000000) (Real.log (479 / 320)) := by
  have h := reflection_log_5_neg
  have he : Real.log (479 / 320) = -Real.log (320 / 479) := by
    rw [show ((479 / 320) : ℝ) = ((320 / 479) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (68691663 / 100000000) ≤ -Real.log (161 / 320) ∧
    -Real.log (161 / 320) ≤ (686916631 / 1000000000) := by
  have h := checkLog_sound (w := (159 / 481)) (n := 12)
    (lo := (68691663 / 100000000)) (hi := (686916631 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 161) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(320 / 161) = 1/(161 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-686916631 / 1000000000) (-68691663 / 100000000) (Real.log (161 / 320)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (98853693 / 250000000) ≤ -Real.log (200 / 297) ∧
    -Real.log (200 / 297) ≤ (395414773 / 1000000000) := by
  have h := checkLog_sound (w := (97 / 497)) (n := 12)
    (lo := (98853693 / 250000000)) (hi := (395414773 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((297 / 200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(297 / 200) = 1/(200 / 297) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (98853693 / 250000000) (395414773 / 1000000000) (Real.log (297 / 200)) := by
  have h := reflection_log_7_neg
  have he : Real.log (297 / 200) = -Real.log (200 / 297) := by
    rw [show ((297 / 200) : ℝ) = ((200 / 297) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (331794189 / 500000000) ≤ -Real.log (103 / 200) ∧
    -Real.log (103 / 200) ≤ (663588379 / 1000000000) := by
  have h := checkLog_sound (w := (97 / 303)) (n := 12)
    (lo := (331794189 / 500000000)) (hi := (663588379 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200 / 103) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200 / 103) = 1/(103 / 200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-663588379 / 1000000000) (-331794189 / 500000000) (Real.log (103 / 200)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (606872259 / 1000000000) ≤ -Real.log (250000 / 458671) ∧
    -Real.log (250000 / 458671) ≤ (30343613 / 50000000) := by
  have h := checkLog_sound (w := (208671 / 708671)) (n := 12)
    (lo := (606872259 / 1000000000)) (hi := (30343613 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((458671 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(458671 / 250000) = 1/(250000 / 458671) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (606872259 / 1000000000) (30343613 / 50000000) (Real.log (458671 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (458671 / 250000) = -Real.log (250000 / 458671) := by
    rw [show ((458671 / 250000) : ℝ) = ((250000 / 458671) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (449974121 / 250000000) ≤ -Real.log (41329 / 250000) ∧
    -Real.log (41329 / 250000) ≤ (1799896487 / 1000000000) := by
  have h := checkLog_sound (w := (21171 / 103829)) (n := 12)
    (lo := (103400531 / 250000000)) (hi := (3308817 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 41329) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(62500 / 41329) = 1/(41329 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-1799896487 / 1000000000) (-449974121 / 250000000) (Real.log (41329 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (304155899 / 500000000) ≤ -Real.log (1000000 / 1837327) ∧
    -Real.log (1000000 / 1837327) ≤ (608311799 / 1000000000) := by
  have h := checkLog_sound (w := (837327 / 2837327)) (n := 12)
    (lo := (304155899 / 500000000)) (hi := (608311799 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1837327 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1837327 / 1000000) = 1/(1000000 / 1837327) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (304155899 / 500000000) (608311799 / 1000000000) (Real.log (1837327 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1837327 / 1000000) = -Real.log (1000000 / 1837327) := by
    rw [show ((1837327 / 1000000) : ℝ) = ((1000000 / 1837327) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1816013227 / 1000000000) ≤ -Real.log (162673 / 1000000) ∧
    -Real.log (162673 / 1000000) ≤ (181601323 / 100000000) := by
  have h := checkLog_sound (w := (87327 / 412673)) (n := 12)
    (lo := (429718867 / 1000000000)) (hi := (107429717 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 162673) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(250000 / 162673) = 1/(162673 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-181601323 / 100000000) (-1816013227 / 1000000000) (Real.log (162673 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (59435339 / 100000000) ≤ -Real.log (1000000 / 1811859) ∧
    -Real.log (1000000 / 1811859) ≤ (594353391 / 1000000000) := by
  have h := checkLog_sound (w := (811859 / 2811859)) (n := 12)
    (lo := (59435339 / 100000000)) (hi := (594353391 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1811859 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1811859 / 1000000) = 1/(1000000 / 1811859) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (59435339 / 100000000) (594353391 / 1000000000) (Real.log (1811859 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1811859 / 1000000) = -Real.log (1000000 / 1811859) := by
    rw [show ((1811859 / 1000000) : ℝ) = ((1000000 / 1811859) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (417640899 / 250000000) ≤ -Real.log (188141 / 1000000) ∧
    -Real.log (188141 / 1000000) ≤ (1670563599 / 1000000000) := by
  have h := checkLog_sound (w := (61859 / 438141)) (n := 12)
    (lo := (71067309 / 250000000)) (hi := (284269237 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 188141) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(250000 / 188141) = 1/(188141 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-1670563599 / 1000000000) (-417640899 / 250000000) (Real.log (188141 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (23860539 / 40000000) ≤ -Real.log (1000000 / 1815777) ∧
    -Real.log (1000000 / 1815777) ≤ (149128369 / 250000000) := by
  have h := checkLog_sound (w := (815777 / 2815777)) (n := 12)
    (lo := (23860539 / 40000000)) (hi := (149128369 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1815777 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1815777 / 1000000) = 1/(1000000 / 1815777) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (23860539 / 40000000) (149128369 / 250000000) (Real.log (1815777 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1815777 / 1000000) = -Real.log (1000000 / 1815777) := by
    rw [show ((1815777 / 1000000) : ℝ) = ((1000000 / 1815777) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (1691608297 / 1000000000) ≤ -Real.log (184223 / 1000000) ∧
    -Real.log (184223 / 1000000) ≤ (16916083 / 10000000) := by
  have h := checkLog_sound (w := (65777 / 434223)) (n := 12)
    (lo := (305313937 / 1000000000)) (hi := (152656969 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 184223) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(250000 / 184223) = 1/(184223 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-16916083 / 10000000) (-1691608297 / 1000000000) (Real.log (184223 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (2406768743 / 1000000000) ≤ -Real.log (250000000000 / 2774510634179) ∧
    -Real.log (250000000000 / 2774510634179) ≤ (2406768747 / 1000000000) := by
  have h := checkLog_sound (w := (774510634179 / 4774510634179)) (n := 12)
    (lo := (327327203 / 1000000000)) (hi := (81831801 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2774510634179 / 2000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(2774510634179 / 2000000000000) = 1/(250000000000 / 2774510634179) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (2406768743 / 1000000000) (2406768747 / 1000000000) (Real.log (2774510634179 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (2774510634179 / 250000000000) = -Real.log (250000000000 / 2774510634179) := by
    rw [show ((2774510634179 / 250000000000) : ℝ) = ((250000000000 / 2774510634179) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (75760157 / 31250000) ≤ -Real.log (100000000000 / 1129460328389) ∧
    -Real.log (100000000000 / 1129460328389) ≤ (606081257 / 250000000) := by
  have h := checkLog_sound (w := (329460328389 / 1929460328389)) (n := 12)
    (lo := (86220871 / 250000000)) (hi := (68976697 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1129460328389 / 800000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1129460328389 / 800000000000) = 1/(100000000000 / 1129460328389) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (75760157 / 31250000) (606081257 / 250000000) (Real.log (1129460328389 / 100000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1129460328389 / 100000000000) = -Real.log (100000000000 / 1129460328389) := by
    rw [show ((1129460328389 / 100000000000) : ℝ) = ((100000000000 / 1129460328389) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (452983397 / 200000000) ≤ -Real.log (500000000000 / 4815162564247) ∧
    -Real.log (500000000000 / 4815162564247) ≤ (2264916989 / 1000000000) := by
  have h := checkLog_sound (w := (815162564247 / 8815162564247)) (n := 12)
    (lo := (37095089 / 200000000)) (hi := (92737723 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4815162564247 / 4000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(4815162564247 / 4000000000000) = 1/(500000000000 / 4815162564247) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (452983397 / 200000000) (2264916989 / 1000000000) (Real.log (4815162564247 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (4815162564247 / 500000000000) = -Real.log (500000000000 / 4815162564247) := by
    rw [show ((4815162564247 / 500000000000) : ℝ) = ((500000000000 / 4815162564247) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (572030443 / 250000000) ≤ -Real.log (4000000000 / 39425630893) ∧
    -Real.log (4000000000 / 39425630893) ≤ (143007611 / 62500000) := by
  have h := checkLog_sound (w := (7425630893 / 71425630893)) (n := 12)
    (lo := (26085029 / 125000000)) (hi := (208680233 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((39425630893 / 32000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(39425630893 / 32000000000) = 1/(4000000000 / 39425630893) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (572030443 / 250000000) (143007611 / 62500000) (Real.log (39425630893 / 4000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (39425630893 / 4000000000) = -Real.log (4000000000 / 39425630893) := by
    rw [show ((39425630893 / 4000000000) : ℝ) = ((4000000000 / 39425630893) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0210
