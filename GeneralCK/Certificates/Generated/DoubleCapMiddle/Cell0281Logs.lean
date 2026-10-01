import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0281
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

theorem reflection_log_1_neg : (228597401 / 1000000000) ≤ -Real.log (1024 / 1287) ∧
    -Real.log (1024 / 1287) ≤ (114298701 / 500000000) := by
  have h := checkLog_sound (w := (263 / 2311)) (n := 12)
    (lo := (228597401 / 1000000000)) (hi := (114298701 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1287 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1287 / 1024) = 1/(1024 / 1287) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (228597401 / 1000000000) (114298701 / 500000000) (Real.log (1287 / 1024)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1287 / 1024) = -Real.log (1024 / 1287) := by
    rw [show ((1287 / 1024) : ℝ) = ((1024 / 1287) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (296838447 / 1000000000) ≤ -Real.log (761 / 1024) ∧
    -Real.log (761 / 1024) ≤ (18552403 / 62500000) := by
  have h := checkLog_sound (w := (263 / 1785)) (n := 12)
    (lo := (296838447 / 1000000000)) (hi := (18552403 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 761) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 761) = 1/(761 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-18552403 / 62500000) (-296838447 / 1000000000) (Real.log (761 / 1024)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (57032773 / 250000000) ≤ -Real.log (160 / 201) ∧
    -Real.log (160 / 201) ≤ (228131093 / 1000000000) := by
  have h := checkLog_sound (w := (41 / 361)) (n := 12)
    (lo := (57032773 / 250000000)) (hi := (228131093 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((201 / 160) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(201 / 160) = 1/(160 / 201) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (57032773 / 250000000) (228131093 / 1000000000) (Real.log (201 / 160)) := by
  have h := reflection_log_3_neg
  have he : Real.log (201 / 160) = -Real.log (160 / 201) := by
    rw [show ((201 / 160) : ℝ) = ((160 / 201) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (148025161 / 500000000) ≤ -Real.log (119 / 160) ∧
    -Real.log (119 / 160) ≤ (296050323 / 1000000000) := by
  have h := checkLog_sound (w := (41 / 279)) (n := 12)
    (lo := (148025161 / 500000000)) (hi := (296050323 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 119) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(160 / 119) = 1/(119 / 160) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-296050323 / 1000000000) (-148025161 / 500000000) (Real.log (119 / 160)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (103634601 / 250000000) ≤ -Real.log (512 / 775) ∧
    -Real.log (512 / 775) ≤ (82907681 / 200000000) := by
  have h := checkLog_sound (w := (263 / 1287)) (n := 12)
    (lo := (103634601 / 250000000)) (hi := (82907681 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((775 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(775 / 512) = 1/(512 / 775) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (103634601 / 250000000) (82907681 / 200000000) (Real.log (775 / 512)) := by
  have h := reflection_log_5_neg
  have he : Real.log (775 / 512) = -Real.log (512 / 775) := by
    rw [show ((775 / 512) : ℝ) = ((512 / 775) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (45054483 / 62500000) ≤ -Real.log (249 / 512) ∧
    -Real.log (249 / 512) ≤ (72087173 / 100000000) := by
  have h := checkLog_sound (w := (7 / 505)) (n := 12)
    (lo := (6931137 / 250000000)) (hi := (27724549 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((256 / 249) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(256 / 249) = 1/(249 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-72087173 / 100000000) (-45054483 / 62500000) (Real.log (249 / 512)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (41376391 / 100000000) ≤ -Real.log (80 / 121) ∧
    -Real.log (80 / 121) ≤ (413763911 / 1000000000) := by
  have h := checkLog_sound (w := (41 / 201)) (n := 12)
    (lo := (41376391 / 100000000)) (hi := (413763911 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((121 / 80) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(121 / 80) = 1/(80 / 121) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (41376391 / 100000000) (413763911 / 1000000000) (Real.log (121 / 80)) := by
  have h := reflection_log_7_neg
  have he : Real.log (121 / 80) = -Real.log (80 / 121) := by
    rw [show ((121 / 80) : ℝ) = ((80 / 121) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (718464987 / 1000000000) ≤ -Real.log (39 / 80) ∧
    -Real.log (39 / 80) ≤ (718464989 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 79)) (n := 12)
    (lo := (25317807 / 1000000000)) (hi := (1582363 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40 / 39) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(40 / 39) = 1/(39 / 80) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-718464989 / 1000000000) (-718464987 / 1000000000) (Real.log (39 / 80)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (312518333 / 1000000000) ≤ -Real.log (1000000 / 1366863) ∧
    -Real.log (1000000 / 1366863) ≤ (156259167 / 500000000) := by
  have h := checkLog_sound (w := (366863 / 2366863)) (n := 12)
    (lo := (312518333 / 1000000000)) (hi := (156259167 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1366863 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1366863 / 1000000) = 1/(1000000 / 1366863) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (312518333 / 1000000000) (156259167 / 500000000) (Real.log (1366863 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1366863 / 1000000) = -Real.log (1000000 / 1366863) := by
    rw [show ((1366863 / 1000000) : ℝ) = ((1000000 / 1366863) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (9141369 / 20000000) ≤ -Real.log (633137 / 1000000) ∧
    -Real.log (633137 / 1000000) ≤ (457068451 / 1000000000) := by
  have h := checkLog_sound (w := (366863 / 1633137)) (n := 12)
    (lo := (9141369 / 20000000)) (hi := (457068451 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 633137) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 633137) = 1/(633137 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-457068451 / 1000000000) (-9141369 / 20000000) (Real.log (633137 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (156574753 / 500000000) ≤ -Real.log (500000 / 683863) ∧
    -Real.log (500000 / 683863) ≤ (313149507 / 1000000000) := by
  have h := checkLog_sound (w := (183863 / 1183863)) (n := 12)
    (lo := (156574753 / 500000000)) (hi := (313149507 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((683863 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(683863 / 500000) = 1/(500000 / 683863) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (156574753 / 500000000) (313149507 / 1000000000) (Real.log (683863 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (683863 / 500000) = -Real.log (500000 / 683863) := by
    rw [show ((683863 / 500000) : ℝ) = ((500000 / 683863) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (229216217 / 500000000) ≤ -Real.log (316137 / 500000) ∧
    -Real.log (316137 / 500000) ≤ (91686487 / 200000000) := by
  have h := checkLog_sound (w := (183863 / 816137)) (n := 12)
    (lo := (229216217 / 500000000)) (hi := (91686487 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 316137) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 316137) = 1/(316137 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-91686487 / 200000000) (-229216217 / 500000000) (Real.log (316137 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (238577433 / 1000000000) ≤ -Real.log (500000 / 634721) ∧
    -Real.log (500000 / 634721) ≤ (119288717 / 500000000) := by
  have h := checkLog_sound (w := (134721 / 1134721)) (n := 12)
    (lo := (238577433 / 1000000000)) (hi := (119288717 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((634721 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(634721 / 500000) = 1/(500000 / 634721) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (238577433 / 1000000000) (119288717 / 500000000) (Real.log (634721 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (634721 / 500000) = -Real.log (500000 / 634721) := by
    rw [show ((634721 / 500000) : ℝ) = ((500000 / 634721) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (313946653 / 1000000000) ≤ -Real.log (365279 / 500000) ∧
    -Real.log (365279 / 500000) ≤ (156973327 / 500000000) := by
  have h := checkLog_sound (w := (134721 / 865279)) (n := 12)
    (lo := (313946653 / 1000000000)) (hi := (156973327 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 365279) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 365279) = 1/(365279 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-156973327 / 500000000) (-313946653 / 1000000000) (Real.log (365279 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (59779027 / 250000000) ≤ -Real.log (500000 / 635063) ∧
    -Real.log (500000 / 635063) ≤ (239116109 / 1000000000) := by
  have h := checkLog_sound (w := (135063 / 1135063)) (n := 12)
    (lo := (59779027 / 250000000)) (hi := (239116109 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((635063 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(635063 / 500000) = 1/(500000 / 635063) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (59779027 / 250000000) (239116109 / 1000000000) (Real.log (635063 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (635063 / 500000) = -Real.log (500000 / 635063) := by
    rw [show ((635063 / 500000) : ℝ) = ((500000 / 635063) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (157441681 / 500000000) ≤ -Real.log (364937 / 500000) ∧
    -Real.log (364937 / 500000) ≤ (314883363 / 1000000000) := by
  have h := checkLog_sound (w := (135063 / 864937)) (n := 12)
    (lo := (157441681 / 500000000)) (hi := (314883363 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 364937) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 364937) = 1/(364937 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-314883363 / 1000000000) (-157441681 / 500000000) (Real.log (364937 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (769586783 / 1000000000) ≤ -Real.log (500000000000 / 1079436993889) ∧
    -Real.log (500000000000 / 1079436993889) ≤ (153917357 / 200000000) := by
  have h := checkLog_sound (w := (79436993889 / 2079436993889)) (n := 12)
    (lo := (76439603 / 1000000000)) (hi := (19109901 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1079436993889 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1079436993889 / 1000000000000) = 1/(500000000000 / 1079436993889) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (769586783 / 1000000000) (153917357 / 200000000) (Real.log (1079436993889 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1079436993889 / 500000000000) = -Real.log (500000000000 / 1079436993889) := by
    rw [show ((1079436993889 / 500000000000) : ℝ) = ((500000000000 / 1079436993889) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (38579097 / 50000000) ≤ -Real.log (125000000000 / 270398197617) ∧
    -Real.log (125000000000 / 270398197617) ≤ (385790971 / 500000000) := by
  have h := checkLog_sound (w := (20398197617 / 520398197617)) (n := 12)
    (lo := (1960869 / 25000000)) (hi := (78434761 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((270398197617 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(270398197617 / 250000000000) = 1/(125000000000 / 270398197617) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (38579097 / 50000000) (385790971 / 500000000) (Real.log (270398197617 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (270398197617 / 125000000000) = -Real.log (125000000000 / 270398197617) := by
    rw [show ((270398197617 / 125000000000) : ℝ) = ((125000000000 / 270398197617) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (552524087 / 1000000000) ≤ -Real.log (488281250 / 848453821) ∧
    -Real.log (488281250 / 848453821) ≤ (69065511 / 125000000) := by
  have h := checkLog_sound (w := (360172571 / 1336735071)) (n := 12)
    (lo := (552524087 / 1000000000)) (hi := (69065511 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((848453821 / 488281250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(848453821 / 488281250) = 1/(488281250 / 848453821) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (552524087 / 1000000000) (69065511 / 125000000) (Real.log (848453821 / 488281250)) := by
  have h := reflection_log_19_neg
  have he : Real.log (848453821 / 488281250) = -Real.log (488281250 / 848453821) := by
    rw [show ((848453821 / 488281250) : ℝ) = ((488281250 / 848453821) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (55399947 / 100000000) ≤ -Real.log (250000000000 / 435049748313) ∧
    -Real.log (250000000000 / 435049748313) ≤ (553999471 / 1000000000) := by
  have h := checkLog_sound (w := (185049748313 / 685049748313)) (n := 12)
    (lo := (55399947 / 100000000)) (hi := (553999471 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((435049748313 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(435049748313 / 250000000000) = 1/(250000000000 / 435049748313) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (55399947 / 100000000) (553999471 / 1000000000) (Real.log (435049748313 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (435049748313 / 250000000000) = -Real.log (250000000000 / 435049748313) := by
    rw [show ((435049748313 / 250000000000) : ℝ) = ((250000000000 / 435049748313) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0281
