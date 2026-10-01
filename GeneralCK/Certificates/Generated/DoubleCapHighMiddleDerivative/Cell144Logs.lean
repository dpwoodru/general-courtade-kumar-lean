import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell144
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed GeneralCK.Reflection

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

theorem reflection_log_1_neg : (288902031 / 1000000000) ≤ -Real.log (1024 / 1367) ∧
    -Real.log (1024 / 1367) ≤ (18056377 / 62500000) := by
  have h := checkLog_sound (w := (343 / 2391)) (n := 12)
    (lo := (288902031 / 1000000000)) (hi := (18056377 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1367 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1367 / 1024) = 1/(1024 / 1367) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (288902031 / 1000000000) (18056377 / 62500000) (Real.log (1367 / 1024)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1367 / 1024) = -Real.log (1024 / 1367) := by
    rw [show ((1367 / 1024) : ℝ) = ((1024 / 1367) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (407909499 / 1000000000) ≤ -Real.log (681 / 1024) ∧
    -Real.log (681 / 1024) ≤ (815819 / 2000000) := by
  have h := checkLog_sound (w := (343 / 1705)) (n := 12)
    (lo := (407909499 / 1000000000)) (hi := (815819 / 2000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 681) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 681) = 1/(681 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-815819 / 2000000) (-407909499 / 1000000000) (Real.log (681 / 1024)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (288463017 / 1000000000) ≤ -Real.log (320 / 427) ∧
    -Real.log (320 / 427) ≤ (144231509 / 500000000) := by
  have h := checkLog_sound (w := (107 / 747)) (n := 12)
    (lo := (288463017 / 1000000000)) (hi := (144231509 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((427 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(427 / 320) = 1/(320 / 427) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (288463017 / 1000000000) (144231509 / 500000000) (Real.log (427 / 320)) := by
  have h := reflection_log_3_neg
  have he : Real.log (427 / 320) = -Real.log (320 / 427) := by
    rw [show ((427 / 320) : ℝ) = ((320 / 427) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (40702883 / 100000000) ≤ -Real.log (213 / 320) ∧
    -Real.log (213 / 320) ≤ (407028831 / 1000000000) := by
  have h := checkLog_sound (w := (107 / 533)) (n := 12)
    (lo := (40702883 / 100000000)) (hi := (407028831 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 213) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(320 / 213) = 1/(213 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-407028831 / 1000000000) (-40702883 / 100000000) (Real.log (213 / 320)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (53292293 / 250000000) ≤ -Real.log (500000 / 618797) ∧
    -Real.log (500000 / 618797) ≤ (213169173 / 1000000000) := by
  have h := checkLog_sound (w := (118797 / 1118797)) (n := 12)
    (lo := (53292293 / 250000000)) (hi := (213169173 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((618797 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(618797 / 500000) = 1/(500000 / 618797) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (53292293 / 250000000) (213169173 / 1000000000) (Real.log (618797 / 500000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (618797 / 500000) = -Real.log (500000 / 618797) := by
    rw [show ((618797 / 500000) : ℝ) = ((500000 / 618797) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (33909507 / 125000000) ≤ -Real.log (381203 / 500000) ∧
    -Real.log (381203 / 500000) ≤ (271276057 / 1000000000) := by
  have h := checkLog_sound (w := (118797 / 881203)) (n := 12)
    (lo := (33909507 / 125000000)) (hi := (271276057 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 381203) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 381203) = 1/(381203 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-271276057 / 1000000000) (-33909507 / 125000000) (Real.log (381203 / 500000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (106755049 / 500000000) ≤ -Real.log (15625 / 19344) ∧
    -Real.log (15625 / 19344) ≤ (213510099 / 1000000000) := by
  have h := checkLog_sound (w := (3719 / 34969)) (n := 12)
    (lo := (106755049 / 500000000)) (hi := (213510099 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((19344 / 15625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(19344 / 15625) = 1/(15625 / 19344) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (106755049 / 500000000) (213510099 / 1000000000) (Real.log (19344 / 15625)) := by
  have h := reflection_log_7_neg
  have he : Real.log (19344 / 15625) = -Real.log (15625 / 19344) := by
    rw [show ((19344 / 15625) : ℝ) = ((15625 / 19344) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (6795743 / 25000000) ≤ -Real.log (11906 / 15625) ∧
    -Real.log (11906 / 15625) ≤ (271829721 / 1000000000) := by
  have h := checkLog_sound (w := (3719 / 27531)) (n := 12)
    (lo := (6795743 / 25000000)) (hi := (271829721 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 11906) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625 / 11906) = 1/(11906 / 15625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-271829721 / 1000000000) (-6795743 / 25000000) (Real.log (11906 / 15625)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (157579651 / 1000000000) ≤ -Real.log (500000 / 585337) ∧
    -Real.log (500000 / 585337) ≤ (39394913 / 250000000) := by
  have h := checkLog_sound (w := (85337 / 1085337)) (n := 12)
    (lo := (157579651 / 1000000000)) (hi := (39394913 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((585337 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(585337 / 500000) = 1/(500000 / 585337) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (157579651 / 1000000000) (39394913 / 250000000) (Real.log (585337 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (585337 / 500000) = -Real.log (500000 / 585337) := by
    rw [show ((585337 / 500000) : ℝ) = ((500000 / 585337) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (46785489 / 250000000) ≤ -Real.log (414663 / 500000) ∧
    -Real.log (414663 / 500000) ≤ (187141957 / 1000000000) := by
  have h := checkLog_sound (w := (85337 / 914663)) (n := 12)
    (lo := (46785489 / 250000000)) (hi := (187141957 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 414663) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 414663) = 1/(414663 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-187141957 / 1000000000) (-46785489 / 250000000) (Real.log (414663 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (9865383 / 62500000) ≤ -Real.log (500000 / 585493) ∧
    -Real.log (500000 / 585493) ≤ (157846129 / 1000000000) := by
  have h := checkLog_sound (w := (85493 / 1085493)) (n := 12)
    (lo := (9865383 / 62500000)) (hi := (157846129 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((585493 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(585493 / 500000) = 1/(500000 / 585493) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (9865383 / 62500000) (157846129 / 1000000000) (Real.log (585493 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (585493 / 500000) = -Real.log (500000 / 585493) := by
    rw [show ((585493 / 500000) : ℝ) = ((500000 / 585493) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (46879559 / 250000000) ≤ -Real.log (414507 / 500000) ∧
    -Real.log (414507 / 500000) ≤ (187518237 / 1000000000) := by
  have h := checkLog_sound (w := (85493 / 914507)) (n := 12)
    (lo := (46879559 / 250000000)) (hi := (187518237 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 414507) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 414507) = 1/(414507 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-187518237 / 1000000000) (-46879559 / 250000000) (Real.log (414507 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (347745923 / 500000000) ≤ -Real.log (6250000000 / 12529342723) ∧
    -Real.log (6250000000 / 12529342723) ≤ (86936481 / 125000000) := by
  have h := checkLog_sound (w := (29342723 / 25029342723)) (n := 12)
    (lo := (1172333 / 500000000)) (hi := (2344667 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12529342723 / 12500000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(12529342723 / 12500000000) = 1/(6250000000 / 12529342723) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (347745923 / 500000000) (86936481 / 125000000) (Real.log (12529342723 / 6250000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (12529342723 / 6250000000) = -Real.log (6250000000 / 12529342723) := by
    rw [show ((12529342723 / 6250000000) : ℝ) = ((6250000000 / 12529342723) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (69681153 / 100000000) ≤ -Real.log (250000000000 / 501835535977) ∧
    -Real.log (250000000000 / 501835535977) ≤ (174202883 / 250000000) := by
  have h := checkLog_sound (w := (1835535977 / 1001835535977)) (n := 12)
    (lo := (73287 / 20000000)) (hi := (3664351 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((501835535977 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(501835535977 / 500000000000) = 1/(250000000000 / 501835535977) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (69681153 / 100000000) (174202883 / 250000000) (Real.log (501835535977 / 250000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (501835535977 / 250000000000) = -Real.log (250000000000 / 501835535977) := by
    rw [show ((501835535977 / 250000000000) : ℝ) = ((250000000000 / 501835535977) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (121111307 / 250000000) ≤ -Real.log (250000000000 / 405818553369) ∧
    -Real.log (250000000000 / 405818553369) ≤ (484445229 / 1000000000) := by
  have h := checkLog_sound (w := (155818553369 / 655818553369)) (n := 12)
    (lo := (121111307 / 250000000)) (hi := (484445229 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((405818553369 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(405818553369 / 250000000000) = 1/(250000000000 / 405818553369) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (121111307 / 250000000) (484445229 / 1000000000) (Real.log (405818553369 / 250000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (405818553369 / 250000000000) = -Real.log (250000000000 / 405818553369) := by
    rw [show ((405818553369 / 250000000000) : ℝ) = ((250000000000 / 405818553369) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (485339819 / 1000000000) ≤ -Real.log (100000000000 / 162472702839) ∧
    -Real.log (100000000000 / 162472702839) ≤ (24266991 / 50000000) := by
  have h := checkLog_sound (w := (62472702839 / 262472702839)) (n := 12)
    (lo := (485339819 / 1000000000)) (hi := (24266991 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((162472702839 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(162472702839 / 100000000000) = 1/(100000000000 / 162472702839) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (485339819 / 1000000000) (24266991 / 50000000) (Real.log (162472702839 / 100000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (162472702839 / 100000000000) = -Real.log (100000000000 / 162472702839) := by
    rw [show ((162472702839 / 100000000000) : ℝ) = ((100000000000 / 162472702839) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (344721607 / 1000000000) ≤ -Real.log (100000000000 / 141159688711) ∧
    -Real.log (100000000000 / 141159688711) ≤ (43090201 / 125000000) := by
  have h := checkLog_sound (w := (41159688711 / 241159688711)) (n := 12)
    (lo := (344721607 / 1000000000)) (hi := (43090201 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((141159688711 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(141159688711 / 100000000000) = 1/(100000000000 / 141159688711) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (344721607 / 1000000000) (43090201 / 125000000) (Real.log (141159688711 / 100000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (141159688711 / 100000000000) = -Real.log (100000000000 / 141159688711) := by
    rw [show ((141159688711 / 100000000000) : ℝ) = ((100000000000 / 141159688711) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (69072873 / 200000000) ≤ -Real.log (100000000000 / 141250449329) ∧
    -Real.log (100000000000 / 141250449329) ≤ (172682183 / 500000000) := by
  have h := checkLog_sound (w := (41250449329 / 241250449329)) (n := 12)
    (lo := (69072873 / 200000000)) (hi := (172682183 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((141250449329 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(141250449329 / 100000000000) = 1/(100000000000 / 141250449329) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (69072873 / 200000000) (172682183 / 500000000) (Real.log (141250449329 / 100000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (141250449329 / 100000000000) = -Real.log (100000000000 / 141250449329) := by
    rw [show ((141250449329 / 100000000000) : ℝ) = ((100000000000 / 141250449329) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (29672107 / 1000000000) ≤ -Real.log (242690946951 / 250000000000) ∧
    -Real.log (242690946951 / 250000000000) ≤ (7418027 / 250000000) := by
  have h := checkLog_sound (w := (7309053049 / 492690946951)) (n := 12)
    (lo := (29672107 / 1000000000)) (hi := (7418027 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 242690946951) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 242690946951) = 1/(242690946951 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-7418027 / 250000000) (-29672107 / 1000000000) (Real.log (242690946951 / 250000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (461911 / 15625000) ≤ -Real.log (242717596431 / 250000000000) ∧
    -Real.log (242717596431 / 250000000000) ≤ (5912461 / 200000000) := by
  have h := checkLog_sound (w := (7282403569 / 492717596431)) (n := 12)
    (lo := (461911 / 15625000)) (hi := (5912461 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 242717596431) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 242717596431) = 1/(242717596431 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-5912461 / 200000000) (-461911 / 15625000) (Real.log (242717596431 / 250000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell144
