import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_14528_neg : (839415341 / 1000000000) ≤ -Real.log (431963 / 1000000) ∧
    -Real.log (431963 / 1000000) ≤ (839415343 / 1000000000) := by
  have h := checkLog_sound (w := (68037 / 931963)) (n := 12)
    (lo := (146268161 / 1000000000)) (hi := (73134081 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 431963) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 431963) = 1/(431963 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14528 : Bounds (-839415343 / 1000000000) (-839415341 / 1000000000) (Real.log (431963 / 1000000)) := by
  have h := reflection_log_14528_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14529_neg : (389590823 / 1000000000) ≤ -Real.log (677333966631 / 1000000000000) ∧
    -Real.log (677333966631 / 1000000000000) ≤ (48698853 / 125000000) := by
  have h := checkLog_sound (w := (322666033369 / 1677333966631)) (n := 12)
    (lo := (389590823 / 1000000000)) (hi := (48698853 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 677333966631) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 677333966631) = 1/(677333966631 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14529 : Bounds (-48698853 / 125000000) (-389590823 / 1000000000) (Real.log (677333966631 / 1000000000000)) := by
  have h := reflection_log_14529_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14530_neg : (76700073 / 200000000) ≤ -Real.log (681471829311 / 1000000000000) ∧
    -Real.log (681471829311 / 1000000000000) ≤ (191750183 / 500000000) := by
  have h := checkLog_sound (w := (318528170689 / 1681471829311)) (n := 12)
    (lo := (76700073 / 200000000)) (hi := (191750183 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 681471829311) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 681471829311) = 1/(681471829311 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14530 : Bounds (-191750183 / 500000000) (-76700073 / 200000000) (Real.log (681471829311 / 1000000000000)) := by
  have h := reflection_log_14530_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14531_neg : (639241679 / 500000000) ≤ -Real.log (500000000000 / 1795594524547) ∧
    -Real.log (500000000000 / 1795594524547) ≤ (7990521 / 6250000) := by
  have h := checkLog_sound (w := (795594524547 / 2795594524547)) (n := 12)
    (lo := (292668089 / 500000000)) (hi := (585336179 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1795594524547 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1795594524547 / 1000000000000) = 1/(500000000000 / 1795594524547) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14531 : Bounds (639241679 / 500000000) (7990521 / 6250000) (Real.log (1795594524547 / 500000000000)) := by
  have h := reflection_log_14531_neg
  have he : Real.log (1795594524547 / 500000000000) = -Real.log (500000000000 / 1795594524547) := by
    rw [show ((1795594524547 / 500000000000) : ℝ) = ((500000000000 / 1795594524547) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14532_neg : (64461993 / 50000000) ≤ -Real.log (2500000000 / 9075065457) ∧
    -Real.log (2500000000 / 9075065457) ≤ (644619931 / 500000000) := by
  have h := checkLog_sound (w := (4075065457 / 14075065457)) (n := 12)
    (lo := (14902317 / 25000000)) (hi := (596092681 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9075065457 / 5000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(9075065457 / 5000000000) = 1/(2500000000 / 9075065457) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14532 : Bounds (64461993 / 50000000) (644619931 / 500000000) (Real.log (9075065457 / 2500000000)) := by
  have h := reflection_log_14532_neg
  have he : Real.log (9075065457 / 2500000000) = -Real.log (2500000000 / 9075065457) := by
    rw [show ((9075065457 / 2500000000) : ℝ) = ((2500000000 / 9075065457) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14533_neg : (3217836321 / 1000000000) ≤ -Real.log (125000000000 / 3121753246753) ∧
    -Real.log (125000000000 / 3121753246753) ≤ (1608918163 / 500000000) := by
  have h := checkLog_sound (w := (1121753246753 / 5121753246753)) (n := 12)
    (lo := (445247601 / 1000000000)) (hi := (222623801 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3121753246753 / 2000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3121753246753 / 2000000000000) = 1/(125000000000 / 3121753246753) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14533 : Bounds (3217836321 / 1000000000) (1608918163 / 500000000) (Real.log (3121753246753 / 125000000000)) := by
  have h := reflection_log_14533_neg
  have he : Real.log (3121753246753 / 125000000000) = -Real.log (125000000000 / 3121753246753) := by
    rw [show ((3121753246753 / 125000000000) : ℝ) = ((125000000000 / 3121753246753) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14534_neg : (407391937 / 125000000) ≤ -Real.log (250000000000 / 6506756756757) ∧
    -Real.log (250000000000 / 6506756756757) ≤ (3259135501 / 1000000000) := by
  have h := checkLog_sound (w := (2506756756757 / 10506756756757)) (n := 12)
    (lo := (60818347 / 125000000)) (hi := (486546777 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6506756756757 / 4000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(6506756756757 / 4000000000000) = 1/(250000000000 / 6506756756757) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14534 : Bounds (407391937 / 125000000) (3259135501 / 1000000000) (Real.log (6506756756757 / 250000000000)) := by
  have h := reflection_log_14534_neg
  have he : Real.log (6506756756757 / 250000000000) = -Real.log (250000000000 / 6506756756757) := by
    rw [show ((6506756756757 / 250000000000) : ℝ) = ((250000000000 / 6506756756757) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14535_neg : (657001733 / 1000000000) ≤ -Real.log (1000 / 1929) ∧
    -Real.log (1000 / 1929) ≤ (328500867 / 500000000) := by
  have h := checkLog_sound (w := (929 / 2929)) (n := 12)
    (lo := (657001733 / 1000000000)) (hi := (328500867 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1929 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1929 / 1000) = 1/(1000 / 1929) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14535 : Bounds (657001733 / 1000000000) (328500867 / 500000000) (Real.log (1929 / 1000)) := by
  have h := reflection_log_14535_neg
  have he : Real.log (1929 / 1000) = -Real.log (1000 / 1929) := by
    rw [show ((1929 / 1000) : ℝ) = ((1000 / 1929) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14536_neg : (13225377 / 5000000) ≤ -Real.log (71 / 1000) ∧
    -Real.log (71 / 1000) ≤ (661268851 / 250000000) := by
  have h := checkLog_sound (w := (27 / 98)) (n := 12)
    (lo := (28281693 / 50000000)) (hi := (565633861 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 71) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125 / 71) = 1/(71 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14536 : Bounds (-661268851 / 250000000) (-13225377 / 5000000) (Real.log (71 / 1000)) := by
  have h := reflection_log_14536_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14537_neg : (116071 / 125000000) ≤ -Real.log (1000000 / 1000929) ∧
    -Real.log (1000000 / 1000929) ≤ (928569 / 1000000000) := by
  have h := checkLog_sound (w := (929 / 2000929)) (n := 12)
    (lo := (116071 / 125000000)) (hi := (928569 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000929 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000929 / 1000000) = 1/(1000000 / 1000929) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14537 : Bounds (116071 / 125000000) (928569 / 1000000000) (Real.log (1000929 / 1000000)) := by
  have h := reflection_log_14537_neg
  have he : Real.log (1000929 / 1000000) = -Real.log (1000000 / 1000929) := by
    rw [show ((1000929 / 1000000) : ℝ) = ((1000000 / 1000929) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14538_neg : (929431 / 1000000000) ≤ -Real.log (999071 / 1000000) ∧
    -Real.log (999071 / 1000000) ≤ (116179 / 125000000) := by
  have h := checkLog_sound (w := (929 / 1999071)) (n := 12)
    (lo := (929431 / 1000000000)) (hi := (116179 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999071) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999071) = 1/(999071 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14538 : Bounds (-116179 / 125000000) (-929431 / 1000000000) (Real.log (999071 / 1000000)) := by
  have h := reflection_log_14538_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14539_neg : (449397779 / 1000000000) ≤ -Real.log (125000 / 195921) ∧
    -Real.log (125000 / 195921) ≤ (22469889 / 50000000) := by
  have h := checkLog_sound (w := (70921 / 320921)) (n := 12)
    (lo := (449397779 / 1000000000)) (hi := (22469889 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((195921 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(195921 / 125000) = 1/(125000 / 195921) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14539 : Bounds (449397779 / 1000000000) (22469889 / 50000000) (Real.log (195921 / 125000)) := by
  have h := reflection_log_14539_neg
  have he : Real.log (195921 / 125000) = -Real.log (125000 / 195921) := by
    rw [show ((195921 / 125000) : ℝ) = ((125000 / 195921) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14540_neg : (209466949 / 250000000) ≤ -Real.log (54079 / 125000) ∧
    -Real.log (54079 / 125000) ≤ (418933899 / 500000000) := by
  have h := checkLog_sound (w := (8421 / 116579)) (n := 12)
    (lo := (18090077 / 125000000)) (hi := (144720617 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 54079) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(62500 / 54079) = 1/(54079 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14540 : Bounds (-418933899 / 500000000) (-209466949 / 250000000) (Real.log (54079 / 125000)) := by
  have h := reflection_log_14540_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14541_neg : (451743549 / 1000000000) ≤ -Real.log (1000000 / 1571049) ∧
    -Real.log (1000000 / 1571049) ≤ (9034871 / 20000000) := by
  have h := checkLog_sound (w := (571049 / 2571049)) (n := 12)
    (lo := (451743549 / 1000000000)) (hi := (9034871 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1571049 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1571049 / 1000000) = 1/(1000000 / 1571049) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14541 : Bounds (451743549 / 1000000000) (9034871 / 20000000) (Real.log (1571049 / 1000000)) := by
  have h := reflection_log_14541_neg
  have he : Real.log (1571049 / 1000000) = -Real.log (1000000 / 1571049) := by
    rw [show ((1571049 / 1000000) : ℝ) = ((1000000 / 1571049) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14542_neg : (169282517 / 200000000) ≤ -Real.log (428951 / 1000000) ∧
    -Real.log (428951 / 1000000) ≤ (846412587 / 1000000000) := by
  have h := checkLog_sound (w := (71049 / 928951)) (n := 12)
    (lo := (30653081 / 200000000)) (hi := (76632703 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 428951) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 428951) = 1/(428951 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14542 : Bounds (-846412587 / 1000000000) (-169282517 / 200000000) (Real.log (428951 / 1000000)) := by
  have h := reflection_log_14542_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14543_neg : (98667259 / 250000000) ≤ -Real.log (673903039599 / 1000000000000) ∧
    -Real.log (673903039599 / 1000000000000) ≤ (394669037 / 1000000000) := by
  have h := checkLog_sound (w := (326096960401 / 1673903039599)) (n := 12)
    (lo := (98667259 / 250000000)) (hi := (394669037 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 673903039599) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 673903039599) = 1/(673903039599 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14543 : Bounds (-394669037 / 1000000000) (-98667259 / 250000000) (Real.log (673903039599 / 1000000000000)) := by
  have h := reflection_log_14543_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14544_neg : (388470017 / 1000000000) ≤ -Real.log (10595211759 / 15625000000) ∧
    -Real.log (10595211759 / 15625000000) ≤ (194235009 / 500000000) := by
  have h := checkLog_sound (w := (5029788241 / 26220211759)) (n := 12)
    (lo := (388470017 / 1000000000)) (hi := (194235009 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 10595211759) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 10595211759) = 1/(10595211759 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14544 : Bounds (-194235009 / 500000000) (-388470017 / 1000000000) (Real.log (10595211759 / 15625000000)) := by
  have h := reflection_log_14544_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14545_neg : (51490623 / 40000000) ≤ -Real.log (62500000000 / 226429159193) ∧
    -Real.log (62500000000 / 226429159193) ≤ (1287265577 / 1000000000) := by
  have h := checkLog_sound (w := (101429159193 / 351429159193)) (n := 12)
    (lo := (118823679 / 200000000)) (hi := (148529599 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((226429159193 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(226429159193 / 125000000000) = 1/(62500000000 / 226429159193) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14545 : Bounds (51490623 / 40000000) (1287265577 / 1000000000) (Real.log (226429159193 / 62500000000)) := by
  have h := reflection_log_14545_neg
  have he : Real.log (226429159193 / 62500000000) = -Real.log (62500000000 / 226429159193) := by
    rw [show ((226429159193 / 62500000000) : ℝ) = ((62500000000 / 226429159193) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14546_neg : (649078067 / 500000000) ≤ -Real.log (250000000000 / 915634303219) ∧
    -Real.log (250000000000 / 915634303219) ≤ (162269517 / 125000000) := by
  have h := checkLog_sound (w := (415634303219 / 1415634303219)) (n := 12)
    (lo := (302504477 / 500000000)) (hi := (121001791 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((915634303219 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(915634303219 / 500000000000) = 1/(250000000000 / 915634303219) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14546 : Bounds (649078067 / 500000000) (162269517 / 125000000) (Real.log (915634303219 / 250000000000)) := by
  have h := reflection_log_14546_neg
  have he : Real.log (915634303219 / 250000000000) = -Real.log (250000000000 / 915634303219) := by
    rw [show ((915634303219 / 250000000000) : ℝ) = ((250000000000 / 915634303219) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14547_neg : (407391937 / 125000000) ≤ -Real.log (500000000000 / 13013513513513) ∧
    -Real.log (500000000000 / 13013513513513) ≤ (3259135501 / 1000000000) := by
  have h := checkLog_sound (w := (5013513513513 / 21013513513513)) (n := 12)
    (lo := (60818347 / 125000000)) (hi := (486546777 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((13013513513513 / 8000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(13013513513513 / 8000000000000) = 1/(500000000000 / 13013513513513) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14547 : Bounds (407391937 / 125000000) (3259135501 / 1000000000) (Real.log (13013513513513 / 500000000000)) := by
  have h := reflection_log_14547_neg
  have he : Real.log (13013513513513 / 500000000000) = -Real.log (500000000000 / 13013513513513) := by
    rw [show ((13013513513513 / 500000000000) : ℝ) = ((500000000000 / 13013513513513) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14548_neg : (3302077133 / 1000000000) ≤ -Real.log (250000000000 / 6792253521127) ∧
    -Real.log (250000000000 / 6792253521127) ≤ (1651038569 / 500000000) := by
  have h := checkLog_sound (w := (2792253521127 / 10792253521127)) (n := 12)
    (lo := (529488413 / 1000000000)) (hi := (264744207 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6792253521127 / 4000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(6792253521127 / 4000000000000) = 1/(250000000000 / 6792253521127) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14548 : Bounds (3302077133 / 1000000000) (1651038569 / 500000000) (Real.log (6792253521127 / 250000000000)) := by
  have h := reflection_log_14548_neg
  have he : Real.log (6792253521127 / 250000000000) = -Real.log (250000000000 / 6792253521127) := by
    rw [show ((6792253521127 / 250000000000) : ℝ) = ((250000000000 / 6792253521127) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14549_neg : (131711147 / 200000000) ≤ -Real.log (250 / 483) ∧
    -Real.log (250 / 483) ≤ (82319467 / 125000000) := by
  have h := checkLog_sound (w := (233 / 733)) (n := 12)
    (lo := (131711147 / 200000000)) (hi := (82319467 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((483 / 250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(483 / 250) = 1/(250 / 483) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14549 : Bounds (131711147 / 200000000) (82319467 / 125000000) (Real.log (483 / 250)) := by
  have h := reflection_log_14549_neg
  have he : Real.log (483 / 250) = -Real.log (250 / 483) := by
    rw [show ((483 / 250) : ℝ) = ((250 / 483) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14550_neg : (672061893 / 250000000) ≤ -Real.log (17 / 250) ∧
    -Real.log (17 / 250) ≤ (336030947 / 125000000) := by
  have h := checkLog_sound (w := (57 / 193)) (n := 12)
    (lo := (38050377 / 62500000)) (hi := (608806033 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 68) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125 / 68) = 1/(17 / 250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14550 : Bounds (-336030947 / 125000000) (-672061893 / 250000000) (Real.log (17 / 250)) := by
  have h := reflection_log_14550_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14551_neg : (186313 / 200000000) ≤ -Real.log (250000 / 250233) ∧
    -Real.log (250000 / 250233) ≤ (465783 / 500000000) := by
  have h := checkLog_sound (w := (233 / 500233)) (n := 12)
    (lo := (186313 / 200000000)) (hi := (465783 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250233 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250233 / 250000) = 1/(250000 / 250233) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14551 : Bounds (186313 / 200000000) (465783 / 500000000) (Real.log (250233 / 250000)) := by
  have h := reflection_log_14551_neg
  have he : Real.log (250233 / 250000) = -Real.log (250000 / 250233) := by
    rw [show ((250233 / 250000) : ℝ) = ((250000 / 250233) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14552_neg : (466217 / 500000000) ≤ -Real.log (249767 / 250000) ∧
    -Real.log (249767 / 250000) ≤ (186487 / 200000000) := by
  have h := checkLog_sound (w := (233 / 499767)) (n := 12)
    (lo := (466217 / 500000000)) (hi := (186487 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 249767) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 249767) = 1/(249767 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14552 : Bounds (-186487 / 200000000) (-466217 / 500000000) (Real.log (249767 / 250000)) := by
  have h := reflection_log_14552_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14553_neg : (90263653 / 200000000) ≤ -Real.log (1000000 / 1570381) ∧
    -Real.log (1000000 / 1570381) ≤ (225659133 / 500000000) := by
  have h := checkLog_sound (w := (570381 / 2570381)) (n := 12)
    (lo := (90263653 / 200000000)) (hi := (225659133 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1570381 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1570381 / 1000000) = 1/(1000000 / 1570381) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14553 : Bounds (90263653 / 200000000) (225659133 / 500000000) (Real.log (1570381 / 1000000)) := by
  have h := reflection_log_14553_neg
  have he : Real.log (1570381 / 1000000) = -Real.log (1000000 / 1570381) := by
    rw [show ((1570381 / 1000000) : ℝ) = ((1000000 / 1570381) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14554_neg : (844856509 / 1000000000) ≤ -Real.log (429619 / 1000000) ∧
    -Real.log (429619 / 1000000) ≤ (844856511 / 1000000000) := by
  have h := checkLog_sound (w := (70381 / 929619)) (n := 12)
    (lo := (151709329 / 1000000000)) (hi := (15170933 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 429619) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 429619) = 1/(429619 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14554 : Bounds (-844856511 / 1000000000) (-844856509 / 1000000000) (Real.log (429619 / 1000000)) := by
  have h := reflection_log_14554_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14555_neg : (226838981 / 500000000) ≤ -Real.log (1000000 / 1574091) ∧
    -Real.log (1000000 / 1574091) ≤ (453677963 / 1000000000) := by
  have h := checkLog_sound (w := (574091 / 2574091)) (n := 12)
    (lo := (226838981 / 500000000)) (hi := (453677963 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1574091 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1574091 / 1000000) = 1/(1000000 / 1574091) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14555 : Bounds (226838981 / 500000000) (453677963 / 1000000000) (Real.log (1574091 / 1000000)) := by
  have h := reflection_log_14555_neg
  have he : Real.log (1574091 / 1000000) = -Real.log (1000000 / 1574091) := by
    rw [show ((1574091 / 1000000) : ℝ) = ((1000000 / 1574091) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14556_neg : (853529569 / 1000000000) ≤ -Real.log (425909 / 1000000) ∧
    -Real.log (425909 / 1000000) ≤ (853529571 / 1000000000) := by
  have h := checkLog_sound (w := (74091 / 925909)) (n := 12)
    (lo := (160382389 / 1000000000)) (hi := (16038239 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 425909) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 425909) = 1/(425909 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14556 : Bounds (-853529571 / 1000000000) (-853529569 / 1000000000) (Real.log (425909 / 1000000)) := by
  have h := reflection_log_14556_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14557_neg : (399851607 / 1000000000) ≤ -Real.log (670419523719 / 1000000000000) ∧
    -Real.log (670419523719 / 1000000000000) ≤ (49981451 / 125000000) := by
  have h := checkLog_sound (w := (329580476281 / 1670419523719)) (n := 12)
    (lo := (399851607 / 1000000000)) (hi := (49981451 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 670419523719) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 670419523719) = 1/(670419523719 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14557 : Bounds (-49981451 / 125000000) (-399851607 / 1000000000) (Real.log (670419523719 / 1000000000000)) := by
  have h := reflection_log_14557_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14558_neg : (98384561 / 250000000) ≤ -Real.log (674665514839 / 1000000000000) ∧
    -Real.log (674665514839 / 1000000000000) ≤ (78707649 / 200000000) := by
  have h := checkLog_sound (w := (325334485161 / 1674665514839)) (n := 12)
    (lo := (98384561 / 250000000)) (hi := (78707649 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 674665514839) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 674665514839) = 1/(674665514839 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14558 : Bounds (-78707649 / 200000000) (-98384561 / 250000000) (Real.log (674665514839 / 1000000000000)) := by
  have h := reflection_log_14558_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14559_neg : (648087387 / 500000000) ≤ -Real.log (250000000000 / 913821898007) ∧
    -Real.log (250000000000 / 913821898007) ≤ (162021847 / 125000000) := by
  have h := checkLog_sound (w := (413821898007 / 1413821898007)) (n := 12)
    (lo := (301513797 / 500000000)) (hi := (120605519 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((913821898007 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(913821898007 / 500000000000) = 1/(250000000000 / 913821898007) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14559 : Bounds (648087387 / 500000000) (162021847 / 125000000) (Real.log (913821898007 / 250000000000)) := by
  have h := reflection_log_14559_neg
  have he : Real.log (913821898007 / 250000000000) = -Real.log (250000000000 / 913821898007) := by
    rw [show ((913821898007 / 250000000000) : ℝ) = ((250000000000 / 913821898007) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14560_neg : (326801883 / 250000000) ≤ -Real.log (976562500 / 3609217561) ∧
    -Real.log (976562500 / 3609217561) ≤ (653603767 / 500000000) := by
  have h := checkLog_sound (w := (1656092561 / 5562342561)) (n := 12)
    (lo := (9594693 / 15625000)) (hi := (614060353 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3609217561 / 1953125000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(3609217561 / 1953125000) = 1/(976562500 / 3609217561) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14560 : Bounds (326801883 / 250000000) (653603767 / 500000000) (Real.log (3609217561 / 976562500)) := by
  have h := reflection_log_14560_neg
  have he : Real.log (3609217561 / 976562500) = -Real.log (976562500 / 3609217561) := by
    rw [show ((3609217561 / 976562500) : ℝ) = ((976562500 / 3609217561) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14561_neg : (3302077133 / 1000000000) ≤ -Real.log (500000000000 / 13584507042253) ∧
    -Real.log (500000000000 / 13584507042253) ≤ (1651038569 / 500000000) := by
  have h := checkLog_sound (w := (5584507042253 / 21584507042253)) (n := 12)
    (lo := (529488413 / 1000000000)) (hi := (264744207 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((13584507042253 / 8000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(13584507042253 / 8000000000000) = 1/(500000000000 / 13584507042253) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14561 : Bounds (3302077133 / 1000000000) (1651038569 / 500000000) (Real.log (13584507042253 / 500000000000)) := by
  have h := reflection_log_14561_neg
  have he : Real.log (13584507042253 / 500000000000) = -Real.log (500000000000 / 13584507042253) := by
    rw [show ((13584507042253 / 500000000000) : ℝ) = ((500000000000 / 13584507042253) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14562_neg : (3346803307 / 1000000000) ≤ -Real.log (250000000000 / 7102941176471) ∧
    -Real.log (250000000000 / 7102941176471) ≤ (209175207 / 62500000) := by
  have h := checkLog_sound (w := (3102941176471 / 11102941176471)) (n := 12)
    (lo := (574214587 / 1000000000)) (hi := (143553647 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7102941176471 / 4000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(7102941176471 / 4000000000000) = 1/(250000000000 / 7102941176471) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14562 : Bounds (3346803307 / 1000000000) (209175207 / 62500000) (Real.log (7102941176471 / 250000000000)) := by
  have h := reflection_log_14562_neg
  have he : Real.log (7102941176471 / 250000000000) = -Real.log (250000000000 / 7102941176471) := by
    rw [show ((7102941176471 / 250000000000) : ℝ) = ((250000000000 / 7102941176471) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14563_neg : (330053663 / 500000000) ≤ -Real.log (200 / 387) ∧
    -Real.log (200 / 387) ≤ (660107327 / 1000000000) := by
  have h := checkLog_sound (w := (187 / 587)) (n := 12)
    (lo := (330053663 / 500000000)) (hi := (660107327 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((387 / 200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(387 / 200) = 1/(200 / 387) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14563 : Bounds (330053663 / 500000000) (660107327 / 1000000000) (Real.log (387 / 200)) := by
  have h := reflection_log_14563_neg
  have he : Real.log (387 / 200) = -Real.log (200 / 387) := by
    rw [show ((387 / 200) : ℝ) = ((200 / 387) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14564_neg : (2733368007 / 1000000000) ≤ -Real.log (13 / 200) ∧
    -Real.log (13 / 200) ≤ (2733368011 / 1000000000) := by
  have h := checkLog_sound (w := (6 / 19)) (n := 12)
    (lo := (653926467 / 1000000000)) (hi := (163481617 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25 / 13) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(25 / 13) = 1/(13 / 200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14564 : Bounds (-2733368011 / 1000000000) (-2733368007 / 1000000000) (Real.log (13 / 200)) := by
  have h := reflection_log_14564_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14565_neg : (934563 / 1000000000) ≤ -Real.log (200000 / 200187) ∧
    -Real.log (200000 / 200187) ≤ (233641 / 250000000) := by
  have h := checkLog_sound (w := (187 / 400187)) (n := 12)
    (lo := (934563 / 1000000000)) (hi := (233641 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200187 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200187 / 200000) = 1/(200000 / 200187) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14565 : Bounds (934563 / 1000000000) (233641 / 250000000) (Real.log (200187 / 200000)) := by
  have h := reflection_log_14565_neg
  have he : Real.log (200187 / 200000) = -Real.log (200000 / 200187) := by
    rw [show ((200187 / 200000) : ℝ) = ((200000 / 200187) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14566_neg : (935437 / 1000000000) ≤ -Real.log (199813 / 200000) ∧
    -Real.log (199813 / 200000) ≤ (467719 / 500000000) := by
  have h := checkLog_sound (w := (187 / 399813)) (n := 12)
    (lo := (935437 / 1000000000)) (hi := (467719 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 199813) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 199813) = 1/(199813 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14566 : Bounds (-467719 / 500000000) (-935437 / 1000000000) (Real.log (199813 / 200000)) := by
  have h := reflection_log_14566_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14567_neg : (56656767 / 125000000) ≤ -Real.log (62500 / 98339) ∧
    -Real.log (62500 / 98339) ≤ (453254137 / 1000000000) := by
  have h := checkLog_sound (w := (35839 / 160839)) (n := 12)
    (lo := (56656767 / 125000000)) (hi := (453254137 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((98339 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(98339 / 62500) = 1/(62500 / 98339) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14567 : Bounds (56656767 / 125000000) (453254137 / 1000000000) (Real.log (98339 / 62500)) := by
  have h := reflection_log_14567_neg
  have he : Real.log (98339 / 62500) = -Real.log (62500 / 98339) := by
    rw [show ((98339 / 62500) : ℝ) = ((62500 / 98339) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14568_neg : (212991183 / 250000000) ≤ -Real.log (26661 / 62500) ∧
    -Real.log (26661 / 62500) ≤ (425982367 / 500000000) := by
  have h := checkLog_sound (w := (4589 / 57911)) (n := 12)
    (lo := (9926097 / 62500000)) (hi := (158817553 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 26661) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(31250 / 26661) = 1/(26661 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14568 : Bounds (-425982367 / 500000000) (-212991183 / 250000000) (Real.log (26661 / 62500)) := by
  have h := reflection_log_14568_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14569_neg : (455628297 / 1000000000) ≤ -Real.log (250000 / 394291) ∧
    -Real.log (250000 / 394291) ≤ (227814149 / 500000000) := by
  have h := checkLog_sound (w := (144291 / 644291)) (n := 12)
    (lo := (455628297 / 1000000000)) (hi := (227814149 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((394291 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(394291 / 250000) = 1/(250000 / 394291) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14569 : Bounds (455628297 / 1000000000) (227814149 / 500000000) (Real.log (394291 / 250000)) := by
  have h := reflection_log_14569_neg
  have he : Real.log (394291 / 250000) = -Real.log (250000 / 394291) := by
    rw [show ((394291 / 250000) : ℝ) = ((250000 / 394291) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14570_neg : (860770881 / 1000000000) ≤ -Real.log (105709 / 250000) ∧
    -Real.log (105709 / 250000) ≤ (860770883 / 1000000000) := by
  have h := checkLog_sound (w := (19291 / 230709)) (n := 12)
    (lo := (167623701 / 1000000000)) (hi := (83811851 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 105709) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(125000 / 105709) = 1/(105709 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14570 : Bounds (-860770883 / 1000000000) (-860770881 / 1000000000) (Real.log (105709 / 250000)) := by
  have h := reflection_log_14570_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14571_neg : (50642823 / 125000000) ≤ -Real.log (41680107319 / 62500000000) ∧
    -Real.log (41680107319 / 62500000000) ≤ (81028517 / 200000000) := by
  have h := checkLog_sound (w := (20819892681 / 104180107319)) (n := 12)
    (lo := (50642823 / 125000000)) (hi := (81028517 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 41680107319) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 41680107319) = 1/(41680107319 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14571 : Bounds (-81028517 / 200000000) (-50642823 / 125000000) (Real.log (41680107319 / 62500000000)) := by
  have h := reflection_log_14571_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14572_neg : (99677649 / 250000000) ≤ -Real.log (2621816079 / 3906250000) ∧
    -Real.log (2621816079 / 3906250000) ≤ (398710597 / 1000000000) := by
  have h := checkLog_sound (w := (1284433921 / 6528066079)) (n := 12)
    (lo := (99677649 / 250000000)) (hi := (398710597 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3906250000 / 2621816079) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3906250000 / 2621816079) = 1/(2621816079 / 3906250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14572 : Bounds (-398710597 / 1000000000) (-99677649 / 250000000) (Real.log (2621816079 / 3906250000)) := by
  have h := reflection_log_14572_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14573_neg : (1305218869 / 1000000000) ≤ -Real.log (125000000000 / 461062038183) ∧
    -Real.log (125000000000 / 461062038183) ≤ (1305218871 / 1000000000) := by
  have h := checkLog_sound (w := (211062038183 / 711062038183)) (n := 12)
    (lo := (612071689 / 1000000000)) (hi := (61207169 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((461062038183 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(461062038183 / 250000000000) = 1/(125000000000 / 461062038183) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14573 : Bounds (1305218869 / 1000000000) (1305218871 / 1000000000) (Real.log (461062038183 / 125000000000)) := by
  have h := reflection_log_14573_neg
  have he : Real.log (461062038183 / 125000000000) = -Real.log (125000000000 / 461062038183) := by
    rw [show ((461062038183 / 125000000000) : ℝ) = ((125000000000 / 461062038183) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14574_neg : (658199589 / 500000000) ≤ -Real.log (500000000000 / 1864983114021) ∧
    -Real.log (500000000000 / 1864983114021) ≤ (65819959 / 50000000) := by
  have h := checkLog_sound (w := (864983114021 / 2864983114021)) (n := 12)
    (lo := (311625999 / 500000000)) (hi := (623251999 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1864983114021 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1864983114021 / 1000000000000) = 1/(500000000000 / 1864983114021) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14574 : Bounds (658199589 / 500000000) (65819959 / 50000000) (Real.log (1864983114021 / 500000000000)) := by
  have h := reflection_log_14574_neg
  have he : Real.log (1864983114021 / 500000000000) = -Real.log (500000000000 / 1864983114021) := by
    rw [show ((1864983114021 / 500000000000) : ℝ) = ((500000000000 / 1864983114021) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14575_neg : (3346803307 / 1000000000) ≤ -Real.log (500000000000 / 14205882352941) ∧
    -Real.log (500000000000 / 14205882352941) ≤ (209175207 / 62500000) := by
  have h := checkLog_sound (w := (6205882352941 / 22205882352941)) (n := 12)
    (lo := (574214587 / 1000000000)) (hi := (143553647 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((14205882352941 / 8000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(14205882352941 / 8000000000000) = 1/(500000000000 / 14205882352941) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14575 : Bounds (3346803307 / 1000000000) (209175207 / 62500000) (Real.log (14205882352941 / 500000000000)) := by
  have h := reflection_log_14575_neg
  have he : Real.log (14205882352941 / 500000000000) = -Real.log (500000000000 / 14205882352941) := by
    rw [show ((14205882352941 / 500000000000) : ℝ) = ((500000000000 / 14205882352941) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14576_neg : (3393475333 / 1000000000) ≤ -Real.log (62500000000 / 1860576923077) ∧
    -Real.log (62500000000 / 1860576923077) ≤ (1696737669 / 500000000) := by
  have h := checkLog_sound (w := (860576923077 / 2860576923077)) (n := 12)
    (lo := (620886613 / 1000000000)) (hi := (310443307 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1860576923077 / 1000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1860576923077 / 1000000000000) = 1/(62500000000 / 1860576923077) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14576 : Bounds (3393475333 / 1000000000) (1696737669 / 500000000) (Real.log (1860576923077 / 62500000000)) := by
  have h := reflection_log_14576_neg
  have he : Real.log (1860576923077 / 62500000000) = -Real.log (62500000000 / 1860576923077) := by
    rw [show ((1860576923077 / 62500000000) : ℝ) = ((62500000000 / 1860576923077) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14577_neg : (661656513 / 1000000000) ≤ -Real.log (500 / 969) ∧
    -Real.log (500 / 969) ≤ (330828257 / 500000000) := by
  have h := checkLog_sound (w := (469 / 1469)) (n := 12)
    (lo := (661656513 / 1000000000)) (hi := (330828257 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((969 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(969 / 500) = 1/(500 / 969) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14577 : Bounds (661656513 / 1000000000) (330828257 / 500000000) (Real.log (969 / 500)) := by
  have h := reflection_log_14577_neg
  have he : Real.log (969 / 500) = -Real.log (500 / 969) := by
    rw [show ((969 / 500) : ℝ) = ((500 / 969) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14578_neg : (2780620891 / 1000000000) ≤ -Real.log (31 / 500) ∧
    -Real.log (31 / 500) ≤ (86894403 / 31250000) := by
  have h := checkLog_sound (w := (1 / 249)) (n := 12)
    (lo := (8032171 / 1000000000)) (hi := (2008043 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 124) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(125 / 124) = 1/(31 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14578 : Bounds (-86894403 / 31250000) (-2780620891 / 1000000000) (Real.log (31 / 500)) := by
  have h := reflection_log_14578_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14579_neg : (23439 / 25000000) ≤ -Real.log (500000 / 500469) ∧
    -Real.log (500000 / 500469) ≤ (937561 / 1000000000) := by
  have h := checkLog_sound (w := (469 / 1000469)) (n := 12)
    (lo := (23439 / 25000000)) (hi := (937561 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500469 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500469 / 500000) = 1/(500000 / 500469) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14579 : Bounds (23439 / 25000000) (937561 / 1000000000) (Real.log (500469 / 500000)) := by
  have h := reflection_log_14579_neg
  have he : Real.log (500469 / 500000) = -Real.log (500000 / 500469) := by
    rw [show ((500469 / 500000) : ℝ) = ((500000 / 500469) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14580_neg : (23461 / 25000000) ≤ -Real.log (499531 / 500000) ∧
    -Real.log (499531 / 500000) ≤ (938441 / 1000000000) := by
  have h := checkLog_sound (w := (469 / 999531)) (n := 12)
    (lo := (23461 / 25000000)) (hi := (938441 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499531) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499531) = 1/(499531 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14580 : Bounds (-938441 / 1000000000) (-23461 / 25000000) (Real.log (499531 / 500000)) := by
  have h := reflection_log_14580_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14581_neg : (455205931 / 1000000000) ≤ -Real.log (500000 / 788249) ∧
    -Real.log (500000 / 788249) ≤ (113801483 / 250000000) := by
  have h := checkLog_sound (w := (288249 / 1288249)) (n := 12)
    (lo := (455205931 / 1000000000)) (hi := (113801483 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((788249 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(788249 / 500000) = 1/(500000 / 788249) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14581 : Bounds (455205931 / 1000000000) (113801483 / 250000000) (Real.log (788249 / 500000)) := by
  have h := reflection_log_14581_neg
  have he : Real.log (788249 / 500000) = -Real.log (500000 / 788249) := by
    rw [show ((788249 / 500000) : ℝ) = ((500000 / 788249) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14582_neg : (859197041 / 1000000000) ≤ -Real.log (211751 / 500000) ∧
    -Real.log (211751 / 500000) ≤ (859197043 / 1000000000) := by
  have h := checkLog_sound (w := (38249 / 461751)) (n := 12)
    (lo := (166049861 / 1000000000)) (hi := (83024931 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 211751) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 211751) = 1/(211751 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14582 : Bounds (-859197043 / 1000000000) (-859197041 / 1000000000) (Real.log (211751 / 500000)) := by
  have h := reflection_log_14582_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14583_neg : (228797859 / 500000000) ≤ -Real.log (100000 / 158027) ∧
    -Real.log (100000 / 158027) ≤ (457595719 / 1000000000) := by
  have h := checkLog_sound (w := (58027 / 258027)) (n := 12)
    (lo := (228797859 / 500000000)) (hi := (457595719 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((158027 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(158027 / 100000) = 1/(100000 / 158027) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14583 : Bounds (228797859 / 500000000) (457595719 / 1000000000) (Real.log (158027 / 100000)) := by
  have h := reflection_log_14583_neg
  have he : Real.log (158027 / 100000) = -Real.log (100000 / 158027) := by
    rw [show ((158027 / 100000) : ℝ) = ((100000 / 158027) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14584_neg : (868143631 / 1000000000) ≤ -Real.log (41973 / 100000) ∧
    -Real.log (41973 / 100000) ≤ (868143633 / 1000000000) := by
  have h := checkLog_sound (w := (8027 / 91973)) (n := 12)
    (lo := (174996451 / 1000000000)) (hi := (43749113 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 41973) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(50000 / 41973) = 1/(41973 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14584 : Bounds (-868143633 / 1000000000) (-868143631 / 1000000000) (Real.log (41973 / 100000)) := by
  have h := reflection_log_14584_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14585_neg : (410547913 / 1000000000) ≤ -Real.log (6632867271 / 10000000000) ∧
    -Real.log (6632867271 / 10000000000) ≤ (205273957 / 500000000) := by
  have h := checkLog_sound (w := (3367132729 / 16632867271)) (n := 12)
    (lo := (410547913 / 1000000000)) (hi := (205273957 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 6632867271) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 6632867271) = 1/(6632867271 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14585 : Bounds (-205273957 / 500000000) (-410547913 / 1000000000) (Real.log (6632867271 / 10000000000)) := by
  have h := reflection_log_14585_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14586_neg : (40399111 / 100000000) ≤ -Real.log (166912513999 / 250000000000) ∧
    -Real.log (166912513999 / 250000000000) ≤ (403991111 / 1000000000) := by
  have h := checkLog_sound (w := (83087486001 / 416912513999)) (n := 12)
    (lo := (40399111 / 100000000)) (hi := (403991111 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 166912513999) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 166912513999) = 1/(166912513999 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14586 : Bounds (-403991111 / 1000000000) (-40399111 / 100000000) (Real.log (166912513999 / 250000000000)) := by
  have h := reflection_log_14586_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14587_neg : (1314402973 / 1000000000) ≤ -Real.log (6250000000 / 23265799217) ∧
    -Real.log (6250000000 / 23265799217) ≤ (52576119 / 40000000) := by
  have h := checkLog_sound (w := (10765799217 / 35765799217)) (n := 12)
    (lo := (621255793 / 1000000000)) (hi := (310627897 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((23265799217 / 12500000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(23265799217 / 12500000000) = 1/(6250000000 / 23265799217) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14587 : Bounds (1314402973 / 1000000000) (52576119 / 40000000) (Real.log (23265799217 / 6250000000)) := by
  have h := reflection_log_14587_neg
  have he : Real.log (23265799217 / 6250000000) = -Real.log (6250000000 / 23265799217) := by
    rw [show ((23265799217 / 6250000000) : ℝ) = ((6250000000 / 23265799217) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14588_neg : (1325739349 / 1000000000) ≤ -Real.log (125000000000 / 470620994449) ∧
    -Real.log (125000000000 / 470620994449) ≤ (1325739351 / 1000000000) := by
  have h := checkLog_sound (w := (220620994449 / 720620994449)) (n := 12)
    (lo := (632592169 / 1000000000)) (hi := (63259217 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((470620994449 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(470620994449 / 250000000000) = 1/(125000000000 / 470620994449) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14588 : Bounds (1325739349 / 1000000000) (1325739351 / 1000000000) (Real.log (470620994449 / 125000000000)) := by
  have h := reflection_log_14588_neg
  have he : Real.log (470620994449 / 125000000000) = -Real.log (125000000000 / 470620994449) := by
    rw [show ((470620994449 / 125000000000) : ℝ) = ((125000000000 / 470620994449) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14589_neg : (3393475333 / 1000000000) ≤ -Real.log (100000000000 / 2976923076923) ∧
    -Real.log (100000000000 / 2976923076923) ≤ (1696737669 / 500000000) := by
  have h := checkLog_sound (w := (1376923076923 / 4576923076923)) (n := 12)
    (lo := (620886613 / 1000000000)) (hi := (310443307 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2976923076923 / 1600000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(2976923076923 / 1600000000000) = 1/(100000000000 / 2976923076923) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14589 : Bounds (3393475333 / 1000000000) (1696737669 / 500000000) (Real.log (2976923076923 / 100000000000)) := by
  have h := reflection_log_14589_neg
  have he : Real.log (2976923076923 / 100000000000) = -Real.log (100000000000 / 2976923076923) := by
    rw [show ((2976923076923 / 100000000000) : ℝ) = ((100000000000 / 2976923076923) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14590_neg : (688455481 / 200000000) ≤ -Real.log (100000000000 / 3125806451613) ∧
    -Real.log (100000000000 / 3125806451613) ≤ (344227741 / 100000000) := by
  have h := checkLog_sound (w := (1525806451613 / 4725806451613)) (n := 12)
    (lo := (133937737 / 200000000)) (hi := (334844343 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3125806451613 / 1600000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3125806451613 / 1600000000000) = 1/(100000000000 / 3125806451613) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14590 : Bounds (688455481 / 200000000) (344227741 / 100000000) (Real.log (3125806451613 / 100000000000)) := by
  have h := reflection_log_14590_neg
  have he : Real.log (3125806451613 / 100000000000) = -Real.log (100000000000 / 3125806451613) := by
    rw [show ((3125806451613 / 100000000000) : ℝ) = ((100000000000 / 3125806451613) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14591_neg : (82900413 / 125000000) ≤ -Real.log (1000 / 1941) ∧
    -Real.log (1000 / 1941) ≤ (132640661 / 200000000) := by
  have h := checkLog_sound (w := (941 / 2941)) (n := 12)
    (lo := (82900413 / 125000000)) (hi := (132640661 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1941 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1941 / 1000) = 1/(1000 / 1941) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14591 : Bounds (82900413 / 125000000) (132640661 / 200000000) (Real.log (1941 / 1000)) := by
  have h := reflection_log_14591_neg
  have he : Real.log (1941 / 1000) = -Real.log (1000 / 1941) := by
    rw [show ((1941 / 1000) : ℝ) = ((1000 / 1941) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily
