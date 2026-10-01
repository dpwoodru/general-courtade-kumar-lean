import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_15680_neg : (556601923 / 1000000000) ≤ -Real.log (22926135111 / 40000000000) ∧
    -Real.log (22926135111 / 40000000000) ≤ (139150481 / 250000000) := by
  have h := checkLog_sound (w := (17073864889 / 62926135111)) (n := 12)
    (lo := (556601923 / 1000000000)) (hi := (139150481 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 22926135111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 22926135111) = 1/(22926135111 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15680 : Bounds (-139150481 / 250000000) (-556601923 / 1000000000) (Real.log (22926135111 / 40000000000)) := by
  have h := reflection_log_15680_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15681_neg : (138599219 / 250000000) ≤ -Real.log (143604650511 / 250000000000) ∧
    -Real.log (143604650511 / 250000000000) ≤ (554396877 / 1000000000) := by
  have h := checkLog_sound (w := (106395349489 / 393604650511)) (n := 12)
    (lo := (138599219 / 250000000)) (hi := (554396877 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 143604650511) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 143604650511) = 1/(143604650511 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15681 : Bounds (-554396877 / 1000000000) (-138599219 / 250000000) (Real.log (143604650511 / 250000000000)) := by
  have h := reflection_log_15681_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15682_neg : (62352531 / 40000000) ≤ -Real.log (125000000000 / 594147149013) ∧
    -Real.log (125000000000 / 594147149013) ≤ (779406639 / 500000000) := by
  have h := checkLog_sound (w := (94147149013 / 1094147149013)) (n := 12)
    (lo := (34503783 / 200000000)) (hi := (43129729 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((594147149013 / 500000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(594147149013 / 500000000000) = 1/(125000000000 / 594147149013) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15682 : Bounds (62352531 / 40000000) (779406639 / 500000000) (Real.log (594147149013 / 125000000000)) := by
  have h := reflection_log_15682_neg
  have he : Real.log (594147149013 / 125000000000) = -Real.log (125000000000 / 594147149013) := by
    rw [show ((594147149013 / 125000000000) : ℝ) = ((125000000000 / 594147149013) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15683_neg : (781095421 / 500000000) ≤ -Real.log (250000000000 / 1192314626513) ∧
    -Real.log (250000000000 / 1192314626513) ≤ (312438169 / 200000000) := by
  have h := checkLog_sound (w := (192314626513 / 2192314626513)) (n := 12)
    (lo := (87948241 / 500000000)) (hi := (175896483 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1192314626513 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1192314626513 / 1000000000000) = 1/(250000000000 / 1192314626513) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15683 : Bounds (781095421 / 500000000) (312438169 / 200000000) (Real.log (1192314626513 / 250000000000)) := by
  have h := reflection_log_15683_neg
  have he : Real.log (1192314626513 / 250000000000) = -Real.log (250000000000 / 1192314626513) := by
    rw [show ((1192314626513 / 250000000000) : ℝ) = ((250000000000 / 1192314626513) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15684_neg : (6500789039 / 1000000000) ≤ -Real.log (250000000000 / 166416666666667) ∧
    -Real.log (250000000000 / 166416666666667) ≤ (6500789049 / 1000000000) := by
  have h := checkLog_sound (w := (38416666666667 / 294416666666667)) (n := 12)
    (lo := (262464419 / 1000000000)) (hi := (13123221 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((166416666666667 / 128000000000000) : ℝ) 9 (by norm_num)
  have hq : (2 : ℝ)^9*(166416666666667 / 128000000000000) = 1/(250000000000 / 166416666666667) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15684 : Bounds (6500789039 / 1000000000) (6500789049 / 1000000000) (Real.log (166416666666667 / 250000000000)) := by
  have h := reflection_log_15684_neg
  have he : Real.log (166416666666667 / 250000000000) = -Real.log (250000000000 / 166416666666667) := by
    rw [show ((166416666666667 / 250000000000) : ℝ) = ((250000000000 / 166416666666667) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15685_neg : (691746199 / 1000000000) ≤ -Real.log (2500 / 4993) ∧
    -Real.log (2500 / 4993) ≤ (3458731 / 5000000) := by
  have h := checkLog_sound (w := (2493 / 7493)) (n := 12)
    (lo := (691746199 / 1000000000)) (hi := (3458731 / 5000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4993 / 2500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4993 / 2500) = 1/(2500 / 4993) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15685 : Bounds (691746199 / 1000000000) (3458731 / 5000000) (Real.log (4993 / 2500)) := by
  have h := reflection_log_15685_neg
  have he : Real.log (4993 / 2500) = -Real.log (2500 / 4993) := by
    rw [show ((4993 / 2500) : ℝ) = ((2500 / 4993) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15686_neg : (5878135857 / 1000000000) ≤ -Real.log (7 / 2500) ∧
    -Real.log (7 / 2500) ≤ (2939067933 / 500000000) := by
  have h := checkLog_sound (w := (177 / 1073)) (n := 12)
    (lo := (332958417 / 1000000000)) (hi := (166479209 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625 / 448) : ℝ) 8 (by norm_num)
  have hq : (2 : ℝ)^8*(625 / 448) = 1/(7 / 2500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15686 : Bounds (-2939067933 / 500000000) (-5878135857 / 1000000000) (Real.log (7 / 2500)) := by
  have h := reflection_log_15686_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15687_neg : (996703 / 1000000000) ≤ -Real.log (2500000 / 2502493) ∧
    -Real.log (2500000 / 2502493) ≤ (31147 / 31250000) := by
  have h := checkLog_sound (w := (2493 / 5002493)) (n := 12)
    (lo := (996703 / 1000000000)) (hi := (31147 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2502493 / 2500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2502493 / 2500000) = 1/(2500000 / 2502493) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15687 : Bounds (996703 / 1000000000) (31147 / 31250000) (Real.log (2502493 / 2500000)) := by
  have h := reflection_log_15687_neg
  have he : Real.log (2502493 / 2500000) = -Real.log (2500000 / 2502493) := by
    rw [show ((2502493 / 2500000) : ℝ) = ((2500000 / 2502493) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15688_neg : (997697 / 1000000000) ≤ -Real.log (2497507 / 2500000) ∧
    -Real.log (2497507 / 2500000) ≤ (498849 / 500000000) := by
  have h := checkLog_sound (w := (2493 / 4997507)) (n := 12)
    (lo := (997697 / 1000000000)) (hi := (498849 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000 / 2497507) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000 / 2497507) = 1/(2497507 / 2500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15688 : Bounds (-498849 / 500000000) (-997697 / 1000000000) (Real.log (2497507 / 2500000)) := by
  have h := reflection_log_15688_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15689_neg : (25120909 / 50000000) ≤ -Real.log (1000000 / 1652713) ∧
    -Real.log (1000000 / 1652713) ≤ (502418181 / 1000000000) := by
  have h := checkLog_sound (w := (652713 / 2652713)) (n := 12)
    (lo := (25120909 / 50000000)) (hi := (502418181 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1652713 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1652713 / 1000000) = 1/(1000000 / 1652713) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15689 : Bounds (25120909 / 50000000) (502418181 / 1000000000) (Real.log (1652713 / 1000000)) := by
  have h := reflection_log_15689_neg
  have he : Real.log (1652713 / 1000000) = -Real.log (1000000 / 1652713) := by
    rw [show ((1652713 / 1000000) : ℝ) = ((1000000 / 1652713) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15690_neg : (846083 / 800000) ≤ -Real.log (347287 / 1000000) ∧
    -Real.log (347287 / 1000000) ≤ (132200469 / 125000000) := by
  have h := checkLog_sound (w := (152713 / 847287)) (n := 12)
    (lo := (36445657 / 100000000)) (hi := (364456571 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 347287) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 347287) = 1/(347287 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15690 : Bounds (-132200469 / 125000000) (-846083 / 800000) (Real.log (347287 / 1000000)) := by
  have h := reflection_log_15690_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15691_neg : (503006131 / 1000000000) ≤ -Real.log (200000 / 330737) ∧
    -Real.log (200000 / 330737) ≤ (125751533 / 250000000) := by
  have h := checkLog_sound (w := (130737 / 530737)) (n := 12)
    (lo := (503006131 / 1000000000)) (hi := (125751533 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((330737 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(330737 / 200000) = 1/(200000 / 330737) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15691 : Bounds (503006131 / 1000000000) (125751533 / 250000000) (Real.log (330737 / 200000)) := by
  have h := reflection_log_15691_neg
  have he : Real.log (330737 / 200000) = -Real.log (200000 / 330737) := by
    rw [show ((330737 / 200000) : ℝ) = ((200000 / 330737) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15692_neg : (66275407 / 62500000) ≤ -Real.log (69263 / 200000) ∧
    -Real.log (69263 / 200000) ≤ (530203257 / 500000000) := by
  have h := checkLog_sound (w := (30737 / 169263)) (n := 12)
    (lo := (91814833 / 250000000)) (hi := (367259333 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 69263) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(100000 / 69263) = 1/(69263 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15692 : Bounds (-530203257 / 500000000) (-66275407 / 62500000) (Real.log (69263 / 200000)) := by
  have h := reflection_log_15692_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15693_neg : (278700191 / 500000000) ≤ -Real.log (22907836831 / 40000000000) ∧
    -Real.log (22907836831 / 40000000000) ≤ (557400383 / 1000000000) := by
  have h := checkLog_sound (w := (17092163169 / 62907836831)) (n := 12)
    (lo := (278700191 / 500000000)) (hi := (557400383 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 22907836831) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 22907836831) = 1/(22907836831 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15693 : Bounds (-557400383 / 1000000000) (-278700191 / 500000000) (Real.log (22907836831 / 40000000000)) := by
  have h := reflection_log_15693_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15694_neg : (555185571 / 1000000000) ≤ -Real.log (573965739631 / 1000000000000) ∧
    -Real.log (573965739631 / 1000000000000) ≤ (138796393 / 250000000) := by
  have h := checkLog_sound (w := (426034260369 / 1573965739631)) (n := 12)
    (lo := (555185571 / 1000000000)) (hi := (138796393 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 573965739631) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 573965739631) = 1/(573965739631 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15694 : Bounds (-138796393 / 250000000) (-555185571 / 1000000000) (Real.log (573965739631 / 1000000000000)) := by
  have h := reflection_log_15694_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15695_neg : (156002193 / 100000000) ≤ -Real.log (250000000000 / 1189731403709) ∧
    -Real.log (250000000000 / 1189731403709) ≤ (1560021933 / 1000000000) := by
  have h := checkLog_sound (w := (189731403709 / 2189731403709)) (n := 12)
    (lo := (17372757 / 100000000)) (hi := (173727571 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1189731403709 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1189731403709 / 1000000000000) = 1/(250000000000 / 1189731403709) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15695 : Bounds (156002193 / 100000000) (1560021933 / 1000000000) (Real.log (1189731403709 / 250000000000)) := by
  have h := reflection_log_15695_neg
  have he : Real.log (1189731403709 / 250000000000) = -Real.log (250000000000 / 1189731403709) := by
    rw [show ((1189731403709 / 250000000000) : ℝ) = ((250000000000 / 1189731403709) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15696_neg : (1563412643 / 1000000000) ≤ -Real.log (50000000000 / 238754457647) ∧
    -Real.log (50000000000 / 238754457647) ≤ (781706323 / 500000000) := by
  have h := checkLog_sound (w := (38754457647 / 438754457647)) (n := 12)
    (lo := (177118283 / 1000000000)) (hi := (44279571 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((238754457647 / 200000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(238754457647 / 200000000000) = 1/(50000000000 / 238754457647) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15696 : Bounds (1563412643 / 1000000000) (781706323 / 500000000) (Real.log (238754457647 / 50000000000)) := by
  have h := reflection_log_15696_neg
  have he : Real.log (238754457647 / 50000000000) = -Real.log (50000000000 / 238754457647) := by
    rw [show ((238754457647 / 50000000000) : ℝ) = ((50000000000 / 238754457647) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15697_neg : (6500789039 / 1000000000) ≤ -Real.log (500000000000 / 332833333333333) ∧
    -Real.log (500000000000 / 332833333333333) ≤ (6500789049 / 1000000000) := by
  have h := checkLog_sound (w := (76833333333333 / 588833333333333)) (n := 12)
    (lo := (262464419 / 1000000000)) (hi := (13123221 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((332833333333333 / 256000000000000) : ℝ) 9 (by norm_num)
  have hq : (2 : ℝ)^9*(332833333333333 / 256000000000000) = 1/(500000000000 / 332833333333333) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15697 : Bounds (6500789039 / 1000000000) (6500789049 / 1000000000) (Real.log (332833333333333 / 500000000000)) := by
  have h := reflection_log_15697_neg
  have he : Real.log (332833333333333 / 500000000000) = -Real.log (500000000000 / 332833333333333) := by
    rw [show ((332833333333333 / 500000000000) : ℝ) = ((500000000000 / 332833333333333) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15698_neg : (821235257 / 125000000) ≤ -Real.log (250000000000 / 178321428571429) ∧
    -Real.log (250000000000 / 178321428571429) ≤ (3284941033 / 500000000) := by
  have h := checkLog_sound (w := (50321428571429 / 306321428571429)) (n := 12)
    (lo := (82889359 / 250000000)) (hi := (331557437 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((178321428571429 / 128000000000000) : ℝ) 9 (by norm_num)
  have hq : (2 : ℝ)^9*(178321428571429 / 128000000000000) = 1/(250000000000 / 178321428571429) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15698 : Bounds (821235257 / 125000000) (3284941033 / 500000000) (Real.log (178321428571429 / 250000000000)) := by
  have h := reflection_log_15698_neg
  have he : Real.log (178321428571429 / 250000000000) = -Real.log (250000000000 / 178321428571429) := by
    rw [show ((178321428571429 / 250000000000) : ℝ) = ((250000000000 / 178321428571429) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15699_neg : (345923167 / 500000000) ≤ -Real.log (5000 / 9987) ∧
    -Real.log (5000 / 9987) ≤ (138369267 / 200000000) := by
  have h := checkLog_sound (w := (4987 / 14987)) (n := 12)
    (lo := (345923167 / 500000000)) (hi := (138369267 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9987 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(9987 / 5000) = 1/(5000 / 9987) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15699 : Bounds (345923167 / 500000000) (138369267 / 200000000) (Real.log (9987 / 5000)) := by
  have h := reflection_log_15699_neg
  have he : Real.log (9987 / 5000) = -Real.log (5000 / 9987) := by
    rw [show ((9987 / 5000) : ℝ) = ((5000 / 9987) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15700_neg : (5952243829 / 1000000000) ≤ -Real.log (13 / 5000) ∧
    -Real.log (13 / 5000) ≤ (2976121919 / 500000000) := by
  have h := checkLog_sound (w := (209 / 1041)) (n := 12)
    (lo := (407066389 / 1000000000)) (hi := (40706639 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625 / 416) : ℝ) 8 (by norm_num)
  have hq : (2 : ℝ)^8*(625 / 416) = 1/(13 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15700 : Bounds (-2976121919 / 500000000) (-5952243829 / 1000000000) (Real.log (13 / 5000)) := by
  have h := reflection_log_15700_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15701_neg : (498451 / 500000000) ≤ -Real.log (5000000 / 5004987) ∧
    -Real.log (5000000 / 5004987) ≤ (996903 / 1000000000) := by
  have h := checkLog_sound (w := (4987 / 10004987)) (n := 12)
    (lo := (498451 / 500000000)) (hi := (996903 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5004987 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5004987 / 5000000) = 1/(5000000 / 5004987) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15701 : Bounds (498451 / 500000000) (996903 / 1000000000) (Real.log (5004987 / 5000000)) := by
  have h := reflection_log_15701_neg
  have he : Real.log (5004987 / 5000000) = -Real.log (5000000 / 5004987) := by
    rw [show ((5004987 / 5000000) : ℝ) = ((5000000 / 5004987) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15702_neg : (997897 / 1000000000) ≤ -Real.log (4995013 / 5000000) ∧
    -Real.log (4995013 / 5000000) ≤ (498949 / 500000000) := by
  have h := checkLog_sound (w := (4987 / 9995013)) (n := 12)
    (lo := (997897 / 1000000000)) (hi := (498949 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4995013) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4995013) = 1/(4995013 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15702 : Bounds (-498949 / 500000000) (-997897 / 1000000000) (Real.log (4995013 / 5000000)) := by
  have h := reflection_log_15702_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15703_neg : (50262993 / 100000000) ≤ -Real.log (1000000 / 1653063) ∧
    -Real.log (1000000 / 1653063) ≤ (502629931 / 1000000000) := by
  have h := checkLog_sound (w := (653063 / 2653063)) (n := 12)
    (lo := (50262993 / 100000000)) (hi := (502629931 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1653063 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1653063 / 1000000) = 1/(1000000 / 1653063) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15703 : Bounds (50262993 / 100000000) (502629931 / 1000000000) (Real.log (1653063 / 1000000)) := by
  have h := reflection_log_15703_neg
  have he : Real.log (1653063 / 1000000) = -Real.log (1000000 / 1653063) := by
    rw [show ((1653063 / 1000000) : ℝ) = ((1000000 / 1653063) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15704_neg : (1058612071 / 1000000000) ≤ -Real.log (346937 / 1000000) ∧
    -Real.log (346937 / 1000000) ≤ (1058612073 / 1000000000) := by
  have h := checkLog_sound (w := (153063 / 846937)) (n := 12)
    (lo := (365464891 / 1000000000)) (hi := (91366223 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 346937) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 346937) = 1/(346937 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15704 : Bounds (-1058612073 / 1000000000) (-1058612071 / 1000000000) (Real.log (346937 / 1000000)) := by
  have h := reflection_log_15704_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15705_neg : (50321957 / 100000000) ≤ -Real.log (500000 / 827019) ∧
    -Real.log (500000 / 827019) ≤ (503219571 / 1000000000) := by
  have h := checkLog_sound (w := (327019 / 1327019)) (n := 12)
    (lo := (50321957 / 100000000)) (hi := (503219571 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((827019 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(827019 / 500000) = 1/(500000 / 827019) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15705 : Bounds (50321957 / 100000000) (503219571 / 1000000000) (Real.log (827019 / 500000)) := by
  have h := reflection_log_15705_neg
  have he : Real.log (827019 / 500000) = -Real.log (500000 / 827019) := by
    rw [show ((827019 / 500000) : ℝ) = ((500000 / 827019) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15706_neg : (212285267 / 200000000) ≤ -Real.log (172981 / 500000) ∧
    -Real.log (172981 / 500000) ≤ (1061426337 / 1000000000) := by
  have h := checkLog_sound (w := (77019 / 422981)) (n := 12)
    (lo := (73655831 / 200000000)) (hi := (92069789 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 172981) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 172981) = 1/(172981 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15706 : Bounds (-1061426337 / 1000000000) (-212285267 / 200000000) (Real.log (172981 / 500000)) := by
  have h := reflection_log_15706_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15707_neg : (111641353 / 200000000) ≤ -Real.log (143058573639 / 250000000000) ∧
    -Real.log (143058573639 / 250000000000) ≤ (279103383 / 500000000) := by
  have h := checkLog_sound (w := (106941426361 / 393058573639)) (n := 12)
    (lo := (111641353 / 200000000)) (hi := (279103383 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 143058573639) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 143058573639) = 1/(143058573639 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15707 : Bounds (-279103383 / 500000000) (-111641353 / 200000000) (Real.log (143058573639 / 250000000000)) := by
  have h := reflection_log_15707_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15708_neg : (555982141 / 1000000000) ≤ -Real.log (573508718031 / 1000000000000) ∧
    -Real.log (573508718031 / 1000000000000) ≤ (277991071 / 500000000) := by
  have h := checkLog_sound (w := (426491281969 / 1573508718031)) (n := 12)
    (lo := (555982141 / 1000000000)) (hi := (277991071 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 573508718031) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 573508718031) = 1/(573508718031 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15708 : Bounds (-277991071 / 500000000) (-555982141 / 1000000000) (Real.log (573508718031 / 1000000000000)) := by
  have h := reflection_log_15708_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15709_neg : (1561242001 / 1000000000) ≤ -Real.log (500000000000 / 2382367692117) ∧
    -Real.log (500000000000 / 2382367692117) ≤ (390310501 / 250000000) := by
  have h := checkLog_sound (w := (382367692117 / 4382367692117)) (n := 12)
    (lo := (174947641 / 1000000000)) (hi := (87473821 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2382367692117 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2382367692117 / 2000000000000) = 1/(500000000000 / 2382367692117) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15709 : Bounds (1561242001 / 1000000000) (390310501 / 250000000) (Real.log (2382367692117 / 500000000000)) := by
  have h := reflection_log_15709_neg
  have he : Real.log (2382367692117 / 500000000000) = -Real.log (500000000000 / 2382367692117) := by
    rw [show ((2382367692117 / 500000000000) : ℝ) = ((500000000000 / 2382367692117) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15710_neg : (782322953 / 500000000) ≤ -Real.log (500000000000 / 2390490863159) ∧
    -Real.log (500000000000 / 2390490863159) ≤ (1564645909 / 1000000000) := by
  have h := checkLog_sound (w := (390490863159 / 4390490863159)) (n := 12)
    (lo := (89175773 / 500000000)) (hi := (178351547 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2390490863159 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2390490863159 / 2000000000000) = 1/(500000000000 / 2390490863159) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15710 : Bounds (782322953 / 500000000) (1564645909 / 1000000000) (Real.log (2390490863159 / 500000000000)) := by
  have h := reflection_log_15710_neg
  have he : Real.log (2390490863159 / 500000000000) = -Real.log (500000000000 / 2390490863159) := by
    rw [show ((2390490863159 / 500000000000) : ℝ) = ((500000000000 / 2390490863159) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15711_neg : (821235257 / 125000000) ≤ -Real.log (500000000000 / 356642857142857) ∧
    -Real.log (500000000000 / 356642857142857) ≤ (3284941033 / 500000000) := by
  have h := checkLog_sound (w := (100642857142857 / 612642857142857)) (n := 12)
    (lo := (82889359 / 250000000)) (hi := (331557437 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((356642857142857 / 256000000000000) : ℝ) 9 (by norm_num)
  have hq : (2 : ℝ)^9*(356642857142857 / 256000000000000) = 1/(500000000000 / 356642857142857) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15711 : Bounds (821235257 / 125000000) (3284941033 / 500000000) (Real.log (356642857142857 / 500000000000)) := by
  have h := reflection_log_15711_neg
  have he : Real.log (356642857142857 / 500000000000) = -Real.log (500000000000 / 356642857142857) := by
    rw [show ((356642857142857 / 500000000000) : ℝ) = ((500000000000 / 356642857142857) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15712_neg : (6644090163 / 1000000000) ≤ -Real.log (100000000000 / 76823076923077) ∧
    -Real.log (100000000000 / 76823076923077) ≤ (6644090173 / 1000000000) := by
  have h := checkLog_sound (w := (25623076923077 / 128023076923077)) (n := 12)
    (lo := (405765543 / 1000000000)) (hi := (50720693 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((76823076923077 / 51200000000000) : ℝ) 9 (by norm_num)
  have hq : (2 : ℝ)^9*(76823076923077 / 51200000000000) = 1/(100000000000 / 76823076923077) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15712 : Bounds (6644090163 / 1000000000) (6644090173 / 1000000000) (Real.log (76823076923077 / 100000000000)) := by
  have h := reflection_log_15712_neg
  have he : Real.log (76823076923077 / 100000000000) = -Real.log (100000000000 / 76823076923077) := by
    rw [show ((76823076923077 / 100000000000) : ℝ) = ((100000000000 / 76823076923077) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15713_neg : (691946459 / 1000000000) ≤ -Real.log (1250 / 2497) ∧
    -Real.log (1250 / 2497) ≤ (34597323 / 50000000) := by
  have h := checkLog_sound (w := (1247 / 3747)) (n := 12)
    (lo := (691946459 / 1000000000)) (hi := (34597323 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2497 / 1250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2497 / 1250) = 1/(1250 / 2497) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15713 : Bounds (691946459 / 1000000000) (34597323 / 50000000) (Real.log (2497 / 1250)) := by
  have h := reflection_log_15713_neg
  have he : Real.log (2497 / 1250) = -Real.log (1250 / 2497) := by
    rw [show ((2497 / 1250) : ℝ) = ((1250 / 2497) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15714_neg : (6032286537 / 1000000000) ≤ -Real.log (3 / 1250) ∧
    -Real.log (3 / 1250) ≤ (3016143273 / 500000000) := by
  have h := checkLog_sound (w := (241 / 1009)) (n := 12)
    (lo := (487109097 / 1000000000)) (hi := (243554549 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625 / 384) : ℝ) 8 (by norm_num)
  have hq : (2 : ℝ)^8*(625 / 384) = 1/(3 / 1250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15714 : Bounds (-3016143273 / 500000000) (-6032286537 / 1000000000) (Real.log (3 / 1250)) := by
  have h := reflection_log_15714_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15715_neg : (498551 / 500000000) ≤ -Real.log (1250000 / 1251247) ∧
    -Real.log (1250000 / 1251247) ≤ (997103 / 1000000000) := by
  have h := checkLog_sound (w := (1247 / 2501247)) (n := 12)
    (lo := (498551 / 500000000)) (hi := (997103 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1251247 / 1250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1251247 / 1250000) = 1/(1250000 / 1251247) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15715 : Bounds (498551 / 500000000) (997103 / 1000000000) (Real.log (1251247 / 1250000)) := by
  have h := reflection_log_15715_neg
  have he : Real.log (1251247 / 1250000) = -Real.log (1250000 / 1251247) := by
    rw [show ((1251247 / 1250000) : ℝ) = ((1250000 / 1251247) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15716_neg : (998097 / 1000000000) ≤ -Real.log (1248753 / 1250000) ∧
    -Real.log (1248753 / 1250000) ≤ (499049 / 500000000) := by
  have h := checkLog_sound (w := (1247 / 2498753)) (n := 12)
    (lo := (998097 / 1000000000)) (hi := (499049 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250000 / 1248753) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1250000 / 1248753) = 1/(1248753 / 1250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15716 : Bounds (-499049 / 500000000) (-998097 / 1000000000) (Real.log (1248753 / 1250000)) := by
  have h := reflection_log_15716_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15717_neg : (100568811 / 200000000) ≤ -Real.log (1000000 / 1653417) ∧
    -Real.log (1000000 / 1653417) ≤ (62855507 / 125000000) := by
  have h := checkLog_sound (w := (653417 / 2653417)) (n := 12)
    (lo := (100568811 / 200000000)) (hi := (62855507 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1653417 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1653417 / 1000000) = 1/(1000000 / 1653417) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15717 : Bounds (100568811 / 200000000) (62855507 / 125000000) (Real.log (1653417 / 1000000)) := by
  have h := reflection_log_15717_neg
  have he : Real.log (1653417 / 1000000) = -Real.log (1000000 / 1653417) := by
    rw [show ((1653417 / 1000000) : ℝ) = ((1000000 / 1653417) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15718_neg : (21192659 / 20000000) ≤ -Real.log (346583 / 1000000) ∧
    -Real.log (346583 / 1000000) ≤ (132454119 / 125000000) := by
  have h := checkLog_sound (w := (153417 / 846583)) (n := 12)
    (lo := (36648577 / 100000000)) (hi := (366485771 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 346583) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 346583) = 1/(346583 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15718 : Bounds (-132454119 / 125000000) (-21192659 / 20000000) (Real.log (346583 / 1000000)) := by
  have h := reflection_log_15718_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15719_neg : (503435383 / 1000000000) ≤ -Real.log (200000 / 330879) ∧
    -Real.log (200000 / 330879) ≤ (62929423 / 125000000) := by
  have h := checkLog_sound (w := (130879 / 530879)) (n := 12)
    (lo := (503435383 / 1000000000)) (hi := (62929423 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((330879 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(330879 / 200000) = 1/(200000 / 330879) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15719 : Bounds (503435383 / 1000000000) (62929423 / 125000000) (Real.log (330879 / 200000)) := by
  have h := reflection_log_15719_neg
  have he : Real.log (330879 / 200000) = -Real.log (200000 / 330879) := by
    rw [show ((330879 / 200000) : ℝ) = ((200000 / 330879) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15720_neg : (531229387 / 500000000) ≤ -Real.log (69121 / 200000) ∧
    -Real.log (69121 / 200000) ≤ (132807347 / 125000000) := by
  have h := checkLog_sound (w := (30879 / 169121)) (n := 12)
    (lo := (184655797 / 500000000)) (hi := (73862319 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 69121) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(100000 / 69121) = 1/(69121 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15720 : Bounds (-132807347 / 125000000) (-531229387 / 500000000) (Real.log (69121 / 200000)) := by
  have h := reflection_log_15720_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15721_neg : (559023391 / 1000000000) ≤ -Real.log (22870687359 / 40000000000) ∧
    -Real.log (22870687359 / 40000000000) ≤ (17469481 / 31250000) := by
  have h := checkLog_sound (w := (17129312641 / 62870687359)) (n := 12)
    (lo := (559023391 / 1000000000)) (hi := (17469481 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 22870687359) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 22870687359) = 1/(22870687359 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15721 : Bounds (-17469481 / 31250000) (-559023391 / 1000000000) (Real.log (22870687359 / 40000000000)) := by
  have h := reflection_log_15721_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15722_neg : (111357779 / 200000000) ≤ -Real.log (573046224111 / 1000000000000) ∧
    -Real.log (573046224111 / 1000000000000) ≤ (17399653 / 31250000) := by
  have h := checkLog_sound (w := (426953775889 / 1573046224111)) (n := 12)
    (lo := (111357779 / 200000000)) (hi := (17399653 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 573046224111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 573046224111) = 1/(573046224111 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15722 : Bounds (-17399653 / 31250000) (-111357779 / 200000000) (Real.log (573046224111 / 1000000000000)) := by
  have h := reflection_log_15722_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15723_neg : (312495401 / 200000000) ≤ -Real.log (500000000000 / 2385311743507) ∧
    -Real.log (500000000000 / 2385311743507) ≤ (97654813 / 62500000) := by
  have h := checkLog_sound (w := (385311743507 / 4385311743507)) (n := 12)
    (lo := (35236529 / 200000000)) (hi := (88091323 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2385311743507 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2385311743507 / 2000000000000) = 1/(500000000000 / 2385311743507) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15723 : Bounds (312495401 / 200000000) (97654813 / 62500000) (Real.log (2385311743507 / 500000000000)) := by
  have h := reflection_log_15723_neg
  have he : Real.log (2385311743507 / 500000000000) = -Real.log (500000000000 / 2385311743507) := by
    rw [show ((2385311743507 / 500000000000) : ℝ) = ((500000000000 / 2385311743507) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15724_neg : (391473539 / 250000000) ≤ -Real.log (250000000000 / 1196738328439) ∧
    -Real.log (250000000000 / 1196738328439) ≤ (1565894159 / 1000000000) := by
  have h := checkLog_sound (w := (196738328439 / 2196738328439)) (n := 12)
    (lo := (44899949 / 250000000)) (hi := (179599797 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1196738328439 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1196738328439 / 1000000000000) = 1/(250000000000 / 1196738328439) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15724 : Bounds (391473539 / 250000000) (1565894159 / 1000000000) (Real.log (1196738328439 / 250000000000)) := by
  have h := reflection_log_15724_neg
  have he : Real.log (1196738328439 / 250000000000) = -Real.log (250000000000 / 1196738328439) := by
    rw [show ((1196738328439 / 250000000000) : ℝ) = ((250000000000 / 1196738328439) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15725_neg : (6644090163 / 1000000000) ≤ -Real.log (62500000000 / 48014423076923) ∧
    -Real.log (62500000000 / 48014423076923) ≤ (6644090173 / 1000000000) := by
  have h := checkLog_sound (w := (16014423076923 / 80014423076923)) (n := 12)
    (lo := (405765543 / 1000000000)) (hi := (50720693 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((48014423076923 / 32000000000000) : ℝ) 9 (by norm_num)
  have hq : (2 : ℝ)^9*(48014423076923 / 32000000000000) = 1/(62500000000 / 48014423076923) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15725 : Bounds (6644090163 / 1000000000) (6644090173 / 1000000000) (Real.log (48014423076923 / 62500000000)) := by
  have h := reflection_log_15725_neg
  have he : Real.log (48014423076923 / 62500000000) = -Real.log (62500000000 / 48014423076923) := by
    rw [show ((48014423076923 / 62500000000) : ℝ) = ((62500000000 / 48014423076923) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15726_neg : (1681058249 / 250000000) ≤ -Real.log (500000000000 / 416166666666667) ∧
    -Real.log (500000000000 / 416166666666667) ≤ (3362116503 / 500000000) := by
  have h := checkLog_sound (w := (160166666666667 / 672166666666667)) (n := 12)
    (lo := (60738547 / 125000000)) (hi := (485908377 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((416166666666667 / 256000000000000) : ℝ) 9 (by norm_num)
  have hq : (2 : ℝ)^9*(416166666666667 / 256000000000000) = 1/(500000000000 / 416166666666667) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15726 : Bounds (1681058249 / 250000000) (3362116503 / 500000000) (Real.log (416166666666667 / 500000000000)) := by
  have h := reflection_log_15726_neg
  have he : Real.log (416166666666667 / 500000000000) = -Real.log (500000000000 / 416166666666667) := by
    rw [show ((416166666666667 / 500000000000) : ℝ) = ((500000000000 / 416166666666667) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15727_neg : (27681863 / 40000000) ≤ -Real.log (5000 / 9989) ∧
    -Real.log (5000 / 9989) ≤ (43252911 / 62500000) := by
  have h := checkLog_sound (w := (4989 / 14989)) (n := 12)
    (lo := (27681863 / 40000000)) (hi := (43252911 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9989 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(9989 / 5000) = 1/(5000 / 9989) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15727 : Bounds (27681863 / 40000000) (43252911 / 62500000) (Real.log (9989 / 5000)) := by
  have h := reflection_log_15727_neg
  have he : Real.log (9989 / 5000) = -Real.log (5000 / 9989) := by
    rw [show ((9989 / 5000) : ℝ) = ((5000 / 9989) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15728_neg : (3059648957 / 500000000) ≤ -Real.log (11 / 5000) ∧
    -Real.log (11 / 5000) ≤ (6119297923 / 1000000000) := by
  have h := checkLog_sound (w := (273 / 977)) (n := 12)
    (lo := (287060237 / 500000000)) (hi := (22964819 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625 / 352) : ℝ) 8 (by norm_num)
  have hq : (2 : ℝ)^8*(625 / 352) = 1/(11 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15728 : Bounds (-6119297923 / 1000000000) (-3059648957 / 500000000) (Real.log (11 / 5000)) := by
  have h := reflection_log_15728_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15729_neg : (498651 / 500000000) ≤ -Real.log (5000000 / 5004989) ∧
    -Real.log (5000000 / 5004989) ≤ (997303 / 1000000000) := by
  have h := checkLog_sound (w := (4989 / 10004989)) (n := 12)
    (lo := (498651 / 500000000)) (hi := (997303 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5004989 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5004989 / 5000000) = 1/(5000000 / 5004989) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15729 : Bounds (498651 / 500000000) (997303 / 1000000000) (Real.log (5004989 / 5000000)) := by
  have h := reflection_log_15729_neg
  have he : Real.log (5004989 / 5000000) = -Real.log (5000000 / 5004989) := by
    rw [show ((5004989 / 5000000) : ℝ) = ((5000000 / 5004989) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15730_neg : (499149 / 500000000) ≤ -Real.log (4995011 / 5000000) ∧
    -Real.log (4995011 / 5000000) ≤ (998299 / 1000000000) := by
  have h := checkLog_sound (w := (4989 / 9995011)) (n := 12)
    (lo := (499149 / 500000000)) (hi := (998299 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4995011) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4995011) = 1/(4995011 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15730 : Bounds (-998299 / 1000000000) (-499149 / 500000000) (Real.log (4995011 / 5000000)) := by
  have h := reflection_log_15730_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15731_neg : (125764987 / 250000000) ≤ -Real.log (500000 / 826887) ∧
    -Real.log (500000 / 826887) ≤ (503059949 / 1000000000) := by
  have h := checkLog_sound (w := (326887 / 1326887)) (n := 12)
    (lo := (125764987 / 250000000)) (hi := (503059949 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((826887 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(826887 / 500000) = 1/(500000 / 826887) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15731 : Bounds (125764987 / 250000000) (503059949 / 1000000000) (Real.log (826887 / 500000)) := by
  have h := reflection_log_15731_neg
  have he : Real.log (826887 / 500000) = -Real.log (500000 / 826887) := by
    rw [show ((826887 / 500000) : ℝ) = ((500000 / 826887) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15732_neg : (1060663537 / 1000000000) ≤ -Real.log (173113 / 500000) ∧
    -Real.log (173113 / 500000) ≤ (1060663539 / 1000000000) := by
  have h := checkLog_sound (w := (76887 / 423113)) (n := 12)
    (lo := (367516357 / 1000000000)) (hi := (183758179 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 173113) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 173113) = 1/(173113 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15732 : Bounds (-1060663539 / 1000000000) (-1060663537 / 1000000000) (Real.log (173113 / 500000)) := by
  have h := reflection_log_15732_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15733_neg : (503652961 / 1000000000) ≤ -Real.log (200000 / 330951) ∧
    -Real.log (200000 / 330951) ≤ (251826481 / 500000000) := by
  have h := checkLog_sound (w := (130951 / 530951)) (n := 12)
    (lo := (503652961 / 1000000000)) (hi := (251826481 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((330951 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(330951 / 200000) = 1/(200000 / 330951) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15733 : Bounds (503652961 / 1000000000) (251826481 / 500000000) (Real.log (330951 / 200000)) := by
  have h := reflection_log_15733_neg
  have he : Real.log (330951 / 200000) = -Real.log (200000 / 330951) := by
    rw [show ((330951 / 200000) : ℝ) = ((200000 / 330951) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15734_neg : (132937621 / 125000000) ≤ -Real.log (69049 / 200000) ∧
    -Real.log (69049 / 200000) ≤ (106350097 / 100000000) := by
  have h := checkLog_sound (w := (30951 / 169049)) (n := 12)
    (lo := (92588447 / 250000000)) (hi := (370353789 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 69049) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(100000 / 69049) = 1/(69049 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15734 : Bounds (-106350097 / 100000000) (-132937621 / 125000000) (Real.log (69049 / 200000)) := by
  have h := reflection_log_15734_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15735_neg : (559848007 / 1000000000) ≤ -Real.log (22851835599 / 40000000000) ∧
    -Real.log (22851835599 / 40000000000) ≤ (69981001 / 125000000) := by
  have h := checkLog_sound (w := (17148164401 / 62851835599)) (n := 12)
    (lo := (559848007 / 1000000000)) (hi := (69981001 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 22851835599) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 22851835599) = 1/(22851835599 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15735 : Bounds (-69981001 / 125000000) (-559848007 / 1000000000) (Real.log (22851835599 / 40000000000)) := by
  have h := reflection_log_15735_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15736_neg : (557603589 / 1000000000) ≤ -Real.log (143144889231 / 250000000000) ∧
    -Real.log (143144889231 / 250000000000) ≤ (55760359 / 100000000) := by
  have h := checkLog_sound (w := (106855110769 / 393144889231)) (n := 12)
    (lo := (557603589 / 1000000000)) (hi := (55760359 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 143144889231) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 143144889231) = 1/(143144889231 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15736 : Bounds (-55760359 / 100000000) (-557603589 / 1000000000) (Real.log (143144889231 / 250000000000)) := by
  have h := reflection_log_15736_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15737_neg : (312744697 / 200000000) ≤ -Real.log (250000000000 / 1194143420771) ∧
    -Real.log (250000000000 / 1194143420771) ≤ (48866359 / 31250000) := by
  have h := checkLog_sound (w := (194143420771 / 2194143420771)) (n := 12)
    (lo := (1419433 / 8000000)) (hi := (88714563 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1194143420771 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1194143420771 / 1000000000000) = 1/(250000000000 / 1194143420771) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15737 : Bounds (312744697 / 200000000) (48866359 / 31250000) (Real.log (1194143420771 / 250000000000)) := by
  have h := reflection_log_15737_neg
  have he : Real.log (1194143420771 / 250000000000) = -Real.log (250000000000 / 1194143420771) := by
    rw [show ((1194143420771 / 250000000000) : ℝ) = ((250000000000 / 1194143420771) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15738_neg : (1567153929 / 1000000000) ≤ -Real.log (500000000000 / 2396493794263) ∧
    -Real.log (500000000000 / 2396493794263) ≤ (391788483 / 250000000) := by
  have h := checkLog_sound (w := (396493794263 / 4396493794263)) (n := 12)
    (lo := (180859569 / 1000000000)) (hi := (18085957 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2396493794263 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2396493794263 / 2000000000000) = 1/(500000000000 / 2396493794263) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15738 : Bounds (1567153929 / 1000000000) (391788483 / 250000000) (Real.log (2396493794263 / 500000000000)) := by
  have h := reflection_log_15738_neg
  have he : Real.log (2396493794263 / 500000000000) = -Real.log (500000000000 / 2396493794263) := by
    rw [show ((2396493794263 / 500000000000) : ℝ) = ((500000000000 / 2396493794263) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15739_neg : (1681058249 / 250000000) ≤ -Real.log (250000000000 / 208083333333333) ∧
    -Real.log (250000000000 / 208083333333333) ≤ (3362116503 / 500000000) := by
  have h := checkLog_sound (w := (80083333333333 / 336083333333333)) (n := 12)
    (lo := (60738547 / 125000000)) (hi := (485908377 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((208083333333333 / 128000000000000) : ℝ) 9 (by norm_num)
  have hq : (2 : ℝ)^9*(208083333333333 / 128000000000000) = 1/(250000000000 / 208083333333333) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15739 : Bounds (1681058249 / 250000000) (3362116503 / 500000000) (Real.log (208083333333333 / 250000000000)) := by
  have h := reflection_log_15739_neg
  have he : Real.log (208083333333333 / 250000000000) = -Real.log (250000000000 / 208083333333333) := by
    rw [show ((208083333333333 / 250000000000) : ℝ) = ((250000000000 / 208083333333333) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15740_neg : (851418061 / 125000000) ≤ -Real.log (100000000000 / 90809090909091) ∧
    -Real.log (100000000000 / 90809090909091) ≤ (3405672249 / 500000000) := by
  have h := checkLog_sound (w := (39609090909091 / 142009090909091)) (n := 12)
    (lo := (143254967 / 250000000)) (hi := (573019869 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((90809090909091 / 51200000000000) : ℝ) 9 (by norm_num)
  have hq : (2 : ℝ)^9*(90809090909091 / 51200000000000) = 1/(100000000000 / 90809090909091) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15740 : Bounds (851418061 / 125000000) (3405672249 / 500000000) (Real.log (90809090909091 / 100000000000)) := by
  have h := reflection_log_15740_neg
  have he : Real.log (90809090909091 / 100000000000) = -Real.log (100000000000 / 90809090909091) := by
    rw [show ((90809090909091 / 100000000000) : ℝ) = ((100000000000 / 90809090909091) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15741_neg : (17303667 / 25000000) ≤ -Real.log (500 / 999) ∧
    -Real.log (500 / 999) ≤ (692146681 / 1000000000) := by
  have h := checkLog_sound (w := (499 / 1499)) (n := 12)
    (lo := (17303667 / 25000000)) (hi := (692146681 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((999 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(999 / 500) = 1/(500 / 999) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15741 : Bounds (17303667 / 25000000) (692146681 / 1000000000) (Real.log (999 / 500)) := by
  have h := reflection_log_15741_neg
  have he : Real.log (999 / 500) = -Real.log (500 / 999) := by
    rw [show ((999 / 500) : ℝ) = ((500 / 999) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15742_neg : (6214608093 / 1000000000) ≤ -Real.log (1 / 500) ∧
    -Real.log (1 / 500) ≤ (3107304051 / 500000000) := by
  have h := checkLog_sound (w := (61 / 189)) (n := 12)
    (lo := (669430653 / 1000000000)) (hi := (334715327 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 64) : ℝ) 8 (by norm_num)
  have hq : (2 : ℝ)^8*(125 / 64) = 1/(1 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15742 : Bounds (-3107304051 / 500000000) (-6214608093 / 1000000000) (Real.log (1 / 500)) := by
  have h := reflection_log_15742_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15743_neg : (498751 / 500000000) ≤ -Real.log (500000 / 500499) ∧
    -Real.log (500000 / 500499) ≤ (997503 / 1000000000) := by
  have h := checkLog_sound (w := (499 / 1000499)) (n := 12)
    (lo := (498751 / 500000000)) (hi := (997503 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500499 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500499 / 500000) = 1/(500000 / 500499) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15743 : Bounds (498751 / 500000000) (997503 / 1000000000) (Real.log (500499 / 500000)) := by
  have h := reflection_log_15743_neg
  have he : Real.log (500499 / 500000) = -Real.log (500000 / 500499) := by
    rw [show ((500499 / 500000) : ℝ) = ((500000 / 500499) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily
