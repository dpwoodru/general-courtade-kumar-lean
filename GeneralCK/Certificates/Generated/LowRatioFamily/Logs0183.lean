import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_11712_neg : (92986797 / 200000000) ≤ -Real.log (500000000000 / 795954548283) ∧
    -Real.log (500000000000 / 795954548283) ≤ (232466993 / 500000000) := by
  have h := checkLog_sound (w := (295954548283 / 1295954548283)) (n := 12)
    (lo := (92986797 / 200000000)) (hi := (232466993 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((795954548283 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(795954548283 / 500000000000) = 1/(500000000000 / 795954548283) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11712 : Bounds (92986797 / 200000000) (232466993 / 500000000) (Real.log (795954548283 / 500000000000)) := by
  have h := reflection_log_11712_neg
  have he : Real.log (795954548283 / 500000000000) = -Real.log (500000000000 / 795954548283) := by
    rw [show ((795954548283 / 500000000000) : ℝ) = ((500000000000 / 795954548283) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11713_neg : (2354957 / 2500000) ≤ -Real.log (100000000000 / 256506238859) ∧
    -Real.log (100000000000 / 256506238859) ≤ (470991401 / 500000000) := by
  have h := checkLog_sound (w := (56506238859 / 456506238859)) (n := 12)
    (lo := (12441781 / 50000000)) (hi := (248835621 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((256506238859 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(256506238859 / 200000000000) = 1/(100000000000 / 256506238859) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11713 : Bounds (2354957 / 2500000) (470991401 / 500000000) (Real.log (256506238859 / 100000000000)) := by
  have h := reflection_log_11713_neg
  have he : Real.log (256506238859 / 100000000000) = -Real.log (100000000000 / 256506238859) := by
    rw [show ((256506238859 / 100000000000) : ℝ) = ((100000000000 / 256506238859) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11714_neg : (118057701 / 125000000) ≤ -Real.log (100000000000 / 257142857143) ∧
    -Real.log (100000000000 / 257142857143) ≤ (94446161 / 100000000) := by
  have h := checkLog_sound (w := (57142857143 / 457142857143)) (n := 12)
    (lo := (62828607 / 250000000)) (hi := (251314429 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((257142857143 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(257142857143 / 200000000000) = 1/(100000000000 / 257142857143) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11714 : Bounds (118057701 / 125000000) (94446161 / 100000000) (Real.log (257142857143 / 100000000000)) := by
  have h := reflection_log_11714_neg
  have he : Real.log (257142857143 / 100000000000) = -Real.log (100000000000 / 257142857143) := by
    rw [show ((257142857143 / 100000000000) : ℝ) = ((100000000000 / 257142857143) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11715_neg : (365337317 / 1000000000) ≤ -Real.log (1000 / 1441) ∧
    -Real.log (1000 / 1441) ≤ (182668659 / 500000000) := by
  have h := checkLog_sound (w := (441 / 2441)) (n := 12)
    (lo := (365337317 / 1000000000)) (hi := (182668659 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1441 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1441 / 1000) = 1/(1000 / 1441) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11715 : Bounds (365337317 / 1000000000) (182668659 / 500000000) (Real.log (1441 / 1000)) := by
  have h := reflection_log_11715_neg
  have he : Real.log (1441 / 1000) = -Real.log (1000 / 1441) := by
    rw [show ((1441 / 1000) : ℝ) = ((1000 / 1441) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11716_neg : (116321161 / 200000000) ≤ -Real.log (559 / 1000) ∧
    -Real.log (559 / 1000) ≤ (290802903 / 500000000) := by
  have h := checkLog_sound (w := (441 / 1559)) (n := 12)
    (lo := (116321161 / 200000000)) (hi := (290802903 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 559) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 559) = 1/(559 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11716 : Bounds (-290802903 / 500000000) (-116321161 / 200000000) (Real.log (559 / 1000)) := by
  have h := reflection_log_11716_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11717_neg : (220451 / 500000000) ≤ -Real.log (1000000 / 1000441) ∧
    -Real.log (1000000 / 1000441) ≤ (440903 / 1000000000) := by
  have h := checkLog_sound (w := (441 / 2000441)) (n := 12)
    (lo := (220451 / 500000000)) (hi := (440903 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000441 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000441 / 1000000) = 1/(1000000 / 1000441) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11717 : Bounds (220451 / 500000000) (440903 / 1000000000) (Real.log (1000441 / 1000000)) := by
  have h := reflection_log_11717_neg
  have he : Real.log (1000441 / 1000000) = -Real.log (1000000 / 1000441) := by
    rw [show ((1000441 / 1000000) : ℝ) = ((1000000 / 1000441) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11718_neg : (441097 / 1000000000) ≤ -Real.log (999559 / 1000000) ∧
    -Real.log (999559 / 1000000) ≤ (220549 / 500000000) := by
  have h := checkLog_sound (w := (441 / 1999559)) (n := 12)
    (lo := (441097 / 1000000000)) (hi := (220549 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999559) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999559) = 1/(999559 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11718 : Bounds (-220549 / 500000000) (-441097 / 1000000000) (Real.log (999559 / 1000000)) := by
  have h := reflection_log_11718_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11719_neg : (102670613 / 500000000) ≤ -Real.log (125000 / 153493) ∧
    -Real.log (125000 / 153493) ≤ (205341227 / 1000000000) := by
  have h := checkLog_sound (w := (28493 / 278493)) (n := 12)
    (lo := (102670613 / 500000000)) (hi := (205341227 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((153493 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(153493 / 125000) = 1/(125000 / 153493) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11719 : Bounds (102670613 / 500000000) (205341227 / 1000000000) (Real.log (153493 / 125000)) := by
  have h := reflection_log_11719_neg
  have he : Real.log (153493 / 125000) = -Real.log (125000 / 153493) := by
    rw [show ((153493 / 125000) : ℝ) = ((125000 / 153493) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11720_neg : (16168637 / 62500000) ≤ -Real.log (96507 / 125000) ∧
    -Real.log (96507 / 125000) ≤ (258698193 / 1000000000) := by
  have h := checkLog_sound (w := (28493 / 221507)) (n := 12)
    (lo := (16168637 / 62500000)) (hi := (258698193 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 96507) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 96507) = 1/(96507 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11720 : Bounds (-258698193 / 1000000000) (-16168637 / 62500000) (Real.log (96507 / 125000)) := by
  have h := reflection_log_11720_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11721_neg : (206140617 / 1000000000) ≤ -Real.log (500000 / 614463) ∧
    -Real.log (500000 / 614463) ≤ (103070309 / 500000000) := by
  have h := checkLog_sound (w := (114463 / 1114463)) (n := 12)
    (lo := (206140617 / 1000000000)) (hi := (103070309 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((614463 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(614463 / 500000) = 1/(500000 / 614463) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11721 : Bounds (206140617 / 1000000000) (103070309 / 500000000) (Real.log (614463 / 500000)) := by
  have h := reflection_log_11721_neg
  have he : Real.log (614463 / 500000) = -Real.log (500000 / 614463) := by
    rw [show ((614463 / 500000) : ℝ) = ((500000 / 614463) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11722_neg : (25997093 / 100000000) ≤ -Real.log (385537 / 500000) ∧
    -Real.log (385537 / 500000) ≤ (259970931 / 1000000000) := by
  have h := checkLog_sound (w := (114463 / 885537)) (n := 12)
    (lo := (25997093 / 100000000)) (hi := (259970931 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 385537) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 385537) = 1/(385537 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11722 : Bounds (-259970931 / 1000000000) (-25997093 / 100000000) (Real.log (385537 / 500000)) := by
  have h := reflection_log_11722_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11723_neg : (53830313 / 1000000000) ≤ -Real.log (236898221631 / 250000000000) ∧
    -Real.log (236898221631 / 250000000000) ≤ (26915157 / 500000000) := by
  have h := checkLog_sound (w := (13101778369 / 486898221631)) (n := 12)
    (lo := (53830313 / 1000000000)) (hi := (26915157 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 236898221631) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 236898221631) = 1/(236898221631 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11723 : Bounds (-26915157 / 500000000) (-53830313 / 1000000000) (Real.log (236898221631 / 250000000000)) := by
  have h := reflection_log_11723_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11724_neg : (26678483 / 500000000) ≤ -Real.log (14813148951 / 15625000000) ∧
    -Real.log (14813148951 / 15625000000) ≤ (53356967 / 1000000000) := by
  have h := checkLog_sound (w := (811851049 / 30438148951)) (n := 12)
    (lo := (26678483 / 500000000)) (hi := (53356967 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 14813148951) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 14813148951) = 1/(14813148951 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11724 : Bounds (-53356967 / 1000000000) (-26678483 / 500000000) (Real.log (14813148951 / 15625000000)) := by
  have h := reflection_log_11724_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11725_neg : (232019709 / 500000000) ≤ -Real.log (250000000000 / 397621416063) ∧
    -Real.log (250000000000 / 397621416063) ≤ (464039419 / 1000000000) := by
  have h := checkLog_sound (w := (147621416063 / 647621416063)) (n := 12)
    (lo := (232019709 / 500000000)) (hi := (464039419 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((397621416063 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(397621416063 / 250000000000) = 1/(250000000000 / 397621416063) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11725 : Bounds (232019709 / 500000000) (464039419 / 1000000000) (Real.log (397621416063 / 250000000000)) := by
  have h := reflection_log_11725_neg
  have he : Real.log (397621416063 / 250000000000) = -Real.log (250000000000 / 397621416063) := by
    rw [show ((397621416063 / 250000000000) : ℝ) = ((250000000000 / 397621416063) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11726_neg : (466111547 / 1000000000) ≤ -Real.log (15625000000 / 24902887077) ∧
    -Real.log (15625000000 / 24902887077) ≤ (116527887 / 250000000) := by
  have h := checkLog_sound (w := (9277887077 / 40527887077)) (n := 12)
    (lo := (466111547 / 1000000000)) (hi := (116527887 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24902887077 / 15625000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24902887077 / 15625000000) = 1/(15625000000 / 24902887077) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11726 : Bounds (466111547 / 1000000000) (116527887 / 250000000) (Real.log (24902887077 / 15625000000)) := by
  have h := reflection_log_11726_neg
  have he : Real.log (24902887077 / 15625000000) = -Real.log (15625000000 / 24902887077) := by
    rw [show ((24902887077 / 15625000000) : ℝ) = ((15625000000 / 24902887077) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11727_neg : (118057701 / 125000000) ≤ -Real.log (250000000000 / 642857142857) ∧
    -Real.log (250000000000 / 642857142857) ≤ (94446161 / 100000000) := by
  have h := checkLog_sound (w := (142857142857 / 1142857142857)) (n := 12)
    (lo := (62828607 / 250000000)) (hi := (251314429 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((642857142857 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(642857142857 / 500000000000) = 1/(250000000000 / 642857142857) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11727 : Bounds (118057701 / 125000000) (94446161 / 100000000) (Real.log (642857142857 / 250000000000)) := by
  have h := reflection_log_11727_neg
  have he : Real.log (642857142857 / 250000000000) = -Real.log (250000000000 / 642857142857) := by
    rw [show ((642857142857 / 250000000000) : ℝ) = ((250000000000 / 642857142857) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11728_neg : (473471561 / 500000000) ≤ -Real.log (500000000000 / 1288908765653) ∧
    -Real.log (500000000000 / 1288908765653) ≤ (236735781 / 250000000) := by
  have h := checkLog_sound (w := (288908765653 / 2288908765653)) (n := 12)
    (lo := (126897971 / 500000000)) (hi := (253795943 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1288908765653 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1288908765653 / 1000000000000) = 1/(500000000000 / 1288908765653) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11728 : Bounds (473471561 / 500000000) (236735781 / 250000000) (Real.log (1288908765653 / 500000000000)) := by
  have h := reflection_log_11728_neg
  have he : Real.log (1288908765653 / 500000000000) = -Real.log (500000000000 / 1288908765653) := by
    rw [show ((1288908765653 / 500000000000) : ℝ) = ((500000000000 / 1288908765653) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11729_neg : (183015519 / 500000000) ≤ -Real.log (500 / 721) ∧
    -Real.log (500 / 721) ≤ (366031039 / 1000000000) := by
  have h := checkLog_sound (w := (221 / 1221)) (n := 12)
    (lo := (183015519 / 500000000)) (hi := (366031039 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((721 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(721 / 500) = 1/(500 / 721) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11729 : Bounds (183015519 / 500000000) (366031039 / 1000000000) (Real.log (721 / 500)) := by
  have h := reflection_log_11729_neg
  have he : Real.log (721 / 500) = -Real.log (500 / 721) := by
    rw [show ((721 / 500) : ℝ) = ((500 / 721) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11730_neg : (145849079 / 250000000) ≤ -Real.log (279 / 500) ∧
    -Real.log (279 / 500) ≤ (583396317 / 1000000000) := by
  have h := checkLog_sound (w := (221 / 779)) (n := 12)
    (lo := (145849079 / 250000000)) (hi := (583396317 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 279) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500 / 279) = 1/(279 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11730 : Bounds (-583396317 / 1000000000) (-145849079 / 250000000) (Real.log (279 / 500)) := by
  have h := reflection_log_11730_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11731_neg : (220951 / 500000000) ≤ -Real.log (500000 / 500221) ∧
    -Real.log (500000 / 500221) ≤ (441903 / 1000000000) := by
  have h := checkLog_sound (w := (221 / 1000221)) (n := 12)
    (lo := (220951 / 500000000)) (hi := (441903 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500221 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500221 / 500000) = 1/(500000 / 500221) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11731 : Bounds (220951 / 500000000) (441903 / 1000000000) (Real.log (500221 / 500000)) := by
  have h := reflection_log_11731_neg
  have he : Real.log (500221 / 500000) = -Real.log (500000 / 500221) := by
    rw [show ((500221 / 500000) : ℝ) = ((500000 / 500221) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11732_neg : (442097 / 1000000000) ≤ -Real.log (499779 / 500000) ∧
    -Real.log (499779 / 500000) ≤ (221049 / 500000000) := by
  have h := checkLog_sound (w := (221 / 999779)) (n := 12)
    (lo := (442097 / 1000000000)) (hi := (221049 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499779) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499779) = 1/(499779 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11732 : Bounds (-221049 / 500000000) (-442097 / 1000000000) (Real.log (499779 / 500000)) := by
  have h := reflection_log_11732_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11733_neg : (10289777 / 50000000) ≤ -Real.log (500000 / 614251) ∧
    -Real.log (500000 / 614251) ≤ (205795541 / 1000000000) := by
  have h := checkLog_sound (w := (114251 / 1114251)) (n := 12)
    (lo := (10289777 / 50000000)) (hi := (205795541 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((614251 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(614251 / 500000) = 1/(500000 / 614251) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11733 : Bounds (10289777 / 50000000) (205795541 / 1000000000) (Real.log (614251 / 500000)) := by
  have h := reflection_log_11733_neg
  have he : Real.log (614251 / 500000) = -Real.log (500000 / 614251) := by
    rw [show ((614251 / 500000) : ℝ) = ((500000 / 614251) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11734_neg : (259421199 / 1000000000) ≤ -Real.log (385749 / 500000) ∧
    -Real.log (385749 / 500000) ≤ (648553 / 2500000) := by
  have h := checkLog_sound (w := (114251 / 885749)) (n := 12)
    (lo := (259421199 / 1000000000)) (hi := (648553 / 2500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 385749) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 385749) = 1/(385749 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11734 : Bounds (-648553 / 2500000) (-259421199 / 1000000000) (Real.log (385749 / 500000)) := by
  have h := reflection_log_11734_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11735_neg : (103297691 / 500000000) ≤ -Real.log (200000 / 245897) ∧
    -Real.log (200000 / 245897) ≤ (206595383 / 1000000000) := by
  have h := checkLog_sound (w := (45897 / 445897)) (n := 12)
    (lo := (103297691 / 500000000)) (hi := (206595383 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((245897 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(245897 / 200000) = 1/(200000 / 245897) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11735 : Bounds (103297691 / 500000000) (206595383 / 1000000000) (Real.log (245897 / 200000)) := by
  have h := reflection_log_11735_neg
  have he : Real.log (245897 / 200000) = -Real.log (200000 / 245897) := by
    rw [show ((245897 / 200000) : ℝ) = ((200000 / 245897) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11736_neg : (65174039 / 250000000) ≤ -Real.log (154103 / 200000) ∧
    -Real.log (154103 / 200000) ≤ (260696157 / 1000000000) := by
  have h := checkLog_sound (w := (45897 / 354103)) (n := 12)
    (lo := (65174039 / 250000000)) (hi := (260696157 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 154103) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 154103) = 1/(154103 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11736 : Bounds (-260696157 / 1000000000) (-65174039 / 250000000) (Real.log (154103 / 200000)) := by
  have h := reflection_log_11736_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11737_neg : (27050387 / 500000000) ≤ -Real.log (37893465391 / 40000000000) ∧
    -Real.log (37893465391 / 40000000000) ≤ (2164031 / 40000000) := by
  have h := checkLog_sound (w := (2106534609 / 77893465391)) (n := 12)
    (lo := (27050387 / 500000000)) (hi := (2164031 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 37893465391) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 37893465391) = 1/(37893465391 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11737 : Bounds (-2164031 / 40000000) (-27050387 / 500000000) (Real.log (37893465391 / 40000000000)) := by
  have h := reflection_log_11737_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11738_neg : (26812829 / 500000000) ≤ -Real.log (236946708999 / 250000000000) ∧
    -Real.log (236946708999 / 250000000000) ≤ (53625659 / 1000000000) := by
  have h := checkLog_sound (w := (13053291001 / 486946708999)) (n := 12)
    (lo := (26812829 / 500000000)) (hi := (53625659 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 236946708999) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 236946708999) = 1/(236946708999 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11738 : Bounds (-53625659 / 1000000000) (-26812829 / 500000000) (Real.log (236946708999 / 250000000000)) := by
  have h := reflection_log_11738_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11739_neg : (23260837 / 50000000) ≤ -Real.log (7812500000 / 12440306877) ∧
    -Real.log (7812500000 / 12440306877) ≤ (465216741 / 1000000000) := by
  have h := checkLog_sound (w := (4627806877 / 20252806877)) (n := 12)
    (lo := (23260837 / 50000000)) (hi := (465216741 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12440306877 / 7812500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12440306877 / 7812500000) = 1/(7812500000 / 12440306877) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11739 : Bounds (23260837 / 50000000) (465216741 / 1000000000) (Real.log (12440306877 / 7812500000)) := by
  have h := reflection_log_11739_neg
  have he : Real.log (12440306877 / 7812500000) = -Real.log (7812500000 / 12440306877) := by
    rw [show ((12440306877 / 7812500000) : ℝ) = ((7812500000 / 12440306877) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11740_neg : (467291539 / 1000000000) ≤ -Real.log (500000000000 / 797833267361) ∧
    -Real.log (500000000000 / 797833267361) ≤ (23364577 / 50000000) := by
  have h := checkLog_sound (w := (297833267361 / 1297833267361)) (n := 12)
    (lo := (467291539 / 1000000000)) (hi := (23364577 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((797833267361 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(797833267361 / 500000000000) = 1/(500000000000 / 797833267361) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11740 : Bounds (467291539 / 1000000000) (23364577 / 50000000) (Real.log (797833267361 / 500000000000)) := by
  have h := reflection_log_11740_neg
  have he : Real.log (797833267361 / 500000000000) = -Real.log (500000000000 / 797833267361) := by
    rw [show ((797833267361 / 500000000000) : ℝ) = ((500000000000 / 797833267361) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11741_neg : (473471561 / 500000000) ≤ -Real.log (125000000000 / 322227191413) ∧
    -Real.log (125000000000 / 322227191413) ≤ (236735781 / 250000000) := by
  have h := checkLog_sound (w := (72227191413 / 572227191413)) (n := 12)
    (lo := (126897971 / 500000000)) (hi := (253795943 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((322227191413 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(322227191413 / 250000000000) = 1/(125000000000 / 322227191413) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11741 : Bounds (473471561 / 500000000) (236735781 / 250000000) (Real.log (322227191413 / 125000000000)) := by
  have h := reflection_log_11741_neg
  have he : Real.log (322227191413 / 125000000000) = -Real.log (125000000000 / 322227191413) := by
    rw [show ((322227191413 / 125000000000) : ℝ) = ((125000000000 / 322227191413) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11742_neg : (474713677 / 500000000) ≤ -Real.log (500000000000 / 1292114695341) ∧
    -Real.log (500000000000 / 1292114695341) ≤ (237356839 / 250000000) := by
  have h := checkLog_sound (w := (292114695341 / 2292114695341)) (n := 12)
    (lo := (128140087 / 500000000)) (hi := (10251207 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1292114695341 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1292114695341 / 1000000000000) = 1/(500000000000 / 1292114695341) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11742 : Bounds (474713677 / 500000000) (237356839 / 250000000) (Real.log (1292114695341 / 500000000000)) := by
  have h := reflection_log_11742_neg
  have he : Real.log (1292114695341 / 500000000000) = -Real.log (500000000000 / 1292114695341) := by
    rw [show ((1292114695341 / 500000000000) : ℝ) = ((500000000000 / 1292114695341) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11743_neg : (366724279 / 1000000000) ≤ -Real.log (1000 / 1443) ∧
    -Real.log (1000 / 1443) ≤ (9168107 / 25000000) := by
  have h := checkLog_sound (w := (443 / 2443)) (n := 12)
    (lo := (366724279 / 1000000000)) (hi := (9168107 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1443 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1443 / 1000) = 1/(1000 / 1443) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11743 : Bounds (366724279 / 1000000000) (9168107 / 25000000) (Real.log (1443 / 1000)) := by
  have h := reflection_log_11743_neg
  have he : Real.log (1443 / 1000) = -Real.log (1000 / 1443) := by
    rw [show ((1443 / 1000) : ℝ) = ((1000 / 1443) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11744_neg : (585190039 / 1000000000) ≤ -Real.log (557 / 1000) ∧
    -Real.log (557 / 1000) ≤ (14629751 / 25000000) := by
  have h := checkLog_sound (w := (443 / 1557)) (n := 12)
    (lo := (585190039 / 1000000000)) (hi := (14629751 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 557) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 557) = 1/(557 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11744 : Bounds (-14629751 / 25000000) (-585190039 / 1000000000) (Real.log (557 / 1000)) := by
  have h := reflection_log_11744_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11745_neg : (442901 / 1000000000) ≤ -Real.log (1000000 / 1000443) ∧
    -Real.log (1000000 / 1000443) ≤ (221451 / 500000000) := by
  have h := checkLog_sound (w := (443 / 2000443)) (n := 12)
    (lo := (442901 / 1000000000)) (hi := (221451 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000443 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000443 / 1000000) = 1/(1000000 / 1000443) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11745 : Bounds (442901 / 1000000000) (221451 / 500000000) (Real.log (1000443 / 1000000)) := by
  have h := reflection_log_11745_neg
  have he : Real.log (1000443 / 1000000) = -Real.log (1000000 / 1000443) := by
    rw [show ((1000443 / 1000000) : ℝ) = ((1000000 / 1000443) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11746_neg : (221549 / 500000000) ≤ -Real.log (999557 / 1000000) ∧
    -Real.log (999557 / 1000000) ≤ (443099 / 1000000000) := by
  have h := checkLog_sound (w := (443 / 1999557)) (n := 12)
    (lo := (221549 / 500000000)) (hi := (443099 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999557) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999557) = 1/(999557 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11746 : Bounds (-443099 / 1000000000) (-221549 / 500000000) (Real.log (999557 / 1000000)) := by
  have h := reflection_log_11746_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11747_neg : (41249767 / 200000000) ≤ -Real.log (1000000 / 1229059) ∧
    -Real.log (1000000 / 1229059) ≤ (51562209 / 250000000) := by
  have h := checkLog_sound (w := (229059 / 2229059)) (n := 12)
    (lo := (41249767 / 200000000)) (hi := (51562209 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1229059 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1229059 / 1000000) = 1/(1000000 / 1229059) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11747 : Bounds (41249767 / 200000000) (51562209 / 250000000) (Real.log (1229059 / 1000000)) := by
  have h := reflection_log_11747_neg
  have he : Real.log (1229059 / 1000000) = -Real.log (1000000 / 1229059) := by
    rw [show ((1229059 / 1000000) : ℝ) = ((1000000 / 1229059) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11748_neg : (32517929 / 125000000) ≤ -Real.log (770941 / 1000000) ∧
    -Real.log (770941 / 1000000) ≤ (260143433 / 1000000000) := by
  have h := checkLog_sound (w := (229059 / 1770941)) (n := 12)
    (lo := (32517929 / 125000000)) (hi := (260143433 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 770941) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 770941) = 1/(770941 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11748 : Bounds (-260143433 / 1000000000) (-32517929 / 125000000) (Real.log (770941 / 1000000)) := by
  have h := reflection_log_11748_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11749_neg : (207049941 / 1000000000) ≤ -Real.log (250000 / 307511) ∧
    -Real.log (250000 / 307511) ≤ (103524971 / 500000000) := by
  have h := checkLog_sound (w := (57511 / 557511)) (n := 12)
    (lo := (207049941 / 1000000000)) (hi := (103524971 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((307511 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(307511 / 250000) = 1/(250000 / 307511) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11749 : Bounds (207049941 / 1000000000) (103524971 / 500000000) (Real.log (307511 / 250000)) := by
  have h := reflection_log_11749_neg
  have he : Real.log (307511 / 250000) = -Real.log (250000 / 307511) := by
    rw [show ((307511 / 250000) : ℝ) = ((250000 / 307511) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11750_neg : (65355477 / 250000000) ≤ -Real.log (192489 / 250000) ∧
    -Real.log (192489 / 250000) ≤ (261421909 / 1000000000) := by
  have h := checkLog_sound (w := (57511 / 442489)) (n := 12)
    (lo := (65355477 / 250000000)) (hi := (261421909 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 192489) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 192489) = 1/(192489 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11750 : Bounds (-261421909 / 1000000000) (-65355477 / 250000000) (Real.log (192489 / 250000)) := by
  have h := reflection_log_11750_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11751_neg : (54371967 / 1000000000) ≤ -Real.log (59192484879 / 62500000000) ∧
    -Real.log (59192484879 / 62500000000) ≤ (424781 / 7812500) := by
  have h := checkLog_sound (w := (3307515121 / 121692484879)) (n := 12)
    (lo := (54371967 / 1000000000)) (hi := (424781 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 59192484879) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 59192484879) = 1/(59192484879 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11751 : Bounds (-424781 / 7812500) (-54371967 / 1000000000) (Real.log (59192484879 / 62500000000)) := by
  have h := reflection_log_11751_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11752_neg : (13473649 / 250000000) ≤ -Real.log (947531974519 / 1000000000000) ∧
    -Real.log (947531974519 / 1000000000000) ≤ (53894597 / 1000000000) := by
  have h := checkLog_sound (w := (52468025481 / 1947531974519)) (n := 12)
    (lo := (13473649 / 250000000)) (hi := (53894597 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 947531974519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 947531974519) = 1/(947531974519 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11752 : Bounds (-53894597 / 1000000000) (-13473649 / 250000000) (Real.log (947531974519 / 1000000000000)) := by
  have h := reflection_log_11752_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11753_neg : (116598067 / 250000000) ≤ -Real.log (250000000000 / 398558060863) ∧
    -Real.log (250000000000 / 398558060863) ≤ (466392269 / 1000000000) := by
  have h := checkLog_sound (w := (148558060863 / 648558060863)) (n := 12)
    (lo := (116598067 / 250000000)) (hi := (466392269 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((398558060863 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(398558060863 / 250000000000) = 1/(250000000000 / 398558060863) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11753 : Bounds (116598067 / 250000000) (466392269 / 1000000000) (Real.log (398558060863 / 250000000000)) := by
  have h := reflection_log_11753_neg
  have he : Real.log (398558060863 / 250000000000) = -Real.log (250000000000 / 398558060863) := by
    rw [show ((398558060863 / 250000000000) : ℝ) = ((250000000000 / 398558060863) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11754_neg : (468471849 / 1000000000) ≤ -Real.log (100000000000 / 159755102889) ∧
    -Real.log (100000000000 / 159755102889) ≤ (9369437 / 20000000) := by
  have h := checkLog_sound (w := (59755102889 / 259755102889)) (n := 12)
    (lo := (468471849 / 1000000000)) (hi := (9369437 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((159755102889 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(159755102889 / 100000000000) = 1/(100000000000 / 159755102889) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11754 : Bounds (468471849 / 1000000000) (9369437 / 20000000) (Real.log (159755102889 / 100000000000)) := by
  have h := reflection_log_11754_neg
  have he : Real.log (159755102889 / 100000000000) = -Real.log (100000000000 / 159755102889) := by
    rw [show ((159755102889 / 100000000000) : ℝ) = ((100000000000 / 159755102889) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11755_neg : (474713677 / 500000000) ≤ -Real.log (25000000000 / 64605734767) ∧
    -Real.log (25000000000 / 64605734767) ≤ (237356839 / 250000000) := by
  have h := checkLog_sound (w := (14605734767 / 114605734767)) (n := 12)
    (lo := (128140087 / 500000000)) (hi := (10251207 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((64605734767 / 50000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(64605734767 / 50000000000) = 1/(25000000000 / 64605734767) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11755 : Bounds (474713677 / 500000000) (237356839 / 250000000) (Real.log (64605734767 / 25000000000)) := by
  have h := reflection_log_11755_neg
  have he : Real.log (64605734767 / 25000000000) = -Real.log (25000000000 / 64605734767) := by
    rw [show ((64605734767 / 25000000000) : ℝ) = ((25000000000 / 64605734767) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11756_neg : (475957159 / 500000000) ≤ -Real.log (250000000000 / 647666068223) ∧
    -Real.log (250000000000 / 647666068223) ≤ (11898929 / 12500000) := by
  have h := checkLog_sound (w := (147666068223 / 1147666068223)) (n := 12)
    (lo := (129383569 / 500000000)) (hi := (258767139 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((647666068223 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(647666068223 / 500000000000) = 1/(250000000000 / 647666068223) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11756 : Bounds (475957159 / 500000000) (11898929 / 12500000) (Real.log (647666068223 / 250000000000)) := by
  have h := reflection_log_11756_neg
  have he : Real.log (647666068223 / 250000000000) = -Real.log (250000000000 / 647666068223) := by
    rw [show ((647666068223 / 250000000000) : ℝ) = ((250000000000 / 647666068223) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11757_neg : (4592713 / 12500000) ≤ -Real.log (250 / 361) ∧
    -Real.log (250 / 361) ≤ (367417041 / 1000000000) := by
  have h := checkLog_sound (w := (111 / 611)) (n := 12)
    (lo := (4592713 / 12500000)) (hi := (367417041 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((361 / 250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(361 / 250) = 1/(250 / 361) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11757 : Bounds (4592713 / 12500000) (367417041 / 1000000000) (Real.log (361 / 250)) := by
  have h := reflection_log_11757_neg
  have he : Real.log (361 / 250) = -Real.log (250 / 361) := by
    rw [show ((361 / 250) : ℝ) = ((250 / 361) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11758_neg : (73373373 / 125000000) ≤ -Real.log (139 / 250) ∧
    -Real.log (139 / 250) ≤ (117397397 / 200000000) := by
  have h := checkLog_sound (w := (111 / 389)) (n := 12)
    (lo := (73373373 / 125000000)) (hi := (117397397 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250 / 139) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250 / 139) = 1/(139 / 250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11758 : Bounds (-117397397 / 200000000) (-73373373 / 125000000) (Real.log (139 / 250)) := by
  have h := reflection_log_11758_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11759_neg : (443901 / 1000000000) ≤ -Real.log (250000 / 250111) ∧
    -Real.log (250000 / 250111) ≤ (221951 / 500000000) := by
  have h := checkLog_sound (w := (111 / 500111)) (n := 12)
    (lo := (443901 / 1000000000)) (hi := (221951 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250111 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250111 / 250000) = 1/(250000 / 250111) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11759 : Bounds (443901 / 1000000000) (221951 / 500000000) (Real.log (250111 / 250000)) := by
  have h := reflection_log_11759_neg
  have he : Real.log (250111 / 250000) = -Real.log (250000 / 250111) := by
    rw [show ((250111 / 250000) : ℝ) = ((250000 / 250111) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11760_neg : (222049 / 500000000) ≤ -Real.log (249889 / 250000) ∧
    -Real.log (249889 / 250000) ≤ (444099 / 1000000000) := by
  have h := checkLog_sound (w := (111 / 499889)) (n := 12)
    (lo := (222049 / 500000000)) (hi := (444099 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 249889) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 249889) = 1/(249889 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11760 : Bounds (-444099 / 1000000000) (-222049 / 500000000) (Real.log (249889 / 250000)) := by
  have h := reflection_log_11760_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11761_neg : (3229743 / 15625000) ≤ -Real.log (500000 / 614809) ∧
    -Real.log (500000 / 614809) ≤ (206703553 / 1000000000) := by
  have h := checkLog_sound (w := (114809 / 1114809)) (n := 12)
    (lo := (3229743 / 15625000)) (hi := (206703553 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((614809 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(614809 / 500000) = 1/(500000 / 614809) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11761 : Bounds (3229743 / 15625000) (206703553 / 1000000000) (Real.log (614809 / 500000)) := by
  have h := reflection_log_11761_neg
  have he : Real.log (614809 / 500000) = -Real.log (500000 / 614809) := by
    rw [show ((614809 / 500000) : ℝ) = ((500000 / 614809) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11762_neg : (260868783 / 1000000000) ≤ -Real.log (385191 / 500000) ∧
    -Real.log (385191 / 500000) ≤ (16304299 / 62500000) := by
  have h := checkLog_sound (w := (114809 / 885191)) (n := 12)
    (lo := (260868783 / 1000000000)) (hi := (16304299 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 385191) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 385191) = 1/(385191 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11762 : Bounds (-16304299 / 62500000) (-260868783 / 1000000000) (Real.log (385191 / 500000)) := by
  have h := reflection_log_11762_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11763_neg : (41501021 / 200000000) ≤ -Real.log (250000 / 307651) ∧
    -Real.log (250000 / 307651) ≤ (103752553 / 500000000) := by
  have h := checkLog_sound (w := (57651 / 557651)) (n := 12)
    (lo := (41501021 / 200000000)) (hi := (103752553 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((307651 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(307651 / 250000) = 1/(250000 / 307651) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11763 : Bounds (41501021 / 200000000) (103752553 / 500000000) (Real.log (307651 / 250000)) := by
  have h := reflection_log_11763_neg
  have he : Real.log (307651 / 250000) = -Real.log (250000 / 307651) := by
    rw [show ((307651 / 250000) : ℝ) = ((250000 / 307651) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11764_neg : (262149487 / 1000000000) ≤ -Real.log (192349 / 250000) ∧
    -Real.log (192349 / 250000) ≤ (16384343 / 62500000) := by
  have h := checkLog_sound (w := (57651 / 442349)) (n := 12)
    (lo := (262149487 / 1000000000)) (hi := (16384343 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 192349) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 192349) = 1/(192349 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11764 : Bounds (-16384343 / 62500000) (-262149487 / 1000000000) (Real.log (192349 / 250000)) := by
  have h := reflection_log_11764_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11765_neg : (54644381 / 1000000000) ≤ -Real.log (59176362199 / 62500000000) ∧
    -Real.log (59176362199 / 62500000000) ≤ (27322191 / 500000000) := by
  have h := checkLog_sound (w := (3323637801 / 121676362199)) (n := 12)
    (lo := (54644381 / 1000000000)) (hi := (27322191 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 59176362199) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 59176362199) = 1/(59176362199 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11765 : Bounds (-27322191 / 500000000) (-54644381 / 1000000000) (Real.log (59176362199 / 62500000000)) := by
  have h := reflection_log_11765_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11766_neg : (54165231 / 1000000000) ≤ -Real.log (236818893519 / 250000000000) ∧
    -Real.log (236818893519 / 250000000000) ≤ (3385327 / 62500000) := by
  have h := checkLog_sound (w := (13181106481 / 486818893519)) (n := 12)
    (lo := (54165231 / 1000000000)) (hi := (3385327 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 236818893519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 236818893519) = 1/(236818893519 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11766 : Bounds (-3385327 / 62500000) (-54165231 / 1000000000) (Real.log (236818893519 / 250000000000)) := by
  have h := reflection_log_11766_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11767_neg : (93514467 / 200000000) ≤ -Real.log (500000000000 / 798057327403) ∧
    -Real.log (500000000000 / 798057327403) ≤ (29223271 / 62500000) := by
  have h := checkLog_sound (w := (298057327403 / 1298057327403)) (n := 12)
    (lo := (93514467 / 200000000)) (hi := (29223271 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((798057327403 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(798057327403 / 500000000000) = 1/(500000000000 / 798057327403) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11767 : Bounds (93514467 / 200000000) (29223271 / 62500000) (Real.log (798057327403 / 500000000000)) := by
  have h := reflection_log_11767_neg
  have he : Real.log (798057327403 / 500000000000) = -Real.log (500000000000 / 798057327403) := by
    rw [show ((798057327403 / 500000000000) : ℝ) = ((500000000000 / 798057327403) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11768_neg : (469654593 / 1000000000) ≤ -Real.log (1953125000 / 3123909453) ∧
    -Real.log (1953125000 / 3123909453) ≤ (234827297 / 500000000) := by
  have h := checkLog_sound (w := (1170784453 / 5077034453)) (n := 12)
    (lo := (469654593 / 1000000000)) (hi := (234827297 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3123909453 / 1953125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3123909453 / 1953125000) = 1/(1953125000 / 3123909453) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11768 : Bounds (469654593 / 1000000000) (234827297 / 500000000) (Real.log (3123909453 / 1953125000)) := by
  have h := reflection_log_11768_neg
  have he : Real.log (3123909453 / 1953125000) = -Real.log (1953125000 / 3123909453) := by
    rw [show ((3123909453 / 1953125000) : ℝ) = ((1953125000 / 3123909453) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11769_neg : (475957159 / 500000000) ≤ -Real.log (100000000000 / 259066427289) ∧
    -Real.log (100000000000 / 259066427289) ≤ (11898929 / 12500000) := by
  have h := checkLog_sound (w := (59066427289 / 459066427289)) (n := 12)
    (lo := (129383569 / 500000000)) (hi := (258767139 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((259066427289 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(259066427289 / 200000000000) = 1/(100000000000 / 259066427289) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11769 : Bounds (475957159 / 500000000) (11898929 / 12500000) (Real.log (259066427289 / 100000000000)) := by
  have h := reflection_log_11769_neg
  have he : Real.log (259066427289 / 100000000000) = -Real.log (100000000000 / 259066427289) := by
    rw [show ((259066427289 / 100000000000) : ℝ) = ((100000000000 / 259066427289) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11770_neg : (119300503 / 125000000) ≤ -Real.log (12500000000 / 32464028777) ∧
    -Real.log (12500000000 / 32464028777) ≤ (477202013 / 500000000) := by
  have h := checkLog_sound (w := (7464028777 / 57464028777)) (n := 12)
    (lo := (65314211 / 250000000)) (hi := (52251369 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((32464028777 / 25000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(32464028777 / 25000000000) = 1/(12500000000 / 32464028777) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11770 : Bounds (119300503 / 125000000) (477202013 / 500000000) (Real.log (32464028777 / 12500000000)) := by
  have h := reflection_log_11770_neg
  have he : Real.log (32464028777 / 12500000000) = -Real.log (12500000000 / 32464028777) := by
    rw [show ((32464028777 / 12500000000) : ℝ) = ((12500000000 / 32464028777) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11771_neg : (368109321 / 1000000000) ≤ -Real.log (200 / 289) ∧
    -Real.log (200 / 289) ≤ (184054661 / 500000000) := by
  have h := checkLog_sound (w := (89 / 489)) (n := 12)
    (lo := (368109321 / 1000000000)) (hi := (184054661 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((289 / 200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(289 / 200) = 1/(200 / 289) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11771 : Bounds (368109321 / 1000000000) (184054661 / 500000000) (Real.log (289 / 200)) := by
  have h := reflection_log_11771_neg
  have he : Real.log (289 / 200) = -Real.log (200 / 289) := by
    rw [show ((289 / 200) : ℝ) = ((200 / 289) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11772_neg : (117757433 / 200000000) ≤ -Real.log (111 / 200) ∧
    -Real.log (111 / 200) ≤ (294393583 / 500000000) := by
  have h := checkLog_sound (w := (89 / 311)) (n := 12)
    (lo := (117757433 / 200000000)) (hi := (294393583 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200 / 111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200 / 111) = 1/(111 / 200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11772 : Bounds (-294393583 / 500000000) (-117757433 / 200000000) (Real.log (111 / 200)) := by
  have h := reflection_log_11772_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11773_neg : (444901 / 1000000000) ≤ -Real.log (200000 / 200089) ∧
    -Real.log (200000 / 200089) ≤ (222451 / 500000000) := by
  have h := checkLog_sound (w := (89 / 400089)) (n := 12)
    (lo := (444901 / 1000000000)) (hi := (222451 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200089 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200089 / 200000) = 1/(200000 / 200089) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11773 : Bounds (444901 / 1000000000) (222451 / 500000000) (Real.log (200089 / 200000)) := by
  have h := reflection_log_11773_neg
  have he : Real.log (200089 / 200000) = -Real.log (200000 / 200089) := by
    rw [show ((200089 / 200000) : ℝ) = ((200000 / 200089) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11774_neg : (445099 / 1000000000) ≤ -Real.log (199911 / 200000) ∧
    -Real.log (199911 / 200000) ≤ (4451 / 10000000) := by
  have h := checkLog_sound (w := (89 / 399911)) (n := 12)
    (lo := (445099 / 1000000000)) (hi := (4451 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 199911) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 199911) = 1/(199911 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11774 : Bounds (-4451 / 10000000) (-445099 / 1000000000) (Real.log (199911 / 200000)) := by
  have h := reflection_log_11774_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11775_neg : (404604 / 1953125) ≤ -Real.log (31250 / 38443) ∧
    -Real.log (31250 / 38443) ≤ (207157249 / 1000000000) := by
  have h := checkLog_sound (w := (7193 / 69693)) (n := 12)
    (lo := (404604 / 1953125)) (hi := (207157249 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((38443 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(38443 / 31250) = 1/(31250 / 38443) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11775 : Bounds (404604 / 1953125) (207157249 / 1000000000) (Real.log (38443 / 31250)) := by
  have h := reflection_log_11775_neg
  have he : Real.log (38443 / 31250) = -Real.log (31250 / 38443) := by
    rw [show ((38443 / 31250) : ℝ) = ((31250 / 38443) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily
