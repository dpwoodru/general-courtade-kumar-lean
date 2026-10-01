import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_4736_neg : (88660849 / 1000000000) ≤ -Real.log (100000 / 109271) ∧
    -Real.log (100000 / 109271) ≤ (1773217 / 20000000) := by
  have h := checkLog_sound (w := (9271 / 209271)) (n := 12)
    (lo := (88660849 / 1000000000)) (hi := (1773217 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((109271 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(109271 / 100000) = 1/(100000 / 109271) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4736 : Bounds (88660849 / 1000000000) (1773217 / 20000000) (Real.log (109271 / 100000)) := by
  have h := reflection_log_4736_neg
  have he : Real.log (109271 / 100000) = -Real.log (100000 / 109271) := by
    rw [show ((109271 / 100000) : ℝ) = ((100000 / 109271) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4737_neg : (12161643 / 125000000) ≤ -Real.log (90729 / 100000) ∧
    -Real.log (90729 / 100000) ≤ (19458629 / 200000000) := by
  have h := checkLog_sound (w := (9271 / 190729)) (n := 12)
    (lo := (12161643 / 125000000)) (hi := (19458629 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 90729) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 90729) = 1/(90729 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4737 : Bounds (-19458629 / 200000000) (-12161643 / 125000000) (Real.log (90729 / 100000)) := by
  have h := reflection_log_4737_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4738_neg : (1726459 / 200000000) ≤ -Real.log (9914048559 / 10000000000) ∧
    -Real.log (9914048559 / 10000000000) ≤ (1079037 / 125000000) := by
  have h := checkLog_sound (w := (85951441 / 19914048559)) (n := 12)
    (lo := (1726459 / 200000000)) (hi := (1079037 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 9914048559) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 9914048559) = 1/(9914048559 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4738 : Bounds (-1079037 / 125000000) (-1726459 / 200000000) (Real.log (9914048559 / 10000000000)) := by
  have h := reflection_log_4738_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4739_neg : (21471 / 2500000) ≤ -Real.log (1586317399 / 1600000000) ∧
    -Real.log (1586317399 / 1600000000) ≤ (8588401 / 1000000000) := by
  have h := checkLog_sound (w := (13682601 / 3186317399)) (n := 12)
    (lo := (21471 / 2500000)) (hi := (8588401 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600000000 / 1586317399) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1600000000 / 1586317399) = 1/(1586317399 / 1600000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4739 : Bounds (-8588401 / 1000000000) (-21471 / 2500000) (Real.log (1586317399 / 1600000000)) := by
  have h := reflection_log_4739_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4740_neg : (185479929 / 1000000000) ≤ -Real.log (250000000000 / 300949009669) ∧
    -Real.log (250000000000 / 300949009669) ≤ (18547993 / 100000000) := by
  have h := checkLog_sound (w := (50949009669 / 550949009669)) (n := 12)
    (lo := (185479929 / 1000000000)) (hi := (18547993 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((300949009669 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(300949009669 / 250000000000) = 1/(250000000000 / 300949009669) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4740 : Bounds (185479929 / 1000000000) (18547993 / 100000000) (Real.log (300949009669 / 250000000000)) := by
  have h := reflection_log_4740_neg
  have he : Real.log (300949009669 / 250000000000) = -Real.log (250000000000 / 300949009669) := by
    rw [show ((300949009669 / 250000000000) : ℝ) = ((250000000000 / 300949009669) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4741_neg : (185953993 / 1000000000) ≤ -Real.log (250000000000 / 301091712683) ∧
    -Real.log (250000000000 / 301091712683) ≤ (92976997 / 500000000) := by
  have h := checkLog_sound (w := (51091712683 / 551091712683)) (n := 12)
    (lo := (185953993 / 1000000000)) (hi := (92976997 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((301091712683 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(301091712683 / 250000000000) = 1/(250000000000 / 301091712683) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4741 : Bounds (185953993 / 1000000000) (92976997 / 500000000) (Real.log (301091712683 / 250000000000)) := by
  have h := reflection_log_4741_neg
  have he : Real.log (301091712683 / 250000000000) = -Real.log (250000000000 / 301091712683) := by
    rw [show ((301091712683 / 250000000000) : ℝ) = ((250000000000 / 301091712683) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4742_neg : (18611973 / 50000000) ≤ -Real.log (250000000000 / 362745098039) ∧
    -Real.log (250000000000 / 362745098039) ≤ (372239461 / 1000000000) := by
  have h := checkLog_sound (w := (112745098039 / 612745098039)) (n := 12)
    (lo := (18611973 / 50000000)) (hi := (372239461 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((362745098039 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(362745098039 / 250000000000) = 1/(250000000000 / 362745098039) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4742 : Bounds (18611973 / 50000000) (372239461 / 1000000000) (Real.log (362745098039 / 250000000000)) := by
  have h := reflection_log_4742_neg
  have he : Real.log (362745098039 / 250000000000) = -Real.log (250000000000 / 362745098039) := by
    rw [show ((362745098039 / 250000000000) : ℝ) = ((250000000000 / 362745098039) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4743_neg : (46555809 / 125000000) ≤ -Real.log (125000000000 / 181410099277) ∧
    -Real.log (125000000000 / 181410099277) ≤ (372446473 / 1000000000) := by
  have h := checkLog_sound (w := (56410099277 / 306410099277)) (n := 12)
    (lo := (46555809 / 125000000)) (hi := (372446473 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((181410099277 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(181410099277 / 125000000000) = 1/(125000000000 / 181410099277) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4743 : Bounds (46555809 / 125000000) (372446473 / 1000000000) (Real.log (181410099277 / 125000000000)) := by
  have h := reflection_log_4743_neg
  have he : Real.log (181410099277 / 125000000000) = -Real.log (125000000000 / 181410099277) := by
    rw [show ((181410099277 / 125000000000) : ℝ) = ((125000000000 / 181410099277) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4744_neg : (169067441 / 1000000000) ≤ -Real.log (5000 / 5921) ∧
    -Real.log (5000 / 5921) ≤ (84533721 / 500000000) := by
  have h := checkLog_sound (w := (921 / 10921)) (n := 12)
    (lo := (169067441 / 1000000000)) (hi := (84533721 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5921 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5921 / 5000) = 1/(5000 / 5921) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4744 : Bounds (169067441 / 1000000000) (84533721 / 500000000) (Real.log (5921 / 5000)) := by
  have h := reflection_log_4744_neg
  have he : Real.log (5921 / 5000) = -Real.log (5000 / 5921) := by
    rw [show ((5921 / 5000) : ℝ) = ((5000 / 5921) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4745_neg : (50896513 / 250000000) ≤ -Real.log (4079 / 5000) ∧
    -Real.log (4079 / 5000) ≤ (203586053 / 1000000000) := by
  have h := checkLog_sound (w := (921 / 9079)) (n := 12)
    (lo := (50896513 / 250000000)) (hi := (203586053 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4079) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4079) = 1/(4079 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4745 : Bounds (-203586053 / 1000000000) (-50896513 / 250000000) (Real.log (4079 / 5000)) := by
  have h := reflection_log_4745_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4746_neg : (184183 / 1000000000) ≤ -Real.log (5000000 / 5000921) ∧
    -Real.log (5000000 / 5000921) ≤ (23023 / 125000000) := by
  have h := checkLog_sound (w := (921 / 10000921)) (n := 12)
    (lo := (184183 / 1000000000)) (hi := (23023 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000921 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000921 / 5000000) = 1/(5000000 / 5000921) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4746 : Bounds (184183 / 1000000000) (23023 / 125000000) (Real.log (5000921 / 5000000)) := by
  have h := reflection_log_4746_neg
  have he : Real.log (5000921 / 5000000) = -Real.log (5000000 / 5000921) := by
    rw [show ((5000921 / 5000000) : ℝ) = ((5000000 / 5000921) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4747_neg : (23027 / 125000000) ≤ -Real.log (4999079 / 5000000) ∧
    -Real.log (4999079 / 5000000) ≤ (184217 / 1000000000) := by
  have h := checkLog_sound (w := (921 / 9999079)) (n := 12)
    (lo := (23027 / 125000000)) (hi := (184217 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999079) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999079) = 1/(4999079 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4747 : Bounds (-184217 / 1000000000) (-23027 / 125000000) (Real.log (4999079 / 5000000)) := by
  have h := reflection_log_4747_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4748_neg : (44246223 / 500000000) ≤ -Real.log (500000 / 546263) ∧
    -Real.log (500000 / 546263) ≤ (88492447 / 1000000000) := by
  have h := checkLog_sound (w := (46263 / 1046263)) (n := 12)
    (lo := (44246223 / 500000000)) (hi := (88492447 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((546263 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(546263 / 500000) = 1/(500000 / 546263) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4748 : Bounds (44246223 / 500000000) (88492447 / 1000000000) (Real.log (546263 / 500000)) := by
  have h := reflection_log_4748_neg
  have he : Real.log (546263 / 500000) = -Real.log (500000 / 546263) := by
    rw [show ((546263 / 500000) : ℝ) = ((500000 / 546263) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4749_neg : (97090363 / 1000000000) ≤ -Real.log (453737 / 500000) ∧
    -Real.log (453737 / 500000) ≤ (24272591 / 250000000) := by
  have h := checkLog_sound (w := (46263 / 953737)) (n := 12)
    (lo := (97090363 / 1000000000)) (hi := (24272591 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 453737) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 453737) = 1/(453737 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4749 : Bounds (-24272591 / 250000000) (-97090363 / 1000000000) (Real.log (453737 / 500000)) := by
  have h := reflection_log_4749_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4750_neg : (88707521 / 1000000000) ≤ -Real.log (1000000 / 1092761) ∧
    -Real.log (1000000 / 1092761) ≤ (44353761 / 500000000) := by
  have h := checkLog_sound (w := (92761 / 2092761)) (n := 12)
    (lo := (88707521 / 1000000000)) (hi := (44353761 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1092761 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1092761 / 1000000) = 1/(1000000 / 1092761) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4750 : Bounds (88707521 / 1000000000) (44353761 / 500000000) (Real.log (1092761 / 1000000)) := by
  have h := reflection_log_4750_neg
  have he : Real.log (1092761 / 1000000) = -Real.log (1000000 / 1092761) := by
    rw [show ((1092761 / 1000000) : ℝ) = ((1000000 / 1092761) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4751_neg : (97349357 / 1000000000) ≤ -Real.log (907239 / 1000000) ∧
    -Real.log (907239 / 1000000) ≤ (48674679 / 500000000) := by
  have h := checkLog_sound (w := (92761 / 1907239)) (n := 12)
    (lo := (97349357 / 1000000000)) (hi := (48674679 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 907239) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 907239) = 1/(907239 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4751 : Bounds (-48674679 / 500000000) (-97349357 / 1000000000) (Real.log (907239 / 1000000)) := by
  have h := reflection_log_4751_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4752_neg : (2160459 / 250000000) ≤ -Real.log (991395396879 / 1000000000000) ∧
    -Real.log (991395396879 / 1000000000000) ≤ (8641837 / 1000000000) := by
  have h := checkLog_sound (w := (8604603121 / 1991395396879)) (n := 12)
    (lo := (2160459 / 250000000)) (hi := (8641837 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 991395396879) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 991395396879) = 1/(991395396879 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4752 : Bounds (-8641837 / 1000000000) (-2160459 / 250000000) (Real.log (991395396879 / 1000000000000)) := by
  have h := reflection_log_4752_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4753_neg : (8597917 / 1000000000) ≤ -Real.log (247859734831 / 250000000000) ∧
    -Real.log (247859734831 / 250000000000) ≤ (4298959 / 500000000) := by
  have h := checkLog_sound (w := (2140265169 / 497859734831)) (n := 12)
    (lo := (8597917 / 1000000000)) (hi := (4298959 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247859734831) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247859734831) = 1/(247859734831 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4753 : Bounds (-4298959 / 500000000) (-8597917 / 1000000000) (Real.log (247859734831 / 250000000000)) := by
  have h := reflection_log_4753_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4754_neg : (185582809 / 1000000000) ≤ -Real.log (500000000000 / 601959945959) ∧
    -Real.log (500000000000 / 601959945959) ≤ (18558281 / 100000000) := by
  have h := checkLog_sound (w := (101959945959 / 1101959945959)) (n := 12)
    (lo := (185582809 / 1000000000)) (hi := (18558281 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((601959945959 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(601959945959 / 500000000000) = 1/(500000000000 / 601959945959) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4754 : Bounds (185582809 / 1000000000) (18558281 / 100000000) (Real.log (601959945959 / 500000000000)) := by
  have h := reflection_log_4754_neg
  have he : Real.log (601959945959 / 500000000000) = -Real.log (500000000000 / 601959945959) := by
    rw [show ((601959945959 / 500000000000) : ℝ) = ((500000000000 / 601959945959) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4755_neg : (93028439 / 500000000) ≤ -Real.log (62500000000 / 75280673009) ∧
    -Real.log (62500000000 / 75280673009) ≤ (186056879 / 1000000000) := by
  have h := checkLog_sound (w := (12780673009 / 137780673009)) (n := 12)
    (lo := (93028439 / 500000000)) (hi := (186056879 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((75280673009 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(75280673009 / 62500000000) = 1/(62500000000 / 75280673009) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4755 : Bounds (93028439 / 500000000) (186056879 / 1000000000) (Real.log (75280673009 / 62500000000)) := by
  have h := reflection_log_4755_neg
  have he : Real.log (75280673009 / 62500000000) = -Real.log (62500000000 / 75280673009) := by
    rw [show ((75280673009 / 62500000000) : ℝ) = ((62500000000 / 75280673009) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4756_neg : (46555809 / 125000000) ≤ -Real.log (500000000000 / 725640397107) ∧
    -Real.log (500000000000 / 725640397107) ≤ (372446473 / 1000000000) := by
  have h := checkLog_sound (w := (225640397107 / 1225640397107)) (n := 12)
    (lo := (46555809 / 125000000)) (hi := (372446473 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((725640397107 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(725640397107 / 500000000000) = 1/(500000000000 / 725640397107) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4756 : Bounds (46555809 / 125000000) (372446473 / 1000000000) (Real.log (725640397107 / 500000000000)) := by
  have h := reflection_log_4756_neg
  have he : Real.log (725640397107 / 500000000000) = -Real.log (500000000000 / 725640397107) := by
    rw [show ((725640397107 / 500000000000) : ℝ) = ((500000000000 / 725640397107) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4757_neg : (372653493 / 1000000000) ≤ -Real.log (6250000000 / 9072382937) ∧
    -Real.log (6250000000 / 9072382937) ≤ (186326747 / 500000000) := by
  have h := checkLog_sound (w := (2822382937 / 15322382937)) (n := 12)
    (lo := (372653493 / 1000000000)) (hi := (186326747 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9072382937 / 6250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(9072382937 / 6250000000) = 1/(6250000000 / 9072382937) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4757 : Bounds (372653493 / 1000000000) (186326747 / 500000000) (Real.log (9072382937 / 6250000000)) := by
  have h := reflection_log_4757_neg
  have he : Real.log (9072382937 / 6250000000) = -Real.log (6250000000 / 9072382937) := by
    rw [show ((9072382937 / 6250000000) : ℝ) = ((6250000000 / 9072382937) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4758_neg : (84575941 / 500000000) ≤ -Real.log (10000 / 11843) ∧
    -Real.log (10000 / 11843) ≤ (169151883 / 1000000000) := by
  have h := checkLog_sound (w := (1843 / 21843)) (n := 12)
    (lo := (84575941 / 500000000)) (hi := (169151883 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11843 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11843 / 10000) = 1/(10000 / 11843) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4758 : Bounds (84575941 / 500000000) (169151883 / 1000000000) (Real.log (11843 / 10000)) := by
  have h := reflection_log_4758_neg
  have he : Real.log (11843 / 10000) = -Real.log (10000 / 11843) := by
    rw [show ((11843 / 10000) : ℝ) = ((10000 / 11843) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4759_neg : (101854319 / 500000000) ≤ -Real.log (8157 / 10000) ∧
    -Real.log (8157 / 10000) ≤ (203708639 / 1000000000) := by
  have h := checkLog_sound (w := (1843 / 18157)) (n := 12)
    (lo := (101854319 / 500000000)) (hi := (203708639 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8157) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8157) = 1/(8157 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4759 : Bounds (-203708639 / 1000000000) (-101854319 / 500000000) (Real.log (8157 / 10000)) := by
  have h := reflection_log_4759_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4760_neg : (184283 / 1000000000) ≤ -Real.log (10000000 / 10001843) ∧
    -Real.log (10000000 / 10001843) ≤ (46071 / 250000000) := by
  have h := checkLog_sound (w := (1843 / 20001843)) (n := 12)
    (lo := (184283 / 1000000000)) (hi := (46071 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001843 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001843 / 10000000) = 1/(10000000 / 10001843) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4760 : Bounds (184283 / 1000000000) (46071 / 250000000) (Real.log (10001843 / 10000000)) := by
  have h := reflection_log_4760_neg
  have he : Real.log (10001843 / 10000000) = -Real.log (10000000 / 10001843) := by
    rw [show ((10001843 / 10000000) : ℝ) = ((10000000 / 10001843) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4761_neg : (46079 / 250000000) ≤ -Real.log (9998157 / 10000000) ∧
    -Real.log (9998157 / 10000000) ≤ (184317 / 1000000000) := by
  have h := checkLog_sound (w := (1843 / 19998157)) (n := 12)
    (lo := (46079 / 250000000)) (hi := (184317 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998157) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998157) = 1/(9998157 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4761 : Bounds (-184317 / 1000000000) (-46079 / 250000000) (Real.log (9998157 / 10000000)) := by
  have h := reflection_log_4761_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4762_neg : (44269563 / 500000000) ≤ -Real.log (1000000 / 1092577) ∧
    -Real.log (1000000 / 1092577) ≤ (88539127 / 1000000000) := by
  have h := checkLog_sound (w := (92577 / 2092577)) (n := 12)
    (lo := (44269563 / 500000000)) (hi := (88539127 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1092577 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1092577 / 1000000) = 1/(1000000 / 1092577) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4762 : Bounds (44269563 / 500000000) (88539127 / 1000000000) (Real.log (1092577 / 1000000)) := by
  have h := reflection_log_4762_neg
  have he : Real.log (1092577 / 1000000) = -Real.log (1000000 / 1092577) := by
    rw [show ((1092577 / 1000000) : ℝ) = ((1000000 / 1092577) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4763_neg : (24286641 / 250000000) ≤ -Real.log (907423 / 1000000) ∧
    -Real.log (907423 / 1000000) ≤ (19429313 / 200000000) := by
  have h := checkLog_sound (w := (92577 / 1907423)) (n := 12)
    (lo := (24286641 / 250000000)) (hi := (19429313 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 907423) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 907423) = 1/(907423 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4763 : Bounds (-19429313 / 200000000) (-24286641 / 250000000) (Real.log (907423 / 1000000)) := by
  have h := reflection_log_4763_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4764_neg : (8875419 / 100000000) ≤ -Real.log (250000 / 273203) ∧
    -Real.log (250000 / 273203) ≤ (88754191 / 1000000000) := by
  have h := checkLog_sound (w := (23203 / 523203)) (n := 12)
    (lo := (8875419 / 100000000)) (hi := (88754191 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((273203 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(273203 / 250000) = 1/(250000 / 273203) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4764 : Bounds (8875419 / 100000000) (88754191 / 1000000000) (Real.log (273203 / 250000)) := by
  have h := reflection_log_4764_neg
  have he : Real.log (273203 / 250000) = -Real.log (250000 / 273203) := by
    rw [show ((273203 / 250000) : ℝ) = ((250000 / 273203) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4765_neg : (97405573 / 1000000000) ≤ -Real.log (226797 / 250000) ∧
    -Real.log (226797 / 250000) ≤ (48702787 / 500000000) := by
  have h := checkLog_sound (w := (23203 / 476797)) (n := 12)
    (lo := (97405573 / 1000000000)) (hi := (48702787 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 226797) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 226797) = 1/(226797 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4765 : Bounds (-48702787 / 500000000) (-97405573 / 1000000000) (Real.log (226797 / 250000)) := by
  have h := reflection_log_4765_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4766_neg : (4325691 / 500000000) ≤ -Real.log (61961620791 / 62500000000) ∧
    -Real.log (61961620791 / 62500000000) ≤ (8651383 / 1000000000) := by
  have h := checkLog_sound (w := (538379209 / 124461620791)) (n := 12)
    (lo := (4325691 / 500000000)) (hi := (8651383 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 61961620791) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 61961620791) = 1/(61961620791 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4766 : Bounds (-8651383 / 1000000000) (-4325691 / 500000000) (Real.log (61961620791 / 62500000000)) := by
  have h := reflection_log_4766_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4767_neg : (4303719 / 500000000) ≤ -Real.log (991429499071 / 1000000000000) ∧
    -Real.log (991429499071 / 1000000000000) ≤ (8607439 / 1000000000) := by
  have h := checkLog_sound (w := (8570500929 / 1991429499071)) (n := 12)
    (lo := (4303719 / 500000000)) (hi := (8607439 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 991429499071) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 991429499071) = 1/(991429499071 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4767 : Bounds (-8607439 / 1000000000) (-4303719 / 500000000) (Real.log (991429499071 / 1000000000000)) := by
  have h := reflection_log_4767_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4768_neg : (18568569 / 100000000) ≤ -Real.log (250000000000 / 301010939771) ∧
    -Real.log (250000000000 / 301010939771) ≤ (185685691 / 1000000000) := by
  have h := checkLog_sound (w := (51010939771 / 551010939771)) (n := 12)
    (lo := (18568569 / 100000000)) (hi := (185685691 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((301010939771 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(301010939771 / 250000000000) = 1/(250000000000 / 301010939771) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4768 : Bounds (18568569 / 100000000) (185685691 / 1000000000) (Real.log (301010939771 / 250000000000)) := by
  have h := reflection_log_4768_neg
  have he : Real.log (301010939771 / 250000000000) = -Real.log (250000000000 / 301010939771) := by
    rw [show ((301010939771 / 250000000000) : ℝ) = ((250000000000 / 301010939771) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4769_neg : (46539941 / 250000000) ≤ -Real.log (100000000000 / 120461469949) ∧
    -Real.log (100000000000 / 120461469949) ≤ (37231953 / 200000000) := by
  have h := checkLog_sound (w := (20461469949 / 220461469949)) (n := 12)
    (lo := (46539941 / 250000000)) (hi := (37231953 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((120461469949 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(120461469949 / 100000000000) = 1/(100000000000 / 120461469949) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4769 : Bounds (46539941 / 250000000) (37231953 / 200000000) (Real.log (120461469949 / 100000000000)) := by
  have h := reflection_log_4769_neg
  have he : Real.log (120461469949 / 100000000000) = -Real.log (100000000000 / 120461469949) := by
    rw [show ((120461469949 / 100000000000) : ℝ) = ((100000000000 / 120461469949) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4770_neg : (372653493 / 1000000000) ≤ -Real.log (500000000000 / 725790634959) ∧
    -Real.log (500000000000 / 725790634959) ≤ (186326747 / 500000000) := by
  have h := checkLog_sound (w := (225790634959 / 1225790634959)) (n := 12)
    (lo := (372653493 / 1000000000)) (hi := (186326747 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((725790634959 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(725790634959 / 500000000000) = 1/(500000000000 / 725790634959) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4770 : Bounds (372653493 / 1000000000) (186326747 / 500000000) (Real.log (725790634959 / 500000000000)) := by
  have h := reflection_log_4770_neg
  have he : Real.log (725790634959 / 500000000000) = -Real.log (500000000000 / 725790634959) := by
    rw [show ((725790634959 / 500000000000) : ℝ) = ((500000000000 / 725790634959) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4771_neg : (372860521 / 1000000000) ≤ -Real.log (500000000000 / 725940909649) ∧
    -Real.log (500000000000 / 725940909649) ≤ (186430261 / 500000000) := by
  have h := checkLog_sound (w := (225940909649 / 1225940909649)) (n := 12)
    (lo := (372860521 / 1000000000)) (hi := (186430261 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((725940909649 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(725940909649 / 500000000000) = 1/(500000000000 / 725940909649) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4771 : Bounds (372860521 / 1000000000) (186430261 / 500000000) (Real.log (725940909649 / 500000000000)) := by
  have h := reflection_log_4771_neg
  have he : Real.log (725940909649 / 500000000000) = -Real.log (500000000000 / 725940909649) := by
    rw [show ((725940909649 / 500000000000) : ℝ) = ((500000000000 / 725940909649) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4772_neg : (169236317 / 1000000000) ≤ -Real.log (2500 / 2961) ∧
    -Real.log (2500 / 2961) ≤ (84618159 / 500000000) := by
  have h := checkLog_sound (w := (461 / 5461)) (n := 12)
    (lo := (169236317 / 1000000000)) (hi := (84618159 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2961 / 2500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2961 / 2500) = 1/(2500 / 2961) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4772 : Bounds (169236317 / 1000000000) (84618159 / 500000000) (Real.log (2961 / 2500)) := by
  have h := reflection_log_4772_neg
  have he : Real.log (2961 / 2500) = -Real.log (2500 / 2961) := by
    rw [show ((2961 / 2500) : ℝ) = ((2500 / 2961) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4773_neg : (5095781 / 25000000) ≤ -Real.log (2039 / 2500) ∧
    -Real.log (2039 / 2500) ≤ (203831241 / 1000000000) := by
  have h := checkLog_sound (w := (461 / 4539)) (n := 12)
    (lo := (5095781 / 25000000)) (hi := (203831241 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500 / 2039) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500 / 2039) = 1/(2039 / 2500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4773 : Bounds (-203831241 / 1000000000) (-5095781 / 25000000) (Real.log (2039 / 2500)) := by
  have h := reflection_log_4773_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4774_neg : (184383 / 1000000000) ≤ -Real.log (2500000 / 2500461) ∧
    -Real.log (2500000 / 2500461) ≤ (2881 / 15625000) := by
  have h := checkLog_sound (w := (461 / 5000461)) (n := 12)
    (lo := (184383 / 1000000000)) (hi := (2881 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500461 / 2500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500461 / 2500000) = 1/(2500000 / 2500461) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4774 : Bounds (184383 / 1000000000) (2881 / 15625000) (Real.log (2500461 / 2500000)) := by
  have h := reflection_log_4774_neg
  have he : Real.log (2500461 / 2500000) = -Real.log (2500000 / 2500461) := by
    rw [show ((2500461 / 2500000) : ℝ) = ((2500000 / 2500461) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4775_neg : (184417 / 1000000000) ≤ -Real.log (2499539 / 2500000) ∧
    -Real.log (2499539 / 2500000) ≤ (92209 / 500000000) := by
  have h := checkLog_sound (w := (461 / 4999539)) (n := 12)
    (lo := (184417 / 1000000000)) (hi := (92209 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000 / 2499539) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000 / 2499539) = 1/(2499539 / 2500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4775 : Bounds (-92209 / 500000000) (-184417 / 1000000000) (Real.log (2499539 / 2500000)) := by
  have h := reflection_log_4775_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4776_neg : (88585803 / 1000000000) ≤ -Real.log (250000 / 273157) ∧
    -Real.log (250000 / 273157) ≤ (22146451 / 250000000) := by
  have h := checkLog_sound (w := (23157 / 523157)) (n := 12)
    (lo := (88585803 / 1000000000)) (hi := (22146451 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((273157 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(273157 / 250000) = 1/(250000 / 273157) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4776 : Bounds (88585803 / 1000000000) (22146451 / 250000000) (Real.log (273157 / 250000)) := by
  have h := reflection_log_4776_neg
  have he : Real.log (273157 / 250000) = -Real.log (250000 / 273157) := by
    rw [show ((273157 / 250000) : ℝ) = ((250000 / 273157) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4777_neg : (97202769 / 1000000000) ≤ -Real.log (226843 / 250000) ∧
    -Real.log (226843 / 250000) ≤ (9720277 / 100000000) := by
  have h := checkLog_sound (w := (23157 / 476843)) (n := 12)
    (lo := (97202769 / 1000000000)) (hi := (9720277 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 226843) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 226843) = 1/(226843 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4777 : Bounds (-9720277 / 100000000) (-97202769 / 1000000000) (Real.log (226843 / 250000)) := by
  have h := reflection_log_4777_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4778_neg : (44400429 / 500000000) ≤ -Real.log (1000000 / 1092863) ∧
    -Real.log (1000000 / 1092863) ≤ (88800859 / 1000000000) := by
  have h := checkLog_sound (w := (92863 / 2092863)) (n := 12)
    (lo := (44400429 / 500000000)) (hi := (88800859 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1092863 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1092863 / 1000000) = 1/(1000000 / 1092863) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4778 : Bounds (44400429 / 500000000) (88800859 / 1000000000) (Real.log (1092863 / 1000000)) := by
  have h := reflection_log_4778_neg
  have he : Real.log (1092863 / 1000000) = -Real.log (1000000 / 1092863) := by
    rw [show ((1092863 / 1000000) : ℝ) = ((1000000 / 1092863) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4779_neg : (3045681 / 31250000) ≤ -Real.log (907137 / 1000000) ∧
    -Real.log (907137 / 1000000) ≤ (97461793 / 1000000000) := by
  have h := checkLog_sound (w := (92863 / 1907137)) (n := 12)
    (lo := (3045681 / 31250000)) (hi := (97461793 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 907137) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 907137) = 1/(907137 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4779 : Bounds (-97461793 / 1000000000) (-3045681 / 31250000) (Real.log (907137 / 1000000)) := by
  have h := reflection_log_4779_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4780_neg : (4330467 / 500000000) ≤ -Real.log (991376463231 / 1000000000000) ∧
    -Real.log (991376463231 / 1000000000000) ≤ (1732187 / 200000000) := by
  have h := checkLog_sound (w := (8623536769 / 1991376463231)) (n := 12)
    (lo := (4330467 / 500000000)) (hi := (1732187 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 991376463231) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 991376463231) = 1/(991376463231 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4780 : Bounds (-1732187 / 200000000) (-4330467 / 500000000) (Real.log (991376463231 / 1000000000000)) := by
  have h := reflection_log_4780_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4781_neg : (4308483 / 500000000) ≤ -Real.log (61963753351 / 62500000000) ∧
    -Real.log (61963753351 / 62500000000) ≤ (8616967 / 1000000000) := by
  have h := checkLog_sound (w := (536246649 / 124463753351)) (n := 12)
    (lo := (4308483 / 500000000)) (hi := (8616967 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 61963753351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 61963753351) = 1/(61963753351 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4781 : Bounds (-8616967 / 1000000000) (-4308483 / 500000000) (Real.log (61963753351 / 62500000000)) := by
  have h := reflection_log_4781_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4782_neg : (185788573 / 1000000000) ≤ -Real.log (500000000000 / 602083820087) ∧
    -Real.log (500000000000 / 602083820087) ≤ (92894287 / 500000000) := by
  have h := checkLog_sound (w := (102083820087 / 1102083820087)) (n := 12)
    (lo := (185788573 / 1000000000)) (hi := (92894287 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((602083820087 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(602083820087 / 500000000000) = 1/(500000000000 / 602083820087) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4782 : Bounds (185788573 / 1000000000) (92894287 / 500000000) (Real.log (602083820087 / 500000000000)) := by
  have h := reflection_log_4782_neg
  have he : Real.log (602083820087 / 500000000000) = -Real.log (500000000000 / 602083820087) := by
    rw [show ((602083820087 / 500000000000) : ℝ) = ((500000000000 / 602083820087) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4783_neg : (186262651 / 1000000000) ≤ -Real.log (100000000000 / 120473864477) ∧
    -Real.log (100000000000 / 120473864477) ≤ (46565663 / 250000000) := by
  have h := checkLog_sound (w := (20473864477 / 220473864477)) (n := 12)
    (lo := (186262651 / 1000000000)) (hi := (46565663 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((120473864477 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(120473864477 / 100000000000) = 1/(100000000000 / 120473864477) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4783 : Bounds (186262651 / 1000000000) (46565663 / 250000000) (Real.log (120473864477 / 100000000000)) := by
  have h := reflection_log_4783_neg
  have he : Real.log (120473864477 / 100000000000) = -Real.log (100000000000 / 120473864477) := by
    rw [show ((120473864477 / 100000000000) : ℝ) = ((100000000000 / 120473864477) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4784_neg : (372860521 / 1000000000) ≤ -Real.log (31250000000 / 45371306853) ∧
    -Real.log (31250000000 / 45371306853) ≤ (186430261 / 500000000) := by
  have h := checkLog_sound (w := (14121306853 / 76621306853)) (n := 12)
    (lo := (372860521 / 1000000000)) (hi := (186430261 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((45371306853 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(45371306853 / 31250000000) = 1/(31250000000 / 45371306853) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4784 : Bounds (372860521 / 1000000000) (186430261 / 500000000) (Real.log (45371306853 / 31250000000)) := by
  have h := reflection_log_4784_neg
  have he : Real.log (45371306853 / 31250000000) = -Real.log (31250000000 / 45371306853) := by
    rw [show ((45371306853 / 31250000000) : ℝ) = ((31250000000 / 45371306853) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4785_neg : (373067557 / 1000000000) ≤ -Real.log (500000000000 / 726091221187) ∧
    -Real.log (500000000000 / 726091221187) ≤ (186533779 / 500000000) := by
  have h := checkLog_sound (w := (226091221187 / 1226091221187)) (n := 12)
    (lo := (373067557 / 1000000000)) (hi := (186533779 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((726091221187 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(726091221187 / 500000000000) = 1/(500000000000 / 726091221187) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4785 : Bounds (373067557 / 1000000000) (186533779 / 500000000) (Real.log (726091221187 / 500000000000)) := by
  have h := reflection_log_4785_neg
  have he : Real.log (726091221187 / 500000000000) = -Real.log (500000000000 / 726091221187) := by
    rw [show ((726091221187 / 500000000000) : ℝ) = ((500000000000 / 726091221187) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4786_neg : (21165093 / 125000000) ≤ -Real.log (2000 / 2369) ∧
    -Real.log (2000 / 2369) ≤ (33864149 / 200000000) := by
  have h := checkLog_sound (w := (369 / 4369)) (n := 12)
    (lo := (21165093 / 125000000)) (hi := (33864149 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2369 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2369 / 2000) = 1/(2000 / 2369) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4786 : Bounds (21165093 / 125000000) (33864149 / 200000000) (Real.log (2369 / 2000)) := by
  have h := reflection_log_4786_neg
  have he : Real.log (2369 / 2000) = -Real.log (2000 / 2369) := by
    rw [show ((2369 / 2000) : ℝ) = ((2000 / 2369) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4787_neg : (3186779 / 15625000) ≤ -Real.log (1631 / 2000) ∧
    -Real.log (1631 / 2000) ≤ (203953857 / 1000000000) := by
  have h := checkLog_sound (w := (369 / 3631)) (n := 12)
    (lo := (3186779 / 15625000)) (hi := (203953857 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1631) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1631) = 1/(1631 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4787 : Bounds (-203953857 / 1000000000) (-3186779 / 15625000) (Real.log (1631 / 2000)) := by
  have h := reflection_log_4787_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4788_neg : (92241 / 500000000) ≤ -Real.log (2000000 / 2000369) ∧
    -Real.log (2000000 / 2000369) ≤ (184483 / 1000000000) := by
  have h := checkLog_sound (w := (369 / 4000369)) (n := 12)
    (lo := (92241 / 500000000)) (hi := (184483 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000369 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000369 / 2000000) = 1/(2000000 / 2000369) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4788 : Bounds (92241 / 500000000) (184483 / 1000000000) (Real.log (2000369 / 2000000)) := by
  have h := reflection_log_4788_neg
  have he : Real.log (2000369 / 2000000) = -Real.log (2000000 / 2000369) := by
    rw [show ((2000369 / 2000000) : ℝ) = ((2000000 / 2000369) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4789_neg : (184517 / 1000000000) ≤ -Real.log (1999631 / 2000000) ∧
    -Real.log (1999631 / 2000000) ≤ (92259 / 500000000) := by
  have h := checkLog_sound (w := (369 / 3999631)) (n := 12)
    (lo := (184517 / 1000000000)) (hi := (92259 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999631) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999631) = 1/(1999631 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4789 : Bounds (-92259 / 500000000) (-184517 / 1000000000) (Real.log (1999631 / 2000000)) := by
  have h := reflection_log_4789_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4790_neg : (44316239 / 500000000) ≤ -Real.log (1000000 / 1092679) ∧
    -Real.log (1000000 / 1092679) ≤ (88632479 / 1000000000) := by
  have h := checkLog_sound (w := (92679 / 2092679)) (n := 12)
    (lo := (44316239 / 500000000)) (hi := (88632479 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1092679 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1092679 / 1000000) = 1/(1000000 / 1092679) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4790 : Bounds (44316239 / 500000000) (88632479 / 1000000000) (Real.log (1092679 / 1000000)) := by
  have h := reflection_log_4790_neg
  have he : Real.log (1092679 / 1000000) = -Real.log (1000000 / 1092679) := by
    rw [show ((1092679 / 1000000) : ℝ) = ((1000000 / 1092679) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4791_neg : (97258977 / 1000000000) ≤ -Real.log (907321 / 1000000) ∧
    -Real.log (907321 / 1000000) ≤ (48629489 / 500000000) := by
  have h := checkLog_sound (w := (92679 / 1907321)) (n := 12)
    (lo := (97258977 / 1000000000)) (hi := (48629489 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 907321) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 907321) = 1/(907321 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4791 : Bounds (-48629489 / 500000000) (-97258977 / 1000000000) (Real.log (907321 / 1000000)) := by
  have h := reflection_log_4791_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4792_neg : (88847523 / 1000000000) ≤ -Real.log (500000 / 546457) ∧
    -Real.log (500000 / 546457) ≤ (22211881 / 250000000) := by
  have h := checkLog_sound (w := (46457 / 1046457)) (n := 12)
    (lo := (88847523 / 1000000000)) (hi := (22211881 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((546457 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(546457 / 500000) = 1/(500000 / 546457) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4792 : Bounds (88847523 / 1000000000) (22211881 / 250000000) (Real.log (546457 / 500000)) := by
  have h := reflection_log_4792_neg
  have he : Real.log (546457 / 500000) = -Real.log (500000 / 546457) := by
    rw [show ((546457 / 500000) : ℝ) = ((500000 / 546457) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4793_neg : (19503603 / 200000000) ≤ -Real.log (453543 / 500000) ∧
    -Real.log (453543 / 500000) ≤ (1523719 / 15625000) := by
  have h := checkLog_sound (w := (46457 / 953543)) (n := 12)
    (lo := (19503603 / 200000000)) (hi := (1523719 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 453543) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 453543) = 1/(453543 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4793 : Bounds (-1523719 / 15625000) (-19503603 / 200000000) (Real.log (453543 / 500000)) := by
  have h := reflection_log_4793_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4794_neg : (8670491 / 1000000000) ≤ -Real.log (247841747151 / 250000000000) ∧
    -Real.log (247841747151 / 250000000000) ≤ (2167623 / 250000000) := by
  have h := checkLog_sound (w := (2158252849 / 497841747151)) (n := 12)
    (lo := (8670491 / 1000000000)) (hi := (2167623 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247841747151) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247841747151) = 1/(247841747151 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4794 : Bounds (-2167623 / 250000000) (-8670491 / 1000000000) (Real.log (247841747151 / 250000000000)) := by
  have h := reflection_log_4794_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4795_neg : (4313249 / 500000000) ≤ -Real.log (991410602959 / 1000000000000) ∧
    -Real.log (991410602959 / 1000000000000) ≤ (8626499 / 1000000000) := by
  have h := checkLog_sound (w := (8589397041 / 1991410602959)) (n := 12)
    (lo := (4313249 / 500000000)) (hi := (8626499 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 991410602959) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 991410602959) = 1/(991410602959 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4795 : Bounds (-8626499 / 1000000000) (-4313249 / 500000000) (Real.log (991410602959 / 1000000000000)) := by
  have h := reflection_log_4795_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4796_neg : (1452277 / 7812500) ≤ -Real.log (250000000000 / 301072883797) ∧
    -Real.log (250000000000 / 301072883797) ≤ (185891457 / 1000000000) := by
  have h := checkLog_sound (w := (51072883797 / 551072883797)) (n := 12)
    (lo := (1452277 / 7812500)) (hi := (185891457 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((301072883797 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(301072883797 / 250000000000) = 1/(250000000000 / 301072883797) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4796 : Bounds (1452277 / 7812500) (185891457 / 1000000000) (Real.log (301072883797 / 250000000000)) := by
  have h := reflection_log_4796_neg
  have he : Real.log (301072883797 / 250000000000) = -Real.log (250000000000 / 301072883797) := by
    rw [show ((301072883797 / 250000000000) : ℝ) = ((250000000000 / 301072883797) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4797_neg : (93182769 / 500000000) ≤ -Real.log (250000000000 / 301215650997) ∧
    -Real.log (250000000000 / 301215650997) ≤ (186365539 / 1000000000) := by
  have h := checkLog_sound (w := (51215650997 / 551215650997)) (n := 12)
    (lo := (93182769 / 500000000)) (hi := (186365539 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((301215650997 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(301215650997 / 250000000000) = 1/(250000000000 / 301215650997) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4797 : Bounds (93182769 / 500000000) (186365539 / 1000000000) (Real.log (301215650997 / 250000000000)) := by
  have h := reflection_log_4797_neg
  have he : Real.log (301215650997 / 250000000000) = -Real.log (250000000000 / 301215650997) := by
    rw [show ((301215650997 / 250000000000) : ℝ) = ((250000000000 / 301215650997) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4798_neg : (373067557 / 1000000000) ≤ -Real.log (250000000000 / 363045610593) ∧
    -Real.log (250000000000 / 363045610593) ≤ (186533779 / 500000000) := by
  have h := checkLog_sound (w := (113045610593 / 613045610593)) (n := 12)
    (lo := (373067557 / 1000000000)) (hi := (186533779 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((363045610593 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(363045610593 / 250000000000) = 1/(250000000000 / 363045610593) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4798 : Bounds (373067557 / 1000000000) (186533779 / 500000000) (Real.log (363045610593 / 250000000000)) := by
  have h := reflection_log_4798_neg
  have he : Real.log (363045610593 / 250000000000) = -Real.log (250000000000 / 363045610593) := by
    rw [show ((363045610593 / 250000000000) : ℝ) = ((250000000000 / 363045610593) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4799_neg : (373274601 / 1000000000) ≤ -Real.log (50000000000 / 72624156959) ∧
    -Real.log (50000000000 / 72624156959) ≤ (186637301 / 500000000) := by
  have h := checkLog_sound (w := (22624156959 / 122624156959)) (n := 12)
    (lo := (373274601 / 1000000000)) (hi := (186637301 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((72624156959 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(72624156959 / 50000000000) = 1/(50000000000 / 72624156959) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4799 : Bounds (373274601 / 1000000000) (186637301 / 500000000) (Real.log (72624156959 / 50000000000)) := by
  have h := reflection_log_4799_neg
  have he : Real.log (72624156959 / 50000000000) = -Real.log (50000000000 / 72624156959) := by
    rw [show ((72624156959 / 50000000000) : ℝ) = ((50000000000 / 72624156959) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily
