import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_4608_neg : (22006611 / 250000000) ≤ -Real.log (1000000 / 1092017) ∧
    -Real.log (1000000 / 1092017) ≤ (17605289 / 200000000) := by
  have h := checkLog_sound (w := (92017 / 2092017)) (n := 12)
    (lo := (22006611 / 250000000)) (hi := (17605289 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1092017 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1092017 / 1000000) = 1/(1000000 / 1092017) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4608 : Bounds (22006611 / 250000000) (17605289 / 200000000) (Real.log (1092017 / 1000000)) := by
  have h := reflection_log_4608_neg
  have he : Real.log (1092017 / 1000000) = -Real.log (1000000 / 1092017) := by
    rw [show ((1092017 / 1000000) : ℝ) = ((1000000 / 1092017) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4609_neg : (96529623 / 1000000000) ≤ -Real.log (907983 / 1000000) ∧
    -Real.log (907983 / 1000000) ≤ (12066203 / 125000000) := by
  have h := checkLog_sound (w := (92017 / 1907983)) (n := 12)
    (lo := (96529623 / 1000000000)) (hi := (12066203 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 907983) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 907983) = 1/(907983 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4609 : Bounds (-12066203 / 125000000) (-96529623 / 1000000000) (Real.log (907983 / 1000000)) := by
  have h := reflection_log_4609_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4610_neg : (1378761 / 15625000) ≤ -Real.log (1000000 / 1092251) ∧
    -Real.log (1000000 / 1092251) ≤ (17648141 / 200000000) := by
  have h := checkLog_sound (w := (92251 / 2092251)) (n := 12)
    (lo := (1378761 / 15625000)) (hi := (17648141 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1092251 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1092251 / 1000000) = 1/(1000000 / 1092251) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4610 : Bounds (1378761 / 15625000) (17648141 / 200000000) (Real.log (1092251 / 1000000)) := by
  have h := reflection_log_4610_neg
  have he : Real.log (1092251 / 1000000) = -Real.log (1000000 / 1092251) := by
    rw [show ((1092251 / 1000000) : ℝ) = ((1000000 / 1092251) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4611_neg : (9678737 / 100000000) ≤ -Real.log (907749 / 1000000) ∧
    -Real.log (907749 / 1000000) ≤ (96787371 / 1000000000) := by
  have h := checkLog_sound (w := (92251 / 1907749)) (n := 12)
    (lo := (9678737 / 100000000)) (hi := (96787371 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 907749) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 907749) = 1/(907749 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4611 : Bounds (-96787371 / 1000000000) (-9678737 / 100000000) (Real.log (907749 / 1000000)) := by
  have h := reflection_log_4611_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4612_neg : (1709333 / 200000000) ≤ -Real.log (991489752999 / 1000000000000) ∧
    -Real.log (991489752999 / 1000000000000) ≤ (4273333 / 500000000) := by
  have h := checkLog_sound (w := (8510247001 / 1991489752999)) (n := 12)
    (lo := (1709333 / 200000000)) (hi := (4273333 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 991489752999) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 991489752999) = 1/(991489752999 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4612 : Bounds (-4273333 / 500000000) (-1709333 / 200000000) (Real.log (991489752999 / 1000000000000)) := by
  have h := reflection_log_4612_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4613_neg : (4251589 / 500000000) ≤ -Real.log (991532871711 / 1000000000000) ∧
    -Real.log (991532871711 / 1000000000000) ≤ (8503179 / 1000000000) := by
  have h := checkLog_sound (w := (8467128289 / 1991532871711)) (n := 12)
    (lo := (4251589 / 500000000)) (hi := (8503179 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 991532871711) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 991532871711) = 1/(991532871711 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4613 : Bounds (-8503179 / 1000000000) (-4251589 / 500000000) (Real.log (991532871711 / 1000000000000)) := by
  have h := reflection_log_4613_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4614_neg : (184556067 / 1000000000) ≤ -Real.log (250000000000 / 300671102873) ∧
    -Real.log (250000000000 / 300671102873) ≤ (46139017 / 250000000) := by
  have h := checkLog_sound (w := (50671102873 / 550671102873)) (n := 12)
    (lo := (184556067 / 1000000000)) (hi := (46139017 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((300671102873 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(300671102873 / 250000000000) = 1/(250000000000 / 300671102873) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4614 : Bounds (184556067 / 1000000000) (46139017 / 250000000) (Real.log (300671102873 / 250000000000)) := by
  have h := reflection_log_4614_neg
  have he : Real.log (300671102873 / 250000000000) = -Real.log (250000000000 / 300671102873) := by
    rw [show ((300671102873 / 250000000000) : ℝ) = ((250000000000 / 300671102873) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4615_neg : (92514037 / 500000000) ≤ -Real.log (250000000000 / 300813055151) ∧
    -Real.log (250000000000 / 300813055151) ≤ (7401123 / 40000000) := by
  have h := checkLog_sound (w := (50813055151 / 550813055151)) (n := 12)
    (lo := (92514037 / 500000000)) (hi := (7401123 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((300813055151 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(300813055151 / 250000000000) = 1/(250000000000 / 300813055151) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4615 : Bounds (92514037 / 500000000) (7401123 / 40000000) (Real.log (300813055151 / 250000000000)) := by
  have h := reflection_log_4615_neg
  have he : Real.log (300813055151 / 250000000000) = -Real.log (250000000000 / 300813055151) := by
    rw [show ((300813055151 / 250000000000) : ℝ) = ((250000000000 / 300813055151) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4616_neg : (185188351 / 500000000) ≤ -Real.log (25000000000 / 36207002081) ∧
    -Real.log (25000000000 / 36207002081) ≤ (370376703 / 1000000000) := by
  have h := checkLog_sound (w := (11207002081 / 61207002081)) (n := 12)
    (lo := (185188351 / 500000000)) (hi := (370376703 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((36207002081 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(36207002081 / 25000000000) = 1/(25000000000 / 36207002081) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4616 : Bounds (185188351 / 500000000) (370376703 / 1000000000) (Real.log (36207002081 / 25000000000)) := by
  have h := reflection_log_4616_neg
  have he : Real.log (36207002081 / 25000000000) = -Real.log (25000000000 / 36207002081) := by
    rw [show ((36207002081 / 25000000000) : ℝ) = ((25000000000 / 36207002081) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4617_neg : (92645911 / 250000000) ≤ -Real.log (125000000000 / 181072477963) ∧
    -Real.log (125000000000 / 181072477963) ≤ (74116729 / 200000000) := by
  have h := checkLog_sound (w := (56072477963 / 306072477963)) (n := 12)
    (lo := (92645911 / 250000000)) (hi := (74116729 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((181072477963 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(181072477963 / 125000000000) = 1/(125000000000 / 181072477963) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4617 : Bounds (92645911 / 250000000) (74116729 / 200000000) (Real.log (181072477963 / 125000000000)) := by
  have h := reflection_log_4617_neg
  have he : Real.log (181072477963 / 125000000000) = -Real.log (125000000000 / 181072477963) := by
    rw [show ((181072477963 / 125000000000) : ℝ) = ((125000000000 / 181072477963) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4618_neg : (33661429 / 200000000) ≤ -Real.log (10000 / 11833) ∧
    -Real.log (10000 / 11833) ≤ (84153573 / 500000000) := by
  have h := checkLog_sound (w := (1833 / 21833)) (n := 12)
    (lo := (33661429 / 200000000)) (hi := (84153573 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11833 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11833 / 10000) = 1/(10000 / 11833) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4618 : Bounds (33661429 / 200000000) (84153573 / 500000000) (Real.log (11833 / 10000)) := by
  have h := reflection_log_4618_neg
  have he : Real.log (11833 / 10000) = -Real.log (10000 / 11833) := by
    rw [show ((11833 / 10000) : ℝ) = ((10000 / 11833) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4619_neg : (25310431 / 125000000) ≤ -Real.log (8167 / 10000) ∧
    -Real.log (8167 / 10000) ≤ (202483449 / 1000000000) := by
  have h := checkLog_sound (w := (1833 / 18167)) (n := 12)
    (lo := (25310431 / 125000000)) (hi := (202483449 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8167) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8167) = 1/(8167 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4619 : Bounds (-202483449 / 1000000000) (-25310431 / 125000000) (Real.log (8167 / 10000)) := by
  have h := reflection_log_4619_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4620_neg : (183283 / 1000000000) ≤ -Real.log (10000000 / 10001833) ∧
    -Real.log (10000000 / 10001833) ≤ (45821 / 250000000) := by
  have h := checkLog_sound (w := (1833 / 20001833)) (n := 12)
    (lo := (183283 / 1000000000)) (hi := (45821 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001833 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001833 / 10000000) = 1/(10000000 / 10001833) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4620 : Bounds (183283 / 1000000000) (45821 / 250000000) (Real.log (10001833 / 10000000)) := by
  have h := reflection_log_4620_neg
  have he : Real.log (10001833 / 10000000) = -Real.log (10000000 / 10001833) := by
    rw [show ((10001833 / 10000000) : ℝ) = ((10000000 / 10001833) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4621_neg : (45829 / 250000000) ≤ -Real.log (9998167 / 10000000) ∧
    -Real.log (9998167 / 10000000) ≤ (183317 / 1000000000) := by
  have h := checkLog_sound (w := (1833 / 19998167)) (n := 12)
    (lo := (45829 / 250000000)) (hi := (183317 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998167) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998167) = 1/(9998167 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4621 : Bounds (-183317 / 1000000000) (-45829 / 250000000) (Real.log (9998167 / 10000000)) := by
  have h := reflection_log_4621_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4622_neg : (44036573 / 500000000) ≤ -Real.log (250000 / 273017) ∧
    -Real.log (250000 / 273017) ≤ (88073147 / 1000000000) := by
  have h := checkLog_sound (w := (23017 / 523017)) (n := 12)
    (lo := (44036573 / 500000000)) (hi := (88073147 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((273017 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(273017 / 250000) = 1/(250000 / 273017) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4622 : Bounds (44036573 / 500000000) (88073147 / 1000000000) (Real.log (273017 / 250000)) := by
  have h := reflection_log_4622_neg
  have he : Real.log (273017 / 250000) = -Real.log (250000 / 273017) := by
    rw [show ((273017 / 250000) : ℝ) = ((250000 / 273017) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4623_neg : (96585793 / 1000000000) ≤ -Real.log (226983 / 250000) ∧
    -Real.log (226983 / 250000) ≤ (48292897 / 500000000) := by
  have h := checkLog_sound (w := (23017 / 476983)) (n := 12)
    (lo := (96585793 / 1000000000)) (hi := (48292897 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 226983) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 226983) = 1/(226983 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4623 : Bounds (-48292897 / 500000000) (-96585793 / 1000000000) (Real.log (226983 / 250000)) := by
  have h := reflection_log_4623_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4624_neg : (17657479 / 200000000) ≤ -Real.log (500000 / 546151) ∧
    -Real.log (500000 / 546151) ≤ (22071849 / 250000000) := by
  have h := checkLog_sound (w := (46151 / 1046151)) (n := 12)
    (lo := (17657479 / 200000000)) (hi := (22071849 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((546151 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(546151 / 500000) = 1/(500000 / 546151) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4624 : Bounds (17657479 / 200000000) (22071849 / 250000000) (Real.log (546151 / 500000)) := by
  have h := reflection_log_4624_neg
  have he : Real.log (546151 / 500000) = -Real.log (500000 / 546151) := by
    rw [show ((546151 / 500000) : ℝ) = ((500000 / 546151) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4625_neg : (48421777 / 500000000) ≤ -Real.log (453849 / 500000) ∧
    -Real.log (453849 / 500000) ≤ (19368711 / 200000000) := by
  have h := checkLog_sound (w := (46151 / 953849)) (n := 12)
    (lo := (48421777 / 500000000)) (hi := (19368711 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 453849) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 453849) = 1/(453849 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4625 : Bounds (-19368711 / 200000000) (-48421777 / 500000000) (Real.log (453849 / 500000)) := by
  have h := reflection_log_4625_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4626_neg : (4278079 / 500000000) ≤ -Real.log (247870085199 / 250000000000) ∧
    -Real.log (247870085199 / 250000000000) ≤ (8556159 / 1000000000) := by
  have h := checkLog_sound (w := (2129914801 / 497870085199)) (n := 12)
    (lo := (4278079 / 500000000)) (hi := (8556159 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247870085199) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247870085199) = 1/(247870085199 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4626 : Bounds (-8556159 / 1000000000) (-4278079 / 500000000) (Real.log (247870085199 / 250000000000)) := by
  have h := reflection_log_4626_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4627_neg : (4256323 / 500000000) ≤ -Real.log (61970217711 / 62500000000) ∧
    -Real.log (61970217711 / 62500000000) ≤ (8512647 / 1000000000) := by
  have h := checkLog_sound (w := (529782289 / 124470217711)) (n := 12)
    (lo := (4256323 / 500000000)) (hi := (8512647 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 61970217711) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 61970217711) = 1/(61970217711 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4627 : Bounds (-8512647 / 1000000000) (-4256323 / 500000000) (Real.log (61970217711 / 62500000000)) := by
  have h := reflection_log_4627_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4628_neg : (184658939 / 1000000000) ≤ -Real.log (125000000000 / 150351017477) ∧
    -Real.log (125000000000 / 150351017477) ≤ (9232947 / 50000000) := by
  have h := checkLog_sound (w := (25351017477 / 275351017477)) (n := 12)
    (lo := (184658939 / 1000000000)) (hi := (9232947 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((150351017477 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(150351017477 / 125000000000) = 1/(125000000000 / 150351017477) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4628 : Bounds (184658939 / 1000000000) (9232947 / 50000000) (Real.log (150351017477 / 125000000000)) := by
  have h := reflection_log_4628_neg
  have he : Real.log (150351017477 / 125000000000) = -Real.log (125000000000 / 150351017477) := by
    rw [show ((150351017477 / 125000000000) : ℝ) = ((125000000000 / 150351017477) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4629_neg : (3702619 / 20000000) ≤ -Real.log (125000000000 / 150422001591) ∧
    -Real.log (125000000000 / 150422001591) ≤ (185130951 / 1000000000) := by
  have h := checkLog_sound (w := (25422001591 / 275422001591)) (n := 12)
    (lo := (3702619 / 20000000)) (hi := (185130951 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((150422001591 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(150422001591 / 125000000000) = 1/(125000000000 / 150422001591) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4629 : Bounds (3702619 / 20000000) (185130951 / 1000000000) (Real.log (150422001591 / 125000000000)) := by
  have h := reflection_log_4629_neg
  have he : Real.log (150422001591 / 125000000000) = -Real.log (125000000000 / 150422001591) := by
    rw [show ((150422001591 / 125000000000) : ℝ) = ((125000000000 / 150422001591) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4630_neg : (92645911 / 250000000) ≤ -Real.log (500000000000 / 724289911851) ∧
    -Real.log (500000000000 / 724289911851) ≤ (74116729 / 200000000) := by
  have h := checkLog_sound (w := (224289911851 / 1224289911851)) (n := 12)
    (lo := (92645911 / 250000000)) (hi := (74116729 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((724289911851 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(724289911851 / 500000000000) = 1/(500000000000 / 724289911851) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4630 : Bounds (92645911 / 250000000) (74116729 / 200000000) (Real.log (724289911851 / 500000000000)) := by
  have h := reflection_log_4630_neg
  have he : Real.log (724289911851 / 500000000000) = -Real.log (500000000000 / 724289911851) := by
    rw [show ((724289911851 / 500000000000) : ℝ) = ((500000000000 / 724289911851) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4631_neg : (185395297 / 500000000) ≤ -Real.log (500000000000 / 724439818783) ∧
    -Real.log (500000000000 / 724439818783) ≤ (74158119 / 200000000) := by
  have h := checkLog_sound (w := (224439818783 / 1224439818783)) (n := 12)
    (lo := (185395297 / 500000000)) (hi := (74158119 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((724439818783 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(724439818783 / 500000000000) = 1/(500000000000 / 724439818783) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4631 : Bounds (185395297 / 500000000) (74158119 / 200000000) (Real.log (724439818783 / 500000000000)) := by
  have h := reflection_log_4631_neg
  have he : Real.log (724439818783 / 500000000000) = -Real.log (500000000000 / 724439818783) := by
    rw [show ((724439818783 / 500000000000) : ℝ) = ((500000000000 / 724439818783) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4632_neg : (168391651 / 1000000000) ≤ -Real.log (5000 / 5917) ∧
    -Real.log (5000 / 5917) ≤ (42097913 / 250000000) := by
  have h := checkLog_sound (w := (917 / 10917)) (n := 12)
    (lo := (168391651 / 1000000000)) (hi := (42097913 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5917 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5917 / 5000) = 1/(5000 / 5917) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4632 : Bounds (168391651 / 1000000000) (42097913 / 250000000) (Real.log (5917 / 5000)) := by
  have h := reflection_log_4632_neg
  have he : Real.log (5917 / 5000) = -Real.log (5000 / 5917) := by
    rw [show ((5917 / 5000) : ℝ) = ((5000 / 5917) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4633_neg : (2026059 / 10000000) ≤ -Real.log (4083 / 5000) ∧
    -Real.log (4083 / 5000) ≤ (202605901 / 1000000000) := by
  have h := checkLog_sound (w := (917 / 9083)) (n := 12)
    (lo := (2026059 / 10000000)) (hi := (202605901 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4083) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4083) = 1/(4083 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4633 : Bounds (-202605901 / 1000000000) (-2026059 / 10000000) (Real.log (4083 / 5000)) := by
  have h := reflection_log_4633_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4634_neg : (183383 / 1000000000) ≤ -Real.log (5000000 / 5000917) ∧
    -Real.log (5000000 / 5000917) ≤ (22923 / 125000000) := by
  have h := checkLog_sound (w := (917 / 10000917)) (n := 12)
    (lo := (183383 / 1000000000)) (hi := (22923 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000917 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000917 / 5000000) = 1/(5000000 / 5000917) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4634 : Bounds (183383 / 1000000000) (22923 / 125000000) (Real.log (5000917 / 5000000)) := by
  have h := reflection_log_4634_neg
  have he : Real.log (5000917 / 5000000) = -Real.log (5000000 / 5000917) := by
    rw [show ((5000917 / 5000000) : ℝ) = ((5000000 / 5000917) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4635_neg : (22927 / 125000000) ≤ -Real.log (4999083 / 5000000) ∧
    -Real.log (4999083 / 5000000) ≤ (183417 / 1000000000) := by
  have h := checkLog_sound (w := (917 / 9999083)) (n := 12)
    (lo := (22927 / 125000000)) (hi := (183417 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999083) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999083) = 1/(4999083 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4635 : Bounds (-183417 / 1000000000) (-22927 / 125000000) (Real.log (4999083 / 5000000)) := by
  have h := reflection_log_4635_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4636_neg : (17623969 / 200000000) ≤ -Real.log (1000000 / 1092119) ∧
    -Real.log (1000000 / 1092119) ≤ (44059923 / 500000000) := by
  have h := checkLog_sound (w := (92119 / 2092119)) (n := 12)
    (lo := (17623969 / 200000000)) (hi := (44059923 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1092119 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1092119 / 1000000) = 1/(1000000 / 1092119) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4636 : Bounds (17623969 / 200000000) (44059923 / 500000000) (Real.log (1092119 / 1000000)) := by
  have h := reflection_log_4636_neg
  have he : Real.log (1092119 / 1000000) = -Real.log (1000000 / 1092119) := by
    rw [show ((1092119 / 1000000) : ℝ) = ((1000000 / 1092119) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4637_neg : (48320983 / 500000000) ≤ -Real.log (907881 / 1000000) ∧
    -Real.log (907881 / 1000000) ≤ (96641967 / 1000000000) := by
  have h := checkLog_sound (w := (92119 / 1907881)) (n := 12)
    (lo := (48320983 / 500000000)) (hi := (96641967 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 907881) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 907881) = 1/(907881 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4637 : Bounds (-96641967 / 1000000000) (-48320983 / 500000000) (Real.log (907881 / 1000000)) := by
  have h := reflection_log_4637_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4638_neg : (17666817 / 200000000) ≤ -Real.log (1000000 / 1092353) ∧
    -Real.log (1000000 / 1092353) ≤ (44167043 / 500000000) := by
  have h := checkLog_sound (w := (92353 / 2092353)) (n := 12)
    (lo := (17666817 / 200000000)) (hi := (44167043 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1092353 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1092353 / 1000000) = 1/(1000000 / 1092353) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4638 : Bounds (17666817 / 200000000) (44167043 / 500000000) (Real.log (1092353 / 1000000)) := by
  have h := reflection_log_4638_neg
  have he : Real.log (1092353 / 1000000) = -Real.log (1000000 / 1092353) := by
    rw [show ((1092353 / 1000000) : ℝ) = ((1000000 / 1092353) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4639_neg : (48449871 / 500000000) ≤ -Real.log (907647 / 1000000) ∧
    -Real.log (907647 / 1000000) ≤ (96899743 / 1000000000) := by
  have h := checkLog_sound (w := (92353 / 1907647)) (n := 12)
    (lo := (48449871 / 500000000)) (hi := (96899743 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 907647) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 907647) = 1/(907647 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4639 : Bounds (-96899743 / 1000000000) (-48449871 / 500000000) (Real.log (907647 / 1000000)) := by
  have h := reflection_log_4639_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4640_neg : (8565657 / 1000000000) ≤ -Real.log (991470923391 / 1000000000000) ∧
    -Real.log (991470923391 / 1000000000000) ≤ (4282829 / 500000000) := by
  have h := checkLog_sound (w := (8529076609 / 1991470923391)) (n := 12)
    (lo := (8565657 / 1000000000)) (hi := (4282829 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 991470923391) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 991470923391) = 1/(991470923391 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4640 : Bounds (-4282829 / 500000000) (-8565657 / 1000000000) (Real.log (991470923391 / 1000000000000)) := by
  have h := reflection_log_4640_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4641_neg : (213053 / 25000000) ≤ -Real.log (991514089839 / 1000000000000) ∧
    -Real.log (991514089839 / 1000000000000) ≤ (8522121 / 1000000000) := by
  have h := checkLog_sound (w := (8485910161 / 1991514089839)) (n := 12)
    (lo := (213053 / 25000000)) (hi := (8522121 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 991514089839) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 991514089839) = 1/(991514089839 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4641 : Bounds (-8522121 / 1000000000) (-213053 / 25000000) (Real.log (991514089839 / 1000000000000)) := by
  have h := reflection_log_4641_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4642_neg : (184761811 / 1000000000) ≤ -Real.log (25000000000 / 30073297051) ∧
    -Real.log (25000000000 / 30073297051) ≤ (46190453 / 250000000) := by
  have h := checkLog_sound (w := (5073297051 / 55073297051)) (n := 12)
    (lo := (184761811 / 1000000000)) (hi := (46190453 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((30073297051 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(30073297051 / 25000000000) = 1/(25000000000 / 30073297051) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4642 : Bounds (184761811 / 1000000000) (46190453 / 250000000) (Real.log (30073297051 / 25000000000)) := by
  have h := reflection_log_4642_neg
  have he : Real.log (30073297051 / 25000000000) = -Real.log (25000000000 / 30073297051) := by
    rw [show ((30073297051 / 25000000000) : ℝ) = ((25000000000 / 30073297051) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4643_neg : (185233827 / 1000000000) ≤ -Real.log (250000000000 / 300874954691) ∧
    -Real.log (250000000000 / 300874954691) ≤ (46308457 / 250000000) := by
  have h := checkLog_sound (w := (50874954691 / 550874954691)) (n := 12)
    (lo := (185233827 / 1000000000)) (hi := (46308457 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((300874954691 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(300874954691 / 250000000000) = 1/(250000000000 / 300874954691) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4643 : Bounds (185233827 / 1000000000) (46308457 / 250000000) (Real.log (300874954691 / 250000000000)) := by
  have h := reflection_log_4643_neg
  have he : Real.log (300874954691 / 250000000000) = -Real.log (250000000000 / 300874954691) := by
    rw [show ((300874954691 / 250000000000) : ℝ) = ((250000000000 / 300874954691) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4644_neg : (185395297 / 500000000) ≤ -Real.log (250000000000 / 362219909391) ∧
    -Real.log (250000000000 / 362219909391) ≤ (74158119 / 200000000) := by
  have h := checkLog_sound (w := (112219909391 / 612219909391)) (n := 12)
    (lo := (185395297 / 500000000)) (hi := (74158119 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((362219909391 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(362219909391 / 250000000000) = 1/(250000000000 / 362219909391) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4644 : Bounds (185395297 / 500000000) (74158119 / 200000000) (Real.log (362219909391 / 250000000000)) := by
  have h := reflection_log_4644_neg
  have he : Real.log (362219909391 / 250000000000) = -Real.log (250000000000 / 362219909391) := by
    rw [show ((362219909391 / 250000000000) : ℝ) = ((250000000000 / 362219909391) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4645_neg : (370997551 / 1000000000) ≤ -Real.log (50000000000 / 72458976243) ∧
    -Real.log (50000000000 / 72458976243) ≤ (23187347 / 62500000) := by
  have h := checkLog_sound (w := (22458976243 / 122458976243)) (n := 12)
    (lo := (370997551 / 1000000000)) (hi := (23187347 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((72458976243 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(72458976243 / 50000000000) = 1/(50000000000 / 72458976243) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4645 : Bounds (370997551 / 1000000000) (23187347 / 62500000) (Real.log (72458976243 / 50000000000)) := by
  have h := reflection_log_4645_neg
  have he : Real.log (72458976243 / 50000000000) = -Real.log (50000000000 / 72458976243) := by
    rw [show ((72458976243 / 50000000000) : ℝ) = ((50000000000 / 72458976243) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4646_neg : (168476149 / 1000000000) ≤ -Real.log (2000 / 2367) ∧
    -Real.log (2000 / 2367) ≤ (3369523 / 20000000) := by
  have h := checkLog_sound (w := (367 / 4367)) (n := 12)
    (lo := (168476149 / 1000000000)) (hi := (3369523 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2367 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2367 / 2000) = 1/(2000 / 2367) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4646 : Bounds (168476149 / 1000000000) (3369523 / 20000000) (Real.log (2367 / 2000)) := by
  have h := reflection_log_4646_neg
  have he : Real.log (2367 / 2000) = -Real.log (2000 / 2367) := by
    rw [show ((2367 / 2000) : ℝ) = ((2000 / 2367) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4647_neg : (101364183 / 500000000) ≤ -Real.log (1633 / 2000) ∧
    -Real.log (1633 / 2000) ≤ (202728367 / 1000000000) := by
  have h := checkLog_sound (w := (367 / 3633)) (n := 12)
    (lo := (101364183 / 500000000)) (hi := (202728367 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1633) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1633) = 1/(1633 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4647 : Bounds (-202728367 / 1000000000) (-101364183 / 500000000) (Real.log (1633 / 2000)) := by
  have h := reflection_log_4647_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4648_neg : (183483 / 1000000000) ≤ -Real.log (2000000 / 2000367) ∧
    -Real.log (2000000 / 2000367) ≤ (45871 / 250000000) := by
  have h := checkLog_sound (w := (367 / 4000367)) (n := 12)
    (lo := (183483 / 1000000000)) (hi := (45871 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000367 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000367 / 2000000) = 1/(2000000 / 2000367) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4648 : Bounds (183483 / 1000000000) (45871 / 250000000) (Real.log (2000367 / 2000000)) := by
  have h := reflection_log_4648_neg
  have he : Real.log (2000367 / 2000000) = -Real.log (2000000 / 2000367) := by
    rw [show ((2000367 / 2000000) : ℝ) = ((2000000 / 2000367) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4649_neg : (45879 / 250000000) ≤ -Real.log (1999633 / 2000000) ∧
    -Real.log (1999633 / 2000000) ≤ (183517 / 1000000000) := by
  have h := checkLog_sound (w := (367 / 3999633)) (n := 12)
    (lo := (45879 / 250000000)) (hi := (183517 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999633) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999633) = 1/(1999633 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4649 : Bounds (-183517 / 1000000000) (-45879 / 250000000) (Real.log (1999633 / 2000000)) := by
  have h := reflection_log_4649_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4650_neg : (44083271 / 500000000) ≤ -Real.log (100000 / 109217) ∧
    -Real.log (100000 / 109217) ≤ (88166543 / 1000000000) := by
  have h := checkLog_sound (w := (9217 / 209217)) (n := 12)
    (lo := (44083271 / 500000000)) (hi := (88166543 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((109217 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(109217 / 100000) = 1/(100000 / 109217) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4650 : Bounds (44083271 / 500000000) (88166543 / 1000000000) (Real.log (109217 / 100000)) := by
  have h := reflection_log_4650_neg
  have he : Real.log (109217 / 100000) = -Real.log (100000 / 109217) := by
    rw [show ((109217 / 100000) : ℝ) = ((100000 / 109217) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4651_neg : (48349071 / 500000000) ≤ -Real.log (90783 / 100000) ∧
    -Real.log (90783 / 100000) ≤ (96698143 / 1000000000) := by
  have h := checkLog_sound (w := (9217 / 190783)) (n := 12)
    (lo := (48349071 / 500000000)) (hi := (96698143 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 90783) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 90783) = 1/(90783 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4651 : Bounds (-96698143 / 1000000000) (-48349071 / 500000000) (Real.log (90783 / 100000)) := by
  have h := reflection_log_4651_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4652_neg : (22095193 / 250000000) ≤ -Real.log (250000 / 273101) ∧
    -Real.log (250000 / 273101) ≤ (88380773 / 1000000000) := by
  have h := checkLog_sound (w := (23101 / 523101)) (n := 12)
    (lo := (22095193 / 250000000)) (hi := (88380773 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((273101 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(273101 / 250000) = 1/(250000 / 273101) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4652 : Bounds (22095193 / 250000000) (88380773 / 1000000000) (Real.log (273101 / 250000)) := by
  have h := reflection_log_4652_neg
  have he : Real.log (273101 / 250000) = -Real.log (250000 / 273101) := by
    rw [show ((273101 / 250000) : ℝ) = ((250000 / 273101) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4653_neg : (96955933 / 1000000000) ≤ -Real.log (226899 / 250000) ∧
    -Real.log (226899 / 250000) ≤ (48477967 / 500000000) := by
  have h := checkLog_sound (w := (23101 / 476899)) (n := 12)
    (lo := (96955933 / 1000000000)) (hi := (48477967 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 226899) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 226899) = 1/(226899 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4653 : Bounds (-48477967 / 500000000) (-96955933 / 1000000000) (Real.log (226899 / 250000)) := by
  have h := reflection_log_4653_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4654_neg : (8575161 / 1000000000) ≤ -Real.log (61966343799 / 62500000000) ∧
    -Real.log (61966343799 / 62500000000) ≤ (4287581 / 500000000) := by
  have h := checkLog_sound (w := (533656201 / 124466343799)) (n := 12)
    (lo := (8575161 / 1000000000)) (hi := (4287581 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 61966343799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 61966343799) = 1/(61966343799 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4654 : Bounds (-4287581 / 500000000) (-8575161 / 1000000000) (Real.log (61966343799 / 62500000000)) := by
  have h := reflection_log_4654_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4655_neg : (8531599 / 1000000000) ≤ -Real.log (9915046911 / 10000000000) ∧
    -Real.log (9915046911 / 10000000000) ≤ (21329 / 2500000) := by
  have h := checkLog_sound (w := (84953089 / 19915046911)) (n := 12)
    (lo := (8531599 / 1000000000)) (hi := (21329 / 2500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 9915046911) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 9915046911) = 1/(9915046911 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4655 : Bounds (-21329 / 2500000) (-8531599 / 1000000000) (Real.log (9915046911 / 10000000000)) := by
  have h := reflection_log_4655_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4656_neg : (36972937 / 200000000) ≤ -Real.log (100000000000 / 120305563817) ∧
    -Real.log (100000000000 / 120305563817) ≤ (92432343 / 500000000) := by
  have h := checkLog_sound (w := (20305563817 / 220305563817)) (n := 12)
    (lo := (36972937 / 200000000)) (hi := (92432343 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((120305563817 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(120305563817 / 100000000000) = 1/(100000000000 / 120305563817) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4656 : Bounds (36972937 / 200000000) (92432343 / 500000000) (Real.log (120305563817 / 100000000000)) := by
  have h := reflection_log_4656_neg
  have he : Real.log (120305563817 / 100000000000) = -Real.log (100000000000 / 120305563817) := by
    rw [show ((120305563817 / 100000000000) : ℝ) = ((100000000000 / 120305563817) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4657_neg : (37067341 / 200000000) ≤ -Real.log (125000000000 / 150452954839) ∧
    -Real.log (125000000000 / 150452954839) ≤ (92668353 / 500000000) := by
  have h := checkLog_sound (w := (25452954839 / 275452954839)) (n := 12)
    (lo := (37067341 / 200000000)) (hi := (92668353 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((150452954839 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(150452954839 / 125000000000) = 1/(125000000000 / 150452954839) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4657 : Bounds (37067341 / 200000000) (92668353 / 500000000) (Real.log (150452954839 / 125000000000)) := by
  have h := reflection_log_4657_neg
  have he : Real.log (150452954839 / 125000000000) = -Real.log (125000000000 / 150452954839) := by
    rw [show ((150452954839 / 125000000000) : ℝ) = ((125000000000 / 150452954839) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4658_neg : (370997551 / 1000000000) ≤ -Real.log (500000000000 / 724589762429) ∧
    -Real.log (500000000000 / 724589762429) ≤ (23187347 / 62500000) := by
  have h := checkLog_sound (w := (224589762429 / 1224589762429)) (n := 12)
    (lo := (370997551 / 1000000000)) (hi := (23187347 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((724589762429 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(724589762429 / 500000000000) = 1/(500000000000 / 724589762429) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4658 : Bounds (370997551 / 1000000000) (23187347 / 62500000) (Real.log (724589762429 / 500000000000)) := by
  have h := reflection_log_4658_neg
  have he : Real.log (724589762429 / 500000000000) = -Real.log (500000000000 / 724589762429) := by
    rw [show ((724589762429 / 500000000000) : ℝ) = ((500000000000 / 724589762429) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4659_neg : (92801129 / 250000000) ≤ -Real.log (100000000000 / 144947948561) ∧
    -Real.log (100000000000 / 144947948561) ≤ (371204517 / 1000000000) := by
  have h := checkLog_sound (w := (44947948561 / 244947948561)) (n := 12)
    (lo := (92801129 / 250000000)) (hi := (371204517 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((144947948561 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(144947948561 / 100000000000) = 1/(100000000000 / 144947948561) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4659 : Bounds (92801129 / 250000000) (371204517 / 1000000000) (Real.log (144947948561 / 100000000000)) := by
  have h := reflection_log_4659_neg
  have he : Real.log (144947948561 / 100000000000) = -Real.log (100000000000 / 144947948561) := by
    rw [show ((144947948561 / 100000000000) : ℝ) = ((100000000000 / 144947948561) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4660_neg : (168560641 / 1000000000) ≤ -Real.log (2500 / 2959) ∧
    -Real.log (2500 / 2959) ≤ (84280321 / 500000000) := by
  have h := checkLog_sound (w := (459 / 5459)) (n := 12)
    (lo := (168560641 / 1000000000)) (hi := (84280321 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2959 / 2500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2959 / 2500) = 1/(2500 / 2959) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4660 : Bounds (168560641 / 1000000000) (84280321 / 500000000) (Real.log (2959 / 2500)) := by
  have h := reflection_log_4660_neg
  have he : Real.log (2959 / 2500) = -Real.log (2500 / 2959) := by
    rw [show ((2959 / 2500) : ℝ) = ((2500 / 2959) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4661_neg : (6339089 / 31250000) ≤ -Real.log (2041 / 2500) ∧
    -Real.log (2041 / 2500) ≤ (202850849 / 1000000000) := by
  have h := checkLog_sound (w := (459 / 4541)) (n := 12)
    (lo := (6339089 / 31250000)) (hi := (202850849 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500 / 2041) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500 / 2041) = 1/(2041 / 2500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4661 : Bounds (-202850849 / 1000000000) (-6339089 / 31250000) (Real.log (2041 / 2500)) := by
  have h := reflection_log_4661_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4662_neg : (183583 / 1000000000) ≤ -Real.log (2500000 / 2500459) ∧
    -Real.log (2500000 / 2500459) ≤ (5737 / 31250000) := by
  have h := checkLog_sound (w := (459 / 5000459)) (n := 12)
    (lo := (183583 / 1000000000)) (hi := (5737 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500459 / 2500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500459 / 2500000) = 1/(2500000 / 2500459) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4662 : Bounds (183583 / 1000000000) (5737 / 31250000) (Real.log (2500459 / 2500000)) := by
  have h := reflection_log_4662_neg
  have he : Real.log (2500459 / 2500000) = -Real.log (2500000 / 2500459) := by
    rw [show ((2500459 / 2500000) : ℝ) = ((2500000 / 2500459) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4663_neg : (2869 / 15625000) ≤ -Real.log (2499541 / 2500000) ∧
    -Real.log (2499541 / 2500000) ≤ (183617 / 1000000000) := by
  have h := checkLog_sound (w := (459 / 4999541)) (n := 12)
    (lo := (2869 / 15625000)) (hi := (183617 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000 / 2499541) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000 / 2499541) = 1/(2499541 / 2500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4663 : Bounds (-183617 / 1000000000) (-2869 / 15625000) (Real.log (2499541 / 2500000)) := by
  have h := reflection_log_4663_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4664_neg : (88213237 / 1000000000) ≤ -Real.log (1000000 / 1092221) ∧
    -Real.log (1000000 / 1092221) ≤ (44106619 / 500000000) := by
  have h := checkLog_sound (w := (92221 / 2092221)) (n := 12)
    (lo := (88213237 / 1000000000)) (hi := (44106619 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1092221 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1092221 / 1000000) = 1/(1000000 / 1092221) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4664 : Bounds (88213237 / 1000000000) (44106619 / 500000000) (Real.log (1092221 / 1000000)) := by
  have h := reflection_log_4664_neg
  have he : Real.log (1092221 / 1000000) = -Real.log (1000000 / 1092221) := by
    rw [show ((1092221 / 1000000) : ℝ) = ((1000000 / 1092221) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4665_neg : (48377161 / 500000000) ≤ -Real.log (907779 / 1000000) ∧
    -Real.log (907779 / 1000000) ≤ (96754323 / 1000000000) := by
  have h := checkLog_sound (w := (92221 / 1907779)) (n := 12)
    (lo := (48377161 / 500000000)) (hi := (96754323 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 907779) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 907779) = 1/(907779 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4665 : Bounds (-96754323 / 1000000000) (-48377161 / 500000000) (Real.log (907779 / 1000000)) := by
  have h := reflection_log_4665_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4666_neg : (88427457 / 1000000000) ≤ -Real.log (200000 / 218491) ∧
    -Real.log (200000 / 218491) ≤ (44213729 / 500000000) := by
  have h := checkLog_sound (w := (18491 / 418491)) (n := 12)
    (lo := (88427457 / 1000000000)) (hi := (44213729 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((218491 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(218491 / 200000) = 1/(200000 / 218491) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4666 : Bounds (88427457 / 1000000000) (44213729 / 500000000) (Real.log (218491 / 200000)) := by
  have h := reflection_log_4666_neg
  have he : Real.log (218491 / 200000) = -Real.log (200000 / 218491) := by
    rw [show ((218491 / 200000) : ℝ) = ((200000 / 218491) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4667_neg : (97012127 / 1000000000) ≤ -Real.log (181509 / 200000) ∧
    -Real.log (181509 / 200000) ≤ (3031629 / 31250000) := by
  have h := checkLog_sound (w := (18491 / 381509)) (n := 12)
    (lo := (97012127 / 1000000000)) (hi := (3031629 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 181509) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 181509) = 1/(181509 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4667 : Bounds (-3031629 / 31250000) (-97012127 / 1000000000) (Real.log (181509 / 200000)) := by
  have h := reflection_log_4667_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4668_neg : (858467 / 100000000) ≤ -Real.log (39658082919 / 40000000000) ∧
    -Real.log (39658082919 / 40000000000) ≤ (8584671 / 1000000000) := by
  have h := checkLog_sound (w := (341917081 / 79658082919)) (n := 12)
    (lo := (858467 / 100000000)) (hi := (8584671 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39658082919) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39658082919) = 1/(39658082919 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4668 : Bounds (-8584671 / 1000000000) (-858467 / 100000000) (Real.log (39658082919 / 40000000000)) := by
  have h := reflection_log_4668_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4669_neg : (2135271 / 250000000) ≤ -Real.log (991495287159 / 1000000000000) ∧
    -Real.log (991495287159 / 1000000000000) ≤ (1708217 / 200000000) := by
  have h := checkLog_sound (w := (8504712841 / 1991495287159)) (n := 12)
    (lo := (2135271 / 250000000)) (hi := (1708217 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 991495287159) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 991495287159) = 1/(991495287159 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4669 : Bounds (-1708217 / 200000000) (-2135271 / 250000000) (Real.log (991495287159 / 1000000000000)) := by
  have h := reflection_log_4669_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4670_neg : (184967559 / 1000000000) ≤ -Real.log (500000000000 / 601589704101) ∧
    -Real.log (500000000000 / 601589704101) ≤ (4624189 / 25000000) := by
  have h := checkLog_sound (w := (101589704101 / 1101589704101)) (n := 12)
    (lo := (184967559 / 1000000000)) (hi := (4624189 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((601589704101 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(601589704101 / 500000000000) = 1/(500000000000 / 601589704101) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4670 : Bounds (184967559 / 1000000000) (4624189 / 25000000) (Real.log (601589704101 / 500000000000)) := by
  have h := reflection_log_4670_neg
  have he : Real.log (601589704101 / 500000000000) = -Real.log (500000000000 / 601589704101) := by
    rw [show ((601589704101 / 500000000000) : ℝ) = ((500000000000 / 601589704101) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4671_neg : (5794987 / 31250000) ≤ -Real.log (500000000000 / 601873736289) ∧
    -Real.log (500000000000 / 601873736289) ≤ (37087917 / 200000000) := by
  have h := checkLog_sound (w := (101873736289 / 1101873736289)) (n := 12)
    (lo := (5794987 / 31250000)) (hi := (37087917 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((601873736289 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(601873736289 / 500000000000) = 1/(500000000000 / 601873736289) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4671 : Bounds (5794987 / 31250000) (37087917 / 200000000) (Real.log (601873736289 / 500000000000)) := by
  have h := reflection_log_4671_neg
  have he : Real.log (601873736289 / 500000000000) = -Real.log (500000000000 / 601873736289) := by
    rw [show ((601873736289 / 500000000000) : ℝ) = ((500000000000 / 601873736289) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily
