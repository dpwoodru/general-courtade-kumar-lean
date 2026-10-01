import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_6656_neg : (9990829 / 1000000000) ≤ -Real.log (39602356519 / 40000000000) ∧
    -Real.log (39602356519 / 40000000000) ≤ (999083 / 100000000) := by
  have h := checkLog_sound (w := (397643481 / 79602356519)) (n := 12)
    (lo := (9990829 / 1000000000)) (hi := (999083 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39602356519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39602356519) = 1/(39602356519 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6656 : Bounds (-999083 / 100000000) (-9990829 / 1000000000) (Real.log (39602356519 / 40000000000)) := by
  have h := reflection_log_6656_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6657_neg : (9940741 / 1000000000) ≤ -Real.log (241725709 / 244140625) ∧
    -Real.log (241725709 / 244140625) ≤ (4970371 / 500000000) := by
  have h := checkLog_sound (w := (1207458 / 242933167)) (n := 12)
    (lo := (9940741 / 1000000000)) (hi := (4970371 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((244140625 / 241725709) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(244140625 / 241725709) = 1/(241725709 / 244140625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6657 : Bounds (-4970371 / 500000000) (-9940741 / 1000000000) (Real.log (241725709 / 244140625)) := by
  have h := reflection_log_6657_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6658_neg : (39914353 / 200000000) ≤ -Real.log (800000000 / 976703859) ∧
    -Real.log (800000000 / 976703859) ≤ (99785883 / 500000000) := by
  have h := checkLog_sound (w := (176703859 / 1776703859)) (n := 12)
    (lo := (39914353 / 200000000)) (hi := (99785883 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((976703859 / 800000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(976703859 / 800000000) = 1/(800000000 / 976703859) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6658 : Bounds (39914353 / 200000000) (99785883 / 500000000) (Real.log (976703859 / 800000000)) := by
  have h := reflection_log_6658_neg
  have he : Real.log (976703859 / 800000000) = -Real.log (800000000 / 976703859) := by
    rw [show ((976703859 / 800000000) : ℝ) = ((800000000 / 976703859) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6659_neg : (200074753 / 1000000000) ≤ -Real.log (500000000000 / 610747032917) ∧
    -Real.log (500000000000 / 610747032917) ≤ (100037377 / 500000000) := by
  have h := checkLog_sound (w := (110747032917 / 1110747032917)) (n := 12)
    (lo := (200074753 / 1000000000)) (hi := (100037377 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((610747032917 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(610747032917 / 500000000000) = 1/(500000000000 / 610747032917) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6659 : Bounds (200074753 / 1000000000) (100037377 / 500000000) (Real.log (610747032917 / 500000000000)) := by
  have h := reflection_log_6659_neg
  have he : Real.log (610747032917 / 500000000000) = -Real.log (500000000000 / 610747032917) := by
    rw [show ((610747032917 / 500000000000) : ℝ) = ((500000000000 / 610747032917) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6660_neg : (400675727 / 1000000000) ≤ -Real.log (500000000000 / 746416552411) ∧
    -Real.log (500000000000 / 746416552411) ≤ (25042233 / 62500000) := by
  have h := checkLog_sound (w := (246416552411 / 1246416552411)) (n := 12)
    (lo := (400675727 / 1000000000)) (hi := (25042233 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((746416552411 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(746416552411 / 500000000000) = 1/(500000000000 / 746416552411) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6660 : Bounds (400675727 / 1000000000) (25042233 / 62500000) (Real.log (746416552411 / 500000000000)) := by
  have h := reflection_log_6660_neg
  have he : Real.log (746416552411 / 500000000000) = -Real.log (500000000000 / 746416552411) := by
    rw [show ((746416552411 / 500000000000) : ℝ) = ((500000000000 / 746416552411) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6661_neg : (200441933 / 500000000) ≤ -Real.log (500000000000 / 746571927201) ∧
    -Real.log (500000000000 / 746571927201) ≤ (400883867 / 1000000000) := by
  have h := checkLog_sound (w := (246571927201 / 1246571927201)) (n := 12)
    (lo := (200441933 / 500000000)) (hi := (400883867 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((746571927201 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(746571927201 / 500000000000) = 1/(500000000000 / 746571927201) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6661 : Bounds (200441933 / 500000000) (400883867 / 1000000000) (Real.log (746571927201 / 500000000000)) := by
  have h := reflection_log_6661_neg
  have he : Real.log (746571927201 / 500000000000) = -Real.log (500000000000 / 746571927201) := by
    rw [show ((746571927201 / 500000000000) : ℝ) = ((500000000000 / 746571927201) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6662_neg : (180570023 / 1000000000) ≤ -Real.log (10000 / 11979) ∧
    -Real.log (10000 / 11979) ≤ (22571253 / 125000000) := by
  have h := checkLog_sound (w := (1979 / 21979)) (n := 12)
    (lo := (180570023 / 1000000000)) (hi := (22571253 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11979 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11979 / 10000) = 1/(10000 / 11979) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6662 : Bounds (180570023 / 1000000000) (22571253 / 125000000) (Real.log (11979 / 10000)) := by
  have h := reflection_log_6662_neg
  have he : Real.log (11979 / 10000) = -Real.log (10000 / 11979) := by
    rw [show ((11979 / 10000) : ℝ) = ((10000 / 11979) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6663_neg : (22052199 / 100000000) ≤ -Real.log (8021 / 10000) ∧
    -Real.log (8021 / 10000) ≤ (220521991 / 1000000000) := by
  have h := checkLog_sound (w := (1979 / 18021)) (n := 12)
    (lo := (22052199 / 100000000)) (hi := (220521991 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8021) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8021) = 1/(8021 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6663 : Bounds (-220521991 / 1000000000) (-22052199 / 100000000) (Real.log (8021 / 10000)) := by
  have h := reflection_log_6663_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6664_neg : (4947 / 25000000) ≤ -Real.log (10000000 / 10001979) ∧
    -Real.log (10000000 / 10001979) ≤ (197881 / 1000000000) := by
  have h := checkLog_sound (w := (1979 / 20001979)) (n := 12)
    (lo := (4947 / 25000000)) (hi := (197881 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001979 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001979 / 10000000) = 1/(10000000 / 10001979) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6664 : Bounds (4947 / 25000000) (197881 / 1000000000) (Real.log (10001979 / 10000000)) := by
  have h := reflection_log_6664_neg
  have he : Real.log (10001979 / 10000000) = -Real.log (10000000 / 10001979) := by
    rw [show ((10001979 / 10000000) : ℝ) = ((10000000 / 10001979) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6665_neg : (197919 / 1000000000) ≤ -Real.log (9998021 / 10000000) ∧
    -Real.log (9998021 / 10000000) ≤ (1237 / 6250000) := by
  have h := checkLog_sound (w := (1979 / 19998021)) (n := 12)
    (lo := (197919 / 1000000000)) (hi := (1237 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998021) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998021) = 1/(9998021 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6665 : Bounds (-1237 / 6250000) (-197919 / 1000000000) (Real.log (9998021 / 10000000)) := by
  have h := reflection_log_6665_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6666_neg : (94861897 / 1000000000) ≤ -Real.log (1000000 / 1099507) ∧
    -Real.log (1000000 / 1099507) ≤ (47430949 / 500000000) := by
  have h := checkLog_sound (w := (99507 / 2099507)) (n := 12)
    (lo := (94861897 / 1000000000)) (hi := (47430949 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1099507 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1099507 / 1000000) = 1/(1000000 / 1099507) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6666 : Bounds (94861897 / 1000000000) (47430949 / 500000000) (Real.log (1099507 / 1000000)) := by
  have h := reflection_log_6666_neg
  have he : Real.log (1099507 / 1000000) = -Real.log (1000000 / 1099507) := by
    rw [show ((1099507 / 1000000) : ℝ) = ((1000000 / 1099507) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6667_neg : (104812887 / 1000000000) ≤ -Real.log (900493 / 1000000) ∧
    -Real.log (900493 / 1000000) ≤ (13101611 / 125000000) := by
  have h := checkLog_sound (w := (99507 / 1900493)) (n := 12)
    (lo := (104812887 / 1000000000)) (hi := (13101611 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 900493) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 900493) = 1/(900493 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6667 : Bounds (-13101611 / 125000000) (-104812887 / 1000000000) (Real.log (900493 / 1000000)) := by
  have h := reflection_log_6667_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6668_neg : (95088337 / 1000000000) ≤ -Real.log (250000 / 274939) ∧
    -Real.log (250000 / 274939) ≤ (47544169 / 500000000) := by
  have h := checkLog_sound (w := (24939 / 524939)) (n := 12)
    (lo := (95088337 / 1000000000)) (hi := (47544169 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((274939 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(274939 / 250000) = 1/(250000 / 274939) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6668 : Bounds (95088337 / 1000000000) (47544169 / 500000000) (Real.log (274939 / 250000)) := by
  have h := reflection_log_6668_neg
  have he : Real.log (274939 / 250000) = -Real.log (250000 / 274939) := by
    rw [show ((274939 / 250000) : ℝ) = ((250000 / 274939) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6669_neg : (105089441 / 1000000000) ≤ -Real.log (225061 / 250000) ∧
    -Real.log (225061 / 250000) ≤ (52544721 / 500000000) := by
  have h := checkLog_sound (w := (24939 / 475061)) (n := 12)
    (lo := (105089441 / 1000000000)) (hi := (52544721 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 225061) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 225061) = 1/(225061 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6669 : Bounds (-52544721 / 500000000) (-105089441 / 1000000000) (Real.log (225061 / 250000)) := by
  have h := reflection_log_6669_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6670_neg : (625069 / 62500000) ≤ -Real.log (61878046279 / 62500000000) ∧
    -Real.log (61878046279 / 62500000000) ≤ (2000221 / 200000000) := by
  have h := checkLog_sound (w := (621953721 / 124378046279)) (n := 12)
    (lo := (625069 / 62500000)) (hi := (2000221 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 61878046279) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 61878046279) = 1/(61878046279 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6670 : Bounds (-2000221 / 200000000) (-625069 / 62500000) (Real.log (61878046279 / 62500000000)) := by
  have h := reflection_log_6670_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6671_neg : (995099 / 100000000) ≤ -Real.log (990098356951 / 1000000000000) ∧
    -Real.log (990098356951 / 1000000000000) ≤ (9950991 / 1000000000) := by
  have h := checkLog_sound (w := (9901643049 / 1990098356951)) (n := 12)
    (lo := (995099 / 100000000)) (hi := (9950991 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 990098356951) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 990098356951) = 1/(990098356951 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6671 : Bounds (-9950991 / 1000000000) (-995099 / 100000000) (Real.log (990098356951 / 1000000000000)) := by
  have h := reflection_log_6671_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6672_neg : (39934957 / 200000000) ≤ -Real.log (500000000000 / 610502802353) ∧
    -Real.log (500000000000 / 610502802353) ≤ (99837393 / 500000000) := by
  have h := checkLog_sound (w := (110502802353 / 1110502802353)) (n := 12)
    (lo := (39934957 / 200000000)) (hi := (99837393 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((610502802353 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(610502802353 / 500000000000) = 1/(500000000000 / 610502802353) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6672 : Bounds (39934957 / 200000000) (99837393 / 500000000) (Real.log (610502802353 / 500000000000)) := by
  have h := reflection_log_6672_neg
  have he : Real.log (610502802353 / 500000000000) = -Real.log (500000000000 / 610502802353) := by
    rw [show ((610502802353 / 500000000000) : ℝ) = ((500000000000 / 610502802353) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6673_neg : (100088889 / 500000000) ≤ -Real.log (50000000000 / 61080995819) ∧
    -Real.log (50000000000 / 61080995819) ≤ (200177779 / 1000000000) := by
  have h := checkLog_sound (w := (11080995819 / 111080995819)) (n := 12)
    (lo := (100088889 / 500000000)) (hi := (200177779 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((61080995819 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(61080995819 / 50000000000) = 1/(50000000000 / 61080995819) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6673 : Bounds (100088889 / 500000000) (200177779 / 1000000000) (Real.log (61080995819 / 50000000000)) := by
  have h := reflection_log_6673_neg
  have he : Real.log (61080995819 / 50000000000) = -Real.log (50000000000 / 61080995819) := by
    rw [show ((61080995819 / 50000000000) : ℝ) = ((50000000000 / 61080995819) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6674_neg : (200441933 / 500000000) ≤ -Real.log (625000000 / 933214909) ∧
    -Real.log (625000000 / 933214909) ≤ (400883867 / 1000000000) := by
  have h := checkLog_sound (w := (308214909 / 1558214909)) (n := 12)
    (lo := (200441933 / 500000000)) (hi := (400883867 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((933214909 / 625000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(933214909 / 625000000) = 1/(625000000 / 933214909) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6674 : Bounds (200441933 / 500000000) (400883867 / 1000000000) (Real.log (933214909 / 625000000)) := by
  have h := reflection_log_6674_neg
  have he : Real.log (933214909 / 625000000) = -Real.log (625000000 / 933214909) := by
    rw [show ((933214909 / 625000000) : ℝ) = ((625000000 / 933214909) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6675_neg : (200546007 / 500000000) ≤ -Real.log (500000000000 / 746727340731) ∧
    -Real.log (500000000000 / 746727340731) ≤ (80218403 / 200000000) := by
  have h := checkLog_sound (w := (246727340731 / 1246727340731)) (n := 12)
    (lo := (200546007 / 500000000)) (hi := (80218403 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((746727340731 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(746727340731 / 500000000000) = 1/(500000000000 / 746727340731) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6675 : Bounds (200546007 / 500000000) (80218403 / 200000000) (Real.log (746727340731 / 500000000000)) := by
  have h := reflection_log_6675_neg
  have he : Real.log (746727340731 / 500000000000) = -Real.log (500000000000 / 746727340731) := by
    rw [show ((746727340731 / 500000000000) : ℝ) = ((500000000000 / 746727340731) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6676_neg : (180653499 / 1000000000) ≤ -Real.log (500 / 599) ∧
    -Real.log (500 / 599) ≤ (361307 / 2000000) := by
  have h := checkLog_sound (w := (99 / 1099)) (n := 12)
    (lo := (180653499 / 1000000000)) (hi := (361307 / 2000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((599 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(599 / 500) = 1/(500 / 599) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6676 : Bounds (180653499 / 1000000000) (361307 / 2000000) (Real.log (599 / 500)) := by
  have h := reflection_log_6676_neg
  have he : Real.log (599 / 500) = -Real.log (500 / 599) := by
    rw [show ((599 / 500) : ℝ) = ((500 / 599) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6677_neg : (220646671 / 1000000000) ≤ -Real.log (401 / 500) ∧
    -Real.log (401 / 500) ≤ (13790417 / 62500000) := by
  have h := checkLog_sound (w := (99 / 901)) (n := 12)
    (lo := (220646671 / 1000000000)) (hi := (13790417 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 401) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500 / 401) = 1/(401 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6677 : Bounds (-13790417 / 62500000) (-220646671 / 1000000000) (Real.log (401 / 500)) := by
  have h := reflection_log_6677_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6678_neg : (9899 / 50000000) ≤ -Real.log (500000 / 500099) ∧
    -Real.log (500000 / 500099) ≤ (197981 / 1000000000) := by
  have h := checkLog_sound (w := (99 / 1000099)) (n := 12)
    (lo := (9899 / 50000000)) (hi := (197981 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500099 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500099 / 500000) = 1/(500000 / 500099) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6678 : Bounds (9899 / 50000000) (197981 / 1000000000) (Real.log (500099 / 500000)) := by
  have h := reflection_log_6678_neg
  have he : Real.log (500099 / 500000) = -Real.log (500000 / 500099) := by
    rw [show ((500099 / 500000) : ℝ) = ((500000 / 500099) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6679_neg : (198019 / 1000000000) ≤ -Real.log (499901 / 500000) ∧
    -Real.log (499901 / 500000) ≤ (9901 / 50000000) := by
  have h := checkLog_sound (w := (99 / 999901)) (n := 12)
    (lo := (198019 / 1000000000)) (hi := (9901 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499901) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499901) = 1/(499901 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6679 : Bounds (-9901 / 50000000) (-198019 / 1000000000) (Real.log (499901 / 500000)) := by
  have h := reflection_log_6679_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6680_neg : (2372707 / 25000000) ≤ -Real.log (500000 / 549779) ∧
    -Real.log (500000 / 549779) ≤ (94908281 / 1000000000) := by
  have h := checkLog_sound (w := (49779 / 1049779)) (n := 12)
    (lo := (2372707 / 25000000)) (hi := (94908281 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((549779 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(549779 / 500000) = 1/(500000 / 549779) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6680 : Bounds (2372707 / 25000000) (94908281 / 1000000000) (Real.log (549779 / 500000)) := by
  have h := reflection_log_6680_neg
  have he : Real.log (549779 / 500000) = -Real.log (500000 / 549779) := by
    rw [show ((549779 / 500000) : ℝ) = ((500000 / 549779) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6681_neg : (4194781 / 40000000) ≤ -Real.log (450221 / 500000) ∧
    -Real.log (450221 / 500000) ≤ (52434763 / 500000000) := by
  have h := checkLog_sound (w := (49779 / 950221)) (n := 12)
    (lo := (4194781 / 40000000)) (hi := (52434763 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 450221) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 450221) = 1/(450221 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6681 : Bounds (-52434763 / 500000000) (-4194781 / 40000000) (Real.log (450221 / 500000)) := by
  have h := reflection_log_6681_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6682_neg : (95134709 / 1000000000) ≤ -Real.log (1000000 / 1099807) ∧
    -Real.log (1000000 / 1099807) ≤ (9513471 / 100000000) := by
  have h := checkLog_sound (w := (99807 / 2099807)) (n := 12)
    (lo := (95134709 / 1000000000)) (hi := (9513471 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1099807 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1099807 / 1000000) = 1/(1000000 / 1099807) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6682 : Bounds (95134709 / 1000000000) (9513471 / 100000000) (Real.log (1099807 / 1000000)) := by
  have h := reflection_log_6682_neg
  have he : Real.log (1099807 / 1000000) = -Real.log (1000000 / 1099807) := by
    rw [show ((1099807 / 1000000) : ℝ) = ((1000000 / 1099807) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6683_neg : (52573047 / 500000000) ≤ -Real.log (900193 / 1000000) ∧
    -Real.log (900193 / 1000000) ≤ (21029219 / 200000000) := by
  have h := checkLog_sound (w := (99807 / 1900193)) (n := 12)
    (lo := (52573047 / 500000000)) (hi := (21029219 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 900193) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 900193) = 1/(900193 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6683 : Bounds (-21029219 / 200000000) (-52573047 / 500000000) (Real.log (900193 / 1000000)) := by
  have h := reflection_log_6683_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6684_neg : (1251423 / 125000000) ≤ -Real.log (990038562751 / 1000000000000) ∧
    -Real.log (990038562751 / 1000000000000) ≤ (2002277 / 200000000) := by
  have h := checkLog_sound (w := (9961437249 / 1990038562751)) (n := 12)
    (lo := (1251423 / 125000000)) (hi := (2002277 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 990038562751) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 990038562751) = 1/(990038562751 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6684 : Bounds (-2002277 / 200000000) (-1251423 / 125000000) (Real.log (990038562751 / 1000000000000)) := by
  have h := reflection_log_6684_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6685_neg : (2490311 / 250000000) ≤ -Real.log (247522051159 / 250000000000) ∧
    -Real.log (247522051159 / 250000000000) ≤ (1992249 / 200000000) := by
  have h := checkLog_sound (w := (2477948841 / 497522051159)) (n := 12)
    (lo := (2490311 / 250000000)) (hi := (1992249 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247522051159) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247522051159) = 1/(247522051159 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6685 : Bounds (-1992249 / 200000000) (-2490311 / 250000000) (Real.log (247522051159 / 250000000000)) := by
  have h := reflection_log_6685_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6686_neg : (39955561 / 200000000) ≤ -Real.log (125000000000 / 152641424989) ∧
    -Real.log (125000000000 / 152641424989) ≤ (99888903 / 500000000) := by
  have h := checkLog_sound (w := (27641424989 / 277641424989)) (n := 12)
    (lo := (39955561 / 200000000)) (hi := (99888903 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((152641424989 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(152641424989 / 125000000000) = 1/(125000000000 / 152641424989) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6686 : Bounds (39955561 / 200000000) (99888903 / 500000000) (Real.log (152641424989 / 125000000000)) := by
  have h := reflection_log_6686_neg
  have he : Real.log (152641424989 / 125000000000) = -Real.log (125000000000 / 152641424989) := by
    rw [show ((152641424989 / 125000000000) : ℝ) = ((125000000000 / 152641424989) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6687_neg : (50070201 / 250000000) ≤ -Real.log (15625000000 / 19089777831) ∧
    -Real.log (15625000000 / 19089777831) ≤ (40056161 / 200000000) := by
  have h := checkLog_sound (w := (3464777831 / 34714777831)) (n := 12)
    (lo := (50070201 / 250000000)) (hi := (40056161 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((19089777831 / 15625000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(19089777831 / 15625000000) = 1/(15625000000 / 19089777831) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6687 : Bounds (50070201 / 250000000) (40056161 / 200000000) (Real.log (19089777831 / 15625000000)) := by
  have h := reflection_log_6687_neg
  have he : Real.log (19089777831 / 15625000000) = -Real.log (15625000000 / 19089777831) := by
    rw [show ((19089777831 / 15625000000) : ℝ) = ((15625000000 / 19089777831) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6688_neg : (200546007 / 500000000) ≤ -Real.log (50000000000 / 74672734073) ∧
    -Real.log (50000000000 / 74672734073) ≤ (80218403 / 200000000) := by
  have h := checkLog_sound (w := (24672734073 / 124672734073)) (n := 12)
    (lo := (200546007 / 500000000)) (hi := (80218403 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((74672734073 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(74672734073 / 50000000000) = 1/(50000000000 / 74672734073) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6688 : Bounds (200546007 / 500000000) (80218403 / 200000000) (Real.log (74672734073 / 50000000000)) := by
  have h := reflection_log_6688_neg
  have he : Real.log (74672734073 / 50000000000) = -Real.log (50000000000 / 74672734073) := by
    rw [show ((74672734073 / 50000000000) : ℝ) = ((50000000000 / 74672734073) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6689_neg : (40130017 / 100000000) ≤ -Real.log (250000000000 / 373441396509) ∧
    -Real.log (250000000000 / 373441396509) ≤ (401300171 / 1000000000) := by
  have h := checkLog_sound (w := (123441396509 / 623441396509)) (n := 12)
    (lo := (40130017 / 100000000)) (hi := (401300171 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((373441396509 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(373441396509 / 250000000000) = 1/(250000000000 / 373441396509) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6689 : Bounds (40130017 / 100000000) (401300171 / 1000000000) (Real.log (373441396509 / 250000000000)) := by
  have h := reflection_log_6689_neg
  have he : Real.log (373441396509 / 250000000000) = -Real.log (250000000000 / 373441396509) := by
    rw [show ((373441396509 / 250000000000) : ℝ) = ((250000000000 / 373441396509) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6690_neg : (22592121 / 125000000) ≤ -Real.log (10000 / 11981) ∧
    -Real.log (10000 / 11981) ≤ (180736969 / 1000000000) := by
  have h := checkLog_sound (w := (1981 / 21981)) (n := 12)
    (lo := (22592121 / 125000000)) (hi := (180736969 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11981 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11981 / 10000) = 1/(10000 / 11981) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6690 : Bounds (22592121 / 125000000) (180736969 / 1000000000) (Real.log (11981 / 10000)) := by
  have h := reflection_log_6690_neg
  have he : Real.log (11981 / 10000) = -Real.log (10000 / 11981) := by
    rw [show ((11981 / 10000) : ℝ) = ((10000 / 11981) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6691_neg : (220771367 / 1000000000) ≤ -Real.log (8019 / 10000) ∧
    -Real.log (8019 / 10000) ≤ (27596421 / 125000000) := by
  have h := checkLog_sound (w := (1981 / 18019)) (n := 12)
    (lo := (220771367 / 1000000000)) (hi := (27596421 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8019) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8019) = 1/(8019 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6691 : Bounds (-27596421 / 125000000) (-220771367 / 1000000000) (Real.log (8019 / 10000)) := by
  have h := reflection_log_6691_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6692_neg : (619 / 3125000) ≤ -Real.log (10000000 / 10001981) ∧
    -Real.log (10000000 / 10001981) ≤ (198081 / 1000000000) := by
  have h := checkLog_sound (w := (1981 / 20001981)) (n := 12)
    (lo := (619 / 3125000)) (hi := (198081 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001981 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001981 / 10000000) = 1/(10000000 / 10001981) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6692 : Bounds (619 / 3125000) (198081 / 1000000000) (Real.log (10001981 / 10000000)) := by
  have h := reflection_log_6692_neg
  have he : Real.log (10001981 / 10000000) = -Real.log (10000000 / 10001981) := by
    rw [show ((10001981 / 10000000) : ℝ) = ((10000000 / 10001981) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6693_neg : (198119 / 1000000000) ≤ -Real.log (9998019 / 10000000) ∧
    -Real.log (9998019 / 10000000) ≤ (4953 / 25000000) := by
  have h := checkLog_sound (w := (1981 / 19998019)) (n := 12)
    (lo := (198119 / 1000000000)) (hi := (4953 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998019) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998019) = 1/(9998019 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6693 : Bounds (-4953 / 25000000) (-198119 / 1000000000) (Real.log (9998019 / 10000000)) := by
  have h := reflection_log_6693_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6694_neg : (47477331 / 500000000) ≤ -Real.log (1000000 / 1099609) ∧
    -Real.log (1000000 / 1099609) ≤ (94954663 / 1000000000) := by
  have h := checkLog_sound (w := (99609 / 2099609)) (n := 12)
    (lo := (47477331 / 500000000)) (hi := (94954663 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1099609 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1099609 / 1000000) = 1/(1000000 / 1099609) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6694 : Bounds (47477331 / 500000000) (94954663 / 1000000000) (Real.log (1099609 / 1000000)) := by
  have h := reflection_log_6694_neg
  have he : Real.log (1099609 / 1000000) = -Real.log (1000000 / 1099609) := by
    rw [show ((1099609 / 1000000) : ℝ) = ((1000000 / 1099609) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6695_neg : (20985233 / 200000000) ≤ -Real.log (900391 / 1000000) ∧
    -Real.log (900391 / 1000000) ≤ (52463083 / 500000000) := by
  have h := checkLog_sound (w := (99609 / 1900391)) (n := 12)
    (lo := (20985233 / 200000000)) (hi := (52463083 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 900391) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 900391) = 1/(900391 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6695 : Bounds (-52463083 / 500000000) (-20985233 / 200000000) (Real.log (900391 / 1000000)) := by
  have h := reflection_log_6695_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6696_neg : (2379527 / 25000000) ≤ -Real.log (500000 / 549929) ∧
    -Real.log (500000 / 549929) ≤ (95181081 / 1000000000) := by
  have h := checkLog_sound (w := (49929 / 1049929)) (n := 12)
    (lo := (2379527 / 25000000)) (hi := (95181081 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((549929 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(549929 / 500000) = 1/(500000 / 549929) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6696 : Bounds (2379527 / 25000000) (95181081 / 1000000000) (Real.log (549929 / 500000)) := by
  have h := reflection_log_6696_neg
  have he : Real.log (549929 / 500000) = -Real.log (500000 / 549929) := by
    rw [show ((549929 / 500000) : ℝ) = ((500000 / 549929) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6697_neg : (420811 / 4000000) ≤ -Real.log (450071 / 500000) ∧
    -Real.log (450071 / 500000) ≤ (105202751 / 1000000000) := by
  have h := checkLog_sound (w := (49929 / 950071)) (n := 12)
    (lo := (420811 / 4000000)) (hi := (105202751 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 450071) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 450071) = 1/(450071 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6697 : Bounds (-105202751 / 1000000000) (-420811 / 4000000) (Real.log (450071 / 500000)) := by
  have h := reflection_log_6697_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6698_neg : (10021669 / 1000000000) ≤ -Real.log (247507094959 / 250000000000) ∧
    -Real.log (247507094959 / 250000000000) ≤ (1002167 / 100000000) := by
  have h := checkLog_sound (w := (2492905041 / 497507094959)) (n := 12)
    (lo := (10021669 / 1000000000)) (hi := (1002167 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247507094959) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247507094959) = 1/(247507094959 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6698 : Bounds (-1002167 / 100000000) (-10021669 / 1000000000) (Real.log (247507094959 / 250000000000)) := by
  have h := reflection_log_6698_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6699_neg : (9971503 / 1000000000) ≤ -Real.log (990078047119 / 1000000000000) ∧
    -Real.log (990078047119 / 1000000000000) ≤ (623219 / 62500000) := by
  have h := checkLog_sound (w := (9921952881 / 1990078047119)) (n := 12)
    (lo := (9971503 / 1000000000)) (hi := (623219 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 990078047119) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 990078047119) = 1/(990078047119 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6699 : Bounds (-623219 / 62500000) (-9971503 / 1000000000) (Real.log (990078047119 / 1000000000000)) := by
  have h := reflection_log_6699_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6700_neg : (199880827 / 1000000000) ≤ -Real.log (500000000000 / 610628604683) ∧
    -Real.log (500000000000 / 610628604683) ≤ (49970207 / 250000000) := by
  have h := checkLog_sound (w := (110628604683 / 1110628604683)) (n := 12)
    (lo := (199880827 / 1000000000)) (hi := (49970207 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((610628604683 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(610628604683 / 500000000000) = 1/(500000000000 / 610628604683) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6700 : Bounds (199880827 / 1000000000) (49970207 / 250000000) (Real.log (610628604683 / 500000000000)) := by
  have h := reflection_log_6700_neg
  have he : Real.log (610628604683 / 500000000000) = -Real.log (500000000000 / 610628604683) := by
    rw [show ((610628604683 / 500000000000) : ℝ) = ((500000000000 / 610628604683) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6701_neg : (20038383 / 100000000) ≤ -Real.log (4000000000 / 4887486641) ∧
    -Real.log (4000000000 / 4887486641) ≤ (200383831 / 1000000000) := by
  have h := checkLog_sound (w := (887486641 / 8887486641)) (n := 12)
    (lo := (20038383 / 100000000)) (hi := (200383831 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4887486641 / 4000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4887486641 / 4000000000) = 1/(4000000000 / 4887486641) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6701 : Bounds (20038383 / 100000000) (200383831 / 1000000000) (Real.log (4887486641 / 4000000000)) := by
  have h := reflection_log_6701_neg
  have he : Real.log (4887486641 / 4000000000) = -Real.log (4000000000 / 4887486641) := by
    rw [show ((4887486641 / 4000000000) : ℝ) = ((4000000000 / 4887486641) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6702_neg : (40130017 / 100000000) ≤ -Real.log (500000000000 / 746882793017) ∧
    -Real.log (500000000000 / 746882793017) ≤ (401300171 / 1000000000) := by
  have h := checkLog_sound (w := (246882793017 / 1246882793017)) (n := 12)
    (lo := (40130017 / 100000000)) (hi := (401300171 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((746882793017 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(746882793017 / 500000000000) = 1/(500000000000 / 746882793017) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6702 : Bounds (40130017 / 100000000) (401300171 / 1000000000) (Real.log (746882793017 / 500000000000)) := by
  have h := reflection_log_6702_neg
  have he : Real.log (746882793017 / 500000000000) = -Real.log (500000000000 / 746882793017) := by
    rw [show ((746882793017 / 500000000000) : ℝ) = ((500000000000 / 746882793017) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6703_neg : (80301667 / 200000000) ≤ -Real.log (125000000000 / 186759571019) ∧
    -Real.log (125000000000 / 186759571019) ≤ (25094271 / 62500000) := by
  have h := checkLog_sound (w := (61759571019 / 311759571019)) (n := 12)
    (lo := (80301667 / 200000000)) (hi := (25094271 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((186759571019 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(186759571019 / 125000000000) = 1/(125000000000 / 186759571019) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6703 : Bounds (80301667 / 200000000) (25094271 / 62500000) (Real.log (186759571019 / 125000000000)) := by
  have h := reflection_log_6703_neg
  have he : Real.log (186759571019 / 125000000000) = -Real.log (125000000000 / 186759571019) := by
    rw [show ((186759571019 / 125000000000) : ℝ) = ((125000000000 / 186759571019) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6704_neg : (18082043 / 100000000) ≤ -Real.log (5000 / 5991) ∧
    -Real.log (5000 / 5991) ≤ (180820431 / 1000000000) := by
  have h := checkLog_sound (w := (991 / 10991)) (n := 12)
    (lo := (18082043 / 100000000)) (hi := (180820431 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5991 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5991 / 5000) = 1/(5000 / 5991) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6704 : Bounds (18082043 / 100000000) (180820431 / 1000000000) (Real.log (5991 / 5000)) := by
  have h := reflection_log_6704_neg
  have he : Real.log (5991 / 5000) = -Real.log (5000 / 5991) := by
    rw [show ((5991 / 5000) : ℝ) = ((5000 / 5991) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6705_neg : (110448039 / 500000000) ≤ -Real.log (4009 / 5000) ∧
    -Real.log (4009 / 5000) ≤ (220896079 / 1000000000) := by
  have h := checkLog_sound (w := (991 / 9009)) (n := 12)
    (lo := (110448039 / 500000000)) (hi := (220896079 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4009) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4009) = 1/(4009 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6705 : Bounds (-220896079 / 1000000000) (-110448039 / 500000000) (Real.log (4009 / 5000)) := by
  have h := reflection_log_6705_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6706_neg : (9909 / 50000000) ≤ -Real.log (5000000 / 5000991) ∧
    -Real.log (5000000 / 5000991) ≤ (198181 / 1000000000) := by
  have h := checkLog_sound (w := (991 / 10000991)) (n := 12)
    (lo := (9909 / 50000000)) (hi := (198181 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000991 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000991 / 5000000) = 1/(5000000 / 5000991) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6706 : Bounds (9909 / 50000000) (198181 / 1000000000) (Real.log (5000991 / 5000000)) := by
  have h := reflection_log_6706_neg
  have he : Real.log (5000991 / 5000000) = -Real.log (5000000 / 5000991) := by
    rw [show ((5000991 / 5000000) : ℝ) = ((5000000 / 5000991) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6707_neg : (198219 / 1000000000) ≤ -Real.log (4999009 / 5000000) ∧
    -Real.log (4999009 / 5000000) ≤ (9911 / 50000000) := by
  have h := checkLog_sound (w := (991 / 9999009)) (n := 12)
    (lo := (198219 / 1000000000)) (hi := (9911 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999009) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999009) = 1/(4999009 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6707 : Bounds (-9911 / 50000000) (-198219 / 1000000000) (Real.log (4999009 / 5000000)) := by
  have h := reflection_log_6707_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6708_neg : (95001041 / 1000000000) ≤ -Real.log (50000 / 54983) ∧
    -Real.log (50000 / 54983) ≤ (47500521 / 500000000) := by
  have h := checkLog_sound (w := (4983 / 104983)) (n := 12)
    (lo := (95001041 / 1000000000)) (hi := (47500521 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((54983 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(54983 / 50000) = 1/(50000 / 54983) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6708 : Bounds (95001041 / 1000000000) (47500521 / 500000000) (Real.log (54983 / 50000)) := by
  have h := reflection_log_6708_neg
  have he : Real.log (54983 / 50000) = -Real.log (50000 / 54983) := by
    rw [show ((54983 / 50000) : ℝ) = ((50000 / 54983) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6709_neg : (104982809 / 1000000000) ≤ -Real.log (45017 / 50000) ∧
    -Real.log (45017 / 50000) ≤ (10498281 / 100000000) := by
  have h := checkLog_sound (w := (4983 / 95017)) (n := 12)
    (lo := (104982809 / 1000000000)) (hi := (10498281 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 45017) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 45017) = 1/(45017 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6709 : Bounds (-10498281 / 100000000) (-104982809 / 1000000000) (Real.log (45017 / 50000)) := by
  have h := reflection_log_6709_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6710_neg : (95227449 / 1000000000) ≤ -Real.log (1000000 / 1099909) ∧
    -Real.log (1000000 / 1099909) ≤ (1904549 / 20000000) := by
  have h := checkLog_sound (w := (99909 / 2099909)) (n := 12)
    (lo := (95227449 / 1000000000)) (hi := (1904549 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1099909 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1099909 / 1000000) = 1/(1000000 / 1099909) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6710 : Bounds (95227449 / 1000000000) (1904549 / 20000000) (Real.log (1099909 / 1000000)) := by
  have h := reflection_log_6710_neg
  have he : Real.log (1099909 / 1000000) = -Real.log (1000000 / 1099909) := by
    rw [show ((1099909 / 1000000) : ℝ) = ((1000000 / 1099909) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6711_neg : (105259409 / 1000000000) ≤ -Real.log (900091 / 1000000) ∧
    -Real.log (900091 / 1000000) ≤ (10525941 / 100000000) := by
  have h := checkLog_sound (w := (99909 / 1900091)) (n := 12)
    (lo := (105259409 / 1000000000)) (hi := (10525941 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 900091) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 900091) = 1/(900091 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6711 : Bounds (-10525941 / 100000000) (-105259409 / 1000000000) (Real.log (900091 / 1000000)) := by
  have h := reflection_log_6711_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6712_neg : (250799 / 25000000) ≤ -Real.log (990018191719 / 1000000000000) ∧
    -Real.log (990018191719 / 1000000000000) ≤ (10031961 / 1000000000) := by
  have h := checkLog_sound (w := (9981808281 / 1990018191719)) (n := 12)
    (lo := (250799 / 25000000)) (hi := (10031961 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 990018191719) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 990018191719) = 1/(990018191719 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6712 : Bounds (-10031961 / 1000000000) (-250799 / 25000000) (Real.log (990018191719 / 1000000000000)) := by
  have h := reflection_log_6712_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6713_neg : (1247721 / 125000000) ≤ -Real.log (2475169711 / 2500000000) ∧
    -Real.log (2475169711 / 2500000000) ≤ (9981769 / 1000000000) := by
  have h := checkLog_sound (w := (24830289 / 4975169711)) (n := 12)
    (lo := (1247721 / 125000000)) (hi := (9981769 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000000 / 2475169711) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000000 / 2475169711) = 1/(2475169711 / 2500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6713 : Bounds (-9981769 / 1000000000) (-1247721 / 125000000) (Real.log (2475169711 / 2500000000)) := by
  have h := reflection_log_6713_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6714_neg : (3999677 / 20000000) ≤ -Real.log (250000000000 / 305345758269) ∧
    -Real.log (250000000000 / 305345758269) ≤ (199983851 / 1000000000) := by
  have h := checkLog_sound (w := (55345758269 / 555345758269)) (n := 12)
    (lo := (3999677 / 20000000)) (hi := (199983851 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((305345758269 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(305345758269 / 250000000000) = 1/(250000000000 / 305345758269) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6714 : Bounds (3999677 / 20000000) (199983851 / 1000000000) (Real.log (305345758269 / 250000000000)) := by
  have h := reflection_log_6714_neg
  have he : Real.log (305345758269 / 250000000000) = -Real.log (250000000000 / 305345758269) := by
    rw [show ((305345758269 / 250000000000) : ℝ) = ((250000000000 / 305345758269) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6715_neg : (100243429 / 500000000) ≤ -Real.log (500000000000 / 610998776791) ∧
    -Real.log (500000000000 / 610998776791) ≤ (200486859 / 1000000000) := by
  have h := checkLog_sound (w := (110998776791 / 1110998776791)) (n := 12)
    (lo := (100243429 / 500000000)) (hi := (200486859 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((610998776791 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(610998776791 / 500000000000) = 1/(500000000000 / 610998776791) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6715 : Bounds (100243429 / 500000000) (200486859 / 1000000000) (Real.log (610998776791 / 500000000000)) := by
  have h := reflection_log_6715_neg
  have he : Real.log (610998776791 / 500000000000) = -Real.log (500000000000 / 610998776791) := by
    rw [show ((610998776791 / 500000000000) : ℝ) = ((500000000000 / 610998776791) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6716_neg : (80301667 / 200000000) ≤ -Real.log (20000000000 / 29881531363) ∧
    -Real.log (20000000000 / 29881531363) ≤ (25094271 / 62500000) := by
  have h := checkLog_sound (w := (9881531363 / 49881531363)) (n := 12)
    (lo := (80301667 / 200000000)) (hi := (25094271 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((29881531363 / 20000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(29881531363 / 20000000000) = 1/(20000000000 / 29881531363) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6716 : Bounds (80301667 / 200000000) (25094271 / 62500000) (Real.log (29881531363 / 20000000000)) := by
  have h := reflection_log_6716_neg
  have he : Real.log (29881531363 / 20000000000) = -Real.log (20000000000 / 29881531363) := by
    rw [show ((29881531363 / 20000000000) : ℝ) = ((20000000000 / 29881531363) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6717_neg : (401716509 / 1000000000) ≤ -Real.log (500000000000 / 747193813919) ∧
    -Real.log (500000000000 / 747193813919) ≤ (40171651 / 100000000) := by
  have h := checkLog_sound (w := (247193813919 / 1247193813919)) (n := 12)
    (lo := (401716509 / 1000000000)) (hi := (40171651 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((747193813919 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(747193813919 / 500000000000) = 1/(500000000000 / 747193813919) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6717 : Bounds (401716509 / 1000000000) (40171651 / 100000000) (Real.log (747193813919 / 500000000000)) := by
  have h := reflection_log_6717_neg
  have he : Real.log (747193813919 / 500000000000) = -Real.log (500000000000 / 747193813919) := by
    rw [show ((747193813919 / 500000000000) : ℝ) = ((500000000000 / 747193813919) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6718_neg : (36180777 / 200000000) ≤ -Real.log (10000 / 11983) ∧
    -Real.log (10000 / 11983) ≤ (90451943 / 500000000) := by
  have h := checkLog_sound (w := (1983 / 21983)) (n := 12)
    (lo := (36180777 / 200000000)) (hi := (90451943 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11983 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11983 / 10000) = 1/(10000 / 11983) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6718 : Bounds (36180777 / 200000000) (90451943 / 500000000) (Real.log (11983 / 10000)) := by
  have h := reflection_log_6718_neg
  have he : Real.log (11983 / 10000) = -Real.log (10000 / 11983) := by
    rw [show ((11983 / 10000) : ℝ) = ((10000 / 11983) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6719_neg : (44204161 / 200000000) ≤ -Real.log (8017 / 10000) ∧
    -Real.log (8017 / 10000) ≤ (110510403 / 500000000) := by
  have h := checkLog_sound (w := (1983 / 18017)) (n := 12)
    (lo := (44204161 / 200000000)) (hi := (110510403 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8017) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8017) = 1/(8017 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6719 : Bounds (-110510403 / 500000000) (-44204161 / 200000000) (Real.log (8017 / 10000)) := by
  have h := reflection_log_6719_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.LowRatioFamily
