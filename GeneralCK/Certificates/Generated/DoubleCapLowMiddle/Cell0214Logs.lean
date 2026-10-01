import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0214
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

theorem reflection_log_1_neg : (272522937 / 500000000) ≤ -Real.log (3200 / 5519) ∧
    -Real.log (3200 / 5519) ≤ (4360367 / 8000000) := by
  have h := checkLog_sound (w := (2319 / 8719)) (n := 12)
    (lo := (272522937 / 500000000)) (hi := (4360367 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5519 / 3200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5519 / 3200) = 1/(3200 / 5519) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (272522937 / 500000000) (4360367 / 8000000) (Real.log (5519 / 3200)) := by
  have h := reflection_log_1_neg
  have he : Real.log (5519 / 3200) = -Real.log (3200 / 5519) := by
    rw [show ((5519 / 3200) : ℝ) = ((3200 / 5519) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (644924231 / 500000000) ≤ -Real.log (881 / 3200) ∧
    -Real.log (881 / 3200) ≤ (80615529 / 62500000) := by
  have h := checkLog_sound (w := (719 / 2481)) (n := 12)
    (lo := (298350641 / 500000000)) (hi := (596701283 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 881) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1600 / 881) = 1/(881 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-80615529 / 62500000) (-644924231 / 500000000) (Real.log (881 / 3200)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (270798641 / 500000000) ≤ -Real.log (32 / 55) ∧
    -Real.log (32 / 55) ≤ (541597283 / 1000000000) := by
  have h := checkLog_sound (w := (23 / 87)) (n := 12)
    (lo := (270798641 / 500000000)) (hi := (541597283 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((55 / 32) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(55 / 32) = 1/(32 / 55) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (270798641 / 500000000) (541597283 / 1000000000) (Real.log (55 / 32)) := by
  have h := reflection_log_3_neg
  have he : Real.log (55 / 32) = -Real.log (32 / 55) := by
    rw [show ((55 / 32) : ℝ) = ((32 / 55) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (317127831 / 250000000) ≤ -Real.log (9 / 32) ∧
    -Real.log (9 / 32) ≤ (634255663 / 500000000) := by
  have h := checkLog_sound (w := (7 / 25)) (n := 12)
    (lo := (35960259 / 62500000)) (hi := (115072829 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((16 / 9) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(16 / 9) = 1/(9 / 32) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-634255663 / 500000000) (-317127831 / 250000000) (Real.log (9 / 32)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (371132429 / 1000000000) ≤ -Real.log (1600 / 2319) ∧
    -Real.log (1600 / 2319) ≤ (37113243 / 100000000) := by
  have h := checkLog_sound (w := (719 / 3919)) (n := 12)
    (lo := (371132429 / 1000000000)) (hi := (37113243 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2319 / 1600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2319 / 1600) = 1/(1600 / 2319) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (371132429 / 1000000000) (37113243 / 100000000) (Real.log (2319 / 1600)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2319 / 1600) = -Real.log (1600 / 2319) := by
    rw [show ((2319 / 1600) : ℝ) = ((1600 / 2319) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (298350641 / 500000000) ≤ -Real.log (881 / 1600) ∧
    -Real.log (881 / 1600) ≤ (596701283 / 1000000000) := by
  have h := checkLog_sound (w := (719 / 2481)) (n := 12)
    (lo := (298350641 / 500000000)) (hi := (596701283 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 881) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1600 / 881) = 1/(881 / 1600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-596701283 / 1000000000) (-298350641 / 500000000) (Real.log (881 / 1600)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (362905493 / 1000000000) ≤ -Real.log (16 / 23) ∧
    -Real.log (16 / 23) ≤ (181452747 / 500000000) := by
  have h := checkLog_sound (w := (7 / 39)) (n := 12)
    (lo := (362905493 / 1000000000)) (hi := (181452747 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((23 / 16) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(23 / 16) = 1/(16 / 23) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (362905493 / 1000000000) (181452747 / 500000000) (Real.log (23 / 16)) := by
  have h := reflection_log_7_neg
  have he : Real.log (23 / 16) = -Real.log (16 / 23) := by
    rw [show ((23 / 16) : ℝ) = ((16 / 23) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (35960259 / 62500000) ≤ -Real.log (9 / 16) ∧
    -Real.log (9 / 16) ≤ (115072829 / 200000000) := by
  have h := checkLog_sound (w := (7 / 25)) (n := 12)
    (lo := (35960259 / 62500000)) (hi := (115072829 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((16 / 9) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(16 / 9) = 1/(9 / 16) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-115072829 / 200000000) (-35960259 / 62500000) (Real.log (9 / 16)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (601416137 / 1000000000) ≤ -Real.log (1000000 / 1824701) ∧
    -Real.log (1000000 / 1824701) ≤ (300708069 / 500000000) := by
  have h := checkLog_sound (w := (824701 / 2824701)) (n := 12)
    (lo := (601416137 / 1000000000)) (hi := (300708069 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1824701 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1824701 / 1000000) = 1/(1000000 / 1824701) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (601416137 / 1000000000) (300708069 / 500000000) (Real.log (1824701 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1824701 / 1000000) = -Real.log (1000000 / 1824701) := by
    rw [show ((1824701 / 1000000) : ℝ) = ((1000000 / 1824701) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (174126219 / 100000000) ≤ -Real.log (175299 / 1000000) ∧
    -Real.log (175299 / 1000000) ≤ (1741262193 / 1000000000) := by
  have h := checkLog_sound (w := (74701 / 425299)) (n := 12)
    (lo := (35496783 / 100000000)) (hi := (354967831 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 175299) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(250000 / 175299) = 1/(175299 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-1741262193 / 1000000000) (-174126219 / 100000000) (Real.log (175299 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (602735483 / 1000000000) ≤ -Real.log (100000 / 182711) ∧
    -Real.log (100000 / 182711) ≤ (150683871 / 250000000) := by
  have h := checkLog_sound (w := (82711 / 282711)) (n := 12)
    (lo := (602735483 / 1000000000)) (hi := (150683871 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((182711 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(182711 / 100000) = 1/(100000 / 182711) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (602735483 / 1000000000) (150683871 / 250000000) (Real.log (182711 / 100000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (182711 / 100000) = -Real.log (100000 / 182711) := by
    rw [show ((182711 / 100000) : ℝ) = ((100000 / 182711) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1755099723 / 1000000000) ≤ -Real.log (17289 / 100000) ∧
    -Real.log (17289 / 100000) ≤ (877549863 / 500000000) := by
  have h := checkLog_sound (w := (7711 / 42289)) (n := 12)
    (lo := (368805363 / 1000000000)) (hi := (92201341 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 17289) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(25000 / 17289) = 1/(17289 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-877549863 / 500000000) (-1755099723 / 1000000000) (Real.log (17289 / 100000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (58573289 / 100000000) ≤ -Real.log (1000000 / 1796307) ∧
    -Real.log (1000000 / 1796307) ≤ (585732891 / 1000000000) := by
  have h := checkLog_sound (w := (796307 / 2796307)) (n := 12)
    (lo := (58573289 / 100000000)) (hi := (585732891 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1796307 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1796307 / 1000000) = 1/(1000000 / 1796307) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (58573289 / 100000000) (585732891 / 1000000000) (Real.log (1796307 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1796307 / 1000000) = -Real.log (1000000 / 1796307) := by
    rw [show ((1796307 / 1000000) : ℝ) = ((1000000 / 1796307) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (1591141319 / 1000000000) ≤ -Real.log (203693 / 1000000) ∧
    -Real.log (203693 / 1000000) ≤ (795570661 / 500000000) := by
  have h := checkLog_sound (w := (46307 / 453693)) (n := 12)
    (lo := (204846959 / 1000000000)) (hi := (2560587 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 203693) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(250000 / 203693) = 1/(203693 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-795570661 / 500000000) (-1591141319 / 1000000000) (Real.log (203693 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (73485763 / 125000000) ≤ -Real.log (1000000 / 1800179) ∧
    -Real.log (1000000 / 1800179) ≤ (117577221 / 200000000) := by
  have h := checkLog_sound (w := (800179 / 2800179)) (n := 12)
    (lo := (73485763 / 125000000)) (hi := (117577221 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1800179 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1800179 / 1000000) = 1/(1000000 / 1800179) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (73485763 / 125000000) (117577221 / 200000000) (Real.log (1800179 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1800179 / 1000000) = -Real.log (1000000 / 1800179) := by
    rw [show ((1800179 / 1000000) : ℝ) = ((1000000 / 1800179) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (12580729 / 7812500) ≤ -Real.log (199821 / 1000000) ∧
    -Real.log (199821 / 1000000) ≤ (322066663 / 200000000) := by
  have h := checkLog_sound (w := (50179 / 449821)) (n := 12)
    (lo := (28004869 / 125000000)) (hi := (224038953 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 199821) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(250000 / 199821) = 1/(199821 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-322066663 / 200000000) (-12580729 / 7812500) (Real.log (199821 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (2342678327 / 1000000000) ≤ -Real.log (500000000000 / 5204539101763) ∧
    -Real.log (500000000000 / 5204539101763) ≤ (2342678331 / 1000000000) := by
  have h := checkLog_sound (w := (1204539101763 / 9204539101763)) (n := 12)
    (lo := (263236787 / 1000000000)) (hi := (65809197 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5204539101763 / 4000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(5204539101763 / 4000000000000) = 1/(500000000000 / 5204539101763) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (2342678327 / 1000000000) (2342678331 / 1000000000) (Real.log (5204539101763 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (5204539101763 / 500000000000) = -Real.log (500000000000 / 5204539101763) := by
    rw [show ((5204539101763 / 500000000000) : ℝ) = ((500000000000 / 5204539101763) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1178917603 / 500000000) ≤ -Real.log (62500000000 / 660503065533) ∧
    -Real.log (62500000000 / 660503065533) ≤ (235783521 / 100000000) := by
  have h := checkLog_sound (w := (160503065533 / 1160503065533)) (n := 12)
    (lo := (139196833 / 500000000)) (hi := (278393667 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((660503065533 / 500000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(660503065533 / 500000000000) = 1/(62500000000 / 660503065533) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1178917603 / 500000000) (235783521 / 100000000) (Real.log (660503065533 / 62500000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (660503065533 / 62500000000) = -Real.log (62500000000 / 660503065533) := by
    rw [show ((660503065533 / 62500000000) : ℝ) = ((62500000000 / 660503065533) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (2176874209 / 1000000000) ≤ -Real.log (250000000000 / 2204674436529) ∧
    -Real.log (250000000000 / 2204674436529) ≤ (2176874213 / 1000000000) := by
  have h := checkLog_sound (w := (204674436529 / 4204674436529)) (n := 12)
    (lo := (97432669 / 1000000000)) (hi := (9743267 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2204674436529 / 2000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(2204674436529 / 2000000000000) = 1/(250000000000 / 2204674436529) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (2176874209 / 1000000000) (2176874213 / 1000000000) (Real.log (2204674436529 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (2204674436529 / 250000000000) = -Real.log (250000000000 / 2204674436529) := by
    rw [show ((2204674436529 / 250000000000) : ℝ) = ((250000000000 / 2204674436529) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (439643883 / 200000000) ≤ -Real.log (500000000000 / 4504479008713) ∧
    -Real.log (500000000000 / 4504479008713) ≤ (2198219419 / 1000000000) := by
  have h := checkLog_sound (w := (504479008713 / 8504479008713)) (n := 12)
    (lo := (950223 / 8000000)) (hi := (29694469 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4504479008713 / 4000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(4504479008713 / 4000000000000) = 1/(500000000000 / 4504479008713) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (439643883 / 200000000) (2198219419 / 1000000000) (Real.log (4504479008713 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (4504479008713 / 500000000000) = -Real.log (500000000000 / 4504479008713) := by
    rw [show ((4504479008713 / 500000000000) : ℝ) = ((500000000000 / 4504479008713) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0214
