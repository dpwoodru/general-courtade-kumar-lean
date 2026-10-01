import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_2560_neg : (68048971 / 200000000) ≤ -Real.log (250000000000 / 351322910403) ∧
    -Real.log (250000000000 / 351322910403) ≤ (42530607 / 125000000) := by
  have h := checkLog_sound (w := (101322910403 / 601322910403)) (n := 12)
    (lo := (68048971 / 200000000)) (hi := (42530607 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((351322910403 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(351322910403 / 250000000000) = 1/(250000000000 / 351322910403) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2560 : Bounds (68048971 / 200000000) (42530607 / 125000000) (Real.log (351322910403 / 250000000000)) := by
  have h := reflection_log_2560_neg
  have he : Real.log (351322910403 / 250000000000) = -Real.log (250000000000 / 351322910403) := by
    rw [show ((351322910403 / 250000000000) : ℝ) = ((250000000000 / 351322910403) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2561_neg : (155806451 / 1000000000) ≤ -Real.log (5000 / 5843) ∧
    -Real.log (5000 / 5843) ≤ (38951613 / 250000000) := by
  have h := checkLog_sound (w := (843 / 10843)) (n := 12)
    (lo := (155806451 / 1000000000)) (hi := (38951613 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5843 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5843 / 5000) = 1/(5000 / 5843) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2561 : Bounds (155806451 / 1000000000) (38951613 / 250000000) (Real.log (5843 / 5000)) := by
  have h := reflection_log_2561_neg
  have he : Real.log (5843 / 5000) = -Real.log (5000 / 5843) := by
    rw [show ((5843 / 5000) : ℝ) = ((5000 / 5843) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2562_neg : (46161063 / 250000000) ≤ -Real.log (4157 / 5000) ∧
    -Real.log (4157 / 5000) ≤ (184644253 / 1000000000) := by
  have h := checkLog_sound (w := (843 / 9157)) (n := 12)
    (lo := (46161063 / 250000000)) (hi := (184644253 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4157) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4157) = 1/(4157 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2562 : Bounds (-184644253 / 1000000000) (-46161063 / 250000000) (Real.log (4157 / 5000)) := by
  have h := reflection_log_2562_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2563_neg : (33717 / 200000000) ≤ -Real.log (5000000 / 5000843) ∧
    -Real.log (5000000 / 5000843) ≤ (84293 / 500000000) := by
  have h := checkLog_sound (w := (843 / 10000843)) (n := 12)
    (lo := (33717 / 200000000)) (hi := (84293 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000843 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000843 / 5000000) = 1/(5000000 / 5000843) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2563 : Bounds (33717 / 200000000) (84293 / 500000000) (Real.log (5000843 / 5000000)) := by
  have h := reflection_log_2563_neg
  have he : Real.log (5000843 / 5000000) = -Real.log (5000000 / 5000843) := by
    rw [show ((5000843 / 5000000) : ℝ) = ((5000000 / 5000843) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2564_neg : (84307 / 500000000) ≤ -Real.log (4999157 / 5000000) ∧
    -Real.log (4999157 / 5000000) ≤ (33723 / 200000000) := by
  have h := checkLog_sound (w := (843 / 9999157)) (n := 12)
    (lo := (84307 / 500000000)) (hi := (33723 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999157) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999157) = 1/(4999157 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2564 : Bounds (-33723 / 200000000) (-84307 / 500000000) (Real.log (4999157 / 5000000)) := by
  have h := reflection_log_2564_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2565_neg : (81212177 / 1000000000) ≤ -Real.log (1000000 / 1084601) ∧
    -Real.log (1000000 / 1084601) ≤ (40606089 / 500000000) := by
  have h := checkLog_sound (w := (84601 / 2084601)) (n := 12)
    (lo := (81212177 / 1000000000)) (hi := (40606089 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1084601 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1084601 / 1000000) = 1/(1000000 / 1084601) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2565 : Bounds (81212177 / 1000000000) (40606089 / 500000000) (Real.log (1084601 / 1000000)) := by
  have h := reflection_log_2565_neg
  have he : Real.log (1084601 / 1000000) = -Real.log (1000000 / 1084601) := by
    rw [show ((1084601 / 1000000) : ℝ) = ((1000000 / 1084601) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2566_neg : (88395243 / 1000000000) ≤ -Real.log (915399 / 1000000) ∧
    -Real.log (915399 / 1000000) ≤ (22098811 / 250000000) := by
  have h := checkLog_sound (w := (84601 / 1915399)) (n := 12)
    (lo := (88395243 / 1000000000)) (hi := (22098811 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 915399) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 915399) = 1/(915399 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2566 : Bounds (-22098811 / 250000000) (-88395243 / 1000000000) (Real.log (915399 / 1000000)) := by
  have h := reflection_log_2566_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2567_neg : (40707037 / 500000000) ≤ -Real.log (50000 / 54241) ∧
    -Real.log (50000 / 54241) ≤ (3256563 / 40000000) := by
  have h := checkLog_sound (w := (4241 / 104241)) (n := 12)
    (lo := (40707037 / 500000000)) (hi := (3256563 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((54241 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(54241 / 50000) = 1/(50000 / 54241) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2567 : Bounds (40707037 / 500000000) (3256563 / 40000000) (Real.log (54241 / 50000)) := by
  have h := reflection_log_2567_neg
  have he : Real.log (54241 / 50000) = -Real.log (50000 / 54241) := by
    rw [show ((54241 / 50000) : ℝ) = ((50000 / 54241) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2568_neg : (88634511 / 1000000000) ≤ -Real.log (45759 / 50000) ∧
    -Real.log (45759 / 50000) ≤ (5539657 / 62500000) := by
  have h := checkLog_sound (w := (4241 / 95759)) (n := 12)
    (lo := (88634511 / 1000000000)) (hi := (5539657 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 45759) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 45759) = 1/(45759 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2568 : Bounds (-5539657 / 62500000) (-88634511 / 1000000000) (Real.log (45759 / 50000)) := by
  have h := reflection_log_2568_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2569_neg : (7220437 / 1000000000) ≤ -Real.log (2482013919 / 2500000000) ∧
    -Real.log (2482013919 / 2500000000) ≤ (3610219 / 500000000) := by
  have h := checkLog_sound (w := (17986081 / 4982013919)) (n := 12)
    (lo := (7220437 / 1000000000)) (hi := (3610219 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000000 / 2482013919) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000000 / 2482013919) = 1/(2482013919 / 2500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2569 : Bounds (-3610219 / 500000000) (-7220437 / 1000000000) (Real.log (2482013919 / 2500000000)) := by
  have h := reflection_log_2569_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2570_neg : (1436613 / 200000000) ≤ -Real.log (992842670799 / 1000000000000) ∧
    -Real.log (992842670799 / 1000000000000) ≤ (3591533 / 500000000) := by
  have h := checkLog_sound (w := (7157329201 / 1992842670799)) (n := 12)
    (lo := (1436613 / 200000000)) (hi := (3591533 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 992842670799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 992842670799) = 1/(992842670799 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2570 : Bounds (-3591533 / 500000000) (-1436613 / 200000000) (Real.log (992842670799 / 1000000000000)) := by
  have h := reflection_log_2570_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2571_neg : (8480371 / 50000000) ≤ -Real.log (7812500000 / 9256559503) ∧
    -Real.log (7812500000 / 9256559503) ≤ (169607421 / 1000000000) := by
  have h := checkLog_sound (w := (1444059503 / 17069059503)) (n := 12)
    (lo := (8480371 / 50000000)) (hi := (169607421 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9256559503 / 7812500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(9256559503 / 7812500000) = 1/(7812500000 / 9256559503) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2571 : Bounds (8480371 / 50000000) (169607421 / 1000000000) (Real.log (9256559503 / 7812500000)) := by
  have h := reflection_log_2571_neg
  have he : Real.log (9256559503 / 7812500000) = -Real.log (7812500000 / 9256559503) := by
    rw [show ((9256559503 / 7812500000) : ℝ) = ((7812500000 / 9256559503) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2572_neg : (85024293 / 500000000) ≤ -Real.log (500000000000 / 592681221181) ∧
    -Real.log (500000000000 / 592681221181) ≤ (170048587 / 1000000000) := by
  have h := checkLog_sound (w := (92681221181 / 1092681221181)) (n := 12)
    (lo := (85024293 / 500000000)) (hi := (170048587 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((592681221181 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(592681221181 / 500000000000) = 1/(500000000000 / 592681221181) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2572 : Bounds (85024293 / 500000000) (170048587 / 1000000000) (Real.log (592681221181 / 500000000000)) := by
  have h := reflection_log_2572_neg
  have he : Real.log (592681221181 / 500000000000) = -Real.log (500000000000 / 592681221181) := by
    rw [show ((592681221181 / 500000000000) : ℝ) = ((500000000000 / 592681221181) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2573_neg : (68048971 / 200000000) ≤ -Real.log (100000000000 / 140529164161) ∧
    -Real.log (100000000000 / 140529164161) ≤ (42530607 / 125000000) := by
  have h := checkLog_sound (w := (40529164161 / 240529164161)) (n := 12)
    (lo := (68048971 / 200000000)) (hi := (42530607 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((140529164161 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(140529164161 / 100000000000) = 1/(100000000000 / 140529164161) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2573 : Bounds (68048971 / 200000000) (42530607 / 125000000) (Real.log (140529164161 / 100000000000)) := by
  have h := reflection_log_2573_neg
  have he : Real.log (140529164161 / 100000000000) = -Real.log (100000000000 / 140529164161) := by
    rw [show ((140529164161 / 100000000000) : ℝ) = ((100000000000 / 140529164161) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2574_neg : (340450703 / 1000000000) ≤ -Real.log (5000000000 / 7027904739) ∧
    -Real.log (5000000000 / 7027904739) ≤ (21278169 / 62500000) := by
  have h := checkLog_sound (w := (2027904739 / 12027904739)) (n := 12)
    (lo := (340450703 / 1000000000)) (hi := (21278169 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7027904739 / 5000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7027904739 / 5000000000) = 1/(5000000000 / 7027904739) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2574 : Bounds (340450703 / 1000000000) (21278169 / 62500000) (Real.log (7027904739 / 5000000000)) := by
  have h := reflection_log_2574_neg
  have he : Real.log (7027904739 / 5000000000) = -Real.log (5000000000 / 7027904739) := by
    rw [show ((7027904739 / 5000000000) : ℝ) = ((5000000000 / 7027904739) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2575_neg : (155892019 / 1000000000) ≤ -Real.log (10000 / 11687) ∧
    -Real.log (10000 / 11687) ≤ (7794601 / 50000000) := by
  have h := checkLog_sound (w := (1687 / 21687)) (n := 12)
    (lo := (155892019 / 1000000000)) (hi := (7794601 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11687 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11687 / 10000) = 1/(10000 / 11687) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2575 : Bounds (155892019 / 1000000000) (7794601 / 50000000) (Real.log (11687 / 10000)) := by
  have h := reflection_log_2575_neg
  have he : Real.log (11687 / 10000) = -Real.log (10000 / 11687) := by
    rw [show ((11687 / 10000) : ℝ) = ((10000 / 11687) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2576_neg : (92382269 / 500000000) ≤ -Real.log (8313 / 10000) ∧
    -Real.log (8313 / 10000) ≤ (184764539 / 1000000000) := by
  have h := checkLog_sound (w := (1687 / 18313)) (n := 12)
    (lo := (92382269 / 500000000)) (hi := (184764539 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8313) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8313) = 1/(8313 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2576 : Bounds (-184764539 / 1000000000) (-92382269 / 500000000) (Real.log (8313 / 10000)) := by
  have h := reflection_log_2576_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2577_neg : (33737 / 200000000) ≤ -Real.log (10000000 / 10001687) ∧
    -Real.log (10000000 / 10001687) ≤ (84343 / 500000000) := by
  have h := checkLog_sound (w := (1687 / 20001687)) (n := 12)
    (lo := (33737 / 200000000)) (hi := (84343 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001687 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001687 / 10000000) = 1/(10000000 / 10001687) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2577 : Bounds (33737 / 200000000) (84343 / 500000000) (Real.log (10001687 / 10000000)) := by
  have h := reflection_log_2577_neg
  have he : Real.log (10001687 / 10000000) = -Real.log (10000000 / 10001687) := by
    rw [show ((10001687 / 10000000) : ℝ) = ((10000000 / 10001687) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2578_neg : (84357 / 500000000) ≤ -Real.log (9998313 / 10000000) ∧
    -Real.log (9998313 / 10000000) ≤ (33743 / 200000000) := by
  have h := checkLog_sound (w := (1687 / 19998313)) (n := 12)
    (lo := (84357 / 500000000)) (hi := (33743 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998313) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998313) = 1/(9998313 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2578 : Bounds (-33743 / 200000000) (-84357 / 500000000) (Real.log (9998313 / 10000000)) := by
  have h := reflection_log_2578_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2579_neg : (20314569 / 250000000) ≤ -Real.log (1000000 / 1084651) ∧
    -Real.log (1000000 / 1084651) ≤ (81258277 / 1000000000) := by
  have h := checkLog_sound (w := (84651 / 2084651)) (n := 12)
    (lo := (20314569 / 250000000)) (hi := (81258277 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1084651 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1084651 / 1000000) = 1/(1000000 / 1084651) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2579 : Bounds (20314569 / 250000000) (81258277 / 1000000000) (Real.log (1084651 / 1000000)) := by
  have h := reflection_log_2579_neg
  have he : Real.log (1084651 / 1000000) = -Real.log (1000000 / 1084651) := by
    rw [show ((1084651 / 1000000) : ℝ) = ((1000000 / 1084651) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2580_neg : (17689973 / 200000000) ≤ -Real.log (915349 / 1000000) ∧
    -Real.log (915349 / 1000000) ≤ (44224933 / 500000000) := by
  have h := checkLog_sound (w := (84651 / 1915349)) (n := 12)
    (lo := (17689973 / 200000000)) (hi := (44224933 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 915349) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 915349) = 1/(915349 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2580 : Bounds (-44224933 / 500000000) (-17689973 / 200000000) (Real.log (915349 / 1000000)) := by
  have h := reflection_log_2580_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2581_neg : (16292217 / 200000000) ≤ -Real.log (1000000 / 1084871) ∧
    -Real.log (1000000 / 1084871) ≤ (40730543 / 500000000) := by
  have h := checkLog_sound (w := (84871 / 2084871)) (n := 12)
    (lo := (16292217 / 200000000)) (hi := (40730543 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1084871 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1084871 / 1000000) = 1/(1000000 / 1084871) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2581 : Bounds (16292217 / 200000000) (40730543 / 500000000) (Real.log (1084871 / 1000000)) := by
  have h := reflection_log_2581_neg
  have he : Real.log (1084871 / 1000000) = -Real.log (1000000 / 1084871) := by
    rw [show ((1084871 / 1000000) : ℝ) = ((1000000 / 1084871) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2582_neg : (277157 / 3125000) ≤ -Real.log (915129 / 1000000) ∧
    -Real.log (915129 / 1000000) ≤ (88690241 / 1000000000) := by
  have h := checkLog_sound (w := (84871 / 1915129)) (n := 12)
    (lo := (277157 / 3125000)) (hi := (88690241 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 915129) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 915129) = 1/(915129 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2582 : Bounds (-88690241 / 1000000000) (-277157 / 3125000) (Real.log (915129 / 1000000)) := by
  have h := reflection_log_2582_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2583_neg : (3614577 / 500000000) ≤ -Real.log (992796913359 / 1000000000000) ∧
    -Real.log (992796913359 / 1000000000000) ≤ (1445831 / 200000000) := by
  have h := checkLog_sound (w := (7203086641 / 1992796913359)) (n := 12)
    (lo := (3614577 / 500000000)) (hi := (1445831 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 992796913359) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 992796913359) = 1/(992796913359 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2583 : Bounds (-1445831 / 200000000) (-3614577 / 500000000) (Real.log (992796913359 / 1000000000000)) := by
  have h := reflection_log_2583_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2584_neg : (7191589 / 1000000000) ≤ -Real.log (992834208199 / 1000000000000) ∧
    -Real.log (992834208199 / 1000000000000) ≤ (719159 / 100000000) := by
  have h := checkLog_sound (w := (7165791801 / 1992834208199)) (n := 12)
    (lo := (7191589 / 1000000000)) (hi := (719159 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 992834208199) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 992834208199) = 1/(992834208199 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2584 : Bounds (-719159 / 100000000) (-7191589 / 1000000000) (Real.log (992834208199 / 1000000000000)) := by
  have h := reflection_log_2584_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2585_neg : (169708141 / 1000000000) ≤ -Real.log (62500000000 / 74059935063) ∧
    -Real.log (62500000000 / 74059935063) ≤ (84854071 / 500000000) := by
  have h := checkLog_sound (w := (11559935063 / 136559935063)) (n := 12)
    (lo := (169708141 / 1000000000)) (hi := (84854071 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((74059935063 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(74059935063 / 62500000000) = 1/(62500000000 / 74059935063) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2585 : Bounds (169708141 / 1000000000) (84854071 / 500000000) (Real.log (74059935063 / 62500000000)) := by
  have h := reflection_log_2585_neg
  have he : Real.log (74059935063 / 62500000000) = -Real.log (62500000000 / 74059935063) := by
    rw [show ((74059935063 / 62500000000) : ℝ) = ((62500000000 / 74059935063) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2586_neg : (6806053 / 40000000) ≤ -Real.log (500000000000 / 592742116139) ∧
    -Real.log (500000000000 / 592742116139) ≤ (85075663 / 500000000) := by
  have h := checkLog_sound (w := (92742116139 / 1092742116139)) (n := 12)
    (lo := (6806053 / 40000000)) (hi := (85075663 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((592742116139 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(592742116139 / 500000000000) = 1/(500000000000 / 592742116139) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2586 : Bounds (6806053 / 40000000) (85075663 / 500000000) (Real.log (592742116139 / 500000000000)) := by
  have h := reflection_log_2586_neg
  have he : Real.log (592742116139 / 500000000000) = -Real.log (500000000000 / 592742116139) := by
    rw [show ((592742116139 / 500000000000) : ℝ) = ((500000000000 / 592742116139) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2587_neg : (340450703 / 1000000000) ≤ -Real.log (500000000000 / 702790473899) ∧
    -Real.log (500000000000 / 702790473899) ≤ (21278169 / 62500000) := by
  have h := checkLog_sound (w := (202790473899 / 1202790473899)) (n := 12)
    (lo := (340450703 / 1000000000)) (hi := (21278169 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((702790473899 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(702790473899 / 500000000000) = 1/(500000000000 / 702790473899) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2587 : Bounds (340450703 / 1000000000) (21278169 / 62500000) (Real.log (702790473899 / 500000000000)) := by
  have h := reflection_log_2587_neg
  have he : Real.log (702790473899 / 500000000000) = -Real.log (500000000000 / 702790473899) := by
    rw [show ((702790473899 / 500000000000) : ℝ) = ((500000000000 / 702790473899) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2588_neg : (170328279 / 500000000) ≤ -Real.log (100000000000 / 140587032359) ∧
    -Real.log (100000000000 / 140587032359) ≤ (340656559 / 1000000000) := by
  have h := checkLog_sound (w := (40587032359 / 240587032359)) (n := 12)
    (lo := (170328279 / 500000000)) (hi := (340656559 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((140587032359 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(140587032359 / 100000000000) = 1/(100000000000 / 140587032359) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2588 : Bounds (170328279 / 500000000) (340656559 / 1000000000) (Real.log (140587032359 / 100000000000)) := by
  have h := reflection_log_2588_neg
  have he : Real.log (140587032359 / 100000000000) = -Real.log (100000000000 / 140587032359) := by
    rw [show ((140587032359 / 100000000000) : ℝ) = ((100000000000 / 140587032359) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2589_neg : (155977581 / 1000000000) ≤ -Real.log (1250 / 1461) ∧
    -Real.log (1250 / 1461) ≤ (77988791 / 500000000) := by
  have h := checkLog_sound (w := (211 / 2711)) (n := 12)
    (lo := (155977581 / 1000000000)) (hi := (77988791 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1461 / 1250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1461 / 1250) = 1/(1250 / 1461) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2589 : Bounds (155977581 / 1000000000) (77988791 / 500000000) (Real.log (1461 / 1250)) := by
  have h := reflection_log_2589_neg
  have he : Real.log (1461 / 1250) = -Real.log (1250 / 1461) := by
    rw [show ((1461 / 1250) : ℝ) = ((1250 / 1461) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2590_neg : (184884839 / 1000000000) ≤ -Real.log (1039 / 1250) ∧
    -Real.log (1039 / 1250) ≤ (4622121 / 25000000) := by
  have h := checkLog_sound (w := (211 / 2289)) (n := 12)
    (lo := (184884839 / 1000000000)) (hi := (4622121 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250 / 1039) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1250 / 1039) = 1/(1039 / 1250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2590 : Bounds (-4622121 / 25000000) (-184884839 / 1000000000) (Real.log (1039 / 1250)) := by
  have h := reflection_log_2590_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2591_neg : (33757 / 200000000) ≤ -Real.log (1250000 / 1250211) ∧
    -Real.log (1250000 / 1250211) ≤ (84393 / 500000000) := by
  have h := checkLog_sound (w := (211 / 2500211)) (n := 12)
    (lo := (33757 / 200000000)) (hi := (84393 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250211 / 1250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1250211 / 1250000) = 1/(1250000 / 1250211) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2591 : Bounds (33757 / 200000000) (84393 / 500000000) (Real.log (1250211 / 1250000)) := by
  have h := reflection_log_2591_neg
  have he : Real.log (1250211 / 1250000) = -Real.log (1250000 / 1250211) := by
    rw [show ((1250211 / 1250000) : ℝ) = ((1250000 / 1250211) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2592_neg : (84407 / 500000000) ≤ -Real.log (1249789 / 1250000) ∧
    -Real.log (1249789 / 1250000) ≤ (33763 / 200000000) := by
  have h := checkLog_sound (w := (211 / 2499789)) (n := 12)
    (lo := (84407 / 500000000)) (hi := (33763 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250000 / 1249789) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1250000 / 1249789) = 1/(1249789 / 1250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2592 : Bounds (-33763 / 200000000) (-84407 / 500000000) (Real.log (1249789 / 1250000)) := by
  have h := reflection_log_2592_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2593_neg : (40652647 / 500000000) ≤ -Real.log (500000 / 542351) ∧
    -Real.log (500000 / 542351) ≤ (16261059 / 200000000) := by
  have h := checkLog_sound (w := (42351 / 1042351)) (n := 12)
    (lo := (40652647 / 500000000)) (hi := (16261059 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((542351 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(542351 / 500000) = 1/(500000 / 542351) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2593 : Bounds (40652647 / 500000000) (16261059 / 200000000) (Real.log (542351 / 500000)) := by
  have h := reflection_log_2593_neg
  have he : Real.log (542351 / 500000) = -Real.log (500000 / 542351) := by
    rw [show ((542351 / 500000) : ℝ) = ((500000 / 542351) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2594_neg : (88505583 / 1000000000) ≤ -Real.log (457649 / 500000) ∧
    -Real.log (457649 / 500000) ≤ (5531599 / 62500000) := by
  have h := checkLog_sound (w := (42351 / 957649)) (n := 12)
    (lo := (88505583 / 1000000000)) (hi := (5531599 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 457649) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 457649) = 1/(457649 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2594 : Bounds (-5531599 / 62500000) (-88505583 / 1000000000) (Real.log (457649 / 500000)) := by
  have h := reflection_log_2594_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2595_neg : (16301619 / 200000000) ≤ -Real.log (500000 / 542461) ∧
    -Real.log (500000 / 542461) ≤ (318391 / 3906250) := by
  have h := checkLog_sound (w := (42461 / 1042461)) (n := 12)
    (lo := (16301619 / 200000000)) (hi := (318391 / 3906250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((542461 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(542461 / 500000) = 1/(500000 / 542461) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2595 : Bounds (16301619 / 200000000) (318391 / 3906250) (Real.log (542461 / 500000)) := by
  have h := reflection_log_2595_neg
  have he : Real.log (542461 / 500000) = -Real.log (500000 / 542461) := by
    rw [show ((542461 / 500000) : ℝ) = ((500000 / 542461) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2596_neg : (88745971 / 1000000000) ≤ -Real.log (457539 / 500000) ∧
    -Real.log (457539 / 500000) ≤ (22186493 / 250000000) := by
  have h := checkLog_sound (w := (42461 / 957539)) (n := 12)
    (lo := (88745971 / 1000000000)) (hi := (22186493 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 457539) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 457539) = 1/(457539 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2596 : Bounds (-22186493 / 250000000) (-88745971 / 1000000000) (Real.log (457539 / 500000)) := by
  have h := reflection_log_2596_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2597_neg : (1809469 / 250000000) ≤ -Real.log (248197063479 / 250000000000) ∧
    -Real.log (248197063479 / 250000000000) ≤ (7237877 / 1000000000) := by
  have h := checkLog_sound (w := (1802936521 / 498197063479)) (n := 12)
    (lo := (1809469 / 250000000)) (hi := (7237877 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248197063479) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248197063479) = 1/(248197063479 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2597 : Bounds (-7237877 / 1000000000) (-1809469 / 250000000) (Real.log (248197063479 / 250000000000)) := by
  have h := reflection_log_2597_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2598_neg : (225009 / 31250000) ≤ -Real.log (248206392799 / 250000000000) ∧
    -Real.log (248206392799 / 250000000000) ≤ (7200289 / 1000000000) := by
  have h := checkLog_sound (w := (1793607201 / 498206392799)) (n := 12)
    (lo := (225009 / 31250000)) (hi := (7200289 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248206392799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248206392799) = 1/(248206392799 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2598 : Bounds (-7200289 / 1000000000) (-225009 / 31250000) (Real.log (248206392799 / 250000000000)) := by
  have h := reflection_log_2598_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2599_neg : (84905439 / 500000000) ≤ -Real.log (500000000000 / 592540352977) ∧
    -Real.log (500000000000 / 592540352977) ≤ (169810879 / 1000000000) := by
  have h := checkLog_sound (w := (92540352977 / 1092540352977)) (n := 12)
    (lo := (84905439 / 500000000)) (hi := (169810879 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((592540352977 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(592540352977 / 500000000000) = 1/(500000000000 / 592540352977) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2599 : Bounds (84905439 / 500000000) (169810879 / 1000000000) (Real.log (592540352977 / 500000000000)) := by
  have h := reflection_log_2599_neg
  have he : Real.log (592540352977 / 500000000000) = -Real.log (500000000000 / 592540352977) := by
    rw [show ((592540352977 / 500000000000) : ℝ) = ((500000000000 / 592540352977) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2600_neg : (85127033 / 500000000) ≤ -Real.log (100000000000 / 118560603577) ∧
    -Real.log (100000000000 / 118560603577) ≤ (170254067 / 1000000000) := by
  have h := checkLog_sound (w := (18560603577 / 218560603577)) (n := 12)
    (lo := (85127033 / 500000000)) (hi := (170254067 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((118560603577 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(118560603577 / 100000000000) = 1/(100000000000 / 118560603577) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2600 : Bounds (85127033 / 500000000) (170254067 / 1000000000) (Real.log (118560603577 / 100000000000)) := by
  have h := reflection_log_2600_neg
  have he : Real.log (118560603577 / 100000000000) = -Real.log (100000000000 / 118560603577) := by
    rw [show ((118560603577 / 100000000000) : ℝ) = ((100000000000 / 118560603577) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2601_neg : (170328279 / 500000000) ≤ -Real.log (250000000000 / 351467580897) ∧
    -Real.log (250000000000 / 351467580897) ≤ (340656559 / 1000000000) := by
  have h := checkLog_sound (w := (101467580897 / 601467580897)) (n := 12)
    (lo := (170328279 / 500000000)) (hi := (340656559 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((351467580897 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(351467580897 / 250000000000) = 1/(250000000000 / 351467580897) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2601 : Bounds (170328279 / 500000000) (340656559 / 1000000000) (Real.log (351467580897 / 250000000000)) := by
  have h := reflection_log_2601_neg
  have he : Real.log (351467580897 / 250000000000) = -Real.log (250000000000 / 351467580897) := by
    rw [show ((351467580897 / 250000000000) : ℝ) = ((250000000000 / 351467580897) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2602_neg : (17043121 / 50000000) ≤ -Real.log (100000000000 / 140615976901) ∧
    -Real.log (100000000000 / 140615976901) ≤ (340862421 / 1000000000) := by
  have h := checkLog_sound (w := (40615976901 / 240615976901)) (n := 12)
    (lo := (17043121 / 50000000)) (hi := (340862421 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((140615976901 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(140615976901 / 100000000000) = 1/(100000000000 / 140615976901) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2602 : Bounds (17043121 / 50000000) (340862421 / 1000000000) (Real.log (140615976901 / 100000000000)) := by
  have h := reflection_log_2602_neg
  have he : Real.log (140615976901 / 100000000000) = -Real.log (100000000000 / 140615976901) := by
    rw [show ((140615976901 / 100000000000) : ℝ) = ((100000000000 / 140615976901) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2603_neg : (31212627 / 200000000) ≤ -Real.log (10000 / 11689) ∧
    -Real.log (10000 / 11689) ≤ (4876973 / 31250000) := by
  have h := checkLog_sound (w := (1689 / 21689)) (n := 12)
    (lo := (31212627 / 200000000)) (hi := (4876973 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11689 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11689 / 10000) = 1/(10000 / 11689) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2603 : Bounds (31212627 / 200000000) (4876973 / 31250000) (Real.log (11689 / 10000)) := by
  have h := reflection_log_2603_neg
  have he : Real.log (11689 / 10000) = -Real.log (10000 / 11689) := by
    rw [show ((11689 / 10000) : ℝ) = ((10000 / 11689) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2604_neg : (92502577 / 500000000) ≤ -Real.log (8311 / 10000) ∧
    -Real.log (8311 / 10000) ≤ (37001031 / 200000000) := by
  have h := checkLog_sound (w := (1689 / 18311)) (n := 12)
    (lo := (92502577 / 500000000)) (hi := (37001031 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8311) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8311) = 1/(8311 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2604 : Bounds (-37001031 / 200000000) (-92502577 / 500000000) (Real.log (8311 / 10000)) := by
  have h := reflection_log_2604_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2605_neg : (33777 / 200000000) ≤ -Real.log (10000000 / 10001689) ∧
    -Real.log (10000000 / 10001689) ≤ (84443 / 500000000) := by
  have h := checkLog_sound (w := (1689 / 20001689)) (n := 12)
    (lo := (33777 / 200000000)) (hi := (84443 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001689 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001689 / 10000000) = 1/(10000000 / 10001689) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2605 : Bounds (33777 / 200000000) (84443 / 500000000) (Real.log (10001689 / 10000000)) := by
  have h := reflection_log_2605_neg
  have he : Real.log (10001689 / 10000000) = -Real.log (10000000 / 10001689) := by
    rw [show ((10001689 / 10000000) : ℝ) = ((10000000 / 10001689) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2606_neg : (84457 / 500000000) ≤ -Real.log (9998311 / 10000000) ∧
    -Real.log (9998311 / 10000000) ≤ (33783 / 200000000) := by
  have h := checkLog_sound (w := (1689 / 19998311)) (n := 12)
    (lo := (84457 / 500000000)) (hi := (33783 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998311) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998311) = 1/(9998311 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2606 : Bounds (-33783 / 200000000) (-84457 / 500000000) (Real.log (9998311 / 10000000)) := by
  have h := reflection_log_2606_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2607_neg : (81352311 / 1000000000) ≤ -Real.log (1000000 / 1084753) ∧
    -Real.log (1000000 / 1084753) ≤ (10169039 / 125000000) := by
  have h := checkLog_sound (w := (84753 / 2084753)) (n := 12)
    (lo := (81352311 / 1000000000)) (hi := (10169039 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1084753 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1084753 / 1000000) = 1/(1000000 / 1084753) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2607 : Bounds (81352311 / 1000000000) (10169039 / 125000000) (Real.log (1084753 / 1000000)) := by
  have h := reflection_log_2607_neg
  have he : Real.log (1084753 / 1000000) = -Real.log (1000000 / 1084753) := by
    rw [show ((1084753 / 1000000) : ℝ) = ((1000000 / 1084753) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2608_neg : (11070163 / 125000000) ≤ -Real.log (915247 / 1000000) ∧
    -Real.log (915247 / 1000000) ≤ (17712261 / 200000000) := by
  have h := checkLog_sound (w := (84753 / 1915247)) (n := 12)
    (lo := (11070163 / 125000000)) (hi := (17712261 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 915247) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 915247) = 1/(915247 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2608 : Bounds (-17712261 / 200000000) (-11070163 / 125000000) (Real.log (915247 / 1000000)) := by
  have h := reflection_log_2608_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2609_neg : (81555101 / 1000000000) ≤ -Real.log (1000000 / 1084973) ∧
    -Real.log (1000000 / 1084973) ≤ (40777551 / 500000000) := by
  have h := checkLog_sound (w := (84973 / 2084973)) (n := 12)
    (lo := (81555101 / 1000000000)) (hi := (40777551 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1084973 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1084973 / 1000000) = 1/(1000000 / 1084973) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2609 : Bounds (81555101 / 1000000000) (40777551 / 500000000) (Real.log (1084973 / 1000000)) := by
  have h := reflection_log_2609_neg
  have he : Real.log (1084973 / 1000000) = -Real.log (1000000 / 1084973) := by
    rw [show ((1084973 / 1000000) : ℝ) = ((1000000 / 1084973) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2610_neg : (17760341 / 200000000) ≤ -Real.log (915027 / 1000000) ∧
    -Real.log (915027 / 1000000) ≤ (44400853 / 500000000) := by
  have h := checkLog_sound (w := (84973 / 1915027)) (n := 12)
    (lo := (17760341 / 200000000)) (hi := (44400853 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 915027) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 915027) = 1/(915027 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2610 : Bounds (-44400853 / 500000000) (-17760341 / 200000000) (Real.log (915027 / 1000000)) := by
  have h := reflection_log_2610_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2611_neg : (1811651 / 250000000) ≤ -Real.log (992779589271 / 1000000000000) ∧
    -Real.log (992779589271 / 1000000000000) ≤ (1449321 / 200000000) := by
  have h := checkLog_sound (w := (7220410729 / 1992779589271)) (n := 12)
    (lo := (1811651 / 250000000)) (hi := (1449321 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 992779589271) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 992779589271) = 1/(992779589271 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2611 : Bounds (-1449321 / 200000000) (-1811651 / 250000000) (Real.log (992779589271 / 1000000000000)) := by
  have h := reflection_log_2611_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2612_neg : (7208993 / 1000000000) ≤ -Real.log (992816928991 / 1000000000000) ∧
    -Real.log (992816928991 / 1000000000000) ≤ (3604497 / 500000000) := by
  have h := checkLog_sound (w := (7183071009 / 1992816928991)) (n := 12)
    (lo := (7208993 / 1000000000)) (hi := (3604497 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 992816928991) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 992816928991) = 1/(992816928991 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2612 : Bounds (-3604497 / 500000000) (-7208993 / 1000000000) (Real.log (992816928991 / 1000000000000)) := by
  have h := reflection_log_2612_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2613_neg : (10619601 / 62500000) ≤ -Real.log (100000000000 / 118520246447) ∧
    -Real.log (100000000000 / 118520246447) ≤ (169913617 / 1000000000) := by
  have h := checkLog_sound (w := (18520246447 / 218520246447)) (n := 12)
    (lo := (10619601 / 62500000)) (hi := (169913617 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((118520246447 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(118520246447 / 100000000000) = 1/(100000000000 / 118520246447) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2613 : Bounds (10619601 / 62500000) (169913617 / 1000000000) (Real.log (118520246447 / 100000000000)) := by
  have h := reflection_log_2613_neg
  have he : Real.log (118520246447 / 100000000000) = -Real.log (100000000000 / 118520246447) := by
    rw [show ((118520246447 / 100000000000) : ℝ) = ((100000000000 / 118520246447) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2614_neg : (170356807 / 1000000000) ≤ -Real.log (25000000000 / 29643196321) ∧
    -Real.log (25000000000 / 29643196321) ≤ (21294601 / 125000000) := by
  have h := checkLog_sound (w := (4643196321 / 54643196321)) (n := 12)
    (lo := (170356807 / 1000000000)) (hi := (21294601 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((29643196321 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(29643196321 / 25000000000) = 1/(25000000000 / 29643196321) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2614 : Bounds (170356807 / 1000000000) (21294601 / 125000000) (Real.log (29643196321 / 25000000000)) := by
  have h := reflection_log_2614_neg
  have he : Real.log (29643196321 / 25000000000) = -Real.log (25000000000 / 29643196321) := by
    rw [show ((29643196321 / 25000000000) : ℝ) = ((25000000000 / 29643196321) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2615_neg : (17043121 / 50000000) ≤ -Real.log (62500000000 / 87884985563) ∧
    -Real.log (62500000000 / 87884985563) ≤ (340862421 / 1000000000) := by
  have h := checkLog_sound (w := (25384985563 / 150384985563)) (n := 12)
    (lo := (17043121 / 50000000)) (hi := (340862421 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((87884985563 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(87884985563 / 62500000000) = 1/(62500000000 / 87884985563) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2615 : Bounds (17043121 / 50000000) (340862421 / 1000000000) (Real.log (87884985563 / 62500000000)) := by
  have h := reflection_log_2615_neg
  have he : Real.log (87884985563 / 62500000000) = -Real.log (62500000000 / 87884985563) := by
    rw [show ((87884985563 / 62500000000) : ℝ) = ((62500000000 / 87884985563) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2616_neg : (34106829 / 100000000) ≤ -Real.log (500000000000 / 703224642041) ∧
    -Real.log (500000000000 / 703224642041) ≤ (341068291 / 1000000000) := by
  have h := checkLog_sound (w := (203224642041 / 1203224642041)) (n := 12)
    (lo := (34106829 / 100000000)) (hi := (341068291 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((703224642041 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(703224642041 / 500000000000) = 1/(500000000000 / 703224642041) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2616 : Bounds (34106829 / 100000000) (341068291 / 1000000000) (Real.log (703224642041 / 500000000000)) := by
  have h := reflection_log_2616_neg
  have he : Real.log (703224642041 / 500000000000) = -Real.log (500000000000 / 703224642041) := by
    rw [show ((703224642041 / 500000000000) : ℝ) = ((500000000000 / 703224642041) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2617_neg : (78074341 / 500000000) ≤ -Real.log (1000 / 1169) ∧
    -Real.log (1000 / 1169) ≤ (156148683 / 1000000000) := by
  have h := checkLog_sound (w := (169 / 2169)) (n := 12)
    (lo := (78074341 / 500000000)) (hi := (156148683 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1169 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1169 / 1000) = 1/(1000 / 1169) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2617 : Bounds (78074341 / 500000000) (156148683 / 1000000000) (Real.log (1169 / 1000)) := by
  have h := reflection_log_2617_neg
  have he : Real.log (1169 / 1000) = -Real.log (1000 / 1169) := by
    rw [show ((1169 / 1000) : ℝ) = ((1000 / 1169) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2618_neg : (46281371 / 250000000) ≤ -Real.log (831 / 1000) ∧
    -Real.log (831 / 1000) ≤ (37025097 / 200000000) := by
  have h := checkLog_sound (w := (169 / 1831)) (n := 12)
    (lo := (46281371 / 250000000)) (hi := (37025097 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 831) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 831) = 1/(831 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2618 : Bounds (-37025097 / 200000000) (-46281371 / 250000000) (Real.log (831 / 1000)) := by
  have h := reflection_log_2618_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2619_neg : (33797 / 200000000) ≤ -Real.log (1000000 / 1000169) ∧
    -Real.log (1000000 / 1000169) ≤ (84493 / 500000000) := by
  have h := checkLog_sound (w := (169 / 2000169)) (n := 12)
    (lo := (33797 / 200000000)) (hi := (84493 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000169 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000169 / 1000000) = 1/(1000000 / 1000169) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2619 : Bounds (33797 / 200000000) (84493 / 500000000) (Real.log (1000169 / 1000000)) := by
  have h := reflection_log_2619_neg
  have he : Real.log (1000169 / 1000000) = -Real.log (1000000 / 1000169) := by
    rw [show ((1000169 / 1000000) : ℝ) = ((1000000 / 1000169) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2620_neg : (84507 / 500000000) ≤ -Real.log (999831 / 1000000) ∧
    -Real.log (999831 / 1000000) ≤ (33803 / 200000000) := by
  have h := checkLog_sound (w := (169 / 1999831)) (n := 12)
    (lo := (84507 / 500000000)) (hi := (33803 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999831) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999831) = 1/(999831 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2620 : Bounds (-33803 / 200000000) (-84507 / 500000000) (Real.log (999831 / 1000000)) := by
  have h := reflection_log_2620_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2621_neg : (3255973 / 40000000) ≤ -Real.log (250000 / 271201) ∧
    -Real.log (250000 / 271201) ≤ (40699663 / 500000000) := by
  have h := checkLog_sound (w := (21201 / 521201)) (n := 12)
    (lo := (3255973 / 40000000)) (hi := (40699663 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((271201 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(271201 / 250000) = 1/(250000 / 271201) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2621 : Bounds (3255973 / 40000000) (40699663 / 500000000) (Real.log (271201 / 250000)) := by
  have h := reflection_log_2621_neg
  have he : Real.log (271201 / 250000) = -Real.log (250000 / 271201) := by
    rw [show ((271201 / 250000) : ℝ) = ((250000 / 271201) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2622_neg : (22154257 / 250000000) ≤ -Real.log (228799 / 250000) ∧
    -Real.log (228799 / 250000) ≤ (88617029 / 1000000000) := by
  have h := checkLog_sound (w := (21201 / 478799)) (n := 12)
    (lo := (22154257 / 250000000)) (hi := (88617029 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 228799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 228799) = 1/(228799 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2622 : Bounds (-88617029 / 1000000000) (-22154257 / 250000000) (Real.log (228799 / 250000)) := by
  have h := reflection_log_2622_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2623_neg : (2550037 / 31250000) ≤ -Real.log (1000000 / 1085023) ∧
    -Real.log (1000000 / 1085023) ≤ (16320237 / 200000000) := by
  have h := checkLog_sound (w := (85023 / 2085023)) (n := 12)
    (lo := (2550037 / 31250000)) (hi := (16320237 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1085023 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1085023 / 1000000) = 1/(1000000 / 1085023) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2623 : Bounds (2550037 / 31250000) (16320237 / 200000000) (Real.log (1085023 / 1000000)) := by
  have h := reflection_log_2623_neg
  have he : Real.log (1085023 / 1000000) = -Real.log (1000000 / 1085023) := by
    rw [show ((1085023 / 1000000) : ℝ) = ((1000000 / 1085023) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily
