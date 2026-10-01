import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0076
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

theorem reflection_log_1_neg : (8449367 / 12500000) ≤ -Real.log (25600 / 50327) ∧
    -Real.log (25600 / 50327) ≤ (675949361 / 1000000000) := by
  have h := checkLog_sound (w := (24727 / 75927)) (n := 12)
    (lo := (8449367 / 12500000)) (hi := (675949361 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50327 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50327 / 25600) = 1/(25600 / 50327) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (8449367 / 12500000) (675949361 / 1000000000) (Real.log (50327 / 25600)) := by
  have h := reflection_log_1_neg
  have he : Real.log (50327 / 25600) = -Real.log (25600 / 50327) := by
    rw [show ((50327 / 25600) : ℝ) = ((25600 / 50327) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (422301509 / 125000000) ≤ -Real.log (873 / 25600) ∧
    -Real.log (873 / 25600) ≤ (3378412077 / 1000000000) := by
  have h := checkLog_sound (w := (727 / 2473)) (n := 12)
    (lo := (75727919 / 125000000)) (hi := (605823353 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 873) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1600 / 873) = 1/(873 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-3378412077 / 1000000000) (-422301509 / 125000000) (Real.log (873 / 25600)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (675760577 / 1000000000) ≤ -Real.log (10240 / 20127) ∧
    -Real.log (10240 / 20127) ≤ (337880289 / 500000000) := by
  have h := checkLog_sound (w := (9887 / 30367)) (n := 12)
    (lo := (675760577 / 1000000000)) (hi := (337880289 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20127 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20127 / 10240) = 1/(10240 / 20127) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (675760577 / 1000000000) (337880289 / 500000000) (Real.log (20127 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (20127 / 10240) = -Real.log (10240 / 20127) := by
    rw [show ((20127 / 10240) : ℝ) = ((10240 / 20127) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (3367588839 / 1000000000) ≤ -Real.log (353 / 10240) ∧
    -Real.log (353 / 10240) ≤ (841897211 / 250000000) := by
  have h := checkLog_sound (w := (287 / 993)) (n := 12)
    (lo := (595000119 / 1000000000)) (hi := (14875003 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 353) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(640 / 353) = 1/(353 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-841897211 / 250000000) (-3367588839 / 1000000000) (Real.log (353 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (658450593 / 1000000000) ≤ -Real.log (12800 / 24727) ∧
    -Real.log (12800 / 24727) ≤ (329225297 / 500000000) := by
  have h := checkLog_sound (w := (11927 / 37527)) (n := 12)
    (lo := (658450593 / 1000000000)) (hi := (329225297 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24727 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24727 / 12800) = 1/(12800 / 24727) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (658450593 / 1000000000) (329225297 / 500000000) (Real.log (24727 / 12800)) := by
  have h := reflection_log_5_neg
  have he : Real.log (24727 / 12800) = -Real.log (12800 / 24727) := by
    rw [show ((24727 / 12800) : ℝ) = ((12800 / 24727) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (671316223 / 250000000) ≤ -Real.log (873 / 12800) ∧
    -Real.log (873 / 12800) ≤ (5244658 / 1953125) := by
  have h := checkLog_sound (w := (727 / 2473)) (n := 12)
    (lo := (75727919 / 125000000)) (hi := (605823353 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 873) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1600 / 873) = 1/(873 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-5244658 / 1953125) (-671316223 / 250000000) (Real.log (873 / 12800)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (658066323 / 1000000000) ≤ -Real.log (5120 / 9887) ∧
    -Real.log (5120 / 9887) ≤ (164516581 / 250000000) := by
  have h := checkLog_sound (w := (4767 / 15007)) (n := 12)
    (lo := (658066323 / 1000000000)) (hi := (164516581 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9887 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(9887 / 5120) = 1/(5120 / 9887) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (658066323 / 1000000000) (164516581 / 250000000) (Real.log (9887 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (9887 / 5120) = -Real.log (5120 / 9887) := by
    rw [show ((9887 / 5120) : ℝ) = ((5120 / 9887) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (2674441659 / 1000000000) ≤ -Real.log (353 / 5120) ∧
    -Real.log (353 / 5120) ≤ (2674441663 / 1000000000) := by
  have h := checkLog_sound (w := (287 / 993)) (n := 12)
    (lo := (595000119 / 1000000000)) (hi := (14875003 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 353) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(640 / 353) = 1/(353 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-2674441663 / 1000000000) (-2674441659 / 1000000000) (Real.log (353 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (678733297 / 1000000000) ≤ -Real.log (1000000 / 1971379) ∧
    -Real.log (1000000 / 1971379) ≤ (339366649 / 500000000) := by
  have h := checkLog_sound (w := (971379 / 2971379)) (n := 12)
    (lo := (678733297 / 1000000000)) (hi := (339366649 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1971379 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1971379 / 1000000) = 1/(1000000 / 1971379) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (678733297 / 1000000000) (339366649 / 500000000) (Real.log (1971379 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1971379 / 1000000) = -Real.log (1000000 / 1971379) := by
    rw [show ((1971379 / 1000000) : ℝ) = ((1000000 / 1971379) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (1776807281 / 500000000) ≤ -Real.log (28621 / 1000000) ∧
    -Real.log (28621 / 1000000) ≤ (444201821 / 125000000) := by
  have h := checkLog_sound (w := (2629 / 59871)) (n := 12)
    (lo := (43939331 / 500000000)) (hi := (87878663 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 28621) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 28621) = 1/(28621 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-444201821 / 125000000) (-1776807281 / 500000000) (Real.log (28621 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (678881913 / 1000000000) ≤ -Real.log (125000 / 246459) ∧
    -Real.log (125000 / 246459) ≤ (339440957 / 500000000) := by
  have h := checkLog_sound (w := (121459 / 371459)) (n := 12)
    (lo := (678881913 / 1000000000)) (hi := (339440957 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((246459 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(246459 / 125000) = 1/(125000 / 246459) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (678881913 / 1000000000) (339440957 / 500000000) (Real.log (246459 / 125000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (246459 / 125000) = -Real.log (125000 / 246459) := by
    rw [show ((246459 / 125000) : ℝ) = ((125000 / 246459) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (3563904561 / 1000000000) ≤ -Real.log (3541 / 125000) ∧
    -Real.log (3541 / 125000) ≤ (3563904567 / 1000000000) := by
  have h := checkLog_sound (w := (1461 / 29789)) (n := 12)
    (lo := (98168661 / 1000000000)) (hi := (49084331 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 14164) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 14164) = 1/(3541 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-3563904567 / 1000000000) (-3563904561 / 1000000000) (Real.log (3541 / 125000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (339313891 / 500000000) ≤ -Real.log (1000000 / 1971171) ∧
    -Real.log (1000000 / 1971171) ≤ (678627783 / 1000000000) := by
  have h := checkLog_sound (w := (971171 / 2971171)) (n := 12)
    (lo := (339313891 / 500000000)) (hi := (678627783 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1971171 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1971171 / 1000000) = 1/(1000000 / 1971171) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (339313891 / 500000000) (678627783 / 1000000000) (Real.log (1971171 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1971171 / 1000000) = -Real.log (1000000 / 1971171) := by
    rw [show ((1971171 / 1000000) : ℝ) = ((1000000 / 1971171) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (3546373451 / 1000000000) ≤ -Real.log (28829 / 1000000) ∧
    -Real.log (28829 / 1000000) ≤ (3546373457 / 1000000000) := by
  have h := checkLog_sound (w := (2421 / 60079)) (n := 12)
    (lo := (80637551 / 1000000000)) (hi := (5039847 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 28829) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 28829) = 1/(28829 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-3546373457 / 1000000000) (-3546373451 / 1000000000) (Real.log (28829 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (678779457 / 1000000000) ≤ -Real.log (100000 / 197147) ∧
    -Real.log (100000 / 197147) ≤ (339389729 / 500000000) := by
  have h := checkLog_sound (w := (97147 / 297147)) (n := 12)
    (lo := (678779457 / 1000000000)) (hi := (339389729 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((197147 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(197147 / 100000) = 1/(100000 / 197147) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (678779457 / 1000000000) (339389729 / 500000000) (Real.log (197147 / 100000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (197147 / 100000) = -Real.log (100000 / 197147) := by
    rw [show ((197147 / 100000) : ℝ) = ((100000 / 197147) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (355679911 / 100000000) ≤ -Real.log (2853 / 100000) ∧
    -Real.log (2853 / 100000) ≤ (889199779 / 250000000) := by
  have h := checkLog_sound (w := (136 / 2989)) (n := 12)
    (lo := (9106321 / 100000000)) (hi := (91063211 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3125 / 2853) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3125 / 2853) = 1/(2853 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-889199779 / 250000000) (-355679911 / 100000000) (Real.log (2853 / 100000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (4232347859 / 1000000000) ≤ -Real.log (100000000000 / 6887876035079) ∧
    -Real.log (100000000000 / 6887876035079) ≤ (2116173933 / 500000000) := by
  have h := checkLog_sound (w := (487876035079 / 13287876035079)) (n := 12)
    (lo := (73464779 / 1000000000)) (hi := (3673239 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6887876035079 / 6400000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(6887876035079 / 6400000000000) = 1/(100000000000 / 6887876035079) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (4232347859 / 1000000000) (2116173933 / 500000000) (Real.log (6887876035079 / 100000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (6887876035079 / 100000000000) = -Real.log (100000000000 / 6887876035079) := by
    rw [show ((6887876035079 / 100000000000) : ℝ) = ((100000000000 / 6887876035079) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (2121393237 / 500000000) ≤ -Real.log (50000000000 / 3480076249647) ∧
    -Real.log (50000000000 / 3480076249647) ≤ (4242786481 / 1000000000) := by
  have h := checkLog_sound (w := (280076249647 / 6680076249647)) (n := 12)
    (lo := (41951697 / 500000000)) (hi := (16780679 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3480076249647 / 3200000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(3480076249647 / 3200000000000) = 1/(50000000000 / 3480076249647) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (2121393237 / 500000000) (4242786481 / 1000000000) (Real.log (3480076249647 / 50000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (3480076249647 / 50000000000) = -Real.log (50000000000 / 3480076249647) := by
    rw [show ((3480076249647 / 50000000000) : ℝ) = ((50000000000 / 3480076249647) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (4225001233 / 1000000000) ≤ -Real.log (500000000000 / 34187294044191) ∧
    -Real.log (500000000000 / 34187294044191) ≤ (105625031 / 25000000) := by
  have h := checkLog_sound (w := (2187294044191 / 66187294044191)) (n := 12)
    (lo := (66118153 / 1000000000)) (hi := (33059077 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((34187294044191 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(34187294044191 / 32000000000000) = 1/(500000000000 / 34187294044191) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (4225001233 / 1000000000) (105625031 / 25000000) (Real.log (34187294044191 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (34187294044191 / 500000000000) = -Real.log (500000000000 / 34187294044191) := by
    rw [show ((34187294044191 / 500000000000) : ℝ) = ((500000000000 / 34187294044191) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (4235578567 / 1000000000) ≤ -Real.log (500000000000 / 34550823694357) ∧
    -Real.log (500000000000 / 34550823694357) ≤ (2117789287 / 500000000) := by
  have h := checkLog_sound (w := (2550823694357 / 66550823694357)) (n := 12)
    (lo := (76695487 / 1000000000)) (hi := (1198367 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((34550823694357 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(34550823694357 / 32000000000000) = 1/(500000000000 / 34550823694357) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (4235578567 / 1000000000) (2117789287 / 500000000) (Real.log (34550823694357 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (34550823694357 / 500000000000) = -Real.log (500000000000 / 34550823694357) := by
    rw [show ((34550823694357 / 500000000000) : ℝ) = ((500000000000 / 34550823694357) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0076
