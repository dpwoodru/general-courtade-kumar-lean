import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0354
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

theorem reflection_log_1_neg : (5279937 / 25000000) ≤ -Real.log (1280 / 1581) ∧
    -Real.log (1280 / 1581) ≤ (211197481 / 1000000000) := by
  have h := checkLog_sound (w := (301 / 2861)) (n := 12)
    (lo := (5279937 / 25000000)) (hi := (211197481 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1581 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1581 / 1280) = 1/(1280 / 1581) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (5279937 / 25000000) (211197481 / 1000000000) (Real.log (1581 / 1280)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1581 / 1280) = -Real.log (1280 / 1581) := by
    rw [show ((1581 / 1280) : ℝ) = ((1280 / 1581) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (134041857 / 500000000) ≤ -Real.log (979 / 1280) ∧
    -Real.log (979 / 1280) ≤ (53616743 / 200000000) := by
  have h := checkLog_sound (w := (301 / 2259)) (n := 12)
    (lo := (134041857 / 500000000)) (hi := (53616743 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 979) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 979) = 1/(979 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-53616743 / 200000000) (-134041857 / 500000000) (Real.log (979 / 1280)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (10548013 / 50000000) ≤ -Real.log (2048 / 2529) ∧
    -Real.log (2048 / 2529) ≤ (210960261 / 1000000000) := by
  have h := checkLog_sound (w := (481 / 4577)) (n := 12)
    (lo := (10548013 / 50000000)) (hi := (210960261 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2529 / 2048) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2529 / 2048) = 1/(2048 / 2529) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (10548013 / 50000000) (210960261 / 1000000000) (Real.log (2529 / 2048)) := by
  have h := reflection_log_3_neg
  have he : Real.log (2529 / 2048) = -Real.log (2048 / 2529) := by
    rw [show ((2529 / 2048) : ℝ) = ((2048 / 2529) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (267700743 / 1000000000) ≤ -Real.log (1567 / 2048) ∧
    -Real.log (1567 / 2048) ≤ (33462593 / 125000000) := by
  have h := checkLog_sound (w := (481 / 3615)) (n := 12)
    (lo := (267700743 / 1000000000)) (hi := (33462593 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2048 / 1567) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2048 / 1567) = 1/(1567 / 2048) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-33462593 / 125000000) (-267700743 / 1000000000) (Real.log (1567 / 2048)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (385474963 / 1000000000) ≤ -Real.log (640 / 941) ∧
    -Real.log (640 / 941) ≤ (96368741 / 250000000) := by
  have h := checkLog_sound (w := (301 / 1581)) (n := 12)
    (lo := (385474963 / 1000000000)) (hi := (96368741 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((941 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(941 / 640) = 1/(640 / 941) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (385474963 / 1000000000) (96368741 / 250000000) (Real.log (941 / 640)) := by
  have h := reflection_log_5_neg
  have he : Real.log (941 / 640) = -Real.log (640 / 941) := by
    rw [show ((941 / 640) : ℝ) = ((640 / 941) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (158867017 / 250000000) ≤ -Real.log (339 / 640) ∧
    -Real.log (339 / 640) ≤ (635468069 / 1000000000) := by
  have h := checkLog_sound (w := (301 / 979)) (n := 12)
    (lo := (158867017 / 250000000)) (hi := (635468069 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 339) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 339) = 1/(339 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-635468069 / 1000000000) (-158867017 / 250000000) (Real.log (339 / 640)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (385076371 / 1000000000) ≤ -Real.log (1024 / 1505) ∧
    -Real.log (1024 / 1505) ≤ (96269093 / 250000000) := by
  have h := checkLog_sound (w := (481 / 2529)) (n := 12)
    (lo := (385076371 / 1000000000)) (hi := (96269093 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1505 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1505 / 1024) = 1/(1024 / 1505) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (385076371 / 1000000000) (96269093 / 250000000) (Real.log (1505 / 1024)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1505 / 1024) = -Real.log (1024 / 1505) := by
    rw [show ((1505 / 1024) : ℝ) = ((1024 / 1505) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (126872497 / 200000000) ≤ -Real.log (543 / 1024) ∧
    -Real.log (543 / 1024) ≤ (317181243 / 500000000) := by
  have h := checkLog_sound (w := (481 / 1567)) (n := 12)
    (lo := (126872497 / 200000000)) (hi := (317181243 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 543) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 543) = 1/(543 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-317181243 / 500000000) (-126872497 / 200000000) (Real.log (543 / 1024)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (289319231 / 1000000000) ≤ -Real.log (500000 / 667759) ∧
    -Real.log (500000 / 667759) ≤ (4520613 / 15625000) := by
  have h := checkLog_sound (w := (167759 / 1167759)) (n := 12)
    (lo := (289319231 / 1000000000)) (hi := (4520613 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((667759 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(667759 / 500000) = 1/(500000 / 667759) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (289319231 / 1000000000) (4520613 / 15625000) (Real.log (667759 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (667759 / 500000) = -Real.log (500000 / 667759) := by
    rw [show ((667759 / 500000) : ℝ) = ((500000 / 667759) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (408747489 / 1000000000) ≤ -Real.log (332241 / 500000) ∧
    -Real.log (332241 / 500000) ≤ (40874749 / 100000000) := by
  have h := checkLog_sound (w := (167759 / 832241)) (n := 12)
    (lo := (408747489 / 1000000000)) (hi := (40874749 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 332241) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 332241) = 1/(332241 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-40874749 / 100000000) (-408747489 / 1000000000) (Real.log (332241 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (57927931 / 200000000) ≤ -Real.log (500000 / 667973) ∧
    -Real.log (500000 / 667973) ≤ (36204957 / 125000000) := by
  have h := checkLog_sound (w := (167973 / 1167973)) (n := 12)
    (lo := (57927931 / 200000000)) (hi := (36204957 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((667973 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(667973 / 500000) = 1/(500000 / 667973) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (57927931 / 200000000) (36204957 / 125000000) (Real.log (667973 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (667973 / 500000) = -Real.log (500000 / 667973) := by
    rw [show ((667973 / 500000) : ℝ) = ((500000 / 667973) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (409391807 / 1000000000) ≤ -Real.log (332027 / 500000) ∧
    -Real.log (332027 / 500000) ≤ (6396747 / 15625000) := by
  have h := checkLog_sound (w := (167973 / 832027)) (n := 12)
    (lo := (409391807 / 1000000000)) (hi := (6396747 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 332027) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 332027) = 1/(332027 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-6396747 / 15625000) (-409391807 / 1000000000) (Real.log (332027 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (109517963 / 500000000) ≤ -Real.log (250000 / 311219) ∧
    -Real.log (250000 / 311219) ≤ (219035927 / 1000000000) := by
  have h := checkLog_sound (w := (61219 / 561219)) (n := 12)
    (lo := (109517963 / 500000000)) (hi := (219035927 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((311219 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(311219 / 250000) = 1/(250000 / 311219) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (109517963 / 500000000) (219035927 / 1000000000) (Real.log (311219 / 250000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (311219 / 250000) = -Real.log (250000 / 311219) := by
    rw [show ((311219 / 250000) : ℝ) = ((250000 / 311219) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (35109163 / 125000000) ≤ -Real.log (188781 / 250000) ∧
    -Real.log (188781 / 250000) ≤ (56174661 / 200000000) := by
  have h := checkLog_sound (w := (61219 / 438781)) (n := 12)
    (lo := (35109163 / 125000000)) (hi := (56174661 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 188781) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 188781) = 1/(188781 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-56174661 / 200000000) (-35109163 / 125000000) (Real.log (188781 / 250000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (219303387 / 1000000000) ≤ -Real.log (1000000 / 1245209) ∧
    -Real.log (1000000 / 1245209) ≤ (54825847 / 250000000) := by
  have h := checkLog_sound (w := (245209 / 2245209)) (n := 12)
    (lo := (219303387 / 1000000000)) (hi := (54825847 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1245209 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1245209 / 1000000) = 1/(1000000 / 1245209) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (219303387 / 1000000000) (54825847 / 250000000) (Real.log (1245209 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1245209 / 1000000) = -Real.log (1000000 / 1245209) := by
    rw [show ((1245209 / 1000000) : ℝ) = ((1000000 / 1245209) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (281314389 / 1000000000) ≤ -Real.log (754791 / 1000000) ∧
    -Real.log (754791 / 1000000) ≤ (28131439 / 100000000) := by
  have h := checkLog_sound (w := (245209 / 1754791)) (n := 12)
    (lo := (281314389 / 1000000000)) (hi := (28131439 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 754791) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 754791) = 1/(754791 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-28131439 / 100000000) (-281314389 / 1000000000) (Real.log (754791 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (4362917 / 6250000) ≤ -Real.log (500000000000 / 1004931661053) ∧
    -Real.log (500000000000 / 1004931661053) ≤ (349033361 / 500000000) := by
  have h := checkLog_sound (w := (4931661053 / 2004931661053)) (n := 12)
    (lo := (245977 / 50000000)) (hi := (4919541 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1004931661053 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1004931661053 / 1000000000000) = 1/(500000000000 / 1004931661053) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (4362917 / 6250000) (349033361 / 500000000) (Real.log (1004931661053 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1004931661053 / 500000000000) = -Real.log (500000000000 / 1004931661053) := by
    rw [show ((1004931661053 / 500000000000) : ℝ) = ((500000000000 / 1004931661053) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (349515731 / 500000000) ≤ -Real.log (500000000000 / 1005901628483) ∧
    -Real.log (500000000000 / 1005901628483) ≤ (87378933 / 125000000) := by
  have h := checkLog_sound (w := (5901628483 / 2005901628483)) (n := 12)
    (lo := (2942141 / 500000000)) (hi := (5884283 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1005901628483 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1005901628483 / 1000000000000) = 1/(500000000000 / 1005901628483) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (349515731 / 500000000) (87378933 / 125000000) (Real.log (1005901628483 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1005901628483 / 500000000000) = -Real.log (500000000000 / 1005901628483) := by
    rw [show ((1005901628483 / 500000000000) : ℝ) = ((500000000000 / 1005901628483) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (499909231 / 1000000000) ≤ -Real.log (500000000000 / 824285812661) ∧
    -Real.log (500000000000 / 824285812661) ≤ (31244327 / 62500000) := by
  have h := checkLog_sound (w := (324285812661 / 1324285812661)) (n := 12)
    (lo := (499909231 / 1000000000)) (hi := (31244327 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((824285812661 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(824285812661 / 500000000000) = 1/(500000000000 / 824285812661) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (499909231 / 1000000000) (31244327 / 62500000) (Real.log (824285812661 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (824285812661 / 500000000000) = -Real.log (500000000000 / 824285812661) := by
    rw [show ((824285812661 / 500000000000) : ℝ) = ((500000000000 / 824285812661) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (31288611 / 62500000) ≤ -Real.log (500000000000 / 824870063369) ∧
    -Real.log (500000000000 / 824870063369) ≤ (500617777 / 1000000000) := by
  have h := checkLog_sound (w := (324870063369 / 1324870063369)) (n := 12)
    (lo := (31288611 / 62500000)) (hi := (500617777 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((824870063369 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(824870063369 / 500000000000) = 1/(500000000000 / 824870063369) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (31288611 / 62500000) (500617777 / 1000000000) (Real.log (824870063369 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (824870063369 / 500000000000) = -Real.log (500000000000 / 824870063369) := by
    rw [show ((824870063369 / 500000000000) : ℝ) = ((500000000000 / 824870063369) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0354
