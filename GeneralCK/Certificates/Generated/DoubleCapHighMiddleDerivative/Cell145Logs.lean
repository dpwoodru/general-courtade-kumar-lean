import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell145
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed GeneralCK.Reflection

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

theorem reflection_log_1_neg : (72335213 / 250000000) ≤ -Real.log (2560 / 3419) ∧
    -Real.log (2560 / 3419) ≤ (289340853 / 1000000000) := by
  have h := checkLog_sound (w := (859 / 5979)) (n := 12)
    (lo := (72335213 / 250000000)) (hi := (289340853 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3419 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3419 / 2560) = 1/(2560 / 3419) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (72335213 / 250000000) (289340853 / 1000000000) (Real.log (3419 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3419 / 2560) = -Real.log (2560 / 3419) := by
    rw [show ((3419 / 2560) : ℝ) = ((2560 / 3419) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (81758189 / 200000000) ≤ -Real.log (1701 / 2560) ∧
    -Real.log (1701 / 2560) ≤ (204395473 / 500000000) := by
  have h := checkLog_sound (w := (859 / 4261)) (n := 12)
    (lo := (81758189 / 200000000)) (hi := (204395473 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1701) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1701) = 1/(1701 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-204395473 / 500000000) (-81758189 / 200000000) (Real.log (1701 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (288902031 / 1000000000) ≤ -Real.log (1024 / 1367) ∧
    -Real.log (1024 / 1367) ≤ (18056377 / 62500000) := by
  have h := checkLog_sound (w := (343 / 2391)) (n := 12)
    (lo := (288902031 / 1000000000)) (hi := (18056377 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1367 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1367 / 1024) = 1/(1024 / 1367) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (288902031 / 1000000000) (18056377 / 62500000) (Real.log (1367 / 1024)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1367 / 1024) = -Real.log (1024 / 1367) := by
    rw [show ((1367 / 1024) : ℝ) = ((1024 / 1367) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (407909499 / 1000000000) ≤ -Real.log (681 / 1024) ∧
    -Real.log (681 / 1024) ≤ (815819 / 2000000) := by
  have h := checkLog_sound (w := (343 / 1705)) (n := 12)
    (lo := (407909499 / 1000000000)) (hi := (815819 / 2000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 681) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 681) = 1/(681 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-815819 / 2000000) (-407909499 / 1000000000) (Real.log (681 / 1024)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (21350929 / 100000000) ≤ -Real.log (200000 / 247603) ∧
    -Real.log (200000 / 247603) ≤ (213509291 / 1000000000) := by
  have h := checkLog_sound (w := (47603 / 447603)) (n := 12)
    (lo := (21350929 / 100000000)) (hi := (213509291 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((247603 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(247603 / 200000) = 1/(200000 / 247603) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (21350929 / 100000000) (213509291 / 1000000000) (Real.log (247603 / 200000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (247603 / 200000) = -Real.log (200000 / 247603) := by
    rw [show ((247603 / 200000) : ℝ) = ((200000 / 247603) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (33978551 / 125000000) ≤ -Real.log (152397 / 200000) ∧
    -Real.log (152397 / 200000) ≤ (271828409 / 1000000000) := by
  have h := checkLog_sound (w := (47603 / 352397)) (n := 12)
    (lo := (33978551 / 125000000)) (hi := (271828409 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 152397) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 152397) = 1/(152397 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-271828409 / 1000000000) (-33978551 / 125000000) (Real.log (152397 / 200000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (53462727 / 250000000) ≤ -Real.log (500000 / 619219) ∧
    -Real.log (500000 / 619219) ≤ (213850909 / 1000000000) := by
  have h := checkLog_sound (w := (119219 / 1119219)) (n := 12)
    (lo := (53462727 / 250000000)) (hi := (213850909 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((619219 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(619219 / 500000) = 1/(500000 / 619219) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (53462727 / 250000000) (213850909 / 1000000000) (Real.log (619219 / 500000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (619219 / 500000) = -Real.log (500000 / 619219) := by
    rw [show ((619219 / 500000) : ℝ) = ((500000 / 619219) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (272383691 / 1000000000) ≤ -Real.log (380781 / 500000) ∧
    -Real.log (380781 / 500000) ≤ (68095923 / 250000000) := by
  have h := checkLog_sound (w := (119219 / 880781)) (n := 12)
    (lo := (272383691 / 1000000000)) (hi := (68095923 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 380781) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 380781) = 1/(380781 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-68095923 / 250000000) (-272383691 / 1000000000) (Real.log (380781 / 500000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (78922637 / 500000000) ≤ -Real.log (200000 / 234197) ∧
    -Real.log (200000 / 234197) ≤ (6313811 / 40000000) := by
  have h := checkLog_sound (w := (34197 / 434197)) (n := 12)
    (lo := (78922637 / 500000000)) (hi := (6313811 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((234197 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(234197 / 200000) = 1/(200000 / 234197) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (78922637 / 500000000) (6313811 / 40000000) (Real.log (234197 / 200000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (234197 / 200000) = -Real.log (200000 / 234197) := by
    rw [show ((234197 / 200000) : ℝ) = ((200000 / 234197) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (187517029 / 1000000000) ≤ -Real.log (165803 / 200000) ∧
    -Real.log (165803 / 200000) ≤ (18751703 / 100000000) := by
  have h := checkLog_sound (w := (34197 / 365803)) (n := 12)
    (lo := (187517029 / 1000000000)) (hi := (18751703 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 165803) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 165803) = 1/(165803 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-18751703 / 100000000) (-187517029 / 1000000000) (Real.log (165803 / 200000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (31622507 / 200000000) ≤ -Real.log (500000 / 585649) ∧
    -Real.log (500000 / 585649) ≤ (19764067 / 125000000) := by
  have h := checkLog_sound (w := (85649 / 1085649)) (n := 12)
    (lo := (31622507 / 200000000)) (hi := (19764067 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((585649 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(585649 / 500000) = 1/(500000 / 585649) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (31622507 / 200000000) (19764067 / 125000000) (Real.log (585649 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (585649 / 500000) = -Real.log (500000 / 585649) := by
    rw [show ((585649 / 500000) : ℝ) = ((500000 / 585649) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (187894657 / 1000000000) ≤ -Real.log (414351 / 500000) ∧
    -Real.log (414351 / 500000) ≤ (93947329 / 500000000) := by
  have h := checkLog_sound (w := (85649 / 914351)) (n := 12)
    (lo := (187894657 / 1000000000)) (hi := (93947329 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 414351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 414351) = 1/(414351 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-93947329 / 500000000) (-187894657 / 1000000000) (Real.log (414351 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (69681153 / 100000000) ≤ -Real.log (500000000000 / 1003671071953) ∧
    -Real.log (500000000000 / 1003671071953) ≤ (174202883 / 250000000) := by
  have h := checkLog_sound (w := (3671071953 / 2003671071953)) (n := 12)
    (lo := (73287 / 20000000)) (hi := (3664351 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1003671071953 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1003671071953 / 1000000000000) = 1/(500000000000 / 1003671071953) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (69681153 / 100000000) (174202883 / 250000000) (Real.log (1003671071953 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1003671071953 / 500000000000) = -Real.log (500000000000 / 1003671071953) := by
    rw [show ((1003671071953 / 500000000000) : ℝ) = ((500000000000 / 1003671071953) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (174532949 / 250000000) ≤ -Real.log (500000000000 / 1004997060553) ∧
    -Real.log (500000000000 / 1004997060553) ≤ (349065899 / 500000000) := by
  have h := checkLog_sound (w := (4997060553 / 2004997060553)) (n := 12)
    (lo := (623077 / 125000000)) (hi := (4984617 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1004997060553 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1004997060553 / 1000000000000) = 1/(500000000000 / 1004997060553) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (174532949 / 250000000) (349065899 / 500000000) (Real.log (1004997060553 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (1004997060553 / 500000000000) = -Real.log (500000000000 / 1004997060553) := by
    rw [show ((1004997060553 / 500000000000) : ℝ) = ((500000000000 / 1004997060553) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (485337699 / 1000000000) ≤ -Real.log (250000000000 / 406180895949) ∧
    -Real.log (250000000000 / 406180895949) ≤ (4853377 / 10000000) := by
  have h := checkLog_sound (w := (156180895949 / 656180895949)) (n := 12)
    (lo := (485337699 / 1000000000)) (hi := (4853377 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((406180895949 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(406180895949 / 250000000000) = 1/(250000000000 / 406180895949) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (485337699 / 1000000000) (4853377 / 10000000) (Real.log (406180895949 / 250000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (406180895949 / 250000000000) = -Real.log (250000000000 / 406180895949) := by
    rw [show ((406180895949 / 250000000000) : ℝ) = ((250000000000 / 406180895949) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (486234599 / 1000000000) ≤ -Real.log (500000000000 / 813090726691) ∧
    -Real.log (500000000000 / 813090726691) ≤ (2431173 / 5000000) := by
  have h := checkLog_sound (w := (313090726691 / 1313090726691)) (n := 12)
    (lo := (486234599 / 1000000000)) (hi := (2431173 / 5000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((813090726691 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(813090726691 / 500000000000) = 1/(500000000000 / 813090726691) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (486234599 / 1000000000) (2431173 / 5000000) (Real.log (813090726691 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (813090726691 / 500000000000) = -Real.log (500000000000 / 813090726691) := by
    rw [show ((813090726691 / 500000000000) : ℝ) = ((500000000000 / 813090726691) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (2698143 / 7812500) ≤ -Real.log (250000000000 / 353125395801) ∧
    -Real.log (250000000000 / 353125395801) ≤ (69072461 / 200000000) := by
  have h := checkLog_sound (w := (103125395801 / 603125395801)) (n := 12)
    (lo := (2698143 / 7812500)) (hi := (69072461 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((353125395801 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(353125395801 / 250000000000) = 1/(250000000000 / 353125395801) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (2698143 / 7812500) (69072461 / 200000000) (Real.log (353125395801 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (353125395801 / 250000000000) = -Real.log (250000000000 / 353125395801) := by
    rw [show ((353125395801 / 250000000000) : ℝ) = ((250000000000 / 353125395801) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (346007193 / 1000000000) ≤ -Real.log (250000000000 / 353353195721) ∧
    -Real.log (250000000000 / 353353195721) ≤ (173003597 / 500000000) := by
  have h := checkLog_sound (w := (103353195721 / 603353195721)) (n := 12)
    (lo := (346007193 / 1000000000)) (hi := (173003597 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((353353195721 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(353353195721 / 250000000000) = 1/(250000000000 / 353353195721) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (346007193 / 1000000000) (173003597 / 500000000) (Real.log (353353195721 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (353353195721 / 250000000000) = -Real.log (250000000000 / 353353195721) := by
    rw [show ((353353195721 / 250000000000) : ℝ) = ((250000000000 / 353353195721) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (14891061 / 500000000) ≤ -Real.log (242664248799 / 250000000000) ∧
    -Real.log (242664248799 / 250000000000) ≤ (29782123 / 1000000000) := by
  have h := checkLog_sound (w := (7335751201 / 492664248799)) (n := 12)
    (lo := (14891061 / 500000000)) (hi := (29782123 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 242664248799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 242664248799) = 1/(242664248799 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-29782123 / 1000000000) (-14891061 / 500000000) (Real.log (242664248799 / 250000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (14835877 / 500000000) ≤ -Real.log (38830565191 / 40000000000) ∧
    -Real.log (38830565191 / 40000000000) ≤ (5934351 / 200000000) := by
  have h := checkLog_sound (w := (1169434809 / 78830565191)) (n := 12)
    (lo := (14835877 / 500000000)) (hi := (5934351 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 38830565191) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 38830565191) = 1/(38830565191 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-5934351 / 200000000) (-14835877 / 500000000) (Real.log (38830565191 / 40000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell145
