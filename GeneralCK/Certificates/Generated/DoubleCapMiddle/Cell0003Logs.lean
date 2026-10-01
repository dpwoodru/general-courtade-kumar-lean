import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0003
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

theorem reflection_log_1_neg : (223143551 / 500000000) ≤ -Real.log (16 / 25) ∧
    -Real.log (16 / 25) ≤ (446287103 / 1000000000) := by
  have h := checkLog_sound (w := (9 / 41)) (n := 12)
    (lo := (223143551 / 500000000)) (hi := (446287103 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25 / 16) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25 / 16) = 1/(16 / 25) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (223143551 / 500000000) (446287103 / 1000000000) (Real.log (25 / 16)) := by
  have h := reflection_log_1_neg
  have he : Real.log (25 / 16) = -Real.log (16 / 25) := by
    rw [show ((25 / 16) : ℝ) = ((16 / 25) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (206669643 / 250000000) ≤ -Real.log (7 / 16) ∧
    -Real.log (7 / 16) ≤ (413339287 / 500000000) := by
  have h := checkLog_sound (w := (1 / 15)) (n := 12)
    (lo := (521607 / 3906250)) (hi := (133531393 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8 / 7) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(8 / 7) = 1/(7 / 16) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-413339287 / 500000000) (-206669643 / 250000000) (Real.log (7 / 16)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (43825493 / 100000000) ≤ -Real.log (20 / 31) ∧
    -Real.log (20 / 31) ≤ (438254931 / 1000000000) := by
  have h := checkLog_sound (w := (11 / 51)) (n := 12)
    (lo := (43825493 / 100000000)) (hi := (438254931 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31 / 20) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31 / 20) = 1/(20 / 31) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (43825493 / 100000000) (438254931 / 1000000000) (Real.log (31 / 20)) := by
  have h := reflection_log_3_neg
  have he : Real.log (31 / 20) = -Real.log (20 / 31) := by
    rw [show ((31 / 20) : ℝ) = ((20 / 31) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (159701539 / 200000000) ≤ -Real.log (9 / 20) ∧
    -Real.log (9 / 20) ≤ (798507697 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 19)) (n := 12)
    (lo := (21072103 / 200000000)) (hi := (26340129 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10 / 9) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(10 / 9) = 1/(9 / 20) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-798507697 / 1000000000) (-159701539 / 200000000) (Real.log (9 / 20)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (23556607 / 200000000) ≤ -Real.log (8 / 9) ∧
    -Real.log (8 / 9) ≤ (29445759 / 250000000) := by
  have h := checkLog_sound (w := (1 / 17)) (n := 12)
    (lo := (23556607 / 200000000)) (hi := (29445759 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9 / 8) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(9 / 8) = 1/(8 / 9) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (23556607 / 200000000) (29445759 / 250000000) (Real.log (9 / 8)) := by
  have h := reflection_log_5_neg
  have he : Real.log (9 / 8) = -Real.log (8 / 9) := by
    rw [show ((9 / 8) : ℝ) = ((8 / 9) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (521607 / 3906250) ≤ -Real.log (7 / 8) ∧
    -Real.log (7 / 8) ≤ (133531393 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 15)) (n := 12)
    (lo := (521607 / 3906250)) (hi := (133531393 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8 / 7) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(8 / 7) = 1/(7 / 8) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-133531393 / 1000000000) (-521607 / 3906250) (Real.log (7 / 8)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (95310179 / 1000000000) ≤ -Real.log (10 / 11) ∧
    -Real.log (10 / 11) ≤ (4765509 / 50000000) := by
  have h := checkLog_sound (w := (1 / 21)) (n := 12)
    (lo := (95310179 / 1000000000)) (hi := (4765509 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11 / 10) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11 / 10) = 1/(10 / 11) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (95310179 / 1000000000) (4765509 / 50000000) (Real.log (11 / 10)) := by
  have h := reflection_log_7_neg
  have he : Real.log (11 / 10) = -Real.log (10 / 11) := by
    rw [show ((11 / 10) : ℝ) = ((10 / 11) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (21072103 / 200000000) ≤ -Real.log (9 / 10) ∧
    -Real.log (9 / 10) ≤ (26340129 / 250000000) := by
  have h := checkLog_sound (w := (1 / 19)) (n := 12)
    (lo := (21072103 / 200000000)) (hi := (26340129 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10 / 9) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10 / 9) = 1/(9 / 10) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-26340129 / 250000000) (-21072103 / 200000000) (Real.log (9 / 10)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (28896159 / 50000000) ≤ -Real.log (1000000 / 1782333) ∧
    -Real.log (1000000 / 1782333) ≤ (577923181 / 1000000000) := by
  have h := checkLog_sound (w := (782333 / 2782333)) (n := 12)
    (lo := (28896159 / 50000000)) (hi := (577923181 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1782333 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1782333 / 1000000) = 1/(1000000 / 1782333) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (28896159 / 50000000) (577923181 / 1000000000) (Real.log (1782333 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1782333 / 1000000) = -Real.log (1000000 / 1782333) := by
    rw [show ((1782333 / 1000000) : ℝ) = ((1000000 / 1782333) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (304957781 / 200000000) ≤ -Real.log (217667 / 1000000) ∧
    -Real.log (217667 / 1000000) ≤ (381197227 / 250000000) := by
  have h := checkLog_sound (w := (32333 / 467667)) (n := 12)
    (lo := (27698909 / 200000000)) (hi := (69247273 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 217667) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(250000 / 217667) = 1/(217667 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-381197227 / 250000000) (-304957781 / 200000000) (Real.log (217667 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (289337921 / 500000000) ≤ -Real.log (40000 / 71347) ∧
    -Real.log (40000 / 71347) ≤ (578675843 / 1000000000) := by
  have h := checkLog_sound (w := (31347 / 111347)) (n := 12)
    (lo := (289337921 / 500000000)) (hi := (578675843 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((71347 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(71347 / 40000) = 1/(40000 / 71347) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (289337921 / 500000000) (578675843 / 1000000000) (Real.log (71347 / 40000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (71347 / 40000) = -Real.log (40000 / 71347) := by
    rw [show ((71347 / 40000) : ℝ) = ((40000 / 71347) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1530973371 / 1000000000) ≤ -Real.log (8653 / 40000) ∧
    -Real.log (8653 / 40000) ≤ (765486687 / 500000000) := by
  have h := checkLog_sound (w := (1347 / 18653)) (n := 12)
    (lo := (144679011 / 1000000000)) (hi := (36169753 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8653) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(10000 / 8653) = 1/(8653 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-765486687 / 500000000) (-1530973371 / 1000000000) (Real.log (8653 / 40000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (26229059 / 50000000) ≤ -Real.log (1000000 / 1689751) ∧
    -Real.log (1000000 / 1689751) ≤ (524581181 / 1000000000) := by
  have h := checkLog_sound (w := (689751 / 2689751)) (n := 12)
    (lo := (26229059 / 50000000)) (hi := (524581181 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1689751 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1689751 / 1000000) = 1/(1000000 / 1689751) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (26229059 / 50000000) (524581181 / 1000000000) (Real.log (1689751 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1689751 / 1000000) = -Real.log (1000000 / 1689751) := by
    rw [show ((1689751 / 1000000) : ℝ) = ((1000000 / 1689751) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (1170380077 / 1000000000) ≤ -Real.log (310249 / 1000000) ∧
    -Real.log (310249 / 1000000) ≤ (1170380079 / 1000000000) := by
  have h := checkLog_sound (w := (189751 / 810249)) (n := 12)
    (lo := (477232897 / 1000000000)) (hi := (238616449 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 310249) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 310249) = 1/(310249 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-1170380079 / 1000000000) (-1170380077 / 1000000000) (Real.log (310249 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (264573577 / 500000000) ≤ -Real.log (250000 / 424371) ∧
    -Real.log (250000 / 424371) ≤ (105829431 / 200000000) := by
  have h := checkLog_sound (w := (174371 / 674371)) (n := 12)
    (lo := (264573577 / 500000000)) (hi := (105829431 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((424371 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(424371 / 250000) = 1/(250000 / 424371) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (264573577 / 500000000) (105829431 / 200000000) (Real.log (424371 / 250000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (424371 / 250000) = -Real.log (250000 / 424371) := by
    rw [show ((424371 / 250000) : ℝ) = ((250000 / 424371) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (1195621109 / 1000000000) ≤ -Real.log (75629 / 250000) ∧
    -Real.log (75629 / 250000) ≤ (1195621111 / 1000000000) := by
  have h := checkLog_sound (w := (49371 / 200629)) (n := 12)
    (lo := (502473929 / 1000000000)) (hi := (50247393 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 75629) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(125000 / 75629) = 1/(75629 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-1195621111 / 1000000000) (-1195621109 / 1000000000) (Real.log (75629 / 250000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (420542417 / 200000000) ≤ -Real.log (500000000000 / 4094173668953) ∧
    -Real.log (500000000000 / 4094173668953) ≤ (2102712089 / 1000000000) := by
  have h := checkLog_sound (w := (94173668953 / 8094173668953)) (n := 12)
    (lo := (4654109 / 200000000)) (hi := (11635273 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4094173668953 / 4000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(4094173668953 / 4000000000000) = 1/(500000000000 / 4094173668953) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (420542417 / 200000000) (2102712089 / 1000000000) (Real.log (4094173668953 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (4094173668953 / 500000000000) = -Real.log (500000000000 / 4094173668953) := by
    rw [show ((4094173668953 / 500000000000) : ℝ) = ((500000000000 / 4094173668953) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (2109649213 / 1000000000) ≤ -Real.log (100000000000 / 824534843407) ∧
    -Real.log (100000000000 / 824534843407) ≤ (2109649217 / 1000000000) := by
  have h := checkLog_sound (w := (24534843407 / 1624534843407)) (n := 12)
    (lo := (30207673 / 1000000000)) (hi := (15103837 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((824534843407 / 800000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(824534843407 / 800000000000) = 1/(100000000000 / 824534843407) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (2109649213 / 1000000000) (2109649217 / 1000000000) (Real.log (824534843407 / 100000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (824534843407 / 100000000000) = -Real.log (100000000000 / 824534843407) := by
    rw [show ((824534843407 / 100000000000) : ℝ) = ((100000000000 / 824534843407) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1694961257 / 1000000000) ≤ -Real.log (500000000000 / 2723217480153) ∧
    -Real.log (500000000000 / 2723217480153) ≤ (84748063 / 50000000) := by
  have h := checkLog_sound (w := (723217480153 / 4723217480153)) (n := 12)
    (lo := (308666897 / 1000000000)) (hi := (154333449 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2723217480153 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2723217480153 / 2000000000000) = 1/(500000000000 / 2723217480153) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (1694961257 / 1000000000) (84748063 / 50000000) (Real.log (2723217480153 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (2723217480153 / 500000000000) = -Real.log (500000000000 / 2723217480153) := by
    rw [show ((2723217480153 / 500000000000) : ℝ) = ((500000000000 / 2723217480153) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (215596033 / 125000000) ≤ -Real.log (500000000000 / 2805610281771) ∧
    -Real.log (500000000000 / 2805610281771) ≤ (1724768267 / 1000000000) := by
  have h := checkLog_sound (w := (805610281771 / 4805610281771)) (n := 12)
    (lo := (21154619 / 62500000)) (hi := (67694781 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2805610281771 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2805610281771 / 2000000000000) = 1/(500000000000 / 2805610281771) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (215596033 / 125000000) (1724768267 / 1000000000) (Real.log (2805610281771 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (2805610281771 / 500000000000) = -Real.log (500000000000 / 2805610281771) := by
    rw [show ((2805610281771 / 500000000000) : ℝ) = ((500000000000 / 2805610281771) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0003
