import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0403
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

theorem reflection_log_1_neg : (199507021 / 1000000000) ≤ -Real.log (10240 / 12501) ∧
    -Real.log (10240 / 12501) ≤ (99753511 / 500000000) := by
  have h := checkLog_sound (w := (2261 / 22741)) (n := 12)
    (lo := (199507021 / 1000000000)) (hi := (99753511 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12501 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12501 / 10240) = 1/(10240 / 12501) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (199507021 / 1000000000) (99753511 / 500000000) (Real.log (12501 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12501 / 10240) = -Real.log (10240 / 12501) := by
    rw [show ((12501 / 10240) : ℝ) = ((10240 / 12501) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (249488529 / 1000000000) ≤ -Real.log (7979 / 10240) ∧
    -Real.log (7979 / 10240) ≤ (24948853 / 100000000) := by
  have h := checkLog_sound (w := (2261 / 18219)) (n := 12)
    (lo := (249488529 / 1000000000)) (hi := (24948853 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7979) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7979) = 1/(7979 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-24948853 / 100000000) (-249488529 / 1000000000) (Real.log (7979 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (199267011 / 1000000000) ≤ -Real.log (5120 / 6249) ∧
    -Real.log (5120 / 6249) ≤ (49816753 / 250000000) := by
  have h := checkLog_sound (w := (1129 / 11369)) (n := 12)
    (lo := (199267011 / 1000000000)) (hi := (49816753 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6249 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6249 / 5120) = 1/(5120 / 6249) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (199267011 / 1000000000) (49816753 / 250000000) (Real.log (6249 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6249 / 5120) = -Real.log (5120 / 6249) := by
    rw [show ((6249 / 5120) : ℝ) = ((5120 / 6249) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (62278153 / 250000000) ≤ -Real.log (3991 / 5120) ∧
    -Real.log (3991 / 5120) ≤ (249112613 / 1000000000) := by
  have h := checkLog_sound (w := (1129 / 9111)) (n := 12)
    (lo := (62278153 / 250000000)) (hi := (249112613 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3991) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3991) = 1/(3991 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-249112613 / 1000000000) (-62278153 / 250000000) (Real.log (3991 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (365754691 / 1000000000) ≤ -Real.log (5120 / 7381) ∧
    -Real.log (5120 / 7381) ≤ (91438673 / 250000000) := by
  have h := checkLog_sound (w := (2261 / 12501)) (n := 12)
    (lo := (365754691 / 1000000000)) (hi := (91438673 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7381 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7381 / 5120) = 1/(5120 / 7381) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (365754691 / 1000000000) (91438673 / 250000000) (Real.log (7381 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (7381 / 5120) = -Real.log (5120 / 7381) := by
    rw [show ((7381 / 5120) : ℝ) = ((5120 / 7381) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (23307301 / 40000000) ≤ -Real.log (2859 / 5120) ∧
    -Real.log (2859 / 5120) ≤ (291341263 / 500000000) := by
  have h := checkLog_sound (w := (2261 / 7979)) (n := 12)
    (lo := (23307301 / 40000000)) (hi := (291341263 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2859) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2859) = 1/(2859 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-291341263 / 500000000) (-23307301 / 40000000) (Real.log (2859 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (1141713 / 3125000) ≤ -Real.log (2560 / 3689) ∧
    -Real.log (2560 / 3689) ≤ (365348161 / 1000000000) := by
  have h := checkLog_sound (w := (1129 / 6249)) (n := 12)
    (lo := (1141713 / 3125000)) (hi := (365348161 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3689 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3689 / 2560) = 1/(2560 / 3689) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (1141713 / 3125000) (365348161 / 1000000000) (Real.log (3689 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (3689 / 2560) = -Real.log (2560 / 3689) := by
    rw [show ((3689 / 2560) : ℝ) = ((2560 / 3689) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (581633757 / 1000000000) ≤ -Real.log (1431 / 2560) ∧
    -Real.log (1431 / 2560) ≤ (290816879 / 500000000) := by
  have h := checkLog_sound (w := (1129 / 3991)) (n := 12)
    (lo := (581633757 / 1000000000)) (hi := (290816879 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1431) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1431) = 1/(1431 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-290816879 / 500000000) (-581633757 / 1000000000) (Real.log (1431 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (68383109 / 250000000) ≤ -Real.log (5000 / 6573) ∧
    -Real.log (5000 / 6573) ≤ (273532437 / 1000000000) := by
  have h := checkLog_sound (w := (1573 / 11573)) (n := 12)
    (lo := (68383109 / 250000000)) (hi := (273532437 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6573 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6573 / 5000) = 1/(5000 / 6573) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (68383109 / 250000000) (273532437 / 1000000000) (Real.log (6573 / 5000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (6573 / 5000) = -Real.log (5000 / 6573) := by
    rw [show ((6573 / 5000) : ℝ) = ((5000 / 6573) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (377752669 / 1000000000) ≤ -Real.log (3427 / 5000) ∧
    -Real.log (3427 / 5000) ≤ (37775267 / 100000000) := by
  have h := checkLog_sound (w := (1573 / 8427)) (n := 12)
    (lo := (377752669 / 1000000000)) (hi := (37775267 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 3427) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 3427) = 1/(3427 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-37775267 / 100000000) (-377752669 / 1000000000) (Real.log (3427 / 5000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (273857197 / 1000000000) ≤ -Real.log (1000000 / 1315027) ∧
    -Real.log (1000000 / 1315027) ≤ (136928599 / 500000000) := by
  have h := checkLog_sound (w := (315027 / 2315027)) (n := 12)
    (lo := (273857197 / 1000000000)) (hi := (136928599 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1315027 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1315027 / 1000000) = 1/(1000000 / 1315027) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (273857197 / 1000000000) (136928599 / 500000000) (Real.log (1315027 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1315027 / 1000000) = -Real.log (1000000 / 1315027) := by
    rw [show ((1315027 / 1000000) : ℝ) = ((1000000 / 1315027) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (378375857 / 1000000000) ≤ -Real.log (684973 / 1000000) ∧
    -Real.log (684973 / 1000000) ≤ (189187929 / 500000000) := by
  have h := checkLog_sound (w := (315027 / 1684973)) (n := 12)
    (lo := (378375857 / 1000000000)) (hi := (189187929 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 684973) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 684973) = 1/(684973 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-189187929 / 500000000) (-378375857 / 1000000000) (Real.log (684973 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (51493651 / 250000000) ≤ -Real.log (500000 / 614361) ∧
    -Real.log (500000 / 614361) ≤ (41194921 / 200000000) := by
  have h := checkLog_sound (w := (114361 / 1114361)) (n := 12)
    (lo := (51493651 / 250000000)) (hi := (41194921 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((614361 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(614361 / 500000) = 1/(500000 / 614361) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (51493651 / 250000000) (41194921 / 200000000) (Real.log (614361 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (614361 / 500000) = -Real.log (500000 / 614361) := by
    rw [show ((614361 / 500000) : ℝ) = ((500000 / 614361) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (259706399 / 1000000000) ≤ -Real.log (385639 / 500000) ∧
    -Real.log (385639 / 500000) ≤ (324633 / 1250000) := by
  have h := checkLog_sound (w := (114361 / 885639)) (n := 12)
    (lo := (259706399 / 1000000000)) (hi := (324633 / 1250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 385639) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 385639) = 1/(385639 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-324633 / 1250000) (-259706399 / 1000000000) (Real.log (385639 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (206241513 / 1000000000) ≤ -Real.log (20000 / 24581) ∧
    -Real.log (20000 / 24581) ≤ (103120757 / 500000000) := by
  have h := checkLog_sound (w := (4581 / 44581)) (n := 12)
    (lo := (206241513 / 1000000000)) (hi := (103120757 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24581 / 20000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24581 / 20000) = 1/(20000 / 24581) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (206241513 / 1000000000) (103120757 / 500000000) (Real.log (24581 / 20000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (24581 / 20000) = -Real.log (20000 / 24581) := by
    rw [show ((24581 / 20000) : ℝ) = ((20000 / 24581) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (130065879 / 500000000) ≤ -Real.log (15419 / 20000) ∧
    -Real.log (15419 / 20000) ≤ (260131759 / 1000000000) := by
  have h := checkLog_sound (w := (4581 / 35419)) (n := 12)
    (lo := (130065879 / 500000000)) (hi := (260131759 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20000 / 15419) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20000 / 15419) = 1/(15419 / 20000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-260131759 / 1000000000) (-130065879 / 500000000) (Real.log (15419 / 20000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (325642553 / 500000000) ≤ -Real.log (250000000000 / 479501021301) ∧
    -Real.log (250000000000 / 479501021301) ≤ (651285107 / 1000000000) := by
  have h := checkLog_sound (w := (229501021301 / 729501021301)) (n := 12)
    (lo := (325642553 / 500000000)) (hi := (651285107 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((479501021301 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(479501021301 / 250000000000) = 1/(250000000000 / 479501021301) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (325642553 / 500000000) (651285107 / 1000000000) (Real.log (479501021301 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (479501021301 / 250000000000) = -Real.log (250000000000 / 479501021301) := by
    rw [show ((479501021301 / 250000000000) : ℝ) = ((250000000000 / 479501021301) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (130446611 / 200000000) ≤ -Real.log (250000000000 / 479955779279) ∧
    -Real.log (250000000000 / 479955779279) ≤ (20382283 / 31250000) := by
  have h := checkLog_sound (w := (229955779279 / 729955779279)) (n := 12)
    (lo := (130446611 / 200000000)) (hi := (20382283 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((479955779279 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(479955779279 / 250000000000) = 1/(250000000000 / 479955779279) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (130446611 / 200000000) (20382283 / 31250000) (Real.log (479955779279 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (479955779279 / 250000000000) = -Real.log (250000000000 / 479955779279) := by
    rw [show ((479955779279 / 250000000000) : ℝ) = ((250000000000 / 479955779279) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (116420251 / 250000000) ≤ -Real.log (500000000000 / 796549363523) ∧
    -Real.log (500000000000 / 796549363523) ≤ (93136201 / 200000000) := by
  have h := checkLog_sound (w := (296549363523 / 1296549363523)) (n := 12)
    (lo := (116420251 / 250000000)) (hi := (93136201 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((796549363523 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(796549363523 / 500000000000) = 1/(500000000000 / 796549363523) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (116420251 / 250000000) (93136201 / 200000000) (Real.log (796549363523 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (796549363523 / 500000000000) = -Real.log (500000000000 / 796549363523) := by
    rw [show ((796549363523 / 500000000000) : ℝ) = ((500000000000 / 796549363523) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (466373271 / 1000000000) ≤ -Real.log (31250000000 / 49818811207) ∧
    -Real.log (31250000000 / 49818811207) ≤ (58296659 / 125000000) := by
  have h := checkLog_sound (w := (18568811207 / 81068811207)) (n := 12)
    (lo := (466373271 / 1000000000)) (hi := (58296659 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49818811207 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49818811207 / 31250000000) = 1/(31250000000 / 49818811207) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (466373271 / 1000000000) (58296659 / 125000000) (Real.log (49818811207 / 31250000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (49818811207 / 31250000000) = -Real.log (31250000000 / 49818811207) := by
    rw [show ((49818811207 / 31250000000) : ℝ) = ((31250000000 / 49818811207) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0403
