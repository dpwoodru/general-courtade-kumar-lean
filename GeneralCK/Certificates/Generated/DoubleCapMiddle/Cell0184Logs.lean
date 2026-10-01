import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0184
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

theorem reflection_log_1_neg : (136413087 / 500000000) ≤ -Real.log (2560 / 3363) ∧
    -Real.log (2560 / 3363) ≤ (10913047 / 40000000) := by
  have h := checkLog_sound (w := (803 / 5923)) (n := 12)
    (lo := (136413087 / 500000000)) (hi := (10913047 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3363 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3363 / 2560) = 1/(2560 / 3363) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (136413087 / 500000000) (10913047 / 40000000) (Real.log (3363 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3363 / 2560) = -Real.log (2560 / 3363) := by
    rw [show ((3363 / 2560) : ℝ) = ((2560 / 3363) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (376399449 / 1000000000) ≤ -Real.log (1757 / 2560) ∧
    -Real.log (1757 / 2560) ≤ (7527989 / 20000000) := by
  have h := checkLog_sound (w := (803 / 4317)) (n := 12)
    (lo := (376399449 / 1000000000)) (hi := (7527989 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1757) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1757) = 1/(1757 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-7527989 / 20000000) (-376399449 / 1000000000) (Real.log (1757 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (68095011 / 250000000) ≤ -Real.log (5120 / 6723) ∧
    -Real.log (5120 / 6723) ≤ (54476009 / 200000000) := by
  have h := checkLog_sound (w := (1603 / 11843)) (n := 12)
    (lo := (68095011 / 250000000)) (hi := (54476009 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6723 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6723 / 5120) = 1/(5120 / 6723) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (68095011 / 250000000) (54476009 / 200000000) (Real.log (6723 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6723 / 5120) = -Real.log (5120 / 6723) := by
    rw [show ((6723 / 5120) : ℝ) = ((5120 / 6723) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (75109217 / 200000000) ≤ -Real.log (3517 / 5120) ∧
    -Real.log (3517 / 5120) ≤ (187773043 / 500000000) := by
  have h := checkLog_sound (w := (1603 / 8637)) (n := 12)
    (lo := (75109217 / 200000000)) (hi := (187773043 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3517) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3517) = 1/(3517 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-187773043 / 500000000) (-75109217 / 200000000) (Real.log (3517 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (121737271 / 250000000) ≤ -Real.log (1280 / 2083) ∧
    -Real.log (1280 / 2083) ≤ (97389817 / 200000000) := by
  have h := checkLog_sound (w := (803 / 3363)) (n := 12)
    (lo := (121737271 / 250000000)) (hi := (97389817 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2083 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2083 / 1280) = 1/(1280 / 2083) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (121737271 / 250000000) (97389817 / 200000000) (Real.log (2083 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2083 / 1280) = -Real.log (1280 / 2083) := by
    rw [show ((2083 / 1280) : ℝ) = ((1280 / 2083) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (197419773 / 200000000) ≤ -Real.log (477 / 1280) ∧
    -Real.log (477 / 1280) ≤ (987098867 / 1000000000) := by
  have h := checkLog_sound (w := (163 / 1117)) (n := 12)
    (lo := (58790337 / 200000000)) (hi := (146975843 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 477) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 477) = 1/(477 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-987098867 / 1000000000) (-197419773 / 200000000) (Real.log (477 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (486228709 / 1000000000) ≤ -Real.log (2560 / 4163) ∧
    -Real.log (2560 / 4163) ≤ (48622871 / 100000000) := by
  have h := checkLog_sound (w := (1603 / 6723)) (n := 12)
    (lo := (486228709 / 1000000000)) (hi := (48622871 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4163 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4163 / 2560) = 1/(2560 / 4163) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (486228709 / 1000000000) (48622871 / 100000000) (Real.log (4163 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (4163 / 2560) = -Real.log (2560 / 4163) := by
    rw [show ((4163 / 2560) : ℝ) = ((2560 / 4163) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (196791829 / 200000000) ≤ -Real.log (957 / 2560) ∧
    -Real.log (957 / 2560) ≤ (983959147 / 1000000000) := by
  have h := checkLog_sound (w := (323 / 2237)) (n := 12)
    (lo := (58162393 / 200000000)) (hi := (145405983 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 957) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 957) = 1/(957 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-983959147 / 1000000000) (-196791829 / 200000000) (Real.log (957 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (372608527 / 1000000000) ≤ -Real.log (250000 / 362879) ∧
    -Real.log (250000 / 362879) ≤ (23288033 / 62500000) := by
  have h := checkLog_sound (w := (112879 / 612879)) (n := 12)
    (lo := (372608527 / 1000000000)) (hi := (23288033 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((362879 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(362879 / 250000) = 1/(250000 / 362879) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (372608527 / 1000000000) (23288033 / 62500000) (Real.log (362879 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (362879 / 250000) = -Real.log (250000 / 362879) := by
    rw [show ((362879 / 250000) : ℝ) = ((250000 / 362879) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (60059717 / 100000000) ≤ -Real.log (137121 / 250000) ∧
    -Real.log (137121 / 250000) ≤ (600597171 / 1000000000) := by
  have h := checkLog_sound (w := (112879 / 387121)) (n := 12)
    (lo := (60059717 / 100000000)) (hi := (600597171 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 137121) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 137121) = 1/(137121 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-600597171 / 1000000000) (-60059717 / 100000000) (Real.log (137121 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (373218737 / 1000000000) ≤ -Real.log (500000 / 726201) ∧
    -Real.log (500000 / 726201) ≤ (186609369 / 500000000) := by
  have h := checkLog_sound (w := (226201 / 1226201)) (n := 12)
    (lo := (373218737 / 1000000000)) (hi := (186609369 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((726201 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(726201 / 500000) = 1/(500000 / 726201) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (373218737 / 1000000000) (186609369 / 500000000) (Real.log (726201 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (726201 / 500000) = -Real.log (500000 / 726201) := by
    rw [show ((726201 / 500000) : ℝ) = ((500000 / 726201) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (602213837 / 1000000000) ≤ -Real.log (273799 / 500000) ∧
    -Real.log (273799 / 500000) ≤ (301106919 / 500000000) := by
  have h := checkLog_sound (w := (226201 / 773799)) (n := 12)
    (lo := (602213837 / 1000000000)) (hi := (301106919 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 273799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 273799) = 1/(273799 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-301106919 / 500000000) (-602213837 / 1000000000) (Real.log (273799 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (145706427 / 500000000) ≤ -Real.log (1000000 / 1338317) ∧
    -Real.log (1000000 / 1338317) ≤ (58282571 / 200000000) := by
  have h := checkLog_sound (w := (338317 / 2338317)) (n := 12)
    (lo := (145706427 / 500000000)) (hi := (58282571 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1338317 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1338317 / 1000000) = 1/(1000000 / 1338317) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (145706427 / 500000000) (58282571 / 200000000) (Real.log (1338317 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1338317 / 1000000) = -Real.log (1000000 / 1338317) := by
    rw [show ((1338317 / 1000000) : ℝ) = ((1000000 / 1338317) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (412968689 / 1000000000) ≤ -Real.log (661683 / 1000000) ∧
    -Real.log (661683 / 1000000) ≤ (41296869 / 100000000) := by
  have h := checkLog_sound (w := (338317 / 1661683)) (n := 12)
    (lo := (412968689 / 1000000000)) (hi := (41296869 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 661683) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 661683) = 1/(661683 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-41296869 / 100000000) (-412968689 / 1000000000) (Real.log (661683 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (2335743 / 8000000) ≤ -Real.log (50000 / 66953) ∧
    -Real.log (50000 / 66953) ≤ (72991969 / 250000000) := by
  have h := checkLog_sound (w := (16953 / 116953)) (n := 12)
    (lo := (2335743 / 8000000)) (hi := (72991969 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((66953 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(66953 / 50000) = 1/(50000 / 66953) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (2335743 / 8000000) (72991969 / 250000000) (Real.log (66953 / 50000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (66953 / 50000) = -Real.log (50000 / 66953) := by
    rw [show ((66953 / 50000) : ℝ) = ((50000 / 66953) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (207046107 / 500000000) ≤ -Real.log (33047 / 50000) ∧
    -Real.log (33047 / 50000) ≤ (82818443 / 200000000) := by
  have h := checkLog_sound (w := (16953 / 83047)) (n := 12)
    (lo := (207046107 / 500000000)) (hi := (82818443 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 33047) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 33047) = 1/(33047 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-82818443 / 200000000) (-207046107 / 500000000) (Real.log (33047 / 50000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (973205697 / 1000000000) ≤ -Real.log (781250000 / 2067511313) ∧
    -Real.log (781250000 / 2067511313) ≤ (973205699 / 1000000000) := by
  have h := checkLog_sound (w := (505011313 / 3630011313)) (n := 12)
    (lo := (280058517 / 1000000000)) (hi := (140029259 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2067511313 / 1562500000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(2067511313 / 1562500000) = 1/(781250000 / 2067511313) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (973205697 / 1000000000) (973205699 / 1000000000) (Real.log (2067511313 / 781250000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (2067511313 / 781250000) = -Real.log (781250000 / 2067511313) := by
    rw [show ((2067511313 / 781250000) : ℝ) = ((781250000 / 2067511313) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (487716287 / 500000000) ≤ -Real.log (20000000000 / 53046285779) ∧
    -Real.log (20000000000 / 53046285779) ≤ (7620567 / 7812500) := by
  have h := checkLog_sound (w := (13046285779 / 93046285779)) (n := 12)
    (lo := (141142697 / 500000000)) (hi := (56457079 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((53046285779 / 40000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(53046285779 / 40000000000) = 1/(20000000000 / 53046285779) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (487716287 / 500000000) (7620567 / 7812500) (Real.log (53046285779 / 20000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (53046285779 / 20000000000) = -Real.log (20000000000 / 53046285779) := by
    rw [show ((53046285779 / 20000000000) : ℝ) = ((20000000000 / 53046285779) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (704381543 / 1000000000) ≤ -Real.log (500000000000 / 1011297706001) ∧
    -Real.log (500000000000 / 1011297706001) ≤ (140876309 / 200000000) := by
  have h := checkLog_sound (w := (11297706001 / 2011297706001)) (n := 12)
    (lo := (11234363 / 1000000000)) (hi := (2808591 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1011297706001 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1011297706001 / 1000000000000) = 1/(500000000000 / 1011297706001) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (704381543 / 1000000000) (140876309 / 200000000) (Real.log (1011297706001 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (1011297706001 / 500000000000) = -Real.log (500000000000 / 1011297706001) := by
    rw [show ((1011297706001 / 500000000000) : ℝ) = ((500000000000 / 1011297706001) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (706060089 / 1000000000) ≤ -Real.log (125000000000 / 253249160287) ∧
    -Real.log (125000000000 / 253249160287) ≤ (706060091 / 1000000000) := by
  have h := checkLog_sound (w := (3249160287 / 503249160287)) (n := 12)
    (lo := (12912909 / 1000000000)) (hi := (1291291 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((253249160287 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(253249160287 / 250000000000) = 1/(125000000000 / 253249160287) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (706060089 / 1000000000) (706060091 / 1000000000) (Real.log (253249160287 / 125000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (253249160287 / 125000000000) = -Real.log (125000000000 / 253249160287) := by
    rw [show ((253249160287 / 125000000000) : ℝ) = ((125000000000 / 253249160287) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0184
