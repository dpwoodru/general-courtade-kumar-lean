import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell078
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

theorem reflection_log_1_neg : (51901123 / 200000000) ≤ -Real.log (5120 / 6637) ∧
    -Real.log (5120 / 6637) ≤ (16219101 / 62500000) := by
  have h := checkLog_sound (w := (1517 / 11757)) (n := 12)
    (lo := (51901123 / 200000000)) (hi := (16219101 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6637 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6637 / 5120) = 1/(5120 / 6637) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (51901123 / 200000000) (16219101 / 62500000) (Real.log (6637 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6637 / 5120) = -Real.log (5120 / 6637) := by
    rw [show ((6637 / 5120) : ℝ) = ((5120 / 6637) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (351387607 / 1000000000) ≤ -Real.log (3603 / 5120) ∧
    -Real.log (3603 / 5120) ≤ (43923451 / 125000000) := by
  have h := checkLog_sound (w := (1517 / 8723)) (n := 12)
    (lo := (351387607 / 1000000000)) (hi := (43923451 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3603) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3603) = 1/(3603 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-43923451 / 125000000) (-351387607 / 1000000000) (Real.log (3603 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (259053501 / 1000000000) ≤ -Real.log (2560 / 3317) ∧
    -Real.log (2560 / 3317) ≤ (129526751 / 500000000) := by
  have h := checkLog_sound (w := (757 / 5877)) (n := 12)
    (lo := (259053501 / 1000000000)) (hi := (129526751 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3317 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3317 / 2560) = 1/(2560 / 3317) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (259053501 / 1000000000) (129526751 / 500000000) (Real.log (3317 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3317 / 2560) = -Real.log (2560 / 3317) := by
    rw [show ((3317 / 2560) : ℝ) = ((2560 / 3317) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (175277657 / 500000000) ≤ -Real.log (1803 / 2560) ∧
    -Real.log (1803 / 2560) ≤ (70111063 / 200000000) := by
  have h := checkLog_sound (w := (757 / 4363)) (n := 12)
    (lo := (175277657 / 500000000)) (hi := (70111063 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1803) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1803) = 1/(1803 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-70111063 / 200000000) (-175277657 / 500000000) (Real.log (1803 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (190524487 / 1000000000) ≤ -Real.log (250000 / 302471) ∧
    -Real.log (250000 / 302471) ≤ (23815561 / 125000000) := by
  have h := checkLog_sound (w := (52471 / 552471)) (n := 12)
    (lo := (190524487 / 1000000000)) (hi := (23815561 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((302471 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(302471 / 250000) = 1/(250000 / 302471) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (190524487 / 1000000000) (23815561 / 125000000) (Real.log (302471 / 250000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (302471 / 250000) = -Real.log (250000 / 302471) := by
    rw [show ((302471 / 250000) : ℝ) = ((250000 / 302471) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (58893877 / 250000000) ≤ -Real.log (197529 / 250000) ∧
    -Real.log (197529 / 250000) ≤ (235575509 / 1000000000) := by
  have h := checkLog_sound (w := (52471 / 447529)) (n := 12)
    (lo := (58893877 / 250000000)) (hi := (235575509 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 197529) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 197529) = 1/(197529 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-235575509 / 1000000000) (-58893877 / 250000000) (Real.log (197529 / 250000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (190871567 / 1000000000) ≤ -Real.log (15625 / 18911) ∧
    -Real.log (15625 / 18911) ≤ (11929473 / 62500000) := by
  have h := checkLog_sound (w := (1643 / 17268)) (n := 12)
    (lo := (190871567 / 1000000000)) (hi := (11929473 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((18911 / 15625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(18911 / 15625) = 1/(15625 / 18911) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (190871567 / 1000000000) (11929473 / 62500000) (Real.log (18911 / 15625)) := by
  have h := reflection_log_7_neg
  have he : Real.log (18911 / 15625) = -Real.log (15625 / 18911) := by
    rw [show ((18911 / 15625) : ℝ) = ((15625 / 18911) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (236107217 / 1000000000) ≤ -Real.log (12339 / 15625) ∧
    -Real.log (12339 / 15625) ≤ (118053609 / 500000000) := by
  have h := checkLog_sound (w := (1643 / 13982)) (n := 12)
    (lo := (236107217 / 1000000000)) (hi := (118053609 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 12339) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625 / 12339) = 1/(12339 / 15625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-118053609 / 500000000) (-236107217 / 1000000000) (Real.log (12339 / 15625)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (139974093 / 1000000000) ≤ -Real.log (250000 / 287561) ∧
    -Real.log (250000 / 287561) ≤ (69987047 / 500000000) := by
  have h := checkLog_sound (w := (37561 / 537561)) (n := 12)
    (lo := (139974093 / 1000000000)) (hi := (69987047 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((287561 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(287561 / 250000) = 1/(250000 / 287561) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (139974093 / 1000000000) (69987047 / 500000000) (Real.log (287561 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (287561 / 250000) = -Real.log (250000 / 287561) := by
    rw [show ((287561 / 250000) : ℝ) = ((250000 / 287561) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (162806029 / 1000000000) ≤ -Real.log (212439 / 250000) ∧
    -Real.log (212439 / 250000) ≤ (16280603 / 100000000) := by
  have h := checkLog_sound (w := (37561 / 462439)) (n := 12)
    (lo := (162806029 / 1000000000)) (hi := (16280603 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 212439) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 212439) = 1/(212439 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-16280603 / 100000000) (-162806029 / 1000000000) (Real.log (212439 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (17530337 / 125000000) ≤ -Real.log (1000000 / 1150553) ∧
    -Real.log (1000000 / 1150553) ≤ (140242697 / 1000000000) := by
  have h := checkLog_sound (w := (150553 / 2150553)) (n := 12)
    (lo := (17530337 / 125000000)) (hi := (140242697 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1150553 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1150553 / 1000000) = 1/(1000000 / 1150553) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (17530337 / 125000000) (140242697 / 1000000000) (Real.log (1150553 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1150553 / 1000000) = -Real.log (1000000 / 1150553) := by
    rw [show ((1150553 / 1000000) : ℝ) = ((1000000 / 1150553) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (163169729 / 1000000000) ≤ -Real.log (849447 / 1000000) ∧
    -Real.log (849447 / 1000000) ≤ (16316973 / 100000000) := by
  have h := checkLog_sound (w := (150553 / 1849447)) (n := 12)
    (lo := (163169729 / 1000000000)) (hi := (16316973 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 849447) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 849447) = 1/(849447 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-16316973 / 100000000) (-163169729 / 1000000000) (Real.log (849447 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (121921763 / 200000000) ≤ -Real.log (100000000000 / 183971159179) ∧
    -Real.log (100000000000 / 183971159179) ≤ (38100551 / 62500000) := by
  have h := checkLog_sound (w := (83971159179 / 283971159179)) (n := 12)
    (lo := (121921763 / 200000000)) (hi := (38100551 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((183971159179 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(183971159179 / 100000000000) = 1/(100000000000 / 183971159179) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (121921763 / 200000000) (38100551 / 62500000) (Real.log (183971159179 / 100000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (183971159179 / 100000000000) = -Real.log (100000000000 / 183971159179) := by
    rw [show ((183971159179 / 100000000000) : ℝ) = ((100000000000 / 183971159179) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (305446611 / 500000000) ≤ -Real.log (500000000000 / 921038023869) ∧
    -Real.log (500000000000 / 921038023869) ≤ (610893223 / 1000000000) := by
  have h := checkLog_sound (w := (421038023869 / 1421038023869)) (n := 12)
    (lo := (305446611 / 500000000)) (hi := (610893223 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((921038023869 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(921038023869 / 500000000000) = 1/(500000000000 / 921038023869) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (305446611 / 500000000) (610893223 / 1000000000) (Real.log (921038023869 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (921038023869 / 500000000000) = -Real.log (500000000000 / 921038023869) := by
    rw [show ((921038023869 / 500000000000) : ℝ) = ((500000000000 / 921038023869) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (106524999 / 250000000) ≤ -Real.log (7812500000 / 11963077257) ∧
    -Real.log (7812500000 / 11963077257) ≤ (426099997 / 1000000000) := by
  have h := checkLog_sound (w := (4150577257 / 19775577257)) (n := 12)
    (lo := (106524999 / 250000000)) (hi := (426099997 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11963077257 / 7812500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11963077257 / 7812500000) = 1/(7812500000 / 11963077257) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (106524999 / 250000000) (426099997 / 1000000000) (Real.log (11963077257 / 7812500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (11963077257 / 7812500000) = -Real.log (7812500000 / 11963077257) := by
    rw [show ((11963077257 / 7812500000) : ℝ) = ((7812500000 / 11963077257) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (85395757 / 200000000) ≤ -Real.log (400000000 / 613048059) ∧
    -Real.log (400000000 / 613048059) ≤ (213489393 / 500000000) := by
  have h := checkLog_sound (w := (213048059 / 1013048059)) (n := 12)
    (lo := (85395757 / 200000000)) (hi := (213489393 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((613048059 / 400000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(613048059 / 400000000) = 1/(400000000 / 613048059) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (85395757 / 200000000) (213489393 / 500000000) (Real.log (613048059 / 400000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (613048059 / 400000000) = -Real.log (400000000 / 613048059) := by
    rw [show ((613048059 / 400000000) : ℝ) = ((400000000 / 613048059) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (302780123 / 1000000000) ≤ -Real.log (50000000000 / 67680840147) ∧
    -Real.log (50000000000 / 67680840147) ≤ (75695031 / 250000000) := by
  have h := checkLog_sound (w := (17680840147 / 117680840147)) (n := 12)
    (lo := (302780123 / 1000000000)) (hi := (75695031 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((67680840147 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(67680840147 / 50000000000) = 1/(50000000000 / 67680840147) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (302780123 / 1000000000) (75695031 / 250000000) (Real.log (67680840147 / 50000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (67680840147 / 50000000000) = -Real.log (50000000000 / 67680840147) := by
    rw [show ((67680840147 / 50000000000) : ℝ) = ((50000000000 / 67680840147) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (12136497 / 40000000) ≤ -Real.log (500000000000 / 677236484443) ∧
    -Real.log (500000000000 / 677236484443) ≤ (151706213 / 500000000) := by
  have h := checkLog_sound (w := (177236484443 / 1177236484443)) (n := 12)
    (lo := (12136497 / 40000000)) (hi := (151706213 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((677236484443 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(677236484443 / 500000000000) = 1/(500000000000 / 677236484443) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (12136497 / 40000000) (151706213 / 500000000) (Real.log (677236484443 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (677236484443 / 500000000000) = -Real.log (500000000000 / 677236484443) := by
    rw [show ((677236484443 / 500000000000) : ℝ) = ((500000000000 / 677236484443) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (22927033 / 1000000000) ≤ -Real.log (977333794191 / 1000000000000) ∧
    -Real.log (977333794191 / 1000000000000) ≤ (11463517 / 500000000) := by
  have h := checkLog_sound (w := (22666205809 / 1977333794191)) (n := 12)
    (lo := (22927033 / 1000000000)) (hi := (11463517 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 977333794191) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 977333794191) = 1/(977333794191 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-11463517 / 500000000) (-22927033 / 1000000000) (Real.log (977333794191 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (4566387 / 200000000) ≤ -Real.log (61089171279 / 62500000000) ∧
    -Real.log (61089171279 / 62500000000) ≤ (356749 / 15625000) := by
  have h := checkLog_sound (w := (1410828721 / 123589171279)) (n := 12)
    (lo := (4566387 / 200000000)) (hi := (356749 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 61089171279) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 61089171279) = 1/(61089171279 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-356749 / 15625000) (-4566387 / 200000000) (Real.log (61089171279 / 62500000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell078
