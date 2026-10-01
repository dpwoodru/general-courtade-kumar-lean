import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_10432_neg : (360064303 / 1000000000) ≤ -Real.log (62500000000 / 89588849089) ∧
    -Real.log (62500000000 / 89588849089) ≤ (22504019 / 62500000) := by
  have h := checkLog_sound (w := (27088849089 / 152088849089)) (n := 12)
    (lo := (360064303 / 1000000000)) (hi := (22504019 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((89588849089 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(89588849089 / 62500000000) = 1/(62500000000 / 89588849089) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10432 : Bounds (360064303 / 1000000000) (22504019 / 62500000) (Real.log (89588849089 / 62500000000)) := by
  have h := reflection_log_10432_neg
  have he : Real.log (89588849089 / 62500000000) = -Real.log (62500000000 / 89588849089) := by
    rw [show ((89588849089 / 62500000000) : ℝ) = ((62500000000 / 89588849089) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10433_neg : (362029023 / 500000000) ≤ -Real.log (500000000000 / 1031393568147) ∧
    -Real.log (500000000000 / 1031393568147) ≤ (11313407 / 15625000) := by
  have h := checkLog_sound (w := (31393568147 / 2031393568147)) (n := 12)
    (lo := (15455433 / 500000000)) (hi := (30910867 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1031393568147 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1031393568147 / 1000000000000) = 1/(500000000000 / 1031393568147) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10433 : Bounds (362029023 / 500000000) (11313407 / 15625000) (Real.log (1031393568147 / 500000000000)) := by
  have h := reflection_log_10433_neg
  have he : Real.log (1031393568147 / 500000000000) = -Real.log (500000000000 / 1031393568147) := by
    rw [show ((1031393568147 / 500000000000) : ℝ) = ((500000000000 / 1031393568147) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10434_neg : (90791591 / 125000000) ≤ -Real.log (500000000000 / 1033742331289) ∧
    -Real.log (500000000000 / 1033742331289) ≤ (72633273 / 100000000) := by
  have h := checkLog_sound (w := (33742331289 / 2033742331289)) (n := 12)
    (lo := (8296387 / 250000000)) (hi := (33185549 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1033742331289 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1033742331289 / 1000000000000) = 1/(500000000000 / 1033742331289) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10434 : Bounds (90791591 / 125000000) (72633273 / 100000000) (Real.log (1033742331289 / 500000000000)) := by
  have h := reflection_log_10434_neg
  have he : Real.log (1033742331289 / 500000000000) = -Real.log (500000000000 / 1033742331289) := by
    rw [show ((1033742331289 / 500000000000) : ℝ) = ((500000000000 / 1033742331289) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10435_neg : (299363577 / 1000000000) ≤ -Real.log (1000 / 1349) ∧
    -Real.log (1000 / 1349) ≤ (149681789 / 500000000) := by
  have h := checkLog_sound (w := (349 / 2349)) (n := 12)
    (lo := (299363577 / 1000000000)) (hi := (149681789 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1349 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1349 / 1000) = 1/(1000 / 1349) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10435 : Bounds (299363577 / 1000000000) (149681789 / 500000000) (Real.log (1349 / 1000)) := by
  have h := reflection_log_10435_neg
  have he : Real.log (1349 / 1000) = -Real.log (1000 / 1349) := by
    rw [show ((1349 / 1000) : ℝ) = ((1000 / 1349) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10436_neg : (107311409 / 250000000) ≤ -Real.log (651 / 1000) ∧
    -Real.log (651 / 1000) ≤ (429245637 / 1000000000) := by
  have h := checkLog_sound (w := (349 / 1651)) (n := 12)
    (lo := (107311409 / 250000000)) (hi := (429245637 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 651) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 651) = 1/(651 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10436 : Bounds (-429245637 / 1000000000) (-107311409 / 250000000) (Real.log (651 / 1000)) := by
  have h := reflection_log_10436_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10437_neg : (348939 / 1000000000) ≤ -Real.log (1000000 / 1000349) ∧
    -Real.log (1000000 / 1000349) ≤ (17447 / 50000000) := by
  have h := checkLog_sound (w := (349 / 2000349)) (n := 12)
    (lo := (348939 / 1000000000)) (hi := (17447 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000349 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000349 / 1000000) = 1/(1000000 / 1000349) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10437 : Bounds (348939 / 1000000000) (17447 / 50000000) (Real.log (1000349 / 1000000)) := by
  have h := reflection_log_10437_neg
  have he : Real.log (1000349 / 1000000) = -Real.log (1000000 / 1000349) := by
    rw [show ((1000349 / 1000000) : ℝ) = ((1000000 / 1000349) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10438_neg : (17453 / 50000000) ≤ -Real.log (999651 / 1000000) ∧
    -Real.log (999651 / 1000000) ≤ (349061 / 1000000000) := by
  have h := checkLog_sound (w := (349 / 1999651)) (n := 12)
    (lo := (17453 / 50000000)) (hi := (349061 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999651) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999651) = 1/(999651 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10438 : Bounds (-349061 / 1000000000) (-17453 / 50000000) (Real.log (999651 / 1000000)) := by
  have h := reflection_log_10438_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10439_neg : (163623669 / 1000000000) ≤ -Real.log (1000000 / 1177771) ∧
    -Real.log (1000000 / 1177771) ≤ (16362367 / 100000000) := by
  have h := checkLog_sound (w := (177771 / 2177771)) (n := 12)
    (lo := (163623669 / 1000000000)) (hi := (16362367 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1177771 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1177771 / 1000000) = 1/(1000000 / 1177771) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10439 : Bounds (163623669 / 1000000000) (16362367 / 100000000) (Real.log (1177771 / 1000000)) := by
  have h := reflection_log_10439_neg
  have he : Real.log (1177771 / 1000000) = -Real.log (1000000 / 1177771) := by
    rw [show ((1177771 / 1000000) : ℝ) = ((1000000 / 1177771) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10440_neg : (195736333 / 1000000000) ≤ -Real.log (822229 / 1000000) ∧
    -Real.log (822229 / 1000000) ≤ (97868167 / 500000000) := by
  have h := checkLog_sound (w := (177771 / 1822229)) (n := 12)
    (lo := (195736333 / 1000000000)) (hi := (97868167 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 822229) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 822229) = 1/(822229 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10440 : Bounds (-97868167 / 500000000) (-195736333 / 1000000000) (Real.log (822229 / 1000000)) := by
  have h := reflection_log_10440_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10441_neg : (82184009 / 500000000) ≤ -Real.log (125000 / 147331) ∧
    -Real.log (125000 / 147331) ≤ (164368019 / 1000000000) := by
  have h := checkLog_sound (w := (22331 / 272331)) (n := 12)
    (lo := (82184009 / 500000000)) (hi := (164368019 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((147331 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(147331 / 125000) = 1/(125000 / 147331) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10441 : Bounds (82184009 / 500000000) (164368019 / 1000000000) (Real.log (147331 / 125000)) := by
  have h := reflection_log_10441_neg
  have he : Real.log (147331 / 125000) = -Real.log (125000 / 147331) := by
    rw [show ((147331 / 125000) : ℝ) = ((125000 / 147331) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10442_neg : (39360703 / 200000000) ≤ -Real.log (102669 / 125000) ∧
    -Real.log (102669 / 125000) ≤ (49200879 / 250000000) := by
  have h := checkLog_sound (w := (22331 / 227669)) (n := 12)
    (lo := (39360703 / 200000000)) (hi := (49200879 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 102669) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 102669) = 1/(102669 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10442 : Bounds (-49200879 / 250000000) (-39360703 / 200000000) (Real.log (102669 / 125000)) := by
  have h := reflection_log_10442_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10443_neg : (32435497 / 1000000000) ≤ -Real.log (15126326439 / 15625000000) ∧
    -Real.log (15126326439 / 15625000000) ≤ (16217749 / 500000000) := by
  have h := checkLog_sound (w := (498673561 / 30751326439)) (n := 12)
    (lo := (32435497 / 1000000000)) (hi := (16217749 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 15126326439) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 15126326439) = 1/(15126326439 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10443 : Bounds (-16217749 / 500000000) (-32435497 / 1000000000) (Real.log (15126326439 / 15625000000)) := by
  have h := reflection_log_10443_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10444_neg : (4014083 / 125000000) ≤ -Real.log (968397471559 / 1000000000000) ∧
    -Real.log (968397471559 / 1000000000000) ≤ (6422533 / 200000000) := by
  have h := checkLog_sound (w := (31602528441 / 1968397471559)) (n := 12)
    (lo := (4014083 / 125000000)) (hi := (6422533 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 968397471559) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 968397471559) = 1/(968397471559 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10444 : Bounds (-6422533 / 200000000) (-4014083 / 125000000) (Real.log (968397471559 / 1000000000000)) := by
  have h := reflection_log_10444_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10445_neg : (179680001 / 500000000) ≤ -Real.log (125000000000 / 179051547683) ∧
    -Real.log (125000000000 / 179051547683) ≤ (359360003 / 1000000000) := by
  have h := checkLog_sound (w := (54051547683 / 304051547683)) (n := 12)
    (lo := (179680001 / 500000000)) (hi := (359360003 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((179051547683 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(179051547683 / 125000000000) = 1/(125000000000 / 179051547683) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10445 : Bounds (179680001 / 500000000) (359360003 / 1000000000) (Real.log (179051547683 / 125000000000)) := by
  have h := reflection_log_10445_neg
  have he : Real.log (179051547683 / 125000000000) = -Real.log (125000000000 / 179051547683) := by
    rw [show ((179051547683 / 125000000000) : ℝ) = ((125000000000 / 179051547683) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10446_neg : (180585767 / 500000000) ≤ -Real.log (500000000000 / 717504796969) ∧
    -Real.log (500000000000 / 717504796969) ≤ (72234307 / 200000000) := by
  have h := checkLog_sound (w := (217504796969 / 1217504796969)) (n := 12)
    (lo := (180585767 / 500000000)) (hi := (72234307 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((717504796969 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(717504796969 / 500000000000) = 1/(500000000000 / 717504796969) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10446 : Bounds (180585767 / 500000000) (72234307 / 200000000) (Real.log (717504796969 / 500000000000)) := by
  have h := reflection_log_10446_neg
  have he : Real.log (717504796969 / 500000000000) = -Real.log (500000000000 / 717504796969) := by
    rw [show ((717504796969 / 500000000000) : ℝ) = ((500000000000 / 717504796969) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10447_neg : (90791591 / 125000000) ≤ -Real.log (62500000000 / 129217791411) ∧
    -Real.log (62500000000 / 129217791411) ≤ (72633273 / 100000000) := by
  have h := checkLog_sound (w := (4217791411 / 254217791411)) (n := 12)
    (lo := (8296387 / 250000000)) (hi := (33185549 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((129217791411 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(129217791411 / 125000000000) = 1/(62500000000 / 129217791411) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10447 : Bounds (90791591 / 125000000) (72633273 / 100000000) (Real.log (129217791411 / 62500000000)) := by
  have h := reflection_log_10447_neg
  have he : Real.log (129217791411 / 62500000000) = -Real.log (62500000000 / 129217791411) := by
    rw [show ((129217791411 / 62500000000) : ℝ) = ((62500000000 / 129217791411) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10448_neg : (728609213 / 1000000000) ≤ -Real.log (125000000000 / 259024577573) ∧
    -Real.log (125000000000 / 259024577573) ≤ (145721843 / 200000000) := by
  have h := checkLog_sound (w := (9024577573 / 509024577573)) (n := 12)
    (lo := (35462033 / 1000000000)) (hi := (17731017 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((259024577573 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(259024577573 / 250000000000) = 1/(125000000000 / 259024577573) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10448 : Bounds (728609213 / 1000000000) (145721843 / 200000000) (Real.log (259024577573 / 125000000000)) := by
  have h := reflection_log_10448_neg
  have he : Real.log (259024577573 / 125000000000) = -Real.log (125000000000 / 259024577573) := by
    rw [show ((259024577573 / 125000000000) : ℝ) = ((125000000000 / 259024577573) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10449_neg : (18756537 / 62500000) ≤ -Real.log (20 / 27) ∧
    -Real.log (20 / 27) ≤ (300104593 / 1000000000) := by
  have h := checkLog_sound (w := (7 / 47)) (n := 12)
    (lo := (18756537 / 62500000)) (hi := (300104593 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((27 / 20) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(27 / 20) = 1/(20 / 27) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10449 : Bounds (18756537 / 62500000) (300104593 / 1000000000) (Real.log (27 / 20)) := by
  have h := reflection_log_10449_neg
  have he : Real.log (27 / 20) = -Real.log (20 / 27) := by
    rw [show ((27 / 20) : ℝ) = ((20 / 27) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10450_neg : (107695729 / 250000000) ≤ -Real.log (13 / 20) ∧
    -Real.log (13 / 20) ≤ (430782917 / 1000000000) := by
  have h := checkLog_sound (w := (7 / 33)) (n := 12)
    (lo := (107695729 / 250000000)) (hi := (430782917 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20 / 13) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20 / 13) = 1/(13 / 20) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10450 : Bounds (-430782917 / 1000000000) (-107695729 / 250000000) (Real.log (13 / 20)) := by
  have h := reflection_log_10450_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10451_neg : (174969 / 500000000) ≤ -Real.log (20000 / 20007) ∧
    -Real.log (20000 / 20007) ≤ (349939 / 1000000000) := by
  have h := checkLog_sound (w := (7 / 40007)) (n := 12)
    (lo := (174969 / 500000000)) (hi := (349939 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20007 / 20000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20007 / 20000) = 1/(20000 / 20007) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10451 : Bounds (174969 / 500000000) (349939 / 1000000000) (Real.log (20007 / 20000)) := by
  have h := reflection_log_10451_neg
  have he : Real.log (20007 / 20000) = -Real.log (20000 / 20007) := by
    rw [show ((20007 / 20000) : ℝ) = ((20000 / 20007) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10452_neg : (350061 / 1000000000) ≤ -Real.log (19993 / 20000) ∧
    -Real.log (19993 / 20000) ≤ (175031 / 500000000) := by
  have h := checkLog_sound (w := (7 / 39993)) (n := 12)
    (lo := (350061 / 1000000000)) (hi := (175031 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20000 / 19993) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20000 / 19993) = 1/(19993 / 20000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10452 : Bounds (-175031 / 500000000) (-350061 / 1000000000) (Real.log (19993 / 20000)) := by
  have h := reflection_log_10452_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10453_neg : (164077813 / 1000000000) ≤ -Real.log (500000 / 589153) ∧
    -Real.log (500000 / 589153) ≤ (82038907 / 500000000) := by
  have h := checkLog_sound (w := (89153 / 1089153)) (n := 12)
    (lo := (164077813 / 1000000000)) (hi := (82038907 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((589153 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(589153 / 500000) = 1/(500000 / 589153) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10453 : Bounds (164077813 / 1000000000) (82038907 / 500000000) (Real.log (589153 / 500000)) := by
  have h := reflection_log_10453_neg
  have he : Real.log (589153 / 500000) = -Real.log (500000 / 589153) := by
    rw [show ((589153 / 500000) : ℝ) = ((500000 / 589153) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10454_neg : (12274201 / 62500000) ≤ -Real.log (410847 / 500000) ∧
    -Real.log (410847 / 500000) ≤ (196387217 / 1000000000) := by
  have h := checkLog_sound (w := (89153 / 910847)) (n := 12)
    (lo := (12274201 / 62500000)) (hi := (196387217 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 410847) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 410847) = 1/(410847 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10454 : Bounds (-196387217 / 1000000000) (-12274201 / 62500000) (Real.log (410847 / 500000)) := by
  have h := reflection_log_10454_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10455_neg : (6592873 / 40000000) ≤ -Real.log (1000000 / 1179183) ∧
    -Real.log (1000000 / 1179183) ≤ (82410913 / 500000000) := by
  have h := checkLog_sound (w := (179183 / 2179183)) (n := 12)
    (lo := (6592873 / 40000000)) (hi := (82410913 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1179183 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1179183 / 1000000) = 1/(1000000 / 1179183) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10455 : Bounds (6592873 / 40000000) (82410913 / 500000000) (Real.log (1179183 / 1000000)) := by
  have h := reflection_log_10455_neg
  have he : Real.log (1179183 / 1000000) = -Real.log (1000000 / 1179183) := by
    rw [show ((1179183 / 1000000) : ℝ) = ((1000000 / 1179183) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10456_neg : (197455093 / 1000000000) ≤ -Real.log (820817 / 1000000) ∧
    -Real.log (820817 / 1000000) ≤ (98727547 / 500000000) := by
  have h := checkLog_sound (w := (179183 / 1820817)) (n := 12)
    (lo := (197455093 / 1000000000)) (hi := (98727547 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 820817) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 820817) = 1/(820817 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10456 : Bounds (-98727547 / 500000000) (-197455093 / 1000000000) (Real.log (820817 / 1000000)) := by
  have h := reflection_log_10456_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10457_neg : (32633267 / 1000000000) ≤ -Real.log (967893452511 / 1000000000000) ∧
    -Real.log (967893452511 / 1000000000000) ≤ (8158317 / 250000000) := by
  have h := checkLog_sound (w := (32106547489 / 1967893452511)) (n := 12)
    (lo := (32633267 / 1000000000)) (hi := (8158317 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 967893452511) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 967893452511) = 1/(967893452511 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10457 : Bounds (-8158317 / 250000000) (-32633267 / 1000000000) (Real.log (967893452511 / 1000000000000)) := by
  have h := reflection_log_10457_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10458_neg : (16154701 / 500000000) ≤ -Real.log (242051742591 / 250000000000) ∧
    -Real.log (242051742591 / 250000000000) ≤ (32309403 / 1000000000) := by
  have h := checkLog_sound (w := (7948257409 / 492051742591)) (n := 12)
    (lo := (16154701 / 500000000)) (hi := (32309403 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 242051742591) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 242051742591) = 1/(242051742591 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10458 : Bounds (-32309403 / 1000000000) (-16154701 / 500000000) (Real.log (242051742591 / 250000000000)) := by
  have h := reflection_log_10458_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10459_neg : (360465029 / 1000000000) ≤ -Real.log (500000000000 / 716998055237) ∧
    -Real.log (500000000000 / 716998055237) ≤ (36046503 / 100000000) := by
  have h := checkLog_sound (w := (216998055237 / 1216998055237)) (n := 12)
    (lo := (360465029 / 1000000000)) (hi := (36046503 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((716998055237 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(716998055237 / 500000000000) = 1/(500000000000 / 716998055237) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10459 : Bounds (360465029 / 1000000000) (36046503 / 100000000) (Real.log (716998055237 / 500000000000)) := by
  have h := reflection_log_10459_neg
  have he : Real.log (716998055237 / 500000000000) = -Real.log (500000000000 / 716998055237) := by
    rw [show ((716998055237 / 500000000000) : ℝ) = ((500000000000 / 716998055237) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10460_neg : (362276919 / 1000000000) ≤ -Real.log (250000000000 / 359149176979) ∧
    -Real.log (250000000000 / 359149176979) ≤ (9056923 / 25000000) := by
  have h := checkLog_sound (w := (109149176979 / 609149176979)) (n := 12)
    (lo := (362276919 / 1000000000)) (hi := (9056923 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((359149176979 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(359149176979 / 250000000000) = 1/(250000000000 / 359149176979) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10460 : Bounds (362276919 / 1000000000) (9056923 / 25000000) (Real.log (359149176979 / 250000000000)) := by
  have h := reflection_log_10460_neg
  have he : Real.log (359149176979 / 250000000000) = -Real.log (250000000000 / 359149176979) := by
    rw [show ((359149176979 / 250000000000) : ℝ) = ((250000000000 / 359149176979) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10461_neg : (728609213 / 1000000000) ≤ -Real.log (500000000000 / 1036098310291) ∧
    -Real.log (500000000000 / 1036098310291) ≤ (145721843 / 200000000) := by
  have h := checkLog_sound (w := (36098310291 / 2036098310291)) (n := 12)
    (lo := (35462033 / 1000000000)) (hi := (17731017 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1036098310291 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1036098310291 / 1000000000000) = 1/(500000000000 / 1036098310291) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10461 : Bounds (728609213 / 1000000000) (145721843 / 200000000) (Real.log (1036098310291 / 500000000000)) := by
  have h := reflection_log_10461_neg
  have he : Real.log (1036098310291 / 500000000000) = -Real.log (500000000000 / 1036098310291) := by
    rw [show ((1036098310291 / 500000000000) : ℝ) = ((500000000000 / 1036098310291) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10462_neg : (730887507 / 1000000000) ≤ -Real.log (250000000000 / 519230769231) ∧
    -Real.log (250000000000 / 519230769231) ≤ (730887509 / 1000000000) := by
  have h := checkLog_sound (w := (19230769231 / 1019230769231)) (n := 12)
    (lo := (37740327 / 1000000000)) (hi := (4717541 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((519230769231 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(519230769231 / 500000000000) = 1/(250000000000 / 519230769231) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10462 : Bounds (730887507 / 1000000000) (730887509 / 1000000000) (Real.log (519230769231 / 250000000000)) := by
  have h := reflection_log_10462_neg
  have he : Real.log (519230769231 / 250000000000) = -Real.log (250000000000 / 519230769231) := by
    rw [show ((519230769231 / 250000000000) : ℝ) = ((250000000000 / 519230769231) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10463_neg : (150422529 / 500000000) ≤ -Real.log (1000 / 1351) ∧
    -Real.log (1000 / 1351) ≤ (300845059 / 1000000000) := by
  have h := checkLog_sound (w := (351 / 2351)) (n := 12)
    (lo := (150422529 / 500000000)) (hi := (300845059 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1351 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1351 / 1000) = 1/(1000 / 1351) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10463 : Bounds (150422529 / 500000000) (300845059 / 1000000000) (Real.log (1351 / 1000)) := by
  have h := reflection_log_10463_neg
  have he : Real.log (1351 / 1000) = -Real.log (1000 / 1351) := by
    rw [show ((1351 / 1000) : ℝ) = ((1000 / 1351) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10464_neg : (216161281 / 500000000) ≤ -Real.log (649 / 1000) ∧
    -Real.log (649 / 1000) ≤ (432322563 / 1000000000) := by
  have h := checkLog_sound (w := (351 / 1649)) (n := 12)
    (lo := (216161281 / 500000000)) (hi := (432322563 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 649) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 649) = 1/(649 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10464 : Bounds (-432322563 / 1000000000) (-216161281 / 500000000) (Real.log (649 / 1000)) := by
  have h := reflection_log_10464_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10465_neg : (175469 / 500000000) ≤ -Real.log (1000000 / 1000351) ∧
    -Real.log (1000000 / 1000351) ≤ (350939 / 1000000000) := by
  have h := checkLog_sound (w := (351 / 2000351)) (n := 12)
    (lo := (175469 / 500000000)) (hi := (350939 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000351 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000351 / 1000000) = 1/(1000000 / 1000351) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10465 : Bounds (175469 / 500000000) (350939 / 1000000000) (Real.log (1000351 / 1000000)) := by
  have h := reflection_log_10465_neg
  have he : Real.log (1000351 / 1000000) = -Real.log (1000000 / 1000351) := by
    rw [show ((1000351 / 1000000) : ℝ) = ((1000000 / 1000351) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10466_neg : (351061 / 1000000000) ≤ -Real.log (999649 / 1000000) ∧
    -Real.log (999649 / 1000000) ≤ (175531 / 500000000) := by
  have h := checkLog_sound (w := (351 / 1999649)) (n := 12)
    (lo := (351061 / 1000000000)) (hi := (175531 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999649) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999649) = 1/(999649 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10466 : Bounds (-175531 / 500000000) (-351061 / 1000000000) (Real.log (999649 / 1000000)) := by
  have h := reflection_log_10466_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10467_neg : (20566469 / 125000000) ≤ -Real.log (1000000 / 1178841) ∧
    -Real.log (1000000 / 1178841) ≤ (164531753 / 1000000000) := by
  have h := checkLog_sound (w := (178841 / 2178841)) (n := 12)
    (lo := (20566469 / 125000000)) (hi := (164531753 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1178841 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1178841 / 1000000) = 1/(1000000 / 1178841) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10467 : Bounds (20566469 / 125000000) (164531753 / 1000000000) (Real.log (1178841 / 1000000)) := by
  have h := reflection_log_10467_neg
  have he : Real.log (1178841 / 1000000) = -Real.log (1000000 / 1178841) := by
    rw [show ((1178841 / 1000000) : ℝ) = ((1000000 / 1178841) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10468_neg : (98519261 / 500000000) ≤ -Real.log (821159 / 1000000) ∧
    -Real.log (821159 / 1000000) ≤ (197038523 / 1000000000) := by
  have h := checkLog_sound (w := (178841 / 1821159)) (n := 12)
    (lo := (98519261 / 500000000)) (hi := (197038523 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 821159) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 821159) = 1/(821159 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10468 : Bounds (-197038523 / 1000000000) (-98519261 / 500000000) (Real.log (821159 / 1000000)) := by
  have h := reflection_log_10468_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10469_neg : (82638137 / 500000000) ≤ -Real.log (1000000 / 1179719) ∧
    -Real.log (1000000 / 1179719) ≤ (6611051 / 40000000) := by
  have h := checkLog_sound (w := (179719 / 2179719)) (n := 12)
    (lo := (82638137 / 500000000)) (hi := (6611051 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1179719 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1179719 / 1000000) = 1/(1000000 / 1179719) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10469 : Bounds (82638137 / 500000000) (6611051 / 40000000) (Real.log (1179719 / 1000000)) := by
  have h := reflection_log_10469_neg
  have he : Real.log (1179719 / 1000000) = -Real.log (1000000 / 1179719) := by
    rw [show ((1179719 / 1000000) : ℝ) = ((1000000 / 1179719) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10470_neg : (99054157 / 500000000) ≤ -Real.log (820281 / 1000000) ∧
    -Real.log (820281 / 1000000) ≤ (39621663 / 200000000) := by
  have h := checkLog_sound (w := (179719 / 1820281)) (n := 12)
    (lo := (99054157 / 500000000)) (hi := (39621663 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 820281) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 820281) = 1/(820281 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10470 : Bounds (-39621663 / 200000000) (-99054157 / 500000000) (Real.log (820281 / 1000000)) := by
  have h := reflection_log_10470_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10471_neg : (32832039 / 1000000000) ≤ -Real.log (967701081039 / 1000000000000) ∧
    -Real.log (967701081039 / 1000000000000) ≤ (820801 / 25000000) := by
  have h := checkLog_sound (w := (32298918961 / 1967701081039)) (n := 12)
    (lo := (32832039 / 1000000000)) (hi := (820801 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 967701081039) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 967701081039) = 1/(967701081039 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10471 : Bounds (-820801 / 25000000) (-32832039 / 1000000000) (Real.log (967701081039 / 1000000000000)) := by
  have h := reflection_log_10471_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10472_neg : (32506769 / 1000000000) ≤ -Real.log (968015896719 / 1000000000000) ∧
    -Real.log (968015896719 / 1000000000000) ≤ (3250677 / 100000000) := by
  have h := checkLog_sound (w := (31984103281 / 1968015896719)) (n := 12)
    (lo := (32506769 / 1000000000)) (hi := (3250677 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 968015896719) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 968015896719) = 1/(968015896719 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10472 : Bounds (-3250677 / 100000000) (-32506769 / 1000000000) (Real.log (968015896719 / 1000000000000)) := by
  have h := reflection_log_10472_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10473_neg : (180785137 / 500000000) ≤ -Real.log (500000000000 / 717790951569) ∧
    -Real.log (500000000000 / 717790951569) ≤ (14462811 / 40000000) := by
  have h := checkLog_sound (w := (217790951569 / 1217790951569)) (n := 12)
    (lo := (180785137 / 500000000)) (hi := (14462811 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((717790951569 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(717790951569 / 500000000000) = 1/(500000000000 / 717790951569) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10473 : Bounds (180785137 / 500000000) (14462811 / 40000000) (Real.log (717790951569 / 500000000000)) := by
  have h := reflection_log_10473_neg
  have he : Real.log (717790951569 / 500000000000) = -Real.log (500000000000 / 717790951569) := by
    rw [show ((717790951569 / 500000000000) : ℝ) = ((500000000000 / 717790951569) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10474_neg : (363384589 / 1000000000) ≤ -Real.log (250000000000 / 359547216137) ∧
    -Real.log (250000000000 / 359547216137) ≤ (36338459 / 100000000) := by
  have h := checkLog_sound (w := (109547216137 / 609547216137)) (n := 12)
    (lo := (363384589 / 1000000000)) (hi := (36338459 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((359547216137 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(359547216137 / 250000000000) = 1/(250000000000 / 359547216137) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10474 : Bounds (363384589 / 1000000000) (36338459 / 100000000) (Real.log (359547216137 / 250000000000)) := by
  have h := reflection_log_10474_neg
  have he : Real.log (359547216137 / 250000000000) = -Real.log (250000000000 / 359547216137) := by
    rw [show ((359547216137 / 250000000000) : ℝ) = ((250000000000 / 359547216137) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10475_neg : (730887507 / 1000000000) ≤ -Real.log (500000000000 / 1038461538461) ∧
    -Real.log (500000000000 / 1038461538461) ≤ (730887509 / 1000000000) := by
  have h := checkLog_sound (w := (38461538461 / 2038461538461)) (n := 12)
    (lo := (37740327 / 1000000000)) (hi := (4717541 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1038461538461 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1038461538461 / 1000000000000) = 1/(500000000000 / 1038461538461) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10475 : Bounds (730887507 / 1000000000) (730887509 / 1000000000) (Real.log (1038461538461 / 500000000000)) := by
  have h := reflection_log_10475_neg
  have he : Real.log (1038461538461 / 500000000000) = -Real.log (500000000000 / 1038461538461) := by
    rw [show ((1038461538461 / 500000000000) : ℝ) = ((500000000000 / 1038461538461) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10476_neg : (36658381 / 50000000) ≤ -Real.log (500000000000 / 1040832049307) ∧
    -Real.log (500000000000 / 1040832049307) ≤ (366583811 / 500000000) := by
  have h := checkLog_sound (w := (40832049307 / 2040832049307)) (n := 12)
    (lo := (1000511 / 25000000)) (hi := (40020441 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1040832049307 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1040832049307 / 1000000000000) = 1/(500000000000 / 1040832049307) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10476 : Bounds (36658381 / 50000000) (366583811 / 500000000) (Real.log (1040832049307 / 500000000000)) := by
  have h := reflection_log_10476_neg
  have he : Real.log (1040832049307 / 500000000000) = -Real.log (500000000000 / 1040832049307) := by
    rw [show ((1040832049307 / 500000000000) : ℝ) = ((500000000000 / 1040832049307) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10477_neg : (301584977 / 1000000000) ≤ -Real.log (125 / 169) ∧
    -Real.log (125 / 169) ≤ (150792489 / 500000000) := by
  have h := checkLog_sound (w := (22 / 147)) (n := 12)
    (lo := (301584977 / 1000000000)) (hi := (150792489 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((169 / 125) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(169 / 125) = 1/(125 / 169) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10477 : Bounds (301584977 / 1000000000) (150792489 / 500000000) (Real.log (169 / 125)) := by
  have h := reflection_log_10477_neg
  have he : Real.log (169 / 125) = -Real.log (125 / 169) := by
    rw [show ((169 / 125) : ℝ) = ((125 / 169) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10478_neg : (216932291 / 500000000) ≤ -Real.log (81 / 125) ∧
    -Real.log (81 / 125) ≤ (433864583 / 1000000000) := by
  have h := checkLog_sound (w := (22 / 103)) (n := 12)
    (lo := (216932291 / 500000000)) (hi := (433864583 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 81) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125 / 81) = 1/(81 / 125) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10478 : Bounds (-433864583 / 1000000000) (-216932291 / 500000000) (Real.log (81 / 125)) := by
  have h := reflection_log_10478_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10479_neg : (175969 / 500000000) ≤ -Real.log (31250 / 31261) ∧
    -Real.log (31250 / 31261) ≤ (351939 / 1000000000) := by
  have h := checkLog_sound (w := (11 / 62511)) (n := 12)
    (lo := (175969 / 500000000)) (hi := (351939 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31261 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31261 / 31250) = 1/(31250 / 31261) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10479 : Bounds (175969 / 500000000) (351939 / 1000000000) (Real.log (31261 / 31250)) := by
  have h := reflection_log_10479_neg
  have he : Real.log (31261 / 31250) = -Real.log (31250 / 31261) := by
    rw [show ((31261 / 31250) : ℝ) = ((31250 / 31261) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10480_neg : (352061 / 1000000000) ≤ -Real.log (31239 / 31250) ∧
    -Real.log (31239 / 31250) ≤ (176031 / 500000000) := by
  have h := checkLog_sound (w := (11 / 62489)) (n := 12)
    (lo := (352061 / 1000000000)) (hi := (176031 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 31239) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31250 / 31239) = 1/(31239 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10480 : Bounds (-176031 / 500000000) (-352061 / 1000000000) (Real.log (31239 / 31250)) := by
  have h := reflection_log_10480_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10481_neg : (32997097 / 200000000) ≤ -Real.log (62500 / 73711) ∧
    -Real.log (62500 / 73711) ≤ (82492743 / 500000000) := by
  have h := checkLog_sound (w := (11211 / 136211)) (n := 12)
    (lo := (32997097 / 200000000)) (hi := (82492743 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((73711 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(73711 / 62500) = 1/(62500 / 73711) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10481 : Bounds (32997097 / 200000000) (82492743 / 500000000) (Real.log (73711 / 62500)) := by
  have h := reflection_log_10481_neg
  have he : Real.log (73711 / 62500) = -Real.log (62500 / 73711) := by
    rw [show ((73711 / 62500) : ℝ) = ((62500 / 73711) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10482_neg : (49422563 / 250000000) ≤ -Real.log (51289 / 62500) ∧
    -Real.log (51289 / 62500) ≤ (197690253 / 1000000000) := by
  have h := checkLog_sound (w := (11211 / 113789)) (n := 12)
    (lo := (49422563 / 250000000)) (hi := (197690253 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 51289) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 51289) = 1/(51289 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10482 : Bounds (-197690253 / 1000000000) (-49422563 / 250000000) (Real.log (51289 / 62500)) := by
  have h := reflection_log_10482_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10483_neg : (41432629 / 250000000) ≤ -Real.log (200000 / 236051) ∧
    -Real.log (200000 / 236051) ≤ (165730517 / 1000000000) := by
  have h := checkLog_sound (w := (36051 / 436051)) (n := 12)
    (lo := (41432629 / 250000000)) (hi := (165730517 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((236051 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(236051 / 200000) = 1/(200000 / 236051) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10483 : Bounds (41432629 / 250000000) (165730517 / 1000000000) (Real.log (236051 / 200000)) := by
  have h := reflection_log_10483_neg
  have he : Real.log (236051 / 200000) = -Real.log (200000 / 236051) := by
    rw [show ((236051 / 200000) : ℝ) = ((200000 / 236051) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10484_neg : (99380981 / 500000000) ≤ -Real.log (163949 / 200000) ∧
    -Real.log (163949 / 200000) ≤ (198761963 / 1000000000) := by
  have h := checkLog_sound (w := (36051 / 363949)) (n := 12)
    (lo := (99380981 / 500000000)) (hi := (198761963 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 163949) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 163949) = 1/(163949 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10484 : Bounds (-198761963 / 1000000000) (-99380981 / 500000000) (Real.log (163949 / 200000)) := by
  have h := reflection_log_10484_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10485_neg : (6606289 / 200000000) ≤ -Real.log (38700325399 / 40000000000) ∧
    -Real.log (38700325399 / 40000000000) ≤ (16515723 / 500000000) := by
  have h := checkLog_sound (w := (1299674601 / 78700325399)) (n := 12)
    (lo := (6606289 / 200000000)) (hi := (16515723 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 38700325399) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 38700325399) = 1/(38700325399 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10485 : Bounds (-16515723 / 500000000) (-6606289 / 200000000) (Real.log (38700325399 / 40000000000)) := by
  have h := reflection_log_10485_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10486_neg : (32704767 / 1000000000) ≤ -Real.log (3780563479 / 3906250000) ∧
    -Real.log (3780563479 / 3906250000) ≤ (127753 / 3906250) := by
  have h := checkLog_sound (w := (125686521 / 7686813479)) (n := 12)
    (lo := (32704767 / 1000000000)) (hi := (127753 / 3906250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3906250000 / 3780563479) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3906250000 / 3780563479) = 1/(3780563479 / 3906250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10486 : Bounds (-127753 / 3906250) (-32704767 / 1000000000) (Real.log (3780563479 / 3906250000)) := by
  have h := reflection_log_10486_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10487_neg : (362675737 / 1000000000) ≤ -Real.log (125000000000 / 179646220437) ∧
    -Real.log (125000000000 / 179646220437) ≤ (181337869 / 500000000) := by
  have h := checkLog_sound (w := (54646220437 / 304646220437)) (n := 12)
    (lo := (362675737 / 1000000000)) (hi := (181337869 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((179646220437 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(179646220437 / 125000000000) = 1/(125000000000 / 179646220437) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10487 : Bounds (362675737 / 1000000000) (181337869 / 500000000) (Real.log (179646220437 / 125000000000)) := by
  have h := reflection_log_10487_neg
  have he : Real.log (179646220437 / 125000000000) = -Real.log (125000000000 / 179646220437) := by
    rw [show ((179646220437 / 125000000000) : ℝ) = ((125000000000 / 179646220437) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10488_neg : (364492479 / 1000000000) ≤ -Real.log (250000000000 / 359945775821) ∧
    -Real.log (250000000000 / 359945775821) ≤ (1139039 / 3125000) := by
  have h := checkLog_sound (w := (109945775821 / 609945775821)) (n := 12)
    (lo := (364492479 / 1000000000)) (hi := (1139039 / 3125000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((359945775821 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(359945775821 / 250000000000) = 1/(250000000000 / 359945775821) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10488 : Bounds (364492479 / 1000000000) (1139039 / 3125000) (Real.log (359945775821 / 250000000000)) := by
  have h := reflection_log_10488_neg
  have he : Real.log (359945775821 / 250000000000) = -Real.log (250000000000 / 359945775821) := by
    rw [show ((359945775821 / 250000000000) : ℝ) = ((250000000000 / 359945775821) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10489_neg : (36658381 / 50000000) ≤ -Real.log (250000000000 / 520416024653) ∧
    -Real.log (250000000000 / 520416024653) ≤ (366583811 / 500000000) := by
  have h := checkLog_sound (w := (20416024653 / 1020416024653)) (n := 12)
    (lo := (1000511 / 25000000)) (hi := (40020441 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((520416024653 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(520416024653 / 500000000000) = 1/(250000000000 / 520416024653) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10489 : Bounds (36658381 / 50000000) (366583811 / 500000000) (Real.log (520416024653 / 250000000000)) := by
  have h := reflection_log_10489_neg
  have he : Real.log (520416024653 / 250000000000) = -Real.log (250000000000 / 520416024653) := by
    rw [show ((520416024653 / 250000000000) : ℝ) = ((250000000000 / 520416024653) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10490_neg : (735449559 / 1000000000) ≤ -Real.log (7812500000 / 16300154321) ∧
    -Real.log (7812500000 / 16300154321) ≤ (735449561 / 1000000000) := by
  have h := checkLog_sound (w := (675154321 / 31925154321)) (n := 12)
    (lo := (42302379 / 1000000000)) (hi := (2115119 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((16300154321 / 15625000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(16300154321 / 15625000000) = 1/(7812500000 / 16300154321) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10490 : Bounds (735449559 / 1000000000) (735449561 / 1000000000) (Real.log (16300154321 / 7812500000)) := by
  have h := reflection_log_10490_neg
  have he : Real.log (16300154321 / 7812500000) = -Real.log (7812500000 / 16300154321) := by
    rw [show ((16300154321 / 7812500000) : ℝ) = ((7812500000 / 16300154321) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10491_neg : (302324349 / 1000000000) ≤ -Real.log (1000 / 1353) ∧
    -Real.log (1000 / 1353) ≤ (6046487 / 20000000) := by
  have h := checkLog_sound (w := (353 / 2353)) (n := 12)
    (lo := (302324349 / 1000000000)) (hi := (6046487 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1353 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1353 / 1000) = 1/(1000 / 1353) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10491 : Bounds (302324349 / 1000000000) (6046487 / 20000000) (Real.log (1353 / 1000)) := by
  have h := reflection_log_10491_neg
  have he : Real.log (1353 / 1000) = -Real.log (1000 / 1353) := by
    rw [show ((1353 / 1000) : ℝ) = ((1000 / 1353) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10492_neg : (54426123 / 125000000) ≤ -Real.log (647 / 1000) ∧
    -Real.log (647 / 1000) ≤ (87081797 / 200000000) := by
  have h := checkLog_sound (w := (353 / 1647)) (n := 12)
    (lo := (54426123 / 125000000)) (hi := (87081797 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 647) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 647) = 1/(647 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10492 : Bounds (-87081797 / 200000000) (-54426123 / 125000000) (Real.log (647 / 1000)) := by
  have h := reflection_log_10492_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10493_neg : (352937 / 1000000000) ≤ -Real.log (1000000 / 1000353) ∧
    -Real.log (1000000 / 1000353) ≤ (176469 / 500000000) := by
  have h := checkLog_sound (w := (353 / 2000353)) (n := 12)
    (lo := (352937 / 1000000000)) (hi := (176469 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000353 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000353 / 1000000) = 1/(1000000 / 1000353) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10493 : Bounds (352937 / 1000000000) (176469 / 500000000) (Real.log (1000353 / 1000000)) := by
  have h := reflection_log_10493_neg
  have he : Real.log (1000353 / 1000000) = -Real.log (1000000 / 1000353) := by
    rw [show ((1000353 / 1000000) : ℝ) = ((1000000 / 1000353) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10494_neg : (176531 / 500000000) ≤ -Real.log (999647 / 1000000) ∧
    -Real.log (999647 / 1000000) ≤ (353063 / 1000000000) := by
  have h := checkLog_sound (w := (353 / 1999647)) (n := 12)
    (lo := (176531 / 500000000)) (hi := (353063 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999647) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999647) = 1/(999647 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10494 : Bounds (-353063 / 1000000000) (-176531 / 500000000) (Real.log (999647 / 1000000)) := by
  have h := reflection_log_10494_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10495_neg : (165439011 / 1000000000) ≤ -Real.log (1000000 / 1179911) ∧
    -Real.log (1000000 / 1179911) ≤ (41359753 / 250000000) := by
  have h := checkLog_sound (w := (179911 / 2179911)) (n := 12)
    (lo := (165439011 / 1000000000)) (hi := (41359753 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1179911 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1179911 / 1000000) = 1/(1000000 / 1179911) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10495 : Bounds (165439011 / 1000000000) (41359753 / 250000000) (Real.log (1179911 / 1000000)) := by
  have h := reflection_log_10495_neg
  have he : Real.log (1179911 / 1000000) = -Real.log (1000000 / 1179911) := by
    rw [show ((1179911 / 1000000) : ℝ) = ((1000000 / 1179911) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily
