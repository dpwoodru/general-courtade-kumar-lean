import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_1472_neg : (40203 / 250000000) ≤ -Real.log (1249799 / 1250000) ∧
    -Real.log (1249799 / 1250000) ≤ (160813 / 1000000000) := by
  have h := checkLog_sound (w := (201 / 2499799)) (n := 12)
    (lo := (40203 / 250000000)) (hi := (160813 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250000 / 1249799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1250000 / 1249799) = 1/(1249799 / 1250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1472 : Bounds (-160813 / 1000000000) (-40203 / 250000000) (Real.log (1249799 / 1250000)) := by
  have h := reflection_log_1472_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1473_neg : (15511987 / 200000000) ≤ -Real.log (1000000 / 1080647) ∧
    -Real.log (1000000 / 1080647) ≤ (605937 / 7812500) := by
  have h := checkLog_sound (w := (80647 / 2080647)) (n := 12)
    (lo := (15511987 / 200000000)) (hi := (605937 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1080647 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1080647 / 1000000) = 1/(1000000 / 1080647) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1473 : Bounds (15511987 / 200000000) (605937 / 7812500) (Real.log (1080647 / 1000000)) := by
  have h := reflection_log_1473_neg
  have he : Real.log (1080647 / 1000000) = -Real.log (1000000 / 1080647) := by
    rw [show ((1080647 / 1000000) : ℝ) = ((1000000 / 1080647) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1474_neg : (84085117 / 1000000000) ≤ -Real.log (919353 / 1000000) ∧
    -Real.log (919353 / 1000000) ≤ (42042559 / 500000000) := by
  have h := checkLog_sound (w := (80647 / 1919353)) (n := 12)
    (lo := (84085117 / 1000000000)) (hi := (42042559 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 919353) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 919353) = 1/(919353 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1474 : Bounds (-42042559 / 500000000) (-84085117 / 1000000000) (Real.log (919353 / 1000000)) := by
  have h := reflection_log_1474_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1475_neg : (7775517 / 100000000) ≤ -Real.log (500000 / 540429) ∧
    -Real.log (500000 / 540429) ≤ (77755171 / 1000000000) := by
  have h := checkLog_sound (w := (40429 / 1040429)) (n := 12)
    (lo := (7775517 / 100000000)) (hi := (77755171 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((540429 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(540429 / 500000) = 1/(500000 / 540429) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1475 : Bounds (7775517 / 100000000) (77755171 / 1000000000) (Real.log (540429 / 500000)) := by
  have h := reflection_log_1475_neg
  have he : Real.log (540429 / 500000) = -Real.log (500000 / 540429) := by
    rw [show ((540429 / 500000) : ℝ) = ((500000 / 540429) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1476_neg : (21078663 / 250000000) ≤ -Real.log (459571 / 500000) ∧
    -Real.log (459571 / 500000) ≤ (84314653 / 1000000000) := by
  have h := checkLog_sound (w := (40429 / 959571)) (n := 12)
    (lo := (21078663 / 250000000)) (hi := (84314653 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 459571) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 459571) = 1/(459571 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1476 : Bounds (-84314653 / 1000000000) (-21078663 / 250000000) (Real.log (459571 / 500000)) := by
  have h := reflection_log_1476_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1477_neg : (3279741 / 500000000) ≤ -Real.log (248365495959 / 250000000000) ∧
    -Real.log (248365495959 / 250000000000) ≤ (6559483 / 1000000000) := by
  have h := checkLog_sound (w := (1634504041 / 498365495959)) (n := 12)
    (lo := (3279741 / 500000000)) (hi := (6559483 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248365495959) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248365495959) = 1/(248365495959 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1477 : Bounds (-6559483 / 1000000000) (-3279741 / 500000000) (Real.log (248365495959 / 250000000000)) := by
  have h := reflection_log_1477_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1478_neg : (6525181 / 1000000000) ≤ -Real.log (993496061391 / 1000000000000) ∧
    -Real.log (993496061391 / 1000000000000) ≤ (3262591 / 500000000) := by
  have h := checkLog_sound (w := (6503938609 / 1993496061391)) (n := 12)
    (lo := (6525181 / 1000000000)) (hi := (3262591 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993496061391) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993496061391) = 1/(993496061391 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1478 : Bounds (-3262591 / 500000000) (-6525181 / 1000000000) (Real.log (993496061391 / 1000000000000)) := by
  have h := reflection_log_1478_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1479_neg : (161645053 / 1000000000) ≤ -Real.log (62500000000 / 73465184211) ∧
    -Real.log (62500000000 / 73465184211) ≤ (80822527 / 500000000) := by
  have h := checkLog_sound (w := (10965184211 / 135965184211)) (n := 12)
    (lo := (161645053 / 1000000000)) (hi := (80822527 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((73465184211 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(73465184211 / 62500000000) = 1/(62500000000 / 73465184211) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1479 : Bounds (161645053 / 1000000000) (80822527 / 500000000) (Real.log (73465184211 / 62500000000)) := by
  have h := reflection_log_1479_neg
  have he : Real.log (73465184211 / 62500000000) = -Real.log (62500000000 / 73465184211) := by
    rw [show ((73465184211 / 62500000000) : ℝ) = ((62500000000 / 73465184211) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1480_neg : (81034911 / 500000000) ≤ -Real.log (125000000000 / 146992793279) ∧
    -Real.log (125000000000 / 146992793279) ≤ (162069823 / 1000000000) := by
  have h := checkLog_sound (w := (21992793279 / 271992793279)) (n := 12)
    (lo := (81034911 / 500000000)) (hi := (162069823 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((146992793279 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(146992793279 / 125000000000) = 1/(125000000000 / 146992793279) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1480 : Bounds (81034911 / 500000000) (162069823 / 1000000000) (Real.log (146992793279 / 125000000000)) := by
  have h := reflection_log_1480_neg
  have he : Real.log (146992793279 / 125000000000) = -Real.log (125000000000 / 146992793279) := by
    rw [show ((146992793279 / 125000000000) : ℝ) = ((125000000000 / 146992793279) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1481_neg : (324210339 / 1000000000) ≤ -Real.log (500000000000 / 691469081377) ∧
    -Real.log (500000000000 / 691469081377) ≤ (16210517 / 50000000) := by
  have h := checkLog_sound (w := (191469081377 / 1191469081377)) (n := 12)
    (lo := (324210339 / 1000000000)) (hi := (16210517 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((691469081377 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(691469081377 / 500000000000) = 1/(500000000000 / 691469081377) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1481 : Bounds (324210339 / 1000000000) (16210517 / 50000000) (Real.log (691469081377 / 500000000000)) := by
  have h := reflection_log_1481_neg
  have he : Real.log (691469081377 / 500000000000) = -Real.log (500000000000 / 691469081377) := by
    rw [show ((691469081377 / 500000000000) : ℝ) = ((500000000000 / 691469081377) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1482_neg : (81103911 / 250000000) ≤ -Real.log (500000000000 / 691611058151) ∧
    -Real.log (500000000000 / 691611058151) ≤ (64883129 / 200000000) := by
  have h := checkLog_sound (w := (191611058151 / 1191611058151)) (n := 12)
    (lo := (81103911 / 250000000)) (hi := (64883129 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((691611058151 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(691611058151 / 500000000000) = 1/(500000000000 / 691611058151) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1482 : Bounds (81103911 / 250000000) (64883129 / 200000000) (Real.log (691611058151 / 500000000000)) := by
  have h := reflection_log_1482_neg
  have he : Real.log (691611058151 / 500000000000) = -Real.log (500000000000 / 691611058151) := by
    rw [show ((691611058151 / 500000000000) : ℝ) = ((500000000000 / 691611058151) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1483_neg : (74597783 / 500000000) ≤ -Real.log (10000 / 11609) ∧
    -Real.log (10000 / 11609) ≤ (149195567 / 1000000000) := by
  have h := checkLog_sound (w := (1609 / 21609)) (n := 12)
    (lo := (74597783 / 500000000)) (hi := (149195567 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11609 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11609 / 10000) = 1/(10000 / 11609) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1483 : Bounds (74597783 / 500000000) (149195567 / 1000000000) (Real.log (11609 / 10000)) := by
  have h := reflection_log_1483_neg
  have he : Real.log (11609 / 10000) = -Real.log (10000 / 11609) := by
    rw [show ((11609 / 10000) : ℝ) = ((10000 / 11609) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1484_neg : (17542539 / 100000000) ≤ -Real.log (8391 / 10000) ∧
    -Real.log (8391 / 10000) ≤ (175425391 / 1000000000) := by
  have h := checkLog_sound (w := (1609 / 18391)) (n := 12)
    (lo := (17542539 / 100000000)) (hi := (175425391 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8391) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8391) = 1/(8391 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1484 : Bounds (-175425391 / 1000000000) (-17542539 / 100000000) (Real.log (8391 / 10000)) := by
  have h := reflection_log_1484_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1485_neg : (160887 / 1000000000) ≤ -Real.log (10000000 / 10001609) ∧
    -Real.log (10000000 / 10001609) ≤ (20111 / 125000000) := by
  have h := checkLog_sound (w := (1609 / 20001609)) (n := 12)
    (lo := (160887 / 1000000000)) (hi := (20111 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001609 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001609 / 10000000) = 1/(10000000 / 10001609) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1485 : Bounds (160887 / 1000000000) (20111 / 125000000) (Real.log (10001609 / 10000000)) := by
  have h := reflection_log_1485_neg
  have he : Real.log (10001609 / 10000000) = -Real.log (10000000 / 10001609) := by
    rw [show ((10001609 / 10000000) : ℝ) = ((10000000 / 10001609) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1486_neg : (10057 / 62500000) ≤ -Real.log (9998391 / 10000000) ∧
    -Real.log (9998391 / 10000000) ≤ (160913 / 1000000000) := by
  have h := checkLog_sound (w := (1609 / 19998391)) (n := 12)
    (lo := (10057 / 62500000)) (hi := (160913 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998391) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998391) = 1/(9998391 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1486 : Bounds (-160913 / 1000000000) (-10057 / 62500000) (Real.log (9998391 / 10000000)) := by
  have h := reflection_log_1486_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1487_neg : (77606203 / 1000000000) ≤ -Real.log (1000000 / 1080697) ∧
    -Real.log (1000000 / 1080697) ≤ (19401551 / 250000000) := by
  have h := checkLog_sound (w := (80697 / 2080697)) (n := 12)
    (lo := (77606203 / 1000000000)) (hi := (19401551 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1080697 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1080697 / 1000000) = 1/(1000000 / 1080697) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1487 : Bounds (77606203 / 1000000000) (19401551 / 250000000) (Real.log (1080697 / 1000000)) := by
  have h := reflection_log_1487_neg
  have he : Real.log (1080697 / 1000000) = -Real.log (1000000 / 1080697) := by
    rw [show ((1080697 / 1000000) : ℝ) = ((1000000 / 1080697) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1488_neg : (5258719 / 62500000) ≤ -Real.log (919303 / 1000000) ∧
    -Real.log (919303 / 1000000) ≤ (16827901 / 200000000) := by
  have h := checkLog_sound (w := (80697 / 1919303)) (n := 12)
    (lo := (5258719 / 62500000)) (hi := (16827901 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 919303) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 919303) = 1/(919303 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1488 : Bounds (-16827901 / 200000000) (-5258719 / 62500000) (Real.log (919303 / 1000000)) := by
  have h := reflection_log_1488_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1489_neg : (77802353 / 1000000000) ≤ -Real.log (1000000 / 1080909) ∧
    -Real.log (1000000 / 1080909) ≤ (38901177 / 500000000) := by
  have h := checkLog_sound (w := (80909 / 2080909)) (n := 12)
    (lo := (77802353 / 1000000000)) (hi := (38901177 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1080909 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1080909 / 1000000) = 1/(1000000 / 1080909) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1489 : Bounds (77802353 / 1000000000) (38901177 / 500000000) (Real.log (1080909 / 1000000)) := by
  have h := reflection_log_1489_neg
  have he : Real.log (1080909 / 1000000) = -Real.log (1000000 / 1080909) := by
    rw [show ((1080909 / 1000000) : ℝ) = ((1000000 / 1080909) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1490_neg : (4218507 / 50000000) ≤ -Real.log (919091 / 1000000) ∧
    -Real.log (919091 / 1000000) ≤ (84370141 / 1000000000) := by
  have h := checkLog_sound (w := (80909 / 1919091)) (n := 12)
    (lo := (4218507 / 50000000)) (hi := (84370141 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 919091) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 919091) = 1/(919091 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1490 : Bounds (-84370141 / 1000000000) (-4218507 / 50000000) (Real.log (919091 / 1000000)) := by
  have h := reflection_log_1490_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1491_neg : (6567787 / 1000000000) ≤ -Real.log (993453733719 / 1000000000000) ∧
    -Real.log (993453733719 / 1000000000000) ≤ (1641947 / 250000000) := by
  have h := checkLog_sound (w := (6546266281 / 1993453733719)) (n := 12)
    (lo := (6567787 / 1000000000)) (hi := (1641947 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993453733719) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993453733719) = 1/(993453733719 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1491 : Bounds (-1641947 / 250000000) (-6567787 / 1000000000) (Real.log (993453733719 / 1000000000000)) := by
  have h := reflection_log_1491_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1492_neg : (6533301 / 1000000000) ≤ -Real.log (993487994191 / 1000000000000) ∧
    -Real.log (993487994191 / 1000000000000) ≤ (3266651 / 500000000) := by
  have h := checkLog_sound (w := (6512005809 / 1993487994191)) (n := 12)
    (lo := (6533301 / 1000000000)) (hi := (3266651 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993487994191) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993487994191) = 1/(993487994191 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1492 : Bounds (-3266651 / 500000000) (-6533301 / 1000000000) (Real.log (993487994191 / 1000000000000)) := by
  have h := reflection_log_1492_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1493_neg : (40436427 / 250000000) ≤ -Real.log (250000000000 / 293890316903) ∧
    -Real.log (250000000000 / 293890316903) ≤ (161745709 / 1000000000) := by
  have h := checkLog_sound (w := (43890316903 / 543890316903)) (n := 12)
    (lo := (40436427 / 250000000)) (hi := (161745709 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((293890316903 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(293890316903 / 250000000000) = 1/(250000000000 / 293890316903) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1493 : Bounds (40436427 / 250000000) (161745709 / 1000000000) (Real.log (293890316903 / 250000000000)) := by
  have h := reflection_log_1493_neg
  have he : Real.log (293890316903 / 250000000000) = -Real.log (250000000000 / 293890316903) := by
    rw [show ((293890316903 / 250000000000) : ℝ) = ((250000000000 / 293890316903) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1494_neg : (81086247 / 500000000) ≤ -Real.log (500000000000 / 588031544211) ∧
    -Real.log (500000000000 / 588031544211) ≤ (32434499 / 200000000) := by
  have h := checkLog_sound (w := (88031544211 / 1088031544211)) (n := 12)
    (lo := (81086247 / 500000000)) (hi := (32434499 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((588031544211 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(588031544211 / 500000000000) = 1/(500000000000 / 588031544211) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1494 : Bounds (81086247 / 500000000) (32434499 / 200000000) (Real.log (588031544211 / 500000000000)) := by
  have h := reflection_log_1494_neg
  have he : Real.log (588031544211 / 500000000000) = -Real.log (500000000000 / 588031544211) := by
    rw [show ((588031544211 / 500000000000) : ℝ) = ((500000000000 / 588031544211) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1495_neg : (81103911 / 250000000) ≤ -Real.log (10000000000 / 13832221163) ∧
    -Real.log (10000000000 / 13832221163) ≤ (64883129 / 200000000) := by
  have h := checkLog_sound (w := (3832221163 / 23832221163)) (n := 12)
    (lo := (81103911 / 250000000)) (hi := (64883129 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((13832221163 / 10000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(13832221163 / 10000000000) = 1/(10000000000 / 13832221163) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1495 : Bounds (81103911 / 250000000) (64883129 / 200000000) (Real.log (13832221163 / 10000000000)) := by
  have h := reflection_log_1495_neg
  have he : Real.log (13832221163 / 10000000000) = -Real.log (10000000000 / 13832221163) := by
    rw [show ((13832221163 / 10000000000) : ℝ) = ((10000000000 / 13832221163) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1496_neg : (81155239 / 250000000) ≤ -Real.log (100000000000 / 138350613753) ∧
    -Real.log (100000000000 / 138350613753) ≤ (324620957 / 1000000000) := by
  have h := checkLog_sound (w := (38350613753 / 238350613753)) (n := 12)
    (lo := (81155239 / 250000000)) (hi := (324620957 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((138350613753 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(138350613753 / 100000000000) = 1/(100000000000 / 138350613753) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1496 : Bounds (81155239 / 250000000) (324620957 / 1000000000) (Real.log (138350613753 / 100000000000)) := by
  have h := reflection_log_1496_neg
  have he : Real.log (138350613753 / 100000000000) = -Real.log (100000000000 / 138350613753) := by
    rw [show ((138350613753 / 100000000000) : ℝ) = ((100000000000 / 138350613753) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1497_neg : (74640851 / 500000000) ≤ -Real.log (1000 / 1161) ∧
    -Real.log (1000 / 1161) ≤ (149281703 / 1000000000) := by
  have h := checkLog_sound (w := (161 / 2161)) (n := 12)
    (lo := (74640851 / 500000000)) (hi := (149281703 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1161 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1161 / 1000) = 1/(1000 / 1161) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1497 : Bounds (74640851 / 500000000) (149281703 / 1000000000) (Real.log (1161 / 1000)) := by
  have h := reflection_log_1497_neg
  have he : Real.log (1161 / 1000) = -Real.log (1000 / 1161) := by
    rw [show ((1161 / 1000) : ℝ) = ((1000 / 1161) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1498_neg : (43886143 / 250000000) ≤ -Real.log (839 / 1000) ∧
    -Real.log (839 / 1000) ≤ (175544573 / 1000000000) := by
  have h := checkLog_sound (w := (161 / 1839)) (n := 12)
    (lo := (43886143 / 250000000)) (hi := (175544573 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 839) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 839) = 1/(839 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1498 : Bounds (-175544573 / 1000000000) (-43886143 / 250000000) (Real.log (839 / 1000)) := by
  have h := reflection_log_1498_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1499_neg : (160987 / 1000000000) ≤ -Real.log (1000000 / 1000161) ∧
    -Real.log (1000000 / 1000161) ≤ (40247 / 250000000) := by
  have h := checkLog_sound (w := (161 / 2000161)) (n := 12)
    (lo := (160987 / 1000000000)) (hi := (40247 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000161 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000161 / 1000000) = 1/(1000000 / 1000161) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1499 : Bounds (160987 / 1000000000) (40247 / 250000000) (Real.log (1000161 / 1000000)) := by
  have h := reflection_log_1499_neg
  have he : Real.log (1000161 / 1000000) = -Real.log (1000000 / 1000161) := by
    rw [show ((1000161 / 1000000) : ℝ) = ((1000000 / 1000161) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1500_neg : (40253 / 250000000) ≤ -Real.log (999839 / 1000000) ∧
    -Real.log (999839 / 1000000) ≤ (161013 / 1000000000) := by
  have h := checkLog_sound (w := (161 / 1999839)) (n := 12)
    (lo := (40253 / 250000000)) (hi := (161013 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999839) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999839) = 1/(999839 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1500 : Bounds (-161013 / 1000000000) (-40253 / 250000000) (Real.log (999839 / 1000000)) := by
  have h := reflection_log_1500_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1501_neg : (77653393 / 1000000000) ≤ -Real.log (250000 / 270187) ∧
    -Real.log (250000 / 270187) ≤ (38826697 / 500000000) := by
  have h := checkLog_sound (w := (20187 / 520187)) (n := 12)
    (lo := (77653393 / 1000000000)) (hi := (38826697 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((270187 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(270187 / 250000) = 1/(250000 / 270187) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1501 : Bounds (77653393 / 1000000000) (38826697 / 500000000) (Real.log (270187 / 250000)) := by
  have h := reflection_log_1501_neg
  have he : Real.log (270187 / 250000) = -Real.log (250000 / 270187) := by
    rw [show ((270187 / 250000) : ℝ) = ((250000 / 270187) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1502_neg : (84194983 / 1000000000) ≤ -Real.log (229813 / 250000) ∧
    -Real.log (229813 / 250000) ≤ (10524373 / 125000000) := by
  have h := checkLog_sound (w := (20187 / 479813)) (n := 12)
    (lo := (84194983 / 1000000000)) (hi := (10524373 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 229813) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 229813) = 1/(229813 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1502 : Bounds (-10524373 / 125000000) (-84194983 / 1000000000) (Real.log (229813 / 250000)) := by
  have h := reflection_log_1502_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1503_neg : (15569907 / 200000000) ≤ -Real.log (3125 / 3378) ∧
    -Real.log (3125 / 3378) ≤ (1216399 / 15625000) := by
  have h := checkLog_sound (w := (253 / 6503)) (n := 12)
    (lo := (15569907 / 200000000)) (hi := (1216399 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3378 / 3125) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3378 / 3125) = 1/(3125 / 3378) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1503 : Bounds (15569907 / 200000000) (1216399 / 15625000) (Real.log (3378 / 3125)) := by
  have h := reflection_log_1503_neg
  have he : Real.log (3378 / 3125) = -Real.log (3125 / 3378) := by
    rw [show ((3378 / 3125) : ℝ) = ((3125 / 3378) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1504_neg : (2638301 / 31250000) ≤ -Real.log (2872 / 3125) ∧
    -Real.log (2872 / 3125) ≤ (84425633 / 1000000000) := by
  have h := checkLog_sound (w := (253 / 5997)) (n := 12)
    (lo := (2638301 / 31250000)) (hi := (84425633 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3125 / 2872) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3125 / 2872) = 1/(2872 / 3125) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1504 : Bounds (-84425633 / 1000000000) (-2638301 / 31250000) (Real.log (2872 / 3125)) := by
  have h := reflection_log_1504_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1505_neg : (205503 / 31250000) ≤ -Real.log (9701616 / 9765625) ∧
    -Real.log (9701616 / 9765625) ≤ (6576097 / 1000000000) := by
  have h := checkLog_sound (w := (64009 / 19467241)) (n := 12)
    (lo := (205503 / 31250000)) (hi := (6576097 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9765625 / 9701616) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(9765625 / 9701616) = 1/(9701616 / 9765625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1505 : Bounds (-6576097 / 1000000000) (-205503 / 31250000) (Real.log (9701616 / 9765625)) := by
  have h := reflection_log_1505_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1506_neg : (6541589 / 1000000000) ≤ -Real.log (62092485031 / 62500000000) ∧
    -Real.log (62092485031 / 62500000000) ≤ (654159 / 100000000) := by
  have h := checkLog_sound (w := (407514969 / 124592485031)) (n := 12)
    (lo := (6541589 / 1000000000)) (hi := (654159 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 62092485031) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 62092485031) = 1/(62092485031 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1506 : Bounds (-654159 / 100000000) (-6541589 / 1000000000) (Real.log (62092485031 / 62500000000)) := by
  have h := reflection_log_1506_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1507_neg : (161848377 / 1000000000) ≤ -Real.log (125000000000 / 146960245939) ∧
    -Real.log (125000000000 / 146960245939) ≤ (80924189 / 500000000) := by
  have h := checkLog_sound (w := (21960245939 / 271960245939)) (n := 12)
    (lo := (161848377 / 1000000000)) (hi := (80924189 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((146960245939 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(146960245939 / 125000000000) = 1/(125000000000 / 146960245939) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1507 : Bounds (161848377 / 1000000000) (80924189 / 500000000) (Real.log (146960245939 / 125000000000)) := by
  have h := reflection_log_1507_neg
  have he : Real.log (146960245939 / 125000000000) = -Real.log (125000000000 / 146960245939) := by
    rw [show ((146960245939 / 125000000000) : ℝ) = ((125000000000 / 146960245939) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1508_neg : (162275167 / 1000000000) ≤ -Real.log (250000000000 / 294045961003) ∧
    -Real.log (250000000000 / 294045961003) ≤ (5071099 / 31250000) := by
  have h := checkLog_sound (w := (44045961003 / 544045961003)) (n := 12)
    (lo := (162275167 / 1000000000)) (hi := (5071099 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((294045961003 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(294045961003 / 250000000000) = 1/(250000000000 / 294045961003) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1508 : Bounds (162275167 / 1000000000) (5071099 / 31250000) (Real.log (294045961003 / 250000000000)) := by
  have h := reflection_log_1508_neg
  have he : Real.log (294045961003 / 250000000000) = -Real.log (250000000000 / 294045961003) := by
    rw [show ((294045961003 / 250000000000) : ℝ) = ((250000000000 / 294045961003) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1509_neg : (81155239 / 250000000) ≤ -Real.log (125000000000 / 172938267191) ∧
    -Real.log (125000000000 / 172938267191) ≤ (324620957 / 1000000000) := by
  have h := checkLog_sound (w := (47938267191 / 297938267191)) (n := 12)
    (lo := (81155239 / 250000000)) (hi := (324620957 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((172938267191 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(172938267191 / 125000000000) = 1/(125000000000 / 172938267191) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1509 : Bounds (81155239 / 250000000) (324620957 / 1000000000) (Real.log (172938267191 / 125000000000)) := by
  have h := reflection_log_1509_neg
  have he : Real.log (172938267191 / 125000000000) = -Real.log (125000000000 / 172938267191) := by
    rw [show ((172938267191 / 125000000000) : ℝ) = ((125000000000 / 172938267191) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1510_neg : (12993051 / 40000000) ≤ -Real.log (500000000000 / 691895113231) ∧
    -Real.log (500000000000 / 691895113231) ≤ (81206569 / 250000000) := by
  have h := checkLog_sound (w := (191895113231 / 1191895113231)) (n := 12)
    (lo := (12993051 / 40000000)) (hi := (81206569 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((691895113231 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(691895113231 / 500000000000) = 1/(500000000000 / 691895113231) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1510 : Bounds (12993051 / 40000000) (81206569 / 250000000) (Real.log (691895113231 / 500000000000)) := by
  have h := reflection_log_1510_neg
  have he : Real.log (691895113231 / 500000000000) = -Real.log (500000000000 / 691895113231) := by
    rw [show ((691895113231 / 500000000000) : ℝ) = ((500000000000 / 691895113231) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1511_neg : (149367831 / 1000000000) ≤ -Real.log (10000 / 11611) ∧
    -Real.log (10000 / 11611) ≤ (18670979 / 125000000) := by
  have h := checkLog_sound (w := (1611 / 21611)) (n := 12)
    (lo := (149367831 / 1000000000)) (hi := (18670979 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11611 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11611 / 10000) = 1/(10000 / 11611) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1511 : Bounds (149367831 / 1000000000) (18670979 / 125000000) (Real.log (11611 / 10000)) := by
  have h := reflection_log_1511_neg
  have he : Real.log (11611 / 10000) = -Real.log (10000 / 11611) := by
    rw [show ((11611 / 10000) : ℝ) = ((10000 / 11611) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1512_neg : (175663769 / 1000000000) ≤ -Real.log (8389 / 10000) ∧
    -Real.log (8389 / 10000) ≤ (17566377 / 100000000) := by
  have h := checkLog_sound (w := (1611 / 18389)) (n := 12)
    (lo := (175663769 / 1000000000)) (hi := (17566377 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8389) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8389) = 1/(8389 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1512 : Bounds (-17566377 / 100000000) (-175663769 / 1000000000) (Real.log (8389 / 10000)) := by
  have h := reflection_log_1512_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1513_neg : (161087 / 1000000000) ≤ -Real.log (10000000 / 10001611) ∧
    -Real.log (10000000 / 10001611) ≤ (2517 / 15625000) := by
  have h := checkLog_sound (w := (1611 / 20001611)) (n := 12)
    (lo := (161087 / 1000000000)) (hi := (2517 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001611 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001611 / 10000000) = 1/(10000000 / 10001611) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1513 : Bounds (161087 / 1000000000) (2517 / 15625000) (Real.log (10001611 / 10000000)) := by
  have h := reflection_log_1513_neg
  have he : Real.log (10001611 / 10000000) = -Real.log (10000000 / 10001611) := by
    rw [show ((10001611 / 10000000) : ℝ) = ((10000000 / 10001611) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1514_neg : (20139 / 125000000) ≤ -Real.log (9998389 / 10000000) ∧
    -Real.log (9998389 / 10000000) ≤ (161113 / 1000000000) := by
  have h := checkLog_sound (w := (1611 / 19998389)) (n := 12)
    (lo := (20139 / 125000000)) (hi := (161113 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998389) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998389) = 1/(9998389 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1514 : Bounds (-161113 / 1000000000) (-20139 / 125000000) (Real.log (9998389 / 10000000)) := by
  have h := reflection_log_1514_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1515_neg : (38850291 / 500000000) ≤ -Real.log (1000000 / 1080799) ∧
    -Real.log (1000000 / 1080799) ≤ (77700583 / 1000000000) := by
  have h := checkLog_sound (w := (80799 / 2080799)) (n := 12)
    (lo := (38850291 / 500000000)) (hi := (77700583 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1080799 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1080799 / 1000000) = 1/(1000000 / 1080799) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1515 : Bounds (38850291 / 500000000) (77700583 / 1000000000) (Real.log (1080799 / 1000000)) := by
  have h := reflection_log_1515_neg
  have he : Real.log (1080799 / 1000000) = -Real.log (1000000 / 1080799) := by
    rw [show ((1080799 / 1000000) : ℝ) = ((1000000 / 1080799) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1516_neg : (2632827 / 31250000) ≤ -Real.log (919201 / 1000000) ∧
    -Real.log (919201 / 1000000) ≤ (16850093 / 200000000) := by
  have h := checkLog_sound (w := (80799 / 1919201)) (n := 12)
    (lo := (2632827 / 31250000)) (hi := (16850093 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 919201) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 919201) = 1/(919201 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1516 : Bounds (-16850093 / 200000000) (-2632827 / 31250000) (Real.log (919201 / 1000000)) := by
  have h := reflection_log_1516_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1517_neg : (38948357 / 500000000) ≤ -Real.log (1000000 / 1081011) ∧
    -Real.log (1000000 / 1081011) ≤ (15579343 / 200000000) := by
  have h := checkLog_sound (w := (81011 / 2081011)) (n := 12)
    (lo := (38948357 / 500000000)) (hi := (15579343 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1081011 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1081011 / 1000000) = 1/(1000000 / 1081011) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1517 : Bounds (38948357 / 500000000) (15579343 / 200000000) (Real.log (1081011 / 1000000)) := by
  have h := reflection_log_1517_neg
  have he : Real.log (1081011 / 1000000) = -Real.log (1000000 / 1081011) := by
    rw [show ((1081011 / 1000000) : ℝ) = ((1000000 / 1081011) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1518_neg : (42240563 / 500000000) ≤ -Real.log (918989 / 1000000) ∧
    -Real.log (918989 / 1000000) ≤ (84481127 / 1000000000) := by
  have h := checkLog_sound (w := (81011 / 1918989)) (n := 12)
    (lo := (42240563 / 500000000)) (hi := (84481127 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 918989) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 918989) = 1/(918989 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1518 : Bounds (-84481127 / 1000000000) (-42240563 / 500000000) (Real.log (918989 / 1000000)) := by
  have h := reflection_log_1518_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1519_neg : (6584411 / 1000000000) ≤ -Real.log (993437217879 / 1000000000000) ∧
    -Real.log (993437217879 / 1000000000000) ≤ (1646103 / 250000000) := by
  have h := checkLog_sound (w := (6562782121 / 1993437217879)) (n := 12)
    (lo := (6584411 / 1000000000)) (hi := (1646103 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993437217879) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993437217879) = 1/(993437217879 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1519 : Bounds (-1646103 / 250000000) (-6584411 / 1000000000) (Real.log (993437217879 / 1000000000000)) := by
  have h := reflection_log_1519_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1520_neg : (3274941 / 500000000) ≤ -Real.log (993471521599 / 1000000000000) ∧
    -Real.log (993471521599 / 1000000000000) ≤ (6549883 / 1000000000) := by
  have h := checkLog_sound (w := (6528478401 / 1993471521599)) (n := 12)
    (lo := (3274941 / 500000000)) (hi := (6549883 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993471521599) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993471521599) = 1/(993471521599 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1520 : Bounds (-6549883 / 1000000000) (-3274941 / 500000000) (Real.log (993471521599 / 1000000000000)) := by
  have h := reflection_log_1520_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1521_neg : (80975523 / 500000000) ≤ -Real.log (500000000000 / 587901340403) ∧
    -Real.log (500000000000 / 587901340403) ≤ (161951047 / 1000000000) := by
  have h := checkLog_sound (w := (87901340403 / 1087901340403)) (n := 12)
    (lo := (80975523 / 500000000)) (hi := (161951047 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((587901340403 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(587901340403 / 500000000000) = 1/(500000000000 / 587901340403) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1521 : Bounds (80975523 / 500000000) (161951047 / 1000000000) (Real.log (587901340403 / 500000000000)) := by
  have h := reflection_log_1521_neg
  have he : Real.log (587901340403 / 500000000000) = -Real.log (500000000000 / 587901340403) := by
    rw [show ((587901340403 / 500000000000) : ℝ) = ((500000000000 / 587901340403) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1522_neg : (2029723 / 12500000) ≤ -Real.log (500000000000 / 588152306503) ∧
    -Real.log (500000000000 / 588152306503) ≤ (162377841 / 1000000000) := by
  have h := checkLog_sound (w := (88152306503 / 1088152306503)) (n := 12)
    (lo := (2029723 / 12500000)) (hi := (162377841 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((588152306503 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(588152306503 / 500000000000) = 1/(500000000000 / 588152306503) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1522 : Bounds (2029723 / 12500000) (162377841 / 1000000000) (Real.log (588152306503 / 500000000000)) := by
  have h := reflection_log_1522_neg
  have he : Real.log (588152306503 / 500000000000) = -Real.log (500000000000 / 588152306503) := by
    rw [show ((588152306503 / 500000000000) : ℝ) = ((500000000000 / 588152306503) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1523_neg : (12993051 / 40000000) ≤ -Real.log (50000000000 / 69189511323) ∧
    -Real.log (50000000000 / 69189511323) ≤ (81206569 / 250000000) := by
  have h := checkLog_sound (w := (19189511323 / 119189511323)) (n := 12)
    (lo := (12993051 / 40000000)) (hi := (81206569 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((69189511323 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(69189511323 / 50000000000) = 1/(50000000000 / 69189511323) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1523 : Bounds (12993051 / 40000000) (81206569 / 250000000) (Real.log (69189511323 / 50000000000)) := by
  have h := reflection_log_1523_neg
  have he : Real.log (69189511323 / 50000000000) = -Real.log (50000000000 / 69189511323) := by
    rw [show ((69189511323 / 50000000000) : ℝ) = ((50000000000 / 69189511323) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1524_neg : (812579 / 2500000) ≤ -Real.log (500000000000 / 692037191561) ∧
    -Real.log (500000000000 / 692037191561) ≤ (325031601 / 1000000000) := by
  have h := checkLog_sound (w := (192037191561 / 1192037191561)) (n := 12)
    (lo := (812579 / 2500000)) (hi := (325031601 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((692037191561 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(692037191561 / 500000000000) = 1/(500000000000 / 692037191561) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1524 : Bounds (812579 / 2500000) (325031601 / 1000000000) (Real.log (692037191561 / 500000000000)) := by
  have h := reflection_log_1524_neg
  have he : Real.log (692037191561 / 500000000000) = -Real.log (500000000000 / 692037191561) := by
    rw [show ((692037191561 / 500000000000) : ℝ) = ((500000000000 / 692037191561) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1525_neg : (149453953 / 1000000000) ≤ -Real.log (2500 / 2903) ∧
    -Real.log (2500 / 2903) ≤ (74726977 / 500000000) := by
  have h := checkLog_sound (w := (403 / 5403)) (n := 12)
    (lo := (149453953 / 1000000000)) (hi := (74726977 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2903 / 2500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2903 / 2500) = 1/(2500 / 2903) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1525 : Bounds (149453953 / 1000000000) (74726977 / 500000000) (Real.log (2903 / 2500)) := by
  have h := reflection_log_1525_neg
  have he : Real.log (2903 / 2500) = -Real.log (2500 / 2903) := by
    rw [show ((2903 / 2500) : ℝ) = ((2500 / 2903) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1526_neg : (175782979 / 1000000000) ≤ -Real.log (2097 / 2500) ∧
    -Real.log (2097 / 2500) ≤ (8789149 / 50000000) := by
  have h := checkLog_sound (w := (403 / 4597)) (n := 12)
    (lo := (175782979 / 1000000000)) (hi := (8789149 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500 / 2097) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500 / 2097) = 1/(2097 / 2500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1526 : Bounds (-8789149 / 50000000) (-175782979 / 1000000000) (Real.log (2097 / 2500)) := by
  have h := reflection_log_1526_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1527_neg : (161187 / 1000000000) ≤ -Real.log (2500000 / 2500403) ∧
    -Real.log (2500000 / 2500403) ≤ (40297 / 250000000) := by
  have h := checkLog_sound (w := (403 / 5000403)) (n := 12)
    (lo := (161187 / 1000000000)) (hi := (40297 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500403 / 2500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500403 / 2500000) = 1/(2500000 / 2500403) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1527 : Bounds (161187 / 1000000000) (40297 / 250000000) (Real.log (2500403 / 2500000)) := by
  have h := reflection_log_1527_neg
  have he : Real.log (2500403 / 2500000) = -Real.log (2500000 / 2500403) := by
    rw [show ((2500403 / 2500000) : ℝ) = ((2500000 / 2500403) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1528_neg : (40303 / 250000000) ≤ -Real.log (2499597 / 2500000) ∧
    -Real.log (2499597 / 2500000) ≤ (161213 / 1000000000) := by
  have h := checkLog_sound (w := (403 / 4999597)) (n := 12)
    (lo := (40303 / 250000000)) (hi := (161213 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000 / 2499597) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000 / 2499597) = 1/(2499597 / 2500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1528 : Bounds (-161213 / 1000000000) (-40303 / 250000000) (Real.log (2499597 / 2500000)) := by
  have h := reflection_log_1528_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1529_neg : (77746843 / 1000000000) ≤ -Real.log (1000000 / 1080849) ∧
    -Real.log (1000000 / 1080849) ≤ (19436711 / 250000000) := by
  have h := checkLog_sound (w := (80849 / 2080849)) (n := 12)
    (lo := (77746843 / 1000000000)) (hi := (19436711 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1080849 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1080849 / 1000000) = 1/(1000000 / 1080849) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1529 : Bounds (77746843 / 1000000000) (19436711 / 250000000) (Real.log (1080849 / 1000000)) := by
  have h := reflection_log_1529_neg
  have he : Real.log (1080849 / 1000000) = -Real.log (1000000 / 1080849) := by
    rw [show ((1080849 / 1000000) : ℝ) = ((1000000 / 1080849) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1530_neg : (84304861 / 1000000000) ≤ -Real.log (919151 / 1000000) ∧
    -Real.log (919151 / 1000000) ≤ (42152431 / 500000000) := by
  have h := checkLog_sound (w := (80849 / 1919151)) (n := 12)
    (lo := (84304861 / 1000000000)) (hi := (42152431 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 919151) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 919151) = 1/(919151 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1530 : Bounds (-42152431 / 500000000) (-84304861 / 1000000000) (Real.log (919151 / 1000000)) := by
  have h := reflection_log_1530_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1531_neg : (38971483 / 500000000) ≤ -Real.log (1000000 / 1081061) ∧
    -Real.log (1000000 / 1081061) ≤ (77942967 / 1000000000) := by
  have h := checkLog_sound (w := (81061 / 2081061)) (n := 12)
    (lo := (38971483 / 500000000)) (hi := (77942967 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1081061 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1081061 / 1000000) = 1/(1000000 / 1081061) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1531 : Bounds (38971483 / 500000000) (77942967 / 1000000000) (Real.log (1081061 / 1000000)) := by
  have h := reflection_log_1531_neg
  have he : Real.log (1081061 / 1000000) = -Real.log (1000000 / 1081061) := by
    rw [show ((1081061 / 1000000) : ℝ) = ((1000000 / 1081061) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1532_neg : (16907107 / 200000000) ≤ -Real.log (918939 / 1000000) ∧
    -Real.log (918939 / 1000000) ≤ (5283471 / 62500000) := by
  have h := checkLog_sound (w := (81061 / 1918939)) (n := 12)
    (lo := (16907107 / 200000000)) (hi := (5283471 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 918939) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 918939) = 1/(918939 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1532 : Bounds (-5283471 / 62500000) (-16907107 / 200000000) (Real.log (918939 / 1000000)) := by
  have h := reflection_log_1532_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1533_neg : (6592569 / 1000000000) ≤ -Real.log (993429114279 / 1000000000000) ∧
    -Real.log (993429114279 / 1000000000000) ≤ (659257 / 100000000) := by
  have h := checkLog_sound (w := (6570885721 / 1993429114279)) (n := 12)
    (lo := (6592569 / 1000000000)) (hi := (659257 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993429114279) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993429114279) = 1/(993429114279 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1533 : Bounds (-659257 / 100000000) (-6592569 / 1000000000) (Real.log (993429114279 / 1000000000000)) := by
  have h := reflection_log_1533_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1534_neg : (6558017 / 1000000000) ≤ -Real.log (993463439199 / 1000000000000) ∧
    -Real.log (993463439199 / 1000000000000) ≤ (3279009 / 500000000) := by
  have h := checkLog_sound (w := (6536560801 / 1993463439199)) (n := 12)
    (lo := (6558017 / 1000000000)) (hi := (3279009 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993463439199) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993463439199) = 1/(993463439199 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1534 : Bounds (-3279009 / 500000000) (-6558017 / 1000000000) (Real.log (993463439199 / 1000000000000)) := by
  have h := reflection_log_1534_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1535_neg : (20256463 / 125000000) ≤ -Real.log (62500000000 / 73495065011) ∧
    -Real.log (62500000000 / 73495065011) ≤ (32410341 / 200000000) := by
  have h := checkLog_sound (w := (10995065011 / 135995065011)) (n := 12)
    (lo := (20256463 / 125000000)) (hi := (32410341 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((73495065011 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(73495065011 / 62500000000) = 1/(62500000000 / 73495065011) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1535 : Bounds (20256463 / 125000000) (32410341 / 200000000) (Real.log (73495065011 / 62500000000)) := by
  have h := reflection_log_1535_neg
  have he : Real.log (73495065011 / 62500000000) = -Real.log (62500000000 / 73495065011) := by
    rw [show ((73495065011 / 62500000000) : ℝ) = ((62500000000 / 73495065011) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily
