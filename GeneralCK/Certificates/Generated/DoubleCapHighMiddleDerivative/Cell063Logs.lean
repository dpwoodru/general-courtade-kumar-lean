import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell063
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

theorem reflection_log_1_neg : (252702353 / 1000000000) ≤ -Real.log (80 / 103) ∧
    -Real.log (80 / 103) ≤ (126351177 / 500000000) := by
  have h := checkLog_sound (w := (23 / 183)) (n := 12)
    (lo := (252702353 / 1000000000)) (hi := (126351177 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((103 / 80) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(103 / 80) = 1/(80 / 103) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (252702353 / 1000000000) (126351177 / 500000000) (Real.log (103 / 80)) := by
  have h := reflection_log_1_neg
  have he : Real.log (103 / 80) = -Real.log (80 / 103) := by
    rw [show ((103 / 80) : ℝ) = ((80 / 103) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (169487683 / 500000000) ≤ -Real.log (57 / 80) ∧
    -Real.log (57 / 80) ≤ (338975367 / 1000000000) := by
  have h := checkLog_sound (w := (23 / 137)) (n := 12)
    (lo := (169487683 / 500000000)) (hi := (338975367 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80 / 57) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(80 / 57) = 1/(57 / 80) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-338975367 / 1000000000) (-169487683 / 500000000) (Real.log (57 / 80)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (15765447 / 62500000) ≤ -Real.log (5120 / 6589) ∧
    -Real.log (5120 / 6589) ≤ (252247153 / 1000000000) := by
  have h := checkLog_sound (w := (1469 / 11709)) (n := 12)
    (lo := (15765447 / 62500000)) (hi := (252247153 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6589 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6589 / 5120) = 1/(5120 / 6589) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (15765447 / 62500000) (252247153 / 1000000000) (Real.log (6589 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6589 / 5120) = -Real.log (5120 / 6589) := by
    rw [show ((6589 / 5120) : ℝ) = ((5120 / 6589) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (42269167 / 125000000) ≤ -Real.log (3651 / 5120) ∧
    -Real.log (3651 / 5120) ≤ (338153337 / 1000000000) := by
  have h := checkLog_sound (w := (1469 / 8771)) (n := 12)
    (lo := (42269167 / 125000000)) (hi := (338153337 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3651) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3651) = 1/(3651 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-338153337 / 1000000000) (-42269167 / 125000000) (Real.log (3651 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (92658117 / 500000000) ≤ -Real.log (1000000 / 1203599) ∧
    -Real.log (1000000 / 1203599) ≤ (37063247 / 200000000) := by
  have h := checkLog_sound (w := (203599 / 2203599)) (n := 12)
    (lo := (92658117 / 500000000)) (hi := (37063247 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1203599 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1203599 / 1000000) = 1/(1000000 / 1203599) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (92658117 / 500000000) (37063247 / 200000000) (Real.log (1203599 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1203599 / 1000000) = -Real.log (1000000 / 1203599) := by
    rw [show ((1203599 / 1000000) : ℝ) = ((1000000 / 1203599) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (227652451 / 1000000000) ≤ -Real.log (796401 / 1000000) ∧
    -Real.log (796401 / 1000000) ≤ (56913113 / 250000000) := by
  have h := checkLog_sound (w := (203599 / 1796401)) (n := 12)
    (lo := (227652451 / 1000000000)) (hi := (56913113 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 796401) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 796401) = 1/(796401 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-56913113 / 250000000) (-227652451 / 1000000000) (Real.log (796401 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (185665127 / 1000000000) ≤ -Real.log (1000000 / 1204019) ∧
    -Real.log (1000000 / 1204019) ≤ (23208141 / 125000000) := by
  have h := checkLog_sound (w := (204019 / 2204019)) (n := 12)
    (lo := (185665127 / 1000000000)) (hi := (23208141 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1204019 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1204019 / 1000000) = 1/(1000000 / 1204019) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (185665127 / 1000000000) (23208141 / 125000000) (Real.log (1204019 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1204019 / 1000000) = -Real.log (1000000 / 1204019) := by
    rw [show ((1204019 / 1000000) : ℝ) = ((1000000 / 1204019) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (114089981 / 500000000) ≤ -Real.log (795981 / 1000000) ∧
    -Real.log (795981 / 1000000) ≤ (228179963 / 1000000000) := by
  have h := checkLog_sound (w := (204019 / 1795981)) (n := 12)
    (lo := (114089981 / 500000000)) (hi := (228179963 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 795981) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 795981) = 1/(795981 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-228179963 / 1000000000) (-114089981 / 500000000) (Real.log (795981 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (135962559 / 1000000000) ≤ -Real.log (1000000 / 1145639) ∧
    -Real.log (1000000 / 1145639) ≤ (424883 / 3125000) := by
  have h := checkLog_sound (w := (145639 / 2145639)) (n := 12)
    (lo := (135962559 / 1000000000)) (hi := (424883 / 3125000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1145639 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1145639 / 1000000) = 1/(1000000 / 1145639) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (135962559 / 1000000000) (424883 / 3125000) (Real.log (1145639 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1145639 / 1000000) = -Real.log (1000000 / 1145639) := by
    rw [show ((1145639 / 1000000) : ℝ) = ((1000000 / 1145639) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (157401457 / 1000000000) ≤ -Real.log (854361 / 1000000) ∧
    -Real.log (854361 / 1000000) ≤ (78700729 / 500000000) := by
  have h := checkLog_sound (w := (145639 / 1854361)) (n := 12)
    (lo := (157401457 / 1000000000)) (hi := (78700729 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 854361) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 854361) = 1/(854361 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-78700729 / 500000000) (-157401457 / 1000000000) (Real.log (854361 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (136231369 / 1000000000) ≤ -Real.log (1000000 / 1145947) ∧
    -Real.log (1000000 / 1145947) ≤ (13623137 / 100000000) := by
  have h := checkLog_sound (w := (145947 / 2145947)) (n := 12)
    (lo := (136231369 / 1000000000)) (hi := (13623137 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1145947 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1145947 / 1000000) = 1/(1000000 / 1145947) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (136231369 / 1000000000) (13623137 / 100000000) (Real.log (1145947 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1145947 / 1000000) = -Real.log (1000000 / 1145947) := by
    rw [show ((1145947 / 1000000) : ℝ) = ((1000000 / 1145947) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (78881013 / 500000000) ≤ -Real.log (854053 / 1000000) ∧
    -Real.log (854053 / 1000000) ≤ (157762027 / 1000000000) := by
  have h := checkLog_sound (w := (145947 / 1854053)) (n := 12)
    (lo := (78881013 / 500000000)) (hi := (157762027 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 854053) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 854053) = 1/(854053 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-157762027 / 1000000000) (-78881013 / 500000000) (Real.log (854053 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (590400489 / 1000000000) ≤ -Real.log (100000000000 / 180471103807) ∧
    -Real.log (100000000000 / 180471103807) ≤ (59040049 / 100000000) := by
  have h := checkLog_sound (w := (80471103807 / 280471103807)) (n := 12)
    (lo := (590400489 / 1000000000)) (hi := (59040049 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((180471103807 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(180471103807 / 100000000000) = 1/(100000000000 / 180471103807) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (590400489 / 1000000000) (59040049 / 100000000) (Real.log (180471103807 / 100000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (180471103807 / 100000000000) = -Real.log (100000000000 / 180471103807) := by
    rw [show ((180471103807 / 100000000000) : ℝ) = ((100000000000 / 180471103807) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (14791943 / 25000000) ≤ -Real.log (50000000000 / 90350877193) ∧
    -Real.log (50000000000 / 90350877193) ≤ (591677721 / 1000000000) := by
  have h := checkLog_sound (w := (40350877193 / 140350877193)) (n := 12)
    (lo := (14791943 / 25000000)) (hi := (591677721 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((90350877193 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(90350877193 / 50000000000) = 1/(50000000000 / 90350877193) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (14791943 / 25000000) (591677721 / 1000000000) (Real.log (90350877193 / 50000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (90350877193 / 50000000000) = -Real.log (50000000000 / 90350877193) := by
    rw [show ((90350877193 / 50000000000) : ℝ) = ((50000000000 / 90350877193) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (206484343 / 500000000) ≤ -Real.log (100000000000 / 151129770053) ∧
    -Real.log (100000000000 / 151129770053) ≤ (412968687 / 1000000000) := by
  have h := checkLog_sound (w := (51129770053 / 251129770053)) (n := 12)
    (lo := (206484343 / 500000000)) (hi := (412968687 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((151129770053 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(151129770053 / 100000000000) = 1/(100000000000 / 151129770053) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (206484343 / 500000000) (412968687 / 1000000000) (Real.log (151129770053 / 100000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (151129770053 / 100000000000) = -Real.log (100000000000 / 151129770053) := by
    rw [show ((151129770053 / 100000000000) : ℝ) = ((100000000000 / 151129770053) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (41384509 / 100000000) ≤ -Real.log (7812500000 / 11817365537) ∧
    -Real.log (7812500000 / 11817365537) ≤ (413845091 / 1000000000) := by
  have h := checkLog_sound (w := (4004865537 / 19629865537)) (n := 12)
    (lo := (41384509 / 100000000)) (hi := (413845091 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11817365537 / 7812500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11817365537 / 7812500000) = 1/(7812500000 / 11817365537) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (41384509 / 100000000) (413845091 / 1000000000) (Real.log (11817365537 / 7812500000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (11817365537 / 7812500000) = -Real.log (7812500000 / 11817365537) := by
    rw [show ((11817365537 / 7812500000) : ℝ) = ((7812500000 / 11817365537) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (293364017 / 1000000000) ≤ -Real.log (500000000000 / 670465412161) ∧
    -Real.log (500000000000 / 670465412161) ≤ (146682009 / 500000000) := by
  have h := checkLog_sound (w := (170465412161 / 1170465412161)) (n := 12)
    (lo := (293364017 / 1000000000)) (hi := (146682009 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((670465412161 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(670465412161 / 500000000000) = 1/(500000000000 / 670465412161) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (293364017 / 1000000000) (146682009 / 500000000) (Real.log (670465412161 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (670465412161 / 500000000000) = -Real.log (500000000000 / 670465412161) := by
    rw [show ((670465412161 / 500000000000) : ℝ) = ((500000000000 / 670465412161) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (58798679 / 200000000) ≤ -Real.log (500000000000 / 670887521033) ∧
    -Real.log (500000000000 / 670887521033) ≤ (73498349 / 250000000) := by
  have h := checkLog_sound (w := (170887521033 / 1170887521033)) (n := 12)
    (lo := (58798679 / 200000000)) (hi := (73498349 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((670887521033 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(670887521033 / 500000000000) = 1/(500000000000 / 670887521033) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (58798679 / 200000000) (73498349 / 250000000) (Real.log (670887521033 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (670887521033 / 500000000000) = -Real.log (500000000000 / 670887521033) := by
    rw [show ((670887521033 / 500000000000) : ℝ) = ((500000000000 / 670887521033) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (672833 / 31250000) ≤ -Real.log (978699473191 / 1000000000000) ∧
    -Real.log (978699473191 / 1000000000000) ≤ (21530657 / 1000000000) := by
  have h := checkLog_sound (w := (21300526809 / 1978699473191)) (n := 12)
    (lo := (672833 / 31250000)) (hi := (21530657 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 978699473191) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 978699473191) = 1/(978699473191 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-21530657 / 1000000000) (-672833 / 31250000) (Real.log (978699473191 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (21438897 / 1000000000) ≤ -Real.log (978789281679 / 1000000000000) ∧
    -Real.log (978789281679 / 1000000000000) ≤ (10719449 / 500000000) := by
  have h := checkLog_sound (w := (21210718321 / 1978789281679)) (n := 12)
    (lo := (21438897 / 1000000000)) (hi := (10719449 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 978789281679) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 978789281679) = 1/(978789281679 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-10719449 / 500000000) (-21438897 / 1000000000) (Real.log (978789281679 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell063
