import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell062
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

theorem reflection_log_1_neg : (15765447 / 62500000) ≤ -Real.log (5120 / 6589) ∧
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


theorem reflection_log_1 : Bounds (15765447 / 62500000) (252247153 / 1000000000) (Real.log (6589 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6589 / 5120) = -Real.log (5120 / 6589) := by
    rw [show ((6589 / 5120) : ℝ) = ((5120 / 6589) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (42269167 / 125000000) ≤ -Real.log (3651 / 5120) ∧
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


theorem reflection_log_2 : Bounds (-338153337 / 1000000000) (-42269167 / 125000000) (Real.log (3651 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (1967123 / 7812500) ≤ -Real.log (2560 / 3293) ∧
    -Real.log (2560 / 3293) ≤ (50358349 / 200000000) := by
  have h := checkLog_sound (w := (733 / 5853)) (n := 12)
    (lo := (1967123 / 7812500)) (hi := (50358349 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3293 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3293 / 2560) = 1/(2560 / 3293) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (1967123 / 7812500) (50358349 / 200000000) (Real.log (3293 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3293 / 2560) = -Real.log (2560 / 3293) := by
    rw [show ((3293 / 2560) : ℝ) = ((2560 / 3293) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (337331981 / 1000000000) ≤ -Real.log (1827 / 2560) ∧
    -Real.log (1827 / 2560) ≤ (168665991 / 500000000) := by
  have h := checkLog_sound (w := (733 / 4387)) (n := 12)
    (lo := (337331981 / 1000000000)) (hi := (168665991 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1827) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1827) = 1/(1827 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-168665991 / 500000000) (-337331981 / 1000000000) (Real.log (1827 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (184968051 / 1000000000) ≤ -Real.log (50000 / 60159) ∧
    -Real.log (50000 / 60159) ≤ (46242013 / 250000000) := by
  have h := checkLog_sound (w := (10159 / 110159)) (n := 12)
    (lo := (184968051 / 1000000000)) (hi := (46242013 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((60159 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(60159 / 50000) = 1/(50000 / 60159) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (184968051 / 1000000000) (46242013 / 250000000) (Real.log (60159 / 50000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (60159 / 50000) = -Real.log (50000 / 60159) := by
    rw [show ((60159 / 50000) : ℝ) = ((50000 / 60159) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (28390809 / 125000000) ≤ -Real.log (39841 / 50000) ∧
    -Real.log (39841 / 50000) ≤ (227126473 / 1000000000) := by
  have h := checkLog_sound (w := (10159 / 89841)) (n := 12)
    (lo := (28390809 / 125000000)) (hi := (227126473 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 39841) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 39841) = 1/(39841 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-227126473 / 1000000000) (-28390809 / 125000000) (Real.log (39841 / 50000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (37063413 / 200000000) ≤ -Real.log (2500 / 3009) ∧
    -Real.log (2500 / 3009) ≤ (92658533 / 500000000) := by
  have h := checkLog_sound (w := (509 / 5509)) (n := 12)
    (lo := (37063413 / 200000000)) (hi := (92658533 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3009 / 2500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3009 / 2500) = 1/(2500 / 3009) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (37063413 / 200000000) (92658533 / 500000000) (Real.log (3009 / 2500)) := by
  have h := reflection_log_7_neg
  have he : Real.log (3009 / 2500) = -Real.log (2500 / 3009) := by
    rw [show ((3009 / 2500) : ℝ) = ((2500 / 3009) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (113826853 / 500000000) ≤ -Real.log (1991 / 2500) ∧
    -Real.log (1991 / 2500) ≤ (227653707 / 1000000000) := by
  have h := checkLog_sound (w := (509 / 4491)) (n := 12)
    (lo := (113826853 / 500000000)) (hi := (227653707 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500 / 1991) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500 / 1991) = 1/(1991 / 2500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-227653707 / 1000000000) (-113826853 / 500000000) (Real.log (1991 / 2500)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (2120241 / 15625000) ≤ -Real.log (1000000 / 1145333) ∧
    -Real.log (1000000 / 1145333) ≤ (5427817 / 40000000) := by
  have h := checkLog_sound (w := (145333 / 2145333)) (n := 12)
    (lo := (2120241 / 15625000)) (hi := (5427817 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1145333 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1145333 / 1000000) = 1/(1000000 / 1145333) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (2120241 / 15625000) (5427817 / 40000000) (Real.log (1145333 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1145333 / 1000000) = -Real.log (1000000 / 1145333) := by
    rw [show ((1145333 / 1000000) : ℝ) = ((1000000 / 1145333) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (157043359 / 1000000000) ≤ -Real.log (854667 / 1000000) ∧
    -Real.log (854667 / 1000000) ≤ (981521 / 6250000) := by
  have h := checkLog_sound (w := (145333 / 1854667)) (n := 12)
    (lo := (157043359 / 1000000000)) (hi := (981521 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 854667) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 854667) = 1/(854667 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-981521 / 6250000) (-157043359 / 1000000000) (Real.log (854667 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (16995429 / 125000000) ≤ -Real.log (25000 / 28641) ∧
    -Real.log (25000 / 28641) ≤ (135963433 / 1000000000) := by
  have h := checkLog_sound (w := (3641 / 53641)) (n := 12)
    (lo := (16995429 / 125000000)) (hi := (135963433 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((28641 / 25000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(28641 / 25000) = 1/(25000 / 28641) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (16995429 / 125000000) (135963433 / 1000000000) (Real.log (28641 / 25000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (28641 / 25000) = -Real.log (25000 / 28641) := by
    rw [show ((28641 / 25000) : ℝ) = ((25000 / 28641) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (39350657 / 250000000) ≤ -Real.log (21359 / 25000) ∧
    -Real.log (21359 / 25000) ≤ (157402629 / 1000000000) := by
  have h := checkLog_sound (w := (3641 / 46359)) (n := 12)
    (lo := (39350657 / 250000000)) (hi := (157402629 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 21359) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25000 / 21359) = 1/(21359 / 25000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-157402629 / 1000000000) (-39350657 / 250000000) (Real.log (21359 / 25000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (23564949 / 40000000) ≤ -Real.log (31250000000 / 56325259989) ∧
    -Real.log (31250000000 / 56325259989) ≤ (294561863 / 500000000) := by
  have h := checkLog_sound (w := (25075259989 / 87575259989)) (n := 12)
    (lo := (23564949 / 40000000)) (hi := (294561863 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((56325259989 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(56325259989 / 31250000000) = 1/(31250000000 / 56325259989) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (23564949 / 40000000) (294561863 / 500000000) (Real.log (56325259989 / 31250000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (56325259989 / 31250000000) = -Real.log (31250000000 / 56325259989) := by
    rw [show ((56325259989 / 31250000000) : ℝ) = ((31250000000 / 56325259989) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (590400489 / 1000000000) ≤ -Real.log (125000000000 / 225588879759) ∧
    -Real.log (125000000000 / 225588879759) ≤ (59040049 / 100000000) := by
  have h := checkLog_sound (w := (100588879759 / 350588879759)) (n := 12)
    (lo := (590400489 / 1000000000)) (hi := (59040049 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((225588879759 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(225588879759 / 125000000000) = 1/(125000000000 / 225588879759) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (590400489 / 1000000000) (59040049 / 100000000) (Real.log (225588879759 / 125000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (225588879759 / 125000000000) = -Real.log (125000000000 / 225588879759) := by
    rw [show ((225588879759 / 125000000000) : ℝ) = ((125000000000 / 225588879759) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (103023631 / 250000000) ≤ -Real.log (500000000000 / 754988579603) ∧
    -Real.log (500000000000 / 754988579603) ≤ (16483781 / 40000000) := by
  have h := checkLog_sound (w := (254988579603 / 1254988579603)) (n := 12)
    (lo := (103023631 / 250000000)) (hi := (16483781 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((754988579603 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(754988579603 / 500000000000) = 1/(500000000000 / 754988579603) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (103023631 / 250000000) (16483781 / 40000000) (Real.log (754988579603 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (754988579603 / 500000000000) = -Real.log (500000000000 / 754988579603) := by
    rw [show ((754988579603 / 500000000000) : ℝ) = ((500000000000 / 754988579603) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (103242693 / 250000000) ≤ -Real.log (250000000000 / 377825213461) ∧
    -Real.log (250000000000 / 377825213461) ≤ (412970773 / 1000000000) := by
  have h := checkLog_sound (w := (127825213461 / 627825213461)) (n := 12)
    (lo := (103242693 / 250000000)) (hi := (412970773 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((377825213461 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(377825213461 / 250000000000) = 1/(250000000000 / 377825213461) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (103242693 / 250000000) (412970773 / 1000000000) (Real.log (377825213461 / 250000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (377825213461 / 250000000000) = -Real.log (250000000000 / 377825213461) := by
    rw [show ((377825213461 / 250000000000) : ℝ) = ((250000000000 / 377825213461) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (9148087 / 31250000) ≤ -Real.log (100000000000 / 134009269107) ∧
    -Real.log (100000000000 / 134009269107) ≤ (58547757 / 200000000) := by
  have h := checkLog_sound (w := (34009269107 / 234009269107)) (n := 12)
    (lo := (9148087 / 31250000)) (hi := (58547757 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((134009269107 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(134009269107 / 100000000000) = 1/(100000000000 / 134009269107) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (9148087 / 31250000) (58547757 / 200000000) (Real.log (134009269107 / 100000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (134009269107 / 100000000000) = -Real.log (100000000000 / 134009269107) := by
    rw [show ((134009269107 / 100000000000) : ℝ) = ((100000000000 / 134009269107) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (293366061 / 1000000000) ≤ -Real.log (500000000000 / 670466782153) ∧
    -Real.log (500000000000 / 670466782153) ≤ (146683031 / 500000000) := by
  have h := checkLog_sound (w := (170466782153 / 1170466782153)) (n := 12)
    (lo := (293366061 / 1000000000)) (hi := (146683031 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((670466782153 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(670466782153 / 500000000000) = 1/(500000000000 / 670466782153) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (293366061 / 1000000000) (146683031 / 500000000) (Real.log (670466782153 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (670466782153 / 500000000000) = -Real.log (500000000000 / 670466782153) := by
    rw [show ((670466782153 / 500000000000) : ℝ) = ((500000000000 / 670466782153) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (4287839 / 200000000) ≤ -Real.log (611743119 / 625000000) ∧
    -Real.log (611743119 / 625000000) ≤ (5359799 / 250000000) := by
  have h := checkLog_sound (w := (13256881 / 1236743119)) (n := 12)
    (lo := (4287839 / 200000000)) (hi := (5359799 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625000000 / 611743119) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625000000 / 611743119) = 1/(611743119 / 625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-5359799 / 250000000) (-4287839 / 200000000) (Real.log (611743119 / 625000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (4269587 / 200000000) ≤ -Real.log (978878319111 / 1000000000000) ∧
    -Real.log (978878319111 / 1000000000000) ≤ (667123 / 31250000) := by
  have h := checkLog_sound (w := (21121680889 / 1978878319111)) (n := 12)
    (lo := (4269587 / 200000000)) (hi := (667123 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 978878319111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 978878319111) = 1/(978878319111 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-667123 / 31250000) (-4269587 / 200000000) (Real.log (978878319111 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell062
