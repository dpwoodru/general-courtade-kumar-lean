import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell124
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

theorem reflection_log_1_neg : (280084927 / 1000000000) ≤ -Real.log (1024 / 1355) ∧
    -Real.log (1024 / 1355) ≤ (4376327 / 15625000) := by
  have h := checkLog_sound (w := (331 / 2379)) (n := 12)
    (lo := (280084927 / 1000000000)) (hi := (4376327 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1355 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1355 / 1024) = 1/(1024 / 1355) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (280084927 / 1000000000) (4376327 / 15625000) (Real.log (1355 / 1024)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1355 / 1024) = -Real.log (1024 / 1355) := by
    rw [show ((1355 / 1024) : ℝ) = ((1024 / 1355) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (195220903 / 500000000) ≤ -Real.log (693 / 1024) ∧
    -Real.log (693 / 1024) ≤ (390441807 / 1000000000) := by
  have h := checkLog_sound (w := (331 / 1717)) (n := 12)
    (lo := (195220903 / 500000000)) (hi := (390441807 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 693) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 693) = 1/(693 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-390441807 / 1000000000) (-195220903 / 500000000) (Real.log (693 / 1024)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (11185681 / 40000000) ≤ -Real.log (1280 / 1693) ∧
    -Real.log (1280 / 1693) ≤ (139821013 / 500000000) := by
  have h := checkLog_sound (w := (413 / 2973)) (n := 12)
    (lo := (11185681 / 40000000)) (hi := (139821013 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1693 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1693 / 1280) = 1/(1280 / 1693) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (11185681 / 40000000) (139821013 / 500000000) (Real.log (1693 / 1280)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1693 / 1280) = -Real.log (1280 / 1693) := by
    rw [show ((1693 / 1280) : ℝ) = ((1280 / 1693) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (19478819 / 50000000) ≤ -Real.log (867 / 1280) ∧
    -Real.log (867 / 1280) ≤ (389576381 / 1000000000) := by
  have h := checkLog_sound (w := (413 / 2147)) (n := 12)
    (lo := (19478819 / 50000000)) (hi := (389576381 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 867) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 867) = 1/(867 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-389576381 / 1000000000) (-19478819 / 50000000) (Real.log (867 / 1280)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (8254119 / 40000000) ≤ -Real.log (1000000 / 1229187) ∧
    -Real.log (1000000 / 1229187) ≤ (12897061 / 62500000) := by
  have h := checkLog_sound (w := (229187 / 2229187)) (n := 12)
    (lo := (8254119 / 40000000)) (hi := (12897061 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1229187 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1229187 / 1000000) = 1/(1000000 / 1229187) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (8254119 / 40000000) (12897061 / 62500000) (Real.log (1229187 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1229187 / 1000000) = -Real.log (1000000 / 1229187) := by
    rw [show ((1229187 / 1000000) : ℝ) = ((1000000 / 1229187) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (65077369 / 250000000) ≤ -Real.log (770813 / 1000000) ∧
    -Real.log (770813 / 1000000) ≤ (260309477 / 1000000000) := by
  have h := checkLog_sound (w := (229187 / 1770813)) (n := 12)
    (lo := (65077369 / 250000000)) (hi := (260309477 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 770813) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 770813) = 1/(770813 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-260309477 / 1000000000) (-65077369 / 250000000) (Real.log (770813 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (206695419 / 1000000000) ≤ -Real.log (125000 / 153701) ∧
    -Real.log (125000 / 153701) ≤ (10334771 / 50000000) := by
  have h := checkLog_sound (w := (28701 / 278701)) (n := 12)
    (lo := (206695419 / 1000000000)) (hi := (10334771 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((153701 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(153701 / 125000) = 1/(125000 / 153701) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (206695419 / 1000000000) (10334771 / 50000000) (Real.log (153701 / 125000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (153701 / 125000) = -Real.log (125000 / 153701) := by
    rw [show ((153701 / 125000) : ℝ) = ((125000 / 153701) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (130427901 / 500000000) ≤ -Real.log (96299 / 125000) ∧
    -Real.log (96299 / 125000) ≤ (260855803 / 1000000000) := by
  have h := checkLog_sound (w := (28701 / 221299)) (n := 12)
    (lo := (130427901 / 500000000)) (hi := (260855803 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 96299) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 96299) = 1/(96299 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-260855803 / 1000000000) (-130427901 / 500000000) (Real.log (96299 / 125000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (19031431 / 125000000) ≤ -Real.log (1000000 / 1164453) ∧
    -Real.log (1000000 / 1164453) ≤ (152251449 / 1000000000) := by
  have h := checkLog_sound (w := (164453 / 2164453)) (n := 12)
    (lo := (19031431 / 125000000)) (hi := (152251449 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1164453 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1164453 / 1000000) = 1/(1000000 / 1164453) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (19031431 / 125000000) (152251449 / 1000000000) (Real.log (1164453 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1164453 / 1000000) = -Real.log (1000000 / 1164453) := by
    rw [show ((1164453 / 1000000) : ℝ) = ((1000000 / 1164453) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (89834339 / 500000000) ≤ -Real.log (835547 / 1000000) ∧
    -Real.log (835547 / 1000000) ≤ (179668679 / 1000000000) := by
  have h := checkLog_sound (w := (164453 / 1835547)) (n := 12)
    (lo := (89834339 / 500000000)) (hi := (179668679 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 835547) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 835547) = 1/(835547 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-179668679 / 1000000000) (-89834339 / 500000000) (Real.log (835547 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (152518491 / 1000000000) ≤ -Real.log (250000 / 291191) ∧
    -Real.log (250000 / 291191) ≤ (38129623 / 250000000) := by
  have h := checkLog_sound (w := (41191 / 541191)) (n := 12)
    (lo := (152518491 / 1000000000)) (hi := (38129623 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((291191 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(291191 / 250000) = 1/(250000 / 291191) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (152518491 / 1000000000) (38129623 / 250000000) (Real.log (291191 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (291191 / 250000) = -Real.log (250000 / 291191) := by
    rw [show ((291191 / 250000) : ℝ) = ((250000 / 291191) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (180040959 / 1000000000) ≤ -Real.log (208809 / 250000) ∧
    -Real.log (208809 / 250000) ≤ (140657 / 781250) := by
  have h := checkLog_sound (w := (41191 / 458809)) (n := 12)
    (lo := (180040959 / 1000000000)) (hi := (140657 / 781250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 208809) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 208809) = 1/(208809 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-140657 / 781250) (-180040959 / 1000000000) (Real.log (208809 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (133843681 / 200000000) ≤ -Real.log (500000000000 / 976355247981) ∧
    -Real.log (500000000000 / 976355247981) ≤ (334609203 / 500000000) := by
  have h := checkLog_sound (w := (476355247981 / 1476355247981)) (n := 12)
    (lo := (133843681 / 200000000)) (hi := (334609203 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((976355247981 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(976355247981 / 500000000000) = 1/(500000000000 / 976355247981) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (133843681 / 200000000) (334609203 / 500000000) (Real.log (976355247981 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (976355247981 / 500000000000) = -Real.log (500000000000 / 976355247981) := by
    rw [show ((976355247981 / 500000000000) : ℝ) = ((500000000000 / 976355247981) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (335263367 / 500000000) ≤ -Real.log (250000000000 / 488816738817) ∧
    -Real.log (250000000000 / 488816738817) ≤ (134105347 / 200000000) := by
  have h := checkLog_sound (w := (238816738817 / 738816738817)) (n := 12)
    (lo := (335263367 / 500000000)) (hi := (134105347 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((488816738817 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(488816738817 / 250000000000) = 1/(250000000000 / 488816738817) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (335263367 / 500000000) (134105347 / 200000000) (Real.log (488816738817 / 250000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (488816738817 / 250000000000) = -Real.log (250000000000 / 488816738817) := by
    rw [show ((488816738817 / 250000000000) : ℝ) = ((250000000000 / 488816738817) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (116665613 / 250000000) ≤ -Real.log (250000000000 / 398665759399) ∧
    -Real.log (250000000000 / 398665759399) ≤ (466662453 / 1000000000) := by
  have h := checkLog_sound (w := (148665759399 / 648665759399)) (n := 12)
    (lo := (116665613 / 250000000)) (hi := (466662453 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((398665759399 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(398665759399 / 250000000000) = 1/(250000000000 / 398665759399) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (116665613 / 250000000) (466662453 / 1000000000) (Real.log (398665759399 / 250000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (398665759399 / 250000000000) = -Real.log (250000000000 / 398665759399) := by
    rw [show ((398665759399 / 250000000000) : ℝ) = ((250000000000 / 398665759399) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (233775611 / 500000000) ≤ -Real.log (100000000000 / 159608095619) ∧
    -Real.log (100000000000 / 159608095619) ≤ (467551223 / 1000000000) := by
  have h := checkLog_sound (w := (59608095619 / 259608095619)) (n := 12)
    (lo := (233775611 / 500000000)) (hi := (467551223 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((159608095619 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(159608095619 / 100000000000) = 1/(100000000000 / 159608095619) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (233775611 / 500000000) (467551223 / 1000000000) (Real.log (159608095619 / 100000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (159608095619 / 100000000000) = -Real.log (100000000000 / 159608095619) := by
    rw [show ((159608095619 / 100000000000) : ℝ) = ((100000000000 / 159608095619) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (331920127 / 1000000000) ≤ -Real.log (500000000000 / 696820765319) ∧
    -Real.log (500000000000 / 696820765319) ≤ (1296563 / 3906250) := by
  have h := checkLog_sound (w := (196820765319 / 1196820765319)) (n := 12)
    (lo := (331920127 / 1000000000)) (hi := (1296563 / 3906250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((696820765319 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(696820765319 / 500000000000) = 1/(500000000000 / 696820765319) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (331920127 / 1000000000) (1296563 / 3906250) (Real.log (696820765319 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (696820765319 / 500000000000) = -Real.log (500000000000 / 696820765319) := by
    rw [show ((696820765319 / 500000000000) : ℝ) = ((500000000000 / 696820765319) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (6651189 / 20000000) ≤ -Real.log (500000000000 / 697266401353) ∧
    -Real.log (500000000000 / 697266401353) ≤ (332559451 / 1000000000) := by
  have h := checkLog_sound (w := (197266401353 / 1197266401353)) (n := 12)
    (lo := (6651189 / 20000000)) (hi := (332559451 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((697266401353 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(697266401353 / 500000000000) = 1/(500000000000 / 697266401353) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (6651189 / 20000000) (332559451 / 1000000000) (Real.log (697266401353 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (697266401353 / 500000000000) = -Real.log (500000000000 / 697266401353) := by
    rw [show ((697266401353 / 500000000000) : ℝ) = ((500000000000 / 697266401353) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (27522467 / 1000000000) ≤ -Real.log (60803301519 / 62500000000) ∧
    -Real.log (60803301519 / 62500000000) ≤ (6880617 / 250000000) := by
  have h := checkLog_sound (w := (1696698481 / 123303301519)) (n := 12)
    (lo := (27522467 / 1000000000)) (hi := (6880617 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 60803301519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 60803301519) = 1/(60803301519 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-6880617 / 250000000) (-27522467 / 1000000000) (Real.log (60803301519 / 62500000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (27417229 / 1000000000) ≤ -Real.log (972955210791 / 1000000000000) ∧
    -Real.log (972955210791 / 1000000000000) ≤ (2741723 / 100000000) := by
  have h := checkLog_sound (w := (27044789209 / 1972955210791)) (n := 12)
    (lo := (27417229 / 1000000000)) (hi := (2741723 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 972955210791) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 972955210791) = 1/(972955210791 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-2741723 / 100000000) (-27417229 / 1000000000) (Real.log (972955210791 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell124
