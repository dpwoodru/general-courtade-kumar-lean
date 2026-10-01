import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell180
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

theorem reflection_log_1_neg : (152289759 / 500000000) ≤ -Real.log (5120 / 6943) ∧
    -Real.log (5120 / 6943) ≤ (304579519 / 1000000000) := by
  have h := checkLog_sound (w := (1823 / 12063)) (n := 12)
    (lo := (152289759 / 500000000)) (hi := (304579519 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6943 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6943 / 5120) = 1/(5120 / 6943) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (152289759 / 500000000) (304579519 / 1000000000) (Real.log (6943 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6943 / 5120) = -Real.log (5120 / 6943) := by
    rw [show ((6943 / 5120) : ℝ) = ((5120 / 6943) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (220070737 / 500000000) ≤ -Real.log (3297 / 5120) ∧
    -Real.log (3297 / 5120) ≤ (17605659 / 40000000) := by
  have h := checkLog_sound (w := (1823 / 8417)) (n := 12)
    (lo := (220070737 / 500000000)) (hi := (17605659 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3297) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3297) = 1/(3297 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-17605659 / 40000000) (-220070737 / 500000000) (Real.log (3297 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (60829467 / 200000000) ≤ -Real.log (256 / 347) ∧
    -Real.log (256 / 347) ≤ (38018417 / 125000000) := by
  have h := checkLog_sound (w := (91 / 603)) (n := 12)
    (lo := (60829467 / 200000000)) (hi := (38018417 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((347 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(347 / 256) = 1/(256 / 347) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (60829467 / 200000000) (38018417 / 125000000) (Real.log (347 / 256)) := by
  have h := reflection_log_3_neg
  have he : Real.log (347 / 256) = -Real.log (256 / 347) := by
    rw [show ((347 / 256) : ℝ) = ((256 / 347) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (43923197 / 100000000) ≤ -Real.log (165 / 256) ∧
    -Real.log (165 / 256) ≤ (439231971 / 1000000000) := by
  have h := checkLog_sound (w := (91 / 421)) (n := 12)
    (lo := (43923197 / 100000000)) (hi := (439231971 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((256 / 165) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(256 / 165) = 1/(165 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-439231971 / 1000000000) (-43923197 / 100000000) (Real.log (165 / 256)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (225341933 / 1000000000) ≤ -Real.log (1000000 / 1252751) ∧
    -Real.log (1000000 / 1252751) ≤ (112670967 / 500000000) := by
  have h := checkLog_sound (w := (252751 / 2252751)) (n := 12)
    (lo := (225341933 / 1000000000)) (hi := (112670967 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1252751 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1252751 / 1000000) = 1/(1000000 / 1252751) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (225341933 / 1000000000) (112670967 / 500000000) (Real.log (1252751 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1252751 / 1000000) = -Real.log (1000000 / 1252751) := by
    rw [show ((1252751 / 1000000) : ℝ) = ((1000000 / 1252751) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (18209801 / 62500000) ≤ -Real.log (747249 / 1000000) ∧
    -Real.log (747249 / 1000000) ≤ (291356817 / 1000000000) := by
  have h := checkLog_sound (w := (252751 / 1747249)) (n := 12)
    (lo := (18209801 / 62500000)) (hi := (291356817 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 747249) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 747249) = 1/(747249 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-291356817 / 1000000000) (-18209801 / 62500000) (Real.log (747249 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (56419883 / 250000000) ≤ -Real.log (500000 / 626587) ∧
    -Real.log (500000 / 626587) ≤ (225679533 / 1000000000) := by
  have h := checkLog_sound (w := (126587 / 1126587)) (n := 12)
    (lo := (56419883 / 250000000)) (hi := (225679533 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((626587 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(626587 / 500000) = 1/(500000 / 626587) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (56419883 / 250000000) (225679533 / 1000000000) (Real.log (626587 / 500000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (626587 / 500000) = -Real.log (500000 / 626587) := by
    rw [show ((626587 / 500000) : ℝ) = ((500000 / 626587) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (72980763 / 250000000) ≤ -Real.log (373413 / 500000) ∧
    -Real.log (373413 / 500000) ≤ (291923053 / 1000000000) := by
  have h := checkLog_sound (w := (126587 / 873413)) (n := 12)
    (lo := (72980763 / 250000000)) (hi := (291923053 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 373413) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 373413) = 1/(373413 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-291923053 / 1000000000) (-72980763 / 250000000) (Real.log (373413 / 500000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (2611857 / 15625000) ≤ -Real.log (500000 / 590971) ∧
    -Real.log (500000 / 590971) ≤ (167158849 / 1000000000) := by
  have h := checkLog_sound (w := (90971 / 1090971)) (n := 12)
    (lo := (2611857 / 15625000)) (hi := (167158849 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((590971 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(590971 / 500000) = 1/(500000 / 590971) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (2611857 / 15625000) (167158849 / 1000000000) (Real.log (590971 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (590971 / 500000) = -Real.log (500000 / 590971) := by
    rw [show ((590971 / 500000) : ℝ) = ((500000 / 590971) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (5020551 / 25000000) ≤ -Real.log (409029 / 500000) ∧
    -Real.log (409029 / 500000) ≤ (200822041 / 1000000000) := by
  have h := checkLog_sound (w := (90971 / 909029)) (n := 12)
    (lo := (5020551 / 25000000)) (hi := (200822041 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 409029) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 409029) = 1/(409029 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-200822041 / 1000000000) (-5020551 / 25000000) (Real.log (409029 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (167425323 / 1000000000) ≤ -Real.log (1000000 / 1182257) ∧
    -Real.log (1000000 / 1182257) ≤ (41856331 / 250000000) := by
  have h := checkLog_sound (w := (182257 / 2182257)) (n := 12)
    (lo := (167425323 / 1000000000)) (hi := (41856331 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1182257 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1182257 / 1000000) = 1/(1000000 / 1182257) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (167425323 / 1000000000) (41856331 / 250000000) (Real.log (1182257 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1182257 / 1000000) = -Real.log (1000000 / 1182257) := by
    rw [show ((1182257 / 1000000) : ℝ) = ((1000000 / 1182257) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (50301793 / 250000000) ≤ -Real.log (817743 / 1000000) ∧
    -Real.log (817743 / 1000000) ≤ (201207173 / 1000000000) := by
  have h := checkLog_sound (w := (182257 / 1817743)) (n := 12)
    (lo := (50301793 / 250000000)) (hi := (201207173 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 817743) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 817743) = 1/(817743 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-201207173 / 1000000000) (-50301793 / 250000000) (Real.log (817743 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (148675861 / 200000000) ≤ -Real.log (100000000000 / 210303030303) ∧
    -Real.log (100000000000 / 210303030303) ≤ (743379307 / 1000000000) := by
  have h := checkLog_sound (w := (10303030303 / 410303030303)) (n := 12)
    (lo := (401857 / 8000000)) (hi := (25116063 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((210303030303 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(210303030303 / 200000000000) = 1/(100000000000 / 210303030303) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (148675861 / 200000000) (743379307 / 1000000000) (Real.log (210303030303 / 100000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (210303030303 / 100000000000) = -Real.log (100000000000 / 210303030303) := by
    rw [show ((210303030303 / 100000000000) : ℝ) = ((100000000000 / 210303030303) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (744720993 / 1000000000) ≤ -Real.log (250000000000 / 526463451623) ∧
    -Real.log (250000000000 / 526463451623) ≤ (148944199 / 200000000) := by
  have h := checkLog_sound (w := (26463451623 / 1026463451623)) (n := 12)
    (lo := (51573813 / 1000000000)) (hi := (25786907 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((526463451623 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(526463451623 / 500000000000) = 1/(250000000000 / 526463451623) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (744720993 / 1000000000) (148944199 / 200000000) (Real.log (526463451623 / 250000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (526463451623 / 250000000000) = -Real.log (250000000000 / 526463451623) := by
    rw [show ((526463451623 / 250000000000) : ℝ) = ((250000000000 / 526463451623) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (516698749 / 1000000000) ≤ -Real.log (500000000000 / 838242005007) ∧
    -Real.log (500000000000 / 838242005007) ≤ (413359 / 800000) := by
  have h := checkLog_sound (w := (338242005007 / 1338242005007)) (n := 12)
    (lo := (516698749 / 1000000000)) (hi := (413359 / 800000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((838242005007 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(838242005007 / 500000000000) = 1/(500000000000 / 838242005007) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (516698749 / 1000000000) (413359 / 800000) (Real.log (838242005007 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (838242005007 / 500000000000) = -Real.log (500000000000 / 838242005007) := by
    rw [show ((838242005007 / 500000000000) : ℝ) = ((500000000000 / 838242005007) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (103520517 / 200000000) ≤ -Real.log (100000000000 / 167799996251) ∧
    -Real.log (100000000000 / 167799996251) ≤ (258801293 / 500000000) := by
  have h := checkLog_sound (w := (67799996251 / 267799996251)) (n := 12)
    (lo := (103520517 / 200000000)) (hi := (258801293 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((167799996251 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(167799996251 / 100000000000) = 1/(100000000000 / 167799996251) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (103520517 / 200000000) (258801293 / 500000000) (Real.log (167799996251 / 100000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (167799996251 / 100000000000) = -Real.log (100000000000 / 167799996251) := by
    rw [show ((167799996251 / 100000000000) : ℝ) = ((100000000000 / 167799996251) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (45997611 / 125000000) ≤ -Real.log (25000000000 / 36120360659) ∧
    -Real.log (25000000000 / 36120360659) ≤ (367980889 / 1000000000) := by
  have h := checkLog_sound (w := (11120360659 / 61120360659)) (n := 12)
    (lo := (45997611 / 125000000)) (hi := (367980889 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((36120360659 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(36120360659 / 25000000000) = 1/(25000000000 / 36120360659) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (45997611 / 125000000) (367980889 / 1000000000) (Real.log (36120360659 / 25000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (36120360659 / 25000000000) = -Real.log (25000000000 / 36120360659) := by
    rw [show ((36120360659 / 25000000000) : ℝ) = ((25000000000 / 36120360659) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (23039531 / 62500000) ≤ -Real.log (250000000000 / 361439046253) ∧
    -Real.log (250000000000 / 361439046253) ≤ (368632497 / 1000000000) := by
  have h := checkLog_sound (w := (111439046253 / 611439046253)) (n := 12)
    (lo := (23039531 / 62500000)) (hi := (368632497 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((361439046253 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(361439046253 / 250000000000) = 1/(250000000000 / 361439046253) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (23039531 / 62500000) (368632497 / 1000000000) (Real.log (361439046253 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (361439046253 / 250000000000) = -Real.log (250000000000 / 361439046253) := by
    rw [show ((361439046253 / 250000000000) : ℝ) = ((250000000000 / 361439046253) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (33781849 / 1000000000) ≤ -Real.log (966782385951 / 1000000000000) ∧
    -Real.log (966782385951 / 1000000000000) ≤ (675637 / 20000000) := by
  have h := checkLog_sound (w := (33217614049 / 1966782385951)) (n := 12)
    (lo := (33781849 / 1000000000)) (hi := (675637 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 966782385951) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 966782385951) = 1/(966782385951 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-675637 / 20000000) (-33781849 / 1000000000) (Real.log (966782385951 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (33663191 / 1000000000) ≤ -Real.log (241724277159 / 250000000000) ∧
    -Real.log (241724277159 / 250000000000) ≤ (4207899 / 125000000) := by
  have h := checkLog_sound (w := (8275722841 / 491724277159)) (n := 12)
    (lo := (33663191 / 1000000000)) (hi := (4207899 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 241724277159) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 241724277159) = 1/(241724277159 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-4207899 / 125000000) (-33663191 / 1000000000) (Real.log (241724277159 / 250000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell180
