import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell060
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

theorem reflection_log_1_neg : (251336129 / 1000000000) ≤ -Real.log (5120 / 6583) ∧
    -Real.log (5120 / 6583) ≤ (25133613 / 100000000) := by
  have h := checkLog_sound (w := (1463 / 11703)) (n := 12)
    (lo := (251336129 / 1000000000)) (hi := (25133613 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6583 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6583 / 5120) = 1/(5120 / 6583) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (251336129 / 1000000000) (25133613 / 100000000) (Real.log (6583 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6583 / 5120) = -Real.log (5120 / 6583) := by
    rw [show ((6583 / 5120) : ℝ) = ((5120 / 6583) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (336511299 / 1000000000) ≤ -Real.log (3657 / 5120) ∧
    -Real.log (3657 / 5120) ≤ (3365113 / 10000000) := by
  have h := checkLog_sound (w := (1463 / 8777)) (n := 12)
    (lo := (336511299 / 1000000000)) (hi := (3365113 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3657) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3657) = 1/(3657 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-3365113 / 10000000) (-336511299 / 1000000000) (Real.log (3657 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (125440153 / 500000000) ≤ -Real.log (256 / 329) ∧
    -Real.log (256 / 329) ≤ (250880307 / 1000000000) := by
  have h := checkLog_sound (w := (73 / 585)) (n := 12)
    (lo := (125440153 / 500000000)) (hi := (250880307 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((329 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(329 / 256) = 1/(256 / 329) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (125440153 / 500000000) (250880307 / 1000000000) (Real.log (329 / 256)) := by
  have h := reflection_log_3_neg
  have he : Real.log (329 / 256) = -Real.log (256 / 329) := by
    rw [show ((329 / 256) : ℝ) = ((256 / 329) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (335691291 / 1000000000) ≤ -Real.log (183 / 256) ∧
    -Real.log (183 / 256) ≤ (83922823 / 250000000) := by
  have h := checkLog_sound (w := (73 / 439)) (n := 12)
    (lo := (335691291 / 1000000000)) (hi := (83922823 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((256 / 183) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(256 / 183) = 1/(183 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-83922823 / 250000000) (-335691291 / 1000000000) (Real.log (183 / 256)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (184272153 / 1000000000) ≤ -Real.log (1000000 / 1202343) ∧
    -Real.log (1000000 / 1202343) ≤ (92136077 / 500000000) := by
  have h := checkLog_sound (w := (202343 / 2202343)) (n := 12)
    (lo := (184272153 / 1000000000)) (hi := (92136077 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1202343 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1202343 / 1000000) = 1/(1000000 / 1202343) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (184272153 / 1000000000) (92136077 / 500000000) (Real.log (1202343 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1202343 / 1000000) = -Real.log (1000000 / 1202343) := by
    rw [show ((1202343 / 1000000) : ℝ) = ((1000000 / 1202343) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (113038299 / 500000000) ≤ -Real.log (797657 / 1000000) ∧
    -Real.log (797657 / 1000000) ≤ (226076599 / 1000000000) := by
  have h := checkLog_sound (w := (202343 / 1797657)) (n := 12)
    (lo := (113038299 / 500000000)) (hi := (226076599 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 797657) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 797657) = 1/(797657 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-226076599 / 1000000000) (-113038299 / 500000000) (Real.log (797657 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (92310289 / 500000000) ≤ -Real.log (500000 / 601381) ∧
    -Real.log (500000 / 601381) ≤ (184620579 / 1000000000) := by
  have h := checkLog_sound (w := (101381 / 1101381)) (n := 12)
    (lo := (92310289 / 500000000)) (hi := (184620579 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((601381 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(601381 / 500000) = 1/(500000 / 601381) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (92310289 / 500000000) (184620579 / 1000000000) (Real.log (601381 / 500000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (601381 / 500000) = -Real.log (500000 / 601381) := by
    rw [show ((601381 / 500000) : ℝ) = ((500000 / 601381) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (28325253 / 125000000) ≤ -Real.log (398619 / 500000) ∧
    -Real.log (398619 / 500000) ≤ (9064081 / 40000000) := by
  have h := checkLog_sound (w := (101381 / 898619)) (n := 12)
    (lo := (28325253 / 125000000)) (hi := (9064081 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 398619) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 398619) = 1/(398619 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-9064081 / 40000000) (-28325253 / 125000000) (Real.log (398619 / 500000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (27032013 / 200000000) ≤ -Real.log (12500 / 14309) ∧
    -Real.log (12500 / 14309) ≤ (67580033 / 500000000) := by
  have h := checkLog_sound (w := (1809 / 26809)) (n := 12)
    (lo := (27032013 / 200000000)) (hi := (67580033 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((14309 / 12500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(14309 / 12500) = 1/(12500 / 14309) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (27032013 / 200000000) (67580033 / 500000000) (Real.log (14309 / 12500)) := by
  have h := reflection_log_9_neg
  have he : Real.log (14309 / 12500) = -Real.log (12500 / 14309) := by
    rw [show ((14309 / 12500) : ℝ) = ((12500 / 14309) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (78163189 / 500000000) ≤ -Real.log (10691 / 12500) ∧
    -Real.log (10691 / 12500) ≤ (156326379 / 1000000000) := by
  have h := checkLog_sound (w := (1809 / 23191)) (n := 12)
    (lo := (78163189 / 500000000)) (hi := (156326379 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12500 / 10691) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12500 / 10691) = 1/(10691 / 12500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-156326379 / 1000000000) (-78163189 / 500000000) (Real.log (10691 / 12500)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (135428217 / 1000000000) ≤ -Real.log (1000000 / 1145027) ∧
    -Real.log (1000000 / 1145027) ≤ (67714109 / 500000000) := by
  have h := checkLog_sound (w := (145027 / 2145027)) (n := 12)
    (lo := (135428217 / 1000000000)) (hi := (67714109 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1145027 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1145027 / 1000000) = 1/(1000000 / 1145027) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (135428217 / 1000000000) (67714109 / 500000000) (Real.log (1145027 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1145027 / 1000000) = -Real.log (1000000 / 1145027) := by
    rw [show ((1145027 / 1000000) : ℝ) = ((1000000 / 1145027) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (156685389 / 1000000000) ≤ -Real.log (854973 / 1000000) ∧
    -Real.log (854973 / 1000000) ≤ (15668539 / 100000000) := by
  have h := checkLog_sound (w := (145027 / 1854973)) (n := 12)
    (lo := (156685389 / 1000000000)) (hi := (15668539 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 854973) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 854973) = 1/(854973 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-15668539 / 100000000) (-156685389 / 1000000000) (Real.log (854973 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (586571597 / 1000000000) ≤ -Real.log (20000000000 / 35956284153) ∧
    -Real.log (20000000000 / 35956284153) ≤ (293285799 / 500000000) := by
  have h := checkLog_sound (w := (15956284153 / 55956284153)) (n := 12)
    (lo := (586571597 / 1000000000)) (hi := (293285799 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((35956284153 / 20000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(35956284153 / 20000000000) = 1/(20000000000 / 35956284153) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (586571597 / 1000000000) (293285799 / 500000000) (Real.log (35956284153 / 20000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (35956284153 / 20000000000) = -Real.log (20000000000 / 35956284153) := by
    rw [show ((35956284153 / 20000000000) : ℝ) = ((20000000000 / 35956284153) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (587847429 / 1000000000) ≤ -Real.log (500000000000 / 900054689637) ∧
    -Real.log (500000000000 / 900054689637) ≤ (58784743 / 100000000) := by
  have h := checkLog_sound (w := (400054689637 / 1400054689637)) (n := 12)
    (lo := (587847429 / 1000000000)) (hi := (58784743 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((900054689637 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(900054689637 / 500000000000) = 1/(500000000000 / 900054689637) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (587847429 / 1000000000) (58784743 / 100000000) (Real.log (900054689637 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (900054689637 / 500000000000) = -Real.log (500000000000 / 900054689637) := by
    rw [show ((900054689637 / 500000000000) : ℝ) = ((500000000000 / 900054689637) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (410348751 / 1000000000) ≤ -Real.log (125000000000 / 188417922741) ∧
    -Real.log (125000000000 / 188417922741) ≤ (25646797 / 62500000) := by
  have h := checkLog_sound (w := (63417922741 / 313417922741)) (n := 12)
    (lo := (410348751 / 1000000000)) (hi := (25646797 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((188417922741 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(188417922741 / 125000000000) = 1/(125000000000 / 188417922741) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (410348751 / 1000000000) (25646797 / 62500000) (Real.log (188417922741 / 125000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (188417922741 / 125000000000) = -Real.log (125000000000 / 188417922741) := by
    rw [show ((188417922741 / 125000000000) : ℝ) = ((125000000000 / 188417922741) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (411222603 / 1000000000) ≤ -Real.log (100000000000 / 150866115263) ∧
    -Real.log (100000000000 / 150866115263) ≤ (102805651 / 250000000) := by
  have h := checkLog_sound (w := (50866115263 / 250866115263)) (n := 12)
    (lo := (411222603 / 1000000000)) (hi := (102805651 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((150866115263 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(150866115263 / 100000000000) = 1/(100000000000 / 150866115263) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (411222603 / 1000000000) (102805651 / 250000000) (Real.log (150866115263 / 100000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (150866115263 / 100000000000) = -Real.log (100000000000 / 150866115263) := by
    rw [show ((150866115263 / 100000000000) : ℝ) = ((100000000000 / 150866115263) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (291486443 / 1000000000) ≤ -Real.log (7812500000 / 10456371013) ∧
    -Real.log (7812500000 / 10456371013) ≤ (72871611 / 250000000) := by
  have h := checkLog_sound (w := (2643871013 / 18268871013)) (n := 12)
    (lo := (291486443 / 1000000000)) (hi := (72871611 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10456371013 / 7812500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10456371013 / 7812500000) = 1/(7812500000 / 10456371013) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (291486443 / 1000000000) (72871611 / 250000000) (Real.log (10456371013 / 7812500000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (10456371013 / 7812500000) = -Real.log (7812500000 / 10456371013) := by
    rw [show ((10456371013 / 7812500000) : ℝ) = ((7812500000 / 10456371013) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (292113607 / 1000000000) ≤ -Real.log (500000000000 / 669627578883) ∧
    -Real.log (500000000000 / 669627578883) ≤ (36514201 / 125000000) := by
  have h := checkLog_sound (w := (169627578883 / 1169627578883)) (n := 12)
    (lo := (292113607 / 1000000000)) (hi := (36514201 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((669627578883 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(669627578883 / 500000000000) = 1/(500000000000 / 669627578883) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (292113607 / 1000000000) (36514201 / 125000000) (Real.log (669627578883 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (669627578883 / 500000000000) = -Real.log (500000000000 / 669627578883) := by
    rw [show ((669627578883 / 500000000000) : ℝ) = ((500000000000 / 669627578883) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (21257171 / 1000000000) ≤ -Real.log (978967169271 / 1000000000000) ∧
    -Real.log (978967169271 / 1000000000000) ≤ (5314293 / 250000000) := by
  have h := checkLog_sound (w := (21032830729 / 1978967169271)) (n := 12)
    (lo := (21257171 / 1000000000)) (hi := (5314293 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 978967169271) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 978967169271) = 1/(978967169271 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-5314293 / 250000000) (-21257171 / 1000000000) (Real.log (978967169271 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (2645789 / 125000000) ≤ -Real.log (152977519 / 156250000) ∧
    -Real.log (152977519 / 156250000) ≤ (21166313 / 1000000000) := by
  have h := checkLog_sound (w := (3272481 / 309227519)) (n := 12)
    (lo := (2645789 / 125000000)) (hi := (21166313 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((156250000 / 152977519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(156250000 / 152977519) = 1/(152977519 / 156250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-21166313 / 1000000000) (-2645789 / 125000000) (Real.log (152977519 / 156250000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell060
