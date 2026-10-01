import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0191
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

theorem reflection_log_1_neg : (269699077 / 1000000000) ≤ -Real.log (1024 / 1341) ∧
    -Real.log (1024 / 1341) ≤ (134849539 / 500000000) := by
  have h := checkLog_sound (w := (317 / 2365)) (n := 12)
    (lo := (269699077 / 1000000000)) (hi := (134849539 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1341 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1341 / 1024) = 1/(1024 / 1341) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (269699077 / 1000000000) (134849539 / 500000000) (Real.log (1341 / 1024)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1341 / 1024) = -Real.log (1024 / 1341) := by
    rw [show ((1341 / 1024) : ℝ) = ((1024 / 1341) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (370441139 / 1000000000) ≤ -Real.log (707 / 1024) ∧
    -Real.log (707 / 1024) ≤ (18522057 / 50000000) := by
  have h := checkLog_sound (w := (317 / 1731)) (n := 12)
    (lo := (370441139 / 1000000000)) (hi := (18522057 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 707) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 707) = 1/(707 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-18522057 / 50000000) (-370441139 / 1000000000) (Real.log (707 / 1024)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (5385031 / 20000000) ≤ -Real.log (2560 / 3351) ∧
    -Real.log (2560 / 3351) ≤ (269251551 / 1000000000) := by
  have h := checkLog_sound (w := (791 / 5911)) (n := 12)
    (lo := (5385031 / 20000000)) (hi := (269251551 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3351 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3351 / 2560) = 1/(2560 / 3351) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (5385031 / 20000000) (269251551 / 1000000000) (Real.log (3351 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3351 / 2560) = -Real.log (2560 / 3351) := by
    rw [show ((3351 / 2560) : ℝ) = ((2560 / 3351) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (369592843 / 1000000000) ≤ -Real.log (1769 / 2560) ∧
    -Real.log (1769 / 2560) ≤ (92398211 / 250000000) := by
  have h := checkLog_sound (w := (791 / 4329)) (n := 12)
    (lo := (369592843 / 1000000000)) (hi := (92398211 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1769) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1769) = 1/(1769 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-92398211 / 250000000) (-369592843 / 1000000000) (Real.log (1769 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (48189553 / 100000000) ≤ -Real.log (512 / 829) ∧
    -Real.log (512 / 829) ≤ (481895531 / 1000000000) := by
  have h := checkLog_sound (w := (317 / 1341)) (n := 12)
    (lo := (48189553 / 100000000)) (hi := (481895531 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((829 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(829 / 512) = 1/(512 / 829) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (48189553 / 100000000) (481895531 / 1000000000) (Real.log (829 / 512)) := by
  have h := reflection_log_5_neg
  have he : Real.log (829 / 512) = -Real.log (512 / 829) := by
    rw [show ((829 / 512) : ℝ) = ((512 / 829) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (193065013 / 200000000) ≤ -Real.log (195 / 512) ∧
    -Real.log (195 / 512) ≤ (965325067 / 1000000000) := by
  have h := checkLog_sound (w := (61 / 451)) (n := 12)
    (lo := (54435577 / 200000000)) (hi := (136088943 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((256 / 195) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(256 / 195) = 1/(195 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-965325067 / 1000000000) (-193065013 / 200000000) (Real.log (195 / 512)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (30073219 / 62500000) ≤ -Real.log (1280 / 2071) ∧
    -Real.log (1280 / 2071) ≤ (96234301 / 200000000) := by
  have h := checkLog_sound (w := (791 / 3351)) (n := 12)
    (lo := (30073219 / 62500000)) (hi := (96234301 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2071 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2071 / 1280) = 1/(1280 / 2071) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (30073219 / 62500000) (96234301 / 200000000) (Real.log (2071 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2071 / 1280) = -Real.log (1280 / 2071) := by
    rw [show ((2071 / 1280) : ℝ) = ((1280 / 2071) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (481126433 / 500000000) ≤ -Real.log (489 / 1280) ∧
    -Real.log (489 / 1280) ≤ (240563217 / 250000000) := by
  have h := checkLog_sound (w := (151 / 1129)) (n := 12)
    (lo := (134552843 / 500000000)) (hi := (269105687 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 489) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 489) = 1/(489 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-240563217 / 250000000) (-481126433 / 500000000) (Real.log (489 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (368335593 / 1000000000) ≤ -Real.log (1000000 / 1445327) ∧
    -Real.log (1000000 / 1445327) ≤ (184167797 / 500000000) := by
  have h := checkLog_sound (w := (445327 / 2445327)) (n := 12)
    (lo := (368335593 / 1000000000)) (hi := (184167797 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1445327 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1445327 / 1000000) = 1/(1000000 / 1445327) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (368335593 / 1000000000) (184167797 / 500000000) (Real.log (1445327 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1445327 / 1000000) = -Real.log (1000000 / 1445327) := by
    rw [show ((1445327 / 1000000) : ℝ) = ((1000000 / 1445327) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (36836033 / 62500000) ≤ -Real.log (554673 / 1000000) ∧
    -Real.log (554673 / 1000000) ≤ (589376529 / 1000000000) := by
  have h := checkLog_sound (w := (445327 / 1554673)) (n := 12)
    (lo := (36836033 / 62500000)) (hi := (589376529 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 554673) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 554673) = 1/(554673 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-589376529 / 1000000000) (-36836033 / 62500000) (Real.log (554673 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (92236931 / 250000000) ≤ -Real.log (250000 / 361553) ∧
    -Real.log (250000 / 361553) ≤ (14757909 / 40000000) := by
  have h := checkLog_sound (w := (111553 / 611553)) (n := 12)
    (lo := (92236931 / 250000000)) (hi := (14757909 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((361553 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(361553 / 250000) = 1/(250000 / 361553) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (92236931 / 250000000) (14757909 / 40000000) (Real.log (361553 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (361553 / 250000) = -Real.log (250000 / 361553) := by
    rw [show ((361553 / 250000) : ℝ) = ((250000 / 361553) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (73871667 / 125000000) ≤ -Real.log (138447 / 250000) ∧
    -Real.log (138447 / 250000) ≤ (590973337 / 1000000000) := by
  have h := checkLog_sound (w := (111553 / 388447)) (n := 12)
    (lo := (73871667 / 125000000)) (hi := (590973337 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 138447) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 138447) = 1/(138447 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-590973337 / 1000000000) (-73871667 / 125000000) (Real.log (138447 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (71884453 / 250000000) ≤ -Real.log (1000000 / 1333141) ∧
    -Real.log (1000000 / 1333141) ≤ (287537813 / 1000000000) := by
  have h := checkLog_sound (w := (333141 / 2333141)) (n := 12)
    (lo := (71884453 / 250000000)) (hi := (287537813 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1333141 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1333141 / 1000000) = 1/(1000000 / 1333141) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (71884453 / 250000000) (287537813 / 1000000000) (Real.log (1333141 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1333141 / 1000000) = -Real.log (1000000 / 1333141) := by
    rw [show ((1333141 / 1000000) : ℝ) = ((1000000 / 1333141) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (405176649 / 1000000000) ≤ -Real.log (666859 / 1000000) ∧
    -Real.log (666859 / 1000000) ≤ (8103533 / 20000000) := by
  have h := checkLog_sound (w := (333141 / 1666859)) (n := 12)
    (lo := (405176649 / 1000000000)) (hi := (8103533 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 666859) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 666859) = 1/(666859 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-8103533 / 20000000) (-405176649 / 1000000000) (Real.log (666859 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (144045619 / 500000000) ≤ -Real.log (1000000 / 1333879) ∧
    -Real.log (1000000 / 1333879) ≤ (288091239 / 1000000000) := by
  have h := checkLog_sound (w := (333879 / 2333879)) (n := 12)
    (lo := (144045619 / 500000000)) (hi := (288091239 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1333879 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1333879 / 1000000) = 1/(1000000 / 1333879) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (144045619 / 500000000) (288091239 / 1000000000) (Real.log (1333879 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1333879 / 1000000) = -Real.log (1000000 / 1333879) := by
    rw [show ((1333879 / 1000000) : ℝ) = ((1000000 / 1333879) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (406283943 / 1000000000) ≤ -Real.log (666121 / 1000000) ∧
    -Real.log (666121 / 1000000) ≤ (50785493 / 125000000) := by
  have h := checkLog_sound (w := (333879 / 1666121)) (n := 12)
    (lo := (406283943 / 1000000000)) (hi := (50785493 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 666121) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 666121) = 1/(666121 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-50785493 / 125000000) (-406283943 / 1000000000) (Real.log (666121 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (957712121 / 1000000000) ≤ -Real.log (500000000000 / 1302864029797) ∧
    -Real.log (500000000000 / 1302864029797) ≤ (957712123 / 1000000000) := by
  have h := checkLog_sound (w := (302864029797 / 2302864029797)) (n := 12)
    (lo := (264564941 / 1000000000)) (hi := (132282471 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1302864029797 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1302864029797 / 1000000000000) = 1/(500000000000 / 1302864029797) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (957712121 / 1000000000) (957712123 / 1000000000) (Real.log (1302864029797 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1302864029797 / 500000000000) = -Real.log (500000000000 / 1302864029797) := by
    rw [show ((1302864029797 / 500000000000) : ℝ) = ((500000000000 / 1302864029797) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (47996053 / 50000000) ≤ -Real.log (250000000000 / 652872579399) ∧
    -Real.log (250000000000 / 652872579399) ≤ (479960531 / 500000000) := by
  have h := checkLog_sound (w := (152872579399 / 1152872579399)) (n := 12)
    (lo := (6669347 / 25000000)) (hi := (266773881 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((652872579399 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(652872579399 / 500000000000) = 1/(250000000000 / 652872579399) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (47996053 / 50000000) (479960531 / 500000000) (Real.log (652872579399 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (652872579399 / 250000000000) = -Real.log (250000000000 / 652872579399) := by
    rw [show ((652872579399 / 250000000000) : ℝ) = ((250000000000 / 652872579399) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (692714461 / 1000000000) ≤ -Real.log (125000000000 / 249891843703) ∧
    -Real.log (125000000000 / 249891843703) ≤ (346357231 / 500000000) := by
  have h := checkLog_sound (w := (124891843703 / 374891843703)) (n := 12)
    (lo := (692714461 / 1000000000)) (hi := (346357231 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((249891843703 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(249891843703 / 125000000000) = 1/(125000000000 / 249891843703) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (692714461 / 1000000000) (346357231 / 500000000) (Real.log (249891843703 / 125000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (249891843703 / 125000000000) = -Real.log (125000000000 / 249891843703) := by
    rw [show ((249891843703 / 125000000000) : ℝ) = ((125000000000 / 249891843703) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (694375181 / 1000000000) ≤ -Real.log (500000000000 / 1001228755737) ∧
    -Real.log (500000000000 / 1001228755737) ≤ (694375183 / 1000000000) := by
  have h := checkLog_sound (w := (1228755737 / 2001228755737)) (n := 12)
    (lo := (1228001 / 1000000000)) (hi := (614001 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1001228755737 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1001228755737 / 1000000000000) = 1/(500000000000 / 1001228755737) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (694375181 / 1000000000) (694375183 / 1000000000) (Real.log (1001228755737 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1001228755737 / 500000000000) = -Real.log (500000000000 / 1001228755737) := by
    rw [show ((1001228755737 / 500000000000) : ℝ) = ((500000000000 / 1001228755737) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0191
