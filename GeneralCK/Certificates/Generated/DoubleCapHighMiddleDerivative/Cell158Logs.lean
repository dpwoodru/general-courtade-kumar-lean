import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell158
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

theorem reflection_log_1_neg : (295028071 / 1000000000) ≤ -Real.log (5120 / 6877) ∧
    -Real.log (5120 / 6877) ≤ (36878509 / 125000000) := by
  have h := checkLog_sound (w := (1757 / 11997)) (n := 12)
    (lo := (295028071 / 1000000000)) (hi := (36878509 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6877 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6877 / 5120) = 1/(5120 / 6877) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (295028071 / 1000000000) (36878509 / 125000000) (Real.log (6877 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6877 / 5120) = -Real.log (5120 / 6877) := by
    rw [show ((6877 / 5120) : ℝ) = ((5120 / 6877) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (210160503 / 500000000) ≤ -Real.log (3363 / 5120) ∧
    -Real.log (3363 / 5120) ≤ (420321007 / 1000000000) := by
  have h := checkLog_sound (w := (1757 / 8483)) (n := 12)
    (lo := (210160503 / 500000000)) (hi := (420321007 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3363) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3363) = 1/(3363 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-420321007 / 1000000000) (-210160503 / 500000000) (Real.log (3363 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (294591739 / 1000000000) ≤ -Real.log (2560 / 3437) ∧
    -Real.log (2560 / 3437) ≤ (14729587 / 50000000) := by
  have h := checkLog_sound (w := (877 / 5997)) (n := 12)
    (lo := (294591739 / 1000000000)) (hi := (14729587 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3437 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3437 / 2560) = 1/(2560 / 3437) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (294591739 / 1000000000) (14729587 / 50000000) (Real.log (3437 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3437 / 2560) = -Real.log (2560 / 3437) := by
    rw [show ((3437 / 2560) : ℝ) = ((2560 / 3437) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (419429343 / 1000000000) ≤ -Real.log (1683 / 2560) ∧
    -Real.log (1683 / 2560) ≤ (13107167 / 31250000) := by
  have h := checkLog_sound (w := (877 / 4243)) (n := 12)
    (lo := (419429343 / 1000000000)) (hi := (13107167 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1683) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1683) = 1/(1683 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-13107167 / 31250000) (-419429343 / 1000000000) (Real.log (1683 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (217917921 / 1000000000) ≤ -Real.log (200000 / 248697) ∧
    -Real.log (200000 / 248697) ≤ (108958961 / 500000000) := by
  have h := checkLog_sound (w := (48697 / 448697)) (n := 12)
    (lo := (217917921 / 1000000000)) (hi := (108958961 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((248697 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(248697 / 200000) = 1/(200000 / 248697) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (217917921 / 1000000000) (108958961 / 500000000) (Real.log (248697 / 200000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (248697 / 200000) = -Real.log (200000 / 248697) := by
    rw [show ((248697 / 200000) : ℝ) = ((200000 / 248697) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (279032917 / 1000000000) ≤ -Real.log (151303 / 200000) ∧
    -Real.log (151303 / 200000) ≤ (139516459 / 500000000) := by
  have h := checkLog_sound (w := (48697 / 351303)) (n := 12)
    (lo := (279032917 / 1000000000)) (hi := (139516459 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 151303) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 151303) = 1/(151303 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-139516459 / 500000000) (-279032917 / 1000000000) (Real.log (151303 / 200000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (13641077 / 62500000) ≤ -Real.log (1000000 / 1243907) ∧
    -Real.log (1000000 / 1243907) ≤ (218257233 / 1000000000) := by
  have h := checkLog_sound (w := (243907 / 2243907)) (n := 12)
    (lo := (13641077 / 62500000)) (hi := (218257233 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1243907 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1243907 / 1000000) = 1/(1000000 / 1243907) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (13641077 / 62500000) (218257233 / 1000000000) (Real.log (1243907 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1243907 / 1000000) = -Real.log (1000000 / 1243907) := by
    rw [show ((1243907 / 1000000) : ℝ) = ((1000000 / 1243907) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (139795447 / 500000000) ≤ -Real.log (756093 / 1000000) ∧
    -Real.log (756093 / 1000000) ≤ (55918179 / 200000000) := by
  have h := checkLog_sound (w := (243907 / 1756093)) (n := 12)
    (lo := (139795447 / 500000000)) (hi := (55918179 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 756093) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 756093) = 1/(756093 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-55918179 / 200000000) (-139795447 / 500000000) (Real.log (756093 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (40326611 / 250000000) ≤ -Real.log (200000 / 235009) ∧
    -Real.log (200000 / 235009) ≤ (32261289 / 200000000) := by
  have h := checkLog_sound (w := (35009 / 435009)) (n := 12)
    (lo := (40326611 / 250000000)) (hi := (32261289 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((235009 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(235009 / 200000) = 1/(200000 / 235009) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (40326611 / 250000000) (32261289 / 200000000) (Real.log (235009 / 200000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (235009 / 200000) = -Real.log (200000 / 235009) := by
    rw [show ((235009 / 200000) : ℝ) = ((200000 / 235009) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (192426439 / 1000000000) ≤ -Real.log (164991 / 200000) ∧
    -Real.log (164991 / 200000) ≤ (4810661 / 25000000) := by
  have h := checkLog_sound (w := (35009 / 364991)) (n := 12)
    (lo := (192426439 / 1000000000)) (hi := (4810661 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 164991) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 164991) = 1/(164991 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-4810661 / 25000000) (-192426439 / 1000000000) (Real.log (164991 / 200000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (80786391 / 500000000) ≤ -Real.log (500000 / 587679) ∧
    -Real.log (500000 / 587679) ≤ (161572783 / 1000000000) := by
  have h := checkLog_sound (w := (87679 / 1087679)) (n := 12)
    (lo := (80786391 / 500000000)) (hi := (161572783 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((587679 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(587679 / 500000) = 1/(500000 / 587679) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (80786391 / 500000000) (161572783 / 1000000000) (Real.log (587679 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (587679 / 500000) = -Real.log (500000 / 587679) := by
    rw [show ((587679 / 500000) : ℝ) = ((500000 / 587679) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (96402963 / 500000000) ≤ -Real.log (412321 / 500000) ∧
    -Real.log (412321 / 500000) ≤ (192805927 / 1000000000) := by
  have h := checkLog_sound (w := (87679 / 912321)) (n := 12)
    (lo := (96402963 / 500000000)) (hi := (192805927 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 412321) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 412321) = 1/(412321 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-192805927 / 1000000000) (-96402963 / 500000000) (Real.log (412321 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (357010541 / 500000000) ≤ -Real.log (500000000000 / 1021093285799) ∧
    -Real.log (500000000000 / 1021093285799) ≤ (178505271 / 250000000) := by
  have h := checkLog_sound (w := (21093285799 / 2021093285799)) (n := 12)
    (lo := (10436951 / 500000000)) (hi := (20873903 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1021093285799 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1021093285799 / 1000000000000) = 1/(500000000000 / 1021093285799) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (357010541 / 500000000) (178505271 / 250000000) (Real.log (1021093285799 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1021093285799 / 500000000000) = -Real.log (500000000000 / 1021093285799) := by
    rw [show ((1021093285799 / 500000000000) : ℝ) = ((500000000000 / 1021093285799) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (715349077 / 1000000000) ≤ -Real.log (781250000 / 1597578427) ∧
    -Real.log (781250000 / 1597578427) ≤ (715349079 / 1000000000) := by
  have h := checkLog_sound (w := (35078427 / 3160078427)) (n := 12)
    (lo := (22201897 / 1000000000)) (hi := (11100949 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1597578427 / 1562500000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1597578427 / 1562500000) = 1/(781250000 / 1597578427) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (715349077 / 1000000000) (715349079 / 1000000000) (Real.log (1597578427 / 781250000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (1597578427 / 781250000) = -Real.log (781250000 / 1597578427) := by
    rw [show ((1597578427 / 781250000) : ℝ) = ((781250000 / 1597578427) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (496950839 / 1000000000) ≤ -Real.log (500000000000 / 821850855567) ∧
    -Real.log (500000000000 / 821850855567) ≤ (12423771 / 25000000) := by
  have h := checkLog_sound (w := (321850855567 / 1321850855567)) (n := 12)
    (lo := (496950839 / 1000000000)) (hi := (12423771 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((821850855567 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(821850855567 / 500000000000) = 1/(500000000000 / 821850855567) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (496950839 / 1000000000) (12423771 / 25000000) (Real.log (821850855567 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (821850855567 / 500000000000) = -Real.log (500000000000 / 821850855567) := by
    rw [show ((821850855567 / 500000000000) : ℝ) = ((500000000000 / 821850855567) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (497848127 / 1000000000) ≤ -Real.log (250000000000 / 411294311679) ∧
    -Real.log (250000000000 / 411294311679) ≤ (7778877 / 15625000) := by
  have h := checkLog_sound (w := (161294311679 / 661294311679)) (n := 12)
    (lo := (497848127 / 1000000000)) (hi := (7778877 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((411294311679 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(411294311679 / 250000000000) = 1/(250000000000 / 411294311679) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (497848127 / 1000000000) (7778877 / 15625000) (Real.log (411294311679 / 250000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (411294311679 / 250000000000) = -Real.log (250000000000 / 411294311679) := by
    rw [show ((411294311679 / 250000000000) : ℝ) = ((250000000000 / 411294311679) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (88433221 / 250000000) ≤ -Real.log (50000000000 / 71218733143) ∧
    -Real.log (50000000000 / 71218733143) ≤ (70746577 / 200000000) := by
  have h := checkLog_sound (w := (21218733143 / 121218733143)) (n := 12)
    (lo := (88433221 / 250000000)) (hi := (70746577 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((71218733143 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(71218733143 / 50000000000) = 1/(50000000000 / 71218733143) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (88433221 / 250000000) (70746577 / 200000000) (Real.log (71218733143 / 50000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (71218733143 / 50000000000) = -Real.log (50000000000 / 71218733143) := by
    rw [show ((71218733143 / 50000000000) : ℝ) = ((50000000000 / 71218733143) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (88594677 / 250000000) ≤ -Real.log (125000000000 / 178161856903) ∧
    -Real.log (125000000000 / 178161856903) ≤ (354378709 / 1000000000) := by
  have h := checkLog_sound (w := (53161856903 / 303161856903)) (n := 12)
    (lo := (88594677 / 250000000)) (hi := (354378709 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((178161856903 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(178161856903 / 125000000000) = 1/(125000000000 / 178161856903) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (88594677 / 250000000) (354378709 / 1000000000) (Real.log (178161856903 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (178161856903 / 125000000000) = -Real.log (125000000000 / 178161856903) := by
    rw [show ((178161856903 / 125000000000) : ℝ) = ((125000000000 / 178161856903) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (3904143 / 125000000) ≤ -Real.log (242312392959 / 250000000000) ∧
    -Real.log (242312392959 / 250000000000) ≤ (6246629 / 200000000) := by
  have h := checkLog_sound (w := (7687607041 / 492312392959)) (n := 12)
    (lo := (3904143 / 125000000)) (hi := (6246629 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 242312392959) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 242312392959) = 1/(242312392959 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-6246629 / 200000000) (-3904143 / 125000000) (Real.log (242312392959 / 250000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (15559997 / 500000000) ≤ -Real.log (38774369919 / 40000000000) ∧
    -Real.log (38774369919 / 40000000000) ≤ (6223999 / 200000000) := by
  have h := checkLog_sound (w := (1225630081 / 78774369919)) (n := 12)
    (lo := (15559997 / 500000000)) (hi := (6223999 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 38774369919) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 38774369919) = 1/(38774369919 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-6223999 / 200000000) (-15559997 / 500000000) (Real.log (38774369919 / 40000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell158
