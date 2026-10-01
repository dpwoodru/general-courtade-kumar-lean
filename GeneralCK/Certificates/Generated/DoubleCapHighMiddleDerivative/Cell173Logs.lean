import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell173
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

theorem reflection_log_1_neg : (150775153 / 500000000) ≤ -Real.log (2560 / 3461) ∧
    -Real.log (2560 / 3461) ≤ (301550307 / 1000000000) := by
  have h := checkLog_sound (w := (901 / 6021)) (n := 12)
    (lo := (150775153 / 500000000)) (hi := (301550307 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3461 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3461 / 2560) = 1/(2560 / 3461) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (150775153 / 500000000) (301550307 / 1000000000) (Real.log (3461 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3461 / 2560) = -Real.log (2560 / 3461) := by
    rw [show ((3461 / 2560) : ℝ) = ((2560 / 3461) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (433792247 / 1000000000) ≤ -Real.log (1659 / 2560) ∧
    -Real.log (1659 / 2560) ≤ (54224031 / 125000000) := by
  have h := checkLog_sound (w := (901 / 4219)) (n := 12)
    (lo := (433792247 / 1000000000)) (hi := (54224031 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1659) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1659) = 1/(1659 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-54224031 / 125000000) (-433792247 / 1000000000) (Real.log (1659 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (301116811 / 1000000000) ≤ -Real.log (5120 / 6919) ∧
    -Real.log (5120 / 6919) ≤ (75279203 / 250000000) := by
  have h := checkLog_sound (w := (1799 / 12039)) (n := 12)
    (lo := (301116811 / 1000000000)) (hi := (75279203 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6919 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6919 / 5120) = 1/(5120 / 6919) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (301116811 / 1000000000) (75279203 / 250000000) (Real.log (6919 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6919 / 5120) = -Real.log (5120 / 6919) := by
    rw [show ((6919 / 5120) : ℝ) = ((5120 / 6919) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (27055531 / 62500000) ≤ -Real.log (3321 / 5120) ∧
    -Real.log (3321 / 5120) ≤ (432888497 / 1000000000) := by
  have h := checkLog_sound (w := (1799 / 8441)) (n := 12)
    (lo := (27055531 / 62500000)) (hi := (432888497 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3321) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3321) = 1/(3321 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-432888497 / 1000000000) (-27055531 / 62500000) (Real.log (3321 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (111492569 / 500000000) ≤ -Real.log (500000 / 624901) ∧
    -Real.log (500000 / 624901) ≤ (222985139 / 1000000000) := by
  have h := checkLog_sound (w := (124901 / 1124901)) (n := 12)
    (lo := (111492569 / 500000000)) (hi := (222985139 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((624901 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(624901 / 500000) = 1/(500000 / 624901) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (111492569 / 500000000) (222985139 / 1000000000) (Real.log (624901 / 500000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (624901 / 500000) = -Real.log (500000 / 624901) := by
    rw [show ((624901 / 500000) : ℝ) = ((500000 / 624901) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (287418107 / 1000000000) ≤ -Real.log (375099 / 500000) ∧
    -Real.log (375099 / 500000) ≤ (71854527 / 250000000) := by
  have h := checkLog_sound (w := (124901 / 875099)) (n := 12)
    (lo := (287418107 / 1000000000)) (hi := (71854527 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 375099) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 375099) = 1/(375099 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-71854527 / 250000000) (-287418107 / 1000000000) (Real.log (375099 / 500000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (44664547 / 200000000) ≤ -Real.log (62500 / 78139) ∧
    -Real.log (62500 / 78139) ≤ (13957671 / 62500000) := by
  have h := checkLog_sound (w := (15639 / 140639)) (n := 12)
    (lo := (44664547 / 200000000)) (hi := (13957671 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((78139 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(78139 / 62500) = 1/(62500 / 78139) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (44664547 / 200000000) (13957671 / 62500000) (Real.log (78139 / 62500)) := by
  have h := reflection_log_7_neg
  have he : Real.log (78139 / 62500) = -Real.log (62500 / 78139) := by
    rw [show ((78139 / 62500) : ℝ) = ((62500 / 78139) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (287980783 / 1000000000) ≤ -Real.log (46861 / 62500) ∧
    -Real.log (46861 / 62500) ≤ (17998799 / 62500000) := by
  have h := checkLog_sound (w := (15639 / 109361)) (n := 12)
    (lo := (287980783 / 1000000000)) (hi := (17998799 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 46861) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 46861) = 1/(46861 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-17998799 / 62500000) (-287980783 / 1000000000) (Real.log (46861 / 62500)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (33059493 / 200000000) ≤ -Real.log (31250 / 36867) ∧
    -Real.log (31250 / 36867) ≤ (82648733 / 500000000) := by
  have h := checkLog_sound (w := (5617 / 68117)) (n := 12)
    (lo := (33059493 / 200000000)) (hi := (82648733 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((36867 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(36867 / 31250) = 1/(31250 / 36867) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (33059493 / 200000000) (82648733 / 500000000) (Real.log (36867 / 31250)) := by
  have h := reflection_log_9_neg
  have he : Real.log (36867 / 31250) = -Real.log (31250 / 36867) := by
    rw [show ((36867 / 31250) : ℝ) = ((31250 / 36867) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (24767349 / 125000000) ≤ -Real.log (25633 / 31250) ∧
    -Real.log (25633 / 31250) ≤ (198138793 / 1000000000) := by
  have h := checkLog_sound (w := (5617 / 56883)) (n := 12)
    (lo := (24767349 / 125000000)) (hi := (198138793 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 25633) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31250 / 25633) = 1/(25633 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-198138793 / 1000000000) (-24767349 / 125000000) (Real.log (25633 / 31250)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (165563589 / 1000000000) ≤ -Real.log (500000 / 590029) ∧
    -Real.log (500000 / 590029) ≤ (16556359 / 100000000) := by
  have h := checkLog_sound (w := (90029 / 1090029)) (n := 12)
    (lo := (165563589 / 1000000000)) (hi := (16556359 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((590029 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(590029 / 500000) = 1/(500000 / 590029) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (165563589 / 1000000000) (16556359 / 100000000) (Real.log (590029 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (590029 / 500000) = -Real.log (500000 / 590029) := by
    rw [show ((590029 / 500000) : ℝ) = ((500000 / 590029) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (24815209 / 125000000) ≤ -Real.log (409971 / 500000) ∧
    -Real.log (409971 / 500000) ≤ (198521673 / 1000000000) := by
  have h := checkLog_sound (w := (90029 / 909971)) (n := 12)
    (lo := (24815209 / 125000000)) (hi := (198521673 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 409971) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 409971) = 1/(409971 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-198521673 / 1000000000) (-24815209 / 125000000) (Real.log (409971 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (734005307 / 1000000000) ≤ -Real.log (500000000000 / 1041704305931) ∧
    -Real.log (500000000000 / 1041704305931) ≤ (734005309 / 1000000000) := by
  have h := checkLog_sound (w := (41704305931 / 2041704305931)) (n := 12)
    (lo := (40858127 / 1000000000)) (hi := (2553633 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1041704305931 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1041704305931 / 1000000000000) = 1/(500000000000 / 1041704305931) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (734005307 / 1000000000) (734005309 / 1000000000) (Real.log (1041704305931 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1041704305931 / 500000000000) = -Real.log (500000000000 / 1041704305931) := by
    rw [show ((1041704305931 / 500000000000) : ℝ) = ((500000000000 / 1041704305931) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (91917819 / 125000000) ≤ -Real.log (12500000000 / 26077456299) ∧
    -Real.log (12500000000 / 26077456299) ≤ (367671277 / 500000000) := by
  have h := checkLog_sound (w := (1077456299 / 51077456299)) (n := 12)
    (lo := (10548843 / 250000000)) (hi := (42195373 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((26077456299 / 25000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(26077456299 / 25000000000) = 1/(12500000000 / 26077456299) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (91917819 / 125000000) (367671277 / 500000000) (Real.log (26077456299 / 12500000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (26077456299 / 12500000000) = -Real.log (12500000000 / 26077456299) := by
    rw [show ((26077456299 / 12500000000) : ℝ) = ((12500000000 / 26077456299) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (255201623 / 500000000) ≤ -Real.log (125000000000 / 208245356559) ∧
    -Real.log (125000000000 / 208245356559) ≤ (510403247 / 1000000000) := by
  have h := checkLog_sound (w := (83245356559 / 333245356559)) (n := 12)
    (lo := (255201623 / 500000000)) (hi := (510403247 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((208245356559 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(208245356559 / 125000000000) = 1/(125000000000 / 208245356559) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (255201623 / 500000000) (510403247 / 1000000000) (Real.log (208245356559 / 125000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (208245356559 / 125000000000) = -Real.log (125000000000 / 208245356559) := by
    rw [show ((208245356559 / 125000000000) : ℝ) = ((125000000000 / 208245356559) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (255651759 / 500000000) ≤ -Real.log (500000000000 / 833731674527) ∧
    -Real.log (500000000000 / 833731674527) ≤ (511303519 / 1000000000) := by
  have h := checkLog_sound (w := (333731674527 / 1333731674527)) (n := 12)
    (lo := (255651759 / 500000000)) (hi := (511303519 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((833731674527 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(833731674527 / 500000000000) = 1/(500000000000 / 833731674527) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (255651759 / 500000000) (511303519 / 1000000000) (Real.log (833731674527 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (833731674527 / 500000000000) = -Real.log (500000000000 / 833731674527) := by
    rw [show ((833731674527 / 500000000000) : ℝ) = ((500000000000 / 833731674527) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (181718129 / 500000000) ≤ -Real.log (500000000000 / 719131588187) ∧
    -Real.log (500000000000 / 719131588187) ≤ (363436259 / 1000000000) := by
  have h := checkLog_sound (w := (219131588187 / 1219131588187)) (n := 12)
    (lo := (181718129 / 500000000)) (hi := (363436259 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((719131588187 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(719131588187 / 500000000000) = 1/(500000000000 / 719131588187) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (181718129 / 500000000) (363436259 / 1000000000) (Real.log (719131588187 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (719131588187 / 500000000000) = -Real.log (500000000000 / 719131588187) := by
    rw [show ((719131588187 / 500000000000) : ℝ) = ((500000000000 / 719131588187) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (182042631 / 500000000) ≤ -Real.log (125000000000 / 179899614851) ∧
    -Real.log (125000000000 / 179899614851) ≤ (364085263 / 1000000000) := by
  have h := checkLog_sound (w := (54899614851 / 304899614851)) (n := 12)
    (lo := (182042631 / 500000000)) (hi := (364085263 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((179899614851 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(179899614851 / 125000000000) = 1/(125000000000 / 179899614851) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (182042631 / 500000000) (364085263 / 1000000000) (Real.log (179899614851 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (179899614851 / 125000000000) = -Real.log (125000000000 / 179899614851) := by
    rw [show ((179899614851 / 125000000000) : ℝ) = ((125000000000 / 179899614851) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (32958083 / 1000000000) ≤ -Real.log (241894779159 / 250000000000) ∧
    -Real.log (241894779159 / 250000000000) ≤ (8239521 / 250000000) := by
  have h := checkLog_sound (w := (8105220841 / 491894779159)) (n := 12)
    (lo := (32958083 / 1000000000)) (hi := (8239521 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 241894779159) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 241894779159) = 1/(241894779159 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-8239521 / 250000000) (-32958083 / 1000000000) (Real.log (241894779159 / 250000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (16420663 / 500000000) ≤ -Real.log (945011811 / 976562500) ∧
    -Real.log (945011811 / 976562500) ≤ (32841327 / 1000000000) := by
  have h := checkLog_sound (w := (31550689 / 1921574311)) (n := 12)
    (lo := (16420663 / 500000000)) (hi := (32841327 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((976562500 / 945011811) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(976562500 / 945011811) = 1/(945011811 / 976562500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-32841327 / 1000000000) (-16420663 / 500000000) (Real.log (945011811 / 976562500)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell173
