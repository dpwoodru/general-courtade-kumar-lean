import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell105
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

theorem reflection_log_1_neg : (67909013 / 250000000) ≤ -Real.log (2560 / 3359) ∧
    -Real.log (2560 / 3359) ≤ (271636053 / 1000000000) := by
  have h := checkLog_sound (w := (799 / 5919)) (n := 12)
    (lo := (67909013 / 250000000)) (hi := (271636053 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3359 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3359 / 2560) = 1/(2560 / 3359) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (67909013 / 250000000) (271636053 / 1000000000) (Real.log (3359 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3359 / 2560) = -Real.log (2560 / 3359) := by
    rw [show ((3359 / 2560) : ℝ) = ((2560 / 3359) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (93531357 / 250000000) ≤ -Real.log (1761 / 2560) ∧
    -Real.log (1761 / 2560) ≤ (374125429 / 1000000000) := by
  have h := checkLog_sound (w := (799 / 4321)) (n := 12)
    (lo := (93531357 / 250000000)) (hi := (374125429 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1761) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1761) = 1/(1761 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-374125429 / 1000000000) (-93531357 / 250000000) (Real.log (1761 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (27118939 / 100000000) ≤ -Real.log (1024 / 1343) ∧
    -Real.log (1024 / 1343) ≤ (271189391 / 1000000000) := by
  have h := checkLog_sound (w := (319 / 2367)) (n := 12)
    (lo := (27118939 / 100000000)) (hi := (271189391 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1343 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1343 / 1024) = 1/(1024 / 1343) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (27118939 / 100000000) (271189391 / 1000000000) (Real.log (1343 / 1024)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1343 / 1024) = -Real.log (1024 / 1343) := by
    rw [show ((1343 / 1024) : ℝ) = ((1024 / 1343) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (186637001 / 500000000) ≤ -Real.log (705 / 1024) ∧
    -Real.log (705 / 1024) ≤ (373274003 / 1000000000) := by
  have h := checkLog_sound (w := (319 / 1729)) (n := 12)
    (lo := (186637001 / 500000000)) (hi := (373274003 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 705) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 705) = 1/(705 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-373274003 / 1000000000) (-186637001 / 500000000) (Real.log (705 / 1024)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (49960133 / 250000000) ≤ -Real.log (125000 / 152651) ∧
    -Real.log (125000 / 152651) ≤ (199840533 / 1000000000) := by
  have h := checkLog_sound (w := (27651 / 277651)) (n := 12)
    (lo := (49960133 / 250000000)) (hi := (199840533 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((152651 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(152651 / 125000) = 1/(125000 / 152651) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (49960133 / 250000000) (199840533 / 1000000000) (Real.log (152651 / 125000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (152651 / 125000) = -Real.log (125000 / 152651) := by
    rw [show ((152651 / 125000) : ℝ) = ((125000 / 152651) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (250011277 / 1000000000) ≤ -Real.log (97349 / 125000) ∧
    -Real.log (97349 / 125000) ≤ (125005639 / 500000000) := by
  have h := checkLog_sound (w := (27651 / 222349)) (n := 12)
    (lo := (250011277 / 1000000000)) (hi := (125005639 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 97349) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 97349) = 1/(97349 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-125005639 / 500000000) (-250011277 / 1000000000) (Real.log (97349 / 125000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (200185213 / 1000000000) ≤ -Real.log (1000000 / 1221629) ∧
    -Real.log (1000000 / 1221629) ≤ (100092607 / 500000000) := by
  have h := checkLog_sound (w := (221629 / 2221629)) (n := 12)
    (lo := (200185213 / 1000000000)) (hi := (100092607 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1221629 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1221629 / 1000000) = 1/(1000000 / 1221629) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (200185213 / 1000000000) (100092607 / 500000000) (Real.log (1221629 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1221629 / 1000000) = -Real.log (1000000 / 1221629) := by
    rw [show ((1221629 / 1000000) : ℝ) = ((1000000 / 1221629) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (62638001 / 250000000) ≤ -Real.log (778371 / 1000000) ∧
    -Real.log (778371 / 1000000) ≤ (50110401 / 200000000) := by
  have h := checkLog_sound (w := (221629 / 1778371)) (n := 12)
    (lo := (62638001 / 250000000)) (hi := (50110401 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 778371) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 778371) = 1/(778371 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-50110401 / 200000000) (-62638001 / 250000000) (Real.log (778371 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (147184759 / 1000000000) ≤ -Real.log (125000 / 144821) ∧
    -Real.log (125000 / 144821) ≤ (3679619 / 25000000) := by
  have h := checkLog_sound (w := (19821 / 269821)) (n := 12)
    (lo := (147184759 / 1000000000)) (hi := (3679619 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((144821 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(144821 / 125000) = 1/(125000 / 144821) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (147184759 / 1000000000) (3679619 / 25000000) (Real.log (144821 / 125000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (144821 / 125000) = -Real.log (125000 / 144821) := by
    rw [show ((144821 / 125000) : ℝ) = ((125000 / 144821) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (43162519 / 250000000) ≤ -Real.log (105179 / 125000) ∧
    -Real.log (105179 / 125000) ≤ (172650077 / 1000000000) := by
  have h := checkLog_sound (w := (19821 / 230179)) (n := 12)
    (lo := (43162519 / 250000000)) (hi := (172650077 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 105179) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 105179) = 1/(105179 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-172650077 / 1000000000) (-43162519 / 250000000) (Real.log (105179 / 125000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (29490459 / 200000000) ≤ -Real.log (500000 / 579439) ∧
    -Real.log (500000 / 579439) ≤ (18431537 / 125000000) := by
  have h := checkLog_sound (w := (79439 / 1079439)) (n := 12)
    (lo := (29490459 / 200000000)) (hi := (18431537 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((579439 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(579439 / 500000) = 1/(500000 / 579439) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (29490459 / 200000000) (18431537 / 125000000) (Real.log (579439 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (579439 / 500000) = -Real.log (500000 / 579439) := by
    rw [show ((579439 / 500000) : ℝ) = ((500000 / 579439) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (43254641 / 250000000) ≤ -Real.log (420561 / 500000) ∧
    -Real.log (420561 / 500000) ≤ (34603713 / 200000000) := by
  have h := checkLog_sound (w := (79439 / 920561)) (n := 12)
    (lo := (43254641 / 250000000)) (hi := (34603713 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 420561) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 420561) = 1/(420561 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-34603713 / 200000000) (-43254641 / 250000000) (Real.log (420561 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (644463393 / 1000000000) ≤ -Real.log (500000000000 / 952482269503) ∧
    -Real.log (500000000000 / 952482269503) ≤ (322231697 / 500000000) := by
  have h := checkLog_sound (w := (452482269503 / 1452482269503)) (n := 12)
    (lo := (644463393 / 1000000000)) (hi := (322231697 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((952482269503 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(952482269503 / 500000000000) = 1/(500000000000 / 952482269503) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (644463393 / 1000000000) (322231697 / 500000000) (Real.log (952482269503 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (952482269503 / 500000000000) = -Real.log (500000000000 / 952482269503) := by
    rw [show ((952482269503 / 500000000000) : ℝ) = ((500000000000 / 952482269503) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (645761481 / 1000000000) ≤ -Real.log (50000000000 / 95371947757) ∧
    -Real.log (50000000000 / 95371947757) ≤ (322880741 / 500000000) := by
  have h := checkLog_sound (w := (45371947757 / 145371947757)) (n := 12)
    (lo := (645761481 / 1000000000)) (hi := (322880741 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((95371947757 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(95371947757 / 50000000000) = 1/(50000000000 / 95371947757) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (645761481 / 1000000000) (322880741 / 500000000) (Real.log (95371947757 / 50000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (95371947757 / 50000000000) = -Real.log (50000000000 / 95371947757) := by
    rw [show ((95371947757 / 50000000000) : ℝ) = ((50000000000 / 95371947757) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (44985181 / 100000000) ≤ -Real.log (500000000000 / 784039897687) ∧
    -Real.log (500000000000 / 784039897687) ≤ (449851811 / 1000000000) := by
  have h := checkLog_sound (w := (284039897687 / 1284039897687)) (n := 12)
    (lo := (44985181 / 100000000)) (hi := (449851811 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((784039897687 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(784039897687 / 500000000000) = 1/(500000000000 / 784039897687) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (44985181 / 100000000) (449851811 / 1000000000) (Real.log (784039897687 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (784039897687 / 500000000000) = -Real.log (500000000000 / 784039897687) := by
    rw [show ((784039897687 / 500000000000) : ℝ) = ((500000000000 / 784039897687) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (225368609 / 500000000) ≤ -Real.log (250000000000 / 392367200217) ∧
    -Real.log (250000000000 / 392367200217) ≤ (450737219 / 1000000000) := by
  have h := checkLog_sound (w := (142367200217 / 642367200217)) (n := 12)
    (lo := (225368609 / 500000000)) (hi := (450737219 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((392367200217 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(392367200217 / 250000000000) = 1/(250000000000 / 392367200217) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (225368609 / 500000000) (450737219 / 1000000000) (Real.log (392367200217 / 250000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (392367200217 / 250000000000) = -Real.log (250000000000 / 392367200217) := by
    rw [show ((392367200217 / 250000000000) : ℝ) = ((250000000000 / 392367200217) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (79958709 / 250000000) ≤ -Real.log (500000000000 / 688450165907) ∧
    -Real.log (500000000000 / 688450165907) ≤ (319834837 / 1000000000) := by
  have h := checkLog_sound (w := (188450165907 / 1188450165907)) (n := 12)
    (lo := (79958709 / 250000000)) (hi := (319834837 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((688450165907 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(688450165907 / 500000000000) = 1/(500000000000 / 688450165907) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (79958709 / 250000000) (319834837 / 1000000000) (Real.log (688450165907 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (688450165907 / 500000000000) = -Real.log (500000000000 / 688450165907) := by
    rw [show ((688450165907 / 500000000000) : ℝ) = ((500000000000 / 688450165907) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (320470859 / 1000000000) ≤ -Real.log (125000000000 / 172222043889) ∧
    -Real.log (125000000000 / 172222043889) ≤ (16023543 / 50000000) := by
  have h := checkLog_sound (w := (47222043889 / 297222043889)) (n := 12)
    (lo := (320470859 / 1000000000)) (hi := (16023543 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((172222043889 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(172222043889 / 125000000000) = 1/(125000000000 / 172222043889) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (320470859 / 1000000000) (16023543 / 50000000) (Real.log (172222043889 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (172222043889 / 125000000000) = -Real.log (125000000000 / 172222043889) := by
    rw [show ((172222043889 / 125000000000) : ℝ) = ((125000000000 / 172222043889) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (6391567 / 250000000) ≤ -Real.log (243689445279 / 250000000000) ∧
    -Real.log (243689445279 / 250000000000) ≤ (25566269 / 1000000000) := by
  have h := checkLog_sound (w := (6310554721 / 493689445279)) (n := 12)
    (lo := (6391567 / 250000000)) (hi := (25566269 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 243689445279) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 243689445279) = 1/(243689445279 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-25566269 / 1000000000) (-6391567 / 250000000) (Real.log (243689445279 / 250000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (6366329 / 250000000) ≤ -Real.log (15232127959 / 15625000000) ∧
    -Real.log (15232127959 / 15625000000) ≤ (25465317 / 1000000000) := by
  have h := checkLog_sound (w := (392872041 / 30857127959)) (n := 12)
    (lo := (6366329 / 250000000)) (hi := (25465317 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 15232127959) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 15232127959) = 1/(15232127959 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-25465317 / 1000000000) (-6366329 / 250000000) (Real.log (15232127959 / 15625000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell105
