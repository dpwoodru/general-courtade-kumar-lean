import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell198
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

theorem reflection_log_1_neg : (156163523 / 500000000) ≤ -Real.log (5120 / 6997) ∧
    -Real.log (5120 / 6997) ≤ (312327047 / 1000000000) := by
  have h := checkLog_sound (w := (1877 / 12117)) (n := 12)
    (lo := (156163523 / 500000000)) (hi := (312327047 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6997 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6997 / 5120) = 1/(5120 / 6997) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (156163523 / 500000000) (312327047 / 1000000000) (Real.log (6997 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6997 / 5120) = -Real.log (5120 / 6997) := by
    rw [show ((6997 / 5120) : ℝ) = ((5120 / 6997) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (456655611 / 1000000000) ≤ -Real.log (3243 / 5120) ∧
    -Real.log (3243 / 5120) ≤ (114163903 / 250000000) := by
  have h := checkLog_sound (w := (1877 / 8363)) (n := 12)
    (lo := (456655611 / 1000000000)) (hi := (114163903 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3243) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3243) = 1/(3243 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-114163903 / 250000000) (-456655611 / 1000000000) (Real.log (3243 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (311898199 / 1000000000) ≤ -Real.log (2560 / 3497) ∧
    -Real.log (2560 / 3497) ≤ (1559491 / 5000000) := by
  have h := checkLog_sound (w := (937 / 6057)) (n := 12)
    (lo := (311898199 / 1000000000)) (hi := (1559491 / 5000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3497 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3497 / 2560) = 1/(2560 / 3497) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (311898199 / 1000000000) (1559491 / 5000000) (Real.log (3497 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3497 / 2560) = -Real.log (2560 / 3497) := by
    rw [show ((3497 / 2560) : ℝ) = ((2560 / 3497) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (455730969 / 1000000000) ≤ -Real.log (1623 / 2560) ∧
    -Real.log (1623 / 2560) ≤ (45573097 / 100000000) := by
  have h := checkLog_sound (w := (937 / 4183)) (n := 12)
    (lo := (455730969 / 1000000000)) (hi := (45573097 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1623) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1623) = 1/(1623 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-45573097 / 100000000) (-455730969 / 1000000000) (Real.log (1623 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (115691953 / 500000000) ≤ -Real.log (1000000 / 1260343) ∧
    -Real.log (1000000 / 1260343) ≤ (231383907 / 1000000000) := by
  have h := checkLog_sound (w := (260343 / 2260343)) (n := 12)
    (lo := (115691953 / 500000000)) (hi := (231383907 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1260343 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1260343 / 1000000) = 1/(1000000 / 1260343) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (115691953 / 500000000) (231383907 / 1000000000) (Real.log (1260343 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1260343 / 1000000) = -Real.log (1000000 / 1260343) := by
    rw [show ((1260343 / 1000000) : ℝ) = ((1000000 / 1260343) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (301568713 / 1000000000) ≤ -Real.log (739657 / 1000000) ∧
    -Real.log (739657 / 1000000) ≤ (150784357 / 500000000) := by
  have h := checkLog_sound (w := (260343 / 1739657)) (n := 12)
    (lo := (301568713 / 1000000000)) (hi := (150784357 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 739657) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 739657) = 1/(739657 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-150784357 / 500000000) (-301568713 / 1000000000) (Real.log (739657 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (14482467 / 62500000) ≤ -Real.log (500000 / 630383) ∧
    -Real.log (500000 / 630383) ≤ (231719473 / 1000000000) := by
  have h := checkLog_sound (w := (130383 / 1130383)) (n := 12)
    (lo := (14482467 / 62500000)) (hi := (231719473 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((630383 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(630383 / 500000) = 1/(500000 / 630383) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (14482467 / 62500000) (231719473 / 1000000000) (Real.log (630383 / 500000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (630383 / 500000) = -Real.log (500000 / 630383) := by
    rw [show ((630383 / 500000) : ℝ) = ((500000 / 630383) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (75535191 / 250000000) ≤ -Real.log (369617 / 500000) ∧
    -Real.log (369617 / 500000) ≤ (60428153 / 200000000) := by
  have h := checkLog_sound (w := (130383 / 869617)) (n := 12)
    (lo := (75535191 / 250000000)) (hi := (60428153 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 369617) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 369617) = 1/(369617 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-60428153 / 200000000) (-75535191 / 250000000) (Real.log (369617 / 500000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (21493071 / 125000000) ≤ -Real.log (250000 / 296903) ∧
    -Real.log (250000 / 296903) ≤ (171944569 / 1000000000) := by
  have h := checkLog_sound (w := (46903 / 546903)) (n := 12)
    (lo := (21493071 / 125000000)) (hi := (171944569 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((296903 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(296903 / 250000) = 1/(250000 / 296903) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (21493071 / 125000000) (171944569 / 1000000000) (Real.log (296903 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (296903 / 250000) = -Real.log (250000 / 296903) := by
    rw [show ((296903 / 250000) : ℝ) = ((250000 / 296903) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (10388861 / 50000000) ≤ -Real.log (203097 / 250000) ∧
    -Real.log (203097 / 250000) ≤ (207777221 / 1000000000) := by
  have h := checkLog_sound (w := (46903 / 453097)) (n := 12)
    (lo := (10388861 / 50000000)) (hi := (207777221 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 203097) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 203097) = 1/(203097 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-207777221 / 1000000000) (-10388861 / 50000000) (Real.log (203097 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (86105727 / 500000000) ≤ -Real.log (1000000 / 1187929) ∧
    -Real.log (1000000 / 1187929) ≤ (34442291 / 200000000) := by
  have h := checkLog_sound (w := (187929 / 2187929)) (n := 12)
    (lo := (86105727 / 500000000)) (hi := (34442291 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1187929 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1187929 / 1000000) = 1/(1000000 / 1187929) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (86105727 / 500000000) (34442291 / 200000000) (Real.log (1187929 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1187929 / 1000000) = -Real.log (1000000 / 1187929) := by
    rw [show ((1187929 / 1000000) : ℝ) = ((1000000 / 1187929) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (13010469 / 62500000) ≤ -Real.log (812071 / 1000000) ∧
    -Real.log (812071 / 1000000) ≤ (41633501 / 200000000) := by
  have h := checkLog_sound (w := (187929 / 1812071)) (n := 12)
    (lo := (13010469 / 62500000)) (hi := (41633501 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 812071) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 812071) = 1/(812071 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-41633501 / 200000000) (-13010469 / 62500000) (Real.log (812071 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (47976823 / 62500000) ≤ -Real.log (500000000000 / 1077325939617) ∧
    -Real.log (500000000000 / 1077325939617) ≤ (76762917 / 100000000) := by
  have h := checkLog_sound (w := (77325939617 / 2077325939617)) (n := 12)
    (lo := (18620497 / 250000000)) (hi := (74481989 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1077325939617 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1077325939617 / 1000000000000) = 1/(500000000000 / 1077325939617) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (47976823 / 62500000) (76762917 / 100000000) (Real.log (1077325939617 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1077325939617 / 500000000000) = -Real.log (500000000000 / 1077325939617) := by
    rw [show ((1077325939617 / 500000000000) : ℝ) = ((500000000000 / 1077325939617) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (768982657 / 1000000000) ≤ -Real.log (125000000000 / 269696268887) ∧
    -Real.log (125000000000 / 269696268887) ≤ (768982659 / 1000000000) := by
  have h := checkLog_sound (w := (19696268887 / 519696268887)) (n := 12)
    (lo := (75835477 / 1000000000)) (hi := (37917739 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((269696268887 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(269696268887 / 250000000000) = 1/(125000000000 / 269696268887) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (768982657 / 1000000000) (768982659 / 1000000000) (Real.log (269696268887 / 125000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (269696268887 / 125000000000) = -Real.log (125000000000 / 269696268887) := by
    rw [show ((269696268887 / 125000000000) : ℝ) = ((125000000000 / 269696268887) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (532952619 / 1000000000) ≤ -Real.log (500000000000 / 851978011429) ∧
    -Real.log (500000000000 / 851978011429) ≤ (26647631 / 50000000) := by
  have h := checkLog_sound (w := (351978011429 / 1351978011429)) (n := 12)
    (lo := (532952619 / 1000000000)) (hi := (26647631 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((851978011429 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(851978011429 / 500000000000) = 1/(500000000000 / 851978011429) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (532952619 / 1000000000) (26647631 / 50000000) (Real.log (851978011429 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (851978011429 / 500000000000) = -Real.log (500000000000 / 851978011429) := by
    rw [show ((851978011429 / 500000000000) : ℝ) = ((500000000000 / 851978011429) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (133465059 / 250000000) ≤ -Real.log (100000000000 / 170550326419) ∧
    -Real.log (100000000000 / 170550326419) ≤ (533860237 / 1000000000) := by
  have h := checkLog_sound (w := (70550326419 / 270550326419)) (n := 12)
    (lo := (133465059 / 250000000)) (hi := (533860237 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((170550326419 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(170550326419 / 100000000000) = 1/(100000000000 / 170550326419) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (133465059 / 250000000) (533860237 / 1000000000) (Real.log (170550326419 / 100000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (170550326419 / 100000000000) = -Real.log (100000000000 / 170550326419) := by
    rw [show ((170550326419 / 100000000000) : ℝ) = ((100000000000 / 170550326419) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (94930447 / 250000000) ≤ -Real.log (500000000000 / 730938910963) ∧
    -Real.log (500000000000 / 730938910963) ≤ (379721789 / 1000000000) := by
  have h := checkLog_sound (w := (230938910963 / 1230938910963)) (n := 12)
    (lo := (94930447 / 250000000)) (hi := (379721789 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((730938910963 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(730938910963 / 500000000000) = 1/(500000000000 / 730938910963) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (94930447 / 250000000) (379721789 / 1000000000) (Real.log (730938910963 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (730938910963 / 500000000000) = -Real.log (500000000000 / 730938910963) := by
    rw [show ((730938910963 / 500000000000) : ℝ) = ((500000000000 / 730938910963) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (380378959 / 1000000000) ≤ -Real.log (7812500000 / 11428428441) ∧
    -Real.log (7812500000 / 11428428441) ≤ (4754737 / 12500000) := by
  have h := checkLog_sound (w := (3615928441 / 19240928441)) (n := 12)
    (lo := (380378959 / 1000000000)) (hi := (4754737 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11428428441 / 7812500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11428428441 / 7812500000) = 1/(7812500000 / 11428428441) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (380378959 / 1000000000) (4754737 / 12500000) (Real.log (11428428441 / 7812500000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (11428428441 / 7812500000) = -Real.log (7812500000 / 11428428441) := by
    rw [show ((11428428441 / 7812500000) : ℝ) = ((7812500000 / 11428428441) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (35956049 / 1000000000) ≤ -Real.log (964682690959 / 1000000000000) ∧
    -Real.log (964682690959 / 1000000000000) ≤ (719121 / 20000000) := by
  have h := checkLog_sound (w := (35317309041 / 1964682690959)) (n := 12)
    (lo := (35956049 / 1000000000)) (hi := (719121 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 964682690959) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 964682690959) = 1/(964682690959 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-719121 / 20000000) (-35956049 / 1000000000) (Real.log (964682690959 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (8958163 / 250000000) ≤ -Real.log (60300108591 / 62500000000) ∧
    -Real.log (60300108591 / 62500000000) ≤ (35832653 / 1000000000) := by
  have h := checkLog_sound (w := (2199891409 / 122800108591)) (n := 12)
    (lo := (8958163 / 250000000)) (hi := (35832653 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 60300108591) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 60300108591) = 1/(60300108591 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-35832653 / 1000000000) (-8958163 / 250000000) (Real.log (60300108591 / 62500000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell198
