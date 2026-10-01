import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell075
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

theorem reflection_log_1_neg : (12907433 / 50000000) ≤ -Real.log (1280 / 1657) ∧
    -Real.log (1280 / 1657) ≤ (258148661 / 1000000000) := by
  have h := checkLog_sound (w := (377 / 2937)) (n := 12)
    (lo := (12907433 / 50000000)) (hi := (258148661 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1657 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1657 / 1280) = 1/(1280 / 1657) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (12907433 / 50000000) (258148661 / 1000000000) (Real.log (1657 / 1280)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1657 / 1280) = -Real.log (1280 / 1657) := by
    rw [show ((1657 / 1280) : ℝ) = ((1280 / 1657) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (348892803 / 1000000000) ≤ -Real.log (903 / 1280) ∧
    -Real.log (903 / 1280) ≤ (87223201 / 250000000) := by
  have h := checkLog_sound (w := (377 / 2183)) (n := 12)
    (lo := (348892803 / 1000000000)) (hi := (87223201 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 903) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 903) = 1/(903 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-87223201 / 250000000) (-348892803 / 1000000000) (Real.log (903 / 1280)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (64423983 / 250000000) ≤ -Real.log (1024 / 1325) ∧
    -Real.log (1024 / 1325) ≤ (257695933 / 1000000000) := by
  have h := checkLog_sound (w := (301 / 2349)) (n := 12)
    (lo := (64423983 / 250000000)) (hi := (257695933 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1325 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1325 / 1024) = 1/(1024 / 1325) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (64423983 / 250000000) (257695933 / 1000000000) (Real.log (1325 / 1024)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1325 / 1024) = -Real.log (1024 / 1325) := by
    rw [show ((1325 / 1024) : ℝ) = ((1024 / 1325) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (348062583 / 1000000000) ≤ -Real.log (723 / 1024) ∧
    -Real.log (723 / 1024) ≤ (43507823 / 125000000) := by
  have h := checkLog_sound (w := (301 / 1747)) (n := 12)
    (lo := (348062583 / 1000000000)) (hi := (43507823 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 723) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 723) = 1/(723 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-43507823 / 125000000) (-348062583 / 1000000000) (Real.log (723 / 1024)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (47371251 / 250000000) ≤ -Real.log (1000000 / 1208627) ∧
    -Real.log (1000000 / 1208627) ≤ (37897001 / 200000000) := by
  have h := checkLog_sound (w := (208627 / 2208627)) (n := 12)
    (lo := (47371251 / 250000000)) (hi := (37897001 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1208627 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1208627 / 1000000) = 1/(1000000 / 1208627) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (47371251 / 250000000) (37897001 / 200000000) (Real.log (1208627 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1208627 / 1000000) = -Real.log (1000000 / 1208627) := by
    rw [show ((1208627 / 1000000) : ℝ) = ((1000000 / 1208627) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (233985867 / 1000000000) ≤ -Real.log (791373 / 1000000) ∧
    -Real.log (791373 / 1000000) ≤ (58496467 / 250000000) := by
  have h := checkLog_sound (w := (208627 / 1791373)) (n := 12)
    (lo := (233985867 / 1000000000)) (hi := (58496467 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 791373) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 791373) = 1/(791373 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-58496467 / 250000000) (-233985867 / 1000000000) (Real.log (791373 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (37966489 / 200000000) ≤ -Real.log (1000000 / 1209047) ∧
    -Real.log (1000000 / 1209047) ≤ (94916223 / 500000000) := by
  have h := checkLog_sound (w := (209047 / 2209047)) (n := 12)
    (lo := (37966489 / 200000000)) (hi := (94916223 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1209047 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1209047 / 1000000) = 1/(1000000 / 1209047) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (37966489 / 200000000) (94916223 / 500000000) (Real.log (1209047 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1209047 / 1000000) = -Real.log (1000000 / 1209047) := by
    rw [show ((1209047 / 1000000) : ℝ) = ((1000000 / 1209047) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (234516731 / 1000000000) ≤ -Real.log (790953 / 1000000) ∧
    -Real.log (790953 / 1000000) ≤ (58629183 / 250000000) := by
  have h := checkLog_sound (w := (209047 / 1790953)) (n := 12)
    (lo := (234516731 / 1000000000)) (hi := (58629183 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 790953) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 790953) = 1/(790953 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-58629183 / 250000000) (-234516731 / 1000000000) (Real.log (790953 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (139172203 / 1000000000) ≤ -Real.log (500000 / 574661) ∧
    -Real.log (500000 / 574661) ≤ (34793051 / 250000000) := by
  have h := checkLog_sound (w := (74661 / 1074661)) (n := 12)
    (lo := (139172203 / 1000000000)) (hi := (34793051 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((574661 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(574661 / 500000) = 1/(500000 / 574661) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (139172203 / 1000000000) (34793051 / 250000000) (Real.log (574661 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (574661 / 500000) = -Real.log (500000 / 574661) := by
    rw [show ((574661 / 500000) : ℝ) = ((500000 / 574661) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (25269 / 156250) ≤ -Real.log (425339 / 500000) ∧
    -Real.log (425339 / 500000) ≤ (161721601 / 1000000000) := by
  have h := checkLog_sound (w := (74661 / 925339)) (n := 12)
    (lo := (25269 / 156250)) (hi := (161721601 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 425339) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 425339) = 1/(425339 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-161721601 / 1000000000) (-25269 / 156250) (Real.log (425339 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (139441021 / 1000000000) ≤ -Real.log (1000000 / 1149631) ∧
    -Real.log (1000000 / 1149631) ≤ (69720511 / 500000000) := by
  have h := checkLog_sound (w := (149631 / 2149631)) (n := 12)
    (lo := (139441021 / 1000000000)) (hi := (69720511 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1149631 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1149631 / 1000000) = 1/(1000000 / 1149631) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (139441021 / 1000000000) (69720511 / 500000000) (Real.log (1149631 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1149631 / 1000000) = -Real.log (1000000 / 1149631) := by
    rw [show ((1149631 / 1000000) : ℝ) = ((1000000 / 1149631) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (81042453 / 500000000) ≤ -Real.log (850369 / 1000000) ∧
    -Real.log (850369 / 1000000) ≤ (162084907 / 1000000000) := by
  have h := checkLog_sound (w := (149631 / 1850369)) (n := 12)
    (lo := (81042453 / 500000000)) (hi := (162084907 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 850369) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 850369) = 1/(850369 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-162084907 / 1000000000) (-81042453 / 500000000) (Real.log (850369 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (151439629 / 250000000) ≤ -Real.log (1250000000 / 2290802213) ∧
    -Real.log (1250000000 / 2290802213) ≤ (605758517 / 1000000000) := by
  have h := checkLog_sound (w := (1040802213 / 3540802213)) (n := 12)
    (lo := (151439629 / 250000000)) (hi := (605758517 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2290802213 / 1250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2290802213 / 1250000000) = 1/(1250000000 / 2290802213) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (151439629 / 250000000) (605758517 / 1000000000) (Real.log (2290802213 / 1250000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (2290802213 / 1250000000) = -Real.log (1250000000 / 2290802213) := by
    rw [show ((2290802213 / 1250000000) : ℝ) = ((1250000000 / 2290802213) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (75880183 / 125000000) ≤ -Real.log (500000000000 / 917497231451) ∧
    -Real.log (500000000000 / 917497231451) ≤ (121408293 / 200000000) := by
  have h := checkLog_sound (w := (417497231451 / 1417497231451)) (n := 12)
    (lo := (75880183 / 125000000)) (hi := (121408293 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((917497231451 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(917497231451 / 500000000000) = 1/(500000000000 / 917497231451) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (75880183 / 125000000) (121408293 / 200000000) (Real.log (917497231451 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (917497231451 / 500000000000) = -Real.log (500000000000 / 917497231451) := by
    rw [show ((917497231451 / 500000000000) : ℝ) = ((500000000000 / 917497231451) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (423470871 / 1000000000) ≤ -Real.log (500000000000 / 763626633711) ∧
    -Real.log (500000000000 / 763626633711) ≤ (52933859 / 125000000) := by
  have h := checkLog_sound (w := (263626633711 / 1263626633711)) (n := 12)
    (lo := (423470871 / 1000000000)) (hi := (52933859 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((763626633711 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(763626633711 / 500000000000) = 1/(500000000000 / 763626633711) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (423470871 / 1000000000) (52933859 / 125000000) (Real.log (763626633711 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (763626633711 / 500000000000) = -Real.log (500000000000 / 763626633711) := by
    rw [show ((763626633711 / 500000000000) : ℝ) = ((500000000000 / 763626633711) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (424349177 / 1000000000) ≤ -Real.log (31250000000 / 47768601611) ∧
    -Real.log (31250000000 / 47768601611) ≤ (212174589 / 500000000) := by
  have h := checkLog_sound (w := (16518601611 / 79018601611)) (n := 12)
    (lo := (424349177 / 1000000000)) (hi := (212174589 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((47768601611 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(47768601611 / 31250000000) = 1/(31250000000 / 47768601611) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (424349177 / 1000000000) (212174589 / 500000000) (Real.log (47768601611 / 31250000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (47768601611 / 31250000000) = -Real.log (31250000000 / 47768601611) := by
    rw [show ((47768601611 / 31250000000) : ℝ) = ((31250000000 / 47768601611) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (300893803 / 1000000000) ≤ -Real.log (125000000000 / 168883231963) ∧
    -Real.log (125000000000 / 168883231963) ≤ (75223451 / 250000000) := by
  have h := checkLog_sound (w := (43883231963 / 293883231963)) (n := 12)
    (lo := (300893803 / 1000000000)) (hi := (75223451 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((168883231963 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(168883231963 / 125000000000) = 1/(125000000000 / 168883231963) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (300893803 / 1000000000) (75223451 / 250000000) (Real.log (168883231963 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (168883231963 / 125000000000) = -Real.log (125000000000 / 168883231963) := by
    rw [show ((168883231963 / 125000000000) : ℝ) = ((125000000000 / 168883231963) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (301525927 / 1000000000) ≤ -Real.log (500000000000 / 675960083211) ∧
    -Real.log (500000000000 / 675960083211) ≤ (37690741 / 125000000) := by
  have h := checkLog_sound (w := (175960083211 / 1175960083211)) (n := 12)
    (lo := (301525927 / 1000000000)) (hi := (37690741 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((675960083211 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(675960083211 / 500000000000) = 1/(500000000000 / 675960083211) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (301525927 / 1000000000) (37690741 / 125000000) (Real.log (675960083211 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (675960083211 / 500000000000) = -Real.log (500000000000 / 675960083211) := by
    rw [show ((675960083211 / 500000000000) : ℝ) = ((500000000000 / 675960083211) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (5660971 / 250000000) ≤ -Real.log (977610563839 / 1000000000000) ∧
    -Real.log (977610563839 / 1000000000000) ≤ (4528777 / 200000000) := by
  have h := checkLog_sound (w := (22389436161 / 1977610563839)) (n := 12)
    (lo := (5660971 / 250000000)) (hi := (4528777 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 977610563839) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 977610563839) = 1/(977610563839 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-4528777 / 200000000) (-5660971 / 250000000) (Real.log (977610563839 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (22549397 / 1000000000) ≤ -Real.log (244425735079 / 250000000000) ∧
    -Real.log (244425735079 / 250000000000) ≤ (11274699 / 500000000) := by
  have h := checkLog_sound (w := (5574264921 / 494425735079)) (n := 12)
    (lo := (22549397 / 1000000000)) (hi := (11274699 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 244425735079) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 244425735079) = 1/(244425735079 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-11274699 / 500000000) (-22549397 / 1000000000) (Real.log (244425735079 / 250000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell075
