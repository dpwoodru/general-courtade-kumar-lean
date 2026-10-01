import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_8576_neg : (65597789 / 250000000) ≤ -Real.log (250000000000 / 325008740133) ∧
    -Real.log (250000000000 / 325008740133) ≤ (262391157 / 1000000000) := by
  have h := checkLog_sound (w := (75008740133 / 575008740133)) (n := 12)
    (lo := (65597789 / 250000000)) (hi := (262391157 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((325008740133 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(325008740133 / 250000000000) = 1/(250000000000 / 325008740133) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8576 : Bounds (65597789 / 250000000) (262391157 / 1000000000) (Real.log (325008740133 / 250000000000)) := by
  have h := reflection_log_8576_neg
  have he : Real.log (325008740133 / 250000000000) = -Real.log (250000000000 / 325008740133) := by
    rw [show ((325008740133 / 250000000000) : ℝ) = ((250000000000 / 325008740133) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8577_neg : (525787163 / 1000000000) ≤ -Real.log (125000000000 / 211473755047) ∧
    -Real.log (125000000000 / 211473755047) ≤ (131446791 / 250000000) := by
  have h := checkLog_sound (w := (86473755047 / 336473755047)) (n := 12)
    (lo := (525787163 / 1000000000)) (hi := (131446791 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((211473755047 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(211473755047 / 125000000000) = 1/(125000000000 / 211473755047) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8577 : Bounds (525787163 / 1000000000) (131446791 / 250000000) (Real.log (211473755047 / 125000000000)) := by
  have h := reflection_log_8577_neg
  have he : Real.log (211473755047 / 125000000000) = -Real.log (125000000000 / 211473755047) := by
    rw [show ((211473755047 / 125000000000) : ℝ) = ((125000000000 / 211473755047) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8578_neg : (526858031 / 1000000000) ≤ -Real.log (250000000000 / 423400673401) ∧
    -Real.log (250000000000 / 423400673401) ≤ (32928627 / 62500000) := by
  have h := checkLog_sound (w := (173400673401 / 673400673401)) (n := 12)
    (lo := (526858031 / 1000000000)) (hi := (32928627 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((423400673401 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(423400673401 / 250000000000) = 1/(250000000000 / 423400673401) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8578 : Bounds (526858031 / 1000000000) (32928627 / 62500000) (Real.log (423400673401 / 250000000000)) := by
  have h := reflection_log_8578_neg
  have he : Real.log (423400673401 / 250000000000) = -Real.log (250000000000 / 423400673401) := by
    rw [show ((423400673401 / 250000000000) : ℝ) = ((250000000000 / 423400673401) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8579_neg : (114761579 / 500000000) ≤ -Real.log (500 / 629) ∧
    -Real.log (500 / 629) ≤ (229523159 / 1000000000) := by
  have h := checkLog_sound (w := (129 / 1129)) (n := 12)
    (lo := (114761579 / 500000000)) (hi := (229523159 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((629 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(629 / 500) = 1/(500 / 629) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8579 : Bounds (114761579 / 500000000) (229523159 / 1000000000) (Real.log (629 / 500)) := by
  have h := reflection_log_8579_neg
  have he : Real.log (629 / 500) = -Real.log (500 / 629) := by
    rw [show ((629 / 500) : ℝ) = ((500 / 629) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8580_neg : (59681207 / 200000000) ≤ -Real.log (371 / 500) ∧
    -Real.log (371 / 500) ≤ (74601509 / 250000000) := by
  have h := checkLog_sound (w := (129 / 871)) (n := 12)
    (lo := (59681207 / 200000000)) (hi := (74601509 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 371) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500 / 371) = 1/(371 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8580 : Bounds (-74601509 / 250000000) (-59681207 / 200000000) (Real.log (371 / 500)) := by
  have h := reflection_log_8580_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8581_neg : (128983 / 500000000) ≤ -Real.log (500000 / 500129) ∧
    -Real.log (500000 / 500129) ≤ (257967 / 1000000000) := by
  have h := checkLog_sound (w := (129 / 1000129)) (n := 12)
    (lo := (128983 / 500000000)) (hi := (257967 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500129 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500129 / 500000) = 1/(500000 / 500129) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8581 : Bounds (128983 / 500000000) (257967 / 1000000000) (Real.log (500129 / 500000)) := by
  have h := reflection_log_8581_neg
  have he : Real.log (500129 / 500000) = -Real.log (500000 / 500129) := by
    rw [show ((500129 / 500000) : ℝ) = ((500000 / 500129) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8582_neg : (258033 / 1000000000) ≤ -Real.log (499871 / 500000) ∧
    -Real.log (499871 / 500000) ≤ (129017 / 500000000) := by
  have h := checkLog_sound (w := (129 / 999871)) (n := 12)
    (lo := (258033 / 1000000000)) (hi := (129017 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499871) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499871) = 1/(499871 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8582 : Bounds (-129017 / 500000000) (-258033 / 1000000000) (Real.log (499871 / 500000)) := by
  have h := reflection_log_8582_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8583_neg : (61194207 / 500000000) ≤ -Real.log (1000000 / 1130193) ∧
    -Real.log (1000000 / 1130193) ≤ (24477683 / 200000000) := by
  have h := checkLog_sound (w := (130193 / 2130193)) (n := 12)
    (lo := (61194207 / 500000000)) (hi := (24477683 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1130193 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1130193 / 1000000) = 1/(1000000 / 1130193) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8583 : Bounds (61194207 / 500000000) (24477683 / 200000000) (Real.log (1130193 / 1000000)) := by
  have h := reflection_log_8583_neg
  have he : Real.log (1130193 / 1000000) = -Real.log (1000000 / 1130193) := by
    rw [show ((1130193 / 1000000) : ℝ) = ((1000000 / 1130193) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8584_neg : (139483931 / 1000000000) ≤ -Real.log (869807 / 1000000) ∧
    -Real.log (869807 / 1000000) ≤ (34870983 / 250000000) := by
  have h := checkLog_sound (w := (130193 / 1869807)) (n := 12)
    (lo := (139483931 / 1000000000)) (hi := (34870983 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 869807) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 869807) = 1/(869807 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8584 : Bounds (-34870983 / 250000000) (-139483931 / 1000000000) (Real.log (869807 / 1000000)) := by
  have h := reflection_log_8584_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8585_neg : (1228431 / 10000000) ≤ -Real.log (1000000 / 1130707) ∧
    -Real.log (1000000 / 1130707) ≤ (122843101 / 1000000000) := by
  have h := checkLog_sound (w := (130707 / 2130707)) (n := 12)
    (lo := (1228431 / 10000000)) (hi := (122843101 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1130707 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1130707 / 1000000) = 1/(1000000 / 1130707) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8585 : Bounds (1228431 / 10000000) (122843101 / 1000000000) (Real.log (1130707 / 1000000)) := by
  have h := reflection_log_8585_neg
  have he : Real.log (1130707 / 1000000) = -Real.log (1000000 / 1130707) := by
    rw [show ((1130707 / 1000000) : ℝ) = ((1000000 / 1130707) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8586_neg : (140075041 / 1000000000) ≤ -Real.log (869293 / 1000000) ∧
    -Real.log (869293 / 1000000) ≤ (70037521 / 500000000) := by
  have h := checkLog_sound (w := (130707 / 1869293)) (n := 12)
    (lo := (140075041 / 1000000000)) (hi := (70037521 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 869293) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 869293) = 1/(869293 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8586 : Bounds (-70037521 / 500000000) (-140075041 / 1000000000) (Real.log (869293 / 1000000)) := by
  have h := reflection_log_8586_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8587_neg : (861597 / 50000000) ≤ -Real.log (982915680151 / 1000000000000) ∧
    -Real.log (982915680151 / 1000000000000) ≤ (17231941 / 1000000000) := by
  have h := checkLog_sound (w := (17084319849 / 1982915680151)) (n := 12)
    (lo := (861597 / 50000000)) (hi := (17231941 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 982915680151) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 982915680151) = 1/(982915680151 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8587 : Bounds (-17231941 / 1000000000) (-861597 / 50000000) (Real.log (982915680151 / 1000000000000)) := by
  have h := reflection_log_8587_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8588_neg : (4273879 / 250000000) ≤ -Real.log (983049782751 / 1000000000000) ∧
    -Real.log (983049782751 / 1000000000000) ≤ (17095517 / 1000000000) := by
  have h := checkLog_sound (w := (16950217249 / 1983049782751)) (n := 12)
    (lo := (4273879 / 250000000)) (hi := (17095517 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 983049782751) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 983049782751) = 1/(983049782751 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8588 : Bounds (-17095517 / 1000000000) (-4273879 / 250000000) (Real.log (983049782751 / 1000000000000)) := by
  have h := reflection_log_8588_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8589_neg : (52374469 / 200000000) ≤ -Real.log (500000000000 / 649680331383) ∧
    -Real.log (500000000000 / 649680331383) ≤ (130936173 / 500000000) := by
  have h := checkLog_sound (w := (149680331383 / 1149680331383)) (n := 12)
    (lo := (52374469 / 200000000)) (hi := (130936173 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((649680331383 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(649680331383 / 500000000000) = 1/(500000000000 / 649680331383) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8589 : Bounds (52374469 / 200000000) (130936173 / 500000000) (Real.log (649680331383 / 500000000000)) := by
  have h := reflection_log_8589_neg
  have he : Real.log (649680331383 / 500000000000) = -Real.log (500000000000 / 649680331383) := by
    rw [show ((649680331383 / 500000000000) : ℝ) = ((500000000000 / 649680331383) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8590_neg : (131459071 / 500000000) ≤ -Real.log (125000000000 / 162590030059) ∧
    -Real.log (125000000000 / 162590030059) ≤ (262918143 / 1000000000) := by
  have h := checkLog_sound (w := (37590030059 / 287590030059)) (n := 12)
    (lo := (131459071 / 500000000)) (hi := (262918143 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((162590030059 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(162590030059 / 125000000000) = 1/(125000000000 / 162590030059) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8590 : Bounds (131459071 / 500000000) (262918143 / 1000000000) (Real.log (162590030059 / 125000000000)) := by
  have h := reflection_log_8590_neg
  have he : Real.log (162590030059 / 125000000000) = -Real.log (125000000000 / 162590030059) := by
    rw [show ((162590030059 / 125000000000) : ℝ) = ((125000000000 / 162590030059) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8591_neg : (526858031 / 1000000000) ≤ -Real.log (500000000000 / 846801346801) ∧
    -Real.log (500000000000 / 846801346801) ≤ (32928627 / 62500000) := by
  have h := checkLog_sound (w := (346801346801 / 1346801346801)) (n := 12)
    (lo := (526858031 / 1000000000)) (hi := (32928627 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((846801346801 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(846801346801 / 500000000000) = 1/(500000000000 / 846801346801) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8591 : Bounds (526858031 / 1000000000) (32928627 / 62500000) (Real.log (846801346801 / 500000000000)) := by
  have h := reflection_log_8591_neg
  have he : Real.log (846801346801 / 500000000000) = -Real.log (500000000000 / 846801346801) := by
    rw [show ((846801346801 / 500000000000) : ℝ) = ((500000000000 / 846801346801) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8592_neg : (263964597 / 500000000) ≤ -Real.log (500000000000 / 847708894879) ∧
    -Real.log (500000000000 / 847708894879) ≤ (105585839 / 200000000) := by
  have h := checkLog_sound (w := (347708894879 / 1347708894879)) (n := 12)
    (lo := (263964597 / 500000000)) (hi := (105585839 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((847708894879 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(847708894879 / 500000000000) = 1/(500000000000 / 847708894879) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8592 : Bounds (263964597 / 500000000) (105585839 / 200000000) (Real.log (847708894879 / 500000000000)) := by
  have h := reflection_log_8592_neg
  have he : Real.log (847708894879 / 500000000000) = -Real.log (500000000000 / 847708894879) := by
    rw [show ((847708894879 / 500000000000) : ℝ) = ((500000000000 / 847708894879) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8593_neg : (45984107 / 200000000) ≤ -Real.log (2000 / 2517) ∧
    -Real.log (2000 / 2517) ≤ (28740067 / 125000000) := by
  have h := checkLog_sound (w := (517 / 4517)) (n := 12)
    (lo := (45984107 / 200000000)) (hi := (28740067 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2517 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2517 / 2000) = 1/(2000 / 2517) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8593 : Bounds (45984107 / 200000000) (28740067 / 125000000) (Real.log (2517 / 2000)) := by
  have h := reflection_log_8593_neg
  have he : Real.log (2517 / 2000) = -Real.log (2000 / 2517) := by
    rw [show ((2517 / 2000) : ℝ) = ((2000 / 2517) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8594_neg : (299080117 / 1000000000) ≤ -Real.log (1483 / 2000) ∧
    -Real.log (1483 / 2000) ≤ (149540059 / 500000000) := by
  have h := checkLog_sound (w := (517 / 3483)) (n := 12)
    (lo := (299080117 / 1000000000)) (hi := (149540059 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1483) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1483) = 1/(1483 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8594 : Bounds (-149540059 / 500000000) (-299080117 / 1000000000) (Real.log (1483 / 2000)) := by
  have h := reflection_log_8594_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8595_neg : (129233 / 500000000) ≤ -Real.log (2000000 / 2000517) ∧
    -Real.log (2000000 / 2000517) ≤ (258467 / 1000000000) := by
  have h := checkLog_sound (w := (517 / 4000517)) (n := 12)
    (lo := (129233 / 500000000)) (hi := (258467 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000517 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000517 / 2000000) = 1/(2000000 / 2000517) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8595 : Bounds (129233 / 500000000) (258467 / 1000000000) (Real.log (2000517 / 2000000)) := by
  have h := reflection_log_8595_neg
  have he : Real.log (2000517 / 2000000) = -Real.log (2000000 / 2000517) := by
    rw [show ((2000517 / 2000000) : ℝ) = ((2000000 / 2000517) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8596_neg : (258533 / 1000000000) ≤ -Real.log (1999483 / 2000000) ∧
    -Real.log (1999483 / 2000000) ≤ (129267 / 500000000) := by
  have h := checkLog_sound (w := (517 / 3999483)) (n := 12)
    (lo := (258533 / 1000000000)) (hi := (129267 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999483) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999483) = 1/(1999483 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8596 : Bounds (-129267 / 500000000) (-258533 / 1000000000) (Real.log (1999483 / 2000000)) := by
  have h := reflection_log_8596_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8597_neg : (7663597 / 62500000) ≤ -Real.log (250000 / 282613) ∧
    -Real.log (250000 / 282613) ≤ (122617553 / 1000000000) := by
  have h := checkLog_sound (w := (32613 / 532613)) (n := 12)
    (lo := (7663597 / 62500000)) (hi := (122617553 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((282613 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(282613 / 250000) = 1/(250000 / 282613) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8597 : Bounds (7663597 / 62500000) (122617553 / 1000000000) (Real.log (282613 / 250000)) := by
  have h := reflection_log_8597_neg
  have he : Real.log (282613 / 250000) = -Real.log (250000 / 282613) := by
    rw [show ((282613 / 250000) : ℝ) = ((250000 / 282613) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8598_neg : (69890871 / 500000000) ≤ -Real.log (217387 / 250000) ∧
    -Real.log (217387 / 250000) ≤ (139781743 / 1000000000) := by
  have h := checkLog_sound (w := (32613 / 467387)) (n := 12)
    (lo := (69890871 / 500000000)) (hi := (139781743 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 217387) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 217387) = 1/(217387 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8598 : Bounds (-139781743 / 1000000000) (-69890871 / 500000000) (Real.log (217387 / 250000)) := by
  have h := reflection_log_8598_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8599_neg : (61536509 / 500000000) ≤ -Real.log (1000000 / 1130967) ∧
    -Real.log (1000000 / 1130967) ≤ (123073019 / 1000000000) := by
  have h := checkLog_sound (w := (130967 / 2130967)) (n := 12)
    (lo := (61536509 / 500000000)) (hi := (123073019 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1130967 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1130967 / 1000000) = 1/(1000000 / 1130967) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8599 : Bounds (61536509 / 500000000) (123073019 / 1000000000) (Real.log (1130967 / 1000000)) := by
  have h := reflection_log_8599_neg
  have he : Real.log (1130967 / 1000000) = -Real.log (1000000 / 1130967) := by
    rw [show ((1130967 / 1000000) : ℝ) = ((1000000 / 1130967) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8600_neg : (140374179 / 1000000000) ≤ -Real.log (869033 / 1000000) ∧
    -Real.log (869033 / 1000000) ≤ (7018709 / 50000000) := by
  have h := checkLog_sound (w := (130967 / 1869033)) (n := 12)
    (lo := (140374179 / 1000000000)) (hi := (7018709 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 869033) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 869033) = 1/(869033 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8600 : Bounds (-7018709 / 50000000) (-140374179 / 1000000000) (Real.log (869033 / 1000000)) := by
  have h := reflection_log_8600_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8601_neg : (432529 / 25000000) ≤ -Real.log (982847644911 / 1000000000000) ∧
    -Real.log (982847644911 / 1000000000000) ≤ (17301161 / 1000000000) := by
  have h := checkLog_sound (w := (17152355089 / 1982847644911)) (n := 12)
    (lo := (432529 / 25000000)) (hi := (17301161 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 982847644911) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 982847644911) = 1/(982847644911 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8601 : Bounds (-17301161 / 1000000000) (-432529 / 25000000) (Real.log (982847644911 / 1000000000000)) := by
  have h := reflection_log_8601_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8602_neg : (17164189 / 1000000000) ≤ -Real.log (61436392231 / 62500000000) ∧
    -Real.log (61436392231 / 62500000000) ≤ (1716419 / 100000000) := by
  have h := checkLog_sound (w := (1063607769 / 123936392231)) (n := 12)
    (lo := (17164189 / 1000000000)) (hi := (1716419 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 61436392231) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 61436392231) = 1/(61436392231 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8602 : Bounds (-1716419 / 100000000) (-17164189 / 1000000000) (Real.log (61436392231 / 62500000000)) := by
  have h := reflection_log_8602_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8603_neg : (52479859 / 200000000) ≤ -Real.log (10000000000 / 13000455409) ∧
    -Real.log (10000000000 / 13000455409) ≤ (4099989 / 15625000) := by
  have h := checkLog_sound (w := (3000455409 / 23000455409)) (n := 12)
    (lo := (52479859 / 200000000)) (hi := (4099989 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((13000455409 / 10000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(13000455409 / 10000000000) = 1/(10000000000 / 13000455409) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8603 : Bounds (52479859 / 200000000) (4099989 / 15625000) (Real.log (13000455409 / 10000000000)) := by
  have h := reflection_log_8603_neg
  have he : Real.log (13000455409 / 10000000000) = -Real.log (10000000000 / 13000455409) := by
    rw [show ((13000455409 / 10000000000) : ℝ) = ((10000000000 / 13000455409) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8604_neg : (131723599 / 500000000) ≤ -Real.log (6250000000 / 8133803607) ∧
    -Real.log (6250000000 / 8133803607) ≤ (263447199 / 1000000000) := by
  have h := checkLog_sound (w := (1883803607 / 14383803607)) (n := 12)
    (lo := (131723599 / 500000000)) (hi := (263447199 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8133803607 / 6250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(8133803607 / 6250000000) = 1/(6250000000 / 8133803607) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8604 : Bounds (131723599 / 500000000) (263447199 / 1000000000) (Real.log (8133803607 / 6250000000)) := by
  have h := reflection_log_8604_neg
  have he : Real.log (8133803607 / 6250000000) = -Real.log (6250000000 / 8133803607) := by
    rw [show ((8133803607 / 6250000000) : ℝ) = ((6250000000 / 8133803607) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8605_neg : (263964597 / 500000000) ≤ -Real.log (250000000000 / 423854447439) ∧
    -Real.log (250000000000 / 423854447439) ≤ (105585839 / 200000000) := by
  have h := checkLog_sound (w := (173854447439 / 673854447439)) (n := 12)
    (lo := (263964597 / 500000000)) (hi := (105585839 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((423854447439 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(423854447439 / 250000000000) = 1/(250000000000 / 423854447439) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8605 : Bounds (263964597 / 500000000) (105585839 / 200000000) (Real.log (423854447439 / 250000000000)) := by
  have h := reflection_log_8605_neg
  have he : Real.log (423854447439 / 250000000000) = -Real.log (250000000000 / 423854447439) := by
    rw [show ((423854447439 / 250000000000) : ℝ) = ((250000000000 / 423854447439) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8606_neg : (132250163 / 250000000) ≤ -Real.log (125000000000 / 212154416723) ∧
    -Real.log (125000000000 / 212154416723) ≤ (529000653 / 1000000000) := by
  have h := checkLog_sound (w := (87154416723 / 337154416723)) (n := 12)
    (lo := (132250163 / 250000000)) (hi := (529000653 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((212154416723 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(212154416723 / 125000000000) = 1/(125000000000 / 212154416723) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8606 : Bounds (132250163 / 250000000) (529000653 / 1000000000) (Real.log (212154416723 / 125000000000)) := by
  have h := reflection_log_8606_neg
  have he : Real.log (212154416723 / 125000000000) = -Real.log (125000000000 / 212154416723) := by
    rw [show ((212154416723 / 125000000000) : ℝ) = ((125000000000 / 212154416723) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8607_neg : (46063551 / 200000000) ≤ -Real.log (1000 / 1259) ∧
    -Real.log (1000 / 1259) ≤ (57579439 / 250000000) := by
  have h := checkLog_sound (w := (259 / 2259)) (n := 12)
    (lo := (46063551 / 200000000)) (hi := (57579439 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1259 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1259 / 1000) = 1/(1000 / 1259) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8607 : Bounds (46063551 / 200000000) (57579439 / 250000000) (Real.log (1259 / 1000)) := by
  have h := reflection_log_8607_neg
  have he : Real.log (1259 / 1000) = -Real.log (1000 / 1259) := by
    rw [show ((1259 / 1000) : ℝ) = ((1000 / 1259) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8608_neg : (299754653 / 1000000000) ≤ -Real.log (741 / 1000) ∧
    -Real.log (741 / 1000) ≤ (149877327 / 500000000) := by
  have h := checkLog_sound (w := (259 / 1741)) (n := 12)
    (lo := (299754653 / 1000000000)) (hi := (149877327 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 741) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 741) = 1/(741 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8608 : Bounds (-149877327 / 500000000) (-299754653 / 1000000000) (Real.log (741 / 1000)) := by
  have h := reflection_log_8608_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8609_neg : (129483 / 500000000) ≤ -Real.log (1000000 / 1000259) ∧
    -Real.log (1000000 / 1000259) ≤ (258967 / 1000000000) := by
  have h := checkLog_sound (w := (259 / 2000259)) (n := 12)
    (lo := (129483 / 500000000)) (hi := (258967 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000259 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000259 / 1000000) = 1/(1000000 / 1000259) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8609 : Bounds (129483 / 500000000) (258967 / 1000000000) (Real.log (1000259 / 1000000)) := by
  have h := reflection_log_8609_neg
  have he : Real.log (1000259 / 1000000) = -Real.log (1000000 / 1000259) := by
    rw [show ((1000259 / 1000000) : ℝ) = ((1000000 / 1000259) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8610_neg : (259033 / 1000000000) ≤ -Real.log (999741 / 1000000) ∧
    -Real.log (999741 / 1000000) ≤ (129517 / 500000000) := by
  have h := checkLog_sound (w := (259 / 1999741)) (n := 12)
    (lo := (259033 / 1000000000)) (hi := (129517 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999741) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999741) = 1/(999741 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8610 : Bounds (-129517 / 500000000) (-259033 / 1000000000) (Real.log (999741 / 1000000)) := by
  have h := reflection_log_8610_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8611_neg : (61423319 / 500000000) ≤ -Real.log (1000000 / 1130711) ∧
    -Real.log (1000000 / 1130711) ≤ (122846639 / 1000000000) := by
  have h := checkLog_sound (w := (130711 / 2130711)) (n := 12)
    (lo := (61423319 / 500000000)) (hi := (122846639 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1130711 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1130711 / 1000000) = 1/(1000000 / 1130711) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8611 : Bounds (61423319 / 500000000) (122846639 / 1000000000) (Real.log (1130711 / 1000000)) := by
  have h := reflection_log_8611_neg
  have he : Real.log (1130711 / 1000000) = -Real.log (1000000 / 1130711) := by
    rw [show ((1130711 / 1000000) : ℝ) = ((1000000 / 1130711) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8612_neg : (70039821 / 500000000) ≤ -Real.log (869289 / 1000000) ∧
    -Real.log (869289 / 1000000) ≤ (140079643 / 1000000000) := by
  have h := checkLog_sound (w := (130711 / 1869289)) (n := 12)
    (lo := (70039821 / 500000000)) (hi := (140079643 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 869289) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 869289) = 1/(869289 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8612 : Bounds (-140079643 / 1000000000) (-70039821 / 500000000) (Real.log (869289 / 1000000)) := by
  have h := reflection_log_8612_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8613_neg : (30825721 / 250000000) ≤ -Real.log (1000000 / 1131227) ∧
    -Real.log (1000000 / 1131227) ≤ (24660577 / 200000000) := by
  have h := checkLog_sound (w := (131227 / 2131227)) (n := 12)
    (lo := (30825721 / 250000000)) (hi := (24660577 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1131227 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1131227 / 1000000) = 1/(1000000 / 1131227) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8613 : Bounds (30825721 / 250000000) (24660577 / 200000000) (Real.log (1131227 / 1000000)) := by
  have h := reflection_log_8613_neg
  have he : Real.log (1131227 / 1000000) = -Real.log (1000000 / 1131227) := by
    rw [show ((1131227 / 1000000) : ℝ) = ((1000000 / 1131227) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8614_neg : (140673407 / 1000000000) ≤ -Real.log (868773 / 1000000) ∧
    -Real.log (868773 / 1000000) ≤ (1099011 / 7812500) := by
  have h := checkLog_sound (w := (131227 / 1868773)) (n := 12)
    (lo := (140673407 / 1000000000)) (hi := (1099011 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 868773) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 868773) = 1/(868773 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8614 : Bounds (-1099011 / 7812500) (-140673407 / 1000000000) (Real.log (868773 / 1000000)) := by
  have h := reflection_log_8614_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8615_neg : (17370523 / 1000000000) ≤ -Real.log (982779474471 / 1000000000000) ∧
    -Real.log (982779474471 / 1000000000000) ≤ (4342631 / 250000000) := by
  have h := checkLog_sound (w := (17220525529 / 1982779474471)) (n := 12)
    (lo := (17370523 / 1000000000)) (hi := (4342631 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 982779474471) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 982779474471) = 1/(982779474471 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8615 : Bounds (-4342631 / 250000000) (-17370523 / 1000000000) (Real.log (982779474471 / 1000000000000)) := by
  have h := reflection_log_8615_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8616_neg : (4308251 / 250000000) ≤ -Real.log (982914634479 / 1000000000000) ∧
    -Real.log (982914634479 / 1000000000000) ≤ (3446601 / 200000000) := by
  have h := checkLog_sound (w := (17085365521 / 1982914634479)) (n := 12)
    (lo := (4308251 / 250000000)) (hi := (3446601 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 982914634479) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 982914634479) = 1/(982914634479 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8616 : Bounds (-3446601 / 200000000) (-4308251 / 250000000) (Real.log (982914634479 / 1000000000000)) := by
  have h := reflection_log_8616_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8617_neg : (262926281 / 1000000000) ≤ -Real.log (500000000000 / 650365413573) ∧
    -Real.log (500000000000 / 650365413573) ≤ (131463141 / 500000000) := by
  have h := checkLog_sound (w := (150365413573 / 1150365413573)) (n := 12)
    (lo := (262926281 / 1000000000)) (hi := (131463141 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((650365413573 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(650365413573 / 500000000000) = 1/(500000000000 / 650365413573) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8617 : Bounds (262926281 / 1000000000) (131463141 / 500000000) (Real.log (650365413573 / 500000000000)) := by
  have h := reflection_log_8617_neg
  have he : Real.log (650365413573 / 500000000000) = -Real.log (500000000000 / 650365413573) := by
    rw [show ((650365413573 / 500000000000) : ℝ) = ((500000000000 / 650365413573) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8618_neg : (263976291 / 1000000000) ≤ -Real.log (100000000000 / 130209732577) ∧
    -Real.log (100000000000 / 130209732577) ≤ (65994073 / 250000000) := by
  have h := checkLog_sound (w := (30209732577 / 230209732577)) (n := 12)
    (lo := (263976291 / 1000000000)) (hi := (65994073 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((130209732577 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(130209732577 / 100000000000) = 1/(100000000000 / 130209732577) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8618 : Bounds (263976291 / 1000000000) (65994073 / 250000000) (Real.log (130209732577 / 100000000000)) := by
  have h := reflection_log_8618_neg
  have he : Real.log (130209732577 / 100000000000) = -Real.log (100000000000 / 130209732577) := by
    rw [show ((130209732577 / 100000000000) : ℝ) = ((100000000000 / 130209732577) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8619_neg : (132250163 / 250000000) ≤ -Real.log (500000000000 / 848617666891) ∧
    -Real.log (500000000000 / 848617666891) ≤ (529000653 / 1000000000) := by
  have h := checkLog_sound (w := (348617666891 / 1348617666891)) (n := 12)
    (lo := (132250163 / 250000000)) (hi := (529000653 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((848617666891 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(848617666891 / 500000000000) = 1/(500000000000 / 848617666891) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8619 : Bounds (132250163 / 250000000) (529000653 / 1000000000) (Real.log (848617666891 / 500000000000)) := by
  have h := reflection_log_8619_neg
  have he : Real.log (848617666891 / 500000000000) = -Real.log (500000000000 / 848617666891) := by
    rw [show ((848617666891 / 500000000000) : ℝ) = ((500000000000 / 848617666891) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8620_neg : (66259051 / 125000000) ≤ -Real.log (250000000000 / 424763832659) ∧
    -Real.log (250000000000 / 424763832659) ≤ (530072409 / 1000000000) := by
  have h := checkLog_sound (w := (174763832659 / 674763832659)) (n := 12)
    (lo := (66259051 / 125000000)) (hi := (530072409 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((424763832659 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(424763832659 / 250000000000) = 1/(250000000000 / 424763832659) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8620 : Bounds (66259051 / 125000000) (530072409 / 1000000000) (Real.log (424763832659 / 250000000000)) := by
  have h := reflection_log_8620_neg
  have he : Real.log (424763832659 / 250000000000) = -Real.log (250000000000 / 424763832659) := by
    rw [show ((424763832659 / 250000000000) : ℝ) = ((250000000000 / 424763832659) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8621_neg : (3604919 / 15625000) ≤ -Real.log (2000 / 2519) ∧
    -Real.log (2000 / 2519) ≤ (230714817 / 1000000000) := by
  have h := checkLog_sound (w := (519 / 4519)) (n := 12)
    (lo := (3604919 / 15625000)) (hi := (230714817 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2519 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2519 / 2000) = 1/(2000 / 2519) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8621 : Bounds (3604919 / 15625000) (230714817 / 1000000000) (Real.log (2519 / 2000)) := by
  have h := reflection_log_8621_neg
  have he : Real.log (2519 / 2000) = -Real.log (2000 / 2519) := by
    rw [show ((2519 / 2000) : ℝ) = ((2000 / 2519) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8622_neg : (60085929 / 200000000) ≤ -Real.log (1481 / 2000) ∧
    -Real.log (1481 / 2000) ≤ (150214823 / 500000000) := by
  have h := checkLog_sound (w := (519 / 3481)) (n := 12)
    (lo := (60085929 / 200000000)) (hi := (150214823 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1481) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1481) = 1/(1481 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8622 : Bounds (-150214823 / 500000000) (-60085929 / 200000000) (Real.log (1481 / 2000)) := by
  have h := reflection_log_8622_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8623_neg : (129733 / 500000000) ≤ -Real.log (2000000 / 2000519) ∧
    -Real.log (2000000 / 2000519) ≤ (259467 / 1000000000) := by
  have h := checkLog_sound (w := (519 / 4000519)) (n := 12)
    (lo := (129733 / 500000000)) (hi := (259467 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000519 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000519 / 2000000) = 1/(2000000 / 2000519) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8623 : Bounds (129733 / 500000000) (259467 / 1000000000) (Real.log (2000519 / 2000000)) := by
  have h := reflection_log_8623_neg
  have he : Real.log (2000519 / 2000000) = -Real.log (2000000 / 2000519) := by
    rw [show ((2000519 / 2000000) : ℝ) = ((2000000 / 2000519) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8624_neg : (259533 / 1000000000) ≤ -Real.log (1999481 / 2000000) ∧
    -Real.log (1999481 / 2000000) ≤ (129767 / 500000000) := by
  have h := checkLog_sound (w := (519 / 3999481)) (n := 12)
    (lo := (259533 / 1000000000)) (hi := (129767 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999481) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999481) = 1/(1999481 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8624 : Bounds (-129767 / 500000000) (-259533 / 1000000000) (Real.log (1999481 / 2000000)) := by
  have h := reflection_log_8624_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8625_neg : (123075671 / 1000000000) ≤ -Real.log (100000 / 113097) ∧
    -Real.log (100000 / 113097) ≤ (15384459 / 125000000) := by
  have h := checkLog_sound (w := (13097 / 213097)) (n := 12)
    (lo := (123075671 / 1000000000)) (hi := (15384459 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((113097 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(113097 / 100000) = 1/(100000 / 113097) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8625 : Bounds (123075671 / 1000000000) (15384459 / 125000000) (Real.log (113097 / 100000)) := by
  have h := reflection_log_8625_neg
  have he : Real.log (113097 / 100000) = -Real.log (100000 / 113097) := by
    rw [show ((113097 / 100000) : ℝ) = ((100000 / 113097) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8626_neg : (140377631 / 1000000000) ≤ -Real.log (86903 / 100000) ∧
    -Real.log (86903 / 100000) ≤ (4386801 / 31250000) := by
  have h := checkLog_sound (w := (13097 / 186903)) (n := 12)
    (lo := (140377631 / 1000000000)) (hi := (4386801 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 86903) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 86903) = 1/(86903 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8626 : Bounds (-4386801 / 31250000) (-140377631 / 1000000000) (Real.log (86903 / 100000)) := by
  have h := reflection_log_8626_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8627_neg : (123531813 / 1000000000) ≤ -Real.log (500000 / 565743) ∧
    -Real.log (500000 / 565743) ≤ (61765907 / 500000000) := by
  have h := checkLog_sound (w := (65743 / 1065743)) (n := 12)
    (lo := (123531813 / 1000000000)) (hi := (61765907 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((565743 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(565743 / 500000) = 1/(500000 / 565743) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8627 : Bounds (123531813 / 1000000000) (61765907 / 500000000) (Real.log (565743 / 500000)) := by
  have h := reflection_log_8627_neg
  have he : Real.log (565743 / 500000) = -Real.log (500000 / 565743) := by
    rw [show ((565743 / 500000) : ℝ) = ((500000 / 565743) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8628_neg : (140971573 / 1000000000) ≤ -Real.log (434257 / 500000) ∧
    -Real.log (434257 / 500000) ≤ (70485787 / 500000000) := by
  have h := checkLog_sound (w := (65743 / 934257)) (n := 12)
    (lo := (140971573 / 1000000000)) (hi := (70485787 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 434257) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 434257) = 1/(434257 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8628 : Bounds (-70485787 / 500000000) (-140971573 / 1000000000) (Real.log (434257 / 500000)) := by
  have h := reflection_log_8628_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8629_neg : (217997 / 12500000) ≤ -Real.log (245677857951 / 250000000000) ∧
    -Real.log (245677857951 / 250000000000) ≤ (17439761 / 1000000000) := by
  have h := checkLog_sound (w := (4322142049 / 495677857951)) (n := 12)
    (lo := (217997 / 12500000)) (hi := (17439761 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 245677857951) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 245677857951) = 1/(245677857951 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8629 : Bounds (-17439761 / 1000000000) (-217997 / 12500000) (Real.log (245677857951 / 250000000000)) := by
  have h := reflection_log_8629_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8630_neg : (432549 / 25000000) ≤ -Real.log (9828468591 / 10000000000) ∧
    -Real.log (9828468591 / 10000000000) ≤ (17301961 / 1000000000) := by
  have h := checkLog_sound (w := (171531409 / 19828468591)) (n := 12)
    (lo := (432549 / 25000000)) (hi := (17301961 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 9828468591) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 9828468591) = 1/(9828468591 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8630 : Bounds (-17301961 / 1000000000) (-432549 / 25000000) (Real.log (9828468591 / 10000000000)) := by
  have h := reflection_log_8630_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8631_neg : (263453303 / 1000000000) ≤ -Real.log (250000000000 / 325354130467) ∧
    -Real.log (250000000000 / 325354130467) ≤ (32931663 / 125000000) := by
  have h := checkLog_sound (w := (75354130467 / 575354130467)) (n := 12)
    (lo := (263453303 / 1000000000)) (hi := (32931663 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((325354130467 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(325354130467 / 250000000000) = 1/(250000000000 / 325354130467) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8631 : Bounds (263453303 / 1000000000) (32931663 / 125000000) (Real.log (325354130467 / 250000000000)) := by
  have h := reflection_log_8631_neg
  have he : Real.log (325354130467 / 250000000000) = -Real.log (250000000000 / 325354130467) := by
    rw [show ((325354130467 / 250000000000) : ℝ) = ((250000000000 / 325354130467) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8632_neg : (132251693 / 500000000) ≤ -Real.log (50000000000 / 65139191769) ∧
    -Real.log (50000000000 / 65139191769) ≤ (264503387 / 1000000000) := by
  have h := checkLog_sound (w := (15139191769 / 115139191769)) (n := 12)
    (lo := (132251693 / 500000000)) (hi := (264503387 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((65139191769 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(65139191769 / 50000000000) = 1/(50000000000 / 65139191769) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8632 : Bounds (132251693 / 500000000) (264503387 / 1000000000) (Real.log (65139191769 / 50000000000)) := by
  have h := reflection_log_8632_neg
  have he : Real.log (65139191769 / 50000000000) = -Real.log (50000000000 / 65139191769) := by
    rw [show ((65139191769 / 50000000000) : ℝ) = ((50000000000 / 65139191769) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8633_neg : (66259051 / 125000000) ≤ -Real.log (500000000000 / 849527665317) ∧
    -Real.log (500000000000 / 849527665317) ≤ (530072409 / 1000000000) := by
  have h := checkLog_sound (w := (349527665317 / 1349527665317)) (n := 12)
    (lo := (66259051 / 125000000)) (hi := (530072409 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((849527665317 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(849527665317 / 500000000000) = 1/(500000000000 / 849527665317) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8633 : Bounds (66259051 / 125000000) (530072409 / 1000000000) (Real.log (849527665317 / 500000000000)) := by
  have h := reflection_log_8633_neg
  have he : Real.log (849527665317 / 500000000000) = -Real.log (500000000000 / 849527665317) := by
    rw [show ((849527665317 / 500000000000) : ℝ) = ((500000000000 / 849527665317) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8634_neg : (265572231 / 500000000) ≤ -Real.log (500000000000 / 850438892641) ∧
    -Real.log (500000000000 / 850438892641) ≤ (531144463 / 1000000000) := by
  have h := checkLog_sound (w := (350438892641 / 1350438892641)) (n := 12)
    (lo := (265572231 / 500000000)) (hi := (531144463 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((850438892641 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(850438892641 / 500000000000) = 1/(500000000000 / 850438892641) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8634 : Bounds (265572231 / 500000000) (531144463 / 1000000000) (Real.log (850438892641 / 500000000000)) := by
  have h := reflection_log_8634_neg
  have he : Real.log (850438892641 / 500000000000) = -Real.log (500000000000 / 850438892641) := by
    rw [show ((850438892641 / 500000000000) : ℝ) = ((500000000000 / 850438892641) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8635_neg : (5777793 / 25000000) ≤ -Real.log (50 / 63) ∧
    -Real.log (50 / 63) ≤ (231111721 / 1000000000) := by
  have h := checkLog_sound (w := (13 / 113)) (n := 12)
    (lo := (5777793 / 25000000)) (hi := (231111721 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((63 / 50) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(63 / 50) = 1/(50 / 63) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8635 : Bounds (5777793 / 25000000) (231111721 / 1000000000) (Real.log (63 / 50)) := by
  have h := reflection_log_8635_neg
  have he : Real.log (63 / 50) = -Real.log (50 / 63) := by
    rw [show ((63 / 50) : ℝ) = ((50 / 63) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8636_neg : (75276273 / 250000000) ≤ -Real.log (37 / 50) ∧
    -Real.log (37 / 50) ≤ (301105093 / 1000000000) := by
  have h := checkLog_sound (w := (13 / 87)) (n := 12)
    (lo := (75276273 / 250000000)) (hi := (301105093 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50 / 37) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50 / 37) = 1/(37 / 50) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8636 : Bounds (-301105093 / 1000000000) (-75276273 / 250000000) (Real.log (37 / 50)) := by
  have h := reflection_log_8636_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8637_neg : (129983 / 500000000) ≤ -Real.log (50000 / 50013) ∧
    -Real.log (50000 / 50013) ≤ (259967 / 1000000000) := by
  have h := checkLog_sound (w := (13 / 100013)) (n := 12)
    (lo := (129983 / 500000000)) (hi := (259967 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50013 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50013 / 50000) = 1/(50000 / 50013) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8637 : Bounds (129983 / 500000000) (259967 / 1000000000) (Real.log (50013 / 50000)) := by
  have h := reflection_log_8637_neg
  have he : Real.log (50013 / 50000) = -Real.log (50000 / 50013) := by
    rw [show ((50013 / 50000) : ℝ) = ((50000 / 50013) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8638_neg : (260033 / 1000000000) ≤ -Real.log (49987 / 50000) ∧
    -Real.log (49987 / 50000) ≤ (130017 / 500000000) := by
  have h := checkLog_sound (w := (13 / 99987)) (n := 12)
    (lo := (260033 / 1000000000)) (hi := (130017 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 49987) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 49987) = 1/(49987 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8638 : Bounds (-130017 / 500000000) (-260033 / 1000000000) (Real.log (49987 / 50000)) := by
  have h := reflection_log_8638_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8639_neg : (30826163 / 250000000) ≤ -Real.log (1000000 / 1131229) ∧
    -Real.log (1000000 / 1131229) ≤ (123304653 / 1000000000) := by
  have h := checkLog_sound (w := (131229 / 2131229)) (n := 12)
    (lo := (30826163 / 250000000)) (hi := (123304653 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1131229 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1131229 / 1000000) = 1/(1000000 / 1131229) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8639 : Bounds (30826163 / 250000000) (123304653 / 1000000000) (Real.log (1131229 / 1000000)) := by
  have h := reflection_log_8639_neg
  have he : Real.log (1131229 / 1000000) = -Real.log (1000000 / 1131229) := by
    rw [show ((1131229 / 1000000) : ℝ) = ((1000000 / 1131229) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily
