import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_4096_neg : (4078841 / 500000000) ≤ -Real.log (15498054711 / 15625000000) ∧
    -Real.log (15498054711 / 15625000000) ≤ (8157683 / 1000000000) := by
  have h := checkLog_sound (w := (126945289 / 31123054711)) (n := 12)
    (lo := (4078841 / 500000000)) (hi := (8157683 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 15498054711) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 15498054711) = 1/(15498054711 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4096 : Bounds (-8157683 / 1000000000) (-4078841 / 500000000) (Real.log (15498054711 / 15625000000)) := by
  have h := reflection_log_4096_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4097_neg : (903813 / 5000000) ≤ -Real.log (250000000000 / 299532677411) ∧
    -Real.log (250000000000 / 299532677411) ≤ (180762601 / 1000000000) := by
  have h := checkLog_sound (w := (49532677411 / 549532677411)) (n := 12)
    (lo := (903813 / 5000000)) (hi := (180762601 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((299532677411 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(299532677411 / 250000000000) = 1/(250000000000 / 299532677411) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4097 : Bounds (903813 / 5000000) (180762601 / 1000000000) (Real.log (299532677411 / 250000000000)) := by
  have h := reflection_log_4097_neg
  have he : Real.log (299532677411 / 250000000000) = -Real.log (250000000000 / 299532677411) := by
    rw [show ((299532677411 / 250000000000) : ℝ) = ((250000000000 / 299532677411) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4098_neg : (181226377 / 1000000000) ≤ -Real.log (250000000000 / 299671626171) ∧
    -Real.log (250000000000 / 299671626171) ≤ (90613189 / 500000000) := by
  have h := checkLog_sound (w := (49671626171 / 549671626171)) (n := 12)
    (lo := (181226377 / 1000000000)) (hi := (90613189 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((299671626171 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(299671626171 / 250000000000) = 1/(250000000000 / 299671626171) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4098 : Bounds (181226377 / 1000000000) (90613189 / 500000000) (Real.log (299671626171 / 250000000000)) := by
  have h := reflection_log_4098_neg
  have he : Real.log (299671626171 / 250000000000) = -Real.log (250000000000 / 299671626171) := by
    rw [show ((299671626171 / 250000000000) : ℝ) = ((250000000000 / 299671626171) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4099_neg : (362725333 / 1000000000) ≤ -Real.log (500000000000 / 718620521569) ∧
    -Real.log (500000000000 / 718620521569) ≤ (181362667 / 500000000) := by
  have h := checkLog_sound (w := (218620521569 / 1218620521569)) (n := 12)
    (lo := (362725333 / 1000000000)) (hi := (181362667 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((718620521569 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(718620521569 / 500000000000) = 1/(500000000000 / 718620521569) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4099 : Bounds (362725333 / 1000000000) (181362667 / 500000000) (Real.log (718620521569 / 500000000000)) := by
  have h := reflection_log_4099_neg
  have he : Real.log (718620521569 / 500000000000) = -Real.log (500000000000 / 718620521569) := by
    rw [show ((718620521569 / 500000000000) : ℝ) = ((500000000000 / 718620521569) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4100_neg : (90732997 / 250000000) ≤ -Real.log (500000000000 / 718769043267) ∧
    -Real.log (500000000000 / 718769043267) ≤ (362931989 / 1000000000) := by
  have h := checkLog_sound (w := (218769043267 / 1218769043267)) (n := 12)
    (lo := (90732997 / 250000000)) (hi := (362931989 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((718769043267 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(718769043267 / 500000000000) = 1/(500000000000 / 718769043267) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4100 : Bounds (90732997 / 250000000) (362931989 / 1000000000) (Real.log (718769043267 / 500000000000)) := by
  have h := reflection_log_4100_neg
  have he : Real.log (718769043267 / 500000000000) = -Real.log (500000000000 / 718769043267) := by
    rw [show ((718769043267 / 500000000000) : ℝ) = ((500000000000 / 718769043267) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4101_neg : (165175397 / 1000000000) ≤ -Real.log (2500 / 2949) ∧
    -Real.log (2500 / 2949) ≤ (82587699 / 500000000) := by
  have h := checkLog_sound (w := (449 / 5449)) (n := 12)
    (lo := (165175397 / 1000000000)) (hi := (82587699 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2949 / 2500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2949 / 2500) = 1/(2500 / 2949) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4101 : Bounds (165175397 / 1000000000) (82587699 / 500000000) (Real.log (2949 / 2500)) := by
  have h := reflection_log_4101_neg
  have he : Real.log (2949 / 2500) = -Real.log (2500 / 2949) := by
    rw [show ((2949 / 2500) : ℝ) = ((2500 / 2949) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4102_neg : (49490813 / 250000000) ≤ -Real.log (2051 / 2500) ∧
    -Real.log (2051 / 2500) ≤ (197963253 / 1000000000) := by
  have h := checkLog_sound (w := (449 / 4551)) (n := 12)
    (lo := (49490813 / 250000000)) (hi := (197963253 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500 / 2051) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500 / 2051) = 1/(2051 / 2500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4102 : Bounds (-197963253 / 1000000000) (-49490813 / 250000000) (Real.log (2051 / 2500)) := by
  have h := reflection_log_4102_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4103_neg : (179583 / 1000000000) ≤ -Real.log (2500000 / 2500449) ∧
    -Real.log (2500000 / 2500449) ≤ (1403 / 7812500) := by
  have h := checkLog_sound (w := (449 / 5000449)) (n := 12)
    (lo := (179583 / 1000000000)) (hi := (1403 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500449 / 2500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500449 / 2500000) = 1/(2500000 / 2500449) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4103 : Bounds (179583 / 1000000000) (1403 / 7812500) (Real.log (2500449 / 2500000)) := by
  have h := reflection_log_4103_neg
  have he : Real.log (2500449 / 2500000) = -Real.log (2500000 / 2500449) := by
    rw [show ((2500449 / 2500000) : ℝ) = ((2500000 / 2500449) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4104_neg : (5613 / 31250000) ≤ -Real.log (2499551 / 2500000) ∧
    -Real.log (2499551 / 2500000) ≤ (179617 / 1000000000) := by
  have h := checkLog_sound (w := (449 / 4999551)) (n := 12)
    (lo := (5613 / 31250000)) (hi := (179617 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000 / 2499551) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000 / 2499551) = 1/(2499551 / 2500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4104 : Bounds (-179617 / 1000000000) (-5613 / 31250000) (Real.log (2499551 / 2500000)) := by
  have h := reflection_log_4104_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4105_neg : (86349241 / 1000000000) ≤ -Real.log (1000000 / 1090187) ∧
    -Real.log (1000000 / 1090187) ≤ (43174621 / 500000000) := by
  have h := checkLog_sound (w := (90187 / 2090187)) (n := 12)
    (lo := (86349241 / 1000000000)) (hi := (43174621 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1090187 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1090187 / 1000000) = 1/(1000000 / 1090187) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4105 : Bounds (86349241 / 1000000000) (43174621 / 500000000) (Real.log (1090187 / 1000000)) := by
  have h := reflection_log_4105_neg
  have he : Real.log (1090187 / 1000000) = -Real.log (1000000 / 1090187) := by
    rw [show ((1090187 / 1000000) : ℝ) = ((1000000 / 1090187) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4106_neg : (18903239 / 200000000) ≤ -Real.log (909813 / 1000000) ∧
    -Real.log (909813 / 1000000) ≤ (23629049 / 250000000) := by
  have h := checkLog_sound (w := (90187 / 1909813)) (n := 12)
    (lo := (18903239 / 200000000)) (hi := (23629049 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 909813) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 909813) = 1/(909813 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4106 : Bounds (-23629049 / 250000000) (-18903239 / 200000000) (Real.log (909813 / 1000000)) := by
  have h := reflection_log_4106_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4107_neg : (86560191 / 1000000000) ≤ -Real.log (1000000 / 1090417) ∧
    -Real.log (1000000 / 1090417) ≤ (1352503 / 15625000) := by
  have h := checkLog_sound (w := (90417 / 2090417)) (n := 12)
    (lo := (86560191 / 1000000000)) (hi := (1352503 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1090417 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1090417 / 1000000) = 1/(1000000 / 1090417) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4107 : Bounds (86560191 / 1000000000) (1352503 / 15625000) (Real.log (1090417 / 1000000)) := by
  have h := reflection_log_4107_neg
  have he : Real.log (1090417 / 1000000) = -Real.log (1000000 / 1090417) := by
    rw [show ((1090417 / 1000000) : ℝ) = ((1000000 / 1090417) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4108_neg : (47384513 / 500000000) ≤ -Real.log (909583 / 1000000) ∧
    -Real.log (909583 / 1000000) ≤ (94769027 / 1000000000) := by
  have h := checkLog_sound (w := (90417 / 1909583)) (n := 12)
    (lo := (47384513 / 500000000)) (hi := (94769027 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 909583) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 909583) = 1/(909583 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4108 : Bounds (-94769027 / 1000000000) (-47384513 / 500000000) (Real.log (909583 / 1000000)) := by
  have h := reflection_log_4108_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4109_neg : (4104417 / 500000000) ≤ -Real.log (991824766111 / 1000000000000) ∧
    -Real.log (991824766111 / 1000000000000) ≤ (1641767 / 200000000) := by
  have h := checkLog_sound (w := (8175233889 / 1991824766111)) (n := 12)
    (lo := (4104417 / 500000000)) (hi := (1641767 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 991824766111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 991824766111) = 1/(991824766111 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4109 : Bounds (-1641767 / 200000000) (-4104417 / 500000000) (Real.log (991824766111 / 1000000000000)) := by
  have h := reflection_log_4109_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4110_neg : (8166953 / 1000000000) ≤ -Real.log (991866305031 / 1000000000000) ∧
    -Real.log (991866305031 / 1000000000000) ≤ (4083477 / 500000000) := by
  have h := checkLog_sound (w := (8133694969 / 1991866305031)) (n := 12)
    (lo := (8166953 / 1000000000)) (hi := (4083477 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 991866305031) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 991866305031) = 1/(991866305031 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4110 : Bounds (-4083477 / 500000000) (-8166953 / 1000000000) (Real.log (991866305031 / 1000000000000)) := by
  have h := reflection_log_4110_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4111_neg : (45216359 / 250000000) ≤ -Real.log (125000000000 / 149781740863) ∧
    -Real.log (125000000000 / 149781740863) ≤ (180865437 / 1000000000) := by
  have h := checkLog_sound (w := (24781740863 / 274781740863)) (n := 12)
    (lo := (45216359 / 250000000)) (hi := (180865437 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((149781740863 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(149781740863 / 125000000000) = 1/(125000000000 / 149781740863) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4111 : Bounds (45216359 / 250000000) (180865437 / 1000000000) (Real.log (149781740863 / 125000000000)) := by
  have h := reflection_log_4111_neg
  have he : Real.log (149781740863 / 125000000000) = -Real.log (125000000000 / 149781740863) := by
    rw [show ((149781740863 / 125000000000) : ℝ) = ((125000000000 / 149781740863) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4112_neg : (90664609 / 500000000) ≤ -Real.log (125000000000 / 149851223033) ∧
    -Real.log (125000000000 / 149851223033) ≤ (181329219 / 1000000000) := by
  have h := checkLog_sound (w := (24851223033 / 274851223033)) (n := 12)
    (lo := (90664609 / 500000000)) (hi := (181329219 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((149851223033 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(149851223033 / 125000000000) = 1/(125000000000 / 149851223033) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4112 : Bounds (90664609 / 500000000) (181329219 / 1000000000) (Real.log (149851223033 / 125000000000)) := by
  have h := reflection_log_4112_neg
  have he : Real.log (149851223033 / 125000000000) = -Real.log (125000000000 / 149851223033) := by
    rw [show ((149851223033 / 125000000000) : ℝ) = ((125000000000 / 149851223033) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4113_neg : (90732997 / 250000000) ≤ -Real.log (250000000000 / 359384521633) ∧
    -Real.log (250000000000 / 359384521633) ≤ (362931989 / 1000000000) := by
  have h := checkLog_sound (w := (109384521633 / 609384521633)) (n := 12)
    (lo := (90732997 / 250000000)) (hi := (362931989 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((359384521633 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(359384521633 / 250000000000) = 1/(250000000000 / 359384521633) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4113 : Bounds (90732997 / 250000000) (362931989 / 1000000000) (Real.log (359384521633 / 250000000000)) := by
  have h := reflection_log_4113_neg
  have he : Real.log (359384521633 / 250000000000) = -Real.log (250000000000 / 359384521633) := by
    rw [show ((359384521633 / 250000000000) : ℝ) = ((250000000000 / 359384521633) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4114_neg : (7262773 / 20000000) ≤ -Real.log (500000000000 / 718917601171) ∧
    -Real.log (500000000000 / 718917601171) ≤ (363138651 / 1000000000) := by
  have h := checkLog_sound (w := (218917601171 / 1218917601171)) (n := 12)
    (lo := (7262773 / 20000000)) (hi := (363138651 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((718917601171 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(718917601171 / 500000000000) = 1/(500000000000 / 718917601171) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4114 : Bounds (7262773 / 20000000) (363138651 / 1000000000) (Real.log (718917601171 / 500000000000)) := by
  have h := reflection_log_4114_neg
  have he : Real.log (718917601171 / 500000000000) = -Real.log (500000000000 / 718917601171) := by
    rw [show ((718917601171 / 500000000000) : ℝ) = ((500000000000 / 718917601171) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4115_neg : (20657521 / 125000000) ≤ -Real.log (10000 / 11797) ∧
    -Real.log (10000 / 11797) ≤ (165260169 / 1000000000) := by
  have h := checkLog_sound (w := (1797 / 21797)) (n := 12)
    (lo := (20657521 / 125000000)) (hi := (165260169 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11797 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11797 / 10000) = 1/(10000 / 11797) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4115 : Bounds (20657521 / 125000000) (165260169 / 1000000000) (Real.log (11797 / 10000)) := by
  have h := reflection_log_4115_neg
  have he : Real.log (11797 / 10000) = -Real.log (10000 / 11797) := by
    rw [show ((11797 / 10000) : ℝ) = ((10000 / 11797) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4116_neg : (198085151 / 1000000000) ≤ -Real.log (8203 / 10000) ∧
    -Real.log (8203 / 10000) ≤ (6190161 / 31250000) := by
  have h := checkLog_sound (w := (1797 / 18203)) (n := 12)
    (lo := (198085151 / 1000000000)) (hi := (6190161 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8203) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8203) = 1/(8203 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4116 : Bounds (-6190161 / 31250000) (-198085151 / 1000000000) (Real.log (8203 / 10000)) := by
  have h := reflection_log_4116_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4117_neg : (179683 / 1000000000) ≤ -Real.log (10000000 / 10001797) ∧
    -Real.log (10000000 / 10001797) ≤ (44921 / 250000000) := by
  have h := checkLog_sound (w := (1797 / 20001797)) (n := 12)
    (lo := (179683 / 1000000000)) (hi := (44921 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001797 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001797 / 10000000) = 1/(10000000 / 10001797) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4117 : Bounds (179683 / 1000000000) (44921 / 250000000) (Real.log (10001797 / 10000000)) := by
  have h := reflection_log_4117_neg
  have he : Real.log (10001797 / 10000000) = -Real.log (10000000 / 10001797) := by
    rw [show ((10001797 / 10000000) : ℝ) = ((10000000 / 10001797) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4118_neg : (44929 / 250000000) ≤ -Real.log (9998203 / 10000000) ∧
    -Real.log (9998203 / 10000000) ≤ (179717 / 1000000000) := by
  have h := checkLog_sound (w := (1797 / 19998203)) (n := 12)
    (lo := (44929 / 250000000)) (hi := (179717 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998203) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998203) = 1/(9998203 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4118 : Bounds (-179717 / 1000000000) (-44929 / 250000000) (Real.log (9998203 / 10000000)) := by
  have h := reflection_log_4118_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4119_neg : (86396021 / 1000000000) ≤ -Real.log (500000 / 545119) ∧
    -Real.log (500000 / 545119) ≤ (43198011 / 500000000) := by
  have h := checkLog_sound (w := (45119 / 1045119)) (n := 12)
    (lo := (86396021 / 1000000000)) (hi := (43198011 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((545119 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(545119 / 500000) = 1/(500000 / 545119) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4119 : Bounds (86396021 / 1000000000) (43198011 / 500000000) (Real.log (545119 / 500000)) := by
  have h := reflection_log_4119_neg
  have he : Real.log (545119 / 500000) = -Real.log (500000 / 545119) := by
    rw [show ((545119 / 500000) : ℝ) = ((500000 / 545119) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4120_neg : (23643063 / 250000000) ≤ -Real.log (454881 / 500000) ∧
    -Real.log (454881 / 500000) ≤ (94572253 / 1000000000) := by
  have h := checkLog_sound (w := (45119 / 954881)) (n := 12)
    (lo := (23643063 / 250000000)) (hi := (94572253 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 454881) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 454881) = 1/(454881 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4120 : Bounds (-94572253 / 1000000000) (-23643063 / 250000000) (Real.log (454881 / 500000)) := by
  have h := reflection_log_4120_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4121_neg : (86606961 / 1000000000) ≤ -Real.log (250000 / 272617) ∧
    -Real.log (250000 / 272617) ≤ (43303481 / 500000000) := by
  have h := checkLog_sound (w := (22617 / 522617)) (n := 12)
    (lo := (86606961 / 1000000000)) (hi := (43303481 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((272617 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(272617 / 250000) = 1/(250000 / 272617) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4121 : Bounds (86606961 / 1000000000) (43303481 / 500000000) (Real.log (272617 / 250000)) := by
  have h := reflection_log_4121_neg
  have he : Real.log (272617 / 250000) = -Real.log (250000 / 272617) := by
    rw [show ((272617 / 250000) : ℝ) = ((250000 / 272617) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4122_neg : (94825097 / 1000000000) ≤ -Real.log (227383 / 250000) ∧
    -Real.log (227383 / 250000) ≤ (47412549 / 500000000) := by
  have h := checkLog_sound (w := (22617 / 477383)) (n := 12)
    (lo := (94825097 / 1000000000)) (hi := (47412549 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 227383) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 227383) = 1/(227383 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4122 : Bounds (-47412549 / 500000000) (-94825097 / 1000000000) (Real.log (227383 / 250000)) := by
  have h := reflection_log_4122_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4123_neg : (1643627 / 200000000) ≤ -Real.log (61988471311 / 62500000000) ∧
    -Real.log (61988471311 / 62500000000) ≤ (1027267 / 125000000) := by
  have h := checkLog_sound (w := (511528689 / 124488471311)) (n := 12)
    (lo := (1643627 / 200000000)) (hi := (1027267 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 61988471311) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 61988471311) = 1/(61988471311 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4123 : Bounds (-1027267 / 125000000) (-1643627 / 200000000) (Real.log (61988471311 / 62500000000)) := by
  have h := reflection_log_4123_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4124_neg : (8176231 / 1000000000) ≤ -Real.log (247964275839 / 250000000000) ∧
    -Real.log (247964275839 / 250000000000) ≤ (1022029 / 125000000) := by
  have h := checkLog_sound (w := (2035724161 / 497964275839)) (n := 12)
    (lo := (8176231 / 1000000000)) (hi := (1022029 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247964275839) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247964275839) = 1/(247964275839 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4124 : Bounds (-1022029 / 125000000) (-8176231 / 1000000000) (Real.log (247964275839 / 250000000000)) := by
  have h := reflection_log_4124_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4125_neg : (180968273 / 1000000000) ≤ -Real.log (50000000000 / 59918857899) ∧
    -Real.log (50000000000 / 59918857899) ≤ (90484137 / 500000000) := by
  have h := checkLog_sound (w := (9918857899 / 109918857899)) (n := 12)
    (lo := (180968273 / 1000000000)) (hi := (90484137 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((59918857899 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(59918857899 / 50000000000) = 1/(50000000000 / 59918857899) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4125 : Bounds (180968273 / 1000000000) (90484137 / 500000000) (Real.log (59918857899 / 50000000000)) := by
  have h := reflection_log_4125_neg
  have he : Real.log (59918857899 / 50000000000) = -Real.log (50000000000 / 59918857899) := by
    rw [show ((59918857899 / 50000000000) : ℝ) = ((50000000000 / 59918857899) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4126_neg : (181432059 / 1000000000) ≤ -Real.log (125000000000 / 149866634709) ∧
    -Real.log (125000000000 / 149866634709) ≤ (9071603 / 50000000) := by
  have h := checkLog_sound (w := (24866634709 / 274866634709)) (n := 12)
    (lo := (181432059 / 1000000000)) (hi := (9071603 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((149866634709 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(149866634709 / 125000000000) = 1/(125000000000 / 149866634709) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4126 : Bounds (181432059 / 1000000000) (9071603 / 50000000) (Real.log (149866634709 / 125000000000)) := by
  have h := reflection_log_4126_neg
  have he : Real.log (149866634709 / 125000000000) = -Real.log (125000000000 / 149866634709) := by
    rw [show ((149866634709 / 125000000000) : ℝ) = ((125000000000 / 149866634709) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4127_neg : (7262773 / 20000000) ≤ -Real.log (50000000000 / 71891760117) ∧
    -Real.log (50000000000 / 71891760117) ≤ (363138651 / 1000000000) := by
  have h := checkLog_sound (w := (21891760117 / 121891760117)) (n := 12)
    (lo := (7262773 / 20000000)) (hi := (363138651 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((71891760117 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(71891760117 / 50000000000) = 1/(50000000000 / 71891760117) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4127 : Bounds (7262773 / 20000000) (363138651 / 1000000000) (Real.log (71891760117 / 50000000000)) := by
  have h := reflection_log_4127_neg
  have he : Real.log (71891760117 / 50000000000) = -Real.log (50000000000 / 71891760117) := by
    rw [show ((71891760117 / 50000000000) : ℝ) = ((50000000000 / 71891760117) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4128_neg : (9083633 / 25000000) ≤ -Real.log (100000000000 / 143813239059) ∧
    -Real.log (100000000000 / 143813239059) ≤ (363345321 / 1000000000) := by
  have h := checkLog_sound (w := (43813239059 / 243813239059)) (n := 12)
    (lo := (9083633 / 25000000)) (hi := (363345321 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((143813239059 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(143813239059 / 100000000000) = 1/(100000000000 / 143813239059) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4128 : Bounds (9083633 / 25000000) (363345321 / 1000000000) (Real.log (143813239059 / 100000000000)) := by
  have h := reflection_log_4128_neg
  have he : Real.log (143813239059 / 100000000000) = -Real.log (100000000000 / 143813239059) := by
    rw [show ((143813239059 / 100000000000) : ℝ) = ((100000000000 / 143813239059) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4129_neg : (41336233 / 250000000) ≤ -Real.log (5000 / 5899) ∧
    -Real.log (5000 / 5899) ≤ (165344933 / 1000000000) := by
  have h := checkLog_sound (w := (899 / 10899)) (n := 12)
    (lo := (41336233 / 250000000)) (hi := (165344933 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5899 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5899 / 5000) = 1/(5000 / 5899) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4129 : Bounds (41336233 / 250000000) (165344933 / 1000000000) (Real.log (5899 / 5000)) := by
  have h := reflection_log_4129_neg
  have he : Real.log (5899 / 5000) = -Real.log (5000 / 5899) := by
    rw [show ((5899 / 5000) : ℝ) = ((5000 / 5899) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4130_neg : (99103533 / 500000000) ≤ -Real.log (4101 / 5000) ∧
    -Real.log (4101 / 5000) ≤ (198207067 / 1000000000) := by
  have h := checkLog_sound (w := (899 / 9101)) (n := 12)
    (lo := (99103533 / 500000000)) (hi := (198207067 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4101) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4101) = 1/(4101 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4130 : Bounds (-198207067 / 1000000000) (-99103533 / 500000000) (Real.log (4101 / 5000)) := by
  have h := reflection_log_4130_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4131_neg : (179783 / 1000000000) ≤ -Real.log (5000000 / 5000899) ∧
    -Real.log (5000000 / 5000899) ≤ (22473 / 125000000) := by
  have h := checkLog_sound (w := (899 / 10000899)) (n := 12)
    (lo := (179783 / 1000000000)) (hi := (22473 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000899 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000899 / 5000000) = 1/(5000000 / 5000899) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4131 : Bounds (179783 / 1000000000) (22473 / 125000000) (Real.log (5000899 / 5000000)) := by
  have h := reflection_log_4131_neg
  have he : Real.log (5000899 / 5000000) = -Real.log (5000000 / 5000899) := by
    rw [show ((5000899 / 5000000) : ℝ) = ((5000000 / 5000899) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4132_neg : (22477 / 125000000) ≤ -Real.log (4999101 / 5000000) ∧
    -Real.log (4999101 / 5000000) ≤ (179817 / 1000000000) := by
  have h := checkLog_sound (w := (899 / 9999101)) (n := 12)
    (lo := (22477 / 125000000)) (hi := (179817 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999101) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999101) = 1/(4999101 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4132 : Bounds (-179817 / 1000000000) (-22477 / 125000000) (Real.log (4999101 / 5000000)) := by
  have h := reflection_log_4132_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4133_neg : (86441881 / 1000000000) ≤ -Real.log (62500 / 68143) ∧
    -Real.log (62500 / 68143) ≤ (43220941 / 500000000) := by
  have h := checkLog_sound (w := (5643 / 130643)) (n := 12)
    (lo := (86441881 / 1000000000)) (hi := (43220941 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((68143 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(68143 / 62500) = 1/(62500 / 68143) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4133 : Bounds (86441881 / 1000000000) (43220941 / 500000000) (Real.log (68143 / 62500)) := by
  have h := reflection_log_4133_neg
  have he : Real.log (68143 / 62500) = -Real.log (62500 / 68143) := by
    rw [show ((68143 / 62500) : ℝ) = ((62500 / 68143) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4134_neg : (94627213 / 1000000000) ≤ -Real.log (56857 / 62500) ∧
    -Real.log (56857 / 62500) ≤ (47313607 / 500000000) := by
  have h := checkLog_sound (w := (5643 / 119357)) (n := 12)
    (lo := (94627213 / 1000000000)) (hi := (47313607 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 56857) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 56857) = 1/(56857 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4134 : Bounds (-47313607 / 500000000) (-94627213 / 1000000000) (Real.log (56857 / 62500)) := by
  have h := reflection_log_4134_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4135_neg : (86653729 / 1000000000) ≤ -Real.log (1000000 / 1090519) ∧
    -Real.log (1000000 / 1090519) ≤ (8665373 / 100000000) := by
  have h := checkLog_sound (w := (90519 / 2090519)) (n := 12)
    (lo := (86653729 / 1000000000)) (hi := (8665373 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1090519 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1090519 / 1000000) = 1/(1000000 / 1090519) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4135 : Bounds (86653729 / 1000000000) (8665373 / 100000000) (Real.log (1090519 / 1000000)) := by
  have h := reflection_log_4135_neg
  have he : Real.log (1090519 / 1000000) = -Real.log (1000000 / 1090519) := by
    rw [show ((1090519 / 1000000) : ℝ) = ((1000000 / 1090519) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4136_neg : (94881171 / 1000000000) ≤ -Real.log (909481 / 1000000) ∧
    -Real.log (909481 / 1000000) ≤ (23720293 / 250000000) := by
  have h := checkLog_sound (w := (90519 / 1909481)) (n := 12)
    (lo := (94881171 / 1000000000)) (hi := (23720293 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 909481) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 909481) = 1/(909481 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4136 : Bounds (-23720293 / 250000000) (-94881171 / 1000000000) (Real.log (909481 / 1000000)) := by
  have h := reflection_log_4136_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4137_neg : (4113721 / 500000000) ≤ -Real.log (991806310639 / 1000000000000) ∧
    -Real.log (991806310639 / 1000000000000) ≤ (8227443 / 1000000000) := by
  have h := checkLog_sound (w := (8193689361 / 1991806310639)) (n := 12)
    (lo := (4113721 / 500000000)) (hi := (8227443 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 991806310639) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 991806310639) = 1/(991806310639 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4137 : Bounds (-8227443 / 1000000000) (-4113721 / 500000000) (Real.log (991806310639 / 1000000000000)) := by
  have h := reflection_log_4137_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4138_neg : (8185331 / 1000000000) ≤ -Real.log (3874406551 / 3906250000) ∧
    -Real.log (3874406551 / 3906250000) ≤ (2046333 / 250000000) := by
  have h := checkLog_sound (w := (31843449 / 7780656551)) (n := 12)
    (lo := (8185331 / 1000000000)) (hi := (2046333 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3906250000 / 3874406551) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3906250000 / 3874406551) = 1/(3874406551 / 3906250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4138 : Bounds (-2046333 / 250000000) (-8185331 / 1000000000) (Real.log (3874406551 / 3906250000)) := by
  have h := reflection_log_4138_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4139_neg : (90534547 / 500000000) ≤ -Real.log (500000000000 / 599248993087) ∧
    -Real.log (500000000000 / 599248993087) ≤ (36213819 / 200000000) := by
  have h := checkLog_sound (w := (99248993087 / 1099248993087)) (n := 12)
    (lo := (90534547 / 500000000)) (hi := (36213819 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((599248993087 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(599248993087 / 500000000000) = 1/(500000000000 / 599248993087) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4139 : Bounds (90534547 / 500000000) (36213819 / 200000000) (Real.log (599248993087 / 500000000000)) := by
  have h := reflection_log_4139_neg
  have he : Real.log (599248993087 / 500000000000) = -Real.log (500000000000 / 599248993087) := by
    rw [show ((599248993087 / 500000000000) : ℝ) = ((500000000000 / 599248993087) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4140_neg : (181534901 / 1000000000) ≤ -Real.log (500000000000 / 599528192453) ∧
    -Real.log (500000000000 / 599528192453) ≤ (90767451 / 500000000) := by
  have h := checkLog_sound (w := (99528192453 / 1099528192453)) (n := 12)
    (lo := (181534901 / 1000000000)) (hi := (90767451 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((599528192453 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(599528192453 / 500000000000) = 1/(500000000000 / 599528192453) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4140 : Bounds (181534901 / 1000000000) (90767451 / 500000000) (Real.log (599528192453 / 500000000000)) := by
  have h := reflection_log_4140_neg
  have he : Real.log (599528192453 / 500000000000) = -Real.log (500000000000 / 599528192453) := by
    rw [show ((599528192453 / 500000000000) : ℝ) = ((500000000000 / 599528192453) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4141_neg : (9083633 / 25000000) ≤ -Real.log (250000000000 / 359533097647) ∧
    -Real.log (250000000000 / 359533097647) ≤ (363345321 / 1000000000) := by
  have h := checkLog_sound (w := (109533097647 / 609533097647)) (n := 12)
    (lo := (9083633 / 25000000)) (hi := (363345321 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((359533097647 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(359533097647 / 250000000000) = 1/(250000000000 / 359533097647) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4141 : Bounds (9083633 / 25000000) (363345321 / 1000000000) (Real.log (359533097647 / 250000000000)) := by
  have h := reflection_log_4141_neg
  have he : Real.log (359533097647 / 250000000000) = -Real.log (250000000000 / 359533097647) := by
    rw [show ((359533097647 / 250000000000) : ℝ) = ((250000000000 / 359533097647) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4142_neg : (181775999 / 500000000) ≤ -Real.log (500000000000 / 719214825653) ∧
    -Real.log (500000000000 / 719214825653) ≤ (363551999 / 1000000000) := by
  have h := checkLog_sound (w := (219214825653 / 1219214825653)) (n := 12)
    (lo := (181775999 / 500000000)) (hi := (363551999 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((719214825653 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(719214825653 / 500000000000) = 1/(500000000000 / 719214825653) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4142 : Bounds (181775999 / 500000000) (363551999 / 1000000000) (Real.log (719214825653 / 500000000000)) := by
  have h := reflection_log_4142_neg
  have he : Real.log (719214825653 / 500000000000) = -Real.log (500000000000 / 719214825653) := by
    rw [show ((719214825653 / 500000000000) : ℝ) = ((500000000000 / 719214825653) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4143_neg : (165429689 / 1000000000) ≤ -Real.log (10000 / 11799) ∧
    -Real.log (10000 / 11799) ≤ (16542969 / 100000000) := by
  have h := checkLog_sound (w := (1799 / 21799)) (n := 12)
    (lo := (165429689 / 1000000000)) (hi := (16542969 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11799 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11799 / 10000) = 1/(10000 / 11799) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4143 : Bounds (165429689 / 1000000000) (16542969 / 100000000) (Real.log (11799 / 10000)) := by
  have h := reflection_log_4143_neg
  have he : Real.log (11799 / 10000) = -Real.log (10000 / 11799) := by
    rw [show ((11799 / 10000) : ℝ) = ((10000 / 11799) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4144_neg : (99164497 / 500000000) ≤ -Real.log (8201 / 10000) ∧
    -Real.log (8201 / 10000) ≤ (39665799 / 200000000) := by
  have h := checkLog_sound (w := (1799 / 18201)) (n := 12)
    (lo := (99164497 / 500000000)) (hi := (39665799 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8201) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8201) = 1/(8201 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4144 : Bounds (-39665799 / 200000000) (-99164497 / 500000000) (Real.log (8201 / 10000)) := by
  have h := reflection_log_4144_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4145_neg : (179883 / 1000000000) ≤ -Real.log (10000000 / 10001799) ∧
    -Real.log (10000000 / 10001799) ≤ (44971 / 250000000) := by
  have h := checkLog_sound (w := (1799 / 20001799)) (n := 12)
    (lo := (179883 / 1000000000)) (hi := (44971 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001799 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001799 / 10000000) = 1/(10000000 / 10001799) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4145 : Bounds (179883 / 1000000000) (44971 / 250000000) (Real.log (10001799 / 10000000)) := by
  have h := reflection_log_4145_neg
  have he : Real.log (10001799 / 10000000) = -Real.log (10000000 / 10001799) := by
    rw [show ((10001799 / 10000000) : ℝ) = ((10000000 / 10001799) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4146_neg : (44979 / 250000000) ≤ -Real.log (9998201 / 10000000) ∧
    -Real.log (9998201 / 10000000) ≤ (179917 / 1000000000) := by
  have h := checkLog_sound (w := (1799 / 19998201)) (n := 12)
    (lo := (44979 / 250000000)) (hi := (179917 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998201) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998201) = 1/(9998201 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4146 : Bounds (-179917 / 1000000000) (-44979 / 250000000) (Real.log (9998201 / 10000000)) := by
  have h := reflection_log_4146_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4147_neg : (86488657 / 1000000000) ≤ -Real.log (1000000 / 1090339) ∧
    -Real.log (1000000 / 1090339) ≤ (43244329 / 500000000) := by
  have h := checkLog_sound (w := (90339 / 2090339)) (n := 12)
    (lo := (86488657 / 1000000000)) (hi := (43244329 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1090339 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1090339 / 1000000) = 1/(1000000 / 1090339) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4147 : Bounds (86488657 / 1000000000) (43244329 / 500000000) (Real.log (1090339 / 1000000)) := by
  have h := reflection_log_4147_neg
  have he : Real.log (1090339 / 1000000) = -Real.log (1000000 / 1090339) := by
    rw [show ((1090339 / 1000000) : ℝ) = ((1000000 / 1090339) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4148_neg : (23670819 / 250000000) ≤ -Real.log (909661 / 1000000) ∧
    -Real.log (909661 / 1000000) ≤ (94683277 / 1000000000) := by
  have h := checkLog_sound (w := (90339 / 1909661)) (n := 12)
    (lo := (23670819 / 250000000)) (hi := (94683277 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 909661) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 909661) = 1/(909661 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4148 : Bounds (-94683277 / 1000000000) (-23670819 / 250000000) (Real.log (909661 / 1000000)) := by
  have h := reflection_log_4148_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4149_neg : (17340099 / 200000000) ≤ -Real.log (100000 / 109057) ∧
    -Real.log (100000 / 109057) ≤ (5418781 / 62500000) := by
  have h := checkLog_sound (w := (9057 / 209057)) (n := 12)
    (lo := (17340099 / 200000000)) (hi := (5418781 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((109057 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(109057 / 100000) = 1/(100000 / 109057) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4149 : Bounds (17340099 / 200000000) (5418781 / 62500000) (Real.log (109057 / 100000)) := by
  have h := reflection_log_4149_neg
  have he : Real.log (109057 / 100000) = -Real.log (100000 / 109057) := by
    rw [show ((109057 / 100000) : ℝ) = ((100000 / 109057) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4150_neg : (94937249 / 1000000000) ≤ -Real.log (90943 / 100000) ∧
    -Real.log (90943 / 100000) ≤ (379749 / 4000000) := by
  have h := checkLog_sound (w := (9057 / 190943)) (n := 12)
    (lo := (94937249 / 1000000000)) (hi := (379749 / 4000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 90943) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 90943) = 1/(90943 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4150 : Bounds (-379749 / 4000000) (-94937249 / 1000000000) (Real.log (90943 / 100000)) := by
  have h := reflection_log_4150_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4151_neg : (4118377 / 500000000) ≤ -Real.log (9917970751 / 10000000000) ∧
    -Real.log (9917970751 / 10000000000) ≤ (1647351 / 200000000) := by
  have h := checkLog_sound (w := (82029249 / 19917970751)) (n := 12)
    (lo := (4118377 / 500000000)) (hi := (1647351 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 9917970751) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 9917970751) = 1/(9917970751 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4151 : Bounds (-1647351 / 200000000) (-4118377 / 500000000) (Real.log (9917970751 / 10000000000)) := by
  have h := reflection_log_4151_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4152_neg : (8194619 / 1000000000) ≤ -Real.log (991838865079 / 1000000000000) ∧
    -Real.log (991838865079 / 1000000000000) ≤ (409731 / 50000000) := by
  have h := checkLog_sound (w := (8161134921 / 1991838865079)) (n := 12)
    (lo := (8194619 / 1000000000)) (hi := (409731 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 991838865079) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 991838865079) = 1/(991838865079 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4152 : Bounds (-409731 / 50000000) (-8194619 / 1000000000) (Real.log (991838865079 / 1000000000000)) := by
  have h := reflection_log_4152_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4153_neg : (181171933 / 1000000000) ≤ -Real.log (125000000000 / 149827655577) ∧
    -Real.log (125000000000 / 149827655577) ≤ (90585967 / 500000000) := by
  have h := checkLog_sound (w := (24827655577 / 274827655577)) (n := 12)
    (lo := (181171933 / 1000000000)) (hi := (90585967 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((149827655577 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(149827655577 / 125000000000) = 1/(125000000000 / 149827655577) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4153 : Bounds (181171933 / 1000000000) (90585967 / 500000000) (Real.log (149827655577 / 125000000000)) := by
  have h := reflection_log_4153_neg
  have he : Real.log (149827655577 / 125000000000) = -Real.log (125000000000 / 149827655577) := by
    rw [show ((149827655577 / 125000000000) : ℝ) = ((125000000000 / 149827655577) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4154_neg : (11352359 / 62500000) ≤ -Real.log (100000000000 / 119917970597) ∧
    -Real.log (100000000000 / 119917970597) ≤ (36327549 / 200000000) := by
  have h := checkLog_sound (w := (19917970597 / 219917970597)) (n := 12)
    (lo := (11352359 / 62500000)) (hi := (36327549 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((119917970597 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(119917970597 / 100000000000) = 1/(100000000000 / 119917970597) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4154 : Bounds (11352359 / 62500000) (36327549 / 200000000) (Real.log (119917970597 / 100000000000)) := by
  have h := reflection_log_4154_neg
  have he : Real.log (119917970597 / 100000000000) = -Real.log (100000000000 / 119917970597) := by
    rw [show ((119917970597 / 100000000000) : ℝ) = ((100000000000 / 119917970597) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4155_neg : (181775999 / 500000000) ≤ -Real.log (125000000000 / 179803706413) ∧
    -Real.log (125000000000 / 179803706413) ≤ (363551999 / 1000000000) := by
  have h := checkLog_sound (w := (54803706413 / 304803706413)) (n := 12)
    (lo := (181775999 / 500000000)) (hi := (363551999 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((179803706413 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(179803706413 / 125000000000) = 1/(125000000000 / 179803706413) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4155 : Bounds (181775999 / 500000000) (363551999 / 1000000000) (Real.log (179803706413 / 125000000000)) := by
  have h := reflection_log_4155_neg
  have he : Real.log (179803706413 / 125000000000) = -Real.log (125000000000 / 179803706413) := by
    rw [show ((179803706413 / 125000000000) : ℝ) = ((125000000000 / 179803706413) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4156_neg : (90939671 / 250000000) ≤ -Real.log (250000000000 / 359681746129) ∧
    -Real.log (250000000000 / 359681746129) ≤ (72751737 / 200000000) := by
  have h := checkLog_sound (w := (109681746129 / 609681746129)) (n := 12)
    (lo := (90939671 / 250000000)) (hi := (72751737 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((359681746129 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(359681746129 / 250000000000) = 1/(250000000000 / 359681746129) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4156 : Bounds (90939671 / 250000000) (72751737 / 200000000) (Real.log (359681746129 / 250000000000)) := by
  have h := reflection_log_4156_neg
  have he : Real.log (359681746129 / 250000000000) = -Real.log (250000000000 / 359681746129) := by
    rw [show ((359681746129 / 250000000000) : ℝ) = ((250000000000 / 359681746129) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4157_neg : (82757219 / 500000000) ≤ -Real.log (50 / 59) ∧
    -Real.log (50 / 59) ≤ (165514439 / 1000000000) := by
  have h := checkLog_sound (w := (9 / 109)) (n := 12)
    (lo := (82757219 / 500000000)) (hi := (165514439 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((59 / 50) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(59 / 50) = 1/(50 / 59) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4157 : Bounds (82757219 / 500000000) (165514439 / 1000000000) (Real.log (59 / 50)) := by
  have h := reflection_log_4157_neg
  have he : Real.log (59 / 50) = -Real.log (50 / 59) := by
    rw [show ((59 / 50) : ℝ) = ((50 / 59) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4158_neg : (99225469 / 500000000) ≤ -Real.log (41 / 50) ∧
    -Real.log (41 / 50) ≤ (198450939 / 1000000000) := by
  have h := checkLog_sound (w := (9 / 91)) (n := 12)
    (lo := (99225469 / 500000000)) (hi := (198450939 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50 / 41) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50 / 41) = 1/(41 / 50) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4158 : Bounds (-198450939 / 1000000000) (-99225469 / 500000000) (Real.log (41 / 50)) := by
  have h := reflection_log_4158_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4159_neg : (179983 / 1000000000) ≤ -Real.log (50000 / 50009) ∧
    -Real.log (50000 / 50009) ≤ (11249 / 62500000) := by
  have h := checkLog_sound (w := (9 / 100009)) (n := 12)
    (lo := (179983 / 1000000000)) (hi := (11249 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50009 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50009 / 50000) = 1/(50000 / 50009) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4159 : Bounds (179983 / 1000000000) (11249 / 62500000) (Real.log (50009 / 50000)) := by
  have h := reflection_log_4159_neg
  have he : Real.log (50009 / 50000) = -Real.log (50000 / 50009) := by
    rw [show ((50009 / 50000) : ℝ) = ((50000 / 50009) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily
