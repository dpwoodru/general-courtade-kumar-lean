import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0433
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

theorem reflection_log_1_neg : (48070389 / 250000000) ≤ -Real.log (10240 / 12411) ∧
    -Real.log (10240 / 12411) ≤ (192281557 / 1000000000) := by
  have h := checkLog_sound (w := (2171 / 22651)) (n := 12)
    (lo := (48070389 / 250000000)) (hi := (192281557 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12411 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12411 / 10240) = 1/(10240 / 12411) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (48070389 / 250000000) (192281557 / 1000000000) (Real.log (12411 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12411 / 10240) = -Real.log (10240 / 12411) := by
    rw [show ((12411 / 10240) : ℝ) = ((10240 / 12411) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (11913603 / 50000000) ≤ -Real.log (8069 / 10240) ∧
    -Real.log (8069 / 10240) ≤ (238272061 / 1000000000) := by
  have h := checkLog_sound (w := (2171 / 18309)) (n := 12)
    (lo := (11913603 / 50000000)) (hi := (238272061 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 8069) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 8069) = 1/(8069 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-238272061 / 1000000000) (-11913603 / 50000000) (Real.log (8069 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (96019903 / 500000000) ≤ -Real.log (1280 / 1551) ∧
    -Real.log (1280 / 1551) ≤ (192039807 / 1000000000) := by
  have h := checkLog_sound (w := (271 / 2831)) (n := 12)
    (lo := (96019903 / 500000000)) (hi := (192039807 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1551 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1551 / 1280) = 1/(1280 / 1551) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (96019903 / 500000000) (192039807 / 1000000000) (Real.log (1551 / 1280)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1551 / 1280) = -Real.log (1280 / 1551) := by
    rw [show ((1551 / 1280) : ℝ) = ((1280 / 1551) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (14868771 / 62500000) ≤ -Real.log (1009 / 1280) ∧
    -Real.log (1009 / 1280) ≤ (237900337 / 1000000000) := by
  have h := checkLog_sound (w := (271 / 2289)) (n := 12)
    (lo := (14868771 / 62500000)) (hi := (237900337 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 1009) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 1009) = 1/(1009 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-237900337 / 1000000000) (-14868771 / 62500000) (Real.log (1009 / 1280)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (353486271 / 1000000000) ≤ -Real.log (5120 / 7291) ∧
    -Real.log (5120 / 7291) ≤ (5523223 / 15625000) := by
  have h := checkLog_sound (w := (2171 / 12411)) (n := 12)
    (lo := (353486271 / 1000000000)) (hi := (5523223 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7291 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7291 / 5120) = 1/(5120 / 7291) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (353486271 / 1000000000) (5523223 / 15625000) (Real.log (7291 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (7291 / 5120) = -Real.log (5120 / 7291) := by
    rw [show ((7291 / 5120) : ℝ) = ((5120 / 7291) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (551688309 / 1000000000) ≤ -Real.log (2949 / 5120) ∧
    -Real.log (2949 / 5120) ≤ (55168831 / 100000000) := by
  have h := checkLog_sound (w := (2171 / 8069)) (n := 12)
    (lo := (551688309 / 1000000000)) (hi := (55168831 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2949) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2949) = 1/(2949 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-55168831 / 100000000) (-551688309 / 1000000000) (Real.log (2949 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (2206717 / 6250000) ≤ -Real.log (640 / 911) ∧
    -Real.log (640 / 911) ≤ (353074721 / 1000000000) := by
  have h := checkLog_sound (w := (271 / 1551)) (n := 12)
    (lo := (2206717 / 6250000)) (hi := (353074721 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((911 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(911 / 640) = 1/(640 / 911) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (2206717 / 6250000) (353074721 / 1000000000) (Real.log (911 / 640)) := by
  have h := reflection_log_7_neg
  have he : Real.log (911 / 640) = -Real.log (640 / 911) := by
    rw [show ((911 / 640) : ℝ) = ((640 / 911) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (137667883 / 250000000) ≤ -Real.log (369 / 640) ∧
    -Real.log (369 / 640) ≤ (550671533 / 1000000000) := by
  have h := checkLog_sound (w := (271 / 1009)) (n := 12)
    (lo := (137667883 / 250000000)) (hi := (550671533 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 369) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 369) = 1/(369 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-550671533 / 1000000000) (-137667883 / 250000000) (Real.log (369 / 640)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (10551023 / 40000000) ≤ -Real.log (250000 / 325459) ∧
    -Real.log (250000 / 325459) ≤ (32971947 / 125000000) := by
  have h := checkLog_sound (w := (75459 / 575459)) (n := 12)
    (lo := (10551023 / 40000000)) (hi := (32971947 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((325459 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(325459 / 250000) = 1/(250000 / 325459) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (10551023 / 40000000) (32971947 / 125000000) (Real.log (325459 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (325459 / 250000) = -Real.log (250000 / 325459) := by
    rw [show ((325459 / 250000) : ℝ) = ((250000 / 325459) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (179650623 / 500000000) ≤ -Real.log (174541 / 250000) ∧
    -Real.log (174541 / 250000) ≤ (359301247 / 1000000000) := by
  have h := checkLog_sound (w := (75459 / 424541)) (n := 12)
    (lo := (179650623 / 500000000)) (hi := (359301247 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 174541) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 174541) = 1/(174541 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-359301247 / 1000000000) (-179650623 / 500000000) (Real.log (174541 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (8253211 / 31250000) ≤ -Real.log (500000 / 651131) ∧
    -Real.log (500000 / 651131) ≤ (264102753 / 1000000000) := by
  have h := checkLog_sound (w := (151131 / 1151131)) (n := 12)
    (lo := (8253211 / 31250000)) (hi := (264102753 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((651131 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(651131 / 500000) = 1/(500000 / 651131) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (8253211 / 31250000) (264102753 / 1000000000) (Real.log (651131 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (651131 / 500000) = -Real.log (500000 / 651131) := by
    rw [show ((651131 / 500000) : ℝ) = ((500000 / 651131) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (89977901 / 250000000) ≤ -Real.log (348869 / 500000) ∧
    -Real.log (348869 / 500000) ≤ (71982321 / 200000000) := by
  have h := checkLog_sound (w := (151131 / 848869)) (n := 12)
    (lo := (89977901 / 250000000)) (hi := (71982321 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 348869) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 348869) = 1/(348869 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-71982321 / 200000000) (-89977901 / 250000000) (Real.log (348869 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (197992293 / 1000000000) ≤ -Real.log (1000000 / 1218953) ∧
    -Real.log (1000000 / 1218953) ≤ (98996147 / 500000000) := by
  have h := checkLog_sound (w := (218953 / 2218953)) (n := 12)
    (lo := (197992293 / 1000000000)) (hi := (98996147 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1218953 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1218953 / 1000000) = 1/(1000000 / 1218953) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (197992293 / 1000000000) (98996147 / 500000000) (Real.log (1218953 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1218953 / 1000000) = -Real.log (1000000 / 1218953) := by
    rw [show ((1218953 / 1000000) : ℝ) = ((1000000 / 1218953) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (247119951 / 1000000000) ≤ -Real.log (781047 / 1000000) ∧
    -Real.log (781047 / 1000000) ≤ (15444997 / 62500000) := by
  have h := checkLog_sound (w := (218953 / 1781047)) (n := 12)
    (lo := (247119951 / 1000000000)) (hi := (15444997 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 781047) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 781047) = 1/(781047 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-15444997 / 62500000) (-247119951 / 1000000000) (Real.log (781047 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (619559 / 3125000) ≤ -Real.log (500000 / 609639) ∧
    -Real.log (500000 / 609639) ≤ (198258881 / 1000000000) := by
  have h := checkLog_sound (w := (109639 / 1109639)) (n := 12)
    (lo := (619559 / 3125000)) (hi := (198258881 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((609639 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(609639 / 500000) = 1/(500000 / 609639) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (619559 / 3125000) (198258881 / 1000000000) (Real.log (609639 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (609639 / 500000) = -Real.log (500000 / 609639) := by
    rw [show ((609639 / 500000) : ℝ) = ((500000 / 609639) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (123768073 / 500000000) ≤ -Real.log (390361 / 500000) ∧
    -Real.log (390361 / 500000) ≤ (247536147 / 1000000000) := by
  have h := checkLog_sound (w := (109639 / 890361)) (n := 12)
    (lo := (123768073 / 500000000)) (hi := (247536147 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 390361) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 390361) = 1/(390361 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-247536147 / 1000000000) (-123768073 / 500000000) (Real.log (390361 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (311538411 / 500000000) ≤ -Real.log (125000000000 / 233082055219) ∧
    -Real.log (125000000000 / 233082055219) ≤ (623076823 / 1000000000) := by
  have h := checkLog_sound (w := (108082055219 / 358082055219)) (n := 12)
    (lo := (311538411 / 500000000)) (hi := (623076823 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((233082055219 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(233082055219 / 125000000000) = 1/(125000000000 / 233082055219) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (311538411 / 500000000) (623076823 / 1000000000) (Real.log (233082055219 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (233082055219 / 125000000000) = -Real.log (125000000000 / 233082055219) := by
    rw [show ((233082055219 / 125000000000) : ℝ) = ((125000000000 / 233082055219) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (624014357 / 1000000000) ≤ -Real.log (500000000000 / 933202720793) ∧
    -Real.log (500000000000 / 933202720793) ≤ (312007179 / 500000000) := by
  have h := checkLog_sound (w := (433202720793 / 1433202720793)) (n := 12)
    (lo := (624014357 / 1000000000)) (hi := (312007179 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((933202720793 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(933202720793 / 500000000000) = 1/(500000000000 / 933202720793) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (624014357 / 1000000000) (312007179 / 500000000) (Real.log (933202720793 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (933202720793 / 500000000000) = -Real.log (500000000000 / 933202720793) := by
    rw [show ((933202720793 / 500000000000) : ℝ) = ((500000000000 / 933202720793) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (89022449 / 200000000) ≤ -Real.log (500000000000 / 780332681643) ∧
    -Real.log (500000000000 / 780332681643) ≤ (222556123 / 500000000) := by
  have h := checkLog_sound (w := (280332681643 / 1280332681643)) (n := 12)
    (lo := (89022449 / 200000000)) (hi := (222556123 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((780332681643 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(780332681643 / 500000000000) = 1/(500000000000 / 780332681643) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (89022449 / 200000000) (222556123 / 500000000) (Real.log (780332681643 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (780332681643 / 500000000000) = -Real.log (500000000000 / 780332681643) := by
    rw [show ((780332681643 / 500000000000) : ℝ) = ((500000000000 / 780332681643) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (222897513 / 500000000) ≤ -Real.log (62500000000 / 97608207531) ∧
    -Real.log (62500000000 / 97608207531) ≤ (445795027 / 1000000000) := by
  have h := checkLog_sound (w := (35108207531 / 160108207531)) (n := 12)
    (lo := (222897513 / 500000000)) (hi := (445795027 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((97608207531 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(97608207531 / 62500000000) = 1/(62500000000 / 97608207531) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (222897513 / 500000000) (445795027 / 1000000000) (Real.log (97608207531 / 62500000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (97608207531 / 62500000000) = -Real.log (62500000000 / 97608207531) := by
    rw [show ((97608207531 / 62500000000) : ℝ) = ((62500000000 / 97608207531) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0433
