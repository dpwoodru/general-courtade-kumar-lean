import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0146
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

theorem reflection_log_1_neg : (294009667 / 1000000000) ≤ -Real.log (512 / 687) ∧
    -Real.log (512 / 687) ≤ (73502417 / 250000000) := by
  have h := checkLog_sound (w := (175 / 1199)) (n := 12)
    (lo := (294009667 / 1000000000)) (hi := (73502417 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((687 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(687 / 512) = 1/(512 / 687) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (294009667 / 1000000000) (73502417 / 250000000) (Real.log (687 / 512)) := by
  have h := reflection_log_1_neg
  have he : Real.log (687 / 512) = -Real.log (512 / 687) := by
    rw [show ((687 / 512) : ℝ) = ((512 / 687) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (209120847 / 500000000) ≤ -Real.log (337 / 512) ∧
    -Real.log (337 / 512) ≤ (83648339 / 200000000) := by
  have h := checkLog_sound (w := (175 / 849)) (n := 12)
    (lo := (209120847 / 500000000)) (hi := (83648339 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 337) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 337) = 1/(337 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-83648339 / 200000000) (-209120847 / 500000000) (Real.log (337 / 512)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (293135923 / 1000000000) ≤ -Real.log (320 / 429) ∧
    -Real.log (320 / 429) ≤ (73283981 / 250000000) := by
  have h := checkLog_sound (w := (109 / 749)) (n := 12)
    (lo := (293135923 / 1000000000)) (hi := (73283981 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((429 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(429 / 320) = 1/(320 / 429) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (293135923 / 1000000000) (73283981 / 250000000) (Real.log (429 / 320)) := by
  have h := reflection_log_3_neg
  have he : Real.log (429 / 320) = -Real.log (320 / 429) := by
    rw [show ((429 / 320) : ℝ) = ((320 / 429) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (208231431 / 500000000) ≤ -Real.log (211 / 320) ∧
    -Real.log (211 / 320) ≤ (416462863 / 1000000000) := by
  have h := checkLog_sound (w := (109 / 531)) (n := 12)
    (lo := (208231431 / 500000000)) (hi := (416462863 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 211) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(320 / 211) = 1/(211 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-416462863 / 1000000000) (-208231431 / 500000000) (Real.log (211 / 320)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (104186129 / 200000000) ≤ -Real.log (256 / 431) ∧
    -Real.log (256 / 431) ≤ (260465323 / 500000000) := by
  have h := checkLog_sound (w := (175 / 687)) (n := 12)
    (lo := (104186129 / 200000000)) (hi := (260465323 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((431 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(431 / 256) = 1/(256 / 431) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (104186129 / 200000000) (260465323 / 500000000) (Real.log (431 / 256)) := by
  have h := reflection_log_5_neg
  have he : Real.log (431 / 256) = -Real.log (256 / 431) := by
    rw [show ((431 / 256) : ℝ) = ((256 / 431) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1150728289 / 1000000000) ≤ -Real.log (81 / 256) ∧
    -Real.log (81 / 256) ≤ (1150728291 / 1000000000) := by
  have h := checkLog_sound (w := (47 / 209)) (n := 12)
    (lo := (457581109 / 1000000000)) (hi := (45758111 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((128 / 81) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(128 / 81) = 1/(81 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1150728291 / 1000000000) (-1150728289 / 1000000000) (Real.log (81 / 256)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (129884391 / 250000000) ≤ -Real.log (160 / 269) ∧
    -Real.log (160 / 269) ≤ (103907513 / 200000000) := by
  have h := checkLog_sound (w := (109 / 429)) (n := 12)
    (lo := (129884391 / 250000000)) (hi := (103907513 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((269 / 160) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(269 / 160) = 1/(160 / 269) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (129884391 / 250000000) (103907513 / 200000000) (Real.log (269 / 160)) := by
  have h := reflection_log_7_neg
  have he : Real.log (269 / 160) = -Real.log (160 / 269) := by
    rw [show ((269 / 160) : ℝ) = ((160 / 269) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (1143348181 / 1000000000) ≤ -Real.log (51 / 160) ∧
    -Real.log (51 / 160) ≤ (1143348183 / 1000000000) := by
  have h := checkLog_sound (w := (29 / 131)) (n := 12)
    (lo := (450201001 / 1000000000)) (hi := (225100501 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80 / 51) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(80 / 51) = 1/(51 / 160) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1143348183 / 1000000000) (-1143348181 / 1000000000) (Real.log (51 / 160)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (200553479 / 500000000) ≤ -Real.log (1000000 / 1493477) ∧
    -Real.log (1000000 / 1493477) ≤ (401106959 / 1000000000) := by
  have h := checkLog_sound (w := (493477 / 2493477)) (n := 12)
    (lo := (200553479 / 500000000)) (hi := (401106959 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1493477 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1493477 / 1000000) = 1/(1000000 / 1493477) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (200553479 / 500000000) (401106959 / 1000000000) (Real.log (1493477 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1493477 / 1000000) = -Real.log (1000000 / 1493477) := by
    rw [show ((1493477 / 1000000) : ℝ) = ((1000000 / 1493477) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (340092773 / 500000000) ≤ -Real.log (506523 / 1000000) ∧
    -Real.log (506523 / 1000000) ≤ (680185547 / 1000000000) := by
  have h := checkLog_sound (w := (493477 / 1506523)) (n := 12)
    (lo := (340092773 / 500000000)) (hi := (680185547 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 506523) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 506523) = 1/(506523 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-680185547 / 1000000000) (-340092773 / 500000000) (Real.log (506523 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (402314149 / 1000000000) ≤ -Real.log (1000000 / 1495281) ∧
    -Real.log (1000000 / 1495281) ≤ (8046283 / 20000000) := by
  have h := checkLog_sound (w := (495281 / 2495281)) (n := 12)
    (lo := (402314149 / 1000000000)) (hi := (8046283 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1495281 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1495281 / 1000000) = 1/(1000000 / 1495281) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (402314149 / 1000000000) (8046283 / 20000000) (Real.log (1495281 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1495281 / 1000000) = -Real.log (1000000 / 1495281) := by
    rw [show ((1495281 / 1000000) : ℝ) = ((1000000 / 1495281) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (4273459 / 6250000) ≤ -Real.log (504719 / 1000000) ∧
    -Real.log (504719 / 1000000) ≤ (683753441 / 1000000000) := by
  have h := checkLog_sound (w := (495281 / 1504719)) (n := 12)
    (lo := (4273459 / 6250000)) (hi := (683753441 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 504719) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 504719) = 1/(504719 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-683753441 / 1000000000) (-4273459 / 6250000) (Real.log (504719 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (31777641 / 100000000) ≤ -Real.log (1000000 / 1374069) ∧
    -Real.log (1000000 / 1374069) ≤ (317776411 / 1000000000) := by
  have h := checkLog_sound (w := (374069 / 2374069)) (n := 12)
    (lo := (31777641 / 100000000)) (hi := (317776411 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1374069 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1374069 / 1000000) = 1/(1000000 / 1374069) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (31777641 / 100000000) (317776411 / 1000000000) (Real.log (1374069 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1374069 / 1000000) = -Real.log (1000000 / 1374069) := by
    rw [show ((1374069 / 1000000) : ℝ) = ((1000000 / 1374069) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (468515137 / 1000000000) ≤ -Real.log (625931 / 1000000) ∧
    -Real.log (625931 / 1000000) ≤ (234257569 / 500000000) := by
  have h := checkLog_sound (w := (374069 / 1625931)) (n := 12)
    (lo := (468515137 / 1000000000)) (hi := (234257569 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 625931) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 625931) = 1/(625931 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-234257569 / 500000000) (-468515137 / 1000000000) (Real.log (625931 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (63782943 / 200000000) ≤ -Real.log (500000 / 687817) ∧
    -Real.log (500000 / 687817) ≤ (79728679 / 250000000) := by
  have h := checkLog_sound (w := (187817 / 1187817)) (n := 12)
    (lo := (63782943 / 200000000)) (hi := (79728679 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((687817 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(687817 / 500000) = 1/(500000 / 687817) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (63782943 / 200000000) (79728679 / 250000000) (Real.log (687817 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (687817 / 500000) = -Real.log (500000 / 687817) := by
    rw [show ((687817 / 500000) : ℝ) = ((500000 / 687817) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (29438659 / 62500000) ≤ -Real.log (312183 / 500000) ∧
    -Real.log (312183 / 500000) ≤ (94203709 / 200000000) := by
  have h := checkLog_sound (w := (187817 / 812183)) (n := 12)
    (lo := (29438659 / 62500000)) (hi := (94203709 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 312183) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 312183) = 1/(312183 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-94203709 / 200000000) (-29438659 / 62500000) (Real.log (312183 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (135161563 / 125000000) ≤ -Real.log (500000000000 / 1474244012611) ∧
    -Real.log (500000000000 / 1474244012611) ≤ (540646253 / 500000000) := by
  have h := checkLog_sound (w := (474244012611 / 2474244012611)) (n := 12)
    (lo := (97036331 / 250000000)) (hi := (15525813 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1474244012611 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1474244012611 / 1000000000000) = 1/(500000000000 / 1474244012611) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (135161563 / 125000000) (540646253 / 500000000) (Real.log (1474244012611 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1474244012611 / 500000000000) = -Real.log (500000000000 / 1474244012611) := by
    rw [show ((1474244012611 / 500000000000) : ℝ) = ((500000000000 / 1474244012611) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (271516897 / 250000000) ≤ -Real.log (250000000000 / 740650243007) ∧
    -Real.log (250000000000 / 740650243007) ≤ (108606759 / 100000000) := by
  have h := checkLog_sound (w := (240650243007 / 1240650243007)) (n := 12)
    (lo := (49115051 / 125000000)) (hi := (392920409 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((740650243007 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(740650243007 / 500000000000) = 1/(250000000000 / 740650243007) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (271516897 / 250000000) (108606759 / 100000000) (Real.log (740650243007 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (740650243007 / 250000000000) = -Real.log (250000000000 / 740650243007) := by
    rw [show ((740650243007 / 250000000000) : ℝ) = ((250000000000 / 740650243007) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (786291547 / 1000000000) ≤ -Real.log (125000000000 / 274405046243) ∧
    -Real.log (125000000000 / 274405046243) ≤ (786291549 / 1000000000) := by
  have h := checkLog_sound (w := (24405046243 / 524405046243)) (n := 12)
    (lo := (93144367 / 1000000000)) (hi := (5821523 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((274405046243 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(274405046243 / 250000000000) = 1/(125000000000 / 274405046243) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (786291547 / 1000000000) (786291549 / 1000000000) (Real.log (274405046243 / 125000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (274405046243 / 125000000000) = -Real.log (125000000000 / 274405046243) := by
    rw [show ((274405046243 / 125000000000) : ℝ) = ((125000000000 / 274405046243) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (789933259 / 1000000000) ≤ -Real.log (125000000000 / 275406172021) ∧
    -Real.log (125000000000 / 275406172021) ≤ (789933261 / 1000000000) := by
  have h := checkLog_sound (w := (25406172021 / 525406172021)) (n := 12)
    (lo := (96786079 / 1000000000)) (hi := (604913 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((275406172021 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(275406172021 / 250000000000) = 1/(125000000000 / 275406172021) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (789933259 / 1000000000) (789933261 / 1000000000) (Real.log (275406172021 / 125000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (275406172021 / 125000000000) = -Real.log (125000000000 / 275406172021) := by
    rw [show ((275406172021 / 125000000000) : ℝ) = ((125000000000 / 275406172021) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0146
