import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell225
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

theorem reflection_log_1_neg : (161918471 / 500000000) ≤ -Real.log (2560 / 3539) ∧
    -Real.log (2560 / 3539) ≤ (323836943 / 1000000000) := by
  have h := checkLog_sound (w := (979 / 6099)) (n := 12)
    (lo := (161918471 / 500000000)) (hi := (323836943 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3539 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3539 / 2560) = 1/(2560 / 3539) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (161918471 / 500000000) (323836943 / 1000000000) (Real.log (3539 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3539 / 2560) = -Real.log (2560 / 3539) := by
    rw [show ((3539 / 2560) : ℝ) = ((2560 / 3539) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (4819497 / 10000000) ≤ -Real.log (1581 / 2560) ∧
    -Real.log (1581 / 2560) ≤ (481949701 / 1000000000) := by
  have h := checkLog_sound (w := (979 / 4141)) (n := 12)
    (lo := (4819497 / 10000000)) (hi := (481949701 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1581) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1581) = 1/(1581 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-481949701 / 1000000000) (-4819497 / 10000000) (Real.log (1581 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (80853251 / 250000000) ≤ -Real.log (1024 / 1415) ∧
    -Real.log (1024 / 1415) ≤ (64682601 / 200000000) := by
  have h := checkLog_sound (w := (391 / 2439)) (n := 12)
    (lo := (80853251 / 250000000)) (hi := (64682601 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1415 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1415 / 1024) = 1/(1024 / 1415) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (80853251 / 250000000) (64682601 / 200000000) (Real.log (1415 / 1024)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1415 / 1024) = -Real.log (1024 / 1415) := by
    rw [show ((1415 / 1024) : ℝ) = ((1024 / 1415) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (481001383 / 1000000000) ≤ -Real.log (633 / 1024) ∧
    -Real.log (633 / 1024) ≤ (60125173 / 125000000) := by
  have h := checkLog_sound (w := (391 / 1657)) (n := 12)
    (lo := (481001383 / 1000000000)) (hi := (60125173 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 633) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 633) = 1/(633 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-60125173 / 125000000) (-481001383 / 1000000000) (Real.log (633 / 1024)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (240390759 / 1000000000) ≤ -Real.log (500000 / 635873) ∧
    -Real.log (500000 / 635873) ≤ (6009769 / 25000000) := by
  have h := checkLog_sound (w := (135873 / 1135873)) (n := 12)
    (lo := (240390759 / 1000000000)) (hi := (6009769 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((635873 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(635873 / 500000) = 1/(500000 / 635873) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (240390759 / 1000000000) (6009769 / 25000000) (Real.log (635873 / 500000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (635873 / 500000) = -Real.log (500000 / 635873) := by
    rw [show ((635873 / 500000) : ℝ) = ((500000 / 635873) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (31710539 / 100000000) ≤ -Real.log (364127 / 500000) ∧
    -Real.log (364127 / 500000) ≤ (317105391 / 1000000000) := by
  have h := checkLog_sound (w := (135873 / 864127)) (n := 12)
    (lo := (31710539 / 100000000)) (hi := (317105391 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 364127) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 364127) = 1/(364127 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-317105391 / 1000000000) (-31710539 / 100000000) (Real.log (364127 / 500000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (240724103 / 1000000000) ≤ -Real.log (100000 / 127217) ∧
    -Real.log (100000 / 127217) ≤ (30090513 / 125000000) := by
  have h := checkLog_sound (w := (27217 / 227217)) (n := 12)
    (lo := (240724103 / 1000000000)) (hi := (30090513 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((127217 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(127217 / 100000) = 1/(100000 / 127217) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (240724103 / 1000000000) (30090513 / 125000000) (Real.log (127217 / 100000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (127217 / 100000) = -Real.log (100000 / 127217) := by
    rw [show ((127217 / 100000) : ℝ) = ((100000 / 127217) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (158843887 / 500000000) ≤ -Real.log (72783 / 100000) ∧
    -Real.log (72783 / 100000) ≤ (12707511 / 40000000) := by
  have h := checkLog_sound (w := (27217 / 172783)) (n := 12)
    (lo := (158843887 / 500000000)) (hi := (12707511 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 72783) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 72783) = 1/(72783 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-12707511 / 40000000) (-158843887 / 500000000) (Real.log (72783 / 100000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (35824121 / 200000000) ≤ -Real.log (200000 / 239233) ∧
    -Real.log (200000 / 239233) ≤ (89560303 / 500000000) := by
  have h := checkLog_sound (w := (39233 / 439233)) (n := 12)
    (lo := (35824121 / 200000000)) (hi := (89560303 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((239233 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(239233 / 200000) = 1/(200000 / 239233) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (35824121 / 200000000) (89560303 / 500000000) (Real.log (239233 / 200000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (239233 / 200000) = -Real.log (200000 / 239233) := by
    rw [show ((239233 / 200000) : ℝ) = ((200000 / 239233) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (109180627 / 500000000) ≤ -Real.log (160767 / 200000) ∧
    -Real.log (160767 / 200000) ≤ (43672251 / 200000000) := by
  have h := checkLog_sound (w := (39233 / 360767)) (n := 12)
    (lo := (109180627 / 500000000)) (hi := (43672251 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 160767) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 160767) = 1/(160767 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-43672251 / 200000000) (-109180627 / 500000000) (Real.log (160767 / 200000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (35877451 / 200000000) ≤ -Real.log (250000 / 299121) ∧
    -Real.log (250000 / 299121) ≤ (22423407 / 125000000) := by
  have h := checkLog_sound (w := (49121 / 549121)) (n := 12)
    (lo := (35877451 / 200000000)) (hi := (22423407 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((299121 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(299121 / 250000) = 1/(250000 / 299121) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (35877451 / 200000000) (22423407 / 125000000) (Real.log (299121 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (299121 / 250000) = -Real.log (250000 / 299121) := by
    rw [show ((299121 / 250000) : ℝ) = ((250000 / 299121) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (218758181 / 1000000000) ≤ -Real.log (200879 / 250000) ∧
    -Real.log (200879 / 250000) ≤ (109379091 / 500000000) := by
  have h := checkLog_sound (w := (49121 / 450879)) (n := 12)
    (lo := (218758181 / 1000000000)) (hi := (109379091 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 200879) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 200879) = 1/(200879 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-109379091 / 500000000) (-218758181 / 1000000000) (Real.log (200879 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (804414387 / 1000000000) ≤ -Real.log (250000000000 / 558846761453) ∧
    -Real.log (250000000000 / 558846761453) ≤ (804414389 / 1000000000) := by
  have h := checkLog_sound (w := (58846761453 / 1058846761453)) (n := 12)
    (lo := (111267207 / 1000000000)) (hi := (13908401 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((558846761453 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(558846761453 / 500000000000) = 1/(250000000000 / 558846761453) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (804414387 / 1000000000) (804414389 / 1000000000) (Real.log (558846761453 / 250000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (558846761453 / 250000000000) = -Real.log (250000000000 / 558846761453) := by
    rw [show ((558846761453 / 250000000000) : ℝ) = ((250000000000 / 558846761453) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (402893321 / 500000000) ≤ -Real.log (31250000000 / 69951771031) ∧
    -Real.log (31250000000 / 69951771031) ≤ (201446661 / 250000000) := by
  have h := checkLog_sound (w := (7451771031 / 132451771031)) (n := 12)
    (lo := (56319731 / 500000000)) (hi := (112639463 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((69951771031 / 62500000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(69951771031 / 62500000000) = 1/(31250000000 / 69951771031) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (402893321 / 500000000) (201446661 / 250000000) (Real.log (69951771031 / 31250000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (69951771031 / 31250000000) = -Real.log (31250000000 / 69951771031) := by
    rw [show ((69951771031 / 31250000000) : ℝ) = ((31250000000 / 69951771031) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (557496149 / 1000000000) ≤ -Real.log (500000000000 / 873147281031) ∧
    -Real.log (500000000000 / 873147281031) ≤ (11149923 / 20000000) := by
  have h := checkLog_sound (w := (373147281031 / 1373147281031)) (n := 12)
    (lo := (557496149 / 1000000000)) (hi := (11149923 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((873147281031 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(873147281031 / 500000000000) = 1/(500000000000 / 873147281031) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (557496149 / 1000000000) (11149923 / 20000000) (Real.log (873147281031 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (873147281031 / 500000000000) = -Real.log (500000000000 / 873147281031) := by
    rw [show ((873147281031 / 500000000000) : ℝ) = ((500000000000 / 873147281031) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (279205939 / 500000000) ≤ -Real.log (500000000000 / 873947212949) ∧
    -Real.log (500000000000 / 873947212949) ≤ (558411879 / 1000000000) := by
  have h := checkLog_sound (w := (373947212949 / 1373947212949)) (n := 12)
    (lo := (279205939 / 500000000)) (hi := (558411879 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((873947212949 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(873947212949 / 500000000000) = 1/(500000000000 / 873947212949) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (279205939 / 500000000) (558411879 / 1000000000) (Real.log (873947212949 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (873947212949 / 500000000000) = -Real.log (500000000000 / 873947212949) := by
    rw [show ((873947212949 / 500000000000) : ℝ) = ((500000000000 / 873947212949) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (19874093 / 50000000) ≤ -Real.log (100000000000 / 148807280101) ∧
    -Real.log (100000000000 / 148807280101) ≤ (397481861 / 1000000000) := by
  have h := checkLog_sound (w := (48807280101 / 248807280101)) (n := 12)
    (lo := (19874093 / 50000000)) (hi := (397481861 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((148807280101 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(148807280101 / 100000000000) = 1/(100000000000 / 148807280101) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (19874093 / 50000000) (397481861 / 1000000000) (Real.log (148807280101 / 100000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (148807280101 / 100000000000) = -Real.log (100000000000 / 148807280101) := by
    rw [show ((148807280101 / 100000000000) : ℝ) = ((100000000000 / 148807280101) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (398145437 / 1000000000) ≤ -Real.log (500000000000 / 744530289379) ∧
    -Real.log (500000000000 / 744530289379) ≤ (199072719 / 500000000) := by
  have h := checkLog_sound (w := (244530289379 / 1244530289379)) (n := 12)
    (lo := (398145437 / 1000000000)) (hi := (199072719 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((744530289379 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(744530289379 / 500000000000) = 1/(500000000000 / 744530289379) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (398145437 / 1000000000) (199072719 / 500000000) (Real.log (744530289379 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (744530289379 / 500000000000) = -Real.log (500000000000 / 744530289379) := by
    rw [show ((744530289379 / 500000000000) : ℝ) = ((500000000000 / 744530289379) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1574837 / 40000000) ≤ -Real.log (60087127359 / 62500000000) ∧
    -Real.log (60087127359 / 62500000000) ≤ (19685463 / 500000000) := by
  have h := checkLog_sound (w := (2412872641 / 122587127359)) (n := 12)
    (lo := (1574837 / 40000000)) (hi := (19685463 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 60087127359) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 60087127359) = 1/(60087127359 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-19685463 / 500000000) (-1574837 / 40000000) (Real.log (60087127359 / 62500000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (4905081 / 125000000) ≤ -Real.log (38460771711 / 40000000000) ∧
    -Real.log (38460771711 / 40000000000) ≤ (39240649 / 1000000000) := by
  have h := checkLog_sound (w := (1539228289 / 78460771711)) (n := 12)
    (lo := (4905081 / 125000000)) (hi := (39240649 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 38460771711) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 38460771711) = 1/(38460771711 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-39240649 / 1000000000) (-4905081 / 125000000) (Real.log (38460771711 / 40000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell225
