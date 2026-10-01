import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0106
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

theorem reflection_log_1_neg : (82086951 / 250000000) ≤ -Real.log (512 / 711) ∧
    -Real.log (512 / 711) ≤ (65669561 / 200000000) := by
  have h := checkLog_sound (w := (199 / 1223)) (n := 12)
    (lo := (82086951 / 250000000)) (hi := (65669561 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((711 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(711 / 512) = 1/(512 / 711) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (82086951 / 250000000) (65669561 / 200000000) (Real.log (711 / 512)) := by
  have h := reflection_log_1_neg
  have he : Real.log (711 / 512) = -Real.log (512 / 711) := by
    rw [show ((711 / 512) : ℝ) = ((512 / 711) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (246060717 / 500000000) ≤ -Real.log (313 / 512) ∧
    -Real.log (313 / 512) ≤ (98424287 / 200000000) := by
  have h := checkLog_sound (w := (199 / 825)) (n := 12)
    (lo := (246060717 / 500000000)) (hi := (98424287 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 313) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 313) = 1/(313 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-98424287 / 200000000) (-246060717 / 500000000) (Real.log (313 / 512)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (163751783 / 500000000) ≤ -Real.log (80 / 111) ∧
    -Real.log (80 / 111) ≤ (327503567 / 1000000000) := by
  have h := checkLog_sound (w := (31 / 191)) (n := 12)
    (lo := (163751783 / 500000000)) (hi := (327503567 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((111 / 80) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(111 / 80) = 1/(80 / 111) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (163751783 / 500000000) (327503567 / 1000000000) (Real.log (111 / 80)) := by
  have h := reflection_log_3_neg
  have he : Real.log (111 / 80) = -Real.log (80 / 111) := by
    rw [show ((111 / 80) : ℝ) = ((80 / 111) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (3829737 / 7812500) ≤ -Real.log (49 / 80) ∧
    -Real.log (49 / 80) ≤ (490206337 / 1000000000) := by
  have h := checkLog_sound (w := (31 / 129)) (n := 12)
    (lo := (3829737 / 7812500)) (hi := (490206337 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80 / 49) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(80 / 49) = 1/(49 / 80) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-490206337 / 1000000000) (-3829737 / 7812500) (Real.log (49 / 80)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (287559987 / 500000000) ≤ -Real.log (256 / 455) ∧
    -Real.log (256 / 455) ≤ (23004799 / 40000000) := by
  have h := checkLog_sound (w := (199 / 711)) (n := 12)
    (lo := (287559987 / 500000000)) (hi := (23004799 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((455 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(455 / 256) = 1/(256 / 455) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (287559987 / 500000000) (23004799 / 40000000) (Real.log (455 / 256)) := by
  have h := reflection_log_5_neg
  have he : Real.log (455 / 256) = -Real.log (256 / 455) := by
    rw [show ((455 / 256) : ℝ) = ((256 / 455) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (60085047 / 40000000) ≤ -Real.log (57 / 256) ∧
    -Real.log (57 / 256) ≤ (751063089 / 500000000) := by
  have h := checkLog_sound (w := (7 / 121)) (n := 12)
    (lo := (23166363 / 200000000)) (hi := (14478977 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((64 / 57) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(64 / 57) = 1/(57 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-751063089 / 500000000) (-60085047 / 40000000) (Real.log (57 / 256)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (286900211 / 500000000) ≤ -Real.log (40 / 71) ∧
    -Real.log (40 / 71) ≤ (573800423 / 1000000000) := by
  have h := checkLog_sound (w := (31 / 111)) (n := 12)
    (lo := (286900211 / 500000000)) (hi := (573800423 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((71 / 40) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(71 / 40) = 1/(40 / 71) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (286900211 / 500000000) (573800423 / 1000000000) (Real.log (71 / 40)) := by
  have h := reflection_log_7_neg
  have he : Real.log (71 / 40) = -Real.log (40 / 71) := by
    rw [show ((71 / 40) : ℝ) = ((40 / 71) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (11933239 / 8000000) ≤ -Real.log (9 / 40) ∧
    -Real.log (9 / 40) ≤ (745827439 / 500000000) := by
  have h := checkLog_sound (w := (1 / 19)) (n := 12)
    (lo := (21072103 / 200000000)) (hi := (26340129 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10 / 9) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(10 / 9) = 1/(9 / 40) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-745827439 / 500000000) (-11933239 / 8000000) (Real.log (9 / 40)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (224587863 / 500000000) ≤ -Real.log (50000 / 78351) ∧
    -Real.log (50000 / 78351) ≤ (449175727 / 1000000000) := by
  have h := checkLog_sound (w := (28351 / 128351)) (n := 12)
    (lo := (224587863 / 500000000)) (hi := (449175727 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((78351 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(78351 / 50000) = 1/(50000 / 78351) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (224587863 / 500000000) (449175727 / 1000000000) (Real.log (78351 / 50000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (78351 / 50000) = -Real.log (50000 / 78351) := by
    rw [show ((78351 / 50000) : ℝ) = ((50000 / 78351) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (41853187 / 50000000) ≤ -Real.log (21649 / 50000) ∧
    -Real.log (21649 / 50000) ≤ (418531871 / 500000000) := by
  have h := checkLog_sound (w := (3351 / 46649)) (n := 12)
    (lo := (1798957 / 12500000)) (hi := (143916561 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 21649) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(25000 / 21649) = 1/(21649 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-418531871 / 500000000) (-41853187 / 50000000) (Real.log (21649 / 50000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (450377923 / 1000000000) ≤ -Real.log (200000 / 313781) ∧
    -Real.log (200000 / 313781) ≤ (112594481 / 250000000) := by
  have h := checkLog_sound (w := (113781 / 513781)) (n := 12)
    (lo := (450377923 / 1000000000)) (hi := (112594481 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((313781 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(313781 / 200000) = 1/(200000 / 313781) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (450377923 / 1000000000) (112594481 / 250000000) (Real.log (313781 / 200000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (313781 / 200000) = -Real.log (200000 / 313781) := by
    rw [show ((313781 / 200000) : ℝ) = ((200000 / 313781) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (420713397 / 500000000) ≤ -Real.log (86219 / 200000) ∧
    -Real.log (86219 / 200000) ≤ (210356699 / 250000000) := by
  have h := checkLog_sound (w := (13781 / 186219)) (n := 12)
    (lo := (74139807 / 500000000)) (hi := (29655923 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 86219) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(100000 / 86219) = 1/(86219 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-210356699 / 250000000) (-420713397 / 500000000) (Real.log (86219 / 200000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (45568149 / 125000000) ≤ -Real.log (1000000 / 1439859) ∧
    -Real.log (1000000 / 1439859) ≤ (364545193 / 1000000000) := by
  have h := checkLog_sound (w := (439859 / 2439859)) (n := 12)
    (lo := (45568149 / 125000000)) (hi := (364545193 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1439859 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1439859 / 1000000) = 1/(1000000 / 1439859) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (45568149 / 125000000) (364545193 / 1000000000) (Real.log (1439859 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1439859 / 1000000) = -Real.log (1000000 / 1439859) := by
    rw [show ((1439859 / 1000000) : ℝ) = ((1000000 / 1439859) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (579566741 / 1000000000) ≤ -Real.log (560141 / 1000000) ∧
    -Real.log (560141 / 1000000) ≤ (289783371 / 500000000) := by
  have h := checkLog_sound (w := (439859 / 1560141)) (n := 12)
    (lo := (579566741 / 1000000000)) (hi := (289783371 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 560141) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 560141) = 1/(560141 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-289783371 / 500000000) (-579566741 / 1000000000) (Real.log (560141 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (73150999 / 200000000) ≤ -Real.log (500000 / 720801) ∧
    -Real.log (500000 / 720801) ≤ (91438749 / 250000000) := by
  have h := checkLog_sound (w := (220801 / 1220801)) (n := 12)
    (lo := (73150999 / 200000000)) (hi := (91438749 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((720801 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(720801 / 500000) = 1/(500000 / 720801) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (73150999 / 200000000) (91438749 / 250000000) (Real.log (720801 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (720801 / 500000) = -Real.log (500000 / 720801) := by
    rw [show ((720801 / 500000) : ℝ) = ((500000 / 720801) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (582683309 / 1000000000) ≤ -Real.log (279199 / 500000) ∧
    -Real.log (279199 / 500000) ≤ (58268331 / 100000000) := by
  have h := checkLog_sound (w := (220801 / 779199)) (n := 12)
    (lo := (582683309 / 1000000000)) (hi := (58268331 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 279199) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 279199) = 1/(279199 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-58268331 / 100000000) (-582683309 / 1000000000) (Real.log (279199 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1286239467 / 1000000000) ≤ -Real.log (500000000000 / 1809575500023) ∧
    -Real.log (500000000000 / 1809575500023) ≤ (1286239469 / 1000000000) := by
  have h := checkLog_sound (w := (809575500023 / 2809575500023)) (n := 12)
    (lo := (593092287 / 1000000000)) (hi := (9267067 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1809575500023 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1809575500023 / 1000000000000) = 1/(500000000000 / 1809575500023) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1286239467 / 1000000000) (1286239469 / 1000000000) (Real.log (1809575500023 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1809575500023 / 500000000000) = -Real.log (500000000000 / 1809575500023) := by
    rw [show ((1809575500023 / 500000000000) : ℝ) = ((500000000000 / 1809575500023) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (645902359 / 500000000) ≤ -Real.log (250000000000 / 909837158863) ∧
    -Real.log (250000000000 / 909837158863) ≤ (16147559 / 12500000) := by
  have h := checkLog_sound (w := (409837158863 / 1409837158863)) (n := 12)
    (lo := (299328769 / 500000000)) (hi := (598657539 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((909837158863 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(909837158863 / 500000000000) = 1/(250000000000 / 909837158863) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (645902359 / 500000000) (16147559 / 12500000) (Real.log (909837158863 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (909837158863 / 250000000000) = -Real.log (250000000000 / 909837158863) := by
    rw [show ((909837158863 / 250000000000) : ℝ) = ((250000000000 / 909837158863) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (236027983 / 250000000) ≤ -Real.log (250000000000 / 642632390773) ∧
    -Real.log (250000000000 / 642632390773) ≤ (472055967 / 500000000) := by
  have h := checkLog_sound (w := (142632390773 / 1142632390773)) (n := 12)
    (lo := (15685297 / 62500000)) (hi := (250964753 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((642632390773 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(642632390773 / 500000000000) = 1/(250000000000 / 642632390773) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (236027983 / 250000000) (472055967 / 500000000) (Real.log (642632390773 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (642632390773 / 250000000000) = -Real.log (250000000000 / 642632390773) := by
    rw [show ((642632390773 / 250000000000) : ℝ) = ((250000000000 / 642632390773) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (948438303 / 1000000000) ≤ -Real.log (500000000000 / 1290837359733) ∧
    -Real.log (500000000000 / 1290837359733) ≤ (189687661 / 200000000) := by
  have h := checkLog_sound (w := (290837359733 / 2290837359733)) (n := 12)
    (lo := (255291123 / 1000000000)) (hi := (63822781 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1290837359733 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1290837359733 / 1000000000000) = 1/(500000000000 / 1290837359733) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (948438303 / 1000000000) (189687661 / 200000000) (Real.log (1290837359733 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1290837359733 / 500000000000) = -Real.log (500000000000 / 1290837359733) := by
    rw [show ((1290837359733 / 500000000000) : ℝ) = ((500000000000 / 1290837359733) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0106
