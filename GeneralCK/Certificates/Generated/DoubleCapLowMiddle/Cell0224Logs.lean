import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0224
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

theorem reflection_log_1_neg : (499258987 / 1000000000) ≤ -Real.log (400 / 659) ∧
    -Real.log (400 / 659) ≤ (124814747 / 250000000) := by
  have h := checkLog_sound (w := (259 / 1059)) (n := 12)
    (lo := (499258987 / 1000000000)) (hi := (124814747 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((659 / 400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(659 / 400) = 1/(400 / 659) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (499258987 / 1000000000) (124814747 / 250000000) (Real.log (659 / 400)) := by
  have h := reflection_log_1_neg
  have he : Real.log (659 / 400) = -Real.log (400 / 659) := by
    rw [show ((659 / 400) : ℝ) = ((400 / 659) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (65169041 / 62500000) ≤ -Real.log (141 / 400) ∧
    -Real.log (141 / 400) ≤ (521352329 / 500000000) := by
  have h := checkLog_sound (w := (59 / 341)) (n := 12)
    (lo := (87389369 / 250000000)) (hi := (349557477 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200 / 141) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(200 / 141) = 1/(141 / 400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-521352329 / 500000000) (-65169041 / 62500000) (Real.log (141 / 400)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (246012497 / 500000000) ≤ -Real.log (1600 / 2617) ∧
    -Real.log (1600 / 2617) ≤ (98404999 / 200000000) := by
  have h := checkLog_sound (w := (1017 / 4217)) (n := 12)
    (lo := (246012497 / 500000000)) (hi := (98404999 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2617 / 1600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2617 / 1600) = 1/(1600 / 2617) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (246012497 / 500000000) (98404999 / 200000000) (Real.log (2617 / 1600)) := by
  have h := reflection_log_3_neg
  have he : Real.log (2617 / 1600) = -Real.log (1600 / 2617) := by
    rw [show ((2617 / 1600) : ℝ) = ((1600 / 2617) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (1009571721 / 1000000000) ≤ -Real.log (583 / 1600) ∧
    -Real.log (583 / 1600) ≤ (1009571723 / 1000000000) := by
  have h := checkLog_sound (w := (217 / 1383)) (n := 12)
    (lo := (316424541 / 1000000000)) (hi := (158212271 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 583) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(800 / 583) = 1/(583 / 1600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-1009571723 / 1000000000) (-1009571721 / 1000000000) (Real.log (583 / 1600)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (51702139 / 200000000) ≤ -Real.log (200 / 259) ∧
    -Real.log (200 / 259) ≤ (32313837 / 125000000) := by
  have h := checkLog_sound (w := (59 / 459)) (n := 12)
    (lo := (51702139 / 200000000)) (hi := (32313837 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((259 / 200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(259 / 200) = 1/(200 / 259) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (51702139 / 200000000) (32313837 / 125000000) (Real.log (259 / 200)) := by
  have h := reflection_log_5_neg
  have he : Real.log (259 / 200) = -Real.log (200 / 259) := by
    rw [show ((259 / 200) : ℝ) = ((200 / 259) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (87389369 / 250000000) ≤ -Real.log (141 / 200) ∧
    -Real.log (141 / 200) ≤ (349557477 / 1000000000) := by
  have h := checkLog_sound (w := (59 / 341)) (n := 12)
    (lo := (87389369 / 250000000)) (hi := (349557477 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200 / 141) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200 / 141) = 1/(141 / 200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-349557477 / 1000000000) (-87389369 / 250000000) (Real.log (141 / 200)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (60000167 / 250000000) ≤ -Real.log (800 / 1017) ∧
    -Real.log (800 / 1017) ≤ (240000669 / 1000000000) := by
  have h := checkLog_sound (w := (217 / 1817)) (n := 12)
    (lo := (60000167 / 250000000)) (hi := (240000669 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1017 / 800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1017 / 800) = 1/(800 / 1017) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (60000167 / 250000000) (240000669 / 1000000000) (Real.log (1017 / 800)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1017 / 800) = -Real.log (800 / 1017) := by
    rw [show ((1017 / 800) : ℝ) = ((800 / 1017) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (316424541 / 1000000000) ≤ -Real.log (583 / 800) ∧
    -Real.log (583 / 800) ≤ (158212271 / 500000000) := by
  have h := checkLog_sound (w := (217 / 1383)) (n := 12)
    (lo := (316424541 / 1000000000)) (hi := (158212271 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 583) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(800 / 583) = 1/(583 / 800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-158212271 / 500000000) (-316424541 / 1000000000) (Real.log (583 / 800)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (293166137 / 500000000) ≤ -Real.log (125000 / 224673) ∧
    -Real.log (125000 / 224673) ≤ (23453291 / 40000000) := by
  have h := checkLog_sound (w := (99673 / 349673)) (n := 12)
    (lo := (293166137 / 500000000)) (hi := (23453291 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((224673 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(224673 / 125000) = 1/(125000 / 224673) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (293166137 / 500000000) (23453291 / 40000000) (Real.log (224673 / 125000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (224673 / 125000) = -Real.log (125000 / 224673) := by
    rw [show ((224673 / 125000) : ℝ) = ((125000 / 224673) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (319288543 / 200000000) ≤ -Real.log (25327 / 125000) ∧
    -Real.log (25327 / 125000) ≤ (798221359 / 500000000) := by
  have h := checkLog_sound (w := (5923 / 56577)) (n := 12)
    (lo := (42029671 / 200000000)) (hi := (52537089 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 25327) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(31250 / 25327) = 1/(25327 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-798221359 / 500000000) (-319288543 / 200000000) (Real.log (25327 / 125000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (588086619 / 1000000000) ≤ -Real.log (50000 / 90027) ∧
    -Real.log (50000 / 90027) ≤ (29404331 / 50000000) := by
  have h := checkLog_sound (w := (40027 / 140027)) (n := 12)
    (lo := (588086619 / 1000000000)) (hi := (29404331 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((90027 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(90027 / 50000) = 1/(50000 / 90027) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (588086619 / 1000000000) (29404331 / 50000000) (Real.log (90027 / 50000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (90027 / 50000) = -Real.log (50000 / 90027) := by
    rw [show ((90027 / 50000) : ℝ) = ((50000 / 90027) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (806070781 / 500000000) ≤ -Real.log (9973 / 50000) ∧
    -Real.log (9973 / 50000) ≤ (322428313 / 200000000) := by
  have h := checkLog_sound (w := (2527 / 22473)) (n := 12)
    (lo := (112923601 / 500000000)) (hi := (225847203 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12500 / 9973) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(12500 / 9973) = 1/(9973 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-322428313 / 200000000) (-806070781 / 500000000) (Real.log (9973 / 50000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (1085307 / 1953125) ≤ -Real.log (1000000 / 1743121) ∧
    -Real.log (1000000 / 1743121) ≤ (111135437 / 200000000) := by
  have h := checkLog_sound (w := (743121 / 2743121)) (n := 12)
    (lo := (1085307 / 1953125)) (hi := (111135437 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1743121 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1743121 / 1000000) = 1/(1000000 / 1743121) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (1085307 / 1953125) (111135437 / 200000000) (Real.log (1743121 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1743121 / 1000000) = -Real.log (1000000 / 1743121) := by
    rw [show ((1743121 / 1000000) : ℝ) = ((1000000 / 1743121) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (1359150121 / 1000000000) ≤ -Real.log (256879 / 1000000) ∧
    -Real.log (256879 / 1000000) ≤ (1359150123 / 1000000000) := by
  have h := checkLog_sound (w := (243121 / 756879)) (n := 12)
    (lo := (666002941 / 1000000000)) (hi := (333001471 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 256879) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 256879) = 1/(256879 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-1359150123 / 1000000000) (-1359150121 / 1000000000) (Real.log (256879 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (559969439 / 1000000000) ≤ -Real.log (1000000 / 1750619) ∧
    -Real.log (1000000 / 1750619) ≤ (3499809 / 6250000) := by
  have h := checkLog_sound (w := (750619 / 2750619)) (n := 12)
    (lo := (559969439 / 1000000000)) (hi := (3499809 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1750619 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1750619 / 1000000) = 1/(1000000 / 1750619) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (559969439 / 1000000000) (3499809 / 6250000) (Real.log (1750619 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1750619 / 1000000) = -Real.log (1000000 / 1750619) := by
    rw [show ((1750619 / 1000000) : ℝ) = ((1000000 / 1750619) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (138877343 / 100000000) ≤ -Real.log (249381 / 1000000) ∧
    -Real.log (249381 / 1000000) ≤ (1388773433 / 1000000000) := by
  have h := checkLog_sound (w := (619 / 499381)) (n := 12)
    (lo := (247907 / 100000000)) (hi := (2479071 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 249381) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(250000 / 249381) = 1/(249381 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-1388773433 / 1000000000) (-138877343 / 100000000) (Real.log (249381 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (2182774989 / 1000000000) ≤ -Real.log (125000000000 / 1108861096853) ∧
    -Real.log (125000000000 / 1108861096853) ≤ (2182774993 / 1000000000) := by
  have h := checkLog_sound (w := (108861096853 / 2108861096853)) (n := 12)
    (lo := (103333449 / 1000000000)) (hi := (2066669 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1108861096853 / 1000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1108861096853 / 1000000000000) = 1/(125000000000 / 1108861096853) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (2182774989 / 1000000000) (2182774993 / 1000000000) (Real.log (1108861096853 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1108861096853 / 125000000000) = -Real.log (125000000000 / 1108861096853) := by
    rw [show ((1108861096853 / 125000000000) : ℝ) = ((125000000000 / 1108861096853) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1100114091 / 500000000) ≤ -Real.log (250000000000 / 2256768274341) ∧
    -Real.log (250000000000 / 2256768274341) ≤ (1100114093 / 500000000) := by
  have h := checkLog_sound (w := (256768274341 / 4256768274341)) (n := 12)
    (lo := (60393321 / 500000000)) (hi := (120786643 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2256768274341 / 2000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(2256768274341 / 2000000000000) = 1/(250000000000 / 2256768274341) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1100114091 / 500000000) (1100114093 / 500000000) (Real.log (2256768274341 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (2256768274341 / 250000000000) = -Real.log (250000000000 / 2256768274341) := by
    rw [show ((2256768274341 / 250000000000) : ℝ) = ((250000000000 / 2256768274341) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (382965461 / 200000000) ≤ -Real.log (25000000000 / 169644170991) ∧
    -Real.log (25000000000 / 169644170991) ≤ (478706827 / 250000000) := by
  have h := checkLog_sound (w := (69644170991 / 269644170991)) (n := 12)
    (lo := (105706589 / 200000000)) (hi := (264266473 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((169644170991 / 100000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(169644170991 / 100000000000) = 1/(25000000000 / 169644170991) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (382965461 / 200000000) (478706827 / 250000000) (Real.log (169644170991 / 25000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (169644170991 / 25000000000) = -Real.log (25000000000 / 169644170991) := by
    rw [show ((169644170991 / 25000000000) : ℝ) = ((25000000000 / 169644170991) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (194874287 / 100000000) ≤ -Real.log (125000000000 / 877482145793) ∧
    -Real.log (125000000000 / 877482145793) ≤ (1948742873 / 1000000000) := by
  have h := checkLog_sound (w := (377482145793 / 1377482145793)) (n := 12)
    (lo := (56244851 / 100000000)) (hi := (562448511 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((877482145793 / 500000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(877482145793 / 500000000000) = 1/(125000000000 / 877482145793) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (194874287 / 100000000) (1948742873 / 1000000000) (Real.log (877482145793 / 125000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (877482145793 / 125000000000) = -Real.log (125000000000 / 877482145793) := by
    rw [show ((877482145793 / 125000000000) : ℝ) = ((125000000000 / 877482145793) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0224
