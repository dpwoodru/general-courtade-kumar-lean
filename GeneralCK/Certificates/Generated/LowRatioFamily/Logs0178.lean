import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_11392_neg : (222027513 / 250000000) ≤ -Real.log (50000000000 / 121526586621) ∧
    -Real.log (50000000000 / 121526586621) ≤ (444055027 / 500000000) := by
  have h := checkLog_sound (w := (21526586621 / 221526586621)) (n := 12)
    (lo := (24370359 / 125000000)) (hi := (194962873 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((121526586621 / 100000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(121526586621 / 100000000000) = 1/(50000000000 / 121526586621) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11392 : Bounds (222027513 / 250000000) (444055027 / 500000000) (Real.log (121526586621 / 50000000000)) := by
  have h := reflection_log_11392_neg
  have he : Real.log (121526586621 / 50000000000) = -Real.log (50000000000 / 121526586621) := by
    rw [show ((121526586621 / 50000000000) : ℝ) = ((50000000000 / 121526586621) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11393_neg : (87311857 / 250000000) ≤ -Real.log (500 / 709) ∧
    -Real.log (500 / 709) ≤ (349247429 / 1000000000) := by
  have h := checkLog_sound (w := (209 / 1209)) (n := 12)
    (lo := (87311857 / 250000000)) (hi := (349247429 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((709 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(709 / 500) = 1/(500 / 709) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11393 : Bounds (87311857 / 250000000) (349247429 / 1000000000) (Real.log (709 / 500)) := by
  have h := reflection_log_11393_neg
  have he : Real.log (709 / 500) = -Real.log (500 / 709) := by
    rw [show ((709 / 500) : ℝ) = ((500 / 709) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11394_neg : (541284831 / 1000000000) ≤ -Real.log (291 / 500) ∧
    -Real.log (291 / 500) ≤ (16915151 / 31250000) := by
  have h := checkLog_sound (w := (209 / 791)) (n := 12)
    (lo := (541284831 / 1000000000)) (hi := (16915151 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 291) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500 / 291) = 1/(291 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11394 : Bounds (-16915151 / 31250000) (-541284831 / 1000000000) (Real.log (291 / 500)) := by
  have h := reflection_log_11394_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11395_neg : (52239 / 125000000) ≤ -Real.log (500000 / 500209) ∧
    -Real.log (500000 / 500209) ≤ (417913 / 1000000000) := by
  have h := checkLog_sound (w := (209 / 1000209)) (n := 12)
    (lo := (52239 / 125000000)) (hi := (417913 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500209 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500209 / 500000) = 1/(500000 / 500209) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11395 : Bounds (52239 / 125000000) (417913 / 1000000000) (Real.log (500209 / 500000)) := by
  have h := reflection_log_11395_neg
  have he : Real.log (500209 / 500000) = -Real.log (500000 / 500209) := by
    rw [show ((500209 / 500000) : ℝ) = ((500000 / 500209) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11396_neg : (418087 / 1000000000) ≤ -Real.log (499791 / 500000) ∧
    -Real.log (499791 / 500000) ≤ (52261 / 125000000) := by
  have h := checkLog_sound (w := (209 / 999791)) (n := 12)
    (lo := (418087 / 1000000000)) (hi := (52261 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499791) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499791) = 1/(499791 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11396 : Bounds (-52261 / 125000000) (-418087 / 1000000000) (Real.log (499791 / 500000)) := by
  have h := reflection_log_11396_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11397_neg : (9745269 / 50000000) ≤ -Real.log (250000 / 303799) ∧
    -Real.log (250000 / 303799) ≤ (194905381 / 1000000000) := by
  have h := checkLog_sound (w := (53799 / 553799)) (n := 12)
    (lo := (9745269 / 50000000)) (hi := (194905381 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((303799 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(303799 / 250000) = 1/(250000 / 303799) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11397 : Bounds (9745269 / 50000000) (194905381 / 1000000000) (Real.log (303799 / 250000)) := by
  have h := reflection_log_11397_neg
  have he : Real.log (303799 / 250000) = -Real.log (250000 / 303799) := by
    rw [show ((303799 / 250000) : ℝ) = ((250000 / 303799) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11398_neg : (242321273 / 1000000000) ≤ -Real.log (196201 / 250000) ∧
    -Real.log (196201 / 250000) ≤ (121160637 / 500000000) := by
  have h := checkLog_sound (w := (53799 / 446201)) (n := 12)
    (lo := (242321273 / 1000000000)) (hi := (121160637 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 196201) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 196201) = 1/(196201 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11398 : Bounds (-121160637 / 500000000) (-242321273 / 1000000000) (Real.log (196201 / 250000)) := by
  have h := reflection_log_11398_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11399_neg : (7827671 / 40000000) ≤ -Real.log (125000 / 152019) ∧
    -Real.log (125000 / 152019) ≤ (764421 / 3906250) := by
  have h := checkLog_sound (w := (27019 / 277019)) (n := 12)
    (lo := (7827671 / 40000000)) (hi := (764421 / 3906250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((152019 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(152019 / 125000) = 1/(125000 / 152019) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11399 : Bounds (7827671 / 40000000) (764421 / 3906250) (Real.log (152019 / 125000)) := by
  have h := reflection_log_11399_neg
  have he : Real.log (152019 / 125000) = -Real.log (125000 / 152019) := by
    rw [show ((152019 / 125000) : ℝ) = ((125000 / 152019) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11400_neg : (121770077 / 500000000) ≤ -Real.log (97981 / 125000) ∧
    -Real.log (97981 / 125000) ≤ (48708031 / 200000000) := by
  have h := checkLog_sound (w := (27019 / 222981)) (n := 12)
    (lo := (121770077 / 500000000)) (hi := (48708031 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 97981) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 97981) = 1/(97981 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11400 : Bounds (-48708031 / 200000000) (-121770077 / 500000000) (Real.log (97981 / 125000)) := by
  have h := reflection_log_11400_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11401_neg : (47848379 / 1000000000) ≤ -Real.log (14894973639 / 15625000000) ∧
    -Real.log (14894973639 / 15625000000) ≤ (2392419 / 50000000) := by
  have h := checkLog_sound (w := (730026361 / 30519973639)) (n := 12)
    (lo := (47848379 / 1000000000)) (hi := (2392419 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 14894973639) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 14894973639) = 1/(14894973639 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11401 : Bounds (-2392419 / 50000000) (-47848379 / 1000000000) (Real.log (14894973639 / 15625000000)) := by
  have h := reflection_log_11401_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11402_neg : (47415893 / 1000000000) ≤ -Real.log (59605667599 / 62500000000) ∧
    -Real.log (59605667599 / 62500000000) ≤ (23707947 / 500000000) := by
  have h := checkLog_sound (w := (2894332401 / 122105667599)) (n := 12)
    (lo := (47415893 / 1000000000)) (hi := (23707947 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 59605667599) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 59605667599) = 1/(59605667599 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11402 : Bounds (-23707947 / 500000000) (-47415893 / 1000000000) (Real.log (59605667599 / 62500000000)) := by
  have h := reflection_log_11402_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11403_neg : (218613327 / 500000000) ≤ -Real.log (100000000000 / 154840699079) ∧
    -Real.log (100000000000 / 154840699079) ≤ (87445331 / 200000000) := by
  have h := checkLog_sound (w := (54840699079 / 254840699079)) (n := 12)
    (lo := (218613327 / 500000000)) (hi := (87445331 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((154840699079 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(154840699079 / 100000000000) = 1/(100000000000 / 154840699079) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11403 : Bounds (218613327 / 500000000) (87445331 / 200000000) (Real.log (154840699079 / 100000000000)) := by
  have h := reflection_log_11403_neg
  have he : Real.log (154840699079 / 100000000000) = -Real.log (100000000000 / 154840699079) := by
    rw [show ((154840699079 / 100000000000) : ℝ) = ((100000000000 / 154840699079) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11404_neg : (43923193 / 100000000) ≤ -Real.log (500000000000 / 775757544831) ∧
    -Real.log (500000000000 / 775757544831) ≤ (439231931 / 1000000000) := by
  have h := checkLog_sound (w := (275757544831 / 1275757544831)) (n := 12)
    (lo := (43923193 / 100000000)) (hi := (439231931 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((775757544831 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(775757544831 / 500000000000) = 1/(500000000000 / 775757544831) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11404 : Bounds (43923193 / 100000000) (439231931 / 1000000000) (Real.log (775757544831 / 500000000000)) := by
  have h := reflection_log_11404_neg
  have he : Real.log (775757544831 / 500000000000) = -Real.log (500000000000 / 775757544831) := by
    rw [show ((775757544831 / 500000000000) : ℝ) = ((500000000000 / 775757544831) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11405_neg : (222027513 / 250000000) ≤ -Real.log (500000000000 / 1215265866209) ∧
    -Real.log (500000000000 / 1215265866209) ≤ (444055027 / 500000000) := by
  have h := checkLog_sound (w := (215265866209 / 2215265866209)) (n := 12)
    (lo := (24370359 / 125000000)) (hi := (194962873 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1215265866209 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1215265866209 / 1000000000000) = 1/(500000000000 / 1215265866209) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11405 : Bounds (222027513 / 250000000) (444055027 / 500000000) (Real.log (1215265866209 / 500000000000)) := by
  have h := reflection_log_11405_neg
  have he : Real.log (1215265866209 / 500000000000) = -Real.log (500000000000 / 1215265866209) := by
    rw [show ((1215265866209 / 500000000000) : ℝ) = ((500000000000 / 1215265866209) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11406_neg : (445266129 / 500000000) ≤ -Real.log (25000000000 / 60910652921) ∧
    -Real.log (25000000000 / 60910652921) ≤ (44526613 / 50000000) := by
  have h := checkLog_sound (w := (10910652921 / 110910652921)) (n := 12)
    (lo := (98692539 / 500000000)) (hi := (197385079 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((60910652921 / 50000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(60910652921 / 50000000000) = 1/(25000000000 / 60910652921) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11406 : Bounds (445266129 / 500000000) (44526613 / 50000000) (Real.log (60910652921 / 25000000000)) := by
  have h := reflection_log_11406_neg
  have he : Real.log (60910652921 / 25000000000) = -Real.log (25000000000 / 60910652921) := by
    rw [show ((60910652921 / 25000000000) : ℝ) = ((25000000000 / 60910652921) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11407_neg : (174976199 / 500000000) ≤ -Real.log (1000 / 1419) ∧
    -Real.log (1000 / 1419) ≤ (349952399 / 1000000000) := by
  have h := checkLog_sound (w := (419 / 2419)) (n := 12)
    (lo := (174976199 / 500000000)) (hi := (349952399 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1419 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1419 / 1000) = 1/(1000 / 1419) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11407 : Bounds (174976199 / 500000000) (349952399 / 1000000000) (Real.log (1419 / 1000)) := by
  have h := reflection_log_11407_neg
  have he : Real.log (1419 / 1000) = -Real.log (1000 / 1419) := by
    rw [show ((1419 / 1000) : ℝ) = ((1000 / 1419) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11408_neg : (271502261 / 500000000) ≤ -Real.log (581 / 1000) ∧
    -Real.log (581 / 1000) ≤ (543004523 / 1000000000) := by
  have h := checkLog_sound (w := (419 / 1581)) (n := 12)
    (lo := (271502261 / 500000000)) (hi := (543004523 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 581) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 581) = 1/(581 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11408 : Bounds (-543004523 / 1000000000) (-271502261 / 500000000) (Real.log (581 / 1000)) := by
  have h := reflection_log_11408_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11409_neg : (13091 / 31250000) ≤ -Real.log (1000000 / 1000419) ∧
    -Real.log (1000000 / 1000419) ≤ (418913 / 1000000000) := by
  have h := checkLog_sound (w := (419 / 2000419)) (n := 12)
    (lo := (13091 / 31250000)) (hi := (418913 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000419 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000419 / 1000000) = 1/(1000000 / 1000419) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11409 : Bounds (13091 / 31250000) (418913 / 1000000000) (Real.log (1000419 / 1000000)) := by
  have h := reflection_log_11409_neg
  have he : Real.log (1000419 / 1000000) = -Real.log (1000000 / 1000419) := by
    rw [show ((1000419 / 1000000) : ℝ) = ((1000000 / 1000419) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11410_neg : (419087 / 1000000000) ≤ -Real.log (999581 / 1000000) ∧
    -Real.log (999581 / 1000000) ≤ (26193 / 62500000) := by
  have h := checkLog_sound (w := (419 / 1999581)) (n := 12)
    (lo := (419087 / 1000000000)) (hi := (26193 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999581) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999581) = 1/(999581 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11410 : Bounds (-26193 / 62500000) (-419087 / 1000000000) (Real.log (999581 / 1000000)) := by
  have h := reflection_log_11410_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11411_neg : (97679351 / 500000000) ≤ -Real.log (1000000 / 1215747) ∧
    -Real.log (1000000 / 1215747) ≤ (195358703 / 1000000000) := by
  have h := checkLog_sound (w := (215747 / 2215747)) (n := 12)
    (lo := (97679351 / 500000000)) (hi := (195358703 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1215747 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1215747 / 1000000) = 1/(1000000 / 1215747) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11411 : Bounds (97679351 / 500000000) (195358703 / 1000000000) (Real.log (1215747 / 1000000)) := by
  have h := reflection_log_11411_neg
  have he : Real.log (1215747 / 1000000) = -Real.log (1000000 / 1215747) := by
    rw [show ((1215747 / 1000000) : ℝ) = ((1000000 / 1215747) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11412_neg : (121511803 / 500000000) ≤ -Real.log (784253 / 1000000) ∧
    -Real.log (784253 / 1000000) ≤ (243023607 / 1000000000) := by
  have h := checkLog_sound (w := (215747 / 1784253)) (n := 12)
    (lo := (121511803 / 500000000)) (hi := (243023607 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 784253) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 784253) = 1/(784253 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11412 : Bounds (-243023607 / 1000000000) (-121511803 / 500000000) (Real.log (784253 / 1000000)) := by
  have h := reflection_log_11412_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11413_neg : (196145563 / 1000000000) ≤ -Real.log (15625 / 19011) ∧
    -Real.log (15625 / 19011) ≤ (49036391 / 250000000) := by
  have h := checkLog_sound (w := (1693 / 17318)) (n := 12)
    (lo := (196145563 / 1000000000)) (hi := (49036391 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((19011 / 15625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(19011 / 15625) = 1/(15625 / 19011) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11413 : Bounds (196145563 / 1000000000) (49036391 / 250000000) (Real.log (19011 / 15625)) := by
  have h := reflection_log_11413_neg
  have he : Real.log (19011 / 15625) = -Real.log (15625 / 19011) := by
    rw [show ((19011 / 15625) : ℝ) = ((15625 / 19011) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11414_neg : (244244621 / 1000000000) ≤ -Real.log (12239 / 15625) ∧
    -Real.log (12239 / 15625) ≤ (122122311 / 500000000) := by
  have h := checkLog_sound (w := (1693 / 13932)) (n := 12)
    (lo := (244244621 / 1000000000)) (hi := (122122311 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 12239) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625 / 12239) = 1/(12239 / 15625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11414 : Bounds (-122122311 / 500000000) (-244244621 / 1000000000) (Real.log (12239 / 15625)) := by
  have h := reflection_log_11414_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11415_neg : (48099057 / 1000000000) ≤ -Real.log (232675629 / 244140625) ∧
    -Real.log (232675629 / 244140625) ≤ (24049529 / 500000000) := by
  have h := checkLog_sound (w := (5732498 / 238408127)) (n := 12)
    (lo := (48099057 / 1000000000)) (hi := (24049529 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((244140625 / 232675629) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(244140625 / 232675629) = 1/(232675629 / 244140625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11415 : Bounds (-24049529 / 500000000) (-48099057 / 1000000000) (Real.log (232675629 / 244140625)) := by
  have h := reflection_log_11415_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11416_neg : (47664903 / 1000000000) ≤ -Real.log (953453231991 / 1000000000000) ∧
    -Real.log (953453231991 / 1000000000000) ≤ (5958113 / 125000000) := by
  have h := checkLog_sound (w := (46546768009 / 1953453231991)) (n := 12)
    (lo := (47664903 / 1000000000)) (hi := (5958113 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 953453231991) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 953453231991) = 1/(953453231991 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11416 : Bounds (-5958113 / 125000000) (-47664903 / 1000000000) (Real.log (953453231991 / 1000000000000)) := by
  have h := reflection_log_11416_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11417_neg : (438382309 / 1000000000) ≤ -Real.log (250000000000 / 387549362259) ∧
    -Real.log (250000000000 / 387549362259) ≤ (43838231 / 100000000) := by
  have h := checkLog_sound (w := (137549362259 / 637549362259)) (n := 12)
    (lo := (438382309 / 1000000000)) (hi := (43838231 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((387549362259 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(387549362259 / 250000000000) = 1/(250000000000 / 387549362259) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11417 : Bounds (438382309 / 1000000000) (43838231 / 100000000) (Real.log (387549362259 / 250000000000)) := by
  have h := reflection_log_11417_neg
  have he : Real.log (387549362259 / 250000000000) = -Real.log (250000000000 / 387549362259) := by
    rw [show ((387549362259 / 250000000000) : ℝ) = ((250000000000 / 387549362259) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11418_neg : (55048773 / 125000000) ≤ -Real.log (500000000000 / 776656589591) ∧
    -Real.log (500000000000 / 776656589591) ≤ (88078037 / 200000000) := by
  have h := checkLog_sound (w := (276656589591 / 1276656589591)) (n := 12)
    (lo := (55048773 / 125000000)) (hi := (88078037 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((776656589591 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(776656589591 / 500000000000) = 1/(500000000000 / 776656589591) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11418 : Bounds (55048773 / 125000000) (88078037 / 200000000) (Real.log (776656589591 / 500000000000)) := by
  have h := reflection_log_11418_neg
  have he : Real.log (776656589591 / 500000000000) = -Real.log (500000000000 / 776656589591) := by
    rw [show ((776656589591 / 500000000000) : ℝ) = ((500000000000 / 776656589591) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11419_neg : (445266129 / 500000000) ≤ -Real.log (500000000000 / 1218213058419) ∧
    -Real.log (500000000000 / 1218213058419) ≤ (44526613 / 50000000) := by
  have h := checkLog_sound (w := (218213058419 / 2218213058419)) (n := 12)
    (lo := (98692539 / 500000000)) (hi := (197385079 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1218213058419 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1218213058419 / 1000000000000) = 1/(500000000000 / 1218213058419) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11419 : Bounds (445266129 / 500000000) (44526613 / 50000000) (Real.log (1218213058419 / 500000000000)) := by
  have h := reflection_log_11419_neg
  have he : Real.log (1218213058419 / 500000000000) = -Real.log (500000000000 / 1218213058419) := by
    rw [show ((1218213058419 / 500000000000) : ℝ) = ((500000000000 / 1218213058419) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11420_neg : (892956919 / 1000000000) ≤ -Real.log (50000000000 / 122117039587) ∧
    -Real.log (50000000000 / 122117039587) ≤ (892956921 / 1000000000) := by
  have h := checkLog_sound (w := (22117039587 / 222117039587)) (n := 12)
    (lo := (199809739 / 1000000000)) (hi := (9990487 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((122117039587 / 100000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(122117039587 / 100000000000) = 1/(50000000000 / 122117039587) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11420 : Bounds (892956919 / 1000000000) (892956921 / 1000000000) (Real.log (122117039587 / 50000000000)) := by
  have h := reflection_log_11420_neg
  have he : Real.log (122117039587 / 50000000000) = -Real.log (50000000000 / 122117039587) := by
    rw [show ((122117039587 / 50000000000) : ℝ) = ((50000000000 / 122117039587) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11421_neg : (350656871 / 1000000000) ≤ -Real.log (50 / 71) ∧
    -Real.log (50 / 71) ≤ (43832109 / 125000000) := by
  have h := checkLog_sound (w := (21 / 121)) (n := 12)
    (lo := (350656871 / 1000000000)) (hi := (43832109 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((71 / 50) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(71 / 50) = 1/(50 / 71) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11421 : Bounds (350656871 / 1000000000) (43832109 / 125000000) (Real.log (71 / 50)) := by
  have h := reflection_log_11421_neg
  have he : Real.log (71 / 50) = -Real.log (50 / 71) := by
    rw [show ((71 / 50) : ℝ) = ((50 / 71) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11422_neg : (21789087 / 40000000) ≤ -Real.log (29 / 50) ∧
    -Real.log (29 / 50) ≤ (68090897 / 125000000) := by
  have h := checkLog_sound (w := (21 / 79)) (n := 12)
    (lo := (21789087 / 40000000)) (hi := (68090897 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50 / 29) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50 / 29) = 1/(29 / 50) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11422 : Bounds (-68090897 / 125000000) (-21789087 / 40000000) (Real.log (29 / 50)) := by
  have h := reflection_log_11422_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11423_neg : (419911 / 1000000000) ≤ -Real.log (50000 / 50021) ∧
    -Real.log (50000 / 50021) ≤ (52489 / 125000000) := by
  have h := checkLog_sound (w := (21 / 100021)) (n := 12)
    (lo := (419911 / 1000000000)) (hi := (52489 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50021 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50021 / 50000) = 1/(50000 / 50021) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11423 : Bounds (419911 / 1000000000) (52489 / 125000000) (Real.log (50021 / 50000)) := by
  have h := reflection_log_11423_neg
  have he : Real.log (50021 / 50000) = -Real.log (50000 / 50021) := by
    rw [show ((50021 / 50000) : ℝ) = ((50000 / 50021) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11424_neg : (52511 / 125000000) ≤ -Real.log (49979 / 50000) ∧
    -Real.log (49979 / 50000) ≤ (420089 / 1000000000) := by
  have h := checkLog_sound (w := (21 / 99979)) (n := 12)
    (lo := (52511 / 125000000)) (hi := (420089 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 49979) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 49979) = 1/(49979 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11424 : Bounds (-420089 / 1000000000) (-52511 / 125000000) (Real.log (49979 / 50000)) := by
  have h := reflection_log_11424_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11425_neg : (195812641 / 1000000000) ≤ -Real.log (1000000 / 1216299) ∧
    -Real.log (1000000 / 1216299) ≤ (97906321 / 500000000) := by
  have h := checkLog_sound (w := (216299 / 2216299)) (n := 12)
    (lo := (195812641 / 1000000000)) (hi := (97906321 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1216299 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1216299 / 1000000) = 1/(1000000 / 1216299) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11425 : Bounds (195812641 / 1000000000) (97906321 / 500000000) (Real.log (1216299 / 1000000)) := by
  have h := reflection_log_11425_neg
  have he : Real.log (1216299 / 1000000) = -Real.log (1000000 / 1216299) := by
    rw [show ((1216299 / 1000000) : ℝ) = ((1000000 / 1216299) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11426_neg : (60931927 / 250000000) ≤ -Real.log (783701 / 1000000) ∧
    -Real.log (783701 / 1000000) ≤ (243727709 / 1000000000) := by
  have h := checkLog_sound (w := (216299 / 1783701)) (n := 12)
    (lo := (60931927 / 250000000)) (hi := (243727709 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 783701) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 783701) = 1/(783701 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11426 : Bounds (-243727709 / 1000000000) (-60931927 / 250000000) (Real.log (783701 / 1000000)) := by
  have h := reflection_log_11426_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11427_neg : (39319829 / 200000000) ≤ -Real.log (125000 / 152157) ∧
    -Real.log (125000 / 152157) ≤ (98299573 / 500000000) := by
  have h := checkLog_sound (w := (27157 / 277157)) (n := 12)
    (lo := (39319829 / 200000000)) (hi := (98299573 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((152157 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(152157 / 125000) = 1/(125000 / 152157) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11427 : Bounds (39319829 / 200000000) (98299573 / 500000000) (Real.log (152157 / 125000)) := by
  have h := reflection_log_11427_neg
  have he : Real.log (152157 / 125000) = -Real.log (125000 / 152157) := by
    rw [show ((152157 / 125000) : ℝ) = ((125000 / 152157) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11428_neg : (15309349 / 62500000) ≤ -Real.log (97843 / 125000) ∧
    -Real.log (97843 / 125000) ≤ (48989917 / 200000000) := by
  have h := checkLog_sound (w := (27157 / 222843)) (n := 12)
    (lo := (15309349 / 62500000)) (hi := (48989917 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 97843) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 97843) = 1/(97843 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11428 : Bounds (-48989917 / 200000000) (-15309349 / 62500000) (Real.log (97843 / 125000)) := by
  have h := reflection_log_11428_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11429_neg : (24175219 / 500000000) ≤ -Real.log (14887497351 / 15625000000) ∧
    -Real.log (14887497351 / 15625000000) ≤ (48350439 / 1000000000) := by
  have h := checkLog_sound (w := (737502649 / 30512497351)) (n := 12)
    (lo := (24175219 / 500000000)) (hi := (48350439 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 14887497351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 14887497351) = 1/(14887497351 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11429 : Bounds (-48350439 / 1000000000) (-24175219 / 500000000) (Real.log (14887497351 / 15625000000)) := by
  have h := reflection_log_11429_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11430_neg : (47915067 / 1000000000) ≤ -Real.log (953214742599 / 1000000000000) ∧
    -Real.log (953214742599 / 1000000000000) ≤ (11978767 / 250000000) := by
  have h := checkLog_sound (w := (46785257401 / 1953214742599)) (n := 12)
    (lo := (47915067 / 1000000000)) (hi := (11978767 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 953214742599) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 953214742599) = 1/(953214742599 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11430 : Bounds (-11978767 / 250000000) (-47915067 / 1000000000) (Real.log (953214742599 / 1000000000000)) := by
  have h := reflection_log_11430_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11431_neg : (8790807 / 20000000) ≤ -Real.log (500000000000 / 775996840631) ∧
    -Real.log (500000000000 / 775996840631) ≤ (439540351 / 1000000000) := by
  have h := checkLog_sound (w := (275996840631 / 1275996840631)) (n := 12)
    (lo := (8790807 / 20000000)) (hi := (439540351 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((775996840631 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(775996840631 / 500000000000) = 1/(500000000000 / 775996840631) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11431 : Bounds (8790807 / 20000000) (439540351 / 1000000000) (Real.log (775996840631 / 500000000000)) := by
  have h := reflection_log_11431_neg
  have he : Real.log (775996840631 / 500000000000) = -Real.log (500000000000 / 775996840631) := by
    rw [show ((775996840631 / 500000000000) : ℝ) = ((500000000000 / 775996840631) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11432_neg : (441548729 / 1000000000) ≤ -Real.log (100000000000 / 155511380477) ∧
    -Real.log (100000000000 / 155511380477) ≤ (44154873 / 100000000) := by
  have h := checkLog_sound (w := (55511380477 / 255511380477)) (n := 12)
    (lo := (441548729 / 1000000000)) (hi := (44154873 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((155511380477 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(155511380477 / 100000000000) = 1/(100000000000 / 155511380477) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11432 : Bounds (441548729 / 1000000000) (44154873 / 100000000) (Real.log (155511380477 / 100000000000)) := by
  have h := reflection_log_11432_neg
  have he : Real.log (155511380477 / 100000000000) = -Real.log (100000000000 / 155511380477) := by
    rw [show ((155511380477 / 100000000000) : ℝ) = ((100000000000 / 155511380477) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11433_neg : (892956919 / 1000000000) ≤ -Real.log (500000000000 / 1221170395869) ∧
    -Real.log (500000000000 / 1221170395869) ≤ (892956921 / 1000000000) := by
  have h := checkLog_sound (w := (221170395869 / 2221170395869)) (n := 12)
    (lo := (199809739 / 1000000000)) (hi := (9990487 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1221170395869 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1221170395869 / 1000000000000) = 1/(500000000000 / 1221170395869) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11433 : Bounds (892956919 / 1000000000) (892956921 / 1000000000) (Real.log (1221170395869 / 500000000000)) := by
  have h := reflection_log_11433_neg
  have he : Real.log (1221170395869 / 500000000000) = -Real.log (500000000000 / 1221170395869) := by
    rw [show ((1221170395869 / 500000000000) : ℝ) = ((500000000000 / 1221170395869) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11434_neg : (447692023 / 500000000) ≤ -Real.log (100000000000 / 244827586207) ∧
    -Real.log (100000000000 / 244827586207) ≤ (55961503 / 62500000) := by
  have h := checkLog_sound (w := (44827586207 / 444827586207)) (n := 12)
    (lo := (101118433 / 500000000)) (hi := (202236867 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((244827586207 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(244827586207 / 200000000000) = 1/(100000000000 / 244827586207) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11434 : Bounds (447692023 / 500000000) (55961503 / 62500000) (Real.log (244827586207 / 100000000000)) := by
  have h := reflection_log_11434_neg
  have he : Real.log (244827586207 / 100000000000) = -Real.log (100000000000 / 244827586207) := by
    rw [show ((244827586207 / 100000000000) : ℝ) = ((100000000000 / 244827586207) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11435_neg : (351360849 / 1000000000) ≤ -Real.log (1000 / 1421) ∧
    -Real.log (1000 / 1421) ≤ (7027217 / 20000000) := by
  have h := checkLog_sound (w := (421 / 2421)) (n := 12)
    (lo := (351360849 / 1000000000)) (hi := (7027217 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1421 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1421 / 1000) = 1/(1000 / 1421) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11435 : Bounds (351360849 / 1000000000) (7027217 / 20000000) (Real.log (1421 / 1000)) := by
  have h := reflection_log_11435_neg
  have he : Real.log (1421 / 1000) = -Real.log (1000 / 1421) := by
    rw [show ((1421 / 1000) : ℝ) = ((1000 / 1421) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11436_neg : (546452801 / 1000000000) ≤ -Real.log (579 / 1000) ∧
    -Real.log (579 / 1000) ≤ (273226401 / 500000000) := by
  have h := checkLog_sound (w := (421 / 1579)) (n := 12)
    (lo := (546452801 / 1000000000)) (hi := (273226401 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 579) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 579) = 1/(579 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11436 : Bounds (-273226401 / 500000000) (-546452801 / 1000000000) (Real.log (579 / 1000)) := by
  have h := reflection_log_11436_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11437_neg : (420911 / 1000000000) ≤ -Real.log (1000000 / 1000421) ∧
    -Real.log (1000000 / 1000421) ≤ (26307 / 62500000) := by
  have h := checkLog_sound (w := (421 / 2000421)) (n := 12)
    (lo := (420911 / 1000000000)) (hi := (26307 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000421 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000421 / 1000000) = 1/(1000000 / 1000421) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11437 : Bounds (420911 / 1000000000) (26307 / 62500000) (Real.log (1000421 / 1000000)) := by
  have h := reflection_log_11437_neg
  have he : Real.log (1000421 / 1000000) = -Real.log (1000000 / 1000421) := by
    rw [show ((1000421 / 1000000) : ℝ) = ((1000000 / 1000421) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11438_neg : (13159 / 31250000) ≤ -Real.log (999579 / 1000000) ∧
    -Real.log (999579 / 1000000) ≤ (421089 / 1000000000) := by
  have h := checkLog_sound (w := (421 / 1999579)) (n := 12)
    (lo := (13159 / 31250000)) (hi := (421089 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999579) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999579) = 1/(999579 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11438 : Bounds (-421089 / 1000000000) (-13159 / 31250000) (Real.log (999579 / 1000000)) := by
  have h := reflection_log_11438_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11439_neg : (12266597 / 62500000) ≤ -Real.log (20000 / 24337) ∧
    -Real.log (20000 / 24337) ≤ (196265553 / 1000000000) := by
  have h := checkLog_sound (w := (4337 / 44337)) (n := 12)
    (lo := (12266597 / 62500000)) (hi := (196265553 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24337 / 20000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24337 / 20000) = 1/(20000 / 24337) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11439 : Bounds (12266597 / 62500000) (196265553 / 1000000000) (Real.log (24337 / 20000)) := by
  have h := reflection_log_11439_neg
  have he : Real.log (24337 / 20000) = -Real.log (20000 / 24337) := by
    rw [show ((24337 / 20000) : ℝ) = ((20000 / 24337) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11440_neg : (24443103 / 100000000) ≤ -Real.log (15663 / 20000) ∧
    -Real.log (15663 / 20000) ≤ (244431031 / 1000000000) := by
  have h := checkLog_sound (w := (4337 / 35663)) (n := 12)
    (lo := (24443103 / 100000000)) (hi := (244431031 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20000 / 15663) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20000 / 15663) = 1/(15663 / 20000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11440 : Bounds (-244431031 / 1000000000) (-24443103 / 100000000) (Real.log (15663 / 20000)) := by
  have h := reflection_log_11440_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11441_neg : (98526671 / 500000000) ≤ -Real.log (1000000 / 1217809) ∧
    -Real.log (1000000 / 1217809) ≤ (197053343 / 1000000000) := by
  have h := checkLog_sound (w := (217809 / 2217809)) (n := 12)
    (lo := (98526671 / 500000000)) (hi := (197053343 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1217809 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1217809 / 1000000) = 1/(1000000 / 1217809) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11441 : Bounds (98526671 / 500000000) (197053343 / 1000000000) (Real.log (1217809 / 1000000)) := by
  have h := reflection_log_11441_neg
  have he : Real.log (1217809 / 1000000) = -Real.log (1000000 / 1217809) := by
    rw [show ((1217809 / 1000000) : ℝ) = ((1000000 / 1217809) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11442_neg : (122828161 / 500000000) ≤ -Real.log (782191 / 1000000) ∧
    -Real.log (782191 / 1000000) ≤ (245656323 / 1000000000) := by
  have h := checkLog_sound (w := (217809 / 1782191)) (n := 12)
    (lo := (122828161 / 500000000)) (hi := (245656323 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 782191) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 782191) = 1/(782191 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11442 : Bounds (-245656323 / 1000000000) (-122828161 / 500000000) (Real.log (782191 / 1000000)) := by
  have h := reflection_log_11442_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11443_neg : (2430149 / 50000000) ≤ -Real.log (952559239519 / 1000000000000) ∧
    -Real.log (952559239519 / 1000000000000) ≤ (48602981 / 1000000000) := by
  have h := checkLog_sound (w := (47440760481 / 1952559239519)) (n := 12)
    (lo := (2430149 / 50000000)) (hi := (48602981 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 952559239519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 952559239519) = 1/(952559239519 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11443 : Bounds (-48602981 / 1000000000) (-2430149 / 50000000) (Real.log (952559239519 / 1000000000000)) := by
  have h := reflection_log_11443_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11444_neg : (48165477 / 1000000000) ≤ -Real.log (381190431 / 400000000) ∧
    -Real.log (381190431 / 400000000) ≤ (24082739 / 500000000) := by
  have h := checkLog_sound (w := (18809569 / 781190431)) (n := 12)
    (lo := (48165477 / 1000000000)) (hi := (24082739 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400000000 / 381190431) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400000000 / 381190431) = 1/(381190431 / 400000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11444 : Bounds (-24082739 / 500000000) (-48165477 / 1000000000) (Real.log (381190431 / 400000000)) := by
  have h := reflection_log_11444_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11445_neg : (220348291 / 500000000) ≤ -Real.log (500000000000 / 776894592351) ∧
    -Real.log (500000000000 / 776894592351) ≤ (440696583 / 1000000000) := by
  have h := checkLog_sound (w := (276894592351 / 1276894592351)) (n := 12)
    (lo := (220348291 / 500000000)) (hi := (440696583 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((776894592351 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(776894592351 / 500000000000) = 1/(500000000000 / 776894592351) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11445 : Bounds (220348291 / 500000000) (440696583 / 1000000000) (Real.log (776894592351 / 500000000000)) := by
  have h := reflection_log_11445_neg
  have he : Real.log (776894592351 / 500000000000) = -Real.log (500000000000 / 776894592351) := by
    rw [show ((776894592351 / 500000000000) : ℝ) = ((500000000000 / 776894592351) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11446_neg : (88541933 / 200000000) ≤ -Real.log (100000000000 / 155692024071) ∧
    -Real.log (100000000000 / 155692024071) ≤ (221354833 / 500000000) := by
  have h := checkLog_sound (w := (55692024071 / 255692024071)) (n := 12)
    (lo := (88541933 / 200000000)) (hi := (221354833 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((155692024071 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(155692024071 / 100000000000) = 1/(100000000000 / 155692024071) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11446 : Bounds (88541933 / 200000000) (221354833 / 500000000) (Real.log (155692024071 / 100000000000)) := by
  have h := reflection_log_11446_neg
  have he : Real.log (155692024071 / 100000000000) = -Real.log (100000000000 / 155692024071) := by
    rw [show ((155692024071 / 100000000000) : ℝ) = ((100000000000 / 155692024071) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11447_neg : (447692023 / 500000000) ≤ -Real.log (250000000000 / 612068965517) ∧
    -Real.log (250000000000 / 612068965517) ≤ (55961503 / 62500000) := by
  have h := checkLog_sound (w := (112068965517 / 1112068965517)) (n := 12)
    (lo := (101118433 / 500000000)) (hi := (202236867 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((612068965517 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(612068965517 / 500000000000) = 1/(250000000000 / 612068965517) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11447 : Bounds (447692023 / 500000000) (55961503 / 62500000) (Real.log (612068965517 / 250000000000)) := by
  have h := reflection_log_11447_neg
  have he : Real.log (612068965517 / 250000000000) = -Real.log (250000000000 / 612068965517) := by
    rw [show ((612068965517 / 250000000000) : ℝ) = ((250000000000 / 612068965517) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11448_neg : (897813649 / 1000000000) ≤ -Real.log (250000000000 / 613557858377) ∧
    -Real.log (250000000000 / 613557858377) ≤ (897813651 / 1000000000) := by
  have h := checkLog_sound (w := (113557858377 / 1113557858377)) (n := 12)
    (lo := (204666469 / 1000000000)) (hi := (20466647 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((613557858377 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(613557858377 / 500000000000) = 1/(250000000000 / 613557858377) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11448 : Bounds (897813649 / 1000000000) (897813651 / 1000000000) (Real.log (613557858377 / 250000000000)) := by
  have h := reflection_log_11448_neg
  have he : Real.log (613557858377 / 250000000000) = -Real.log (250000000000 / 613557858377) := by
    rw [show ((613557858377 / 250000000000) : ℝ) = ((250000000000 / 613557858377) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11449_neg : (352064331 / 1000000000) ≤ -Real.log (500 / 711) ∧
    -Real.log (500 / 711) ≤ (88016083 / 250000000) := by
  have h := checkLog_sound (w := (211 / 1211)) (n := 12)
    (lo := (352064331 / 1000000000)) (hi := (88016083 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((711 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(711 / 500) = 1/(500 / 711) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11449 : Bounds (352064331 / 1000000000) (88016083 / 250000000) (Real.log (711 / 500)) := by
  have h := reflection_log_11449_neg
  have he : Real.log (711 / 500) = -Real.log (500 / 711) := by
    rw [show ((711 / 500) : ℝ) = ((500 / 711) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11450_neg : (54818141 / 100000000) ≤ -Real.log (289 / 500) ∧
    -Real.log (289 / 500) ≤ (548181411 / 1000000000) := by
  have h := checkLog_sound (w := (211 / 789)) (n := 12)
    (lo := (54818141 / 100000000)) (hi := (548181411 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 289) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500 / 289) = 1/(289 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11450 : Bounds (-548181411 / 1000000000) (-54818141 / 100000000) (Real.log (289 / 500)) := by
  have h := reflection_log_11450_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11451_neg : (42191 / 100000000) ≤ -Real.log (500000 / 500211) ∧
    -Real.log (500000 / 500211) ≤ (421911 / 1000000000) := by
  have h := checkLog_sound (w := (211 / 1000211)) (n := 12)
    (lo := (42191 / 100000000)) (hi := (421911 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500211 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500211 / 500000) = 1/(500000 / 500211) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11451 : Bounds (42191 / 100000000) (421911 / 1000000000) (Real.log (500211 / 500000)) := by
  have h := reflection_log_11451_neg
  have he : Real.log (500211 / 500000) = -Real.log (500000 / 500211) := by
    rw [show ((500211 / 500000) : ℝ) = ((500000 / 500211) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11452_neg : (422089 / 1000000000) ≤ -Real.log (499789 / 500000) ∧
    -Real.log (499789 / 500000) ≤ (42209 / 100000000) := by
  have h := checkLog_sound (w := (211 / 999789)) (n := 12)
    (lo := (422089 / 1000000000)) (hi := (42209 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499789) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499789) = 1/(499789 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11452 : Bounds (-42209 / 100000000) (-422089 / 1000000000) (Real.log (499789 / 500000)) := by
  have h := reflection_log_11452_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11453_neg : (196719079 / 1000000000) ≤ -Real.log (500000 / 608701) ∧
    -Real.log (500000 / 608701) ≤ (4917977 / 25000000) := by
  have h := checkLog_sound (w := (108701 / 1108701)) (n := 12)
    (lo := (196719079 / 1000000000)) (hi := (4917977 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((608701 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(608701 / 500000) = 1/(500000 / 608701) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11453 : Bounds (196719079 / 1000000000) (4917977 / 25000000) (Real.log (608701 / 500000)) := by
  have h := reflection_log_11453_neg
  have he : Real.log (608701 / 500000) = -Real.log (500000 / 608701) := by
    rw [show ((608701 / 500000) : ℝ) = ((500000 / 608701) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11454_neg : (61284031 / 250000000) ≤ -Real.log (391299 / 500000) ∧
    -Real.log (391299 / 500000) ≤ (1961089 / 8000000) := by
  have h := checkLog_sound (w := (108701 / 891299)) (n := 12)
    (lo := (61284031 / 250000000)) (hi := (1961089 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 391299) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 391299) = 1/(391299 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11454 : Bounds (-1961089 / 8000000) (-61284031 / 250000000) (Real.log (391299 / 500000)) := by
  have h := reflection_log_11454_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11455_neg : (98754077 / 500000000) ≤ -Real.log (1000000 / 1218363) ∧
    -Real.log (1000000 / 1218363) ≤ (39501631 / 200000000) := by
  have h := checkLog_sound (w := (218363 / 2218363)) (n := 12)
    (lo := (98754077 / 500000000)) (hi := (39501631 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1218363 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1218363 / 1000000) = 1/(1000000 / 1218363) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11455 : Bounds (98754077 / 500000000) (39501631 / 200000000) (Real.log (1218363 / 1000000)) := by
  have h := reflection_log_11455_neg
  have he : Real.log (1218363 / 1000000) = -Real.log (1000000 / 1218363) := by
    rw [show ((1218363 / 1000000) : ℝ) = ((1000000 / 1218363) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily
