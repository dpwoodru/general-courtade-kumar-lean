import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell196
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

theorem reflection_log_1_neg : (19466823 / 62500000) ≤ -Real.log (5120 / 6991) ∧
    -Real.log (5120 / 6991) ≤ (311469169 / 1000000000) := by
  have h := checkLog_sound (w := (1871 / 12111)) (n := 12)
    (lo := (19466823 / 62500000)) (hi := (311469169 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6991 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6991 / 5120) = 1/(5120 / 6991) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (19466823 / 62500000) (311469169 / 1000000000) (Real.log (6991 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6991 / 5120) = -Real.log (5120 / 6991) := by
    rw [show ((6991 / 5120) : ℝ) = ((5120 / 6991) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (227403591 / 500000000) ≤ -Real.log (3249 / 5120) ∧
    -Real.log (3249 / 5120) ≤ (454807183 / 1000000000) := by
  have h := checkLog_sound (w := (1871 / 8369)) (n := 12)
    (lo := (227403591 / 500000000)) (hi := (454807183 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3249) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3249) = 1/(3249 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-454807183 / 1000000000) (-227403591 / 500000000) (Real.log (3249 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (311039953 / 1000000000) ≤ -Real.log (1280 / 1747) ∧
    -Real.log (1280 / 1747) ≤ (155519977 / 500000000) := by
  have h := checkLog_sound (w := (467 / 3027)) (n := 12)
    (lo := (311039953 / 1000000000)) (hi := (155519977 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1747 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1747 / 1280) = 1/(1280 / 1747) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (311039953 / 1000000000) (155519977 / 500000000) (Real.log (1747 / 1280)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1747 / 1280) = -Real.log (1280 / 1747) := by
    rw [show ((1747 / 1280) : ℝ) = ((1280 / 1747) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (453884247 / 1000000000) ≤ -Real.log (813 / 1280) ∧
    -Real.log (813 / 1280) ≤ (56735531 / 125000000) := by
  have h := checkLog_sound (w := (467 / 2093)) (n := 12)
    (lo := (453884247 / 1000000000)) (hi := (56735531 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 813) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 813) = 1/(813 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-56735531 / 125000000) (-453884247 / 1000000000) (Real.log (813 / 1280)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (115357011 / 500000000) ≤ -Real.log (1000000 / 1259499) ∧
    -Real.log (1000000 / 1259499) ≤ (230714023 / 1000000000) := by
  have h := checkLog_sound (w := (259499 / 2259499)) (n := 12)
    (lo := (115357011 / 500000000)) (hi := (230714023 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1259499 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1259499 / 1000000) = 1/(1000000 / 1259499) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (115357011 / 500000000) (230714023 / 1000000000) (Real.log (1259499 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1259499 / 1000000) = -Real.log (1000000 / 1259499) := by
    rw [show ((1259499 / 1000000) : ℝ) = ((1000000 / 1259499) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (150214147 / 500000000) ≤ -Real.log (740501 / 1000000) ∧
    -Real.log (740501 / 1000000) ≤ (60085659 / 200000000) := by
  have h := checkLog_sound (w := (259499 / 1740501)) (n := 12)
    (lo := (150214147 / 500000000)) (hi := (60085659 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 740501) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 740501) = 1/(740501 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-60085659 / 200000000) (-150214147 / 500000000) (Real.log (740501 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (115524907 / 500000000) ≤ -Real.log (500000 / 629961) ∧
    -Real.log (500000 / 629961) ≤ (46209963 / 200000000) := by
  have h := checkLog_sound (w := (129961 / 1129961)) (n := 12)
    (lo := (115524907 / 500000000)) (hi := (46209963 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((629961 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(629961 / 500000) = 1/(500000 / 629961) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (115524907 / 500000000) (46209963 / 200000000) (Real.log (629961 / 500000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (629961 / 500000) = -Real.log (500000 / 629961) := by
    rw [show ((629961 / 500000) : ℝ) = ((500000 / 629961) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (75249923 / 250000000) ≤ -Real.log (370039 / 500000) ∧
    -Real.log (370039 / 500000) ≤ (300999693 / 1000000000) := by
  have h := checkLog_sound (w := (129961 / 870039)) (n := 12)
    (lo := (75249923 / 250000000)) (hi := (300999693 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 370039) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 370039) = 1/(370039 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-300999693 / 1000000000) (-75249923 / 250000000) (Real.log (370039 / 500000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (42853277 / 250000000) ≤ -Real.log (1000000 / 1186981) ∧
    -Real.log (1000000 / 1186981) ≤ (171413109 / 1000000000) := by
  have h := checkLog_sound (w := (186981 / 2186981)) (n := 12)
    (lo := (42853277 / 250000000)) (hi := (171413109 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1186981 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1186981 / 1000000) = 1/(1000000 / 1186981) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (42853277 / 250000000) (171413109 / 1000000000) (Real.log (1186981 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1186981 / 1000000) = -Real.log (1000000 / 1186981) := by
    rw [show ((1186981 / 1000000) : ℝ) = ((1000000 / 1186981) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (207000799 / 1000000000) ≤ -Real.log (813019 / 1000000) ∧
    -Real.log (813019 / 1000000) ≤ (258751 / 1250000) := by
  have h := checkLog_sound (w := (186981 / 1813019)) (n := 12)
    (lo := (207000799 / 1000000000)) (hi := (258751 / 1250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 813019) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 813019) = 1/(813019 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-258751 / 1250000) (-207000799 / 1000000000) (Real.log (813019 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (171680137 / 1000000000) ≤ -Real.log (500000 / 593649) ∧
    -Real.log (500000 / 593649) ≤ (85840069 / 500000000) := by
  have h := checkLog_sound (w := (93649 / 1093649)) (n := 12)
    (lo := (171680137 / 1000000000)) (hi := (85840069 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((593649 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(593649 / 500000) = 1/(500000 / 593649) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (171680137 / 1000000000) (85840069 / 500000000) (Real.log (593649 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (593649 / 500000) = -Real.log (500000 / 593649) := by
    rw [show ((593649 / 500000) : ℝ) = ((500000 / 593649) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (10369539 / 50000000) ≤ -Real.log (406351 / 500000) ∧
    -Real.log (406351 / 500000) ≤ (207390781 / 1000000000) := by
  have h := checkLog_sound (w := (93649 / 906351)) (n := 12)
    (lo := (10369539 / 50000000)) (hi := (207390781 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 406351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 406351) = 1/(406351 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-207390781 / 1000000000) (-10369539 / 50000000) (Real.log (406351 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (3824621 / 5000000) ≤ -Real.log (500000000000 / 1074415744157) ∧
    -Real.log (500000000000 / 1074415744157) ≤ (382462101 / 500000000) := by
  have h := checkLog_sound (w := (74415744157 / 2074415744157)) (n := 12)
    (lo := (3588851 / 50000000)) (hi := (71777021 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1074415744157 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1074415744157 / 1000000000000) = 1/(500000000000 / 1074415744157) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (3824621 / 5000000) (382462101 / 500000000) (Real.log (1074415744157 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1074415744157 / 500000000000) = -Real.log (500000000000 / 1074415744157) := by
    rw [show ((1074415744157 / 500000000000) : ℝ) = ((500000000000 / 1074415744157) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (15325527 / 20000000) ≤ -Real.log (125000000000 / 268967374577) ∧
    -Real.log (125000000000 / 268967374577) ≤ (2993267 / 3906250) := by
  have h := checkLog_sound (w := (18967374577 / 518967374577)) (n := 12)
    (lo := (7312917 / 100000000)) (hi := (73129171 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((268967374577 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(268967374577 / 250000000000) = 1/(125000000000 / 268967374577) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (15325527 / 20000000) (2993267 / 3906250) (Real.log (268967374577 / 125000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (268967374577 / 125000000000) = -Real.log (125000000000 / 268967374577) := by
    rw [show ((268967374577 / 125000000000) : ℝ) = ((125000000000 / 268967374577) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (531142317 / 1000000000) ≤ -Real.log (500000000000 / 850437068957) ∧
    -Real.log (500000000000 / 850437068957) ≤ (265571159 / 500000000) := by
  have h := checkLog_sound (w := (350437068957 / 1350437068957)) (n := 12)
    (lo := (531142317 / 1000000000)) (hi := (265571159 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((850437068957 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(850437068957 / 500000000000) = 1/(500000000000 / 850437068957) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (531142317 / 1000000000) (265571159 / 500000000) (Real.log (850437068957 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (850437068957 / 500000000000) = -Real.log (500000000000 / 850437068957) := by
    rw [show ((850437068957 / 500000000000) : ℝ) = ((500000000000 / 850437068957) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (532049507 / 1000000000) ≤ -Real.log (500000000000 / 851208926627) ∧
    -Real.log (500000000000 / 851208926627) ≤ (133012377 / 250000000) := by
  have h := checkLog_sound (w := (351208926627 / 1351208926627)) (n := 12)
    (lo := (532049507 / 1000000000)) (hi := (133012377 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((851208926627 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(851208926627 / 500000000000) = 1/(500000000000 / 851208926627) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (532049507 / 1000000000) (133012377 / 250000000) (Real.log (851208926627 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (851208926627 / 500000000000) = -Real.log (500000000000 / 851208926627) := by
    rw [show ((851208926627 / 500000000000) : ℝ) = ((500000000000 / 851208926627) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (94603477 / 250000000) ≤ -Real.log (500000000000 / 729983555119) ∧
    -Real.log (500000000000 / 729983555119) ≤ (378413909 / 1000000000) := by
  have h := checkLog_sound (w := (229983555119 / 1229983555119)) (n := 12)
    (lo := (94603477 / 250000000)) (hi := (378413909 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((729983555119 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(729983555119 / 500000000000) = 1/(500000000000 / 729983555119) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (94603477 / 250000000) (378413909 / 1000000000) (Real.log (729983555119 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (729983555119 / 500000000000) = -Real.log (500000000000 / 729983555119) := by
    rw [show ((729983555119 / 500000000000) : ℝ) = ((500000000000 / 729983555119) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (379070917 / 1000000000) ≤ -Real.log (500000000000 / 730463318659) ∧
    -Real.log (500000000000 / 730463318659) ≤ (189535459 / 500000000) := by
  have h := checkLog_sound (w := (230463318659 / 1230463318659)) (n := 12)
    (lo := (379070917 / 1000000000)) (hi := (189535459 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((730463318659 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(730463318659 / 500000000000) = 1/(500000000000 / 730463318659) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (379070917 / 1000000000) (189535459 / 500000000) (Real.log (730463318659 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (730463318659 / 500000000000) = -Real.log (500000000000 / 730463318659) := by
    rw [show ((730463318659 / 500000000000) : ℝ) = ((500000000000 / 730463318659) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (35710643 / 1000000000) ≤ -Real.log (241229864799 / 250000000000) ∧
    -Real.log (241229864799 / 250000000000) ≤ (8927661 / 250000000) := by
  have h := checkLog_sound (w := (8770135201 / 491229864799)) (n := 12)
    (lo := (35710643 / 1000000000)) (hi := (8927661 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 241229864799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 241229864799) = 1/(241229864799 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-8927661 / 250000000) (-35710643 / 1000000000) (Real.log (241229864799 / 250000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (3558769 / 100000000) ≤ -Real.log (965038105639 / 1000000000000) ∧
    -Real.log (965038105639 / 1000000000000) ≤ (35587691 / 1000000000) := by
  have h := checkLog_sound (w := (34961894361 / 1965038105639)) (n := 12)
    (lo := (3558769 / 100000000)) (hi := (35587691 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 965038105639) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 965038105639) = 1/(965038105639 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-35587691 / 1000000000) (-3558769 / 100000000) (Real.log (965038105639 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell196
