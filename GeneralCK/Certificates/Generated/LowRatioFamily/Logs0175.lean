import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_11200_neg : (404081 / 1000000000) ≤ -Real.log (249899 / 250000) ∧
    -Real.log (249899 / 250000) ≤ (202041 / 500000000) := by
  have h := checkLog_sound (w := (101 / 499899)) (n := 12)
    (lo := (404081 / 1000000000)) (hi := (202041 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 249899) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 249899) = 1/(249899 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11200 : Bounds (-202041 / 500000000) (-404081 / 1000000000) (Real.log (249899 / 250000)) := by
  have h := reflection_log_11200_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11201_neg : (188557903 / 1000000000) ≤ -Real.log (1000000 / 1207507) ∧
    -Real.log (1000000 / 1207507) ≤ (11784869 / 62500000) := by
  have h := checkLog_sound (w := (207507 / 2207507)) (n := 12)
    (lo := (188557903 / 1000000000)) (hi := (11784869 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1207507 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1207507 / 1000000) = 1/(1000000 / 1207507) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11201 : Bounds (188557903 / 1000000000) (11784869 / 62500000) (Real.log (1207507 / 1000000)) := by
  have h := reflection_log_11201_neg
  have he : Real.log (1207507 / 1000000) = -Real.log (1000000 / 1207507) := by
    rw [show ((1207507 / 1000000) : ℝ) = ((1000000 / 1207507) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11202_neg : (116285803 / 500000000) ≤ -Real.log (792493 / 1000000) ∧
    -Real.log (792493 / 1000000) ≤ (232571607 / 1000000000) := by
  have h := checkLog_sound (w := (207507 / 1792493)) (n := 12)
    (lo := (116285803 / 500000000)) (hi := (232571607 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 792493) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 792493) = 1/(792493 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11202 : Bounds (-232571607 / 1000000000) (-116285803 / 500000000) (Real.log (792493 / 1000000)) := by
  have h := reflection_log_11202_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11203_neg : (369797 / 1953125) ≤ -Real.log (1000000 / 1208447) ∧
    -Real.log (1000000 / 1208447) ≤ (37867213 / 200000000) := by
  have h := checkLog_sound (w := (208447 / 2208447)) (n := 12)
    (lo := (369797 / 1953125)) (hi := (37867213 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1208447 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1208447 / 1000000) = 1/(1000000 / 1208447) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11203 : Bounds (369797 / 1953125) (37867213 / 200000000) (Real.log (1208447 / 1000000)) := by
  have h := reflection_log_11203_neg
  have he : Real.log (1208447 / 1000000) = -Real.log (1000000 / 1208447) := by
    rw [show ((1208447 / 1000000) : ℝ) = ((1000000 / 1208447) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11204_neg : (5843961 / 25000000) ≤ -Real.log (791553 / 1000000) ∧
    -Real.log (791553 / 1000000) ≤ (233758441 / 1000000000) := by
  have h := checkLog_sound (w := (208447 / 1791553)) (n := 12)
    (lo := (5843961 / 25000000)) (hi := (233758441 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 791553) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 791553) = 1/(791553 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11204 : Bounds (-233758441 / 1000000000) (-5843961 / 25000000) (Real.log (791553 / 1000000)) := by
  have h := reflection_log_11204_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11205_neg : (5552797 / 125000000) ≤ -Real.log (956549848191 / 1000000000000) ∧
    -Real.log (956549848191 / 1000000000000) ≤ (44422377 / 1000000000) := by
  have h := checkLog_sound (w := (43450151809 / 1956549848191)) (n := 12)
    (lo := (5552797 / 125000000)) (hi := (44422377 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 956549848191) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 956549848191) = 1/(956549848191 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11205 : Bounds (-44422377 / 1000000000) (-5552797 / 125000000) (Real.log (956549848191 / 1000000000000)) := by
  have h := reflection_log_11205_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11206_neg : (22006851 / 500000000) ≤ -Real.log (956940844951 / 1000000000000) ∧
    -Real.log (956940844951 / 1000000000000) ≤ (44013703 / 1000000000) := by
  have h := checkLog_sound (w := (43059155049 / 1956940844951)) (n := 12)
    (lo := (22006851 / 500000000)) (hi := (44013703 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 956940844951) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 956940844951) = 1/(956940844951 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11206 : Bounds (-44013703 / 1000000000) (-22006851 / 500000000) (Real.log (956940844951 / 1000000000000)) := by
  have h := reflection_log_11206_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11207_neg : (421129509 / 1000000000) ≤ -Real.log (500000000000 / 761840798593) ∧
    -Real.log (500000000000 / 761840798593) ≤ (42112951 / 100000000) := by
  have h := checkLog_sound (w := (261840798593 / 1261840798593)) (n := 12)
    (lo := (421129509 / 1000000000)) (hi := (42112951 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((761840798593 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(761840798593 / 500000000000) = 1/(500000000000 / 761840798593) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11207 : Bounds (421129509 / 1000000000) (42112951 / 100000000) (Real.log (761840798593 / 500000000000)) := by
  have h := reflection_log_11207_neg
  have he : Real.log (761840798593 / 500000000000) = -Real.log (500000000000 / 761840798593) := by
    rw [show ((761840798593 / 500000000000) : ℝ) = ((500000000000 / 761840798593) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11208_neg : (52886813 / 125000000) ≤ -Real.log (250000000000 / 381669641831) ∧
    -Real.log (250000000000 / 381669641831) ≤ (84618901 / 200000000) := by
  have h := checkLog_sound (w := (131669641831 / 631669641831)) (n := 12)
    (lo := (52886813 / 125000000)) (hi := (84618901 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((381669641831 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(381669641831 / 250000000000) = 1/(250000000000 / 381669641831) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11208 : Bounds (52886813 / 125000000) (84618901 / 200000000) (Real.log (381669641831 / 250000000000)) := by
  have h := reflection_log_11208_neg
  have he : Real.log (381669641831 / 250000000000) = -Real.log (250000000000 / 381669641831) := by
    rw [show ((381669641831 / 250000000000) : ℝ) = ((250000000000 / 381669641831) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11209_neg : (427225483 / 500000000) ≤ -Real.log (250000000000 / 587520938023) ∧
    -Real.log (250000000000 / 587520938023) ≤ (106806371 / 125000000) := by
  have h := checkLog_sound (w := (87520938023 / 1087520938023)) (n := 12)
    (lo := (80651893 / 500000000)) (hi := (161303787 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((587520938023 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(587520938023 / 500000000000) = 1/(250000000000 / 587520938023) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11209 : Bounds (427225483 / 500000000) (106806371 / 125000000) (Real.log (587520938023 / 250000000000)) := by
  have h := reflection_log_11209_neg
  have he : Real.log (587520938023 / 250000000000) = -Real.log (250000000000 / 587520938023) := by
    rw [show ((587520938023 / 250000000000) : ℝ) = ((250000000000 / 587520938023) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11210_neg : (214209979 / 250000000) ≤ -Real.log (250000000000 / 588926174497) ∧
    -Real.log (250000000000 / 588926174497) ≤ (428419959 / 500000000) := by
  have h := checkLog_sound (w := (88926174497 / 1088926174497)) (n := 12)
    (lo := (2557699 / 15625000)) (hi := (163692737 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((588926174497 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(588926174497 / 500000000000) = 1/(250000000000 / 588926174497) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11210 : Bounds (214209979 / 250000000) (428419959 / 500000000) (Real.log (588926174497 / 250000000000)) := by
  have h := reflection_log_11210_neg
  have he : Real.log (588926174497 / 250000000000) = -Real.log (250000000000 / 588926174497) := by
    rw [show ((588926174497 / 250000000000) : ℝ) = ((250000000000 / 588926174497) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11211_neg : (170018651 / 500000000) ≤ -Real.log (200 / 281) ∧
    -Real.log (200 / 281) ≤ (340037303 / 1000000000) := by
  have h := checkLog_sound (w := (81 / 481)) (n := 12)
    (lo := (170018651 / 500000000)) (hi := (340037303 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((281 / 200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(281 / 200) = 1/(200 / 281) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11211 : Bounds (170018651 / 500000000) (340037303 / 1000000000) (Real.log (281 / 200)) := by
  have h := reflection_log_11211_neg
  have he : Real.log (281 / 200) = -Real.log (200 / 281) := by
    rw [show ((281 / 200) : ℝ) = ((200 / 281) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11212_neg : (519193873 / 1000000000) ≤ -Real.log (119 / 200) ∧
    -Real.log (119 / 200) ≤ (259596937 / 500000000) := by
  have h := checkLog_sound (w := (81 / 319)) (n := 12)
    (lo := (519193873 / 1000000000)) (hi := (259596937 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200 / 119) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200 / 119) = 1/(119 / 200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11212 : Bounds (-259596937 / 500000000) (-519193873 / 1000000000) (Real.log (119 / 200)) := by
  have h := reflection_log_11212_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11213_neg : (202459 / 500000000) ≤ -Real.log (200000 / 200081) ∧
    -Real.log (200000 / 200081) ≤ (404919 / 1000000000) := by
  have h := checkLog_sound (w := (81 / 400081)) (n := 12)
    (lo := (202459 / 500000000)) (hi := (404919 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200081 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200081 / 200000) = 1/(200000 / 200081) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11213 : Bounds (202459 / 500000000) (404919 / 1000000000) (Real.log (200081 / 200000)) := by
  have h := reflection_log_11213_neg
  have he : Real.log (200081 / 200000) = -Real.log (200000 / 200081) := by
    rw [show ((200081 / 200000) : ℝ) = ((200000 / 200081) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11214_neg : (202541 / 500000000) ≤ -Real.log (199919 / 200000) ∧
    -Real.log (199919 / 200000) ≤ (405083 / 1000000000) := by
  have h := checkLog_sound (w := (81 / 399919)) (n := 12)
    (lo := (202541 / 500000000)) (hi := (405083 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 199919) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 199919) = 1/(199919 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11214 : Bounds (-405083 / 1000000000) (-202541 / 500000000) (Real.log (199919 / 200000)) := by
  have h := reflection_log_11214_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11215_neg : (47252907 / 250000000) ≤ -Real.log (200000 / 241611) ∧
    -Real.log (200000 / 241611) ≤ (189011629 / 1000000000) := by
  have h := checkLog_sound (w := (41611 / 441611)) (n := 12)
    (lo := (47252907 / 250000000)) (hi := (189011629 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((241611 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(241611 / 200000) = 1/(200000 / 241611) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11215 : Bounds (47252907 / 250000000) (189011629 / 1000000000) (Real.log (241611 / 200000)) := by
  have h := reflection_log_11215_neg
  have he : Real.log (241611 / 200000) = -Real.log (200000 / 241611) := by
    rw [show ((241611 / 200000) : ℝ) = ((200000 / 241611) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11216_neg : (116631667 / 500000000) ≤ -Real.log (158389 / 200000) ∧
    -Real.log (158389 / 200000) ≤ (46652667 / 200000000) := by
  have h := checkLog_sound (w := (41611 / 358389)) (n := 12)
    (lo := (116631667 / 500000000)) (hi := (46652667 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 158389) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 158389) = 1/(158389 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11216 : Bounds (-46652667 / 200000000) (-116631667 / 500000000) (Real.log (158389 / 200000)) := by
  have h := reflection_log_11216_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11217_neg : (37957887 / 200000000) ≤ -Real.log (200000 / 241799) ∧
    -Real.log (200000 / 241799) ≤ (47447359 / 250000000) := by
  have h := checkLog_sound (w := (41799 / 441799)) (n := 12)
    (lo := (37957887 / 200000000)) (hi := (47447359 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((241799 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(241799 / 200000) = 1/(200000 / 241799) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11217 : Bounds (37957887 / 200000000) (47447359 / 250000000) (Real.log (241799 / 200000)) := by
  have h := reflection_log_11217_neg
  have he : Real.log (241799 / 200000) = -Real.log (200000 / 241799) := by
    rw [show ((241799 / 200000) : ℝ) = ((200000 / 241799) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11218_neg : (23445099 / 100000000) ≤ -Real.log (158201 / 200000) ∧
    -Real.log (158201 / 200000) ≤ (234450991 / 1000000000) := by
  have h := checkLog_sound (w := (41799 / 358201)) (n := 12)
    (lo := (23445099 / 100000000)) (hi := (234450991 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 158201) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 158201) = 1/(158201 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11218 : Bounds (-234450991 / 1000000000) (-23445099 / 100000000) (Real.log (158201 / 200000)) := by
  have h := reflection_log_11218_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11219_neg : (22330777 / 500000000) ≤ -Real.log (38252843599 / 40000000000) ∧
    -Real.log (38252843599 / 40000000000) ≤ (8932311 / 200000000) := by
  have h := checkLog_sound (w := (1747156401 / 78252843599)) (n := 12)
    (lo := (22330777 / 500000000)) (hi := (8932311 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 38252843599) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 38252843599) = 1/(38252843599 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11219 : Bounds (-8932311 / 200000000) (-22330777 / 500000000) (Real.log (38252843599 / 40000000000)) := by
  have h := reflection_log_11219_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11220_neg : (8850341 / 200000000) ≤ -Real.log (38268524679 / 40000000000) ∧
    -Real.log (38268524679 / 40000000000) ≤ (22125853 / 500000000) := by
  have h := checkLog_sound (w := (1731475321 / 78268524679)) (n := 12)
    (lo := (8850341 / 200000000)) (hi := (22125853 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 38268524679) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 38268524679) = 1/(38268524679 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11220 : Bounds (-22125853 / 500000000) (-8850341 / 200000000) (Real.log (38268524679 / 40000000000)) := by
  have h := reflection_log_11220_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11221_neg : (211137481 / 500000000) ≤ -Real.log (100000000000 / 152542790219) ∧
    -Real.log (100000000000 / 152542790219) ≤ (422274963 / 1000000000) := by
  have h := checkLog_sound (w := (52542790219 / 252542790219)) (n := 12)
    (lo := (211137481 / 500000000)) (hi := (422274963 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((152542790219 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(152542790219 / 100000000000) = 1/(100000000000 / 152542790219) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11221 : Bounds (211137481 / 500000000) (422274963 / 1000000000) (Real.log (152542790219 / 100000000000)) := by
  have h := reflection_log_11221_neg
  have he : Real.log (152542790219 / 100000000000) = -Real.log (100000000000 / 152542790219) := by
    rw [show ((152542790219 / 100000000000) : ℝ) = ((100000000000 / 152542790219) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11222_neg : (212120213 / 500000000) ≤ -Real.log (500000000000 / 764214511919) ∧
    -Real.log (500000000000 / 764214511919) ≤ (424240427 / 1000000000) := by
  have h := checkLog_sound (w := (264214511919 / 1264214511919)) (n := 12)
    (lo := (212120213 / 500000000)) (hi := (424240427 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((764214511919 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(764214511919 / 500000000000) = 1/(500000000000 / 764214511919) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11222 : Bounds (212120213 / 500000000) (424240427 / 1000000000) (Real.log (764214511919 / 500000000000)) := by
  have h := reflection_log_11222_neg
  have he : Real.log (764214511919 / 500000000000) = -Real.log (500000000000 / 764214511919) := by
    rw [show ((764214511919 / 500000000000) : ℝ) = ((500000000000 / 764214511919) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11223_neg : (214209979 / 250000000) ≤ -Real.log (500000000000 / 1177852348993) ∧
    -Real.log (500000000000 / 1177852348993) ≤ (428419959 / 500000000) := by
  have h := checkLog_sound (w := (177852348993 / 2177852348993)) (n := 12)
    (lo := (2557699 / 15625000)) (hi := (163692737 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1177852348993 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1177852348993 / 1000000000000) = 1/(500000000000 / 1177852348993) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11223 : Bounds (214209979 / 250000000) (428419959 / 500000000) (Real.log (1177852348993 / 500000000000)) := by
  have h := reflection_log_11223_neg
  have he : Real.log (1177852348993 / 500000000000) = -Real.log (500000000000 / 1177852348993) := by
    rw [show ((1177852348993 / 500000000000) : ℝ) = ((500000000000 / 1177852348993) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11224_neg : (34369247 / 40000000) ≤ -Real.log (125000000000 / 295168067227) ∧
    -Real.log (125000000000 / 295168067227) ≤ (859231177 / 1000000000) := by
  have h := checkLog_sound (w := (45168067227 / 545168067227)) (n := 12)
    (lo := (33216799 / 200000000)) (hi := (41520999 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((295168067227 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(295168067227 / 250000000000) = 1/(125000000000 / 295168067227) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11224 : Bounds (34369247 / 40000000) (859231177 / 1000000000) (Real.log (295168067227 / 125000000000)) := by
  have h := reflection_log_11224_neg
  have he : Real.log (295168067227 / 125000000000) = -Real.log (125000000000 / 295168067227) := by
    rw [show ((295168067227 / 125000000000) : ℝ) = ((125000000000 / 295168067227) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11225_neg : (340748793 / 1000000000) ≤ -Real.log (500 / 703) ∧
    -Real.log (500 / 703) ≤ (170374397 / 500000000) := by
  have h := checkLog_sound (w := (203 / 1203)) (n := 12)
    (lo := (340748793 / 1000000000)) (hi := (170374397 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((703 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(703 / 500) = 1/(500 / 703) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11225 : Bounds (340748793 / 1000000000) (170374397 / 500000000) (Real.log (703 / 500)) := by
  have h := reflection_log_11225_neg
  have he : Real.log (703 / 500) = -Real.log (500 / 703) := by
    rw [show ((703 / 500) : ℝ) = ((500 / 703) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11226_neg : (520875959 / 1000000000) ≤ -Real.log (297 / 500) ∧
    -Real.log (297 / 500) ≤ (13021899 / 25000000) := by
  have h := checkLog_sound (w := (203 / 797)) (n := 12)
    (lo := (520875959 / 1000000000)) (hi := (13021899 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 297) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500 / 297) = 1/(297 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11226 : Bounds (-13021899 / 25000000) (-520875959 / 1000000000) (Real.log (297 / 500)) := by
  have h := reflection_log_11226_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11227_neg : (405917 / 1000000000) ≤ -Real.log (500000 / 500203) ∧
    -Real.log (500000 / 500203) ≤ (202959 / 500000000) := by
  have h := checkLog_sound (w := (203 / 1000203)) (n := 12)
    (lo := (405917 / 1000000000)) (hi := (202959 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500203 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500203 / 500000) = 1/(500000 / 500203) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11227 : Bounds (405917 / 1000000000) (202959 / 500000000) (Real.log (500203 / 500000)) := by
  have h := reflection_log_11227_neg
  have he : Real.log (500203 / 500000) = -Real.log (500000 / 500203) := by
    rw [show ((500203 / 500000) : ℝ) = ((500000 / 500203) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11228_neg : (203041 / 500000000) ≤ -Real.log (499797 / 500000) ∧
    -Real.log (499797 / 500000) ≤ (406083 / 1000000000) := by
  have h := checkLog_sound (w := (203 / 999797)) (n := 12)
    (lo := (203041 / 500000000)) (hi := (406083 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499797) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499797) = 1/(499797 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11228 : Bounds (-406083 / 1000000000) (-203041 / 500000000) (Real.log (499797 / 500000)) := by
  have h := reflection_log_11228_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11229_neg : (189465147 / 1000000000) ≤ -Real.log (1000000 / 1208603) ∧
    -Real.log (1000000 / 1208603) ≤ (47366287 / 250000000) := by
  have h := checkLog_sound (w := (208603 / 2208603)) (n := 12)
    (lo := (189465147 / 1000000000)) (hi := (47366287 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1208603 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1208603 / 1000000) = 1/(1000000 / 1208603) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11229 : Bounds (189465147 / 1000000000) (47366287 / 250000000) (Real.log (1208603 / 1000000)) := by
  have h := reflection_log_11229_neg
  have he : Real.log (1208603 / 1000000) = -Real.log (1000000 / 1208603) := by
    rw [show ((1208603 / 1000000) : ℝ) = ((1000000 / 1208603) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11230_neg : (11697777 / 50000000) ≤ -Real.log (791397 / 1000000) ∧
    -Real.log (791397 / 1000000) ≤ (233955541 / 1000000000) := by
  have h := checkLog_sound (w := (208603 / 1791397)) (n := 12)
    (lo := (11697777 / 50000000)) (hi := (233955541 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 791397) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 791397) = 1/(791397 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11230 : Bounds (-233955541 / 1000000000) (-11697777 / 50000000) (Real.log (791397 / 1000000)) := by
  have h := reflection_log_11230_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11231_neg : (190243429 / 1000000000) ≤ -Real.log (125000 / 151193) ∧
    -Real.log (125000 / 151193) ≤ (19024343 / 100000000) := by
  have h := checkLog_sound (w := (26193 / 276193)) (n := 12)
    (lo := (190243429 / 1000000000)) (hi := (19024343 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((151193 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(151193 / 125000) = 1/(125000 / 151193) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11231 : Bounds (190243429 / 1000000000) (19024343 / 100000000) (Real.log (151193 / 125000)) := by
  have h := reflection_log_11231_neg
  have he : Real.log (151193 / 125000) = -Real.log (125000 / 151193) := by
    rw [show ((151193 / 125000) : ℝ) = ((125000 / 151193) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11232_neg : (58786321 / 250000000) ≤ -Real.log (98807 / 125000) ∧
    -Real.log (98807 / 125000) ≤ (47029057 / 200000000) := by
  have h := checkLog_sound (w := (26193 / 223807)) (n := 12)
    (lo := (58786321 / 250000000)) (hi := (47029057 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 98807) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 98807) = 1/(98807 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11232 : Bounds (-47029057 / 200000000) (-58786321 / 250000000) (Real.log (98807 / 125000)) := by
  have h := reflection_log_11232_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11233_neg : (8980371 / 200000000) ≤ -Real.log (14938926751 / 15625000000) ∧
    -Real.log (14938926751 / 15625000000) ≤ (1403183 / 31250000) := by
  have h := checkLog_sound (w := (686073249 / 30563926751)) (n := 12)
    (lo := (8980371 / 200000000)) (hi := (1403183 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 14938926751) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 14938926751) = 1/(14938926751 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11233 : Bounds (-1403183 / 31250000) (-8980371 / 200000000) (Real.log (14938926751 / 15625000000)) := by
  have h := reflection_log_11233_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11234_neg : (44490393 / 1000000000) ≤ -Real.log (956484788391 / 1000000000000) ∧
    -Real.log (956484788391 / 1000000000000) ≤ (22245197 / 500000000) := by
  have h := checkLog_sound (w := (43515211609 / 1956484788391)) (n := 12)
    (lo := (44490393 / 1000000000)) (hi := (22245197 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 956484788391) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 956484788391) = 1/(956484788391 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11234 : Bounds (-22245197 / 500000000) (-44490393 / 1000000000) (Real.log (956484788391 / 1000000000000)) := by
  have h := reflection_log_11234_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11235_neg : (423420687 / 1000000000) ≤ -Real.log (250000000000 / 381794156409) ∧
    -Real.log (250000000000 / 381794156409) ≤ (26463793 / 62500000) := by
  have h := checkLog_sound (w := (131794156409 / 631794156409)) (n := 12)
    (lo := (423420687 / 1000000000)) (hi := (26463793 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((381794156409 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(381794156409 / 250000000000) = 1/(250000000000 / 381794156409) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11235 : Bounds (423420687 / 1000000000) (26463793 / 62500000) (Real.log (381794156409 / 250000000000)) := by
  have h := reflection_log_11235_neg
  have he : Real.log (381794156409 / 250000000000) = -Real.log (250000000000 / 381794156409) := by
    rw [show ((381794156409 / 250000000000) : ℝ) = ((250000000000 / 381794156409) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11236_neg : (425388713 / 1000000000) ≤ -Real.log (125000000000 / 191273138543) ∧
    -Real.log (125000000000 / 191273138543) ≤ (212694357 / 500000000) := by
  have h := checkLog_sound (w := (66273138543 / 316273138543)) (n := 12)
    (lo := (425388713 / 1000000000)) (hi := (212694357 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((191273138543 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(191273138543 / 125000000000) = 1/(125000000000 / 191273138543) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11236 : Bounds (425388713 / 1000000000) (212694357 / 500000000) (Real.log (191273138543 / 125000000000)) := by
  have h := reflection_log_11236_neg
  have he : Real.log (191273138543 / 125000000000) = -Real.log (125000000000 / 191273138543) := by
    rw [show ((191273138543 / 125000000000) : ℝ) = ((125000000000 / 191273138543) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11237_neg : (34369247 / 40000000) ≤ -Real.log (500000000000 / 1180672268907) ∧
    -Real.log (500000000000 / 1180672268907) ≤ (859231177 / 1000000000) := by
  have h := checkLog_sound (w := (180672268907 / 2180672268907)) (n := 12)
    (lo := (33216799 / 200000000)) (hi := (41520999 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1180672268907 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1180672268907 / 1000000000000) = 1/(500000000000 / 1180672268907) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11237 : Bounds (34369247 / 40000000) (859231177 / 1000000000) (Real.log (1180672268907 / 500000000000)) := by
  have h := reflection_log_11237_neg
  have he : Real.log (1180672268907 / 500000000000) = -Real.log (500000000000 / 1180672268907) := by
    rw [show ((1180672268907 / 500000000000) : ℝ) = ((500000000000 / 1180672268907) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11238_neg : (53851547 / 62500000) ≤ -Real.log (250000000000 / 591750841751) ∧
    -Real.log (250000000000 / 591750841751) ≤ (430812377 / 500000000) := by
  have h := checkLog_sound (w := (91750841751 / 1091750841751)) (n := 12)
    (lo := (42119393 / 250000000)) (hi := (168477573 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((591750841751 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(591750841751 / 500000000000) = 1/(250000000000 / 591750841751) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11238 : Bounds (53851547 / 62500000) (430812377 / 500000000) (Real.log (591750841751 / 250000000000)) := by
  have h := reflection_log_11238_neg
  have he : Real.log (591750841751 / 250000000000) = -Real.log (250000000000 / 591750841751) := by
    rw [show ((591750841751 / 250000000000) : ℝ) = ((250000000000 / 591750841751) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11239_neg : (170729889 / 500000000) ≤ -Real.log (1000 / 1407) ∧
    -Real.log (1000 / 1407) ≤ (341459779 / 1000000000) := by
  have h := checkLog_sound (w := (407 / 2407)) (n := 12)
    (lo := (170729889 / 500000000)) (hi := (341459779 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1407 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1407 / 1000) = 1/(1000 / 1407) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11239 : Bounds (170729889 / 500000000) (341459779 / 1000000000) (Real.log (1407 / 1000)) := by
  have h := reflection_log_11239_neg
  have he : Real.log (1407 / 1000) = -Real.log (1000 / 1407) := by
    rw [show ((1407 / 1000) : ℝ) = ((1000 / 1407) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11240_neg : (522560879 / 1000000000) ≤ -Real.log (593 / 1000) ∧
    -Real.log (593 / 1000) ≤ (6532011 / 12500000) := by
  have h := checkLog_sound (w := (407 / 1593)) (n := 12)
    (lo := (522560879 / 1000000000)) (hi := (6532011 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 593) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 593) = 1/(593 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11240 : Bounds (-6532011 / 12500000) (-522560879 / 1000000000) (Real.log (593 / 1000)) := by
  have h := reflection_log_11240_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11241_neg : (406917 / 1000000000) ≤ -Real.log (1000000 / 1000407) ∧
    -Real.log (1000000 / 1000407) ≤ (203459 / 500000000) := by
  have h := checkLog_sound (w := (407 / 2000407)) (n := 12)
    (lo := (406917 / 1000000000)) (hi := (203459 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000407 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000407 / 1000000) = 1/(1000000 / 1000407) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11241 : Bounds (406917 / 1000000000) (203459 / 500000000) (Real.log (1000407 / 1000000)) := by
  have h := reflection_log_11241_neg
  have he : Real.log (1000407 / 1000000) = -Real.log (1000000 / 1000407) := by
    rw [show ((1000407 / 1000000) : ℝ) = ((1000000 / 1000407) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11242_neg : (203541 / 500000000) ≤ -Real.log (999593 / 1000000) ∧
    -Real.log (999593 / 1000000) ≤ (407083 / 1000000000) := by
  have h := checkLog_sound (w := (407 / 1999593)) (n := 12)
    (lo := (203541 / 500000000)) (hi := (407083 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999593) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999593) = 1/(999593 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11242 : Bounds (-407083 / 1000000000) (-203541 / 500000000) (Real.log (999593 / 1000000)) := by
  have h := reflection_log_11242_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11243_neg : (9495923 / 50000000) ≤ -Real.log (1000000 / 1209151) ∧
    -Real.log (1000000 / 1209151) ≤ (189918461 / 1000000000) := by
  have h := checkLog_sound (w := (209151 / 2209151)) (n := 12)
    (lo := (9495923 / 50000000)) (hi := (189918461 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1209151 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1209151 / 1000000) = 1/(1000000 / 1209151) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11243 : Bounds (9495923 / 50000000) (189918461 / 1000000000) (Real.log (1209151 / 1000000)) := by
  have h := reflection_log_11243_neg
  have he : Real.log (1209151 / 1000000) = -Real.log (1000000 / 1209151) := by
    rw [show ((1209151 / 1000000) : ℝ) = ((1000000 / 1209151) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11244_neg : (234648227 / 1000000000) ≤ -Real.log (790849 / 1000000) ∧
    -Real.log (790849 / 1000000) ≤ (58662057 / 250000000) := by
  have h := checkLog_sound (w := (209151 / 1790849)) (n := 12)
    (lo := (234648227 / 1000000000)) (hi := (58662057 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 790849) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 790849) = 1/(790849 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11244 : Bounds (-58662057 / 250000000) (-234648227 / 1000000000) (Real.log (790849 / 1000000)) := by
  have h := reflection_log_11244_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11245_neg : (744911 / 3906250) ≤ -Real.log (1000000 / 1210093) ∧
    -Real.log (1000000 / 1210093) ≤ (190697217 / 1000000000) := by
  have h := checkLog_sound (w := (210093 / 2210093)) (n := 12)
    (lo := (744911 / 3906250)) (hi := (190697217 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1210093 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1210093 / 1000000) = 1/(1000000 / 1210093) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11245 : Bounds (744911 / 3906250) (190697217 / 1000000000) (Real.log (1210093 / 1000000)) := by
  have h := reflection_log_11245_neg
  have he : Real.log (1210093 / 1000000) = -Real.log (1000000 / 1210093) := by
    rw [show ((1210093 / 1000000) : ℝ) = ((1000000 / 1210093) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11246_neg : (235840061 / 1000000000) ≤ -Real.log (789907 / 1000000) ∧
    -Real.log (789907 / 1000000) ≤ (117920031 / 500000000) := by
  have h := checkLog_sound (w := (210093 / 1789907)) (n := 12)
    (lo := (235840061 / 1000000000)) (hi := (117920031 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 789907) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 789907) = 1/(789907 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11246 : Bounds (-117920031 / 500000000) (-235840061 / 1000000000) (Real.log (789907 / 1000000)) := by
  have h := reflection_log_11246_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11247_neg : (9028569 / 200000000) ≤ -Real.log (955860931351 / 1000000000000) ∧
    -Real.log (955860931351 / 1000000000000) ≤ (22571423 / 500000000) := by
  have h := checkLog_sound (w := (44139068649 / 1955860931351)) (n := 12)
    (lo := (9028569 / 200000000)) (hi := (22571423 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 955860931351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 955860931351) = 1/(955860931351 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11247 : Bounds (-22571423 / 500000000) (-9028569 / 200000000) (Real.log (955860931351 / 1000000000000)) := by
  have h := reflection_log_11247_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11248_neg : (22364883 / 500000000) ≤ -Real.log (956255859199 / 1000000000000) ∧
    -Real.log (956255859199 / 1000000000000) ≤ (44729767 / 1000000000) := by
  have h := checkLog_sound (w := (43744140801 / 1956255859199)) (n := 12)
    (lo := (22364883 / 500000000)) (hi := (44729767 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 956255859199) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 956255859199) = 1/(956255859199 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11248 : Bounds (-44729767 / 1000000000) (-22364883 / 500000000) (Real.log (956255859199 / 1000000000000)) := by
  have h := reflection_log_11248_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11249_neg : (424566687 / 1000000000) ≤ -Real.log (500000000000 / 764463886279) ∧
    -Real.log (500000000000 / 764463886279) ≤ (13267709 / 31250000) := by
  have h := checkLog_sound (w := (264463886279 / 1264463886279)) (n := 12)
    (lo := (424566687 / 1000000000)) (hi := (13267709 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((764463886279 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(764463886279 / 500000000000) = 1/(500000000000 / 764463886279) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11249 : Bounds (424566687 / 1000000000) (13267709 / 31250000) (Real.log (764463886279 / 500000000000)) := by
  have h := reflection_log_11249_neg
  have he : Real.log (764463886279 / 500000000000) = -Real.log (500000000000 / 764463886279) := by
    rw [show ((764463886279 / 500000000000) : ℝ) = ((500000000000 / 764463886279) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11250_neg : (213268639 / 500000000) ≤ -Real.log (62500000000 / 95746477117) ∧
    -Real.log (62500000000 / 95746477117) ≤ (426537279 / 1000000000) := by
  have h := checkLog_sound (w := (33246477117 / 158246477117)) (n := 12)
    (lo := (213268639 / 500000000)) (hi := (426537279 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((95746477117 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(95746477117 / 62500000000) = 1/(62500000000 / 95746477117) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11250 : Bounds (213268639 / 500000000) (426537279 / 1000000000) (Real.log (95746477117 / 62500000000)) := by
  have h := reflection_log_11250_neg
  have he : Real.log (95746477117 / 62500000000) = -Real.log (62500000000 / 95746477117) := by
    rw [show ((95746477117 / 62500000000) : ℝ) = ((62500000000 / 95746477117) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11251_neg : (53851547 / 62500000) ≤ -Real.log (500000000000 / 1183501683501) ∧
    -Real.log (500000000000 / 1183501683501) ≤ (430812377 / 500000000) := by
  have h := checkLog_sound (w := (183501683501 / 2183501683501)) (n := 12)
    (lo := (42119393 / 250000000)) (hi := (168477573 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1183501683501 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1183501683501 / 1000000000000) = 1/(500000000000 / 1183501683501) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11251 : Bounds (53851547 / 62500000) (430812377 / 500000000) (Real.log (1183501683501 / 500000000000)) := by
  have h := reflection_log_11251_neg
  have he : Real.log (1183501683501 / 500000000000) = -Real.log (500000000000 / 1183501683501) := by
    rw [show ((1183501683501 / 500000000000) : ℝ) = ((500000000000 / 1183501683501) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11252_neg : (864020657 / 1000000000) ≤ -Real.log (50000000000 / 118634064081) ∧
    -Real.log (50000000000 / 118634064081) ≤ (864020659 / 1000000000) := by
  have h := checkLog_sound (w := (18634064081 / 218634064081)) (n := 12)
    (lo := (170873477 / 1000000000)) (hi := (85436739 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((118634064081 / 100000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(118634064081 / 100000000000) = 1/(50000000000 / 118634064081) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11252 : Bounds (864020657 / 1000000000) (864020659 / 1000000000) (Real.log (118634064081 / 50000000000)) := by
  have h := reflection_log_11252_neg
  have he : Real.log (118634064081 / 50000000000) = -Real.log (50000000000 / 118634064081) := by
    rw [show ((118634064081 / 50000000000) : ℝ) = ((50000000000 / 118634064081) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11253_neg : (342170257 / 1000000000) ≤ -Real.log (125 / 176) ∧
    -Real.log (125 / 176) ≤ (171085129 / 500000000) := by
  have h := checkLog_sound (w := (51 / 301)) (n := 12)
    (lo := (342170257 / 1000000000)) (hi := (171085129 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((176 / 125) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(176 / 125) = 1/(125 / 176) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11253 : Bounds (342170257 / 1000000000) (171085129 / 500000000) (Real.log (176 / 125)) := by
  have h := reflection_log_11253_neg
  have he : Real.log (176 / 125) = -Real.log (125 / 176) := by
    rw [show ((176 / 125) : ℝ) = ((125 / 176) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11254_neg : (131062161 / 250000000) ≤ -Real.log (74 / 125) ∧
    -Real.log (74 / 125) ≤ (104849729 / 200000000) := by
  have h := checkLog_sound (w := (51 / 199)) (n := 12)
    (lo := (131062161 / 250000000)) (hi := (104849729 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 74) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125 / 74) = 1/(74 / 125) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11254 : Bounds (-104849729 / 200000000) (-131062161 / 250000000) (Real.log (74 / 125)) := by
  have h := reflection_log_11254_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11255_neg : (101979 / 250000000) ≤ -Real.log (125000 / 125051) ∧
    -Real.log (125000 / 125051) ≤ (407917 / 1000000000) := by
  have h := checkLog_sound (w := (51 / 250051)) (n := 12)
    (lo := (101979 / 250000000)) (hi := (407917 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125051 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125051 / 125000) = 1/(125000 / 125051) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11255 : Bounds (101979 / 250000000) (407917 / 1000000000) (Real.log (125051 / 125000)) := by
  have h := reflection_log_11255_neg
  have he : Real.log (125051 / 125000) = -Real.log (125000 / 125051) := by
    rw [show ((125051 / 125000) : ℝ) = ((125000 / 125051) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11256_neg : (408083 / 1000000000) ≤ -Real.log (124949 / 125000) ∧
    -Real.log (124949 / 125000) ≤ (102021 / 250000000) := by
  have h := checkLog_sound (w := (51 / 249949)) (n := 12)
    (lo := (408083 / 1000000000)) (hi := (102021 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 124949) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 124949) = 1/(124949 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11256 : Bounds (-102021 / 250000000) (-408083 / 1000000000) (Real.log (124949 / 125000)) := by
  have h := reflection_log_11256_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11257_neg : (11898223 / 62500000) ≤ -Real.log (1000000 / 1209699) ∧
    -Real.log (1000000 / 1209699) ≤ (190371569 / 1000000000) := by
  have h := checkLog_sound (w := (209699 / 2209699)) (n := 12)
    (lo := (11898223 / 62500000)) (hi := (190371569 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1209699 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1209699 / 1000000) = 1/(1000000 / 1209699) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11257 : Bounds (11898223 / 62500000) (190371569 / 1000000000) (Real.log (1209699 / 1000000)) := by
  have h := reflection_log_11257_neg
  have he : Real.log (1209699 / 1000000) = -Real.log (1000000 / 1209699) := by
    rw [show ((1209699 / 1000000) : ℝ) = ((1000000 / 1209699) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11258_neg : (235341393 / 1000000000) ≤ -Real.log (790301 / 1000000) ∧
    -Real.log (790301 / 1000000) ≤ (117670697 / 500000000) := by
  have h := checkLog_sound (w := (209699 / 1790301)) (n := 12)
    (lo := (235341393 / 1000000000)) (hi := (117670697 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 790301) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 790301) = 1/(790301 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11258 : Bounds (-117670697 / 500000000) (-235341393 / 1000000000) (Real.log (790301 / 1000000)) := by
  have h := reflection_log_11258_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11259_neg : (191151623 / 1000000000) ≤ -Real.log (1000000 / 1210643) ∧
    -Real.log (1000000 / 1210643) ≤ (23893953 / 125000000) := by
  have h := checkLog_sound (w := (210643 / 2210643)) (n := 12)
    (lo := (191151623 / 1000000000)) (hi := (23893953 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1210643 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1210643 / 1000000) = 1/(1000000 / 1210643) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11259 : Bounds (191151623 / 1000000000) (23893953 / 125000000) (Real.log (1210643 / 1000000)) := by
  have h := reflection_log_11259_neg
  have he : Real.log (1210643 / 1000000) = -Real.log (1000000 / 1210643) := by
    rw [show ((1210643 / 1000000) : ℝ) = ((1000000 / 1210643) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11260_neg : (59134147 / 250000000) ≤ -Real.log (789357 / 1000000) ∧
    -Real.log (789357 / 1000000) ≤ (236536589 / 1000000000) := by
  have h := checkLog_sound (w := (210643 / 1789357)) (n := 12)
    (lo := (59134147 / 250000000)) (hi := (236536589 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 789357) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 789357) = 1/(789357 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11260 : Bounds (-236536589 / 1000000000) (-59134147 / 250000000) (Real.log (789357 / 1000000)) := by
  have h := reflection_log_11260_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11261_neg : (9076993 / 200000000) ≤ -Real.log (955629526551 / 1000000000000) ∧
    -Real.log (955629526551 / 1000000000000) ≤ (22692483 / 500000000) := by
  have h := checkLog_sound (w := (44370473449 / 1955629526551)) (n := 12)
    (lo := (9076993 / 200000000)) (hi := (22692483 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 955629526551) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 955629526551) = 1/(955629526551 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11261 : Bounds (-22692483 / 500000000) (-9076993 / 200000000) (Real.log (955629526551 / 1000000000000)) := by
  have h := reflection_log_11261_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11262_neg : (1798793 / 40000000) ≤ -Real.log (956026329399 / 1000000000000) ∧
    -Real.log (956026329399 / 1000000000000) ≤ (22484913 / 500000000) := by
  have h := checkLog_sound (w := (43973670601 / 1956026329399)) (n := 12)
    (lo := (1798793 / 40000000)) (hi := (22484913 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 956026329399) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 956026329399) = 1/(956026329399 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11262 : Bounds (-22484913 / 500000000) (-1798793 / 40000000) (Real.log (956026329399 / 1000000000000)) := by
  have h := reflection_log_11262_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11263_neg : (425712961 / 1000000000) ≤ -Real.log (125000000000 / 191335168499) ∧
    -Real.log (125000000000 / 191335168499) ≤ (212856481 / 500000000) := by
  have h := checkLog_sound (w := (66335168499 / 316335168499)) (n := 12)
    (lo := (425712961 / 1000000000)) (hi := (212856481 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((191335168499 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(191335168499 / 125000000000) = 1/(125000000000 / 191335168499) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11263 : Bounds (425712961 / 1000000000) (212856481 / 500000000) (Real.log (191335168499 / 125000000000)) := by
  have h := reflection_log_11263_neg
  have he : Real.log (191335168499 / 125000000000) = -Real.log (125000000000 / 191335168499) := by
    rw [show ((191335168499 / 125000000000) : ℝ) = ((125000000000 / 191335168499) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily
