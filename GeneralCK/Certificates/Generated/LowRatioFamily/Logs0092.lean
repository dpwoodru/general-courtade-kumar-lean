import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_5888_neg : (193907301 / 1000000000) ≤ -Real.log (250000000000 / 303495935679) ∧
    -Real.log (250000000000 / 303495935679) ≤ (96953651 / 500000000) := by
  have h := checkLog_sound (w := (53495935679 / 553495935679)) (n := 12)
    (lo := (193907301 / 1000000000)) (hi := (96953651 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((303495935679 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(303495935679 / 250000000000) = 1/(250000000000 / 303495935679) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5888 : Bounds (193907301 / 1000000000) (96953651 / 500000000) (Real.log (303495935679 / 250000000000)) := by
  have h := reflection_log_5888_neg
  have he : Real.log (303495935679 / 250000000000) = -Real.log (250000000000 / 303495935679) := by
    rw [show ((303495935679 / 250000000000) : ℝ) = ((250000000000 / 303495935679) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5889_neg : (38879579 / 200000000) ≤ -Real.log (500000000000 / 607289731217) ∧
    -Real.log (500000000000 / 607289731217) ≤ (24299737 / 125000000) := by
  have h := checkLog_sound (w := (107289731217 / 1107289731217)) (n := 12)
    (lo := (38879579 / 200000000)) (hi := (24299737 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((607289731217 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(607289731217 / 500000000000) = 1/(500000000000 / 607289731217) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5889 : Bounds (38879579 / 200000000) (24299737 / 125000000) (Real.log (607289731217 / 500000000000)) := by
  have h := reflection_log_5889_neg
  have he : Real.log (607289731217 / 500000000000) = -Real.log (500000000000 / 607289731217) := by
    rw [show ((607289731217 / 500000000000) : ℝ) = ((500000000000 / 607289731217) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5890_neg : (77848223 / 200000000) ≤ -Real.log (500000000000 / 737930180737) ∧
    -Real.log (500000000000 / 737930180737) ≤ (97310279 / 250000000) := by
  have h := checkLog_sound (w := (237930180737 / 1237930180737)) (n := 12)
    (lo := (77848223 / 200000000)) (hi := (97310279 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((737930180737 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(737930180737 / 500000000000) = 1/(500000000000 / 737930180737) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5890 : Bounds (77848223 / 200000000) (97310279 / 250000000) (Real.log (737930180737 / 500000000000)) := by
  have h := reflection_log_5890_neg
  have he : Real.log (737930180737 / 500000000000) = -Real.log (500000000000 / 737930180737) := by
    rw [show ((737930180737 / 500000000000) : ℝ) = ((500000000000 / 737930180737) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5891_neg : (389448791 / 1000000000) ≤ -Real.log (20000000000 / 29523337873) ∧
    -Real.log (20000000000 / 29523337873) ≤ (48681099 / 125000000) := by
  have h := checkLog_sound (w := (9523337873 / 49523337873)) (n := 12)
    (lo := (389448791 / 1000000000)) (hi := (48681099 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((29523337873 / 20000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(29523337873 / 20000000000) = 1/(20000000000 / 29523337873) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5891 : Bounds (389448791 / 1000000000) (48681099 / 125000000) (Real.log (29523337873 / 20000000000)) := by
  have h := reflection_log_5891_neg
  have he : Real.log (29523337873 / 20000000000) = -Real.log (20000000000 / 29523337873) := by
    rw [show ((29523337873 / 20000000000) : ℝ) = ((20000000000 / 29523337873) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5892_neg : (87984041 / 500000000) ≤ -Real.log (2500 / 2981) ∧
    -Real.log (2500 / 2981) ≤ (175968083 / 1000000000) := by
  have h := checkLog_sound (w := (481 / 5481)) (n := 12)
    (lo := (87984041 / 500000000)) (hi := (175968083 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2981 / 2500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2981 / 2500) = 1/(2500 / 2981) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5892 : Bounds (87984041 / 500000000) (175968083 / 1000000000) (Real.log (2981 / 2500)) := by
  have h := reflection_log_5892_neg
  have he : Real.log (2981 / 2500) = -Real.log (2500 / 2981) := by
    rw [show ((2981 / 2500) : ℝ) = ((2500 / 2981) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5893_neg : (26711049 / 125000000) ≤ -Real.log (2019 / 2500) ∧
    -Real.log (2019 / 2500) ≤ (213688393 / 1000000000) := by
  have h := checkLog_sound (w := (481 / 4519)) (n := 12)
    (lo := (26711049 / 125000000)) (hi := (213688393 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500 / 2019) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500 / 2019) = 1/(2019 / 2500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5893 : Bounds (-213688393 / 1000000000) (-26711049 / 125000000) (Real.log (2019 / 2500)) := by
  have h := reflection_log_5893_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5894_neg : (192381 / 1000000000) ≤ -Real.log (2500000 / 2500481) ∧
    -Real.log (2500000 / 2500481) ≤ (96191 / 500000000) := by
  have h := checkLog_sound (w := (481 / 5000481)) (n := 12)
    (lo := (192381 / 1000000000)) (hi := (96191 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500481 / 2500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500481 / 2500000) = 1/(2500000 / 2500481) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5894 : Bounds (192381 / 1000000000) (96191 / 500000000) (Real.log (2500481 / 2500000)) := by
  have h := reflection_log_5894_neg
  have he : Real.log (2500481 / 2500000) = -Real.log (2500000 / 2500481) := by
    rw [show ((2500481 / 2500000) : ℝ) = ((2500000 / 2500481) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5895_neg : (96209 / 500000000) ≤ -Real.log (2499519 / 2500000) ∧
    -Real.log (2499519 / 2500000) ≤ (192419 / 1000000000) := by
  have h := checkLog_sound (w := (481 / 4999519)) (n := 12)
    (lo := (96209 / 500000000)) (hi := (192419 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000 / 2499519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000 / 2499519) = 1/(2499519 / 2500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5895 : Bounds (-192419 / 1000000000) (-96209 / 500000000) (Real.log (2499519 / 2500000)) := by
  have h := reflection_log_5895_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5896_neg : (46153747 / 500000000) ≤ -Real.log (500000 / 548351) ∧
    -Real.log (500000 / 548351) ≤ (18461499 / 200000000) := by
  have h := checkLog_sound (w := (48351 / 1048351)) (n := 12)
    (lo := (46153747 / 500000000)) (hi := (18461499 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((548351 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(548351 / 500000) = 1/(500000 / 548351) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5896 : Bounds (46153747 / 500000000) (18461499 / 200000000) (Real.log (548351 / 500000)) := by
  have h := reflection_log_5896_neg
  have he : Real.log (548351 / 500000) = -Real.log (500000 / 548351) := by
    rw [show ((548351 / 500000) : ℝ) = ((500000 / 548351) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5897_neg : (6356423 / 62500000) ≤ -Real.log (451649 / 500000) ∧
    -Real.log (451649 / 500000) ≤ (101702769 / 1000000000) := by
  have h := checkLog_sound (w := (48351 / 951649)) (n := 12)
    (lo := (6356423 / 62500000)) (hi := (101702769 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 451649) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 451649) = 1/(451649 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5897 : Bounds (-101702769 / 1000000000) (-6356423 / 62500000) (Real.log (451649 / 500000)) := by
  have h := reflection_log_5897_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5898_neg : (92529043 / 1000000000) ≤ -Real.log (200000 / 219389) ∧
    -Real.log (200000 / 219389) ≤ (23132261 / 250000000) := by
  have h := checkLog_sound (w := (19389 / 419389)) (n := 12)
    (lo := (92529043 / 1000000000)) (hi := (23132261 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((219389 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(219389 / 200000) = 1/(200000 / 219389) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5898 : Bounds (92529043 / 1000000000) (23132261 / 250000000) (Real.log (219389 / 200000)) := by
  have h := reflection_log_5898_neg
  have he : Real.log (219389 / 200000) = -Real.log (200000 / 219389) := by
    rw [show ((219389 / 200000) : ℝ) = ((200000 / 219389) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5899_neg : (101971819 / 1000000000) ≤ -Real.log (180611 / 200000) ∧
    -Real.log (180611 / 200000) ≤ (5098591 / 50000000) := by
  have h := checkLog_sound (w := (19389 / 380611)) (n := 12)
    (lo := (101971819 / 1000000000)) (hi := (5098591 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 180611) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 180611) = 1/(180611 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5899 : Bounds (-5098591 / 50000000) (-101971819 / 1000000000) (Real.log (180611 / 200000)) := by
  have h := reflection_log_5899_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5900_neg : (1180347 / 125000000) ≤ -Real.log (39624066679 / 40000000000) ∧
    -Real.log (39624066679 / 40000000000) ≤ (9442777 / 1000000000) := by
  have h := checkLog_sound (w := (375933321 / 79624066679)) (n := 12)
    (lo := (1180347 / 125000000)) (hi := (9442777 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39624066679) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39624066679) = 1/(39624066679 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5900 : Bounds (-9442777 / 1000000000) (-1180347 / 125000000) (Real.log (39624066679 / 40000000000)) := by
  have h := reflection_log_5900_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5901_neg : (4697637 / 500000000) ≤ -Real.log (247662180799 / 250000000000) ∧
    -Real.log (247662180799 / 250000000000) ≤ (375811 / 40000000) := by
  have h := checkLog_sound (w := (2337819201 / 497662180799)) (n := 12)
    (lo := (4697637 / 500000000)) (hi := (375811 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247662180799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247662180799) = 1/(247662180799 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5901 : Bounds (-375811 / 40000000) (-4697637 / 500000000) (Real.log (247662180799 / 250000000000)) := by
  have h := reflection_log_5901_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5902_neg : (194010263 / 1000000000) ≤ -Real.log (125000000000 / 151763592967) ∧
    -Real.log (125000000000 / 151763592967) ≤ (24251283 / 125000000) := by
  have h := checkLog_sound (w := (26763592967 / 276763592967)) (n := 12)
    (lo := (194010263 / 1000000000)) (hi := (24251283 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((151763592967 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(151763592967 / 125000000000) = 1/(125000000000 / 151763592967) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5902 : Bounds (194010263 / 1000000000) (24251283 / 125000000) (Real.log (151763592967 / 125000000000)) := by
  have h := reflection_log_5902_neg
  have he : Real.log (151763592967 / 125000000000) = -Real.log (125000000000 / 151763592967) := by
    rw [show ((151763592967 / 125000000000) : ℝ) = ((125000000000 / 151763592967) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5903_neg : (97250431 / 500000000) ≤ -Real.log (250000000000 / 303676132683) ∧
    -Real.log (250000000000 / 303676132683) ≤ (194500863 / 1000000000) := by
  have h := checkLog_sound (w := (53676132683 / 553676132683)) (n := 12)
    (lo := (97250431 / 500000000)) (hi := (194500863 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((303676132683 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(303676132683 / 250000000000) = 1/(250000000000 / 303676132683) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5903 : Bounds (97250431 / 500000000) (194500863 / 1000000000) (Real.log (303676132683 / 250000000000)) := by
  have h := reflection_log_5903_neg
  have he : Real.log (303676132683 / 250000000000) = -Real.log (250000000000 / 303676132683) := by
    rw [show ((303676132683 / 250000000000) : ℝ) = ((250000000000 / 303676132683) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5904_neg : (389448791 / 1000000000) ≤ -Real.log (62500000000 / 92260430853) ∧
    -Real.log (62500000000 / 92260430853) ≤ (48681099 / 125000000) := by
  have h := checkLog_sound (w := (29760430853 / 154760430853)) (n := 12)
    (lo := (389448791 / 1000000000)) (hi := (48681099 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((92260430853 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(92260430853 / 62500000000) = 1/(62500000000 / 92260430853) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5904 : Bounds (389448791 / 1000000000) (48681099 / 125000000) (Real.log (92260430853 / 62500000000)) := by
  have h := reflection_log_5904_neg
  have he : Real.log (92260430853 / 62500000000) = -Real.log (62500000000 / 92260430853) := by
    rw [show ((92260430853 / 62500000000) : ℝ) = ((62500000000 / 92260430853) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5905_neg : (15586259 / 40000000) ≤ -Real.log (500000000000 / 738236750867) ∧
    -Real.log (500000000000 / 738236750867) ≤ (97414119 / 250000000) := by
  have h := checkLog_sound (w := (238236750867 / 1238236750867)) (n := 12)
    (lo := (15586259 / 40000000)) (hi := (97414119 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((738236750867 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(738236750867 / 500000000000) = 1/(500000000000 / 738236750867) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5905 : Bounds (15586259 / 40000000) (97414119 / 250000000) (Real.log (738236750867 / 500000000000)) := by
  have h := reflection_log_5905_neg
  have he : Real.log (738236750867 / 500000000000) = -Real.log (500000000000 / 738236750867) := by
    rw [show ((738236750867 / 500000000000) : ℝ) = ((500000000000 / 738236750867) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5906_neg : (176051943 / 1000000000) ≤ -Real.log (400 / 477) ∧
    -Real.log (400 / 477) ≤ (22006493 / 125000000) := by
  have h := checkLog_sound (w := (77 / 877)) (n := 12)
    (lo := (176051943 / 1000000000)) (hi := (22006493 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((477 / 400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(477 / 400) = 1/(400 / 477) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5906 : Bounds (176051943 / 1000000000) (22006493 / 125000000) (Real.log (477 / 400)) := by
  have h := reflection_log_5906_neg
  have he : Real.log (477 / 400) = -Real.log (400 / 477) := by
    rw [show ((477 / 400) : ℝ) = ((400 / 477) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5907_neg : (213812223 / 1000000000) ≤ -Real.log (323 / 400) ∧
    -Real.log (323 / 400) ≤ (417602 / 1953125) := by
  have h := checkLog_sound (w := (77 / 723)) (n := 12)
    (lo := (213812223 / 1000000000)) (hi := (417602 / 1953125))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 323) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400 / 323) = 1/(323 / 400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5907 : Bounds (-417602 / 1953125) (-213812223 / 1000000000) (Real.log (323 / 400)) := by
  have h := reflection_log_5907_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5908_neg : (192481 / 1000000000) ≤ -Real.log (400000 / 400077) ∧
    -Real.log (400000 / 400077) ≤ (96241 / 500000000) := by
  have h := checkLog_sound (w := (77 / 800077)) (n := 12)
    (lo := (192481 / 1000000000)) (hi := (96241 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400077 / 400000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400077 / 400000) = 1/(400000 / 400077) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5908 : Bounds (192481 / 1000000000) (96241 / 500000000) (Real.log (400077 / 400000)) := by
  have h := reflection_log_5908_neg
  have he : Real.log (400077 / 400000) = -Real.log (400000 / 400077) := by
    rw [show ((400077 / 400000) : ℝ) = ((400000 / 400077) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5909_neg : (96259 / 500000000) ≤ -Real.log (399923 / 400000) ∧
    -Real.log (399923 / 400000) ≤ (192519 / 1000000000) := by
  have h := checkLog_sound (w := (77 / 799923)) (n := 12)
    (lo := (96259 / 500000000)) (hi := (192519 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400000 / 399923) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400000 / 399923) = 1/(399923 / 400000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5909 : Bounds (-192519 / 1000000000) (-96259 / 500000000) (Real.log (399923 / 400000)) := by
  have h := reflection_log_5909_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5910_neg : (23088499 / 250000000) ≤ -Real.log (1000000 / 1096753) ∧
    -Real.log (1000000 / 1096753) ≤ (92353997 / 1000000000) := by
  have h := checkLog_sound (w := (96753 / 2096753)) (n := 12)
    (lo := (23088499 / 250000000)) (hi := (92353997 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1096753 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1096753 / 1000000) = 1/(1000000 / 1096753) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5910 : Bounds (23088499 / 250000000) (92353997 / 1000000000) (Real.log (1096753 / 1000000)) := by
  have h := reflection_log_5910_neg
  have he : Real.log (1096753 / 1000000) = -Real.log (1000000 / 1096753) := by
    rw [show ((1096753 / 1000000) : ℝ) = ((1000000 / 1096753) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5911_neg : (10175923 / 100000000) ≤ -Real.log (903247 / 1000000) ∧
    -Real.log (903247 / 1000000) ≤ (101759231 / 1000000000) := by
  have h := checkLog_sound (w := (96753 / 1903247)) (n := 12)
    (lo := (10175923 / 100000000)) (hi := (101759231 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 903247) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 903247) = 1/(903247 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5911 : Bounds (-101759231 / 1000000000) (-10175923 / 100000000) (Real.log (903247 / 1000000)) := by
  have h := reflection_log_5911_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5912_neg : (46287767 / 500000000) ≤ -Real.log (250000 / 274249) ∧
    -Real.log (250000 / 274249) ≤ (18515107 / 200000000) := by
  have h := checkLog_sound (w := (24249 / 524249)) (n := 12)
    (lo := (46287767 / 500000000)) (hi := (18515107 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((274249 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(274249 / 250000) = 1/(250000 / 274249) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5912 : Bounds (46287767 / 500000000) (18515107 / 200000000) (Real.log (274249 / 250000)) := by
  have h := reflection_log_5912_neg
  have he : Real.log (274249 / 250000) = -Real.log (250000 / 274249) := by
    rw [show ((274249 / 250000) : ℝ) = ((250000 / 274249) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5913_neg : (20405659 / 200000000) ≤ -Real.log (225751 / 250000) ∧
    -Real.log (225751 / 250000) ≤ (12753537 / 125000000) := by
  have h := checkLog_sound (w := (24249 / 475751)) (n := 12)
    (lo := (20405659 / 200000000)) (hi := (12753537 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 225751) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 225751) = 1/(225751 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5913 : Bounds (-12753537 / 125000000) (-20405659 / 200000000) (Real.log (225751 / 250000)) := by
  have h := reflection_log_5913_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5914_neg : (236319 / 25000000) ≤ -Real.log (61911985999 / 62500000000) ∧
    -Real.log (61911985999 / 62500000000) ≤ (9452761 / 1000000000) := by
  have h := checkLog_sound (w := (588014001 / 124411985999)) (n := 12)
    (lo := (236319 / 25000000)) (hi := (9452761 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 61911985999) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 61911985999) = 1/(61911985999 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5914 : Bounds (-9452761 / 1000000000) (-236319 / 25000000) (Real.log (61911985999 / 62500000000)) := by
  have h := reflection_log_5914_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5915_neg : (9405233 / 1000000000) ≤ -Real.log (990638856991 / 1000000000000) ∧
    -Real.log (990638856991 / 1000000000000) ≤ (4702617 / 500000000) := by
  have h := checkLog_sound (w := (9361143009 / 1990638856991)) (n := 12)
    (lo := (9405233 / 1000000000)) (hi := (4702617 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 990638856991) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 990638856991) = 1/(990638856991 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5915 : Bounds (-4702617 / 500000000) (-9405233 / 1000000000) (Real.log (990638856991 / 1000000000000)) := by
  have h := reflection_log_5915_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5916_neg : (97056613 / 500000000) ≤ -Real.log (125000000000 / 151779219859) ∧
    -Real.log (125000000000 / 151779219859) ≤ (194113227 / 1000000000) := by
  have h := checkLog_sound (w := (26779219859 / 276779219859)) (n := 12)
    (lo := (97056613 / 500000000)) (hi := (194113227 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((151779219859 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(151779219859 / 125000000000) = 1/(125000000000 / 151779219859) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5916 : Bounds (97056613 / 500000000) (194113227 / 1000000000) (Real.log (151779219859 / 125000000000)) := by
  have h := reflection_log_5916_neg
  have he : Real.log (151779219859 / 125000000000) = -Real.log (125000000000 / 151779219859) := by
    rw [show ((151779219859 / 125000000000) : ℝ) = ((125000000000 / 151779219859) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5917_neg : (19460383 / 100000000) ≤ -Real.log (500000000000 / 607414806579) ∧
    -Real.log (500000000000 / 607414806579) ≤ (194603831 / 1000000000) := by
  have h := checkLog_sound (w := (107414806579 / 1107414806579)) (n := 12)
    (lo := (19460383 / 100000000)) (hi := (194603831 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((607414806579 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(607414806579 / 500000000000) = 1/(500000000000 / 607414806579) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5917 : Bounds (19460383 / 100000000) (194603831 / 1000000000) (Real.log (607414806579 / 500000000000)) := by
  have h := reflection_log_5917_neg
  have he : Real.log (607414806579 / 500000000000) = -Real.log (500000000000 / 607414806579) := by
    rw [show ((607414806579 / 500000000000) : ℝ) = ((500000000000 / 607414806579) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5918_neg : (15586259 / 40000000) ≤ -Real.log (250000000000 / 369118375433) ∧
    -Real.log (250000000000 / 369118375433) ≤ (97414119 / 250000000) := by
  have h := checkLog_sound (w := (119118375433 / 619118375433)) (n := 12)
    (lo := (15586259 / 40000000)) (hi := (97414119 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((369118375433 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(369118375433 / 250000000000) = 1/(250000000000 / 369118375433) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5918 : Bounds (15586259 / 40000000) (97414119 / 250000000) (Real.log (369118375433 / 250000000000)) := by
  have h := reflection_log_5918_neg
  have he : Real.log (369118375433 / 250000000000) = -Real.log (250000000000 / 369118375433) := by
    rw [show ((369118375433 / 250000000000) : ℝ) = ((250000000000 / 369118375433) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5919_neg : (389864167 / 1000000000) ≤ -Real.log (6250000000 / 9229876161) ∧
    -Real.log (6250000000 / 9229876161) ≤ (48733021 / 125000000) := by
  have h := checkLog_sound (w := (2979876161 / 15479876161)) (n := 12)
    (lo := (389864167 / 1000000000)) (hi := (48733021 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9229876161 / 6250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(9229876161 / 6250000000) = 1/(6250000000 / 9229876161) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5919 : Bounds (389864167 / 1000000000) (48733021 / 125000000) (Real.log (9229876161 / 6250000000)) := by
  have h := reflection_log_5919_neg
  have he : Real.log (9229876161 / 6250000000) = -Real.log (6250000000 / 9229876161) := by
    rw [show ((9229876161 / 6250000000) : ℝ) = ((6250000000 / 9229876161) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5920_neg : (176135797 / 1000000000) ≤ -Real.log (5000 / 5963) ∧
    -Real.log (5000 / 5963) ≤ (88067899 / 500000000) := by
  have h := checkLog_sound (w := (963 / 10963)) (n := 12)
    (lo := (176135797 / 1000000000)) (hi := (88067899 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5963 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5963 / 5000) = 1/(5000 / 5963) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5920 : Bounds (176135797 / 1000000000) (88067899 / 500000000) (Real.log (5963 / 5000)) := by
  have h := reflection_log_5920_neg
  have he : Real.log (5963 / 5000) = -Real.log (5000 / 5963) := by
    rw [show ((5963 / 5000) : ℝ) = ((5000 / 5963) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5921_neg : (21393607 / 100000000) ≤ -Real.log (4037 / 5000) ∧
    -Real.log (4037 / 5000) ≤ (213936071 / 1000000000) := by
  have h := checkLog_sound (w := (963 / 9037)) (n := 12)
    (lo := (21393607 / 100000000)) (hi := (213936071 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4037) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4037) = 1/(4037 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5921 : Bounds (-213936071 / 1000000000) (-21393607 / 100000000) (Real.log (4037 / 5000)) := by
  have h := reflection_log_5921_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5922_neg : (192581 / 1000000000) ≤ -Real.log (5000000 / 5000963) ∧
    -Real.log (5000000 / 5000963) ≤ (96291 / 500000000) := by
  have h := checkLog_sound (w := (963 / 10000963)) (n := 12)
    (lo := (192581 / 1000000000)) (hi := (96291 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000963 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000963 / 5000000) = 1/(5000000 / 5000963) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5922 : Bounds (192581 / 1000000000) (96291 / 500000000) (Real.log (5000963 / 5000000)) := by
  have h := reflection_log_5922_neg
  have he : Real.log (5000963 / 5000000) = -Real.log (5000000 / 5000963) := by
    rw [show ((5000963 / 5000000) : ℝ) = ((5000000 / 5000963) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5923_neg : (96309 / 500000000) ≤ -Real.log (4999037 / 5000000) ∧
    -Real.log (4999037 / 5000000) ≤ (192619 / 1000000000) := by
  have h := checkLog_sound (w := (963 / 9999037)) (n := 12)
    (lo := (96309 / 500000000)) (hi := (192619 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999037) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999037) = 1/(4999037 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5923 : Bounds (-192619 / 1000000000) (-96309 / 500000000) (Real.log (4999037 / 5000000)) := by
  have h := reflection_log_5923_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5924_neg : (5775031 / 62500000) ≤ -Real.log (250000 / 274201) ∧
    -Real.log (250000 / 274201) ≤ (92400497 / 1000000000) := by
  have h := checkLog_sound (w := (24201 / 524201)) (n := 12)
    (lo := (5775031 / 62500000)) (hi := (92400497 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((274201 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(274201 / 250000) = 1/(250000 / 274201) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5924 : Bounds (5775031 / 62500000) (92400497 / 1000000000) (Real.log (274201 / 250000)) := by
  have h := reflection_log_5924_neg
  have he : Real.log (274201 / 250000) = -Real.log (250000 / 274201) := by
    rw [show ((274201 / 250000) : ℝ) = ((250000 / 274201) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5925_neg : (50907847 / 500000000) ≤ -Real.log (225799 / 250000) ∧
    -Real.log (225799 / 250000) ≤ (20363139 / 200000000) := by
  have h := checkLog_sound (w := (24201 / 475799)) (n := 12)
    (lo := (50907847 / 500000000)) (hi := (20363139 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 225799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 225799) = 1/(225799 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5925 : Bounds (-20363139 / 200000000) (-50907847 / 500000000) (Real.log (225799 / 250000)) := by
  have h := reflection_log_5925_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5926_neg : (11577753 / 125000000) ≤ -Real.log (1000000 / 1097047) ∧
    -Real.log (1000000 / 1097047) ≤ (3704881 / 40000000) := by
  have h := checkLog_sound (w := (97047 / 2097047)) (n := 12)
    (lo := (11577753 / 125000000)) (hi := (3704881 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1097047 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1097047 / 1000000) = 1/(1000000 / 1097047) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5926 : Bounds (11577753 / 125000000) (3704881 / 40000000) (Real.log (1097047 / 1000000)) := by
  have h := reflection_log_5926_neg
  have he : Real.log (1097047 / 1000000) = -Real.log (1000000 / 1097047) := by
    rw [show ((1097047 / 1000000) : ℝ) = ((1000000 / 1097047) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5927_neg : (4083391 / 40000000) ≤ -Real.log (902953 / 1000000) ∧
    -Real.log (902953 / 1000000) ≤ (12760597 / 125000000) := by
  have h := checkLog_sound (w := (97047 / 1902953)) (n := 12)
    (lo := (4083391 / 40000000)) (hi := (12760597 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 902953) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 902953) = 1/(902953 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5927 : Bounds (-12760597 / 125000000) (-4083391 / 40000000) (Real.log (902953 / 1000000)) := by
  have h := reflection_log_5927_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5928_neg : (9462751 / 1000000000) ≤ -Real.log (990581879791 / 1000000000000) ∧
    -Real.log (990581879791 / 1000000000000) ≤ (295711 / 31250000) := by
  have h := checkLog_sound (w := (9418120209 / 1990581879791)) (n := 12)
    (lo := (9462751 / 1000000000)) (hi := (295711 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 990581879791) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 990581879791) = 1/(990581879791 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5928 : Bounds (-295711 / 31250000) (-9462751 / 1000000000) (Real.log (990581879791 / 1000000000000)) := by
  have h := reflection_log_5928_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5929_neg : (4707599 / 500000000) ≤ -Real.log (61914311599 / 62500000000) ∧
    -Real.log (61914311599 / 62500000000) ≤ (9415199 / 1000000000) := by
  have h := checkLog_sound (w := (585688401 / 124414311599)) (n := 12)
    (lo := (4707599 / 500000000)) (hi := (9415199 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 61914311599) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 61914311599) = 1/(61914311599 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5929 : Bounds (-9415199 / 1000000000) (-4707599 / 500000000) (Real.log (61914311599 / 62500000000)) := by
  have h := reflection_log_5929_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5930_neg : (194216191 / 1000000000) ≤ -Real.log (250000000000 / 303589697031) ∧
    -Real.log (250000000000 / 303589697031) ≤ (758657 / 3906250) := by
  have h := checkLog_sound (w := (53589697031 / 553589697031)) (n := 12)
    (lo := (194216191 / 1000000000)) (hi := (758657 / 3906250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((303589697031 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(303589697031 / 250000000000) = 1/(250000000000 / 303589697031) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5930 : Bounds (194216191 / 1000000000) (758657 / 3906250) (Real.log (303589697031 / 250000000000)) := by
  have h := reflection_log_5930_neg
  have he : Real.log (303589697031 / 250000000000) = -Real.log (250000000000 / 303589697031) := by
    rw [show ((303589697031 / 250000000000) : ℝ) = ((250000000000 / 303589697031) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5931_neg : (486767 / 2500000) ≤ -Real.log (500000000000 / 607477354857) ∧
    -Real.log (500000000000 / 607477354857) ≤ (194706801 / 1000000000) := by
  have h := checkLog_sound (w := (107477354857 / 1107477354857)) (n := 12)
    (lo := (486767 / 2500000)) (hi := (194706801 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((607477354857 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(607477354857 / 500000000000) = 1/(500000000000 / 607477354857) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5931 : Bounds (486767 / 2500000) (194706801 / 1000000000) (Real.log (607477354857 / 500000000000)) := by
  have h := reflection_log_5931_neg
  have he : Real.log (607477354857 / 500000000000) = -Real.log (500000000000 / 607477354857) := by
    rw [show ((607477354857 / 500000000000) : ℝ) = ((500000000000 / 607477354857) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5932_neg : (389864167 / 1000000000) ≤ -Real.log (500000000000 / 738390092879) ∧
    -Real.log (500000000000 / 738390092879) ≤ (48733021 / 125000000) := by
  have h := checkLog_sound (w := (238390092879 / 1238390092879)) (n := 12)
    (lo := (389864167 / 1000000000)) (hi := (48733021 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((738390092879 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(738390092879 / 500000000000) = 1/(500000000000 / 738390092879) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5932 : Bounds (389864167 / 1000000000) (48733021 / 125000000) (Real.log (738390092879 / 500000000000)) := by
  have h := reflection_log_5932_neg
  have he : Real.log (738390092879 / 500000000000) = -Real.log (500000000000 / 738390092879) := by
    rw [show ((738390092879 / 500000000000) : ℝ) = ((500000000000 / 738390092879) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5933_neg : (97517967 / 250000000) ≤ -Real.log (125000000000 / 184635868219) ∧
    -Real.log (125000000000 / 184635868219) ≤ (390071869 / 1000000000) := by
  have h := checkLog_sound (w := (59635868219 / 309635868219)) (n := 12)
    (lo := (97517967 / 250000000)) (hi := (390071869 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((184635868219 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(184635868219 / 125000000000) = 1/(125000000000 / 184635868219) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5933 : Bounds (97517967 / 250000000) (390071869 / 1000000000) (Real.log (184635868219 / 125000000000)) := by
  have h := reflection_log_5933_neg
  have he : Real.log (184635868219 / 125000000000) = -Real.log (125000000000 / 184635868219) := by
    rw [show ((184635868219 / 125000000000) : ℝ) = ((125000000000 / 184635868219) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5934_neg : (44054911 / 250000000) ≤ -Real.log (10000 / 11927) ∧
    -Real.log (10000 / 11927) ≤ (35243929 / 200000000) := by
  have h := checkLog_sound (w := (1927 / 21927)) (n := 12)
    (lo := (44054911 / 250000000)) (hi := (35243929 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11927 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11927 / 10000) = 1/(10000 / 11927) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5934 : Bounds (44054911 / 250000000) (35243929 / 200000000) (Real.log (11927 / 10000)) := by
  have h := reflection_log_5934_neg
  have he : Real.log (11927 / 10000) = -Real.log (10000 / 11927) := by
    rw [show ((11927 / 10000) : ℝ) = ((10000 / 11927) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5935_neg : (53514983 / 250000000) ≤ -Real.log (8073 / 10000) ∧
    -Real.log (8073 / 10000) ≤ (214059933 / 1000000000) := by
  have h := checkLog_sound (w := (1927 / 18073)) (n := 12)
    (lo := (53514983 / 250000000)) (hi := (214059933 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8073) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8073) = 1/(8073 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5935 : Bounds (-214059933 / 1000000000) (-53514983 / 250000000) (Real.log (8073 / 10000)) := by
  have h := reflection_log_5935_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5936_neg : (192681 / 1000000000) ≤ -Real.log (10000000 / 10001927) ∧
    -Real.log (10000000 / 10001927) ≤ (96341 / 500000000) := by
  have h := checkLog_sound (w := (1927 / 20001927)) (n := 12)
    (lo := (192681 / 1000000000)) (hi := (96341 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001927 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001927 / 10000000) = 1/(10000000 / 10001927) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5936 : Bounds (192681 / 1000000000) (96341 / 500000000) (Real.log (10001927 / 10000000)) := by
  have h := reflection_log_5936_neg
  have he : Real.log (10001927 / 10000000) = -Real.log (10000000 / 10001927) := by
    rw [show ((10001927 / 10000000) : ℝ) = ((10000000 / 10001927) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5937_neg : (96359 / 500000000) ≤ -Real.log (9998073 / 10000000) ∧
    -Real.log (9998073 / 10000000) ≤ (192719 / 1000000000) := by
  have h := checkLog_sound (w := (1927 / 19998073)) (n := 12)
    (lo := (96359 / 500000000)) (hi := (192719 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998073) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998073) = 1/(9998073 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5937 : Bounds (-192719 / 1000000000) (-96359 / 500000000) (Real.log (9998073 / 10000000)) := by
  have h := reflection_log_5937_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5938_neg : (92446993 / 1000000000) ≤ -Real.log (200000 / 219371) ∧
    -Real.log (200000 / 219371) ≤ (46223497 / 500000000) := by
  have h := checkLog_sound (w := (19371 / 419371)) (n := 12)
    (lo := (92446993 / 1000000000)) (hi := (46223497 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((219371 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(219371 / 200000) = 1/(200000 / 219371) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5938 : Bounds (92446993 / 1000000000) (46223497 / 500000000) (Real.log (219371 / 200000)) := by
  have h := reflection_log_5938_neg
  have he : Real.log (219371 / 200000) = -Real.log (200000 / 219371) := by
    rw [show ((219371 / 200000) : ℝ) = ((200000 / 219371) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5939_neg : (50936081 / 500000000) ≤ -Real.log (180629 / 200000) ∧
    -Real.log (180629 / 200000) ≤ (101872163 / 1000000000) := by
  have h := checkLog_sound (w := (19371 / 380629)) (n := 12)
    (lo := (50936081 / 500000000)) (hi := (101872163 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 180629) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 180629) = 1/(180629 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5939 : Bounds (-101872163 / 1000000000) (-50936081 / 500000000) (Real.log (180629 / 200000)) := by
  have h := reflection_log_5939_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5940_neg : (92669423 / 1000000000) ≤ -Real.log (1000000 / 1097099) ∧
    -Real.log (1000000 / 1097099) ≤ (5791839 / 62500000) := by
  have h := checkLog_sound (w := (97099 / 2097099)) (n := 12)
    (lo := (92669423 / 1000000000)) (hi := (5791839 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1097099 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1097099 / 1000000) = 1/(1000000 / 1097099) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5940 : Bounds (92669423 / 1000000000) (5791839 / 62500000) (Real.log (1097099 / 1000000)) := by
  have h := reflection_log_5940_neg
  have he : Real.log (1097099 / 1000000) = -Real.log (1000000 / 1097099) := by
    rw [show ((1097099 / 1000000) : ℝ) = ((1000000 / 1097099) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5941_neg : (51071183 / 500000000) ≤ -Real.log (902901 / 1000000) ∧
    -Real.log (902901 / 1000000) ≤ (102142367 / 1000000000) := by
  have h := checkLog_sound (w := (97099 / 1902901)) (n := 12)
    (lo := (51071183 / 500000000)) (hi := (102142367 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 902901) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 902901) = 1/(902901 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5941 : Bounds (-102142367 / 1000000000) (-51071183 / 500000000) (Real.log (902901 / 1000000)) := by
  have h := reflection_log_5941_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5942_neg : (4736471 / 500000000) ≤ -Real.log (990571784199 / 1000000000000) ∧
    -Real.log (990571784199 / 1000000000000) ≤ (9472943 / 1000000000) := by
  have h := checkLog_sound (w := (9428215801 / 1990571784199)) (n := 12)
    (lo := (4736471 / 500000000)) (hi := (9472943 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 990571784199) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 990571784199) = 1/(990571784199 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5942 : Bounds (-9472943 / 1000000000) (-4736471 / 500000000) (Real.log (990571784199 / 1000000000000)) := by
  have h := reflection_log_5942_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5943_neg : (589073 / 62500000) ≤ -Real.log (39624764359 / 40000000000) ∧
    -Real.log (39624764359 / 40000000000) ≤ (9425169 / 1000000000) := by
  have h := checkLog_sound (w := (375235641 / 79624764359)) (n := 12)
    (lo := (589073 / 62500000)) (hi := (9425169 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39624764359) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39624764359) = 1/(39624764359 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5943 : Bounds (-9425169 / 1000000000) (-589073 / 62500000) (Real.log (39624764359 / 40000000000)) := by
  have h := reflection_log_5943_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5944_neg : (48579789 / 250000000) ≤ -Real.log (500000000000 / 607241915749) ∧
    -Real.log (500000000000 / 607241915749) ≤ (194319157 / 1000000000) := by
  have h := checkLog_sound (w := (107241915749 / 1107241915749)) (n := 12)
    (lo := (48579789 / 250000000)) (hi := (194319157 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((607241915749 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(607241915749 / 500000000000) = 1/(500000000000 / 607241915749) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5944 : Bounds (48579789 / 250000000) (194319157 / 1000000000) (Real.log (607241915749 / 500000000000)) := by
  have h := reflection_log_5944_neg
  have he : Real.log (607241915749 / 500000000000) = -Real.log (500000000000 / 607241915749) := by
    rw [show ((607241915749 / 500000000000) : ℝ) = ((500000000000 / 607241915749) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5945_neg : (194811789 / 1000000000) ≤ -Real.log (500000000000 / 607541136847) ∧
    -Real.log (500000000000 / 607541136847) ≤ (19481179 / 100000000) := by
  have h := checkLog_sound (w := (107541136847 / 1107541136847)) (n := 12)
    (lo := (194811789 / 1000000000)) (hi := (19481179 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((607541136847 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(607541136847 / 500000000000) = 1/(500000000000 / 607541136847) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5945 : Bounds (194811789 / 1000000000) (19481179 / 100000000) (Real.log (607541136847 / 500000000000)) := by
  have h := reflection_log_5945_neg
  have he : Real.log (607541136847 / 500000000000) = -Real.log (500000000000 / 607541136847) := by
    rw [show ((607541136847 / 500000000000) : ℝ) = ((500000000000 / 607541136847) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5946_neg : (97517967 / 250000000) ≤ -Real.log (4000000000 / 5908347783) ∧
    -Real.log (4000000000 / 5908347783) ≤ (390071869 / 1000000000) := by
  have h := checkLog_sound (w := (1908347783 / 9908347783)) (n := 12)
    (lo := (97517967 / 250000000)) (hi := (390071869 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5908347783 / 4000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5908347783 / 4000000000) = 1/(4000000000 / 5908347783) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5946 : Bounds (97517967 / 250000000) (390071869 / 1000000000) (Real.log (5908347783 / 4000000000)) := by
  have h := reflection_log_5946_neg
  have he : Real.log (5908347783 / 4000000000) = -Real.log (4000000000 / 5908347783) := by
    rw [show ((5908347783 / 4000000000) : ℝ) = ((4000000000 / 5908347783) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5947_neg : (390279577 / 1000000000) ≤ -Real.log (500000000000 / 738696890871) ∧
    -Real.log (500000000000 / 738696890871) ≤ (195139789 / 500000000) := by
  have h := checkLog_sound (w := (238696890871 / 1238696890871)) (n := 12)
    (lo := (390279577 / 1000000000)) (hi := (195139789 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((738696890871 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(738696890871 / 500000000000) = 1/(500000000000 / 738696890871) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5947 : Bounds (390279577 / 1000000000) (195139789 / 500000000) (Real.log (738696890871 / 500000000000)) := by
  have h := reflection_log_5947_neg
  have he : Real.log (738696890871 / 500000000000) = -Real.log (500000000000 / 738696890871) := by
    rw [show ((738696890871 / 500000000000) : ℝ) = ((500000000000 / 738696890871) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5948_neg : (44075871 / 250000000) ≤ -Real.log (1250 / 1491) ∧
    -Real.log (1250 / 1491) ≤ (35260697 / 200000000) := by
  have h := checkLog_sound (w := (241 / 2741)) (n := 12)
    (lo := (44075871 / 250000000)) (hi := (35260697 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1491 / 1250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1491 / 1250) = 1/(1250 / 1491) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5948 : Bounds (44075871 / 250000000) (35260697 / 200000000) (Real.log (1491 / 1250)) := by
  have h := reflection_log_5948_neg
  have he : Real.log (1491 / 1250) = -Real.log (1250 / 1491) := by
    rw [show ((1491 / 1250) : ℝ) = ((1250 / 1491) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5949_neg : (214183809 / 1000000000) ≤ -Real.log (1009 / 1250) ∧
    -Real.log (1009 / 1250) ≤ (21418381 / 100000000) := by
  have h := checkLog_sound (w := (241 / 2259)) (n := 12)
    (lo := (214183809 / 1000000000)) (hi := (21418381 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250 / 1009) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1250 / 1009) = 1/(1009 / 1250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5949 : Bounds (-21418381 / 100000000) (-214183809 / 1000000000) (Real.log (1009 / 1250)) := by
  have h := reflection_log_5949_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5950_neg : (192781 / 1000000000) ≤ -Real.log (1250000 / 1250241) ∧
    -Real.log (1250000 / 1250241) ≤ (96391 / 500000000) := by
  have h := checkLog_sound (w := (241 / 2500241)) (n := 12)
    (lo := (192781 / 1000000000)) (hi := (96391 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250241 / 1250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1250241 / 1250000) = 1/(1250000 / 1250241) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5950 : Bounds (192781 / 1000000000) (96391 / 500000000) (Real.log (1250241 / 1250000)) := by
  have h := reflection_log_5950_neg
  have he : Real.log (1250241 / 1250000) = -Real.log (1250000 / 1250241) := by
    rw [show ((1250241 / 1250000) : ℝ) = ((1250000 / 1250241) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5951_neg : (96409 / 500000000) ≤ -Real.log (1249759 / 1250000) ∧
    -Real.log (1249759 / 1250000) ≤ (192819 / 1000000000) := by
  have h := checkLog_sound (w := (241 / 2499759)) (n := 12)
    (lo := (96409 / 500000000)) (hi := (192819 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250000 / 1249759) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1250000 / 1249759) = 1/(1249759 / 1250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5951 : Bounds (-192819 / 1000000000) (-96409 / 500000000) (Real.log (1249759 / 1250000)) := by
  have h := reflection_log_5951_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.LowRatioFamily
