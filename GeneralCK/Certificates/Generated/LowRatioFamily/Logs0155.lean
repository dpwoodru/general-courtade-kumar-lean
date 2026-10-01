import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_9920_neg : (19503 / 62500000) ≤ -Real.log (124961 / 125000) ∧
    -Real.log (124961 / 125000) ≤ (312049 / 1000000000) := by
  have h := checkLog_sound (w := (39 / 249961)) (n := 12)
    (lo := (19503 / 62500000)) (hi := (312049 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 124961) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 124961) = 1/(124961 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9920 : Bounds (-312049 / 1000000000) (-19503 / 62500000) (Real.log (124961 / 125000)) := by
  have h := reflection_log_9920_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9921_neg : (73407203 / 500000000) ≤ -Real.log (1000000 / 1158139) ∧
    -Real.log (1000000 / 1158139) ≤ (146814407 / 1000000000) := by
  have h := checkLog_sound (w := (158139 / 2158139)) (n := 12)
    (lo := (73407203 / 500000000)) (hi := (146814407 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1158139 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1158139 / 1000000) = 1/(1000000 / 1158139) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9921 : Bounds (73407203 / 500000000) (146814407 / 1000000000) (Real.log (1158139 / 1000000)) := by
  have h := reflection_log_9921_neg
  have he : Real.log (1158139 / 1000000) = -Real.log (1000000 / 1158139) := by
    rw [show ((1158139 / 1000000) : ℝ) = ((1000000 / 1158139) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9922_neg : (172140361 / 1000000000) ≤ -Real.log (841861 / 1000000) ∧
    -Real.log (841861 / 1000000) ≤ (86070181 / 500000000) := by
  have h := checkLog_sound (w := (158139 / 1841861)) (n := 12)
    (lo := (172140361 / 1000000000)) (hi := (86070181 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 841861) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 841861) = 1/(841861 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9922 : Bounds (-86070181 / 500000000) (-172140361 / 1000000000) (Real.log (841861 / 1000000)) := by
  have h := reflection_log_9922_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9923_neg : (36883567 / 250000000) ≤ -Real.log (1000000 / 1158973) ∧
    -Real.log (1000000 / 1158973) ≤ (147534269 / 1000000000) := by
  have h := checkLog_sound (w := (158973 / 2158973)) (n := 12)
    (lo := (36883567 / 250000000)) (hi := (147534269 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1158973 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1158973 / 1000000) = 1/(1000000 / 1158973) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9923 : Bounds (36883567 / 250000000) (147534269 / 1000000000) (Real.log (1158973 / 1000000)) := by
  have h := reflection_log_9923_neg
  have he : Real.log (1158973 / 1000000) = -Real.log (1000000 / 1158973) := by
    rw [show ((1158973 / 1000000) : ℝ) = ((1000000 / 1158973) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9924_neg : (86565757 / 500000000) ≤ -Real.log (841027 / 1000000) ∧
    -Real.log (841027 / 1000000) ≤ (34626303 / 200000000) := by
  have h := checkLog_sound (w := (158973 / 1841027)) (n := 12)
    (lo := (86565757 / 500000000)) (hi := (34626303 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 841027) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 841027) = 1/(841027 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9924 : Bounds (-34626303 / 200000000) (-86565757 / 500000000) (Real.log (841027 / 1000000)) := by
  have h := reflection_log_9924_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9925_neg : (12798623 / 500000000) ≤ -Real.log (974727585271 / 1000000000000) ∧
    -Real.log (974727585271 / 1000000000000) ≤ (25597247 / 1000000000) := by
  have h := checkLog_sound (w := (25272414729 / 1974727585271)) (n := 12)
    (lo := (12798623 / 500000000)) (hi := (25597247 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 974727585271) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 974727585271) = 1/(974727585271 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9925 : Bounds (-25597247 / 1000000000) (-12798623 / 500000000) (Real.log (974727585271 / 1000000000000)) := by
  have h := reflection_log_9925_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9926_neg : (5065191 / 200000000) ≤ -Real.log (974992056679 / 1000000000000) ∧
    -Real.log (974992056679 / 1000000000000) ≤ (6331489 / 250000000) := by
  have h := checkLog_sound (w := (25007943321 / 1974992056679)) (n := 12)
    (lo := (5065191 / 200000000)) (hi := (6331489 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 974992056679) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 974992056679) = 1/(974992056679 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9926 : Bounds (-6331489 / 250000000) (-5065191 / 200000000) (Real.log (974992056679 / 1000000000000)) := by
  have h := reflection_log_9926_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9927_neg : (318954767 / 1000000000) ≤ -Real.log (500000000000 / 687844549159) ∧
    -Real.log (500000000000 / 687844549159) ≤ (19934673 / 62500000) := by
  have h := checkLog_sound (w := (187844549159 / 1187844549159)) (n := 12)
    (lo := (318954767 / 1000000000)) (hi := (19934673 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((687844549159 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(687844549159 / 500000000000) = 1/(500000000000 / 687844549159) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9927 : Bounds (318954767 / 1000000000) (19934673 / 62500000) (Real.log (687844549159 / 500000000000)) := by
  have h := reflection_log_9927_neg
  have he : Real.log (687844549159 / 500000000000) = -Real.log (500000000000 / 687844549159) := by
    rw [show ((687844549159 / 500000000000) : ℝ) = ((500000000000 / 687844549159) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9928_neg : (320665783 / 1000000000) ≤ -Real.log (250000000000 / 344511234479) ∧
    -Real.log (250000000000 / 344511234479) ≤ (40083223 / 125000000) := by
  have h := checkLog_sound (w := (94511234479 / 594511234479)) (n := 12)
    (lo := (320665783 / 1000000000)) (hi := (40083223 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((344511234479 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(344511234479 / 250000000000) = 1/(250000000000 / 344511234479) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9928 : Bounds (320665783 / 1000000000) (40083223 / 125000000) (Real.log (344511234479 / 250000000000)) := by
  have h := reflection_log_9928_neg
  have he : Real.log (344511234479 / 250000000000) = -Real.log (250000000000 / 344511234479) := by
    rw [show ((344511234479 / 250000000000) : ℝ) = ((250000000000 / 344511234479) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9929_neg : (160826053 / 250000000) ≤ -Real.log (500000000000 / 951378809869) ∧
    -Real.log (500000000000 / 951378809869) ≤ (643304213 / 1000000000) := by
  have h := checkLog_sound (w := (451378809869 / 1451378809869)) (n := 12)
    (lo := (160826053 / 250000000)) (hi := (643304213 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((951378809869 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(951378809869 / 500000000000) = 1/(500000000000 / 951378809869) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9929 : Bounds (160826053 / 250000000) (643304213 / 1000000000) (Real.log (951378809869 / 500000000000)) := by
  have h := reflection_log_9929_neg
  have he : Real.log (951378809869 / 500000000000) = -Real.log (500000000000 / 951378809869) := by
    rw [show ((951378809869 / 500000000000) : ℝ) = ((500000000000 / 951378809869) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9930_neg : (645519131 / 1000000000) ≤ -Real.log (250000000000 / 476744186047) ∧
    -Real.log (250000000000 / 476744186047) ≤ (161379783 / 250000000) := by
  have h := checkLog_sound (w := (226744186047 / 726744186047)) (n := 12)
    (lo := (645519131 / 1000000000)) (hi := (161379783 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((476744186047 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(476744186047 / 250000000000) = 1/(250000000000 / 476744186047) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9930 : Bounds (645519131 / 1000000000) (161379783 / 250000000) (Real.log (476744186047 / 250000000000)) := by
  have h := reflection_log_9930_neg
  have he : Real.log (476744186047 / 250000000000) = -Real.log (250000000000 / 476744186047) := by
    rw [show ((476744186047 / 250000000000) : ℝ) = ((250000000000 / 476744186047) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9931_neg : (54462919 / 200000000) ≤ -Real.log (1000 / 1313) ∧
    -Real.log (1000 / 1313) ≤ (68078649 / 250000000) := by
  have h := checkLog_sound (w := (313 / 2313)) (n := 12)
    (lo := (54462919 / 200000000)) (hi := (68078649 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1313 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1313 / 1000) = 1/(1000 / 1313) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9931 : Bounds (54462919 / 200000000) (68078649 / 250000000) (Real.log (1313 / 1000)) := by
  have h := reflection_log_9931_neg
  have he : Real.log (1313 / 1000) = -Real.log (1000 / 1313) := by
    rw [show ((1313 / 1000) : ℝ) = ((1000 / 1313) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9932_neg : (187710493 / 500000000) ≤ -Real.log (687 / 1000) ∧
    -Real.log (687 / 1000) ≤ (375420987 / 1000000000) := by
  have h := checkLog_sound (w := (313 / 1687)) (n := 12)
    (lo := (187710493 / 500000000)) (hi := (375420987 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 687) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 687) = 1/(687 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9932 : Bounds (-375420987 / 1000000000) (-187710493 / 500000000) (Real.log (687 / 1000)) := by
  have h := reflection_log_9932_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9933_neg : (312951 / 1000000000) ≤ -Real.log (1000000 / 1000313) ∧
    -Real.log (1000000 / 1000313) ≤ (39119 / 125000000) := by
  have h := checkLog_sound (w := (313 / 2000313)) (n := 12)
    (lo := (312951 / 1000000000)) (hi := (39119 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000313 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000313 / 1000000) = 1/(1000000 / 1000313) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9933 : Bounds (312951 / 1000000000) (39119 / 125000000) (Real.log (1000313 / 1000000)) := by
  have h := reflection_log_9933_neg
  have he : Real.log (1000313 / 1000000) = -Real.log (1000000 / 1000313) := by
    rw [show ((1000313 / 1000000) : ℝ) = ((1000000 / 1000313) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9934_neg : (39131 / 125000000) ≤ -Real.log (999687 / 1000000) ∧
    -Real.log (999687 / 1000000) ≤ (313049 / 1000000000) := by
  have h := checkLog_sound (w := (313 / 1999687)) (n := 12)
    (lo := (39131 / 125000000)) (hi := (313049 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999687) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999687) = 1/(999687 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9934 : Bounds (-313049 / 1000000000) (-39131 / 125000000) (Real.log (999687 / 1000000)) := by
  have h := reflection_log_9934_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9935_neg : (147269343 / 1000000000) ≤ -Real.log (500000 / 579333) ∧
    -Real.log (500000 / 579333) ≤ (4602167 / 31250000) := by
  have h := checkLog_sound (w := (79333 / 1079333)) (n := 12)
    (lo := (147269343 / 1000000000)) (hi := (4602167 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((579333 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(579333 / 500000) = 1/(500000 / 579333) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9935 : Bounds (147269343 / 1000000000) (4602167 / 31250000) (Real.log (579333 / 500000)) := by
  have h := reflection_log_9935_neg
  have he : Real.log (579333 / 500000) = -Real.log (500000 / 579333) := by
    rw [show ((579333 / 500000) : ℝ) = ((500000 / 579333) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9936_neg : (172766551 / 1000000000) ≤ -Real.log (420667 / 500000) ∧
    -Real.log (420667 / 500000) ≤ (21595819 / 125000000) := by
  have h := checkLog_sound (w := (79333 / 920667)) (n := 12)
    (lo := (172766551 / 1000000000)) (hi := (21595819 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 420667) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 420667) = 1/(420667 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9936 : Bounds (-21595819 / 125000000) (-172766551 / 1000000000) (Real.log (420667 / 500000)) := by
  have h := reflection_log_9936_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9937_neg : (73995301 / 500000000) ≤ -Real.log (500000 / 579751) ∧
    -Real.log (500000 / 579751) ≤ (147990603 / 1000000000) := by
  have h := checkLog_sound (w := (79751 / 1079751)) (n := 12)
    (lo := (73995301 / 500000000)) (hi := (147990603 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((579751 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(579751 / 500000) = 1/(500000 / 579751) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9937 : Bounds (73995301 / 500000000) (147990603 / 1000000000) (Real.log (579751 / 500000)) := by
  have h := reflection_log_9937_neg
  have he : Real.log (579751 / 500000) = -Real.log (500000 / 579751) := by
    rw [show ((579751 / 500000) : ℝ) = ((500000 / 579751) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9938_neg : (34752141 / 200000000) ≤ -Real.log (420249 / 500000) ∧
    -Real.log (420249 / 500000) ≤ (86880353 / 500000000) := by
  have h := checkLog_sound (w := (79751 / 920249)) (n := 12)
    (lo := (34752141 / 200000000)) (hi := (86880353 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 420249) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 420249) = 1/(420249 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9938 : Bounds (-86880353 / 500000000) (-34752141 / 200000000) (Real.log (420249 / 500000)) := by
  have h := reflection_log_9938_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9939_neg : (25770103 / 1000000000) ≤ -Real.log (243639777999 / 250000000000) ∧
    -Real.log (243639777999 / 250000000000) ≤ (3221263 / 125000000) := by
  have h := checkLog_sound (w := (6360222001 / 493639777999)) (n := 12)
    (lo := (25770103 / 1000000000)) (hi := (3221263 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 243639777999) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 243639777999) = 1/(243639777999 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9939 : Bounds (-3221263 / 125000000) (-25770103 / 1000000000) (Real.log (243639777999 / 250000000000)) := by
  have h := reflection_log_9939_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9940_neg : (3187151 / 125000000) ≤ -Real.log (243706275111 / 250000000000) ∧
    -Real.log (243706275111 / 250000000000) ≤ (25497209 / 1000000000) := by
  have h := checkLog_sound (w := (6293724889 / 493706275111)) (n := 12)
    (lo := (3187151 / 125000000)) (hi := (25497209 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 243706275111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 243706275111) = 1/(243706275111 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9940 : Bounds (-25497209 / 1000000000) (-3187151 / 125000000) (Real.log (243706275111 / 250000000000)) := by
  have h := reflection_log_9940_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9941_neg : (160017947 / 500000000) ≤ -Real.log (250000000000 / 344294299291) ∧
    -Real.log (250000000000 / 344294299291) ≤ (64007179 / 200000000) := by
  have h := checkLog_sound (w := (94294299291 / 594294299291)) (n := 12)
    (lo := (160017947 / 500000000)) (hi := (64007179 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((344294299291 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(344294299291 / 250000000000) = 1/(250000000000 / 344294299291) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9941 : Bounds (160017947 / 500000000) (64007179 / 200000000) (Real.log (344294299291 / 250000000000)) := by
  have h := reflection_log_9941_neg
  have he : Real.log (344294299291 / 250000000000) = -Real.log (250000000000 / 344294299291) := by
    rw [show ((344294299291 / 250000000000) : ℝ) = ((250000000000 / 344294299291) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9942_neg : (80437827 / 250000000) ≤ -Real.log (62500000000 / 86221353293) ∧
    -Real.log (62500000000 / 86221353293) ≤ (321751309 / 1000000000) := by
  have h := checkLog_sound (w := (23721353293 / 148721353293)) (n := 12)
    (lo := (80437827 / 250000000)) (hi := (321751309 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((86221353293 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(86221353293 / 62500000000) = 1/(62500000000 / 86221353293) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9942 : Bounds (80437827 / 250000000) (321751309 / 1000000000) (Real.log (86221353293 / 62500000000)) := by
  have h := reflection_log_9942_neg
  have he : Real.log (86221353293 / 62500000000) = -Real.log (62500000000 / 86221353293) := by
    rw [show ((86221353293 / 62500000000) : ℝ) = ((62500000000 / 86221353293) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9943_neg : (645519131 / 1000000000) ≤ -Real.log (500000000000 / 953488372093) ∧
    -Real.log (500000000000 / 953488372093) ≤ (161379783 / 250000000) := by
  have h := checkLog_sound (w := (453488372093 / 1453488372093)) (n := 12)
    (lo := (645519131 / 1000000000)) (hi := (161379783 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((953488372093 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(953488372093 / 500000000000) = 1/(500000000000 / 953488372093) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9943 : Bounds (645519131 / 1000000000) (161379783 / 250000000) (Real.log (953488372093 / 500000000000)) := by
  have h := reflection_log_9943_neg
  have he : Real.log (953488372093 / 500000000000) = -Real.log (500000000000 / 953488372093) := by
    rw [show ((953488372093 / 500000000000) : ℝ) = ((500000000000 / 953488372093) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9944_neg : (323867791 / 500000000) ≤ -Real.log (125000000000 / 238901018923) ∧
    -Real.log (125000000000 / 238901018923) ≤ (647735583 / 1000000000) := by
  have h := checkLog_sound (w := (113901018923 / 363901018923)) (n := 12)
    (lo := (323867791 / 500000000)) (hi := (647735583 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((238901018923 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(238901018923 / 125000000000) = 1/(125000000000 / 238901018923) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9944 : Bounds (323867791 / 500000000) (647735583 / 1000000000) (Real.log (238901018923 / 125000000000)) := by
  have h := reflection_log_9944_neg
  have he : Real.log (238901018923 / 125000000000) = -Real.log (125000000000 / 238901018923) := by
    rw [show ((238901018923 / 125000000000) : ℝ) = ((125000000000 / 238901018923) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9945_neg : (3413449 / 12500000) ≤ -Real.log (500 / 657) ∧
    -Real.log (500 / 657) ≤ (273075921 / 1000000000) := by
  have h := checkLog_sound (w := (157 / 1157)) (n := 12)
    (lo := (3413449 / 12500000)) (hi := (273075921 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((657 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(657 / 500) = 1/(500 / 657) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9945 : Bounds (3413449 / 12500000) (273075921 / 1000000000) (Real.log (657 / 500)) := by
  have h := reflection_log_9945_neg
  have he : Real.log (657 / 500) = -Real.log (500 / 657) := by
    rw [show ((657 / 500) : ℝ) = ((500 / 657) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9946_neg : (376877651 / 1000000000) ≤ -Real.log (343 / 500) ∧
    -Real.log (343 / 500) ≤ (94219413 / 250000000) := by
  have h := checkLog_sound (w := (157 / 843)) (n := 12)
    (lo := (376877651 / 1000000000)) (hi := (94219413 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 343) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500 / 343) = 1/(343 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9946 : Bounds (-94219413 / 250000000) (-376877651 / 1000000000) (Real.log (343 / 500)) := by
  have h := reflection_log_9946_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9947_neg : (6279 / 20000000) ≤ -Real.log (500000 / 500157) ∧
    -Real.log (500000 / 500157) ≤ (313951 / 1000000000) := by
  have h := checkLog_sound (w := (157 / 1000157)) (n := 12)
    (lo := (6279 / 20000000)) (hi := (313951 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500157 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500157 / 500000) = 1/(500000 / 500157) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9947 : Bounds (6279 / 20000000) (313951 / 1000000000) (Real.log (500157 / 500000)) := by
  have h := reflection_log_9947_neg
  have he : Real.log (500157 / 500000) = -Real.log (500000 / 500157) := by
    rw [show ((500157 / 500000) : ℝ) = ((500000 / 500157) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9948_neg : (314049 / 1000000000) ≤ -Real.log (499843 / 500000) ∧
    -Real.log (499843 / 500000) ≤ (6281 / 20000000) := by
  have h := checkLog_sound (w := (157 / 999843)) (n := 12)
    (lo := (314049 / 1000000000)) (hi := (6281 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499843) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499843) = 1/(499843 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9948 : Bounds (-6281 / 20000000) (-314049 / 1000000000) (Real.log (499843 / 500000)) := by
  have h := reflection_log_9948_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9949_neg : (147724073 / 1000000000) ≤ -Real.log (1000000 / 1159193) ∧
    -Real.log (1000000 / 1159193) ≤ (73862037 / 500000000) := by
  have h := checkLog_sound (w := (159193 / 2159193)) (n := 12)
    (lo := (147724073 / 1000000000)) (hi := (73862037 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1159193 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1159193 / 1000000) = 1/(1000000 / 1159193) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9949 : Bounds (147724073 / 1000000000) (73862037 / 500000000) (Real.log (1159193 / 1000000)) := by
  have h := reflection_log_9949_neg
  have he : Real.log (1159193 / 1000000) = -Real.log (1000000 / 1159193) := by
    rw [show ((1159193 / 1000000) : ℝ) = ((1000000 / 1159193) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9950_neg : (86696567 / 500000000) ≤ -Real.log (840807 / 1000000) ∧
    -Real.log (840807 / 1000000) ≤ (34678627 / 200000000) := by
  have h := checkLog_sound (w := (159193 / 1840807)) (n := 12)
    (lo := (86696567 / 500000000)) (hi := (34678627 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 840807) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 840807) = 1/(840807 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9950 : Bounds (-34678627 / 200000000) (-86696567 / 500000000) (Real.log (840807 / 1000000)) := by
  have h := reflection_log_9950_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9951_neg : (74222933 / 500000000) ≤ -Real.log (100000 / 116003) ∧
    -Real.log (100000 / 116003) ≤ (148445867 / 1000000000) := by
  have h := checkLog_sound (w := (16003 / 216003)) (n := 12)
    (lo := (74222933 / 500000000)) (hi := (148445867 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((116003 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(116003 / 100000) = 1/(100000 / 116003) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9951 : Bounds (74222933 / 500000000) (148445867 / 1000000000) (Real.log (116003 / 100000)) := by
  have h := reflection_log_9951_neg
  have he : Real.log (116003 / 100000) = -Real.log (100000 / 116003) := by
    rw [show ((116003 / 100000) : ℝ) = ((100000 / 116003) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9952_neg : (87194551 / 500000000) ≤ -Real.log (83997 / 100000) ∧
    -Real.log (83997 / 100000) ≤ (174389103 / 1000000000) := by
  have h := checkLog_sound (w := (16003 / 183997)) (n := 12)
    (lo := (87194551 / 500000000)) (hi := (174389103 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 83997) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 83997) = 1/(83997 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9952 : Bounds (-174389103 / 1000000000) (-87194551 / 500000000) (Real.log (83997 / 100000)) := by
  have h := reflection_log_9952_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9953_neg : (5188647 / 200000000) ≤ -Real.log (9743903991 / 10000000000) ∧
    -Real.log (9743903991 / 10000000000) ≤ (6485809 / 250000000) := by
  have h := checkLog_sound (w := (256096009 / 19743903991)) (n := 12)
    (lo := (5188647 / 200000000)) (hi := (6485809 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 9743903991) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 9743903991) = 1/(9743903991 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9953 : Bounds (-6485809 / 250000000) (-5188647 / 200000000) (Real.log (9743903991 / 10000000000)) := by
  have h := reflection_log_9953_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9954_neg : (1283453 / 50000000) ≤ -Real.log (974657588751 / 1000000000000) ∧
    -Real.log (974657588751 / 1000000000000) ≤ (25669061 / 1000000000) := by
  have h := checkLog_sound (w := (25342411249 / 1974657588751)) (n := 12)
    (lo := (1283453 / 50000000)) (hi := (25669061 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 974657588751) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 974657588751) = 1/(974657588751 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9954 : Bounds (-25669061 / 1000000000) (-1283453 / 50000000) (Real.log (974657588751 / 1000000000000)) := by
  have h := reflection_log_9954_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9955_neg : (321117207 / 1000000000) ≤ -Real.log (250000000000 / 344666790357) ∧
    -Real.log (250000000000 / 344666790357) ≤ (40139651 / 125000000) := by
  have h := checkLog_sound (w := (94666790357 / 594666790357)) (n := 12)
    (lo := (321117207 / 1000000000)) (hi := (40139651 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((344666790357 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(344666790357 / 250000000000) = 1/(250000000000 / 344666790357) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9955 : Bounds (321117207 / 1000000000) (40139651 / 125000000) (Real.log (344666790357 / 250000000000)) := by
  have h := reflection_log_9955_neg
  have he : Real.log (344666790357 / 250000000000) = -Real.log (250000000000 / 344666790357) := by
    rw [show ((344666790357 / 250000000000) : ℝ) = ((250000000000 / 344666790357) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9956_neg : (40354371 / 125000000) ≤ -Real.log (250000000000 / 345259354501) ∧
    -Real.log (250000000000 / 345259354501) ≤ (322834969 / 1000000000) := by
  have h := checkLog_sound (w := (95259354501 / 595259354501)) (n := 12)
    (lo := (40354371 / 125000000)) (hi := (322834969 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((345259354501 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(345259354501 / 250000000000) = 1/(250000000000 / 345259354501) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9956 : Bounds (40354371 / 125000000) (322834969 / 1000000000) (Real.log (345259354501 / 250000000000)) := by
  have h := reflection_log_9956_neg
  have he : Real.log (345259354501 / 250000000000) = -Real.log (250000000000 / 345259354501) := by
    rw [show ((345259354501 / 250000000000) : ℝ) = ((250000000000 / 345259354501) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9957_neg : (323867791 / 500000000) ≤ -Real.log (500000000000 / 955604075691) ∧
    -Real.log (500000000000 / 955604075691) ≤ (647735583 / 1000000000) := by
  have h := checkLog_sound (w := (455604075691 / 1455604075691)) (n := 12)
    (lo := (323867791 / 500000000)) (hi := (647735583 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((955604075691 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(955604075691 / 500000000000) = 1/(500000000000 / 955604075691) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9957 : Bounds (323867791 / 500000000) (647735583 / 1000000000) (Real.log (955604075691 / 500000000000)) := by
  have h := reflection_log_9957_neg
  have he : Real.log (955604075691 / 500000000000) = -Real.log (500000000000 / 955604075691) := by
    rw [show ((955604075691 / 500000000000) : ℝ) = ((500000000000 / 955604075691) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9958_neg : (649953571 / 1000000000) ≤ -Real.log (250000000000 / 478862973761) ∧
    -Real.log (250000000000 / 478862973761) ≤ (162488393 / 250000000) := by
  have h := checkLog_sound (w := (228862973761 / 728862973761)) (n := 12)
    (lo := (649953571 / 1000000000)) (hi := (162488393 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((478862973761 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(478862973761 / 250000000000) = 1/(250000000000 / 478862973761) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9958 : Bounds (649953571 / 1000000000) (162488393 / 250000000) (Real.log (478862973761 / 250000000000)) := by
  have h := reflection_log_9958_neg
  have he : Real.log (478862973761 / 250000000000) = -Real.log (250000000000 / 478862973761) := by
    rw [show ((478862973761 / 250000000000) : ℝ) = ((250000000000 / 478862973761) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9959_neg : (54767333 / 200000000) ≤ -Real.log (200 / 263) ∧
    -Real.log (200 / 263) ≤ (136918333 / 500000000) := by
  have h := checkLog_sound (w := (63 / 463)) (n := 12)
    (lo := (54767333 / 200000000)) (hi := (136918333 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((263 / 200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(263 / 200) = 1/(200 / 263) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9959 : Bounds (54767333 / 200000000) (136918333 / 500000000) (Real.log (263 / 200)) := by
  have h := reflection_log_9959_neg
  have he : Real.log (263 / 200) = -Real.log (200 / 263) := by
    rw [show ((263 / 200) : ℝ) = ((200 / 263) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9960_neg : (9458411 / 25000000) ≤ -Real.log (137 / 200) ∧
    -Real.log (137 / 200) ≤ (378336441 / 1000000000) := by
  have h := checkLog_sound (w := (63 / 337)) (n := 12)
    (lo := (9458411 / 25000000)) (hi := (378336441 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200 / 137) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200 / 137) = 1/(137 / 200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9960 : Bounds (-378336441 / 1000000000) (-9458411 / 25000000) (Real.log (137 / 200)) := by
  have h := reflection_log_9960_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9961_neg : (6299 / 20000000) ≤ -Real.log (200000 / 200063) ∧
    -Real.log (200000 / 200063) ≤ (314951 / 1000000000) := by
  have h := checkLog_sound (w := (63 / 400063)) (n := 12)
    (lo := (6299 / 20000000)) (hi := (314951 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200063 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200063 / 200000) = 1/(200000 / 200063) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9961 : Bounds (6299 / 20000000) (314951 / 1000000000) (Real.log (200063 / 200000)) := by
  have h := reflection_log_9961_neg
  have he : Real.log (200063 / 200000) = -Real.log (200000 / 200063) := by
    rw [show ((200063 / 200000) : ℝ) = ((200000 / 200063) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9962_neg : (315049 / 1000000000) ≤ -Real.log (199937 / 200000) ∧
    -Real.log (199937 / 200000) ≤ (6301 / 20000000) := by
  have h := checkLog_sound (w := (63 / 399937)) (n := 12)
    (lo := (315049 / 1000000000)) (hi := (6301 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 199937) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 199937) = 1/(199937 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9962 : Bounds (-6301 / 20000000) (-315049 / 1000000000) (Real.log (199937 / 200000)) := by
  have h := reflection_log_9962_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9963_neg : (74089729 / 500000000) ≤ -Real.log (1000000 / 1159721) ∧
    -Real.log (1000000 / 1159721) ≤ (148179459 / 1000000000) := by
  have h := checkLog_sound (w := (159721 / 2159721)) (n := 12)
    (lo := (74089729 / 500000000)) (hi := (148179459 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1159721 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1159721 / 1000000) = 1/(1000000 / 1159721) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9963 : Bounds (74089729 / 500000000) (148179459 / 1000000000) (Real.log (1159721 / 1000000)) := by
  have h := reflection_log_9963_neg
  have he : Real.log (1159721 / 1000000) = -Real.log (1000000 / 1159721) := by
    rw [show ((1159721 / 1000000) : ℝ) = ((1000000 / 1159721) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9964_neg : (174021299 / 1000000000) ≤ -Real.log (840279 / 1000000) ∧
    -Real.log (840279 / 1000000) ≤ (1740213 / 10000000) := by
  have h := checkLog_sound (w := (159721 / 1840279)) (n := 12)
    (lo := (174021299 / 1000000000)) (hi := (1740213 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 840279) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 840279) = 1/(840279 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9964 : Bounds (-1740213 / 10000000) (-174021299 / 1000000000) (Real.log (840279 / 1000000)) := by
  have h := reflection_log_9964_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9965_neg : (29780357 / 200000000) ≤ -Real.log (1000000 / 1160559) ∧
    -Real.log (1000000 / 1160559) ≤ (74450893 / 500000000) := by
  have h := checkLog_sound (w := (160559 / 2160559)) (n := 12)
    (lo := (29780357 / 200000000)) (hi := (74450893 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1160559 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1160559 / 1000000) = 1/(1000000 / 1160559) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9965 : Bounds (29780357 / 200000000) (74450893 / 500000000) (Real.log (1160559 / 1000000)) := by
  have h := reflection_log_9965_neg
  have he : Real.log (1160559 / 1000000) = -Real.log (1000000 / 1160559) := by
    rw [show ((1160559 / 1000000) : ℝ) = ((1000000 / 1160559) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9966_neg : (43754771 / 250000000) ≤ -Real.log (839441 / 1000000) ∧
    -Real.log (839441 / 1000000) ≤ (35003817 / 200000000) := by
  have h := checkLog_sound (w := (160559 / 1839441)) (n := 12)
    (lo := (43754771 / 250000000)) (hi := (35003817 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 839441) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 839441) = 1/(839441 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9966 : Bounds (-35003817 / 200000000) (-43754771 / 250000000) (Real.log (839441 / 1000000)) := by
  have h := reflection_log_9966_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9967_neg : (26117299 / 1000000000) ≤ -Real.log (974220807519 / 1000000000000) ∧
    -Real.log (974220807519 / 1000000000000) ≤ (261173 / 10000000) := by
  have h := checkLog_sound (w := (25779192481 / 1974220807519)) (n := 12)
    (lo := (26117299 / 1000000000)) (hi := (261173 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 974220807519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 974220807519) = 1/(974220807519 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9967 : Bounds (-261173 / 10000000) (-26117299 / 1000000000) (Real.log (974220807519 / 1000000000000)) := by
  have h := reflection_log_9967_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9968_neg : (323023 / 12500000) ≤ -Real.log (974489202159 / 1000000000000) ∧
    -Real.log (974489202159 / 1000000000000) ≤ (25841841 / 1000000000) := by
  have h := checkLog_sound (w := (25510797841 / 1974489202159)) (n := 12)
    (lo := (323023 / 12500000)) (hi := (25841841 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 974489202159) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 974489202159) = 1/(974489202159 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9968 : Bounds (-25841841 / 1000000000) (-323023 / 12500000) (Real.log (974489202159 / 1000000000000)) := by
  have h := reflection_log_9968_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9969_neg : (161100379 / 500000000) ≤ -Real.log (500000000000 / 690080913601) ∧
    -Real.log (500000000000 / 690080913601) ≤ (322200759 / 1000000000) := by
  have h := checkLog_sound (w := (190080913601 / 1190080913601)) (n := 12)
    (lo := (161100379 / 500000000)) (hi := (322200759 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((690080913601 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(690080913601 / 500000000000) = 1/(500000000000 / 690080913601) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9969 : Bounds (161100379 / 500000000) (322200759 / 1000000000) (Real.log (690080913601 / 500000000000)) := by
  have h := reflection_log_9969_neg
  have he : Real.log (690080913601 / 500000000000) = -Real.log (500000000000 / 690080913601) := by
    rw [show ((690080913601 / 500000000000) : ℝ) = ((500000000000 / 690080913601) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9970_neg : (32392087 / 100000000) ≤ -Real.log (1250000000 / 1728172379) ∧
    -Real.log (1250000000 / 1728172379) ≤ (323920871 / 1000000000) := by
  have h := checkLog_sound (w := (478172379 / 2978172379)) (n := 12)
    (lo := (32392087 / 100000000)) (hi := (323920871 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1728172379 / 1250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1728172379 / 1250000000) = 1/(1250000000 / 1728172379) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9970 : Bounds (32392087 / 100000000) (323920871 / 1000000000) (Real.log (1728172379 / 1250000000)) := by
  have h := reflection_log_9970_neg
  have he : Real.log (1728172379 / 1250000000) = -Real.log (1250000000 / 1728172379) := by
    rw [show ((1728172379 / 1250000000) : ℝ) = ((1250000000 / 1728172379) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9971_neg : (649953571 / 1000000000) ≤ -Real.log (500000000000 / 957725947521) ∧
    -Real.log (500000000000 / 957725947521) ≤ (162488393 / 250000000) := by
  have h := checkLog_sound (w := (457725947521 / 1457725947521)) (n := 12)
    (lo := (649953571 / 1000000000)) (hi := (162488393 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((957725947521 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(957725947521 / 500000000000) = 1/(500000000000 / 957725947521) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9971 : Bounds (649953571 / 1000000000) (162488393 / 250000000) (Real.log (957725947521 / 500000000000)) := by
  have h := reflection_log_9971_neg
  have he : Real.log (957725947521 / 500000000000) = -Real.log (500000000000 / 957725947521) := by
    rw [show ((957725947521 / 500000000000) : ℝ) = ((500000000000 / 957725947521) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9972_neg : (326086553 / 500000000) ≤ -Real.log (500000000000 / 959854014599) ∧
    -Real.log (500000000000 / 959854014599) ≤ (652173107 / 1000000000) := by
  have h := checkLog_sound (w := (459854014599 / 1459854014599)) (n := 12)
    (lo := (326086553 / 500000000)) (hi := (652173107 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((959854014599 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(959854014599 / 500000000000) = 1/(500000000000 / 959854014599) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9972 : Bounds (326086553 / 500000000) (652173107 / 1000000000) (Real.log (959854014599 / 500000000000)) := by
  have h := reflection_log_9972_neg
  have he : Real.log (959854014599 / 500000000000) = -Real.log (500000000000 / 959854014599) := by
    rw [show ((959854014599 / 500000000000) : ℝ) = ((500000000000 / 959854014599) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9973_neg : (8581151 / 31250000) ≤ -Real.log (250 / 329) ∧
    -Real.log (250 / 329) ≤ (274596833 / 1000000000) := by
  have h := checkLog_sound (w := (79 / 579)) (n := 12)
    (lo := (8581151 / 31250000)) (hi := (274596833 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((329 / 250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(329 / 250) = 1/(250 / 329) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9973 : Bounds (8581151 / 31250000) (274596833 / 1000000000) (Real.log (329 / 250)) := by
  have h := reflection_log_9973_neg
  have he : Real.log (329 / 250) = -Real.log (250 / 329) := by
    rw [show ((329 / 250) : ℝ) = ((250 / 329) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9974_neg : (379797361 / 1000000000) ≤ -Real.log (171 / 250) ∧
    -Real.log (171 / 250) ≤ (189898681 / 500000000) := by
  have h := checkLog_sound (w := (79 / 421)) (n := 12)
    (lo := (379797361 / 1000000000)) (hi := (189898681 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250 / 171) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250 / 171) = 1/(171 / 250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9974 : Bounds (-189898681 / 500000000) (-379797361 / 1000000000) (Real.log (171 / 250)) := by
  have h := reflection_log_9974_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9975_neg : (6319 / 20000000) ≤ -Real.log (250000 / 250079) ∧
    -Real.log (250000 / 250079) ≤ (315951 / 1000000000) := by
  have h := checkLog_sound (w := (79 / 500079)) (n := 12)
    (lo := (6319 / 20000000)) (hi := (315951 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250079 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250079 / 250000) = 1/(250000 / 250079) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9975 : Bounds (6319 / 20000000) (315951 / 1000000000) (Real.log (250079 / 250000)) := by
  have h := reflection_log_9975_neg
  have he : Real.log (250079 / 250000) = -Real.log (250000 / 250079) := by
    rw [show ((250079 / 250000) : ℝ) = ((250000 / 250079) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9976_neg : (316049 / 1000000000) ≤ -Real.log (249921 / 250000) ∧
    -Real.log (249921 / 250000) ≤ (6321 / 20000000) := by
  have h := checkLog_sound (w := (79 / 499921)) (n := 12)
    (lo := (316049 / 1000000000)) (hi := (6321 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 249921) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 249921) = 1/(249921 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9976 : Bounds (-6321 / 20000000) (-316049 / 1000000000) (Real.log (249921 / 250000)) := by
  have h := reflection_log_9976_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9977_neg : (148634637 / 1000000000) ≤ -Real.log (1000000 / 1160249) ∧
    -Real.log (1000000 / 1160249) ≤ (74317319 / 500000000) := by
  have h := checkLog_sound (w := (160249 / 2160249)) (n := 12)
    (lo := (148634637 / 1000000000)) (hi := (74317319 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1160249 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1160249 / 1000000) = 1/(1000000 / 1160249) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9977 : Bounds (148634637 / 1000000000) (74317319 / 500000000) (Real.log (1160249 / 1000000)) := by
  have h := reflection_log_9977_neg
  have he : Real.log (1160249 / 1000000) = -Real.log (1000000 / 1160249) := by
    rw [show ((1160249 / 1000000) : ℝ) = ((1000000 / 1160249) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9978_neg : (174649859 / 1000000000) ≤ -Real.log (839751 / 1000000) ∧
    -Real.log (839751 / 1000000) ≤ (8732493 / 50000000) := by
  have h := checkLog_sound (w := (160249 / 1839751)) (n := 12)
    (lo := (174649859 / 1000000000)) (hi := (8732493 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 839751) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 839751) = 1/(839751 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9978 : Bounds (-8732493 / 50000000) (-174649859 / 1000000000) (Real.log (839751 / 1000000)) := by
  have h := reflection_log_9978_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9979_neg : (29871327 / 200000000) ≤ -Real.log (1000000 / 1161087) ∧
    -Real.log (1000000 / 1161087) ≤ (37339159 / 250000000) := by
  have h := checkLog_sound (w := (161087 / 2161087)) (n := 12)
    (lo := (29871327 / 200000000)) (hi := (37339159 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1161087 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1161087 / 1000000) = 1/(1000000 / 1161087) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9979 : Bounds (29871327 / 200000000) (37339159 / 250000000) (Real.log (1161087 / 1000000)) := by
  have h := reflection_log_9979_neg
  have he : Real.log (1161087 / 1000000) = -Real.log (1000000 / 1161087) := by
    rw [show ((1161087 / 1000000) : ℝ) = ((1000000 / 1161087) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9980_neg : (10978017 / 62500000) ≤ -Real.log (838913 / 1000000) ∧
    -Real.log (838913 / 1000000) ≤ (175648273 / 1000000000) := by
  have h := checkLog_sound (w := (161087 / 1838913)) (n := 12)
    (lo := (10978017 / 62500000)) (hi := (175648273 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 838913) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 838913) = 1/(838913 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9980 : Bounds (-175648273 / 1000000000) (-10978017 / 62500000) (Real.log (838913 / 1000000)) := by
  have h := reflection_log_9980_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9981_neg : (26291637 / 1000000000) ≤ -Real.log (974050978431 / 1000000000000) ∧
    -Real.log (974050978431 / 1000000000000) ≤ (13145819 / 500000000) := by
  have h := checkLog_sound (w := (25949021569 / 1974050978431)) (n := 12)
    (lo := (26291637 / 1000000000)) (hi := (13145819 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 974050978431) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 974050978431) = 1/(974050978431 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9981 : Bounds (-13145819 / 500000000) (-26291637 / 1000000000) (Real.log (974050978431 / 1000000000000)) := by
  have h := reflection_log_9981_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9982_neg : (13007611 / 500000000) ≤ -Real.log (974320257999 / 1000000000000) ∧
    -Real.log (974320257999 / 1000000000000) ≤ (26015223 / 1000000000) := by
  have h := checkLog_sound (w := (25679742001 / 1974320257999)) (n := 12)
    (lo := (13007611 / 500000000)) (hi := (26015223 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 974320257999) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 974320257999) = 1/(974320257999 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9982 : Bounds (-26015223 / 1000000000) (-13007611 / 500000000) (Real.log (974320257999 / 1000000000000)) := by
  have h := reflection_log_9982_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9983_neg : (20205281 / 62500000) ≤ -Real.log (50000000000 / 69082918627) ∧
    -Real.log (50000000000 / 69082918627) ≤ (323284497 / 1000000000) := by
  have h := checkLog_sound (w := (19082918627 / 119082918627)) (n := 12)
    (lo := (20205281 / 62500000)) (hi := (323284497 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((69082918627 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(69082918627 / 50000000000) = 1/(50000000000 / 69082918627) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9983 : Bounds (20205281 / 62500000) (323284497 / 1000000000) (Real.log (69082918627 / 50000000000)) := by
  have h := reflection_log_9983_neg
  have he : Real.log (69082918627 / 50000000000) = -Real.log (50000000000 / 69082918627) := by
    rw [show ((69082918627 / 50000000000) : ℝ) = ((50000000000 / 69082918627) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily
