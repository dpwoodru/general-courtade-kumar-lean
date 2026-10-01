import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_1024_neg : (39403 / 250000000) ≤ -Real.log (1249803 / 1250000) ∧
    -Real.log (1249803 / 1250000) ≤ (157613 / 1000000000) := by
  have h := checkLog_sound (w := (197 / 2499803)) (n := 12)
    (lo := (39403 / 250000000)) (hi := (157613 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250000 / 1249803) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1250000 / 1249803) = 1/(1249803 / 1250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1024 : Bounds (-157613 / 1000000000) (-39403 / 250000000) (Real.log (1249803 / 1250000)) := by
  have h := reflection_log_1024_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1025_neg : (38029391 / 500000000) ≤ -Real.log (500000 / 539513) ∧
    -Real.log (500000 / 539513) ≤ (76058783 / 1000000000) := by
  have h := checkLog_sound (w := (39513 / 1039513)) (n := 12)
    (lo := (38029391 / 500000000)) (hi := (76058783 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((539513 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(539513 / 500000) = 1/(500000 / 539513) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1025 : Bounds (38029391 / 500000000) (76058783 / 1000000000) (Real.log (539513 / 500000)) := by
  have h := reflection_log_1025_neg
  have he : Real.log (539513 / 500000) = -Real.log (500000 / 539513) := by
    rw [show ((539513 / 500000) : ℝ) = ((500000 / 539513) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1026_neg : (82323473 / 1000000000) ≤ -Real.log (460487 / 500000) ∧
    -Real.log (460487 / 500000) ≤ (41161737 / 500000000) := by
  have h := checkLog_sound (w := (39513 / 960487)) (n := 12)
    (lo := (82323473 / 1000000000)) (hi := (41161737 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 460487) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 460487) = 1/(460487 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1026 : Bounds (-41161737 / 500000000) (-82323473 / 1000000000) (Real.log (460487 / 500000)) := by
  have h := reflection_log_1026_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1027_neg : (7625153 / 100000000) ≤ -Real.log (500000 / 539617) ∧
    -Real.log (500000 / 539617) ≤ (76251531 / 1000000000) := by
  have h := checkLog_sound (w := (39617 / 1039617)) (n := 12)
    (lo := (7625153 / 100000000)) (hi := (76251531 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((539617 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(539617 / 500000) = 1/(500000 / 539617) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1027 : Bounds (7625153 / 100000000) (76251531 / 1000000000) (Real.log (539617 / 500000)) := by
  have h := reflection_log_1027_neg
  have he : Real.log (539617 / 500000) = -Real.log (500000 / 539617) := by
    rw [show ((539617 / 500000) : ℝ) = ((500000 / 539617) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1028_neg : (41274673 / 500000000) ≤ -Real.log (460383 / 500000) ∧
    -Real.log (460383 / 500000) ≤ (82549347 / 1000000000) := by
  have h := checkLog_sound (w := (39617 / 960383)) (n := 12)
    (lo := (41274673 / 500000000)) (hi := (82549347 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 460383) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 460383) = 1/(460383 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1028 : Bounds (-82549347 / 1000000000) (-41274673 / 500000000) (Real.log (460383 / 500000)) := by
  have h := reflection_log_1028_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1029_neg : (787227 / 125000000) ≤ -Real.log (248430493311 / 250000000000) ∧
    -Real.log (248430493311 / 250000000000) ≤ (6297817 / 1000000000) := by
  have h := checkLog_sound (w := (1569506689 / 498430493311)) (n := 12)
    (lo := (787227 / 125000000)) (hi := (6297817 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248430493311) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248430493311) = 1/(248430493311 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1029 : Bounds (-6297817 / 1000000000) (-787227 / 125000000) (Real.log (248430493311 / 250000000000)) := by
  have h := reflection_log_1029_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1030_neg : (626469 / 100000000) ≤ -Real.log (248438722831 / 250000000000) ∧
    -Real.log (248438722831 / 250000000000) ≤ (6264691 / 1000000000) := by
  have h := checkLog_sound (w := (1561277169 / 498438722831)) (n := 12)
    (lo := (626469 / 100000000)) (hi := (6264691 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248438722831) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248438722831) = 1/(248438722831 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1030 : Bounds (-6264691 / 1000000000) (-626469 / 100000000) (Real.log (248438722831 / 250000000000)) := by
  have h := reflection_log_1030_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1031_neg : (31676451 / 200000000) ≤ -Real.log (500000000000 / 585806982607) ∧
    -Real.log (500000000000 / 585806982607) ≤ (9898891 / 62500000) := by
  have h := checkLog_sound (w := (85806982607 / 1085806982607)) (n := 12)
    (lo := (31676451 / 200000000)) (hi := (9898891 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((585806982607 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(585806982607 / 500000000000) = 1/(500000000000 / 585806982607) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1031 : Bounds (31676451 / 200000000) (9898891 / 62500000) (Real.log (585806982607 / 500000000000)) := by
  have h := reflection_log_1031_neg
  have he : Real.log (585806982607 / 500000000000) = -Real.log (500000000000 / 585806982607) := by
    rw [show ((585806982607 / 500000000000) : ℝ) = ((500000000000 / 585806982607) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1032_neg : (39700219 / 250000000) ≤ -Real.log (25000000000 / 29302613259) ∧
    -Real.log (25000000000 / 29302613259) ≤ (158800877 / 1000000000) := by
  have h := checkLog_sound (w := (4302613259 / 54302613259)) (n := 12)
    (lo := (39700219 / 250000000)) (hi := (158800877 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((29302613259 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(29302613259 / 25000000000) = 1/(25000000000 / 29302613259) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1032 : Bounds (39700219 / 250000000) (158800877 / 1000000000) (Real.log (29302613259 / 25000000000)) := by
  have h := reflection_log_1032_neg
  have he : Real.log (29302613259 / 25000000000) = -Real.log (25000000000 / 29302613259) := by
    rw [show ((29302613259 / 25000000000) : ℝ) = ((25000000000 / 29302613259) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1033_neg : (317644123 / 1000000000) ≤ -Real.log (250000000000 / 343471810089) ∧
    -Real.log (250000000000 / 343471810089) ≤ (79411031 / 250000000) := by
  have h := checkLog_sound (w := (93471810089 / 593471810089)) (n := 12)
    (lo := (317644123 / 1000000000)) (hi := (79411031 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((343471810089 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(343471810089 / 250000000000) = 1/(250000000000 / 343471810089) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1033 : Bounds (317644123 / 1000000000) (79411031 / 250000000) (Real.log (343471810089 / 250000000000)) := by
  have h := reflection_log_1033_neg
  have he : Real.log (343471810089 / 250000000000) = -Real.log (250000000000 / 343471810089) := by
    rw [show ((343471810089 / 250000000000) : ℝ) = ((250000000000 / 343471810089) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1034_neg : (158924607 / 500000000) ≤ -Real.log (250000000000 / 343542260209) ∧
    -Real.log (250000000000 / 343542260209) ≤ (63569843 / 200000000) := by
  have h := checkLog_sound (w := (93542260209 / 593542260209)) (n := 12)
    (lo := (158924607 / 500000000)) (hi := (63569843 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((343542260209 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(343542260209 / 250000000000) = 1/(250000000000 / 343542260209) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1034 : Bounds (158924607 / 500000000) (63569843 / 200000000) (Real.log (343542260209 / 250000000000)) := by
  have h := reflection_log_1034_neg
  have he : Real.log (343542260209 / 250000000000) = -Real.log (250000000000 / 343542260209) := by
    rw [show ((343542260209 / 250000000000) : ℝ) = ((250000000000 / 343542260209) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1035_neg : (73217639 / 500000000) ≤ -Real.log (10000 / 11577) ∧
    -Real.log (10000 / 11577) ≤ (146435279 / 1000000000) := by
  have h := checkLog_sound (w := (1577 / 21577)) (n := 12)
    (lo := (73217639 / 500000000)) (hi := (146435279 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11577 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11577 / 10000) = 1/(10000 / 11577) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1035 : Bounds (73217639 / 500000000) (146435279 / 1000000000) (Real.log (11577 / 10000)) := by
  have h := reflection_log_1035_neg
  have he : Real.log (11577 / 10000) = -Real.log (10000 / 11577) := by
    rw [show ((11577 / 10000) : ℝ) = ((10000 / 11577) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1036_neg : (171619033 / 1000000000) ≤ -Real.log (8423 / 10000) ∧
    -Real.log (8423 / 10000) ≤ (85809517 / 500000000) := by
  have h := checkLog_sound (w := (1577 / 18423)) (n := 12)
    (lo := (171619033 / 1000000000)) (hi := (85809517 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8423) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8423) = 1/(8423 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1036 : Bounds (-85809517 / 500000000) (-171619033 / 1000000000) (Real.log (8423 / 10000)) := by
  have h := reflection_log_1036_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1037_neg : (157687 / 1000000000) ≤ -Real.log (10000000 / 10001577) ∧
    -Real.log (10000000 / 10001577) ≤ (19711 / 125000000) := by
  have h := checkLog_sound (w := (1577 / 20001577)) (n := 12)
    (lo := (157687 / 1000000000)) (hi := (19711 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001577 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001577 / 10000000) = 1/(10000000 / 10001577) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1037 : Bounds (157687 / 1000000000) (19711 / 125000000) (Real.log (10001577 / 10000000)) := by
  have h := reflection_log_1037_neg
  have he : Real.log (10001577 / 10000000) = -Real.log (10000000 / 10001577) := by
    rw [show ((10001577 / 10000000) : ℝ) = ((10000000 / 10001577) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1038_neg : (9857 / 62500000) ≤ -Real.log (9998423 / 10000000) ∧
    -Real.log (9998423 / 10000000) ≤ (157713 / 1000000000) := by
  have h := checkLog_sound (w := (1577 / 19998423)) (n := 12)
    (lo := (9857 / 62500000)) (hi := (157713 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998423) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998423) = 1/(9998423 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1038 : Bounds (-157713 / 1000000000) (-9857 / 62500000) (Real.log (9998423 / 10000000)) := by
  have h := reflection_log_1038_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1039_neg : (38053023 / 500000000) ≤ -Real.log (1000000 / 1079077) ∧
    -Real.log (1000000 / 1079077) ≤ (76106047 / 1000000000) := by
  have h := checkLog_sound (w := (79077 / 2079077)) (n := 12)
    (lo := (38053023 / 500000000)) (hi := (76106047 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1079077 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1079077 / 1000000) = 1/(1000000 / 1079077) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1039 : Bounds (38053023 / 500000000) (76106047 / 1000000000) (Real.log (1079077 / 1000000)) := by
  have h := reflection_log_1039_neg
  have he : Real.log (1079077 / 1000000) = -Real.log (1000000 / 1079077) := by
    rw [show ((1079077 / 1000000) : ℝ) = ((1000000 / 1079077) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1040_neg : (1647577 / 20000000) ≤ -Real.log (920923 / 1000000) ∧
    -Real.log (920923 / 1000000) ≤ (82378851 / 1000000000) := by
  have h := checkLog_sound (w := (79077 / 1920923)) (n := 12)
    (lo := (1647577 / 20000000)) (hi := (82378851 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 920923) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 920923) = 1/(920923 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1040 : Bounds (-82378851 / 1000000000) (-1647577 / 20000000) (Real.log (920923 / 1000000)) := by
  have h := reflection_log_1040_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1041_neg : (2384337 / 31250000) ≤ -Real.log (200000 / 215857) ∧
    -Real.log (200000 / 215857) ≤ (15259757 / 200000000) := by
  have h := checkLog_sound (w := (15857 / 415857)) (n := 12)
    (lo := (2384337 / 31250000)) (hi := (15259757 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((215857 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(215857 / 200000) = 1/(200000 / 215857) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1041 : Bounds (2384337 / 31250000) (15259757 / 200000000) (Real.log (215857 / 200000)) := by
  have h := reflection_log_1041_neg
  have he : Real.log (215857 / 200000) = -Real.log (200000 / 215857) := by
    rw [show ((215857 / 200000) : ℝ) = ((200000 / 215857) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1042_neg : (1290699 / 15625000) ≤ -Real.log (184143 / 200000) ∧
    -Real.log (184143 / 200000) ≤ (82604737 / 1000000000) := by
  have h := checkLog_sound (w := (15857 / 384143)) (n := 12)
    (lo := (1290699 / 15625000)) (hi := (82604737 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 184143) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 184143) = 1/(184143 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1042 : Bounds (-82604737 / 1000000000) (-1290699 / 15625000) (Real.log (184143 / 200000)) := by
  have h := reflection_log_1042_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1043_neg : (197061 / 31250000) ≤ -Real.log (39748555551 / 40000000000) ∧
    -Real.log (39748555551 / 40000000000) ≤ (6305953 / 1000000000) := by
  have h := checkLog_sound (w := (251444449 / 79748555551)) (n := 12)
    (lo := (197061 / 31250000)) (hi := (6305953 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39748555551) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39748555551) = 1/(39748555551 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1043 : Bounds (-6305953 / 1000000000) (-197061 / 31250000) (Real.log (39748555551 / 40000000000)) := by
  have h := reflection_log_1043_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1044_neg : (1568201 / 250000000) ≤ -Real.log (993746828071 / 1000000000000) ∧
    -Real.log (993746828071 / 1000000000000) ≤ (1254561 / 200000000) := by
  have h := checkLog_sound (w := (6253171929 / 1993746828071)) (n := 12)
    (lo := (1568201 / 250000000)) (hi := (1254561 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993746828071) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993746828071) = 1/(993746828071 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1044 : Bounds (-1254561 / 200000000) (-1568201 / 250000000) (Real.log (993746828071 / 1000000000000)) := by
  have h := reflection_log_1044_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1045_neg : (158484897 / 1000000000) ≤ -Real.log (250000000000 / 292933556877) ∧
    -Real.log (250000000000 / 292933556877) ≤ (79242449 / 500000000) := by
  have h := checkLog_sound (w := (42933556877 / 542933556877)) (n := 12)
    (lo := (158484897 / 1000000000)) (hi := (79242449 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((292933556877 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(292933556877 / 250000000000) = 1/(250000000000 / 292933556877) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1045 : Bounds (158484897 / 1000000000) (79242449 / 500000000) (Real.log (292933556877 / 250000000000)) := by
  have h := reflection_log_1045_neg
  have he : Real.log (292933556877 / 250000000000) = -Real.log (250000000000 / 292933556877) := by
    rw [show ((292933556877 / 250000000000) : ℝ) = ((250000000000 / 292933556877) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1046_neg : (158903521 / 1000000000) ≤ -Real.log (500000000000 / 586112423497) ∧
    -Real.log (500000000000 / 586112423497) ≤ (79451761 / 500000000) := by
  have h := checkLog_sound (w := (86112423497 / 1086112423497)) (n := 12)
    (lo := (158903521 / 1000000000)) (hi := (79451761 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((586112423497 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(586112423497 / 500000000000) = 1/(500000000000 / 586112423497) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1046 : Bounds (158903521 / 1000000000) (79451761 / 500000000) (Real.log (586112423497 / 500000000000)) := by
  have h := reflection_log_1046_neg
  have he : Real.log (586112423497 / 500000000000) = -Real.log (500000000000 / 586112423497) := by
    rw [show ((586112423497 / 500000000000) : ℝ) = ((500000000000 / 586112423497) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1047_neg : (158924607 / 500000000) ≤ -Real.log (500000000000 / 687084520417) ∧
    -Real.log (500000000000 / 687084520417) ≤ (63569843 / 200000000) := by
  have h := checkLog_sound (w := (187084520417 / 1187084520417)) (n := 12)
    (lo := (158924607 / 500000000)) (hi := (63569843 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((687084520417 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(687084520417 / 500000000000) = 1/(500000000000 / 687084520417) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1047 : Bounds (158924607 / 500000000) (63569843 / 200000000) (Real.log (687084520417 / 500000000000)) := by
  have h := reflection_log_1047_neg
  have he : Real.log (687084520417 / 500000000000) = -Real.log (500000000000 / 687084520417) := by
    rw [show ((687084520417 / 500000000000) : ℝ) = ((500000000000 / 687084520417) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1048_neg : (318054311 / 1000000000) ≤ -Real.log (250000000000 / 343612727057) ∧
    -Real.log (250000000000 / 343612727057) ≤ (39756789 / 125000000) := by
  have h := checkLog_sound (w := (93612727057 / 593612727057)) (n := 12)
    (lo := (318054311 / 1000000000)) (hi := (39756789 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((343612727057 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(343612727057 / 250000000000) = 1/(250000000000 / 343612727057) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1048 : Bounds (318054311 / 1000000000) (39756789 / 125000000) (Real.log (343612727057 / 250000000000)) := by
  have h := reflection_log_1048_neg
  have he : Real.log (343612727057 / 250000000000) = -Real.log (250000000000 / 343612727057) := by
    rw [show ((343612727057 / 250000000000) : ℝ) = ((250000000000 / 343612727057) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1049_neg : (36630413 / 250000000) ≤ -Real.log (5000 / 5789) ∧
    -Real.log (5000 / 5789) ≤ (146521653 / 1000000000) := by
  have h := checkLog_sound (w := (789 / 10789)) (n := 12)
    (lo := (36630413 / 250000000)) (hi := (146521653 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5789 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5789 / 5000) = 1/(5000 / 5789) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1049 : Bounds (36630413 / 250000000) (146521653 / 1000000000) (Real.log (5789 / 5000)) := by
  have h := reflection_log_1049_neg
  have he : Real.log (5789 / 5000) = -Real.log (5000 / 5789) := by
    rw [show ((5789 / 5000) : ℝ) = ((5000 / 5789) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1050_neg : (171737763 / 1000000000) ≤ -Real.log (4211 / 5000) ∧
    -Real.log (4211 / 5000) ≤ (42934441 / 250000000) := by
  have h := checkLog_sound (w := (789 / 9211)) (n := 12)
    (lo := (171737763 / 1000000000)) (hi := (42934441 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4211) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4211) = 1/(4211 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1050 : Bounds (-42934441 / 250000000) (-171737763 / 1000000000) (Real.log (4211 / 5000)) := by
  have h := reflection_log_1050_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1051_neg : (157787 / 1000000000) ≤ -Real.log (5000000 / 5000789) ∧
    -Real.log (5000000 / 5000789) ≤ (39447 / 250000000) := by
  have h := checkLog_sound (w := (789 / 10000789)) (n := 12)
    (lo := (157787 / 1000000000)) (hi := (39447 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000789 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000789 / 5000000) = 1/(5000000 / 5000789) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1051 : Bounds (157787 / 1000000000) (39447 / 250000000) (Real.log (5000789 / 5000000)) := by
  have h := reflection_log_1051_neg
  have he : Real.log (5000789 / 5000000) = -Real.log (5000000 / 5000789) := by
    rw [show ((5000789 / 5000000) : ℝ) = ((5000000 / 5000789) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1052_neg : (39453 / 250000000) ≤ -Real.log (4999211 / 5000000) ∧
    -Real.log (4999211 / 5000000) ≤ (157813 / 1000000000) := by
  have h := checkLog_sound (w := (789 / 9999211)) (n := 12)
    (lo := (39453 / 250000000)) (hi := (157813 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999211) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999211) = 1/(4999211 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1052 : Bounds (-157813 / 1000000000) (-39453 / 250000000) (Real.log (4999211 / 5000000)) := by
  have h := reflection_log_1052_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1053_neg : (3807619 / 50000000) ≤ -Real.log (1000000 / 1079127) ∧
    -Real.log (1000000 / 1079127) ≤ (76152381 / 1000000000) := by
  have h := checkLog_sound (w := (79127 / 2079127)) (n := 12)
    (lo := (3807619 / 50000000)) (hi := (76152381 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1079127 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1079127 / 1000000) = 1/(1000000 / 1079127) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1053 : Bounds (3807619 / 50000000) (76152381 / 1000000000) (Real.log (1079127 / 1000000)) := by
  have h := reflection_log_1053_neg
  have he : Real.log (1079127 / 1000000) = -Real.log (1000000 / 1079127) := by
    rw [show ((1079127 / 1000000) : ℝ) = ((1000000 / 1079127) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1054_neg : (16486629 / 200000000) ≤ -Real.log (920873 / 1000000) ∧
    -Real.log (920873 / 1000000) ≤ (41216573 / 500000000) := by
  have h := checkLog_sound (w := (79127 / 1920873)) (n := 12)
    (lo := (16486629 / 200000000)) (hi := (41216573 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 920873) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 920873) = 1/(920873 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1054 : Bounds (-41216573 / 500000000) (-16486629 / 200000000) (Real.log (920873 / 1000000)) := by
  have h := reflection_log_1054_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1055_neg : (76346037 / 1000000000) ≤ -Real.log (125000 / 134917) ∧
    -Real.log (125000 / 134917) ≤ (38173019 / 500000000) := by
  have h := checkLog_sound (w := (9917 / 259917)) (n := 12)
    (lo := (76346037 / 1000000000)) (hi := (38173019 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((134917 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(134917 / 125000) = 1/(125000 / 134917) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1055 : Bounds (76346037 / 1000000000) (38173019 / 500000000) (Real.log (134917 / 125000)) := by
  have h := reflection_log_1055_neg
  have he : Real.log (134917 / 125000) = -Real.log (125000 / 134917) := by
    rw [show ((134917 / 125000) : ℝ) = ((125000 / 134917) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1056_neg : (8266013 / 100000000) ≤ -Real.log (115083 / 125000) ∧
    -Real.log (115083 / 125000) ≤ (82660131 / 1000000000) := by
  have h := checkLog_sound (w := (9917 / 240083)) (n := 12)
    (lo := (8266013 / 100000000)) (hi := (82660131 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 115083) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 115083) = 1/(115083 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1056 : Bounds (-82660131 / 1000000000) (-8266013 / 100000000) (Real.log (115083 / 125000)) := by
  have h := reflection_log_1056_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1057_neg : (1578523 / 250000000) ≤ -Real.log (15526653111 / 15625000000) ∧
    -Real.log (15526653111 / 15625000000) ≤ (6314093 / 1000000000) := by
  have h := checkLog_sound (w := (98346889 / 31151653111)) (n := 12)
    (lo := (1578523 / 250000000)) (hi := (6314093 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 15526653111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 15526653111) = 1/(15526653111 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1057 : Bounds (-6314093 / 1000000000) (-1578523 / 250000000) (Real.log (15526653111 / 15625000000)) := by
  have h := reflection_log_1057_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1058_neg : (1570191 / 250000000) ≤ -Real.log (993738917871 / 1000000000000) ∧
    -Real.log (993738917871 / 1000000000000) ≤ (1256153 / 200000000) := by
  have h := checkLog_sound (w := (6261082129 / 1993738917871)) (n := 12)
    (lo := (1570191 / 250000000)) (hi := (1256153 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993738917871) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993738917871) = 1/(993738917871 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1058 : Bounds (-1256153 / 200000000) (-1570191 / 250000000) (Real.log (993738917871 / 1000000000000)) := by
  have h := reflection_log_1058_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1059_neg : (79292763 / 500000000) ≤ -Real.log (125000000000 / 146481518081) ∧
    -Real.log (125000000000 / 146481518081) ≤ (158585527 / 1000000000) := by
  have h := checkLog_sound (w := (21481518081 / 271481518081)) (n := 12)
    (lo := (79292763 / 500000000)) (hi := (158585527 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((146481518081 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(146481518081 / 125000000000) = 1/(125000000000 / 146481518081) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1059 : Bounds (79292763 / 500000000) (158585527 / 1000000000) (Real.log (146481518081 / 125000000000)) := by
  have h := reflection_log_1059_neg
  have he : Real.log (146481518081 / 125000000000) = -Real.log (125000000000 / 146481518081) := by
    rw [show ((146481518081 / 125000000000) : ℝ) = ((125000000000 / 146481518081) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1060_neg : (159006167 / 1000000000) ≤ -Real.log (1562500000 / 1831789339) ∧
    -Real.log (1562500000 / 1831789339) ≤ (19875771 / 125000000) := by
  have h := checkLog_sound (w := (269289339 / 3394289339)) (n := 12)
    (lo := (159006167 / 1000000000)) (hi := (19875771 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1831789339 / 1562500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1831789339 / 1562500000) = 1/(1562500000 / 1831789339) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1060 : Bounds (159006167 / 1000000000) (19875771 / 125000000) (Real.log (1831789339 / 1562500000)) := by
  have h := reflection_log_1060_neg
  have he : Real.log (1831789339 / 1562500000) = -Real.log (1562500000 / 1831789339) := by
    rw [show ((1831789339 / 1562500000) : ℝ) = ((1562500000 / 1831789339) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1061_neg : (318054311 / 1000000000) ≤ -Real.log (500000000000 / 687225454113) ∧
    -Real.log (500000000000 / 687225454113) ≤ (39756789 / 125000000) := by
  have h := checkLog_sound (w := (187225454113 / 1187225454113)) (n := 12)
    (lo := (318054311 / 1000000000)) (hi := (39756789 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((687225454113 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(687225454113 / 500000000000) = 1/(500000000000 / 687225454113) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1061 : Bounds (318054311 / 1000000000) (39756789 / 125000000) (Real.log (687225454113 / 500000000000)) := by
  have h := reflection_log_1061_neg
  have he : Real.log (687225454113 / 500000000000) = -Real.log (500000000000 / 687225454113) := by
    rw [show ((687225454113 / 500000000000) : ℝ) = ((500000000000 / 687225454113) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1062_neg : (63651883 / 200000000) ≤ -Real.log (250000000000 / 343683210639) ∧
    -Real.log (250000000000 / 343683210639) ≤ (39782427 / 125000000) := by
  have h := checkLog_sound (w := (93683210639 / 593683210639)) (n := 12)
    (lo := (63651883 / 200000000)) (hi := (39782427 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((343683210639 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(343683210639 / 250000000000) = 1/(250000000000 / 343683210639) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1062 : Bounds (63651883 / 200000000) (39782427 / 125000000) (Real.log (343683210639 / 250000000000)) := by
  have h := reflection_log_1062_neg
  have he : Real.log (343683210639 / 250000000000) = -Real.log (250000000000 / 343683210639) := by
    rw [show ((343683210639 / 250000000000) : ℝ) = ((250000000000 / 343683210639) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1063_neg : (146608019 / 1000000000) ≤ -Real.log (10000 / 11579) ∧
    -Real.log (10000 / 11579) ≤ (7330401 / 50000000) := by
  have h := checkLog_sound (w := (1579 / 21579)) (n := 12)
    (lo := (146608019 / 1000000000)) (hi := (7330401 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11579 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11579 / 10000) = 1/(10000 / 11579) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1063 : Bounds (146608019 / 1000000000) (7330401 / 50000000) (Real.log (11579 / 10000)) := by
  have h := reflection_log_1063_neg
  have he : Real.log (11579 / 10000) = -Real.log (10000 / 11579) := by
    rw [show ((11579 / 10000) : ℝ) = ((10000 / 11579) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1064_neg : (85928253 / 500000000) ≤ -Real.log (8421 / 10000) ∧
    -Real.log (8421 / 10000) ≤ (171856507 / 1000000000) := by
  have h := checkLog_sound (w := (1579 / 18421)) (n := 12)
    (lo := (85928253 / 500000000)) (hi := (171856507 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8421) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8421) = 1/(8421 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1064 : Bounds (-171856507 / 1000000000) (-85928253 / 500000000) (Real.log (8421 / 10000)) := by
  have h := reflection_log_1064_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1065_neg : (157887 / 1000000000) ≤ -Real.log (10000000 / 10001579) ∧
    -Real.log (10000000 / 10001579) ≤ (2467 / 15625000) := by
  have h := checkLog_sound (w := (1579 / 20001579)) (n := 12)
    (lo := (157887 / 1000000000)) (hi := (2467 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001579 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001579 / 10000000) = 1/(10000000 / 10001579) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1065 : Bounds (157887 / 1000000000) (2467 / 15625000) (Real.log (10001579 / 10000000)) := by
  have h := reflection_log_1065_neg
  have he : Real.log (10001579 / 10000000) = -Real.log (10000000 / 10001579) := by
    rw [show ((10001579 / 10000000) : ℝ) = ((10000000 / 10001579) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1066_neg : (19739 / 125000000) ≤ -Real.log (9998421 / 10000000) ∧
    -Real.log (9998421 / 10000000) ≤ (157913 / 1000000000) := by
  have h := checkLog_sound (w := (1579 / 19998421)) (n := 12)
    (lo := (19739 / 125000000)) (hi := (157913 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998421) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998421) = 1/(9998421 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1066 : Bounds (-157913 / 1000000000) (-19739 / 125000000) (Real.log (9998421 / 10000000)) := by
  have h := reflection_log_1066_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1067_neg : (1904991 / 25000000) ≤ -Real.log (500000 / 539589) ∧
    -Real.log (500000 / 539589) ≤ (76199641 / 1000000000) := by
  have h := checkLog_sound (w := (39589 / 1039589)) (n := 12)
    (lo := (1904991 / 25000000)) (hi := (76199641 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((539589 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(539589 / 500000) = 1/(500000 / 539589) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1067 : Bounds (1904991 / 25000000) (76199641 / 1000000000) (Real.log (539589 / 500000)) := by
  have h := reflection_log_1067_neg
  have he : Real.log (539589 / 500000) = -Real.log (500000 / 539589) := by
    rw [show ((539589 / 500000) : ℝ) = ((500000 / 539589) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1068_neg : (82488529 / 1000000000) ≤ -Real.log (460411 / 500000) ∧
    -Real.log (460411 / 500000) ≤ (8248853 / 100000000) := by
  have h := checkLog_sound (w := (39589 / 960411)) (n := 12)
    (lo := (82488529 / 1000000000)) (hi := (8248853 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 460411) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 460411) = 1/(460411 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1068 : Bounds (-8248853 / 100000000) (-82488529 / 1000000000) (Real.log (460411 / 500000)) := by
  have h := reflection_log_1068_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1069_neg : (76393287 / 1000000000) ≤ -Real.log (1000000 / 1079387) ∧
    -Real.log (1000000 / 1079387) ≤ (9549161 / 125000000) := by
  have h := checkLog_sound (w := (79387 / 2079387)) (n := 12)
    (lo := (76393287 / 1000000000)) (hi := (9549161 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1079387 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1079387 / 1000000) = 1/(1000000 / 1079387) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1069 : Bounds (76393287 / 1000000000) (9549161 / 125000000) (Real.log (1079387 / 1000000)) := by
  have h := reflection_log_1069_neg
  have he : Real.log (1079387 / 1000000) = -Real.log (1000000 / 1079387) := by
    rw [show ((1079387 / 1000000) : ℝ) = ((1000000 / 1079387) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1070_neg : (41357763 / 500000000) ≤ -Real.log (920613 / 1000000) ∧
    -Real.log (920613 / 1000000) ≤ (82715527 / 1000000000) := by
  have h := checkLog_sound (w := (79387 / 1920613)) (n := 12)
    (lo := (41357763 / 500000000)) (hi := (82715527 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 920613) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 920613) = 1/(920613 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1070 : Bounds (-82715527 / 1000000000) (-41357763 / 500000000) (Real.log (920613 / 1000000)) := by
  have h := reflection_log_1070_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1071_neg : (6322239 / 1000000000) ≤ -Real.log (993697704231 / 1000000000000) ∧
    -Real.log (993697704231 / 1000000000000) ≤ (19757 / 3125000) := by
  have h := checkLog_sound (w := (6302295769 / 1993697704231)) (n := 12)
    (lo := (6322239 / 1000000000)) (hi := (19757 / 3125000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993697704231) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993697704231) = 1/(993697704231 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1071 : Bounds (-19757 / 3125000) (-6322239 / 1000000000) (Real.log (993697704231 / 1000000000000)) := by
  have h := reflection_log_1071_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1072_neg : (6288889 / 1000000000) ≤ -Real.log (248432711079 / 250000000000) ∧
    -Real.log (248432711079 / 250000000000) ≤ (628889 / 100000000) := by
  have h := checkLog_sound (w := (1567288921 / 498432711079)) (n := 12)
    (lo := (6288889 / 1000000000)) (hi := (628889 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248432711079) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248432711079) = 1/(248432711079 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1072 : Bounds (-628889 / 100000000) (-6288889 / 1000000000) (Real.log (248432711079 / 250000000000)) := by
  have h := reflection_log_1072_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1073_neg : (158688169 / 1000000000) ≤ -Real.log (250000000000 / 292993108331) ∧
    -Real.log (250000000000 / 292993108331) ≤ (15868817 / 100000000) := by
  have h := checkLog_sound (w := (42993108331 / 542993108331)) (n := 12)
    (lo := (158688169 / 1000000000)) (hi := (15868817 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((292993108331 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(292993108331 / 250000000000) = 1/(250000000000 / 292993108331) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1073 : Bounds (158688169 / 1000000000) (15868817 / 100000000) (Real.log (292993108331 / 250000000000)) := by
  have h := reflection_log_1073_neg
  have he : Real.log (292993108331 / 250000000000) = -Real.log (250000000000 / 292993108331) := by
    rw [show ((292993108331 / 250000000000) : ℝ) = ((250000000000 / 292993108331) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1074_neg : (159108813 / 1000000000) ≤ -Real.log (500000000000 / 586232760129) ∧
    -Real.log (500000000000 / 586232760129) ≤ (79554407 / 500000000) := by
  have h := checkLog_sound (w := (86232760129 / 1086232760129)) (n := 12)
    (lo := (159108813 / 1000000000)) (hi := (79554407 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((586232760129 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(586232760129 / 500000000000) = 1/(500000000000 / 586232760129) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1074 : Bounds (159108813 / 1000000000) (79554407 / 500000000) (Real.log (586232760129 / 500000000000)) := by
  have h := reflection_log_1074_neg
  have he : Real.log (586232760129 / 500000000000) = -Real.log (500000000000 / 586232760129) := by
    rw [show ((586232760129 / 500000000000) : ℝ) = ((500000000000 / 586232760129) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1075_neg : (63651883 / 200000000) ≤ -Real.log (500000000000 / 687366421277) ∧
    -Real.log (500000000000 / 687366421277) ≤ (39782427 / 125000000) := by
  have h := checkLog_sound (w := (187366421277 / 1187366421277)) (n := 12)
    (lo := (63651883 / 200000000)) (hi := (39782427 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((687366421277 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(687366421277 / 500000000000) = 1/(500000000000 / 687366421277) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1075 : Bounds (63651883 / 200000000) (39782427 / 125000000) (Real.log (687366421277 / 500000000000)) := by
  have h := reflection_log_1075_neg
  have he : Real.log (687366421277 / 500000000000) = -Real.log (500000000000 / 687366421277) := by
    rw [show ((687366421277 / 500000000000) : ℝ) = ((500000000000 / 687366421277) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1076_neg : (159232263 / 500000000) ≤ -Real.log (250000000000 / 343753710961) ∧
    -Real.log (250000000000 / 343753710961) ≤ (318464527 / 1000000000) := by
  have h := checkLog_sound (w := (93753710961 / 593753710961)) (n := 12)
    (lo := (159232263 / 500000000)) (hi := (318464527 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((343753710961 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(343753710961 / 250000000000) = 1/(250000000000 / 343753710961) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1076 : Bounds (159232263 / 500000000) (318464527 / 1000000000) (Real.log (343753710961 / 250000000000)) := by
  have h := reflection_log_1076_neg
  have he : Real.log (343753710961 / 250000000000) = -Real.log (250000000000 / 343753710961) := by
    rw [show ((343753710961 / 250000000000) : ℝ) = ((250000000000 / 343753710961) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1077_neg : (146694379 / 1000000000) ≤ -Real.log (500 / 579) ∧
    -Real.log (500 / 579) ≤ (7334719 / 50000000) := by
  have h := checkLog_sound (w := (79 / 1079)) (n := 12)
    (lo := (146694379 / 1000000000)) (hi := (7334719 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((579 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(579 / 500) = 1/(500 / 579) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1077 : Bounds (146694379 / 1000000000) (7334719 / 50000000) (Real.log (579 / 500)) := by
  have h := reflection_log_1077_neg
  have he : Real.log (579 / 500) = -Real.log (500 / 579) := by
    rw [show ((579 / 500) : ℝ) = ((500 / 579) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1078_neg : (5374227 / 31250000) ≤ -Real.log (421 / 500) ∧
    -Real.log (421 / 500) ≤ (34395053 / 200000000) := by
  have h := checkLog_sound (w := (79 / 921)) (n := 12)
    (lo := (5374227 / 31250000)) (hi := (34395053 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 421) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500 / 421) = 1/(421 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1078 : Bounds (-34395053 / 200000000) (-5374227 / 31250000) (Real.log (421 / 500)) := by
  have h := reflection_log_1078_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1079_neg : (157987 / 1000000000) ≤ -Real.log (500000 / 500079) ∧
    -Real.log (500000 / 500079) ≤ (39497 / 250000000) := by
  have h := checkLog_sound (w := (79 / 1000079)) (n := 12)
    (lo := (157987 / 1000000000)) (hi := (39497 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500079 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500079 / 500000) = 1/(500000 / 500079) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1079 : Bounds (157987 / 1000000000) (39497 / 250000000) (Real.log (500079 / 500000)) := by
  have h := reflection_log_1079_neg
  have he : Real.log (500079 / 500000) = -Real.log (500000 / 500079) := by
    rw [show ((500079 / 500000) : ℝ) = ((500000 / 500079) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1080_neg : (39503 / 250000000) ≤ -Real.log (499921 / 500000) ∧
    -Real.log (499921 / 500000) ≤ (158013 / 1000000000) := by
  have h := checkLog_sound (w := (79 / 999921)) (n := 12)
    (lo := (39503 / 250000000)) (hi := (158013 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499921) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499921) = 1/(499921 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1080 : Bounds (-158013 / 1000000000) (-39503 / 250000000) (Real.log (499921 / 500000)) := by
  have h := reflection_log_1080_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1081_neg : (7624597 / 100000000) ≤ -Real.log (250000 / 269807) ∧
    -Real.log (250000 / 269807) ≤ (76245971 / 1000000000) := by
  have h := checkLog_sound (w := (19807 / 519807)) (n := 12)
    (lo := (7624597 / 100000000)) (hi := (76245971 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((269807 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(269807 / 250000) = 1/(250000 / 269807) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1081 : Bounds (7624597 / 100000000) (76245971 / 1000000000) (Real.log (269807 / 250000)) := by
  have h := reflection_log_1081_neg
  have he : Real.log (269807 / 250000) = -Real.log (250000 / 269807) := by
    rw [show ((269807 / 250000) : ℝ) = ((250000 / 269807) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1082_neg : (8254283 / 100000000) ≤ -Real.log (230193 / 250000) ∧
    -Real.log (230193 / 250000) ≤ (82542831 / 1000000000) := by
  have h := checkLog_sound (w := (19807 / 480193)) (n := 12)
    (lo := (8254283 / 100000000)) (hi := (82542831 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 230193) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 230193) = 1/(230193 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1082 : Bounds (-82542831 / 1000000000) (-8254283 / 100000000) (Real.log (230193 / 250000)) := by
  have h := reflection_log_1082_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1083_neg : (9554951 / 125000000) ≤ -Real.log (1000000 / 1079437) ∧
    -Real.log (1000000 / 1079437) ≤ (76439609 / 1000000000) := by
  have h := checkLog_sound (w := (79437 / 2079437)) (n := 12)
    (lo := (9554951 / 125000000)) (hi := (76439609 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1079437 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1079437 / 1000000) = 1/(1000000 / 1079437) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1083 : Bounds (9554951 / 125000000) (76439609 / 1000000000) (Real.log (1079437 / 1000000)) := by
  have h := reflection_log_1083_neg
  have he : Real.log (1079437 / 1000000) = -Real.log (1000000 / 1079437) := by
    rw [show ((1079437 / 1000000) : ℝ) = ((1000000 / 1079437) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1084_neg : (82769839 / 1000000000) ≤ -Real.log (920563 / 1000000) ∧
    -Real.log (920563 / 1000000) ≤ (1034623 / 12500000) := by
  have h := checkLog_sound (w := (79437 / 1920563)) (n := 12)
    (lo := (82769839 / 1000000000)) (hi := (1034623 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 920563) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 920563) = 1/(920563 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1084 : Bounds (-1034623 / 12500000) (-82769839 / 1000000000) (Real.log (920563 / 1000000)) := by
  have h := reflection_log_1084_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1085_neg : (633023 / 100000000) ≤ -Real.log (993689763031 / 1000000000000) ∧
    -Real.log (993689763031 / 1000000000000) ≤ (6330231 / 1000000000) := by
  have h := checkLog_sound (w := (6310236969 / 1993689763031)) (n := 12)
    (lo := (633023 / 100000000)) (hi := (6330231 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993689763031) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993689763031) = 1/(993689763031 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1085 : Bounds (-6330231 / 1000000000) (-633023 / 100000000) (Real.log (993689763031 / 1000000000000)) := by
  have h := reflection_log_1085_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1086_neg : (6296859 / 1000000000) ≤ -Real.log (62107682751 / 62500000000) ∧
    -Real.log (62107682751 / 62500000000) ≤ (314843 / 50000000) := by
  have h := checkLog_sound (w := (392317249 / 124607682751)) (n := 12)
    (lo := (6296859 / 1000000000)) (hi := (314843 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 62107682751) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 62107682751) = 1/(62107682751 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1086 : Bounds (-314843 / 50000000) (-6296859 / 1000000000) (Real.log (62107682751 / 62500000000)) := by
  have h := reflection_log_1086_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1087_neg : (158788801 / 1000000000) ≤ -Real.log (62500000000 / 73255648521) ∧
    -Real.log (62500000000 / 73255648521) ≤ (79394401 / 500000000) := by
  have h := checkLog_sound (w := (10755648521 / 135755648521)) (n := 12)
    (lo := (158788801 / 1000000000)) (hi := (79394401 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((73255648521 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(73255648521 / 62500000000) = 1/(62500000000 / 73255648521) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1087 : Bounds (158788801 / 1000000000) (79394401 / 500000000) (Real.log (73255648521 / 62500000000)) := by
  have h := reflection_log_1087_neg
  have he : Real.log (73255648521 / 62500000000) = -Real.log (62500000000 / 73255648521) := by
    rw [show ((73255648521 / 62500000000) : ℝ) = ((62500000000 / 73255648521) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily
