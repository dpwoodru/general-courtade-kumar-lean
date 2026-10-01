import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_11008_neg : (56033823 / 250000000) ≤ -Real.log (799207 / 1000000) ∧
    -Real.log (799207 / 1000000) ≤ (224135293 / 1000000000) := by
  have h := checkLog_sound (w := (200793 / 1799207)) (n := 12)
    (lo := (56033823 / 250000000)) (hi := (224135293 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 799207) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 799207) = 1/(799207 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11008 : Bounds (-224135293 / 1000000000) (-56033823 / 250000000) (Real.log (799207 / 1000000)) := by
  have h := reflection_log_11008_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11009_neg : (41153121 / 1000000000) ≤ -Real.log (959682171151 / 1000000000000) ∧
    -Real.log (959682171151 / 1000000000000) ≤ (20576561 / 500000000) := by
  have h := checkLog_sound (w := (40317828849 / 1959682171151)) (n := 12)
    (lo := (41153121 / 1000000000)) (hi := (20576561 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 959682171151) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 959682171151) = 1/(959682171151 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11009 : Bounds (-20576561 / 500000000) (-41153121 / 1000000000) (Real.log (959682171151 / 1000000000000)) := by
  have h := reflection_log_11009_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11010_neg : (20383923 / 500000000) ≤ -Real.log (9600519831 / 10000000000) ∧
    -Real.log (9600519831 / 10000000000) ≤ (40767847 / 1000000000) := by
  have h := checkLog_sound (w := (399480169 / 19600519831)) (n := 12)
    (lo := (20383923 / 500000000)) (hi := (40767847 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 9600519831) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 9600519831) = 1/(9600519831 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11010 : Bounds (-40767847 / 1000000000) (-20383923 / 500000000) (Real.log (9600519831 / 10000000000)) := by
  have h := reflection_log_11010_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11011_neg : (202597141 / 500000000) ≤ -Real.log (250000000000 / 374898454001) ∧
    -Real.log (250000000000 / 374898454001) ≤ (405194283 / 1000000000) := by
  have h := checkLog_sound (w := (124898454001 / 624898454001)) (n := 12)
    (lo := (202597141 / 500000000)) (hi := (405194283 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((374898454001 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(374898454001 / 250000000000) = 1/(250000000000 / 374898454001) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11011 : Bounds (202597141 / 500000000) (405194283 / 1000000000) (Real.log (374898454001 / 250000000000)) := by
  have h := reflection_log_11011_neg
  have he : Real.log (374898454001 / 250000000000) = -Real.log (250000000000 / 374898454001) := by
    rw [show ((374898454001 / 250000000000) : ℝ) = ((250000000000 / 374898454001) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11012_neg : (50889683 / 125000000) ≤ -Real.log (25000000000 / 37562014597) ∧
    -Real.log (25000000000 / 37562014597) ≤ (81423493 / 200000000) := by
  have h := checkLog_sound (w := (12562014597 / 62562014597)) (n := 12)
    (lo := (50889683 / 125000000)) (hi := (81423493 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((37562014597 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(37562014597 / 25000000000) = 1/(25000000000 / 37562014597) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11012 : Bounds (50889683 / 125000000) (81423493 / 200000000) (Real.log (37562014597 / 25000000000)) := by
  have h := reflection_log_11012_neg
  have he : Real.log (37562014597 / 25000000000) = -Real.log (25000000000 / 37562014597) := by
    rw [show ((37562014597 / 25000000000) : ℝ) = ((25000000000 / 37562014597) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11013_neg : (821242383 / 1000000000) ≤ -Real.log (500000000000 / 1136661211129) ∧
    -Real.log (500000000000 / 1136661211129) ≤ (164248477 / 200000000) := by
  have h := checkLog_sound (w := (136661211129 / 2136661211129)) (n := 12)
    (lo := (128095203 / 1000000000)) (hi := (32023801 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1136661211129 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1136661211129 / 1000000000000) = 1/(500000000000 / 1136661211129) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11013 : Bounds (821242383 / 1000000000) (164248477 / 200000000) (Real.log (1136661211129 / 500000000000)) := by
  have h := reflection_log_11013_neg
  have he : Real.log (1136661211129 / 500000000000) = -Real.log (500000000000 / 1136661211129) := by
    rw [show ((1136661211129 / 500000000000) : ℝ) = ((500000000000 / 1136661211129) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11014_neg : (205900017 / 250000000) ≤ -Real.log (62500000000 / 142418032787) ∧
    -Real.log (62500000000 / 142418032787) ≤ (82360007 / 100000000) := by
  have h := checkLog_sound (w := (17418032787 / 267418032787)) (n := 12)
    (lo := (16306611 / 125000000)) (hi := (130452889 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((142418032787 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(142418032787 / 125000000000) = 1/(62500000000 / 142418032787) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11014 : Bounds (205900017 / 250000000) (82360007 / 100000000) (Real.log (142418032787 / 62500000000)) := by
  have h := reflection_log_11014_neg
  have he : Real.log (142418032787 / 62500000000) = -Real.log (62500000000 / 142418032787) := by
    rw [show ((142418032787 / 62500000000) : ℝ) = ((62500000000 / 142418032787) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11015_neg : (644576 / 1953125) ≤ -Real.log (1000 / 1391) ∧
    -Real.log (1000 / 1391) ≤ (330022913 / 1000000000) := by
  have h := checkLog_sound (w := (391 / 2391)) (n := 12)
    (lo := (644576 / 1953125)) (hi := (330022913 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1391 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1391 / 1000) = 1/(1000 / 1391) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11015 : Bounds (644576 / 1953125) (330022913 / 1000000000) (Real.log (1391 / 1000)) := by
  have h := reflection_log_11015_neg
  have he : Real.log (1391 / 1000) = -Real.log (1000 / 1391) := by
    rw [show ((1391 / 1000) : ℝ) = ((1000 / 1391) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11016_neg : (495937011 / 1000000000) ≤ -Real.log (609 / 1000) ∧
    -Real.log (609 / 1000) ≤ (123984253 / 250000000) := by
  have h := checkLog_sound (w := (391 / 1609)) (n := 12)
    (lo := (495937011 / 1000000000)) (hi := (123984253 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 609) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 609) = 1/(609 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11016 : Bounds (-123984253 / 250000000) (-495937011 / 1000000000) (Real.log (609 / 1000)) := by
  have h := reflection_log_11016_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11017_neg : (390923 / 1000000000) ≤ -Real.log (1000000 / 1000391) ∧
    -Real.log (1000000 / 1000391) ≤ (97731 / 250000000) := by
  have h := checkLog_sound (w := (391 / 2000391)) (n := 12)
    (lo := (390923 / 1000000000)) (hi := (97731 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000391 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000391 / 1000000) = 1/(1000000 / 1000391) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11017 : Bounds (390923 / 1000000000) (97731 / 250000000) (Real.log (1000391 / 1000000)) := by
  have h := reflection_log_11017_neg
  have he : Real.log (1000391 / 1000000) = -Real.log (1000000 / 1000391) := by
    rw [show ((1000391 / 1000000) : ℝ) = ((1000000 / 1000391) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11018_neg : (97769 / 250000000) ≤ -Real.log (999609 / 1000000) ∧
    -Real.log (999609 / 1000000) ≤ (391077 / 1000000000) := by
  have h := checkLog_sound (w := (391 / 1999609)) (n := 12)
    (lo := (97769 / 250000000)) (hi := (391077 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999609) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999609) = 1/(999609 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11018 : Bounds (-391077 / 1000000000) (-97769 / 250000000) (Real.log (999609 / 1000000)) := by
  have h := reflection_log_11018_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11019_neg : (182666497 / 1000000000) ≤ -Real.log (500000 / 600207) ∧
    -Real.log (500000 / 600207) ≤ (91333249 / 500000000) := by
  have h := checkLog_sound (w := (100207 / 1100207)) (n := 12)
    (lo := (182666497 / 1000000000)) (hi := (91333249 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((600207 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(600207 / 500000) = 1/(500000 / 600207) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11019 : Bounds (182666497 / 1000000000) (91333249 / 500000000) (Real.log (600207 / 500000)) := by
  have h := reflection_log_11019_neg
  have he : Real.log (600207 / 500000) = -Real.log (500000 / 600207) := by
    rw [show ((600207 / 500000) : ℝ) = ((500000 / 600207) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11020_neg : (44732237 / 200000000) ≤ -Real.log (399793 / 500000) ∧
    -Real.log (399793 / 500000) ≤ (111830593 / 500000000) := by
  have h := checkLog_sound (w := (100207 / 899793)) (n := 12)
    (lo := (44732237 / 200000000)) (hi := (111830593 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 399793) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 399793) = 1/(399793 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11020 : Bounds (-111830593 / 500000000) (-44732237 / 200000000) (Real.log (399793 / 500000)) := by
  have h := reflection_log_11020_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11021_neg : (36687187 / 200000000) ≤ -Real.log (500000 / 600669) ∧
    -Real.log (500000 / 600669) ≤ (5732373 / 31250000) := by
  have h := checkLog_sound (w := (100669 / 1100669)) (n := 12)
    (lo := (36687187 / 200000000)) (hi := (5732373 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((600669 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(600669 / 500000) = 1/(500000 / 600669) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11021 : Bounds (36687187 / 200000000) (5732373 / 31250000) (Real.log (600669 / 500000)) := by
  have h := reflection_log_11021_neg
  have he : Real.log (600669 / 500000) = -Real.log (500000 / 600669) := by
    rw [show ((600669 / 500000) : ℝ) = ((500000 / 600669) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11022_neg : (224817451 / 1000000000) ≤ -Real.log (399331 / 500000) ∧
    -Real.log (399331 / 500000) ≤ (56204363 / 250000000) := by
  have h := checkLog_sound (w := (100669 / 899331)) (n := 12)
    (lo := (224817451 / 1000000000)) (hi := (56204363 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 399331) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 399331) = 1/(399331 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11022 : Bounds (-56204363 / 250000000) (-224817451 / 1000000000) (Real.log (399331 / 500000)) := by
  have h := reflection_log_11022_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11023_neg : (8276303 / 200000000) ≤ -Real.log (239865752439 / 250000000000) ∧
    -Real.log (239865752439 / 250000000000) ≤ (10345379 / 250000000) := by
  have h := checkLog_sound (w := (10134247561 / 489865752439)) (n := 12)
    (lo := (8276303 / 200000000)) (hi := (10345379 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 239865752439) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 239865752439) = 1/(239865752439 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11023 : Bounds (-10345379 / 250000000) (-8276303 / 200000000) (Real.log (239865752439 / 250000000000)) := by
  have h := reflection_log_11023_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11024_neg : (40994687 / 1000000000) ≤ -Real.log (239958557151 / 250000000000) ∧
    -Real.log (239958557151 / 250000000000) ≤ (320271 / 7812500) := by
  have h := checkLog_sound (w := (10041442849 / 489958557151)) (n := 12)
    (lo := (40994687 / 1000000000)) (hi := (320271 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 239958557151) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 239958557151) = 1/(239958557151 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11024 : Bounds (-320271 / 7812500) (-40994687 / 1000000000) (Real.log (239958557151 / 250000000000)) := by
  have h := reflection_log_11024_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11025_neg : (203163841 / 500000000) ≤ -Real.log (500000000000 / 750647209931) ∧
    -Real.log (500000000000 / 750647209931) ≤ (406327683 / 1000000000) := by
  have h := checkLog_sound (w := (250647209931 / 1250647209931)) (n := 12)
    (lo := (203163841 / 500000000)) (hi := (406327683 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((750647209931 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(750647209931 / 500000000000) = 1/(500000000000 / 750647209931) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11025 : Bounds (203163841 / 500000000) (406327683 / 1000000000) (Real.log (750647209931 / 500000000000)) := by
  have h := reflection_log_11025_neg
  have he : Real.log (750647209931 / 500000000000) = -Real.log (500000000000 / 750647209931) := by
    rw [show ((750647209931 / 500000000000) : ℝ) = ((500000000000 / 750647209931) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11026_neg : (408253387 / 1000000000) ≤ -Real.log (500000000000 / 752094127429) ∧
    -Real.log (500000000000 / 752094127429) ≤ (102063347 / 250000000) := by
  have h := checkLog_sound (w := (252094127429 / 1252094127429)) (n := 12)
    (lo := (408253387 / 1000000000)) (hi := (102063347 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((752094127429 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(752094127429 / 500000000000) = 1/(500000000000 / 752094127429) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11026 : Bounds (408253387 / 1000000000) (102063347 / 250000000) (Real.log (752094127429 / 500000000000)) := by
  have h := reflection_log_11026_neg
  have he : Real.log (752094127429 / 500000000000) = -Real.log (500000000000 / 752094127429) := by
    rw [show ((752094127429 / 500000000000) : ℝ) = ((500000000000 / 752094127429) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11027_neg : (205900017 / 250000000) ≤ -Real.log (100000000000 / 227868852459) ∧
    -Real.log (100000000000 / 227868852459) ≤ (82360007 / 100000000) := by
  have h := checkLog_sound (w := (27868852459 / 427868852459)) (n := 12)
    (lo := (16306611 / 125000000)) (hi := (130452889 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((227868852459 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(227868852459 / 200000000000) = 1/(100000000000 / 227868852459) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11027 : Bounds (205900017 / 250000000) (82360007 / 100000000) (Real.log (227868852459 / 100000000000)) := by
  have h := reflection_log_11027_neg
  have he : Real.log (227868852459 / 100000000000) = -Real.log (100000000000 / 227868852459) := by
    rw [show ((227868852459 / 100000000000) : ℝ) = ((100000000000 / 227868852459) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11028_neg : (825959923 / 1000000000) ≤ -Real.log (100000000000 / 228407224959) ∧
    -Real.log (100000000000 / 228407224959) ≤ (33038397 / 40000000) := by
  have h := checkLog_sound (w := (28407224959 / 428407224959)) (n := 12)
    (lo := (132812743 / 1000000000)) (hi := (16601593 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((228407224959 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(228407224959 / 200000000000) = 1/(100000000000 / 228407224959) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11028 : Bounds (825959923 / 1000000000) (33038397 / 40000000) (Real.log (228407224959 / 100000000000)) := by
  have h := reflection_log_11028_neg
  have he : Real.log (228407224959 / 100000000000) = -Real.log (100000000000 / 228407224959) := by
    rw [show ((228407224959 / 100000000000) : ℝ) = ((100000000000 / 228407224959) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11029_neg : (330741561 / 1000000000) ≤ -Real.log (125 / 174) ∧
    -Real.log (125 / 174) ≤ (165370781 / 500000000) := by
  have h := checkLog_sound (w := (49 / 299)) (n := 12)
    (lo := (330741561 / 1000000000)) (hi := (165370781 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((174 / 125) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(174 / 125) = 1/(125 / 174) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11029 : Bounds (330741561 / 1000000000) (165370781 / 500000000) (Real.log (174 / 125)) := by
  have h := reflection_log_11029_neg
  have he : Real.log (174 / 125) = -Real.log (125 / 174) := by
    rw [show ((174 / 125) : ℝ) = ((125 / 174) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11030_neg : (497580397 / 1000000000) ≤ -Real.log (76 / 125) ∧
    -Real.log (76 / 125) ≤ (248790199 / 500000000) := by
  have h := checkLog_sound (w := (49 / 201)) (n := 12)
    (lo := (497580397 / 1000000000)) (hi := (248790199 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 76) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125 / 76) = 1/(76 / 125) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11030 : Bounds (-248790199 / 500000000) (-497580397 / 1000000000) (Real.log (76 / 125)) := by
  have h := reflection_log_11030_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11031_neg : (391923 / 1000000000) ≤ -Real.log (125000 / 125049) ∧
    -Real.log (125000 / 125049) ≤ (97981 / 250000000) := by
  have h := checkLog_sound (w := (49 / 250049)) (n := 12)
    (lo := (391923 / 1000000000)) (hi := (97981 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125049 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125049 / 125000) = 1/(125000 / 125049) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11031 : Bounds (391923 / 1000000000) (97981 / 250000000) (Real.log (125049 / 125000)) := by
  have h := reflection_log_11031_neg
  have he : Real.log (125049 / 125000) = -Real.log (125000 / 125049) := by
    rw [show ((125049 / 125000) : ℝ) = ((125000 / 125049) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11032_neg : (98019 / 250000000) ≤ -Real.log (124951 / 125000) ∧
    -Real.log (124951 / 125000) ≤ (392077 / 1000000000) := by
  have h := checkLog_sound (w := (49 / 249951)) (n := 12)
    (lo := (98019 / 250000000)) (hi := (392077 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 124951) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 124951) = 1/(124951 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11032 : Bounds (-392077 / 1000000000) (-98019 / 250000000) (Real.log (124951 / 125000)) := by
  have h := reflection_log_11032_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11033_neg : (183119571 / 1000000000) ≤ -Real.log (500000 / 600479) ∧
    -Real.log (500000 / 600479) ≤ (45779893 / 250000000) := by
  have h := checkLog_sound (w := (100479 / 1100479)) (n := 12)
    (lo := (183119571 / 1000000000)) (hi := (45779893 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((600479 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(600479 / 500000) = 1/(500000 / 600479) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11033 : Bounds (183119571 / 1000000000) (45779893 / 250000000) (Real.log (600479 / 500000)) := by
  have h := reflection_log_11033_neg
  have he : Real.log (600479 / 500000) = -Real.log (500000 / 600479) := by
    rw [show ((600479 / 500000) : ℝ) = ((500000 / 600479) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11034_neg : (28042721 / 125000000) ≤ -Real.log (399521 / 500000) ∧
    -Real.log (399521 / 500000) ≤ (224341769 / 1000000000) := by
  have h := checkLog_sound (w := (100479 / 899521)) (n := 12)
    (lo := (28042721 / 125000000)) (hi := (224341769 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 399521) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 399521) = 1/(399521 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11034 : Bounds (-224341769 / 1000000000) (-28042721 / 125000000) (Real.log (399521 / 500000)) := by
  have h := reflection_log_11034_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11035_neg : (183889493 / 1000000000) ≤ -Real.log (1000000 / 1201883) ∧
    -Real.log (1000000 / 1201883) ≤ (91944747 / 500000000) := by
  have h := checkLog_sound (w := (201883 / 2201883)) (n := 12)
    (lo := (183889493 / 1000000000)) (hi := (91944747 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1201883 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1201883 / 1000000) = 1/(1000000 / 1201883) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11035 : Bounds (183889493 / 1000000000) (91944747 / 500000000) (Real.log (1201883 / 1000000)) := by
  have h := reflection_log_11035_neg
  have he : Real.log (1201883 / 1000000) = -Real.log (1000000 / 1201883) := by
    rw [show ((1201883 / 1000000) : ℝ) = ((1000000 / 1201883) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11036_neg : (9020003 / 40000000) ≤ -Real.log (798117 / 1000000) ∧
    -Real.log (798117 / 1000000) ≤ (56375019 / 250000000) := by
  have h := checkLog_sound (w := (201883 / 1798117)) (n := 12)
    (lo := (9020003 / 40000000)) (hi := (56375019 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 798117) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 798117) = 1/(798117 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11036 : Bounds (-56375019 / 250000000) (-9020003 / 40000000) (Real.log (798117 / 1000000)) := by
  have h := reflection_log_11036_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11037_neg : (20805291 / 500000000) ≤ -Real.log (959243254311 / 1000000000000) ∧
    -Real.log (959243254311 / 1000000000000) ≤ (41610583 / 1000000000) := by
  have h := checkLog_sound (w := (40756745689 / 1959243254311)) (n := 12)
    (lo := (20805291 / 500000000)) (hi := (41610583 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 959243254311) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 959243254311) = 1/(959243254311 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11037 : Bounds (-41610583 / 1000000000) (-20805291 / 500000000) (Real.log (959243254311 / 1000000000000)) := by
  have h := reflection_log_11037_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11038_neg : (41222197 / 1000000000) ≤ -Real.log (239903970559 / 250000000000) ∧
    -Real.log (239903970559 / 250000000000) ≤ (20611099 / 500000000) := by
  have h := checkLog_sound (w := (10096029441 / 489903970559)) (n := 12)
    (lo := (41222197 / 1000000000)) (hi := (20611099 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 239903970559) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 239903970559) = 1/(239903970559 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11038 : Bounds (-20611099 / 500000000) (-41222197 / 1000000000) (Real.log (239903970559 / 250000000000)) := by
  have h := reflection_log_11038_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11039_neg : (20373067 / 50000000) ≤ -Real.log (62500000000 / 93937333707) ∧
    -Real.log (62500000000 / 93937333707) ≤ (407461341 / 1000000000) := by
  have h := checkLog_sound (w := (31437333707 / 156437333707)) (n := 12)
    (lo := (20373067 / 50000000)) (hi := (407461341 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((93937333707 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(93937333707 / 62500000000) = 1/(62500000000 / 93937333707) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11039 : Bounds (20373067 / 50000000) (407461341 / 1000000000) (Real.log (93937333707 / 62500000000)) := by
  have h := reflection_log_11039_neg
  have he : Real.log (93937333707 / 62500000000) = -Real.log (62500000000 / 93937333707) := by
    rw [show ((93937333707 / 62500000000) : ℝ) = ((62500000000 / 93937333707) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11040_neg : (409389569 / 1000000000) ≤ -Real.log (500000000000 / 752949129013) ∧
    -Real.log (500000000000 / 752949129013) ≤ (40938957 / 100000000) := by
  have h := checkLog_sound (w := (252949129013 / 1252949129013)) (n := 12)
    (lo := (409389569 / 1000000000)) (hi := (40938957 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((752949129013 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(752949129013 / 500000000000) = 1/(500000000000 / 752949129013) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11040 : Bounds (409389569 / 1000000000) (40938957 / 100000000) (Real.log (752949129013 / 500000000000)) := by
  have h := reflection_log_11040_neg
  have he : Real.log (752949129013 / 500000000000) = -Real.log (500000000000 / 752949129013) := by
    rw [show ((752949129013 / 500000000000) : ℝ) = ((500000000000 / 752949129013) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11041_neg : (825959923 / 1000000000) ≤ -Real.log (250000000000 / 571018062397) ∧
    -Real.log (250000000000 / 571018062397) ≤ (33038397 / 40000000) := by
  have h := checkLog_sound (w := (71018062397 / 1071018062397)) (n := 12)
    (lo := (132812743 / 1000000000)) (hi := (16601593 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((571018062397 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(571018062397 / 500000000000) = 1/(250000000000 / 571018062397) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11041 : Bounds (825959923 / 1000000000) (33038397 / 40000000) (Real.log (571018062397 / 250000000000)) := by
  have h := reflection_log_11041_neg
  have he : Real.log (571018062397 / 250000000000) = -Real.log (250000000000 / 571018062397) := by
    rw [show ((571018062397 / 250000000000) : ℝ) = ((250000000000 / 571018062397) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11042_neg : (414160979 / 500000000) ≤ -Real.log (250000000000 / 572368421053) ∧
    -Real.log (250000000000 / 572368421053) ≤ (20708049 / 25000000) := by
  have h := checkLog_sound (w := (72368421053 / 1072368421053)) (n := 12)
    (lo := (67587389 / 500000000)) (hi := (135174779 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((572368421053 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(572368421053 / 500000000000) = 1/(250000000000 / 572368421053) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11042 : Bounds (414160979 / 500000000) (20708049 / 25000000) (Real.log (572368421053 / 250000000000)) := by
  have h := reflection_log_11042_neg
  have he : Real.log (572368421053 / 250000000000) = -Real.log (250000000000 / 572368421053) := by
    rw [show ((572368421053 / 250000000000) : ℝ) = ((250000000000 / 572368421053) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11043_neg : (165729847 / 500000000) ≤ -Real.log (1000 / 1393) ∧
    -Real.log (1000 / 1393) ≤ (66291939 / 200000000) := by
  have h := checkLog_sound (w := (393 / 2393)) (n := 12)
    (lo := (165729847 / 500000000)) (hi := (66291939 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1393 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1393 / 1000) = 1/(1000 / 1393) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11043 : Bounds (165729847 / 500000000) (66291939 / 200000000) (Real.log (1393 / 1000)) := by
  have h := reflection_log_11043_neg
  have he : Real.log (1393 / 1000) = -Real.log (1000 / 1393) := by
    rw [show ((1393 / 1000) : ℝ) = ((1000 / 1393) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11044_neg : (499226487 / 1000000000) ≤ -Real.log (607 / 1000) ∧
    -Real.log (607 / 1000) ≤ (62403311 / 125000000) := by
  have h := checkLog_sound (w := (393 / 1607)) (n := 12)
    (lo := (499226487 / 1000000000)) (hi := (62403311 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 607) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 607) = 1/(607 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11044 : Bounds (-62403311 / 125000000) (-499226487 / 1000000000) (Real.log (607 / 1000)) := by
  have h := reflection_log_11044_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11045_neg : (196461 / 500000000) ≤ -Real.log (1000000 / 1000393) ∧
    -Real.log (1000000 / 1000393) ≤ (392923 / 1000000000) := by
  have h := checkLog_sound (w := (393 / 2000393)) (n := 12)
    (lo := (196461 / 500000000)) (hi := (392923 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000393 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000393 / 1000000) = 1/(1000000 / 1000393) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11045 : Bounds (196461 / 500000000) (392923 / 1000000000) (Real.log (1000393 / 1000000)) := by
  have h := reflection_log_11045_neg
  have he : Real.log (1000393 / 1000000) = -Real.log (1000000 / 1000393) := by
    rw [show ((1000393 / 1000000) : ℝ) = ((1000000 / 1000393) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11046_neg : (393077 / 1000000000) ≤ -Real.log (999607 / 1000000) ∧
    -Real.log (999607 / 1000000) ≤ (196539 / 500000000) := by
  have h := checkLog_sound (w := (393 / 1999607)) (n := 12)
    (lo := (393077 / 1000000000)) (hi := (196539 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999607) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999607) = 1/(999607 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11046 : Bounds (-196539 / 500000000) (-393077 / 1000000000) (Real.log (999607 / 1000000)) := by
  have h := reflection_log_11046_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11047_neg : (4589311 / 25000000) ≤ -Real.log (500000 / 600751) ∧
    -Real.log (500000 / 600751) ≤ (183572441 / 1000000000) := by
  have h := checkLog_sound (w := (100751 / 1100751)) (n := 12)
    (lo := (4589311 / 25000000)) (hi := (183572441 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((600751 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(600751 / 500000) = 1/(500000 / 600751) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11047 : Bounds (4589311 / 25000000) (183572441 / 1000000000) (Real.log (600751 / 500000)) := by
  have h := reflection_log_11047_neg
  have he : Real.log (600751 / 500000) = -Real.log (500000 / 600751) := by
    rw [show ((600751 / 500000) : ℝ) = ((500000 / 600751) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11048_neg : (7031963 / 31250000) ≤ -Real.log (399249 / 500000) ∧
    -Real.log (399249 / 500000) ≤ (225022817 / 1000000000) := by
  have h := checkLog_sound (w := (100751 / 899249)) (n := 12)
    (lo := (7031963 / 31250000)) (hi := (225022817 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 399249) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 399249) = 1/(399249 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11048 : Bounds (-225022817 / 1000000000) (-7031963 / 31250000) (Real.log (399249 / 500000)) := by
  have h := reflection_log_11048_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11049_neg : (184343677 / 1000000000) ≤ -Real.log (1000000 / 1202429) ∧
    -Real.log (1000000 / 1202429) ≤ (92171839 / 500000000) := by
  have h := checkLog_sound (w := (202429 / 2202429)) (n := 12)
    (lo := (184343677 / 1000000000)) (hi := (92171839 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1202429 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1202429 / 1000000) = 1/(1000000 / 1202429) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11049 : Bounds (184343677 / 1000000000) (92171839 / 500000000) (Real.log (1202429 / 1000000)) := by
  have h := reflection_log_11049_neg
  have he : Real.log (1202429 / 1000000) = -Real.log (1000000 / 1202429) := by
    rw [show ((1202429 / 1000000) : ℝ) = ((1000000 / 1202429) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11050_neg : (11309221 / 50000000) ≤ -Real.log (797571 / 1000000) ∧
    -Real.log (797571 / 1000000) ≤ (226184421 / 1000000000) := by
  have h := checkLog_sound (w := (202429 / 1797571)) (n := 12)
    (lo := (11309221 / 50000000)) (hi := (226184421 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 797571) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 797571) = 1/(797571 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11050 : Bounds (-226184421 / 1000000000) (-11309221 / 50000000) (Real.log (797571 / 1000000)) := by
  have h := reflection_log_11050_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11051_neg : (20920371 / 500000000) ≤ -Real.log (959022499959 / 1000000000000) ∧
    -Real.log (959022499959 / 1000000000000) ≤ (41840743 / 1000000000) := by
  have h := checkLog_sound (w := (40977500041 / 1959022499959)) (n := 12)
    (lo := (20920371 / 500000000)) (hi := (41840743 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 959022499959) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 959022499959) = 1/(959022499959 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11051 : Bounds (-41840743 / 1000000000) (-20920371 / 500000000) (Real.log (959022499959 / 1000000000000)) := by
  have h := reflection_log_11051_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11052_neg : (331603 / 8000000) ≤ -Real.log (239849235999 / 250000000000) ∧
    -Real.log (239849235999 / 250000000000) ≤ (5181297 / 125000000) := by
  have h := checkLog_sound (w := (10150764001 / 489849235999)) (n := 12)
    (lo := (331603 / 8000000)) (hi := (5181297 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 239849235999) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 239849235999) = 1/(239849235999 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11052 : Bounds (-5181297 / 125000000) (-331603 / 8000000) (Real.log (239849235999 / 250000000000)) := by
  have h := reflection_log_11052_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11053_neg : (51074407 / 125000000) ≤ -Real.log (250000000000 / 376175644773) ∧
    -Real.log (250000000000 / 376175644773) ≤ (408595257 / 1000000000) := by
  have h := checkLog_sound (w := (126175644773 / 626175644773)) (n := 12)
    (lo := (51074407 / 125000000)) (hi := (408595257 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((376175644773 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(376175644773 / 250000000000) = 1/(250000000000 / 376175644773) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11053 : Bounds (51074407 / 125000000) (408595257 / 1000000000) (Real.log (376175644773 / 250000000000)) := by
  have h := reflection_log_11053_neg
  have he : Real.log (376175644773 / 250000000000) = -Real.log (250000000000 / 376175644773) := by
    rw [show ((376175644773 / 250000000000) : ℝ) = ((250000000000 / 376175644773) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11054_neg : (410528097 / 1000000000) ≤ -Real.log (500000000000 / 753806871113) ∧
    -Real.log (500000000000 / 753806871113) ≤ (205264049 / 500000000) := by
  have h := checkLog_sound (w := (253806871113 / 1253806871113)) (n := 12)
    (lo := (410528097 / 1000000000)) (hi := (205264049 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((753806871113 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(753806871113 / 500000000000) = 1/(500000000000 / 753806871113) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11054 : Bounds (410528097 / 1000000000) (205264049 / 500000000) (Real.log (753806871113 / 500000000000)) := by
  have h := reflection_log_11054_neg
  have he : Real.log (753806871113 / 500000000000) = -Real.log (500000000000 / 753806871113) := by
    rw [show ((753806871113 / 500000000000) : ℝ) = ((500000000000 / 753806871113) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11055_neg : (414160979 / 500000000) ≤ -Real.log (100000000000 / 228947368421) ∧
    -Real.log (100000000000 / 228947368421) ≤ (20708049 / 25000000) := by
  have h := checkLog_sound (w := (28947368421 / 428947368421)) (n := 12)
    (lo := (67587389 / 500000000)) (hi := (135174779 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((228947368421 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(228947368421 / 200000000000) = 1/(100000000000 / 228947368421) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11055 : Bounds (414160979 / 500000000) (20708049 / 25000000) (Real.log (228947368421 / 100000000000)) := by
  have h := reflection_log_11055_neg
  have he : Real.log (228947368421 / 100000000000) = -Real.log (100000000000 / 228947368421) := by
    rw [show ((228947368421 / 100000000000) : ℝ) = ((100000000000 / 228947368421) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11056_neg : (415343091 / 500000000) ≤ -Real.log (500000000000 / 1147446457991) ∧
    -Real.log (500000000000 / 1147446457991) ≤ (103835773 / 125000000) := by
  have h := checkLog_sound (w := (147446457991 / 2147446457991)) (n := 12)
    (lo := (68769501 / 500000000)) (hi := (137539003 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1147446457991 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1147446457991 / 1000000000000) = 1/(500000000000 / 1147446457991) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11056 : Bounds (415343091 / 500000000) (103835773 / 125000000) (Real.log (1147446457991 / 500000000000)) := by
  have h := reflection_log_11056_neg
  have he : Real.log (1147446457991 / 500000000000) = -Real.log (500000000000 / 1147446457991) := by
    rw [show ((1147446457991 / 500000000000) : ℝ) = ((500000000000 / 1147446457991) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11057_neg : (10380541 / 31250000) ≤ -Real.log (500 / 697) ∧
    -Real.log (500 / 697) ≤ (332177313 / 1000000000) := by
  have h := checkLog_sound (w := (197 / 1197)) (n := 12)
    (lo := (10380541 / 31250000)) (hi := (332177313 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((697 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(697 / 500) = 1/(500 / 697) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11057 : Bounds (10380541 / 31250000) (332177313 / 1000000000) (Real.log (697 / 500)) := by
  have h := reflection_log_11057_neg
  have he : Real.log (697 / 500) = -Real.log (500 / 697) := by
    rw [show ((697 / 500) : ℝ) = ((500 / 697) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11058_neg : (125218823 / 250000000) ≤ -Real.log (303 / 500) ∧
    -Real.log (303 / 500) ≤ (500875293 / 1000000000) := by
  have h := checkLog_sound (w := (197 / 803)) (n := 12)
    (lo := (125218823 / 250000000)) (hi := (500875293 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 303) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500 / 303) = 1/(303 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11058 : Bounds (-500875293 / 1000000000) (-125218823 / 250000000) (Real.log (303 / 500)) := by
  have h := reflection_log_11058_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11059_neg : (196961 / 500000000) ≤ -Real.log (500000 / 500197) ∧
    -Real.log (500000 / 500197) ≤ (393923 / 1000000000) := by
  have h := checkLog_sound (w := (197 / 1000197)) (n := 12)
    (lo := (196961 / 500000000)) (hi := (393923 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500197 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500197 / 500000) = 1/(500000 / 500197) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11059 : Bounds (196961 / 500000000) (393923 / 1000000000) (Real.log (500197 / 500000)) := by
  have h := reflection_log_11059_neg
  have he : Real.log (500197 / 500000) = -Real.log (500000 / 500197) := by
    rw [show ((500197 / 500000) : ℝ) = ((500000 / 500197) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11060_neg : (394077 / 1000000000) ≤ -Real.log (499803 / 500000) ∧
    -Real.log (499803 / 500000) ≤ (197039 / 500000000) := by
  have h := checkLog_sound (w := (197 / 999803)) (n := 12)
    (lo := (394077 / 1000000000)) (hi := (197039 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499803) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499803) = 1/(499803 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11060 : Bounds (-197039 / 500000000) (-394077 / 1000000000) (Real.log (499803 / 500000)) := by
  have h := reflection_log_11060_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11061_neg : (11501621 / 62500000) ≤ -Real.log (1000000 / 1202047) ∧
    -Real.log (1000000 / 1202047) ≤ (184025937 / 1000000000) := by
  have h := checkLog_sound (w := (202047 / 2202047)) (n := 12)
    (lo := (11501621 / 62500000)) (hi := (184025937 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1202047 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1202047 / 1000000) = 1/(1000000 / 1202047) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11061 : Bounds (11501621 / 62500000) (184025937 / 1000000000) (Real.log (1202047 / 1000000)) := by
  have h := reflection_log_11061_neg
  have he : Real.log (1202047 / 1000000) = -Real.log (1000000 / 1202047) := by
    rw [show ((1202047 / 1000000) : ℝ) = ((1000000 / 1202047) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11062_neg : (11285279 / 50000000) ≤ -Real.log (797953 / 1000000) ∧
    -Real.log (797953 / 1000000) ≤ (225705581 / 1000000000) := by
  have h := checkLog_sound (w := (202047 / 1797953)) (n := 12)
    (lo := (11285279 / 50000000)) (hi := (225705581 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 797953) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 797953) = 1/(797953 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11062 : Bounds (-225705581 / 1000000000) (-11285279 / 50000000) (Real.log (797953 / 1000000)) := by
  have h := reflection_log_11062_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11063_neg : (36959531 / 200000000) ≤ -Real.log (40000 / 48119) ∧
    -Real.log (40000 / 48119) ≤ (23099707 / 125000000) := by
  have h := checkLog_sound (w := (8119 / 88119)) (n := 12)
    (lo := (36959531 / 200000000)) (hi := (23099707 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((48119 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(48119 / 40000) = 1/(40000 / 48119) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11063 : Bounds (36959531 / 200000000) (23099707 / 125000000) (Real.log (48119 / 40000)) := by
  have h := reflection_log_11063_neg
  have he : Real.log (48119 / 40000) = -Real.log (40000 / 48119) := by
    rw [show ((48119 / 40000) : ℝ) = ((40000 / 48119) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11064_neg : (226869233 / 1000000000) ≤ -Real.log (31881 / 40000) ∧
    -Real.log (31881 / 40000) ≤ (113434617 / 500000000) := by
  have h := checkLog_sound (w := (8119 / 71881)) (n := 12)
    (lo := (226869233 / 1000000000)) (hi := (113434617 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000 / 31881) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000 / 31881) = 1/(31881 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11064 : Bounds (-113434617 / 500000000) (-226869233 / 1000000000) (Real.log (31881 / 40000)) := by
  have h := reflection_log_11064_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11065_neg : (42071577 / 1000000000) ≤ -Real.log (1534081839 / 1600000000) ∧
    -Real.log (1534081839 / 1600000000) ≤ (21035789 / 500000000) := by
  have h := checkLog_sound (w := (65918161 / 3134081839)) (n := 12)
    (lo := (42071577 / 1000000000)) (hi := (21035789 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600000000 / 1534081839) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1600000000 / 1534081839) = 1/(1534081839 / 1600000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11065 : Bounds (-21035789 / 500000000) (-42071577 / 1000000000) (Real.log (1534081839 / 1600000000)) := by
  have h := reflection_log_11065_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11066_neg : (41679643 / 1000000000) ≤ -Real.log (959177009791 / 1000000000000) ∧
    -Real.log (959177009791 / 1000000000000) ≤ (10419911 / 250000000) := by
  have h := checkLog_sound (w := (40822990209 / 1959177009791)) (n := 12)
    (lo := (41679643 / 1000000000)) (hi := (10419911 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 959177009791) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 959177009791) = 1/(959177009791 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11066 : Bounds (-10419911 / 250000000) (-41679643 / 1000000000) (Real.log (959177009791 / 1000000000000)) := by
  have h := reflection_log_11066_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11067_neg : (409731517 / 1000000000) ≤ -Real.log (7812500000 / 11768853789) ∧
    -Real.log (7812500000 / 11768853789) ≤ (204865759 / 500000000) := by
  have h := checkLog_sound (w := (3956353789 / 19581353789)) (n := 12)
    (lo := (409731517 / 1000000000)) (hi := (204865759 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11768853789 / 7812500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11768853789 / 7812500000) = 1/(7812500000 / 11768853789) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11067 : Bounds (409731517 / 1000000000) (204865759 / 500000000) (Real.log (11768853789 / 7812500000)) := by
  have h := reflection_log_11067_neg
  have he : Real.log (11768853789 / 7812500000) = -Real.log (7812500000 / 11768853789) := by
    rw [show ((11768853789 / 7812500000) : ℝ) = ((7812500000 / 11768853789) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11068_neg : (51458361 / 125000000) ≤ -Real.log (500000000000 / 754665788401) ∧
    -Real.log (500000000000 / 754665788401) ≤ (411666889 / 1000000000) := by
  have h := checkLog_sound (w := (254665788401 / 1254665788401)) (n := 12)
    (lo := (51458361 / 125000000)) (hi := (411666889 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((754665788401 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(754665788401 / 500000000000) = 1/(500000000000 / 754665788401) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11068 : Bounds (51458361 / 125000000) (411666889 / 1000000000) (Real.log (754665788401 / 500000000000)) := by
  have h := reflection_log_11068_neg
  have he : Real.log (754665788401 / 500000000000) = -Real.log (500000000000 / 754665788401) := by
    rw [show ((754665788401 / 500000000000) : ℝ) = ((500000000000 / 754665788401) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11069_neg : (415343091 / 500000000) ≤ -Real.log (50000000000 / 114744645799) ∧
    -Real.log (50000000000 / 114744645799) ≤ (103835773 / 125000000) := by
  have h := checkLog_sound (w := (14744645799 / 214744645799)) (n := 12)
    (lo := (68769501 / 500000000)) (hi := (137539003 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((114744645799 / 100000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(114744645799 / 100000000000) = 1/(50000000000 / 114744645799) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11069 : Bounds (415343091 / 500000000) (103835773 / 125000000) (Real.log (114744645799 / 50000000000)) := by
  have h := reflection_log_11069_neg
  have he : Real.log (114744645799 / 50000000000) = -Real.log (50000000000 / 114744645799) := by
    rw [show ((114744645799 / 50000000000) : ℝ) = ((50000000000 / 114744645799) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11070_neg : (208263151 / 250000000) ≤ -Real.log (250000000000 / 575082508251) ∧
    -Real.log (250000000000 / 575082508251) ≤ (416526303 / 500000000) := by
  have h := checkLog_sound (w := (75082508251 / 1075082508251)) (n := 12)
    (lo := (8744089 / 62500000)) (hi := (5596217 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((575082508251 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(575082508251 / 500000000000) = 1/(250000000000 / 575082508251) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11070 : Bounds (208263151 / 250000000) (416526303 / 500000000) (Real.log (575082508251 / 250000000000)) := by
  have h := reflection_log_11070_neg
  have he : Real.log (575082508251 / 250000000000) = -Real.log (250000000000 / 575082508251) := by
    rw [show ((575082508251 / 250000000000) : ℝ) = ((250000000000 / 575082508251) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11071_neg : (66578883 / 200000000) ≤ -Real.log (200 / 279) ∧
    -Real.log (200 / 279) ≤ (20805901 / 62500000) := by
  have h := checkLog_sound (w := (79 / 479)) (n := 12)
    (lo := (66578883 / 200000000)) (hi := (20805901 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((279 / 200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(279 / 200) = 1/(200 / 279) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11071 : Bounds (66578883 / 200000000) (20805901 / 62500000) (Real.log (279 / 200)) := by
  have h := reflection_log_11071_neg
  have he : Real.log (279 / 200) = -Real.log (200 / 279) := by
    rw [show ((279 / 200) : ℝ) = ((200 / 279) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily
