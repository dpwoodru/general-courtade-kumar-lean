import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_6016_neg : (12222203 / 31250000) ≤ -Real.log (100000000000 / 147862188623) ∧
    -Real.log (100000000000 / 147862188623) ≤ (391110497 / 1000000000) := by
  have h := checkLog_sound (w := (47862188623 / 247862188623)) (n := 12)
    (lo := (12222203 / 31250000)) (hi := (391110497 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((147862188623 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(147862188623 / 100000000000) = 1/(100000000000 / 147862188623) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6016 : Bounds (12222203 / 31250000) (391110497 / 1000000000) (Real.log (147862188623 / 100000000000)) := by
  have h := reflection_log_6016_neg
  have he : Real.log (147862188623 / 100000000000) = -Real.log (100000000000 / 147862188623) := by
    rw [show ((147862188623 / 100000000000) : ℝ) = ((100000000000 / 147862188623) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6017_neg : (195659123 / 500000000) ≤ -Real.log (250000000000 / 369732275657) ∧
    -Real.log (250000000000 / 369732275657) ≤ (391318247 / 1000000000) := by
  have h := checkLog_sound (w := (119732275657 / 619732275657)) (n := 12)
    (lo := (195659123 / 500000000)) (hi := (391318247 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((369732275657 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(369732275657 / 250000000000) = 1/(250000000000 / 369732275657) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6017 : Bounds (195659123 / 500000000) (391318247 / 1000000000) (Real.log (369732275657 / 250000000000)) := by
  have h := reflection_log_6017_neg
  have he : Real.log (369732275657 / 250000000000) = -Real.log (250000000000 / 369732275657) := by
    rw [show ((369732275657 / 250000000000) : ℝ) = ((250000000000 / 369732275657) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6018_neg : (88361289 / 500000000) ≤ -Real.log (10000 / 11933) ∧
    -Real.log (10000 / 11933) ≤ (176722579 / 1000000000) := by
  have h := checkLog_sound (w := (1933 / 21933)) (n := 12)
    (lo := (88361289 / 500000000)) (hi := (176722579 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11933 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11933 / 10000) = 1/(10000 / 11933) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6018 : Bounds (88361289 / 500000000) (176722579 / 1000000000) (Real.log (11933 / 10000)) := by
  have h := reflection_log_6018_neg
  have he : Real.log (11933 / 10000) = -Real.log (10000 / 11933) := by
    rw [show ((11933 / 10000) : ℝ) = ((10000 / 11933) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6019_neg : (214803427 / 1000000000) ≤ -Real.log (8067 / 10000) ∧
    -Real.log (8067 / 10000) ≤ (53700857 / 250000000) := by
  have h := checkLog_sound (w := (1933 / 18067)) (n := 12)
    (lo := (214803427 / 1000000000)) (hi := (53700857 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8067) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8067) = 1/(8067 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6019 : Bounds (-53700857 / 250000000) (-214803427 / 1000000000) (Real.log (8067 / 10000)) := by
  have h := reflection_log_6019_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6020_neg : (193281 / 1000000000) ≤ -Real.log (10000000 / 10001933) ∧
    -Real.log (10000000 / 10001933) ≤ (96641 / 500000000) := by
  have h := checkLog_sound (w := (1933 / 20001933)) (n := 12)
    (lo := (193281 / 1000000000)) (hi := (96641 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001933 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001933 / 10000000) = 1/(10000000 / 10001933) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6020 : Bounds (193281 / 1000000000) (96641 / 500000000) (Real.log (10001933 / 10000000)) := by
  have h := reflection_log_6020_neg
  have he : Real.log (10001933 / 10000000) = -Real.log (10000000 / 10001933) := by
    rw [show ((10001933 / 10000000) : ℝ) = ((10000000 / 10001933) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6021_neg : (96659 / 500000000) ≤ -Real.log (9998067 / 10000000) ∧
    -Real.log (9998067 / 10000000) ≤ (193319 / 1000000000) := by
  have h := checkLog_sound (w := (1933 / 19998067)) (n := 12)
    (lo := (96659 / 500000000)) (hi := (193319 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998067) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998067) = 1/(9998067 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6021 : Bounds (-193319 / 1000000000) (-96659 / 500000000) (Real.log (9998067 / 10000000)) := by
  have h := reflection_log_6021_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6022_neg : (46362967 / 500000000) ≤ -Real.log (1000000 / 1097161) ∧
    -Real.log (1000000 / 1097161) ≤ (18545187 / 200000000) := by
  have h := checkLog_sound (w := (97161 / 2097161)) (n := 12)
    (lo := (46362967 / 500000000)) (hi := (18545187 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1097161 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1097161 / 1000000) = 1/(1000000 / 1097161) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6022 : Bounds (46362967 / 500000000) (18545187 / 200000000) (Real.log (1097161 / 1000000)) := by
  have h := reflection_log_6022_neg
  have he : Real.log (1097161 / 1000000) = -Real.log (1000000 / 1097161) := by
    rw [show ((1097161 / 1000000) : ℝ) = ((1000000 / 1097161) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6023_neg : (25552759 / 250000000) ≤ -Real.log (902839 / 1000000) ∧
    -Real.log (902839 / 1000000) ≤ (102211037 / 1000000000) := by
  have h := checkLog_sound (w := (97161 / 1902839)) (n := 12)
    (lo := (25552759 / 250000000)) (hi := (102211037 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 902839) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 902839) = 1/(902839 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6023 : Bounds (-102211037 / 1000000000) (-25552759 / 250000000) (Real.log (902839 / 1000000)) := by
  have h := reflection_log_6023_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6024_neg : (92948301 / 1000000000) ≤ -Real.log (200000 / 219481) ∧
    -Real.log (200000 / 219481) ≤ (46474151 / 500000000) := by
  have h := checkLog_sound (w := (19481 / 419481)) (n := 12)
    (lo := (92948301 / 1000000000)) (hi := (46474151 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((219481 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(219481 / 200000) = 1/(200000 / 219481) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6024 : Bounds (92948301 / 1000000000) (46474151 / 500000000) (Real.log (219481 / 200000)) := by
  have h := reflection_log_6024_neg
  have he : Real.log (219481 / 200000) = -Real.log (200000 / 219481) := by
    rw [show ((219481 / 200000) : ℝ) = ((200000 / 219481) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6025_neg : (102481331 / 1000000000) ≤ -Real.log (180519 / 200000) ∧
    -Real.log (180519 / 200000) ≤ (25620333 / 250000000) := by
  have h := checkLog_sound (w := (19481 / 380519)) (n := 12)
    (lo := (102481331 / 1000000000)) (hi := (25620333 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 180519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 180519) = 1/(180519 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6025 : Bounds (-25620333 / 250000000) (-102481331 / 1000000000) (Real.log (180519 / 200000)) := by
  have h := reflection_log_6025_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6026_neg : (9533029 / 1000000000) ≤ -Real.log (39620490639 / 40000000000) ∧
    -Real.log (39620490639 / 40000000000) ≤ (953303 / 100000000) := by
  have h := checkLog_sound (w := (379509361 / 79620490639)) (n := 12)
    (lo := (9533029 / 1000000000)) (hi := (953303 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39620490639) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39620490639) = 1/(39620490639 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6026 : Bounds (-953303 / 100000000) (-9533029 / 1000000000) (Real.log (39620490639 / 40000000000)) := by
  have h := reflection_log_6026_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6027_neg : (9485101 / 1000000000) ≤ -Real.log (990559740079 / 1000000000000) ∧
    -Real.log (990559740079 / 1000000000000) ≤ (4742551 / 500000000) := by
  have h := checkLog_sound (w := (9440259921 / 1990559740079)) (n := 12)
    (lo := (9485101 / 1000000000)) (hi := (4742551 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 990559740079) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 990559740079) = 1/(990559740079 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6027 : Bounds (-4742551 / 500000000) (-9485101 / 1000000000) (Real.log (990559740079 / 1000000000000)) := by
  have h := reflection_log_6027_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6028_neg : (19493697 / 100000000) ≤ -Real.log (250000000000 / 303808597103) ∧
    -Real.log (250000000000 / 303808597103) ≤ (194936971 / 1000000000) := by
  have h := checkLog_sound (w := (53808597103 / 553808597103)) (n := 12)
    (lo := (19493697 / 100000000)) (hi := (194936971 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((303808597103 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(303808597103 / 250000000000) = 1/(250000000000 / 303808597103) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6028 : Bounds (19493697 / 100000000) (194936971 / 1000000000) (Real.log (303808597103 / 250000000000)) := by
  have h := reflection_log_6028_neg
  have he : Real.log (303808597103 / 250000000000) = -Real.log (250000000000 / 303808597103) := by
    rw [show ((303808597103 / 250000000000) : ℝ) = ((250000000000 / 303808597103) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6029_neg : (195429633 / 1000000000) ≤ -Real.log (125000000000 / 151979154549) ∧
    -Real.log (125000000000 / 151979154549) ≤ (97714817 / 500000000) := by
  have h := checkLog_sound (w := (26979154549 / 276979154549)) (n := 12)
    (lo := (195429633 / 1000000000)) (hi := (97714817 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((151979154549 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(151979154549 / 125000000000) = 1/(125000000000 / 151979154549) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6029 : Bounds (195429633 / 1000000000) (97714817 / 500000000) (Real.log (151979154549 / 125000000000)) := by
  have h := reflection_log_6029_neg
  have he : Real.log (151979154549 / 125000000000) = -Real.log (125000000000 / 151979154549) := by
    rw [show ((151979154549 / 125000000000) : ℝ) = ((125000000000 / 151979154549) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6030_neg : (195659123 / 500000000) ≤ -Real.log (500000000000 / 739464551313) ∧
    -Real.log (500000000000 / 739464551313) ≤ (391318247 / 1000000000) := by
  have h := checkLog_sound (w := (239464551313 / 1239464551313)) (n := 12)
    (lo := (195659123 / 500000000)) (hi := (391318247 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((739464551313 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(739464551313 / 500000000000) = 1/(500000000000 / 739464551313) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6030 : Bounds (195659123 / 500000000) (391318247 / 1000000000) (Real.log (739464551313 / 500000000000)) := by
  have h := reflection_log_6030_neg
  have he : Real.log (739464551313 / 500000000000) = -Real.log (500000000000 / 739464551313) := by
    rw [show ((739464551313 / 500000000000) : ℝ) = ((500000000000 / 739464551313) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6031_neg : (78305201 / 200000000) ≤ -Real.log (125000000000 / 184904549399) ∧
    -Real.log (125000000000 / 184904549399) ≤ (195763003 / 500000000) := by
  have h := checkLog_sound (w := (59904549399 / 309904549399)) (n := 12)
    (lo := (78305201 / 200000000)) (hi := (195763003 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((184904549399 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(184904549399 / 125000000000) = 1/(125000000000 / 184904549399) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6031 : Bounds (78305201 / 200000000) (195763003 / 500000000) (Real.log (184904549399 / 125000000000)) := by
  have h := reflection_log_6031_neg
  have he : Real.log (184904549399 / 125000000000) = -Real.log (125000000000 / 184904549399) := by
    rw [show ((184904549399 / 125000000000) : ℝ) = ((125000000000 / 184904549399) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6032_neg : (22100797 / 125000000) ≤ -Real.log (5000 / 5967) ∧
    -Real.log (5000 / 5967) ≤ (176806377 / 1000000000) := by
  have h := checkLog_sound (w := (967 / 10967)) (n := 12)
    (lo := (22100797 / 125000000)) (hi := (176806377 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5967 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5967 / 5000) = 1/(5000 / 5967) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6032 : Bounds (22100797 / 125000000) (176806377 / 1000000000) (Real.log (5967 / 5000)) := by
  have h := reflection_log_6032_neg
  have he : Real.log (5967 / 5000) = -Real.log (5000 / 5967) := by
    rw [show ((5967 / 5000) : ℝ) = ((5000 / 5967) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6033_neg : (53731849 / 250000000) ≤ -Real.log (4033 / 5000) ∧
    -Real.log (4033 / 5000) ≤ (214927397 / 1000000000) := by
  have h := checkLog_sound (w := (967 / 9033)) (n := 12)
    (lo := (53731849 / 250000000)) (hi := (214927397 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4033) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4033) = 1/(4033 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6033 : Bounds (-214927397 / 1000000000) (-53731849 / 250000000) (Real.log (4033 / 5000)) := by
  have h := reflection_log_6033_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6034_neg : (193381 / 1000000000) ≤ -Real.log (5000000 / 5000967) ∧
    -Real.log (5000000 / 5000967) ≤ (96691 / 500000000) := by
  have h := checkLog_sound (w := (967 / 10000967)) (n := 12)
    (lo := (193381 / 1000000000)) (hi := (96691 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000967 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000967 / 5000000) = 1/(5000000 / 5000967) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6034 : Bounds (193381 / 1000000000) (96691 / 500000000) (Real.log (5000967 / 5000000)) := by
  have h := reflection_log_6034_neg
  have he : Real.log (5000967 / 5000000) = -Real.log (5000000 / 5000967) := by
    rw [show ((5000967 / 5000000) : ℝ) = ((5000000 / 5000967) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6035_neg : (96709 / 500000000) ≤ -Real.log (4999033 / 5000000) ∧
    -Real.log (4999033 / 5000000) ≤ (193419 / 1000000000) := by
  have h := checkLog_sound (w := (967 / 9999033)) (n := 12)
    (lo := (96709 / 500000000)) (hi := (193419 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999033) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999033) = 1/(4999033 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6035 : Bounds (-193419 / 1000000000) (-96709 / 500000000) (Real.log (4999033 / 5000000)) := by
  have h := reflection_log_6035_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6036_neg : (1449569 / 15625000) ≤ -Real.log (250000 / 274303) ∧
    -Real.log (250000 / 274303) ≤ (92772417 / 1000000000) := by
  have h := checkLog_sound (w := (24303 / 524303)) (n := 12)
    (lo := (1449569 / 15625000)) (hi := (92772417 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((274303 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(274303 / 250000) = 1/(250000 / 274303) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6036 : Bounds (1449569 / 15625000) (92772417 / 1000000000) (Real.log (274303 / 250000)) := by
  have h := reflection_log_6036_neg
  have he : Real.log (274303 / 250000) = -Real.log (250000 / 274303) := by
    rw [show ((274303 / 250000) : ℝ) = ((250000 / 274303) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6037_neg : (51133763 / 500000000) ≤ -Real.log (225697 / 250000) ∧
    -Real.log (225697 / 250000) ≤ (102267527 / 1000000000) := by
  have h := checkLog_sound (w := (24303 / 475697)) (n := 12)
    (lo := (51133763 / 500000000)) (hi := (102267527 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 225697) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 225697) = 1/(225697 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6037 : Bounds (-102267527 / 1000000000) (-51133763 / 500000000) (Real.log (225697 / 250000)) := by
  have h := reflection_log_6037_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6038_neg : (46497387 / 500000000) ≤ -Real.log (62500 / 68591) ∧
    -Real.log (62500 / 68591) ≤ (3719791 / 40000000) := by
  have h := checkLog_sound (w := (6091 / 131091)) (n := 12)
    (lo := (46497387 / 500000000)) (hi := (3719791 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((68591 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(68591 / 62500) = 1/(62500 / 68591) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6038 : Bounds (46497387 / 500000000) (3719791 / 40000000) (Real.log (68591 / 62500)) := by
  have h := reflection_log_6038_neg
  have he : Real.log (68591 / 62500) = -Real.log (62500 / 68591) := by
    rw [show ((68591 / 62500) : ℝ) = ((62500 / 68591) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6039_neg : (25634459 / 250000000) ≤ -Real.log (56409 / 62500) ∧
    -Real.log (56409 / 62500) ≤ (102537837 / 1000000000) := by
  have h := checkLog_sound (w := (6091 / 118909)) (n := 12)
    (lo := (25634459 / 250000000)) (hi := (102537837 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 56409) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 56409) = 1/(56409 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6039 : Bounds (-102537837 / 1000000000) (-25634459 / 250000000) (Real.log (56409 / 62500)) := by
  have h := reflection_log_6039_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6040_neg : (4771531 / 500000000) ≤ -Real.log (3869149719 / 3906250000) ∧
    -Real.log (3869149719 / 3906250000) ≤ (9543063 / 1000000000) := by
  have h := checkLog_sound (w := (37100281 / 7775399719)) (n := 12)
    (lo := (4771531 / 500000000)) (hi := (9543063 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3906250000 / 3869149719) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3906250000 / 3869149719) = 1/(3869149719 / 3906250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6040 : Bounds (-9543063 / 1000000000) (-4771531 / 500000000) (Real.log (3869149719 / 3906250000)) := by
  have h := reflection_log_6040_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6041_neg : (9495109 / 1000000000) ≤ -Real.log (61909364191 / 62500000000) ∧
    -Real.log (61909364191 / 62500000000) ≤ (949511 / 100000000) := by
  have h := checkLog_sound (w := (590635809 / 124409364191)) (n := 12)
    (lo := (9495109 / 1000000000)) (hi := (949511 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 61909364191) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 61909364191) = 1/(61909364191 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6041 : Bounds (-949511 / 100000000) (-9495109 / 1000000000) (Real.log (61909364191 / 62500000000)) := by
  have h := reflection_log_6041_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6042_neg : (195039943 / 1000000000) ≤ -Real.log (500000000000 / 607679765349) ∧
    -Real.log (500000000000 / 607679765349) ≤ (24379993 / 125000000) := by
  have h := checkLog_sound (w := (107679765349 / 1107679765349)) (n := 12)
    (lo := (195039943 / 1000000000)) (hi := (24379993 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((607679765349 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(607679765349 / 500000000000) = 1/(500000000000 / 607679765349) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6042 : Bounds (195039943 / 1000000000) (24379993 / 125000000) (Real.log (607679765349 / 500000000000)) := by
  have h := reflection_log_6042_neg
  have he : Real.log (607679765349 / 500000000000) = -Real.log (500000000000 / 607679765349) := by
    rw [show ((607679765349 / 500000000000) : ℝ) = ((500000000000 / 607679765349) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6043_neg : (19553261 / 100000000) ≤ -Real.log (250000000000 / 303989611587) ∧
    -Real.log (250000000000 / 303989611587) ≤ (195532611 / 1000000000) := by
  have h := checkLog_sound (w := (53989611587 / 553989611587)) (n := 12)
    (lo := (19553261 / 100000000)) (hi := (195532611 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((303989611587 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(303989611587 / 250000000000) = 1/(250000000000 / 303989611587) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6043 : Bounds (19553261 / 100000000) (195532611 / 1000000000) (Real.log (303989611587 / 250000000000)) := by
  have h := reflection_log_6043_neg
  have he : Real.log (303989611587 / 250000000000) = -Real.log (250000000000 / 303989611587) := by
    rw [show ((303989611587 / 250000000000) : ℝ) = ((250000000000 / 303989611587) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6044_neg : (78305201 / 200000000) ≤ -Real.log (100000000000 / 147923639519) ∧
    -Real.log (100000000000 / 147923639519) ≤ (195763003 / 500000000) := by
  have h := checkLog_sound (w := (47923639519 / 247923639519)) (n := 12)
    (lo := (78305201 / 200000000)) (hi := (195763003 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((147923639519 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(147923639519 / 100000000000) = 1/(100000000000 / 147923639519) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6044 : Bounds (78305201 / 200000000) (195763003 / 500000000) (Real.log (147923639519 / 100000000000)) := by
  have h := reflection_log_6044_neg
  have he : Real.log (147923639519 / 100000000000) = -Real.log (100000000000 / 147923639519) := by
    rw [show ((147923639519 / 100000000000) : ℝ) = ((100000000000 / 147923639519) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6045_neg : (97933443 / 250000000) ≤ -Real.log (250000000000 / 369885940987) ∧
    -Real.log (250000000000 / 369885940987) ≤ (391733773 / 1000000000) := by
  have h := checkLog_sound (w := (119885940987 / 619885940987)) (n := 12)
    (lo := (97933443 / 250000000)) (hi := (391733773 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((369885940987 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(369885940987 / 250000000000) = 1/(250000000000 / 369885940987) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6045 : Bounds (97933443 / 250000000) (391733773 / 1000000000) (Real.log (369885940987 / 250000000000)) := by
  have h := reflection_log_6045_neg
  have he : Real.log (369885940987 / 250000000000) = -Real.log (250000000000 / 369885940987) := by
    rw [show ((369885940987 / 250000000000) : ℝ) = ((250000000000 / 369885940987) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6046_neg : (88445083 / 500000000) ≤ -Real.log (2000 / 2387) ∧
    -Real.log (2000 / 2387) ≤ (176890167 / 1000000000) := by
  have h := checkLog_sound (w := (387 / 4387)) (n := 12)
    (lo := (88445083 / 500000000)) (hi := (176890167 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2387 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2387 / 2000) = 1/(2000 / 2387) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6046 : Bounds (88445083 / 500000000) (176890167 / 1000000000) (Real.log (2387 / 2000)) := by
  have h := reflection_log_6046_neg
  have he : Real.log (2387 / 2000) = -Real.log (2000 / 2387) := by
    rw [show ((2387 / 2000) : ℝ) = ((2000 / 2387) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6047_neg : (215051381 / 1000000000) ≤ -Real.log (1613 / 2000) ∧
    -Real.log (1613 / 2000) ≤ (107525691 / 500000000) := by
  have h := checkLog_sound (w := (387 / 3613)) (n := 12)
    (lo := (215051381 / 1000000000)) (hi := (107525691 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1613) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1613) = 1/(1613 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6047 : Bounds (-107525691 / 500000000) (-215051381 / 1000000000) (Real.log (1613 / 2000)) := by
  have h := reflection_log_6047_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6048_neg : (193481 / 1000000000) ≤ -Real.log (2000000 / 2000387) ∧
    -Real.log (2000000 / 2000387) ≤ (96741 / 500000000) := by
  have h := checkLog_sound (w := (387 / 4000387)) (n := 12)
    (lo := (193481 / 1000000000)) (hi := (96741 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000387 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000387 / 2000000) = 1/(2000000 / 2000387) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6048 : Bounds (193481 / 1000000000) (96741 / 500000000) (Real.log (2000387 / 2000000)) := by
  have h := reflection_log_6048_neg
  have he : Real.log (2000387 / 2000000) = -Real.log (2000000 / 2000387) := by
    rw [show ((2000387 / 2000000) : ℝ) = ((2000000 / 2000387) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6049_neg : (96759 / 500000000) ≤ -Real.log (1999613 / 2000000) ∧
    -Real.log (1999613 / 2000000) ≤ (193519 / 1000000000) := by
  have h := checkLog_sound (w := (387 / 3999613)) (n := 12)
    (lo := (96759 / 500000000)) (hi := (193519 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999613) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999613) = 1/(1999613 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6049 : Bounds (-193519 / 1000000000) (-96759 / 500000000) (Real.log (1999613 / 2000000)) := by
  have h := reflection_log_6049_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6050_neg : (92818897 / 1000000000) ≤ -Real.log (1000000 / 1097263) ∧
    -Real.log (1000000 / 1097263) ≤ (46409449 / 500000000) := by
  have h := checkLog_sound (w := (97263 / 2097263)) (n := 12)
    (lo := (92818897 / 1000000000)) (hi := (46409449 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1097263 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1097263 / 1000000) = 1/(1000000 / 1097263) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6050 : Bounds (92818897 / 1000000000) (46409449 / 500000000) (Real.log (1097263 / 1000000)) := by
  have h := reflection_log_6050_neg
  have he : Real.log (1097263 / 1000000) = -Real.log (1000000 / 1097263) := by
    rw [show ((1097263 / 1000000) : ℝ) = ((1000000 / 1097263) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6051_neg : (102324019 / 1000000000) ≤ -Real.log (902737 / 1000000) ∧
    -Real.log (902737 / 1000000) ≤ (5116201 / 50000000) := by
  have h := checkLog_sound (w := (97263 / 1902737)) (n := 12)
    (lo := (102324019 / 1000000000)) (hi := (5116201 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 902737) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 902737) = 1/(902737 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6051 : Bounds (-5116201 / 50000000) (-102324019 / 1000000000) (Real.log (902737 / 1000000)) := by
  have h := reflection_log_6051_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6052_neg : (23260311 / 250000000) ≤ -Real.log (1000000 / 1097507) ∧
    -Real.log (1000000 / 1097507) ≤ (18608249 / 200000000) := by
  have h := checkLog_sound (w := (97507 / 2097507)) (n := 12)
    (lo := (23260311 / 250000000)) (hi := (18608249 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1097507 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1097507 / 1000000) = 1/(1000000 / 1097507) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6052 : Bounds (23260311 / 250000000) (18608249 / 200000000) (Real.log (1097507 / 1000000)) := by
  have h := reflection_log_6052_neg
  have he : Real.log (1097507 / 1000000) = -Real.log (1000000 / 1097507) := by
    rw [show ((1097507 / 1000000) : ℝ) = ((1000000 / 1097507) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6053_neg : (20518869 / 200000000) ≤ -Real.log (902493 / 1000000) ∧
    -Real.log (902493 / 1000000) ≤ (51297173 / 500000000) := by
  have h := checkLog_sound (w := (97507 / 1902493)) (n := 12)
    (lo := (20518869 / 200000000)) (hi := (51297173 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 902493) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 902493) = 1/(902493 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6053 : Bounds (-51297173 / 500000000) (-20518869 / 200000000) (Real.log (902493 / 1000000)) := by
  have h := reflection_log_6053_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6054_neg : (95531 / 10000000) ≤ -Real.log (990492384951 / 1000000000000) ∧
    -Real.log (990492384951 / 1000000000000) ≤ (9553101 / 1000000000) := by
  have h := checkLog_sound (w := (9507615049 / 1990492384951)) (n := 12)
    (lo := (95531 / 10000000)) (hi := (9553101 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 990492384951) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 990492384951) = 1/(990492384951 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6054 : Bounds (-9553101 / 1000000000) (-95531 / 10000000) (Real.log (990492384951 / 1000000000000)) := by
  have h := reflection_log_6054_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6055_neg : (4752561 / 500000000) ≤ -Real.log (990539908831 / 1000000000000) ∧
    -Real.log (990539908831 / 1000000000000) ≤ (9505123 / 1000000000) := by
  have h := checkLog_sound (w := (9460091169 / 1990539908831)) (n := 12)
    (lo := (4752561 / 500000000)) (hi := (9505123 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 990539908831) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 990539908831) = 1/(990539908831 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6055 : Bounds (-9505123 / 1000000000) (-4752561 / 500000000) (Real.log (990539908831 / 1000000000000)) := by
  have h := reflection_log_6055_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6056_neg : (48785729 / 250000000) ≤ -Real.log (500000000000 / 607742343561) ∧
    -Real.log (500000000000 / 607742343561) ≤ (195142917 / 1000000000) := by
  have h := checkLog_sound (w := (107742343561 / 1107742343561)) (n := 12)
    (lo := (48785729 / 250000000)) (hi := (195142917 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((607742343561 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(607742343561 / 500000000000) = 1/(500000000000 / 607742343561) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6056 : Bounds (48785729 / 250000000) (195142917 / 1000000000) (Real.log (607742343561 / 500000000000)) := by
  have h := reflection_log_6056_neg
  have he : Real.log (607742343561 / 500000000000) = -Real.log (500000000000 / 607742343561) := by
    rw [show ((607742343561 / 500000000000) : ℝ) = ((500000000000 / 607742343561) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6057_neg : (195635589 / 1000000000) ≤ -Real.log (125000000000 / 152010458807) ∧
    -Real.log (125000000000 / 152010458807) ≤ (19563559 / 100000000) := by
  have h := checkLog_sound (w := (27010458807 / 277010458807)) (n := 12)
    (lo := (195635589 / 1000000000)) (hi := (19563559 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((152010458807 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(152010458807 / 125000000000) = 1/(125000000000 / 152010458807) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6057 : Bounds (195635589 / 1000000000) (19563559 / 100000000) (Real.log (152010458807 / 125000000000)) := by
  have h := reflection_log_6057_neg
  have he : Real.log (152010458807 / 125000000000) = -Real.log (125000000000 / 152010458807) := by
    rw [show ((152010458807 / 125000000000) : ℝ) = ((125000000000 / 152010458807) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6058_neg : (97933443 / 250000000) ≤ -Real.log (500000000000 / 739771881973) ∧
    -Real.log (500000000000 / 739771881973) ≤ (391733773 / 1000000000) := by
  have h := checkLog_sound (w := (239771881973 / 1239771881973)) (n := 12)
    (lo := (97933443 / 250000000)) (hi := (391733773 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((739771881973 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(739771881973 / 500000000000) = 1/(500000000000 / 739771881973) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6058 : Bounds (97933443 / 250000000) (391733773 / 1000000000) (Real.log (739771881973 / 500000000000)) := by
  have h := reflection_log_6058_neg
  have he : Real.log (739771881973 / 500000000000) = -Real.log (500000000000 / 739771881973) := by
    rw [show ((739771881973 / 500000000000) : ℝ) = ((500000000000 / 739771881973) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6059_neg : (97985387 / 250000000) ≤ -Real.log (31250000000 / 46245350279) ∧
    -Real.log (31250000000 / 46245350279) ≤ (391941549 / 1000000000) := by
  have h := checkLog_sound (w := (14995350279 / 77495350279)) (n := 12)
    (lo := (97985387 / 250000000)) (hi := (391941549 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((46245350279 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(46245350279 / 31250000000) = 1/(31250000000 / 46245350279) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6059 : Bounds (97985387 / 250000000) (391941549 / 1000000000) (Real.log (46245350279 / 31250000000)) := by
  have h := reflection_log_6059_neg
  have he : Real.log (46245350279 / 31250000000) = -Real.log (31250000000 / 46245350279) := by
    rw [show ((46245350279 / 31250000000) : ℝ) = ((31250000000 / 46245350279) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6060_neg : (3539479 / 20000000) ≤ -Real.log (625 / 746) ∧
    -Real.log (625 / 746) ≤ (176973951 / 1000000000) := by
  have h := checkLog_sound (w := (121 / 1371)) (n := 12)
    (lo := (3539479 / 20000000)) (hi := (176973951 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((746 / 625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(746 / 625) = 1/(625 / 746) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6060 : Bounds (3539479 / 20000000) (176973951 / 1000000000) (Real.log (746 / 625)) := by
  have h := reflection_log_6060_neg
  have he : Real.log (746 / 625) = -Real.log (625 / 746) := by
    rw [show ((746 / 625) : ℝ) = ((625 / 746) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6061_neg : (215175381 / 1000000000) ≤ -Real.log (504 / 625) ∧
    -Real.log (504 / 625) ≤ (107587691 / 500000000) := by
  have h := checkLog_sound (w := (121 / 1129)) (n := 12)
    (lo := (215175381 / 1000000000)) (hi := (107587691 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625 / 504) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625 / 504) = 1/(504 / 625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6061 : Bounds (-107587691 / 500000000) (-215175381 / 1000000000) (Real.log (504 / 625)) := by
  have h := reflection_log_6061_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6062_neg : (193581 / 1000000000) ≤ -Real.log (625000 / 625121) ∧
    -Real.log (625000 / 625121) ≤ (96791 / 500000000) := by
  have h := checkLog_sound (w := (121 / 1250121)) (n := 12)
    (lo := (193581 / 1000000000)) (hi := (96791 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625121 / 625000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625121 / 625000) = 1/(625000 / 625121) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6062 : Bounds (193581 / 1000000000) (96791 / 500000000) (Real.log (625121 / 625000)) := by
  have h := reflection_log_6062_neg
  have he : Real.log (625121 / 625000) = -Real.log (625000 / 625121) := by
    rw [show ((625121 / 625000) : ℝ) = ((625000 / 625121) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6063_neg : (96809 / 500000000) ≤ -Real.log (624879 / 625000) ∧
    -Real.log (624879 / 625000) ≤ (193619 / 1000000000) := by
  have h := checkLog_sound (w := (121 / 1249879)) (n := 12)
    (lo := (96809 / 500000000)) (hi := (193619 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625000 / 624879) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625000 / 624879) = 1/(624879 / 625000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6063 : Bounds (-193619 / 1000000000) (-96809 / 500000000) (Real.log (624879 / 625000)) := by
  have h := reflection_log_6063_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6064_neg : (742923 / 8000000) ≤ -Real.log (500000 / 548657) ∧
    -Real.log (500000 / 548657) ≤ (2902043 / 31250000) := by
  have h := checkLog_sound (w := (48657 / 1048657)) (n := 12)
    (lo := (742923 / 8000000)) (hi := (2902043 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((548657 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(548657 / 500000) = 1/(500000 / 548657) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6064 : Bounds (742923 / 8000000) (2902043 / 31250000) (Real.log (548657 / 500000)) := by
  have h := reflection_log_6064_neg
  have he : Real.log (548657 / 500000) = -Real.log (500000 / 548657) := by
    rw [show ((548657 / 500000) : ℝ) = ((500000 / 548657) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6065_neg : (20476103 / 200000000) ≤ -Real.log (451343 / 500000) ∧
    -Real.log (451343 / 500000) ≤ (25595129 / 250000000) := by
  have h := checkLog_sound (w := (48657 / 951343)) (n := 12)
    (lo := (20476103 / 200000000)) (hi := (25595129 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 451343) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 451343) = 1/(451343 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6065 : Bounds (-25595129 / 250000000) (-20476103 / 200000000) (Real.log (451343 / 500000)) := by
  have h := reflection_log_6065_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6066_neg : (93087711 / 1000000000) ≤ -Real.log (500000 / 548779) ∧
    -Real.log (500000 / 548779) ≤ (2908991 / 31250000) := by
  have h := checkLog_sound (w := (48779 / 1048779)) (n := 12)
    (lo := (93087711 / 1000000000)) (hi := (2908991 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((548779 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(548779 / 500000) = 1/(500000 / 548779) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6066 : Bounds (93087711 / 1000000000) (2908991 / 31250000) (Real.log (548779 / 500000)) := by
  have h := reflection_log_6066_neg
  have he : Real.log (548779 / 500000) = -Real.log (500000 / 548779) := by
    rw [show ((548779 / 500000) : ℝ) = ((500000 / 548779) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6067_neg : (12831357 / 125000000) ≤ -Real.log (451221 / 500000) ∧
    -Real.log (451221 / 500000) ≤ (102650857 / 1000000000) := by
  have h := checkLog_sound (w := (48779 / 951221)) (n := 12)
    (lo := (12831357 / 125000000)) (hi := (102650857 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 451221) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 451221) = 1/(451221 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6067 : Bounds (-102650857 / 1000000000) (-12831357 / 125000000) (Real.log (451221 / 500000)) := by
  have h := reflection_log_6067_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6068_neg : (1195393 / 125000000) ≤ -Real.log (247620609159 / 250000000000) ∧
    -Real.log (247620609159 / 250000000000) ≤ (1912629 / 200000000) := by
  have h := checkLog_sound (w := (2379390841 / 497620609159)) (n := 12)
    (lo := (1195393 / 125000000)) (hi := (1912629 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247620609159) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247620609159) = 1/(247620609159 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6068 : Bounds (-1912629 / 200000000) (-1195393 / 125000000) (Real.log (247620609159 / 250000000000)) := by
  have h := reflection_log_6068_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6069_neg : (475757 / 50000000) ≤ -Real.log (247632496351 / 250000000000) ∧
    -Real.log (247632496351 / 250000000000) ≤ (9515141 / 1000000000) := by
  have h := checkLog_sound (w := (2367503649 / 497632496351)) (n := 12)
    (lo := (475757 / 50000000)) (hi := (9515141 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247632496351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247632496351) = 1/(247632496351 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6069 : Bounds (-9515141 / 1000000000) (-475757 / 50000000) (Real.log (247632496351 / 250000000000)) := by
  have h := reflection_log_6069_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6070_neg : (195245891 / 1000000000) ≤ -Real.log (100000000000 / 121560985769) ∧
    -Real.log (100000000000 / 121560985769) ≤ (48811473 / 250000000) := by
  have h := checkLog_sound (w := (21560985769 / 221560985769)) (n := 12)
    (lo := (195245891 / 1000000000)) (hi := (48811473 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((121560985769 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(121560985769 / 100000000000) = 1/(100000000000 / 121560985769) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6070 : Bounds (195245891 / 1000000000) (48811473 / 250000000) (Real.log (121560985769 / 100000000000)) := by
  have h := reflection_log_6070_neg
  have he : Real.log (121560985769 / 100000000000) = -Real.log (100000000000 / 121560985769) := by
    rw [show ((121560985769 / 100000000000) : ℝ) = ((100000000000 / 121560985769) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6071_neg : (24467321 / 125000000) ≤ -Real.log (500000000000 / 608104454359) ∧
    -Real.log (500000000000 / 608104454359) ≤ (195738569 / 1000000000) := by
  have h := checkLog_sound (w := (108104454359 / 1108104454359)) (n := 12)
    (lo := (24467321 / 125000000)) (hi := (195738569 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((608104454359 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(608104454359 / 500000000000) = 1/(500000000000 / 608104454359) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6071 : Bounds (24467321 / 125000000) (195738569 / 1000000000) (Real.log (608104454359 / 500000000000)) := by
  have h := reflection_log_6071_neg
  have he : Real.log (608104454359 / 500000000000) = -Real.log (500000000000 / 608104454359) := by
    rw [show ((608104454359 / 500000000000) : ℝ) = ((500000000000 / 608104454359) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6072_neg : (97985387 / 250000000) ≤ -Real.log (500000000000 / 739925604463) ∧
    -Real.log (500000000000 / 739925604463) ≤ (391941549 / 1000000000) := by
  have h := checkLog_sound (w := (239925604463 / 1239925604463)) (n := 12)
    (lo := (97985387 / 250000000)) (hi := (391941549 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((739925604463 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(739925604463 / 500000000000) = 1/(500000000000 / 739925604463) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6072 : Bounds (97985387 / 250000000) (391941549 / 1000000000) (Real.log (739925604463 / 500000000000)) := by
  have h := reflection_log_6072_neg
  have he : Real.log (739925604463 / 500000000000) = -Real.log (500000000000 / 739925604463) := by
    rw [show ((739925604463 / 500000000000) : ℝ) = ((500000000000 / 739925604463) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6073_neg : (98037333 / 250000000) ≤ -Real.log (12500000000 / 18501984127) ∧
    -Real.log (12500000000 / 18501984127) ≤ (392149333 / 1000000000) := by
  have h := checkLog_sound (w := (6001984127 / 31001984127)) (n := 12)
    (lo := (98037333 / 250000000)) (hi := (392149333 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((18501984127 / 12500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(18501984127 / 12500000000) = 1/(12500000000 / 18501984127) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6073 : Bounds (98037333 / 250000000) (392149333 / 1000000000) (Real.log (18501984127 / 12500000000)) := by
  have h := reflection_log_6073_neg
  have he : Real.log (18501984127 / 12500000000) = -Real.log (12500000000 / 18501984127) := by
    rw [show ((18501984127 / 12500000000) : ℝ) = ((12500000000 / 18501984127) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6074_neg : (177057727 / 1000000000) ≤ -Real.log (10000 / 11937) ∧
    -Real.log (10000 / 11937) ≤ (2766527 / 15625000) := by
  have h := checkLog_sound (w := (1937 / 21937)) (n := 12)
    (lo := (177057727 / 1000000000)) (hi := (2766527 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11937 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11937 / 10000) = 1/(10000 / 11937) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6074 : Bounds (177057727 / 1000000000) (2766527 / 15625000) (Real.log (11937 / 10000)) := by
  have h := reflection_log_6074_neg
  have he : Real.log (11937 / 10000) = -Real.log (10000 / 11937) := by
    rw [show ((11937 / 10000) : ℝ) = ((10000 / 11937) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6075_neg : (215299397 / 1000000000) ≤ -Real.log (8063 / 10000) ∧
    -Real.log (8063 / 10000) ≤ (107649699 / 500000000) := by
  have h := checkLog_sound (w := (1937 / 18063)) (n := 12)
    (lo := (215299397 / 1000000000)) (hi := (107649699 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8063) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8063) = 1/(8063 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6075 : Bounds (-107649699 / 500000000) (-215299397 / 1000000000) (Real.log (8063 / 10000)) := by
  have h := reflection_log_6075_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6076_neg : (193681 / 1000000000) ≤ -Real.log (10000000 / 10001937) ∧
    -Real.log (10000000 / 10001937) ≤ (96841 / 500000000) := by
  have h := checkLog_sound (w := (1937 / 20001937)) (n := 12)
    (lo := (193681 / 1000000000)) (hi := (96841 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001937 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001937 / 10000000) = 1/(10000000 / 10001937) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6076 : Bounds (193681 / 1000000000) (96841 / 500000000) (Real.log (10001937 / 10000000)) := by
  have h := reflection_log_6076_neg
  have he : Real.log (10001937 / 10000000) = -Real.log (10000000 / 10001937) := by
    rw [show ((10001937 / 10000000) : ℝ) = ((10000000 / 10001937) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6077_neg : (96859 / 500000000) ≤ -Real.log (9998063 / 10000000) ∧
    -Real.log (9998063 / 10000000) ≤ (193719 / 1000000000) := by
  have h := checkLog_sound (w := (1937 / 19998063)) (n := 12)
    (lo := (96859 / 500000000)) (hi := (193719 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998063) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998063) = 1/(9998063 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6077 : Bounds (-193719 / 1000000000) (-96859 / 500000000) (Real.log (9998063 / 10000000)) := by
  have h := reflection_log_6077_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6078_neg : (92911851 / 1000000000) ≤ -Real.log (200000 / 219473) ∧
    -Real.log (200000 / 219473) ≤ (23227963 / 250000000) := by
  have h := checkLog_sound (w := (19473 / 419473)) (n := 12)
    (lo := (92911851 / 1000000000)) (hi := (23227963 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((219473 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(219473 / 200000) = 1/(200000 / 219473) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6078 : Bounds (92911851 / 1000000000) (23227963 / 250000000) (Real.log (219473 / 200000)) := by
  have h := reflection_log_6078_neg
  have he : Real.log (219473 / 200000) = -Real.log (200000 / 219473) := by
    rw [show ((219473 / 200000) : ℝ) = ((200000 / 219473) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6079_neg : (20487403 / 200000000) ≤ -Real.log (180527 / 200000) ∧
    -Real.log (180527 / 200000) ≤ (12804627 / 125000000) := by
  have h := checkLog_sound (w := (19473 / 380527)) (n := 12)
    (lo := (20487403 / 200000000)) (hi := (12804627 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 180527) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 180527) = 1/(180527 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6079 : Bounds (-12804627 / 125000000) (-20487403 / 200000000) (Real.log (180527 / 200000)) := by
  have h := reflection_log_6079_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.LowRatioFamily
