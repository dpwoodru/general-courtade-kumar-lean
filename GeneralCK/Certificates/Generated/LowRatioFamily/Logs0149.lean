import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_9536_neg : (74776033 / 250000000) ≤ -Real.log (500000000000 / 674325027333) ∧
    -Real.log (500000000000 / 674325027333) ≤ (299104133 / 1000000000) := by
  have h := checkLog_sound (w := (174325027333 / 1174325027333)) (n := 12)
    (lo := (74776033 / 250000000)) (hi := (299104133 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((674325027333 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(674325027333 / 500000000000) = 1/(500000000000 / 674325027333) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9536 : Bounds (74776033 / 250000000) (299104133 / 1000000000) (Real.log (674325027333 / 500000000000)) := by
  have h := reflection_log_9536_neg
  have he : Real.log (674325027333 / 500000000000) = -Real.log (500000000000 / 674325027333) := by
    rw [show ((674325027333 / 500000000000) : ℝ) = ((500000000000 / 674325027333) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9537_neg : (600409553 / 1000000000) ≤ -Real.log (500000000000 / 911432604093) ∧
    -Real.log (500000000000 / 911432604093) ≤ (300204777 / 500000000) := by
  have h := checkLog_sound (w := (411432604093 / 1411432604093)) (n := 12)
    (lo := (600409553 / 1000000000)) (hi := (300204777 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((911432604093 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(911432604093 / 500000000000) = 1/(500000000000 / 911432604093) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9537 : Bounds (600409553 / 1000000000) (300204777 / 500000000) (Real.log (911432604093 / 500000000000)) := by
  have h := reflection_log_9537_neg
  have he : Real.log (911432604093 / 500000000000) = -Real.log (500000000000 / 911432604093) := by
    rw [show ((911432604093 / 500000000000) : ℝ) = ((500000000000 / 911432604093) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9538_neg : (60150259 / 100000000) ≤ -Real.log (125000000000 / 228107344633) ∧
    -Real.log (125000000000 / 228107344633) ≤ (601502591 / 1000000000) := by
  have h := checkLog_sound (w := (103107344633 / 353107344633)) (n := 12)
    (lo := (60150259 / 100000000)) (hi := (601502591 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((228107344633 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(228107344633 / 125000000000) = 1/(125000000000 / 228107344633) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9538 : Bounds (60150259 / 100000000) (601502591 / 1000000000) (Real.log (228107344633 / 125000000000)) := by
  have h := reflection_log_9538_neg
  have he : Real.log (228107344633 / 125000000000) = -Real.log (125000000000 / 228107344633) := by
    rw [show ((228107344633 / 125000000000) : ℝ) = ((125000000000 / 228107344633) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9539_neg : (256578327 / 1000000000) ≤ -Real.log (400 / 517) ∧
    -Real.log (400 / 517) ≤ (32072291 / 125000000) := by
  have h := checkLog_sound (w := (117 / 917)) (n := 12)
    (lo := (256578327 / 1000000000)) (hi := (32072291 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((517 / 400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(517 / 400) = 1/(400 / 517) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9539 : Bounds (256578327 / 1000000000) (32072291 / 125000000) (Real.log (517 / 400)) := by
  have h := reflection_log_9539_neg
  have he : Real.log (517 / 400) = -Real.log (400 / 517) := by
    rw [show ((517 / 400) : ℝ) = ((400 / 517) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9540_neg : (346017649 / 1000000000) ≤ -Real.log (283 / 400) ∧
    -Real.log (283 / 400) ≤ (6920353 / 20000000) := by
  have h := checkLog_sound (w := (117 / 683)) (n := 12)
    (lo := (346017649 / 1000000000)) (hi := (6920353 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 283) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400 / 283) = 1/(283 / 400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9540 : Bounds (-6920353 / 20000000) (-346017649 / 1000000000) (Real.log (283 / 400)) := by
  have h := reflection_log_9540_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9541_neg : (292457 / 1000000000) ≤ -Real.log (400000 / 400117) ∧
    -Real.log (400000 / 400117) ≤ (146229 / 500000000) := by
  have h := checkLog_sound (w := (117 / 800117)) (n := 12)
    (lo := (292457 / 1000000000)) (hi := (146229 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400117 / 400000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400117 / 400000) = 1/(400000 / 400117) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9541 : Bounds (292457 / 1000000000) (146229 / 500000000) (Real.log (400117 / 400000)) := by
  have h := reflection_log_9541_neg
  have he : Real.log (400117 / 400000) = -Real.log (400000 / 400117) := by
    rw [show ((400117 / 400000) : ℝ) = ((400000 / 400117) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9542_neg : (146271 / 500000000) ≤ -Real.log (399883 / 400000) ∧
    -Real.log (399883 / 400000) ≤ (292543 / 1000000000) := by
  have h := checkLog_sound (w := (117 / 799883)) (n := 12)
    (lo := (146271 / 500000000)) (hi := (292543 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400000 / 399883) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400000 / 399883) = 1/(399883 / 400000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9542 : Bounds (-292543 / 1000000000) (-146271 / 500000000) (Real.log (399883 / 400000)) := by
  have h := reflection_log_9542_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9543_neg : (13815979 / 100000000) ≤ -Real.log (1000000 / 1148159) ∧
    -Real.log (1000000 / 1148159) ≤ (138159791 / 1000000000) := by
  have h := checkLog_sound (w := (148159 / 2148159)) (n := 12)
    (lo := (13815979 / 100000000)) (hi := (138159791 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1148159 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1148159 / 1000000) = 1/(1000000 / 1148159) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9543 : Bounds (13815979 / 100000000) (138159791 / 1000000000) (Real.log (1148159 / 1000000)) := by
  have h := reflection_log_9543_neg
  have he : Real.log (1148159 / 1000000) = -Real.log (1000000 / 1148159) := by
    rw [show ((1148159 / 1000000) : ℝ) = ((1000000 / 1148159) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9544_neg : (160355389 / 1000000000) ≤ -Real.log (851841 / 1000000) ∧
    -Real.log (851841 / 1000000) ≤ (16035539 / 100000000) := by
  have h := checkLog_sound (w := (148159 / 1851841)) (n := 12)
    (lo := (160355389 / 1000000000)) (hi := (16035539 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 851841) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 851841) = 1/(851841 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9544 : Bounds (-16035539 / 100000000) (-160355389 / 1000000000) (Real.log (851841 / 1000000)) := by
  have h := reflection_log_9544_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9545_neg : (138638703 / 1000000000) ≤ -Real.log (1000000 / 1148709) ∧
    -Real.log (1000000 / 1148709) ≤ (8664919 / 62500000) := by
  have h := checkLog_sound (w := (148709 / 2148709)) (n := 12)
    (lo := (138638703 / 1000000000)) (hi := (8664919 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1148709 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1148709 / 1000000) = 1/(1000000 / 1148709) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9545 : Bounds (138638703 / 1000000000) (8664919 / 62500000) (Real.log (1148709 / 1000000)) := by
  have h := reflection_log_9545_neg
  have he : Real.log (1148709 / 1000000) = -Real.log (1000000 / 1148709) := by
    rw [show ((1148709 / 1000000) : ℝ) = ((1000000 / 1148709) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9546_neg : (80500629 / 500000000) ≤ -Real.log (851291 / 1000000) ∧
    -Real.log (851291 / 1000000) ≤ (161001259 / 1000000000) := by
  have h := checkLog_sound (w := (148709 / 1851291)) (n := 12)
    (lo := (80500629 / 500000000)) (hi := (161001259 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 851291) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 851291) = 1/(851291 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9546 : Bounds (-161001259 / 1000000000) (-80500629 / 500000000) (Real.log (851291 / 1000000)) := by
  have h := reflection_log_9546_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9547_neg : (4472511 / 200000000) ≤ -Real.log (977885633319 / 1000000000000) ∧
    -Real.log (977885633319 / 1000000000000) ≤ (5590639 / 250000000) := by
  have h := checkLog_sound (w := (22114366681 / 1977885633319)) (n := 12)
    (lo := (4472511 / 200000000)) (hi := (5590639 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 977885633319) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 977885633319) = 1/(977885633319 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9547 : Bounds (-5590639 / 250000000) (-4472511 / 200000000) (Real.log (977885633319 / 1000000000000)) := by
  have h := reflection_log_9547_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9548_neg : (22195599 / 1000000000) ≤ -Real.log (978048910719 / 1000000000000) ∧
    -Real.log (978048910719 / 1000000000000) ≤ (55489 / 2500000) := by
  have h := checkLog_sound (w := (21951089281 / 1978048910719)) (n := 12)
    (lo := (22195599 / 1000000000)) (hi := (55489 / 2500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 978048910719) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 978048910719) = 1/(978048910719 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9548 : Bounds (-55489 / 2500000) (-22195599 / 1000000000) (Real.log (978048910719 / 1000000000000)) := by
  have h := reflection_log_9548_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9549_neg : (298515179 / 1000000000) ≤ -Real.log (5000000000 / 6739279983) ∧
    -Real.log (5000000000 / 6739279983) ≤ (14925759 / 50000000) := by
  have h := checkLog_sound (w := (1739279983 / 11739279983)) (n := 12)
    (lo := (298515179 / 1000000000)) (hi := (14925759 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6739279983 / 5000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6739279983 / 5000000000) = 1/(5000000000 / 6739279983) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9549 : Bounds (298515179 / 1000000000) (14925759 / 50000000) (Real.log (6739279983 / 5000000000)) := by
  have h := reflection_log_9549_neg
  have he : Real.log (6739279983 / 5000000000) = -Real.log (5000000000 / 6739279983) := by
    rw [show ((6739279983 / 5000000000) : ℝ) = ((5000000000 / 6739279983) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9550_neg : (299639961 / 1000000000) ≤ -Real.log (500000000000 / 674686446821) ∧
    -Real.log (500000000000 / 674686446821) ≤ (149819981 / 500000000) := by
  have h := checkLog_sound (w := (174686446821 / 1174686446821)) (n := 12)
    (lo := (299639961 / 1000000000)) (hi := (149819981 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((674686446821 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(674686446821 / 500000000000) = 1/(500000000000 / 674686446821) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9550 : Bounds (299639961 / 1000000000) (149819981 / 500000000) (Real.log (674686446821 / 500000000000)) := by
  have h := reflection_log_9550_neg
  have he : Real.log (674686446821 / 500000000000) = -Real.log (500000000000 / 674686446821) := by
    rw [show ((674686446821 / 500000000000) : ℝ) = ((500000000000 / 674686446821) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9551_neg : (60150259 / 100000000) ≤ -Real.log (500000000000 / 912429378531) ∧
    -Real.log (500000000000 / 912429378531) ≤ (601502591 / 1000000000) := by
  have h := checkLog_sound (w := (412429378531 / 1412429378531)) (n := 12)
    (lo := (60150259 / 100000000)) (hi := (601502591 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((912429378531 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(912429378531 / 500000000000) = 1/(500000000000 / 912429378531) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9551 : Bounds (60150259 / 100000000) (601502591 / 1000000000) (Real.log (912429378531 / 500000000000)) := by
  have h := reflection_log_9551_neg
  have he : Real.log (912429378531 / 500000000000) = -Real.log (500000000000 / 912429378531) := by
    rw [show ((912429378531 / 500000000000) : ℝ) = ((500000000000 / 912429378531) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9552_neg : (75324497 / 125000000) ≤ -Real.log (250000000000 / 456713780919) ∧
    -Real.log (250000000000 / 456713780919) ≤ (602595977 / 1000000000) := by
  have h := checkLog_sound (w := (206713780919 / 706713780919)) (n := 12)
    (lo := (75324497 / 125000000)) (hi := (602595977 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((456713780919 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(456713780919 / 250000000000) = 1/(250000000000 / 456713780919) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9552 : Bounds (75324497 / 125000000) (602595977 / 1000000000) (Real.log (456713780919 / 250000000000)) := by
  have h := reflection_log_9552_neg
  have he : Real.log (456713780919 / 250000000000) = -Real.log (250000000000 / 456713780919) := by
    rw [show ((456713780919 / 250000000000) : ℝ) = ((250000000000 / 456713780919) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9553_neg : (256965099 / 1000000000) ≤ -Real.log (1000 / 1293) ∧
    -Real.log (1000 / 1293) ≤ (2569651 / 10000000) := by
  have h := checkLog_sound (w := (293 / 2293)) (n := 12)
    (lo := (256965099 / 1000000000)) (hi := (2569651 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1293 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1293 / 1000) = 1/(1000 / 1293) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9553 : Bounds (256965099 / 1000000000) (2569651 / 10000000) (Real.log (1293 / 1000)) := by
  have h := reflection_log_9553_neg
  have he : Real.log (1293 / 1000) = -Real.log (1000 / 1293) := by
    rw [show ((1293 / 1000) : ℝ) = ((1000 / 1293) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9554_neg : (346724613 / 1000000000) ≤ -Real.log (707 / 1000) ∧
    -Real.log (707 / 1000) ≤ (173362307 / 500000000) := by
  have h := checkLog_sound (w := (293 / 1707)) (n := 12)
    (lo := (346724613 / 1000000000)) (hi := (173362307 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 707) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 707) = 1/(707 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9554 : Bounds (-173362307 / 500000000) (-346724613 / 1000000000) (Real.log (707 / 1000)) := by
  have h := reflection_log_9554_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9555_neg : (292957 / 1000000000) ≤ -Real.log (1000000 / 1000293) ∧
    -Real.log (1000000 / 1000293) ≤ (146479 / 500000000) := by
  have h := checkLog_sound (w := (293 / 2000293)) (n := 12)
    (lo := (292957 / 1000000000)) (hi := (146479 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000293 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000293 / 1000000) = 1/(1000000 / 1000293) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9555 : Bounds (292957 / 1000000000) (146479 / 500000000) (Real.log (1000293 / 1000000)) := by
  have h := reflection_log_9555_neg
  have he : Real.log (1000293 / 1000000) = -Real.log (1000000 / 1000293) := by
    rw [show ((1000293 / 1000000) : ℝ) = ((1000000 / 1000293) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9556_neg : (146521 / 500000000) ≤ -Real.log (999707 / 1000000) ∧
    -Real.log (999707 / 1000000) ≤ (293043 / 1000000000) := by
  have h := checkLog_sound (w := (293 / 1999707)) (n := 12)
    (lo := (146521 / 500000000)) (hi := (293043 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999707) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999707) = 1/(999707 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9556 : Bounds (-293043 / 1000000000) (-146521 / 500000000) (Real.log (999707 / 1000000)) := by
  have h := reflection_log_9556_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9557_neg : (27677591 / 200000000) ≤ -Real.log (1000000 / 1148421) ∧
    -Real.log (1000000 / 1148421) ≤ (34596989 / 250000000) := by
  have h := checkLog_sound (w := (148421 / 2148421)) (n := 12)
    (lo := (27677591 / 200000000)) (hi := (34596989 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1148421 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1148421 / 1000000) = 1/(1000000 / 1148421) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9557 : Bounds (27677591 / 200000000) (34596989 / 250000000) (Real.log (1148421 / 1000000)) := by
  have h := reflection_log_9557_neg
  have he : Real.log (1148421 / 1000000) = -Real.log (1000000 / 1148421) := by
    rw [show ((1148421 / 1000000) : ℝ) = ((1000000 / 1148421) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9558_neg : (32132601 / 200000000) ≤ -Real.log (851579 / 1000000) ∧
    -Real.log (851579 / 1000000) ≤ (80331503 / 500000000) := by
  have h := checkLog_sound (w := (148421 / 1851579)) (n := 12)
    (lo := (32132601 / 200000000)) (hi := (80331503 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 851579) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 851579) = 1/(851579 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9558 : Bounds (-80331503 / 500000000) (-32132601 / 200000000) (Real.log (851579 / 1000000)) := by
  have h := reflection_log_9558_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9559_neg : (138867629 / 1000000000) ≤ -Real.log (250000 / 287243) ∧
    -Real.log (250000 / 287243) ≤ (13886763 / 100000000) := by
  have h := checkLog_sound (w := (37243 / 537243)) (n := 12)
    (lo := (138867629 / 1000000000)) (hi := (13886763 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((287243 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(287243 / 250000) = 1/(250000 / 287243) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9559 : Bounds (138867629 / 1000000000) (13886763 / 100000000) (Real.log (287243 / 250000)) := by
  have h := reflection_log_9559_neg
  have he : Real.log (287243 / 250000) = -Real.log (250000 / 287243) := by
    rw [show ((287243 / 250000) : ℝ) = ((250000 / 287243) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9560_neg : (20163781 / 125000000) ≤ -Real.log (212757 / 250000) ∧
    -Real.log (212757 / 250000) ≤ (161310249 / 1000000000) := by
  have h := checkLog_sound (w := (37243 / 462757)) (n := 12)
    (lo := (20163781 / 125000000)) (hi := (161310249 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 212757) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 212757) = 1/(212757 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9560 : Bounds (-161310249 / 1000000000) (-20163781 / 125000000) (Real.log (212757 / 250000)) := by
  have h := reflection_log_9560_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9561_neg : (11221309 / 500000000) ≤ -Real.log (61112958951 / 62500000000) ∧
    -Real.log (61112958951 / 62500000000) ≤ (22442619 / 1000000000) := by
  have h := checkLog_sound (w := (1387041049 / 123612958951)) (n := 12)
    (lo := (11221309 / 500000000)) (hi := (22442619 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 61112958951) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 61112958951) = 1/(61112958951 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9561 : Bounds (-22442619 / 1000000000) (-11221309 / 500000000) (Real.log (61112958951 / 62500000000)) := by
  have h := reflection_log_9561_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9562_neg : (445501 / 20000000) ≤ -Real.log (977971206759 / 1000000000000) ∧
    -Real.log (977971206759 / 1000000000000) ≤ (22275051 / 1000000000) := by
  have h := checkLog_sound (w := (22028793241 / 1977971206759)) (n := 12)
    (lo := (445501 / 20000000)) (hi := (22275051 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 977971206759) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 977971206759) = 1/(977971206759 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9562 : Bounds (-22275051 / 1000000000) (-445501 / 20000000) (Real.log (977971206759 / 1000000000000)) := by
  have h := reflection_log_9562_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9563_neg : (299050961 / 1000000000) ≤ -Real.log (250000000000 / 337144586703) ∧
    -Real.log (250000000000 / 337144586703) ≤ (149525481 / 500000000) := by
  have h := checkLog_sound (w := (87144586703 / 587144586703)) (n := 12)
    (lo := (299050961 / 1000000000)) (hi := (149525481 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((337144586703 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(337144586703 / 250000000000) = 1/(250000000000 / 337144586703) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9563 : Bounds (299050961 / 1000000000) (149525481 / 500000000) (Real.log (337144586703 / 250000000000)) := by
  have h := reflection_log_9563_neg
  have he : Real.log (337144586703 / 250000000000) = -Real.log (250000000000 / 337144586703) := by
    rw [show ((337144586703 / 250000000000) : ℝ) = ((250000000000 / 337144586703) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9564_neg : (150088939 / 500000000) ≤ -Real.log (500000000000 / 675049469583) ∧
    -Real.log (500000000000 / 675049469583) ≤ (300177879 / 1000000000) := by
  have h := checkLog_sound (w := (175049469583 / 1175049469583)) (n := 12)
    (lo := (150088939 / 500000000)) (hi := (300177879 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((675049469583 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(675049469583 / 500000000000) = 1/(500000000000 / 675049469583) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9564 : Bounds (150088939 / 500000000) (300177879 / 1000000000) (Real.log (675049469583 / 500000000000)) := by
  have h := reflection_log_9564_neg
  have he : Real.log (675049469583 / 500000000000) = -Real.log (500000000000 / 675049469583) := by
    rw [show ((675049469583 / 500000000000) : ℝ) = ((500000000000 / 675049469583) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9565_neg : (75324497 / 125000000) ≤ -Real.log (500000000000 / 913427561837) ∧
    -Real.log (500000000000 / 913427561837) ≤ (602595977 / 1000000000) := by
  have h := checkLog_sound (w := (413427561837 / 1413427561837)) (n := 12)
    (lo := (75324497 / 125000000)) (hi := (602595977 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((913427561837 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(913427561837 / 500000000000) = 1/(500000000000 / 913427561837) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9565 : Bounds (75324497 / 125000000) (602595977 / 1000000000) (Real.log (913427561837 / 500000000000)) := by
  have h := reflection_log_9565_neg
  have he : Real.log (913427561837 / 500000000000) = -Real.log (500000000000 / 913427561837) := by
    rw [show ((913427561837 / 500000000000) : ℝ) = ((500000000000 / 913427561837) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9566_neg : (37730607 / 62500000) ≤ -Real.log (250000000000 / 457213578501) ∧
    -Real.log (250000000000 / 457213578501) ≤ (603689713 / 1000000000) := by
  have h := checkLog_sound (w := (207213578501 / 707213578501)) (n := 12)
    (lo := (37730607 / 62500000)) (hi := (603689713 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((457213578501 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(457213578501 / 250000000000) = 1/(250000000000 / 457213578501) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9566 : Bounds (37730607 / 62500000) (603689713 / 1000000000) (Real.log (457213578501 / 250000000000)) := by
  have h := reflection_log_9566_neg
  have he : Real.log (457213578501 / 250000000000) = -Real.log (250000000000 / 457213578501) := by
    rw [show ((457213578501 / 250000000000) : ℝ) = ((250000000000 / 457213578501) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9567_neg : (128675861 / 500000000) ≤ -Real.log (2000 / 2587) ∧
    -Real.log (2000 / 2587) ≤ (257351723 / 1000000000) := by
  have h := checkLog_sound (w := (587 / 4587)) (n := 12)
    (lo := (128675861 / 500000000)) (hi := (257351723 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2587 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2587 / 2000) = 1/(2000 / 2587) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9567 : Bounds (128675861 / 500000000) (257351723 / 1000000000) (Real.log (2587 / 2000)) := by
  have h := reflection_log_9567_neg
  have he : Real.log (2587 / 2000) = -Real.log (2000 / 2587) := by
    rw [show ((2587 / 2000) : ℝ) = ((2000 / 2587) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9568_neg : (86858019 / 250000000) ≤ -Real.log (1413 / 2000) ∧
    -Real.log (1413 / 2000) ≤ (347432077 / 1000000000) := by
  have h := checkLog_sound (w := (587 / 3413)) (n := 12)
    (lo := (86858019 / 250000000)) (hi := (347432077 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1413) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1413) = 1/(1413 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9568 : Bounds (-347432077 / 1000000000) (-86858019 / 250000000) (Real.log (1413 / 2000)) := by
  have h := reflection_log_9568_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9569_neg : (18341 / 62500000) ≤ -Real.log (2000000 / 2000587) ∧
    -Real.log (2000000 / 2000587) ≤ (293457 / 1000000000) := by
  have h := checkLog_sound (w := (587 / 4000587)) (n := 12)
    (lo := (18341 / 62500000)) (hi := (293457 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000587 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000587 / 2000000) = 1/(2000000 / 2000587) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9569 : Bounds (18341 / 62500000) (293457 / 1000000000) (Real.log (2000587 / 2000000)) := by
  have h := reflection_log_9569_neg
  have he : Real.log (2000587 / 2000000) = -Real.log (2000000 / 2000587) := by
    rw [show ((2000587 / 2000000) : ℝ) = ((2000000 / 2000587) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9570_neg : (293543 / 1000000000) ≤ -Real.log (1999413 / 2000000) ∧
    -Real.log (1999413 / 2000000) ≤ (36693 / 125000000) := by
  have h := checkLog_sound (w := (587 / 3999413)) (n := 12)
    (lo := (293543 / 1000000000)) (hi := (36693 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999413) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999413) = 1/(1999413 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9570 : Bounds (-36693 / 125000000) (-293543 / 1000000000) (Real.log (1999413 / 2000000)) := by
  have h := reflection_log_9570_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9571_neg : (69307599 / 500000000) ≤ -Real.log (500000 / 574341) ∧
    -Real.log (500000 / 574341) ≤ (138615199 / 1000000000) := by
  have h := checkLog_sound (w := (74341 / 1074341)) (n := 12)
    (lo := (69307599 / 500000000)) (hi := (138615199 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((574341 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(574341 / 500000) = 1/(500000 / 574341) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9571 : Bounds (69307599 / 500000000) (138615199 / 1000000000) (Real.log (574341 / 500000)) := by
  have h := reflection_log_9571_neg
  have he : Real.log (574341 / 500000) = -Real.log (500000 / 574341) := by
    rw [show ((574341 / 500000) : ℝ) = ((500000 / 574341) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9572_neg : (80484771 / 500000000) ≤ -Real.log (425659 / 500000) ∧
    -Real.log (425659 / 500000) ≤ (160969543 / 1000000000) := by
  have h := checkLog_sound (w := (74341 / 925659)) (n := 12)
    (lo := (80484771 / 500000000)) (hi := (160969543 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 425659) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 425659) = 1/(425659 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9572 : Bounds (-160969543 / 1000000000) (-80484771 / 500000000) (Real.log (425659 / 500000)) := by
  have h := reflection_log_9572_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9573_neg : (139095633 / 1000000000) ≤ -Real.log (500000 / 574617) ∧
    -Real.log (500000 / 574617) ≤ (69547817 / 500000000) := by
  have h := checkLog_sound (w := (74617 / 1074617)) (n := 12)
    (lo := (139095633 / 1000000000)) (hi := (69547817 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((574617 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(574617 / 500000) = 1/(500000 / 574617) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9573 : Bounds (139095633 / 1000000000) (69547817 / 500000000) (Real.log (574617 / 500000)) := by
  have h := reflection_log_9573_neg
  have he : Real.log (574617 / 500000) = -Real.log (500000 / 574617) := by
    rw [show ((574617 / 500000) : ℝ) = ((500000 / 574617) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9574_neg : (80809079 / 500000000) ≤ -Real.log (425383 / 500000) ∧
    -Real.log (425383 / 500000) ≤ (161618159 / 1000000000) := by
  have h := checkLog_sound (w := (74617 / 925383)) (n := 12)
    (lo := (80809079 / 500000000)) (hi := (161618159 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 425383) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 425383) = 1/(425383 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9574 : Bounds (-161618159 / 1000000000) (-80809079 / 500000000) (Real.log (425383 / 500000)) := by
  have h := reflection_log_9574_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9575_neg : (900901 / 40000000) ≤ -Real.log (244432303311 / 250000000000) ∧
    -Real.log (244432303311 / 250000000000) ≤ (11261263 / 500000000) := by
  have h := checkLog_sound (w := (5567696689 / 494432303311)) (n := 12)
    (lo := (900901 / 40000000)) (hi := (11261263 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 244432303311) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 244432303311) = 1/(244432303311 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9575 : Bounds (-11261263 / 500000000) (-900901 / 40000000) (Real.log (244432303311 / 250000000000)) := by
  have h := reflection_log_9575_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9576_neg : (2794293 / 125000000) ≤ -Real.log (244473415719 / 250000000000) ∧
    -Real.log (244473415719 / 250000000000) ≤ (4470869 / 200000000) := by
  have h := checkLog_sound (w := (5526584281 / 494473415719)) (n := 12)
    (lo := (2794293 / 125000000)) (hi := (4470869 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 244473415719) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 244473415719) = 1/(244473415719 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9576 : Bounds (-4470869 / 200000000) (-2794293 / 125000000) (Real.log (244473415719 / 250000000000)) := by
  have h := reflection_log_9576_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9577_neg : (14979237 / 50000000) ≤ -Real.log (500000000000 / 674649191019) ∧
    -Real.log (500000000000 / 674649191019) ≤ (299584741 / 1000000000) := by
  have h := checkLog_sound (w := (174649191019 / 1174649191019)) (n := 12)
    (lo := (14979237 / 50000000)) (hi := (299584741 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((674649191019 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(674649191019 / 500000000000) = 1/(500000000000 / 674649191019) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9577 : Bounds (14979237 / 50000000) (299584741 / 1000000000) (Real.log (674649191019 / 500000000000)) := by
  have h := reflection_log_9577_neg
  have he : Real.log (674649191019 / 500000000000) = -Real.log (500000000000 / 674649191019) := by
    rw [show ((674649191019 / 500000000000) : ℝ) = ((500000000000 / 674649191019) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9578_neg : (4698653 / 15625000) ≤ -Real.log (500000000000 / 675411335197) ∧
    -Real.log (500000000000 / 675411335197) ≤ (300713793 / 1000000000) := by
  have h := checkLog_sound (w := (175411335197 / 1175411335197)) (n := 12)
    (lo := (4698653 / 15625000)) (hi := (300713793 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((675411335197 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(675411335197 / 500000000000) = 1/(500000000000 / 675411335197) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9578 : Bounds (4698653 / 15625000) (300713793 / 1000000000) (Real.log (675411335197 / 500000000000)) := by
  have h := reflection_log_9578_neg
  have he : Real.log (675411335197 / 500000000000) = -Real.log (500000000000 / 675411335197) := by
    rw [show ((675411335197 / 500000000000) : ℝ) = ((500000000000 / 675411335197) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9579_neg : (37730607 / 62500000) ≤ -Real.log (500000000000 / 914427157001) ∧
    -Real.log (500000000000 / 914427157001) ≤ (603689713 / 1000000000) := by
  have h := checkLog_sound (w := (414427157001 / 1414427157001)) (n := 12)
    (lo := (37730607 / 62500000)) (hi := (603689713 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((914427157001 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(914427157001 / 500000000000) = 1/(500000000000 / 914427157001) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9579 : Bounds (37730607 / 62500000) (603689713 / 1000000000) (Real.log (914427157001 / 500000000000)) := by
  have h := reflection_log_9579_neg
  have he : Real.log (914427157001 / 500000000000) = -Real.log (500000000000 / 914427157001) := by
    rw [show ((914427157001 / 500000000000) : ℝ) = ((500000000000 / 914427157001) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9580_neg : (604783799 / 1000000000) ≤ -Real.log (500000000000 / 915428167021) ∧
    -Real.log (500000000000 / 915428167021) ≤ (3023919 / 5000000) := by
  have h := checkLog_sound (w := (415428167021 / 1415428167021)) (n := 12)
    (lo := (604783799 / 1000000000)) (hi := (3023919 / 5000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((915428167021 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(915428167021 / 500000000000) = 1/(500000000000 / 915428167021) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9580 : Bounds (604783799 / 1000000000) (3023919 / 5000000) (Real.log (915428167021 / 500000000000)) := by
  have h := reflection_log_9580_neg
  have he : Real.log (915428167021 / 500000000000) = -Real.log (500000000000 / 915428167021) := by
    rw [show ((915428167021 / 500000000000) : ℝ) = ((500000000000 / 915428167021) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9581_neg : (64434549 / 250000000) ≤ -Real.log (500 / 647) ∧
    -Real.log (500 / 647) ≤ (257738197 / 1000000000) := by
  have h := checkLog_sound (w := (147 / 1147)) (n := 12)
    (lo := (64434549 / 250000000)) (hi := (257738197 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((647 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(647 / 500) = 1/(500 / 647) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9581 : Bounds (64434549 / 250000000) (257738197 / 1000000000) (Real.log (647 / 500)) := by
  have h := reflection_log_9581_neg
  have he : Real.log (647 / 500) = -Real.log (500 / 647) := by
    rw [show ((647 / 500) : ℝ) = ((500 / 647) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9582_neg : (348140041 / 1000000000) ≤ -Real.log (353 / 500) ∧
    -Real.log (353 / 500) ≤ (174070021 / 500000000) := by
  have h := checkLog_sound (w := (147 / 853)) (n := 12)
    (lo := (348140041 / 1000000000)) (hi := (174070021 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 353) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500 / 353) = 1/(353 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9582 : Bounds (-174070021 / 500000000) (-348140041 / 1000000000) (Real.log (353 / 500)) := by
  have h := reflection_log_9582_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9583_neg : (73489 / 250000000) ≤ -Real.log (500000 / 500147) ∧
    -Real.log (500000 / 500147) ≤ (293957 / 1000000000) := by
  have h := checkLog_sound (w := (147 / 1000147)) (n := 12)
    (lo := (73489 / 250000000)) (hi := (293957 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500147 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500147 / 500000) = 1/(500000 / 500147) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9583 : Bounds (73489 / 250000000) (293957 / 1000000000) (Real.log (500147 / 500000)) := by
  have h := reflection_log_9583_neg
  have he : Real.log (500147 / 500000) = -Real.log (500000 / 500147) := by
    rw [show ((500147 / 500000) : ℝ) = ((500000 / 500147) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9584_neg : (294043 / 1000000000) ≤ -Real.log (499853 / 500000) ∧
    -Real.log (499853 / 500000) ≤ (73511 / 250000000) := by
  have h := checkLog_sound (w := (147 / 999853)) (n := 12)
    (lo := (294043 / 1000000000)) (hi := (73511 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499853) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499853) = 1/(499853 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9584 : Bounds (-73511 / 250000000) (-294043 / 1000000000) (Real.log (499853 / 500000)) := by
  have h := reflection_log_9584_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9585_neg : (138843259 / 1000000000) ≤ -Real.log (62500 / 71809) ∧
    -Real.log (62500 / 71809) ≤ (6942163 / 50000000) := by
  have h := checkLog_sound (w := (9309 / 134309)) (n := 12)
    (lo := (138843259 / 1000000000)) (hi := (6942163 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((71809 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(71809 / 62500) = 1/(62500 / 71809) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9585 : Bounds (138843259 / 1000000000) (6942163 / 50000000) (Real.log (71809 / 62500)) := by
  have h := reflection_log_9585_neg
  have he : Real.log (71809 / 62500) = -Real.log (62500 / 71809) := by
    rw [show ((71809 / 62500) : ℝ) = ((62500 / 71809) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9586_neg : (161277347 / 1000000000) ≤ -Real.log (53191 / 62500) ∧
    -Real.log (53191 / 62500) ≤ (40319337 / 250000000) := by
  have h := checkLog_sound (w := (9309 / 115691)) (n := 12)
    (lo := (161277347 / 1000000000)) (hi := (40319337 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 53191) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 53191) = 1/(53191 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9586 : Bounds (-40319337 / 250000000) (-161277347 / 1000000000) (Real.log (53191 / 62500)) := by
  have h := reflection_log_9586_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9587_neg : (27864891 / 200000000) ≤ -Real.log (1000000 / 1149497) ∧
    -Real.log (1000000 / 1149497) ≤ (17415557 / 125000000) := by
  have h := checkLog_sound (w := (149497 / 2149497)) (n := 12)
    (lo := (27864891 / 200000000)) (hi := (17415557 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1149497 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1149497 / 1000000) = 1/(1000000 / 1149497) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9587 : Bounds (27864891 / 200000000) (17415557 / 125000000) (Real.log (1149497 / 1000000)) := by
  have h := reflection_log_9587_neg
  have he : Real.log (1149497 / 1000000) = -Real.log (1000000 / 1149497) := by
    rw [show ((1149497 / 1000000) : ℝ) = ((1000000 / 1149497) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9588_neg : (161927339 / 1000000000) ≤ -Real.log (850503 / 1000000) ∧
    -Real.log (850503 / 1000000) ≤ (8096367 / 50000000) := by
  have h := checkLog_sound (w := (149497 / 1850503)) (n := 12)
    (lo := (161927339 / 1000000000)) (hi := (8096367 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 850503) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 850503) = 1/(850503 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9588 : Bounds (-8096367 / 50000000) (-161927339 / 1000000000) (Real.log (850503 / 1000000)) := by
  have h := reflection_log_9588_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9589_neg : (5650721 / 250000000) ≤ -Real.log (977650646991 / 1000000000000) ∧
    -Real.log (977650646991 / 1000000000000) ≤ (4520577 / 200000000) := by
  have h := checkLog_sound (w := (22349353009 / 1977650646991)) (n := 12)
    (lo := (5650721 / 250000000)) (hi := (4520577 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 977650646991) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 977650646991) = 1/(977650646991 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9589 : Bounds (-4520577 / 200000000) (-5650721 / 250000000) (Real.log (977650646991 / 1000000000000)) := by
  have h := reflection_log_9589_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9590_neg : (22434087 / 1000000000) ≤ -Real.log (3819592519 / 3906250000) ∧
    -Real.log (3819592519 / 3906250000) ≤ (2804261 / 125000000) := by
  have h := checkLog_sound (w := (86657481 / 7725842519)) (n := 12)
    (lo := (22434087 / 1000000000)) (hi := (2804261 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3906250000 / 3819592519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3906250000 / 3819592519) = 1/(3819592519 / 3906250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9590 : Bounds (-2804261 / 125000000) (-22434087 / 1000000000) (Real.log (3819592519 / 3906250000)) := by
  have h := reflection_log_9590_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9591_neg : (300120607 / 1000000000) ≤ -Real.log (500000000000 / 675010810099) ∧
    -Real.log (500000000000 / 675010810099) ≤ (9378769 / 31250000) := by
  have h := checkLog_sound (w := (175010810099 / 1175010810099)) (n := 12)
    (lo := (300120607 / 1000000000)) (hi := (9378769 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((675010810099 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(675010810099 / 500000000000) = 1/(500000000000 / 675010810099) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9591 : Bounds (300120607 / 1000000000) (9378769 / 31250000) (Real.log (675010810099 / 500000000000)) := by
  have h := reflection_log_9591_neg
  have he : Real.log (675010810099 / 500000000000) = -Real.log (500000000000 / 675010810099) := by
    rw [show ((675010810099 / 500000000000) : ℝ) = ((500000000000 / 675010810099) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9592_neg : (60250359 / 200000000) ≤ -Real.log (500000000000 / 675774806203) ∧
    -Real.log (500000000000 / 675774806203) ≤ (75312949 / 250000000) := by
  have h := checkLog_sound (w := (175774806203 / 1175774806203)) (n := 12)
    (lo := (60250359 / 200000000)) (hi := (75312949 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((675774806203 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(675774806203 / 500000000000) = 1/(500000000000 / 675774806203) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9592 : Bounds (60250359 / 200000000) (75312949 / 250000000) (Real.log (675774806203 / 500000000000)) := by
  have h := reflection_log_9592_neg
  have he : Real.log (675774806203 / 500000000000) = -Real.log (500000000000 / 675774806203) := by
    rw [show ((675774806203 / 500000000000) : ℝ) = ((500000000000 / 675774806203) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9593_neg : (604783799 / 1000000000) ≤ -Real.log (25000000000 / 45771408351) ∧
    -Real.log (25000000000 / 45771408351) ≤ (3023919 / 5000000) := by
  have h := checkLog_sound (w := (20771408351 / 70771408351)) (n := 12)
    (lo := (604783799 / 1000000000)) (hi := (3023919 / 5000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((45771408351 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(45771408351 / 25000000000) = 1/(25000000000 / 45771408351) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9593 : Bounds (604783799 / 1000000000) (3023919 / 5000000) (Real.log (45771408351 / 25000000000)) := by
  have h := reflection_log_9593_neg
  have he : Real.log (45771408351 / 25000000000) = -Real.log (25000000000 / 45771408351) := by
    rw [show ((45771408351 / 25000000000) : ℝ) = ((25000000000 / 45771408351) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9594_neg : (605878237 / 1000000000) ≤ -Real.log (500000000000 / 916430594901) ∧
    -Real.log (500000000000 / 916430594901) ≤ (302939119 / 500000000) := by
  have h := checkLog_sound (w := (416430594901 / 1416430594901)) (n := 12)
    (lo := (605878237 / 1000000000)) (hi := (302939119 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((916430594901 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(916430594901 / 500000000000) = 1/(500000000000 / 916430594901) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9594 : Bounds (605878237 / 1000000000) (302939119 / 500000000) (Real.log (916430594901 / 500000000000)) := by
  have h := reflection_log_9594_neg
  have he : Real.log (916430594901 / 500000000000) = -Real.log (500000000000 / 916430594901) := by
    rw [show ((916430594901 / 500000000000) : ℝ) = ((500000000000 / 916430594901) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9595_neg : (6453113 / 25000000) ≤ -Real.log (2000 / 2589) ∧
    -Real.log (2000 / 2589) ≤ (258124521 / 1000000000) := by
  have h := checkLog_sound (w := (589 / 4589)) (n := 12)
    (lo := (6453113 / 25000000)) (hi := (258124521 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2589 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2589 / 2000) = 1/(2000 / 2589) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9595 : Bounds (6453113 / 25000000) (258124521 / 1000000000) (Real.log (2589 / 2000)) := by
  have h := reflection_log_9595_neg
  have he : Real.log (2589 / 2000) = -Real.log (2000 / 2589) := by
    rw [show ((2589 / 2000) : ℝ) = ((2000 / 2589) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9596_neg : (348848507 / 1000000000) ≤ -Real.log (1411 / 2000) ∧
    -Real.log (1411 / 2000) ≤ (87212127 / 250000000) := by
  have h := checkLog_sound (w := (589 / 3411)) (n := 12)
    (lo := (348848507 / 1000000000)) (hi := (87212127 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1411) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1411) = 1/(1411 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9596 : Bounds (-87212127 / 250000000) (-348848507 / 1000000000) (Real.log (1411 / 2000)) := by
  have h := reflection_log_9596_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9597_neg : (36807 / 125000000) ≤ -Real.log (2000000 / 2000589) ∧
    -Real.log (2000000 / 2000589) ≤ (294457 / 1000000000) := by
  have h := checkLog_sound (w := (589 / 4000589)) (n := 12)
    (lo := (36807 / 125000000)) (hi := (294457 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000589 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000589 / 2000000) = 1/(2000000 / 2000589) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9597 : Bounds (36807 / 125000000) (294457 / 1000000000) (Real.log (2000589 / 2000000)) := by
  have h := reflection_log_9597_neg
  have he : Real.log (2000589 / 2000000) = -Real.log (2000000 / 2000589) := by
    rw [show ((2000589 / 2000000) : ℝ) = ((2000000 / 2000589) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9598_neg : (294543 / 1000000000) ≤ -Real.log (1999411 / 2000000) ∧
    -Real.log (1999411 / 2000000) ≤ (18409 / 62500000) := by
  have h := checkLog_sound (w := (589 / 3999411)) (n := 12)
    (lo := (294543 / 1000000000)) (hi := (18409 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999411) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999411) = 1/(1999411 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9598 : Bounds (-18409 / 62500000) (-294543 / 1000000000) (Real.log (1999411 / 2000000)) := by
  have h := reflection_log_9598_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9599_neg : (139071269 / 1000000000) ≤ -Real.log (500000 / 574603) ∧
    -Real.log (500000 / 574603) ≤ (13907127 / 100000000) := by
  have h := checkLog_sound (w := (74603 / 1074603)) (n := 12)
    (lo := (139071269 / 1000000000)) (hi := (13907127 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((574603 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(574603 / 500000) = 1/(500000 / 574603) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9599 : Bounds (139071269 / 1000000000) (13907127 / 100000000) (Real.log (574603 / 500000)) := by
  have h := reflection_log_9599_neg
  have he : Real.log (574603 / 500000) = -Real.log (500000 / 574603) := by
    rw [show ((574603 / 500000) : ℝ) = ((500000 / 574603) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily
