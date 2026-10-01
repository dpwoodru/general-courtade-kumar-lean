import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_640_neg : (19492907 / 125000000) ≤ -Real.log (500000000000 / 584379940707) ∧
    -Real.log (500000000000 / 584379940707) ≤ (155943257 / 1000000000) := by
  have h := checkLog_sound (w := (84379940707 / 1084379940707)) (n := 12)
    (lo := (19492907 / 125000000)) (hi := (155943257 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((584379940707 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(584379940707 / 500000000000) = 1/(500000000000 / 584379940707) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_640 : Bounds (19492907 / 125000000) (155943257 / 1000000000) (Real.log (584379940707 / 500000000000)) := by
  have h := reflection_log_640_neg
  have he : Real.log (584379940707 / 500000000000) = -Real.log (500000000000 / 584379940707) := by
    rw [show ((584379940707 / 500000000000) : ℝ) = ((500000000000 / 584379940707) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_641_neg : (62380851 / 200000000) ≤ -Real.log (25000000000 / 34150597421) ∧
    -Real.log (25000000000 / 34150597421) ≤ (609188 / 1953125) := by
  have h := checkLog_sound (w := (9150597421 / 59150597421)) (n := 12)
    (lo := (62380851 / 200000000)) (hi := (609188 / 1953125))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((34150597421 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(34150597421 / 25000000000) = 1/(25000000000 / 34150597421) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_641 : Bounds (62380851 / 200000000) (609188 / 1953125) (Real.log (34150597421 / 25000000000)) := by
  have h := reflection_log_641_neg
  have he : Real.log (34150597421 / 25000000000) = -Real.log (25000000000 / 34150597421) := by
    rw [show ((34150597421 / 25000000000) : ℝ) = ((25000000000 / 34150597421) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_642_neg : (156054581 / 500000000) ≤ -Real.log (500000000000 / 683151916707) ∧
    -Real.log (500000000000 / 683151916707) ≤ (312109163 / 1000000000) := by
  have h := checkLog_sound (w := (183151916707 / 1183151916707)) (n := 12)
    (lo := (156054581 / 500000000)) (hi := (312109163 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((683151916707 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(683151916707 / 500000000000) = 1/(500000000000 / 683151916707) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_642 : Bounds (156054581 / 500000000) (312109163 / 1000000000) (Real.log (683151916707 / 500000000000)) := by
  have h := reflection_log_642_neg
  have he : Real.log (683151916707 / 500000000000) = -Real.log (500000000000 / 683151916707) := by
    rw [show ((683151916707 / 500000000000) : ℝ) = ((500000000000 / 683151916707) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_643_neg : (450043 / 3125000) ≤ -Real.log (10000 / 11549) ∧
    -Real.log (10000 / 11549) ≤ (144013761 / 1000000000) := by
  have h := checkLog_sound (w := (1549 / 21549)) (n := 12)
    (lo := (450043 / 3125000)) (hi := (144013761 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11549 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11549 / 10000) = 1/(10000 / 11549) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_643 : Bounds (450043 / 3125000) (144013761 / 1000000000) (Real.log (11549 / 10000)) := by
  have h := reflection_log_643_neg
  have he : Real.log (11549 / 10000) = -Real.log (10000 / 11549) := by
    rw [show ((11549 / 10000) : ℝ) = ((10000 / 11549) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_644_neg : (33660063 / 200000000) ≤ -Real.log (8451 / 10000) ∧
    -Real.log (8451 / 10000) ≤ (42075079 / 250000000) := by
  have h := checkLog_sound (w := (1549 / 18451)) (n := 12)
    (lo := (33660063 / 200000000)) (hi := (42075079 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8451) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8451) = 1/(8451 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_644 : Bounds (-42075079 / 250000000) (-33660063 / 200000000) (Real.log (8451 / 10000)) := by
  have h := reflection_log_644_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_645_neg : (19361 / 125000000) ≤ -Real.log (10000000 / 10001549) ∧
    -Real.log (10000000 / 10001549) ≤ (154889 / 1000000000) := by
  have h := checkLog_sound (w := (1549 / 20001549)) (n := 12)
    (lo := (19361 / 125000000)) (hi := (154889 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001549 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001549 / 10000000) = 1/(10000000 / 10001549) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_645 : Bounds (19361 / 125000000) (154889 / 1000000000) (Real.log (10001549 / 10000000)) := by
  have h := reflection_log_645_neg
  have he : Real.log (10001549 / 10000000) = -Real.log (10000000 / 10001549) := by
    rw [show ((10001549 / 10000000) : ℝ) = ((10000000 / 10001549) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_646_neg : (154911 / 1000000000) ≤ -Real.log (9998451 / 10000000) ∧
    -Real.log (9998451 / 10000000) ≤ (4841 / 31250000) := by
  have h := checkLog_sound (w := (1549 / 19998451)) (n := 12)
    (lo := (154911 / 1000000000)) (hi := (4841 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998451) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998451) = 1/(9998451 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_646 : Bounds (-4841 / 31250000) (-154911 / 1000000000) (Real.log (9998451 / 10000000)) := by
  have h := reflection_log_646_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_647_neg : (14958219 / 200000000) ≤ -Real.log (1000000 / 1077659) ∧
    -Real.log (1000000 / 1077659) ≤ (9348887 / 125000000) := by
  have h := checkLog_sound (w := (77659 / 2077659)) (n := 12)
    (lo := (14958219 / 200000000)) (hi := (9348887 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1077659 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1077659 / 1000000) = 1/(1000000 / 1077659) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_647 : Bounds (14958219 / 200000000) (9348887 / 125000000) (Real.log (1077659 / 1000000)) := by
  have h := reflection_log_647_neg
  have he : Real.log (1077659 / 1000000) = -Real.log (1000000 / 1077659) := by
    rw [show ((1077659 / 1000000) : ℝ) = ((1000000 / 1077659) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_648_neg : (3233611 / 40000000) ≤ -Real.log (922341 / 1000000) ∧
    -Real.log (922341 / 1000000) ≤ (20210069 / 250000000) := by
  have h := checkLog_sound (w := (77659 / 1922341)) (n := 12)
    (lo := (3233611 / 40000000)) (hi := (20210069 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 922341) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 922341) = 1/(922341 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_648 : Bounds (-20210069 / 250000000) (-3233611 / 40000000) (Real.log (922341 / 1000000)) := by
  have h := reflection_log_648_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_649_neg : (9372779 / 125000000) ≤ -Real.log (200000 / 215573) ∧
    -Real.log (200000 / 215573) ≤ (74982233 / 1000000000) := by
  have h := checkLog_sound (w := (15573 / 415573)) (n := 12)
    (lo := (9372779 / 125000000)) (hi := (74982233 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((215573 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(215573 / 200000) = 1/(200000 / 215573) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_649 : Bounds (9372779 / 125000000) (74982233 / 1000000000) (Real.log (215573 / 200000)) := by
  have h := reflection_log_649_neg
  have he : Real.log (215573 / 200000) = -Real.log (200000 / 215573) := by
    rw [show ((215573 / 200000) : ℝ) = ((200000 / 215573) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_650_neg : (16212729 / 200000000) ≤ -Real.log (184427 / 200000) ∧
    -Real.log (184427 / 200000) ≤ (40531823 / 500000000) := by
  have h := checkLog_sound (w := (15573 / 384427)) (n := 12)
    (lo := (16212729 / 200000000)) (hi := (40531823 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 184427) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 184427) = 1/(184427 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_650 : Bounds (-40531823 / 500000000) (-16212729 / 200000000) (Real.log (184427 / 200000)) := by
  have h := reflection_log_650_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_651_neg : (1520353 / 250000000) ≤ -Real.log (39757481671 / 40000000000) ∧
    -Real.log (39757481671 / 40000000000) ≤ (6081413 / 1000000000) := by
  have h := checkLog_sound (w := (242518329 / 79757481671)) (n := 12)
    (lo := (1520353 / 250000000)) (hi := (6081413 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39757481671) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39757481671) = 1/(39757481671 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_651 : Bounds (-6081413 / 1000000000) (-1520353 / 250000000) (Real.log (39757481671 / 40000000000)) := by
  have h := reflection_log_651_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_652_neg : (6049179 / 1000000000) ≤ -Real.log (993969079719 / 1000000000000) ∧
    -Real.log (993969079719 / 1000000000000) ≤ (302459 / 50000000) := by
  have h := checkLog_sound (w := (6030920281 / 1993969079719)) (n := 12)
    (lo := (6049179 / 1000000000)) (hi := (302459 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993969079719) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993969079719) = 1/(993969079719 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_652 : Bounds (-302459 / 50000000) (-6049179 / 1000000000) (Real.log (993969079719 / 1000000000000)) := by
  have h := reflection_log_652_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_653_neg : (155631371 / 1000000000) ≤ -Real.log (500000000000 / 584197709957) ∧
    -Real.log (500000000000 / 584197709957) ≤ (38907843 / 250000000) := by
  have h := checkLog_sound (w := (84197709957 / 1084197709957)) (n := 12)
    (lo := (155631371 / 1000000000)) (hi := (38907843 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((584197709957 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(584197709957 / 500000000000) = 1/(500000000000 / 584197709957) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_653 : Bounds (155631371 / 1000000000) (38907843 / 250000000) (Real.log (584197709957 / 500000000000)) := by
  have h := reflection_log_653_neg
  have he : Real.log (584197709957 / 500000000000) = -Real.log (500000000000 / 584197709957) := by
    rw [show ((584197709957 / 500000000000) : ℝ) = ((500000000000 / 584197709957) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_654_neg : (78022939 / 500000000) ≤ -Real.log (62500000000 / 73054989237) ∧
    -Real.log (62500000000 / 73054989237) ≤ (156045879 / 1000000000) := by
  have h := checkLog_sound (w := (10554989237 / 135554989237)) (n := 12)
    (lo := (78022939 / 500000000)) (hi := (156045879 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((73054989237 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(73054989237 / 62500000000) = 1/(62500000000 / 73054989237) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_654 : Bounds (78022939 / 500000000) (156045879 / 1000000000) (Real.log (73054989237 / 62500000000)) := by
  have h := reflection_log_654_neg
  have he : Real.log (73054989237 / 62500000000) = -Real.log (62500000000 / 73054989237) := by
    rw [show ((73054989237 / 62500000000) : ℝ) = ((62500000000 / 73054989237) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_655_neg : (156054581 / 500000000) ≤ -Real.log (250000000000 / 341575958353) ∧
    -Real.log (250000000000 / 341575958353) ≤ (312109163 / 1000000000) := by
  have h := checkLog_sound (w := (91575958353 / 591575958353)) (n := 12)
    (lo := (156054581 / 500000000)) (hi := (312109163 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((341575958353 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(341575958353 / 250000000000) = 1/(250000000000 / 341575958353) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_655 : Bounds (156054581 / 500000000) (312109163 / 1000000000) (Real.log (341575958353 / 250000000000)) := by
  have h := reflection_log_655_neg
  have he : Real.log (341575958353 / 250000000000) = -Real.log (250000000000 / 341575958353) := by
    rw [show ((341575958353 / 250000000000) : ℝ) = ((250000000000 / 341575958353) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_656_neg : (12492563 / 40000000) ≤ -Real.log (500000000000 / 683291918117) ∧
    -Real.log (500000000000 / 683291918117) ≤ (78078519 / 250000000) := by
  have h := checkLog_sound (w := (183291918117 / 1183291918117)) (n := 12)
    (lo := (12492563 / 40000000)) (hi := (78078519 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((683291918117 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(683291918117 / 500000000000) = 1/(500000000000 / 683291918117) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_656 : Bounds (12492563 / 40000000) (78078519 / 250000000) (Real.log (683291918117 / 500000000000)) := by
  have h := reflection_log_656_neg
  have he : Real.log (683291918117 / 500000000000) = -Real.log (500000000000 / 683291918117) := by
    rw [show ((683291918117 / 500000000000) : ℝ) = ((500000000000 / 683291918117) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_657_neg : (144100343 / 1000000000) ≤ -Real.log (200 / 231) ∧
    -Real.log (200 / 231) ≤ (18012543 / 125000000) := by
  have h := checkLog_sound (w := (31 / 431)) (n := 12)
    (lo := (144100343 / 1000000000)) (hi := (18012543 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((231 / 200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(231 / 200) = 1/(200 / 231) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_657 : Bounds (144100343 / 1000000000) (18012543 / 125000000) (Real.log (231 / 200)) := by
  have h := reflection_log_657_neg
  have he : Real.log (231 / 200) = -Real.log (200 / 231) := by
    rw [show ((231 / 200) : ℝ) = ((200 / 231) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_658_neg : (168418651 / 1000000000) ≤ -Real.log (169 / 200) ∧
    -Real.log (169 / 200) ≤ (42104663 / 250000000) := by
  have h := checkLog_sound (w := (31 / 369)) (n := 12)
    (lo := (168418651 / 1000000000)) (hi := (42104663 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200 / 169) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200 / 169) = 1/(169 / 200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_658 : Bounds (-42104663 / 250000000) (-168418651 / 1000000000) (Real.log (169 / 200)) := by
  have h := reflection_log_658_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_659_neg : (154987 / 1000000000) ≤ -Real.log (200000 / 200031) ∧
    -Real.log (200000 / 200031) ≤ (38747 / 250000000) := by
  have h := checkLog_sound (w := (31 / 400031)) (n := 12)
    (lo := (154987 / 1000000000)) (hi := (38747 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200031 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200031 / 200000) = 1/(200000 / 200031) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_659 : Bounds (154987 / 1000000000) (38747 / 250000000) (Real.log (200031 / 200000)) := by
  have h := reflection_log_659_neg
  have he : Real.log (200031 / 200000) = -Real.log (200000 / 200031) := by
    rw [show ((200031 / 200000) : ℝ) = ((200000 / 200031) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_660_neg : (38753 / 250000000) ≤ -Real.log (199969 / 200000) ∧
    -Real.log (199969 / 200000) ≤ (155013 / 1000000000) := by
  have h := checkLog_sound (w := (31 / 399969)) (n := 12)
    (lo := (38753 / 250000000)) (hi := (155013 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 199969) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 199969) = 1/(199969 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_660 : Bounds (-155013 / 1000000000) (-38753 / 250000000) (Real.log (199969 / 200000)) := by
  have h := reflection_log_660_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_661_neg : (74838419 / 1000000000) ≤ -Real.log (100000 / 107771) ∧
    -Real.log (100000 / 107771) ≤ (3741921 / 50000000) := by
  have h := checkLog_sound (w := (7771 / 207771)) (n := 12)
    (lo := (74838419 / 1000000000)) (hi := (3741921 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((107771 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(107771 / 100000) = 1/(100000 / 107771) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_661 : Bounds (74838419 / 1000000000) (3741921 / 50000000) (Real.log (107771 / 100000)) := by
  have h := reflection_log_661_neg
  have he : Real.log (107771 / 100000) = -Real.log (100000 / 107771) := by
    rw [show ((107771 / 100000) : ℝ) = ((100000 / 107771) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_662_neg : (80895571 / 1000000000) ≤ -Real.log (92229 / 100000) ∧
    -Real.log (92229 / 100000) ≤ (20223893 / 250000000) := by
  have h := checkLog_sound (w := (7771 / 192229)) (n := 12)
    (lo := (80895571 / 1000000000)) (hi := (20223893 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 92229) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 92229) = 1/(92229 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_662 : Bounds (-20223893 / 250000000) (-80895571 / 1000000000) (Real.log (92229 / 100000)) := by
  have h := reflection_log_662_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_663_neg : (75029547 / 1000000000) ≤ -Real.log (250000 / 269479) ∧
    -Real.log (250000 / 269479) ≤ (18757387 / 250000000) := by
  have h := checkLog_sound (w := (19479 / 519479)) (n := 12)
    (lo := (75029547 / 1000000000)) (hi := (18757387 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((269479 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(269479 / 250000) = 1/(250000 / 269479) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_663 : Bounds (75029547 / 1000000000) (18757387 / 250000000) (Real.log (269479 / 250000)) := by
  have h := reflection_log_663_neg
  have he : Real.log (269479 / 250000) = -Real.log (250000 / 269479) := by
    rw [show ((269479 / 250000) : ℝ) = ((250000 / 269479) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_664_neg : (81118953 / 1000000000) ≤ -Real.log (230521 / 250000) ∧
    -Real.log (230521 / 250000) ≤ (40559477 / 500000000) := by
  have h := checkLog_sound (w := (19479 / 480521)) (n := 12)
    (lo := (81118953 / 1000000000)) (hi := (40559477 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 230521) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 230521) = 1/(230521 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_664 : Bounds (-40559477 / 500000000) (-81118953 / 1000000000) (Real.log (230521 / 250000)) := by
  have h := reflection_log_664_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_665_neg : (1217881 / 200000000) ≤ -Real.log (62120568559 / 62500000000) ∧
    -Real.log (62120568559 / 62500000000) ≤ (3044703 / 500000000) := by
  have h := checkLog_sound (w := (379431441 / 124620568559)) (n := 12)
    (lo := (1217881 / 200000000)) (hi := (3044703 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 62120568559) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 62120568559) = 1/(62120568559 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_665 : Bounds (-3044703 / 500000000) (-1217881 / 200000000) (Real.log (62120568559 / 62500000000)) := by
  have h := reflection_log_665_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_666_neg : (6057151 / 1000000000) ≤ -Real.log (9939611559 / 10000000000) ∧
    -Real.log (9939611559 / 10000000000) ≤ (94643 / 15625000) := by
  have h := checkLog_sound (w := (60388441 / 19939611559)) (n := 12)
    (lo := (6057151 / 1000000000)) (hi := (94643 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 9939611559) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 9939611559) = 1/(9939611559 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_666 : Bounds (-94643 / 15625000) (-6057151 / 1000000000) (Real.log (9939611559 / 10000000000)) := by
  have h := reflection_log_666_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_667_neg : (15573399 / 100000000) ≤ -Real.log (500000000000 / 584257662991) ∧
    -Real.log (500000000000 / 584257662991) ≤ (155733991 / 1000000000) := by
  have h := checkLog_sound (w := (84257662991 / 1084257662991)) (n := 12)
    (lo := (15573399 / 100000000)) (hi := (155733991 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((584257662991 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(584257662991 / 500000000000) = 1/(500000000000 / 584257662991) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_667 : Bounds (15573399 / 100000000) (155733991 / 1000000000) (Real.log (584257662991 / 500000000000)) := by
  have h := reflection_log_667_neg
  have he : Real.log (584257662991 / 500000000000) = -Real.log (500000000000 / 584257662991) := by
    rw [show ((584257662991 / 500000000000) : ℝ) = ((500000000000 / 584257662991) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_668_neg : (312297 / 2000000) ≤ -Real.log (12500000000 / 14612497343) ∧
    -Real.log (12500000000 / 14612497343) ≤ (156148501 / 1000000000) := by
  have h := checkLog_sound (w := (2112497343 / 27112497343)) (n := 12)
    (lo := (312297 / 2000000)) (hi := (156148501 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((14612497343 / 12500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(14612497343 / 12500000000) = 1/(12500000000 / 14612497343) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_668 : Bounds (312297 / 2000000) (156148501 / 1000000000) (Real.log (14612497343 / 12500000000)) := by
  have h := reflection_log_668_neg
  have he : Real.log (14612497343 / 12500000000) = -Real.log (12500000000 / 14612497343) := by
    rw [show ((14612497343 / 12500000000) : ℝ) = ((12500000000 / 14612497343) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_669_neg : (12492563 / 40000000) ≤ -Real.log (125000000000 / 170822979529) ∧
    -Real.log (125000000000 / 170822979529) ≤ (78078519 / 250000000) := by
  have h := checkLog_sound (w := (45822979529 / 295822979529)) (n := 12)
    (lo := (12492563 / 40000000)) (hi := (78078519 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((170822979529 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(170822979529 / 125000000000) = 1/(125000000000 / 170822979529) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_669 : Bounds (12492563 / 40000000) (78078519 / 250000000) (Real.log (170822979529 / 125000000000)) := by
  have h := reflection_log_669_neg
  have he : Real.log (170822979529 / 125000000000) = -Real.log (125000000000 / 170822979529) := by
    rw [show ((170822979529 / 125000000000) : ℝ) = ((125000000000 / 170822979529) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_670_neg : (62503799 / 200000000) ≤ -Real.log (500000000000 / 683431952663) ∧
    -Real.log (500000000000 / 683431952663) ≤ (78129749 / 250000000) := by
  have h := checkLog_sound (w := (183431952663 / 1183431952663)) (n := 12)
    (lo := (62503799 / 200000000)) (hi := (78129749 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((683431952663 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(683431952663 / 500000000000) = 1/(500000000000 / 683431952663) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_670 : Bounds (62503799 / 200000000) (78129749 / 250000000) (Real.log (683431952663 / 500000000000)) := by
  have h := reflection_log_670_neg
  have he : Real.log (683431952663 / 500000000000) = -Real.log (500000000000 / 683431952663) := by
    rw [show ((683431952663 / 500000000000) : ℝ) = ((500000000000 / 683431952663) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_671_neg : (3604673 / 25000000) ≤ -Real.log (10000 / 11551) ∧
    -Real.log (10000 / 11551) ≤ (144186921 / 1000000000) := by
  have h := checkLog_sound (w := (1551 / 21551)) (n := 12)
    (lo := (3604673 / 25000000)) (hi := (144186921 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11551 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11551 / 10000) = 1/(10000 / 11551) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_671 : Bounds (3604673 / 25000000) (144186921 / 1000000000) (Real.log (11551 / 10000)) := by
  have h := reflection_log_671_neg
  have he : Real.log (11551 / 10000) = -Real.log (10000 / 11551) := by
    rw [show ((11551 / 10000) : ℝ) = ((10000 / 11551) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_672_neg : (168537001 / 1000000000) ≤ -Real.log (8449 / 10000) ∧
    -Real.log (8449 / 10000) ≤ (84268501 / 500000000) := by
  have h := checkLog_sound (w := (1551 / 18449)) (n := 12)
    (lo := (168537001 / 1000000000)) (hi := (84268501 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8449) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8449) = 1/(8449 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_672 : Bounds (-84268501 / 500000000) (-168537001 / 1000000000) (Real.log (8449 / 10000)) := by
  have h := reflection_log_672_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_673_neg : (155087 / 1000000000) ≤ -Real.log (10000000 / 10001551) ∧
    -Real.log (10000000 / 10001551) ≤ (9693 / 62500000) := by
  have h := checkLog_sound (w := (1551 / 20001551)) (n := 12)
    (lo := (155087 / 1000000000)) (hi := (9693 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001551 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001551 / 10000000) = 1/(10000000 / 10001551) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_673 : Bounds (155087 / 1000000000) (9693 / 62500000) (Real.log (10001551 / 10000000)) := by
  have h := reflection_log_673_neg
  have he : Real.log (10001551 / 10000000) = -Real.log (10000000 / 10001551) := by
    rw [show ((10001551 / 10000000) : ℝ) = ((10000000 / 10001551) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_674_neg : (19389 / 125000000) ≤ -Real.log (9998449 / 10000000) ∧
    -Real.log (9998449 / 10000000) ≤ (155113 / 1000000000) := by
  have h := checkLog_sound (w := (1551 / 19998449)) (n := 12)
    (lo := (19389 / 125000000)) (hi := (155113 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998449) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998449) = 1/(9998449 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_674 : Bounds (-155113 / 1000000000) (-19389 / 125000000) (Real.log (9998449 / 10000000)) := by
  have h := reflection_log_674_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_675_neg : (74884813 / 1000000000) ≤ -Real.log (3125 / 3368) ∧
    -Real.log (3125 / 3368) ≤ (37442407 / 500000000) := by
  have h := checkLog_sound (w := (243 / 6493)) (n := 12)
    (lo := (74884813 / 1000000000)) (hi := (37442407 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3368 / 3125) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3368 / 3125) = 1/(3125 / 3368) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_675 : Bounds (74884813 / 1000000000) (37442407 / 500000000) (Real.log (3368 / 3125)) := by
  have h := reflection_log_675_neg
  have he : Real.log (3368 / 3125) = -Real.log (3125 / 3368) := by
    rw [show ((3368 / 3125) : ℝ) = ((3125 / 3368) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_676_neg : (16189957 / 200000000) ≤ -Real.log (2882 / 3125) ∧
    -Real.log (2882 / 3125) ≤ (40474893 / 500000000) := by
  have h := checkLog_sound (w := (243 / 6007)) (n := 12)
    (lo := (16189957 / 200000000)) (hi := (40474893 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3125 / 2882) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3125 / 2882) = 1/(2882 / 3125) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_676 : Bounds (-40474893 / 500000000) (-16189957 / 200000000) (Real.log (2882 / 3125)) := by
  have h := reflection_log_676_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_677_neg : (75076859 / 1000000000) ≤ -Real.log (1000000 / 1077967) ∧
    -Real.log (1000000 / 1077967) ≤ (3753843 / 50000000) := by
  have h := checkLog_sound (w := (77967 / 2077967)) (n := 12)
    (lo := (75076859 / 1000000000)) (hi := (3753843 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1077967 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1077967 / 1000000) = 1/(1000000 / 1077967) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_677 : Bounds (75076859 / 1000000000) (3753843 / 50000000) (Real.log (1077967 / 1000000)) := by
  have h := reflection_log_677_neg
  have he : Real.log (1077967 / 1000000) = -Real.log (1000000 / 1077967) := by
    rw [show ((1077967 / 1000000) : ℝ) = ((1000000 / 1077967) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_678_neg : (10146783 / 125000000) ≤ -Real.log (922033 / 1000000) ∧
    -Real.log (922033 / 1000000) ≤ (16234853 / 200000000) := by
  have h := checkLog_sound (w := (77967 / 1922033)) (n := 12)
    (lo := (10146783 / 125000000)) (hi := (16234853 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 922033) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 922033) = 1/(922033 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_678 : Bounds (-16234853 / 200000000) (-10146783 / 125000000) (Real.log (922033 / 1000000)) := by
  have h := reflection_log_678_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_679_neg : (1524351 / 250000000) ≤ -Real.log (993921146911 / 1000000000000) ∧
    -Real.log (993921146911 / 1000000000000) ≤ (1219481 / 200000000) := by
  have h := checkLog_sound (w := (6078853089 / 1993921146911)) (n := 12)
    (lo := (1524351 / 250000000)) (hi := (1219481 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993921146911) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993921146911) = 1/(993921146911 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_679 : Bounds (-1219481 / 200000000) (-1524351 / 250000000) (Real.log (993921146911 / 1000000000000)) := by
  have h := reflection_log_679_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_680_neg : (1516243 / 250000000) ≤ -Real.log (9706576 / 9765625) ∧
    -Real.log (9706576 / 9765625) ≤ (6064973 / 1000000000) := by
  have h := checkLog_sound (w := (59049 / 19472201)) (n := 12)
    (lo := (1516243 / 250000000)) (hi := (6064973 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9765625 / 9706576) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(9765625 / 9706576) = 1/(9706576 / 9765625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_680 : Bounds (-6064973 / 1000000000) (-1516243 / 250000000) (Real.log (9706576 / 9765625)) := by
  have h := reflection_log_680_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_681_neg : (77917299 / 500000000) ≤ -Real.log (500000000000 / 584316446911) ∧
    -Real.log (500000000000 / 584316446911) ≤ (155834599 / 1000000000) := by
  have h := checkLog_sound (w := (84316446911 / 1084316446911)) (n := 12)
    (lo := (77917299 / 500000000)) (hi := (155834599 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((584316446911 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(584316446911 / 500000000000) = 1/(500000000000 / 584316446911) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_681 : Bounds (77917299 / 500000000) (155834599 / 1000000000) (Real.log (584316446911 / 500000000000)) := by
  have h := reflection_log_681_neg
  have he : Real.log (584316446911 / 500000000000) = -Real.log (500000000000 / 584316446911) := by
    rw [show ((584316446911 / 500000000000) : ℝ) = ((500000000000 / 584316446911) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_682_neg : (39062781 / 250000000) ≤ -Real.log (250000000000 / 292279940089) ∧
    -Real.log (250000000000 / 292279940089) ≤ (1250009 / 8000000) := by
  have h := checkLog_sound (w := (42279940089 / 542279940089)) (n := 12)
    (lo := (39062781 / 250000000)) (hi := (1250009 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((292279940089 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(292279940089 / 250000000000) = 1/(250000000000 / 292279940089) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_682 : Bounds (39062781 / 250000000) (1250009 / 8000000) (Real.log (292279940089 / 250000000000)) := by
  have h := reflection_log_682_neg
  have he : Real.log (292279940089 / 250000000000) = -Real.log (250000000000 / 292279940089) := by
    rw [show ((292279940089 / 250000000000) : ℝ) = ((250000000000 / 292279940089) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_683_neg : (62503799 / 200000000) ≤ -Real.log (250000000000 / 341715976331) ∧
    -Real.log (250000000000 / 341715976331) ≤ (78129749 / 250000000) := by
  have h := checkLog_sound (w := (91715976331 / 591715976331)) (n := 12)
    (lo := (62503799 / 200000000)) (hi := (78129749 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((341715976331 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(341715976331 / 250000000000) = 1/(250000000000 / 341715976331) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_683 : Bounds (62503799 / 200000000) (78129749 / 250000000) (Real.log (341715976331 / 250000000000)) := by
  have h := reflection_log_683_neg
  have he : Real.log (341715976331 / 250000000000) = -Real.log (250000000000 / 341715976331) := by
    rw [show ((341715976331 / 250000000000) : ℝ) = ((250000000000 / 341715976331) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_684_neg : (156361961 / 500000000) ≤ -Real.log (250000000000 / 341786010179) ∧
    -Real.log (250000000000 / 341786010179) ≤ (312723923 / 1000000000) := by
  have h := checkLog_sound (w := (91786010179 / 591786010179)) (n := 12)
    (lo := (156361961 / 500000000)) (hi := (312723923 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((341786010179 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(341786010179 / 250000000000) = 1/(250000000000 / 341786010179) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_684 : Bounds (156361961 / 500000000) (312723923 / 1000000000) (Real.log (341786010179 / 250000000000)) := by
  have h := reflection_log_684_neg
  have he : Real.log (341786010179 / 250000000000) = -Real.log (250000000000 / 341786010179) := by
    rw [show ((341786010179 / 250000000000) : ℝ) = ((250000000000 / 341786010179) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_685_neg : (144273489 / 1000000000) ≤ -Real.log (625 / 722) ∧
    -Real.log (625 / 722) ≤ (14427349 / 100000000) := by
  have h := checkLog_sound (w := (97 / 1347)) (n := 12)
    (lo := (144273489 / 1000000000)) (hi := (14427349 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((722 / 625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(722 / 625) = 1/(625 / 722) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_685 : Bounds (144273489 / 1000000000) (14427349 / 100000000) (Real.log (722 / 625)) := by
  have h := reflection_log_685_neg
  have he : Real.log (722 / 625) = -Real.log (625 / 722) := by
    rw [show ((722 / 625) : ℝ) = ((625 / 722) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_686_neg : (84327683 / 500000000) ≤ -Real.log (528 / 625) ∧
    -Real.log (528 / 625) ≤ (168655367 / 1000000000) := by
  have h := checkLog_sound (w := (97 / 1153)) (n := 12)
    (lo := (84327683 / 500000000)) (hi := (168655367 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625 / 528) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625 / 528) = 1/(528 / 625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_686 : Bounds (-168655367 / 1000000000) (-84327683 / 500000000) (Real.log (528 / 625)) := by
  have h := reflection_log_686_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_687_neg : (155187 / 1000000000) ≤ -Real.log (625000 / 625097) ∧
    -Real.log (625000 / 625097) ≤ (38797 / 250000000) := by
  have h := checkLog_sound (w := (97 / 1250097)) (n := 12)
    (lo := (155187 / 1000000000)) (hi := (38797 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625097 / 625000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625097 / 625000) = 1/(625000 / 625097) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_687 : Bounds (155187 / 1000000000) (38797 / 250000000) (Real.log (625097 / 625000)) := by
  have h := reflection_log_687_neg
  have he : Real.log (625097 / 625000) = -Real.log (625000 / 625097) := by
    rw [show ((625097 / 625000) : ℝ) = ((625000 / 625097) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_688_neg : (38803 / 250000000) ≤ -Real.log (624903 / 625000) ∧
    -Real.log (624903 / 625000) ≤ (155213 / 1000000000) := by
  have h := checkLog_sound (w := (97 / 1249903)) (n := 12)
    (lo := (38803 / 250000000)) (hi := (155213 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625000 / 624903) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625000 / 624903) = 1/(624903 / 625000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_688 : Bounds (-155213 / 1000000000) (-38803 / 250000000) (Real.log (624903 / 625000)) := by
  have h := reflection_log_688_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_689_neg : (18733033 / 250000000) ≤ -Real.log (1000000 / 1077811) ∧
    -Real.log (1000000 / 1077811) ≤ (74932133 / 1000000000) := by
  have h := checkLog_sound (w := (77811 / 2077811)) (n := 12)
    (lo := (18733033 / 250000000)) (hi := (74932133 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1077811 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1077811 / 1000000) = 1/(1000000 / 1077811) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_689 : Bounds (18733033 / 250000000) (74932133 / 1000000000) (Real.log (1077811 / 1000000)) := by
  have h := reflection_log_689_neg
  have he : Real.log (1077811 / 1000000) = -Real.log (1000000 / 1077811) := by
    rw [show ((1077811 / 1000000) : ℝ) = ((1000000 / 1077811) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_690_neg : (81005087 / 1000000000) ≤ -Real.log (922189 / 1000000) ∧
    -Real.log (922189 / 1000000) ≤ (2531409 / 31250000) := by
  have h := checkLog_sound (w := (77811 / 1922189)) (n := 12)
    (lo := (81005087 / 1000000000)) (hi := (2531409 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 922189) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 922189) = 1/(922189 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_690 : Bounds (-2531409 / 31250000) (-81005087 / 1000000000) (Real.log (922189 / 1000000)) := by
  have h := reflection_log_690_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_691_neg : (37561621 / 500000000) ≤ -Real.log (1000000 / 1078017) ∧
    -Real.log (1000000 / 1078017) ≤ (75123243 / 1000000000) := by
  have h := checkLog_sound (w := (78017 / 2078017)) (n := 12)
    (lo := (37561621 / 500000000)) (hi := (75123243 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1078017 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1078017 / 1000000) = 1/(1000000 / 1078017) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_691 : Bounds (37561621 / 500000000) (75123243 / 1000000000) (Real.log (1078017 / 1000000)) := by
  have h := reflection_log_691_neg
  have he : Real.log (1078017 / 1000000) = -Real.log (1000000 / 1078017) := by
    rw [show ((1078017 / 1000000) : ℝ) = ((1000000 / 1078017) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_692_neg : (81228493 / 1000000000) ≤ -Real.log (921983 / 1000000) ∧
    -Real.log (921983 / 1000000) ≤ (40614247 / 500000000) := by
  have h := checkLog_sound (w := (78017 / 1921983)) (n := 12)
    (lo := (81228493 / 1000000000)) (hi := (40614247 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 921983) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 921983) = 1/(921983 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_692 : Bounds (-40614247 / 500000000) (-81228493 / 1000000000) (Real.log (921983 / 1000000)) := by
  have h := reflection_log_692_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_693_neg : (6105251 / 1000000000) ≤ -Real.log (993913347711 / 1000000000000) ∧
    -Real.log (993913347711 / 1000000000000) ≤ (1526313 / 250000000) := by
  have h := checkLog_sound (w := (6086652289 / 1993913347711)) (n := 12)
    (lo := (6105251 / 1000000000)) (hi := (1526313 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993913347711) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993913347711) = 1/(993913347711 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_693 : Bounds (-1526313 / 250000000) (-6105251 / 1000000000) (Real.log (993913347711 / 1000000000000)) := by
  have h := reflection_log_693_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_694_neg : (3036477 / 500000000) ≤ -Real.log (993945448279 / 1000000000000) ∧
    -Real.log (993945448279 / 1000000000000) ≤ (1214591 / 200000000) := by
  have h := checkLog_sound (w := (6054551721 / 1993945448279)) (n := 12)
    (lo := (3036477 / 500000000)) (hi := (1214591 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993945448279) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993945448279) = 1/(993945448279 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_694 : Bounds (-1214591 / 200000000) (-3036477 / 500000000) (Real.log (993945448279 / 1000000000000)) := by
  have h := reflection_log_694_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_695_neg : (155937219 / 1000000000) ≤ -Real.log (250000000000 / 292188206539) ∧
    -Real.log (250000000000 / 292188206539) ≤ (7796861 / 50000000) := by
  have h := checkLog_sound (w := (42188206539 / 542188206539)) (n := 12)
    (lo := (155937219 / 1000000000)) (hi := (7796861 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((292188206539 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(292188206539 / 250000000000) = 1/(250000000000 / 292188206539) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_695 : Bounds (155937219 / 1000000000) (7796861 / 50000000) (Real.log (292188206539 / 250000000000)) := by
  have h := reflection_log_695_neg
  have he : Real.log (292188206539 / 250000000000) = -Real.log (250000000000 / 292188206539) := by
    rw [show ((292188206539 / 250000000000) : ℝ) = ((250000000000 / 292188206539) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_696_neg : (19543967 / 125000000) ≤ -Real.log (160000000 / 187077983) ∧
    -Real.log (160000000 / 187077983) ≤ (156351737 / 1000000000) := by
  have h := checkLog_sound (w := (27077983 / 347077983)) (n := 12)
    (lo := (19543967 / 125000000)) (hi := (156351737 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((187077983 / 160000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(187077983 / 160000000) = 1/(160000000 / 187077983) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_696 : Bounds (19543967 / 125000000) (156351737 / 1000000000) (Real.log (187077983 / 160000000)) := by
  have h := reflection_log_696_neg
  have he : Real.log (187077983 / 160000000) = -Real.log (160000000 / 187077983) := by
    rw [show ((187077983 / 160000000) : ℝ) = ((160000000 / 187077983) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_697_neg : (156361961 / 500000000) ≤ -Real.log (500000000000 / 683572020357) ∧
    -Real.log (500000000000 / 683572020357) ≤ (312723923 / 1000000000) := by
  have h := checkLog_sound (w := (183572020357 / 1183572020357)) (n := 12)
    (lo := (156361961 / 500000000)) (hi := (312723923 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((683572020357 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(683572020357 / 500000000000) = 1/(500000000000 / 683572020357) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_697 : Bounds (156361961 / 500000000) (312723923 / 1000000000) (Real.log (683572020357 / 500000000000)) := by
  have h := reflection_log_697_neg
  have he : Real.log (683572020357 / 500000000000) = -Real.log (500000000000 / 683572020357) := by
    rw [show ((683572020357 / 500000000000) : ℝ) = ((500000000000 / 683572020357) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_698_neg : (62585771 / 200000000) ≤ -Real.log (500000000000 / 683712121213) ∧
    -Real.log (500000000000 / 683712121213) ≤ (39116107 / 125000000) := by
  have h := checkLog_sound (w := (183712121213 / 1183712121213)) (n := 12)
    (lo := (62585771 / 200000000)) (hi := (39116107 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((683712121213 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(683712121213 / 500000000000) = 1/(500000000000 / 683712121213) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_698 : Bounds (62585771 / 200000000) (39116107 / 125000000) (Real.log (683712121213 / 500000000000)) := by
  have h := reflection_log_698_neg
  have he : Real.log (683712121213 / 500000000000) = -Real.log (500000000000 / 683712121213) := by
    rw [show ((683712121213 / 500000000000) : ℝ) = ((500000000000 / 683712121213) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_699_neg : (2887201 / 20000000) ≤ -Real.log (10000 / 11553) ∧
    -Real.log (10000 / 11553) ≤ (144360051 / 1000000000) := by
  have h := checkLog_sound (w := (1553 / 21553)) (n := 12)
    (lo := (2887201 / 20000000)) (hi := (144360051 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11553 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11553 / 10000) = 1/(10000 / 11553) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_699 : Bounds (2887201 / 20000000) (144360051 / 1000000000) (Real.log (11553 / 10000)) := by
  have h := reflection_log_699_neg
  have he : Real.log (11553 / 10000) = -Real.log (10000 / 11553) := by
    rw [show ((11553 / 10000) : ℝ) = ((10000 / 11553) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_700_neg : (10548359 / 62500000) ≤ -Real.log (8447 / 10000) ∧
    -Real.log (8447 / 10000) ≤ (33754749 / 200000000) := by
  have h := checkLog_sound (w := (1553 / 18447)) (n := 12)
    (lo := (10548359 / 62500000)) (hi := (33754749 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8447) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8447) = 1/(8447 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_700 : Bounds (-33754749 / 200000000) (-10548359 / 62500000) (Real.log (8447 / 10000)) := by
  have h := reflection_log_700_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_701_neg : (155287 / 1000000000) ≤ -Real.log (10000000 / 10001553) ∧
    -Real.log (10000000 / 10001553) ≤ (19411 / 125000000) := by
  have h := checkLog_sound (w := (1553 / 20001553)) (n := 12)
    (lo := (155287 / 1000000000)) (hi := (19411 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001553 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001553 / 10000000) = 1/(10000000 / 10001553) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_701 : Bounds (155287 / 1000000000) (19411 / 125000000) (Real.log (10001553 / 10000000)) := by
  have h := reflection_log_701_neg
  have he : Real.log (10001553 / 10000000) = -Real.log (10000000 / 10001553) := by
    rw [show ((10001553 / 10000000) : ℝ) = ((10000000 / 10001553) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_702_neg : (9707 / 62500000) ≤ -Real.log (9998447 / 10000000) ∧
    -Real.log (9998447 / 10000000) ≤ (155313 / 1000000000) := by
  have h := checkLog_sound (w := (1553 / 19998447)) (n := 12)
    (lo := (9707 / 62500000)) (hi := (155313 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998447) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998447) = 1/(9998447 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_702 : Bounds (-155313 / 1000000000) (-9707 / 62500000) (Real.log (9998447 / 10000000)) := by
  have h := reflection_log_702_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_703_neg : (74979449 / 1000000000) ≤ -Real.log (500000 / 538931) ∧
    -Real.log (500000 / 538931) ≤ (1499589 / 20000000) := by
  have h := checkLog_sound (w := (38931 / 1038931)) (n := 12)
    (lo := (74979449 / 1000000000)) (hi := (1499589 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((538931 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(538931 / 500000) = 1/(500000 / 538931) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_703 : Bounds (74979449 / 1000000000) (1499589 / 20000000) (Real.log (538931 / 500000)) := by
  have h := reflection_log_703_neg
  have he : Real.log (538931 / 500000) = -Real.log (500000 / 538931) := by
    rw [show ((538931 / 500000) : ℝ) = ((500000 / 538931) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily
