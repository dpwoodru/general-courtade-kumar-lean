import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_64_neg : (72723371 / 1000000000) ≤ -Real.log (1000000 / 1075433) ∧
    -Real.log (1000000 / 1075433) ≤ (18180843 / 250000000) := by
  have h := checkLog_sound (w := (75433 / 2075433)) (n := 12)
    (lo := (72723371 / 1000000000)) (hi := (18180843 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1075433 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1075433 / 1000000) = 1/(1000000 / 1075433) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_64 : Bounds (72723371 / 1000000000) (18180843 / 250000000) (Real.log (1075433 / 1000000)) := by
  have h := reflection_log_64_neg
  have he : Real.log (1075433 / 1000000) = -Real.log (1000000 / 1075433) := by
    rw [show ((1075433 / 1000000) : ℝ) = ((1000000 / 1075433) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_65_neg : (78429759 / 1000000000) ≤ -Real.log (924567 / 1000000) ∧
    -Real.log (924567 / 1000000) ≤ (245093 / 3125000) := by
  have h := checkLog_sound (w := (75433 / 1924567)) (n := 12)
    (lo := (78429759 / 1000000000)) (hi := (245093 / 3125000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 924567) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 924567) = 1/(924567 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_65 : Bounds (-245093 / 3125000) (-78429759 / 1000000000) (Real.log (924567 / 1000000)) := by
  have h := reflection_log_65_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_66_neg : (4556949 / 62500000) ≤ -Real.log (200000 / 215127) ∧
    -Real.log (200000 / 215127) ≤ (14582237 / 200000000) := by
  have h := checkLog_sound (w := (15127 / 415127)) (n := 12)
    (lo := (4556949 / 62500000)) (hi := (14582237 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((215127 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(215127 / 200000) = 1/(200000 / 215127) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_66 : Bounds (4556949 / 62500000) (14582237 / 200000000) (Real.log (215127 / 200000)) := by
  have h := reflection_log_66_neg
  have he : Real.log (215127 / 200000) = -Real.log (200000 / 215127) := by
    rw [show ((215127 / 200000) : ℝ) = ((200000 / 215127) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_67_neg : (78648263 / 1000000000) ≤ -Real.log (184873 / 200000) ∧
    -Real.log (184873 / 200000) ≤ (9831033 / 125000000) := by
  have h := checkLog_sound (w := (15127 / 384873)) (n := 12)
    (lo := (78648263 / 1000000000)) (hi := (9831033 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 184873) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 184873) = 1/(184873 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_67 : Bounds (-9831033 / 125000000) (-78648263 / 1000000000) (Real.log (184873 / 200000)) := by
  have h := reflection_log_67_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_68_neg : (2868539 / 500000000) ≤ -Real.log (39771173871 / 40000000000) ∧
    -Real.log (39771173871 / 40000000000) ≤ (5737079 / 1000000000) := by
  have h := checkLog_sound (w := (228826129 / 79771173871)) (n := 12)
    (lo := (2868539 / 500000000)) (hi := (5737079 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39771173871) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39771173871) = 1/(39771173871 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_68 : Bounds (-5737079 / 1000000000) (-2868539 / 500000000) (Real.log (39771173871 / 40000000000)) := by
  have h := reflection_log_68_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_69_neg : (5706387 / 1000000000) ≤ -Real.log (994309862511 / 1000000000000) ∧
    -Real.log (994309862511 / 1000000000000) ≤ (1426597 / 250000000) := by
  have h := checkLog_sound (w := (5690137489 / 1994309862511)) (n := 12)
    (lo := (5706387 / 1000000000)) (hi := (1426597 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 994309862511) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 994309862511) = 1/(994309862511 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_69 : Bounds (-1426597 / 250000000) (-5706387 / 1000000000) (Real.log (994309862511 / 1000000000000)) := by
  have h := reflection_log_69_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_70_neg : (15115313 / 100000000) ≤ -Real.log (500000000000 / 581587380903) ∧
    -Real.log (500000000000 / 581587380903) ≤ (151153131 / 1000000000) := by
  have h := checkLog_sound (w := (81587380903 / 1081587380903)) (n := 12)
    (lo := (15115313 / 100000000)) (hi := (151153131 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((581587380903 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(581587380903 / 500000000000) = 1/(500000000000 / 581587380903) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_70 : Bounds (15115313 / 100000000) (151153131 / 1000000000) (Real.log (581587380903 / 500000000000)) := by
  have h := reflection_log_70_neg
  have he : Real.log (581587380903 / 500000000000) = -Real.log (500000000000 / 581587380903) := by
    rw [show ((581587380903 / 500000000000) : ℝ) = ((500000000000 / 581587380903) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_71_neg : (18944931 / 125000000) ≤ -Real.log (500000000000 / 581823738459) ∧
    -Real.log (500000000000 / 581823738459) ≤ (151559449 / 1000000000) := by
  have h := checkLog_sound (w := (81823738459 / 1081823738459)) (n := 12)
    (lo := (18944931 / 125000000)) (hi := (151559449 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((581823738459 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(581823738459 / 500000000000) = 1/(500000000000 / 581823738459) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_71 : Bounds (18944931 / 125000000) (151559449 / 1000000000) (Real.log (581823738459 / 500000000000)) := by
  have h := reflection_log_71_neg
  have he : Real.log (581823738459 / 500000000000) = -Real.log (500000000000 / 581823738459) := by
    rw [show ((581823738459 / 500000000000) : ℝ) = ((500000000000 / 581823738459) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_72_neg : (37887417 / 125000000) ≤ -Real.log (500000000000 / 677024482109) ∧
    -Real.log (500000000000 / 677024482109) ≤ (303099337 / 1000000000) := by
  have h := checkLog_sound (w := (177024482109 / 1177024482109)) (n := 12)
    (lo := (37887417 / 125000000)) (hi := (303099337 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((677024482109 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(677024482109 / 500000000000) = 1/(500000000000 / 677024482109) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_72 : Bounds (37887417 / 125000000) (303099337 / 1000000000) (Real.log (677024482109 / 500000000000)) := by
  have h := reflection_log_72_neg
  have he : Real.log (677024482109 / 500000000000) = -Real.log (500000000000 / 677024482109) := by
    rw [show ((677024482109 / 500000000000) : ℝ) = ((500000000000 / 677024482109) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_73_neg : (9478249 / 31250000) ≤ -Real.log (500000000000 / 677163037081) ∧
    -Real.log (500000000000 / 677163037081) ≤ (303303969 / 1000000000) := by
  have h := checkLog_sound (w := (177163037081 / 1177163037081)) (n := 12)
    (lo := (9478249 / 31250000)) (hi := (303303969 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((677163037081 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(677163037081 / 500000000000) = 1/(500000000000 / 677163037081) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_73 : Bounds (9478249 / 31250000) (303303969 / 1000000000) (Real.log (677163037081 / 500000000000)) := by
  have h := reflection_log_73_neg
  have he : Real.log (677163037081 / 500000000000) = -Real.log (500000000000 / 677163037081) := by
    rw [show ((677163037081 / 500000000000) : ℝ) = ((500000000000 / 677163037081) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_74_neg : (28056709 / 200000000) ≤ -Real.log (5000 / 5753) ∧
    -Real.log (5000 / 5753) ≤ (70141773 / 500000000) := by
  have h := checkLog_sound (w := (753 / 10753)) (n := 12)
    (lo := (28056709 / 200000000)) (hi := (70141773 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5753 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5753 / 5000) = 1/(5000 / 5753) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_74 : Bounds (28056709 / 200000000) (70141773 / 500000000) (Real.log (5753 / 5000)) := by
  have h := reflection_log_74_neg
  have he : Real.log (5753 / 5000) = -Real.log (5000 / 5753) := by
    rw [show ((5753 / 5000) : ℝ) = ((5000 / 5753) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_75_neg : (163225061 / 1000000000) ≤ -Real.log (4247 / 5000) ∧
    -Real.log (4247 / 5000) ≤ (81612531 / 500000000) := by
  have h := checkLog_sound (w := (753 / 9247)) (n := 12)
    (lo := (163225061 / 1000000000)) (hi := (81612531 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4247) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4247) = 1/(4247 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_75 : Bounds (-81612531 / 500000000) (-163225061 / 1000000000) (Real.log (4247 / 5000)) := by
  have h := reflection_log_75_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_76_neg : (37647 / 250000000) ≤ -Real.log (5000000 / 5000753) ∧
    -Real.log (5000000 / 5000753) ≤ (150589 / 1000000000) := by
  have h := checkLog_sound (w := (753 / 10000753)) (n := 12)
    (lo := (37647 / 250000000)) (hi := (150589 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000753 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000753 / 5000000) = 1/(5000000 / 5000753) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_76 : Bounds (37647 / 250000000) (150589 / 1000000000) (Real.log (5000753 / 5000000)) := by
  have h := reflection_log_76_neg
  have he : Real.log (5000753 / 5000000) = -Real.log (5000000 / 5000753) := by
    rw [show ((5000753 / 5000000) : ℝ) = ((5000000 / 5000753) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_77_neg : (150611 / 1000000000) ≤ -Real.log (4999247 / 5000000) ∧
    -Real.log (4999247 / 5000000) ≤ (37653 / 250000000) := by
  have h := checkLog_sound (w := (753 / 9999247)) (n := 12)
    (lo := (150611 / 1000000000)) (hi := (37653 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999247) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999247) = 1/(4999247 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_77 : Bounds (-37653 / 250000000) (-150611 / 1000000000) (Real.log (4999247 / 5000000)) := by
  have h := reflection_log_77_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_78_neg : (9096349 / 125000000) ≤ -Real.log (250000 / 268871) ∧
    -Real.log (250000 / 268871) ≤ (72770793 / 1000000000) := by
  have h := checkLog_sound (w := (18871 / 518871)) (n := 12)
    (lo := (9096349 / 125000000)) (hi := (72770793 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((268871 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(268871 / 250000) = 1/(250000 / 268871) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_78 : Bounds (9096349 / 125000000) (72770793 / 1000000000) (Real.log (268871 / 250000)) := by
  have h := reflection_log_78_neg
  have he : Real.log (268871 / 250000) = -Real.log (250000 / 268871) := by
    rw [show ((268871 / 250000) : ℝ) = ((250000 / 268871) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_79_neg : (78484921 / 1000000000) ≤ -Real.log (231129 / 250000) ∧
    -Real.log (231129 / 250000) ≤ (39242461 / 500000000) := by
  have h := checkLog_sound (w := (18871 / 481129)) (n := 12)
    (lo := (78484921 / 1000000000)) (hi := (39242461 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 231129) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 231129) = 1/(231129 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_79 : Bounds (-39242461 / 500000000) (-78484921 / 1000000000) (Real.log (231129 / 250000)) := by
  have h := reflection_log_79_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_80_neg : (72958597 / 1000000000) ≤ -Real.log (500000 / 537843) ∧
    -Real.log (500000 / 537843) ≤ (36479299 / 500000000) := by
  have h := checkLog_sound (w := (37843 / 1037843)) (n := 12)
    (lo := (72958597 / 1000000000)) (hi := (36479299 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((537843 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(537843 / 500000) = 1/(500000 / 537843) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_80 : Bounds (72958597 / 1000000000) (36479299 / 500000000) (Real.log (537843 / 500000)) := by
  have h := reflection_log_80_neg
  have he : Real.log (537843 / 500000) = -Real.log (500000 / 537843) := by
    rw [show ((537843 / 500000) : ℝ) = ((500000 / 537843) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_81_neg : (39351719 / 500000000) ≤ -Real.log (462157 / 500000) ∧
    -Real.log (462157 / 500000) ≤ (78703439 / 1000000000) := by
  have h := checkLog_sound (w := (37843 / 962157)) (n := 12)
    (lo := (39351719 / 500000000)) (hi := (78703439 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 462157) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 462157) = 1/(462157 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_81 : Bounds (-78703439 / 1000000000) (-39351719 / 500000000) (Real.log (462157 / 500000)) := by
  have h := reflection_log_81_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_82_neg : (143621 / 25000000) ≤ -Real.log (248567907351 / 250000000000) ∧
    -Real.log (248567907351 / 250000000000) ≤ (5744841 / 1000000000) := by
  have h := checkLog_sound (w := (1432092649 / 498567907351)) (n := 12)
    (lo := (143621 / 25000000)) (hi := (5744841 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248567907351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248567907351) = 1/(248567907351 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_82 : Bounds (-5744841 / 1000000000) (-143621 / 25000000) (Real.log (248567907351 / 250000000000)) := by
  have h := reflection_log_82_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_83_neg : (357133 / 62500000) ≤ -Real.log (62143885359 / 62500000000) ∧
    -Real.log (62143885359 / 62500000000) ≤ (5714129 / 1000000000) := by
  have h := checkLog_sound (w := (356114641 / 124643885359)) (n := 12)
    (lo := (357133 / 62500000)) (hi := (5714129 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 62143885359) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 62143885359) = 1/(62143885359 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_83 : Bounds (-5714129 / 1000000000) (-357133 / 62500000) (Real.log (62143885359 / 62500000000)) := by
  have h := reflection_log_83_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_84_neg : (75627857 / 500000000) ≤ -Real.log (500000000000 / 581647045589) ∧
    -Real.log (500000000000 / 581647045589) ≤ (30251143 / 200000000) := by
  have h := checkLog_sound (w := (81647045589 / 1081647045589)) (n := 12)
    (lo := (75627857 / 500000000)) (hi := (30251143 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((581647045589 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(581647045589 / 500000000000) = 1/(500000000000 / 581647045589) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_84 : Bounds (75627857 / 500000000) (30251143 / 200000000) (Real.log (581647045589 / 500000000000)) := by
  have h := reflection_log_84_neg
  have he : Real.log (581647045589 / 500000000000) = -Real.log (500000000000 / 581647045589) := by
    rw [show ((581647045589 / 500000000000) : ℝ) = ((500000000000 / 581647045589) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_85_neg : (30332407 / 200000000) ≤ -Real.log (20000000000 / 23275337169) ∧
    -Real.log (20000000000 / 23275337169) ≤ (37915509 / 250000000) := by
  have h := checkLog_sound (w := (3275337169 / 43275337169)) (n := 12)
    (lo := (30332407 / 200000000)) (hi := (37915509 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((23275337169 / 20000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(23275337169 / 20000000000) = 1/(20000000000 / 23275337169) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_85 : Bounds (30332407 / 200000000) (37915509 / 250000000) (Real.log (23275337169 / 20000000000)) := by
  have h := reflection_log_85_neg
  have he : Real.log (23275337169 / 20000000000) = -Real.log (20000000000 / 23275337169) := by
    rw [show ((23275337169 / 20000000000) : ℝ) = ((20000000000 / 23275337169) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_86_neg : (9478249 / 31250000) ≤ -Real.log (12500000000 / 16929075927) ∧
    -Real.log (12500000000 / 16929075927) ≤ (303303969 / 1000000000) := by
  have h := checkLog_sound (w := (4429075927 / 29429075927)) (n := 12)
    (lo := (9478249 / 31250000)) (hi := (303303969 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((16929075927 / 12500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(16929075927 / 12500000000) = 1/(12500000000 / 16929075927) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_86 : Bounds (9478249 / 31250000) (303303969 / 1000000000) (Real.log (16929075927 / 12500000000)) := by
  have h := reflection_log_86_neg
  have he : Real.log (16929075927 / 12500000000) = -Real.log (12500000000 / 16929075927) := by
    rw [show ((16929075927 / 12500000000) : ℝ) = ((12500000000 / 16929075927) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_87_neg : (151754303 / 500000000) ≤ -Real.log (500000000000 / 677301624677) ∧
    -Real.log (500000000000 / 677301624677) ≤ (303508607 / 1000000000) := by
  have h := checkLog_sound (w := (177301624677 / 1177301624677)) (n := 12)
    (lo := (151754303 / 500000000)) (hi := (303508607 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((677301624677 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(677301624677 / 500000000000) = 1/(500000000000 / 677301624677) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_87 : Bounds (151754303 / 500000000) (303508607 / 1000000000) (Real.log (677301624677 / 500000000000)) := by
  have h := reflection_log_87_neg
  have he : Real.log (677301624677 / 500000000000) = -Real.log (500000000000 / 677301624677) := by
    rw [show ((677301624677 / 500000000000) : ℝ) = ((500000000000 / 677301624677) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_88_neg : (35092613 / 250000000) ≤ -Real.log (10000 / 11507) ∧
    -Real.log (10000 / 11507) ≤ (140370453 / 1000000000) := by
  have h := checkLog_sound (w := (1507 / 21507)) (n := 12)
    (lo := (35092613 / 250000000)) (hi := (140370453 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11507 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11507 / 10000) = 1/(10000 / 11507) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_88 : Bounds (35092613 / 250000000) (140370453 / 1000000000) (Real.log (11507 / 10000)) := by
  have h := reflection_log_88_neg
  have he : Real.log (11507 / 10000) = -Real.log (10000 / 11507) := by
    rw [show ((11507 / 10000) : ℝ) = ((10000 / 11507) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_89_neg : (81671399 / 500000000) ≤ -Real.log (8493 / 10000) ∧
    -Real.log (8493 / 10000) ≤ (163342799 / 1000000000) := by
  have h := checkLog_sound (w := (1507 / 18493)) (n := 12)
    (lo := (81671399 / 500000000)) (hi := (163342799 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8493) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8493) = 1/(8493 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_89 : Bounds (-163342799 / 1000000000) (-81671399 / 500000000) (Real.log (8493 / 10000)) := by
  have h := reflection_log_89_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_90_neg : (4709 / 31250000) ≤ -Real.log (10000000 / 10001507) ∧
    -Real.log (10000000 / 10001507) ≤ (150689 / 1000000000) := by
  have h := checkLog_sound (w := (1507 / 20001507)) (n := 12)
    (lo := (4709 / 31250000)) (hi := (150689 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001507 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001507 / 10000000) = 1/(10000000 / 10001507) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_90 : Bounds (4709 / 31250000) (150689 / 1000000000) (Real.log (10001507 / 10000000)) := by
  have h := reflection_log_90_neg
  have he : Real.log (10001507 / 10000000) = -Real.log (10000000 / 10001507) := by
    rw [show ((10001507 / 10000000) : ℝ) = ((10000000 / 10001507) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_91_neg : (150711 / 1000000000) ≤ -Real.log (9998493 / 10000000) ∧
    -Real.log (9998493 / 10000000) ≤ (18839 / 125000000) := by
  have h := checkLog_sound (w := (1507 / 19998493)) (n := 12)
    (lo := (150711 / 1000000000)) (hi := (18839 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998493) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998493) = 1/(9998493 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_91 : Bounds (-18839 / 125000000) (-150711 / 1000000000) (Real.log (9998493 / 10000000)) := by
  have h := reflection_log_91_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_92_neg : (18204553 / 250000000) ≤ -Real.log (200000 / 215107) ∧
    -Real.log (200000 / 215107) ≤ (72818213 / 1000000000) := by
  have h := checkLog_sound (w := (15107 / 415107)) (n := 12)
    (lo := (18204553 / 250000000)) (hi := (72818213 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((215107 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(215107 / 200000) = 1/(200000 / 215107) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_92 : Bounds (18204553 / 250000000) (72818213 / 1000000000) (Real.log (215107 / 200000)) := by
  have h := reflection_log_92_neg
  have he : Real.log (215107 / 200000) = -Real.log (200000 / 215107) := by
    rw [show ((215107 / 200000) : ℝ) = ((200000 / 215107) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_93_neg : (78540087 / 1000000000) ≤ -Real.log (184893 / 200000) ∧
    -Real.log (184893 / 200000) ≤ (9817511 / 125000000) := by
  have h := checkLog_sound (w := (15107 / 384893)) (n := 12)
    (lo := (78540087 / 1000000000)) (hi := (9817511 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 184893) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 184893) = 1/(184893 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_93 : Bounds (-9817511 / 125000000) (-78540087 / 1000000000) (Real.log (184893 / 200000)) := by
  have h := reflection_log_93_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_94_neg : (36502539 / 500000000) ≤ -Real.log (125000 / 134467) ∧
    -Real.log (125000 / 134467) ≤ (73005079 / 1000000000) := by
  have h := checkLog_sound (w := (9467 / 259467)) (n := 12)
    (lo := (36502539 / 500000000)) (hi := (73005079 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((134467 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(134467 / 125000) = 1/(125000 / 134467) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_94 : Bounds (36502539 / 500000000) (73005079 / 1000000000) (Real.log (134467 / 125000)) := by
  have h := reflection_log_94_neg
  have he : Real.log (134467 / 125000) = -Real.log (125000 / 134467) := by
    rw [show ((134467 / 125000) : ℝ) = ((125000 / 134467) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_95_neg : (78757533 / 1000000000) ≤ -Real.log (115533 / 125000) ∧
    -Real.log (115533 / 125000) ≤ (39378767 / 500000000) := by
  have h := checkLog_sound (w := (9467 / 240533)) (n := 12)
    (lo := (78757533 / 1000000000)) (hi := (39378767 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 115533) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 115533) = 1/(115533 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_95 : Bounds (-39378767 / 500000000) (-78757533 / 1000000000) (Real.log (115533 / 125000)) := by
  have h := reflection_log_95_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_96_neg : (1150491 / 200000000) ≤ -Real.log (15535375911 / 15625000000) ∧
    -Real.log (15535375911 / 15625000000) ≤ (719057 / 125000000) := by
  have h := checkLog_sound (w := (89624089 / 31160375911)) (n := 12)
    (lo := (1150491 / 200000000)) (hi := (719057 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 15535375911) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 15535375911) = 1/(15535375911 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_96 : Bounds (-719057 / 125000000) (-1150491 / 200000000) (Real.log (15535375911 / 15625000000)) := by
  have h := reflection_log_96_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_97_neg : (2860937 / 500000000) ≤ -Real.log (39771778551 / 40000000000) ∧
    -Real.log (39771778551 / 40000000000) ≤ (1831 / 320000) := by
  have h := checkLog_sound (w := (228221449 / 79771778551)) (n := 12)
    (lo := (2860937 / 500000000)) (hi := (1831 / 320000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39771778551) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39771778551) = 1/(39771778551 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_97 : Bounds (-1831 / 320000) (-2860937 / 500000000) (Real.log (39771778551 / 40000000000)) := by
  have h := reflection_log_97_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_98_neg : (151358299 / 1000000000) ≤ -Real.log (500000000000 / 581706716857) ∧
    -Real.log (500000000000 / 581706716857) ≤ (1513583 / 10000000) := by
  have h := checkLog_sound (w := (81706716857 / 1081706716857)) (n := 12)
    (lo := (151358299 / 1000000000)) (hi := (1513583 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((581706716857 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(581706716857 / 500000000000) = 1/(500000000000 / 581706716857) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_98 : Bounds (151358299 / 1000000000) (1513583 / 10000000) (Real.log (581706716857 / 500000000000)) := by
  have h := reflection_log_98_neg
  have he : Real.log (581706716857 / 500000000000) = -Real.log (500000000000 / 581706716857) := by
    rw [show ((581706716857 / 500000000000) : ℝ) = ((500000000000 / 581706716857) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_99_neg : (37940653 / 250000000) ≤ -Real.log (250000000000 / 290970977989) ∧
    -Real.log (250000000000 / 290970977989) ≤ (151762613 / 1000000000) := by
  have h := checkLog_sound (w := (40970977989 / 540970977989)) (n := 12)
    (lo := (37940653 / 250000000)) (hi := (151762613 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((290970977989 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(290970977989 / 250000000000) = 1/(250000000000 / 290970977989) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_99 : Bounds (37940653 / 250000000) (151762613 / 1000000000) (Real.log (290970977989 / 250000000000)) := by
  have h := reflection_log_99_neg
  have he : Real.log (290970977989 / 250000000000) = -Real.log (250000000000 / 290970977989) := by
    rw [show ((290970977989 / 250000000000) : ℝ) = ((250000000000 / 290970977989) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_100_neg : (151754303 / 500000000) ≤ -Real.log (125000000000 / 169325406169) ∧
    -Real.log (125000000000 / 169325406169) ≤ (303508607 / 1000000000) := by
  have h := checkLog_sound (w := (44325406169 / 294325406169)) (n := 12)
    (lo := (151754303 / 500000000)) (hi := (303508607 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((169325406169 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(169325406169 / 125000000000) = 1/(125000000000 / 169325406169) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_100 : Bounds (151754303 / 500000000) (303508607 / 1000000000) (Real.log (169325406169 / 125000000000)) := by
  have h := reflection_log_100_neg
  have he : Real.log (169325406169 / 125000000000) = -Real.log (125000000000 / 169325406169) := by
    rw [show ((169325406169 / 125000000000) : ℝ) = ((125000000000 / 169325406169) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_101_neg : (303713251 / 1000000000) ≤ -Real.log (125000000000 / 169360061227) ∧
    -Real.log (125000000000 / 169360061227) ≤ (75928313 / 250000000) := by
  have h := checkLog_sound (w := (44360061227 / 294360061227)) (n := 12)
    (lo := (303713251 / 1000000000)) (hi := (75928313 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((169360061227 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(169360061227 / 125000000000) = 1/(125000000000 / 169360061227) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_101 : Bounds (303713251 / 1000000000) (75928313 / 250000000) (Real.log (169360061227 / 125000000000)) := by
  have h := reflection_log_101_neg
  have he : Real.log (169360061227 / 125000000000) = -Real.log (125000000000 / 169360061227) := by
    rw [show ((169360061227 / 125000000000) : ℝ) = ((125000000000 / 169360061227) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_102_neg : (17557169 / 125000000) ≤ -Real.log (2500 / 2877) ∧
    -Real.log (2500 / 2877) ≤ (140457353 / 1000000000) := by
  have h := checkLog_sound (w := (377 / 5377)) (n := 12)
    (lo := (17557169 / 125000000)) (hi := (140457353 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2877 / 2500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2877 / 2500) = 1/(2500 / 2877) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_102 : Bounds (17557169 / 125000000) (140457353 / 1000000000) (Real.log (2877 / 2500)) := by
  have h := reflection_log_102_neg
  have he : Real.log (2877 / 2500) = -Real.log (2500 / 2877) := by
    rw [show ((2877 / 2500) : ℝ) = ((2500 / 2877) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_103_neg : (163460549 / 1000000000) ≤ -Real.log (2123 / 2500) ∧
    -Real.log (2123 / 2500) ≤ (3269211 / 20000000) := by
  have h := checkLog_sound (w := (377 / 4623)) (n := 12)
    (lo := (163460549 / 1000000000)) (hi := (3269211 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500 / 2123) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500 / 2123) = 1/(2123 / 2500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_103 : Bounds (-3269211 / 20000000) (-163460549 / 1000000000) (Real.log (2123 / 2500)) := by
  have h := reflection_log_103_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_104_neg : (37697 / 250000000) ≤ -Real.log (2500000 / 2500377) ∧
    -Real.log (2500000 / 2500377) ≤ (150789 / 1000000000) := by
  have h := checkLog_sound (w := (377 / 5000377)) (n := 12)
    (lo := (37697 / 250000000)) (hi := (150789 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500377 / 2500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500377 / 2500000) = 1/(2500000 / 2500377) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_104 : Bounds (37697 / 250000000) (150789 / 1000000000) (Real.log (2500377 / 2500000)) := by
  have h := reflection_log_104_neg
  have he : Real.log (2500377 / 2500000) = -Real.log (2500000 / 2500377) := by
    rw [show ((2500377 / 2500000) : ℝ) = ((2500000 / 2500377) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_105_neg : (150811 / 1000000000) ≤ -Real.log (2499623 / 2500000) ∧
    -Real.log (2499623 / 2500000) ≤ (37703 / 250000000) := by
  have h := checkLog_sound (w := (377 / 4999623)) (n := 12)
    (lo := (150811 / 1000000000)) (hi := (37703 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000 / 2499623) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000 / 2499623) = 1/(2499623 / 2500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_105 : Bounds (-37703 / 250000000) (-150811 / 1000000000) (Real.log (2499623 / 2500000)) := by
  have h := reflection_log_105_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_106_neg : (72864699 / 1000000000) ≤ -Real.log (200000 / 215117) ∧
    -Real.log (200000 / 215117) ≤ (728647 / 10000000) := by
  have h := checkLog_sound (w := (15117 / 415117)) (n := 12)
    (lo := (72864699 / 1000000000)) (hi := (728647 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((215117 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(215117 / 200000) = 1/(200000 / 215117) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_106 : Bounds (72864699 / 1000000000) (728647 / 10000000) (Real.log (215117 / 200000)) := by
  have h := reflection_log_106_neg
  have he : Real.log (215117 / 200000) = -Real.log (200000 / 215117) := by
    rw [show ((215117 / 200000) : ℝ) = ((200000 / 215117) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_107_neg : (78594173 / 1000000000) ≤ -Real.log (184883 / 200000) ∧
    -Real.log (184883 / 200000) ≤ (39297087 / 500000000) := by
  have h := checkLog_sound (w := (15117 / 384883)) (n := 12)
    (lo := (78594173 / 1000000000)) (hi := (39297087 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 184883) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 184883) = 1/(184883 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_107 : Bounds (-39297087 / 500000000) (-78594173 / 1000000000) (Real.log (184883 / 200000)) := by
  have h := reflection_log_107_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_108_neg : (36526243 / 500000000) ≤ -Real.log (1000000 / 1075787) ∧
    -Real.log (1000000 / 1075787) ≤ (73052487 / 1000000000) := by
  have h := checkLog_sound (w := (75787 / 2075787)) (n := 12)
    (lo := (36526243 / 500000000)) (hi := (73052487 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1075787 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1075787 / 1000000) = 1/(1000000 / 1075787) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_108 : Bounds (36526243 / 500000000) (73052487 / 1000000000) (Real.log (1075787 / 1000000)) := by
  have h := reflection_log_108_neg
  have he : Real.log (1075787 / 1000000) = -Real.log (1000000 / 1075787) := by
    rw [show ((1075787 / 1000000) : ℝ) = ((1000000 / 1075787) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_109_neg : (39406357 / 500000000) ≤ -Real.log (924213 / 1000000) ∧
    -Real.log (924213 / 1000000) ≤ (15762543 / 200000000) := by
  have h := checkLog_sound (w := (75787 / 1924213)) (n := 12)
    (lo := (39406357 / 500000000)) (hi := (15762543 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 924213) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 924213) = 1/(924213 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_109 : Bounds (-15762543 / 200000000) (-39406357 / 500000000) (Real.log (924213 / 1000000)) := by
  have h := reflection_log_109_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_110_neg : (5760227 / 1000000000) ≤ -Real.log (994256330631 / 1000000000000) ∧
    -Real.log (994256330631 / 1000000000000) ≤ (1440057 / 250000000) := by
  have h := checkLog_sound (w := (5743669369 / 1994256330631)) (n := 12)
    (lo := (5760227 / 1000000000)) (hi := (1440057 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 994256330631) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 994256330631) = 1/(994256330631 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_110 : Bounds (-1440057 / 250000000) (-5760227 / 1000000000) (Real.log (994256330631 / 1000000000000)) := by
  have h := reflection_log_110_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_111_neg : (2864737 / 500000000) ≤ -Real.log (39771476311 / 40000000000) ∧
    -Real.log (39771476311 / 40000000000) ≤ (229179 / 40000000) := by
  have h := checkLog_sound (w := (228523689 / 79771476311)) (n := 12)
    (lo := (2864737 / 500000000)) (hi := (229179 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39771476311) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39771476311) = 1/(39771476311 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_111 : Bounds (-229179 / 40000000) (-2864737 / 500000000) (Real.log (39771476311 / 40000000000)) := by
  have h := reflection_log_111_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_112_neg : (151458873 / 1000000000) ≤ -Real.log (500000000000 / 581765224493) ∧
    -Real.log (500000000000 / 581765224493) ≤ (75729437 / 500000000) := by
  have h := checkLog_sound (w := (81765224493 / 1081765224493)) (n := 12)
    (lo := (151458873 / 1000000000)) (hi := (75729437 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((581765224493 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(581765224493 / 500000000000) = 1/(500000000000 / 581765224493) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_112 : Bounds (151458873 / 1000000000) (75729437 / 500000000) (Real.log (581765224493 / 500000000000)) := by
  have h := reflection_log_112_neg
  have he : Real.log (581765224493 / 500000000000) = -Real.log (500000000000 / 581765224493) := by
    rw [show ((581765224493 / 500000000000) : ℝ) = ((500000000000 / 581765224493) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_113_neg : (151865201 / 1000000000) ≤ -Real.log (500000000000 / 582001659791) ∧
    -Real.log (500000000000 / 582001659791) ≤ (75932601 / 500000000) := by
  have h := checkLog_sound (w := (82001659791 / 1082001659791)) (n := 12)
    (lo := (151865201 / 1000000000)) (hi := (75932601 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((582001659791 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(582001659791 / 500000000000) = 1/(500000000000 / 582001659791) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_113 : Bounds (151865201 / 1000000000) (75932601 / 500000000) (Real.log (582001659791 / 500000000000)) := by
  have h := reflection_log_113_neg
  have he : Real.log (582001659791 / 500000000000) = -Real.log (500000000000 / 582001659791) := by
    rw [show ((582001659791 / 500000000000) : ℝ) = ((500000000000 / 582001659791) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_114_neg : (303713251 / 1000000000) ≤ -Real.log (500000000000 / 677440244907) ∧
    -Real.log (500000000000 / 677440244907) ≤ (75928313 / 250000000) := by
  have h := checkLog_sound (w := (177440244907 / 1177440244907)) (n := 12)
    (lo := (303713251 / 1000000000)) (hi := (75928313 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((677440244907 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(677440244907 / 500000000000) = 1/(500000000000 / 677440244907) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_114 : Bounds (303713251 / 1000000000) (75928313 / 250000000) (Real.log (677440244907 / 500000000000)) := by
  have h := reflection_log_114_neg
  have he : Real.log (677440244907 / 500000000000) = -Real.log (500000000000 / 677440244907) := by
    rw [show ((677440244907 / 500000000000) : ℝ) = ((500000000000 / 677440244907) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_115_neg : (303917901 / 1000000000) ≤ -Real.log (500000000000 / 677578897787) ∧
    -Real.log (500000000000 / 677578897787) ≤ (151958951 / 500000000) := by
  have h := checkLog_sound (w := (177578897787 / 1177578897787)) (n := 12)
    (lo := (303917901 / 1000000000)) (hi := (151958951 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((677578897787 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(677578897787 / 500000000000) = 1/(500000000000 / 677578897787) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_115 : Bounds (303917901 / 1000000000) (151958951 / 500000000) (Real.log (677578897787 / 500000000000)) := by
  have h := reflection_log_115_neg
  have he : Real.log (677578897787 / 500000000000) = -Real.log (500000000000 / 677578897787) := by
    rw [show ((677578897787 / 500000000000) : ℝ) = ((500000000000 / 677578897787) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_116_neg : (35136061 / 250000000) ≤ -Real.log (10000 / 11509) ∧
    -Real.log (10000 / 11509) ≤ (28108849 / 200000000) := by
  have h := checkLog_sound (w := (1509 / 21509)) (n := 12)
    (lo := (35136061 / 250000000)) (hi := (28108849 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11509 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11509 / 10000) = 1/(10000 / 11509) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_116 : Bounds (35136061 / 250000000) (28108849 / 200000000) (Real.log (11509 / 10000)) := by
  have h := reflection_log_116_neg
  have he : Real.log (11509 / 10000) = -Real.log (10000 / 11509) := by
    rw [show ((11509 / 10000) : ℝ) = ((10000 / 11509) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_117_neg : (163578313 / 1000000000) ≤ -Real.log (8491 / 10000) ∧
    -Real.log (8491 / 10000) ≤ (81789157 / 500000000) := by
  have h := checkLog_sound (w := (1509 / 18491)) (n := 12)
    (lo := (163578313 / 1000000000)) (hi := (81789157 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8491) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8491) = 1/(8491 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_117 : Bounds (-81789157 / 500000000) (-163578313 / 1000000000) (Real.log (8491 / 10000)) := by
  have h := reflection_log_117_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_118_neg : (18861 / 125000000) ≤ -Real.log (10000000 / 10001509) ∧
    -Real.log (10000000 / 10001509) ≤ (150889 / 1000000000) := by
  have h := checkLog_sound (w := (1509 / 20001509)) (n := 12)
    (lo := (18861 / 125000000)) (hi := (150889 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001509 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001509 / 10000000) = 1/(10000000 / 10001509) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_118 : Bounds (18861 / 125000000) (150889 / 1000000000) (Real.log (10001509 / 10000000)) := by
  have h := reflection_log_118_neg
  have he : Real.log (10001509 / 10000000) = -Real.log (10000000 / 10001509) := by
    rw [show ((10001509 / 10000000) : ℝ) = ((10000000 / 10001509) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_119_neg : (150911 / 1000000000) ≤ -Real.log (9998491 / 10000000) ∧
    -Real.log (9998491 / 10000000) ≤ (1179 / 7812500) := by
  have h := checkLog_sound (w := (1509 / 19998491)) (n := 12)
    (lo := (150911 / 1000000000)) (hi := (1179 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998491) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998491) = 1/(9998491 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_119 : Bounds (-1179 / 7812500) (-150911 / 1000000000) (Real.log (9998491 / 10000000)) := by
  have h := reflection_log_119_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_120_neg : (36456057 / 500000000) ≤ -Real.log (250000 / 268909) ∧
    -Real.log (250000 / 268909) ≤ (14582423 / 200000000) := by
  have h := checkLog_sound (w := (18909 / 518909)) (n := 12)
    (lo := (36456057 / 500000000)) (hi := (14582423 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((268909 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(268909 / 250000) = 1/(250000 / 268909) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_120 : Bounds (36456057 / 500000000) (14582423 / 200000000) (Real.log (268909 / 250000)) := by
  have h := reflection_log_120_neg
  have he : Real.log (268909 / 250000) = -Real.log (250000 / 268909) := by
    rw [show ((268909 / 250000) : ℝ) = ((250000 / 268909) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_121_neg : (15729869 / 200000000) ≤ -Real.log (231091 / 250000) ∧
    -Real.log (231091 / 250000) ≤ (39324673 / 500000000) := by
  have h := checkLog_sound (w := (18909 / 481091)) (n := 12)
    (lo := (15729869 / 200000000)) (hi := (39324673 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 231091) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 231091) = 1/(231091 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_121 : Bounds (-39324673 / 500000000) (-15729869 / 200000000) (Real.log (231091 / 250000)) := by
  have h := reflection_log_121_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_122_neg : (18274973 / 250000000) ≤ -Real.log (500000 / 537919) ∧
    -Real.log (500000 / 537919) ≤ (73099893 / 1000000000) := by
  have h := checkLog_sound (w := (37919 / 1037919)) (n := 12)
    (lo := (18274973 / 250000000)) (hi := (73099893 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((537919 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(537919 / 500000) = 1/(500000 / 537919) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_122 : Bounds (18274973 / 250000000) (73099893 / 1000000000) (Real.log (537919 / 500000)) := by
  have h := reflection_log_122_neg
  have he : Real.log (537919 / 500000) = -Real.log (500000 / 537919) := by
    rw [show ((537919 / 500000) : ℝ) = ((500000 / 537919) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_123_neg : (39433949 / 500000000) ≤ -Real.log (462081 / 500000) ∧
    -Real.log (462081 / 500000) ≤ (78867899 / 1000000000) := by
  have h := checkLog_sound (w := (37919 / 962081)) (n := 12)
    (lo := (39433949 / 500000000)) (hi := (78867899 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 462081) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 462081) = 1/(462081 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_123 : Bounds (-78867899 / 1000000000) (-39433949 / 500000000) (Real.log (462081 / 500000)) := by
  have h := reflection_log_123_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_124_neg : (1153601 / 200000000) ≤ -Real.log (248562149439 / 250000000000) ∧
    -Real.log (248562149439 / 250000000000) ≤ (2884003 / 500000000) := by
  have h := checkLog_sound (w := (1437850561 / 498562149439)) (n := 12)
    (lo := (1153601 / 200000000)) (hi := (2884003 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248562149439) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248562149439) = 1/(248562149439 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_124 : Bounds (-2884003 / 500000000) (-1153601 / 200000000) (Real.log (248562149439 / 250000000000)) := by
  have h := reflection_log_124_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_125_neg : (573723 / 100000000) ≤ -Real.log (62142449719 / 62500000000) ∧
    -Real.log (62142449719 / 62500000000) ≤ (5737231 / 1000000000) := by
  have h := checkLog_sound (w := (357550281 / 124642449719)) (n := 12)
    (lo := (573723 / 100000000)) (hi := (5737231 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 62142449719) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 62142449719) = 1/(62142449719 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_125 : Bounds (-5737231 / 1000000000) (-573723 / 100000000) (Real.log (62142449719 / 62500000000)) := by
  have h := reflection_log_125_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_126_neg : (7578073 / 50000000) ≤ -Real.log (250000000000 / 290912454401) ∧
    -Real.log (250000000000 / 290912454401) ≤ (151561461 / 1000000000) := by
  have h := checkLog_sound (w := (40912454401 / 540912454401)) (n := 12)
    (lo := (7578073 / 50000000)) (hi := (151561461 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((290912454401 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(290912454401 / 250000000000) = 1/(250000000000 / 290912454401) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_126 : Bounds (7578073 / 50000000) (151561461 / 1000000000) (Real.log (290912454401 / 250000000000)) := by
  have h := reflection_log_126_neg
  have he : Real.log (290912454401 / 250000000000) = -Real.log (250000000000 / 290912454401) := by
    rw [show ((290912454401 / 250000000000) : ℝ) = ((250000000000 / 290912454401) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_127_neg : (15196779 / 100000000) ≤ -Real.log (500000000000 / 582061370193) ∧
    -Real.log (500000000000 / 582061370193) ≤ (151967791 / 1000000000) := by
  have h := checkLog_sound (w := (82061370193 / 1082061370193)) (n := 12)
    (lo := (15196779 / 100000000)) (hi := (151967791 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((582061370193 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(582061370193 / 500000000000) = 1/(500000000000 / 582061370193) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_127 : Bounds (15196779 / 100000000) (151967791 / 1000000000) (Real.log (582061370193 / 500000000000)) := by
  have h := reflection_log_127_neg
  have he : Real.log (582061370193 / 500000000000) = -Real.log (500000000000 / 582061370193) := by
    rw [show ((582061370193 / 500000000000) : ℝ) = ((500000000000 / 582061370193) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily
