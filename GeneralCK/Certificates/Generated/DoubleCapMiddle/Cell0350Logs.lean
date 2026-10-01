import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0350
open GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed

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

theorem reflection_log_1_neg : (212145797 / 1000000000) ≤ -Real.log (512 / 633) ∧
    -Real.log (512 / 633) ≤ (106072899 / 500000000) := by
  have h := checkLog_sound (w := (121 / 1145)) (n := 12)
    (lo := (212145797 / 1000000000)) (hi := (106072899 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((633 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(633 / 512) = 1/(512 / 633) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (212145797 / 1000000000) (106072899 / 500000000) (Real.log (633 / 512)) := by
  have h := reflection_log_1_neg
  have he : Real.log (633 / 512) = -Real.log (512 / 633) := by
    rw [show ((633 / 512) : ℝ) = ((512 / 633) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (53923413 / 200000000) ≤ -Real.log (391 / 512) ∧
    -Real.log (391 / 512) ≤ (134808533 / 500000000) := by
  have h := checkLog_sound (w := (121 / 903)) (n := 12)
    (lo := (53923413 / 200000000)) (hi := (134808533 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 391) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 391) = 1/(391 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-134808533 / 500000000) (-53923413 / 200000000) (Real.log (391 / 512)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (105954401 / 500000000) ≤ -Real.log (10240 / 12657) ∧
    -Real.log (10240 / 12657) ≤ (211908803 / 1000000000) := by
  have h := checkLog_sound (w := (2417 / 22897)) (n := 12)
    (lo := (105954401 / 500000000)) (hi := (211908803 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12657 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12657 / 10240) = 1/(10240 / 12657) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (105954401 / 500000000) (211908803 / 1000000000) (Real.log (12657 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12657 / 10240) = -Real.log (10240 / 12657) := by
    rw [show ((12657 / 10240) : ℝ) = ((10240 / 12657) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (134616753 / 500000000) ≤ -Real.log (7823 / 10240) ∧
    -Real.log (7823 / 10240) ≤ (269233507 / 1000000000) := by
  have h := checkLog_sound (w := (2417 / 18063)) (n := 12)
    (lo := (134616753 / 500000000)) (hi := (269233507 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7823) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7823) = 1/(7823 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-269233507 / 1000000000) (-134616753 / 500000000) (Real.log (7823 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (193533871 / 500000000) ≤ -Real.log (256 / 377) ∧
    -Real.log (256 / 377) ≤ (387067743 / 1000000000) := by
  have h := checkLog_sound (w := (121 / 633)) (n := 12)
    (lo := (193533871 / 500000000)) (hi := (387067743 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((377 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(377 / 256) = 1/(256 / 377) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (193533871 / 500000000) (387067743 / 1000000000) (Real.log (377 / 256)) := by
  have h := reflection_log_5_neg
  have he : Real.log (377 / 256) = -Real.log (256 / 377) := by
    rw [show ((377 / 256) : ℝ) = ((256 / 377) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (319951333 / 500000000) ≤ -Real.log (135 / 256) ∧
    -Real.log (135 / 256) ≤ (639902667 / 1000000000) := by
  have h := checkLog_sound (w := (121 / 391)) (n := 12)
    (lo := (319951333 / 500000000)) (hi := (639902667 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((256 / 135) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(256 / 135) = 1/(135 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-639902667 / 1000000000) (-319951333 / 500000000) (Real.log (135 / 256)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (77333957 / 200000000) ≤ -Real.log (5120 / 7537) ∧
    -Real.log (5120 / 7537) ≤ (193334893 / 500000000) := by
  have h := checkLog_sound (w := (2417 / 12657)) (n := 12)
    (lo := (77333957 / 200000000)) (hi := (193334893 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7537 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7537 / 5120) = 1/(5120 / 7537) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (77333957 / 200000000) (193334893 / 500000000) (Real.log (7537 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (7537 / 5120) = -Real.log (5120 / 7537) := by
    rw [show ((7537 / 5120) : ℝ) = ((5120 / 7537) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (638792171 / 1000000000) ≤ -Real.log (2703 / 5120) ∧
    -Real.log (2703 / 5120) ≤ (159698043 / 250000000) := by
  have h := checkLog_sound (w := (2417 / 7823)) (n := 12)
    (lo := (638792171 / 1000000000)) (hi := (159698043 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2703) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2703) = 1/(2703 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-159698043 / 250000000) (-638792171 / 1000000000) (Real.log (2703 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (145299781 / 500000000) ≤ -Real.log (1000000 / 1337229) ∧
    -Real.log (1000000 / 1337229) ≤ (290599563 / 1000000000) := by
  have h := checkLog_sound (w := (337229 / 2337229)) (n := 12)
    (lo := (145299781 / 500000000)) (hi := (290599563 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1337229 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1337229 / 1000000) = 1/(1000000 / 1337229) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (145299781 / 500000000) (290599563 / 1000000000) (Real.log (1337229 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1337229 / 1000000) = -Real.log (1000000 / 1337229) := by
    rw [show ((1337229 / 1000000) : ℝ) = ((1000000 / 1337229) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (102831437 / 250000000) ≤ -Real.log (662771 / 1000000) ∧
    -Real.log (662771 / 1000000) ≤ (411325749 / 1000000000) := by
  have h := checkLog_sound (w := (337229 / 1662771)) (n := 12)
    (lo := (102831437 / 250000000)) (hi := (411325749 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 662771) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 662771) = 1/(662771 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-411325749 / 1000000000) (-102831437 / 250000000) (Real.log (662771 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (290920323 / 1000000000) ≤ -Real.log (500000 / 668829) ∧
    -Real.log (500000 / 668829) ≤ (72730081 / 250000000) := by
  have h := checkLog_sound (w := (168829 / 1168829)) (n := 12)
    (lo := (290920323 / 1000000000)) (hi := (72730081 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((668829 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(668829 / 500000) = 1/(500000 / 668829) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (290920323 / 1000000000) (72730081 / 250000000) (Real.log (668829 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (668829 / 500000) = -Real.log (500000 / 668829) := by
    rw [show ((668829 / 500000) : ℝ) = ((500000 / 668829) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (10299331 / 25000000) ≤ -Real.log (331171 / 500000) ∧
    -Real.log (331171 / 500000) ≤ (411973241 / 1000000000) := by
  have h := checkLog_sound (w := (168829 / 831171)) (n := 12)
    (lo := (10299331 / 25000000)) (hi := (411973241 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 331171) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 331171) = 1/(331171 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-411973241 / 1000000000) (-10299331 / 25000000) (Real.log (331171 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (44020747 / 200000000) ≤ -Real.log (500000 / 623103) ∧
    -Real.log (500000 / 623103) ≤ (27512967 / 125000000) := by
  have h := checkLog_sound (w := (123103 / 1123103)) (n := 12)
    (lo := (44020747 / 200000000)) (hi := (27512967 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((623103 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(623103 / 500000) = 1/(500000 / 623103) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (44020747 / 200000000) (27512967 / 125000000) (Real.log (623103 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (623103 / 500000) = -Real.log (500000 / 623103) := by
    rw [show ((623103 / 500000) : ℝ) = ((500000 / 623103) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (282636157 / 1000000000) ≤ -Real.log (376897 / 500000) ∧
    -Real.log (376897 / 500000) ≤ (141318079 / 500000000) := by
  have h := checkLog_sound (w := (123103 / 876897)) (n := 12)
    (lo := (282636157 / 1000000000)) (hi := (141318079 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 376897) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 376897) = 1/(376897 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-141318079 / 500000000) (-282636157 / 1000000000) (Real.log (376897 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (220370911 / 1000000000) ≤ -Real.log (1000000 / 1246539) ∧
    -Real.log (1000000 / 1246539) ≤ (6886591 / 31250000) := by
  have h := checkLog_sound (w := (246539 / 2246539)) (n := 12)
    (lo := (220370911 / 1000000000)) (hi := (6886591 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1246539 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1246539 / 1000000) = 1/(1000000 / 1246539) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (220370911 / 1000000000) (6886591 / 31250000) (Real.log (1246539 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1246539 / 1000000) = -Real.log (1000000 / 1246539) := by
    rw [show ((1246539 / 1000000) : ℝ) = ((1000000 / 1246539) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (14153901 / 50000000) ≤ -Real.log (753461 / 1000000) ∧
    -Real.log (753461 / 1000000) ≤ (283078021 / 1000000000) := by
  have h := checkLog_sound (w := (246539 / 1753461)) (n := 12)
    (lo := (14153901 / 50000000)) (hi := (283078021 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 753461) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 753461) = 1/(753461 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-283078021 / 1000000000) (-14153901 / 50000000) (Real.log (753461 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (70192531 / 100000000) ≤ -Real.log (1250000000 / 2522041927) ∧
    -Real.log (1250000000 / 2522041927) ≤ (10967583 / 15625000) := by
  have h := checkLog_sound (w := (22041927 / 5022041927)) (n := 12)
    (lo := (877813 / 100000000)) (hi := (8778131 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2522041927 / 2500000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(2522041927 / 2500000000) = 1/(1250000000 / 2522041927) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (70192531 / 100000000) (10967583 / 15625000) (Real.log (2522041927 / 1250000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (2522041927 / 1250000000) = -Real.log (1250000000 / 2522041927) := by
    rw [show ((2522041927 / 1250000000) : ℝ) = ((1250000000 / 2522041927) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (702893563 / 1000000000) ≤ -Real.log (250000000000 / 504897016949) ∧
    -Real.log (250000000000 / 504897016949) ≤ (140578713 / 200000000) := by
  have h := checkLog_sound (w := (4897016949 / 1004897016949)) (n := 12)
    (lo := (9746383 / 1000000000)) (hi := (609149 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((504897016949 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(504897016949 / 500000000000) = 1/(250000000000 / 504897016949) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (702893563 / 1000000000) (140578713 / 200000000) (Real.log (504897016949 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (504897016949 / 250000000000) = -Real.log (250000000000 / 504897016949) := by
    rw [show ((504897016949 / 250000000000) : ℝ) = ((250000000000 / 504897016949) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (502739893 / 1000000000) ≤ -Real.log (100000000000 / 165324478571) ∧
    -Real.log (100000000000 / 165324478571) ≤ (251369947 / 500000000) := by
  have h := checkLog_sound (w := (65324478571 / 265324478571)) (n := 12)
    (lo := (502739893 / 1000000000)) (hi := (251369947 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((165324478571 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(165324478571 / 100000000000) = 1/(100000000000 / 165324478571) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (502739893 / 1000000000) (251369947 / 500000000) (Real.log (165324478571 / 100000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (165324478571 / 100000000000) = -Real.log (100000000000 / 165324478571) := by
    rw [show ((165324478571 / 100000000000) : ℝ) = ((100000000000 / 165324478571) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (503448931 / 1000000000) ≤ -Real.log (500000000000 / 827208707551) ∧
    -Real.log (500000000000 / 827208707551) ≤ (125862233 / 250000000) := by
  have h := checkLog_sound (w := (327208707551 / 1327208707551)) (n := 12)
    (lo := (503448931 / 1000000000)) (hi := (125862233 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((827208707551 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(827208707551 / 500000000000) = 1/(500000000000 / 827208707551) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (503448931 / 1000000000) (125862233 / 250000000) (Real.log (827208707551 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (827208707551 / 500000000000) = -Real.log (500000000000 / 827208707551) := by
    rw [show ((827208707551 / 500000000000) : ℝ) = ((500000000000 / 827208707551) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0350
