import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0264
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

theorem reflection_log_1_neg : (14780723 / 62500000) ≤ -Real.log (2560 / 3243) ∧
    -Real.log (2560 / 3243) ≤ (236491569 / 1000000000) := by
  have h := checkLog_sound (w := (683 / 5803)) (n := 12)
    (lo := (14780723 / 62500000)) (hi := (236491569 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3243 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3243 / 2560) = 1/(2560 / 3243) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (14780723 / 62500000) (236491569 / 1000000000) (Real.log (3243 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3243 / 2560) = -Real.log (2560 / 3243) := by
    rw [show ((3243 / 2560) : ℝ) = ((2560 / 3243) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (124133 / 400000) ≤ -Real.log (1877 / 2560) ∧
    -Real.log (1877 / 2560) ≤ (310332501 / 1000000000) := by
  have h := checkLog_sound (w := (683 / 4437)) (n := 12)
    (lo := (124133 / 400000)) (hi := (310332501 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1877) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1877) = 1/(1877 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-310332501 / 1000000000) (-124133 / 400000) (Real.log (1877 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (236028927 / 1000000000) ≤ -Real.log (5120 / 6483) ∧
    -Real.log (5120 / 6483) ≤ (460994 / 1953125) := by
  have h := checkLog_sound (w := (1363 / 11603)) (n := 12)
    (lo := (236028927 / 1000000000)) (hi := (460994 / 1953125))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6483 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6483 / 5120) = 1/(5120 / 6483) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (236028927 / 1000000000) (460994 / 1953125) (Real.log (6483 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6483 / 5120) = -Real.log (5120 / 6483) := by
    rw [show ((6483 / 5120) : ℝ) = ((5120 / 6483) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (38691709 / 125000000) ≤ -Real.log (3757 / 5120) ∧
    -Real.log (3757 / 5120) ≤ (309533673 / 1000000000) := by
  have h := checkLog_sound (w := (1363 / 8877)) (n := 12)
    (lo := (38691709 / 125000000)) (hi := (309533673 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3757) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3757) = 1/(3757 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-309533673 / 1000000000) (-38691709 / 125000000) (Real.log (3757 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (427613837 / 1000000000) ≤ -Real.log (1280 / 1963) ∧
    -Real.log (1280 / 1963) ≤ (213806919 / 500000000) := by
  have h := checkLog_sound (w := (683 / 3243)) (n := 12)
    (lo := (427613837 / 1000000000)) (hi := (213806919 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1963 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1963 / 1280) = 1/(1280 / 1963) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (427613837 / 1000000000) (213806919 / 500000000) (Real.log (1963 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1963 / 1280) = -Real.log (1280 / 1963) := by
    rw [show ((1963 / 1280) : ℝ) = ((1280 / 1963) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (381349121 / 500000000) ≤ -Real.log (597 / 1280) ∧
    -Real.log (597 / 1280) ≤ (190674561 / 250000000) := by
  have h := checkLog_sound (w := (43 / 1237)) (n := 12)
    (lo := (34775531 / 500000000)) (hi := (69551063 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 597) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 597) = 1/(597 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-190674561 / 250000000) (-381349121 / 500000000) (Real.log (597 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (3334761 / 7812500) ≤ -Real.log (2560 / 3923) ∧
    -Real.log (2560 / 3923) ≤ (426849409 / 1000000000) := by
  have h := checkLog_sound (w := (1363 / 6483)) (n := 12)
    (lo := (3334761 / 7812500)) (hi := (426849409 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3923 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3923 / 2560) = 1/(2560 / 3923) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (3334761 / 7812500) (426849409 / 1000000000) (Real.log (3923 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (3923 / 2560) = -Real.log (2560 / 3923) := by
    rw [show ((3923 / 2560) : ℝ) = ((2560 / 3923) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (760188831 / 1000000000) ≤ -Real.log (1197 / 2560) ∧
    -Real.log (1197 / 2560) ≤ (760188833 / 1000000000) := by
  have h := checkLog_sound (w := (83 / 2477)) (n := 12)
    (lo := (67041651 / 1000000000)) (hi := (16760413 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 1197) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 1197) = 1/(1197 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-760188833 / 1000000000) (-760188831 / 1000000000) (Real.log (1197 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (323203161 / 1000000000) ≤ -Real.log (500000 / 690773) ∧
    -Real.log (500000 / 690773) ≤ (161601581 / 500000000) := by
  have h := checkLog_sound (w := (190773 / 1190773)) (n := 12)
    (lo := (323203161 / 1000000000)) (hi := (161601581 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((690773 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(690773 / 500000) = 1/(500000 / 690773) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (323203161 / 1000000000) (161601581 / 500000000) (Real.log (690773 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (690773 / 500000) = -Real.log (500000 / 690773) := by
    rw [show ((690773 / 500000) : ℝ) = ((500000 / 690773) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (480532463 / 1000000000) ≤ -Real.log (309227 / 500000) ∧
    -Real.log (309227 / 500000) ≤ (30033279 / 62500000) := by
  have h := checkLog_sound (w := (190773 / 809227)) (n := 12)
    (lo := (480532463 / 1000000000)) (hi := (30033279 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 309227) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 309227) = 1/(309227 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-30033279 / 62500000) (-480532463 / 1000000000) (Real.log (309227 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (323829799 / 1000000000) ≤ -Real.log (250000 / 345603) ∧
    -Real.log (250000 / 345603) ≤ (1619149 / 5000000) := by
  have h := checkLog_sound (w := (95603 / 595603)) (n := 12)
    (lo := (323829799 / 1000000000)) (hi := (1619149 / 5000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((345603 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(345603 / 250000) = 1/(250000 / 345603) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (323829799 / 1000000000) (1619149 / 5000000) (Real.log (345603 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (345603 / 250000) = -Real.log (250000 / 345603) := by
    rw [show ((345603 / 250000) : ℝ) = ((250000 / 345603) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (48193371 / 100000000) ≤ -Real.log (154397 / 250000) ∧
    -Real.log (154397 / 250000) ≤ (481933711 / 1000000000) := by
  have h := checkLog_sound (w := (95603 / 404397)) (n := 12)
    (lo := (48193371 / 100000000)) (hi := (481933711 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 154397) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 154397) = 1/(154397 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-481933711 / 1000000000) (-48193371 / 100000000) (Real.log (154397 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (24772767 / 100000000) ≤ -Real.log (1000000 / 1281111) ∧
    -Real.log (1000000 / 1281111) ≤ (247727671 / 1000000000) := by
  have h := checkLog_sound (w := (281111 / 2281111)) (n := 12)
    (lo := (24772767 / 100000000)) (hi := (247727671 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1281111 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1281111 / 1000000) = 1/(1000000 / 1281111) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (24772767 / 100000000) (247727671 / 1000000000) (Real.log (1281111 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1281111 / 1000000) = -Real.log (1000000 / 1281111) := by
    rw [show ((1281111 / 1000000) : ℝ) = ((1000000 / 1281111) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (165024157 / 500000000) ≤ -Real.log (718889 / 1000000) ∧
    -Real.log (718889 / 1000000) ≤ (66009663 / 200000000) := by
  have h := checkLog_sound (w := (281111 / 1718889)) (n := 12)
    (lo := (165024157 / 500000000)) (hi := (66009663 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 718889) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 718889) = 1/(718889 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-66009663 / 200000000) (-165024157 / 500000000) (Real.log (718889 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (1551673 / 6250000) ≤ -Real.log (1000000 / 1281803) ∧
    -Real.log (1000000 / 1281803) ≤ (248267681 / 1000000000) := by
  have h := checkLog_sound (w := (281803 / 2281803)) (n := 12)
    (lo := (1551673 / 6250000)) (hi := (248267681 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1281803 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1281803 / 1000000) = 1/(1000000 / 1281803) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (1551673 / 6250000) (248267681 / 1000000000) (Real.log (1281803 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1281803 / 1000000) = -Real.log (1000000 / 1281803) := by
    rw [show ((1281803 / 1000000) : ℝ) = ((1000000 / 1281803) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (165505687 / 500000000) ≤ -Real.log (718197 / 1000000) ∧
    -Real.log (718197 / 1000000) ≤ (2648091 / 8000000) := by
  have h := checkLog_sound (w := (281803 / 1718197)) (n := 12)
    (lo := (165505687 / 500000000)) (hi := (2648091 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 718197) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 718197) = 1/(718197 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-2648091 / 8000000) (-165505687 / 500000000) (Real.log (718197 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (100466953 / 125000000) ≤ -Real.log (125000000000 / 279233782949) ∧
    -Real.log (125000000000 / 279233782949) ≤ (401867813 / 500000000) := by
  have h := checkLog_sound (w := (29233782949 / 529233782949)) (n := 12)
    (lo := (27647111 / 250000000)) (hi := (22117689 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((279233782949 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(279233782949 / 250000000000) = 1/(125000000000 / 279233782949) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (100466953 / 125000000) (401867813 / 500000000) (Real.log (279233782949 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (279233782949 / 125000000000) = -Real.log (125000000000 / 279233782949) := by
    rw [show ((279233782949 / 125000000000) : ℝ) = ((125000000000 / 279233782949) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (805763509 / 1000000000) ≤ -Real.log (125000000000 / 279800611411) ∧
    -Real.log (125000000000 / 279800611411) ≤ (805763511 / 1000000000) := by
  have h := checkLog_sound (w := (29800611411 / 529800611411)) (n := 12)
    (lo := (112616329 / 1000000000)) (hi := (11261633 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((279800611411 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(279800611411 / 250000000000) = 1/(125000000000 / 279800611411) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (805763509 / 1000000000) (805763511 / 1000000000) (Real.log (279800611411 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (279800611411 / 125000000000) = -Real.log (125000000000 / 279800611411) := by
    rw [show ((279800611411 / 125000000000) : ℝ) = ((125000000000 / 279800611411) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (36110999 / 62500000) ≤ -Real.log (62500000000 / 111379416711) ∧
    -Real.log (62500000000 / 111379416711) ≤ (115555197 / 200000000) := by
  have h := checkLog_sound (w := (48879416711 / 173879416711)) (n := 12)
    (lo := (36110999 / 62500000)) (hi := (115555197 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((111379416711 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(111379416711 / 62500000000) = 1/(62500000000 / 111379416711) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (36110999 / 62500000) (115555197 / 200000000) (Real.log (111379416711 / 62500000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (111379416711 / 62500000000) = -Real.log (62500000000 / 111379416711) := by
    rw [show ((111379416711 / 62500000000) : ℝ) = ((62500000000 / 111379416711) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (289639527 / 500000000) ≤ -Real.log (62500000000 / 111546953691) ∧
    -Real.log (62500000000 / 111546953691) ≤ (115855811 / 200000000) := by
  have h := checkLog_sound (w := (49046953691 / 174046953691)) (n := 12)
    (lo := (289639527 / 500000000)) (hi := (115855811 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((111546953691 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(111546953691 / 62500000000) = 1/(62500000000 / 111546953691) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (289639527 / 500000000) (115855811 / 200000000) (Real.log (111546953691 / 62500000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (111546953691 / 62500000000) = -Real.log (62500000000 / 111546953691) := by
    rw [show ((111546953691 / 62500000000) : ℝ) = ((62500000000 / 111546953691) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0264
