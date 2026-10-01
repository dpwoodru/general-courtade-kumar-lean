import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell110
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed GeneralCK.Reflection

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

theorem reflection_log_1_neg : (27386637 / 100000000) ≤ -Real.log (5120 / 6733) ∧
    -Real.log (5120 / 6733) ≤ (273866371 / 1000000000) := by
  have h := checkLog_sound (w := (1613 / 11853)) (n := 12)
    (lo := (27386637 / 100000000)) (hi := (273866371 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6733 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6733 / 5120) = 1/(5120 / 6733) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (27386637 / 100000000) (273866371 / 1000000000) (Real.log (6733 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6733 / 5120) = -Real.log (5120 / 6733) := by
    rw [show ((6733 / 5120) : ℝ) = ((5120 / 6733) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (378393467 / 1000000000) ≤ -Real.log (3507 / 5120) ∧
    -Real.log (3507 / 5120) ≤ (94598367 / 250000000) := by
  have h := checkLog_sound (w := (1613 / 8627)) (n := 12)
    (lo := (378393467 / 1000000000)) (hi := (94598367 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3507) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3507) = 1/(3507 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-94598367 / 250000000) (-378393467 / 1000000000) (Real.log (3507 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (8544397 / 31250000) ≤ -Real.log (512 / 673) ∧
    -Real.log (512 / 673) ≤ (54684141 / 200000000) := by
  have h := checkLog_sound (w := (161 / 1185)) (n := 12)
    (lo := (8544397 / 31250000)) (hi := (54684141 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((673 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(673 / 512) = 1/(512 / 673) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (8544397 / 31250000) (54684141 / 200000000) (Real.log (673 / 512)) := by
  have h := reflection_log_3_neg
  have he : Real.log (673 / 512) = -Real.log (512 / 673) := by
    rw [show ((673 / 512) : ℝ) = ((512 / 673) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (377538401 / 1000000000) ≤ -Real.log (351 / 512) ∧
    -Real.log (351 / 512) ≤ (188769201 / 500000000) := by
  have h := checkLog_sound (w := (161 / 863)) (n := 12)
    (lo := (377538401 / 1000000000)) (hi := (188769201 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 351) = 1/(351 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-188769201 / 500000000) (-377538401 / 1000000000) (Real.log (351 / 512)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (201557847 / 1000000000) ≤ -Real.log (1000000 / 1223307) ∧
    -Real.log (1000000 / 1223307) ≤ (25194731 / 125000000) := by
  have h := checkLog_sound (w := (223307 / 2223307)) (n := 12)
    (lo := (201557847 / 1000000000)) (hi := (25194731 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1223307 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1223307 / 1000000) = 1/(1000000 / 1223307) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (201557847 / 1000000000) (25194731 / 125000000) (Real.log (1223307 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1223307 / 1000000) = -Real.log (1000000 / 1223307) := by
    rw [show ((1223307 / 1000000) : ℝ) = ((1000000 / 1223307) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (63177529 / 250000000) ≤ -Real.log (776693 / 1000000) ∧
    -Real.log (776693 / 1000000) ≤ (252710117 / 1000000000) := by
  have h := checkLog_sound (w := (223307 / 1776693)) (n := 12)
    (lo := (63177529 / 250000000)) (hi := (252710117 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 776693) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 776693) = 1/(776693 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-252710117 / 1000000000) (-63177529 / 250000000) (Real.log (776693 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (201901937 / 1000000000) ≤ -Real.log (62500 / 76483) ∧
    -Real.log (62500 / 76483) ≤ (100950969 / 500000000) := by
  have h := checkLog_sound (w := (13983 / 138983)) (n := 12)
    (lo := (201901937 / 1000000000)) (hi := (100950969 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((76483 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(76483 / 62500) = 1/(62500 / 76483) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (201901937 / 1000000000) (100950969 / 500000000) (Real.log (76483 / 62500)) := by
  have h := reflection_log_7_neg
  have he : Real.log (76483 / 62500) = -Real.log (62500 / 76483) := by
    rw [show ((76483 / 62500) : ℝ) = ((62500 / 76483) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (15828269 / 62500000) ≤ -Real.log (48517 / 62500) ∧
    -Real.log (48517 / 62500) ≤ (50650461 / 200000000) := by
  have h := checkLog_sound (w := (13983 / 111017)) (n := 12)
    (lo := (15828269 / 62500000)) (hi := (50650461 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 48517) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 48517) = 1/(48517 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-50650461 / 200000000) (-15828269 / 62500000) (Real.log (48517 / 62500)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (37129569 / 250000000) ≤ -Real.log (500000 / 580057) ∧
    -Real.log (500000 / 580057) ≤ (148518277 / 1000000000) := by
  have h := checkLog_sound (w := (80057 / 1080057)) (n := 12)
    (lo := (37129569 / 250000000)) (hi := (148518277 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((580057 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(580057 / 500000) = 1/(500000 / 580057) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (37129569 / 250000000) (148518277 / 1000000000) (Real.log (580057 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (580057 / 500000) = -Real.log (500000 / 580057) := by
    rw [show ((580057 / 500000) : ℝ) = ((500000 / 580057) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (17448911 / 100000000) ≤ -Real.log (419943 / 500000) ∧
    -Real.log (419943 / 500000) ≤ (174489111 / 1000000000) := by
  have h := checkLog_sound (w := (80057 / 919943)) (n := 12)
    (lo := (17448911 / 100000000)) (hi := (174489111 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 419943) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 419943) = 1/(419943 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-174489111 / 1000000000) (-17448911 / 100000000) (Real.log (419943 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (148786317 / 1000000000) ≤ -Real.log (40000 / 46417) ∧
    -Real.log (40000 / 46417) ≤ (74393159 / 500000000) := by
  have h := checkLog_sound (w := (6417 / 86417)) (n := 12)
    (lo := (148786317 / 1000000000)) (hi := (74393159 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((46417 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(46417 / 40000) = 1/(40000 / 46417) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (148786317 / 1000000000) (74393159 / 500000000) (Real.log (46417 / 40000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (46417 / 40000) = -Real.log (40000 / 46417) := by
    rw [show ((46417 / 40000) : ℝ) = ((40000 / 46417) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (174859467 / 1000000000) ≤ -Real.log (33583 / 40000) ∧
    -Real.log (33583 / 40000) ≤ (43714867 / 250000000) := by
  have h := checkLog_sound (w := (6417 / 73583)) (n := 12)
    (lo := (174859467 / 1000000000)) (hi := (43714867 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000 / 33583) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000 / 33583) = 1/(33583 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-43714867 / 250000000) (-174859467 / 1000000000) (Real.log (33583 / 40000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (325479553 / 500000000) ≤ -Real.log (500000000000 / 958689458689) ∧
    -Real.log (500000000000 / 958689458689) ≤ (650959107 / 1000000000) := by
  have h := checkLog_sound (w := (458689458689 / 1458689458689)) (n := 12)
    (lo := (325479553 / 500000000)) (hi := (650959107 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((958689458689 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(958689458689 / 500000000000) = 1/(500000000000 / 958689458689) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (325479553 / 500000000) (650959107 / 1000000000) (Real.log (958689458689 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (958689458689 / 500000000000) = -Real.log (500000000000 / 958689458689) := by
    rw [show ((958689458689 / 500000000000) : ℝ) = ((500000000000 / 958689458689) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (326129919 / 500000000) ≤ -Real.log (500000000000 / 959937268321) ∧
    -Real.log (500000000000 / 959937268321) ≤ (652259839 / 1000000000) := by
  have h := checkLog_sound (w := (459937268321 / 1459937268321)) (n := 12)
    (lo := (326129919 / 500000000)) (hi := (652259839 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((959937268321 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(959937268321 / 500000000000) = 1/(500000000000 / 959937268321) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (326129919 / 500000000) (652259839 / 1000000000) (Real.log (959937268321 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (959937268321 / 500000000000) = -Real.log (500000000000 / 959937268321) := by
    rw [show ((959937268321 / 500000000000) : ℝ) = ((500000000000 / 959937268321) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (454267963 / 1000000000) ≤ -Real.log (62500000000 / 98438749287) ∧
    -Real.log (62500000000 / 98438749287) ≤ (113566991 / 250000000) := by
  have h := checkLog_sound (w := (35938749287 / 160938749287)) (n := 12)
    (lo := (454267963 / 1000000000)) (hi := (113566991 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((98438749287 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(98438749287 / 62500000000) = 1/(62500000000 / 98438749287) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (454267963 / 1000000000) (113566991 / 250000000) (Real.log (98438749287 / 62500000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (98438749287 / 62500000000) = -Real.log (62500000000 / 98438749287) := by
    rw [show ((98438749287 / 62500000000) : ℝ) = ((62500000000 / 98438749287) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (455154241 / 1000000000) ≤ -Real.log (5000000000 / 7882082569) ∧
    -Real.log (5000000000 / 7882082569) ≤ (227577121 / 500000000) := by
  have h := checkLog_sound (w := (2882082569 / 12882082569)) (n := 12)
    (lo := (455154241 / 1000000000)) (hi := (227577121 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7882082569 / 5000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7882082569 / 5000000000) = 1/(5000000000 / 7882082569) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (455154241 / 1000000000) (227577121 / 500000000) (Real.log (7882082569 / 5000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (7882082569 / 5000000000) = -Real.log (5000000000 / 7882082569) := by
    rw [show ((7882082569 / 5000000000) : ℝ) = ((5000000000 / 7882082569) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (161503693 / 500000000) ≤ -Real.log (500000000000 / 690637777031) ∧
    -Real.log (500000000000 / 690637777031) ≤ (323007387 / 1000000000) := by
  have h := checkLog_sound (w := (190637777031 / 1190637777031)) (n := 12)
    (lo := (161503693 / 500000000)) (hi := (323007387 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((690637777031 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(690637777031 / 500000000000) = 1/(500000000000 / 690637777031) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (161503693 / 500000000) (323007387 / 1000000000) (Real.log (690637777031 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (690637777031 / 500000000000) = -Real.log (500000000000 / 690637777031) := by
    rw [show ((690637777031 / 500000000000) : ℝ) = ((500000000000 / 690637777031) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (40455723 / 125000000) ≤ -Real.log (500000000000 / 691078819641) ∧
    -Real.log (500000000000 / 691078819641) ≤ (64729157 / 200000000) := by
  have h := checkLog_sound (w := (191078819641 / 1191078819641)) (n := 12)
    (lo := (40455723 / 125000000)) (hi := (64729157 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((691078819641 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(691078819641 / 500000000000) = 1/(500000000000 / 691078819641) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (40455723 / 125000000) (64729157 / 200000000) (Real.log (691078819641 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (691078819641 / 500000000000) = -Real.log (500000000000 / 691078819641) := by
    rw [show ((691078819641 / 500000000000) : ℝ) = ((500000000000 / 691078819641) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (521463 / 20000000) ≤ -Real.log (1558822111 / 1600000000) ∧
    -Real.log (1558822111 / 1600000000) ≤ (26073151 / 1000000000) := by
  have h := checkLog_sound (w := (41177889 / 3158822111)) (n := 12)
    (lo := (521463 / 20000000)) (hi := (26073151 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600000000 / 1558822111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1600000000 / 1558822111) = 1/(1558822111 / 1600000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-26073151 / 1000000000) (-521463 / 20000000) (Real.log (1558822111 / 1600000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (12985417 / 500000000) ≤ -Real.log (243590876751 / 250000000000) ∧
    -Real.log (243590876751 / 250000000000) ≤ (5194167 / 200000000) := by
  have h := checkLog_sound (w := (6409123249 / 493590876751)) (n := 12)
    (lo := (12985417 / 500000000)) (hi := (5194167 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 243590876751) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 243590876751) = 1/(243590876751 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-5194167 / 200000000) (-12985417 / 500000000) (Real.log (243590876751 / 250000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell110
