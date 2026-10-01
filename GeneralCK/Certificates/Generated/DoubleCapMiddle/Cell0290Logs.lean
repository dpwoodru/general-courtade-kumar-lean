import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0290
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

theorem reflection_log_1_neg : (113131839 / 500000000) ≤ -Real.log (256 / 321) ∧
    -Real.log (256 / 321) ≤ (226263679 / 1000000000) := by
  have h := checkLog_sound (w := (65 / 577)) (n := 12)
    (lo := (113131839 / 500000000)) (hi := (226263679 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((321 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(321 / 256) = 1/(256 / 321) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (113131839 / 500000000) (226263679 / 1000000000) (Real.log (321 / 256)) := by
  have h := reflection_log_1_neg
  have he : Real.log (321 / 256) = -Real.log (256 / 321) := by
    rw [show ((321 / 256) : ℝ) = ((256 / 321) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (18306501 / 62500000) ≤ -Real.log (191 / 256) ∧
    -Real.log (191 / 256) ≤ (292904017 / 1000000000) := by
  have h := checkLog_sound (w := (65 / 447)) (n := 12)
    (lo := (18306501 / 62500000)) (hi := (292904017 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((256 / 191) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(256 / 191) = 1/(191 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-292904017 / 1000000000) (-18306501 / 62500000) (Real.log (191 / 256)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (113015003 / 500000000) ≤ -Real.log (10240 / 12837) ∧
    -Real.log (10240 / 12837) ≤ (226030007 / 1000000000) := by
  have h := checkLog_sound (w := (2597 / 23077)) (n := 12)
    (lo := (113015003 / 500000000)) (hi := (226030007 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12837 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12837 / 10240) = 1/(10240 / 12837) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (113015003 / 500000000) (226030007 / 1000000000) (Real.log (12837 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12837 / 10240) = -Real.log (10240 / 12837) := by
    rw [show ((12837 / 10240) : ℝ) = ((10240 / 12837) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (292511423 / 1000000000) ≤ -Real.log (7643 / 10240) ∧
    -Real.log (7643 / 10240) ≤ (4570491 / 15625000) := by
  have h := checkLog_sound (w := (2597 / 17883)) (n := 12)
    (lo := (292511423 / 1000000000)) (hi := (4570491 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7643) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7643) = 1/(7643 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-4570491 / 15625000) (-292511423 / 1000000000) (Real.log (7643 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (102664981 / 250000000) ≤ -Real.log (128 / 193) ∧
    -Real.log (128 / 193) ≤ (16426397 / 40000000) := by
  have h := checkLog_sound (w := (65 / 321)) (n := 12)
    (lo := (102664981 / 250000000)) (hi := (16426397 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((193 / 128) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(193 / 128) = 1/(128 / 193) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (102664981 / 250000000) (16426397 / 40000000) (Real.log (193 / 128)) := by
  have h := reflection_log_5_neg
  have he : Real.log (193 / 128) = -Real.log (128 / 193) := by
    rw [show ((193 / 128) : ℝ) = ((128 / 193) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (44305971 / 62500000) ≤ -Real.log (63 / 128) ∧
    -Real.log (63 / 128) ≤ (354447769 / 500000000) := by
  have h := checkLog_sound (w := (1 / 127)) (n := 12)
    (lo := (3937089 / 250000000)) (hi := (15748357 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((64 / 63) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(64 / 63) = 1/(63 / 128) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-354447769 / 500000000) (-44305971 / 62500000) (Real.log (63 / 128)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (25641953 / 62500000) ≤ -Real.log (5120 / 7717) ∧
    -Real.log (5120 / 7717) ≤ (410271249 / 1000000000) := by
  have h := checkLog_sound (w := (2597 / 12837)) (n := 12)
    (lo := (25641953 / 62500000)) (hi := (410271249 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7717 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7717 / 5120) = 1/(5120 / 7717) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (25641953 / 62500000) (410271249 / 1000000000) (Real.log (7717 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (7717 / 5120) = -Real.log (5120 / 7717) := by
    rw [show ((7717 / 5120) : ℝ) = ((5120 / 7717) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (88463221 / 125000000) ≤ -Real.log (2523 / 5120) ∧
    -Real.log (2523 / 5120) ≤ (70770577 / 100000000) := by
  have h := checkLog_sound (w := (37 / 5083)) (n := 12)
    (lo := (3639647 / 250000000)) (hi := (14558589 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 2523) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(2560 / 2523) = 1/(2523 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-70770577 / 100000000) (-88463221 / 125000000) (Real.log (2523 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (309677881 / 1000000000) ≤ -Real.log (500000 / 681493) ∧
    -Real.log (500000 / 681493) ≤ (154838941 / 500000000) := by
  have h := checkLog_sound (w := (181493 / 1181493)) (n := 12)
    (lo := (309677881 / 1000000000)) (hi := (154838941 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((681493 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(681493 / 500000) = 1/(500000 / 681493) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (309677881 / 1000000000) (154838941 / 500000000) (Real.log (681493 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (681493 / 500000) = -Real.log (500000 / 681493) := by
    rw [show ((681493 / 500000) : ℝ) = ((500000 / 681493) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (90192729 / 200000000) ≤ -Real.log (318507 / 500000) ∧
    -Real.log (318507 / 500000) ≤ (225481823 / 500000000) := by
  have h := checkLog_sound (w := (181493 / 818507)) (n := 12)
    (lo := (90192729 / 200000000)) (hi := (225481823 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 318507) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 318507) = 1/(318507 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-225481823 / 500000000) (-90192729 / 200000000) (Real.log (318507 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (4843657 / 15625000) ≤ -Real.log (1000000 / 1363417) ∧
    -Real.log (1000000 / 1363417) ≤ (309994049 / 1000000000) := by
  have h := checkLog_sound (w := (363417 / 2363417)) (n := 12)
    (lo := (4843657 / 15625000)) (hi := (309994049 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1363417 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1363417 / 1000000) = 1/(1000000 / 1363417) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (4843657 / 15625000) (309994049 / 1000000000) (Real.log (1363417 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1363417 / 1000000) = -Real.log (1000000 / 1363417) := by
    rw [show ((1363417 / 1000000) : ℝ) = ((1000000 / 1363417) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (112910117 / 250000000) ≤ -Real.log (636583 / 1000000) ∧
    -Real.log (636583 / 1000000) ≤ (451640469 / 1000000000) := by
  have h := checkLog_sound (w := (363417 / 1636583)) (n := 12)
    (lo := (112910117 / 250000000)) (hi := (451640469 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 636583) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 636583) = 1/(636583 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-451640469 / 1000000000) (-112910117 / 250000000) (Real.log (636583 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (236161647 / 1000000000) ≤ -Real.log (1000000 / 1266379) ∧
    -Real.log (1000000 / 1266379) ≤ (14760103 / 62500000) := by
  have h := checkLog_sound (w := (266379 / 2266379)) (n := 12)
    (lo := (236161647 / 1000000000)) (hi := (14760103 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1266379 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1266379 / 1000000) = 1/(1000000 / 1266379) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (236161647 / 1000000000) (14760103 / 62500000) (Real.log (1266379 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1266379 / 1000000) = -Real.log (1000000 / 1266379) := by
    rw [show ((1266379 / 1000000) : ℝ) = ((1000000 / 1266379) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (77440683 / 250000000) ≤ -Real.log (733621 / 1000000) ∧
    -Real.log (733621 / 1000000) ≤ (309762733 / 1000000000) := by
  have h := checkLog_sound (w := (266379 / 1733621)) (n := 12)
    (lo := (77440683 / 250000000)) (hi := (309762733 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 733621) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 733621) = 1/(733621 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-309762733 / 1000000000) (-77440683 / 250000000) (Real.log (733621 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (118215441 / 500000000) ≤ -Real.log (6250 / 7917) ∧
    -Real.log (6250 / 7917) ≤ (236430883 / 1000000000) := by
  have h := checkLog_sound (w := (1667 / 14167)) (n := 12)
    (lo := (118215441 / 500000000)) (hi := (236430883 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7917 / 6250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7917 / 6250) = 1/(6250 / 7917) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (118215441 / 500000000) (236430883 / 1000000000) (Real.log (7917 / 6250)) := by
  have h := reflection_log_15_neg
  have he : Real.log (7917 / 6250) = -Real.log (6250 / 7917) := by
    rw [show ((7917 / 6250) : ℝ) = ((6250 / 7917) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (155113829 / 500000000) ≤ -Real.log (4583 / 6250) ∧
    -Real.log (4583 / 6250) ≤ (310227659 / 1000000000) := by
  have h := checkLog_sound (w := (1667 / 10833)) (n := 12)
    (lo := (155113829 / 500000000)) (hi := (310227659 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6250 / 4583) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6250 / 4583) = 1/(4583 / 6250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-310227659 / 1000000000) (-155113829 / 500000000) (Real.log (4583 / 6250)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (380320763 / 500000000) ≤ -Real.log (125000000000 / 267456052771) ∧
    -Real.log (125000000000 / 267456052771) ≤ (95080191 / 125000000) := by
  have h := checkLog_sound (w := (17456052771 / 517456052771)) (n := 12)
    (lo := (33747173 / 500000000)) (hi := (67494347 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((267456052771 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(267456052771 / 250000000000) = 1/(125000000000 / 267456052771) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (380320763 / 500000000) (95080191 / 125000000) (Real.log (267456052771 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (267456052771 / 125000000000) = -Real.log (125000000000 / 267456052771) := by
    rw [show ((267456052771 / 125000000000) : ℝ) = ((125000000000 / 267456052771) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (190408629 / 250000000) ≤ -Real.log (500000000000 / 1070887064217) ∧
    -Real.log (500000000000 / 1070887064217) ≤ (380817259 / 500000000) := by
  have h := checkLog_sound (w := (70887064217 / 2070887064217)) (n := 12)
    (lo := (8560917 / 125000000)) (hi := (68487337 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1070887064217 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1070887064217 / 1000000000000) = 1/(500000000000 / 1070887064217) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (190408629 / 250000000) (380817259 / 500000000) (Real.log (1070887064217 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1070887064217 / 500000000000) = -Real.log (500000000000 / 1070887064217) := by
    rw [show ((1070887064217 / 500000000000) : ℝ) = ((500000000000 / 1070887064217) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (545924379 / 1000000000) ≤ -Real.log (15625000000 / 26971926751) ∧
    -Real.log (15625000000 / 26971926751) ≤ (27296219 / 50000000) := by
  have h := checkLog_sound (w := (11346926751 / 42596926751)) (n := 12)
    (lo := (545924379 / 1000000000)) (hi := (27296219 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((26971926751 / 15625000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(26971926751 / 15625000000) = 1/(15625000000 / 26971926751) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (545924379 / 1000000000) (27296219 / 50000000) (Real.log (26971926751 / 15625000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (26971926751 / 15625000000) = -Real.log (15625000000 / 26971926751) := by
    rw [show ((26971926751 / 15625000000) : ℝ) = ((15625000000 / 26971926751) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (27332927 / 50000000) ≤ -Real.log (125000000000 / 215933886101) ∧
    -Real.log (125000000000 / 215933886101) ≤ (546658541 / 1000000000) := by
  have h := checkLog_sound (w := (90933886101 / 340933886101)) (n := 12)
    (lo := (27332927 / 50000000)) (hi := (546658541 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((215933886101 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(215933886101 / 125000000000) = 1/(125000000000 / 215933886101) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (27332927 / 50000000) (546658541 / 1000000000) (Real.log (215933886101 / 125000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (215933886101 / 125000000000) = -Real.log (125000000000 / 215933886101) := by
    rw [show ((215933886101 / 125000000000) : ℝ) = ((125000000000 / 215933886101) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0290
