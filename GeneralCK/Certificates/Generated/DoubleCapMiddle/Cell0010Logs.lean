import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0010
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

theorem reflection_log_1_neg : (101366277 / 250000000) ≤ -Real.log (2 / 3) ∧
    -Real.log (2 / 3) ≤ (405465109 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 5)) (n := 12)
    (lo := (101366277 / 250000000)) (hi := (405465109 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3 / 2) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3 / 2) = 1/(2 / 3) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (101366277 / 250000000) (405465109 / 1000000000) (Real.log (3 / 2)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3 / 2) = -Real.log (2 / 3) := by
    rw [show ((3 / 2) : ℝ) = ((2 / 3) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (34657359 / 50000000) ≤ -Real.log (1 / 2) ∧
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


theorem reflection_log_2 : Bounds (-693147181 / 1000000000) (-34657359 / 50000000) (Real.log (1 / 2)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (202537203 / 500000000) ≤ -Real.log (5120 / 7677) ∧
    -Real.log (5120 / 7677) ≤ (405074407 / 1000000000) := by
  have h := checkLog_sound (w := (2557 / 12797)) (n := 12)
    (lo := (202537203 / 500000000)) (hi := (405074407 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7677 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7677 / 5120) = 1/(5120 / 7677) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (202537203 / 500000000) (405074407 / 1000000000) (Real.log (7677 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (7677 / 5120) = -Real.log (5120 / 7677) := by
    rw [show ((7677 / 5120) : ℝ) = ((5120 / 7677) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (691975991 / 1000000000) ≤ -Real.log (2563 / 5120) ∧
    -Real.log (2563 / 5120) ≤ (86496999 / 125000000) := by
  have h := checkLog_sound (w := (2557 / 7683)) (n := 12)
    (lo := (691975991 / 1000000000)) (hi := (86496999 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2563) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2563) = 1/(2563 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-86496999 / 125000000) (-691975991 / 1000000000) (Real.log (2563 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (692561071 / 1000000000) ≤ -Real.log (2560 / 5117) ∧
    -Real.log (2560 / 5117) ≤ (43285067 / 62500000) := by
  have h := checkLog_sound (w := (2557 / 7677)) (n := 12)
    (lo := (692561071 / 1000000000)) (hi := (43285067 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5117 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5117 / 2560) = 1/(2560 / 5117) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (692561071 / 1000000000) (43285067 / 62500000) (Real.log (5117 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (5117 / 2560) = -Real.log (2560 / 5117) := by
    rw [show ((5117 / 2560) : ℝ) = ((2560 / 5117) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (6749150243 / 1000000000) ≤ -Real.log (3 / 2560) ∧
    -Real.log (3 / 2560) ≤ (6749150253 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 4)) (n := 12)
    (lo := (510825623 / 1000000000)) (hi := (63853203 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5 / 3) : ℝ) 9 (by norm_num)
  have hq : (2 : ℝ)^9*(5 / 3) = 1/(3 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-6749150253 / 1000000000) (-6749150243 / 1000000000) (Real.log (3 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (23009913 / 40000000) ≤ -Real.log (1000000 / 1777571) ∧
    -Real.log (1000000 / 1777571) ≤ (287623913 / 500000000) := by
  have h := checkLog_sound (w := (777571 / 2777571)) (n := 12)
    (lo := (23009913 / 40000000)) (hi := (287623913 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1777571 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1777571 / 1000000) = 1/(1000000 / 1777571) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (23009913 / 40000000) (287623913 / 500000000) (Real.log (1777571 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1777571 / 1000000) = -Real.log (1000000 / 1777571) := by
    rw [show ((1777571 / 1000000) : ℝ) = ((1000000 / 1777571) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (23486677 / 15625000) ≤ -Real.log (222429 / 1000000) ∧
    -Real.log (222429 / 1000000) ≤ (1503147331 / 1000000000) := by
  have h := checkLog_sound (w := (27571 / 472429)) (n := 12)
    (lo := (14606621 / 125000000)) (hi := (116852969 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 222429) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(250000 / 222429) = 1/(222429 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1503147331 / 1000000000) (-23486677 / 15625000) (Real.log (222429 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (9009101 / 15625000) ≤ -Real.log (200000 / 355989) ∧
    -Real.log (200000 / 355989) ≤ (115316493 / 200000000) := by
  have h := checkLog_sound (w := (155989 / 555989)) (n := 12)
    (lo := (9009101 / 15625000)) (hi := (115316493 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((355989 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(355989 / 200000) = 1/(200000 / 355989) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (9009101 / 15625000) (115316493 / 200000000) (Real.log (355989 / 200000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (355989 / 200000) = -Real.log (200000 / 355989) := by
    rw [show ((355989 / 200000) : ℝ) = ((200000 / 355989) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (756938881 / 500000000) ≤ -Real.log (44011 / 200000) ∧
    -Real.log (44011 / 200000) ≤ (302775553 / 200000000) := by
  have h := checkLog_sound (w := (5989 / 94011)) (n := 12)
    (lo := (63791701 / 500000000)) (hi := (127583403 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 44011) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(50000 / 44011) = 1/(44011 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-302775553 / 200000000) (-756938881 / 500000000) (Real.log (44011 / 200000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (4037047 / 8000000) ≤ -Real.log (500000 / 828187) ∧
    -Real.log (500000 / 828187) ≤ (126157719 / 250000000) := by
  have h := checkLog_sound (w := (328187 / 1328187)) (n := 12)
    (lo := (4037047 / 8000000)) (hi := (126157719 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((828187 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(828187 / 500000) = 1/(500000 / 828187) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (4037047 / 8000000) (126157719 / 250000000) (Real.log (828187 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (828187 / 500000) = -Real.log (500000 / 828187) := by
    rw [show ((828187 / 500000) : ℝ) = ((500000 / 828187) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1068201421 / 1000000000) ≤ -Real.log (171813 / 500000) ∧
    -Real.log (171813 / 500000) ≤ (1068201423 / 1000000000) := by
  have h := checkLog_sound (w := (78187 / 421813)) (n := 12)
    (lo := (375054241 / 1000000000)) (hi := (187527121 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 171813) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 171813) = 1/(171813 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1068201423 / 1000000000) (-1068201421 / 1000000000) (Real.log (171813 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (506172213 / 1000000000) ≤ -Real.log (1000000 / 1658929) ∧
    -Real.log (1000000 / 1658929) ≤ (253086107 / 500000000) := by
  have h := checkLog_sound (w := (658929 / 2658929)) (n := 12)
    (lo := (506172213 / 1000000000)) (hi := (253086107 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1658929 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1658929 / 1000000) = 1/(1000000 / 1658929) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (506172213 / 1000000000) (253086107 / 500000000) (Real.log (1658929 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1658929 / 1000000) = -Real.log (1000000 / 1658929) := by
    rw [show ((1658929 / 1000000) : ℝ) = ((1000000 / 1658929) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (1075664611 / 1000000000) ≤ -Real.log (341071 / 1000000) ∧
    -Real.log (341071 / 1000000) ≤ (1075664613 / 1000000000) := by
  have h := checkLog_sound (w := (158929 / 841071)) (n := 12)
    (lo := (382517431 / 1000000000)) (hi := (47814679 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 341071) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 341071) = 1/(341071 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-1075664613 / 1000000000) (-1075664611 / 1000000000) (Real.log (341071 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (2078395153 / 1000000000) ≤ -Real.log (250000000000 / 1997908321307) ∧
    -Real.log (250000000000 / 1997908321307) ≤ (519598789 / 250000000) := by
  have h := checkLog_sound (w := (997908321307 / 2997908321307)) (n := 12)
    (lo := (692100793 / 1000000000)) (hi := (346050397 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1997908321307 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1997908321307 / 1000000000000) = 1/(250000000000 / 1997908321307) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (2078395153 / 1000000000) (519598789 / 250000000) (Real.log (1997908321307 / 250000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1997908321307 / 250000000000) = -Real.log (250000000000 / 1997908321307) := by
    rw [show ((1997908321307 / 250000000000) : ℝ) = ((250000000000 / 1997908321307) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (2090460227 / 1000000000) ≤ -Real.log (500000000000 / 4044318465839) ∧
    -Real.log (500000000000 / 4044318465839) ≤ (2090460231 / 1000000000) := by
  have h := checkLog_sound (w := (44318465839 / 8044318465839)) (n := 12)
    (lo := (11018687 / 1000000000)) (hi := (172167 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4044318465839 / 4000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(4044318465839 / 4000000000000) = 1/(500000000000 / 4044318465839) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (2090460227 / 1000000000) (2090460231 / 1000000000) (Real.log (4044318465839 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (4044318465839 / 500000000000) = -Real.log (500000000000 / 4044318465839) := by
    rw [show ((4044318465839 / 500000000000) : ℝ) = ((500000000000 / 4044318465839) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (1572832297 / 1000000000) ≤ -Real.log (2500000000 / 12050703381) ∧
    -Real.log (2500000000 / 12050703381) ≤ (15728323 / 10000000) := by
  have h := checkLog_sound (w := (2050703381 / 22050703381)) (n := 12)
    (lo := (186537937 / 1000000000)) (hi := (93268969 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12050703381 / 10000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(12050703381 / 10000000000) = 1/(2500000000 / 12050703381) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1572832297 / 1000000000) (15728323 / 10000000) (Real.log (12050703381 / 2500000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (12050703381 / 2500000000) = -Real.log (2500000000 / 12050703381) := by
    rw [show ((12050703381 / 2500000000) : ℝ) = ((2500000000 / 12050703381) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (197729603 / 125000000) ≤ -Real.log (50000000000 / 243194085689) ∧
    -Real.log (50000000000 / 243194085689) ≤ (1581836827 / 1000000000) := by
  have h := checkLog_sound (w := (43194085689 / 443194085689)) (n := 12)
    (lo := (3055351 / 15625000)) (hi := (39108493 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((243194085689 / 200000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(243194085689 / 200000000000) = 1/(50000000000 / 243194085689) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (197729603 / 125000000) (1581836827 / 1000000000) (Real.log (243194085689 / 50000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (243194085689 / 50000000000) = -Real.log (50000000000 / 243194085689) := by
    rw [show ((243194085689 / 50000000000) : ℝ) = ((50000000000 / 243194085689) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0010
