import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0364
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

theorem reflection_log_1_neg : (104411373 / 500000000) ≤ -Real.log (5120 / 6309) ∧
    -Real.log (5120 / 6309) ≤ (208822747 / 1000000000) := by
  have h := checkLog_sound (w := (1189 / 11429)) (n := 12)
    (lo := (104411373 / 500000000)) (hi := (208822747 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6309 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6309 / 5120) = 1/(5120 / 6309) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (104411373 / 500000000) (208822747 / 1000000000) (Real.log (6309 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6309 / 5120) = -Real.log (5120 / 6309) := by
    rw [show ((6309 / 5120) : ℝ) = ((5120 / 6309) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (16516287 / 62500000) ≤ -Real.log (3931 / 5120) ∧
    -Real.log (3931 / 5120) ≤ (264260593 / 1000000000) := by
  have h := checkLog_sound (w := (1189 / 9051)) (n := 12)
    (lo := (16516287 / 62500000)) (hi := (264260593 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3931) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3931) = 1/(3931 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-264260593 / 1000000000) (-16516287 / 62500000) (Real.log (3931 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (104292481 / 500000000) ≤ -Real.log (2048 / 2523) ∧
    -Real.log (2048 / 2523) ≤ (208584963 / 1000000000) := by
  have h := checkLog_sound (w := (475 / 4571)) (n := 12)
    (lo := (104292481 / 500000000)) (hi := (208584963 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2523 / 2048) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2523 / 2048) = 1/(2048 / 2523) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (104292481 / 500000000) (208584963 / 1000000000) (Real.log (2523 / 2048)) := by
  have h := reflection_log_3_neg
  have he : Real.log (2523 / 2048) = -Real.log (2048 / 2523) := by
    rw [show ((2523 / 2048) : ℝ) = ((2048 / 2523) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (263879083 / 1000000000) ≤ -Real.log (1573 / 2048) ∧
    -Real.log (1573 / 2048) ≤ (65969771 / 250000000) := by
  have h := checkLog_sound (w := (475 / 3621)) (n := 12)
    (lo := (263879083 / 1000000000)) (hi := (65969771 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2048 / 1573) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2048 / 1573) = 1/(1573 / 2048) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-65969771 / 250000000) (-263879083 / 1000000000) (Real.log (1573 / 2048)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (381481879 / 1000000000) ≤ -Real.log (2560 / 3749) ∧
    -Real.log (2560 / 3749) ≤ (9537047 / 25000000) := by
  have h := checkLog_sound (w := (1189 / 6309)) (n := 12)
    (lo := (381481879 / 1000000000)) (hi := (9537047 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3749 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3749 / 2560) = 1/(2560 / 3749) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (381481879 / 1000000000) (9537047 / 25000000) (Real.log (3749 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (3749 / 2560) = -Real.log (2560 / 3749) := by
    rw [show ((3749 / 2560) : ℝ) = ((2560 / 3749) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (624466857 / 1000000000) ≤ -Real.log (1371 / 2560) ∧
    -Real.log (1371 / 2560) ≤ (312233429 / 500000000) := by
  have h := checkLog_sound (w := (1189 / 3931)) (n := 12)
    (lo := (624466857 / 1000000000)) (hi := (312233429 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1371) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1371) = 1/(1371 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-312233429 / 500000000) (-624466857 / 1000000000) (Real.log (1371 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (95270423 / 250000000) ≤ -Real.log (1024 / 1499) ∧
    -Real.log (1024 / 1499) ≤ (381081693 / 1000000000) := by
  have h := checkLog_sound (w := (475 / 2523)) (n := 12)
    (lo := (95270423 / 250000000)) (hi := (381081693 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1499 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1499 / 1024) = 1/(1024 / 1499) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (95270423 / 250000000) (381081693 / 1000000000) (Real.log (1499 / 1024)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1499 / 1024) = -Real.log (1024 / 1499) := by
    rw [show ((1499 / 1024) : ℝ) = ((1024 / 1499) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (155843341 / 250000000) ≤ -Real.log (549 / 1024) ∧
    -Real.log (549 / 1024) ≤ (124674673 / 200000000) := by
  have h := checkLog_sound (w := (475 / 1573)) (n := 12)
    (lo := (155843341 / 250000000)) (hi := (124674673 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 549) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 549) = 1/(549 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-124674673 / 200000000) (-155843341 / 250000000) (Real.log (549 / 1024)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (286111589 / 1000000000) ≤ -Real.log (1000000 / 1331241) ∧
    -Real.log (1000000 / 1331241) ≤ (28611159 / 100000000) := by
  have h := checkLog_sound (w := (331241 / 2331241)) (n := 12)
    (lo := (286111589 / 1000000000)) (hi := (28611159 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1331241 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1331241 / 1000000) = 1/(1000000 / 1331241) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (286111589 / 1000000000) (28611159 / 100000000) (Real.log (1331241 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1331241 / 1000000) = -Real.log (1000000 / 1331241) := by
    rw [show ((1331241 / 1000000) : ℝ) = ((1000000 / 1331241) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (201165761 / 500000000) ≤ -Real.log (668759 / 1000000) ∧
    -Real.log (668759 / 1000000) ≤ (402331523 / 1000000000) := by
  have h := checkLog_sound (w := (331241 / 1668759)) (n := 12)
    (lo := (201165761 / 500000000)) (hi := (402331523 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 668759) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 668759) = 1/(668759 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-402331523 / 1000000000) (-201165761 / 500000000) (Real.log (668759 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (286433793 / 1000000000) ≤ -Real.log (100000 / 133167) ∧
    -Real.log (100000 / 133167) ≤ (143216897 / 500000000) := by
  have h := checkLog_sound (w := (33167 / 233167)) (n := 12)
    (lo := (286433793 / 1000000000)) (hi := (143216897 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((133167 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(133167 / 100000) = 1/(100000 / 133167) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (286433793 / 1000000000) (143216897 / 500000000) (Real.log (133167 / 100000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (133167 / 100000) = -Real.log (100000 / 133167) := by
    rw [show ((133167 / 100000) : ℝ) = ((100000 / 133167) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (80594643 / 200000000) ≤ -Real.log (66833 / 100000) ∧
    -Real.log (66833 / 100000) ≤ (12592913 / 31250000) := by
  have h := checkLog_sound (w := (33167 / 166833)) (n := 12)
    (lo := (80594643 / 200000000)) (hi := (12592913 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 66833) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 66833) = 1/(66833 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-12592913 / 31250000) (-80594643 / 200000000) (Real.log (66833 / 100000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (108183521 / 500000000) ≤ -Real.log (500000 / 620779) ∧
    -Real.log (500000 / 620779) ≤ (216367043 / 1000000000) := by
  have h := checkLog_sound (w := (120779 / 1120779)) (n := 12)
    (lo := (108183521 / 500000000)) (hi := (216367043 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((620779 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(620779 / 500000) = 1/(500000 / 620779) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (108183521 / 500000000) (216367043 / 1000000000) (Real.log (620779 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (620779 / 500000) = -Real.log (500000 / 620779) := by
    rw [show ((620779 / 500000) : ℝ) = ((500000 / 620779) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (276488949 / 1000000000) ≤ -Real.log (379221 / 500000) ∧
    -Real.log (379221 / 500000) ≤ (5529779 / 20000000) := by
  have h := checkLog_sound (w := (120779 / 879221)) (n := 12)
    (lo := (276488949 / 1000000000)) (hi := (5529779 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 379221) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 379221) = 1/(379221 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-5529779 / 20000000) (-276488949 / 1000000000) (Real.log (379221 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (54158603 / 250000000) ≤ -Real.log (100000 / 124189) ∧
    -Real.log (100000 / 124189) ≤ (216634413 / 1000000000) := by
  have h := checkLog_sound (w := (24189 / 224189)) (n := 12)
    (lo := (54158603 / 250000000)) (hi := (216634413 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((124189 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(124189 / 100000) = 1/(100000 / 124189) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (54158603 / 250000000) (216634413 / 1000000000) (Real.log (124189 / 100000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (124189 / 100000) = -Real.log (100000 / 124189) := by
    rw [show ((124189 / 100000) : ℝ) = ((100000 / 124189) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (55385357 / 200000000) ≤ -Real.log (75811 / 100000) ∧
    -Real.log (75811 / 100000) ≤ (138463393 / 500000000) := by
  have h := checkLog_sound (w := (24189 / 175811)) (n := 12)
    (lo := (55385357 / 200000000)) (hi := (138463393 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 75811) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 75811) = 1/(75811 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-138463393 / 500000000) (-55385357 / 200000000) (Real.log (75811 / 100000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (86055389 / 125000000) ≤ -Real.log (250000000000 / 497653489523) ∧
    -Real.log (250000000000 / 497653489523) ≤ (688443113 / 1000000000) := by
  have h := checkLog_sound (w := (247653489523 / 747653489523)) (n := 12)
    (lo := (86055389 / 125000000)) (hi := (688443113 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((497653489523 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(497653489523 / 250000000000) = 1/(250000000000 / 497653489523) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (86055389 / 125000000) (688443113 / 1000000000) (Real.log (497653489523 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (497653489523 / 250000000000) = -Real.log (250000000000 / 497653489523) := by
    rw [show ((497653489523 / 250000000000) : ℝ) = ((250000000000 / 497653489523) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (689407009 / 1000000000) ≤ -Real.log (500000000000 / 996266814299) ∧
    -Real.log (500000000000 / 996266814299) ≤ (68940701 / 100000000) := by
  have h := checkLog_sound (w := (496266814299 / 1496266814299)) (n := 12)
    (lo := (689407009 / 1000000000)) (hi := (68940701 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((996266814299 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(996266814299 / 500000000000) = 1/(500000000000 / 996266814299) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (689407009 / 1000000000) (68940701 / 100000000) (Real.log (996266814299 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (996266814299 / 500000000000) = -Real.log (500000000000 / 996266814299) := by
    rw [show ((996266814299 / 500000000000) : ℝ) = ((500000000000 / 996266814299) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (61606999 / 125000000) ≤ -Real.log (500000000000 / 818492383069) ∧
    -Real.log (500000000000 / 818492383069) ≤ (492855993 / 1000000000) := by
  have h := checkLog_sound (w := (318492383069 / 1318492383069)) (n := 12)
    (lo := (61606999 / 125000000)) (hi := (492855993 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((818492383069 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(818492383069 / 500000000000) = 1/(500000000000 / 818492383069) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (61606999 / 125000000) (492855993 / 1000000000) (Real.log (818492383069 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (818492383069 / 500000000000) = -Real.log (500000000000 / 818492383069) := by
    rw [show ((818492383069 / 500000000000) : ℝ) = ((500000000000 / 818492383069) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (493561197 / 1000000000) ≤ -Real.log (500000000000 / 819069791983) ∧
    -Real.log (500000000000 / 819069791983) ≤ (246780599 / 500000000) := by
  have h := checkLog_sound (w := (319069791983 / 1319069791983)) (n := 12)
    (lo := (493561197 / 1000000000)) (hi := (246780599 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((819069791983 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(819069791983 / 500000000000) = 1/(500000000000 / 819069791983) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (493561197 / 1000000000) (246780599 / 500000000) (Real.log (819069791983 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (819069791983 / 500000000000) = -Real.log (500000000000 / 819069791983) := by
    rw [show ((819069791983 / 500000000000) : ℝ) = ((500000000000 / 819069791983) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0364
