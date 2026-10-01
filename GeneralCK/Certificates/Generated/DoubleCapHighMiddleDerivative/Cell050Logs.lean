import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell050
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

theorem reflection_log_1_neg : (246768521 / 1000000000) ≤ -Real.log (5120 / 6553) ∧
    -Real.log (5120 / 6553) ≤ (123384261 / 500000000) := by
  have h := checkLog_sound (w := (1433 / 11673)) (n := 12)
    (lo := (246768521 / 1000000000)) (hi := (123384261 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6553 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6553 / 5120) = 1/(5120 / 6553) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (246768521 / 1000000000) (123384261 / 500000000) (Real.log (6553 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6553 / 5120) = -Real.log (5120 / 6553) := by
    rw [show ((6553 / 5120) : ℝ) = ((5120 / 6553) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (328341319 / 1000000000) ≤ -Real.log (3687 / 5120) ∧
    -Real.log (3687 / 5120) ≤ (8208533 / 25000000) := by
  have h := checkLog_sound (w := (1433 / 8807)) (n := 12)
    (lo := (328341319 / 1000000000)) (hi := (8208533 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3687) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3687) = 1/(3687 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-8208533 / 25000000) (-328341319 / 1000000000) (Real.log (3687 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (24631061 / 100000000) ≤ -Real.log (512 / 655) ∧
    -Real.log (512 / 655) ≤ (246310611 / 1000000000) := by
  have h := checkLog_sound (w := (143 / 1167)) (n := 12)
    (lo := (24631061 / 100000000)) (hi := (246310611 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((655 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(655 / 512) = 1/(512 / 655) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (24631061 / 100000000) (246310611 / 1000000000) (Real.log (655 / 512)) := by
  have h := reflection_log_3_neg
  have he : Real.log (655 / 512) = -Real.log (512 / 655) := by
    rw [show ((655 / 512) : ℝ) = ((512 / 655) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (16376399 / 50000000) ≤ -Real.log (369 / 512) ∧
    -Real.log (369 / 512) ≤ (327527981 / 1000000000) := by
  have h := checkLog_sound (w := (143 / 881)) (n := 12)
    (lo := (16376399 / 50000000)) (hi := (327527981 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 369) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 369) = 1/(369 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-327527981 / 1000000000) (-16376399 / 50000000) (Real.log (369 / 512)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (45195927 / 250000000) ≤ -Real.log (250000 / 299539) ∧
    -Real.log (250000 / 299539) ≤ (180783709 / 1000000000) := by
  have h := checkLog_sound (w := (49539 / 549539)) (n := 12)
    (lo := (45195927 / 250000000)) (hi := (180783709 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((299539 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(299539 / 250000) = 1/(250000 / 299539) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (45195927 / 250000000) (180783709 / 1000000000) (Real.log (299539 / 250000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (299539 / 250000) = -Real.log (250000 / 299539) := by
    rw [show ((299539 / 250000) : ℝ) = ((250000 / 299539) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (220841203 / 1000000000) ≤ -Real.log (200461 / 250000) ∧
    -Real.log (200461 / 250000) ≤ (55210301 / 250000000) := by
  have h := checkLog_sound (w := (49539 / 450461)) (n := 12)
    (lo := (220841203 / 1000000000)) (hi := (55210301 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 200461) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 200461) = 1/(200461 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-55210301 / 250000000) (-220841203 / 1000000000) (Real.log (200461 / 250000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (181133351 / 1000000000) ≤ -Real.log (40000 / 47943) ∧
    -Real.log (40000 / 47943) ≤ (22641669 / 125000000) := by
  have h := checkLog_sound (w := (7943 / 87943)) (n := 12)
    (lo := (181133351 / 1000000000)) (hi := (22641669 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((47943 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(47943 / 40000) = 1/(40000 / 47943) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (181133351 / 1000000000) (22641669 / 125000000) (Real.log (47943 / 40000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (47943 / 40000) = -Real.log (40000 / 47943) := by
    rw [show ((47943 / 40000) : ℝ) = ((40000 / 47943) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (44272777 / 200000000) ≤ -Real.log (32057 / 40000) ∧
    -Real.log (32057 / 40000) ≤ (110681943 / 500000000) := by
  have h := checkLog_sound (w := (7943 / 72057)) (n := 12)
    (lo := (44272777 / 200000000)) (hi := (110681943 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000 / 32057) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000 / 32057) = 1/(32057 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-110681943 / 500000000) (-44272777 / 200000000) (Real.log (32057 / 40000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (132482467 / 1000000000) ≤ -Real.log (1000000 / 1141659) ∧
    -Real.log (1000000 / 1141659) ≤ (33120617 / 250000000) := by
  have h := checkLog_sound (w := (141659 / 2141659)) (n := 12)
    (lo := (132482467 / 1000000000)) (hi := (33120617 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1141659 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1141659 / 1000000) = 1/(1000000 / 1141659) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (132482467 / 1000000000) (33120617 / 250000000) (Real.log (1141659 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1141659 / 1000000) = -Real.log (1000000 / 1141659) := by
    rw [show ((1141659 / 1000000) : ℝ) = ((1000000 / 1141659) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (76376911 / 500000000) ≤ -Real.log (858341 / 1000000) ∧
    -Real.log (858341 / 1000000) ≤ (152753823 / 1000000000) := by
  have h := checkLog_sound (w := (141659 / 1858341)) (n := 12)
    (lo := (76376911 / 500000000)) (hi := (152753823 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 858341) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 858341) = 1/(858341 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-152753823 / 1000000000) (-76376911 / 500000000) (Real.log (858341 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (66375669 / 500000000) ≤ -Real.log (500000 / 570983) ∧
    -Real.log (500000 / 570983) ≤ (132751339 / 1000000000) := by
  have h := checkLog_sound (w := (70983 / 1070983)) (n := 12)
    (lo := (66375669 / 500000000)) (hi := (132751339 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((570983 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(570983 / 500000) = 1/(500000 / 570983) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (66375669 / 500000000) (132751339 / 1000000000) (Real.log (570983 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (570983 / 500000) = -Real.log (500000 / 570983) := by
    rw [show ((570983 / 500000) : ℝ) = ((500000 / 570983) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (153111553 / 1000000000) ≤ -Real.log (429017 / 500000) ∧
    -Real.log (429017 / 500000) ≤ (76555777 / 500000000) := by
  have h := checkLog_sound (w := (70983 / 929017)) (n := 12)
    (lo := (153111553 / 1000000000)) (hi := (76555777 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 429017) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 429017) = 1/(429017 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-76555777 / 500000000) (-153111553 / 1000000000) (Real.log (429017 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (573838591 / 1000000000) ≤ -Real.log (250000000000 / 443766937669) ∧
    -Real.log (250000000000 / 443766937669) ≤ (2241557 / 3906250) := by
  have h := checkLog_sound (w := (193766937669 / 693766937669)) (n := 12)
    (lo := (573838591 / 1000000000)) (hi := (2241557 / 3906250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((443766937669 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(443766937669 / 250000000000) = 1/(250000000000 / 443766937669) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (573838591 / 1000000000) (2241557 / 3906250) (Real.log (443766937669 / 250000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (443766937669 / 250000000000) = -Real.log (250000000000 / 443766937669) := by
    rw [show ((443766937669 / 250000000000) : ℝ) = ((250000000000 / 443766937669) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (7188873 / 12500000) ≤ -Real.log (250000000000 / 444331434771) ∧
    -Real.log (250000000000 / 444331434771) ≤ (575109841 / 1000000000) := by
  have h := checkLog_sound (w := (194331434771 / 694331434771)) (n := 12)
    (lo := (7188873 / 12500000)) (hi := (575109841 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((444331434771 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(444331434771 / 250000000000) = 1/(250000000000 / 444331434771) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (7188873 / 12500000) (575109841 / 1000000000) (Real.log (444331434771 / 250000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (444331434771 / 250000000000) = -Real.log (250000000000 / 444331434771) := by
    rw [show ((444331434771 / 250000000000) : ℝ) = ((250000000000 / 444331434771) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (401624911 / 1000000000) ≤ -Real.log (62500000000 / 93390672001) ∧
    -Real.log (62500000000 / 93390672001) ≤ (25101557 / 62500000) := by
  have h := checkLog_sound (w := (30890672001 / 155890672001)) (n := 12)
    (lo := (401624911 / 1000000000)) (hi := (25101557 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((93390672001 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(93390672001 / 62500000000) = 1/(62500000000 / 93390672001) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (401624911 / 1000000000) (25101557 / 62500000) (Real.log (93390672001 / 62500000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (93390672001 / 62500000000) = -Real.log (62500000000 / 93390672001) := by
    rw [show ((93390672001 / 62500000000) : ℝ) = ((62500000000 / 93390672001) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (402497237 / 1000000000) ≤ -Real.log (500000000000 / 747777396513) ∧
    -Real.log (500000000000 / 747777396513) ≤ (201248619 / 500000000) := by
  have h := checkLog_sound (w := (247777396513 / 1247777396513)) (n := 12)
    (lo := (402497237 / 1000000000)) (hi := (201248619 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((747777396513 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(747777396513 / 500000000000) = 1/(500000000000 / 747777396513) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (402497237 / 1000000000) (201248619 / 500000000) (Real.log (747777396513 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (747777396513 / 500000000000) = -Real.log (500000000000 / 747777396513) := by
    rw [show ((747777396513 / 500000000000) : ℝ) = ((500000000000 / 747777396513) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (28523629 / 100000000) ≤ -Real.log (500000000000 / 665038137523) ∧
    -Real.log (500000000000 / 665038137523) ≤ (285236291 / 1000000000) := by
  have h := checkLog_sound (w := (165038137523 / 1165038137523)) (n := 12)
    (lo := (28523629 / 100000000)) (hi := (285236291 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((665038137523 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(665038137523 / 500000000000) = 1/(500000000000 / 665038137523) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (28523629 / 100000000) (285236291 / 1000000000) (Real.log (665038137523 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (665038137523 / 500000000000) = -Real.log (500000000000 / 665038137523) := by
    rw [show ((665038137523 / 500000000000) : ℝ) = ((500000000000 / 665038137523) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (285862891 / 1000000000) ≤ -Real.log (500000000000 / 665454981971) ∧
    -Real.log (500000000000 / 665454981971) ≤ (71465723 / 250000000) := by
  have h := checkLog_sound (w := (165454981971 / 1165454981971)) (n := 12)
    (lo := (285862891 / 1000000000)) (hi := (71465723 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((665454981971 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(665454981971 / 500000000000) = 1/(500000000000 / 665454981971) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (285862891 / 1000000000) (71465723 / 250000000) (Real.log (665454981971 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (665454981971 / 500000000000) = -Real.log (500000000000 / 665454981971) := by
    rw [show ((665454981971 / 500000000000) : ℝ) = ((500000000000 / 665454981971) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (10180107 / 500000000) ≤ -Real.log (244961413711 / 250000000000) ∧
    -Real.log (244961413711 / 250000000000) ≤ (4072043 / 200000000) := by
  have h := checkLog_sound (w := (5038586289 / 494961413711)) (n := 12)
    (lo := (10180107 / 500000000)) (hi := (4072043 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 244961413711) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 244961413711) = 1/(244961413711 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-4072043 / 200000000) (-10180107 / 500000000) (Real.log (244961413711 / 250000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (10135677 / 500000000) ≤ -Real.log (979932727719 / 1000000000000) ∧
    -Real.log (979932727719 / 1000000000000) ≤ (4054271 / 200000000) := by
  have h := checkLog_sound (w := (20067272281 / 1979932727719)) (n := 12)
    (lo := (10135677 / 500000000)) (hi := (4054271 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 979932727719) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 979932727719) = 1/(979932727719 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-4054271 / 200000000) (-10135677 / 500000000) (Real.log (979932727719 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell050
