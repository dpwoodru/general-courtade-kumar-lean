import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0331
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

theorem reflection_log_1_neg : (216638061 / 1000000000) ≤ -Real.log (10240 / 12717) ∧
    -Real.log (10240 / 12717) ≤ (108319031 / 500000000) := by
  have h := checkLog_sound (w := (2477 / 22957)) (n := 12)
    (lo := (216638061 / 1000000000)) (hi := (108319031 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12717 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12717 / 10240) = 1/(10240 / 12717) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (216638061 / 1000000000) (108319031 / 500000000) (Real.log (12717 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12717 / 10240) = -Real.log (10240 / 12717) := by
    rw [show ((12717 / 10240) : ℝ) = ((10240 / 12717) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (138466381 / 500000000) ≤ -Real.log (7763 / 10240) ∧
    -Real.log (7763 / 10240) ≤ (276932763 / 1000000000) := by
  have h := checkLog_sound (w := (2477 / 18003)) (n := 12)
    (lo := (138466381 / 500000000)) (hi := (276932763 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7763) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7763) = 1/(7763 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-276932763 / 1000000000) (-138466381 / 500000000) (Real.log (7763 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (13525133 / 62500000) ≤ -Real.log (5120 / 6357) ∧
    -Real.log (5120 / 6357) ≤ (216402129 / 1000000000) := by
  have h := checkLog_sound (w := (1237 / 11477)) (n := 12)
    (lo := (13525133 / 62500000)) (hi := (216402129 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6357 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6357 / 5120) = 1/(5120 / 6357) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (13525133 / 62500000) (216402129 / 1000000000) (Real.log (6357 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6357 / 5120) = -Real.log (5120 / 6357) := by
    rw [show ((6357 / 5120) : ℝ) = ((5120 / 6357) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (69136597 / 250000000) ≤ -Real.log (3883 / 5120) ∧
    -Real.log (3883 / 5120) ≤ (276546389 / 1000000000) := by
  have h := checkLog_sound (w := (1237 / 9003)) (n := 12)
    (lo := (69136597 / 250000000)) (hi := (276546389 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3883) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3883) = 1/(3883 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-276546389 / 1000000000) (-69136597 / 250000000) (Real.log (3883 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (394598993 / 1000000000) ≤ -Real.log (5120 / 7597) ∧
    -Real.log (5120 / 7597) ≤ (197299497 / 500000000) := by
  have h := checkLog_sound (w := (2477 / 12717)) (n := 12)
    (lo := (394598993 / 1000000000)) (hi := (197299497 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7597 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7597 / 5120) = 1/(5120 / 7597) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (394598993 / 1000000000) (197299497 / 500000000) (Real.log (7597 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (7597 / 5120) = -Real.log (5120 / 7597) := by
    rw [show ((7597 / 5120) : ℝ) = ((5120 / 7597) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (661239803 / 1000000000) ≤ -Real.log (2643 / 5120) ∧
    -Real.log (2643 / 5120) ≤ (165309951 / 250000000) := by
  have h := checkLog_sound (w := (2477 / 7763)) (n := 12)
    (lo := (661239803 / 1000000000)) (hi := (165309951 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2643) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2643) = 1/(2643 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-165309951 / 250000000) (-661239803 / 1000000000) (Real.log (2643 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (197102011 / 500000000) ≤ -Real.log (2560 / 3797) ∧
    -Real.log (2560 / 3797) ≤ (394204023 / 1000000000) := by
  have h := checkLog_sound (w := (1237 / 6357)) (n := 12)
    (lo := (197102011 / 500000000)) (hi := (394204023 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3797 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3797 / 2560) = 1/(2560 / 3797) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (197102011 / 500000000) (394204023 / 1000000000) (Real.log (3797 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (3797 / 2560) = -Real.log (2560 / 3797) := by
    rw [show ((3797 / 2560) : ℝ) = ((2560 / 3797) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (660105373 / 1000000000) ≤ -Real.log (1323 / 2560) ∧
    -Real.log (1323 / 2560) ≤ (330052687 / 500000000) := by
  have h := checkLog_sound (w := (1237 / 3883)) (n := 12)
    (lo := (660105373 / 1000000000)) (hi := (330052687 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1323) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1323) = 1/(1323 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-330052687 / 500000000) (-660105373 / 1000000000) (Real.log (1323 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (74167081 / 250000000) ≤ -Real.log (1000000 / 1345369) ∧
    -Real.log (1000000 / 1345369) ≤ (11866733 / 40000000) := by
  have h := checkLog_sound (w := (345369 / 2345369)) (n := 12)
    (lo := (74167081 / 250000000)) (hi := (11866733 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1345369 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1345369 / 1000000) = 1/(1000000 / 1345369) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (74167081 / 250000000) (11866733 / 40000000) (Real.log (1345369 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1345369 / 1000000) = -Real.log (1000000 / 1345369) := by
    rw [show ((1345369 / 1000000) : ℝ) = ((1000000 / 1345369) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (10592089 / 25000000) ≤ -Real.log (654631 / 1000000) ∧
    -Real.log (654631 / 1000000) ≤ (423683561 / 1000000000) := by
  have h := checkLog_sound (w := (345369 / 1654631)) (n := 12)
    (lo := (10592089 / 25000000)) (hi := (423683561 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 654631) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 654631) = 1/(654631 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-423683561 / 1000000000) (-10592089 / 25000000) (Real.log (654631 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (18561743 / 62500000) ≤ -Real.log (1000000 / 1345799) ∧
    -Real.log (1000000 / 1345799) ≤ (296987889 / 1000000000) := by
  have h := checkLog_sound (w := (345799 / 2345799)) (n := 12)
    (lo := (18561743 / 62500000)) (hi := (296987889 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1345799 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1345799 / 1000000) = 1/(1000000 / 1345799) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (18561743 / 62500000) (296987889 / 1000000000) (Real.log (1345799 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1345799 / 1000000) = -Real.log (1000000 / 1345799) := by
    rw [show ((1345799 / 1000000) : ℝ) = ((1000000 / 1345799) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (84868127 / 200000000) ≤ -Real.log (654201 / 1000000) ∧
    -Real.log (654201 / 1000000) ≤ (106085159 / 250000000) := by
  have h := checkLog_sound (w := (345799 / 1654201)) (n := 12)
    (lo := (84868127 / 200000000)) (hi := (106085159 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 654201) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 654201) = 1/(654201 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-106085159 / 250000000) (-84868127 / 200000000) (Real.log (654201 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (56294969 / 250000000) ≤ -Real.log (250000 / 313137) ∧
    -Real.log (250000 / 313137) ≤ (225179877 / 1000000000) := by
  have h := checkLog_sound (w := (63137 / 563137)) (n := 12)
    (lo := (56294969 / 250000000)) (hi := (225179877 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((313137 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(313137 / 250000) = 1/(250000 / 313137) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (56294969 / 250000000) (225179877 / 1000000000) (Real.log (313137 / 250000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (313137 / 250000) = -Real.log (250000 / 313137) := by
    rw [show ((313137 / 250000) : ℝ) = ((250000 / 313137) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (291085189 / 1000000000) ≤ -Real.log (186863 / 250000) ∧
    -Real.log (186863 / 250000) ≤ (29108519 / 100000000) := by
  have h := checkLog_sound (w := (63137 / 436863)) (n := 12)
    (lo := (291085189 / 1000000000)) (hi := (29108519 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 186863) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 186863) = 1/(186863 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-29108519 / 100000000) (-291085189 / 1000000000) (Real.log (186863 / 250000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (225448093 / 1000000000) ≤ -Real.log (250000 / 313221) ∧
    -Real.log (250000 / 313221) ≤ (112724047 / 500000000) := by
  have h := checkLog_sound (w := (63221 / 563221)) (n := 12)
    (lo := (225448093 / 1000000000)) (hi := (112724047 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((313221 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(313221 / 250000) = 1/(250000 / 313221) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (225448093 / 1000000000) (112724047 / 500000000) (Real.log (313221 / 250000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (313221 / 250000) = -Real.log (250000 / 313221) := by
    rw [show ((313221 / 250000) : ℝ) = ((250000 / 313221) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (145767409 / 500000000) ≤ -Real.log (186779 / 250000) ∧
    -Real.log (186779 / 250000) ≤ (291534819 / 1000000000) := by
  have h := checkLog_sound (w := (63221 / 436779)) (n := 12)
    (lo := (145767409 / 500000000)) (hi := (291534819 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 186779) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 186779) = 1/(186779 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-291534819 / 1000000000) (-145767409 / 500000000) (Real.log (186779 / 250000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (144070377 / 200000000) ≤ -Real.log (250000000000 / 513789065901) ∧
    -Real.log (250000000000 / 513789065901) ≤ (720351887 / 1000000000) := by
  have h := checkLog_sound (w := (13789065901 / 1013789065901)) (n := 12)
    (lo := (5440941 / 200000000)) (hi := (13602353 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((513789065901 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(513789065901 / 500000000000) = 1/(250000000000 / 513789065901) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (144070377 / 200000000) (720351887 / 1000000000) (Real.log (513789065901 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (513789065901 / 250000000000) = -Real.log (250000000000 / 513789065901) := by
    rw [show ((513789065901 / 250000000000) : ℝ) = ((250000000000 / 513789065901) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (721328523 / 1000000000) ≤ -Real.log (250000000000 / 514291097079) ∧
    -Real.log (250000000000 / 514291097079) ≤ (28853141 / 40000000) := by
  have h := checkLog_sound (w := (14291097079 / 1014291097079)) (n := 12)
    (lo := (28181343 / 1000000000)) (hi := (880667 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((514291097079 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(514291097079 / 500000000000) = 1/(250000000000 / 514291097079) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (721328523 / 1000000000) (28853141 / 40000000) (Real.log (514291097079 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (514291097079 / 250000000000) = -Real.log (250000000000 / 514291097079) := by
    rw [show ((514291097079 / 250000000000) : ℝ) = ((250000000000 / 514291097079) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (258132533 / 500000000) ≤ -Real.log (15625000000 / 26183704773) ∧
    -Real.log (15625000000 / 26183704773) ≤ (516265067 / 1000000000) := by
  have h := checkLog_sound (w := (10558704773 / 41808704773)) (n := 12)
    (lo := (258132533 / 500000000)) (hi := (516265067 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((26183704773 / 15625000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(26183704773 / 15625000000) = 1/(15625000000 / 26183704773) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (258132533 / 500000000) (516265067 / 1000000000) (Real.log (26183704773 / 15625000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (26183704773 / 15625000000) = -Real.log (15625000000 / 26183704773) := by
    rw [show ((26183704773 / 15625000000) : ℝ) = ((15625000000 / 26183704773) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (516982911 / 1000000000) ≤ -Real.log (500000000000 / 838480236001) ∧
    -Real.log (500000000000 / 838480236001) ≤ (4038929 / 7812500) := by
  have h := checkLog_sound (w := (338480236001 / 1338480236001)) (n := 12)
    (lo := (516982911 / 1000000000)) (hi := (4038929 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((838480236001 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(838480236001 / 500000000000) = 1/(500000000000 / 838480236001) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (516982911 / 1000000000) (4038929 / 7812500) (Real.log (838480236001 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (838480236001 / 500000000000) = -Real.log (500000000000 / 838480236001) := by
    rw [show ((838480236001 / 500000000000) : ℝ) = ((500000000000 / 838480236001) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0331
