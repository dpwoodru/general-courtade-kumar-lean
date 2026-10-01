import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0045
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

theorem reflection_log_1_neg : (42470593 / 62500000) ≤ -Real.log (10240 / 20203) ∧
    -Real.log (10240 / 20203) ≤ (679529489 / 1000000000) := by
  have h := checkLog_sound (w := (9963 / 30443)) (n := 12)
    (lo := (42470593 / 62500000)) (hi := (679529489 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20203 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20203 / 10240) = 1/(10240 / 20203) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (42470593 / 62500000) (679529489 / 1000000000) (Real.log (20203 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (20203 / 10240) = -Real.log (10240 / 20203) := by
    rw [show ((20203 / 10240) : ℝ) = ((10240 / 20203) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (3610039389 / 1000000000) ≤ -Real.log (277 / 10240) ∧
    -Real.log (277 / 10240) ≤ (722007879 / 200000000) := by
  have h := checkLog_sound (w := (43 / 597)) (n := 12)
    (lo := (144303489 / 1000000000)) (hi := (14430349 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 277) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(320 / 277) = 1/(277 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-722007879 / 200000000) (-3610039389 / 1000000000) (Real.log (277 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (339717719 / 500000000) ≤ -Real.log (102400 / 202011) ∧
    -Real.log (102400 / 202011) ≤ (679435439 / 1000000000) := by
  have h := checkLog_sound (w := (99611 / 304411)) (n := 12)
    (lo := (339717719 / 500000000)) (hi := (679435439 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((202011 / 102400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(202011 / 102400) = 1/(102400 / 202011) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (339717719 / 500000000) (679435439 / 1000000000) (Real.log (202011 / 102400)) := by
  have h := reflection_log_3_neg
  have he : Real.log (202011 / 102400) = -Real.log (102400 / 202011) := by
    rw [show ((202011 / 102400) : ℝ) = ((102400 / 202011) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (3603203601 / 1000000000) ≤ -Real.log (2789 / 102400) ∧
    -Real.log (2789 / 102400) ≤ (3603203607 / 1000000000) := by
  have h := checkLog_sound (w := (411 / 5989)) (n := 12)
    (lo := (137467701 / 1000000000)) (hi := (68733851 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2789) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3200 / 2789) = 1/(2789 / 102400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-3603203607 / 1000000000) (-3603203601 / 1000000000) (Real.log (2789 / 102400)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (41607737 / 62500000) ≤ -Real.log (5120 / 9963) ∧
    -Real.log (5120 / 9963) ≤ (665723793 / 1000000000) := by
  have h := checkLog_sound (w := (4843 / 15083)) (n := 12)
    (lo := (41607737 / 62500000)) (hi := (665723793 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9963 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(9963 / 5120) = 1/(5120 / 9963) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (41607737 / 62500000) (665723793 / 1000000000) (Real.log (9963 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (9963 / 5120) = -Real.log (5120 / 9963) := by
    rw [show ((9963 / 5120) : ℝ) = ((5120 / 9963) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (2916892209 / 1000000000) ≤ -Real.log (277 / 5120) ∧
    -Real.log (277 / 5120) ≤ (1458446107 / 500000000) := by
  have h := checkLog_sound (w := (43 / 597)) (n := 12)
    (lo := (144303489 / 1000000000)) (hi := (14430349 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 277) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(320 / 277) = 1/(277 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1458446107 / 500000000) (-2916892209 / 1000000000) (Real.log (277 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (166383267 / 250000000) ≤ -Real.log (51200 / 99611) ∧
    -Real.log (51200 / 99611) ≤ (665533069 / 1000000000) := by
  have h := checkLog_sound (w := (48411 / 150811)) (n := 12)
    (lo := (166383267 / 250000000)) (hi := (665533069 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((99611 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(99611 / 51200) = 1/(51200 / 99611) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (166383267 / 250000000) (665533069 / 1000000000) (Real.log (99611 / 51200)) := by
  have h := reflection_log_7_neg
  have he : Real.log (99611 / 51200) = -Real.log (51200 / 99611) := by
    rw [show ((99611 / 51200) : ℝ) = ((51200 / 99611) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (2910056421 / 1000000000) ≤ -Real.log (2789 / 51200) ∧
    -Real.log (2789 / 51200) ≤ (1455028213 / 500000000) := by
  have h := checkLog_sound (w := (411 / 5989)) (n := 12)
    (lo := (137467701 / 1000000000)) (hi := (68733851 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2789) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3200 / 2789) = 1/(2789 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1455028213 / 500000000) (-2910056421 / 1000000000) (Real.log (2789 / 51200)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (340822643 / 500000000) ≤ -Real.log (125000 / 247141) ∧
    -Real.log (125000 / 247141) ≤ (681645287 / 1000000000) := by
  have h := checkLog_sound (w := (122141 / 372141)) (n := 12)
    (lo := (340822643 / 500000000)) (hi := (681645287 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((247141 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(247141 / 125000) = 1/(125000 / 247141) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (340822643 / 500000000) (681645287 / 1000000000) (Real.log (247141 / 125000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (247141 / 125000) = -Real.log (125000 / 247141) := by
    rw [show ((247141 / 125000) : ℝ) = ((125000 / 247141) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (3777841821 / 1000000000) ≤ -Real.log (2859 / 125000) ∧
    -Real.log (2859 / 125000) ≤ (3777841827 / 1000000000) := by
  have h := checkLog_sound (w := (4189 / 27061)) (n := 12)
    (lo := (312105921 / 1000000000)) (hi := (156052961 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 11436) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 11436) = 1/(2859 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-3777841827 / 1000000000) (-3777841821 / 1000000000) (Real.log (2859 / 125000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (681721151 / 1000000000) ≤ -Real.log (500000 / 988639) ∧
    -Real.log (500000 / 988639) ≤ (10651893 / 15625000) := by
  have h := checkLog_sound (w := (488639 / 1488639)) (n := 12)
    (lo := (681721151 / 1000000000)) (hi := (10651893 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((988639 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(988639 / 500000) = 1/(500000 / 988639) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (681721151 / 1000000000) (10651893 / 15625000) (Real.log (988639 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (988639 / 500000) = -Real.log (500000 / 988639) := by
    rw [show ((988639 / 500000) : ℝ) = ((500000 / 988639) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1892210829 / 500000000) ≤ -Real.log (11361 / 500000) ∧
    -Real.log (11361 / 500000) ≤ (118263177 / 31250000) := by
  have h := checkLog_sound (w := (2132 / 13493)) (n := 12)
    (lo := (159342879 / 500000000)) (hi := (318685759 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 11361) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 11361) = 1/(11361 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-118263177 / 31250000) (-1892210829 / 500000000) (Real.log (11361 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (681583073 / 1000000000) ≤ -Real.log (200000 / 395401) ∧
    -Real.log (200000 / 395401) ≤ (340791537 / 500000000) := by
  have h := checkLog_sound (w := (195401 / 595401)) (n := 12)
    (lo := (681583073 / 1000000000)) (hi := (340791537 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((395401 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(395401 / 200000) = 1/(200000 / 395401) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (681583073 / 1000000000) (340791537 / 500000000) (Real.log (395401 / 200000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (395401 / 200000) = -Real.log (200000 / 395401) := by
    rw [show ((395401 / 200000) : ℝ) = ((200000 / 395401) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (150899139 / 40000000) ≤ -Real.log (4599 / 200000) ∧
    -Real.log (4599 / 200000) ≤ (3772478481 / 1000000000) := by
  have h := checkLog_sound (w := (1651 / 10849)) (n := 12)
    (lo := (12269703 / 40000000)) (hi := (19171411 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6250 / 4599) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(6250 / 4599) = 1/(4599 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-3772478481 / 1000000000) (-150899139 / 40000000) (Real.log (4599 / 200000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (340829977 / 500000000) ≤ -Real.log (1000000 / 1977157) ∧
    -Real.log (1000000 / 1977157) ≤ (136331991 / 200000000) := by
  have h := checkLog_sound (w := (977157 / 2977157)) (n := 12)
    (lo := (340829977 / 500000000)) (hi := (136331991 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1977157 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1977157 / 1000000) = 1/(1000000 / 1977157) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (340829977 / 500000000) (136331991 / 200000000) (Real.log (1977157 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1977157 / 1000000) = -Real.log (1000000 / 1977157) := by
    rw [show ((1977157 / 1000000) : ℝ) = ((1000000 / 1977157) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (3779110551 / 1000000000) ≤ -Real.log (22843 / 1000000) ∧
    -Real.log (22843 / 1000000) ≤ (3779110557 / 1000000000) := by
  have h := checkLog_sound (w := (8407 / 54093)) (n := 12)
    (lo := (313374651 / 1000000000)) (hi := (78343663 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 22843) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 22843) = 1/(22843 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-3779110557 / 1000000000) (-3779110551 / 1000000000) (Real.log (22843 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (4459487107 / 1000000000) ≤ -Real.log (500000000000 / 43221580972367) ∧
    -Real.log (500000000000 / 43221580972367) ≤ (2229743557 / 500000000) := by
  have h := checkLog_sound (w := (11221580972367 / 75221580972367)) (n := 12)
    (lo := (300604027 / 1000000000)) (hi := (75151007 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((43221580972367 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(43221580972367 / 32000000000000) = 1/(500000000000 / 43221580972367) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (4459487107 / 1000000000) (2229743557 / 500000000) (Real.log (43221580972367 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (43221580972367 / 500000000000) = -Real.log (500000000000 / 43221580972367) := by
    rw [show ((43221580972367 / 500000000000) : ℝ) = ((500000000000 / 43221580972367) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (558267851 / 125000000) ≤ -Real.log (250000000000 / 21755105184403) ∧
    -Real.log (250000000000 / 21755105184403) ≤ (893228563 / 200000000) := by
  have h := checkLog_sound (w := (5755105184403 / 37755105184403)) (n := 12)
    (lo := (19203733 / 62500000)) (hi := (307259729 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((21755105184403 / 16000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(21755105184403 / 16000000000000) = 1/(250000000000 / 21755105184403) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (558267851 / 125000000) (893228563 / 200000000) (Real.log (21755105184403 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (21755105184403 / 250000000000) = -Real.log (250000000000 / 21755105184403) := by
    rw [show ((21755105184403 / 250000000000) : ℝ) = ((250000000000 / 21755105184403) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (4454061547 / 1000000000) ≤ -Real.log (500000000000 / 42987714720591) ∧
    -Real.log (500000000000 / 42987714720591) ≤ (2227030777 / 500000000) := by
  have h := checkLog_sound (w := (10987714720591 / 74987714720591)) (n := 12)
    (lo := (295178467 / 1000000000)) (hi := (73794617 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((42987714720591 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(42987714720591 / 32000000000000) = 1/(500000000000 / 42987714720591) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (4454061547 / 1000000000) (2227030777 / 500000000) (Real.log (42987714720591 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (42987714720591 / 500000000000) = -Real.log (500000000000 / 42987714720591) := by
    rw [show ((42987714720591 / 500000000000) : ℝ) = ((500000000000 / 42987714720591) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (892154101 / 200000000) ≤ -Real.log (500000000000 / 43277087072627) ∧
    -Real.log (500000000000 / 43277087072627) ≤ (278798157 / 62500000) := by
  have h := checkLog_sound (w := (11277087072627 / 75277087072627)) (n := 12)
    (lo := (12075497 / 40000000)) (hi := (150943713 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((43277087072627 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(43277087072627 / 32000000000000) = 1/(500000000000 / 43277087072627) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (892154101 / 200000000) (278798157 / 62500000) (Real.log (43277087072627 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (43277087072627 / 500000000000) = -Real.log (500000000000 / 43277087072627) := by
    rw [show ((43277087072627 / 500000000000) : ℝ) = ((500000000000 / 43277087072627) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0045
