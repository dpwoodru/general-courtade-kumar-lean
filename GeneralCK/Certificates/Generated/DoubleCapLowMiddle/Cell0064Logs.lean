import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0064
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

theorem reflection_log_1_neg : (338870513 / 500000000) ≤ -Real.log (102400 / 201669) ∧
    -Real.log (102400 / 201669) ≤ (677741027 / 1000000000) := by
  have h := checkLog_sound (w := (99269 / 304069)) (n := 12)
    (lo := (338870513 / 500000000)) (hi := (677741027 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((201669 / 102400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(201669 / 102400) = 1/(102400 / 201669) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (338870513 / 500000000) (677741027 / 1000000000) (Real.log (201669 / 102400)) := by
  have h := reflection_log_1_neg
  have he : Real.log (201669 / 102400) = -Real.log (102400 / 201669) := by
    rw [show ((201669 / 102400) : ℝ) = ((102400 / 201669) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (3487534267 / 1000000000) ≤ -Real.log (3131 / 102400) ∧
    -Real.log (3131 / 102400) ≤ (3487534273 / 1000000000) := by
  have h := checkLog_sound (w := (69 / 6331)) (n := 12)
    (lo := (21798367 / 1000000000)) (hi := (681199 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 3131) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3200 / 3131) = 1/(3131 / 102400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-3487534273 / 1000000000) (-3487534267 / 1000000000) (Real.log (3131 / 102400)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (84705851 / 125000000) ≤ -Real.log (2048 / 4033) ∧
    -Real.log (2048 / 4033) ≤ (677646809 / 1000000000) := by
  have h := checkLog_sound (w := (1985 / 6081)) (n := 12)
    (lo := (84705851 / 125000000)) (hi := (677646809 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4033 / 2048) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4033 / 2048) = 1/(2048 / 4033) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (84705851 / 125000000) (677646809 / 1000000000) (Real.log (4033 / 2048)) := by
  have h := reflection_log_3_neg
  have he : Real.log (4033 / 2048) = -Real.log (2048 / 4033) := by
    rw [show ((4033 / 2048) : ℝ) = ((2048 / 4033) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (108796383 / 31250000) ≤ -Real.log (63 / 2048) ∧
    -Real.log (63 / 2048) ≤ (1740742131 / 500000000) := by
  have h := checkLog_sound (w := (1 / 127)) (n := 12)
    (lo := (3937089 / 250000000)) (hi := (15748357 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((64 / 63) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(64 / 63) = 1/(63 / 2048) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-1740742131 / 500000000) (-108796383 / 31250000) (Real.log (63 / 2048)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (165523451 / 250000000) ≤ -Real.log (51200 / 99269) ∧
    -Real.log (51200 / 99269) ≤ (132418761 / 200000000) := by
  have h := checkLog_sound (w := (48069 / 150469)) (n := 12)
    (lo := (165523451 / 250000000)) (hi := (132418761 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((99269 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(99269 / 51200) = 1/(51200 / 99269) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (165523451 / 250000000) (132418761 / 200000000) (Real.log (99269 / 51200)) := by
  have h := reflection_log_5_neg
  have he : Real.log (99269 / 51200) = -Real.log (51200 / 99269) := by
    rw [show ((99269 / 51200) : ℝ) = ((51200 / 99269) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (2794387087 / 1000000000) ≤ -Real.log (3131 / 51200) ∧
    -Real.log (3131 / 51200) ≤ (698596773 / 250000000) := by
  have h := checkLog_sound (w := (69 / 6331)) (n := 12)
    (lo := (21798367 / 1000000000)) (hi := (681199 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 3131) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3200 / 3131) = 1/(3131 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-698596773 / 250000000) (-2794387087 / 1000000000) (Real.log (3131 / 51200)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (661902387 / 1000000000) ≤ -Real.log (1024 / 1985) ∧
    -Real.log (1024 / 1985) ≤ (165475597 / 250000000) := by
  have h := checkLog_sound (w := (961 / 3009)) (n := 12)
    (lo := (661902387 / 1000000000)) (hi := (165475597 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1985 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1985 / 1024) = 1/(1024 / 1985) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (661902387 / 1000000000) (165475597 / 250000000) (Real.log (1985 / 1024)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1985 / 1024) = -Real.log (1024 / 1985) := by
    rw [show ((1985 / 1024) : ℝ) = ((1024 / 1985) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (697084269 / 250000000) ≤ -Real.log (63 / 1024) ∧
    -Real.log (63 / 1024) ≤ (2788337081 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 127)) (n := 12)
    (lo := (3937089 / 250000000)) (hi := (15748357 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((64 / 63) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(64 / 63) = 1/(63 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-2788337081 / 1000000000) (-697084269 / 250000000) (Real.log (63 / 1024)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (170055249 / 250000000) ≤ -Real.log (500000 / 987157) ∧
    -Real.log (500000 / 987157) ≤ (680220997 / 1000000000) := by
  have h := checkLog_sound (w := (487157 / 1487157)) (n := 12)
    (lo := (170055249 / 250000000)) (hi := (680220997 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((987157 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(987157 / 500000) = 1/(500000 / 987157) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (170055249 / 250000000) (680220997 / 1000000000) (Real.log (987157 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (987157 / 500000) = -Real.log (500000 / 987157) := by
    rw [show ((987157 / 500000) : ℝ) = ((500000 / 987157) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (3661809179 / 1000000000) ≤ -Real.log (12843 / 500000) ∧
    -Real.log (12843 / 500000) ≤ (732361837 / 200000000) := by
  have h := checkLog_sound (w := (1391 / 14234)) (n := 12)
    (lo := (196073279 / 1000000000)) (hi := (612729 / 3125000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 12843) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 12843) = 1/(12843 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-732361837 / 200000000) (-3661809179 / 1000000000) (Real.log (12843 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (170073989 / 250000000) ≤ -Real.log (500000 / 987231) ∧
    -Real.log (500000 / 987231) ≤ (680295957 / 1000000000) := by
  have h := checkLog_sound (w := (487231 / 1487231)) (n := 12)
    (lo := (170073989 / 250000000)) (hi := (680295957 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((987231 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(987231 / 500000) = 1/(500000 / 987231) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (170073989 / 250000000) (680295957 / 1000000000) (Real.log (987231 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (987231 / 500000) = -Real.log (500000 / 987231) := by
    rw [show ((987231 / 500000) : ℝ) = ((500000 / 987231) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (3667587737 / 1000000000) ≤ -Real.log (12769 / 500000) ∧
    -Real.log (12769 / 500000) ≤ (3667587743 / 1000000000) := by
  have h := checkLog_sound (w := (1428 / 14197)) (n := 12)
    (lo := (201851837 / 1000000000)) (hi := (100925919 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 12769) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 12769) = 1/(12769 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-3667587743 / 1000000000) (-3667587737 / 1000000000) (Real.log (12769 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (136027889 / 200000000) ≤ -Real.log (1000000 / 1974153) ∧
    -Real.log (1000000 / 1974153) ≤ (340069723 / 500000000) := by
  have h := checkLog_sound (w := (974153 / 2974153)) (n := 12)
    (lo := (136027889 / 200000000)) (hi := (340069723 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1974153 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1974153 / 1000000) = 1/(1000000 / 1974153) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (136027889 / 200000000) (340069723 / 500000000) (Real.log (1974153 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1974153 / 1000000) = -Real.log (1000000 / 1974153) := by
    rw [show ((1974153 / 1000000) : ℝ) = ((1000000 / 1974153) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (114236273 / 31250000) ≤ -Real.log (25847 / 1000000) ∧
    -Real.log (25847 / 1000000) ≤ (1827780371 / 500000000) := by
  have h := checkLog_sound (w := (5403 / 57097)) (n := 12)
    (lo := (47456209 / 250000000)) (hi := (189824837 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 25847) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 25847) = 1/(25847 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-1827780371 / 500000000) (-114236273 / 31250000) (Real.log (25847 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (680215931 / 1000000000) ≤ -Real.log (31250 / 61697) ∧
    -Real.log (31250 / 61697) ≤ (170053983 / 250000000) := by
  have h := checkLog_sound (w := (30447 / 92947)) (n := 12)
    (lo := (680215931 / 1000000000)) (hi := (170053983 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((61697 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(61697 / 31250) = 1/(31250 / 61697) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (680215931 / 1000000000) (170053983 / 250000000) (Real.log (61697 / 31250)) := by
  have h := reflection_log_15_neg
  have he : Real.log (61697 / 31250) = -Real.log (31250 / 61697) := by
    rw [show ((61697 / 31250) : ℝ) = ((31250 / 61697) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (1830709969 / 500000000) ≤ -Real.log (803 / 31250) ∧
    -Real.log (803 / 31250) ≤ (457677493 / 125000000) := by
  have h := checkLog_sound (w := (2777 / 28473)) (n := 12)
    (lo := (97842019 / 500000000)) (hi := (195684039 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 12848) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 12848) = 1/(803 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-457677493 / 125000000) (-1830709969 / 500000000) (Real.log (803 / 31250)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (173681207 / 40000000) ≤ -Real.log (12500000000 / 960792844351) ∧
    -Real.log (12500000000 / 960792844351) ≤ (2171015091 / 500000000) := by
  have h := checkLog_sound (w := (160792844351 / 1760792844351)) (n := 12)
    (lo := (36629419 / 200000000)) (hi := (22893387 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((960792844351 / 800000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(960792844351 / 800000000000) = 1/(12500000000 / 960792844351) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (173681207 / 40000000) (2171015091 / 500000000) (Real.log (960792844351 / 12500000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (960792844351 / 12500000000) = -Real.log (12500000000 / 960792844351) := by
    rw [show ((960792844351 / 12500000000) : ℝ) = ((12500000000 / 960792844351) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1086970923 / 250000000) ≤ -Real.log (50000000000 / 3865733416869) ∧
    -Real.log (50000000000 / 3865733416869) ≤ (4347883699 / 1000000000) := by
  have h := checkLog_sound (w := (665733416869 / 7065733416869)) (n := 12)
    (lo := (47250153 / 250000000)) (hi := (189000613 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3865733416869 / 3200000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(3865733416869 / 3200000000000) = 1/(50000000000 / 3865733416869) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1086970923 / 250000000) (4347883699 / 1000000000) (Real.log (3865733416869 / 50000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (3865733416869 / 50000000000) = -Real.log (50000000000 / 3865733416869) := by
    rw [show ((3865733416869 / 50000000000) : ℝ) = ((50000000000 / 3865733416869) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (4335700181 / 1000000000) ≤ -Real.log (62500000000 / 4773651197431) ∧
    -Real.log (62500000000 / 4773651197431) ≤ (1083925047 / 250000000) := by
  have h := checkLog_sound (w := (773651197431 / 8773651197431)) (n := 12)
    (lo := (176817101 / 1000000000)) (hi := (88408551 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4773651197431 / 4000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(4773651197431 / 4000000000000) = 1/(62500000000 / 4773651197431) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (4335700181 / 1000000000) (1083925047 / 250000000) (Real.log (4773651197431 / 62500000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (4773651197431 / 62500000000) = -Real.log (62500000000 / 4773651197431) := by
    rw [show ((4773651197431 / 62500000000) : ℝ) = ((62500000000 / 4773651197431) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (4341635869 / 1000000000) ≤ -Real.log (250000000000 / 19208281444583) ∧
    -Real.log (250000000000 / 19208281444583) ≤ (1085408969 / 250000000) := by
  have h := checkLog_sound (w := (3208281444583 / 35208281444583)) (n := 12)
    (lo := (182752789 / 1000000000)) (hi := (18275279 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((19208281444583 / 16000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(19208281444583 / 16000000000000) = 1/(250000000000 / 19208281444583) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (4341635869 / 1000000000) (1085408969 / 250000000) (Real.log (19208281444583 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (19208281444583 / 250000000000) = -Real.log (250000000000 / 19208281444583) := by
    rw [show ((19208281444583 / 250000000000) : ℝ) = ((250000000000 / 19208281444583) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0064
