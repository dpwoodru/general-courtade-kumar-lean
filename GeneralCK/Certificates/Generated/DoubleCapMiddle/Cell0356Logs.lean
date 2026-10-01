import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0356
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

theorem reflection_log_1_neg : (26340373 / 125000000) ≤ -Real.log (5120 / 6321) ∧
    -Real.log (5120 / 6321) ≤ (42144597 / 200000000) := by
  have h := checkLog_sound (w := (1201 / 11441)) (n := 12)
    (lo := (26340373 / 125000000)) (hi := (42144597 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6321 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6321 / 5120) = 1/(5120 / 6321) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (26340373 / 125000000) (42144597 / 200000000) (Real.log (6321 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6321 / 5120) = -Real.log (5120 / 6321) := by
    rw [show ((6321 / 5120) : ℝ) = ((5120 / 6321) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (267317919 / 1000000000) ≤ -Real.log (3919 / 5120) ∧
    -Real.log (3919 / 5120) ≤ (1670737 / 6250000) := by
  have h := checkLog_sound (w := (1201 / 9039)) (n := 12)
    (lo := (267317919 / 1000000000)) (hi := (1670737 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3919) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3919) = 1/(3919 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-1670737 / 6250000) (-267317919 / 1000000000) (Real.log (3919 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (52621413 / 250000000) ≤ -Real.log (10240 / 12639) ∧
    -Real.log (10240 / 12639) ≤ (210485653 / 1000000000) := by
  have h := checkLog_sound (w := (2399 / 22879)) (n := 12)
    (lo := (52621413 / 250000000)) (hi := (210485653 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12639 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12639 / 10240) = 1/(10240 / 12639) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (52621413 / 250000000) (210485653 / 1000000000) (Real.log (12639 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12639 / 10240) = -Real.log (10240 / 12639) := by
    rw [show ((12639 / 10240) : ℝ) = ((10240 / 12639) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (133467621 / 500000000) ≤ -Real.log (7841 / 10240) ∧
    -Real.log (7841 / 10240) ≤ (266935243 / 1000000000) := by
  have h := checkLog_sound (w := (2399 / 18081)) (n := 12)
    (lo := (133467621 / 500000000)) (hi := (266935243 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7841) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7841) = 1/(7841 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-266935243 / 1000000000) (-133467621 / 500000000) (Real.log (7841 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (19233881 / 50000000) ≤ -Real.log (2560 / 3761) ∧
    -Real.log (2560 / 3761) ≤ (384677621 / 1000000000) := by
  have h := checkLog_sound (w := (1201 / 6321)) (n := 12)
    (lo := (19233881 / 50000000)) (hi := (384677621 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3761 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3761 / 2560) = 1/(2560 / 3761) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (19233881 / 50000000) (384677621 / 1000000000) (Real.log (3761 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (3761 / 2560) = -Real.log (2560 / 3761) := by
    rw [show ((3761 / 2560) : ℝ) = ((2560 / 3761) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (633258123 / 1000000000) ≤ -Real.log (1359 / 2560) ∧
    -Real.log (1359 / 2560) ≤ (158314531 / 250000000) := by
  have h := checkLog_sound (w := (1201 / 3919)) (n := 12)
    (lo := (633258123 / 1000000000)) (hi := (158314531 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1359) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1359) = 1/(1359 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-158314531 / 250000000) (-633258123 / 1000000000) (Real.log (1359 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (384278711 / 1000000000) ≤ -Real.log (5120 / 7519) ∧
    -Real.log (5120 / 7519) ≤ (48034839 / 125000000) := by
  have h := checkLog_sound (w := (2399 / 12639)) (n := 12)
    (lo := (384278711 / 1000000000)) (hi := (48034839 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7519 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7519 / 5120) = 1/(5120 / 7519) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (384278711 / 1000000000) (48034839 / 125000000) (Real.log (7519 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (7519 / 5120) = -Real.log (5120 / 7519) := by
    rw [show ((7519 / 5120) : ℝ) = ((5120 / 7519) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (632154979 / 1000000000) ≤ -Real.log (2721 / 5120) ∧
    -Real.log (2721 / 5120) ≤ (31607749 / 50000000) := by
  have h := checkLog_sound (w := (2399 / 7841)) (n := 12)
    (lo := (632154979 / 1000000000)) (hi := (31607749 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2721) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2721) = 1/(2721 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-31607749 / 50000000) (-632154979 / 1000000000) (Real.log (2721 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (72169519 / 250000000) ≤ -Real.log (500000 / 667331) ∧
    -Real.log (500000 / 667331) ≤ (288678077 / 1000000000) := by
  have h := checkLog_sound (w := (167331 / 1167331)) (n := 12)
    (lo := (72169519 / 250000000)) (hi := (288678077 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((667331 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(667331 / 500000) = 1/(500000 / 667331) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (72169519 / 250000000) (288678077 / 1000000000) (Real.log (667331 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (667331 / 500000) = -Real.log (500000 / 667331) := by
    rw [show ((667331 / 500000) : ℝ) = ((500000 / 667331) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (1591641 / 3906250) ≤ -Real.log (332669 / 500000) ∧
    -Real.log (332669 / 500000) ≤ (407460097 / 1000000000) := by
  have h := checkLog_sound (w := (167331 / 832669)) (n := 12)
    (lo := (1591641 / 3906250)) (hi := (407460097 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 332669) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 332669) = 1/(332669 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-407460097 / 1000000000) (-1591641 / 3906250) (Real.log (332669 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (144499727 / 500000000) ≤ -Real.log (1000000 / 1335091) ∧
    -Real.log (1000000 / 1335091) ≤ (57799891 / 200000000) := by
  have h := checkLog_sound (w := (335091 / 2335091)) (n := 12)
    (lo := (144499727 / 500000000)) (hi := (57799891 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1335091 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1335091 / 1000000) = 1/(1000000 / 1335091) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (144499727 / 500000000) (57799891 / 200000000) (Real.log (1335091 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1335091 / 1000000) = -Real.log (1000000 / 1335091) := by
    rw [show ((1335091 / 1000000) : ℝ) = ((1000000 / 1335091) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (408105089 / 1000000000) ≤ -Real.log (664909 / 1000000) ∧
    -Real.log (664909 / 1000000) ≤ (40810509 / 100000000) := by
  have h := checkLog_sound (w := (335091 / 1664909)) (n := 12)
    (lo := (408105089 / 1000000000)) (hi := (40810509 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 664909) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 664909) = 1/(664909 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-40810509 / 100000000) (-408105089 / 1000000000) (Real.log (664909 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (109250797 / 500000000) ≤ -Real.log (1000000 / 1244211) ∧
    -Real.log (1000000 / 1244211) ≤ (43700319 / 200000000) := by
  have h := checkLog_sound (w := (244211 / 2244211)) (n := 12)
    (lo := (109250797 / 500000000)) (hi := (43700319 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1244211 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1244211 / 1000000) = 1/(1000000 / 1244211) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (109250797 / 500000000) (43700319 / 200000000) (Real.log (1244211 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1244211 / 1000000) = -Real.log (1000000 / 1244211) := by
    rw [show ((1244211 / 1000000) : ℝ) = ((1000000 / 1244211) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (139996521 / 500000000) ≤ -Real.log (755789 / 1000000) ∧
    -Real.log (755789 / 1000000) ≤ (279993043 / 1000000000) := by
  have h := checkLog_sound (w := (244211 / 1755789)) (n := 12)
    (lo := (139996521 / 500000000)) (hi := (279993043 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 755789) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 755789) = 1/(755789 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-279993043 / 1000000000) (-139996521 / 500000000) (Real.log (755789 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (218769197 / 1000000000) ≤ -Real.log (15625 / 19446) ∧
    -Real.log (15625 / 19446) ≤ (109384599 / 500000000) := by
  have h := checkLog_sound (w := (3821 / 35071)) (n := 12)
    (lo := (218769197 / 1000000000)) (hi := (109384599 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((19446 / 15625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(19446 / 15625) = 1/(15625 / 19446) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (218769197 / 1000000000) (109384599 / 500000000) (Real.log (19446 / 15625)) := by
  have h := reflection_log_15_neg
  have he : Real.log (19446 / 15625) = -Real.log (15625 / 19446) := by
    rw [show ((19446 / 15625) : ℝ) = ((15625 / 19446) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (140216869 / 500000000) ≤ -Real.log (11804 / 15625) ∧
    -Real.log (11804 / 15625) ≤ (280433739 / 1000000000) := by
  have h := checkLog_sound (w := (3821 / 27429)) (n := 12)
    (lo := (140216869 / 500000000)) (hi := (280433739 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 11804) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625 / 11804) = 1/(11804 / 15625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-280433739 / 1000000000) (-140216869 / 500000000) (Real.log (11804 / 15625)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (174034543 / 250000000) ≤ -Real.log (500000000000 / 1002995469971) ∧
    -Real.log (500000000000 / 1002995469971) ≤ (348069087 / 500000000) := by
  have h := checkLog_sound (w := (2995469971 / 2002995469971)) (n := 12)
    (lo := (186937 / 62500000)) (hi := (2990993 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1002995469971 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1002995469971 / 1000000000000) = 1/(500000000000 / 1002995469971) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (174034543 / 250000000) (348069087 / 500000000) (Real.log (1002995469971 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1002995469971 / 500000000000) = -Real.log (500000000000 / 1002995469971) := by
    rw [show ((1002995469971 / 500000000000) : ℝ) = ((500000000000 / 1002995469971) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (697104543 / 1000000000) ≤ -Real.log (250000000000 / 501982602131) ∧
    -Real.log (250000000000 / 501982602131) ≤ (139420909 / 200000000) := by
  have h := checkLog_sound (w := (1982602131 / 1001982602131)) (n := 12)
    (lo := (3957363 / 1000000000)) (hi := (989341 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((501982602131 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(501982602131 / 500000000000) = 1/(250000000000 / 501982602131) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (697104543 / 1000000000) (139420909 / 200000000) (Real.log (501982602131 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (501982602131 / 250000000000) = -Real.log (250000000000 / 501982602131) := by
    rw [show ((501982602131 / 250000000000) : ℝ) = ((250000000000 / 501982602131) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (124623659 / 250000000) ≤ -Real.log (125000000000 / 205780151603) ∧
    -Real.log (125000000000 / 205780151603) ≤ (498494637 / 1000000000) := by
  have h := checkLog_sound (w := (80780151603 / 330780151603)) (n := 12)
    (lo := (124623659 / 250000000)) (hi := (498494637 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((205780151603 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(205780151603 / 125000000000) = 1/(125000000000 / 205780151603) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (124623659 / 250000000) (498494637 / 1000000000) (Real.log (205780151603 / 125000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (205780151603 / 125000000000) = -Real.log (125000000000 / 205780151603) := by
    rw [show ((205780151603 / 125000000000) : ℝ) = ((125000000000 / 205780151603) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (62400367 / 125000000) ≤ -Real.log (500000000000 / 823703829211) ∧
    -Real.log (500000000000 / 823703829211) ≤ (499202937 / 1000000000) := by
  have h := checkLog_sound (w := (323703829211 / 1323703829211)) (n := 12)
    (lo := (62400367 / 125000000)) (hi := (499202937 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((823703829211 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(823703829211 / 500000000000) = 1/(500000000000 / 823703829211) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (62400367 / 125000000) (499202937 / 1000000000) (Real.log (823703829211 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (823703829211 / 500000000000) = -Real.log (500000000000 / 823703829211) := by
    rw [show ((823703829211 / 500000000000) : ℝ) = ((500000000000 / 823703829211) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0356
