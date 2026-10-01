import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell162
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

theorem reflection_log_1_neg : (296771497 / 1000000000) ≤ -Real.log (5120 / 6889) ∧
    -Real.log (5120 / 6889) ≤ (148385749 / 500000000) := by
  have h := checkLog_sound (w := (1769 / 12009)) (n := 12)
    (lo := (296771497 / 1000000000)) (hi := (148385749 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6889 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6889 / 5120) = 1/(5120 / 6889) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (296771497 / 1000000000) (148385749 / 500000000) (Real.log (6889 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6889 / 5120) = -Real.log (5120 / 6889) := by
    rw [show ((6889 / 5120) : ℝ) = ((5120 / 6889) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (42389563 / 100000000) ≤ -Real.log (3351 / 5120) ∧
    -Real.log (3351 / 5120) ≤ (423895631 / 1000000000) := by
  have h := checkLog_sound (w := (1769 / 8471)) (n := 12)
    (lo := (42389563 / 100000000)) (hi := (423895631 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3351) = 1/(3351 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-423895631 / 1000000000) (-42389563 / 100000000) (Real.log (3351 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (11853437 / 40000000) ≤ -Real.log (2560 / 3443) ∧
    -Real.log (2560 / 3443) ≤ (148167963 / 500000000) := by
  have h := checkLog_sound (w := (883 / 6003)) (n := 12)
    (lo := (11853437 / 40000000)) (hi := (148167963 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3443 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3443 / 2560) = 1/(2560 / 3443) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (11853437 / 40000000) (148167963 / 500000000) (Real.log (3443 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3443 / 2560) = -Real.log (2560 / 3443) := by
    rw [show ((3443 / 2560) : ℝ) = ((2560 / 3443) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (16920031 / 40000000) ≤ -Real.log (1677 / 2560) ∧
    -Real.log (1677 / 2560) ≤ (52875097 / 125000000) := by
  have h := checkLog_sound (w := (883 / 4237)) (n := 12)
    (lo := (16920031 / 40000000)) (hi := (52875097 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1677) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1677) = 1/(1677 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-52875097 / 125000000) (-16920031 / 40000000) (Real.log (1677 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (219271263 / 1000000000) ≤ -Real.log (1000000 / 1245169) ∧
    -Real.log (1000000 / 1245169) ≤ (6852227 / 31250000) := by
  have h := checkLog_sound (w := (245169 / 2245169)) (n := 12)
    (lo := (219271263 / 1000000000)) (hi := (6852227 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1245169 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1245169 / 1000000) = 1/(1000000 / 1245169) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (219271263 / 1000000000) (6852227 / 31250000) (Real.log (1245169 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1245169 / 1000000) = -Real.log (1000000 / 1245169) := by
    rw [show ((1245169 / 1000000) : ℝ) = ((1000000 / 1245169) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (56252279 / 200000000) ≤ -Real.log (754831 / 1000000) ∧
    -Real.log (754831 / 1000000) ≤ (70315349 / 250000000) := by
  have h := checkLog_sound (w := (245169 / 1754831)) (n := 12)
    (lo := (56252279 / 200000000)) (hi := (70315349 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 754831) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 754831) = 1/(754831 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-70315349 / 250000000) (-56252279 / 200000000) (Real.log (754831 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (54902529 / 250000000) ≤ -Real.log (1000000 / 1245591) ∧
    -Real.log (1000000 / 1245591) ≤ (219610117 / 1000000000) := by
  have h := checkLog_sound (w := (245591 / 2245591)) (n := 12)
    (lo := (54902529 / 250000000)) (hi := (219610117 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1245591 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1245591 / 1000000) = 1/(1000000 / 1245591) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (54902529 / 250000000) (219610117 / 1000000000) (Real.log (1245591 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1245591 / 1000000) = -Real.log (1000000 / 1245591) := by
    rw [show ((1245591 / 1000000) : ℝ) = ((1000000 / 1245591) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (281820617 / 1000000000) ≤ -Real.log (754409 / 1000000) ∧
    -Real.log (754409 / 1000000) ≤ (140910309 / 500000000) := by
  have h := checkLog_sound (w := (245591 / 1754409)) (n := 12)
    (lo := (281820617 / 1000000000)) (hi := (140910309 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 754409) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 754409) = 1/(754409 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-140910309 / 500000000) (-281820617 / 1000000000) (Real.log (754409 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (81185259 / 500000000) ≤ -Real.log (125000 / 147037) ∧
    -Real.log (125000 / 147037) ≤ (162370519 / 1000000000) := by
  have h := checkLog_sound (w := (22037 / 272037)) (n := 12)
    (lo := (81185259 / 500000000)) (hi := (162370519 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((147037 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(147037 / 125000) = 1/(125000 / 147037) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (81185259 / 500000000) (162370519 / 1000000000) (Real.log (147037 / 125000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (147037 / 125000) = -Real.log (125000 / 147037) := by
    rw [show ((147037 / 125000) : ℝ) = ((125000 / 147037) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (48486009 / 250000000) ≤ -Real.log (102963 / 125000) ∧
    -Real.log (102963 / 125000) ≤ (193944037 / 1000000000) := by
  have h := checkLog_sound (w := (22037 / 227963)) (n := 12)
    (lo := (48486009 / 250000000)) (hi := (193944037 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 102963) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 102963) = 1/(102963 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-193944037 / 1000000000) (-48486009 / 250000000) (Real.log (102963 / 125000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (81318711 / 500000000) ≤ -Real.log (100000 / 117661) ∧
    -Real.log (100000 / 117661) ≤ (162637423 / 1000000000) := by
  have h := checkLog_sound (w := (17661 / 217661)) (n := 12)
    (lo := (81318711 / 500000000)) (hi := (162637423 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((117661 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(117661 / 100000) = 1/(100000 / 117661) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (81318711 / 500000000) (162637423 / 1000000000) (Real.log (117661 / 100000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (117661 / 100000) = -Real.log (100000 / 117661) := by
    rw [show ((117661 / 100000) : ℝ) = ((100000 / 117661) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (97162657 / 500000000) ≤ -Real.log (82339 / 100000) ∧
    -Real.log (82339 / 100000) ≤ (38865063 / 200000000) := by
  have h := checkLog_sound (w := (17661 / 182339)) (n := 12)
    (lo := (97162657 / 500000000)) (hi := (38865063 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 82339) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 82339) = 1/(82339 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-38865063 / 200000000) (-97162657 / 500000000) (Real.log (82339 / 100000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (7193367 / 10000000) ≤ -Real.log (500000000000 / 1026535480023) ∧
    -Real.log (500000000000 / 1026535480023) ≤ (359668351 / 500000000) := by
  have h := checkLog_sound (w := (26535480023 / 2026535480023)) (n := 12)
    (lo := (327369 / 12500000)) (hi := (26189521 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1026535480023 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1026535480023 / 1000000000000) = 1/(500000000000 / 1026535480023) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (7193367 / 10000000) (359668351 / 500000000) (Real.log (1026535480023 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1026535480023 / 500000000000) = -Real.log (500000000000 / 1026535480023) := by
    rw [show ((1026535480023 / 500000000000) : ℝ) = ((500000000000 / 1026535480023) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (720667127 / 1000000000) ≤ -Real.log (500000000000 / 1027902118771) ∧
    -Real.log (500000000000 / 1027902118771) ≤ (720667129 / 1000000000) := by
  have h := checkLog_sound (w := (27902118771 / 2027902118771)) (n := 12)
    (lo := (27519947 / 1000000000)) (hi := (6879987 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1027902118771 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1027902118771 / 1000000000000) = 1/(500000000000 / 1027902118771) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (720667127 / 1000000000) (720667129 / 1000000000) (Real.log (1027902118771 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (1027902118771 / 500000000000) = -Real.log (500000000000 / 1027902118771) := by
    rw [show ((1027902118771 / 500000000000) : ℝ) = ((500000000000 / 1027902118771) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (500532659 / 1000000000) ≤ -Real.log (500000000000 / 824799855861) ∧
    -Real.log (500000000000 / 824799855861) ≤ (25026633 / 50000000) := by
  have h := checkLog_sound (w := (324799855861 / 1324799855861)) (n := 12)
    (lo := (500532659 / 1000000000)) (hi := (25026633 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((824799855861 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(824799855861 / 500000000000) = 1/(500000000000 / 824799855861) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (500532659 / 1000000000) (25026633 / 50000000) (Real.log (824799855861 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (824799855861 / 500000000000) = -Real.log (500000000000 / 824799855861) := by
    rw [show ((824799855861 / 500000000000) : ℝ) = ((500000000000 / 824799855861) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (501430733 / 1000000000) ≤ -Real.log (500000000000 / 825540920111) ∧
    -Real.log (500000000000 / 825540920111) ≤ (250715367 / 500000000) := by
  have h := checkLog_sound (w := (325540920111 / 1325540920111)) (n := 12)
    (lo := (501430733 / 1000000000)) (hi := (250715367 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((825540920111 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(825540920111 / 500000000000) = 1/(500000000000 / 825540920111) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (501430733 / 1000000000) (250715367 / 500000000) (Real.log (825540920111 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (825540920111 / 500000000000) = -Real.log (500000000000 / 825540920111) := by
    rw [show ((825540920111 / 500000000000) : ℝ) = ((500000000000 / 825540920111) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (71262911 / 200000000) ≤ -Real.log (500000000000 / 714028340277) ∧
    -Real.log (500000000000 / 714028340277) ≤ (89078639 / 250000000) := by
  have h := checkLog_sound (w := (214028340277 / 1214028340277)) (n := 12)
    (lo := (71262911 / 200000000)) (hi := (89078639 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((714028340277 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(714028340277 / 500000000000) = 1/(500000000000 / 714028340277) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (71262911 / 200000000) (89078639 / 250000000) (Real.log (714028340277 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (714028340277 / 500000000000) = -Real.log (500000000000 / 714028340277) := by
    rw [show ((714028340277 / 500000000000) : ℝ) = ((500000000000 / 714028340277) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (22310171 / 62500000) ≤ -Real.log (100000000000 / 142898262063) ∧
    -Real.log (100000000000 / 142898262063) ≤ (356962737 / 1000000000) := by
  have h := checkLog_sound (w := (42898262063 / 242898262063)) (n := 12)
    (lo := (22310171 / 62500000)) (hi := (356962737 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((142898262063 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(142898262063 / 100000000000) = 1/(100000000000 / 142898262063) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (22310171 / 62500000) (356962737 / 1000000000) (Real.log (142898262063 / 100000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (142898262063 / 100000000000) = -Real.log (100000000000 / 142898262063) := by
    rw [show ((142898262063 / 100000000000) : ℝ) = ((100000000000 / 142898262063) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (7921973 / 250000000) ≤ -Real.log (9688089079 / 10000000000) ∧
    -Real.log (9688089079 / 10000000000) ≤ (31687893 / 1000000000) := by
  have h := checkLog_sound (w := (311910921 / 19688089079)) (n := 12)
    (lo := (7921973 / 250000000)) (hi := (31687893 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 9688089079) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 9688089079) = 1/(9688089079 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-31687893 / 1000000000) (-7921973 / 250000000) (Real.log (9688089079 / 10000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (15786759 / 500000000) ≤ -Real.log (15139370631 / 15625000000) ∧
    -Real.log (15139370631 / 15625000000) ≤ (31573519 / 1000000000) := by
  have h := checkLog_sound (w := (485629369 / 30764370631)) (n := 12)
    (lo := (15786759 / 500000000)) (hi := (31573519 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 15139370631) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 15139370631) = 1/(15139370631 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-31573519 / 1000000000) (-15786759 / 500000000) (Real.log (15139370631 / 15625000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell162
