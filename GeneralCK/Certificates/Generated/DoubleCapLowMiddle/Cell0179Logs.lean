import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0179
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

theorem reflection_log_1_neg : (627608159 / 1000000000) ≤ -Real.log (1600 / 2997) ∧
    -Real.log (1600 / 2997) ≤ (3922551 / 6250000) := by
  have h := checkLog_sound (w := (1397 / 4597)) (n := 12)
    (lo := (627608159 / 1000000000)) (hi := (3922551 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2997 / 1600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2997 / 1600) = 1/(1600 / 2997) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (627608159 / 1000000000) (3922551 / 6250000) (Real.log (2997 / 1600)) := by
  have h := reflection_log_1_neg
  have he : Real.log (2997 / 1600) = -Real.log (1600 / 2997) := by
    rw [show ((2997 / 1600) : ℝ) = ((1600 / 2997) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (64517279 / 31250000) ≤ -Real.log (203 / 1600) ∧
    -Real.log (203 / 1600) ≤ (2064552931 / 1000000000) := by
  have h := checkLog_sound (w := (197 / 603)) (n := 12)
    (lo := (84782321 / 125000000)) (hi := (678258569 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 203) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(400 / 203) = 1/(203 / 1600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-2064552931 / 1000000000) (-64517279 / 31250000) (Real.log (203 / 1600)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (626021983 / 1000000000) ≤ -Real.log (6400 / 11969) ∧
    -Real.log (6400 / 11969) ≤ (19563187 / 31250000) := by
  have h := checkLog_sound (w := (5569 / 18369)) (n := 12)
    (lo := (626021983 / 1000000000)) (hi := (19563187 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11969 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11969 / 6400) = 1/(6400 / 11969) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (626021983 / 1000000000) (19563187 / 31250000) (Real.log (11969 / 6400)) := by
  have h := reflection_log_3_neg
  have he : Real.log (11969 / 6400) = -Real.log (6400 / 11969) := by
    rw [show ((11969 / 6400) : ℝ) = ((6400 / 11969) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (2041423473 / 1000000000) ≤ -Real.log (831 / 6400) ∧
    -Real.log (831 / 6400) ≤ (510355869 / 250000000) := by
  have h := checkLog_sound (w := (769 / 2431)) (n := 12)
    (lo := (655129113 / 1000000000)) (hi := (327564557 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 831) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1600 / 831) = 1/(831 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-510355869 / 250000000) (-2041423473 / 1000000000) (Real.log (831 / 6400)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (557470631 / 1000000000) ≤ -Real.log (800 / 1397) ∧
    -Real.log (800 / 1397) ≤ (69683829 / 125000000) := by
  have h := checkLog_sound (w := (597 / 2197)) (n := 12)
    (lo := (557470631 / 1000000000)) (hi := (69683829 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1397 / 800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1397 / 800) = 1/(800 / 1397) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (557470631 / 1000000000) (69683829 / 125000000) (Real.log (1397 / 800)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1397 / 800) = -Real.log (800 / 1397) := by
    rw [show ((1397 / 800) : ℝ) = ((800 / 1397) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (342851437 / 250000000) ≤ -Real.log (203 / 800) ∧
    -Real.log (203 / 800) ≤ (5485623 / 4000000) := by
  have h := checkLog_sound (w := (197 / 603)) (n := 12)
    (lo := (84782321 / 125000000)) (hi := (678258569 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 203) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(400 / 203) = 1/(203 / 800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-5485623 / 4000000) (-342851437 / 250000000) (Real.log (203 / 800)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (277032347 / 500000000) ≤ -Real.log (3200 / 5569) ∧
    -Real.log (3200 / 5569) ≤ (110812939 / 200000000) := by
  have h := checkLog_sound (w := (2369 / 8769)) (n := 12)
    (lo := (277032347 / 500000000)) (hi := (110812939 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5569 / 3200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5569 / 3200) = 1/(3200 / 5569) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (277032347 / 500000000) (110812939 / 200000000) (Real.log (5569 / 3200)) := by
  have h := reflection_log_7_neg
  have he : Real.log (5569 / 3200) = -Real.log (3200 / 5569) := by
    rw [show ((5569 / 3200) : ℝ) = ((3200 / 5569) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (1348276293 / 1000000000) ≤ -Real.log (831 / 3200) ∧
    -Real.log (831 / 3200) ≤ (269655259 / 200000000) := by
  have h := checkLog_sound (w := (769 / 2431)) (n := 12)
    (lo := (655129113 / 1000000000)) (hi := (327564557 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 831) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1600 / 831) = 1/(831 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-269655259 / 200000000) (-1348276293 / 1000000000) (Real.log (831 / 3200)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (643794633 / 1000000000) ≤ -Real.log (1000000 / 1903691) ∧
    -Real.log (1000000 / 1903691) ≤ (321897317 / 500000000) := by
  have h := checkLog_sound (w := (903691 / 2903691)) (n := 12)
    (lo := (643794633 / 1000000000)) (hi := (321897317 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1903691 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1903691 / 1000000) = 1/(1000000 / 1903691) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (643794633 / 1000000000) (321897317 / 500000000) (Real.log (1903691 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1903691 / 1000000) = -Real.log (1000000 / 1903691) := by
    rw [show ((1903691 / 1000000) : ℝ) = ((1000000 / 1903691) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (73131047 / 31250000) ≤ -Real.log (96309 / 1000000) ∧
    -Real.log (96309 / 1000000) ≤ (585048377 / 250000000) := by
  have h := checkLog_sound (w := (28691 / 221309)) (n := 12)
    (lo := (65187991 / 250000000)) (hi := (52150393 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 96309) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125000 / 96309) = 1/(96309 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-585048377 / 250000000) (-73131047 / 31250000) (Real.log (96309 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (161198049 / 250000000) ≤ -Real.log (1000000 / 1905591) ∧
    -Real.log (1000000 / 1905591) ≤ (644792197 / 1000000000) := by
  have h := checkLog_sound (w := (905591 / 2905591)) (n := 12)
    (lo := (161198049 / 250000000)) (hi := (644792197 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1905591 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1905591 / 1000000) = 1/(1000000 / 1905591) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (161198049 / 250000000) (644792197 / 1000000000) (Real.log (1905591 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1905591 / 1000000) = -Real.log (1000000 / 1905591) := by
    rw [show ((1905591 / 1000000) : ℝ) = ((1000000 / 1905591) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (2360118869 / 1000000000) ≤ -Real.log (94409 / 1000000) ∧
    -Real.log (94409 / 1000000) ≤ (2360118873 / 1000000000) := by
  have h := checkLog_sound (w := (30591 / 219409)) (n := 12)
    (lo := (280677329 / 1000000000)) (hi := (28067733 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 94409) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125000 / 94409) = 1/(94409 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-2360118873 / 1000000000) (-2360118869 / 1000000000) (Real.log (94409 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (641495927 / 1000000000) ≤ -Real.log (25000 / 47483) ∧
    -Real.log (25000 / 47483) ≤ (80186991 / 125000000) := by
  have h := checkLog_sound (w := (22483 / 72483)) (n := 12)
    (lo := (641495927 / 1000000000)) (hi := (80186991 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((47483 / 25000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(47483 / 25000) = 1/(25000 / 47483) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (641495927 / 1000000000) (80186991 / 125000000) (Real.log (47483 / 25000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (47483 / 25000) = -Real.log (25000 / 47483) := by
    rw [show ((47483 / 25000) : ℝ) = ((25000 / 47483) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (2295808107 / 1000000000) ≤ -Real.log (2517 / 25000) ∧
    -Real.log (2517 / 25000) ≤ (2295808111 / 1000000000) := by
  have h := checkLog_sound (w := (304 / 2821)) (n := 12)
    (lo := (216366567 / 1000000000)) (hi := (27045821 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3125 / 2517) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(3125 / 2517) = 1/(2517 / 25000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-2295808111 / 1000000000) (-2295808107 / 1000000000) (Real.log (2517 / 25000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (160654451 / 250000000) ≤ -Real.log (250000 / 475363) ∧
    -Real.log (250000 / 475363) ≤ (128523561 / 200000000) := by
  have h := checkLog_sound (w := (225363 / 725363)) (n := 12)
    (lo := (160654451 / 250000000)) (hi := (128523561 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((475363 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(475363 / 250000) = 1/(250000 / 475363) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (160654451 / 250000000) (128523561 / 200000000) (Real.log (475363 / 250000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (475363 / 250000) = -Real.log (250000 / 475363) := by
    rw [show ((475363 / 250000) : ℝ) = ((250000 / 475363) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (1158605769 / 500000000) ≤ -Real.log (24637 / 250000) ∧
    -Real.log (24637 / 250000) ≤ (1158605771 / 500000000) := by
  have h := checkLog_sound (w := (6613 / 55887)) (n := 12)
    (lo := (118884999 / 500000000)) (hi := (237769999 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 24637) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(31250 / 24637) = 1/(24637 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-1158605771 / 500000000) (-1158605769 / 500000000) (Real.log (24637 / 250000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (2983988137 / 1000000000) ≤ -Real.log (125000000000 / 2470811398727) ∧
    -Real.log (125000000000 / 2470811398727) ≤ (1491994071 / 500000000) := by
  have h := checkLog_sound (w := (470811398727 / 4470811398727)) (n := 12)
    (lo := (211399417 / 1000000000)) (hi := (105699709 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2470811398727 / 2000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(2470811398727 / 2000000000000) = 1/(125000000000 / 2470811398727) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (2983988137 / 1000000000) (1491994071 / 500000000) (Real.log (2470811398727 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (2470811398727 / 125000000000) = -Real.log (125000000000 / 2470811398727) := by
    rw [show ((2470811398727 / 125000000000) : ℝ) = ((125000000000 / 2470811398727) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (600982213 / 200000000) ≤ -Real.log (500000000000 / 10092210488407) ∧
    -Real.log (500000000000 / 10092210488407) ≤ (300491107 / 100000000) := by
  have h := checkLog_sound (w := (2092210488407 / 18092210488407)) (n := 12)
    (lo := (46464469 / 200000000)) (hi := (116161173 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10092210488407 / 8000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(10092210488407 / 8000000000000) = 1/(500000000000 / 10092210488407) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (600982213 / 200000000) (300491107 / 100000000) (Real.log (10092210488407 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (10092210488407 / 500000000000) = -Real.log (500000000000 / 10092210488407) := by
    rw [show ((10092210488407 / 500000000000) : ℝ) = ((500000000000 / 10092210488407) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (2937304033 / 1000000000) ≤ -Real.log (125000000000 / 2358114819229) ∧
    -Real.log (125000000000 / 2358114819229) ≤ (1468652019 / 500000000) := by
  have h := checkLog_sound (w := (358114819229 / 4358114819229)) (n := 12)
    (lo := (164715313 / 1000000000)) (hi := (82357657 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2358114819229 / 2000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(2358114819229 / 2000000000000) = 1/(125000000000 / 2358114819229) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (2937304033 / 1000000000) (1468652019 / 500000000) (Real.log (2358114819229 / 125000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (2358114819229 / 125000000000) = -Real.log (125000000000 / 2358114819229) := by
    rw [show ((2358114819229 / 125000000000) : ℝ) = ((125000000000 / 2358114819229) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (1479914671 / 500000000) ≤ -Real.log (250000000000 / 4823669683809) ∧
    -Real.log (250000000000 / 4823669683809) ≤ (2959829347 / 1000000000) := by
  have h := checkLog_sound (w := (823669683809 / 8823669683809)) (n := 12)
    (lo := (93620311 / 500000000)) (hi := (187240623 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4823669683809 / 4000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(4823669683809 / 4000000000000) = 1/(250000000000 / 4823669683809) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (1479914671 / 500000000) (2959829347 / 1000000000) (Real.log (4823669683809 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (4823669683809 / 250000000000) = -Real.log (250000000000 / 4823669683809) := by
    rw [show ((4823669683809 / 250000000000) : ℝ) = ((250000000000 / 4823669683809) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0179
