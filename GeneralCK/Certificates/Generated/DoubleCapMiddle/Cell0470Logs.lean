import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0470
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

theorem reflection_log_1_neg : (36708303 / 200000000) ≤ -Real.log (10240 / 12303) ∧
    -Real.log (10240 / 12303) ≤ (45885379 / 250000000) := by
  have h := checkLog_sound (w := (2063 / 22543)) (n := 12)
    (lo := (36708303 / 200000000)) (hi := (45885379 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12303 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12303 / 10240) = 1/(10240 / 12303) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (36708303 / 200000000) (45885379 / 250000000) (Real.log (12303 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12303 / 10240) = -Real.log (10240 / 12303) := by
    rw [show ((12303 / 10240) : ℝ) = ((10240 / 12303) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (56244071 / 250000000) ≤ -Real.log (8177 / 10240) ∧
    -Real.log (8177 / 10240) ≤ (44995257 / 200000000) := by
  have h := checkLog_sound (w := (2063 / 18417)) (n := 12)
    (lo := (56244071 / 250000000)) (hi := (44995257 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 8177) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 8177) = 1/(8177 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-44995257 / 200000000) (-56244071 / 250000000) (Real.log (8177 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (91709793 / 500000000) ≤ -Real.log (20480 / 24603) ∧
    -Real.log (20480 / 24603) ≤ (183419587 / 1000000000) := by
  have h := checkLog_sound (w := (4123 / 45083)) (n := 12)
    (lo := (91709793 / 500000000)) (hi := (183419587 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24603 / 20480) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24603 / 20480) = 1/(20480 / 24603) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (91709793 / 500000000) (183419587 / 1000000000) (Real.log (24603 / 20480)) := by
  have h := reflection_log_3_neg
  have he : Real.log (24603 / 20480) = -Real.log (20480 / 24603) := by
    rw [show ((24603 / 20480) : ℝ) = ((20480 / 24603) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (224792859 / 1000000000) ≤ -Real.log (16357 / 20480) ∧
    -Real.log (16357 / 20480) ≤ (11239643 / 50000000) := by
  have h := checkLog_sound (w := (4123 / 36837)) (n := 12)
    (lo := (224792859 / 1000000000)) (hi := (11239643 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20480 / 16357) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20480 / 16357) = 1/(16357 / 20480) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-11239643 / 50000000) (-224792859 / 1000000000) (Real.log (16357 / 20480)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (84640671 / 250000000) ≤ -Real.log (5120 / 7183) ∧
    -Real.log (5120 / 7183) ≤ (67712537 / 200000000) := by
  have h := checkLog_sound (w := (2063 / 12303)) (n := 12)
    (lo := (84640671 / 250000000)) (hi := (67712537 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7183 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7183 / 5120) = 1/(5120 / 7183) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (84640671 / 250000000) (67712537 / 200000000) (Real.log (7183 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (7183 / 5120) = -Real.log (5120 / 7183) := by
    rw [show ((7183 / 5120) : ℝ) = ((5120 / 7183) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (128930099 / 250000000) ≤ -Real.log (3057 / 5120) ∧
    -Real.log (3057 / 5120) ≤ (515720397 / 1000000000) := by
  have h := checkLog_sound (w := (2063 / 8177)) (n := 12)
    (lo := (128930099 / 250000000)) (hi := (515720397 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3057) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3057) = 1/(3057 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-515720397 / 1000000000) (-128930099 / 250000000) (Real.log (3057 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (67670767 / 200000000) ≤ -Real.log (10240 / 14363) ∧
    -Real.log (10240 / 14363) ≤ (84588459 / 250000000) := by
  have h := checkLog_sound (w := (4123 / 24603)) (n := 12)
    (lo := (67670767 / 200000000)) (hi := (84588459 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((14363 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(14363 / 10240) = 1/(10240 / 14363) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (67670767 / 200000000) (84588459 / 250000000) (Real.log (14363 / 10240)) := by
  have h := reflection_log_7_neg
  have he : Real.log (14363 / 10240) = -Real.log (10240 / 14363) := by
    rw [show ((14363 / 10240) : ℝ) = ((10240 / 14363) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (515229839 / 1000000000) ≤ -Real.log (6117 / 10240) ∧
    -Real.log (6117 / 10240) ≤ (6440373 / 12500000) := by
  have h := checkLog_sound (w := (4123 / 16357)) (n := 12)
    (lo := (515229839 / 1000000000)) (hi := (6440373 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 6117) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 6117) = 1/(6117 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-6440373 / 12500000) (-515229839 / 1000000000) (Real.log (6117 / 10240)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (252135979 / 1000000000) ≤ -Real.log (1000000 / 1286771) ∧
    -Real.log (1000000 / 1286771) ≤ (12606799 / 50000000) := by
  have h := checkLog_sound (w := (286771 / 2286771)) (n := 12)
    (lo := (252135979 / 1000000000)) (hi := (12606799 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1286771 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1286771 / 1000000) = 1/(1000000 / 1286771) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (252135979 / 1000000000) (12606799 / 50000000) (Real.log (1286771 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1286771 / 1000000) = -Real.log (1000000 / 1286771) := by
    rw [show ((1286771 / 1000000) : ℝ) = ((1000000 / 1286771) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (84488183 / 250000000) ≤ -Real.log (713229 / 1000000) ∧
    -Real.log (713229 / 1000000) ≤ (337952733 / 1000000000) := by
  have h := checkLog_sound (w := (286771 / 1713229)) (n := 12)
    (lo := (84488183 / 250000000)) (hi := (337952733 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 713229) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 713229) = 1/(713229 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-337952733 / 1000000000) (-84488183 / 250000000) (Real.log (713229 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (31537687 / 125000000) ≤ -Real.log (125000 / 160873) ∧
    -Real.log (125000 / 160873) ≤ (252301497 / 1000000000) := by
  have h := checkLog_sound (w := (35873 / 285873)) (n := 12)
    (lo := (31537687 / 125000000)) (hi := (252301497 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160873 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(160873 / 125000) = 1/(125000 / 160873) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (31537687 / 125000000) (252301497 / 1000000000) (Real.log (160873 / 125000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (160873 / 125000) = -Real.log (125000 / 160873) := by
    rw [show ((160873 / 125000) : ℝ) = ((125000 / 160873) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (169125709 / 500000000) ≤ -Real.log (89127 / 125000) ∧
    -Real.log (89127 / 125000) ≤ (338251419 / 1000000000) := by
  have h := checkLog_sound (w := (35873 / 214127)) (n := 12)
    (lo := (169125709 / 500000000)) (hi := (338251419 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 89127) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 89127) = 1/(89127 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-338251419 / 1000000000) (-169125709 / 500000000) (Real.log (89127 / 125000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (188554591 / 1000000000) ≤ -Real.log (1000000 / 1207503) ∧
    -Real.log (1000000 / 1207503) ≤ (5892331 / 31250000) := by
  have h := checkLog_sound (w := (207503 / 2207503)) (n := 12)
    (lo := (188554591 / 1000000000)) (hi := (5892331 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1207503 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1207503 / 1000000) = 1/(1000000 / 1207503) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (188554591 / 1000000000) (5892331 / 31250000) (Real.log (1207503 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1207503 / 1000000) = -Real.log (1000000 / 1207503) := by
    rw [show ((1207503 / 1000000) : ℝ) = ((1000000 / 1207503) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (116283279 / 500000000) ≤ -Real.log (792497 / 1000000) ∧
    -Real.log (792497 / 1000000) ≤ (232566559 / 1000000000) := by
  have h := checkLog_sound (w := (207503 / 1792497)) (n := 12)
    (lo := (116283279 / 500000000)) (hi := (232566559 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 792497) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 792497) = 1/(792497 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-232566559 / 1000000000) (-116283279 / 500000000) (Real.log (792497 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (188688743 / 1000000000) ≤ -Real.log (200000 / 241533) ∧
    -Real.log (200000 / 241533) ≤ (23586093 / 125000000) := by
  have h := checkLog_sound (w := (41533 / 441533)) (n := 12)
    (lo := (188688743 / 1000000000)) (hi := (23586093 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((241533 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(241533 / 200000) = 1/(200000 / 241533) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (188688743 / 1000000000) (23586093 / 125000000) (Real.log (241533 / 200000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (241533 / 200000) = -Real.log (200000 / 241533) := by
    rw [show ((241533 / 200000) : ℝ) = ((200000 / 241533) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (58192749 / 250000000) ≤ -Real.log (158467 / 200000) ∧
    -Real.log (158467 / 200000) ≤ (232770997 / 1000000000) := by
  have h := checkLog_sound (w := (41533 / 358467)) (n := 12)
    (lo := (58192749 / 250000000)) (hi := (232770997 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 158467) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 158467) = 1/(158467 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-232770997 / 1000000000) (-58192749 / 250000000) (Real.log (158467 / 200000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (590088711 / 1000000000) ≤ -Real.log (500000000000 / 902074228613) ∧
    -Real.log (500000000000 / 902074228613) ≤ (73761089 / 125000000) := by
  have h := checkLog_sound (w := (402074228613 / 1402074228613)) (n := 12)
    (lo := (590088711 / 1000000000)) (hi := (73761089 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((902074228613 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(902074228613 / 500000000000) = 1/(500000000000 / 902074228613) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (590088711 / 1000000000) (73761089 / 125000000) (Real.log (902074228613 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (902074228613 / 500000000000) = -Real.log (500000000000 / 902074228613) := by
    rw [show ((902074228613 / 500000000000) : ℝ) = ((500000000000 / 902074228613) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (295276457 / 500000000) ≤ -Real.log (100000000000 / 180498614337) ∧
    -Real.log (100000000000 / 180498614337) ≤ (118110583 / 200000000) := by
  have h := checkLog_sound (w := (80498614337 / 280498614337)) (n := 12)
    (lo := (295276457 / 500000000)) (hi := (118110583 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((180498614337 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(180498614337 / 100000000000) = 1/(100000000000 / 180498614337) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (295276457 / 500000000) (118110583 / 200000000) (Real.log (180498614337 / 100000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (180498614337 / 100000000000) = -Real.log (100000000000 / 180498614337) := by
    rw [show ((180498614337 / 100000000000) : ℝ) = ((100000000000 / 180498614337) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (421121149 / 1000000000) ≤ -Real.log (500000000000 / 761834429657) ∧
    -Real.log (500000000000 / 761834429657) ≤ (8422423 / 20000000) := by
  have h := checkLog_sound (w := (261834429657 / 1261834429657)) (n := 12)
    (lo := (421121149 / 1000000000)) (hi := (8422423 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((761834429657 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(761834429657 / 500000000000) = 1/(500000000000 / 761834429657) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (421121149 / 1000000000) (8422423 / 20000000) (Real.log (761834429657 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (761834429657 / 500000000000) = -Real.log (500000000000 / 761834429657) := by
    rw [show ((761834429657 / 500000000000) : ℝ) = ((500000000000 / 761834429657) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (421459739 / 1000000000) ≤ -Real.log (500000000000 / 762092423029) ∧
    -Real.log (500000000000 / 762092423029) ≤ (21072987 / 50000000) := by
  have h := checkLog_sound (w := (262092423029 / 1262092423029)) (n := 12)
    (lo := (421459739 / 1000000000)) (hi := (21072987 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((762092423029 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(762092423029 / 500000000000) = 1/(500000000000 / 762092423029) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (421459739 / 1000000000) (21072987 / 50000000) (Real.log (762092423029 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (762092423029 / 500000000000) = -Real.log (500000000000 / 762092423029) := by
    rw [show ((762092423029 / 500000000000) : ℝ) = ((500000000000 / 762092423029) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0470
