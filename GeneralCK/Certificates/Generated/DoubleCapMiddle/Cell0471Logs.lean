import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0471
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

theorem reflection_log_1_neg : (91709793 / 500000000) ≤ -Real.log (20480 / 24603) ∧
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


theorem reflection_log_1 : Bounds (91709793 / 500000000) (183419587 / 1000000000) (Real.log (24603 / 20480)) := by
  have h := reflection_log_1_neg
  have he : Real.log (24603 / 20480) = -Real.log (20480 / 24603) := by
    rw [show ((24603 / 20480) : ℝ) = ((20480 / 24603) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (224792859 / 1000000000) ≤ -Real.log (16357 / 20480) ∧
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


theorem reflection_log_2 : Bounds (-11239643 / 50000000) (-224792859 / 1000000000) (Real.log (16357 / 20480)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (91648821 / 500000000) ≤ -Real.log (512 / 615) ∧
    -Real.log (512 / 615) ≤ (183297643 / 1000000000) := by
  have h := checkLog_sound (w := (103 / 1127)) (n := 12)
    (lo := (91648821 / 500000000)) (hi := (183297643 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((615 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(615 / 512) = 1/(512 / 615) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (91648821 / 500000000) (183297643 / 1000000000) (Real.log (615 / 512)) := by
  have h := reflection_log_3_neg
  have he : Real.log (615 / 512) = -Real.log (512 / 615) := by
    rw [show ((615 / 512) : ℝ) = ((512 / 615) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (56152367 / 250000000) ≤ -Real.log (409 / 512) ∧
    -Real.log (409 / 512) ≤ (224609469 / 1000000000) := by
  have h := checkLog_sound (w := (103 / 921)) (n := 12)
    (lo := (56152367 / 250000000)) (hi := (224609469 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 409) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 409) = 1/(409 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-224609469 / 1000000000) (-56152367 / 250000000) (Real.log (409 / 512)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (67670767 / 200000000) ≤ -Real.log (10240 / 14363) ∧
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


theorem reflection_log_5 : Bounds (67670767 / 200000000) (84588459 / 250000000) (Real.log (14363 / 10240)) := by
  have h := reflection_log_5_neg
  have he : Real.log (14363 / 10240) = -Real.log (10240 / 14363) := by
    rw [show ((14363 / 10240) : ℝ) = ((10240 / 14363) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (515229839 / 1000000000) ≤ -Real.log (6117 / 10240) ∧
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


theorem reflection_log_6 : Bounds (-6440373 / 12500000) (-515229839 / 1000000000) (Real.log (6117 / 10240)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (21134059 / 62500000) ≤ -Real.log (256 / 359) ∧
    -Real.log (256 / 359) ≤ (67628989 / 200000000) := by
  have h := checkLog_sound (w := (103 / 615)) (n := 12)
    (lo := (21134059 / 62500000)) (hi := (67628989 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((359 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(359 / 256) = 1/(256 / 359) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (21134059 / 62500000) (67628989 / 200000000) (Real.log (359 / 256)) := by
  have h := reflection_log_7_neg
  have he : Real.log (359 / 256) = -Real.log (256 / 359) := by
    rw [show ((359 / 256) : ℝ) = ((256 / 359) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (514739523 / 1000000000) ≤ -Real.log (153 / 256) ∧
    -Real.log (153 / 256) ≤ (128684881 / 250000000) := by
  have h := checkLog_sound (w := (103 / 409)) (n := 12)
    (lo := (514739523 / 1000000000)) (hi := (128684881 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((256 / 153) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(256 / 153) = 1/(153 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-128684881 / 250000000) (-514739523 / 1000000000) (Real.log (153 / 256)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (62992803 / 250000000) ≤ -Real.log (1000000 / 1286559) ∧
    -Real.log (1000000 / 1286559) ≤ (251971213 / 1000000000) := by
  have h := checkLog_sound (w := (286559 / 2286559)) (n := 12)
    (lo := (62992803 / 250000000)) (hi := (251971213 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1286559 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1286559 / 1000000) = 1/(1000000 / 1286559) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (62992803 / 250000000) (251971213 / 1000000000) (Real.log (1286559 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1286559 / 1000000) = -Real.log (1000000 / 1286559) := by
    rw [show ((1286559 / 1000000) : ℝ) = ((1000000 / 1286559) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (21103471 / 62500000) ≤ -Real.log (713441 / 1000000) ∧
    -Real.log (713441 / 1000000) ≤ (337655537 / 1000000000) := by
  have h := checkLog_sound (w := (286559 / 1713441)) (n := 12)
    (lo := (21103471 / 62500000)) (hi := (337655537 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 713441) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 713441) = 1/(713441 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-337655537 / 1000000000) (-21103471 / 62500000) (Real.log (713441 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (63034189 / 250000000) ≤ -Real.log (250000 / 321693) ∧
    -Real.log (250000 / 321693) ≤ (252136757 / 1000000000) := by
  have h := checkLog_sound (w := (71693 / 571693)) (n := 12)
    (lo := (63034189 / 250000000)) (hi := (252136757 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((321693 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(321693 / 250000) = 1/(250000 / 321693) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (63034189 / 250000000) (252136757 / 1000000000) (Real.log (321693 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (321693 / 250000) = -Real.log (250000 / 321693) := by
    rw [show ((321693 / 250000) : ℝ) = ((250000 / 321693) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (168977067 / 500000000) ≤ -Real.log (178307 / 250000) ∧
    -Real.log (178307 / 250000) ≤ (67590827 / 200000000) := by
  have h := checkLog_sound (w := (71693 / 428307)) (n := 12)
    (lo := (168977067 / 500000000)) (hi := (67590827 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 178307) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 178307) = 1/(178307 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-67590827 / 200000000) (-168977067 / 500000000) (Real.log (178307 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (188422077 / 1000000000) ≤ -Real.log (1000000 / 1207343) ∧
    -Real.log (1000000 / 1207343) ≤ (94211039 / 500000000) := by
  have h := checkLog_sound (w := (207343 / 2207343)) (n := 12)
    (lo := (188422077 / 1000000000)) (hi := (94211039 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1207343 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1207343 / 1000000) = 1/(1000000 / 1207343) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (188422077 / 1000000000) (94211039 / 500000000) (Real.log (1207343 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1207343 / 1000000) = -Real.log (1000000 / 1207343) := by
    rw [show ((1207343 / 1000000) : ℝ) = ((1000000 / 1207343) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (46472937 / 200000000) ≤ -Real.log (792657 / 1000000) ∧
    -Real.log (792657 / 1000000) ≤ (116182343 / 500000000) := by
  have h := checkLog_sound (w := (207343 / 1792657)) (n := 12)
    (lo := (46472937 / 200000000)) (hi := (116182343 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 792657) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 792657) = 1/(792657 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-116182343 / 500000000) (-46472937 / 200000000) (Real.log (792657 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (188555419 / 1000000000) ≤ -Real.log (62500 / 75469) ∧
    -Real.log (62500 / 75469) ≤ (9427771 / 50000000) := by
  have h := checkLog_sound (w := (12969 / 137969)) (n := 12)
    (lo := (188555419 / 1000000000)) (hi := (9427771 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((75469 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(75469 / 62500) = 1/(62500 / 75469) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (188555419 / 1000000000) (9427771 / 50000000) (Real.log (75469 / 62500)) := by
  have h := reflection_log_15_neg
  have he : Real.log (75469 / 62500) = -Real.log (62500 / 75469) := by
    rw [show ((75469 / 62500) : ℝ) = ((62500 / 75469) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (11628391 / 50000000) ≤ -Real.log (49531 / 62500) ∧
    -Real.log (49531 / 62500) ≤ (232567821 / 1000000000) := by
  have h := checkLog_sound (w := (12969 / 112031)) (n := 12)
    (lo := (11628391 / 50000000)) (hi := (232567821 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 49531) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 49531) = 1/(49531 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-232567821 / 1000000000) (-11628391 / 50000000) (Real.log (49531 / 62500)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (147406687 / 250000000) ≤ -Real.log (250000000000 / 450828800139) ∧
    -Real.log (250000000000 / 450828800139) ≤ (589626749 / 1000000000) := by
  have h := checkLog_sound (w := (200828800139 / 700828800139)) (n := 12)
    (lo := (147406687 / 250000000)) (hi := (589626749 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((450828800139 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(450828800139 / 250000000000) = 1/(250000000000 / 450828800139) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (147406687 / 250000000) (589626749 / 1000000000) (Real.log (450828800139 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (450828800139 / 250000000000) = -Real.log (250000000000 / 450828800139) := by
    rw [show ((450828800139 / 250000000000) : ℝ) = ((250000000000 / 450828800139) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (59009089 / 100000000) ≤ -Real.log (500000000000 / 902076194429) ∧
    -Real.log (500000000000 / 902076194429) ≤ (590090891 / 1000000000) := by
  have h := checkLog_sound (w := (402076194429 / 1402076194429)) (n := 12)
    (lo := (59009089 / 100000000)) (hi := (590090891 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((902076194429 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(902076194429 / 500000000000) = 1/(500000000000 / 902076194429) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (59009089 / 100000000) (590090891 / 1000000000) (Real.log (902076194429 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (902076194429 / 500000000000) = -Real.log (500000000000 / 902076194429) := by
    rw [show ((902076194429 / 500000000000) : ℝ) = ((500000000000 / 902076194429) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (210393381 / 500000000) ≤ -Real.log (500000000000 / 761579724899) ∧
    -Real.log (500000000000 / 761579724899) ≤ (420786763 / 1000000000) := by
  have h := checkLog_sound (w := (261579724899 / 1261579724899)) (n := 12)
    (lo := (210393381 / 500000000)) (hi := (420786763 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((761579724899 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(761579724899 / 500000000000) = 1/(500000000000 / 761579724899) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (210393381 / 500000000) (420786763 / 1000000000) (Real.log (761579724899 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (761579724899 / 500000000000) = -Real.log (500000000000 / 761579724899) := by
    rw [show ((761579724899 / 500000000000) : ℝ) = ((500000000000 / 761579724899) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (421123239 / 1000000000) ≤ -Real.log (250000000000 / 380918010943) ∧
    -Real.log (250000000000 / 380918010943) ≤ (10528081 / 25000000) := by
  have h := checkLog_sound (w := (130918010943 / 630918010943)) (n := 12)
    (lo := (421123239 / 1000000000)) (hi := (10528081 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((380918010943 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(380918010943 / 250000000000) = 1/(250000000000 / 380918010943) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (421123239 / 1000000000) (10528081 / 25000000) (Real.log (380918010943 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (380918010943 / 250000000000) = -Real.log (250000000000 / 380918010943) := by
    rw [show ((380918010943 / 250000000000) : ℝ) = ((250000000000 / 380918010943) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0471
