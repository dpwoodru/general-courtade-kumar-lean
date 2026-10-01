import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0472
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

theorem reflection_log_1_neg : (91648821 / 500000000) ≤ -Real.log (512 / 615) ∧
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


theorem reflection_log_1 : Bounds (91648821 / 500000000) (183297643 / 1000000000) (Real.log (615 / 512)) := by
  have h := reflection_log_1_neg
  have he : Real.log (615 / 512) = -Real.log (512 / 615) := by
    rw [show ((615 / 512) : ℝ) = ((512 / 615) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (56152367 / 250000000) ≤ -Real.log (409 / 512) ∧
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


theorem reflection_log_2 : Bounds (-224609469 / 1000000000) (-56152367 / 250000000) (Real.log (409 / 512)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (45793921 / 250000000) ≤ -Real.log (20480 / 24597) ∧
    -Real.log (20480 / 24597) ≤ (36635137 / 200000000) := by
  have h := checkLog_sound (w := (4117 / 45077)) (n := 12)
    (lo := (45793921 / 250000000)) (hi := (36635137 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24597 / 20480) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24597 / 20480) = 1/(20480 / 24597) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (45793921 / 250000000) (36635137 / 200000000) (Real.log (24597 / 20480)) := by
  have h := reflection_log_3_neg
  have he : Real.log (24597 / 20480) = -Real.log (20480 / 24597) := by
    rw [show ((24597 / 20480) : ℝ) = ((20480 / 24597) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (224426111 / 1000000000) ≤ -Real.log (16363 / 20480) ∧
    -Real.log (16363 / 20480) ≤ (1753329 / 7812500) := by
  have h := checkLog_sound (w := (4117 / 36843)) (n := 12)
    (lo := (224426111 / 1000000000)) (hi := (1753329 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20480 / 16363) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20480 / 16363) = 1/(16363 / 20480) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-1753329 / 7812500) (-224426111 / 1000000000) (Real.log (16363 / 20480)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (21134059 / 62500000) ≤ -Real.log (256 / 359) ∧
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


theorem reflection_log_5 : Bounds (21134059 / 62500000) (67628989 / 200000000) (Real.log (359 / 256)) := by
  have h := reflection_log_5_neg
  have he : Real.log (359 / 256) = -Real.log (256 / 359) := by
    rw [show ((359 / 256) : ℝ) = ((256 / 359) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (514739523 / 1000000000) ≤ -Real.log (153 / 256) ∧
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


theorem reflection_log_6 : Bounds (-128684881 / 250000000) (-514739523 / 1000000000) (Real.log (153 / 256)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (42242001 / 125000000) ≤ -Real.log (10240 / 14357) ∧
    -Real.log (10240 / 14357) ≤ (337936009 / 1000000000) := by
  have h := checkLog_sound (w := (4117 / 24597)) (n := 12)
    (lo := (42242001 / 125000000)) (hi := (337936009 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((14357 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(14357 / 10240) = 1/(10240 / 14357) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (42242001 / 125000000) (337936009 / 1000000000) (Real.log (14357 / 10240)) := by
  have h := reflection_log_7_neg
  have he : Real.log (14357 / 10240) = -Real.log (10240 / 14357) := by
    rw [show ((14357 / 10240) : ℝ) = ((10240 / 14357) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (514249447 / 1000000000) ≤ -Real.log (6123 / 10240) ∧
    -Real.log (6123 / 10240) ≤ (64281181 / 125000000) := by
  have h := checkLog_sound (w := (4117 / 16363)) (n := 12)
    (lo := (514249447 / 1000000000)) (hi := (64281181 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 6123) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 6123) = 1/(6123 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-64281181 / 125000000) (-514249447 / 1000000000) (Real.log (6123 / 10240)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (50361439 / 200000000) ≤ -Real.log (250000 / 321587) ∧
    -Real.log (250000 / 321587) ≤ (62951799 / 250000000) := by
  have h := checkLog_sound (w := (71587 / 571587)) (n := 12)
    (lo := (50361439 / 200000000)) (hi := (62951799 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((321587 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(321587 / 250000) = 1/(250000 / 321587) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (50361439 / 200000000) (62951799 / 250000000) (Real.log (321587 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (321587 / 250000) = -Real.log (250000 / 321587) := by
    rw [show ((321587 / 250000) : ℝ) = ((250000 / 321587) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (33735983 / 100000000) ≤ -Real.log (178413 / 250000) ∧
    -Real.log (178413 / 250000) ≤ (337359831 / 1000000000) := by
  have h := checkLog_sound (w := (71587 / 428413)) (n := 12)
    (lo := (33735983 / 100000000)) (hi := (337359831 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 178413) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 178413) = 1/(178413 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-337359831 / 1000000000) (-33735983 / 100000000) (Real.log (178413 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (251972767 / 1000000000) ≤ -Real.log (1000000 / 1286561) ∧
    -Real.log (1000000 / 1286561) ≤ (7874149 / 31250000) := by
  have h := checkLog_sound (w := (286561 / 2286561)) (n := 12)
    (lo := (251972767 / 1000000000)) (hi := (7874149 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1286561 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1286561 / 1000000) = 1/(1000000 / 1286561) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (251972767 / 1000000000) (7874149 / 31250000) (Real.log (1286561 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1286561 / 1000000) = -Real.log (1000000 / 1286561) := by
    rw [show ((1286561 / 1000000) : ℝ) = ((1000000 / 1286561) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (337658339 / 1000000000) ≤ -Real.log (713439 / 1000000) ∧
    -Real.log (713439 / 1000000) ≤ (16882917 / 50000000) := by
  have h := checkLog_sound (w := (286561 / 1713439)) (n := 12)
    (lo := (337658339 / 1000000000)) (hi := (16882917 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 713439) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 713439) = 1/(713439 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-16882917 / 50000000) (-337658339 / 1000000000) (Real.log (713439 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (94144773 / 500000000) ≤ -Real.log (1000000 / 1207183) ∧
    -Real.log (1000000 / 1207183) ≤ (188289547 / 1000000000) := by
  have h := checkLog_sound (w := (207183 / 2207183)) (n := 12)
    (lo := (94144773 / 500000000)) (hi := (188289547 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1207183 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1207183 / 1000000) = 1/(1000000 / 1207183) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (94144773 / 500000000) (188289547 / 1000000000) (Real.log (1207183 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1207183 / 1000000) = -Real.log (1000000 / 1207183) := by
    rw [show ((1207183 / 1000000) : ℝ) = ((1000000 / 1207183) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (232162853 / 1000000000) ≤ -Real.log (792817 / 1000000) ∧
    -Real.log (792817 / 1000000) ≤ (116081427 / 500000000) := by
  have h := checkLog_sound (w := (207183 / 1792817)) (n := 12)
    (lo := (232162853 / 1000000000)) (hi := (116081427 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 792817) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 792817) = 1/(792817 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-116081427 / 500000000) (-232162853 / 1000000000) (Real.log (792817 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (37684581 / 200000000) ≤ -Real.log (62500 / 75459) ∧
    -Real.log (62500 / 75459) ≤ (94211453 / 500000000) := by
  have h := checkLog_sound (w := (12959 / 137959)) (n := 12)
    (lo := (37684581 / 200000000)) (hi := (94211453 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((75459 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(75459 / 62500) = 1/(62500 / 75459) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (37684581 / 200000000) (94211453 / 500000000) (Real.log (75459 / 62500)) := by
  have h := reflection_log_15_neg
  have he : Real.log (75459 / 62500) = -Real.log (62500 / 75459) := by
    rw [show ((75459 / 62500) : ℝ) = ((62500 / 75459) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (232365947 / 1000000000) ≤ -Real.log (49541 / 62500) ∧
    -Real.log (49541 / 62500) ≤ (58091487 / 250000000) := by
  have h := checkLog_sound (w := (12959 / 112041)) (n := 12)
    (lo := (232365947 / 1000000000)) (hi := (58091487 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 49541) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 49541) = 1/(49541 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-58091487 / 250000000) (-232365947 / 1000000000) (Real.log (49541 / 62500)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (294583513 / 500000000) ≤ -Real.log (500000000000 / 901243182951) ∧
    -Real.log (500000000000 / 901243182951) ≤ (589167027 / 1000000000) := by
  have h := checkLog_sound (w := (401243182951 / 1401243182951)) (n := 12)
    (lo := (294583513 / 500000000)) (hi := (589167027 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((901243182951 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(901243182951 / 500000000000) = 1/(500000000000 / 901243182951) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (294583513 / 500000000) (589167027 / 1000000000) (Real.log (901243182951 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (901243182951 / 500000000000) = -Real.log (500000000000 / 901243182951) := by
    rw [show ((901243182951 / 500000000000) : ℝ) = ((500000000000 / 901243182951) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (294815553 / 500000000) ≤ -Real.log (250000000000 / 450830764789) ∧
    -Real.log (250000000000 / 450830764789) ≤ (589631107 / 1000000000) := by
  have h := checkLog_sound (w := (200830764789 / 700830764789)) (n := 12)
    (lo := (294815553 / 500000000)) (hi := (589631107 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((450830764789 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(450830764789 / 250000000000) = 1/(250000000000 / 450830764789) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (294815553 / 500000000) (589631107 / 1000000000) (Real.log (450830764789 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (450830764789 / 250000000000) = -Real.log (250000000000 / 450830764789) := by
    rw [show ((450830764789 / 250000000000) : ℝ) = ((250000000000 / 450830764789) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (420452399 / 1000000000) ≤ -Real.log (500000000000 / 761325122947) ∧
    -Real.log (500000000000 / 761325122947) ≤ (1051131 / 2500000) := by
  have h := checkLog_sound (w := (261325122947 / 1261325122947)) (n := 12)
    (lo := (420452399 / 1000000000)) (hi := (1051131 / 2500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((761325122947 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(761325122947 / 500000000000) = 1/(500000000000 / 761325122947) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (420452399 / 1000000000) (1051131 / 2500000) (Real.log (761325122947 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (761325122947 / 500000000000) = -Real.log (500000000000 / 761325122947) := by
    rw [show ((761325122947 / 500000000000) : ℝ) = ((500000000000 / 761325122947) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (105197213 / 250000000) ≤ -Real.log (250000000000 / 380790658243) ∧
    -Real.log (250000000000 / 380790658243) ≤ (420788853 / 1000000000) := by
  have h := checkLog_sound (w := (130790658243 / 630790658243)) (n := 12)
    (lo := (105197213 / 250000000)) (hi := (420788853 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((380790658243 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(380790658243 / 250000000000) = 1/(250000000000 / 380790658243) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (105197213 / 250000000) (420788853 / 1000000000) (Real.log (380790658243 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (380790658243 / 250000000000) = -Real.log (250000000000 / 380790658243) := by
    rw [show ((380790658243 / 250000000000) : ℝ) = ((250000000000 / 380790658243) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0472
