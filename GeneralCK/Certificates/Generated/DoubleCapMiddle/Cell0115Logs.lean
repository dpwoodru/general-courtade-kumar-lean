import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0115
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

theorem reflection_log_1_neg : (320723879 / 1000000000) ≤ -Real.log (320 / 441) ∧
    -Real.log (320 / 441) ≤ (8018097 / 25000000) := by
  have h := checkLog_sound (w := (121 / 761)) (n := 12)
    (lo := (320723879 / 1000000000)) (hi := (8018097 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((441 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(441 / 320) = 1/(320 / 441) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (320723879 / 1000000000) (8018097 / 25000000) (Real.log (441 / 320)) := by
  have h := reflection_log_1_neg
  have he : Real.log (441 / 320) = -Real.log (320 / 441) := by
    rw [show ((441 / 320) : ℝ) = ((320 / 441) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (475016171 / 1000000000) ≤ -Real.log (199 / 320) ∧
    -Real.log (199 / 320) ≤ (118754043 / 250000000) := by
  have h := checkLog_sound (w := (121 / 519)) (n := 12)
    (lo := (475016171 / 1000000000)) (hi := (118754043 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 199) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(320 / 199) = 1/(199 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-118754043 / 250000000) (-475016171 / 1000000000) (Real.log (199 / 320)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (319873177 / 1000000000) ≤ -Real.log (512 / 705) ∧
    -Real.log (512 / 705) ≤ (159936589 / 500000000) := by
  have h := checkLog_sound (w := (193 / 1217)) (n := 12)
    (lo := (319873177 / 1000000000)) (hi := (159936589 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((705 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(705 / 512) = 1/(512 / 705) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (319873177 / 1000000000) (159936589 / 500000000) (Real.log (705 / 512)) := by
  have h := reflection_log_3_neg
  have he : Real.log (705 / 512) = -Real.log (512 / 705) := by
    rw [show ((705 / 512) : ℝ) = ((512 / 705) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (236566761 / 500000000) ≤ -Real.log (319 / 512) ∧
    -Real.log (319 / 512) ≤ (473133523 / 1000000000) := by
  have h := checkLog_sound (w := (193 / 831)) (n := 12)
    (lo := (236566761 / 500000000)) (hi := (473133523 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 319) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 319) = 1/(319 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-473133523 / 1000000000) (-236566761 / 500000000) (Real.log (319 / 512)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (281590427 / 500000000) ≤ -Real.log (160 / 281) ∧
    -Real.log (160 / 281) ≤ (112636171 / 200000000) := by
  have h := checkLog_sound (w := (121 / 441)) (n := 12)
    (lo := (281590427 / 500000000)) (hi := (112636171 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((281 / 160) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(281 / 160) = 1/(160 / 281) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (281590427 / 500000000) (112636171 / 200000000) (Real.log (281 / 160)) := by
  have h := reflection_log_5_neg
  have he : Real.log (281 / 160) = -Real.log (160 / 281) := by
    rw [show ((281 / 160) : ℝ) = ((160 / 281) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1411612167 / 1000000000) ≤ -Real.log (39 / 160) ∧
    -Real.log (39 / 160) ≤ (141161217 / 100000000) := by
  have h := checkLog_sound (w := (1 / 79)) (n := 12)
    (lo := (25317807 / 1000000000)) (hi := (1582363 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40 / 39) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(40 / 39) = 1/(39 / 160) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-141161217 / 100000000) (-1411612167 / 1000000000) (Real.log (39 / 160)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (561845443 / 1000000000) ≤ -Real.log (256 / 449) ∧
    -Real.log (256 / 449) ≤ (140461361 / 250000000) := by
  have h := checkLog_sound (w := (193 / 705)) (n := 12)
    (lo := (561845443 / 1000000000)) (hi := (140461361 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((449 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(449 / 256) = 1/(256 / 449) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (561845443 / 1000000000) (140461361 / 250000000) (Real.log (449 / 256)) := by
  have h := reflection_log_7_neg
  have he : Real.log (449 / 256) = -Real.log (256 / 449) := by
    rw [show ((449 / 256) : ℝ) = ((256 / 449) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (350510679 / 250000000) ≤ -Real.log (63 / 256) ∧
    -Real.log (63 / 256) ≤ (1402042719 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 127)) (n := 12)
    (lo := (3937089 / 250000000)) (hi := (15748357 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((64 / 63) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(64 / 63) = 1/(63 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1402042719 / 1000000000) (-350510679 / 250000000) (Real.log (63 / 256)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (438373633 / 1000000000) ≤ -Real.log (125000 / 193773) ∧
    -Real.log (125000 / 193773) ≤ (219186817 / 500000000) := by
  have h := checkLog_sound (w := (68773 / 318773)) (n := 12)
    (lo := (438373633 / 1000000000)) (hi := (219186817 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((193773 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(193773 / 125000) = 1/(125000 / 193773) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (438373633 / 1000000000) (219186817 / 500000000) (Real.log (193773 / 125000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (193773 / 125000) = -Real.log (125000 / 193773) := by
    rw [show ((193773 / 125000) : ℝ) = ((125000 / 193773) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (199729167 / 250000000) ≤ -Real.log (56227 / 125000) ∧
    -Real.log (56227 / 125000) ≤ (79891667 / 100000000) := by
  have h := checkLog_sound (w := (6273 / 118727)) (n := 12)
    (lo := (6610593 / 62500000)) (hi := (105769489 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 56227) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(62500 / 56227) = 1/(56227 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-79891667 / 100000000) (-199729167 / 250000000) (Real.log (56227 / 125000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (21978703 / 50000000) ≤ -Real.log (500000 / 776023) ∧
    -Real.log (500000 / 776023) ≤ (439574061 / 1000000000) := by
  have h := checkLog_sound (w := (276023 / 1276023)) (n := 12)
    (lo := (21978703 / 50000000)) (hi := (439574061 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((776023 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(776023 / 500000) = 1/(500000 / 776023) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (21978703 / 50000000) (439574061 / 1000000000) (Real.log (776023 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (776023 / 500000) = -Real.log (500000 / 776023) := by
    rw [show ((776023 / 500000) : ℝ) = ((500000 / 776023) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (803064729 / 1000000000) ≤ -Real.log (223977 / 500000) ∧
    -Real.log (223977 / 500000) ≤ (803064731 / 1000000000) := by
  have h := checkLog_sound (w := (26023 / 473977)) (n := 12)
    (lo := (109917549 / 1000000000)) (hi := (2198351 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 223977) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 223977) = 1/(223977 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-803064731 / 1000000000) (-803064729 / 1000000000) (Real.log (223977 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (353759799 / 1000000000) ≤ -Real.log (1000000 / 1424413) ∧
    -Real.log (1000000 / 1424413) ≤ (1768799 / 5000000) := by
  have h := checkLog_sound (w := (424413 / 2424413)) (n := 12)
    (lo := (353759799 / 1000000000)) (hi := (1768799 / 5000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1424413 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1424413 / 1000000) = 1/(1000000 / 1424413) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (353759799 / 1000000000) (1768799 / 5000000) (Real.log (1424413 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1424413 / 1000000) = -Real.log (1000000 / 1424413) := by
    rw [show ((1424413 / 1000000) : ℝ) = ((1000000 / 1424413) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (552364889 / 1000000000) ≤ -Real.log (575587 / 1000000) ∧
    -Real.log (575587 / 1000000) ≤ (55236489 / 100000000) := by
  have h := checkLog_sound (w := (424413 / 1575587)) (n := 12)
    (lo := (552364889 / 1000000000)) (hi := (55236489 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 575587) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 575587) = 1/(575587 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-55236489 / 100000000) (-552364889 / 1000000000) (Real.log (575587 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (354950457 / 1000000000) ≤ -Real.log (100000 / 142611) ∧
    -Real.log (100000 / 142611) ≤ (177475229 / 500000000) := by
  have h := checkLog_sound (w := (42611 / 242611)) (n := 12)
    (lo := (354950457 / 1000000000)) (hi := (177475229 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((142611 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(142611 / 100000) = 1/(100000 / 142611) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (354950457 / 1000000000) (177475229 / 500000000) (Real.log (142611 / 100000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (142611 / 100000) = -Real.log (100000 / 142611) := by
    rw [show ((142611 / 100000) : ℝ) = ((100000 / 142611) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (277658769 / 500000000) ≤ -Real.log (57389 / 100000) ∧
    -Real.log (57389 / 100000) ≤ (555317539 / 1000000000) := by
  have h := checkLog_sound (w := (42611 / 157389)) (n := 12)
    (lo := (277658769 / 500000000)) (hi := (555317539 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 57389) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 57389) = 1/(57389 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-555317539 / 1000000000) (-277658769 / 500000000) (Real.log (57389 / 100000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1237290301 / 1000000000) ≤ -Real.log (500000000000 / 1723131235883) ∧
    -Real.log (500000000000 / 1723131235883) ≤ (1237290303 / 1000000000) := by
  have h := checkLog_sound (w := (723131235883 / 2723131235883)) (n := 12)
    (lo := (544143121 / 1000000000)) (hi := (272071561 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1723131235883 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1723131235883 / 1000000000000) = 1/(500000000000 / 1723131235883) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1237290301 / 1000000000) (1237290303 / 1000000000) (Real.log (1723131235883 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1723131235883 / 500000000000) = -Real.log (500000000000 / 1723131235883) := by
    rw [show ((1723131235883 / 500000000000) : ℝ) = ((500000000000 / 1723131235883) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (124263879 / 100000000) ≤ -Real.log (500000000000 / 1732372073919) ∧
    -Real.log (500000000000 / 1732372073919) ≤ (155329849 / 125000000) := by
  have h := checkLog_sound (w := (732372073919 / 2732372073919)) (n := 12)
    (lo := (54949161 / 100000000)) (hi := (549491611 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1732372073919 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1732372073919 / 1000000000000) = 1/(500000000000 / 1732372073919) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (124263879 / 100000000) (155329849 / 125000000) (Real.log (1732372073919 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1732372073919 / 500000000000) = -Real.log (500000000000 / 1732372073919) := by
    rw [show ((1732372073919 / 500000000000) : ℝ) = ((500000000000 / 1732372073919) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (906124687 / 1000000000) ≤ -Real.log (500000000000 / 1237356820081) ∧
    -Real.log (500000000000 / 1237356820081) ≤ (906124689 / 1000000000) := by
  have h := checkLog_sound (w := (237356820081 / 2237356820081)) (n := 12)
    (lo := (212977507 / 1000000000)) (hi := (53244377 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1237356820081 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1237356820081 / 1000000000000) = 1/(500000000000 / 1237356820081) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (906124687 / 1000000000) (906124689 / 1000000000) (Real.log (1237356820081 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (1237356820081 / 500000000000) = -Real.log (500000000000 / 1237356820081) := by
    rw [show ((1237356820081 / 500000000000) : ℝ) = ((500000000000 / 1237356820081) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (182053599 / 200000000) ≤ -Real.log (500000000000 / 1242494206207) ∧
    -Real.log (500000000000 / 1242494206207) ≤ (910267997 / 1000000000) := by
  have h := checkLog_sound (w := (242494206207 / 2242494206207)) (n := 12)
    (lo := (43424163 / 200000000)) (hi := (13570051 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1242494206207 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1242494206207 / 1000000000000) = 1/(500000000000 / 1242494206207) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (182053599 / 200000000) (910267997 / 1000000000) (Real.log (1242494206207 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1242494206207 / 500000000000) = -Real.log (500000000000 / 1242494206207) := by
    rw [show ((1242494206207 / 500000000000) : ℝ) = ((500000000000 / 1242494206207) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0115
