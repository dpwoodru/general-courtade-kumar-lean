import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0126
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

theorem reflection_log_1_neg : (311326117 / 1000000000) ≤ -Real.log (512 / 699) ∧
    -Real.log (512 / 699) ≤ (155663059 / 500000000) := by
  have h := checkLog_sound (w := (187 / 1211)) (n := 12)
    (lo := (311326117 / 1000000000)) (hi := (155663059 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((699 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(699 / 512) = 1/(512 / 699) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (311326117 / 1000000000) (155663059 / 500000000) (Real.log (699 / 512)) := by
  have h := reflection_log_1_neg
  have he : Real.log (699 / 512) = -Real.log (512 / 699) := by
    rw [show ((699 / 512) : ℝ) = ((512 / 699) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (227249721 / 500000000) ≤ -Real.log (325 / 512) ∧
    -Real.log (325 / 512) ≤ (454499443 / 1000000000) := by
  have h := checkLog_sound (w := (187 / 837)) (n := 12)
    (lo := (227249721 / 500000000)) (hi := (454499443 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 325) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 325) = 1/(325 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-454499443 / 1000000000) (-227249721 / 500000000) (Real.log (325 / 512)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (310467379 / 1000000000) ≤ -Real.log (640 / 873) ∧
    -Real.log (640 / 873) ≤ (15523369 / 50000000) := by
  have h := checkLog_sound (w := (233 / 1513)) (n := 12)
    (lo := (310467379 / 1000000000)) (hi := (15523369 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((873 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(873 / 640) = 1/(640 / 873) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (310467379 / 1000000000) (15523369 / 50000000) (Real.log (873 / 640)) := by
  have h := reflection_log_3_neg
  have he : Real.log (873 / 640) = -Real.log (640 / 873) := by
    rw [show ((873 / 640) : ℝ) = ((640 / 873) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (45265499 / 100000000) ≤ -Real.log (407 / 640) ∧
    -Real.log (407 / 640) ≤ (452654991 / 1000000000) := by
  have h := checkLog_sound (w := (233 / 1047)) (n := 12)
    (lo := (45265499 / 100000000)) (hi := (452654991 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 407) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 407) = 1/(407 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-452654991 / 1000000000) (-45265499 / 100000000) (Real.log (407 / 640)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (21935693 / 40000000) ≤ -Real.log (256 / 443) ∧
    -Real.log (256 / 443) ≤ (274196163 / 500000000) := by
  have h := checkLog_sound (w := (187 / 699)) (n := 12)
    (lo := (21935693 / 40000000)) (hi := (274196163 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((443 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(443 / 256) = 1/(256 / 443) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (21935693 / 40000000) (274196163 / 500000000) (Real.log (443 / 256)) := by
  have h := reflection_log_5_neg
  have he : Real.log (443 / 256) = -Real.log (256 / 443) := by
    rw [show ((443 / 256) : ℝ) = ((256 / 443) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1311070939 / 1000000000) ≤ -Real.log (69 / 256) ∧
    -Real.log (69 / 256) ≤ (1311070941 / 1000000000) := by
  have h := checkLog_sound (w := (59 / 197)) (n := 12)
    (lo := (617923759 / 1000000000)) (hi := (7724047 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((128 / 69) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(128 / 69) = 1/(69 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1311070941 / 1000000000) (-1311070939 / 1000000000) (Real.log (69 / 256)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (109407401 / 200000000) ≤ -Real.log (320 / 553) ∧
    -Real.log (320 / 553) ≤ (273518503 / 500000000) := by
  have h := checkLog_sound (w := (233 / 873)) (n := 12)
    (lo := (109407401 / 200000000)) (hi := (273518503 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((553 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(553 / 320) = 1/(320 / 553) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (109407401 / 200000000) (273518503 / 500000000) (Real.log (553 / 320)) := by
  have h := reflection_log_7_neg
  have he : Real.log (553 / 320) = -Real.log (320 / 553) := by
    rw [show ((553 / 320) : ℝ) = ((320 / 553) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (325603219 / 250000000) ≤ -Real.log (87 / 320) ∧
    -Real.log (87 / 320) ≤ (651206439 / 500000000) := by
  have h := checkLog_sound (w := (73 / 247)) (n := 12)
    (lo := (19039553 / 31250000)) (hi := (609265697 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 87) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(160 / 87) = 1/(87 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-651206439 / 500000000) (-325603219 / 250000000) (Real.log (87 / 320)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (212586153 / 500000000) ≤ -Real.log (500000 / 764927) ∧
    -Real.log (500000 / 764927) ≤ (425172307 / 1000000000) := by
  have h := checkLog_sound (w := (264927 / 1264927)) (n := 12)
    (lo := (212586153 / 500000000)) (hi := (425172307 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((764927 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(764927 / 500000) = 1/(500000 / 764927) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (212586153 / 500000000) (425172307 / 1000000000) (Real.log (764927 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (764927 / 500000) = -Real.log (500000 / 764927) := by
    rw [show ((764927 / 500000) : ℝ) = ((500000 / 764927) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (754711993 / 1000000000) ≤ -Real.log (235073 / 500000) ∧
    -Real.log (235073 / 500000) ≤ (150942399 / 200000000) := by
  have h := checkLog_sound (w := (14927 / 485073)) (n := 12)
    (lo := (61564813 / 1000000000)) (hi := (30782407 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 235073) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 235073) = 1/(235073 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-150942399 / 200000000) (-754711993 / 1000000000) (Real.log (235073 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (426373659 / 1000000000) ≤ -Real.log (1000000 / 1531693) ∧
    -Real.log (1000000 / 1531693) ≤ (21318683 / 50000000) := by
  have h := checkLog_sound (w := (531693 / 2531693)) (n := 12)
    (lo := (426373659 / 1000000000)) (hi := (21318683 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1531693 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1531693 / 1000000) = 1/(1000000 / 1531693) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (426373659 / 1000000000) (21318683 / 50000000) (Real.log (1531693 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1531693 / 1000000) = -Real.log (1000000 / 1531693) := by
    rw [show ((1531693 / 1000000) : ℝ) = ((1000000 / 1531693) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (379315607 / 500000000) ≤ -Real.log (468307 / 1000000) ∧
    -Real.log (468307 / 1000000) ≤ (47414451 / 62500000) := by
  have h := checkLog_sound (w := (31693 / 968307)) (n := 12)
    (lo := (32742017 / 500000000)) (hi := (13096807 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 468307) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 468307) = 1/(468307 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-47414451 / 62500000) (-379315607 / 500000000) (Real.log (468307 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (340803557 / 1000000000) ≤ -Real.log (1000000 / 1406077) ∧
    -Real.log (1000000 / 1406077) ≤ (170401779 / 500000000) := by
  have h := checkLog_sound (w := (406077 / 2406077)) (n := 12)
    (lo := (340803557 / 1000000000)) (hi := (170401779 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1406077 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1406077 / 1000000) = 1/(1000000 / 1406077) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (340803557 / 1000000000) (170401779 / 500000000) (Real.log (1406077 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1406077 / 1000000) = -Real.log (1000000 / 1406077) := by
    rw [show ((1406077 / 1000000) : ℝ) = ((1000000 / 1406077) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (521005597 / 1000000000) ≤ -Real.log (593923 / 1000000) ∧
    -Real.log (593923 / 1000000) ≤ (260502799 / 500000000) := by
  have h := checkLog_sound (w := (406077 / 1593923)) (n := 12)
    (lo := (521005597 / 1000000000)) (hi := (260502799 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 593923) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 593923) = 1/(593923 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-260502799 / 500000000) (-521005597 / 1000000000) (Real.log (593923 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (68394559 / 200000000) ≤ -Real.log (500000 / 703861) ∧
    -Real.log (500000 / 703861) ≤ (85493199 / 250000000) := by
  have h := checkLog_sound (w := (203861 / 1203861)) (n := 12)
    (lo := (68394559 / 200000000)) (hi := (85493199 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((703861 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(703861 / 500000) = 1/(500000 / 703861) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (68394559 / 200000000) (85493199 / 250000000) (Real.log (703861 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (703861 / 500000) = -Real.log (500000 / 703861) := by
    rw [show ((703861 / 500000) : ℝ) = ((500000 / 703861) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (523779159 / 1000000000) ≤ -Real.log (296139 / 500000) ∧
    -Real.log (296139 / 500000) ≤ (13094479 / 25000000) := by
  have h := checkLog_sound (w := (203861 / 796139)) (n := 12)
    (lo := (523779159 / 1000000000)) (hi := (13094479 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 296139) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 296139) = 1/(296139 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-13094479 / 25000000) (-523779159 / 1000000000) (Real.log (296139 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1179884299 / 1000000000) ≤ -Real.log (250000000000 / 813499423583) ∧
    -Real.log (250000000000 / 813499423583) ≤ (1179884301 / 1000000000) := by
  have h := checkLog_sound (w := (313499423583 / 1313499423583)) (n := 12)
    (lo := (486737119 / 1000000000)) (hi := (3042107 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((813499423583 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(813499423583 / 500000000000) = 1/(250000000000 / 813499423583) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1179884299 / 1000000000) (1179884301 / 1000000000) (Real.log (813499423583 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (813499423583 / 250000000000) = -Real.log (250000000000 / 813499423583) := by
    rw [show ((813499423583 / 250000000000) : ℝ) = ((250000000000 / 813499423583) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (592502437 / 500000000) ≤ -Real.log (500000000000 / 1635351382747) ∧
    -Real.log (500000000000 / 1635351382747) ≤ (296251219 / 250000000) := by
  have h := checkLog_sound (w := (635351382747 / 2635351382747)) (n := 12)
    (lo := (245928847 / 500000000)) (hi := (98371539 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1635351382747 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1635351382747 / 1000000000000) = 1/(500000000000 / 1635351382747) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (592502437 / 500000000) (296251219 / 250000000) (Real.log (1635351382747 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1635351382747 / 500000000000) = -Real.log (500000000000 / 1635351382747) := by
    rw [show ((1635351382747 / 500000000000) : ℝ) = ((500000000000 / 1635351382747) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (430904577 / 500000000) ≤ -Real.log (250000000000 / 591859971747) ∧
    -Real.log (250000000000 / 591859971747) ≤ (215452289 / 250000000) := by
  have h := checkLog_sound (w := (91859971747 / 1091859971747)) (n := 12)
    (lo := (84330987 / 500000000)) (hi := (6746479 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((591859971747 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(591859971747 / 500000000000) = 1/(250000000000 / 591859971747) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (430904577 / 500000000) (215452289 / 250000000) (Real.log (591859971747 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (591859971747 / 250000000000) = -Real.log (250000000000 / 591859971747) := by
    rw [show ((591859971747 / 250000000000) : ℝ) = ((250000000000 / 591859971747) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (432875977 / 500000000) ≤ -Real.log (500000000000 / 1188396327401) ∧
    -Real.log (500000000000 / 1188396327401) ≤ (216437989 / 250000000) := by
  have h := checkLog_sound (w := (188396327401 / 2188396327401)) (n := 12)
    (lo := (86302387 / 500000000)) (hi := (6904191 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1188396327401 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1188396327401 / 1000000000000) = 1/(500000000000 / 1188396327401) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (432875977 / 500000000) (216437989 / 250000000) (Real.log (1188396327401 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1188396327401 / 500000000000) = -Real.log (500000000000 / 1188396327401) := by
    rw [show ((1188396327401 / 500000000000) : ℝ) = ((500000000000 / 1188396327401) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0126
