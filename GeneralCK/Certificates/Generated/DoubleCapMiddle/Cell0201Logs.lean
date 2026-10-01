import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0201
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

theorem reflection_log_1_neg : (53042953 / 200000000) ≤ -Real.log (1024 / 1335) ∧
    -Real.log (1024 / 1335) ≤ (132607383 / 500000000) := by
  have h := checkLog_sound (w := (311 / 2359)) (n := 12)
    (lo := (53042953 / 200000000)) (hi := (132607383 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1335 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1335 / 1024) = 1/(1024 / 1335) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (53042953 / 200000000) (132607383 / 500000000) (Real.log (1335 / 1024)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1335 / 1024) = -Real.log (1024 / 1335) := by
    rw [show ((1335 / 1024) : ℝ) = ((1024 / 1335) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (72398077 / 200000000) ≤ -Real.log (713 / 1024) ∧
    -Real.log (713 / 1024) ≤ (180995193 / 500000000) := by
  have h := checkLog_sound (w := (311 / 1737)) (n := 12)
    (lo := (72398077 / 200000000)) (hi := (180995193 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 713) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 713) = 1/(713 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-180995193 / 500000000) (-72398077 / 200000000) (Real.log (713 / 1024)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (132382613 / 500000000) ≤ -Real.log (320 / 417) ∧
    -Real.log (320 / 417) ≤ (264765227 / 1000000000) := by
  have h := checkLog_sound (w := (97 / 737)) (n := 12)
    (lo := (132382613 / 500000000)) (hi := (264765227 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((417 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(417 / 320) = 1/(320 / 417) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (132382613 / 500000000) (264765227 / 1000000000) (Real.log (417 / 320)) := by
  have h := reflection_log_3_neg
  have he : Real.log (417 / 320) = -Real.log (320 / 417) := by
    rw [show ((417 / 320) : ℝ) = ((320 / 417) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (45143653 / 125000000) ≤ -Real.log (223 / 320) ∧
    -Real.log (223 / 320) ≤ (14445969 / 40000000) := by
  have h := checkLog_sound (w := (97 / 543)) (n := 12)
    (lo := (45143653 / 125000000)) (hi := (14445969 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 223) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(320 / 223) = 1/(223 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-14445969 / 40000000) (-45143653 / 125000000) (Real.log (223 / 320)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (18985263 / 40000000) ≤ -Real.log (512 / 823) ∧
    -Real.log (512 / 823) ≤ (59328947 / 125000000) := by
  have h := checkLog_sound (w := (311 / 1335)) (n := 12)
    (lo := (18985263 / 40000000)) (hi := (59328947 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((823 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(823 / 512) = 1/(512 / 823) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (18985263 / 40000000) (59328947 / 125000000) (Real.log (823 / 512)) := by
  have h := reflection_log_5_neg
  have he : Real.log (823 / 512) = -Real.log (512 / 823) := by
    rw [show ((823 / 512) : ℝ) = ((512 / 823) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (233754929 / 250000000) ≤ -Real.log (201 / 512) ∧
    -Real.log (201 / 512) ≤ (467509859 / 500000000) := by
  have h := checkLog_sound (w := (55 / 457)) (n := 12)
    (lo := (30234067 / 125000000)) (hi := (241872537 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((256 / 201) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(256 / 201) = 1/(201 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-467509859 / 500000000) (-233754929 / 250000000) (Real.log (201 / 512)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (473902269 / 1000000000) ≤ -Real.log (160 / 257) ∧
    -Real.log (160 / 257) ≤ (47390227 / 100000000) := by
  have h := checkLog_sound (w := (97 / 417)) (n := 12)
    (lo := (473902269 / 1000000000)) (hi := (47390227 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((257 / 160) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(257 / 160) = 1/(160 / 257) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (473902269 / 1000000000) (47390227 / 100000000) (Real.log (257 / 160)) := by
  have h := reflection_log_7_neg
  have he : Real.log (257 / 160) = -Real.log (160 / 257) := by
    rw [show ((257 / 160) : ℝ) = ((160 / 257) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (58252443 / 62500000) ≤ -Real.log (63 / 160) ∧
    -Real.log (63 / 160) ≤ (93203909 / 100000000) := by
  have h := checkLog_sound (w := (17 / 143)) (n := 12)
    (lo := (59722977 / 250000000)) (hi := (238891909 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80 / 63) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(80 / 63) = 1/(63 / 160) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-93203909 / 100000000) (-58252443 / 62500000) (Real.log (63 / 160)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (4527707 / 12500000) ≤ -Real.log (100000 / 143651) ∧
    -Real.log (100000 / 143651) ≤ (362216561 / 1000000000) := by
  have h := checkLog_sound (w := (43651 / 243651)) (n := 12)
    (lo := (4527707 / 12500000)) (hi := (362216561 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((143651 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(143651 / 100000) = 1/(100000 / 143651) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (4527707 / 12500000) (362216561 / 1000000000) (Real.log (143651 / 100000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (143651 / 100000) = -Real.log (100000 / 143651) := by
    rw [show ((143651 / 100000) : ℝ) = ((100000 / 143651) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (573605691 / 1000000000) ≤ -Real.log (56349 / 100000) ∧
    -Real.log (56349 / 100000) ≤ (143401423 / 250000000) := by
  have h := checkLog_sound (w := (43651 / 156349)) (n := 12)
    (lo := (573605691 / 1000000000)) (hi := (143401423 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 56349) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 56349) = 1/(56349 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-143401423 / 250000000) (-573605691 / 1000000000) (Real.log (56349 / 100000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (9070759 / 25000000) ≤ -Real.log (62500 / 89837) ∧
    -Real.log (62500 / 89837) ≤ (362830361 / 1000000000) := by
  have h := checkLog_sound (w := (27337 / 152337)) (n := 12)
    (lo := (9070759 / 25000000)) (hi := (362830361 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((89837 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(89837 / 62500) = 1/(62500 / 89837) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (9070759 / 25000000) (362830361 / 1000000000) (Real.log (89837 / 62500)) := by
  have h := reflection_log_11_neg
  have he : Real.log (89837 / 62500) = -Real.log (62500 / 89837) := by
    rw [show ((89837 / 62500) : ℝ) = ((62500 / 89837) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (575172163 / 1000000000) ≤ -Real.log (35163 / 62500) ∧
    -Real.log (35163 / 62500) ≤ (143793041 / 250000000) := by
  have h := checkLog_sound (w := (27337 / 97663)) (n := 12)
    (lo := (575172163 / 1000000000)) (hi := (143793041 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 35163) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 35163) = 1/(35163 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-143793041 / 250000000) (-575172163 / 1000000000) (Real.log (35163 / 62500)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (282022839 / 1000000000) ≤ -Real.log (1000000 / 1325809) ∧
    -Real.log (1000000 / 1325809) ≤ (7050571 / 25000000) := by
  have h := checkLog_sound (w := (325809 / 2325809)) (n := 12)
    (lo := (282022839 / 1000000000)) (hi := (7050571 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1325809 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1325809 / 1000000) = 1/(1000000 / 1325809) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (282022839 / 1000000000) (7050571 / 25000000) (Real.log (1325809 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1325809 / 1000000) = -Real.log (1000000 / 1325809) := by
    rw [show ((1325809 / 1000000) : ℝ) = ((1000000 / 1325809) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (15769673 / 40000000) ≤ -Real.log (674191 / 1000000) ∧
    -Real.log (674191 / 1000000) ≤ (197120913 / 500000000) := by
  have h := checkLog_sound (w := (325809 / 1674191)) (n := 12)
    (lo := (15769673 / 40000000)) (hi := (197120913 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 674191) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 674191) = 1/(674191 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-197120913 / 500000000) (-15769673 / 40000000) (Real.log (674191 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (8830439 / 31250000) ≤ -Real.log (50000 / 66327) ∧
    -Real.log (50000 / 66327) ≤ (282574049 / 1000000000) := by
  have h := checkLog_sound (w := (16327 / 116327)) (n := 12)
    (lo := (8830439 / 31250000)) (hi := (282574049 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((66327 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(66327 / 50000) = 1/(50000 / 66327) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (8830439 / 31250000) (282574049 / 1000000000) (Real.log (66327 / 50000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (66327 / 50000) = -Real.log (50000 / 66327) := by
    rw [show ((66327 / 50000) : ℝ) = ((50000 / 66327) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (98831669 / 250000000) ≤ -Real.log (33673 / 50000) ∧
    -Real.log (33673 / 50000) ≤ (395326677 / 1000000000) := by
  have h := checkLog_sound (w := (16327 / 83673)) (n := 12)
    (lo := (98831669 / 250000000)) (hi := (395326677 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 33673) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 33673) = 1/(33673 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-395326677 / 1000000000) (-98831669 / 250000000) (Real.log (33673 / 50000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (233955563 / 250000000) ≤ -Real.log (250000000000 / 637327193029) ∧
    -Real.log (250000000000 / 637327193029) ≤ (467911127 / 500000000) := by
  have h := checkLog_sound (w := (137327193029 / 1137327193029)) (n := 12)
    (lo := (1895899 / 7812500)) (hi := (242675073 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((637327193029 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(637327193029 / 500000000000) = 1/(250000000000 / 637327193029) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (233955563 / 250000000) (467911127 / 500000000) (Real.log (637327193029 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (637327193029 / 250000000000) = -Real.log (250000000000 / 637327193029) := by
    rw [show ((637327193029 / 250000000000) : ℝ) = ((250000000000 / 637327193029) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (938002523 / 1000000000) ≤ -Real.log (31250000000 / 79839781873) ∧
    -Real.log (31250000000 / 79839781873) ≤ (37520101 / 40000000) := by
  have h := checkLog_sound (w := (17339781873 / 142339781873)) (n := 12)
    (lo := (244855343 / 1000000000)) (hi := (15303459 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((79839781873 / 62500000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(79839781873 / 62500000000) = 1/(31250000000 / 79839781873) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (938002523 / 1000000000) (37520101 / 40000000) (Real.log (79839781873 / 31250000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (79839781873 / 31250000000) = -Real.log (31250000000 / 79839781873) := by
    rw [show ((79839781873 / 31250000000) : ℝ) = ((31250000000 / 79839781873) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (84533083 / 125000000) ≤ -Real.log (250000000000 / 491629597547) ∧
    -Real.log (250000000000 / 491629597547) ≤ (135252933 / 200000000) := by
  have h := checkLog_sound (w := (241629597547 / 741629597547)) (n := 12)
    (lo := (84533083 / 125000000)) (hi := (135252933 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((491629597547 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(491629597547 / 250000000000) = 1/(250000000000 / 491629597547) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (84533083 / 125000000) (135252933 / 200000000) (Real.log (491629597547 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (491629597547 / 250000000000) = -Real.log (250000000000 / 491629597547) := by
    rw [show ((491629597547 / 250000000000) : ℝ) = ((250000000000 / 491629597547) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (169475181 / 250000000) ≤ -Real.log (20000000000 / 39394767321) ∧
    -Real.log (20000000000 / 39394767321) ≤ (27116029 / 40000000) := by
  have h := checkLog_sound (w := (19394767321 / 59394767321)) (n := 12)
    (lo := (169475181 / 250000000)) (hi := (27116029 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((39394767321 / 20000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(39394767321 / 20000000000) = 1/(20000000000 / 39394767321) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (169475181 / 250000000) (27116029 / 40000000) (Real.log (39394767321 / 20000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (39394767321 / 20000000000) = -Real.log (20000000000 / 39394767321) := by
    rw [show ((39394767321 / 20000000000) : ℝ) = ((20000000000 / 39394767321) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0201
