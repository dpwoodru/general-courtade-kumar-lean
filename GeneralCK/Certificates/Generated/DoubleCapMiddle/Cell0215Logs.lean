import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0215
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

theorem reflection_log_1_neg : (258902751 / 1000000000) ≤ -Real.log (5120 / 6633) ∧
    -Real.log (5120 / 6633) ≤ (8090711 / 31250000) := by
  have h := checkLog_sound (w := (1513 / 11753)) (n := 12)
    (lo := (258902751 / 1000000000)) (hi := (8090711 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6633 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6633 / 5120) = 1/(5120 / 6633) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (258902751 / 1000000000) (8090711 / 31250000) (Real.log (6633 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6633 / 5120) = -Real.log (5120 / 6633) := by
    rw [show ((6633 / 5120) : ℝ) = ((5120 / 6633) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (350278037 / 1000000000) ≤ -Real.log (3607 / 5120) ∧
    -Real.log (3607 / 5120) ≤ (175139019 / 500000000) := by
  have h := checkLog_sound (w := (1513 / 8727)) (n := 12)
    (lo := (350278037 / 1000000000)) (hi := (175139019 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3607) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3607) = 1/(3607 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-175139019 / 500000000) (-350278037 / 1000000000) (Real.log (3607 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (51690073 / 200000000) ≤ -Real.log (512 / 663) ∧
    -Real.log (512 / 663) ≤ (129225183 / 500000000) := by
  have h := checkLog_sound (w := (151 / 1175)) (n := 12)
    (lo := (51690073 / 200000000)) (hi := (129225183 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((663 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(663 / 512) = 1/(512 / 663) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (51690073 / 200000000) (129225183 / 500000000) (Real.log (663 / 512)) := by
  have h := reflection_log_3_neg
  have he : Real.log (663 / 512) = -Real.log (512 / 663) := by
    rw [show ((663 / 512) : ℝ) = ((512 / 663) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (174723333 / 500000000) ≤ -Real.log (361 / 512) ∧
    -Real.log (361 / 512) ≤ (349446667 / 1000000000) := by
  have h := checkLog_sound (w := (151 / 873)) (n := 12)
    (lo := (174723333 / 500000000)) (hi := (349446667 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 361) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 361) = 1/(361 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-349446667 / 1000000000) (-174723333 / 500000000) (Real.log (361 / 512)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (46437257 / 100000000) ≤ -Real.log (2560 / 4073) ∧
    -Real.log (2560 / 4073) ≤ (464372571 / 1000000000) := by
  have h := checkLog_sound (w := (1513 / 6633)) (n := 12)
    (lo := (46437257 / 100000000)) (hi := (464372571 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4073 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4073 / 2560) = 1/(2560 / 4073) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (46437257 / 100000000) (464372571 / 1000000000) (Real.log (4073 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (4073 / 2560) = -Real.log (2560 / 4073) := by
    rw [show ((4073 / 2560) : ℝ) = ((2560 / 4073) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (447039163 / 500000000) ≤ -Real.log (1047 / 2560) ∧
    -Real.log (1047 / 2560) ≤ (111759791 / 125000000) := by
  have h := checkLog_sound (w := (233 / 2327)) (n := 12)
    (lo := (100465573 / 500000000)) (hi := (200931147 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 1047) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 1047) = 1/(1047 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-111759791 / 125000000) (-447039163 / 500000000) (Real.log (1047 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (23181787 / 50000000) ≤ -Real.log (256 / 407) ∧
    -Real.log (256 / 407) ≤ (463635741 / 1000000000) := by
  have h := checkLog_sound (w := (151 / 663)) (n := 12)
    (lo := (23181787 / 50000000)) (hi := (463635741 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((407 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(407 / 256) = 1/(256 / 407) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (23181787 / 50000000) (463635741 / 1000000000) (Real.log (407 / 256)) := by
  have h := reflection_log_7_neg
  have he : Real.log (407 / 256) = -Real.log (256 / 407) := by
    rw [show ((407 / 256) : ℝ) = ((256 / 407) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (891217093 / 1000000000) ≤ -Real.log (105 / 256) ∧
    -Real.log (105 / 256) ≤ (178243419 / 200000000) := by
  have h := checkLog_sound (w := (23 / 233)) (n := 12)
    (lo := (198069913 / 1000000000)) (hi := (99034957 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((128 / 105) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(128 / 105) = 1/(105 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-178243419 / 200000000) (-891217093 / 1000000000) (Real.log (105 / 256)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (17680969 / 50000000) ≤ -Real.log (1000000 / 1424213) ∧
    -Real.log (1000000 / 1424213) ≤ (353619381 / 1000000000) := by
  have h := checkLog_sound (w := (424213 / 2424213)) (n := 12)
    (lo := (17680969 / 50000000)) (hi := (353619381 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1424213 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1424213 / 1000000) = 1/(1000000 / 1424213) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (17680969 / 50000000) (353619381 / 1000000000) (Real.log (1424213 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1424213 / 1000000) = -Real.log (1000000 / 1424213) := by
    rw [show ((1424213 / 1000000) : ℝ) = ((1000000 / 1424213) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (276008739 / 500000000) ≤ -Real.log (575787 / 1000000) ∧
    -Real.log (575787 / 1000000) ≤ (552017479 / 1000000000) := by
  have h := checkLog_sound (w := (424213 / 1575787)) (n := 12)
    (lo := (276008739 / 500000000)) (hi := (552017479 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 575787) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 575787) = 1/(575787 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-552017479 / 1000000000) (-276008739 / 500000000) (Real.log (575787 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (354234969 / 1000000000) ≤ -Real.log (100000 / 142509) ∧
    -Real.log (100000 / 142509) ≤ (35423497 / 100000000) := by
  have h := checkLog_sound (w := (42509 / 242509)) (n := 12)
    (lo := (354234969 / 1000000000)) (hi := (35423497 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((142509 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(142509 / 100000) = 1/(100000 / 142509) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (354234969 / 1000000000) (35423497 / 100000000) (Real.log (142509 / 100000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (142509 / 100000) = -Real.log (100000 / 142509) := by
    rw [show ((142509 / 100000) : ℝ) = ((100000 / 142509) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (138385443 / 250000000) ≤ -Real.log (57491 / 100000) ∧
    -Real.log (57491 / 100000) ≤ (553541773 / 1000000000) := by
  have h := checkLog_sound (w := (42509 / 157491)) (n := 12)
    (lo := (138385443 / 250000000)) (hi := (553541773 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 57491) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 57491) = 1/(57491 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-553541773 / 1000000000) (-138385443 / 250000000) (Real.log (57491 / 100000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (6858461 / 25000000) ≤ -Real.log (50000 / 65783) ∧
    -Real.log (50000 / 65783) ≤ (274338441 / 1000000000) := by
  have h := checkLog_sound (w := (15783 / 115783)) (n := 12)
    (lo := (6858461 / 25000000)) (hi := (274338441 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((65783 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(65783 / 50000) = 1/(50000 / 65783) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (6858461 / 25000000) (274338441 / 1000000000) (Real.log (65783 / 50000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (65783 / 50000) = -Real.log (50000 / 65783) := by
    rw [show ((65783 / 50000) : ℝ) = ((50000 / 65783) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (47412551 / 125000000) ≤ -Real.log (34217 / 50000) ∧
    -Real.log (34217 / 50000) ≤ (379300409 / 1000000000) := by
  have h := checkLog_sound (w := (15783 / 84217)) (n := 12)
    (lo := (47412551 / 125000000)) (hi := (379300409 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 34217) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 34217) = 1/(34217 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-379300409 / 1000000000) (-47412551 / 125000000) (Real.log (34217 / 50000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (34360883 / 125000000) ≤ -Real.log (500000 / 658191) ∧
    -Real.log (500000 / 658191) ≤ (54977413 / 200000000) := by
  have h := checkLog_sound (w := (158191 / 1158191)) (n := 12)
    (lo := (34360883 / 125000000)) (hi := (54977413 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((658191 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(658191 / 500000) = 1/(500000 / 658191) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (34360883 / 125000000) (54977413 / 200000000) (Real.log (658191 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (658191 / 500000) = -Real.log (500000 / 658191) := by
    rw [show ((658191 / 500000) : ℝ) = ((500000 / 658191) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (95088999 / 250000000) ≤ -Real.log (341809 / 500000) ∧
    -Real.log (341809 / 500000) ≤ (380355997 / 1000000000) := by
  have h := checkLog_sound (w := (158191 / 841809)) (n := 12)
    (lo := (95088999 / 250000000)) (hi := (380355997 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 341809) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 341809) = 1/(341809 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-380355997 / 1000000000) (-95088999 / 250000000) (Real.log (341809 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (452818429 / 500000000) ≤ -Real.log (250000000000 / 618376674013) ∧
    -Real.log (250000000000 / 618376674013) ≤ (45281843 / 50000000) := by
  have h := checkLog_sound (w := (118376674013 / 1118376674013)) (n := 12)
    (lo := (106244839 / 500000000)) (hi := (212489679 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((618376674013 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(618376674013 / 500000000000) = 1/(250000000000 / 618376674013) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (452818429 / 500000000) (45281843 / 50000000) (Real.log (618376674013 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (618376674013 / 250000000000) = -Real.log (250000000000 / 618376674013) := by
    rw [show ((618376674013 / 250000000000) : ℝ) = ((250000000000 / 618376674013) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (907776741 / 1000000000) ≤ -Real.log (500000000000 / 1239402689117) ∧
    -Real.log (500000000000 / 1239402689117) ≤ (907776743 / 1000000000) := by
  have h := checkLog_sound (w := (239402689117 / 2239402689117)) (n := 12)
    (lo := (214629561 / 1000000000)) (hi := (107314781 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1239402689117 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1239402689117 / 1000000000000) = 1/(500000000000 / 1239402689117) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (907776741 / 1000000000) (907776743 / 1000000000) (Real.log (1239402689117 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1239402689117 / 500000000000) = -Real.log (500000000000 / 1239402689117) := by
    rw [show ((1239402689117 / 500000000000) : ℝ) = ((500000000000 / 1239402689117) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (653638849 / 1000000000) ≤ -Real.log (62500000000 / 120157743227) ∧
    -Real.log (62500000000 / 120157743227) ≤ (13072777 / 20000000) := by
  have h := checkLog_sound (w := (57657743227 / 182657743227)) (n := 12)
    (lo := (653638849 / 1000000000)) (hi := (13072777 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((120157743227 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(120157743227 / 62500000000) = 1/(62500000000 / 120157743227) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (653638849 / 1000000000) (13072777 / 20000000) (Real.log (120157743227 / 62500000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (120157743227 / 62500000000) = -Real.log (62500000000 / 120157743227) := by
    rw [show ((120157743227 / 62500000000) : ℝ) = ((62500000000 / 120157743227) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (655243061 / 1000000000) ≤ -Real.log (250000000000 / 481402625443) ∧
    -Real.log (250000000000 / 481402625443) ≤ (327621531 / 500000000) := by
  have h := checkLog_sound (w := (231402625443 / 731402625443)) (n := 12)
    (lo := (655243061 / 1000000000)) (hi := (327621531 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((481402625443 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(481402625443 / 250000000000) = 1/(250000000000 / 481402625443) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (655243061 / 1000000000) (327621531 / 500000000) (Real.log (481402625443 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (481402625443 / 250000000000) = -Real.log (250000000000 / 481402625443) := by
    rw [show ((481402625443 / 250000000000) : ℝ) = ((250000000000 / 481402625443) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0215
