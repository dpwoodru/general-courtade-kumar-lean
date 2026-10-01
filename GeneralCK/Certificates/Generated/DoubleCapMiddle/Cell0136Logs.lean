import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0136
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

theorem reflection_log_1_neg : (151352687 / 500000000) ≤ -Real.log (512 / 693) ∧
    -Real.log (512 / 693) ≤ (2421643 / 8000000) := by
  have h := checkLog_sound (w := (181 / 1205)) (n := 12)
    (lo := (151352687 / 500000000)) (hi := (2421643 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((693 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(693 / 512) = 1/(512 / 693) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (151352687 / 500000000) (2421643 / 8000000) (Real.log (693 / 512)) := by
  have h := reflection_log_1_neg
  have he : Real.log (693 / 512) = -Real.log (512 / 693) := by
    rw [show ((693 / 512) : ℝ) = ((512 / 693) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (436206249 / 1000000000) ≤ -Real.log (331 / 512) ∧
    -Real.log (331 / 512) ≤ (69793 / 160000) := by
  have h := checkLog_sound (w := (181 / 843)) (n := 12)
    (lo := (436206249 / 1000000000)) (hi := (69793 / 160000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 331) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 331) = 1/(331 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-69793 / 160000) (-436206249 / 1000000000) (Real.log (331 / 512)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (150919599 / 500000000) ≤ -Real.log (1280 / 1731) ∧
    -Real.log (1280 / 1731) ≤ (301839199 / 1000000000) := by
  have h := checkLog_sound (w := (451 / 3011)) (n := 12)
    (lo := (150919599 / 500000000)) (hi := (301839199 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1731 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1731 / 1280) = 1/(1280 / 1731) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (150919599 / 500000000) (301839199 / 1000000000) (Real.log (1731 / 1280)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1731 / 1280) = -Real.log (1280 / 1731) := by
    rw [show ((1731 / 1280) : ℝ) = ((1280 / 1731) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (434395201 / 1000000000) ≤ -Real.log (829 / 1280) ∧
    -Real.log (829 / 1280) ≤ (217197601 / 500000000) := by
  have h := checkLog_sound (w := (451 / 2109)) (n := 12)
    (lo := (434395201 / 1000000000)) (hi := (217197601 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 829) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 829) = 1/(829 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-217197601 / 500000000) (-434395201 / 1000000000) (Real.log (829 / 1280)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (2139023 / 4000000) ≤ -Real.log (256 / 437) ∧
    -Real.log (256 / 437) ≤ (534755751 / 1000000000) := by
  have h := checkLog_sound (w := (181 / 693)) (n := 12)
    (lo := (2139023 / 4000000)) (hi := (534755751 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((437 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(437 / 256) = 1/(256 / 437) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (2139023 / 4000000) (534755751 / 1000000000) (Real.log (437 / 256)) := by
  have h := reflection_log_5_neg
  have he : Real.log (437 / 256) = -Real.log (256 / 437) := by
    rw [show ((437 / 256) : ℝ) = ((256 / 437) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (122768933 / 100000000) ≤ -Real.log (75 / 256) ∧
    -Real.log (75 / 256) ≤ (306922333 / 250000000) := by
  have h := checkLog_sound (w := (53 / 203)) (n := 12)
    (lo := (10690843 / 20000000)) (hi := (534542151 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((128 / 75) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(128 / 75) = 1/(75 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-306922333 / 250000000) (-122768933 / 100000000) (Real.log (75 / 256)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (533381809 / 1000000000) ≤ -Real.log (640 / 1091) ∧
    -Real.log (640 / 1091) ≤ (53338181 / 100000000) := by
  have h := checkLog_sound (w := (451 / 1731)) (n := 12)
    (lo := (533381809 / 1000000000)) (hi := (53338181 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1091 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1091 / 640) = 1/(640 / 1091) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (533381809 / 1000000000) (53338181 / 100000000) (Real.log (1091 / 640)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1091 / 640) = -Real.log (640 / 1091) := by
    rw [show ((1091 / 640) : ℝ) = ((640 / 1091) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (30493029 / 25000000) ≤ -Real.log (189 / 640) ∧
    -Real.log (189 / 640) ≤ (609860581 / 500000000) := by
  have h := checkLog_sound (w := (131 / 509)) (n := 12)
    (lo := (26328699 / 50000000)) (hi := (526573981 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 189) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(320 / 189) = 1/(189 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-609860581 / 500000000) (-30493029 / 25000000) (Real.log (189 / 640)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (413154799 / 1000000000) ≤ -Real.log (1000000 / 1511579) ∧
    -Real.log (1000000 / 1511579) ≤ (1032887 / 2500000) := by
  have h := checkLog_sound (w := (511579 / 2511579)) (n := 12)
    (lo := (413154799 / 1000000000)) (hi := (1032887 / 2500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1511579 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1511579 / 1000000) = 1/(1000000 / 1511579) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (413154799 / 1000000000) (1032887 / 2500000) (Real.log (1511579 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1511579 / 1000000) = -Real.log (1000000 / 1511579) := by
    rw [show ((1511579 / 1000000) : ℝ) = ((1000000 / 1511579) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (716577539 / 1000000000) ≤ -Real.log (488421 / 1000000) ∧
    -Real.log (488421 / 1000000) ≤ (716577541 / 1000000000) := by
  have h := checkLog_sound (w := (11579 / 988421)) (n := 12)
    (lo := (23430359 / 1000000000)) (hi := (585759 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 488421) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 488421) = 1/(488421 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-716577541 / 1000000000) (-716577539 / 1000000000) (Real.log (488421 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (207179057 / 500000000) ≤ -Real.log (1000000 / 1513399) ∧
    -Real.log (1000000 / 1513399) ≤ (82871623 / 200000000) := by
  have h := checkLog_sound (w := (513399 / 2513399)) (n := 12)
    (lo := (207179057 / 500000000)) (hi := (82871623 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1513399 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1513399 / 1000000) = 1/(1000000 / 1513399) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (207179057 / 500000000) (82871623 / 200000000) (Real.log (1513399 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1513399 / 1000000) = -Real.log (1000000 / 1513399) := by
    rw [show ((1513399 / 1000000) : ℝ) = ((1000000 / 1513399) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (90038849 / 125000000) ≤ -Real.log (486601 / 1000000) ∧
    -Real.log (486601 / 1000000) ≤ (360155397 / 500000000) := by
  have h := checkLog_sound (w := (13399 / 986601)) (n := 12)
    (lo := (6790903 / 250000000)) (hi := (27163613 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 486601) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 486601) = 1/(486601 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-360155397 / 500000000) (-90038849 / 125000000) (Real.log (486601 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (41151547 / 125000000) ≤ -Real.log (1000000 / 1389873) ∧
    -Real.log (1000000 / 1389873) ≤ (329212377 / 1000000000) := by
  have h := checkLog_sound (w := (389873 / 2389873)) (n := 12)
    (lo := (41151547 / 125000000)) (hi := (329212377 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1389873 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1389873 / 1000000) = 1/(1000000 / 1389873) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (41151547 / 125000000) (329212377 / 1000000000) (Real.log (1389873 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1389873 / 1000000) = -Real.log (1000000 / 1389873) := by
    rw [show ((1389873 / 1000000) : ℝ) = ((1000000 / 1389873) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (247044073 / 500000000) ≤ -Real.log (610127 / 1000000) ∧
    -Real.log (610127 / 1000000) ≤ (494088147 / 1000000000) := by
  have h := checkLog_sound (w := (389873 / 1610127)) (n := 12)
    (lo := (247044073 / 500000000)) (hi := (494088147 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 610127) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 610127) = 1/(610127 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-494088147 / 1000000000) (-247044073 / 500000000) (Real.log (610127 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (66072867 / 200000000) ≤ -Real.log (40000 / 55659) ∧
    -Real.log (40000 / 55659) ≤ (20647771 / 62500000) := by
  have h := checkLog_sound (w := (15659 / 95659)) (n := 12)
    (lo := (66072867 / 200000000)) (hi := (20647771 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((55659 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(55659 / 40000) = 1/(40000 / 55659) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (66072867 / 200000000) (20647771 / 62500000) (Real.log (55659 / 40000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (55659 / 40000) = -Real.log (40000 / 55659) := by
    rw [show ((55659 / 40000) : ℝ) = ((40000 / 55659) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (248358641 / 500000000) ≤ -Real.log (24341 / 40000) ∧
    -Real.log (24341 / 40000) ≤ (496717283 / 1000000000) := by
  have h := checkLog_sound (w := (15659 / 64341)) (n := 12)
    (lo := (248358641 / 500000000)) (hi := (496717283 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000 / 24341) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000 / 24341) = 1/(24341 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-496717283 / 1000000000) (-248358641 / 500000000) (Real.log (24341 / 40000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1129732339 / 1000000000) ≤ -Real.log (500000000000 / 1547414013729) ∧
    -Real.log (500000000000 / 1547414013729) ≤ (1129732341 / 1000000000) := by
  have h := checkLog_sound (w := (547414013729 / 2547414013729)) (n := 12)
    (lo := (436585159 / 1000000000)) (hi := (10914629 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1547414013729 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1547414013729 / 1000000000000) = 1/(500000000000 / 1547414013729) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1129732339 / 1000000000) (1129732341 / 1000000000) (Real.log (1547414013729 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1547414013729 / 500000000000) = -Real.log (500000000000 / 1547414013729) := by
    rw [show ((1547414013729 / 500000000000) : ℝ) = ((500000000000 / 1547414013729) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1134668907 / 1000000000) ≤ -Real.log (100000000000 / 311014362897) ∧
    -Real.log (100000000000 / 311014362897) ≤ (1134668909 / 1000000000) := by
  have h := checkLog_sound (w := (111014362897 / 511014362897)) (n := 12)
    (lo := (441521727 / 1000000000)) (hi := (6898777 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((311014362897 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(311014362897 / 200000000000) = 1/(100000000000 / 311014362897) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1134668907 / 1000000000) (1134668909 / 1000000000) (Real.log (311014362897 / 100000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (311014362897 / 100000000000) = -Real.log (100000000000 / 311014362897) := by
    rw [show ((311014362897 / 100000000000) : ℝ) = ((100000000000 / 311014362897) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (411650261 / 500000000) ≤ -Real.log (250000000000 / 569501513619) ∧
    -Real.log (250000000000 / 569501513619) ≤ (205825131 / 250000000) := by
  have h := checkLog_sound (w := (69501513619 / 1069501513619)) (n := 12)
    (lo := (65076671 / 500000000)) (hi := (130153343 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((569501513619 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(569501513619 / 500000000000) = 1/(250000000000 / 569501513619) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (411650261 / 500000000) (205825131 / 250000000) (Real.log (569501513619 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (569501513619 / 250000000000) = -Real.log (250000000000 / 569501513619) := by
    rw [show ((569501513619 / 250000000000) : ℝ) = ((250000000000 / 569501513619) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (827081617 / 1000000000) ≤ -Real.log (500000000000 / 1143317858757) ∧
    -Real.log (500000000000 / 1143317858757) ≤ (827081619 / 1000000000) := by
  have h := checkLog_sound (w := (143317858757 / 2143317858757)) (n := 12)
    (lo := (133934437 / 1000000000)) (hi := (66967219 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1143317858757 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1143317858757 / 1000000000000) = 1/(500000000000 / 1143317858757) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (827081617 / 1000000000) (827081619 / 1000000000) (Real.log (1143317858757 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1143317858757 / 500000000000) = -Real.log (500000000000 / 1143317858757) := by
    rw [show ((1143317858757 / 500000000000) : ℝ) = ((500000000000 / 1143317858757) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0136
