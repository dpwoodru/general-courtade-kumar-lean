import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0151
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

theorem reflection_log_1_neg : (72408323 / 250000000) ≤ -Real.log (128 / 171) ∧
    -Real.log (128 / 171) ≤ (289633293 / 1000000000) := by
  have h := checkLog_sound (w := (43 / 299)) (n := 12)
    (lo := (72408323 / 250000000)) (hi := (289633293 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((171 / 128) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(171 / 128) = 1/(128 / 171) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (72408323 / 250000000) (289633293 / 1000000000) (Real.log (171 / 128)) := by
  have h := reflection_log_1_neg
  have he : Real.log (171 / 128) = -Real.log (128 / 171) := by
    rw [show ((171 / 128) : ℝ) = ((128 / 171) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (409379007 / 1000000000) ≤ -Real.log (85 / 128) ∧
    -Real.log (85 / 128) ≤ (6396547 / 15625000) := by
  have h := checkLog_sound (w := (43 / 213)) (n := 12)
    (lo := (409379007 / 1000000000)) (hi := (6396547 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((128 / 85) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(128 / 85) = 1/(85 / 128) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-6396547 / 15625000) (-409379007 / 1000000000) (Real.log (85 / 128)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (144377857 / 500000000) ≤ -Real.log (2560 / 3417) ∧
    -Real.log (2560 / 3417) ≤ (57751143 / 200000000) := by
  have h := checkLog_sound (w := (857 / 5977)) (n := 12)
    (lo := (144377857 / 500000000)) (hi := (57751143 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3417 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3417 / 2560) = 1/(2560 / 3417) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (144377857 / 500000000) (57751143 / 200000000) (Real.log (3417 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3417 / 2560) = -Real.log (2560 / 3417) := by
    rw [show ((3417 / 2560) : ℝ) = ((2560 / 3417) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (25475991 / 62500000) ≤ -Real.log (1703 / 2560) ∧
    -Real.log (1703 / 2560) ≤ (407615857 / 1000000000) := by
  have h := checkLog_sound (w := (857 / 4263)) (n := 12)
    (lo := (25475991 / 62500000)) (hi := (407615857 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1703) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1703) = 1/(1703 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-407615857 / 1000000000) (-25475991 / 62500000) (Real.log (1703 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (513945751 / 1000000000) ≤ -Real.log (64 / 107) ∧
    -Real.log (64 / 107) ≤ (64243219 / 125000000) := by
  have h := checkLog_sound (w := (43 / 171)) (n := 12)
    (lo := (513945751 / 1000000000)) (hi := (64243219 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((107 / 64) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(107 / 64) = 1/(64 / 107) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (513945751 / 1000000000) (64243219 / 125000000) (Real.log (107 / 64)) := by
  have h := reflection_log_5_neg
  have he : Real.log (107 / 64) = -Real.log (64 / 107) := by
    rw [show ((107 / 64) : ℝ) = ((64 / 107) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (222872129 / 200000000) ≤ -Real.log (21 / 64) ∧
    -Real.log (21 / 64) ≤ (1114360647 / 1000000000) := by
  have h := checkLog_sound (w := (11 / 53)) (n := 12)
    (lo := (84242693 / 200000000)) (hi := (210606733 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((32 / 21) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(32 / 21) = 1/(21 / 64) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1114360647 / 1000000000) (-222872129 / 200000000) (Real.log (21 / 64)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (256271449 / 500000000) ≤ -Real.log (1280 / 2137) ∧
    -Real.log (1280 / 2137) ≤ (512542899 / 1000000000) := by
  have h := checkLog_sound (w := (857 / 3417)) (n := 12)
    (lo := (256271449 / 500000000)) (hi := (512542899 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2137 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2137 / 1280) = 1/(1280 / 2137) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (256271449 / 500000000) (512542899 / 1000000000) (Real.log (2137 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2137 / 1280) = -Real.log (1280 / 2137) := by
    rw [show ((2137 / 1280) : ℝ) = ((1280 / 2137) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (1107243177 / 1000000000) ≤ -Real.log (423 / 1280) ∧
    -Real.log (423 / 1280) ≤ (1107243179 / 1000000000) := by
  have h := checkLog_sound (w := (217 / 1063)) (n := 12)
    (lo := (414095997 / 1000000000)) (hi := (207047999 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 423) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 423) = 1/(423 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1107243179 / 1000000000) (-1107243177 / 1000000000) (Real.log (423 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (39506791 / 100000000) ≤ -Real.log (200000 / 296897) ∧
    -Real.log (200000 / 296897) ≤ (395067911 / 1000000000) := by
  have h := checkLog_sound (w := (96897 / 496897)) (n := 12)
    (lo := (39506791 / 100000000)) (hi := (395067911 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((296897 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(296897 / 200000) = 1/(200000 / 296897) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (39506791 / 100000000) (395067911 / 1000000000) (Real.log (296897 / 200000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (296897 / 200000) = -Real.log (200000 / 296897) := by
    rw [show ((296897 / 200000) : ℝ) = ((200000 / 296897) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (662588877 / 1000000000) ≤ -Real.log (103103 / 200000) ∧
    -Real.log (103103 / 200000) ≤ (331294439 / 500000000) := by
  have h := checkLog_sound (w := (96897 / 303103)) (n := 12)
    (lo := (662588877 / 1000000000)) (hi := (331294439 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 103103) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 103103) = 1/(103103 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-331294439 / 500000000) (-662588877 / 1000000000) (Real.log (103103 / 200000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (396277699 / 1000000000) ≤ -Real.log (500000 / 743141) ∧
    -Real.log (500000 / 743141) ≤ (3962777 / 10000000) := by
  have h := checkLog_sound (w := (243141 / 1243141)) (n := 12)
    (lo := (396277699 / 1000000000)) (hi := (3962777 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((743141 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(743141 / 500000) = 1/(500000 / 743141) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (396277699 / 1000000000) (3962777 / 10000000) (Real.log (743141 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (743141 / 500000) = -Real.log (500000 / 743141) := by
    rw [show ((743141 / 500000) : ℝ) = ((500000 / 743141) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (333040401 / 500000000) ≤ -Real.log (256859 / 500000) ∧
    -Real.log (256859 / 500000) ≤ (666080803 / 1000000000) := by
  have h := checkLog_sound (w := (243141 / 756859)) (n := 12)
    (lo := (333040401 / 500000000)) (hi := (666080803 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 256859) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 256859) = 1/(256859 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-666080803 / 1000000000) (-333040401 / 500000000) (Real.log (256859 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (312111479 / 1000000000) ≤ -Real.log (1000000 / 1366307) ∧
    -Real.log (1000000 / 1366307) ≤ (7802787 / 25000000) := by
  have h := checkLog_sound (w := (366307 / 2366307)) (n := 12)
    (lo := (312111479 / 1000000000)) (hi := (7802787 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1366307 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1366307 / 1000000) = 1/(1000000 / 1366307) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (312111479 / 1000000000) (7802787 / 25000000) (Real.log (1366307 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1366307 / 1000000) = -Real.log (1000000 / 1366307) := by
    rw [show ((1366307 / 1000000) : ℝ) = ((1000000 / 1366307) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (114047667 / 250000000) ≤ -Real.log (633693 / 1000000) ∧
    -Real.log (633693 / 1000000) ≤ (456190669 / 1000000000) := by
  have h := checkLog_sound (w := (366307 / 1633693)) (n := 12)
    (lo := (114047667 / 250000000)) (hi := (456190669 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 633693) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 633693) = 1/(633693 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-456190669 / 1000000000) (-114047667 / 250000000) (Real.log (633693 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (313242357 / 1000000000) ≤ -Real.log (1000000 / 1367853) ∧
    -Real.log (1000000 / 1367853) ≤ (156621179 / 500000000) := by
  have h := checkLog_sound (w := (367853 / 2367853)) (n := 12)
    (lo := (313242357 / 1000000000)) (hi := (156621179 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1367853 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1367853 / 1000000) = 1/(1000000 / 1367853) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (313242357 / 1000000000) (156621179 / 500000000) (Real.log (1367853 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1367853 / 1000000) = -Real.log (1000000 / 1367853) := by
    rw [show ((1367853 / 1000000) : ℝ) = ((1000000 / 1367853) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (114658329 / 250000000) ≤ -Real.log (632147 / 1000000) ∧
    -Real.log (632147 / 1000000) ≤ (458633317 / 1000000000) := by
  have h := checkLog_sound (w := (367853 / 1632147)) (n := 12)
    (lo := (114658329 / 250000000)) (hi := (458633317 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 632147) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 632147) = 1/(632147 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-458633317 / 1000000000) (-114658329 / 250000000) (Real.log (632147 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (264414197 / 250000000) ≤ -Real.log (10000000000 / 28796155301) ∧
    -Real.log (10000000000 / 28796155301) ≤ (105765679 / 100000000) := by
  have h := checkLog_sound (w := (8796155301 / 48796155301)) (n := 12)
    (lo := (45563701 / 125000000)) (hi := (364509609 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((28796155301 / 20000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(28796155301 / 20000000000) = 1/(10000000000 / 28796155301) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (264414197 / 250000000) (105765679 / 100000000) (Real.log (28796155301 / 10000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (28796155301 / 10000000000) = -Real.log (10000000000 / 28796155301) := by
    rw [show ((28796155301 / 10000000000) : ℝ) = ((10000000000 / 28796155301) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1062358501 / 1000000000) ≤ -Real.log (125000000000 / 361648316781) ∧
    -Real.log (125000000000 / 361648316781) ≤ (1062358503 / 1000000000) := by
  have h := checkLog_sound (w := (111648316781 / 611648316781)) (n := 12)
    (lo := (369211321 / 1000000000)) (hi := (184605661 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((361648316781 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(361648316781 / 250000000000) = 1/(125000000000 / 361648316781) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1062358501 / 1000000000) (1062358503 / 1000000000) (Real.log (361648316781 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (361648316781 / 125000000000) = -Real.log (125000000000 / 361648316781) := by
    rw [show ((361648316781 / 125000000000) : ℝ) = ((125000000000 / 361648316781) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (192075537 / 250000000) ≤ -Real.log (500000000000 / 1078051201449) ∧
    -Real.log (500000000000 / 1078051201449) ≤ (15366043 / 20000000) := by
  have h := checkLog_sound (w := (78051201449 / 2078051201449)) (n := 12)
    (lo := (9394371 / 125000000)) (hi := (75154969 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1078051201449 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1078051201449 / 1000000000000) = 1/(500000000000 / 1078051201449) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (192075537 / 250000000) (15366043 / 20000000) (Real.log (1078051201449 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (1078051201449 / 500000000000) = -Real.log (500000000000 / 1078051201449) := by
    rw [show ((1078051201449 / 500000000000) : ℝ) = ((500000000000 / 1078051201449) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (771875673 / 1000000000) ≤ -Real.log (62500000000 / 135238817079) ∧
    -Real.log (62500000000 / 135238817079) ≤ (30875027 / 40000000) := by
  have h := checkLog_sound (w := (10238817079 / 260238817079)) (n := 12)
    (lo := (78728493 / 1000000000)) (hi := (39364247 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((135238817079 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(135238817079 / 125000000000) = 1/(62500000000 / 135238817079) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (771875673 / 1000000000) (30875027 / 40000000) (Real.log (135238817079 / 62500000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (135238817079 / 62500000000) = -Real.log (62500000000 / 135238817079) := by
    rw [show ((135238817079 / 62500000000) : ℝ) = ((62500000000 / 135238817079) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0151
