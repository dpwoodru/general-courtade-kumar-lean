import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0056
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

theorem reflection_log_1_neg : (92419 / 250000) ≤ -Real.log (512 / 741) ∧
    -Real.log (512 / 741) ≤ (369676001 / 1000000000) := by
  have h := checkLog_sound (w := (229 / 1253)) (n := 12)
    (lo := (92419 / 250000)) (hi := (369676001 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((741 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(741 / 512) = 1/(512 / 741) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (92419 / 250000) (369676001 / 1000000000) (Real.log (741 / 512)) := by
  have h := reflection_log_1_neg
  have he : Real.log (741 / 512) = -Real.log (512 / 741) := by
    rw [show ((741 / 512) : ℝ) = ((512 / 741) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (592877727 / 1000000000) ≤ -Real.log (283 / 512) ∧
    -Real.log (283 / 512) ≤ (18527429 / 31250000) := by
  have h := checkLog_sound (w := (229 / 795)) (n := 12)
    (lo := (592877727 / 1000000000)) (hi := (18527429 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 283) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 283) = 1/(283 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-18527429 / 31250000) (-592877727 / 1000000000) (Real.log (283 / 512)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (73773191 / 200000000) ≤ -Real.log (1280 / 1851) ∧
    -Real.log (1280 / 1851) ≤ (92216489 / 250000000) := by
  have h := checkLog_sound (w := (571 / 3131)) (n := 12)
    (lo := (73773191 / 200000000)) (hi := (92216489 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1851 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1851 / 1280) = 1/(1280 / 1851) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (73773191 / 200000000) (92216489 / 250000000) (Real.log (1851 / 1280)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1851 / 1280) = -Real.log (1280 / 1851) := by
    rw [show ((1851 / 1280) : ℝ) = ((1280 / 1851) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (59075983 / 100000000) ≤ -Real.log (709 / 1280) ∧
    -Real.log (709 / 1280) ≤ (590759831 / 1000000000) := by
  have h := checkLog_sound (w := (571 / 1989)) (n := 12)
    (lo := (59075983 / 100000000)) (hi := (590759831 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 709) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 709) = 1/(709 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-590759831 / 1000000000) (-59075983 / 100000000) (Real.log (709 / 1280)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (319485723 / 500000000) ≤ -Real.log (256 / 485) ∧
    -Real.log (256 / 485) ≤ (638971447 / 1000000000) := by
  have h := checkLog_sound (w := (229 / 741)) (n := 12)
    (lo := (319485723 / 500000000)) (hi := (638971447 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((485 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(485 / 256) = 1/(256 / 485) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (319485723 / 500000000) (638971447 / 1000000000) (Real.log (485 / 256)) := by
  have h := reflection_log_5_neg
  have he : Real.log (485 / 256) = -Real.log (256 / 485) := by
    rw [show ((485 / 256) : ℝ) = ((256 / 485) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (70291893 / 31250000) ≤ -Real.log (27 / 256) ∧
    -Real.log (27 / 256) ≤ (112467029 / 50000000) := by
  have h := checkLog_sound (w := (5 / 59)) (n := 12)
    (lo := (42474759 / 250000000)) (hi := (169899037 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((32 / 27) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(32 / 27) = 1/(27 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-112467029 / 50000000) (-70291893 / 31250000) (Real.log (27 / 256)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (637733567 / 1000000000) ≤ -Real.log (640 / 1211) ∧
    -Real.log (640 / 1211) ≤ (9964587 / 15625000) := by
  have h := checkLog_sound (w := (571 / 1851)) (n := 12)
    (lo := (637733567 / 1000000000)) (hi := (9964587 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1211 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1211 / 640) = 1/(640 / 1211) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (637733567 / 1000000000) (9964587 / 15625000) (Real.log (1211 / 640)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1211 / 640) = -Real.log (640 / 1211) := by
    rw [show ((1211 / 640) : ℝ) = ((640 / 1211) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (222736167 / 100000000) ≤ -Real.log (69 / 640) ∧
    -Real.log (69 / 640) ≤ (1113680837 / 500000000) := by
  have h := checkLog_sound (w := (11 / 149)) (n := 12)
    (lo := (14792013 / 100000000)) (hi := (147920131 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80 / 69) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(80 / 69) = 1/(69 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1113680837 / 500000000) (-222736167 / 100000000) (Real.log (69 / 640)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (20404847 / 40000000) ≤ -Real.log (1000000 / 1665493) ∧
    -Real.log (1000000 / 1665493) ≤ (63765147 / 125000000) := by
  have h := checkLog_sound (w := (665493 / 2665493)) (n := 12)
    (lo := (20404847 / 40000000)) (hi := (63765147 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1665493 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1665493 / 1000000) = 1/(1000000 / 1665493) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (20404847 / 40000000) (63765147 / 125000000) (Real.log (1665493 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1665493 / 1000000) = -Real.log (1000000 / 1665493) := by
    rw [show ((1665493 / 1000000) : ℝ) = ((1000000 / 1665493) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (8555449 / 7812500) ≤ -Real.log (334507 / 1000000) ∧
    -Real.log (334507 / 1000000) ≤ (547548737 / 500000000) := by
  have h := checkLog_sound (w := (165493 / 834507)) (n := 12)
    (lo := (100487573 / 250000000)) (hi := (401950293 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 334507) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 334507) = 1/(334507 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-547548737 / 500000000) (-8555449 / 7812500) (Real.log (334507 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (51137947 / 100000000) ≤ -Real.log (100000 / 166759) ∧
    -Real.log (100000 / 166759) ≤ (511379471 / 1000000000) := by
  have h := checkLog_sound (w := (66759 / 266759)) (n := 12)
    (lo := (51137947 / 100000000)) (hi := (511379471 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((166759 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(166759 / 100000) = 1/(100000 / 166759) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (51137947 / 100000000) (511379471 / 1000000000) (Real.log (166759 / 100000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (166759 / 100000) = -Real.log (100000 / 166759) := by
    rw [show ((166759 / 100000) : ℝ) = ((100000 / 166759) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1101386131 / 1000000000) ≤ -Real.log (33241 / 100000) ∧
    -Real.log (33241 / 100000) ≤ (1101386133 / 1000000000) := by
  have h := checkLog_sound (w := (16759 / 83241)) (n := 12)
    (lo := (408238951 / 1000000000)) (hi := (51029869 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 33241) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(50000 / 33241) = 1/(33241 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1101386133 / 1000000000) (-1101386131 / 1000000000) (Real.log (33241 / 100000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (428850199 / 1000000000) ≤ -Real.log (1000000 / 1535491) ∧
    -Real.log (1000000 / 1535491) ≤ (2144251 / 5000000) := by
  have h := checkLog_sound (w := (535491 / 2535491)) (n := 12)
    (lo := (428850199 / 1000000000)) (hi := (2144251 / 5000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1535491 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1535491 / 1000000) = 1/(1000000 / 1535491) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (428850199 / 1000000000) (2144251 / 5000000) (Real.log (1535491 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1535491 / 1000000) = -Real.log (1000000 / 1535491) := by
    rw [show ((1535491 / 1000000) : ℝ) = ((1000000 / 1535491) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (95846793 / 125000000) ≤ -Real.log (464509 / 1000000) ∧
    -Real.log (464509 / 1000000) ≤ (383387173 / 500000000) := by
  have h := checkLog_sound (w := (35491 / 964509)) (n := 12)
    (lo := (18406791 / 250000000)) (hi := (14725433 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 464509) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 464509) = 1/(464509 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-383387173 / 500000000) (-95846793 / 125000000) (Real.log (464509 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (430244871 / 1000000000) ≤ -Real.log (500000 / 768817) ∧
    -Real.log (500000 / 768817) ≤ (53780609 / 125000000) := by
  have h := checkLog_sound (w := (268817 / 1268817)) (n := 12)
    (lo := (430244871 / 1000000000)) (hi := (53780609 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((768817 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(768817 / 500000) = 1/(500000 / 768817) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (430244871 / 1000000000) (53780609 / 125000000) (Real.log (768817 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (768817 / 500000) = -Real.log (500000 / 768817) := by
    rw [show ((768817 / 500000) : ℝ) = ((500000 / 768817) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (771398493 / 1000000000) ≤ -Real.log (231183 / 500000) ∧
    -Real.log (231183 / 500000) ≤ (154279699 / 200000000) := by
  have h := checkLog_sound (w := (18817 / 481183)) (n := 12)
    (lo := (78251313 / 1000000000)) (hi := (39125657 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 231183) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 231183) = 1/(231183 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-154279699 / 200000000) (-771398493 / 1000000000) (Real.log (231183 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1605218647 / 1000000000) ≤ -Real.log (125000000000 / 622368515457) ∧
    -Real.log (125000000000 / 622368515457) ≤ (32104373 / 20000000) := by
  have h := checkLog_sound (w := (122368515457 / 1122368515457)) (n := 12)
    (lo := (218924287 / 1000000000)) (hi := (855173 / 3906250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((622368515457 / 500000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(622368515457 / 500000000000) = 1/(125000000000 / 622368515457) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1605218647 / 1000000000) (32104373 / 20000000) (Real.log (622368515457 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (622368515457 / 125000000000) = -Real.log (125000000000 / 622368515457) := by
    rw [show ((622368515457 / 125000000000) : ℝ) = ((125000000000 / 622368515457) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1612765601 / 1000000000) ≤ -Real.log (500000000000 / 2508333082639) ∧
    -Real.log (500000000000 / 2508333082639) ≤ (403191401 / 250000000) := by
  have h := checkLog_sound (w := (508333082639 / 4508333082639)) (n := 12)
    (lo := (226471241 / 1000000000)) (hi := (113235621 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2508333082639 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2508333082639 / 2000000000000) = 1/(500000000000 / 2508333082639) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1612765601 / 1000000000) (403191401 / 250000000) (Real.log (2508333082639 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (2508333082639 / 500000000000) = -Real.log (500000000000 / 2508333082639) := by
    rw [show ((2508333082639 / 500000000000) : ℝ) = ((500000000000 / 2508333082639) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (37363267 / 31250000) ≤ -Real.log (500000000000 / 1652810817443) ∧
    -Real.log (500000000000 / 1652810817443) ≤ (597812273 / 500000000) := by
  have h := checkLog_sound (w := (652810817443 / 2652810817443)) (n := 12)
    (lo := (125619341 / 250000000)) (hi := (100495473 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1652810817443 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1652810817443 / 1000000000000) = 1/(500000000000 / 1652810817443) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (37363267 / 31250000) (597812273 / 500000000) (Real.log (1652810817443 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (1652810817443 / 500000000000) = -Real.log (500000000000 / 1652810817443) := by
    rw [show ((1652810817443 / 500000000000) : ℝ) = ((500000000000 / 1652810817443) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (300410841 / 250000000) ≤ -Real.log (500000000000 / 1662788786373) ∧
    -Real.log (500000000000 / 1662788786373) ≤ (600821683 / 500000000) := by
  have h := checkLog_sound (w := (662788786373 / 2662788786373)) (n := 12)
    (lo := (63562023 / 125000000)) (hi := (101699237 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1662788786373 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1662788786373 / 1000000000000) = 1/(500000000000 / 1662788786373) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (300410841 / 250000000) (600821683 / 500000000) (Real.log (1662788786373 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1662788786373 / 500000000000) = -Real.log (500000000000 / 1662788786373) := by
    rw [show ((1662788786373 / 500000000000) : ℝ) = ((500000000000 / 1662788786373) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0056
