import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0036
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

theorem reflection_log_1_neg : (192870301 / 500000000) ≤ -Real.log (512 / 753) ∧
    -Real.log (512 / 753) ≤ (385740603 / 1000000000) := by
  have h := checkLog_sound (w := (241 / 1265)) (n := 12)
    (lo := (192870301 / 500000000)) (hi := (385740603 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((753 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(753 / 512) = 1/(512 / 753) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (192870301 / 500000000) (385740603 / 1000000000) (Real.log (753 / 512)) := by
  have h := reflection_log_1_neg
  have he : Real.log (753 / 512) = -Real.log (512 / 753) := by
    rw [show ((753 / 512) : ℝ) = ((512 / 753) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (159051451 / 250000000) ≤ -Real.log (271 / 512) ∧
    -Real.log (271 / 512) ≤ (127241161 / 200000000) := by
  have h := checkLog_sound (w := (241 / 783)) (n := 12)
    (lo := (159051451 / 250000000)) (hi := (127241161 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 271) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 271) = 1/(271 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-127241161 / 200000000) (-159051451 / 250000000) (Real.log (271 / 512)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (24058967 / 62500000) ≤ -Real.log (1280 / 1881) ∧
    -Real.log (1280 / 1881) ≤ (384943473 / 1000000000) := by
  have h := checkLog_sound (w := (601 / 3161)) (n := 12)
    (lo := (24058967 / 62500000)) (hi := (384943473 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1881 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1881 / 1280) = 1/(1280 / 1881) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (24058967 / 62500000) (384943473 / 1000000000) (Real.log (1881 / 1280)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1881 / 1280) = -Real.log (1280 / 1881) := by
    rw [show ((1881 / 1280) : ℝ) = ((1280 / 1881) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (633994229 / 1000000000) ≤ -Real.log (679 / 1280) ∧
    -Real.log (679 / 1280) ≤ (63399423 / 100000000) := by
  have h := checkLog_sound (w := (601 / 1959)) (n := 12)
    (lo := (633994229 / 1000000000)) (hi := (63399423 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 679) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 679) = 1/(679 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-63399423 / 100000000) (-633994229 / 1000000000) (Real.log (679 / 1280)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (663412581 / 1000000000) ≤ -Real.log (256 / 497) ∧
    -Real.log (256 / 497) ≤ (331706291 / 500000000) := by
  have h := checkLog_sound (w := (241 / 753)) (n := 12)
    (lo := (663412581 / 1000000000)) (hi := (331706291 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((497 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(497 / 256) = 1/(256 / 497) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (663412581 / 1000000000) (331706291 / 500000000) (Real.log (497 / 256)) := by
  have h := reflection_log_5_neg
  have he : Real.log (497 / 256) = -Real.log (256 / 497) := by
    rw [show ((497 / 256) : ℝ) = ((256 / 497) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (2837127241 / 1000000000) ≤ -Real.log (15 / 256) ∧
    -Real.log (15 / 256) ≤ (1418563623 / 500000000) := by
  have h := checkLog_sound (w := (1 / 31)) (n := 12)
    (lo := (64538521 / 1000000000)) (hi := (32269261 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((16 / 15) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(16 / 15) = 1/(15 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1418563623 / 500000000) (-2837127241 / 1000000000) (Real.log (15 / 256)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (10346947 / 15625000) ≤ -Real.log (640 / 1241) ∧
    -Real.log (640 / 1241) ≤ (662204609 / 1000000000) := by
  have h := checkLog_sound (w := (601 / 1881)) (n := 12)
    (lo := (10346947 / 15625000)) (hi := (662204609 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1241 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1241 / 640) = 1/(640 / 1241) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (10346947 / 15625000) (662204609 / 1000000000) (Real.log (1241 / 640)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1241 / 640) = -Real.log (640 / 1241) := by
    rw [show ((1241 / 640) : ℝ) = ((640 / 1241) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (2797906527 / 1000000000) ≤ -Real.log (39 / 640) ∧
    -Real.log (39 / 640) ≤ (699476633 / 250000000) := by
  have h := checkLog_sound (w := (1 / 79)) (n := 12)
    (lo := (25317807 / 1000000000)) (hi := (1582363 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40 / 39) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(40 / 39) = 1/(39 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-699476633 / 250000000) (-2797906527 / 1000000000) (Real.log (39 / 640)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (535951703 / 1000000000) ≤ -Real.log (500000 / 854537) ∧
    -Real.log (500000 / 854537) ≤ (66993963 / 125000000) := by
  have h := checkLog_sound (w := (354537 / 1354537)) (n := 12)
    (lo := (535951703 / 1000000000)) (hi := (66993963 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((854537 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(854537 / 500000) = 1/(500000 / 854537) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (535951703 / 1000000000) (66993963 / 125000000) (Real.log (854537 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (854537 / 500000) = -Real.log (500000 / 854537) := by
    rw [show ((854537 / 500000) : ℝ) = ((500000 / 854537) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (1234686339 / 1000000000) ≤ -Real.log (145463 / 500000) ∧
    -Real.log (145463 / 500000) ≤ (1234686341 / 1000000000) := by
  have h := checkLog_sound (w := (104537 / 395463)) (n := 12)
    (lo := (541539159 / 1000000000)) (hi := (13538479 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 145463) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 145463) = 1/(145463 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-1234686341 / 1000000000) (-1234686339 / 1000000000) (Real.log (145463 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (537295387 / 1000000000) ≤ -Real.log (250000 / 427843) ∧
    -Real.log (250000 / 427843) ≤ (134323847 / 250000000) := by
  have h := checkLog_sound (w := (177843 / 677843)) (n := 12)
    (lo := (537295387 / 1000000000)) (hi := (134323847 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((427843 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(427843 / 250000) = 1/(250000 / 427843) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (537295387 / 1000000000) (134323847 / 250000000) (Real.log (427843 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (427843 / 250000) = -Real.log (250000 / 427843) := by
    rw [show ((427843 / 250000) : ℝ) = ((250000 / 427843) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (155327077 / 125000000) ≤ -Real.log (72157 / 250000) ∧
    -Real.log (72157 / 250000) ≤ (621308309 / 500000000) := by
  have h := checkLog_sound (w := (52843 / 197157)) (n := 12)
    (lo := (137367359 / 250000000)) (hi := (549469437 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 72157) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(125000 / 72157) = 1/(72157 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-621308309 / 500000000) (-155327077 / 125000000) (Real.log (72157 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (22904301 / 50000000) ≤ -Real.log (200000 / 316209) ∧
    -Real.log (200000 / 316209) ≤ (458086021 / 1000000000) := by
  have h := checkLog_sound (w := (116209 / 516209)) (n := 12)
    (lo := (22904301 / 50000000)) (hi := (458086021 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((316209 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(316209 / 200000) = 1/(200000 / 316209) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (22904301 / 50000000) (458086021 / 1000000000) (Real.log (316209 / 200000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (316209 / 200000) = -Real.log (200000 / 316209) := by
    rw [show ((316209 / 200000) : ℝ) = ((200000 / 316209) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (434995881 / 500000000) ≤ -Real.log (83791 / 200000) ∧
    -Real.log (83791 / 200000) ≤ (217497941 / 250000000) := by
  have h := checkLog_sound (w := (16209 / 183791)) (n := 12)
    (lo := (88422291 / 500000000)) (hi := (176844583 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 83791) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(100000 / 83791) = 1/(83791 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-217497941 / 250000000) (-434995881 / 500000000) (Real.log (83791 / 200000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (14363793 / 31250000) ≤ -Real.log (500000 / 791753) ∧
    -Real.log (500000 / 791753) ≤ (459641377 / 1000000000) := by
  have h := checkLog_sound (w := (291753 / 1291753)) (n := 12)
    (lo := (14363793 / 31250000)) (hi := (459641377 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((791753 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(791753 / 500000) = 1/(500000 / 791753) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (14363793 / 31250000) (459641377 / 1000000000) (Real.log (791753 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (791753 / 500000) = -Real.log (500000 / 791753) := by
    rw [show ((791753 / 500000) : ℝ) = ((500000 / 791753) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (437941611 / 500000000) ≤ -Real.log (208247 / 500000) ∧
    -Real.log (208247 / 500000) ≤ (109485403 / 125000000) := by
  have h := checkLog_sound (w := (41753 / 458247)) (n := 12)
    (lo := (91368021 / 500000000)) (hi := (182736043 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 208247) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 208247) = 1/(208247 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-109485403 / 125000000) (-437941611 / 500000000) (Real.log (208247 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1770638041 / 1000000000) ≤ -Real.log (20000000000 / 117492008277) ∧
    -Real.log (20000000000 / 117492008277) ≤ (442659511 / 250000000) := by
  have h := checkLog_sound (w := (37492008277 / 197492008277)) (n := 12)
    (lo := (384343681 / 1000000000)) (hi := (192171841 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((117492008277 / 80000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(117492008277 / 80000000000) = 1/(20000000000 / 117492008277) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1770638041 / 1000000000) (442659511 / 250000000) (Real.log (117492008277 / 20000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (117492008277 / 20000000000) = -Real.log (20000000000 / 117492008277) := by
    rw [show ((117492008277 / 20000000000) : ℝ) = ((20000000000 / 117492008277) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (444978001 / 250000000) ≤ -Real.log (125000000000 / 741166830661) ∧
    -Real.log (125000000000 / 741166830661) ≤ (1779912007 / 1000000000) := by
  have h := checkLog_sound (w := (241166830661 / 1241166830661)) (n := 12)
    (lo := (98404411 / 250000000)) (hi := (78723529 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((741166830661 / 500000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(741166830661 / 500000000000) = 1/(125000000000 / 741166830661) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (444978001 / 250000000) (1779912007 / 1000000000) (Real.log (741166830661 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (741166830661 / 125000000000) = -Real.log (125000000000 / 741166830661) := by
    rw [show ((741166830661 / 125000000000) : ℝ) = ((125000000000 / 741166830661) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1328077783 / 1000000000) ≤ -Real.log (125000000000 / 471722798391) ∧
    -Real.log (125000000000 / 471722798391) ≤ (265615557 / 200000000) := by
  have h := checkLog_sound (w := (221722798391 / 721722798391)) (n := 12)
    (lo := (634930603 / 1000000000)) (hi := (158732651 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((471722798391 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(471722798391 / 250000000000) = 1/(125000000000 / 471722798391) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (1328077783 / 1000000000) (265615557 / 200000000) (Real.log (471722798391 / 125000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (471722798391 / 125000000000) = -Real.log (125000000000 / 471722798391) := by
    rw [show ((471722798391 / 125000000000) : ℝ) = ((125000000000 / 471722798391) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (667762299 / 500000000) ≤ -Real.log (500000000000 / 1900994972317) ∧
    -Real.log (500000000000 / 1900994972317) ≤ (6677623 / 5000000) := by
  have h := checkLog_sound (w := (900994972317 / 2900994972317)) (n := 12)
    (lo := (321188709 / 500000000)) (hi := (642377419 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1900994972317 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1900994972317 / 1000000000000) = 1/(500000000000 / 1900994972317) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (667762299 / 500000000) (6677623 / 5000000) (Real.log (1900994972317 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1900994972317 / 500000000000) = -Real.log (500000000000 / 1900994972317) := by
    rw [show ((1900994972317 / 500000000000) : ℝ) = ((500000000000 / 1900994972317) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0036
