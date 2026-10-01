import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0068
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

theorem reflection_log_1_neg : (179955943 / 500000000) ≤ -Real.log (2560 / 3669) ∧
    -Real.log (2560 / 3669) ≤ (359911887 / 1000000000) := by
  have h := checkLog_sound (w := (1109 / 6229)) (n := 12)
    (lo := (179955943 / 500000000)) (hi := (359911887 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3669 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3669 / 2560) = 1/(2560 / 3669) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (179955943 / 500000000) (359911887 / 1000000000) (Real.log (3669 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3669 / 2560) = -Real.log (2560 / 3669) := by
    rw [show ((3669 / 2560) : ℝ) = ((2560 / 3669) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (141938571 / 250000000) ≤ -Real.log (1451 / 2560) ∧
    -Real.log (1451 / 2560) ≤ (113550857 / 200000000) := by
  have h := checkLog_sound (w := (1109 / 4011)) (n := 12)
    (lo := (141938571 / 250000000)) (hi := (113550857 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1451) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1451) = 1/(1451 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-113550857 / 200000000) (-141938571 / 250000000) (Real.log (1451 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (35909389 / 100000000) ≤ -Real.log (1280 / 1833) ∧
    -Real.log (1280 / 1833) ≤ (359093891 / 1000000000) := by
  have h := checkLog_sound (w := (553 / 3113)) (n := 12)
    (lo := (35909389 / 100000000)) (hi := (359093891 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1833 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1833 / 1280) = 1/(1280 / 1833) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (35909389 / 100000000) (359093891 / 1000000000) (Real.log (1833 / 1280)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1833 / 1280) = -Real.log (1280 / 1833) := by
    rw [show ((1833 / 1280) : ℝ) = ((1280 / 1833) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (565688879 / 1000000000) ≤ -Real.log (727 / 1280) ∧
    -Real.log (727 / 1280) ≤ (7071111 / 12500000) := by
  have h := checkLog_sound (w := (553 / 2007)) (n := 12)
    (lo := (565688879 / 1000000000)) (hi := (7071111 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 727) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 727) = 1/(727 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-7071111 / 12500000) (-565688879 / 1000000000) (Real.log (727 / 1280)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (62401479 / 100000000) ≤ -Real.log (1280 / 2389) ∧
    -Real.log (1280 / 2389) ≤ (624014791 / 1000000000) := by
  have h := checkLog_sound (w := (1109 / 3669)) (n := 12)
    (lo := (62401479 / 100000000)) (hi := (624014791 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2389 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2389 / 1280) = 1/(1280 / 2389) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (62401479 / 100000000) (624014791 / 1000000000) (Real.log (2389 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2389 / 1280) = -Real.log (1280 / 2389) := by
    rw [show ((2389 / 1280) : ℝ) = ((1280 / 2389) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (2012951799 / 1000000000) ≤ -Real.log (171 / 1280) ∧
    -Real.log (171 / 1280) ≤ (1006475901 / 500000000) := by
  have h := checkLog_sound (w := (149 / 491)) (n := 12)
    (lo := (626657439 / 1000000000)) (hi := (3916609 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 171) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(320 / 171) = 1/(171 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1006475901 / 500000000) (-2012951799 / 1000000000) (Real.log (171 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (124551649 / 200000000) ≤ -Real.log (640 / 1193) ∧
    -Real.log (640 / 1193) ≤ (311379123 / 500000000) := by
  have h := checkLog_sound (w := (553 / 1833)) (n := 12)
    (lo := (124551649 / 200000000)) (hi := (311379123 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1193 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1193 / 640) = 1/(640 / 1193) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (124551649 / 200000000) (311379123 / 500000000) (Real.log (1193 / 640)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1193 / 640) = -Real.log (640 / 1193) := by
    rw [show ((1193 / 640) : ℝ) = ((640 / 1193) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (249445007 / 125000000) ≤ -Real.log (87 / 640) ∧
    -Real.log (87 / 640) ≤ (1995560059 / 1000000000) := by
  have h := checkLog_sound (w := (73 / 247)) (n := 12)
    (lo := (19039553 / 31250000)) (hi := (609265697 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 87) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(160 / 87) = 1/(87 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1995560059 / 1000000000) (-249445007 / 125000000) (Real.log (87 / 640)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (495212571 / 1000000000) ≤ -Real.log (1000000 / 1640847) ∧
    -Real.log (1000000 / 1640847) ≤ (123803143 / 250000000) := by
  have h := checkLog_sound (w := (640847 / 2640847)) (n := 12)
    (lo := (495212571 / 1000000000)) (hi := (123803143 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1640847 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1640847 / 1000000) = 1/(1000000 / 1640847) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (495212571 / 1000000000) (123803143 / 250000000) (Real.log (1640847 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1640847 / 1000000) = -Real.log (1000000 / 1640847) := by
    rw [show ((1640847 / 1000000) : ℝ) = ((1000000 / 1640847) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (256001699 / 250000000) ≤ -Real.log (359153 / 1000000) ∧
    -Real.log (359153 / 1000000) ≤ (512003399 / 500000000) := by
  have h := checkLog_sound (w := (140847 / 859153)) (n := 12)
    (lo := (10339363 / 31250000)) (hi := (330859617 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 359153) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 359153) = 1/(359153 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-512003399 / 500000000) (-256001699 / 250000000) (Real.log (359153 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (496445321 / 1000000000) ≤ -Real.log (1000000 / 1642871) ∧
    -Real.log (1000000 / 1642871) ≤ (248222661 / 500000000) := by
  have h := checkLog_sound (w := (642871 / 2642871)) (n := 12)
    (lo := (496445321 / 1000000000)) (hi := (248222661 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1642871 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1642871 / 1000000) = 1/(1000000 / 1642871) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (496445321 / 1000000000) (248222661 / 500000000) (Real.log (1642871 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1642871 / 1000000) = -Real.log (1000000 / 1642871) := by
    rw [show ((1642871 / 1000000) : ℝ) = ((1000000 / 1642871) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1029658217 / 1000000000) ≤ -Real.log (357129 / 1000000) ∧
    -Real.log (357129 / 1000000) ≤ (1029658219 / 1000000000) := by
  have h := checkLog_sound (w := (142871 / 857129)) (n := 12)
    (lo := (336511037 / 1000000000)) (hi := (168255519 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 357129) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 357129) = 1/(357129 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1029658219 / 1000000000) (-1029658217 / 1000000000) (Real.log (357129 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (412537373 / 1000000000) ≤ -Real.log (500000 / 755323) ∧
    -Real.log (500000 / 755323) ≤ (206268687 / 500000000) := by
  have h := checkLog_sound (w := (255323 / 1255323)) (n := 12)
    (lo := (412537373 / 1000000000)) (hi := (206268687 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((755323 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(755323 / 500000) = 1/(500000 / 755323) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (412537373 / 1000000000) (206268687 / 500000000) (Real.log (755323 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (755323 / 500000) = -Real.log (500000 / 755323) := by
    rw [show ((755323 / 500000) : ℝ) = ((500000 / 755323) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (178667281 / 250000000) ≤ -Real.log (244677 / 500000) ∧
    -Real.log (244677 / 500000) ≤ (357334563 / 500000000) := by
  have h := checkLog_sound (w := (5323 / 494677)) (n := 12)
    (lo := (2690243 / 125000000)) (hi := (4304389 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 244677) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 244677) = 1/(244677 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-357334563 / 500000000) (-178667281 / 250000000) (Real.log (244677 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (103467753 / 250000000) ≤ -Real.log (500000 / 756331) ∧
    -Real.log (500000 / 756331) ≤ (413871013 / 1000000000) := by
  have h := checkLog_sound (w := (256331 / 1256331)) (n := 12)
    (lo := (103467753 / 250000000)) (hi := (413871013 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((756331 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(756331 / 500000) = 1/(500000 / 756331) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (103467753 / 250000000) (413871013 / 1000000000) (Real.log (756331 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (756331 / 500000) = -Real.log (500000 / 756331) := by
    rw [show ((756331 / 500000) : ℝ) = ((500000 / 756331) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (14375947 / 20000000) ≤ -Real.log (243669 / 500000) ∧
    -Real.log (243669 / 500000) ≤ (89849669 / 125000000) := by
  have h := checkLog_sound (w := (6331 / 493669)) (n := 12)
    (lo := (2565017 / 100000000)) (hi := (25650171 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 243669) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 243669) = 1/(243669 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-89849669 / 125000000) (-14375947 / 20000000) (Real.log (243669 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (189902421 / 125000000) ≤ -Real.log (31250000000 / 142770542777) ∧
    -Real.log (31250000000 / 142770542777) ≤ (1519219371 / 1000000000) := by
  have h := checkLog_sound (w := (17770542777 / 267770542777)) (n := 12)
    (lo := (8307813 / 62500000)) (hi := (132925009 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((142770542777 / 125000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(142770542777 / 125000000000) = 1/(31250000000 / 142770542777) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (189902421 / 125000000) (1519219371 / 1000000000) (Real.log (142770542777 / 31250000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (142770542777 / 31250000000) = -Real.log (31250000000 / 142770542777) := by
    rw [show ((142770542777 / 31250000000) : ℝ) = ((31250000000 / 142770542777) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1526103537 / 1000000000) ≤ -Real.log (62500000000 / 287513580527) ∧
    -Real.log (62500000000 / 287513580527) ≤ (76305177 / 50000000) := by
  have h := checkLog_sound (w := (37513580527 / 537513580527)) (n := 12)
    (lo := (139809177 / 1000000000)) (hi := (69904589 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((287513580527 / 250000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(287513580527 / 250000000000) = 1/(62500000000 / 287513580527) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1526103537 / 1000000000) (76305177 / 50000000) (Real.log (287513580527 / 62500000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (287513580527 / 62500000000) = -Real.log (62500000000 / 287513580527) := by
    rw [show ((287513580527 / 62500000000) : ℝ) = ((62500000000 / 287513580527) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (563603249 / 500000000) ≤ -Real.log (250000000000 / 771755211973) ∧
    -Real.log (250000000000 / 771755211973) ≤ (2254413 / 2000000) := by
  have h := checkLog_sound (w := (271755211973 / 1271755211973)) (n := 12)
    (lo := (217029659 / 500000000)) (hi := (434059319 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((771755211973 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(771755211973 / 500000000000) = 1/(250000000000 / 771755211973) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (563603249 / 500000000) (2254413 / 2000000) (Real.log (771755211973 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (771755211973 / 250000000000) = -Real.log (250000000000 / 771755211973) := by
    rw [show ((771755211973 / 250000000000) : ℝ) = ((250000000000 / 771755211973) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (1132668363 / 1000000000) ≤ -Real.log (250000000000 / 775981967341) ∧
    -Real.log (250000000000 / 775981967341) ≤ (226533673 / 200000000) := by
  have h := checkLog_sound (w := (275981967341 / 1275981967341)) (n := 12)
    (lo := (439521183 / 1000000000)) (hi := (13735037 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((775981967341 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(775981967341 / 500000000000) = 1/(250000000000 / 775981967341) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (1132668363 / 1000000000) (226533673 / 200000000) (Real.log (775981967341 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (775981967341 / 250000000000) = -Real.log (250000000000 / 775981967341) := by
    rw [show ((775981967341 / 250000000000) : ℝ) = ((250000000000 / 775981967341) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0068
