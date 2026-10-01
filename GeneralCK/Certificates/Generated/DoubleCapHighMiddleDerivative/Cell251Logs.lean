import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell251
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed GeneralCK.Reflection

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

theorem reflection_log_1_neg : (167398363 / 500000000) ≤ -Real.log (1280 / 1789) ∧
    -Real.log (1280 / 1789) ≤ (334796727 / 1000000000) := by
  have h := checkLog_sound (w := (509 / 3069)) (n := 12)
    (lo := (167398363 / 500000000)) (hi := (334796727 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1789 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1789 / 1280) = 1/(1280 / 1789) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (167398363 / 500000000) (334796727 / 1000000000) (Real.log (1789 / 1280)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1789 / 1280) = -Real.log (1280 / 1789) := by
    rw [show ((1789 / 1280) : ℝ) = ((1280 / 1789) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (506926983 / 1000000000) ≤ -Real.log (771 / 1280) ∧
    -Real.log (771 / 1280) ≤ (63365873 / 125000000) := by
  have h := checkLog_sound (w := (509 / 2051)) (n := 12)
    (lo := (506926983 / 1000000000)) (hi := (63365873 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 771) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 771) = 1/(771 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-63365873 / 125000000) (-506926983 / 1000000000) (Real.log (771 / 1280)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (33437741 / 100000000) ≤ -Real.log (5120 / 7153) ∧
    -Real.log (5120 / 7153) ≤ (334377411 / 1000000000) := by
  have h := checkLog_sound (w := (2033 / 12273)) (n := 12)
    (lo := (33437741 / 100000000)) (hi := (334377411 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7153 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7153 / 5120) = 1/(5120 / 7153) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (33437741 / 100000000) (334377411 / 1000000000) (Real.log (7153 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (7153 / 5120) = -Real.log (5120 / 7153) := by
    rw [show ((7153 / 5120) : ℝ) = ((5120 / 7153) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (505954693 / 1000000000) ≤ -Real.log (3087 / 5120) ∧
    -Real.log (3087 / 5120) ≤ (252977347 / 500000000) := by
  have h := checkLog_sound (w := (2033 / 8207)) (n := 12)
    (lo := (505954693 / 1000000000)) (hi := (252977347 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3087) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3087) = 1/(3087 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-252977347 / 500000000) (-505954693 / 1000000000) (Real.log (3087 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (7781371 / 31250000) ≤ -Real.log (1000000 / 1282747) ∧
    -Real.log (1000000 / 1282747) ≤ (249003873 / 1000000000) := by
  have h := checkLog_sound (w := (282747 / 2282747)) (n := 12)
    (lo := (7781371 / 31250000)) (hi := (249003873 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1282747 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1282747 / 1000000) = 1/(1000000 / 1282747) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (7781371 / 31250000) (249003873 / 1000000000) (Real.log (1282747 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1282747 / 1000000) = -Real.log (1000000 / 1282747) := by
    rw [show ((1282747 / 1000000) : ℝ) = ((1000000 / 1282747) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (332326641 / 1000000000) ≤ -Real.log (717253 / 1000000) ∧
    -Real.log (717253 / 1000000) ≤ (166163321 / 500000000) := by
  have h := checkLog_sound (w := (282747 / 1717253)) (n := 12)
    (lo := (332326641 / 1000000000)) (hi := (166163321 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 717253) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 717253) = 1/(717253 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-166163321 / 500000000) (-332326641 / 1000000000) (Real.log (717253 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (124667179 / 500000000) ≤ -Real.log (1000000 / 1283171) ∧
    -Real.log (1000000 / 1283171) ≤ (249334359 / 1000000000) := by
  have h := checkLog_sound (w := (283171 / 2283171)) (n := 12)
    (lo := (124667179 / 500000000)) (hi := (249334359 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1283171 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1283171 / 1000000) = 1/(1000000 / 1283171) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (124667179 / 500000000) (249334359 / 1000000000) (Real.log (1283171 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1283171 / 1000000) = -Real.log (1000000 / 1283171) := by
    rw [show ((1283171 / 1000000) : ℝ) = ((1000000 / 1283171) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (8322949 / 25000000) ≤ -Real.log (716829 / 1000000) ∧
    -Real.log (716829 / 1000000) ≤ (332917961 / 1000000000) := by
  have h := checkLog_sound (w := (283171 / 1716829)) (n := 12)
    (lo := (8322949 / 25000000)) (hi := (332917961 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 716829) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 716829) = 1/(716829 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-332917961 / 1000000000) (-8322949 / 25000000) (Real.log (716829 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (186030503 / 1000000000) ≤ -Real.log (1000000 / 1204459) ∧
    -Real.log (1000000 / 1204459) ≤ (23253813 / 125000000) := by
  have h := checkLog_sound (w := (204459 / 2204459)) (n := 12)
    (lo := (186030503 / 1000000000)) (hi := (23253813 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1204459 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1204459 / 1000000) = 1/(1000000 / 1204459) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (186030503 / 1000000000) (23253813 / 125000000) (Real.log (1204459 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1204459 / 1000000) = -Real.log (1000000 / 1204459) := by
    rw [show ((1204459 / 1000000) : ℝ) = ((1000000 / 1204459) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (57183223 / 250000000) ≤ -Real.log (795541 / 1000000) ∧
    -Real.log (795541 / 1000000) ≤ (228732893 / 1000000000) := by
  have h := checkLog_sound (w := (204459 / 1795541)) (n := 12)
    (lo := (57183223 / 250000000)) (hi := (228732893 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 795541) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 795541) = 1/(795541 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-228732893 / 1000000000) (-57183223 / 250000000) (Real.log (795541 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (186296977 / 1000000000) ≤ -Real.log (50000 / 60239) ∧
    -Real.log (50000 / 60239) ≤ (93148489 / 500000000) := by
  have h := checkLog_sound (w := (10239 / 110239)) (n := 12)
    (lo := (186296977 / 1000000000)) (hi := (93148489 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((60239 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(60239 / 50000) = 1/(50000 / 60239) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (186296977 / 1000000000) (93148489 / 500000000) (Real.log (60239 / 50000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (60239 / 50000) = -Real.log (50000 / 60239) := by
    rw [show ((60239 / 50000) : ℝ) = ((50000 / 60239) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (229136473 / 1000000000) ≤ -Real.log (39761 / 50000) ∧
    -Real.log (39761 / 50000) ≤ (114568237 / 500000000) := by
  have h := checkLog_sound (w := (10239 / 89761)) (n := 12)
    (lo := (229136473 / 1000000000)) (hi := (114568237 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 39761) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 39761) = 1/(39761 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-114568237 / 500000000) (-229136473 / 1000000000) (Real.log (39761 / 50000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (840332103 / 1000000000) ≤ -Real.log (25000000000 / 57928409459) ∧
    -Real.log (25000000000 / 57928409459) ≤ (168066421 / 200000000) := by
  have h := checkLog_sound (w := (7928409459 / 107928409459)) (n := 12)
    (lo := (147184923 / 1000000000)) (hi := (36796231 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((57928409459 / 50000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(57928409459 / 50000000000) = 1/(25000000000 / 57928409459) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (840332103 / 1000000000) (168066421 / 200000000) (Real.log (57928409459 / 25000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (57928409459 / 25000000000) = -Real.log (25000000000 / 57928409459) := by
    rw [show ((57928409459 / 25000000000) : ℝ) = ((25000000000 / 57928409459) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (841723709 / 1000000000) ≤ -Real.log (500000000000 / 1160181582361) ∧
    -Real.log (500000000000 / 1160181582361) ≤ (841723711 / 1000000000) := by
  have h := checkLog_sound (w := (160181582361 / 2160181582361)) (n := 12)
    (lo := (148576529 / 1000000000)) (hi := (14857653 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1160181582361 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1160181582361 / 1000000000000) = 1/(500000000000 / 1160181582361) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (841723709 / 1000000000) (841723711 / 1000000000) (Real.log (1160181582361 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (1160181582361 / 500000000000) = -Real.log (500000000000 / 1160181582361) := by
    rw [show ((1160181582361 / 500000000000) : ℝ) = ((500000000000 / 1160181582361) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (581330513 / 1000000000) ≤ -Real.log (500000000000 / 894208180377) ∧
    -Real.log (500000000000 / 894208180377) ≤ (290665257 / 500000000) := by
  have h := checkLog_sound (w := (394208180377 / 1394208180377)) (n := 12)
    (lo := (581330513 / 1000000000)) (hi := (290665257 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((894208180377 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(894208180377 / 500000000000) = 1/(500000000000 / 894208180377) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (581330513 / 1000000000) (290665257 / 500000000) (Real.log (894208180377 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (894208180377 / 500000000000) = -Real.log (500000000000 / 894208180377) := by
    rw [show ((894208180377 / 500000000000) : ℝ) = ((500000000000 / 894208180377) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (291126159 / 500000000) ≤ -Real.log (500000000000 / 895032846049) ∧
    -Real.log (500000000000 / 895032846049) ≤ (582252319 / 1000000000) := by
  have h := checkLog_sound (w := (395032846049 / 1395032846049)) (n := 12)
    (lo := (291126159 / 500000000)) (hi := (582252319 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((895032846049 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(895032846049 / 500000000000) = 1/(500000000000 / 895032846049) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (291126159 / 500000000) (582252319 / 1000000000) (Real.log (895032846049 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (895032846049 / 500000000000) = -Real.log (500000000000 / 895032846049) := by
    rw [show ((895032846049 / 500000000000) : ℝ) = ((500000000000 / 895032846049) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (103690849 / 250000000) ≤ -Real.log (500000000000 / 757006238521) ∧
    -Real.log (500000000000 / 757006238521) ≤ (414763397 / 1000000000) := by
  have h := checkLog_sound (w := (257006238521 / 1257006238521)) (n := 12)
    (lo := (103690849 / 250000000)) (hi := (414763397 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((757006238521 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(757006238521 / 500000000000) = 1/(500000000000 / 757006238521) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (103690849 / 250000000) (414763397 / 1000000000) (Real.log (757006238521 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (757006238521 / 500000000000) = -Real.log (500000000000 / 757006238521) := by
    rw [show ((757006238521 / 500000000000) : ℝ) = ((500000000000 / 757006238521) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (8308669 / 20000000) ≤ -Real.log (62500000000 / 94689205503) ∧
    -Real.log (62500000000 / 94689205503) ≤ (415433451 / 1000000000) := by
  have h := checkLog_sound (w := (32189205503 / 157189205503)) (n := 12)
    (lo := (8308669 / 20000000)) (hi := (415433451 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((94689205503 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(94689205503 / 62500000000) = 1/(62500000000 / 94689205503) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (8308669 / 20000000) (415433451 / 1000000000) (Real.log (94689205503 / 62500000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (94689205503 / 62500000000) = -Real.log (62500000000 / 94689205503) := by
    rw [show ((94689205503 / 62500000000) : ℝ) = ((62500000000 / 94689205503) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (8567899 / 200000000) ≤ -Real.log (2395162879 / 2500000000) ∧
    -Real.log (2395162879 / 2500000000) ≤ (5354937 / 125000000) := by
  have h := checkLog_sound (w := (104837121 / 4895162879)) (n := 12)
    (lo := (8567899 / 200000000)) (hi := (5354937 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000000 / 2395162879) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000000 / 2395162879) = 1/(2395162879 / 2500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-5354937 / 125000000) (-8567899 / 200000000) (Real.log (2395162879 / 2500000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (42702389 / 1000000000) ≤ -Real.log (958196517319 / 1000000000000) ∧
    -Real.log (958196517319 / 1000000000000) ≤ (4270239 / 100000000) := by
  have h := checkLog_sound (w := (41803482681 / 1958196517319)) (n := 12)
    (lo := (42702389 / 1000000000)) (hi := (4270239 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 958196517319) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 958196517319) = 1/(958196517319 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-4270239 / 100000000) (-42702389 / 1000000000) (Real.log (958196517319 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell251
