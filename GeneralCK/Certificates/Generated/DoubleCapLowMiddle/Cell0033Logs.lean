import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0033
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

theorem reflection_log_1_neg : (680657397 / 1000000000) ≤ -Real.log (51200 / 101129) ∧
    -Real.log (51200 / 101129) ≤ (340328699 / 500000000) := by
  have h := checkLog_sound (w := (49929 / 152329)) (n := 12)
    (lo := (680657397 / 1000000000)) (hi := (340328699 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((101129 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(101129 / 51200) = 1/(51200 / 101129) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (680657397 / 1000000000) (340328699 / 500000000) (Real.log (101129 / 51200)) := by
  have h := reflection_log_1_neg
  have he : Real.log (101129 / 51200) = -Real.log (51200 / 101129) := by
    rw [show ((101129 / 51200) : ℝ) = ((51200 / 101129) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (3695935537 / 1000000000) ≤ -Real.log (1271 / 51200) ∧
    -Real.log (1271 / 51200) ≤ (3695935543 / 1000000000) := by
  have h := checkLog_sound (w := (329 / 2871)) (n := 12)
    (lo := (230199637 / 1000000000)) (hi := (115099819 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1271) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(1600 / 1271) = 1/(1271 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-3695935543 / 1000000000) (-3695935537 / 1000000000) (Real.log (1271 / 51200)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (680563453 / 1000000000) ≤ -Real.log (102400 / 202239) ∧
    -Real.log (102400 / 202239) ≤ (340281727 / 500000000) := by
  have h := checkLog_sound (w := (99839 / 304639)) (n := 12)
    (lo := (680563453 / 1000000000)) (hi := (340281727 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((202239 / 102400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(202239 / 102400) = 1/(102400 / 202239) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (680563453 / 1000000000) (340281727 / 500000000) (Real.log (202239 / 102400)) := by
  have h := reflection_log_3_neg
  have he : Real.log (202239 / 102400) = -Real.log (102400 / 202239) := by
    rw [show ((202239 / 102400) : ℝ) = ((102400 / 202239) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (1844244451 / 500000000) ≤ -Real.log (2561 / 102400) ∧
    -Real.log (2561 / 102400) ≤ (922122227 / 250000000) := by
  have h := checkLog_sound (w := (639 / 5761)) (n := 12)
    (lo := (111376501 / 500000000)) (hi := (222753003 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2561) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3200 / 2561) = 1/(2561 / 102400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-922122227 / 250000000) (-1844244451 / 500000000) (Real.log (2561 / 102400)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (167002411 / 250000000) ≤ -Real.log (25600 / 49929) ∧
    -Real.log (25600 / 49929) ≤ (133601929 / 200000000) := by
  have h := checkLog_sound (w := (24329 / 75529)) (n := 12)
    (lo := (167002411 / 250000000)) (hi := (133601929 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49929 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49929 / 25600) = 1/(25600 / 49929) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (167002411 / 250000000) (133601929 / 200000000) (Real.log (49929 / 25600)) := by
  have h := reflection_log_5_neg
  have he : Real.log (49929 / 25600) = -Real.log (25600 / 49929) := by
    rw [show ((49929 / 25600) : ℝ) = ((25600 / 49929) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (3002788357 / 1000000000) ≤ -Real.log (1271 / 25600) ∧
    -Real.log (1271 / 25600) ≤ (1501394181 / 500000000) := by
  have h := checkLog_sound (w := (329 / 2871)) (n := 12)
    (lo := (230199637 / 1000000000)) (hi := (115099819 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1271) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1600 / 1271) = 1/(1271 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1501394181 / 500000000) (-3002788357 / 1000000000) (Real.log (1271 / 25600)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (166954839 / 250000000) ≤ -Real.log (51200 / 99839) ∧
    -Real.log (51200 / 99839) ≤ (667819357 / 1000000000) := by
  have h := checkLog_sound (w := (48639 / 151039)) (n := 12)
    (lo := (166954839 / 250000000)) (hi := (667819357 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((99839 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(99839 / 51200) = 1/(51200 / 99839) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (166954839 / 250000000) (667819357 / 1000000000) (Real.log (99839 / 51200)) := by
  have h := reflection_log_7_neg
  have he : Real.log (99839 / 51200) = -Real.log (51200 / 99839) := by
    rw [show ((99839 / 51200) : ℝ) = ((51200 / 99839) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (1497670861 / 500000000) ≤ -Real.log (2561 / 51200) ∧
    -Real.log (2561 / 51200) ≤ (2995341727 / 1000000000) := by
  have h := checkLog_sound (w := (639 / 5761)) (n := 12)
    (lo := (111376501 / 500000000)) (hi := (222753003 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2561) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3200 / 2561) = 1/(2561 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-2995341727 / 1000000000) (-1497670861 / 500000000) (Real.log (2561 / 51200)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (68255023 / 100000000) ≤ -Real.log (500000 / 989459) ∧
    -Real.log (500000 / 989459) ≤ (682550231 / 1000000000) := by
  have h := checkLog_sound (w := (489459 / 1489459)) (n := 12)
    (lo := (68255023 / 100000000)) (hi := (682550231 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((989459 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(989459 / 500000) = 1/(500000 / 989459) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (68255023 / 100000000) (682550231 / 1000000000) (Real.log (989459 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (989459 / 500000) = -Real.log (500000 / 989459) := by
    rw [show ((989459 / 500000) : ℝ) = ((500000 / 989459) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (1507553 / 390625) ≤ -Real.log (10541 / 500000) ∧
    -Real.log (10541 / 500000) ≤ (1929667843 / 500000000) := by
  have h := checkLog_sound (w := (2542 / 13083)) (n := 12)
    (lo := (19679989 / 50000000)) (hi := (393599781 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 10541) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 10541) = 1/(10541 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-1929667843 / 500000000) (-1507553 / 390625) (Real.log (10541 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (170656633 / 250000000) ≤ -Real.log (1000000 / 1979069) ∧
    -Real.log (1000000 / 1979069) ≤ (682626533 / 1000000000) := by
  have h := checkLog_sound (w := (979069 / 2979069)) (n := 12)
    (lo := (170656633 / 250000000)) (hi := (682626533 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1979069 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1979069 / 1000000) = 1/(1000000 / 1979069) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (170656633 / 250000000) (682626533 / 1000000000) (Real.log (1979069 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1979069 / 1000000) = -Real.log (1000000 / 1979069) := by
    rw [show ((1979069 / 1000000) : ℝ) = ((1000000 / 1979069) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1933261981 / 500000000) ≤ -Real.log (20931 / 1000000) ∧
    -Real.log (20931 / 1000000) ≤ (60414437 / 15625000) := by
  have h := checkLog_sound (w := (10319 / 52181)) (n := 12)
    (lo := (200394031 / 500000000)) (hi := (400788063 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 20931) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 20931) = 1/(20931 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-60414437 / 15625000) (-1933261981 / 500000000) (Real.log (20931 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (682499191 / 1000000000) ≤ -Real.log (1000000 / 1978817) ∧
    -Real.log (1000000 / 1978817) ≤ (85312399 / 125000000) := by
  have h := checkLog_sound (w := (978817 / 2978817)) (n := 12)
    (lo := (682499191 / 1000000000)) (hi := (85312399 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1978817 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1978817 / 1000000) = 1/(1000000 / 1978817) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (682499191 / 1000000000) (85312399 / 125000000) (Real.log (1978817 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1978817 / 1000000) = -Real.log (1000000 / 1978817) := by
    rw [show ((1978817 / 1000000) : ℝ) = ((1000000 / 1978817) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (1927278151 / 500000000) ≤ -Real.log (21183 / 1000000) ∧
    -Real.log (21183 / 1000000) ≤ (963639077 / 250000000) := by
  have h := checkLog_sound (w := (10067 / 52433)) (n := 12)
    (lo := (194410201 / 500000000)) (hi := (388820403 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 21183) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 21183) = 1/(21183 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-963639077 / 250000000) (-1927278151 / 500000000) (Real.log (21183 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (341288001 / 500000000) ≤ -Real.log (1000000 / 1978969) ∧
    -Real.log (1000000 / 1978969) ≤ (682576003 / 1000000000) := by
  have h := checkLog_sound (w := (978969 / 2978969)) (n := 12)
    (lo := (341288001 / 500000000)) (hi := (682576003 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1978969 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1978969 / 1000000) = 1/(1000000 / 1978969) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (341288001 / 500000000) (682576003 / 1000000000) (Real.log (1978969 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1978969 / 1000000) = -Real.log (1000000 / 1978969) := by
    rw [show ((1978969 / 1000000) : ℝ) = ((1000000 / 1978969) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (482719717 / 125000000) ≤ -Real.log (21031 / 1000000) ∧
    -Real.log (21031 / 1000000) ≤ (1930878871 / 500000000) := by
  have h := checkLog_sound (w := (10219 / 52281)) (n := 12)
    (lo := (99005459 / 250000000)) (hi := (396021837 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 21031) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 21031) = 1/(21031 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-1930878871 / 500000000) (-482719717 / 125000000) (Real.log (21031 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (454188591 / 100000000) ≤ -Real.log (250000000000 / 23466914903709) ∧
    -Real.log (250000000000 / 23466914903709) ≤ (4541885917 / 1000000000) := by
  have h := checkLog_sound (w := (7466914903709 / 39466914903709)) (n := 12)
    (lo := (38300283 / 100000000)) (hi := (383002831 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((23466914903709 / 16000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(23466914903709 / 16000000000000) = 1/(250000000000 / 23466914903709) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (454188591 / 100000000) (4541885917 / 1000000000) (Real.log (23466914903709 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (23466914903709 / 250000000000) = -Real.log (250000000000 / 23466914903709) := by
    rw [show ((23466914903709 / 250000000000) : ℝ) = ((250000000000 / 23466914903709) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (2274575247 / 500000000) ≤ -Real.log (500000000000 / 47276025990159) ∧
    -Real.log (500000000000 / 47276025990159) ≤ (4549150501 / 1000000000) := by
  have h := checkLog_sound (w := (15276025990159 / 79276025990159)) (n := 12)
    (lo := (195133707 / 500000000)) (hi := (78053483 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((47276025990159 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(47276025990159 / 32000000000000) = 1/(500000000000 / 47276025990159) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (2274575247 / 500000000) (4549150501 / 1000000000) (Real.log (47276025990159 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (47276025990159 / 500000000000) = -Real.log (500000000000 / 47276025990159) := by
    rw [show ((47276025990159 / 500000000000) : ℝ) = ((500000000000 / 47276025990159) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (4537055493 / 1000000000) ≤ -Real.log (500000000000 / 46707666525043) ∧
    -Real.log (500000000000 / 46707666525043) ≤ (9074111 / 2000000) := by
  have h := checkLog_sound (w := (14707666525043 / 78707666525043)) (n := 12)
    (lo := (378172413 / 1000000000)) (hi := (189086207 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((46707666525043 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(46707666525043 / 32000000000000) = 1/(500000000000 / 46707666525043) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (4537055493 / 1000000000) (9074111 / 2000000) (Real.log (46707666525043 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (46707666525043 / 500000000000) = -Real.log (500000000000 / 46707666525043) := by
    rw [show ((46707666525043 / 500000000000) : ℝ) = ((500000000000 / 46707666525043) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (4544333737 / 1000000000) ≤ -Real.log (500000000000 / 47048856450003) ∧
    -Real.log (500000000000 / 47048856450003) ≤ (284020859 / 62500000) := by
  have h := checkLog_sound (w := (15048856450003 / 79048856450003)) (n := 12)
    (lo := (385450657 / 1000000000)) (hi := (192725329 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((47048856450003 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(47048856450003 / 32000000000000) = 1/(500000000000 / 47048856450003) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (4544333737 / 1000000000) (284020859 / 62500000) (Real.log (47048856450003 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (47048856450003 / 500000000000) = -Real.log (500000000000 / 47048856450003) := by
    rw [show ((47048856450003 / 500000000000) : ℝ) = ((500000000000 / 47048856450003) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0033
