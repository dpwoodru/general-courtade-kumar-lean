import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0034
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

theorem reflection_log_1_neg : (680563453 / 1000000000) ≤ -Real.log (102400 / 202239) ∧
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


theorem reflection_log_1 : Bounds (680563453 / 1000000000) (340281727 / 500000000) (Real.log (202239 / 102400)) := by
  have h := reflection_log_1_neg
  have he : Real.log (202239 / 102400) = -Real.log (102400 / 202239) := by
    rw [show ((202239 / 102400) : ℝ) = ((102400 / 202239) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (1844244451 / 500000000) ≤ -Real.log (2561 / 102400) ∧
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


theorem reflection_log_2 : Bounds (-922122227 / 250000000) (-1844244451 / 500000000) (Real.log (2561 / 102400)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (680469501 / 1000000000) ≤ -Real.log (5120 / 10111) ∧
    -Real.log (5120 / 10111) ≤ (340234751 / 500000000) := by
  have h := checkLog_sound (w := (4991 / 15231)) (n := 12)
    (lo := (680469501 / 1000000000)) (hi := (340234751 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10111 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10111 / 5120) = 1/(5120 / 10111) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (680469501 / 1000000000) (340234751 / 500000000) (Real.log (10111 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (10111 / 5120) = -Real.log (5120 / 10111) := by
    rw [show ((10111 / 5120) : ℝ) = ((5120 / 10111) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (368109731 / 100000000) ≤ -Real.log (129 / 5120) ∧
    -Real.log (129 / 5120) ≤ (920274329 / 250000000) := by
  have h := checkLog_sound (w := (31 / 289)) (n := 12)
    (lo := (21536141 / 100000000)) (hi := (215361411 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 129) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(160 / 129) = 1/(129 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-920274329 / 250000000) (-368109731 / 100000000) (Real.log (129 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (166954839 / 250000000) ≤ -Real.log (51200 / 99839) ∧
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


theorem reflection_log_5 : Bounds (166954839 / 250000000) (667819357 / 1000000000) (Real.log (99839 / 51200)) := by
  have h := reflection_log_5_neg
  have he : Real.log (99839 / 51200) = -Real.log (51200 / 99839) := by
    rw [show ((99839 / 51200) : ℝ) = ((51200 / 99839) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1497670861 / 500000000) ≤ -Real.log (2561 / 51200) ∧
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


theorem reflection_log_6 : Bounds (-2995341727 / 1000000000) (-1497670861 / 500000000) (Real.log (2561 / 51200)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (667629031 / 1000000000) ≤ -Real.log (2560 / 4991) ∧
    -Real.log (2560 / 4991) ≤ (83453629 / 125000000) := by
  have h := checkLog_sound (w := (2431 / 7551)) (n := 12)
    (lo := (667629031 / 1000000000)) (hi := (83453629 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4991 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4991 / 2560) = 1/(2560 / 4991) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (667629031 / 1000000000) (83453629 / 125000000) (Real.log (4991 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (4991 / 2560) = -Real.log (2560 / 4991) := by
    rw [show ((4991 / 2560) : ℝ) = ((2560 / 4991) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (298795013 / 100000000) ≤ -Real.log (129 / 2560) ∧
    -Real.log (129 / 2560) ≤ (597590027 / 200000000) := by
  have h := checkLog_sound (w := (31 / 289)) (n := 12)
    (lo := (21536141 / 100000000)) (hi := (215361411 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 129) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(160 / 129) = 1/(129 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-597590027 / 200000000) (-298795013 / 100000000) (Real.log (129 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (341237467 / 500000000) ≤ -Real.log (1000000 / 1978769) ∧
    -Real.log (1000000 / 1978769) ≤ (136494987 / 200000000) := by
  have h := checkLog_sound (w := (978769 / 2978769)) (n := 12)
    (lo := (341237467 / 500000000)) (hi := (136494987 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1978769 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1978769 / 1000000) = 1/(1000000 / 1978769) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (341237467 / 500000000) (136494987 / 200000000) (Real.log (1978769 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1978769 / 1000000) = -Real.log (1000000 / 1978769) := by
    rw [show ((1978769 / 1000000) : ℝ) = ((1000000 / 1978769) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (1926146449 / 500000000) ≤ -Real.log (21231 / 1000000) ∧
    -Real.log (21231 / 1000000) ≤ (481536613 / 125000000) := by
  have h := checkLog_sound (w := (10019 / 52481)) (n := 12)
    (lo := (193278499 / 500000000)) (hi := (386556999 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 21231) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 21231) = 1/(21231 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-481536613 / 125000000) (-1926146449 / 500000000) (Real.log (21231 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (42659421 / 62500000) ≤ -Real.log (1000000 / 1978919) ∧
    -Real.log (1000000 / 1978919) ≤ (682550737 / 1000000000) := by
  have h := checkLog_sound (w := (978919 / 2978919)) (n := 12)
    (lo := (42659421 / 62500000)) (hi := (682550737 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1978919 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1978919 / 1000000) = 1/(1000000 / 1978919) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (42659421 / 62500000) (682550737 / 1000000000) (Real.log (1978919 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1978919 / 1000000) = -Real.log (1000000 / 1978919) := by
    rw [show ((1978919 / 1000000) : ℝ) = ((1000000 / 1978919) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (771876623 / 200000000) ≤ -Real.log (21081 / 1000000) ∧
    -Real.log (21081 / 1000000) ≤ (3859383121 / 1000000000) := by
  have h := checkLog_sound (w := (10169 / 52331)) (n := 12)
    (lo := (78729443 / 200000000)) (hi := (24602951 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 21081) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 21081) = 1/(21081 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-3859383121 / 1000000000) (-771876623 / 200000000) (Real.log (21081 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (4265143 / 6250000) ≤ -Real.log (500000 / 989333) ∧
    -Real.log (500000 / 989333) ≤ (682422881 / 1000000000) := by
  have h := checkLog_sound (w := (489333 / 1489333)) (n := 12)
    (lo := (4265143 / 6250000)) (hi := (682422881 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((989333 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(989333 / 500000) = 1/(500000 / 989333) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (4265143 / 6250000) (682422881 / 1000000000) (Real.log (989333 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (989333 / 500000) = -Real.log (500000 / 989333) := by
    rw [show ((989333 / 500000) : ℝ) = ((500000 / 989333) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (3847453231 / 1000000000) ≤ -Real.log (10667 / 500000) ∧
    -Real.log (10667 / 500000) ≤ (3847453237 / 1000000000) := by
  have h := checkLog_sound (w := (2479 / 13146)) (n := 12)
    (lo := (381717331 / 1000000000)) (hi := (95429333 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 10667) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 10667) = 1/(10667 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-3847453237 / 1000000000) (-3847453231 / 1000000000) (Real.log (10667 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (42656231 / 62500000) ≤ -Real.log (500000 / 989409) ∧
    -Real.log (500000 / 989409) ≤ (682499697 / 1000000000) := by
  have h := checkLog_sound (w := (489409 / 1489409)) (n := 12)
    (lo := (42656231 / 62500000)) (hi := (682499697 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((989409 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(989409 / 500000) = 1/(500000 / 989409) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (42656231 / 62500000) (682499697 / 1000000000) (Real.log (989409 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (989409 / 500000) = -Real.log (500000 / 989409) := by
    rw [show ((989409 / 500000) : ℝ) = ((500000 / 989409) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (3854603511 / 1000000000) ≤ -Real.log (10591 / 500000) ∧
    -Real.log (10591 / 500000) ≤ (3854603517 / 1000000000) := by
  have h := checkLog_sound (w := (2517 / 13108)) (n := 12)
    (lo := (388867611 / 1000000000)) (hi := (97216903 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 10591) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 10591) = 1/(10591 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-3854603517 / 1000000000) (-3854603511 / 1000000000) (Real.log (10591 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (566845979 / 125000000) ≤ -Real.log (125000000000 / 11650234327163) ∧
    -Real.log (125000000000 / 11650234327163) ≤ (4534767839 / 1000000000) := by
  have h := checkLog_sound (w := (3650234327163 / 19650234327163)) (n := 12)
    (lo := (23492797 / 62500000)) (hi := (375884753 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11650234327163 / 8000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(11650234327163 / 8000000000000) = 1/(125000000000 / 11650234327163) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (566845979 / 125000000) (4534767839 / 1000000000) (Real.log (11650234327163 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (11650234327163 / 125000000000) = -Real.log (125000000000 / 11650234327163) := by
    rw [show ((11650234327163 / 125000000000) : ℝ) = ((125000000000 / 11650234327163) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (90838677 / 20000000) ≤ -Real.log (500000000000 / 46936079882359) ∧
    -Real.log (500000000000 / 46936079882359) ≤ (4541933857 / 1000000000) := by
  have h := checkLog_sound (w := (14936079882359 / 78936079882359)) (n := 12)
    (lo := (38305077 / 100000000)) (hi := (383050771 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((46936079882359 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(46936079882359 / 32000000000000) = 1/(500000000000 / 46936079882359) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (90838677 / 20000000) (4541933857 / 1000000000) (Real.log (46936079882359 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (46936079882359 / 500000000000) = -Real.log (500000000000 / 46936079882359) := by
    rw [show ((46936079882359 / 500000000000) : ℝ) = ((500000000000 / 46936079882359) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (4529876111 / 1000000000) ≤ -Real.log (62500000000 / 5796691900253) ∧
    -Real.log (62500000000 / 5796691900253) ≤ (2264938059 / 500000000) := by
  have h := checkLog_sound (w := (1796691900253 / 9796691900253)) (n := 12)
    (lo := (370993031 / 1000000000)) (hi := (46374129 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5796691900253 / 4000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(5796691900253 / 4000000000000) = 1/(62500000000 / 5796691900253) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (4529876111 / 1000000000) (2264938059 / 500000000) (Real.log (5796691900253 / 62500000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (5796691900253 / 62500000000) = -Real.log (62500000000 / 5796691900253) := by
    rw [show ((5796691900253 / 62500000000) : ℝ) = ((62500000000 / 5796691900253) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (4537103207 / 1000000000) ≤ -Real.log (500000000000 / 46709895194033) ∧
    -Real.log (500000000000 / 46709895194033) ≤ (2268551607 / 500000000) := by
  have h := checkLog_sound (w := (14709895194033 / 78709895194033)) (n := 12)
    (lo := (378220127 / 1000000000)) (hi := (11819379 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((46709895194033 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(46709895194033 / 32000000000000) = 1/(500000000000 / 46709895194033) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (4537103207 / 1000000000) (2268551607 / 500000000) (Real.log (46709895194033 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (46709895194033 / 500000000000) = -Real.log (500000000000 / 46709895194033) := by
    rw [show ((46709895194033 / 500000000000) : ℝ) = ((500000000000 / 46709895194033) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0034
