import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0035
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

theorem reflection_log_1_neg : (680469501 / 1000000000) ≤ -Real.log (5120 / 10111) ∧
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


theorem reflection_log_1 : Bounds (680469501 / 1000000000) (340234751 / 500000000) (Real.log (10111 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (10111 / 5120) = -Real.log (5120 / 10111) := by
    rw [show ((10111 / 5120) : ℝ) = ((5120 / 10111) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (368109731 / 100000000) ≤ -Real.log (129 / 5120) ∧
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


theorem reflection_log_2 : Bounds (-920274329 / 250000000) (-368109731 / 100000000) (Real.log (129 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (680375539 / 1000000000) ≤ -Real.log (102400 / 202201) ∧
    -Real.log (102400 / 202201) ≤ (34018777 / 50000000) := by
  have h := checkLog_sound (w := (99801 / 304601)) (n := 12)
    (lo := (680375539 / 1000000000)) (hi := (34018777 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((202201 / 102400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(202201 / 102400) = 1/(102400 / 202201) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (680375539 / 1000000000) (34018777 / 50000000) (Real.log (202201 / 102400)) := by
  have h := reflection_log_3_neg
  have he : Real.log (202201 / 102400) = -Real.log (102400 / 202201) := by
    rw [show ((202201 / 102400) : ℝ) = ((102400 / 202201) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (1836879977 / 500000000) ≤ -Real.log (2599 / 102400) ∧
    -Real.log (2599 / 102400) ≤ (91843999 / 25000000) := by
  have h := checkLog_sound (w := (601 / 5799)) (n := 12)
    (lo := (104012027 / 500000000)) (hi := (41604811 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2599) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3200 / 2599) = 1/(2599 / 102400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-91843999 / 25000000) (-1836879977 / 500000000) (Real.log (2599 / 102400)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (667629031 / 1000000000) ≤ -Real.log (2560 / 4991) ∧
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


theorem reflection_log_5 : Bounds (667629031 / 1000000000) (83453629 / 125000000) (Real.log (4991 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (4991 / 2560) = -Real.log (2560 / 4991) := by
    rw [show ((4991 / 2560) : ℝ) = ((2560 / 4991) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (298795013 / 100000000) ≤ -Real.log (129 / 2560) ∧
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


theorem reflection_log_6 : Bounds (-597590027 / 200000000) (-298795013 / 100000000) (Real.log (129 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (667438671 / 1000000000) ≤ -Real.log (51200 / 99801) ∧
    -Real.log (51200 / 99801) ≤ (41714917 / 62500000) := by
  have h := checkLog_sound (w := (48601 / 151001)) (n := 12)
    (lo := (667438671 / 1000000000)) (hi := (41714917 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((99801 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(99801 / 51200) = 1/(51200 / 99801) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (667438671 / 1000000000) (41714917 / 62500000) (Real.log (99801 / 51200)) := by
  have h := reflection_log_7_neg
  have he : Real.log (99801 / 51200) = -Real.log (51200 / 99801) := by
    rw [show ((99801 / 51200) : ℝ) = ((51200 / 99801) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (1490306387 / 500000000) ≤ -Real.log (2599 / 51200) ∧
    -Real.log (2599 / 51200) ≤ (2980612779 / 1000000000) := by
  have h := checkLog_sound (w := (601 / 5799)) (n := 12)
    (lo := (104012027 / 500000000)) (hi := (41604811 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2599) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3200 / 2599) = 1/(2599 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-2980612779 / 1000000000) (-1490306387 / 500000000) (Real.log (2599 / 51200)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (341199563 / 500000000) ≤ -Real.log (1000000 / 1978619) ∧
    -Real.log (1000000 / 1978619) ≤ (682399127 / 1000000000) := by
  have h := checkLog_sound (w := (978619 / 2978619)) (n := 12)
    (lo := (341199563 / 500000000)) (hi := (682399127 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1978619 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1978619 / 1000000) = 1/(1000000 / 1978619) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (341199563 / 500000000) (682399127 / 1000000000) (Real.log (1978619 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1978619 / 1000000) = -Real.log (1000000 / 1978619) := by
    rw [show ((1978619 / 1000000) : ℝ) = ((1000000 / 1978619) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (1922626299 / 500000000) ≤ -Real.log (21381 / 1000000) ∧
    -Real.log (21381 / 1000000) ≤ (961313151 / 250000000) := by
  have h := checkLog_sound (w := (9869 / 52631)) (n := 12)
    (lo := (189758349 / 500000000)) (hi := (379516699 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 21381) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 21381) = 1/(21381 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-961313151 / 250000000) (-1922626299 / 500000000) (Real.log (21381 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (682475439 / 1000000000) ≤ -Real.log (100000 / 197877) ∧
    -Real.log (100000 / 197877) ≤ (8530943 / 12500000) := by
  have h := checkLog_sound (w := (97877 / 297877)) (n := 12)
    (lo := (682475439 / 1000000000)) (hi := (8530943 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((197877 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(197877 / 100000) = 1/(100000 / 197877) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (682475439 / 1000000000) (8530943 / 12500000) (Real.log (197877 / 100000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (197877 / 100000) = -Real.log (100000 / 197877) := by
    rw [show ((197877 / 100000) : ℝ) = ((100000 / 197877) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (192617 / 50000) ≤ -Real.log (2123 / 100000) ∧
    -Real.log (2123 / 100000) ≤ (1926170003 / 500000000) := by
  have h := checkLog_sound (w := (501 / 2624)) (n := 12)
    (lo := (3866041 / 10000000)) (hi := (386604101 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3125 / 2123) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3125 / 2123) = 1/(2123 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1926170003 / 500000000) (-192617 / 50000) (Real.log (2123 / 100000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (682346563 / 1000000000) ≤ -Real.log (200000 / 395703) ∧
    -Real.log (200000 / 395703) ≤ (170586641 / 250000000) := by
  have h := checkLog_sound (w := (195703 / 595703)) (n := 12)
    (lo := (682346563 / 1000000000)) (hi := (170586641 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((395703 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(395703 / 200000) = 1/(200000 / 395703) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (682346563 / 1000000000) (170586641 / 250000000) (Real.log (395703 / 200000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (395703 / 200000) = -Real.log (200000 / 395703) := by
    rw [show ((395703 / 200000) : ℝ) = ((200000 / 395703) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (1920200129 / 500000000) ≤ -Real.log (4297 / 200000) ∧
    -Real.log (4297 / 200000) ≤ (480050033 / 125000000) := by
  have h := checkLog_sound (w := (1953 / 10547)) (n := 12)
    (lo := (187332179 / 500000000)) (hi := (374664359 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6250 / 4297) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(6250 / 4297) = 1/(4297 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-480050033 / 125000000) (-1920200129 / 500000000) (Real.log (4297 / 200000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (136484677 / 200000000) ≤ -Real.log (1000000 / 1978667) ∧
    -Real.log (1000000 / 1978667) ≤ (341211693 / 500000000) := by
  have h := checkLog_sound (w := (978667 / 2978667)) (n := 12)
    (lo := (136484677 / 200000000)) (hi := (341211693 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1978667 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1978667 / 1000000) = 1/(1000000 / 1978667) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (136484677 / 200000000) (341211693 / 500000000) (Real.log (1978667 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1978667 / 1000000) = -Real.log (1000000 / 1978667) := by
    rw [show ((1978667 / 1000000) : ℝ) = ((1000000 / 1978667) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (1923750053 / 500000000) ≤ -Real.log (21333 / 1000000) ∧
    -Real.log (21333 / 1000000) ≤ (240468757 / 62500000) := by
  have h := checkLog_sound (w := (9917 / 52583)) (n := 12)
    (lo := (190882103 / 500000000)) (hi := (381764207 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 21333) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 21333) = 1/(21333 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-240468757 / 62500000) (-1923750053 / 500000000) (Real.log (21333 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (181106069 / 40000000) ≤ -Real.log (31250000000 / 2891906073149) ∧
    -Real.log (31250000000 / 2891906073149) ≤ (1131912933 / 250000000) := by
  have h := checkLog_sound (w := (891906073149 / 4891906073149)) (n := 12)
    (lo := (73753729 / 200000000)) (hi := (184384323 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2891906073149 / 2000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(2891906073149 / 2000000000000) = 1/(31250000000 / 2891906073149) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (181106069 / 40000000) (1131912933 / 250000000) (Real.log (2891906073149 / 31250000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (2891906073149 / 31250000000) = -Real.log (31250000000 / 2891906073149) := by
    rw [show ((2891906073149 / 31250000000) : ℝ) = ((31250000000 / 2891906073149) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (4534815439 / 1000000000) ≤ -Real.log (500000000000 / 46603155911447) ∧
    -Real.log (500000000000 / 46603155911447) ≤ (2267407723 / 500000000) := by
  have h := checkLog_sound (w := (14603155911447 / 78603155911447)) (n := 12)
    (lo := (375932359 / 1000000000)) (hi := (9398309 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((46603155911447 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(46603155911447 / 32000000000000) = 1/(500000000000 / 46603155911447) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (4534815439 / 1000000000) (2267407723 / 500000000) (Real.log (46603155911447 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (46603155911447 / 500000000000) = -Real.log (500000000000 / 46603155911447) := by
    rw [show ((46603155911447 / 500000000000) : ℝ) = ((500000000000 / 46603155911447) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (4522746821 / 1000000000) ≤ -Real.log (500000000000 / 46044100535257) ∧
    -Real.log (500000000000 / 46044100535257) ≤ (1130686707 / 250000000) := by
  have h := checkLog_sound (w := (14044100535257 / 78044100535257)) (n := 12)
    (lo := (363863741 / 1000000000)) (hi := (181931871 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((46044100535257 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(46044100535257 / 32000000000000) = 1/(500000000000 / 46044100535257) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (4522746821 / 1000000000) (1130686707 / 250000000) (Real.log (46044100535257 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (46044100535257 / 500000000000) = -Real.log (500000000000 / 46044100535257) := by
    rw [show ((46044100535257 / 500000000000) : ℝ) = ((500000000000 / 46044100535257) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (4529923491 / 1000000000) ≤ -Real.log (12500000000 / 1159393310833) ∧
    -Real.log (12500000000 / 1159393310833) ≤ (2264961749 / 500000000) := by
  have h := checkLog_sound (w := (359393310833 / 1959393310833)) (n := 12)
    (lo := (371040411 / 1000000000)) (hi := (92760103 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1159393310833 / 800000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(1159393310833 / 800000000000) = 1/(12500000000 / 1159393310833) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (4529923491 / 1000000000) (2264961749 / 500000000) (Real.log (1159393310833 / 12500000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1159393310833 / 12500000000) = -Real.log (12500000000 / 1159393310833) := by
    rw [show ((1159393310833 / 12500000000) : ℝ) = ((12500000000 / 1159393310833) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0035
