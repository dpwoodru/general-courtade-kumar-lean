import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell137
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

theorem reflection_log_1_neg : (3572811 / 12500000) ≤ -Real.log (2560 / 3407) ∧
    -Real.log (2560 / 3407) ≤ (285824881 / 1000000000) := by
  have h := checkLog_sound (w := (847 / 5967)) (n := 12)
    (lo := (3572811 / 12500000)) (hi := (285824881 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3407 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3407 / 2560) = 1/(2560 / 3407) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (3572811 / 12500000) (285824881 / 1000000000) (Real.log (3407 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3407 / 2560) = -Real.log (2560 / 3407) := by
    rw [show ((3407 / 2560) : ℝ) = ((2560 / 3407) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (401761039 / 1000000000) ≤ -Real.log (1713 / 2560) ∧
    -Real.log (1713 / 2560) ≤ (5022013 / 12500000) := by
  have h := checkLog_sound (w := (847 / 4273)) (n := 12)
    (lo := (401761039 / 1000000000)) (hi := (5022013 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1713) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1713) = 1/(1713 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-5022013 / 12500000) (-401761039 / 1000000000) (Real.log (1713 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (285384513 / 1000000000) ≤ -Real.log (5120 / 6811) ∧
    -Real.log (5120 / 6811) ≤ (142692257 / 500000000) := by
  have h := checkLog_sound (w := (1691 / 11931)) (n := 12)
    (lo := (285384513 / 1000000000)) (hi := (142692257 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6811 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6811 / 5120) = 1/(5120 / 6811) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (285384513 / 1000000000) (142692257 / 500000000) (Real.log (6811 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6811 / 5120) = -Real.log (5120 / 6811) := by
    rw [show ((6811 / 5120) : ℝ) = ((5120 / 6811) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (80177153 / 200000000) ≤ -Real.log (3429 / 5120) ∧
    -Real.log (3429 / 5120) ≤ (200442883 / 500000000) := by
  have h := checkLog_sound (w := (1691 / 8549)) (n := 12)
    (lo := (80177153 / 200000000)) (hi := (200442883 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3429) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3429) = 1/(3429 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-200442883 / 500000000) (-80177153 / 200000000) (Real.log (3429 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (210787529 / 1000000000) ≤ -Real.log (20000 / 24693) ∧
    -Real.log (20000 / 24693) ≤ (21078753 / 100000000) := by
  have h := checkLog_sound (w := (4693 / 44693)) (n := 12)
    (lo := (210787529 / 1000000000)) (hi := (21078753 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24693 / 20000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24693 / 20000) = 1/(20000 / 24693) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (210787529 / 1000000000) (21078753 / 100000000) (Real.log (24693 / 20000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (24693 / 20000) = -Real.log (20000 / 24693) := by
    rw [show ((24693 / 20000) : ℝ) = ((20000 / 24693) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (267422033 / 1000000000) ≤ -Real.log (15307 / 20000) ∧
    -Real.log (15307 / 20000) ≤ (133711017 / 500000000) := by
  have h := checkLog_sound (w := (4693 / 35307)) (n := 12)
    (lo := (267422033 / 1000000000)) (hi := (133711017 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20000 / 15307) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20000 / 15307) = 1/(15307 / 20000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-133711017 / 500000000) (-267422033 / 1000000000) (Real.log (15307 / 20000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (211129267 / 1000000000) ≤ -Real.log (15625 / 19298) ∧
    -Real.log (15625 / 19298) ≤ (52782317 / 250000000) := by
  have h := checkLog_sound (w := (3673 / 34923)) (n := 12)
    (lo := (211129267 / 1000000000)) (hi := (52782317 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((19298 / 15625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(19298 / 15625) = 1/(15625 / 19298) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (211129267 / 1000000000) (52782317 / 250000000) (Real.log (19298 / 15625)) := by
  have h := reflection_log_7_neg
  have he : Real.log (19298 / 15625) = -Real.log (15625 / 19298) := by
    rw [show ((19298 / 15625) : ℝ) = ((15625 / 19298) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (267973567 / 1000000000) ≤ -Real.log (11952 / 15625) ∧
    -Real.log (11952 / 15625) ≤ (4187087 / 15625000) := by
  have h := checkLog_sound (w := (3673 / 27577)) (n := 12)
    (lo := (267973567 / 1000000000)) (hi := (4187087 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 11952) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625 / 11952) = 1/(11952 / 15625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-4187087 / 15625000) (-267973567 / 1000000000) (Real.log (11952 / 15625)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (38928721 / 250000000) ≤ -Real.log (1000000 / 1168493) ∧
    -Real.log (1000000 / 1168493) ≤ (31142977 / 200000000) := by
  have h := checkLog_sound (w := (168493 / 2168493)) (n := 12)
    (lo := (38928721 / 250000000)) (hi := (31142977 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1168493 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1168493 / 1000000) = 1/(1000000 / 1168493) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (38928721 / 250000000) (31142977 / 200000000) (Real.log (1168493 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1168493 / 1000000) = -Real.log (1000000 / 1168493) := by
    rw [show ((1168493 / 1000000) : ℝ) = ((1000000 / 1168493) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (184515561 / 1000000000) ≤ -Real.log (831507 / 1000000) ∧
    -Real.log (831507 / 1000000) ≤ (92257781 / 500000000) := by
  have h := checkLog_sound (w := (168493 / 1831507)) (n := 12)
    (lo := (184515561 / 1000000000)) (hi := (92257781 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 831507) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 831507) = 1/(831507 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-92257781 / 500000000) (-184515561 / 1000000000) (Real.log (831507 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (77991357 / 500000000) ≤ -Real.log (500000 / 584403) ∧
    -Real.log (500000 / 584403) ≤ (31196543 / 200000000) := by
  have h := checkLog_sound (w := (84403 / 1084403)) (n := 12)
    (lo := (77991357 / 500000000)) (hi := (31196543 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((584403 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(584403 / 500000) = 1/(500000 / 584403) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (77991357 / 500000000) (31196543 / 200000000) (Real.log (584403 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (584403 / 500000) = -Real.log (500000 / 584403) := by
    rw [show ((584403 / 500000) : ℝ) = ((500000 / 584403) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (184892057 / 1000000000) ≤ -Real.log (415597 / 500000) ∧
    -Real.log (415597 / 500000) ≤ (92446029 / 500000000) := by
  have h := checkLog_sound (w := (84403 / 915597)) (n := 12)
    (lo := (184892057 / 1000000000)) (hi := (92446029 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 415597) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 415597) = 1/(415597 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-92446029 / 500000000) (-184892057 / 1000000000) (Real.log (415597 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (343135139 / 500000000) ≤ -Real.log (500000000000 / 993146689997) ∧
    -Real.log (500000000000 / 993146689997) ≤ (686270279 / 1000000000) := by
  have h := checkLog_sound (w := (493146689997 / 1493146689997)) (n := 12)
    (lo := (343135139 / 500000000)) (hi := (686270279 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((993146689997 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(993146689997 / 500000000000) = 1/(500000000000 / 993146689997) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (343135139 / 500000000) (686270279 / 1000000000) (Real.log (993146689997 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (993146689997 / 500000000000) = -Real.log (500000000000 / 993146689997) := by
    rw [show ((993146689997 / 500000000000) : ℝ) = ((500000000000 / 993146689997) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (687585919 / 1000000000) ≤ -Real.log (125000000000 / 248613543491) ∧
    -Real.log (125000000000 / 248613543491) ≤ (1074353 / 1562500) := by
  have h := checkLog_sound (w := (123613543491 / 373613543491)) (n := 12)
    (lo := (687585919 / 1000000000)) (hi := (1074353 / 1562500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((248613543491 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(248613543491 / 125000000000) = 1/(125000000000 / 248613543491) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (687585919 / 1000000000) (1074353 / 1562500) (Real.log (248613543491 / 125000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (248613543491 / 125000000000) = -Real.log (125000000000 / 248613543491) := by
    rw [show ((248613543491 / 125000000000) : ℝ) = ((125000000000 / 248613543491) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (239104781 / 500000000) ≤ -Real.log (250000000000 / 403295877703) ∧
    -Real.log (250000000000 / 403295877703) ≤ (478209563 / 1000000000) := by
  have h := checkLog_sound (w := (153295877703 / 653295877703)) (n := 12)
    (lo := (239104781 / 500000000)) (hi := (478209563 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((403295877703 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(403295877703 / 250000000000) = 1/(250000000000 / 403295877703) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (239104781 / 500000000) (478209563 / 1000000000) (Real.log (403295877703 / 250000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (403295877703 / 250000000000) = -Real.log (250000000000 / 403295877703) := by
    rw [show ((403295877703 / 250000000000) : ℝ) = ((250000000000 / 403295877703) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (95820567 / 200000000) ≤ -Real.log (500000000000 / 807312583669) ∧
    -Real.log (500000000000 / 807312583669) ≤ (119775709 / 250000000) := by
  have h := checkLog_sound (w := (307312583669 / 1307312583669)) (n := 12)
    (lo := (95820567 / 200000000)) (hi := (119775709 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((807312583669 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(807312583669 / 500000000000) = 1/(500000000000 / 807312583669) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (95820567 / 200000000) (119775709 / 250000000) (Real.log (807312583669 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (807312583669 / 500000000000) = -Real.log (500000000000 / 807312583669) := by
    rw [show ((807312583669 / 500000000000) : ℝ) = ((500000000000 / 807312583669) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (170115223 / 500000000) ≤ -Real.log (62500000000 / 87829462049) ∧
    -Real.log (62500000000 / 87829462049) ≤ (340230447 / 1000000000) := by
  have h := checkLog_sound (w := (25329462049 / 150329462049)) (n := 12)
    (lo := (170115223 / 500000000)) (hi := (340230447 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((87829462049 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(87829462049 / 62500000000) = 1/(62500000000 / 87829462049) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (170115223 / 500000000) (340230447 / 1000000000) (Real.log (87829462049 / 62500000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (87829462049 / 62500000000) = -Real.log (62500000000 / 87829462049) := by
    rw [show ((87829462049 / 62500000000) : ℝ) = ((62500000000 / 87829462049) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (85218693 / 250000000) ≤ -Real.log (20000000000 / 28123542759) ∧
    -Real.log (20000000000 / 28123542759) ≤ (340874773 / 1000000000) := by
  have h := checkLog_sound (w := (8123542759 / 48123542759)) (n := 12)
    (lo := (85218693 / 250000000)) (hi := (340874773 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((28123542759 / 20000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(28123542759 / 20000000000) = 1/(20000000000 / 28123542759) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (85218693 / 250000000) (340874773 / 1000000000) (Real.log (28123542759 / 20000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (28123542759 / 20000000000) = -Real.log (20000000000 / 28123542759) := by
    rw [show ((28123542759 / 20000000000) : ℝ) = ((20000000000 / 28123542759) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (14454671 / 500000000) ≤ -Real.log (242876133591 / 250000000000) ∧
    -Real.log (242876133591 / 250000000000) ≤ (28909343 / 1000000000) := by
  have h := checkLog_sound (w := (7123866409 / 492876133591)) (n := 12)
    (lo := (14454671 / 500000000)) (hi := (28909343 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 242876133591) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 242876133591) = 1/(242876133591 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-28909343 / 1000000000) (-14454671 / 500000000) (Real.log (242876133591 / 250000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (28800677 / 1000000000) ≤ -Real.log (971610108951 / 1000000000000) ∧
    -Real.log (971610108951 / 1000000000000) ≤ (14400339 / 500000000) := by
  have h := checkLog_sound (w := (28389891049 / 1971610108951)) (n := 12)
    (lo := (28800677 / 1000000000)) (hi := (14400339 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 971610108951) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 971610108951) = 1/(971610108951 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-14400339 / 500000000) (-28800677 / 1000000000) (Real.log (971610108951 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell137
