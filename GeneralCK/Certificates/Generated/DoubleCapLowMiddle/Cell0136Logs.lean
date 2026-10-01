import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0136
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

theorem reflection_log_1_neg : (131993201 / 200000000) ≤ -Real.log (25600 / 49529) ∧
    -Real.log (25600 / 49529) ≤ (329983003 / 500000000) := by
  have h := checkLog_sound (w := (23929 / 75129)) (n := 12)
    (lo := (131993201 / 200000000)) (hi := (329983003 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49529 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49529 / 25600) = 1/(25600 / 49529) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (131993201 / 200000000) (329983003 / 500000000) (Real.log (49529 / 25600)) := by
  have h := reflection_log_1_neg
  have he : Real.log (49529 / 25600) = -Real.log (25600 / 49529) := by
    rw [show ((49529 / 25600) : ℝ) = ((25600 / 49529) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (27291701 / 10000000) ≤ -Real.log (1671 / 25600) ∧
    -Real.log (1671 / 25600) ≤ (341146263 / 125000000) := by
  have h := checkLog_sound (w := (1529 / 4871)) (n := 12)
    (lo := (8121607 / 12500000)) (hi := (649728561 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 1671) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(3200 / 1671) = 1/(1671 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-341146263 / 125000000) (-27291701 / 10000000) (Real.log (1671 / 25600)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (659582317 / 1000000000) ≤ -Real.log (2560 / 4951) ∧
    -Real.log (2560 / 4951) ≤ (329791159 / 500000000) := by
  have h := checkLog_sound (w := (2391 / 7511)) (n := 12)
    (lo := (659582317 / 1000000000)) (hi := (329791159 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4951 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4951 / 2560) = 1/(2560 / 4951) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (659582317 / 1000000000) (329791159 / 500000000) (Real.log (4951 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (4951 / 2560) = -Real.log (2560 / 4951) := by
    rw [show ((4951 / 2560) : ℝ) = ((2560 / 4951) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (135893191 / 50000000) ≤ -Real.log (169 / 2560) ∧
    -Real.log (169 / 2560) ≤ (169866489 / 62500000) := by
  have h := checkLog_sound (w := (151 / 489)) (n := 12)
    (lo := (15960557 / 25000000)) (hi := (638422281 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 169) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(320 / 169) = 1/(169 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-169866489 / 62500000) (-135893191 / 50000000) (Real.log (169 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (625645941 / 1000000000) ≤ -Real.log (12800 / 23929) ∧
    -Real.log (12800 / 23929) ≤ (312822971 / 500000000) := by
  have h := checkLog_sound (w := (11129 / 36729)) (n := 12)
    (lo := (625645941 / 1000000000)) (hi := (312822971 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((23929 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(23929 / 12800) = 1/(12800 / 23929) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (625645941 / 1000000000) (312822971 / 500000000) (Real.log (23929 / 12800)) := by
  have h := reflection_log_5_neg
  have he : Real.log (23929 / 12800) = -Real.log (12800 / 23929) := by
    rw [show ((23929 / 12800) : ℝ) = ((12800 / 23929) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (50900573 / 25000000) ≤ -Real.log (1671 / 12800) ∧
    -Real.log (1671 / 12800) ≤ (2036022923 / 1000000000) := by
  have h := checkLog_sound (w := (1529 / 4871)) (n := 12)
    (lo := (8121607 / 12500000)) (hi := (649728561 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 1671) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(3200 / 1671) = 1/(1671 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-2036022923 / 1000000000) (-50900573 / 25000000) (Real.log (1671 / 12800)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (62485161 / 100000000) ≤ -Real.log (1280 / 2391) ∧
    -Real.log (1280 / 2391) ≤ (624851611 / 1000000000) := by
  have h := checkLog_sound (w := (1111 / 3671)) (n := 12)
    (lo := (62485161 / 100000000)) (hi := (624851611 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2391 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2391 / 1280) = 1/(1280 / 2391) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (62485161 / 100000000) (624851611 / 1000000000) (Real.log (2391 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2391 / 1280) = -Real.log (1280 / 2391) := by
    rw [show ((2391 / 1280) : ℝ) = ((1280 / 2391) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (12654479 / 6250000) ≤ -Real.log (169 / 1280) ∧
    -Real.log (169 / 1280) ≤ (2024716643 / 1000000000) := by
  have h := checkLog_sound (w := (151 / 489)) (n := 12)
    (lo := (15960557 / 25000000)) (hi := (638422281 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 169) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(320 / 169) = 1/(169 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-2024716643 / 1000000000) (-12654479 / 6250000) (Real.log (169 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (666503879 / 1000000000) ≤ -Real.log (1000000 / 1947417) ∧
    -Real.log (1000000 / 1947417) ≤ (16662597 / 25000000) := by
  have h := checkLog_sound (w := (947417 / 2947417)) (n := 12)
    (lo := (666503879 / 1000000000)) (hi := (16662597 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1947417 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1947417 / 1000000) = 1/(1000000 / 1947417) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (666503879 / 1000000000) (16662597 / 25000000) (Real.log (1947417 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1947417 / 1000000) = -Real.log (1000000 / 1947417) := by
    rw [show ((1947417 / 1000000) : ℝ) = ((1000000 / 1947417) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (2945362403 / 1000000000) ≤ -Real.log (52583 / 1000000) ∧
    -Real.log (52583 / 1000000) ≤ (368170301 / 125000000) := by
  have h := checkLog_sound (w := (9917 / 115083)) (n := 12)
    (lo := (172773683 / 1000000000)) (hi := (43193421 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 52583) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 52583) = 1/(52583 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-368170301 / 125000000) (-2945362403 / 1000000000) (Real.log (52583 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (666784211 / 1000000000) ≤ -Real.log (1000000 / 1947963) ∧
    -Real.log (1000000 / 1947963) ≤ (166696053 / 250000000) := by
  have h := checkLog_sound (w := (947963 / 2947963)) (n := 12)
    (lo := (666784211 / 1000000000)) (hi := (166696053 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1947963 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1947963 / 1000000) = 1/(1000000 / 1947963) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (666784211 / 1000000000) (166696053 / 250000000) (Real.log (1947963 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1947963 / 1000000) = -Real.log (1000000 / 1947963) := by
    rw [show ((1947963 / 1000000) : ℝ) = ((1000000 / 1947963) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (184737517 / 62500000) ≤ -Real.log (52037 / 1000000) ∧
    -Real.log (52037 / 1000000) ≤ (2955800277 / 1000000000) := by
  have h := checkLog_sound (w := (10463 / 114537)) (n := 12)
    (lo := (5725361 / 31250000)) (hi := (183211553 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 52037) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 52037) = 1/(52037 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-2955800277 / 1000000000) (-184737517 / 62500000) (Real.log (52037 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (666038539 / 1000000000) ≤ -Real.log (1000000 / 1946511) ∧
    -Real.log (1000000 / 1946511) ≤ (33301927 / 50000000) := by
  have h := checkLog_sound (w := (946511 / 2946511)) (n := 12)
    (lo := (666038539 / 1000000000)) (hi := (33301927 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1946511 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1946511 / 1000000) = 1/(1000000 / 1946511) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (666038539 / 1000000000) (33301927 / 50000000) (Real.log (1946511 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1946511 / 1000000) = -Real.log (1000000 / 1946511) := by
    rw [show ((1946511 / 1000000) : ℝ) = ((1000000 / 1946511) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (2928279251 / 1000000000) ≤ -Real.log (53489 / 1000000) ∧
    -Real.log (53489 / 1000000) ≤ (366034907 / 125000000) := by
  have h := checkLog_sound (w := (9011 / 115989)) (n := 12)
    (lo := (155690531 / 1000000000)) (hi := (38922633 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 53489) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 53489) = 1/(53489 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-366034907 / 125000000) (-2928279251 / 1000000000) (Real.log (53489 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (333165407 / 500000000) ≤ -Real.log (25000 / 48677) ∧
    -Real.log (25000 / 48677) ≤ (133266163 / 200000000) := by
  have h := checkLog_sound (w := (23677 / 73677)) (n := 12)
    (lo := (333165407 / 500000000)) (hi := (133266163 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((48677 / 25000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(48677 / 25000) = 1/(25000 / 48677) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (333165407 / 500000000) (133266163 / 200000000) (Real.log (48677 / 25000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (48677 / 25000) = -Real.log (25000 / 48677) := by
    rw [show ((48677 / 25000) : ℝ) = ((25000 / 48677) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (2938973937 / 1000000000) ≤ -Real.log (1323 / 25000) ∧
    -Real.log (1323 / 25000) ≤ (1469486971 / 500000000) := by
  have h := checkLog_sound (w := (479 / 5771)) (n := 12)
    (lo := (166385217 / 1000000000)) (hi := (83192609 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3125 / 2646) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3125 / 2646) = 1/(1323 / 25000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-1469486971 / 500000000) (-2938973937 / 1000000000) (Real.log (1323 / 25000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (3611866281 / 1000000000) ≤ -Real.log (100000000000 / 3703510640321) ∧
    -Real.log (100000000000 / 3703510640321) ≤ (3611866287 / 1000000000) := by
  have h := checkLog_sound (w := (503510640321 / 6903510640321)) (n := 12)
    (lo := (146130381 / 1000000000)) (hi := (73065191 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3703510640321 / 3200000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3703510640321 / 3200000000000) = 1/(100000000000 / 3703510640321) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (3611866281 / 1000000000) (3611866287 / 1000000000) (Real.log (3703510640321 / 100000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (3703510640321 / 100000000000) = -Real.log (100000000000 / 3703510640321) := by
    rw [show ((3703510640321 / 100000000000) : ℝ) = ((100000000000 / 3703510640321) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (3622584483 / 1000000000) ≤ -Real.log (250000000000 / 9358547764091) ∧
    -Real.log (250000000000 / 9358547764091) ≤ (3622584489 / 1000000000) := by
  have h := checkLog_sound (w := (1358547764091 / 17358547764091)) (n := 12)
    (lo := (156848583 / 1000000000)) (hi := (19606073 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9358547764091 / 8000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(9358547764091 / 8000000000000) = 1/(250000000000 / 9358547764091) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (3622584483 / 1000000000) (3622584489 / 1000000000) (Real.log (9358547764091 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (9358547764091 / 250000000000) = -Real.log (250000000000 / 9358547764091) := by
    rw [show ((9358547764091 / 250000000000) : ℝ) = ((250000000000 / 9358547764091) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (359431779 / 100000000) ≤ -Real.log (500000000000 / 18195432705789) ∧
    -Real.log (500000000000 / 18195432705789) ≤ (898579449 / 250000000) := by
  have h := checkLog_sound (w := (2195432705789 / 34195432705789)) (n := 12)
    (lo := (12858189 / 100000000)) (hi := (128581891 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((18195432705789 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(18195432705789 / 16000000000000) = 1/(500000000000 / 18195432705789) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (359431779 / 100000000) (898579449 / 250000000) (Real.log (18195432705789 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (18195432705789 / 500000000000) = -Real.log (500000000000 / 18195432705789) := by
    rw [show ((18195432705789 / 500000000000) : ℝ) = ((500000000000 / 18195432705789) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (3605304751 / 1000000000) ≤ -Real.log (500000000000 / 18396447467877) ∧
    -Real.log (500000000000 / 18396447467877) ≤ (3605304757 / 1000000000) := by
  have h := checkLog_sound (w := (2396447467877 / 34396447467877)) (n := 12)
    (lo := (139568851 / 1000000000)) (hi := (34892213 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((18396447467877 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(18396447467877 / 16000000000000) = 1/(500000000000 / 18396447467877) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (3605304751 / 1000000000) (3605304757 / 1000000000) (Real.log (18396447467877 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (18396447467877 / 500000000000) = -Real.log (500000000000 / 18396447467877) := by
    rw [show ((18396447467877 / 500000000000) : ℝ) = ((500000000000 / 18396447467877) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0136
