import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_3264_neg : (34723 / 200000000) ≤ -Real.log (1249783 / 1250000) ∧
    -Real.log (1249783 / 1250000) ≤ (10851 / 62500000) := by
  have h := checkLog_sound (w := (217 / 2499783)) (n := 12)
    (lo := (34723 / 200000000)) (hi := (10851 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250000 / 1249783) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1250000 / 1249783) = 1/(1249783 / 1250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3264 : Bounds (-10851 / 62500000) (-34723 / 200000000) (Real.log (1249783 / 1250000)) := by
  have h := reflection_log_3264_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3265_neg : (16709711 / 200000000) ≤ -Real.log (500000 / 543569) ∧
    -Real.log (500000 / 543569) ≤ (20887139 / 250000000) := by
  have h := checkLog_sound (w := (43569 / 1043569)) (n := 12)
    (lo := (16709711 / 200000000)) (hi := (20887139 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((543569 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(543569 / 500000) = 1/(500000 / 543569) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3265 : Bounds (16709711 / 200000000) (20887139 / 250000000) (Real.log (543569 / 500000)) := by
  have h := reflection_log_3265_neg
  have he : Real.log (543569 / 500000) = -Real.log (500000 / 543569) := by
    rw [show ((543569 / 500000) : ℝ) = ((500000 / 543569) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3266_neg : (91170559 / 1000000000) ≤ -Real.log (456431 / 500000) ∧
    -Real.log (456431 / 500000) ≤ (71227 / 781250) := by
  have h := checkLog_sound (w := (43569 / 956431)) (n := 12)
    (lo := (91170559 / 1000000000)) (hi := (71227 / 781250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 456431) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 456431) = 1/(456431 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3266 : Bounds (-71227 / 781250) (-91170559 / 1000000000) (Real.log (456431 / 500000)) := by
  have h := reflection_log_3266_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3267_neg : (83755499 / 1000000000) ≤ -Real.log (1000000 / 1087363) ∧
    -Real.log (1000000 / 1087363) ≤ (167511 / 2000000) := by
  have h := checkLog_sound (w := (87363 / 2087363)) (n := 12)
    (lo := (83755499 / 1000000000)) (hi := (167511 / 2000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1087363 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1087363 / 1000000) = 1/(1000000 / 1087363) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3267 : Bounds (83755499 / 1000000000) (167511 / 2000000) (Real.log (1087363 / 1000000)) := by
  have h := reflection_log_3267_neg
  have he : Real.log (1087363 / 1000000) = -Real.log (1000000 / 1087363) := by
    rw [show ((1087363 / 1000000) : ℝ) = ((1000000 / 1087363) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3268_neg : (91417067 / 1000000000) ≤ -Real.log (912637 / 1000000) ∧
    -Real.log (912637 / 1000000) ≤ (22854267 / 250000000) := by
  have h := checkLog_sound (w := (87363 / 1912637)) (n := 12)
    (lo := (91417067 / 1000000000)) (hi := (22854267 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 912637) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 912637) = 1/(912637 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3268 : Bounds (-22854267 / 250000000) (-91417067 / 1000000000) (Real.log (912637 / 1000000)) := by
  have h := reflection_log_3268_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3269_neg : (14964 / 1953125) ≤ -Real.log (992367706231 / 1000000000000) ∧
    -Real.log (992367706231 / 1000000000000) ≤ (7661569 / 1000000000) := by
  have h := checkLog_sound (w := (7632293769 / 1992367706231)) (n := 12)
    (lo := (14964 / 1953125)) (hi := (7661569 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 992367706231) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 992367706231) = 1/(992367706231 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3269 : Bounds (-7661569 / 1000000000) (-14964 / 1953125) (Real.log (992367706231 / 1000000000000)) := by
  have h := reflection_log_3269_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3270_neg : (1905501 / 250000000) ≤ -Real.log (248101742239 / 250000000000) ∧
    -Real.log (248101742239 / 250000000000) ≤ (1524401 / 200000000) := by
  have h := checkLog_sound (w := (1898257761 / 498101742239)) (n := 12)
    (lo := (1905501 / 250000000)) (hi := (1524401 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248101742239) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248101742239) = 1/(248101742239 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3270 : Bounds (-1524401 / 200000000) (-1905501 / 250000000) (Real.log (248101742239 / 250000000000)) := by
  have h := reflection_log_3270_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3271_neg : (87359557 / 500000000) ≤ -Real.log (4000000000 / 4763646641) ∧
    -Real.log (4000000000 / 4763646641) ≤ (34943823 / 200000000) := by
  have h := checkLog_sound (w := (763646641 / 8763646641)) (n := 12)
    (lo := (87359557 / 500000000)) (hi := (34943823 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4763646641 / 4000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4763646641 / 4000000000) = 1/(4000000000 / 4763646641) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3271 : Bounds (87359557 / 500000000) (34943823 / 200000000) (Real.log (4763646641 / 4000000000)) := by
  have h := reflection_log_3271_neg
  have he : Real.log (4763646641 / 4000000000) = -Real.log (4000000000 / 4763646641) := by
    rw [show ((4763646641 / 4000000000) : ℝ) = ((4000000000 / 4763646641) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3272_neg : (87586283 / 500000000) ≤ -Real.log (20000000000 / 23829036079) ∧
    -Real.log (20000000000 / 23829036079) ≤ (175172567 / 1000000000) := by
  have h := checkLog_sound (w := (3829036079 / 43829036079)) (n := 12)
    (lo := (87586283 / 500000000)) (hi := (175172567 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((23829036079 / 20000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(23829036079 / 20000000000) = 1/(20000000000 / 23829036079) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3272 : Bounds (87586283 / 500000000) (175172567 / 1000000000) (Real.log (23829036079 / 20000000000)) := by
  have h := reflection_log_3272_neg
  have he : Real.log (23829036079 / 20000000000) = -Real.log (20000000000 / 23829036079) := by
    rw [show ((23829036079 / 20000000000) : ℝ) = ((20000000000 / 23829036079) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3273_neg : (175273049 / 500000000) ≤ -Real.log (500000000000 / 709921355111) ∧
    -Real.log (500000000000 / 709921355111) ≤ (350546099 / 1000000000) := by
  have h := checkLog_sound (w := (209921355111 / 1209921355111)) (n := 12)
    (lo := (175273049 / 500000000)) (hi := (350546099 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((709921355111 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(709921355111 / 500000000000) = 1/(500000000000 / 709921355111) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3273 : Bounds (175273049 / 500000000) (350546099 / 1000000000) (Real.log (709921355111 / 500000000000)) := by
  have h := reflection_log_3273_neg
  have he : Real.log (709921355111 / 500000000000) = -Real.log (500000000000 / 709921355111) := by
    rw [show ((709921355111 / 500000000000) : ℝ) = ((500000000000 / 709921355111) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3274_neg : (350752309 / 1000000000) ≤ -Real.log (100000000000 / 142013552759) ∧
    -Real.log (100000000000 / 142013552759) ≤ (35075231 / 100000000) := by
  have h := checkLog_sound (w := (42013552759 / 242013552759)) (n := 12)
    (lo := (350752309 / 1000000000)) (hi := (35075231 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((142013552759 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(142013552759 / 100000000000) = 1/(100000000000 / 142013552759) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3274 : Bounds (350752309 / 1000000000) (35075231 / 100000000) (Real.log (142013552759 / 100000000000)) := by
  have h := reflection_log_3274_neg
  have he : Real.log (142013552759 / 100000000000) = -Real.log (100000000000 / 142013552759) := by
    rw [show ((142013552759 / 100000000000) : ℝ) = ((100000000000 / 142013552759) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3275_neg : (1251259 / 7812500) ≤ -Real.log (10000 / 11737) ∧
    -Real.log (10000 / 11737) ≤ (160161153 / 1000000000) := by
  have h := checkLog_sound (w := (1737 / 21737)) (n := 12)
    (lo := (1251259 / 7812500)) (hi := (160161153 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11737 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11737 / 10000) = 1/(10000 / 11737) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3275 : Bounds (1251259 / 7812500) (160161153 / 1000000000) (Real.log (11737 / 10000)) := by
  have h := reflection_log_3275_neg
  have he : Real.log (11737 / 10000) = -Real.log (10000 / 11737) := by
    rw [show ((11737 / 10000) : ℝ) = ((10000 / 11737) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3276_neg : (1526379 / 8000000) ≤ -Real.log (8263 / 10000) ∧
    -Real.log (8263 / 10000) ≤ (2981209 / 15625000) := by
  have h := checkLog_sound (w := (1737 / 18263)) (n := 12)
    (lo := (1526379 / 8000000)) (hi := (2981209 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8263) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8263) = 1/(8263 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3276 : Bounds (-2981209 / 15625000) (-1526379 / 8000000) (Real.log (8263 / 10000)) := by
  have h := reflection_log_3276_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3277_neg : (43421 / 250000000) ≤ -Real.log (10000000 / 10001737) ∧
    -Real.log (10000000 / 10001737) ≤ (34737 / 200000000) := by
  have h := checkLog_sound (w := (1737 / 20001737)) (n := 12)
    (lo := (43421 / 250000000)) (hi := (34737 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001737 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001737 / 10000000) = 1/(10000000 / 10001737) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3277 : Bounds (43421 / 250000000) (34737 / 200000000) (Real.log (10001737 / 10000000)) := by
  have h := reflection_log_3277_neg
  have he : Real.log (10001737 / 10000000) = -Real.log (10000000 / 10001737) := by
    rw [show ((10001737 / 10000000) : ℝ) = ((10000000 / 10001737) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3278_neg : (34743 / 200000000) ≤ -Real.log (9998263 / 10000000) ∧
    -Real.log (9998263 / 10000000) ≤ (43429 / 250000000) := by
  have h := checkLog_sound (w := (1737 / 19998263)) (n := 12)
    (lo := (34743 / 200000000)) (hi := (43429 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998263) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998263) = 1/(9998263 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3278 : Bounds (-43429 / 250000000) (-34743 / 200000000) (Real.log (9998263 / 10000000)) := by
  have h := reflection_log_3278_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3279_neg : (41797733 / 500000000) ≤ -Real.log (1000000 / 1087189) ∧
    -Real.log (1000000 / 1087189) ≤ (83595467 / 1000000000) := by
  have h := checkLog_sound (w := (87189 / 2087189)) (n := 12)
    (lo := (41797733 / 500000000)) (hi := (83595467 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1087189 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1087189 / 1000000) = 1/(1000000 / 1087189) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3279 : Bounds (41797733 / 500000000) (83595467 / 1000000000) (Real.log (1087189 / 1000000)) := by
  have h := reflection_log_3279_neg
  have he : Real.log (1087189 / 1000000) = -Real.log (1000000 / 1087189) := by
    rw [show ((1087189 / 1000000) : ℝ) = ((1000000 / 1087189) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3280_neg : (91226429 / 1000000000) ≤ -Real.log (912811 / 1000000) ∧
    -Real.log (912811 / 1000000) ≤ (9122643 / 100000000) := by
  have h := checkLog_sound (w := (87189 / 1912811)) (n := 12)
    (lo := (91226429 / 1000000000)) (hi := (9122643 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 912811) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 912811) = 1/(912811 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3280 : Bounds (-9122643 / 100000000) (-91226429 / 1000000000) (Real.log (912811 / 1000000)) := by
  have h := reflection_log_3280_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3281_neg : (104753 / 1250000) ≤ -Real.log (500000 / 543707) ∧
    -Real.log (500000 / 543707) ≤ (83802401 / 1000000000) := by
  have h := checkLog_sound (w := (43707 / 1043707)) (n := 12)
    (lo := (104753 / 1250000)) (hi := (83802401 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((543707 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(543707 / 500000) = 1/(500000 / 543707) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3281 : Bounds (104753 / 1250000) (83802401 / 1000000000) (Real.log (543707 / 500000)) := by
  have h := reflection_log_3281_neg
  have he : Real.log (543707 / 500000) = -Real.log (500000 / 543707) := by
    rw [show ((543707 / 500000) : ℝ) = ((500000 / 543707) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3282_neg : (91472951 / 1000000000) ≤ -Real.log (456293 / 500000) ∧
    -Real.log (456293 / 500000) ≤ (11434119 / 125000000) := by
  have h := checkLog_sound (w := (43707 / 956293)) (n := 12)
    (lo := (91472951 / 1000000000)) (hi := (11434119 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 456293) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 456293) = 1/(456293 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3282 : Bounds (-11434119 / 125000000) (-91472951 / 1000000000) (Real.log (456293 / 500000)) := by
  have h := reflection_log_3282_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3283_neg : (153411 / 20000000) ≤ -Real.log (248089698151 / 250000000000) ∧
    -Real.log (248089698151 / 250000000000) ≤ (7670551 / 1000000000) := by
  have h := checkLog_sound (w := (1910301849 / 498089698151)) (n := 12)
    (lo := (153411 / 20000000)) (hi := (7670551 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248089698151) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248089698151) = 1/(248089698151 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3283 : Bounds (-7670551 / 1000000000) (-153411 / 20000000) (Real.log (248089698151 / 250000000000)) := by
  have h := reflection_log_3283_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3284_neg : (7630963 / 1000000000) ≤ -Real.log (992398078279 / 1000000000000) ∧
    -Real.log (992398078279 / 1000000000000) ≤ (1907741 / 250000000) := by
  have h := checkLog_sound (w := (7601921721 / 1992398078279)) (n := 12)
    (lo := (7630963 / 1000000000)) (hi := (1907741 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 992398078279) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 992398078279) = 1/(992398078279 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3284 : Bounds (-1907741 / 250000000) (-7630963 / 1000000000) (Real.log (992398078279 / 1000000000000)) := by
  have h := reflection_log_3284_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3285_neg : (34964379 / 200000000) ≤ -Real.log (250000000000 / 297758517371) ∧
    -Real.log (250000000000 / 297758517371) ≤ (21852737 / 125000000) := by
  have h := checkLog_sound (w := (47758517371 / 547758517371)) (n := 12)
    (lo := (34964379 / 200000000)) (hi := (21852737 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((297758517371 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(297758517371 / 250000000000) = 1/(250000000000 / 297758517371) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3285 : Bounds (34964379 / 200000000) (21852737 / 125000000) (Real.log (297758517371 / 250000000000)) := by
  have h := reflection_log_3285_neg
  have he : Real.log (297758517371 / 250000000000) = -Real.log (250000000000 / 297758517371) := by
    rw [show ((297758517371 / 250000000000) : ℝ) = ((250000000000 / 297758517371) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3286_neg : (175275351 / 1000000000) ≤ -Real.log (250000000000 / 297893568387) ∧
    -Real.log (250000000000 / 297893568387) ≤ (21909419 / 125000000) := by
  have h := checkLog_sound (w := (47893568387 / 547893568387)) (n := 12)
    (lo := (175275351 / 1000000000)) (hi := (21909419 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((297893568387 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(297893568387 / 250000000000) = 1/(250000000000 / 297893568387) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3286 : Bounds (175275351 / 1000000000) (21909419 / 125000000) (Real.log (297893568387 / 250000000000)) := by
  have h := reflection_log_3286_neg
  have he : Real.log (297893568387 / 250000000000) = -Real.log (250000000000 / 297893568387) := by
    rw [show ((297893568387 / 250000000000) : ℝ) = ((250000000000 / 297893568387) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3287_neg : (350752309 / 1000000000) ≤ -Real.log (250000000000 / 355033881897) ∧
    -Real.log (250000000000 / 355033881897) ≤ (35075231 / 100000000) := by
  have h := checkLog_sound (w := (105033881897 / 605033881897)) (n := 12)
    (lo := (350752309 / 1000000000)) (hi := (35075231 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((355033881897 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(355033881897 / 250000000000) = 1/(250000000000 / 355033881897) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3287 : Bounds (350752309 / 1000000000) (35075231 / 100000000) (Real.log (355033881897 / 250000000000)) := by
  have h := reflection_log_3287_neg
  have he : Real.log (355033881897 / 250000000000) = -Real.log (250000000000 / 355033881897) := by
    rw [show ((355033881897 / 250000000000) : ℝ) = ((250000000000 / 355033881897) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3288_neg : (350958527 / 1000000000) ≤ -Real.log (100000000000 / 142042841583) ∧
    -Real.log (100000000000 / 142042841583) ≤ (5483727 / 15625000) := by
  have h := checkLog_sound (w := (42042841583 / 242042841583)) (n := 12)
    (lo := (350958527 / 1000000000)) (hi := (5483727 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((142042841583 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(142042841583 / 100000000000) = 1/(100000000000 / 142042841583) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3288 : Bounds (350958527 / 1000000000) (5483727 / 15625000) (Real.log (142042841583 / 100000000000)) := by
  have h := reflection_log_3288_neg
  have he : Real.log (142042841583 / 100000000000) = -Real.log (100000000000 / 142042841583) := by
    rw [show ((142042841583 / 100000000000) : ℝ) = ((100000000000 / 142042841583) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3289_neg : (160246349 / 1000000000) ≤ -Real.log (5000 / 5869) ∧
    -Real.log (5000 / 5869) ≤ (3204927 / 20000000) := by
  have h := checkLog_sound (w := (869 / 10869)) (n := 12)
    (lo := (160246349 / 1000000000)) (hi := (3204927 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5869 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5869 / 5000) = 1/(5000 / 5869) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3289 : Bounds (160246349 / 1000000000) (3204927 / 20000000) (Real.log (5869 / 5000)) := by
  have h := reflection_log_3289_neg
  have he : Real.log (5869 / 5000) = -Real.log (5000 / 5869) := by
    rw [show ((5869 / 5000) : ℝ) = ((5000 / 5869) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3290_neg : (47729601 / 250000000) ≤ -Real.log (4131 / 5000) ∧
    -Real.log (4131 / 5000) ≤ (38183681 / 200000000) := by
  have h := checkLog_sound (w := (869 / 9131)) (n := 12)
    (lo := (47729601 / 250000000)) (hi := (38183681 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4131) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4131) = 1/(4131 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3290 : Bounds (-38183681 / 200000000) (-47729601 / 250000000) (Real.log (4131 / 5000)) := by
  have h := reflection_log_3290_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3291_neg : (21723 / 125000000) ≤ -Real.log (5000000 / 5000869) ∧
    -Real.log (5000000 / 5000869) ≤ (34757 / 200000000) := by
  have h := checkLog_sound (w := (869 / 10000869)) (n := 12)
    (lo := (21723 / 125000000)) (hi := (34757 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000869 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000869 / 5000000) = 1/(5000000 / 5000869) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3291 : Bounds (21723 / 125000000) (34757 / 200000000) (Real.log (5000869 / 5000000)) := by
  have h := reflection_log_3291_neg
  have he : Real.log (5000869 / 5000000) = -Real.log (5000000 / 5000869) := by
    rw [show ((5000869 / 5000000) : ℝ) = ((5000000 / 5000869) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3292_neg : (34763 / 200000000) ≤ -Real.log (4999131 / 5000000) ∧
    -Real.log (4999131 / 5000000) ≤ (21727 / 125000000) := by
  have h := checkLog_sound (w := (869 / 9999131)) (n := 12)
    (lo := (34763 / 200000000)) (hi := (21727 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999131) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999131) = 1/(4999131 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3292 : Bounds (-21727 / 125000000) (-34763 / 200000000) (Real.log (4999131 / 5000000)) := by
  have h := reflection_log_3292_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3293_neg : (41821187 / 500000000) ≤ -Real.log (25000 / 27181) ∧
    -Real.log (25000 / 27181) ≤ (669139 / 8000000) := by
  have h := checkLog_sound (w := (2181 / 52181)) (n := 12)
    (lo := (41821187 / 500000000)) (hi := (669139 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((27181 / 25000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(27181 / 25000) = 1/(25000 / 27181) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3293 : Bounds (41821187 / 500000000) (669139 / 8000000) (Real.log (27181 / 25000)) := by
  have h := reflection_log_3293_neg
  have he : Real.log (27181 / 25000) = -Real.log (25000 / 27181) := by
    rw [show ((27181 / 25000) : ℝ) = ((25000 / 27181) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3294_neg : (45641151 / 500000000) ≤ -Real.log (22819 / 25000) ∧
    -Real.log (22819 / 25000) ≤ (91282303 / 1000000000) := by
  have h := checkLog_sound (w := (2181 / 47819)) (n := 12)
    (lo := (45641151 / 500000000)) (hi := (91282303 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 22819) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25000 / 22819) = 1/(22819 / 25000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3294 : Bounds (-91282303 / 1000000000) (-45641151 / 500000000) (Real.log (22819 / 25000)) := by
  have h := reflection_log_3294_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3295_neg : (83849299 / 1000000000) ≤ -Real.log (200000 / 217493) ∧
    -Real.log (200000 / 217493) ≤ (838493 / 10000000) := by
  have h := checkLog_sound (w := (17493 / 417493)) (n := 12)
    (lo := (83849299 / 1000000000)) (hi := (838493 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((217493 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(217493 / 200000) = 1/(200000 / 217493) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3295 : Bounds (83849299 / 1000000000) (838493 / 10000000) (Real.log (217493 / 200000)) := by
  have h := reflection_log_3295_neg
  have he : Real.log (217493 / 200000) = -Real.log (200000 / 217493) := by
    rw [show ((217493 / 200000) : ℝ) = ((200000 / 217493) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3296_neg : (45764419 / 500000000) ≤ -Real.log (182507 / 200000) ∧
    -Real.log (182507 / 200000) ≤ (91528839 / 1000000000) := by
  have h := checkLog_sound (w := (17493 / 382507)) (n := 12)
    (lo := (45764419 / 500000000)) (hi := (91528839 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 182507) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 182507) = 1/(182507 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3296 : Bounds (-91528839 / 1000000000) (-45764419 / 500000000) (Real.log (182507 / 200000)) := by
  have h := reflection_log_3296_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3297_neg : (3839769 / 500000000) ≤ -Real.log (39693994951 / 40000000000) ∧
    -Real.log (39693994951 / 40000000000) ≤ (7679539 / 1000000000) := by
  have h := checkLog_sound (w := (306005049 / 79693994951)) (n := 12)
    (lo := (3839769 / 500000000)) (hi := (7679539 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39693994951) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39693994951) = 1/(39693994951 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3297 : Bounds (-7679539 / 1000000000) (-3839769 / 500000000) (Real.log (39693994951 / 40000000000)) := by
  have h := reflection_log_3297_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3298_neg : (7639927 / 1000000000) ≤ -Real.log (620243239 / 625000000) ∧
    -Real.log (620243239 / 625000000) ≤ (954991 / 125000000) := by
  have h := checkLog_sound (w := (4756761 / 1245243239)) (n := 12)
    (lo := (7639927 / 1000000000)) (hi := (954991 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625000000 / 620243239) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625000000 / 620243239) = 1/(620243239 / 625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3298 : Bounds (-954991 / 125000000) (-7639927 / 1000000000) (Real.log (620243239 / 625000000)) := by
  have h := reflection_log_3298_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3299_neg : (174924677 / 1000000000) ≤ -Real.log (250000000000 / 297789123099) ∧
    -Real.log (250000000000 / 297789123099) ≤ (87462339 / 500000000) := by
  have h := checkLog_sound (w := (47789123099 / 547789123099)) (n := 12)
    (lo := (174924677 / 1000000000)) (hi := (87462339 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((297789123099 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(297789123099 / 250000000000) = 1/(250000000000 / 297789123099) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3299 : Bounds (174924677 / 1000000000) (87462339 / 500000000) (Real.log (297789123099 / 250000000000)) := by
  have h := reflection_log_3299_neg
  have he : Real.log (297789123099 / 250000000000) = -Real.log (250000000000 / 297789123099) := by
    rw [show ((297789123099 / 250000000000) : ℝ) = ((250000000000 / 297789123099) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3300_neg : (175378137 / 1000000000) ≤ -Real.log (500000000000 / 595848378419) ∧
    -Real.log (500000000000 / 595848378419) ≤ (87689069 / 500000000) := by
  have h := checkLog_sound (w := (95848378419 / 1095848378419)) (n := 12)
    (lo := (175378137 / 1000000000)) (hi := (87689069 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((595848378419 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(595848378419 / 500000000000) = 1/(500000000000 / 595848378419) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3300 : Bounds (175378137 / 1000000000) (87689069 / 500000000) (Real.log (595848378419 / 500000000000)) := by
  have h := reflection_log_3300_neg
  have he : Real.log (595848378419 / 500000000000) = -Real.log (500000000000 / 595848378419) := by
    rw [show ((595848378419 / 500000000000) : ℝ) = ((500000000000 / 595848378419) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3301_neg : (350958527 / 1000000000) ≤ -Real.log (250000000000 / 355107103957) ∧
    -Real.log (250000000000 / 355107103957) ≤ (5483727 / 15625000) := by
  have h := checkLog_sound (w := (105107103957 / 605107103957)) (n := 12)
    (lo := (350958527 / 1000000000)) (hi := (5483727 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((355107103957 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(355107103957 / 250000000000) = 1/(250000000000 / 355107103957) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3301 : Bounds (350958527 / 1000000000) (5483727 / 15625000) (Real.log (355107103957 / 250000000000)) := by
  have h := reflection_log_3301_neg
  have he : Real.log (355107103957 / 250000000000) = -Real.log (250000000000 / 355107103957) := by
    rw [show ((355107103957 / 250000000000) : ℝ) = ((250000000000 / 355107103957) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3302_neg : (351164753 / 1000000000) ≤ -Real.log (100000000000 / 142072137497) ∧
    -Real.log (100000000000 / 142072137497) ≤ (175582377 / 500000000) := by
  have h := checkLog_sound (w := (42072137497 / 242072137497)) (n := 12)
    (lo := (351164753 / 1000000000)) (hi := (175582377 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((142072137497 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(142072137497 / 100000000000) = 1/(100000000000 / 142072137497) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3302 : Bounds (351164753 / 1000000000) (175582377 / 500000000) (Real.log (142072137497 / 100000000000)) := by
  have h := reflection_log_3302_neg
  have he : Real.log (142072137497 / 100000000000) = -Real.log (100000000000 / 142072137497) := by
    rw [show ((142072137497 / 100000000000) : ℝ) = ((100000000000 / 142072137497) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3303_neg : (80165769 / 500000000) ≤ -Real.log (10000 / 11739) ∧
    -Real.log (10000 / 11739) ≤ (160331539 / 1000000000) := by
  have h := checkLog_sound (w := (1739 / 21739)) (n := 12)
    (lo := (80165769 / 500000000)) (hi := (160331539 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11739 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11739 / 10000) = 1/(10000 / 11739) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3303 : Bounds (80165769 / 500000000) (160331539 / 1000000000) (Real.log (11739 / 10000)) := by
  have h := reflection_log_3303_neg
  have he : Real.log (11739 / 10000) = -Real.log (10000 / 11739) := by
    rw [show ((11739 / 10000) : ℝ) = ((10000 / 11739) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3304_neg : (191039447 / 1000000000) ≤ -Real.log (8261 / 10000) ∧
    -Real.log (8261 / 10000) ≤ (23879931 / 125000000) := by
  have h := checkLog_sound (w := (1739 / 18261)) (n := 12)
    (lo := (191039447 / 1000000000)) (hi := (23879931 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8261) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8261) = 1/(8261 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3304 : Bounds (-23879931 / 125000000) (-191039447 / 1000000000) (Real.log (8261 / 10000)) := by
  have h := reflection_log_3304_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3305_neg : (43471 / 250000000) ≤ -Real.log (10000000 / 10001739) ∧
    -Real.log (10000000 / 10001739) ≤ (34777 / 200000000) := by
  have h := checkLog_sound (w := (1739 / 20001739)) (n := 12)
    (lo := (43471 / 250000000)) (hi := (34777 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001739 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001739 / 10000000) = 1/(10000000 / 10001739) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3305 : Bounds (43471 / 250000000) (34777 / 200000000) (Real.log (10001739 / 10000000)) := by
  have h := reflection_log_3305_neg
  have he : Real.log (10001739 / 10000000) = -Real.log (10000000 / 10001739) := by
    rw [show ((10001739 / 10000000) : ℝ) = ((10000000 / 10001739) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3306_neg : (34783 / 200000000) ≤ -Real.log (9998261 / 10000000) ∧
    -Real.log (9998261 / 10000000) ≤ (43479 / 250000000) := by
  have h := checkLog_sound (w := (1739 / 19998261)) (n := 12)
    (lo := (34783 / 200000000)) (hi := (43479 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998261) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998261) = 1/(9998261 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3306 : Bounds (-43479 / 250000000) (-34783 / 200000000) (Real.log (9998261 / 10000000)) := by
  have h := reflection_log_3306_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3307_neg : (83689281 / 1000000000) ≤ -Real.log (1000000 / 1087291) ∧
    -Real.log (1000000 / 1087291) ≤ (41844641 / 500000000) := by
  have h := checkLog_sound (w := (87291 / 2087291)) (n := 12)
    (lo := (83689281 / 1000000000)) (hi := (41844641 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1087291 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1087291 / 1000000) = 1/(1000000 / 1087291) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3307 : Bounds (83689281 / 1000000000) (41844641 / 500000000) (Real.log (1087291 / 1000000)) := by
  have h := reflection_log_3307_neg
  have he : Real.log (1087291 / 1000000) = -Real.log (1000000 / 1087291) := by
    rw [show ((1087291 / 1000000) : ℝ) = ((1000000 / 1087291) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3308_neg : (45669089 / 500000000) ≤ -Real.log (912709 / 1000000) ∧
    -Real.log (912709 / 1000000) ≤ (91338179 / 1000000000) := by
  have h := checkLog_sound (w := (87291 / 1912709)) (n := 12)
    (lo := (45669089 / 500000000)) (hi := (91338179 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 912709) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 912709) = 1/(912709 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3308 : Bounds (-91338179 / 1000000000) (-45669089 / 500000000) (Real.log (912709 / 1000000)) := by
  have h := reflection_log_3308_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3309_neg : (20973819 / 250000000) ≤ -Real.log (200000 / 217503) ∧
    -Real.log (200000 / 217503) ≤ (83895277 / 1000000000) := by
  have h := checkLog_sound (w := (17503 / 417503)) (n := 12)
    (lo := (20973819 / 250000000)) (hi := (83895277 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((217503 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(217503 / 200000) = 1/(200000 / 217503) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3309 : Bounds (20973819 / 250000000) (83895277 / 1000000000) (Real.log (217503 / 200000)) := by
  have h := reflection_log_3309_neg
  have he : Real.log (217503 / 200000) = -Real.log (200000 / 217503) := by
    rw [show ((217503 / 200000) : ℝ) = ((200000 / 217503) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3310_neg : (5723977 / 62500000) ≤ -Real.log (182497 / 200000) ∧
    -Real.log (182497 / 200000) ≤ (91583633 / 1000000000) := by
  have h := checkLog_sound (w := (17503 / 382497)) (n := 12)
    (lo := (5723977 / 62500000)) (hi := (91583633 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 182497) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 182497) = 1/(182497 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3310 : Bounds (-91583633 / 1000000000) (-5723977 / 62500000) (Real.log (182497 / 200000)) := by
  have h := reflection_log_3310_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3311_neg : (1537671 / 200000000) ≤ -Real.log (39693644991 / 40000000000) ∧
    -Real.log (39693644991 / 40000000000) ≤ (1922089 / 250000000) := by
  have h := checkLog_sound (w := (306355009 / 79693644991)) (n := 12)
    (lo := (1537671 / 200000000)) (hi := (1922089 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39693644991) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39693644991) = 1/(39693644991 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3311 : Bounds (-1922089 / 250000000) (-1537671 / 200000000) (Real.log (39693644991 / 40000000000)) := by
  have h := reflection_log_3311_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3312_neg : (7648897 / 1000000000) ≤ -Real.log (992380281319 / 1000000000000) ∧
    -Real.log (992380281319 / 1000000000000) ≤ (3824449 / 500000000) := by
  have h := checkLog_sound (w := (7619718681 / 1992380281319)) (n := 12)
    (lo := (7648897 / 1000000000)) (hi := (3824449 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 992380281319) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 992380281319) = 1/(992380281319 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3312 : Bounds (-3824449 / 500000000) (-7648897 / 1000000000) (Real.log (992380281319 / 1000000000000)) := by
  have h := reflection_log_3312_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3313_neg : (8751373 / 50000000) ≤ -Real.log (100000000000 / 119127892899) ∧
    -Real.log (100000000000 / 119127892899) ≤ (175027461 / 1000000000) := by
  have h := checkLog_sound (w := (19127892899 / 219127892899)) (n := 12)
    (lo := (8751373 / 50000000)) (hi := (175027461 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((119127892899 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(119127892899 / 100000000000) = 1/(100000000000 / 119127892899) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3313 : Bounds (8751373 / 50000000) (175027461 / 1000000000) (Real.log (119127892899 / 100000000000)) := by
  have h := reflection_log_3313_neg
  have he : Real.log (119127892899 / 100000000000) = -Real.log (100000000000 / 119127892899) := by
    rw [show ((119127892899 / 100000000000) : ℝ) = ((100000000000 / 119127892899) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3314_neg : (175478909 / 1000000000) ≤ -Real.log (125000000000 / 148977106473) ∧
    -Real.log (125000000000 / 148977106473) ≤ (17547891 / 100000000) := by
  have h := checkLog_sound (w := (23977106473 / 273977106473)) (n := 12)
    (lo := (175478909 / 1000000000)) (hi := (17547891 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((148977106473 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(148977106473 / 125000000000) = 1/(125000000000 / 148977106473) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3314 : Bounds (175478909 / 1000000000) (17547891 / 100000000) (Real.log (148977106473 / 125000000000)) := by
  have h := reflection_log_3314_neg
  have he : Real.log (148977106473 / 125000000000) = -Real.log (125000000000 / 148977106473) := by
    rw [show ((148977106473 / 125000000000) : ℝ) = ((125000000000 / 148977106473) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3315_neg : (351164753 / 1000000000) ≤ -Real.log (125000000000 / 177590171871) ∧
    -Real.log (125000000000 / 177590171871) ≤ (175582377 / 500000000) := by
  have h := checkLog_sound (w := (52590171871 / 302590171871)) (n := 12)
    (lo := (351164753 / 1000000000)) (hi := (175582377 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((177590171871 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(177590171871 / 125000000000) = 1/(125000000000 / 177590171871) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3315 : Bounds (351164753 / 1000000000) (175582377 / 500000000) (Real.log (177590171871 / 125000000000)) := by
  have h := reflection_log_3315_neg
  have he : Real.log (177590171871 / 125000000000) = -Real.log (125000000000 / 177590171871) := by
    rw [show ((177590171871 / 125000000000) : ℝ) = ((125000000000 / 177590171871) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3316_neg : (175685493 / 500000000) ≤ -Real.log (250000000000 / 355253601259) ∧
    -Real.log (250000000000 / 355253601259) ≤ (351370987 / 1000000000) := by
  have h := checkLog_sound (w := (105253601259 / 605253601259)) (n := 12)
    (lo := (175685493 / 500000000)) (hi := (351370987 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((355253601259 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(355253601259 / 250000000000) = 1/(250000000000 / 355253601259) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3316 : Bounds (175685493 / 500000000) (351370987 / 1000000000) (Real.log (355253601259 / 250000000000)) := by
  have h := reflection_log_3316_neg
  have he : Real.log (355253601259 / 250000000000) = -Real.log (250000000000 / 355253601259) := by
    rw [show ((355253601259 / 250000000000) : ℝ) = ((250000000000 / 355253601259) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3317_neg : (160416721 / 1000000000) ≤ -Real.log (500 / 587) ∧
    -Real.log (500 / 587) ≤ (80208361 / 500000000) := by
  have h := checkLog_sound (w := (87 / 1087)) (n := 12)
    (lo := (160416721 / 1000000000)) (hi := (80208361 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((587 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(587 / 500) = 1/(500 / 587) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3317 : Bounds (160416721 / 1000000000) (80208361 / 500000000) (Real.log (587 / 500)) := by
  have h := reflection_log_3317_neg
  have he : Real.log (587 / 500) = -Real.log (500 / 587) := by
    rw [show ((587 / 500) : ℝ) = ((500 / 587) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3318_neg : (38232101 / 200000000) ≤ -Real.log (413 / 500) ∧
    -Real.log (413 / 500) ≤ (95580253 / 500000000) := by
  have h := checkLog_sound (w := (87 / 913)) (n := 12)
    (lo := (38232101 / 200000000)) (hi := (95580253 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 413) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500 / 413) = 1/(413 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3318 : Bounds (-95580253 / 500000000) (-38232101 / 200000000) (Real.log (413 / 500)) := by
  have h := reflection_log_3318_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3319_neg : (5437 / 31250000) ≤ -Real.log (500000 / 500087) ∧
    -Real.log (500000 / 500087) ≤ (34797 / 200000000) := by
  have h := checkLog_sound (w := (87 / 1000087)) (n := 12)
    (lo := (5437 / 31250000)) (hi := (34797 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500087 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500087 / 500000) = 1/(500000 / 500087) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3319 : Bounds (5437 / 31250000) (34797 / 200000000) (Real.log (500087 / 500000)) := by
  have h := reflection_log_3319_neg
  have he : Real.log (500087 / 500000) = -Real.log (500000 / 500087) := by
    rw [show ((500087 / 500000) : ℝ) = ((500000 / 500087) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3320_neg : (34803 / 200000000) ≤ -Real.log (499913 / 500000) ∧
    -Real.log (499913 / 500000) ≤ (2719 / 15625000) := by
  have h := checkLog_sound (w := (87 / 999913)) (n := 12)
    (lo := (34803 / 200000000)) (hi := (2719 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499913) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499913) = 1/(499913 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3320 : Bounds (-2719 / 15625000) (-34803 / 200000000) (Real.log (499913 / 500000)) := by
  have h := reflection_log_3320_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3321_neg : (41867633 / 500000000) ≤ -Real.log (1000000 / 1087341) ∧
    -Real.log (1000000 / 1087341) ≤ (83735267 / 1000000000) := by
  have h := checkLog_sound (w := (87341 / 2087341)) (n := 12)
    (lo := (41867633 / 500000000)) (hi := (83735267 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1087341 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1087341 / 1000000) = 1/(1000000 / 1087341) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3321 : Bounds (41867633 / 500000000) (83735267 / 1000000000) (Real.log (1087341 / 1000000)) := by
  have h := reflection_log_3321_neg
  have he : Real.log (1087341 / 1000000) = -Real.log (1000000 / 1087341) := by
    rw [show ((1087341 / 1000000) : ℝ) = ((1000000 / 1087341) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3322_neg : (45696481 / 500000000) ≤ -Real.log (912659 / 1000000) ∧
    -Real.log (912659 / 1000000) ≤ (91392963 / 1000000000) := by
  have h := checkLog_sound (w := (87341 / 1912659)) (n := 12)
    (lo := (45696481 / 500000000)) (hi := (91392963 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 912659) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 912659) = 1/(912659 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3322 : Bounds (-91392963 / 1000000000) (-45696481 / 500000000) (Real.log (912659 / 1000000)) := by
  have h := reflection_log_3322_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3323_neg : (83942171 / 1000000000) ≤ -Real.log (500000 / 543783) ∧
    -Real.log (500000 / 543783) ≤ (20985543 / 250000000) := by
  have h := checkLog_sound (w := (43783 / 1043783)) (n := 12)
    (lo := (83942171 / 1000000000)) (hi := (20985543 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((543783 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(543783 / 500000) = 1/(500000 / 543783) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3323 : Bounds (83942171 / 1000000000) (20985543 / 250000000) (Real.log (543783 / 500000)) := by
  have h := reflection_log_3323_neg
  have he : Real.log (543783 / 500000) = -Real.log (500000 / 543783) := by
    rw [show ((543783 / 500000) : ℝ) = ((500000 / 543783) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3324_neg : (22909881 / 250000000) ≤ -Real.log (456217 / 500000) ∧
    -Real.log (456217 / 500000) ≤ (3665581 / 40000000) := by
  have h := checkLog_sound (w := (43783 / 956217)) (n := 12)
    (lo := (22909881 / 250000000)) (hi := (3665581 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 456217) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 456217) = 1/(456217 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3324 : Bounds (-3665581 / 40000000) (-22909881 / 250000000) (Real.log (456217 / 500000)) := by
  have h := reflection_log_3324_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3325_neg : (7697353 / 1000000000) ≤ -Real.log (248083048911 / 250000000000) ∧
    -Real.log (248083048911 / 250000000000) ≤ (3848677 / 500000000) := by
  have h := checkLog_sound (w := (1916951089 / 498083048911)) (n := 12)
    (lo := (7697353 / 1000000000)) (hi := (3848677 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248083048911) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248083048911) = 1/(248083048911 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3325 : Bounds (-3848677 / 500000000) (-7697353 / 1000000000) (Real.log (248083048911 / 250000000000)) := by
  have h := reflection_log_3325_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3326_neg : (1531539 / 200000000) ≤ -Real.log (992371549719 / 1000000000000) ∧
    -Real.log (992371549719 / 1000000000000) ≤ (239303 / 31250000) := by
  have h := checkLog_sound (w := (7628450281 / 1992371549719)) (n := 12)
    (lo := (1531539 / 200000000)) (hi := (239303 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 992371549719) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 992371549719) = 1/(992371549719 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3326 : Bounds (-239303 / 31250000) (-1531539 / 200000000) (Real.log (992371549719 / 1000000000000)) := by
  have h := reflection_log_3326_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3327_neg : (43782057 / 250000000) ≤ -Real.log (20000000000 / 23827979563) ∧
    -Real.log (20000000000 / 23827979563) ≤ (175128229 / 1000000000) := by
  have h := checkLog_sound (w := (3827979563 / 43827979563)) (n := 12)
    (lo := (43782057 / 250000000)) (hi := (175128229 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((23827979563 / 20000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(23827979563 / 20000000000) = 1/(20000000000 / 23827979563) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3327 : Bounds (43782057 / 250000000) (175128229 / 1000000000) (Real.log (23827979563 / 20000000000)) := by
  have h := reflection_log_3327_neg
  have he : Real.log (23827979563 / 20000000000) = -Real.log (20000000000 / 23827979563) := by
    rw [show ((23827979563 / 20000000000) : ℝ) = ((20000000000 / 23827979563) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily
