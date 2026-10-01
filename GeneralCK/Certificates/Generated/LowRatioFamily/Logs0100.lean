import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_6400_neg : (23495051 / 250000000) ≤ -Real.log (500000 / 549269) ∧
    -Real.log (500000 / 549269) ≤ (18796041 / 200000000) := by
  have h := checkLog_sound (w := (49269 / 1049269)) (n := 12)
    (lo := (23495051 / 250000000)) (hi := (18796041 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((549269 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(549269 / 500000) = 1/(500000 / 549269) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6400 : Bounds (23495051 / 250000000) (18796041 / 200000000) (Real.log (549269 / 500000)) := by
  have h := reflection_log_6400_neg
  have he : Real.log (549269 / 500000) = -Real.log (500000 / 549269) := by
    rw [show ((549269 / 500000) : ℝ) = ((500000 / 549269) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6401_neg : (103737389 / 1000000000) ≤ -Real.log (450731 / 500000) ∧
    -Real.log (450731 / 500000) ≤ (10373739 / 100000000) := by
  have h := checkLog_sound (w := (49269 / 950731)) (n := 12)
    (lo := (103737389 / 1000000000)) (hi := (10373739 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 450731) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 450731) = 1/(450731 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6401 : Bounds (-10373739 / 100000000) (-103737389 / 1000000000) (Real.log (450731 / 500000)) := by
  have h := reflection_log_6401_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6402_neg : (94204113 / 1000000000) ≤ -Real.log (31250 / 34337) ∧
    -Real.log (31250 / 34337) ≤ (47102057 / 500000000) := by
  have h := checkLog_sound (w := (3087 / 65587)) (n := 12)
    (lo := (94204113 / 1000000000)) (hi := (47102057 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((34337 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(34337 / 31250) = 1/(31250 / 34337) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6402 : Bounds (94204113 / 1000000000) (47102057 / 500000000) (Real.log (34337 / 31250)) := by
  have h := reflection_log_6402_neg
  have he : Real.log (34337 / 31250) = -Real.log (31250 / 34337) := by
    rw [show ((34337 / 31250) : ℝ) = ((31250 / 34337) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6403_neg : (26002579 / 250000000) ≤ -Real.log (28163 / 31250) ∧
    -Real.log (28163 / 31250) ≤ (104010317 / 1000000000) := by
  have h := checkLog_sound (w := (3087 / 59413)) (n := 12)
    (lo := (26002579 / 250000000)) (hi := (104010317 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 28163) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31250 / 28163) = 1/(28163 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6403 : Bounds (-104010317 / 1000000000) (-26002579 / 250000000) (Real.log (28163 / 31250)) := by
  have h := reflection_log_6403_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6404_neg : (4903101 / 500000000) ≤ -Real.log (967032931 / 976562500) ∧
    -Real.log (967032931 / 976562500) ≤ (9806203 / 1000000000) := by
  have h := checkLog_sound (w := (9529569 / 1943595431)) (n := 12)
    (lo := (4903101 / 500000000)) (hi := (9806203 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((976562500 / 967032931) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(976562500 / 967032931) = 1/(967032931 / 976562500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6404 : Bounds (-9806203 / 1000000000) (-4903101 / 500000000) (Real.log (967032931 / 976562500)) := by
  have h := reflection_log_6404_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6405_neg : (19057 / 1953125) ≤ -Real.log (247572565639 / 250000000000) ∧
    -Real.log (247572565639 / 250000000000) ≤ (1951437 / 200000000) := by
  have h := checkLog_sound (w := (2427434361 / 497572565639)) (n := 12)
    (lo := (19057 / 1953125)) (hi := (1951437 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247572565639) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247572565639) = 1/(247572565639 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6405 : Bounds (-1951437 / 200000000) (-19057 / 1953125) (Real.log (247572565639 / 250000000000)) := by
  have h := reflection_log_6405_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6406_neg : (98858797 / 500000000) ≤ -Real.log (250000000000 / 304654550053) ∧
    -Real.log (250000000000 / 304654550053) ≤ (39543519 / 200000000) := by
  have h := checkLog_sound (w := (54654550053 / 554654550053)) (n := 12)
    (lo := (98858797 / 500000000)) (hi := (39543519 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((304654550053 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(304654550053 / 250000000000) = 1/(250000000000 / 304654550053) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6406 : Bounds (98858797 / 500000000) (39543519 / 200000000) (Real.log (304654550053 / 250000000000)) := by
  have h := reflection_log_6406_neg
  have he : Real.log (304654550053 / 250000000000) = -Real.log (250000000000 / 304654550053) := by
    rw [show ((304654550053 / 250000000000) : ℝ) = ((250000000000 / 304654550053) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6407_neg : (19821443 / 100000000) ≤ -Real.log (250000000000 / 304805951071) ∧
    -Real.log (250000000000 / 304805951071) ≤ (198214431 / 1000000000) := by
  have h := checkLog_sound (w := (54805951071 / 554805951071)) (n := 12)
    (lo := (19821443 / 100000000)) (hi := (198214431 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((304805951071 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(304805951071 / 250000000000) = 1/(250000000000 / 304805951071) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6407 : Bounds (19821443 / 100000000) (198214431 / 1000000000) (Real.log (304805951071 / 250000000000)) := by
  have h := reflection_log_6407_neg
  have he : Real.log (304805951071 / 250000000000) = -Real.log (250000000000 / 304805951071) := by
    rw [show ((304805951071 / 250000000000) : ℝ) = ((250000000000 / 304805951071) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6408_neg : (396930679 / 1000000000) ≤ -Real.log (4000000000 / 5949011317) ∧
    -Real.log (4000000000 / 5949011317) ≤ (9923267 / 25000000) := by
  have h := checkLog_sound (w := (1949011317 / 9949011317)) (n := 12)
    (lo := (396930679 / 1000000000)) (hi := (9923267 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5949011317 / 4000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5949011317 / 4000000000) = 1/(4000000000 / 5949011317) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6408 : Bounds (396930679 / 1000000000) (9923267 / 25000000) (Real.log (5949011317 / 4000000000)) := by
  have h := reflection_log_6408_neg
  have he : Real.log (5949011317 / 4000000000) = -Real.log (4000000000 / 5949011317) := by
    rw [show ((5949011317 / 4000000000) : ℝ) = ((4000000000 / 5949011317) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6409_neg : (79427733 / 200000000) ≤ -Real.log (3906250000 / 5810789801) ∧
    -Real.log (3906250000 / 5810789801) ≤ (198569333 / 500000000) := by
  have h := checkLog_sound (w := (1904539801 / 9717039801)) (n := 12)
    (lo := (79427733 / 200000000)) (hi := (198569333 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5810789801 / 3906250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5810789801 / 3906250000) = 1/(3906250000 / 5810789801) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6409 : Bounds (79427733 / 200000000) (198569333 / 500000000) (Real.log (5810789801 / 3906250000)) := by
  have h := reflection_log_6409_neg
  have he : Real.log (5810789801 / 3906250000) = -Real.log (3906250000 / 5810789801) := by
    rw [show ((5810789801 / 3906250000) : ℝ) = ((3906250000 / 5810789801) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6410_neg : (22383283 / 125000000) ≤ -Real.log (10000 / 11961) ∧
    -Real.log (10000 / 11961) ≤ (35813253 / 200000000) := by
  have h := checkLog_sound (w := (1961 / 21961)) (n := 12)
    (lo := (22383283 / 125000000)) (hi := (35813253 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11961 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11961 / 10000) = 1/(10000 / 11961) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6410 : Bounds (22383283 / 125000000) (35813253 / 200000000) (Real.log (11961 / 10000)) := by
  have h := reflection_log_6410_neg
  have he : Real.log (11961 / 10000) = -Real.log (10000 / 11961) := by
    rw [show ((11961 / 10000) : ℝ) = ((10000 / 11961) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6411_neg : (43656079 / 200000000) ≤ -Real.log (8039 / 10000) ∧
    -Real.log (8039 / 10000) ≤ (54570099 / 250000000) := by
  have h := checkLog_sound (w := (1961 / 18039)) (n := 12)
    (lo := (43656079 / 200000000)) (hi := (54570099 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8039) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8039) = 1/(8039 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6411 : Bounds (-54570099 / 250000000) (-43656079 / 200000000) (Real.log (8039 / 10000)) := by
  have h := reflection_log_6411_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6412_neg : (2451 / 12500000) ≤ -Real.log (10000000 / 10001961) ∧
    -Real.log (10000000 / 10001961) ≤ (196081 / 1000000000) := by
  have h := checkLog_sound (w := (1961 / 20001961)) (n := 12)
    (lo := (2451 / 12500000)) (hi := (196081 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001961 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001961 / 10000000) = 1/(10000000 / 10001961) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6412 : Bounds (2451 / 12500000) (196081 / 1000000000) (Real.log (10001961 / 10000000)) := by
  have h := reflection_log_6412_neg
  have he : Real.log (10001961 / 10000000) = -Real.log (10000000 / 10001961) := by
    rw [show ((10001961 / 10000000) : ℝ) = ((10000000 / 10001961) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6413_neg : (196119 / 1000000000) ≤ -Real.log (9998039 / 10000000) ∧
    -Real.log (9998039 / 10000000) ≤ (4903 / 25000000) := by
  have h := checkLog_sound (w := (1961 / 19998039)) (n := 12)
    (lo := (196119 / 1000000000)) (hi := (4903 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998039) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998039) = 1/(9998039 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6413 : Bounds (-4903 / 25000000) (-196119 / 1000000000) (Real.log (9998039 / 10000000)) := by
  have h := reflection_log_6413_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6414_neg : (94026629 / 1000000000) ≤ -Real.log (1000000 / 1098589) ∧
    -Real.log (1000000 / 1098589) ≤ (9402663 / 100000000) := by
  have h := checkLog_sound (w := (98589 / 2098589)) (n := 12)
    (lo := (94026629 / 1000000000)) (hi := (9402663 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1098589 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1098589 / 1000000) = 1/(1000000 / 1098589) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6414 : Bounds (94026629 / 1000000000) (9402663 / 100000000) (Real.log (1098589 / 1000000)) := by
  have h := reflection_log_6414_neg
  have he : Real.log (1098589 / 1000000) = -Real.log (1000000 / 1098589) := by
    rw [show ((1098589 / 1000000) : ℝ) = ((1000000 / 1098589) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6415_neg : (20758793 / 200000000) ≤ -Real.log (901411 / 1000000) ∧
    -Real.log (901411 / 1000000) ≤ (51896983 / 500000000) := by
  have h := checkLog_sound (w := (98589 / 1901411)) (n := 12)
    (lo := (20758793 / 200000000)) (hi := (51896983 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 901411) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 901411) = 1/(901411 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6415 : Bounds (-51896983 / 500000000) (-20758793 / 200000000) (Real.log (901411 / 1000000)) := by
  have h := reflection_log_6415_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6416_neg : (94251437 / 1000000000) ≤ -Real.log (250000 / 274709) ∧
    -Real.log (250000 / 274709) ≤ (47125719 / 500000000) := by
  have h := checkLog_sound (w := (24709 / 524709)) (n := 12)
    (lo := (94251437 / 1000000000)) (hi := (47125719 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((274709 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(274709 / 250000) = 1/(250000 / 274709) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6416 : Bounds (94251437 / 1000000000) (47125719 / 500000000) (Real.log (274709 / 250000)) := by
  have h := reflection_log_6416_neg
  have he : Real.log (274709 / 250000) = -Real.log (250000 / 274709) := by
    rw [show ((274709 / 250000) : ℝ) = ((250000 / 274709) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6417_neg : (104068017 / 1000000000) ≤ -Real.log (225291 / 250000) ∧
    -Real.log (225291 / 250000) ≤ (52034009 / 500000000) := by
  have h := checkLog_sound (w := (24709 / 475291)) (n := 12)
    (lo := (104068017 / 1000000000)) (hi := (52034009 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 225291) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 225291) = 1/(225291 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6417 : Bounds (-52034009 / 500000000) (-104068017 / 1000000000) (Real.log (225291 / 250000)) := by
  have h := reflection_log_6417_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6418_neg : (490829 / 50000000) ≤ -Real.log (61889465319 / 62500000000) ∧
    -Real.log (61889465319 / 62500000000) ≤ (9816581 / 1000000000) := by
  have h := checkLog_sound (w := (610534681 / 124389465319)) (n := 12)
    (lo := (490829 / 50000000)) (hi := (9816581 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 61889465319) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 61889465319) = 1/(61889465319 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6418 : Bounds (-9816581 / 1000000000) (-490829 / 50000000) (Real.log (61889465319 / 62500000000)) := by
  have h := reflection_log_6418_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6419_neg : (1220917 / 125000000) ≤ -Real.log (990280209079 / 1000000000000) ∧
    -Real.log (990280209079 / 1000000000000) ≤ (9767337 / 1000000000) := by
  have h := checkLog_sound (w := (9719790921 / 1990280209079)) (n := 12)
    (lo := (1220917 / 125000000)) (hi := (9767337 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 990280209079) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 990280209079) = 1/(990280209079 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6419 : Bounds (-9767337 / 1000000000) (-1220917 / 125000000) (Real.log (990280209079 / 1000000000000)) := by
  have h := reflection_log_6419_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6420_neg : (98910297 / 500000000) ≤ -Real.log (500000000000 / 609371862557) ∧
    -Real.log (500000000000 / 609371862557) ≤ (39564119 / 200000000) := by
  have h := checkLog_sound (w := (109371862557 / 1109371862557)) (n := 12)
    (lo := (98910297 / 500000000)) (hi := (39564119 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((609371862557 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(609371862557 / 500000000000) = 1/(500000000000 / 609371862557) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6420 : Bounds (98910297 / 500000000) (39564119 / 200000000) (Real.log (609371862557 / 500000000000)) := by
  have h := reflection_log_6420_neg
  have he : Real.log (609371862557 / 500000000000) = -Real.log (500000000000 / 609371862557) := by
    rw [show ((609371862557 / 500000000000) : ℝ) = ((500000000000 / 609371862557) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6421_neg : (39663891 / 200000000) ≤ -Real.log (250000000000 / 304837965121) ∧
    -Real.log (250000000000 / 304837965121) ≤ (6197483 / 31250000) := by
  have h := checkLog_sound (w := (54837965121 / 554837965121)) (n := 12)
    (lo := (39663891 / 200000000)) (hi := (6197483 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((304837965121 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(304837965121 / 250000000000) = 1/(250000000000 / 304837965121) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6421 : Bounds (39663891 / 200000000) (6197483 / 31250000) (Real.log (304837965121 / 250000000000)) := by
  have h := reflection_log_6421_neg
  have he : Real.log (304837965121 / 250000000000) = -Real.log (250000000000 / 304837965121) := by
    rw [show ((304837965121 / 250000000000) : ℝ) = ((250000000000 / 304837965121) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6422_neg : (79427733 / 200000000) ≤ -Real.log (500000000000 / 743781094527) ∧
    -Real.log (500000000000 / 743781094527) ≤ (198569333 / 500000000) := by
  have h := checkLog_sound (w := (243781094527 / 1243781094527)) (n := 12)
    (lo := (79427733 / 200000000)) (hi := (198569333 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((743781094527 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(743781094527 / 500000000000) = 1/(500000000000 / 743781094527) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6422 : Bounds (79427733 / 200000000) (198569333 / 500000000) (Real.log (743781094527 / 500000000000)) := by
  have h := reflection_log_6422_neg
  have he : Real.log (743781094527 / 500000000000) = -Real.log (500000000000 / 743781094527) := by
    rw [show ((743781094527 / 500000000000) : ℝ) = ((500000000000 / 743781094527) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6423_neg : (397346659 / 1000000000) ≤ -Real.log (500000000000 / 743935812913) ∧
    -Real.log (500000000000 / 743935812913) ≤ (19867333 / 50000000) := by
  have h := checkLog_sound (w := (243935812913 / 1243935812913)) (n := 12)
    (lo := (397346659 / 1000000000)) (hi := (19867333 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((743935812913 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(743935812913 / 500000000000) = 1/(500000000000 / 743935812913) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6423 : Bounds (397346659 / 1000000000) (19867333 / 50000000) (Real.log (743935812913 / 500000000000)) := by
  have h := reflection_log_6423_neg
  have he : Real.log (743935812913 / 500000000000) = -Real.log (500000000000 / 743935812913) := by
    rw [show ((743935812913 / 500000000000) : ℝ) = ((500000000000 / 743935812913) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6424_neg : (35829973 / 200000000) ≤ -Real.log (5000 / 5981) ∧
    -Real.log (5000 / 5981) ≤ (89574933 / 500000000) := by
  have h := checkLog_sound (w := (981 / 10981)) (n := 12)
    (lo := (35829973 / 200000000)) (hi := (89574933 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5981 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5981 / 5000) = 1/(5000 / 5981) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6424 : Bounds (35829973 / 200000000) (89574933 / 500000000) (Real.log (5981 / 5000)) := by
  have h := reflection_log_6424_neg
  have he : Real.log (5981 / 5000) = -Real.log (5000 / 5981) := by
    rw [show ((5981 / 5000) : ℝ) = ((5000 / 5981) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6425_neg : (54601199 / 250000000) ≤ -Real.log (4019 / 5000) ∧
    -Real.log (4019 / 5000) ≤ (218404797 / 1000000000) := by
  have h := checkLog_sound (w := (981 / 9019)) (n := 12)
    (lo := (54601199 / 250000000)) (hi := (218404797 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4019) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4019) = 1/(4019 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6425 : Bounds (-218404797 / 1000000000) (-54601199 / 250000000) (Real.log (4019 / 5000)) := by
  have h := reflection_log_6425_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6426_neg : (9809 / 50000000) ≤ -Real.log (5000000 / 5000981) ∧
    -Real.log (5000000 / 5000981) ≤ (196181 / 1000000000) := by
  have h := checkLog_sound (w := (981 / 10000981)) (n := 12)
    (lo := (9809 / 50000000)) (hi := (196181 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000981 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000981 / 5000000) = 1/(5000000 / 5000981) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6426 : Bounds (9809 / 50000000) (196181 / 1000000000) (Real.log (5000981 / 5000000)) := by
  have h := reflection_log_6426_neg
  have he : Real.log (5000981 / 5000000) = -Real.log (5000000 / 5000981) := by
    rw [show ((5000981 / 5000000) : ℝ) = ((5000000 / 5000981) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6427_neg : (196219 / 1000000000) ≤ -Real.log (4999019 / 5000000) ∧
    -Real.log (4999019 / 5000000) ≤ (9811 / 50000000) := by
  have h := checkLog_sound (w := (981 / 9999019)) (n := 12)
    (lo := (196219 / 1000000000)) (hi := (9811 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999019) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999019) = 1/(4999019 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6427 : Bounds (-9811 / 50000000) (-196219 / 1000000000) (Real.log (4999019 / 5000000)) := by
  have h := reflection_log_6427_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6428_neg : (94073051 / 1000000000) ≤ -Real.log (12500 / 13733) ∧
    -Real.log (12500 / 13733) ≤ (23518263 / 250000000) := by
  have h := checkLog_sound (w := (1233 / 26233)) (n := 12)
    (lo := (94073051 / 1000000000)) (hi := (23518263 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((13733 / 12500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(13733 / 12500) = 1/(12500 / 13733) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6428 : Bounds (94073051 / 1000000000) (23518263 / 250000000) (Real.log (13733 / 12500)) := by
  have h := reflection_log_6428_neg
  have he : Real.log (13733 / 12500) = -Real.log (12500 / 13733) := by
    rw [show ((13733 / 12500) : ℝ) = ((12500 / 13733) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6429_neg : (20770109 / 200000000) ≤ -Real.log (11267 / 12500) ∧
    -Real.log (11267 / 12500) ≤ (51925273 / 500000000) := by
  have h := checkLog_sound (w := (1233 / 23767)) (n := 12)
    (lo := (20770109 / 200000000)) (hi := (51925273 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12500 / 11267) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12500 / 11267) = 1/(11267 / 12500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6429 : Bounds (-51925273 / 500000000) (-20770109 / 200000000) (Real.log (11267 / 12500)) := by
  have h := reflection_log_6429_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6430_neg : (94297849 / 1000000000) ≤ -Real.log (1000000 / 1098887) ∧
    -Real.log (1000000 / 1098887) ≤ (1885957 / 20000000) := by
  have h := checkLog_sound (w := (98887 / 2098887)) (n := 12)
    (lo := (94297849 / 1000000000)) (hi := (1885957 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1098887 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1098887 / 1000000) = 1/(1000000 / 1098887) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6430 : Bounds (94297849 / 1000000000) (1885957 / 20000000) (Real.log (1098887 / 1000000)) := by
  have h := reflection_log_6430_neg
  have he : Real.log (1098887 / 1000000) = -Real.log (1000000 / 1098887) := by
    rw [show ((1098887 / 1000000) : ℝ) = ((1000000 / 1098887) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6431_neg : (104124613 / 1000000000) ≤ -Real.log (901113 / 1000000) ∧
    -Real.log (901113 / 1000000) ≤ (52062307 / 500000000) := by
  have h := checkLog_sound (w := (98887 / 1901113)) (n := 12)
    (lo := (104124613 / 1000000000)) (hi := (52062307 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 901113) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 901113) = 1/(901113 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6431 : Bounds (-52062307 / 500000000) (-104124613 / 1000000000) (Real.log (901113 / 1000000)) := by
  have h := reflection_log_6431_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6432_neg : (9826763 / 1000000000) ≤ -Real.log (990221361231 / 1000000000000) ∧
    -Real.log (990221361231 / 1000000000000) ≤ (2456691 / 250000000) := by
  have h := checkLog_sound (w := (9778638769 / 1990221361231)) (n := 12)
    (lo := (9826763 / 1000000000)) (hi := (2456691 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 990221361231) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 990221361231) = 1/(990221361231 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6432 : Bounds (-2456691 / 250000000) (-9826763 / 1000000000) (Real.log (990221361231 / 1000000000000)) := by
  have h := reflection_log_6432_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6433_neg : (9777493 / 1000000000) ≤ -Real.log (154729711 / 156250000) ∧
    -Real.log (154729711 / 156250000) ≤ (4888747 / 500000000) := by
  have h := checkLog_sound (w := (1520289 / 310979711)) (n := 12)
    (lo := (9777493 / 1000000000)) (hi := (4888747 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((156250000 / 154729711) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(156250000 / 154729711) = 1/(154729711 / 156250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6433 : Bounds (-4888747 / 500000000) (-9777493 / 1000000000) (Real.log (154729711 / 156250000)) := by
  have h := reflection_log_6433_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6434_neg : (49480899 / 250000000) ≤ -Real.log (500000000000 / 609434632111) ∧
    -Real.log (500000000000 / 609434632111) ≤ (197923597 / 1000000000) := by
  have h := checkLog_sound (w := (109434632111 / 1109434632111)) (n := 12)
    (lo := (49480899 / 250000000)) (hi := (197923597 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((609434632111 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(609434632111 / 500000000000) = 1/(500000000000 / 609434632111) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6434 : Bounds (49480899 / 250000000) (197923597 / 1000000000) (Real.log (609434632111 / 500000000000)) := by
  have h := reflection_log_6434_neg
  have he : Real.log (609434632111 / 500000000000) = -Real.log (500000000000 / 609434632111) := by
    rw [show ((609434632111 / 500000000000) : ℝ) = ((500000000000 / 609434632111) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6435_neg : (99211231 / 500000000) ≤ -Real.log (50000000000 / 60973873421) ∧
    -Real.log (50000000000 / 60973873421) ≤ (198422463 / 1000000000) := by
  have h := checkLog_sound (w := (10973873421 / 110973873421)) (n := 12)
    (lo := (99211231 / 500000000)) (hi := (198422463 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((60973873421 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(60973873421 / 50000000000) = 1/(50000000000 / 60973873421) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6435 : Bounds (99211231 / 500000000) (198422463 / 1000000000) (Real.log (60973873421 / 50000000000)) := by
  have h := reflection_log_6435_neg
  have he : Real.log (60973873421 / 50000000000) = -Real.log (50000000000 / 60973873421) := by
    rw [show ((60973873421 / 50000000000) : ℝ) = ((50000000000 / 60973873421) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6436_neg : (397346659 / 1000000000) ≤ -Real.log (31250000000 / 46495988307) ∧
    -Real.log (31250000000 / 46495988307) ≤ (19867333 / 50000000) := by
  have h := checkLog_sound (w := (15245988307 / 77745988307)) (n := 12)
    (lo := (397346659 / 1000000000)) (hi := (19867333 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((46495988307 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(46495988307 / 31250000000) = 1/(31250000000 / 46495988307) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6436 : Bounds (397346659 / 1000000000) (19867333 / 50000000) (Real.log (46495988307 / 31250000000)) := by
  have h := reflection_log_6436_neg
  have he : Real.log (46495988307 / 31250000000) = -Real.log (31250000000 / 46495988307) := by
    rw [show ((46495988307 / 31250000000) : ℝ) = ((31250000000 / 46495988307) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6437_neg : (198777331 / 500000000) ≤ -Real.log (250000000000 / 372045284897) ∧
    -Real.log (250000000000 / 372045284897) ≤ (397554663 / 1000000000) := by
  have h := checkLog_sound (w := (122045284897 / 622045284897)) (n := 12)
    (lo := (198777331 / 500000000)) (hi := (397554663 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((372045284897 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(372045284897 / 250000000000) = 1/(250000000000 / 372045284897) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6437 : Bounds (198777331 / 500000000) (397554663 / 1000000000) (Real.log (372045284897 / 250000000000)) := by
  have h := reflection_log_6437_neg
  have he : Real.log (372045284897 / 250000000000) = -Real.log (250000000000 / 372045284897) := by
    rw [show ((372045284897 / 250000000000) : ℝ) = ((250000000000 / 372045284897) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6438_neg : (8961673 / 50000000) ≤ -Real.log (10000 / 11963) ∧
    -Real.log (10000 / 11963) ≤ (179233461 / 1000000000) := by
  have h := checkLog_sound (w := (1963 / 21963)) (n := 12)
    (lo := (8961673 / 50000000)) (hi := (179233461 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11963 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11963 / 10000) = 1/(10000 / 11963) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6438 : Bounds (8961673 / 50000000) (179233461 / 1000000000) (Real.log (11963 / 10000)) := by
  have h := reflection_log_6438_neg
  have he : Real.log (11963 / 10000) = -Real.log (10000 / 11963) := by
    rw [show ((11963 / 10000) : ℝ) = ((10000 / 11963) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6439_neg : (218529213 / 1000000000) ≤ -Real.log (8037 / 10000) ∧
    -Real.log (8037 / 10000) ≤ (109264607 / 500000000) := by
  have h := checkLog_sound (w := (1963 / 18037)) (n := 12)
    (lo := (218529213 / 1000000000)) (hi := (109264607 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8037) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8037) = 1/(8037 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6439 : Bounds (-109264607 / 500000000) (-218529213 / 1000000000) (Real.log (8037 / 10000)) := by
  have h := reflection_log_6439_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6440_neg : (4907 / 25000000) ≤ -Real.log (10000000 / 10001963) ∧
    -Real.log (10000000 / 10001963) ≤ (196281 / 1000000000) := by
  have h := checkLog_sound (w := (1963 / 20001963)) (n := 12)
    (lo := (4907 / 25000000)) (hi := (196281 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001963 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001963 / 10000000) = 1/(10000000 / 10001963) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6440 : Bounds (4907 / 25000000) (196281 / 1000000000) (Real.log (10001963 / 10000000)) := by
  have h := reflection_log_6440_neg
  have he : Real.log (10001963 / 10000000) = -Real.log (10000000 / 10001963) := by
    rw [show ((10001963 / 10000000) : ℝ) = ((10000000 / 10001963) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6441_neg : (196319 / 1000000000) ≤ -Real.log (9998037 / 10000000) ∧
    -Real.log (9998037 / 10000000) ≤ (1227 / 6250000) := by
  have h := checkLog_sound (w := (1963 / 19998037)) (n := 12)
    (lo := (196319 / 1000000000)) (hi := (1227 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998037) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998037) = 1/(9998037 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6441 : Bounds (-1227 / 6250000) (-196319 / 1000000000) (Real.log (9998037 / 10000000)) := by
  have h := reflection_log_6441_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6442_neg : (94119471 / 1000000000) ≤ -Real.log (1000000 / 1098691) ∧
    -Real.log (1000000 / 1098691) ≤ (5882467 / 62500000) := by
  have h := checkLog_sound (w := (98691 / 2098691)) (n := 12)
    (lo := (94119471 / 1000000000)) (hi := (5882467 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1098691 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1098691 / 1000000) = 1/(1000000 / 1098691) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6442 : Bounds (94119471 / 1000000000) (5882467 / 62500000) (Real.log (1098691 / 1000000)) := by
  have h := reflection_log_6442_neg
  have he : Real.log (1098691 / 1000000) = -Real.log (1000000 / 1098691) := by
    rw [show ((1098691 / 1000000) : ℝ) = ((1000000 / 1098691) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6443_neg : (103907127 / 1000000000) ≤ -Real.log (901309 / 1000000) ∧
    -Real.log (901309 / 1000000) ≤ (12988391 / 125000000) := by
  have h := checkLog_sound (w := (98691 / 1901309)) (n := 12)
    (lo := (103907127 / 1000000000)) (hi := (12988391 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 901309) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 901309) = 1/(901309 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6443 : Bounds (-12988391 / 125000000) (-103907127 / 1000000000) (Real.log (901309 / 1000000)) := by
  have h := reflection_log_6443_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6444_neg : (47172129 / 500000000) ≤ -Real.log (500000 / 549469) ∧
    -Real.log (500000 / 549469) ≤ (94344259 / 1000000000) := by
  have h := checkLog_sound (w := (49469 / 1049469)) (n := 12)
    (lo := (47172129 / 500000000)) (hi := (94344259 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((549469 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(549469 / 500000) = 1/(500000 / 549469) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6444 : Bounds (47172129 / 500000000) (94344259 / 1000000000) (Real.log (549469 / 500000)) := by
  have h := reflection_log_6444_neg
  have he : Real.log (549469 / 500000) = -Real.log (500000 / 549469) := by
    rw [show ((549469 / 500000) : ℝ) = ((500000 / 549469) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6445_neg : (104181211 / 1000000000) ≤ -Real.log (450531 / 500000) ∧
    -Real.log (450531 / 500000) ≤ (26045303 / 250000000) := by
  have h := checkLog_sound (w := (49469 / 950531)) (n := 12)
    (lo := (104181211 / 1000000000)) (hi := (26045303 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 450531) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 450531) = 1/(450531 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6445 : Bounds (-26045303 / 250000000) (-104181211 / 1000000000) (Real.log (450531 / 500000)) := by
  have h := reflection_log_6445_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6446_neg : (1229619 / 125000000) ≤ -Real.log (247552818039 / 250000000000) ∧
    -Real.log (247552818039 / 250000000000) ≤ (9836953 / 1000000000) := by
  have h := checkLog_sound (w := (2447181961 / 497552818039)) (n := 12)
    (lo := (1229619 / 125000000)) (hi := (9836953 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247552818039) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247552818039) = 1/(247552818039 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6446 : Bounds (-9836953 / 1000000000) (-1229619 / 125000000) (Real.log (247552818039 / 250000000000)) := by
  have h := reflection_log_6446_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6447_neg : (1223457 / 125000000) ≤ -Real.log (990260086519 / 1000000000000) ∧
    -Real.log (990260086519 / 1000000000000) ≤ (9787657 / 1000000000) := by
  have h := checkLog_sound (w := (9739913481 / 1990260086519)) (n := 12)
    (lo := (1223457 / 125000000)) (hi := (9787657 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 990260086519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 990260086519) = 1/(990260086519 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6447 : Bounds (-9787657 / 1000000000) (-1223457 / 125000000) (Real.log (990260086519 / 1000000000000)) := by
  have h := reflection_log_6447_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6448_neg : (198026599 / 1000000000) ≤ -Real.log (1953125000 / 2380849253) ∧
    -Real.log (1953125000 / 2380849253) ≤ (990133 / 5000000) := by
  have h := checkLog_sound (w := (427724253 / 4333974253)) (n := 12)
    (lo := (198026599 / 1000000000)) (hi := (990133 / 5000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2380849253 / 1953125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2380849253 / 1953125000) = 1/(1953125000 / 2380849253) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6448 : Bounds (198026599 / 1000000000) (990133 / 5000000) (Real.log (2380849253 / 1953125000)) := by
  have h := reflection_log_6448_neg
  have he : Real.log (2380849253 / 1953125000) = -Real.log (1953125000 / 2380849253) := by
    rw [show ((2380849253 / 1953125000) : ℝ) = ((1953125000 / 2380849253) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6449_neg : (19852547 / 100000000) ≤ -Real.log (62500000000 / 76225193161) ∧
    -Real.log (62500000000 / 76225193161) ≤ (198525471 / 1000000000) := by
  have h := checkLog_sound (w := (13725193161 / 138725193161)) (n := 12)
    (lo := (19852547 / 100000000)) (hi := (198525471 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((76225193161 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(76225193161 / 62500000000) = 1/(62500000000 / 76225193161) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6449 : Bounds (19852547 / 100000000) (198525471 / 1000000000) (Real.log (76225193161 / 62500000000)) := by
  have h := reflection_log_6449_neg
  have he : Real.log (76225193161 / 62500000000) = -Real.log (62500000000 / 76225193161) := by
    rw [show ((76225193161 / 62500000000) : ℝ) = ((62500000000 / 76225193161) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6450_neg : (198777331 / 500000000) ≤ -Real.log (500000000000 / 744090569793) ∧
    -Real.log (500000000000 / 744090569793) ≤ (397554663 / 1000000000) := by
  have h := checkLog_sound (w := (244090569793 / 1244090569793)) (n := 12)
    (lo := (198777331 / 500000000)) (hi := (397554663 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((744090569793 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(744090569793 / 500000000000) = 1/(500000000000 / 744090569793) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6450 : Bounds (198777331 / 500000000) (397554663 / 1000000000) (Real.log (744090569793 / 500000000000)) := by
  have h := reflection_log_6450_neg
  have he : Real.log (744090569793 / 500000000000) = -Real.log (500000000000 / 744090569793) := by
    rw [show ((744090569793 / 500000000000) : ℝ) = ((500000000000 / 744090569793) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6451_neg : (397762673 / 1000000000) ≤ -Real.log (500000000000 / 744245365187) ∧
    -Real.log (500000000000 / 744245365187) ≤ (198881337 / 500000000) := by
  have h := checkLog_sound (w := (244245365187 / 1244245365187)) (n := 12)
    (lo := (397762673 / 1000000000)) (hi := (198881337 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((744245365187 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(744245365187 / 500000000000) = 1/(500000000000 / 744245365187) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6451 : Bounds (397762673 / 1000000000) (198881337 / 500000000) (Real.log (744245365187 / 500000000000)) := by
  have h := reflection_log_6451_neg
  have he : Real.log (744245365187 / 500000000000) = -Real.log (500000000000 / 744245365187) := by
    rw [show ((744245365187 / 500000000000) : ℝ) = ((500000000000 / 744245365187) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6452_neg : (179317047 / 1000000000) ≤ -Real.log (2500 / 2991) ∧
    -Real.log (2500 / 2991) ≤ (22414631 / 125000000) := by
  have h := checkLog_sound (w := (491 / 5491)) (n := 12)
    (lo := (179317047 / 1000000000)) (hi := (22414631 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2991 / 2500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2991 / 2500) = 1/(2500 / 2991) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6452 : Bounds (179317047 / 1000000000) (22414631 / 125000000) (Real.log (2991 / 2500)) := by
  have h := reflection_log_6452_neg
  have he : Real.log (2991 / 2500) = -Real.log (2500 / 2991) := by
    rw [show ((2991 / 2500) : ℝ) = ((2500 / 2991) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6453_neg : (109326823 / 500000000) ≤ -Real.log (2009 / 2500) ∧
    -Real.log (2009 / 2500) ≤ (218653647 / 1000000000) := by
  have h := checkLog_sound (w := (491 / 4509)) (n := 12)
    (lo := (109326823 / 500000000)) (hi := (218653647 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500 / 2009) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500 / 2009) = 1/(2009 / 2500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6453 : Bounds (-218653647 / 1000000000) (-109326823 / 500000000) (Real.log (2009 / 2500)) := by
  have h := reflection_log_6453_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6454_neg : (9819 / 50000000) ≤ -Real.log (2500000 / 2500491) ∧
    -Real.log (2500000 / 2500491) ≤ (196381 / 1000000000) := by
  have h := checkLog_sound (w := (491 / 5000491)) (n := 12)
    (lo := (9819 / 50000000)) (hi := (196381 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500491 / 2500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500491 / 2500000) = 1/(2500000 / 2500491) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6454 : Bounds (9819 / 50000000) (196381 / 1000000000) (Real.log (2500491 / 2500000)) := by
  have h := reflection_log_6454_neg
  have he : Real.log (2500491 / 2500000) = -Real.log (2500000 / 2500491) := by
    rw [show ((2500491 / 2500000) : ℝ) = ((2500000 / 2500491) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6455_neg : (196419 / 1000000000) ≤ -Real.log (2499509 / 2500000) ∧
    -Real.log (2499509 / 2500000) ≤ (9821 / 50000000) := by
  have h := checkLog_sound (w := (491 / 4999509)) (n := 12)
    (lo := (196419 / 1000000000)) (hi := (9821 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000 / 2499509) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000 / 2499509) = 1/(2499509 / 2500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6455 : Bounds (-9821 / 50000000) (-196419 / 1000000000) (Real.log (2499509 / 2500000)) := by
  have h := reflection_log_6455_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6456_neg : (735671 / 7812500) ≤ -Real.log (500000 / 549371) ∧
    -Real.log (500000 / 549371) ≤ (94165889 / 1000000000) := by
  have h := checkLog_sound (w := (49371 / 1049371)) (n := 12)
    (lo := (735671 / 7812500)) (hi := (94165889 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((549371 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(549371 / 500000) = 1/(500000 / 549371) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6456 : Bounds (735671 / 7812500) (94165889 / 1000000000) (Real.log (549371 / 500000)) := by
  have h := reflection_log_6456_neg
  have he : Real.log (549371 / 500000) = -Real.log (500000 / 549371) := by
    rw [show ((549371 / 500000) : ℝ) = ((500000 / 549371) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6457_neg : (103963713 / 1000000000) ≤ -Real.log (450629 / 500000) ∧
    -Real.log (450629 / 500000) ≤ (51981857 / 500000000) := by
  have h := checkLog_sound (w := (49371 / 950629)) (n := 12)
    (lo := (103963713 / 1000000000)) (hi := (51981857 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 450629) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 450629) = 1/(450629 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6457 : Bounds (-51981857 / 500000000) (-103963713 / 1000000000) (Real.log (450629 / 500000)) := by
  have h := reflection_log_6457_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6458_neg : (47195333 / 500000000) ≤ -Real.log (1000000 / 1098989) ∧
    -Real.log (1000000 / 1098989) ≤ (94390667 / 1000000000) := by
  have h := checkLog_sound (w := (98989 / 2098989)) (n := 12)
    (lo := (47195333 / 500000000)) (hi := (94390667 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1098989 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1098989 / 1000000) = 1/(1000000 / 1098989) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6458 : Bounds (47195333 / 500000000) (94390667 / 1000000000) (Real.log (1098989 / 1000000)) := by
  have h := reflection_log_6458_neg
  have he : Real.log (1098989 / 1000000) = -Real.log (1000000 / 1098989) := by
    rw [show ((1098989 / 1000000) : ℝ) = ((1000000 / 1098989) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6459_neg : (26059453 / 250000000) ≤ -Real.log (901011 / 1000000) ∧
    -Real.log (901011 / 1000000) ≤ (104237813 / 1000000000) := by
  have h := checkLog_sound (w := (98989 / 1901011)) (n := 12)
    (lo := (26059453 / 250000000)) (hi := (104237813 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 901011) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 901011) = 1/(901011 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6459 : Bounds (-104237813 / 1000000000) (-26059453 / 250000000) (Real.log (901011 / 1000000)) := by
  have h := reflection_log_6459_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6460_neg : (4923573 / 500000000) ≤ -Real.log (990201177879 / 1000000000000) ∧
    -Real.log (990201177879 / 1000000000000) ≤ (9847147 / 1000000000) := by
  have h := checkLog_sound (w := (9798822121 / 1990201177879)) (n := 12)
    (lo := (4923573 / 500000000)) (hi := (9847147 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 990201177879) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 990201177879) = 1/(990201177879 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6460 : Bounds (-9847147 / 1000000000) (-4923573 / 500000000) (Real.log (990201177879 / 1000000000000)) := by
  have h := reflection_log_6460_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6461_neg : (153091 / 15625000) ≤ -Real.log (247562504359 / 250000000000) ∧
    -Real.log (247562504359 / 250000000000) ≤ (391913 / 40000000) := by
  have h := checkLog_sound (w := (2437495641 / 497562504359)) (n := 12)
    (lo := (153091 / 15625000)) (hi := (391913 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247562504359) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247562504359) = 1/(247562504359 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6461 : Bounds (-391913 / 40000000) (-153091 / 15625000) (Real.log (247562504359 / 250000000000)) := by
  have h := reflection_log_6461_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6462_neg : (99064801 / 500000000) ≤ -Real.log (50000000000 / 60956019253) ∧
    -Real.log (50000000000 / 60956019253) ≤ (198129603 / 1000000000) := by
  have h := checkLog_sound (w := (10956019253 / 110956019253)) (n := 12)
    (lo := (99064801 / 500000000)) (hi := (198129603 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((60956019253 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(60956019253 / 50000000000) = 1/(50000000000 / 60956019253) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6462 : Bounds (99064801 / 500000000) (198129603 / 1000000000) (Real.log (60956019253 / 50000000000)) := by
  have h := reflection_log_6462_neg
  have he : Real.log (60956019253 / 50000000000) = -Real.log (50000000000 / 60956019253) := by
    rw [show ((60956019253 / 50000000000) : ℝ) = ((50000000000 / 60956019253) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6463_neg : (198628479 / 1000000000) ≤ -Real.log (500000000000 / 609864363477) ∧
    -Real.log (500000000000 / 609864363477) ≤ (310357 / 1562500) := by
  have h := checkLog_sound (w := (109864363477 / 1109864363477)) (n := 12)
    (lo := (198628479 / 1000000000)) (hi := (310357 / 1562500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((609864363477 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(609864363477 / 500000000000) = 1/(500000000000 / 609864363477) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6463 : Bounds (198628479 / 1000000000) (310357 / 1562500) (Real.log (609864363477 / 500000000000)) := by
  have h := reflection_log_6463_neg
  have he : Real.log (609864363477 / 500000000000) = -Real.log (500000000000 / 609864363477) := by
    rw [show ((609864363477 / 500000000000) : ℝ) = ((500000000000 / 609864363477) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily
