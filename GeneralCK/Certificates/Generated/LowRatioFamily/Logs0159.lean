import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_10176_neg : (184537209 / 1000000000) ≤ -Real.log (831489 / 1000000) ∧
    -Real.log (831489 / 1000000) ≤ (18453721 / 100000000) := by
  have h := checkLog_sound (w := (168511 / 1831489)) (n := 12)
    (lo := (184537209 / 1000000000)) (hi := (18453721 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 831489) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 831489) = 1/(831489 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10176 : Bounds (-18453721 / 100000000) (-184537209 / 1000000000) (Real.log (831489 / 1000000)) := by
  have h := reflection_log_10176_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10177_neg : (720173 / 25000000) ≤ -Real.log (971604042879 / 1000000000000) ∧
    -Real.log (971604042879 / 1000000000000) ≤ (28806921 / 1000000000) := by
  have h := checkLog_sound (w := (28395957121 / 1971604042879)) (n := 12)
    (lo := (720173 / 25000000)) (hi := (28806921 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 971604042879) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 971604042879) = 1/(971604042879 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10177 : Bounds (-28806921 / 1000000000) (-720173 / 25000000) (Real.log (971604042879 / 1000000000000)) := by
  have h := reflection_log_10177_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10178_neg : (28511141 / 1000000000) ≤ -Real.log (15185804151 / 15625000000) ∧
    -Real.log (15185804151 / 15625000000) ≤ (14255571 / 500000000) := by
  have h := checkLog_sound (w := (439195849 / 30810804151)) (n := 12)
    (lo := (28511141 / 1000000000)) (hi := (14255571 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 15185804151) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 15185804151) = 1/(15185804151 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10178 : Bounds (-14255571 / 500000000) (-28511141 / 1000000000) (Real.log (15185804151 / 15625000000)) := by
  have h := reflection_log_10178_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10179_neg : (169253891 / 500000000) ≤ -Real.log (250000000000 / 350713166671) ∧
    -Real.log (250000000000 / 350713166671) ≤ (338507783 / 1000000000) := by
  have h := checkLog_sound (w := (100713166671 / 600713166671)) (n := 12)
    (lo := (169253891 / 500000000)) (hi := (338507783 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((350713166671 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(350713166671 / 250000000000) = 1/(250000000000 / 350713166671) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10179 : Bounds (169253891 / 500000000) (338507783 / 1000000000) (Real.log (350713166671 / 250000000000)) := by
  have h := reflection_log_10179_neg
  have he : Real.log (350713166671 / 250000000000) = -Real.log (250000000000 / 350713166671) := by
    rw [show ((350713166671 / 250000000000) : ℝ) = ((250000000000 / 350713166671) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10180_neg : (170133749 / 500000000) ≤ -Real.log (500000000000 / 702661730943) ∧
    -Real.log (500000000000 / 702661730943) ≤ (340267499 / 1000000000) := by
  have h := checkLog_sound (w := (202661730943 / 1202661730943)) (n := 12)
    (lo := (170133749 / 500000000)) (hi := (340267499 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((702661730943 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(702661730943 / 500000000000) = 1/(500000000000 / 702661730943) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10180 : Bounds (170133749 / 500000000) (340267499 / 1000000000) (Real.log (702661730943 / 500000000000)) := by
  have h := reflection_log_10180_neg
  have he : Real.log (702661730943 / 500000000000) = -Real.log (500000000000 / 702661730943) := by
    rw [show ((702661730943 / 500000000000) : ℝ) = ((500000000000 / 702661730943) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10181_neg : (683412921 / 1000000000) ≤ -Real.log (250000000000 / 495156482861) ∧
    -Real.log (250000000000 / 495156482861) ≤ (341706461 / 500000000) := by
  have h := checkLog_sound (w := (245156482861 / 745156482861)) (n := 12)
    (lo := (683412921 / 1000000000)) (hi := (341706461 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((495156482861 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(495156482861 / 250000000000) = 1/(250000000000 / 495156482861) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10181 : Bounds (683412921 / 1000000000) (341706461 / 500000000) (Real.log (495156482861 / 250000000000)) := by
  have h := reflection_log_10181_neg
  have he : Real.log (495156482861 / 250000000000) = -Real.log (250000000000 / 495156482861) := by
    rw [show ((495156482861 / 250000000000) : ℝ) = ((250000000000 / 495156482861) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10182_neg : (171414127 / 250000000) ≤ -Real.log (500000000000 / 992537313433) ∧
    -Real.log (500000000000 / 992537313433) ≤ (685656509 / 1000000000) := by
  have h := checkLog_sound (w := (492537313433 / 1492537313433)) (n := 12)
    (lo := (171414127 / 250000000)) (hi := (685656509 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((992537313433 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(992537313433 / 500000000000) = 1/(500000000000 / 992537313433) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10182 : Bounds (171414127 / 250000000) (685656509 / 1000000000) (Real.log (992537313433 / 500000000000)) := by
  have h := reflection_log_10182_neg
  have he : Real.log (992537313433 / 500000000000) = -Real.log (500000000000 / 992537313433) := by
    rw [show ((992537313433 / 500000000000) : ℝ) = ((500000000000 / 992537313433) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10183_neg : (285930539 / 1000000000) ≤ -Real.log (1000 / 1331) ∧
    -Real.log (1000 / 1331) ≤ (14296527 / 50000000) := by
  have h := checkLog_sound (w := (331 / 2331)) (n := 12)
    (lo := (285930539 / 1000000000)) (hi := (14296527 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1331 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1331 / 1000) = 1/(1000 / 1331) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10183 : Bounds (285930539 / 1000000000) (14296527 / 50000000) (Real.log (1331 / 1000)) := by
  have h := reflection_log_10183_neg
  have he : Real.log (1331 / 1000) = -Real.log (1000 / 1331) := by
    rw [show ((1331 / 1000) : ℝ) = ((1000 / 1331) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10184_neg : (200985609 / 500000000) ≤ -Real.log (669 / 1000) ∧
    -Real.log (669 / 1000) ≤ (401971219 / 1000000000) := by
  have h := checkLog_sound (w := (331 / 1669)) (n := 12)
    (lo := (200985609 / 500000000)) (hi := (401971219 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 669) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 669) = 1/(669 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10184 : Bounds (-401971219 / 1000000000) (-200985609 / 500000000) (Real.log (669 / 1000)) := by
  have h := reflection_log_10184_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10185_neg : (66189 / 200000000) ≤ -Real.log (1000000 / 1000331) ∧
    -Real.log (1000000 / 1000331) ≤ (165473 / 500000000) := by
  have h := checkLog_sound (w := (331 / 2000331)) (n := 12)
    (lo := (66189 / 200000000)) (hi := (165473 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000331 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000331 / 1000000) = 1/(1000000 / 1000331) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10185 : Bounds (66189 / 200000000) (165473 / 500000000) (Real.log (1000331 / 1000000)) := by
  have h := reflection_log_10185_neg
  have he : Real.log (1000331 / 1000000) = -Real.log (1000000 / 1000331) := by
    rw [show ((1000331 / 1000000) : ℝ) = ((1000000 / 1000331) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10186_neg : (165527 / 500000000) ≤ -Real.log (999669 / 1000000) ∧
    -Real.log (999669 / 1000000) ≤ (66211 / 200000000) := by
  have h := checkLog_sound (w := (331 / 1999669)) (n := 12)
    (lo := (165527 / 500000000)) (hi := (66211 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999669) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999669) = 1/(999669 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10186 : Bounds (-66211 / 200000000) (-165527 / 500000000) (Real.log (999669 / 1000000)) := by
  have h := reflection_log_10186_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10187_neg : (77726059 / 500000000) ≤ -Real.log (500000 / 584093) ∧
    -Real.log (500000 / 584093) ≤ (155452119 / 1000000000) := by
  have h := checkLog_sound (w := (84093 / 1084093)) (n := 12)
    (lo := (77726059 / 500000000)) (hi := (155452119 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((584093 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(584093 / 500000) = 1/(500000 / 584093) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10187 : Bounds (77726059 / 500000000) (155452119 / 1000000000) (Real.log (584093 / 500000)) := by
  have h := reflection_log_10187_neg
  have he : Real.log (584093 / 500000) = -Real.log (500000 / 584093) := by
    rw [show ((584093 / 500000) : ℝ) = ((500000 / 584093) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10188_neg : (9207321 / 50000000) ≤ -Real.log (415907 / 500000) ∧
    -Real.log (415907 / 500000) ≤ (184146421 / 1000000000) := by
  have h := checkLog_sound (w := (84093 / 915907)) (n := 12)
    (lo := (9207321 / 50000000)) (hi := (184146421 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 415907) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 415907) = 1/(415907 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10188 : Bounds (-184146421 / 1000000000) (-9207321 / 50000000) (Real.log (415907 / 500000)) := by
  have h := reflection_log_10188_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10189_neg : (156184609 / 1000000000) ≤ -Real.log (500000 / 584521) ∧
    -Real.log (500000 / 584521) ≤ (15618461 / 100000000) := by
  have h := checkLog_sound (w := (84521 / 1084521)) (n := 12)
    (lo := (156184609 / 1000000000)) (hi := (15618461 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((584521 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(584521 / 500000) = 1/(500000 / 584521) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10189 : Bounds (156184609 / 1000000000) (15618461 / 100000000) (Real.log (584521 / 500000)) := by
  have h := reflection_log_10189_neg
  have he : Real.log (584521 / 500000) = -Real.log (500000 / 584521) := by
    rw [show ((584521 / 500000) : ℝ) = ((500000 / 584521) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10190_neg : (92588013 / 500000000) ≤ -Real.log (415479 / 500000) ∧
    -Real.log (415479 / 500000) ≤ (185176027 / 1000000000) := by
  have h := checkLog_sound (w := (84521 / 915479)) (n := 12)
    (lo := (92588013 / 500000000)) (hi := (185176027 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 415479) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 415479) = 1/(415479 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10190 : Bounds (-185176027 / 1000000000) (-92588013 / 500000000) (Real.log (415479 / 500000)) := by
  have h := reflection_log_10190_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10191_neg : (3623927 / 125000000) ≤ -Real.log (242856200559 / 250000000000) ∧
    -Real.log (242856200559 / 250000000000) ≤ (28991417 / 1000000000) := by
  have h := checkLog_sound (w := (7143799441 / 492856200559)) (n := 12)
    (lo := (3623927 / 125000000)) (hi := (28991417 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 242856200559) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 242856200559) = 1/(242856200559 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10191 : Bounds (-28991417 / 1000000000) (-3623927 / 125000000) (Real.log (242856200559 / 250000000000)) := by
  have h := reflection_log_10191_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10192_neg : (14347151 / 500000000) ≤ -Real.log (242928367351 / 250000000000) ∧
    -Real.log (242928367351 / 250000000000) ≤ (28694303 / 1000000000) := by
  have h := checkLog_sound (w := (7071632649 / 492928367351)) (n := 12)
    (lo := (14347151 / 500000000)) (hi := (28694303 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 242928367351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 242928367351) = 1/(242928367351 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10192 : Bounds (-28694303 / 1000000000) (-14347151 / 500000000) (Real.log (242928367351 / 250000000000)) := by
  have h := reflection_log_10192_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10193_neg : (339598539 / 1000000000) ≤ -Real.log (100000000000 / 140438367231) ∧
    -Real.log (100000000000 / 140438367231) ≤ (16979927 / 50000000) := by
  have h := checkLog_sound (w := (40438367231 / 240438367231)) (n := 12)
    (lo := (339598539 / 1000000000)) (hi := (16979927 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((140438367231 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(140438367231 / 100000000000) = 1/(100000000000 / 140438367231) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10193 : Bounds (339598539 / 1000000000) (16979927 / 50000000) (Real.log (140438367231 / 100000000000)) := by
  have h := reflection_log_10193_neg
  have he : Real.log (140438367231 / 100000000000) = -Real.log (100000000000 / 140438367231) := by
    rw [show ((140438367231 / 100000000000) : ℝ) = ((100000000000 / 140438367231) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10194_neg : (85340159 / 250000000) ≤ -Real.log (500000000000 / 703430257607) ∧
    -Real.log (500000000000 / 703430257607) ≤ (341360637 / 1000000000) := by
  have h := checkLog_sound (w := (203430257607 / 1203430257607)) (n := 12)
    (lo := (85340159 / 250000000)) (hi := (341360637 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((703430257607 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(703430257607 / 500000000000) = 1/(500000000000 / 703430257607) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10194 : Bounds (85340159 / 250000000) (341360637 / 1000000000) (Real.log (703430257607 / 500000000000)) := by
  have h := reflection_log_10194_neg
  have he : Real.log (703430257607 / 500000000000) = -Real.log (500000000000 / 703430257607) := by
    rw [show ((703430257607 / 500000000000) : ℝ) = ((500000000000 / 703430257607) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10195_neg : (171414127 / 250000000) ≤ -Real.log (62500000000 / 124067164179) ∧
    -Real.log (62500000000 / 124067164179) ≤ (685656509 / 1000000000) := by
  have h := checkLog_sound (w := (61567164179 / 186567164179)) (n := 12)
    (lo := (171414127 / 250000000)) (hi := (685656509 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((124067164179 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(124067164179 / 62500000000) = 1/(62500000000 / 124067164179) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10195 : Bounds (171414127 / 250000000) (685656509 / 1000000000) (Real.log (124067164179 / 62500000000)) := by
  have h := reflection_log_10195_neg
  have he : Real.log (124067164179 / 62500000000) = -Real.log (62500000000 / 124067164179) := by
    rw [show ((124067164179 / 62500000000) : ℝ) = ((62500000000 / 124067164179) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10196_neg : (343950879 / 500000000) ≤ -Real.log (3906250000 / 7771627429) ∧
    -Real.log (3906250000 / 7771627429) ≤ (687901759 / 1000000000) := by
  have h := checkLog_sound (w := (3865377429 / 11677877429)) (n := 12)
    (lo := (343950879 / 500000000)) (hi := (687901759 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7771627429 / 3906250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7771627429 / 3906250000) = 1/(3906250000 / 7771627429) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10196 : Bounds (343950879 / 500000000) (687901759 / 1000000000) (Real.log (7771627429 / 3906250000)) := by
  have h := reflection_log_10196_neg
  have he : Real.log (7771627429 / 3906250000) = -Real.log (3906250000 / 7771627429) := by
    rw [show ((7771627429 / 3906250000) : ℝ) = ((3906250000 / 7771627429) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10197_neg : (71670393 / 250000000) ≤ -Real.log (250 / 333) ∧
    -Real.log (250 / 333) ≤ (286681573 / 1000000000) := by
  have h := checkLog_sound (w := (83 / 583)) (n := 12)
    (lo := (71670393 / 250000000)) (hi := (286681573 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((333 / 250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(333 / 250) = 1/(250 / 333) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10197 : Bounds (71670393 / 250000000) (286681573 / 1000000000) (Real.log (333 / 250)) := by
  have h := reflection_log_10197_neg
  have he : Real.log (333 / 250) = -Real.log (250 / 333) := by
    rw [show ((333 / 250) : ℝ) = ((250 / 333) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10198_neg : (80693421 / 200000000) ≤ -Real.log (167 / 250) ∧
    -Real.log (167 / 250) ≤ (201733553 / 500000000) := by
  have h := checkLog_sound (w := (83 / 417)) (n := 12)
    (lo := (80693421 / 200000000)) (hi := (201733553 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250 / 167) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250 / 167) = 1/(167 / 250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10198 : Bounds (-201733553 / 500000000) (-80693421 / 200000000) (Real.log (167 / 250)) := by
  have h := reflection_log_10198_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10199_neg : (41493 / 125000000) ≤ -Real.log (250000 / 250083) ∧
    -Real.log (250000 / 250083) ≤ (66389 / 200000000) := by
  have h := checkLog_sound (w := (83 / 500083)) (n := 12)
    (lo := (41493 / 125000000)) (hi := (66389 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250083 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250083 / 250000) = 1/(250000 / 250083) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10199 : Bounds (41493 / 125000000) (66389 / 200000000) (Real.log (250083 / 250000)) := by
  have h := reflection_log_10199_neg
  have he : Real.log (250083 / 250000) = -Real.log (250000 / 250083) := by
    rw [show ((250083 / 250000) : ℝ) = ((250000 / 250083) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10200_neg : (66411 / 200000000) ≤ -Real.log (249917 / 250000) ∧
    -Real.log (249917 / 250000) ≤ (41507 / 125000000) := by
  have h := checkLog_sound (w := (83 / 499917)) (n := 12)
    (lo := (66411 / 200000000)) (hi := (41507 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 249917) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 249917) = 1/(249917 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10200 : Bounds (-41507 / 125000000) (-66411 / 200000000) (Real.log (249917 / 250000)) := by
  have h := reflection_log_10200_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10201_neg : (31181313 / 200000000) ≤ -Real.log (1000000 / 1168717) ∧
    -Real.log (1000000 / 1168717) ≤ (77953283 / 500000000) := by
  have h := checkLog_sound (w := (168717 / 2168717)) (n := 12)
    (lo := (31181313 / 200000000)) (hi := (77953283 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1168717 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1168717 / 1000000) = 1/(1000000 / 1168717) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10201 : Bounds (31181313 / 200000000) (77953283 / 500000000) (Real.log (1168717 / 1000000)) := by
  have h := reflection_log_10201_neg
  have he : Real.log (1168717 / 1000000) = -Real.log (1000000 / 1168717) := by
    rw [show ((1168717 / 1000000) : ℝ) = ((1000000 / 1168717) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10202_neg : (46196247 / 250000000) ≤ -Real.log (831283 / 1000000) ∧
    -Real.log (831283 / 1000000) ≤ (184784989 / 1000000000) := by
  have h := checkLog_sound (w := (168717 / 1831283)) (n := 12)
    (lo := (46196247 / 250000000)) (hi := (184784989 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 831283) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 831283) = 1/(831283 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10202 : Bounds (-184784989 / 1000000000) (-46196247 / 250000000) (Real.log (831283 / 1000000)) := by
  have h := reflection_log_10202_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10203_neg : (156639579 / 1000000000) ≤ -Real.log (500000 / 584787) ∧
    -Real.log (500000 / 584787) ≤ (7831979 / 50000000) := by
  have h := checkLog_sound (w := (84787 / 1084787)) (n := 12)
    (lo := (156639579 / 1000000000)) (hi := (7831979 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((584787 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(584787 / 500000) = 1/(500000 / 584787) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10203 : Bounds (156639579 / 1000000000) (7831979 / 50000000) (Real.log (584787 / 500000)) := by
  have h := reflection_log_10203_neg
  have he : Real.log (584787 / 500000) = -Real.log (500000 / 584787) := by
    rw [show ((584787 / 500000) : ℝ) = ((500000 / 584787) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10204_neg : (23227057 / 125000000) ≤ -Real.log (415213 / 500000) ∧
    -Real.log (415213 / 500000) ≤ (185816457 / 1000000000) := by
  have h := checkLog_sound (w := (84787 / 915213)) (n := 12)
    (lo := (23227057 / 125000000)) (hi := (185816457 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 415213) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 415213) = 1/(415213 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10204 : Bounds (-185816457 / 1000000000) (-23227057 / 125000000) (Real.log (415213 / 500000)) := by
  have h := reflection_log_10204_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10205_neg : (7294219 / 250000000) ≤ -Real.log (242811164631 / 250000000000) ∧
    -Real.log (242811164631 / 250000000000) ≤ (29176877 / 1000000000) := by
  have h := checkLog_sound (w := (7188835369 / 492811164631)) (n := 12)
    (lo := (7294219 / 250000000)) (hi := (29176877 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 242811164631) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 242811164631) = 1/(242811164631 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10205 : Bounds (-29176877 / 1000000000) (-7294219 / 250000000) (Real.log (242811164631 / 250000000000)) := by
  have h := reflection_log_10205_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10206_neg : (14439211 / 500000000) ≤ -Real.log (971534573911 / 1000000000000) ∧
    -Real.log (971534573911 / 1000000000000) ≤ (28878423 / 1000000000) := by
  have h := checkLog_sound (w := (28465426089 / 1971534573911)) (n := 12)
    (lo := (14439211 / 500000000)) (hi := (28878423 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 971534573911) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 971534573911) = 1/(971534573911 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10206 : Bounds (-28878423 / 1000000000) (-14439211 / 500000000) (Real.log (971534573911 / 1000000000000)) := by
  have h := reflection_log_10206_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10207_neg : (170345777 / 500000000) ≤ -Real.log (250000000000 / 351479881099) ∧
    -Real.log (250000000000 / 351479881099) ≤ (68138311 / 200000000) := by
  have h := checkLog_sound (w := (101479881099 / 601479881099)) (n := 12)
    (lo := (170345777 / 500000000)) (hi := (68138311 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((351479881099 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(351479881099 / 250000000000) = 1/(250000000000 / 351479881099) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10207 : Bounds (170345777 / 500000000) (68138311 / 200000000) (Real.log (351479881099 / 250000000000)) := by
  have h := reflection_log_10207_neg
  have he : Real.log (351479881099 / 250000000000) = -Real.log (250000000000 / 351479881099) := by
    rw [show ((351479881099 / 250000000000) : ℝ) = ((250000000000 / 351479881099) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10208_neg : (85614009 / 250000000) ≤ -Real.log (500000000000 / 704201217207) ∧
    -Real.log (500000000000 / 704201217207) ≤ (342456037 / 1000000000) := by
  have h := checkLog_sound (w := (204201217207 / 1204201217207)) (n := 12)
    (lo := (85614009 / 250000000)) (hi := (342456037 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((704201217207 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(704201217207 / 500000000000) = 1/(500000000000 / 704201217207) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10208 : Bounds (85614009 / 250000000) (342456037 / 1000000000) (Real.log (704201217207 / 500000000000)) := by
  have h := reflection_log_10208_neg
  have he : Real.log (704201217207 / 500000000000) = -Real.log (500000000000 / 704201217207) := by
    rw [show ((704201217207 / 500000000000) : ℝ) = ((500000000000 / 704201217207) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10209_neg : (343950879 / 500000000) ≤ -Real.log (500000000000 / 994768310911) ∧
    -Real.log (500000000000 / 994768310911) ≤ (687901759 / 1000000000) := by
  have h := checkLog_sound (w := (494768310911 / 1494768310911)) (n := 12)
    (lo := (343950879 / 500000000)) (hi := (687901759 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((994768310911 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(994768310911 / 500000000000) = 1/(500000000000 / 994768310911) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10209 : Bounds (343950879 / 500000000) (687901759 / 1000000000) (Real.log (994768310911 / 500000000000)) := by
  have h := reflection_log_10209_neg
  have he : Real.log (994768310911 / 500000000000) = -Real.log (500000000000 / 994768310911) := by
    rw [show ((994768310911 / 500000000000) : ℝ) = ((500000000000 / 994768310911) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10210_neg : (690148677 / 1000000000) ≤ -Real.log (62500000000 / 124625748503) ∧
    -Real.log (62500000000 / 124625748503) ≤ (345074339 / 500000000) := by
  have h := checkLog_sound (w := (62125748503 / 187125748503)) (n := 12)
    (lo := (690148677 / 1000000000)) (hi := (345074339 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((124625748503 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(124625748503 / 62500000000) = 1/(62500000000 / 124625748503) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10210 : Bounds (690148677 / 1000000000) (345074339 / 500000000) (Real.log (124625748503 / 62500000000)) := by
  have h := reflection_log_10210_neg
  have he : Real.log (124625748503 / 62500000000) = -Real.log (62500000000 / 124625748503) := by
    rw [show ((124625748503 / 62500000000) : ℝ) = ((62500000000 / 124625748503) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10211_neg : (287432041 / 1000000000) ≤ -Real.log (1000 / 1333) ∧
    -Real.log (1000 / 1333) ≤ (143716021 / 500000000) := by
  have h := checkLog_sound (w := (333 / 2333)) (n := 12)
    (lo := (287432041 / 1000000000)) (hi := (143716021 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1333 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1333 / 1000) = 1/(1000 / 1333) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10211 : Bounds (287432041 / 1000000000) (143716021 / 500000000) (Real.log (1333 / 1000)) := by
  have h := reflection_log_10211_neg
  have he : Real.log (1333 / 1000) = -Real.log (1000 / 1333) := by
    rw [show ((1333 / 1000) : ℝ) = ((1000 / 1333) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10212_neg : (404965233 / 1000000000) ≤ -Real.log (667 / 1000) ∧
    -Real.log (667 / 1000) ≤ (202482617 / 500000000) := by
  have h := checkLog_sound (w := (333 / 1667)) (n := 12)
    (lo := (404965233 / 1000000000)) (hi := (202482617 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 667) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 667) = 1/(667 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10212 : Bounds (-202482617 / 500000000) (-404965233 / 1000000000) (Real.log (667 / 1000)) := by
  have h := reflection_log_10212_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10213_neg : (20809 / 62500000) ≤ -Real.log (1000000 / 1000333) ∧
    -Real.log (1000000 / 1000333) ≤ (66589 / 200000000) := by
  have h := checkLog_sound (w := (333 / 2000333)) (n := 12)
    (lo := (20809 / 62500000)) (hi := (66589 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000333 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000333 / 1000000) = 1/(1000000 / 1000333) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10213 : Bounds (20809 / 62500000) (66589 / 200000000) (Real.log (1000333 / 1000000)) := by
  have h := reflection_log_10213_neg
  have he : Real.log (1000333 / 1000000) = -Real.log (1000000 / 1000333) := by
    rw [show ((1000333 / 1000000) : ℝ) = ((1000000 / 1000333) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10214_neg : (66611 / 200000000) ≤ -Real.log (999667 / 1000000) ∧
    -Real.log (999667 / 1000000) ≤ (1301 / 3906250) := by
  have h := checkLog_sound (w := (333 / 1999667)) (n := 12)
    (lo := (66611 / 200000000)) (hi := (1301 / 3906250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999667) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999667) = 1/(999667 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10214 : Bounds (-1301 / 3906250) (-66611 / 200000000) (Real.log (999667 / 1000000)) := by
  have h := reflection_log_10214_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10215_neg : (156360807 / 1000000000) ≤ -Real.log (31250 / 36539) ∧
    -Real.log (31250 / 36539) ≤ (19545101 / 125000000) := by
  have h := checkLog_sound (w := (5289 / 67789)) (n := 12)
    (lo := (156360807 / 1000000000)) (hi := (19545101 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((36539 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(36539 / 31250) = 1/(31250 / 36539) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10215 : Bounds (156360807 / 1000000000) (19545101 / 125000000) (Real.log (36539 / 31250)) := by
  have h := reflection_log_10215_neg
  have he : Real.log (36539 / 31250) = -Real.log (31250 / 36539) := by
    rw [show ((36539 / 31250) : ℝ) = ((31250 / 36539) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10216_neg : (46355991 / 250000000) ≤ -Real.log (25961 / 31250) ∧
    -Real.log (25961 / 31250) ≤ (37084793 / 200000000) := by
  have h := checkLog_sound (w := (5289 / 57211)) (n := 12)
    (lo := (46355991 / 250000000)) (hi := (37084793 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 25961) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31250 / 25961) = 1/(25961 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10216 : Bounds (-37084793 / 200000000) (-46355991 / 250000000) (Real.log (25961 / 31250)) := by
  have h := reflection_log_10216_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10217_neg : (78547171 / 500000000) ≤ -Real.log (500000 / 585053) ∧
    -Real.log (500000 / 585053) ≤ (157094343 / 1000000000) := by
  have h := checkLog_sound (w := (85053 / 1085053)) (n := 12)
    (lo := (78547171 / 500000000)) (hi := (157094343 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((585053 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(585053 / 500000) = 1/(500000 / 585053) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10217 : Bounds (78547171 / 500000000) (157094343 / 1000000000) (Real.log (585053 / 500000)) := by
  have h := reflection_log_10217_neg
  have he : Real.log (585053 / 500000) = -Real.log (500000 / 585053) := by
    rw [show ((585053 / 500000) : ℝ) = ((500000 / 585053) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10218_neg : (186457297 / 1000000000) ≤ -Real.log (414947 / 500000) ∧
    -Real.log (414947 / 500000) ≤ (93228649 / 500000000) := by
  have h := checkLog_sound (w := (85053 / 914947)) (n := 12)
    (lo := (186457297 / 1000000000)) (hi := (93228649 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 414947) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 414947) = 1/(414947 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10218 : Bounds (-93228649 / 500000000) (-186457297 / 1000000000) (Real.log (414947 / 500000)) := by
  have h := reflection_log_10218_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10219_neg : (14681477 / 500000000) ≤ -Real.log (242765987191 / 250000000000) ∧
    -Real.log (242765987191 / 250000000000) ≤ (5872591 / 200000000) := by
  have h := checkLog_sound (w := (7234012809 / 492765987191)) (n := 12)
    (lo := (14681477 / 500000000)) (hi := (5872591 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 242765987191) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 242765987191) = 1/(242765987191 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10219 : Bounds (-5872591 / 200000000) (-14681477 / 500000000) (Real.log (242765987191 / 250000000000)) := by
  have h := reflection_log_10219_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10220_neg : (29063157 / 1000000000) ≤ -Real.log (948588979 / 976562500) ∧
    -Real.log (948588979 / 976562500) ≤ (14531579 / 500000000) := by
  have h := checkLog_sound (w := (27973521 / 1925151479)) (n := 12)
    (lo := (29063157 / 1000000000)) (hi := (14531579 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((976562500 / 948588979) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(976562500 / 948588979) = 1/(948588979 / 976562500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10220 : Bounds (-14531579 / 500000000) (-29063157 / 1000000000) (Real.log (948588979 / 976562500)) := by
  have h := reflection_log_10220_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10221_neg : (341784771 / 1000000000) ≤ -Real.log (500000000000 / 703728669927) ∧
    -Real.log (500000000000 / 703728669927) ≤ (85446193 / 250000000) := by
  have h := checkLog_sound (w := (203728669927 / 1203728669927)) (n := 12)
    (lo := (341784771 / 1000000000)) (hi := (85446193 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((703728669927 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(703728669927 / 500000000000) = 1/(500000000000 / 703728669927) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10221 : Bounds (341784771 / 1000000000) (85446193 / 250000000) (Real.log (703728669927 / 500000000000)) := by
  have h := reflection_log_10221_neg
  have he : Real.log (703728669927 / 500000000000) = -Real.log (500000000000 / 703728669927) := by
    rw [show ((703728669927 / 500000000000) : ℝ) = ((500000000000 / 703728669927) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10222_neg : (8588791 / 25000000) ≤ -Real.log (7812500000 / 11015205707) ∧
    -Real.log (7812500000 / 11015205707) ≤ (343551641 / 1000000000) := by
  have h := checkLog_sound (w := (3202705707 / 18827705707)) (n := 12)
    (lo := (8588791 / 25000000)) (hi := (343551641 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11015205707 / 7812500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11015205707 / 7812500000) = 1/(7812500000 / 11015205707) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10222 : Bounds (8588791 / 25000000) (343551641 / 1000000000) (Real.log (11015205707 / 7812500000)) := by
  have h := reflection_log_10222_neg
  have he : Real.log (11015205707 / 7812500000) = -Real.log (7812500000 / 11015205707) := by
    rw [show ((11015205707 / 7812500000) : ℝ) = ((7812500000 / 11015205707) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10223_neg : (690148677 / 1000000000) ≤ -Real.log (500000000000 / 997005988023) ∧
    -Real.log (500000000000 / 997005988023) ≤ (345074339 / 500000000) := by
  have h := checkLog_sound (w := (497005988023 / 1497005988023)) (n := 12)
    (lo := (690148677 / 1000000000)) (hi := (345074339 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((997005988023 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(997005988023 / 500000000000) = 1/(500000000000 / 997005988023) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10223 : Bounds (690148677 / 1000000000) (345074339 / 500000000) (Real.log (997005988023 / 500000000000)) := by
  have h := reflection_log_10223_neg
  have he : Real.log (997005988023 / 500000000000) = -Real.log (500000000000 / 997005988023) := by
    rw [show ((997005988023 / 500000000000) : ℝ) = ((500000000000 / 997005988023) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10224_neg : (346198637 / 500000000) ≤ -Real.log (500000000000 / 999250374813) ∧
    -Real.log (500000000000 / 999250374813) ≤ (27695891 / 40000000) := by
  have h := checkLog_sound (w := (499250374813 / 1499250374813)) (n := 12)
    (lo := (346198637 / 500000000)) (hi := (27695891 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((999250374813 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(999250374813 / 500000000000) = 1/(500000000000 / 999250374813) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10224 : Bounds (346198637 / 500000000) (27695891 / 40000000) (Real.log (999250374813 / 500000000000)) := by
  have h := reflection_log_10224_neg
  have he : Real.log (999250374813 / 500000000000) = -Real.log (500000000000 / 999250374813) := by
    rw [show ((999250374813 / 500000000000) : ℝ) = ((500000000000 / 999250374813) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10225_neg : (288181947 / 1000000000) ≤ -Real.log (500 / 667) ∧
    -Real.log (500 / 667) ≤ (72045487 / 250000000) := by
  have h := checkLog_sound (w := (167 / 1167)) (n := 12)
    (lo := (288181947 / 1000000000)) (hi := (72045487 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((667 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(667 / 500) = 1/(500 / 667) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10225 : Bounds (288181947 / 1000000000) (72045487 / 250000000) (Real.log (667 / 500)) := by
  have h := reflection_log_10225_neg
  have he : Real.log (667 / 500) = -Real.log (500 / 667) := by
    rw [show ((667 / 500) : ℝ) = ((500 / 667) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10226_neg : (50808201 / 125000000) ≤ -Real.log (333 / 500) ∧
    -Real.log (333 / 500) ≤ (406465609 / 1000000000) := by
  have h := checkLog_sound (w := (167 / 833)) (n := 12)
    (lo := (50808201 / 125000000)) (hi := (406465609 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 333) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500 / 333) = 1/(333 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10226 : Bounds (-406465609 / 1000000000) (-50808201 / 125000000) (Real.log (333 / 500)) := by
  have h := reflection_log_10226_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10227_neg : (41743 / 125000000) ≤ -Real.log (500000 / 500167) ∧
    -Real.log (500000 / 500167) ≤ (66789 / 200000000) := by
  have h := checkLog_sound (w := (167 / 1000167)) (n := 12)
    (lo := (41743 / 125000000)) (hi := (66789 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500167 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500167 / 500000) = 1/(500000 / 500167) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10227 : Bounds (41743 / 125000000) (66789 / 200000000) (Real.log (500167 / 500000)) := by
  have h := reflection_log_10227_neg
  have he : Real.log (500167 / 500000) = -Real.log (500000 / 500167) := by
    rw [show ((500167 / 500000) : ℝ) = ((500000 / 500167) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10228_neg : (66811 / 200000000) ≤ -Real.log (499833 / 500000) ∧
    -Real.log (499833 / 500000) ≤ (41757 / 125000000) := by
  have h := checkLog_sound (w := (167 / 999833)) (n := 12)
    (lo := (66811 / 200000000)) (hi := (41757 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499833) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499833) = 1/(499833 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10228 : Bounds (-41757 / 125000000) (-66811 / 200000000) (Real.log (499833 / 500000)) := by
  have h := reflection_log_10228_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10229_neg : (78407421 / 500000000) ≤ -Real.log (1000000 / 1169779) ∧
    -Real.log (1000000 / 1169779) ≤ (156814843 / 1000000000) := by
  have h := checkLog_sound (w := (169779 / 2169779)) (n := 12)
    (lo := (78407421 / 500000000)) (hi := (156814843 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1169779 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1169779 / 1000000) = 1/(1000000 / 1169779) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10229 : Bounds (78407421 / 500000000) (156814843 / 1000000000) (Real.log (1169779 / 1000000)) := by
  have h := reflection_log_10229_neg
  have he : Real.log (1169779 / 1000000) = -Real.log (1000000 / 1169779) := by
    rw [show ((1169779 / 1000000) : ℝ) = ((1000000 / 1169779) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10230_neg : (46515837 / 250000000) ≤ -Real.log (830221 / 1000000) ∧
    -Real.log (830221 / 1000000) ≤ (186063349 / 1000000000) := by
  have h := checkLog_sound (w := (169779 / 1830221)) (n := 12)
    (lo := (46515837 / 250000000)) (hi := (186063349 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 830221) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 830221) = 1/(830221 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10230 : Bounds (-186063349 / 1000000000) (-46515837 / 250000000) (Real.log (830221 / 1000000)) := by
  have h := reflection_log_10230_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10231_neg : (157549753 / 1000000000) ≤ -Real.log (1000000 / 1170639) ∧
    -Real.log (1000000 / 1170639) ≤ (78774877 / 500000000) := by
  have h := checkLog_sound (w := (170639 / 2170639)) (n := 12)
    (lo := (157549753 / 1000000000)) (hi := (78774877 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1170639 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1170639 / 1000000) = 1/(1000000 / 1170639) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10231 : Bounds (157549753 / 1000000000) (78774877 / 500000000) (Real.log (1170639 / 1000000)) := by
  have h := reflection_log_10231_neg
  have he : Real.log (1170639 / 1000000) = -Real.log (1000000 / 1170639) := by
    rw [show ((1170639 / 1000000) : ℝ) = ((1000000 / 1170639) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10232_neg : (93549877 / 500000000) ≤ -Real.log (829361 / 1000000) ∧
    -Real.log (829361 / 1000000) ≤ (37419951 / 200000000) := by
  have h := checkLog_sound (w := (170639 / 1829361)) (n := 12)
    (lo := (93549877 / 500000000)) (hi := (37419951 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 829361) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 829361) = 1/(829361 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10232 : Bounds (-37419951 / 200000000) (-93549877 / 500000000) (Real.log (829361 / 1000000)) := by
  have h := reflection_log_10232_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10233_neg : (591 / 20000) ≤ -Real.log (970882331679 / 1000000000000) ∧
    -Real.log (970882331679 / 1000000000000) ≤ (29550001 / 1000000000) := by
  have h := checkLog_sound (w := (29117668321 / 1970882331679)) (n := 12)
    (lo := (591 / 20000)) (hi := (29550001 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 970882331679) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 970882331679) = 1/(970882331679 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10233 : Bounds (-29550001 / 1000000000) (-591 / 20000) (Real.log (970882331679 / 1000000000000)) := by
  have h := reflection_log_10233_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10234_neg : (14624253 / 500000000) ≤ -Real.log (971175091159 / 1000000000000) ∧
    -Real.log (971175091159 / 1000000000000) ≤ (29248507 / 1000000000) := by
  have h := checkLog_sound (w := (28824908841 / 1971175091159)) (n := 12)
    (lo := (14624253 / 500000000)) (hi := (29248507 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 971175091159) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 971175091159) = 1/(971175091159 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10234 : Bounds (-29248507 / 1000000000) (-14624253 / 500000000) (Real.log (971175091159 / 1000000000000)) := by
  have h := reflection_log_10234_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10235_neg : (34287819 / 100000000) ≤ -Real.log (250000000000 / 352249280613) ∧
    -Real.log (250000000000 / 352249280613) ≤ (342878191 / 1000000000) := by
  have h := checkLog_sound (w := (102249280613 / 602249280613)) (n := 12)
    (lo := (34287819 / 100000000)) (hi := (342878191 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((352249280613 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(352249280613 / 250000000000) = 1/(250000000000 / 352249280613) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10235 : Bounds (34287819 / 100000000) (342878191 / 1000000000) (Real.log (352249280613 / 250000000000)) := by
  have h := reflection_log_10235_neg
  have he : Real.log (352249280613 / 250000000000) = -Real.log (250000000000 / 352249280613) := by
    rw [show ((352249280613 / 250000000000) : ℝ) = ((250000000000 / 352249280613) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10236_neg : (344649507 / 1000000000) ≤ -Real.log (500000000000 / 705747557457) ∧
    -Real.log (500000000000 / 705747557457) ≤ (86162377 / 250000000) := by
  have h := checkLog_sound (w := (205747557457 / 1205747557457)) (n := 12)
    (lo := (344649507 / 1000000000)) (hi := (86162377 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((705747557457 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(705747557457 / 500000000000) = 1/(500000000000 / 705747557457) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10236 : Bounds (344649507 / 1000000000) (86162377 / 250000000) (Real.log (705747557457 / 500000000000)) := by
  have h := reflection_log_10236_neg
  have he : Real.log (705747557457 / 500000000000) = -Real.log (500000000000 / 705747557457) := by
    rw [show ((705747557457 / 500000000000) : ℝ) = ((500000000000 / 705747557457) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10237_neg : (346198637 / 500000000) ≤ -Real.log (125000000000 / 249812593703) ∧
    -Real.log (125000000000 / 249812593703) ≤ (27695891 / 40000000) := by
  have h := checkLog_sound (w := (124812593703 / 374812593703)) (n := 12)
    (lo := (346198637 / 500000000)) (hi := (27695891 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((249812593703 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(249812593703 / 125000000000) = 1/(125000000000 / 249812593703) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10237 : Bounds (346198637 / 500000000) (27695891 / 40000000) (Real.log (249812593703 / 125000000000)) := by
  have h := reflection_log_10237_neg
  have he : Real.log (249812593703 / 125000000000) = -Real.log (125000000000 / 249812593703) := by
    rw [show ((249812593703 / 125000000000) : ℝ) = ((125000000000 / 249812593703) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10238_neg : (138929511 / 200000000) ≤ -Real.log (250000000000 / 500750750751) ∧
    -Real.log (250000000000 / 500750750751) ≤ (694647557 / 1000000000) := by
  have h := checkLog_sound (w := (750750751 / 1000750750751)) (n := 12)
    (lo := (12003 / 8000000)) (hi := (187547 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500750750751 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500750750751 / 500000000000) = 1/(250000000000 / 500750750751) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10238 : Bounds (138929511 / 200000000) (694647557 / 1000000000) (Real.log (500750750751 / 250000000000)) := by
  have h := reflection_log_10238_neg
  have he : Real.log (500750750751 / 250000000000) = -Real.log (250000000000 / 500750750751) := by
    rw [show ((500750750751 / 250000000000) : ℝ) = ((250000000000 / 500750750751) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10239_neg : (288931291 / 1000000000) ≤ -Real.log (200 / 267) ∧
    -Real.log (200 / 267) ≤ (72232823 / 250000000) := by
  have h := checkLog_sound (w := (67 / 467)) (n := 12)
    (lo := (288931291 / 1000000000)) (hi := (72232823 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((267 / 200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(267 / 200) = 1/(200 / 267) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10239 : Bounds (288931291 / 1000000000) (72232823 / 250000000) (Real.log (267 / 200)) := by
  have h := reflection_log_10239_neg
  have he : Real.log (267 / 200) = -Real.log (200 / 267) := by
    rw [show ((267 / 200) : ℝ) = ((200 / 267) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily
