import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0024
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

theorem reflection_log_1_neg : (136300499 / 200000000) ≤ -Real.log (102400 / 202429) ∧
    -Real.log (102400 / 202429) ≤ (21296953 / 31250000) := by
  have h := checkLog_sound (w := (100029 / 304829)) (n := 12)
    (lo := (136300499 / 200000000)) (hi := (21296953 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((202429 / 102400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(202429 / 102400) = 1/(102400 / 202429) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (136300499 / 200000000) (21296953 / 31250000) (Real.log (202429 / 102400)) := by
  have h := reflection_log_1_neg
  have he : Real.log (202429 / 102400) = -Real.log (102400 / 202429) := by
    rw [show ((202429 / 102400) : ℝ) = ((102400 / 202429) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (1882787451 / 500000000) ≤ -Real.log (2371 / 102400) ∧
    -Real.log (2371 / 102400) ≤ (941393727 / 250000000) := by
  have h := checkLog_sound (w := (829 / 5571)) (n := 12)
    (lo := (149919501 / 500000000)) (hi := (299839003 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2371) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3200 / 2371) = 1/(2371 / 102400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-941393727 / 250000000) (-1882787451 / 500000000) (Real.log (2371 / 102400)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (68140863 / 100000000) ≤ -Real.log (10240 / 20241) ∧
    -Real.log (10240 / 20241) ≤ (681408631 / 1000000000) := by
  have h := checkLog_sound (w := (10001 / 30481)) (n := 12)
    (lo := (68140863 / 100000000)) (hi := (681408631 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20241 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20241 / 10240) = 1/(10240 / 20241) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (68140863 / 100000000) (681408631 / 1000000000) (Real.log (20241 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (20241 / 10240) = -Real.log (10240 / 20241) := by
    rw [show ((20241 / 10240) : ℝ) = ((10240 / 20241) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (3757593343 / 1000000000) ≤ -Real.log (239 / 10240) ∧
    -Real.log (239 / 10240) ≤ (3757593349 / 1000000000) := by
  have h := checkLog_sound (w := (81 / 559)) (n := 12)
    (lo := (291857443 / 1000000000)) (hi := (72964361 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 239) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(320 / 239) = 1/(239 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-3757593349 / 1000000000) (-3757593343 / 1000000000) (Real.log (239 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (669720611 / 1000000000) ≤ -Real.log (51200 / 100029) ∧
    -Real.log (51200 / 100029) ≤ (167430153 / 250000000) := by
  have h := checkLog_sound (w := (48829 / 151229)) (n := 12)
    (lo := (669720611 / 1000000000)) (hi := (167430153 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100029 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100029 / 51200) = 1/(51200 / 100029) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (669720611 / 1000000000) (167430153 / 250000000) (Real.log (100029 / 51200)) := by
  have h := reflection_log_5_neg
  have he : Real.log (100029 / 51200) = -Real.log (51200 / 100029) := by
    rw [show ((100029 / 51200) : ℝ) = ((51200 / 100029) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1536213861 / 500000000) ≤ -Real.log (2371 / 51200) ∧
    -Real.log (2371 / 51200) ≤ (3072427727 / 1000000000) := by
  have h := checkLog_sound (w := (829 / 5571)) (n := 12)
    (lo := (149919501 / 500000000)) (hi := (299839003 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2371) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3200 / 2371) = 1/(2371 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-3072427727 / 1000000000) (-1536213861 / 500000000) (Real.log (2371 / 51200)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (83691331 / 125000000) ≤ -Real.log (5120 / 10001) ∧
    -Real.log (5120 / 10001) ≤ (669530649 / 1000000000) := by
  have h := checkLog_sound (w := (4881 / 15121)) (n := 12)
    (lo := (83691331 / 125000000)) (hi := (669530649 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001 / 5120) = 1/(5120 / 10001) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (83691331 / 125000000) (669530649 / 1000000000) (Real.log (10001 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (10001 / 5120) = -Real.log (5120 / 10001) := by
    rw [show ((10001 / 5120) : ℝ) = ((5120 / 10001) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (3064446163 / 1000000000) ≤ -Real.log (239 / 5120) ∧
    -Real.log (239 / 5120) ≤ (383055771 / 125000000) := by
  have h := checkLog_sound (w := (81 / 559)) (n := 12)
    (lo := (291857443 / 1000000000)) (hi := (72964361 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 239) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(320 / 239) = 1/(239 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-383055771 / 125000000) (-3064446163 / 1000000000) (Real.log (239 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (683232189 / 1000000000) ≤ -Real.log (250000 / 495067) ∧
    -Real.log (250000 / 495067) ≤ (68323219 / 100000000) := by
  have h := checkLog_sound (w := (245067 / 745067)) (n := 12)
    (lo := (683232189 / 1000000000)) (hi := (68323219 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((495067 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(495067 / 250000) = 1/(250000 / 495067) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (683232189 / 1000000000) (68323219 / 100000000) (Real.log (495067 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (495067 / 250000) = -Real.log (250000 / 495067) := by
    rw [show ((495067 / 250000) : ℝ) = ((250000 / 495067) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (490689199 / 125000000) ≤ -Real.log (4933 / 250000) ∧
    -Real.log (4933 / 250000) ≤ (1962756799 / 500000000) := by
  have h := checkLog_sound (w := (5759 / 25491)) (n := 12)
    (lo := (114944423 / 250000000)) (hi := (459777693 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 9866) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 9866) = 1/(4933 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-1962756799 / 500000000) (-490689199 / 125000000) (Real.log (4933 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (341654219 / 500000000) ≤ -Real.log (1000000 / 1980419) ∧
    -Real.log (1000000 / 1980419) ≤ (683308439 / 1000000000) := by
  have h := checkLog_sound (w := (980419 / 2980419)) (n := 12)
    (lo := (341654219 / 500000000)) (hi := (683308439 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1980419 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1980419 / 1000000) = 1/(1000000 / 1980419) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (341654219 / 500000000) (683308439 / 1000000000) (Real.log (1980419 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1980419 / 1000000) = -Real.log (1000000 / 1980419) := by
    rw [show ((1980419 / 1000000) : ℝ) = ((1000000 / 1980419) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (3933195567 / 1000000000) ≤ -Real.log (19581 / 1000000) ∧
    -Real.log (19581 / 1000000) ≤ (3933195573 / 1000000000) := by
  have h := checkLog_sound (w := (11669 / 50831)) (n := 12)
    (lo := (467459667 / 1000000000)) (hi := (116864917 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 19581) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 19581) = 1/(19581 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-3933195573 / 1000000000) (-3933195567 / 1000000000) (Real.log (19581 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (341594127 / 500000000) ≤ -Real.log (1000000 / 1980181) ∧
    -Real.log (1000000 / 1980181) ≤ (136637651 / 200000000) := by
  have h := checkLog_sound (w := (980181 / 2980181)) (n := 12)
    (lo := (341594127 / 500000000)) (hi := (136637651 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1980181 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1980181 / 1000000) = 1/(1000000 / 1980181) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (341594127 / 500000000) (136637651 / 200000000) (Real.log (1980181 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1980181 / 1000000) = -Real.log (1000000 / 1980181) := by
    rw [show ((1980181 / 1000000) : ℝ) = ((1000000 / 1980181) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (1960557101 / 500000000) ≤ -Real.log (19819 / 1000000) ∧
    -Real.log (19819 / 1000000) ≤ (122534819 / 31250000) := by
  have h := checkLog_sound (w := (11431 / 51069)) (n := 12)
    (lo := (227689151 / 500000000)) (hi := (455378303 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 19819) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 19819) = 1/(19819 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-122534819 / 31250000) (-1960557101 / 500000000) (Real.log (19819 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (683265517 / 1000000000) ≤ -Real.log (500000 / 990167) ∧
    -Real.log (500000 / 990167) ≤ (341632759 / 500000000) := by
  have h := checkLog_sound (w := (490167 / 1490167)) (n := 12)
    (lo := (683265517 / 1000000000)) (hi := (341632759 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((990167 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(990167 / 500000) = 1/(500000 / 990167) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (683265517 / 1000000000) (341632759 / 500000000) (Real.log (990167 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (990167 / 500000) = -Real.log (500000 / 990167) := by
    rw [show ((990167 / 500000) : ℝ) = ((500000 / 990167) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (3928864019 / 1000000000) ≤ -Real.log (9833 / 500000) ∧
    -Real.log (9833 / 500000) ≤ (157154561 / 40000000) := by
  have h := checkLog_sound (w := (2896 / 12729)) (n := 12)
    (lo := (463128119 / 1000000000)) (hi := (11578203 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 9833) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 9833) = 1/(9833 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-157154561 / 40000000) (-3928864019 / 1000000000) (Real.log (9833 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (4608745781 / 1000000000) ≤ -Real.log (100000000000 / 10035819987837) ∧
    -Real.log (100000000000 / 10035819987837) ≤ (1152186447 / 250000000) := by
  have h := checkLog_sound (w := (3635819987837 / 16435819987837)) (n := 12)
    (lo := (449862701 / 1000000000)) (hi := (224931351 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10035819987837 / 6400000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(10035819987837 / 6400000000000) = 1/(100000000000 / 10035819987837) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (4608745781 / 1000000000) (1152186447 / 250000000) (Real.log (10035819987837 / 100000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (10035819987837 / 100000000000) = -Real.log (100000000000 / 10035819987837) := by
    rw [show ((10035819987837 / 100000000000) : ℝ) = ((100000000000 / 10035819987837) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (923300801 / 200000000) ≤ -Real.log (500000000000 / 50569914713243) ∧
    -Real.log (500000000000 / 50569914713243) ≤ (1154126003 / 250000000) := by
  have h := checkLog_sound (w := (18569914713243 / 82569914713243)) (n := 12)
    (lo := (18304837 / 40000000)) (hi := (228810463 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50569914713243 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(50569914713243 / 32000000000000) = 1/(500000000000 / 50569914713243) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (923300801 / 200000000) (1154126003 / 250000000) (Real.log (50569914713243 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (50569914713243 / 500000000000) = -Real.log (500000000000 / 50569914713243) := by
    rw [show ((50569914713243 / 500000000000) : ℝ) = ((500000000000 / 50569914713243) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (575537807 / 125000000) ≤ -Real.log (100000000000 / 9991326504869) ∧
    -Real.log (100000000000 / 9991326504869) ≤ (4604302463 / 1000000000) := by
  have h := checkLog_sound (w := (3591326504869 / 16391326504869)) (n := 12)
    (lo := (27838711 / 62500000)) (hi := (445419377 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9991326504869 / 6400000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(9991326504869 / 6400000000000) = 1/(100000000000 / 9991326504869) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (575537807 / 125000000) (4604302463 / 1000000000) (Real.log (9991326504869 / 100000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (9991326504869 / 100000000000) = -Real.log (100000000000 / 9991326504869) := by
    rw [show ((9991326504869 / 100000000000) : ℝ) = ((100000000000 / 9991326504869) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (18016131 / 3906250) ≤ -Real.log (500000000000 / 50349181328181) ∧
    -Real.log (500000000000 / 50349181328181) ≤ (4612129543 / 1000000000) := by
  have h := checkLog_sound (w := (18349181328181 / 82349181328181)) (n := 12)
    (lo := (56655807 / 125000000)) (hi := (453246457 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50349181328181 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(50349181328181 / 32000000000000) = 1/(500000000000 / 50349181328181) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (18016131 / 3906250) (4612129543 / 1000000000) (Real.log (50349181328181 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (50349181328181 / 500000000000) = -Real.log (500000000000 / 50349181328181) := by
    rw [show ((50349181328181 / 500000000000) : ℝ) = ((500000000000 / 50349181328181) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0024
